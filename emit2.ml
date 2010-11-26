open Utils
open Llvm
open Llvm_target
open Llvm_scalar_opts
open Ast
open Llst

module Type = struct

  let is_public md = 
    let acc = ISet.empty in
    let acc = List.fold_left (
      fun acc x ->
	match x with
	| Dval (x, _, _) -> ISet.add x acc
	| _ -> acc
     ) acc md.md_decls in
    acc

  let rec program ctx mdl = 
    let mds = List.fold_left (module_decl ctx) IMap.empty mdl in
    let mds = List.fold_left (module_refine ctx mds) IMap.empty mdl in
    let t = List.fold_left (module_funs ctx mds) IMap.empty mdl in
    mds, t

  and module_decl ctx acc md = 
    let md_id = Ident.to_string md.md_id in
    let llvm_md = create_module ctx md_id in
    let t = List.fold_left (opaques llvm_md ctx) IMap.empty md.md_decls in
    IMap.add md.md_id (llvm_md, t) acc 

  and module_refine ctx mds acc md = 
    let md_name, dl = Ident.to_string md.md_id, md.md_decls in
    let (llmd, t) = IMap.find md.md_id mds in
    let t' = List.fold_left (def_type mds llmd ctx) t dl in
    List.iter (refine t t') dl ;
    IMap.add md.md_id (llmd, t') acc

  and module_funs ctx mds acc md = 
    let pub = is_public md in
    let md_name, dl, decl = md.md_id, md.md_defs, md.md_decls in
    let (md, tys) = IMap.find md_name mds in
    let fs = List.fold_left (def_fun pub mds tys md ctx) IMap.empty dl in
    let fs = List.fold_left (def_external mds tys md ctx) fs decl in
    IMap.add md_name (md, tys, fs, dl) acc

  and opaques md ctx t = function
    | Dtype (x, _) -> 
	let ty = opaque_type ctx in
	assert (define_type_name (Ident.to_string x) ty md) ;
	IMap.add x ty t
    | _ -> t

  and def_type mds md ctx t = function
    | Dtype (x, ty) -> IMap.add x (type_ mds t ctx ty) t
    | _ -> t

  and def_fun pub mds t md ctx acc df = 
    let link = 
      if ISet.mem df.df_id pub 
      then Llvm.Linkage.External
      else Llvm.Linkage.Private
    in
    IMap.add df.df_id (function_ link mds t md ctx df) acc

  and def_external mds t md ctx acc = function
    | Dval (x, ty, Some v) ->
	let ty = type_ mds t ctx ty in
	let fdec = declare_function v ty md in
	IMap.add x fdec acc
    | _ -> acc

  and refine t t' = function
    | Dtype (x, _) -> 
	let ty = IMap.find x t' in
	refine_type (IMap.find x t) ty
    | _ -> ()

  and function_ link mds t md ctx df = 
    let args = List.map fst df.df_args in
    let args = Array.of_list args in
    let args = Array.map (type_ mds t ctx) args in
    let rett = match df.df_ret with [ty] -> type_ mds t ctx ty 
    | l -> struct_type ctx (Array.of_list (List.map (type_ mds t ctx) l)) in
    let ftype = function_type rett args in
    let fdec = declare_function (Ident.to_string df.df_id) ftype md in
    let cconv = Llvm.CallConv.fast in
    set_linkage link fdec ;
    set_function_call_conv cconv fdec ;
(*    add_function_attr fdec Attribute.Nounwind ;
    add_function_attr fdec Attribute.Readnone ; *)
    fdec

  and type_path mds x y = 
    let (md, _) = IMap.find x mds in
    match type_by_name md y with
    | None -> assert false
    | Some ty -> ty

  and type_ mds t ctx = function
    | Tany -> pointer_type (i8_type ctx)
    | Tprim tp -> type_prim mds t ctx tp
(* TODO add primitive types in a cleaner way *)
    | Tid x -> (try IMap.find x t with Not_found -> pointer_type (i8_type ctx)) 
    | Tfun (ty1, [ty2]) -> 
	let ty1 = List.map (type_ mds t ctx) ty1 in
	let ty2 = type_ mds t ctx ty2 in
	function_type ty2 (Array.of_list ty1) 
    | Tfun _ -> failwith "TODO function type" (* of type_expr_list * type_expr_list *)
    | Tstruct tyl -> 
	let tyl = type_list mds t ctx tyl in
	let st = struct_type ctx tyl in
	st
    | Tptr ty -> 
	let ty = type_ mds t ctx ty in
	pointer_type ty

  and type_prim mds t ctx = function 
    | Tunit -> i1_type ctx
    | Tbool -> i1_type ctx
    | Tchar -> i8_type ctx
    | Tint32 -> i32_type ctx
    | Tfloat -> float_type ctx
    | Tstring -> pointer_type (i8_type ctx)

  and type_list mds t ctx l = 
    let tyl = List.map (type_ mds t ctx) l in
    Array.of_list tyl

end

(*module Globals = struct

  let rec module_ ctx llvm_md strings = 
    IMap.iter (declare_string llvm_md ctx) strings

  and declare_string md ctx s v = 
    let x = const_stringz ctx s in
    let g = define_global v x md in
(*    set_global_constant true g ; *)
    set_linkage Linkage.Private g 
end
*)

type env = {
    mds: (llmodule * lltype IMap.t) IMap.t ;
    cmd: llmodule ;
    ctx: llcontext ;
    fmap: llvalue IMap.t ;
    builder: llbuilder ;
    types: lltype IMap.t ;
    prims: llvalue SMap.t ;
    bls: llbasicblock IMap.t ;
    bldone: SSet.t ;
    orig_types: Llst.type_expr IMap.t ;
  }


let dump_module md_file md pm =
  ignore (PassManager.run_module md pm) ;
  Llvm.dump_module md ;
  (match Llvm_analysis.verify_module md with
  | None -> ()
  | Some r -> failwith r) ;
  Llvm_analysis.assert_valid_module md ;
  if Llvm_bitwriter.write_bitcode_file md md_file
  then () (* TODO dispose all modules *)
  else failwith ("Error: module generation failed"^md_file)


let pervasives ctx md = 
  let string = pointer_type (i8_type ctx) in
  let any = string in
  let rty = string in
  let args = i64_type ctx in
  let fty = function_type rty [|args|] in
  let malloc = declare_function "malloc" fty md in

  let tprint = function_type (i32_type ctx) [|string|] in
  let print = declare_function "puts" tprint md in 

  let tprint_int = function_type (void_type ctx) [|i32_type ctx|] in
  let print_int = declare_function "print_int" tprint_int md in 

  let free = declare_function "free" 
      (function_type (void_type ctx) [|pointer_type (i8_type ctx)|]) md in

  let spawn = declare_function "spawn" 
      (function_type any [|any; any|]) md in

  let wait = declare_function "wait" (function_type any [|any|]) md in  

  set_linkage Linkage.External malloc ; 
  set_linkage Linkage.External free ; 
  set_linkage Linkage.External print ; 
  set_linkage Linkage.External print_int ; 
  set_linkage Linkage.External spawn ; 
  set_linkage Linkage.External wait ; 
  let prims = SMap.empty in 
  let prims = SMap.add "malloc" malloc prims in
  let prims = SMap.add "free" free prims in
  let prims = SMap.add "print" print prims in
  let prims = SMap.add "print_int" print_int prims in
  let prims = SMap.add "spawn" spawn prims in
  let prims = SMap.add "wait" wait prims in
  prims



let optims pm = 
  add_constant_propagation pm ;
  add_sccp pm ;
  add_dead_store_elimination pm ;
  add_aggressive_dce pm ;
  add_scalar_repl_aggregation pm ;
  add_ind_var_simplification pm ;
  add_instruction_combination pm ;
  add_licm pm ;
  add_loop_unswitch pm ;
  add_loop_unroll pm ;
  add_loop_rotation pm ;
  add_loop_index_split pm ;
  add_memory_to_register_promotion pm ; 
  add_reassociation pm ;
  add_jump_threading pm ;
  add_cfg_simplification pm ;
  add_tail_call_elimination pm ; 
  add_gvn pm ;
  add_memcpy_opt pm ;
  add_loop_deletion pm ;
  add_lib_call_simplification pm ;


  add_ind_var_simplification pm ;
  add_instruction_combination pm  



let rec program mdl = 
  let ctx = global_context() in
  let mds, t = Type.program ctx mdl in
  List.rev_map (module_ mds ctx t) mdl 

and module_ mds ctx t md = 
  let orig_types = List.fold_left (
    fun acc dt -> 
      match dt with
      | Dtype (x, Tptr y) -> IMap.add x y acc
      | _ -> acc
   ) IMap.empty md.md_decls in
  let md_id, md, strings = md.md_id, md.md_defs, IMap.empty in
  let (md, tys, fs, dl) = IMap.find md_id t in
(*   Globals.module_ ctx md strings ;*)
  let pm = PassManager.create () in
    optims pm ;  
  let builder = builder ctx in
  let prims = pervasives ctx md in
  let env = 
    { mds = mds ;
      cmd = md ;
      ctx = ctx ; 
      fmap = fs ; 
      builder = builder ; 
      types = tys ;
      prims = prims ;
      bls = IMap.empty ;
      bldone = SSet.empty ;
      orig_types = orig_types ;
    } in
  List.iter (def env) dl ;
  dump_module (Ident.to_string md_id^".bc") md pm

and def env df = 
  function_ env df

and function_ env df = 
  let proto = IMap.find df.df_id env.fmap in
  let params = params proto in
  let params = Array.to_list params in
  let ins = List.fold_left2 param env.fmap df.df_args params in 
  ignore (body env proto ins df.df_body) ;
  ()

and param acc (_, x) v = 
  IMap.add x v acc

and body env proto params bll = 
  let bls = List.fold_left (
    fun acc bl ->
      let bb = append_block env.ctx (Ident.to_string bl.bl_id) proto in
      IMap.add bl.bl_id bb acc
   ) IMap.empty bll in
  let env = { env with bls = bls } in
  List.fold_left (block env proto) params bll

and make_phi env acc (x, ty, lbls) = 
  let lbls = List.map (
    fun (x, l) ->
      let bb = IMap.find l env.bls in
      IMap.find x acc, 
      bb
   ) lbls in
  let v = build_phi lbls (Ident.to_string x) env.builder in
  IMap.add x v acc

and block env proto acc bl =
  let is_tailc = ref false in
  let bb = IMap.find bl.bl_id env.bls in
  position_at_end bb env.builder ;  
  let acc = List.fold_left (make_phi env) acc bl.bl_phi in
  let acc = List.fold_left (instruction proto bb env is_tailc) acc bl.bl_eqs in
  if not !is_tailc then (match bl.bl_ret with
  | Return [] -> assert false
  | Return [_, x] -> 
       ignore (build_ret (IMap.find x acc) env.builder)
  | Return l ->
      let l = List.map (fun (_, x) -> IMap.find x acc) l in
      let t = Array.of_list l in
      ignore (build_aggregate_ret t env.builder)
  | Jump lbl -> 
      let target = IMap.find lbl env.bls in
      ignore (build_br target env.builder) 
  | If ((_, x), l1, l2) -> 
      let b1 = IMap.find l1 env.bls in
      let b2 = IMap.find l2 env.bls in
      let x = IMap.find x acc in
      ignore (build_cond_br x b1 b2 env.builder)
  | Switch ((_, x), cases, default) ->
      let x = IMap.find x acc in
      let default = IMap.find default env.bls in
      let n = List.length cases in
      let sw = build_switch x default n env.builder in
      List.iter (
      fun (v, lbl) -> 
	let v = const env (i32_type env.ctx) v in
	let lbl = IMap.find lbl env.bls in
	ignore (add_case sw v lbl)
     ) cases
  );
  acc

and instruction proto bb env is_tailc acc (idl, e) = 
  match idl with 
  | [x] -> expr proto bb env acc x e
  | xl -> (match e with
    | Eapply (tail, f, l) -> 
	let f = IMap.find f acc in
	let l = List.map (fun (_, v) -> IMap.find v acc) l in
	let t = Array.of_list l in
	let v = build_call f t "" env.builder in
	set_instruction_call_conv (function_call_conv f) v ;
	if tail 
	then begin
	  is_tailc := true ;
	  ignore (build_ret v env.builder) ;
	  acc
	end
	else 
	  let n = ref 0 in
	  List.fold_left (
	  fun acc (_, x) -> 
	    let nv = build_extractvalue v !n (Ident.to_string x) env.builder in
	    incr n ;
	    IMap.add x nv acc
	 ) acc xl
    | _ -> assert false)

and expr proto bb env acc (ty, x) e = 
  let xs = Ident.to_string x in
  match e with
  | Eid y -> 
      Ident.print y ;
      let y = IMap.find y acc in
      IMap.add x y acc
  | Evalue v ->
      let ty = Type.type_ env.mds env.types env.ctx ty in
      let v = const env ty v in
      IMap.add x v acc
  | Ebinop (bop, (_, x1), (_, x2)) -> 
      let x1 = IMap.find x1 acc in
      let x2 = IMap.find x2 acc in
      let bop = binop bop in
      let v = bop x1 x2 xs env.builder in
      IMap.add x v acc
  | Ecast (ty, y) -> 
      let ty = Type.type_ env.mds env.types env.ctx ty in      
      let y = IMap.find y acc in
      let v = build_bitcast y ty xs env.builder in
      IMap.add x v acc

(* TODO make a cleaner mechanism for primitives *)
  | Eapply (_, f, [_, v]) when f = Naming.print_int ->
      let f = SMap.find "print_int" env.prims in
      let v = IMap.find v acc in
      let c = build_call f [|v|] "" env.builder in
      set_instruction_call_conv (function_call_conv f) c ; 
      IMap.add x (const_int (i1_type env.ctx) 0) acc            
  | Eapply (_, f, [_, v]) when f = Naming.free ->
      let f = SMap.find "free" env.prims in
      let v = IMap.find v acc in
      let v = build_bitcast v (pointer_type (i8_type env.ctx)) "" env.builder in 
      let c = build_call f [|v|] "" env.builder in
      set_instruction_call_conv (function_call_conv f) c ;  
      IMap.add x (const_int (i1_type env.ctx) 0) acc
  | Eapply (_, f, [_, v]) when f = Naming.wait ->
      let f = SMap.find "wait" env.prims in
      let v = IMap.find v acc in
      let v = build_bitcast v (pointer_type (i8_type env.ctx)) "" env.builder in 
      let c = build_call f [|v|] "" env.builder in
      set_instruction_call_conv (function_call_conv f) c ;  
      let ty = Type.type_ env.mds env.types env.ctx ty in
      let c = build_bitcast c ty "" env.builder in 
      IMap.add x c acc
  | Eapply (_, f, [(_, v1) ; (_, v2)]) when f = Naming.spawn ->
      let f = SMap.find "spawn" env.prims in
      let v1 = IMap.find v1 acc in
      let v1 = build_bitcast v1 (pointer_type (i8_type env.ctx)) "" env.builder in 
      let v2 = IMap.find v2 acc in
      let v2 = build_bitcast v2 (pointer_type (i8_type env.ctx)) "" env.builder in 
      let c = build_call f [|v1 ; v2|] "" env.builder in
      set_instruction_call_conv (function_call_conv f) c ;  
      let ty = Type.type_ env.mds env.types env.ctx ty in
      let c = build_bitcast c ty "" env.builder in 
      IMap.add x c acc

  | Eapply (_, f, l) -> 
      let f = IMap.find f acc in
      let l = List.map (fun (_, v) -> IMap.find v acc) l in
      let t = Array.of_list l in
      let v = build_call f t xs env.builder in
      set_instruction_call_conv (function_call_conv f) v ;
      IMap.add x v acc
  | Eis_null (_, v) -> 
      let v = IMap.find v acc in
      let v = build_is_null v xs env.builder in
      IMap.add x v acc
  | Eproj ((_, y), n) -> 
      let y = IMap.find y acc in
      let z = const_int (i32_type env.ctx) 0 in
      let v = build_gep y [|z|] xs env.builder in
      let v = build_struct_gep v n xs env.builder in 
      let v = build_load v xs env.builder in
      IMap.add x v acc 
  | Etuple (v, fdl) -> 
      let bl = match v with
      | None ->
	  let orig_ty = match ty with Tid x -> 
	    IMap.find x env.orig_types 
	  | _ -> assert false in
	  let ty = Type.type_ env.mds env.types env.ctx ty in  
	  let oty = Type.type_ env.mds env.types env.ctx orig_ty in  
	  let v = size_of oty in
	  let malloc = SMap.find "malloc" env.prims in
	  let bl = build_call malloc [|v|] "" env.builder in
	  let bl = build_bitcast bl ty xs env.builder in 
	  bl
      | Some (_, v) -> IMap.find v acc in
      let z = const_int (i32_type env.ctx) 0 in
      List.iter (fun (n, (_, v)) -> 
	let n = const_int (i32_type env.ctx) n in
	let v = IMap.find v acc in
	let ptr = build_gep bl [|z;n|] "" env.builder in
	ignore (build_store v ptr env.builder)) fdl ;
      IMap.add x bl acc      
  | Enull -> 
      let v = const_null (Type.type_ env.mds env.types env.ctx ty) in
      IMap.add x v acc
  | Eint_of_ptr _ -> failwith "TODO Eint_of_ptr"
  | Eptr_of_int _ -> failwith "TODO Eptr_of_int"
  | Egetargs _ -> failwith "TODO Egetargs"
  | Egettag (_, v) -> 
      let bl = IMap.find v acc in
      let z = const_int (i32_type env.ctx) 0 in
      let ptr = build_gep bl [|z|] "" env.builder in
      let v = build_load ptr "" env.builder in
      IMap.add x v acc
  | Efield (_, _) -> failwith "TODO Efield"
  | Euop (_, _) -> failwith "TODO Euop"
(*  
  | Switch of id * (value * label) list * label

  | Extract_value of id * type_ * idx
  | Insert of id * type_ * type_ * idx
  | Alloca of id * type_ 
  | Load of id * type_ * id
  | Get_element_ptr of id * int
  | Icmp of id * icmp * type_ * id * id
  | Fcmp of id * fcmp * type_ * id * id
  | Return of id

*)

and binop = function
  | Eeq -> build_icmp Llvm.Icmp.Eq 
  | Elt -> build_icmp Llvm.Icmp.Slt 
  | Elte -> build_icmp Llvm.Icmp.Sle
  | Egt -> build_icmp Llvm.Icmp.Sgt 
  | Egte -> build_icmp Llvm.Icmp.Sge
  | Eplus -> build_add
  | Eminus -> build_sub
  | Estar -> build_mul

and const env ty = function
  | Eunit -> const_int (i1_type env.ctx) 0
  | Ebool true -> const_int (i1_type env.ctx) 1
  | Ebool false -> const_int (i1_type env.ctx) 0
  | Eint s -> 
      const_int_of_string ty s 10 (* TODO different radix *)
  | Eiint x ->
      const_int (i32_type env.ctx) x 
  | Efloat s -> 
      const_float_of_string ty s
  | _ -> failwith "TODO constant"

