open Utils
open Llvm
open Llvm_target
open Llvm_scalar_opts
open Llast

module Type = struct

  let rec program ctx mdl = 
    let mds = List.fold_left (module_decl ctx) SMap.empty mdl in
    let mds = List.fold_left (module_refine ctx mds) SMap.empty mdl in
    let t = List.fold_left (module_funs ctx mds) SMap.empty mdl in
    mds, t

  and module_decl ctx acc md = 
    let llvm_md = create_module ctx md.md_id in
    let t = List.fold_left (opaques llvm_md ctx) SMap.empty md.md_defs in
    SMap.add md.md_id (llvm_md, t) acc 

  and module_refine ctx mds acc md = 
    let md_name, dl = md.md_id, md.md_defs in
    let (md, t) = SMap.find md_name mds in
    let t' = List.fold_left (def_type mds ctx) t dl in
    List.iter (refine t t') dl ;
    SMap.add md_name (md, t') acc

  and module_funs ctx mds acc md = 
    let md_name, dl = md.md_id, md.md_defs in
    let (md, tys) = SMap.find md_name mds in
    let fs = List.fold_left (def_fun mds tys md ctx) SMap.empty dl in
    SMap.add md_name (md, tys, fs, dl) acc

  and opaques md ctx t = function
    | Type (x, _) -> 
	let ty = opaque_type ctx in
	assert (define_type_name x ty md) ;
	SMap.add x ty t
    | _ -> t

  and def_type mds ctx t = function
    | Type (x, ty) -> SMap.add x (type_ mds t ctx ty) t
    | _ -> t

  and def_fun mds t md ctx acc = function
    | Fun f -> SMap.add f.fname (function_ mds t md ctx f) acc
    | _ -> acc

  and refine t t' = function
    | Type (x, _) -> 
	let ty = SMap.find x t' in
	refine_type (SMap.find x t) ty
    | _ -> ()

  and function_ mds t md ctx f = 
    let args = Array.of_list f.ftargs in
    let args = Array.map (type_ mds t ctx) args in
    let rett = type_ mds t ctx f.frett in
    let ftype = function_type rett args in
    let fdec = declare_function f.fname ftype md in
    set_linkage f.flink fdec ;
    set_function_call_conv f.fcc fdec ;
    fdec

  and type_path mds x y = 
    let (md, _) = SMap.find x mds in
    match type_by_name md y with
    | None -> assert false
    | Some ty -> ty

  and type_ mds t ctx = function
    | Any -> pointer_type (i8_type ctx)
    | Id x -> SMap.find x t
    | Path (x, y) -> type_path mds x y
    | Void -> i1_type ctx
    | Int1 -> i1_type ctx
    | Int8 -> i8_type ctx
    | Int16 -> i16_type ctx
    | Int32 -> i32_type ctx
    | Int64 -> i64_type ctx
    | ConstInt -> i32_type ctx
    | Float -> float_type ctx
    | Double -> double_type ctx
    | Union tyl -> failwith "TODO"
(*	let tyl = type_list mds t ctx tyl in
	union_type ctx tyl *)
    | Array ty -> 
	pointer_type (type_ mds t ctx ty)
    | Pointer ty -> 
	let ty = type_ mds t ctx ty in
	pointer_type ty
    | Struct tyl -> 
	let tyl = type_list mds t ctx tyl in
	let st = struct_type ctx tyl in
	st
    | Function _ -> assert false

  and type_list mds t ctx l = 
    let tyl = List.map (type_ mds t ctx) l in
    Array.of_list tyl

end

module Globals = struct

  let rec module_ ctx llvm_md strings = 
    SMap.iter (declare_string llvm_md ctx) strings

  and declare_string md ctx s v = 
    let x = const_stringz ctx s in
    let g = define_global v x md in
(*    set_global_constant true g ; *)
    set_linkage Linkage.Private g 
end

type env = {
    mds: (llmodule * lltype SMap.t) SMap.t ;
    cmd: llmodule ;
    ctx: llcontext ;
    fmap: llvalue SMap.t ;
    builder: llbuilder ;
    types: lltype SMap.t ;
    prims: llvalue SMap.t ;
    bls: llbasicblock SMap.t ;
    bldone: SSet.t ;
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
  let rty = string in
  let args = i64_type ctx in
  let fty = function_type rty [|args|] in
  let malloc = declare_function "malloc" fty md in
  let tprint = function_type (i32_type ctx) [|string|] in
  let print = declare_function "puts" tprint md in 
  let tprint_int = function_type (i32_type ctx) [|i32_type ctx|] in
  let print_int = declare_function "print_int" tprint_int md in 
  set_linkage Linkage.External malloc ; 
  set_linkage Linkage.External print ; 
  set_linkage Linkage.External print_int ; 
  let prims = SMap.empty in 
  let prims = SMap.add "malloc" malloc prims in
  let prims = SMap.add "print" print prims in
  let prims = SMap.add "print_int" print_int prims in
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
(*  add_memory_to_register_demotion pm ; *)
  add_reassociation pm ;
  add_jump_threading pm ;
  add_cfg_simplification pm ;
  add_tail_call_elimination pm ;
  add_gvn pm ;
  add_memcpy_opt pm ;
  add_loop_deletion pm ;
  add_lib_call_simplification pm 

let rec program mdl = 
  let ctx = global_context() in
  let mds, t = Type.program ctx mdl in
  List.rev_map (module_ mds ctx t) mdl 

and module_ mds ctx t md = 
  let md_id, md, strings = md.md_id, md.md_defs, md.md_strings in
  let (md, tys, fs, dl) = SMap.find md_id t in
  Globals.module_ ctx md strings ;
  let pm = PassManager.create () in
(*   optims pm ;  *)
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
      bls = SMap.empty ;
      bldone = SSet.empty ;
    } in
  List.iter (def env) dl ;
  dump_module (md_id^".bc") md pm

and def env = function
  | Type _ -> ()
  | Fun f -> ignore (function_ env f)

and function_ env f = 
  let proto = SMap.find f.fname env.fmap in
  let params = params proto in
  let params = Array.to_list params in
  let ins = List.fold_left2 param env.fmap f.fargs params in 
  ignore (body env proto ins f.fbody) ;
  ()

and param acc x v = 
  SMap.add x v acc

and body env proto params bll = 
  let bls = List.fold_left (
    fun acc bl ->
      let bb = append_block env.ctx bl.bname proto in
      SMap.add bl.bname bb acc
   ) SMap.empty bll in
  let env = { env with bls = bls } in
  List.fold_left (block env proto) params bll

and make_phi env acc (x, ty, lbls) = 
  let lbls = List.map (
    fun (x, l) ->
      let bb = SMap.find l env.bls in
      SMap.find x acc, 
      bb
   ) lbls in
  let v = build_phi lbls x env.builder in
  SMap.add x v acc

and block env proto acc bl = 
  let bb = SMap.find bl.bname env.bls in
  position_at_end bb env.builder ;  
  let acc = List.fold_left (make_phi env) acc bl.bdecl in
  let acc = List.fold_left (instruction proto bb env) acc bl.bbody in
  (match bl.bret with
  | Return [] -> assert false
  | Return [x] -> 
       ignore (build_ret (SMap.find x acc) env.builder)
  | Return l ->
      let l = List.map (fun x -> SMap.find x acc) l in
      let t = Array.of_list l in
      ignore (build_aggregate_ret t env.builder)
  | Jmp lbl -> 
      let target = SMap.find lbl env.bls in
      ignore (build_br target env.builder) 
  | Br (x, l1, l2) -> 
      let b1 = SMap.find l1 env.bls in
      let b2 = SMap.find l2 env.bls in
      let x = SMap.find x acc in
      ignore (build_cond_br x b1 b2 env.builder)
  | Switch (x, cases, default) ->
      let x = SMap.find x acc in
      let default = SMap.find default env.bls in
      let n = List.length cases in
      let sw = build_switch x default n env.builder in
      List.iter (
      fun (v, lbl) -> 
	let v = SMap.find v acc in
	let lbl = SMap.find lbl env.bls in
	ignore (add_case sw v lbl)
     ) cases
  );
  acc

and instruction proto bb env acc = function
  | Alias (x, y) -> 
      let y = SMap.find y acc in
      SMap.add x y acc
  | Const (x, ty, v) ->
      let ty = Type.type_ env.mds env.types env.ctx ty in
      let v = const env ty v in
      SMap.add x v acc
  | Binop (x, bop, ty, x1, x2) -> 
      let x1 = SMap.find x1 acc in
      let x2 = SMap.find x2 acc in
      let bop = binop bop in
      let v = bop x1 x2 x env.builder in
      SMap.add x v acc
  | Alloc (x, ty) -> 
      let ty = Type.type_ env.mds env.types env.ctx ty in      
      let v = size_of ty in
      let malloc = SMap.find "malloc" env.prims in
      let bl = build_call malloc [|v|] "" env.builder in
      let bl = build_bitcast bl ty x env.builder in
      SMap.add x bl acc
  | VAlloc (x, ty, vty) -> 
      let vty = Type.type_ env.mds env.types env.ctx vty in      
      let v1 = size_of vty in
      let v2 = size_of (i32_type env.ctx) in
      let v = const_add v1 v2 in
      let malloc = SMap.find "malloc" env.prims in
      let bl = build_call malloc [|v|] "" env.builder in
      SMap.add x bl acc
  | Store (x, y) -> 
      let x = SMap.find x acc in
      let y = SMap.find y acc in
      ignore (build_store y x env.builder) ;   
      acc
  | Get_element_ptr (x, y, n) -> 
      let y = SMap.find y acc in
      let n = const_int (i32_type env.ctx) n in
      let v = build_gep y [|n|] x env.builder in
      SMap.add x v acc
  | Get_field (x, y, n) -> 
      let y = SMap.find y acc in
      let z = const_int (i32_type env.ctx) 0 in
      let v = build_gep y [|z|] x env.builder in
      let v = build_struct_gep v n x env.builder in 
      SMap.add x v acc
  | Cast (x, y, ty) -> 
      let ty = Type.type_ env.mds env.types env.ctx ty in      
      let y = SMap.find y acc in
      let v = build_bitcast y ty x env.builder in
      SMap.add x v acc
  | Call (tail, x, f, l) ->
      let f = try SMap.find f acc with Not_found -> SMap.find f env.prims in
      let l = List.map (fun v -> SMap.find v acc) l in
      let t = Array.of_list l in
      let v = build_call f t x env.builder in
      set_instruction_call_conv (function_call_conv f) v ;
      set_tail_call tail v ;
      SMap.add x v acc
  | Icmp (x, op, _, v1, v2) -> 
      let cmp = icmp op in
      let v1 = SMap.find v1 acc in
      let v2 = SMap.find v2 acc in
      let v = build_icmp cmp v1 v2 x env.builder in
      SMap.add x v acc
  | Extract_value _ -> failwith "TODO Extract_value in emit.ml"
  | Insert _ -> failwith "TODO Insert in emit.ml"
  | Alloca _ -> failwith "TODO Alloca in emit.ml"
  | Load _ -> failwith "TODO Load in emit.ml"
  | Fcmp _ -> failwith "TODO Fcmp in emit.ml"


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
  | Add -> build_add
  | Fadd -> build_fadd
  | Sub -> build_sub
  | Fsub -> build_fsub
  | Mul -> build_mul
  | Fmul -> build_fmul 
  | Udiv -> build_udiv 
  | Sdiv -> build_sdiv 
  | Fdiv -> build_fdiv 
  | Urem -> build_urem 
  | Srem -> build_srem 
  | Frem -> build_frem 
  | Shl -> build_shl 
  | Lshr -> build_lshr 
  | Ashr -> build_ashr 
  | And -> build_and
  | Or -> build_or 
  | Xor -> build_xor

and const env ty = function
  | Const_int s -> 
      const_int_of_string ty s 10 (* TODO different radix *)
  | Const_float s -> 
      const_float_of_string ty s
  | Const_enum i ->
      let n = const_int (i16_type env.ctx) i in
      let n = const_inttoptr n (pointer_type (i8_type env.ctx)) in
      n
  | Const_string v -> 
      match lookup_global v env.cmd with 
      | None -> assert false
      | Some s -> 
	  let z = const_int (i64_type env.ctx) 0 in
	  let s = const_gep s [|z;z|] in
	  s

and icmp = function
  | Llast.Eq -> Llvm.Icmp.Eq 
  | Llast.Ne -> Llvm.Icmp.Ne 
  | Llast.Ugt -> Llvm.Icmp.Ugt 
  | Llast.Uge -> Llvm.Icmp.Uge
  | Llast.Ult -> Llvm.Icmp.Ult 
  | Llast.Ule -> Llvm.Icmp.Ule 
  | Llast.Sgt -> Llvm.Icmp.Sgt 
  | Llast.Sge -> Llvm.Icmp.Sge
  | Llast.Slt -> Llvm.Icmp.Slt 
  | Llast.Sle -> Llvm.Icmp.Sle
