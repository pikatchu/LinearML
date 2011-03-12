(*
Copyright (c) 2011, Julien Verlaguet
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:
1. Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the
distribution.

3. Neither the name of Julien Verlaguet nor the names of
contributors may be used to endorse or promote products derived
from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)
open Utils
open Llvm
open Llvm_target
open Llvm_scalar_opts
open Llvm_executionengine
open Ast
open Llst

let ccc = Llvm.CallConv.c
let ccfast = Llvm.CallConv.fast 

let make_cconv = function
  | Ast.Cfun -> ccc
  | Ast.Lfun -> ccfast

module MakeNames = struct

  let rec program mdl = 
    List.iter module_ mdl

  and module_ md = 
    List.iter (decl md.md_id) md.md_decls 

  and decl md = function
    | Dval (_, x, _, (Ast.Ext_C y| Ast.Ext_Asm y)) -> 
	Ident.no_origin x ;
	Ident.set_name x (snd y)
    | Dtype (x, _)
    | Dval (_, x, _, _) ->
	Ident.expand_name md x
end

module Type = struct

  let public_name md_id x = 
    Ident.expand_name md_id x ;
    Ident.full x

  let rec program root is_lib ctx mdl = 
    MakeNames.program mdl ;
    let llmd = create_module ctx root in 
    let mds = List.fold_left (module_decl ctx llmd) IMap.empty mdl in
    let mds = List.fold_left (module_refine ctx mds) IMap.empty mdl in
    let t = List.fold_left (module_funs is_lib ctx mds) IMap.empty mdl in
    llmd, mds, t

  and module_decl ctx llmd acc md = 
    let t = List.fold_left (opaques md.md_id llmd ctx) IMap.empty md.md_decls in
    IMap.add md.md_id (llmd, t) acc 

  and module_refine ctx mds acc md = 
    let (llmd, t) = IMap.find md.md_id mds in
    let t' = List.fold_left (def_type mds llmd ctx) t md.md_decls in
    List.iter (refine t t') md.md_decls ;
    IMap.add md.md_id (llmd, t') acc

  and module_funs is_lib ctx mds acc md = 
    let md_sig, md_id, dl, decl = md.md_sig, md.md_id, md.md_defs, md.md_decls in
    let (md, tys) = IMap.find md_id mds in
    let lkinds = List.fold_left (
      fun acc dec -> 
	match dec with 
	| Dval (ll, x, _, _) -> IMap.add x ll acc
	| _ -> acc) IMap.empty decl in
    let fs = List.fold_left (def_fun is_lib md_id mds tys md ctx lkinds) IMap.empty dl in
    let fs = List.fold_left (def_external md_id mds tys md ctx md_sig) fs decl in
    IMap.add md_id (md, tys, fs, dl) acc

  and opaques md_id md ctx t = function
    | Dtype (x, _) -> 
	let ty = opaque_type ctx in
	let name = public_name md_id x in
	assert (define_type_name name ty md) ;
	IMap.add x ty t
    | _ -> t

  and def_type mds md ctx t = function
    | Dtype (x, ty) -> IMap.add x (type_ mds t ctx ty) t
    | _ -> t

  and def_fun is_lib md_name mds t md ctx lkinds acc df = 
    let fun_ = function_ is_lib md_name mds t md ctx lkinds df in
    IMap.add df.df_id fun_ acc

  and def_external md_name mds t md ctx md_sig acc = function
    | Dval (_, x, Tfun (_, ty1, ty2), (Ast.Ext_C (_, v) | Ast.Ext_Asm (_, v))) ->
	let ty = type_fun mds t ctx ty1 ty2 in
	let fdec = declare_function v ty md in
	IMap.add x fdec acc
    | Dval (_, x, Tfun (_, ty1, ty2), _) when md_sig ->
	let ftype = type_fun mds t ctx ty1 ty2 in
	let name = public_name md_name x in
	let fdec = declare_function name ftype md in
	IMap.add x fdec acc
    | _ -> acc

  and refine t t' = function
    | Dtype (x, _) -> 
	let ty = IMap.find x t' in
	refine_type (IMap.find x t) ty
    | _ -> ()

  and function_ is_lib md_name mds t md ctx lkinds df = 
    let link = 
      match IMap.find df.df_id lkinds with 
      | Public | Abstract -> Llvm.Linkage.External 
      | _ -> Llvm.Linkage.Private in
    let args = List.map fst df.df_args in
    let ftype = type_fun mds t ctx args df.df_ret in
    let name = public_name md_name df.df_id in
    let fdec = declare_function name ftype md in
    let cconv = make_cconv df.df_kind in
    set_linkage link fdec ;
    set_function_call_conv cconv fdec ;
    fdec

  and type_path mds x y = 
    let (md, _) = IMap.find x mds in
    match type_by_name md y with
    | None -> assert false
    | Some ty -> ty

  and type_fun mds t ctx ty1 ty2 =
    let ty1, ty2 = 
      if List.length ty2 > Global.max_reg_return
      then Tptr (Tstruct ty2) :: ty1, [Tprim Tunit]
      else ty1, ty2 in
    let ty1 = type_args mds t ctx ty1 in
    let rty = type_list mds t ctx ty2 in
    let fty = function_type rty ty1 in
    fty 

  and type_args mds t ctx l = 
    match l with
    | l -> Array.of_list (List.map (type_ mds t ctx) l)

  and type_ mds t ctx = function
    | Tany -> pointer_type (i8_type ctx)
    | Tprim tp -> type_prim ctx tp
    | Tid x -> (
	try IMap.find x t 
	with Not_found -> 
	  try 
	    let md_id = Ident.origin_id x in
	    let _, tys = IMap.find md_id mds in
	    IMap.find x tys
	  with Not_found ->
	    pointer_type (i8_type ctx)) 
    | Tfun (_, ty1, ty2) -> 
	let fty = type_fun mds t ctx ty1 ty2 in
	pointer_type fty
    | Tstruct tyl -> 
	let tyl = List.map (type_ mds t ctx) tyl in
	let st = struct_type ctx (Array.of_list tyl) in
	st
    | Tptr ty -> 
	let ty = type_ mds t ctx ty in
	pointer_type ty

  and type_prim ctx = function 
    | Tunit -> type_prim ctx Tint
    | Tbool -> i1_type ctx
    | Tchar _
    | Tint when Global.arch_type = "ARCH_32" -> i32_type ctx 
    | Tchar _
    | Tint  -> i64_type ctx 
    | Tfloat when Global.arch_type = "ARCH_32" -> float_type ctx
    | Tfloat -> double_type ctx
    | Tstring -> pointer_type (i8_type ctx)

  and type_list mds t ctx l = 
    let tyl = List.map (type_ mds t ctx) l in
    match tyl with
    | [] -> assert false
    | [x] -> x 
    | _ -> struct_type ctx (Array.of_list tyl)

  and fun_decl mds t ctx = function
    | Tfun (_, ty1, ty2) -> 
	let fty = type_fun mds t ctx ty1 ty2 in
	fty
    | ty -> LlstPp.type_expr ty ; assert false
end

module Pervasives = struct

(*
  let unsafe_iarray_set md ctx interns = 
    let builder = builder ctx in
    let name = "unsafe_iarray_set" in
    let link = Llvm.Linkage.Private in
    let int = Type.type_prim ctx Llst.Tint in
    let iarray = pointer_type int in
    let void_star = pointer_type (i8_type ctx) in
    let args = [| void_star ; int ; int |] in
    let ftype = function_type void_star args in 
    let fdec = declare_function name ftype md in
    let cconv = ccfast in
    set_linkage link fdec ;
    set_function_call_conv cconv fdec ;
    add_function_attr fdec Attribute.Alwaysinline ;
    let params = params fdec in
    let bb = append_block ctx "" fdec in
    position_at_end bb builder ;  
    let t = build_bitcast params.(0) iarray "" builder in
    let t = build_gep t [|params.(1)|] "" builder in
    let _ = build_store params.(2) t builder in
    let _ = build_ret params.(0) builder in 
    SMap.add name fdec interns
*)

  let enot md ctx = 
    let builder = builder ctx in
    let int = Type.type_prim ctx Llst.Tint in
    let bool = Type.type_prim ctx Llst.Tbool in
    let ftype = function_type int [|int|] in
    let fdec = declare_function "not" ftype md in
    set_linkage Llvm.Linkage.Private fdec ;
    add_function_attr fdec Attribute.Alwaysinline ;
    let params = params fdec in
    let bb = append_block ctx "" fdec in
    position_at_end bb builder ;
    let v = build_intcast params.(0) bool "" builder in
    let v = build_not v "" builder in
    let v = build_intcast v int "" builder in
    let _ = build_ret v builder in
    fdec
  
  let mk_trampoline = Ident.make "trampoline"

  let make ctx md = 
    let string = pointer_type (i8_type ctx) in
    let unit = Type.type_prim ctx Llst.Tint in
    let args = i64_type ctx in
    let fty = function_type string [|args|] in
    let malloc = declare_function "malloc" fty md in
    let free = declare_function "free" 
	(function_type unit [|pointer_type (i8_type ctx)|]) md in    
    let trampoline = declare_function "llvm.init.trampoline" 
	(function_type string [|string ; string ; string|]) md in 
    set_linkage Linkage.External malloc ; 
    set_linkage Linkage.External free ; 
    set_linkage Linkage.External trampoline ; 
    let prims = IMap.empty in 
    let prims = IMap.add Naming.malloc malloc prims in
    let prims = IMap.add Naming.ifree free prims in
    let prims = IMap.add mk_trampoline trampoline prims in
    let prims = IMap.add Naming.bnot (enot md ctx) prims in
    prims

end

module MakeRoot = struct

  let make root ctx md = 
    let f = root^"_main" in
    let f = 
      match lookup_function f md with
      | None -> Printf.fprintf stderr "Main not found in %s\n" root ; exit 2
      | Some f -> f in
    let builder = builder ctx in
    let name = "main" in
    let int = Type.type_prim ctx Llst.Tint in
    let z = const_int int 0 in
    let ftype = function_type int [|int|] in 
    let fdec = declare_function name ftype md in
    let bb = append_block ctx "" fdec in
    position_at_end bb builder ;  
    let v = build_call f [|z|] "" builder in
    set_instruction_call_conv ccfast v ; (* TODO check signature etc ... *)
    let _ = build_ret z builder in 
    ()

end

type env = {
    mds: (llmodule * lltype IMap.t) IMap.t ;
    cmd: llmodule ;
    ctx: llcontext ;
    fmap: llvalue IMap.t ;
    builder: llbuilder ;
    types: lltype IMap.t ;
    prims: llvalue IMap.t ;
    bls: llbasicblock IMap.t ;
    orig_types: Llst.type_expr IMap.t ;
    cblock: Ident.t ref ;
    ret: llvalue option ref ;
  }

let dump_module md_file md pm =
  ignore (PassManager.run_module md pm) ;
  (match Llvm_analysis.verify_module md with
  | None -> ()
  | Some r -> failwith r) ;
  Llvm_analysis.assert_valid_module md ;
  if Llvm_bitwriter.write_bitcode_file md md_file
  then () 
  else failwith ("Error: module generation failed"^md_file)

let optims pm = 
  ()
    ;  add_constant_propagation pm
    ;  add_sccp pm
    ;  add_dead_store_elimination pm
    ;  add_aggressive_dce pm
    ;  add_scalar_repl_aggregation pm
    ;  add_ind_var_simplification pm
    ;  add_instruction_combination pm  
    ;  add_licm pm
    ;  add_loop_unswitch pm
    ;  add_loop_unroll pm
    ;  add_loop_rotation pm
    ;  add_loop_index_split pm
    ;  add_memory_to_register_promotion pm 
    ;  add_reassociation pm
    ;  add_jump_threading pm
    ;  add_cfg_simplification pm
    ;  add_gvn pm
    ;  add_memcpy_opt pm
    ;  add_loop_deletion pm
    ;  add_tail_call_elimination pm
    ;  add_lib_call_simplification pm
    ;  add_ind_var_simplification pm
    ;  add_instruction_combination pm  
    ;  add_constant_propagation pm
    ;  add_sccp pm
    ;  add_dead_store_elimination pm
    ;  add_aggressive_dce pm
    ;  add_scalar_repl_aggregation pm
    ;  add_ind_var_simplification pm  
    ; add_instruction_combination pm 


let rec program base root no_opt dump_as mdl = 
  let ctx = global_context() in
  let llmd, mds, t = Type.program base (root <> "") ctx mdl in
  set_data_layout Global.data_layout llmd ;
  let origs = List.fold_left (
    fun acc md ->
      List.fold_left (
      fun acc dt -> 
	match dt with
	| Dtype (x, Tptr y) -> IMap.add x y acc
	| _ -> acc
     ) acc md.md_decls) IMap.empty mdl in
  let _ = List.rev_map (module_ no_opt dump_as mds ctx t origs) mdl in
  let pm = PassManager.create () in
  if no_opt
  then ()
  else optims pm ;
  if dump_as then
    Llvm.dump_module llmd     
  else () ;
  if root <> ""
  then MakeRoot.make root ctx llmd ;
  let md_name = base^".bc" in
  dump_module md_name llmd pm ;
  md_name
  
and module_ no_opt dump_as mds ctx t orig_types md = 
  let md_id, md, strings = md.md_id, md.md_defs, IMap.empty in
  let (md, tys, fs, dl) = IMap.find md_id t in
  let builder = builder ctx in
  let prims = Pervasives.make ctx md in
  let env = { 
    mds = mds ;
    cmd = md ;
    ctx = ctx ; 
    fmap = fs ; 
    builder = builder ; 
    types = tys ;
    prims = prims ;
    bls = IMap.empty ;
    cblock = ref Ident.foo ;
    orig_types = orig_types ;
    ret = ref None ;
  } in
  List.iter (def env) dl ;
(*  dump_module dump_as (Ident.to_string md_id^".bc") md pm ;
*)
  md

and def env df = 
  function_ env df

and function_ env df = 
  let proto = IMap.find df.df_id env.fmap in
  let params = params proto in
  let params = Array.to_list params in
  let ret, params = 
    match params with
    | ret :: params when List.length df.df_ret > Global.max_reg_return ->
      Some ret, params 
    | _ -> None, params in
  env.ret := ret ;
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
  List.fold_left (block env) params bll

and make_phi env acc (x, ty, lbls) = 
  let lbls = List.map (
    fun (x, l) ->
      let bb = IMap.find l env.bls in
      IMap.find x acc, 
      bb
   ) lbls in
  let v = build_phi lbls (Ident.to_string x) env.builder in
  IMap.add x v acc

and block env acc bl =
  env.cblock := bl.bl_id ;
  let bb = IMap.find bl.bl_id env.bls in
  position_at_end bb env.builder ;  
  let acc = List.fold_left (make_phi env) acc bl.bl_phi in
  let acc = instructions bb env acc bl.bl_ret bl.bl_eqs in 
  acc

and return env acc = function
  | Return (_, l) -> 
      let l = List.map (fun (_, x) -> IMap.find x acc) l in
      (match Array.of_list l with
      | [||] -> assert false
      | [|x|] -> ignore (build_ret x env.builder)
      | t -> 
	  (match !(env.ret) with
	  | None -> ignore (build_aggregate_ret t env.builder)
	  | Some rt -> ret_struct env rt t))
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
	let int = Type.type_prim env.ctx Llst.Tint in
	let v = const env int v in
	let lbl = IMap.find lbl env.bls in
	ignore (add_case sw v lbl)
     ) cases

and ret_struct env st t =
  Array.iteri (
  fun i x ->
      let ptr = build_struct_gep st i "" env.builder in 
      let _ = build_store x ptr env.builder in
      ()
 ) t ;
  ignore (build_ret_void env.builder)

and build_args acc l = 
  match l with
  | _ -> List.map (fun (_, v) -> IMap.find v acc) l

and instructions bb env acc ret l = 
  match l with
  | [] -> return env acc ret ; acc
  | [vl1, Eapply (fk, _, f, l) as instr] ->
      (match ret with 
      | Return (tail, vl2) when tail && fk = Ast.Lfun -> 
	  let t = build_args acc l in
	  let f = find_function env acc (fst f) (snd f) in
	  let v = build_call f (Array.of_list t) "" env.builder in
	  set_tail_call true v ;
	  set_instruction_call_conv ccfast v ;
	  if vl2 = []
	  then ignore (build_ret_void env.builder)
	  else ignore (build_ret v env.builder) ;
	  acc
      | Return (_, vl2) ->
	  let acc = instruction bb env acc instr in
	  return env acc ret ;
	  acc
      | _ -> 
	  let acc = instruction bb env acc instr in
	  return env acc ret ;
	  acc
      )
  | instr :: rl -> 
      let acc = instruction bb env acc instr in
      instructions bb env acc ret rl

and instruction bb env acc (idl, e) = 
  match idl, e with 
  | [(_, x)], Efree (_, v) ->
      let f = IMap.find Naming.ifree env.prims in
      let v = IMap.find v acc in
      let v = build_bitcast v (pointer_type (i8_type env.ctx)) "" env.builder in
      let v = build_call f [|v|] "" env.builder in
      let cconv = Llvm.CallConv.c in
      set_instruction_call_conv cconv v ;
      let int = Type.type_prim env.ctx Llst.Tint in
      let z = const_int int 0 in
      IMap.add x z acc
  | [(_, x1) ; (_, x2)], Eswap (t, i, (ty, v)) ->
      let el_ty = Type.type_ env.mds env.types env.ctx ty in
      let t = IMap.find (snd t) acc in
      let i = IMap.find (snd i) acc in
      let v = IMap.find v acc in
      let tarray = pointer_type el_ty in
      let t' = build_bitcast t tarray "" env.builder in
      let t' = build_gep t' [|i|] "" env.builder in
      let res = build_load t' "" env.builder in
      let _ = build_store v t' env.builder in
      let acc = IMap.add x1 t acc in
      let acc = IMap.add x2 res acc in
      acc
  | (xl, Eapply (fk, _, f, l)) -> 
      apply env acc xl fk f l
  | [x], e -> expr bb env acc x e
  | _ -> assert false

and find_function env acc fty f =
  let is_prim = IMap.mem f env.prims in
  try if is_prim then IMap.find f env.prims else IMap.find f acc 
  with Not_found -> 
    let f_name = Ident.full f in
    let ftype = Type.fun_decl env.mds env.types env.ctx fty in   
    let fdec = declare_function f_name ftype env.cmd in
    let cconv = match fty with
    | Tfun (fk, _, _) -> make_cconv fk 
    | _ -> assert false in
    set_linkage Linkage.External fdec ; 
    set_function_call_conv cconv fdec ;
    fdec
  
and apply env acc xl fk (fty, f) argl = 
  let f = find_function env acc fty f in
  let argl = build_args acc argl in
  let ret, argl = 
    match fty with
    | Tfun (_, _, tyl) when List.length tyl > Global.max_reg_return ->
	let int = Type.type_prim env.ctx Llst.Tint in
	let tty = List.map (fun _ -> int) tyl in
	let ty = struct_type env.ctx (Array.of_list tty) in
	let st = build_alloca ty "" env.builder in
	Some st, st :: argl 
    | _ -> None, argl in
  let v = build_call f (Array.of_list argl) "" env.builder in
  let cconv = make_cconv fk in
  set_instruction_call_conv cconv v ;
  match xl with
  | [] -> acc
  | [_, x] -> IMap.add x v acc
  | _ -> 
      match ret with
      | None -> extract_values env acc xl v
      | Some v -> extract_struct env acc xl v

and extract_struct env acc xl st =
  let n = ref 0 in
  List.fold_left (
  fun acc (ty, x) ->
    let ptr = build_struct_gep st !n "" env.builder in 
    let nv = build_load ptr (Ident.to_string x) env.builder in
    incr n ;
    IMap.add x nv acc
 ) acc xl

and extract_values env acc xl v =
  let n = ref 0 in
  List.fold_left (
  fun acc (ty, x) -> 
    let nv = build_extractvalue v !n (Ident.to_string x) env.builder in
    incr n ;
    IMap.add x nv acc
 ) acc xl

and cast env xs ty1 ty2 y = 
  let ty1 = Type.type_ env.mds env.types env.ctx ty1 in
  let ty2 = Type.type_ env.mds env.types env.ctx ty2 in
  match classify_type ty1, classify_type ty2 with
  | TypeKind.Pointer, TypeKind.Pointer -> build_bitcast y ty1 xs env.builder
  | TypeKind.Pointer, _ -> build_inttoptr y ty1 "" env.builder
  | _, TypeKind.Pointer -> build_ptrtoint y ty1 "" env.builder
  | TypeKind.Integer, TypeKind.Integer ->
      build_intcast y ty1 xs env.builder
  | _, _ -> build_bitcast y ty1 xs env.builder

and expr bb env acc (ty, x) e =
  let xs = Ident.to_string x in
  match e with
  | Eswap _ -> assert false
  | Efree _ -> assert false
  | Eid (yty, y) -> 
      let y = try IMap.find y acc with Not_found -> find_function env acc ty y in
      let v = cast env xs ty yty y in
      IMap.add x v acc
  | Evalue v ->
      let ty = Type.type_ env.mds env.types env.ctx ty in
      let v = const env ty v in
      IMap.add x v acc
  | Ebinop (Ediff, (ty, x1), (_, x2)) -> 
      let x1 = IMap.find x1 acc in
      let x2 = IMap.find x2 acc in
      let ty = match ty with Tprim ty -> ty | _ -> assert false in
      let bop = binop ty Eeq in
      let v = bop x1 x2 "" env.builder in
      let v = build_not v xs env.builder in
      IMap.add x v acc      
  | Ebinop (bop, (ty, x1), (_, x2)) -> 
      let x1 = IMap.find x1 acc in
      let x2 = IMap.find x2 acc in
      let ty = match ty with Tprim ty -> ty | _ -> assert false in
      let bop = binop ty bop in
      let v = bop x1 x2 xs env.builder in
      IMap.add x v acc
  | Eapply _ -> assert false
  | Eis_null (_, v) -> 
      let v = IMap.find v acc in
      let v = build_is_null v xs env.builder in
      IMap.add x v acc
  | Eproj ((_, y), n) -> 
      let y = IMap.find y acc in
      let int = Type.type_prim env.ctx Llst.Tint in
      let z = const_int int 0 in
      let v = build_gep y [|z|] xs env.builder in
      let v = build_struct_gep v n xs env.builder in 
      let v = build_load v xs env.builder in
      IMap.add x v acc 
  | Etuple (v, fdl) -> 
      let bl = match v with
      | None ->
	  let orig_ty = 
	    match ty with Tid x -> 
	      IMap.find x env.orig_types 
	    | _ -> assert false 
	  in
	  let ty = Type.type_ env.mds env.types env.ctx ty in  
	  let oty = Type.type_ env.mds env.types env.ctx orig_ty in  
	  let v = size_of oty in
	  let malloc = IMap.find Naming.malloc env.prims in
	  let bl = build_call malloc [|v|] "" env.builder in
	  let bl = build_bitcast bl ty xs env.builder in 
	  bl
      | Some (_, v) -> IMap.find v acc in
      let int = Type.type_prim env.ctx Llst.Tint in
      let z = const_int int 0 in
      List.iter (
      fun (n, (_, v)) -> 
	let int = i32_type env.ctx in
	let n = const_int int n in
	let v = IMap.find v acc in
	let ptr = build_gep bl [|z;n|] "" env.builder in
	ignore (build_store v ptr env.builder)
     ) fdl ;
      IMap.add x bl acc      
  | Enull -> 
      let v = const_null (Type.type_ env.mds env.types env.ctx ty) in
      IMap.add x v acc
  | Eint_of_ptr v -> 
      let ty = Type.type_ env.mds env.types env.ctx ty in
      let v = IMap.find v acc in
      let v = build_ptrtoint v ty "" env.builder in
      IMap.add x v acc
  | Eptr_of_int v ->
      let ty = Type.type_ env.mds env.types env.ctx ty in
      let v = IMap.find v acc in
      let v = build_inttoptr v ty "" env.builder in
      IMap.add x v acc
  | Egettag (_, v) -> 
      let bl = IMap.find v acc in
      let int = Type.type_prim env.ctx Llst.Tint in
      let z = const_int int 0 in
      let ptr = build_gep bl [|z|] "" env.builder in
      let v = build_load ptr "" env.builder in
      IMap.add x v acc
  | Eget (t, i) ->
      let el_ty = Type.type_ env.mds env.types env.ctx ty in
      let t = IMap.find (snd t) acc in
      let i = IMap.find (snd i) acc in
      let tarray = pointer_type el_ty in
      let t = build_bitcast t tarray "" env.builder in
      let t = build_gep t [|i|] "" env.builder in
      let res = build_load t xs env.builder in
      IMap.add x res acc
  | Eset (t, i, (ty, v)) ->
      let el_ty = Type.type_ env.mds env.types env.ctx ty in
      let t = IMap.find (snd t) acc in
      let i = IMap.find (snd i) acc in
      let v = IMap.find v acc in
      let tarray = pointer_type el_ty in
      let t' = build_bitcast t tarray "" env.builder in
      let t' = build_gep t' [|i|] "" env.builder in
      let _ = build_store v t' env.builder in
      IMap.add x t acc
  | Efield (_, _) -> failwith "TODO Efield"
  | Euop (uop, (ty, y)) -> 
      let v = IMap.find y acc in
      let v = 
	match uop with
	| Euminus -> build_neg v "" env.builder
      in
      IMap.add x v acc
  | Epartial ((Tfun (k, tyl1, [rty]), f), el) -> (* TODO return list *)
      let cc = make_cconv k in
      let targs = List.map fst el in
      let tenv = Tstruct targs in
      let tenv = Type.type_ env.mds env.types env.ctx tenv in
      let cls_env = build_alloca tenv "" env.builder in
      let i = ref 0 in
      List.iter (
      fun (_, x) ->
	let x = IMap.find x acc in
	let ptr = build_struct_gep cls_env !i "" env.builder in 
	let _ = build_store x ptr env.builder in
	incr i
     ) el ;
      let link = Llvm.Linkage.Private in
      let tenv = pointer_type tenv in
      let cut_args = Utils.cut tyl1 (List.length el) in
      let cut_args = List.map (Type.type_ env.mds env.types env.ctx) cut_args in
      let rty = Type.type_ env.mds env.types env.ctx rty in
      let tyl1 = Array.of_list (tenv :: cut_args) in
      let ftype = function_type rty tyl1 in 
      let fdec = declare_function "anonymous" ftype env.cmd in
      set_linkage link fdec ;
      set_function_call_conv cc fdec ;
      let params = params fdec in
      add_param_attr params.(0) Attribute.Nest ;
      let bb = append_block env.ctx "" fdec in
      position_at_end bb env.builder ;
      let params = Array.to_list params in
      let st = List.hd params in
      let i = ref 0 in
      let vl = List.fold_right (
	fun ty acc ->
	  let ptr = build_struct_gep st !i "" env.builder in 
	  let res = build_load ptr "" env.builder in
	  incr i ;
	  res :: acc
       ) targs (List.tl params)
      in
      let f = IMap.find f acc in
      let v = build_call f (Array.of_list vl) "" env.builder in
      set_instruction_call_conv cc v ;
      ignore (build_ret v env.builder) ;
      let bb = IMap.find !(env.cblock) env.bls in
      position_at_end bb env.builder ;

      let tr = array_type (i8_type env.ctx) Global.tramp_size in
      let tr = build_alloca tr "" env.builder in
      (* ARRGH alignement HOWTO !!! TODO *)

      let int = Type.type_prim env.ctx Llst.Tint in
      let z = const_int int 0 in
      let tramp = build_gep tr [|z;z|] "" env.builder in
      let vstar = pointer_type (i8_type env.ctx) in
      let cls_env = build_bitcast cls_env vstar "" env.builder in
      let fdec = build_bitcast fdec vstar "" env.builder in
      let make_tr = IMap.find Pervasives.mk_trampoline env.prims in
      let res = build_call make_tr [|tramp ; fdec ; cls_env|] "" env.builder in
      let res_ty = pointer_type (function_type rty (Array.of_list cut_args)) in
      let res = build_bitcast res res_ty "" env.builder in
      IMap.add x res acc

  | Epartial _ -> failwith "TODO multiple return"

and binop ty = function
  | Eeq -> 
      (match ty with
      | Tfloat -> build_fcmp Llvm.Fcmp.Oeq
      | Tbool
      | Tchar
      | Tint -> build_icmp Llvm.Icmp.Eq
      | _ -> assert false)
  | Ediff -> assert false
  | Elt -> 
      (match ty with
      | Tbool | Tchar ->
	  build_icmp Llvm.Icmp.Ult 
      | Tint -> 
	  build_icmp Llvm.Icmp.Slt 
      | Tfloat ->
	  build_fcmp Llvm.Fcmp.Olt 
      | _ -> assert false
      )
  | Elte -> 
      (match ty with
      | Tbool | Tchar ->
	  build_icmp Llvm.Icmp.Ule
      | Tint -> 
	  build_icmp Llvm.Icmp.Sle
      | Tfloat ->
	  build_fcmp Llvm.Fcmp.Ole
      | _ -> assert false
      )
  | Egt -> 
      (match ty with
      | Tbool | Tchar ->
	  build_icmp Llvm.Icmp.Ugt 
      | Tint -> 
	  build_icmp Llvm.Icmp.Sgt 
      | Tfloat ->
	  build_fcmp Llvm.Fcmp.Ogt 
      | _ -> assert false
      )
  | Egte -> 
      (match ty with
      | Tbool | Tchar ->
	  build_icmp Llvm.Icmp.Uge
      | Tint -> 
	  build_icmp Llvm.Icmp.Sge
      | Tfloat ->
	  build_fcmp Llvm.Fcmp.Oge
      | _ -> assert false
      )
  | Eplus -> 
      (match ty with
      | Tint -> build_add
      | Tfloat -> build_fadd
      | _ -> assert false)
  | Eminus -> 
      (match ty with
      | Tint -> build_sub
      | Tfloat -> build_fsub
      | _ -> assert false)
  | Estar -> 
      (match ty with
      | Tint -> build_mul
      | Tfloat -> build_fmul
      | _ -> assert false)
  | Emod -> 
      (match ty with
      | Tint -> build_srem
      | Tfloat -> build_frem
      | _ -> assert false)
  | Ediv -> 
      (match ty with
      | Tint -> build_sdiv
      | Tfloat -> build_fdiv
      | _ -> assert false)
  | Eand -> build_and
  | Eor -> build_or

and const env ty = function
  | Eunit -> const_int_of_string ty "0" 10
  | Ebool true -> const_int (i1_type env.ctx) 1
  | Ebool false -> const_int (i1_type env.ctx) 0
  | Eint s -> 
      const_int_of_string ty s 10 (* TODO different radix *)
  | Eiint x ->
      let int = Type.type_prim env.ctx Llst.Tint in
      const_int int x 
  | Efloat s -> 
      const_float_of_string ty s
  | Estring s -> 
    let x = const_stringz env.ctx s in 
    let g = define_global "" x env.cmd in  
(*    set_global_constant true g ; *)
    set_linkage Linkage.Private g ;
    g
  | Echar c -> const_int_of_string ty c 10

