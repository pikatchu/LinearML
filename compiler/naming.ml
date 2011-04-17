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
open Ast

let prim_types = ref SMap.empty
let prim_type s = 
  let id = Ident.make s in
  prim_types := SMap.add s id !prim_types ;
  id

let prim_values = ref SMap.empty
let prim_value s = 
  let id = Ident.make s in
  prim_values := SMap.add s id !prim_values ;
  id

let prim_cstrs = ref SMap.empty
let prim_cstr s = 
  let id = Ident.make s in
  prim_cstrs := SMap.add s id !prim_cstrs ;
  id

let prim_arrays = ref SMap.empty
let prim_array s = 
  let id = Ident.make s in
  prim_arrays := SMap.add s id !prim_arrays ;
  id

let int 	= prim_type "int"
let bool	= prim_type "bool"
let float	= prim_type "float"
let string      = prim_type "string"
let tobs        = prim_type "obs"
let toption     = prim_type "option"
let array       = prim_type "array"

let malloc      = prim_value "malloc"
let ifree       = prim_value "free"
let vassert     = prim_value "assert"
let eunit       = prim_value "()"
let call        = prim_value "call"
let bnot        = prim_value "not"

let alength     = prim_array "length"
let amake       = prim_array "init"
let imake       = prim_array "imake"
let fmake       = prim_array "fmake"
let aget        = prim_array "get"
let aset        = prim_array "set"
let aswap       = prim_array "swap"

let some        = prim_cstr "Some"
let none        = prim_cstr "None"

let prim_types  = !prim_types
let prim_values = !prim_values
let prim_cstrs  = !prim_cstrs
let prim_arrays = !prim_arrays

module Env:sig

  type t

  val empty: t

  val value: t -> Ast.id -> Nast.id
  val try_value: t -> Ast.id -> Nast.id option
  val field: t -> Ast.id -> Nast.id
  val type_: t -> Ast.id -> Nast.id
  val tvar: t -> Ast.id -> Nast.id
  val cstr: t -> Ast.id -> Nast.id

  val new_value: t -> Ast.id -> t * Nast.id
  val new_decl: t -> Ast.id -> t * Nast.id
  val new_field: t -> Ast.id -> t * Nast.id
  val new_type: t -> Ast.id -> t * Nast.id
  val new_tvar: t -> Ast.id -> t * Nast.id
  val new_cstr: t -> Ast.id -> t * Nast.id

  val add_type: t -> Ast.id -> Nast.id -> t
  val add_value: t -> Ast.id -> Nast.id -> t

  val has_value: t -> Ast.id -> bool

  val alias: t -> Ast.id -> Ast.id -> t

  val pattern_env: t -> t
  val add_env: t -> t -> t
  val check_penv: Pos.t -> t -> t -> unit

  val fresh_tvars: t -> t

  val print_values: t -> unit

end = struct

  type t = {
      values: Ident.t SMap.t ;
      fields: Ident.t SMap.t ;
      types: Ident.t SMap.t ;
      tvars: Ident.t SMap.t ;
      cstrs: Ident.t SMap.t ;
    }

  let empty = {
    values = prim_values ;
    fields = SMap.empty ;
    types = prim_types ;
    tvars = SMap.empty ;
    cstrs = prim_cstrs ;
  }

  let pattern_env t = { t with values = prim_values }
  let add_env t1 t2 = 
    { t1 with values = map_add t1.values t2.values }

  let check_penv p t1 t2 = 
    SMap.iter (fun x _ ->
      if SMap.mem x t2.values
      then ()
      else Error.both_side_pattern p x) t1.values ;
    SMap.iter (fun x _ ->
      if SMap.mem x t1.values
      then ()
      else Error.both_side_pattern p x) t2.values

  let new_id t env (p, x) = 
    let id = Ident.make x in
    if SMap.mem x env
    then Error.multiple_def p x ;
    let env = SMap.add x id env in
    t, env, (p, id)

  let new_value t (p, x) = 
    let id = Ident.make x in
    let values = SMap.add x id t.values in
    { t with values = values }, (p, id) 

  let new_decl t x = 
    let env = t.values in
    let t, env, id = new_id t env x in
    { t with values = env }, id
      
  let new_field t x = 
    let env = t.fields in
    let t, env, id = new_id t env x in
    { t with fields = env }, id

  let new_type t x = 
    let env = t.types in
    let t, env, id = new_id t env x in
    { t with types = env }, id

  let new_tvar t (p, x) = 
    let env = t.tvars in
    let id = Ident.make x in
    let env = SMap.add x id env in
    { t with tvars = env }, (p, id)

  let new_cstr t x = 
    let env = t.cstrs in
    let t, env, id = new_id t env x in
    { t with cstrs = env }, id

  let value t (p, x) =
    try p, SMap.find x t.values
    with Not_found -> Error.unbound_name p x

  let try_value t (p, x) = 
    try Some (p, SMap.find x t.values)
    with Not_found -> None

  let field t (p, x) =
    try p, SMap.find x t.fields
    with Not_found -> Error.unbound_name p x

  let type_ t (p, x) =
    try p, SMap.find x t.types
    with Not_found -> Error.unbound_name p x

  let tvar t (p, x) =
    try p, SMap.find x t.tvars
    with Not_found -> Error.unbound_name p x

  let cstr t (p, x) =
    try p, SMap.find x t.cstrs
    with Not_found -> Error.unbound_name p x

  let add_type t (_, x) (_, id) =
    { t with types = SMap.add x id t.types }

  let add_value t (_, x) (_, id) = 
    { t with values = SMap.add x id t.values }

  let has_value t (_, x) = SMap.mem x t.values

  let alias t x y = 
    let id = value t y in
    add_value t x id

  let fresh_tvars t = { t with tvars = SMap.empty }

  let print_values penv = 
    SMap.iter (fun x _ -> o x ; o " ") penv.values ;
    o "\n"
end

module Genv: sig

  type t

  val garray: Ident.t
  val make: Ast.program -> t
  val module_id: t -> Ast.id -> Nast.id
  val sig_: t -> Nast.id -> Env.t
  val alias: t -> Ast.id -> Ast.id -> t

end = struct
    
  type t = { 
      sigs: Env.t IMap.t ;
      module_ids: Ident.t SMap.t ;
    }

  let empty = {
    sigs = IMap.empty ;
    module_ids = SMap.empty ;
  }

  let garray = Ident.make "Array"

  let sig_ t (_, id) = 
    IMap.find id t.sigs

  let module_id t (p, x) =
    try p, SMap.find x t.module_ids
    with Not_found -> Error.unbound_name p x

  let new_module t (_, x) = 
    let id = if x = "Array" then garray else Ident.make x in
    Ident.set_name id x ;
    let t = { t with module_ids = SMap.add x id t.module_ids } in
    t, id

  let alias t id1 id2 =
    let id2 = module_id t id2 in
    let t, id1 = new_module t id1 in
    let sig_ = sig_ t id2 in
    { t with sigs = IMap.add id1 sig_ t.sigs }

  let rec make mdl = 
    List.fold_left module_decl empty mdl

  and module_decl t md =
    let t, md_id = new_module t md.md_id in
    let env = List.fold_left (decl md_id) Env.empty md.md_defs in
    { t with sigs = IMap.add md_id env t.sigs }

  and decl md_id env = function
    | Dtype (Public, [(id, _)]) when md_id = garray && snd id = "t" ->
	let x = fst id, array in
	Env.add_type env id x
    | Dval (Public, id, _, _) ->
	let env, x = 
	  if md_id = garray
	  then 
	    try 
	      let x = fst id, SMap.find (snd id) prim_arrays in
	      Env.add_value env id x, x
	    with Not_found -> Env.new_decl env id
	  else Env.new_decl env id  
	in 
	Ident.expand_name md_id (snd x) ;
	env
    | Dtype (Public | Abstract as ll, tdef_l) -> 
	List.fold_left (tdef md_id ll) env tdef_l
    | _ -> env

  and tdef md_id ll env (id, (_, ty)) = 
    let env, x = Env.new_type env id in
    Ident.expand_name md_id (snd x) ;
    match ll with
    | Abstract -> env
    | Public -> type_ md_id env ty
    | _ -> assert false

  and type_ md_id env = function
    | Tabs (_, (_, ty)) -> type_ md_id env ty
    | Talgebric vtl -> List.fold_left (variant md_id) env vtl 
    | Trecord fdl -> List.fold_left (field md_id) env fdl
    | _ -> env

  and variant md_id env (id, _) = 
    let env, x = Env.new_cstr env id in
    Ident.expand_name md_id (snd x) ;
    env

  and field md_id env (id, _) = 
    let env, x = Env.new_field env id in
    Ident.expand_name md_id (snd x) ;
    env

end

module FreeVars = struct
  open Ast

  let rec type_expr acc (_, ty) = type_expr_ acc ty
  and type_expr_ acc = function
    | Tany
    | Tid _ 
    | Tabstract
    | Tpath _ -> acc
    | Tvar ((_,v) as x) when not (SMap.mem v acc) -> 
	(* The mem is not necessary but makes the first occurence *)
	(* of the variable as the reference which is nicer        *)
	SMap.add v x acc

    | Tvar _ -> acc
    | Tapply (ty, tyl) -> 
	let acc = type_expr acc ty in
	List.fold_left type_expr acc tyl

    | Ttuple tyl -> List.fold_left type_expr acc tyl
    | Tfun (_, ty1, ty2) -> type_expr (type_expr acc ty1) ty2
    | Tabbrev ty -> type_expr acc ty
    | Talgebric _ 
    | Trecord _ 
    | Tabs _ -> assert false

  let type_expr ty = 
    let vm = type_expr SMap.empty ty in
    SMap.fold (fun _ y acc -> y :: acc) vm []
end

let rec program root mdl = 
  let genv = Genv.make mdl in
  let root_id = 
    try Some (Genv.module_id genv (Pos.none, root))
    with Not_found -> None in
  root_id, List.map (module_ genv) mdl

and module_ genv md = 
  let md_id = Genv.module_id genv md.md_id in
  let env = Genv.sig_ genv md_id in
  let acc = (genv, env, []) in
  let _, env, decls = List.fold_left decl acc md.md_defs in
  let decls = List.rev decls in
  let env = List.fold_left external_ env md.md_defs in
  let env = List.fold_left def_name env md.md_defs in
  let acc = genv, env, [] in
  let _, env, defs = List.fold_left def acc md.md_defs in
  let defs = List.rev defs in
  { Nast.md_sig = md.md_sig ;
    Nast.md_id = md_id ;
    Nast.md_decls = decls ;
    Nast.md_defs = defs ;
  }

and decl (genv, env, acc) = function
  | Dmodule (id1, id2) -> Genv.alias genv id1 id2, env, acc
  | Dtype (ll, tdl) -> 
      let env, ty = dtype genv env ll tdl in
      let ty = Nast.Dtype ty in
      genv, env, ty :: acc
  | Dval (ll, x, y, z) -> 
      let env, (x, y, z) = dval genv env ll x y z in
      let dval = Nast.Dval (ll, x, y, z) in
      genv, env, dval :: acc
  | _ -> genv, env, acc

and dval genv env ll id ((p, ty_) as ty) def = 
  match ty_ with 
  | Tfun (_, _, _) ->
      let env, id = link env id ll in
      let env = Env.fresh_tvars env in
      let tvarl = FreeVars.type_expr ty in
      let env, tvarl = lfold Env.new_tvar env tvarl in
      let env, ty = type_expr genv ll env ty in
      (* The declaration of the type variables is implicit *)
      let ty = match tvarl with [] -> ty | l -> p, Nast.Tabs(tvarl, ty) in
      env, (id, ty, def)  
  | _ -> Error.value_function p

and link env id = function
  | Ast.Abstract -> assert false 
  | Ast.Private -> Env.new_decl env id
  | Ast.Public -> env, Env.value env id

and dtype genv env ll tdl = 
  let env = List.fold_left (bind_type ll) env tdl in
  lfold (type_def genv ll) env tdl

and external_ env = function
  | Dval (_, x, _, (Ext_C _ | Ext_Asm _)) -> Env.add_value env x (Env.value env x)
  | _ -> env

and bind_type ll env (x, _) = 
  let env, id = 
    match ll with
    | Public | Abstract -> env, Env.type_ env x 
    | Private -> Env.new_type env x 
  in
  Env.add_type env x id

and type_def genv ll env (id, ty) = 
  let id = Env.type_ env id in
  let env, ty = type_expr genv ll env ty in
  env, (id, ty)

and type_expr genv ll env (p, ty) = 
  let env, ty = type_expr_ genv env ll ty in
  env, (p, ty)

and type_expr_ genv env ll x = 
  let k = type_expr genv ll in
  match x with
  | Tany -> env, Nast.Tany
  | Tvar x -> env, Nast.Tvar (Env.tvar env x)
  | Tid x -> env, tid env x
  | Tapply (ty, tyl) -> 
      let env, tyl = lfold k env tyl in
      let env, ty = k env ty in
      env, Nast.Tapply (ty, tyl)
  | Ttuple tyl -> 
      let env, tyl = lfold k env tyl in
      env, Nast.Ttuple tyl
  | Tpath (id1, id2) -> 
      let (p1, _) as md_id = Genv.module_id genv id1 in
      let sig_ = Genv.sig_ genv md_id in
      let (p2, v) = Env.type_ sig_ id2 in
      let id2 = Pos.btw p1 p2, v in
      env, Nast.Tpath (md_id, id2)
  | Tfun (fkind, ty1, ty2) -> 
      let env, ty1 = k env ty1 in
      let env, ty2 = k env ty2 in
      env, Nast.Tfun (fkind, ty1, ty2)
  | Talgebric l -> 
      let env, vl = lfold (tvariant genv ll) env l in
      env, Nast.Talgebric (imap_of_list vl)
  | Trecord l -> 
      let env, fdl = lfold (tfield genv ll) env l in
      env, Nast.Trecord (imap_of_list fdl)
  | Tabbrev ty -> 
      let env, ty = k env ty in
      env, Nast.Tabbrev ty
  | Tabstract -> env, Nast.Tabstract
  | Tabs (tvarl, ty) -> 
      let env, tvarl = lfold Env.new_tvar env tvarl in
      let env, ty = type_expr genv ll env ty in
      env, Nast.Tabs (tvarl, ty)

and tid env (p, x) = tid_ env p x
and tid_ env p = function
  | "unit" -> Nast.Tprim Nast.Tunit
  | "bool" -> Nast.Tprim Nast.Tbool
  | "int" -> Nast.Tprim Nast.Tint
  | "float" -> Nast.Tprim Nast.Tfloat
  | "char" -> Nast.Tprim Nast.Tchar
  | "string" -> Nast.Tprim Nast.Tstring
  | x -> Nast.Tid (Env.type_ env (p, x))

and tvariant genv ll env (id, ty) = 
  let env, ty = 
    match ty with 
    | None -> env, None
    | Some ty -> 
	let env, ty = type_expr genv ll env ty in
	env, Some ty 
  in
  let env, id = 
    match ll with
    | Public -> env, Env.cstr env id
    | _ -> Env.new_cstr env id 
  in
  env, (id, ty)

and tfield genv ll env (id, ty) = 
  let env, id = 
    match ll with
    | Public -> env, Env.field env id
    | Private | Abstract -> Env.new_field env id
  in
  let env, ty = type_expr genv ll env ty in
  env, (id, ty) 

and def_name env = function
  | Dlet ((p, _) as x, pl, e) -> 
      (match Env.try_value env x with
      | None -> Error.type_missing p 
      | Some id -> Env.add_value env x id)
  | _ -> env

and def (genv, env, acc) = function
  | Dmodule (id1, id2) -> Genv.alias genv id1 id2, env, acc
  | Dlet (id, pl, e) -> 
      let sub_env, pl = lfold (pat genv) env pl in
      let e = expr genv sub_env e in
      let id = Env.value env id in
      genv, env, (id, pl, e) :: acc
  | Dtype _
  | Dval _ -> genv, env, acc

and dlet genv env acc (id, pl, e) = 
  let id = Env.value env id in
  let env, pl = lfold (pat genv) env pl in
  let e = expr genv env e in
  (id, pl, e) :: acc

and pat genv env (pos, p) = 
  let env, p = pat_ genv env pos p in
  env, (pos, p)

and pat_ genv env pos = function
  | Punit -> env, Nast.Pvalue Nast.Eunit
  | Pany -> env, Nast.Pany
  | Pid x -> 
      let env, x = Env.new_value env x in
      env, Nast.Pid x
  | Pchar x -> env, Nast.Pvalue (Nast.Echar x)
  | Pint x -> env, Nast.Pvalue (Nast.Eint x)
  | Pbool b -> env, Nast.Pvalue (Nast.Ebool b)
  | Pfloat f -> env, Nast.Pvalue (Nast.Efloat f)
  | Pstring s -> env, Nast.Pvalue (Nast.Estring s)
  | Pcstr id -> env, Nast.Pcstr (Env.cstr env id)
  | Pvariant (id, p) -> 
      let env, p = pat genv env p in
      env, Nast.Pvariant (Env.cstr env id, p)
  | Precord fl -> 
      let env, fl = lfold (pat_field genv) env fl in
      let fid = List.filter (
	function _, Nast.PField _ -> false | _ -> true
       ) fl in
      (match fid with
      | [] -> Error.missing_record_name pos
      | [_] -> ()
      | (p1, _) :: (p2, _) :: _ -> Error.multiple_record_name p1 p2) ;
      env, Nast.Precord fl
  | Pbar (p1, p2) ->  (* TODO this is bad *)
      let penv = Env.pattern_env env in
      let penv1, p1 = pat genv penv p1 in
      let penv2, p2 = pat genv penv1 p2 in
      Env.check_penv pos penv1 penv2 ;
      env, Nast.Pbar (p1, p2)
  | Ptuple pl -> 
      let env, pl = lfold (pat genv) env pl in
      env, Nast.Ptuple pl
  | Pevariant (id1, id2, arg) -> 
      let md_id = Genv.module_id genv id1 in
      let md_sig = Genv.sig_ genv md_id in
      let id2 = Env.cstr md_sig id2 in
      let env, arg = pat genv env arg in
      env, Nast.Pevariant (md_id, id2, arg)
  | Pecstr (md_id, id) -> 
      let md_id = Genv.module_id genv md_id in
      let md_sig = Genv.sig_ genv md_id in
      let id = Env.cstr md_sig id in
      env, Nast.Pecstr (md_id, id)
  | Pas (x, p) -> 
      let env, p = pat genv env p in
      let env, x = Env.new_value env x in
      env, Nast.Pas (x, p)
      
and pat_field genv env (p, pf) = 
  let env, pf = pat_field_ genv env pf in
  env, (p, pf)

and pat_field_ genv env = function
  | PFany -> env, Nast.PFany
  | PFid x -> 
      let env, x = Env.new_value env x in
      env, Nast.PFid x
  | PField (id, p) -> 
      let env, p = pat genv env p in
      env, Nast.PField (Env.field env id, p)

and tpat_list genv env idl =
  let env = Env.fresh_tvars env in
  let tyl = List.map snd idl in
  let tvarl = List.map FreeVars.type_expr tyl in
  let tvarl = List.flatten tvarl in
  let env, tvarl = lfold Env.new_tvar env tvarl in
  lfold (tpat genv) env idl

and tpat genv env (x, ty) =
  let env, x = pat genv env x in
  let ll = Ast.Private in
  let env, ty = type_expr genv ll env ty in
  env, (x, ty)

and expr genv env (p, e) = p, expr_ genv env p e
and expr_ genv env p e = 
  let k = expr genv env in
  match e with
  | Eunit -> Nast.Evalue Nast.Eunit
  | Ebool x -> Nast.Evalue (Nast.Ebool x)
  | Eint x -> Nast.Evalue (Nast.Eint x)
  | Efloat x -> Nast.Evalue (Nast.Efloat x)
  | Echar x -> Nast.Evalue (Nast.Echar x)
  | Estring x -> Nast.Evalue (Nast.Estring x)
  | Eid (p, "free") -> Error.free_not_value p
  | Eid (p, "partial") -> Error.partial_not_value p
  | Eid (p, "call") -> Error.call_not_value p
  | Eid x -> Nast.Eid (Env.value env x)
  | Ebinop (bop, e1, e2) -> Nast.Ebinop (bop, k e1, k e2)
  | Euop (uop, e) -> Nast.Euop (uop, k e)
  | Etuple el -> Nast.Etuple (List.map k el)
  | Ecstr x -> Nast.Ecstr (Env.cstr env x)
  | Ematch (e, pel) -> 
      let pel = List.map (pat_expr genv env) pel in
      Nast.Ematch (k e, pel) 
  | Elet (p, e1, e2) -> 
      let env, p = pat genv env p in
      let e2 = expr genv env e2 in
      Nast.Elet (p, k e1, e2)
  | Eif (e1, e2, e3) -> Nast.Eif (k e1, k e2, k e3) 
  | Efun (fk, obs, idl, e) -> 
      let env, idl = tpat_list genv env idl in
      let e = expr genv env e in
      Nast.Efun (fk, obs, idl, e)
  | Eapply ((_, Eid (_, "free")), e) ->
      (match e with
      | [_, Eid y] -> Nast.Efree (Env.value env y)
      | (p, _) :: _ -> Error.free_expects_id p
      | _ -> assert false)
  | Eapply ((_, Eid (_, "partial")), el) ->
      Nast.Epartial (List.map k el)
  | Eapply (e, el) -> Nast.Eapply (k e, List.map k el)
  | Erecord fdl -> Nast.Erecord (List.map (field genv env) fdl)
  | Efield (e, v) -> Nast.Efield (k e, Env.field env v)
  | Eextern (md_id, id2) -> 
      let md_id = Genv.module_id genv md_id in
      let sig_md = Genv.sig_ genv md_id in
      let id2 = 
	if snd md_id = Genv.garray 
	then 
	  (try p, SMap.find (snd id2) prim_arrays
	  with Not_found -> Env.value sig_md id2)
	else Env.value sig_md id2 in
      Nast.Eid id2
  | Eefield (e, id1, id2) -> 
      let id1 = Genv.module_id genv id1 in
      let sig_ = Genv.sig_ genv id1 in
      let id2 = Env.field sig_ id2 in
      Nast.Efield (k e, id2)
  | Eecstr (md_id, id) ->
      let md_id = Genv.module_id genv md_id in
      let sig_md = Genv.sig_ genv md_id in
      let id = Env.cstr sig_md id in      
      Nast.Ecstr id
  | Ewith (e, fdl) -> 
      let e = expr genv env e in
      Nast.Ewith (e, List.map (field genv env) fdl)
  | Eseq (e1, e2) -> 
      let e1 = expr genv env e1 in
      let e2 = expr genv env e2 in
      Nast.Eseq (e1, e2)
  | Eobs y -> Nast.Eobs (Env.value env y)

and field genv env = function
  | Eflocl (id, e) -> 
      Env.field env id, expr genv env e
  | Efextr (md_id, id, e) -> 
      let md_id = Genv.module_id genv md_id in
      let sig_md = Genv.sig_ genv md_id in
      let id = Env.field sig_md id in      
      id, expr genv env e

and pat_expr genv env (p, e) = 
  let env, p = pat genv env p in
  p, expr genv env e
