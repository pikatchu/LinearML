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

let fresh x = Ident.make (Ident.to_string x)

type id = Nast.id
type pstring = Nast.pstring

type program = module_ list

and module_ = {
    md_sig: bool ;
    md_id: id ;
    md_decls: decl list ;
    md_defs: def list ;
  }

and decl = 
  | Dalgebric of tdef
  | Drecord of tdef
  | Dabstract of id * id list
  | Dval of Ast.link * id * type_expr * Ast.extern_def

and tdef = {
    td_id: id ;
    td_args: id list ;
    td_map:  (id * type_expr_list) IMap.t
  }

and type_expr = Pos.t * type_expr_
and type_expr_ = 
  | Tany
  | Tprim of type_prim
  | Tvar of id
  | Tid of id
  | Tapply of id * type_expr_list
  | Tfun of Ast.fun_kind * type_expr_list * type_expr_list

and type_expr_list = Pos.t * type_expr list

and type_prim = Nast.type_prim =   
  | Tunit
  | Tbool
  | Tchar
  | Tint
  | Tfloat
  | Tstring

and def = id * pat * tuple

and tpat = pat_el * type_expr

and pat = Pos.t * pat_tuple list
and pat_tuple = Pos.t * pat_el list
and pat_el = Pos.t * pat_
and pat_ = 
  | Pany 
  | Pid of id
  | Pvalue of value
  | Pvariant of id * pat
  | Precord of pat_field list
  | Pas of id * pat

and pat_field = Pos.t * pat_field_
and pat_field_ = 
  | PFany
  | PFid of id 
  | PField of id * pat

and expr = Pos.t * expr_
and expr_ = 
  | Eid of id
  | Evalue of value
  | Evariant of id * tuple
  | Ebinop of Ast.bop * expr * expr
  | Euop of Ast.uop * expr
  | Erecord of (id * tuple) list 
  | Ewith of expr * (id * tuple) list 
  | Efield of expr * id 
  | Ematch of tuple * (pat * tuple) list
  | Elet of pat * tuple * tuple
  | Eif of expr * tuple * tuple
  | Eapply of id * tuple
  | Eseq of expr * tuple
  | Eobs of id
  | Efree of id
  | Epartial of expr * tuple
  | Ecall of expr * tuple
  | Efun of Ast.fun_kind * bool * tpat list * tuple

and tuple = Pos.t * expr list

and value = Nast.value

module TVars = struct

  let rec type_expr env t (_, ty) = type_expr_ env t ty

  and type_expr_ env t = function
    | Tany
    | Tprim _ 
    | Tid _ -> t
    | Tvar (_, x) -> 
	(try type_expr env t (IMap.find x env)
	with Not_found -> ISet.add x t)
    | Tapply (_, tyl) -> 
	type_expr_list env t tyl
    | Tfun (_, tyl1, tyl2) -> 
	let t = type_expr_list env t tyl1 in
	let t = type_expr_list env t tyl2 in
	t

  and type_expr_list env t (_, tyl) = 
    List.fold_left (type_expr env) t tyl

end

module Subst = struct

  let rec type_expr env t (p, ty) = 
    p, type_expr_ env t ty

  and type_expr_ env t = function
    | Tany
    | Tprim _ 
    | Tid _ as x -> x
    | Tvar (p, x) -> 
	(try snd (type_expr env t (IMap.find x env))
	with Not_found -> 
	  Tvar (p, IMap.find x t)
	)
    | Tapply (x, tyl) -> Tapply (x, type_expr_list env t tyl)
    | Tfun (k, tyl1, tyl2) -> 
	let tyl1 = type_expr_list env t tyl1 in
	let tyl2 = type_expr_list env t tyl2 in
	Tfun (k, tyl1, tyl2)

  and type_expr_list env t (p, tyl) = 
    p, List.map (type_expr env t) tyl

  let make_name x acc =
    let name = fresh x in
    IMap.add x name acc

end

module Instantiate = struct

  let type_expr env ty = 
    let tvars = TVars.type_expr env ISet.empty ty in
    let instv = ISet.fold Subst.make_name tvars IMap.empty in
    Subst.type_expr env instv ty

  let type_expr_list env tyl = 
    let tvars = TVars.type_expr_list env ISet.empty tyl in
    let instv = ISet.fold Subst.make_name tvars IMap.empty in
    Subst.type_expr_list env instv tyl
end

module ExpandType = struct

  let rec id env ty x =
    try type_expr env (IMap.find x env)
    with Not_found -> ty

  and type_expr env ((p, ty_) as ty) = 
    match ty_ with
    | Tvar (_, x) -> id env ty x 
    | Tapply (x, tyl) -> 
	p, Tapply (x, type_expr_list env tyl)
    | Tfun (fk, tyl1, tyl2) -> 
	p, Tfun (fk, type_expr_list env tyl1, type_expr_list env tyl2)
    | _ -> ty

  and type_expr_list env (p, tyl) = 
    p, List.map (type_expr env) tyl

end


module SubType = struct

  let rec type_expr (p1, ty1) (p2, ty2) = 
    match ty1, ty2 with
    | Tvar _, Tany 
    | Tany, Tvar _ -> ()
    | Tvar _, Tvar _ -> ()
    | Tvar _, _ -> Error.too_general p1 p2
    | Tapply (_, tyl1), Tapply (_, tyl2) ->
	type_expr_list tyl1 tyl2
    | Tfun (_, tyl1, tyl2), Tfun (_, tyl3, tyl4) -> 
	type_expr_list tyl1 tyl3 ;
	type_expr_list tyl2 tyl4 
    | _ -> ()

  and type_expr_list (_, tyl1) (_, tyl2) = 
    List.iter2 type_expr tyl1 tyl2

end
