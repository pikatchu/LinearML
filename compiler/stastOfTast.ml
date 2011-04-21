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
open Tast


module Env = struct

  type t = {
      types: type_expr IMap.t ;
      records: ISet.t ;
    }

  let rec program types mdl =
    let recs = ISet.empty in
    let recs = List.fold_left module_ recs mdl in
    { types = types ; records = recs }

  and module_ t md =
    List.fold_left decl t md.md_decls

  and decl t = function
    | Neast.Drecord td -> ISet.add (snd td.Neast.td_id) t
    | _ -> t
end

let check_binop op ((p, _) as ty) =
  let ty =
    match ty with
    | p, Stast.Tprim Stast.Tstring -> Error.no_string p
    | _, Stast.Tapply (x, (_, [_, Stast.Tprim ty])) when snd x = Naming.tobs -> ty
    | _, Stast.Tprim ty -> ty
    | p, _ -> Error.expected_primty p in
  match op, ty with
  | Ast.Eeq, _
  | Ast.Ediff, _
  | Ast.Elt, _
  | Ast.Elte, _
  | Ast.Egt, _
  | Ast.Egte, _ -> ()
  | Ast.Eplus, (Stast.Tint | Stast.Tfloat) -> ()
  | Ast.Eminus, (Stast.Tint | Stast.Tfloat) -> ()
  | Ast.Estar, (Stast.Tint | Stast.Tfloat) -> ()
  | Ast.Ediv, (Stast.Tint | Stast.Tfloat) -> ()
  | Ast.Eor, (Stast.Tbool) -> ()
  | Ast.Eand, (Stast.Tbool) -> ()
  | _ -> Error.expected_numeric p

let check_bool (ty, _) =
  match ty with
  | _, Neast.Tprim Neast.Tbool -> ()
  | p, _ -> Error.expected_bool p

let rec program types mdl =
  let t = Env.program types mdl in
  List.map (module_ t) mdl

and module_ t md = {
  Stast.md_sig = md.md_sig ;
  Stast.md_id = md.md_id ;
  Stast.md_decls = List.fold_right (decl t) md.md_decls [] ;
  Stast.md_defs = List.map (def t) md.md_defs ;
}

and decl t d acc =
  match d with
  | Neast.Dabstract _ -> acc
  | Neast.Dalgebric td -> Stast.Dalgebric (tdef t td) :: acc
  | Neast.Drecord td -> Stast.Drecord (tdef t td) :: acc
  | Neast.Dval (ll, x, ty, v) -> Stast.Dval (ll, x, type_expr t ty, v) :: acc

and tdef t td = {
  Stast.td_id = td.Neast.td_id ;
  Stast.td_args = td.Neast.td_args ;
  Stast.td_map = IMap.map (id_type t) td.Neast.td_map ;
}

and id_type t (x, tyl) =
  let tyl = type_expr_list t tyl in
  x, tyl

and type_expr t (p, ty) = p, type_expr_ t ty
and type_expr_ t = function
    | Neast.Tany -> Stast.Tany
    | Neast.Tprim ty -> Stast.Tprim ty
    | Neast.Tvar ((_, x) as v) ->
	(try snd (type_expr t (IMap.find x t.Env.types))
	with Not_found -> Stast.Tvar v)
    | Neast.Tid x -> Stast.Tid x
    | Neast.Tapply (x, tyl) ->
	let tyl = type_expr_list t tyl in
	Stast.Tapply (x, tyl)
    | Neast.Tfun (k, tyl1, tyl2) ->
	Stast.Tfun (k, type_expr_list t tyl1, type_expr_list t tyl2)

and type_expr_list t (p, tyl) = p, List.map (type_expr t) tyl

and def t (k, x, p, e) =
  let e = tuple t e in
  k, x, pat t p, e

and pat t (tyl, ptl) = type_expr_list t tyl, List.map (pat_tuple t) ptl
and pat_tuple t (tyl, pel) = type_expr_list t tyl, List.map (pat_el t) pel
and pat_el t (ty, p) = type_expr t ty, pat_ t p
and pat_ t = function
  | Pany -> Stast.Pany
  | Pid x -> Stast.Pid x
  | Pvalue v -> Stast.Pvalue v
  | Pvariant (x, p) -> Stast.Pvariant (x, pat t p)
  | Precord pfl -> Stast.Precord (List.map (pat_field t) pfl)
  | Pas (x, p) -> Stast.Pas (x, pat t p)

and pat_field t (p, pa) = p, pat_field_ t pa
and pat_field_ t = function
  | PFany -> Stast.PFany
  | PFid x -> Stast.PFid x
  | PField (x, p) -> Stast.PField (x, pat t p)

and tuple t (tyl, tpl) = type_expr_list t tyl, List.map (tuple_pos t) tpl
and tuple_pos t (tyl, e) =
  let tyl = type_expr_list t tyl in
  tyl, expr_ t tyl e
and expr t (ty, e) =
  let ty = type_expr t ty in
  ty, expr_ t (fst ty, [ty]) e

and expr_ t ty = function
  | Eid x -> Stast.Eid x
  | Evalue v -> Stast.Evalue v
  | Evariant (id, e) ->
      let e = tuple t e in
      Stast.Evariant (id, e)
  | Ebinop (bop, e1, e2) ->
      let e1 = expr t e1 in
      let e2 = expr t e2 in
      check_binop bop (fst e1) ;
      Stast.Ebinop (bop, e1, e2)
  | Euop (uop, e) -> Stast.Euop (uop, expr t e)
  | Erecord (itl) -> Stast.Erecord (List.map (id_tuple t) itl)
  | Ewith (e, itl) ->
      let e = expr t e in
      Stast.Ewith (e, List.map (id_tuple t) itl)
  | Efield (e, x) -> Stast.Efield (expr t e, x)
  | Ematch (e, pal) -> Stast.Ematch (tuple t e, List.map (action t) pal)
  | Elet (p, e1, e2) ->
      let e1 = tuple t e1 in
      let e2 = tuple t e2 in
      Stast.Elet (pat t p, e1, e2)
  | Eif (e1, e2, e3) ->
      check_bool e1 ;
      let e2 = tuple t e2 in
      let e3 = tuple t e3 in
      Stast.Eif (expr t e1, e2, e3)
  | Eapply (fk, fty, x, e) ->
      let fty = type_expr t fty in
      let e = tuple t e in
      Stast.Eapply (fk, fty, x, e)
  | Eseq (e1, e2) ->
      let e2 = tuple t e2 in
      Stast.Eseq (expr t e1, e2)
  | Eobs x -> Stast.Eobs x
  | Efree (ty, x) ->
      let ty' = type_expr t ty in
      (match snd ty' with
      | Stast.Tapply ((_, x), _)
      | Stast.Tid (_, x) when ISet.mem x t.Env.records -> ()
      | _ -> Error.cannot_free (fst ty) (Typing.Print.type_expr t.Env.types ty)) ;
      Stast.Efree (ty', x)
  | Epartial (f, e) ->
      let f = expr t f in
      let e = tuple t e in
      Stast.Epartial (f, e)
  | Efun (k, obs, idl, e) ->
      let idl = List.map (pat_el t) idl in
      let e = tuple t e in
      Stast.Efun (k, obs, idl, e)

and id_tuple t (x, e) =
  let e = tuple t e in
  x, e

and action t (p, a) =
  let e = tuple t a in
  pat t p, e
