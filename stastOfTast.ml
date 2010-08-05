open Utils
open Tast

type t = type_expr IMap.t

module Env = struct

  let rec module_ md = 
    List.fold_left def IMap.empty md.md_defs

  and def t ((p, x), (tyl1, _), (tyl2, _)) = 
    IMap.add x (p, Neast.Tfun (tyl1, tyl2)) t
end

let rec program mdl = 
  List.map module_ mdl 

and module_ md = 
  let t = Env.module_ md in {
    Stast.md_id = md.md_id ;
    Stast.md_decls = List.map (decl t) md.md_decls ;
    Stast.md_defs = List.map (def t) md.md_defs ;
  }

and decl t = function
  | Neast.Dalgebric td -> Stast.Dalgebric (tdef t td)
  | Neast.Drecord td -> Stast.Drecord (tdef t td)
  | Neast.Dval (x, ty) -> Stast.Dval (x, type_expr t ty) 

and tdef t td = {
  Stast.td_id = td.Neast.td_id ;
  Stast.td_args = td.Neast.td_args ;
  Stast.td_map = IMap.map (id_type t) td.Neast.td_map ;
}

and id_type t (x, tyl) = x, type_expr_list t tyl

and type_expr t (p, ty) = p, type_expr_ t ty
and type_expr_ t = function
    | Neast.Tany -> Stast.Tany
    | Neast.Tundef -> assert false (* That's the only interesting part *)
    | Neast.Tdef x -> local_def t x 
    | Neast.Tprim ty -> Stast.Tprim ty
    | Neast.Tvar x -> Stast.Tvar x
    | Neast.Tid x -> Stast.Tid x
    | Neast.Tapply (x, tyl) -> Stast.Tapply (x, type_expr_list t tyl)
    | Neast.Tfun (tyl1, tyl2) -> 
	Stast.Tfun (type_expr_list t tyl1, type_expr_list t tyl2)

and local_def t x =
  let l = IMap.fold (fun x _ acc -> x :: acc) x [] in
  match l with
  | [] -> assert false 
  | x :: _ -> 
      (* This could probably be memoized ... not sure it is worth it *)
      type_expr_ t (snd (IMap.find x t))

and type_expr_list t (p, tyl) = p, List.map (type_expr t) tyl

and def t (x, p, e) = x, pat t p, tuple t e

and pat t (tyl, ptl) = type_expr_list t tyl, List.map (pat_tuple t) ptl
and pat_tuple t (tyl, pel) = type_expr_list t tyl, List.map (pat_el t) pel
and pat_el t (ty, p) = type_expr t ty, pat_ t p
and pat_ t = function
  | Pany -> Stast.Pany
  | Pid x -> Stast.Pid x
  | Pvalue v -> Stast.Pvalue v
  | Pvariant (x, p) -> Stast.Pvariant (x, pat t p)
  | Precord pfl -> Stast.Precord (List.map (pat_field t) pfl)

and pat_field t (p, pa) = p, pat_field_ t pa
and pat_field_ t = function
  | PFany -> Stast.PFany
  | PFid x -> Stast.PFid x
  | PField (x, p) -> Stast.PField (x, pat t p)

and tuple t (tyl, tpl) = type_expr_list t tyl, List.map (tuple_pos t) tpl
and tuple_pos t (tyl, e) = type_expr_list t tyl, expr_ t e
and expr t (ty, e) = type_expr t ty,  expr_ t e
and expr_ t = function
  | Eid x -> Stast.Eid x
  | Evalue v -> Stast.Evalue v
  | Evariant (id, e) -> Stast.Evariant (id, tuple t e)
  | Ebinop (bop, e1, e2) -> Stast.Ebinop (bop, expr t e1, expr t e2)
  | Euop (uop, e) -> Stast.Euop (uop, expr t e)
  | Erecord (itl) -> Stast.Erecord (List.map (id_tuple t) itl)
  | Efield (e, x) -> Stast.Efield (expr t e, x)
  | Ematch (e, pal) -> Stast.Ematch (tuple t e, List.map (action t) pal)
  | Elet (p, e1, e2) -> Stast.Elet (pat t p, tuple t e1, tuple t e2)
  | Eif (e1, e2, e3) -> Stast.Eif (expr t e1, tuple t e2, tuple t e3)
  | Eapply (x, e) -> Stast.Eapply (x, tuple t e)

and id_tuple t (x, e) = x, tuple t e
and action t (p, a) = pat t p, tuple t a
