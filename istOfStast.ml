open Utils
open Stast

let id (_, x) = x
let pstring (_, x) = x

let rec program mdl = 
  List.rev_map module_ mdl

and module_ md = {
    Ist.md_id = id md.md_id ;
    Ist.md_decls = List.map decl md.md_decls ;
    Ist.md_defs = List.map def md.md_defs ;
  }

and decl = function
  | Dalgebric x -> Ist.Dalgebric (tdef x)
  | Drecord x -> Ist.Drecord (tdef x)
  | Dval (x, y, v) -> Ist.Dval (id x, type_expr y, opt pstring v)

and tdef td = {
    Ist.td_id = id td.td_id ;
    Ist.td_args = List.map id td.td_args ;
    Ist.td_map = IMap.map tfield td.td_map ;
  }

and tfield (x, tyl) = id x, type_expr_list tyl

and type_expr (_, ty) = 
  match ty with
  | Tany -> Ist.Tany
  | Tprim x -> Ist.Tprim x
  | Tvar x -> Ist.Tvar (id  x)
  | Tid x -> Ist.Tid (id x)
  (* Special case *)
(*  | Tapply ((_, x), (_, [ty])) when x = Naming.toption -> type_expr ty *)
  | Tapply (x, tyl) -> Ist.Tapply (id x, type_expr_list tyl)
  | Tfun (k, tyl1, tyl2) -> 
      let tyl1 = type_expr_list tyl1 in
      let tyl2 = type_expr_list tyl2 in
      Ist.Tfun (k, tyl1, tyl2)

and type_expr_list (_, tyl) = List.map type_expr tyl

and def (k, x, p, e) = k, id x, pat p, tuple e

and pat (_, ptl) = List.map pat_tuple ptl 
and pat_tuple (_, pel) = List.map pat_el pel 
and pat_el (ty, p) = type_expr ty, pat_ p
and pat_ = function
  | Pany -> Ist.Pany 
  | Pid x -> Ist.Pid (id x)
  | Pvalue x -> Ist.Pvalue (value x)
  | Pvariant (x, p) -> Ist.Pvariant (id x, pat p)
  | Precord x -> Ist.Precord (List.map pat_field x)
  | Pas (x, p) -> Ist.Pas (id x, pat p)

and pat_field (_, pf) = 
  match pf with
  | PFany -> Ist.PFany
  | PFid x -> Ist.PFid (id x) 
  | PField (x, p) -> Ist.PField (id x, pat p)

and tuple (_, tpl) = List.map tuple_pos tpl
and tuple_pos (tyl, e) = type_expr_list tyl, expr_ e
and expr (ty, e) = [type_expr ty], expr_ e

and expr_ = function
  | Eid x -> Ist.Eid (id x)
  | Evalue x -> Ist.Evalue (value x)
  | Evariant (x, e) -> Ist.Evariant (id x, tuple e)
  | Ebinop (x, e1, e2) -> Ist.Ebinop (x, expr e1, expr e2)
  | Euop (x, e) -> Ist.Euop (x, expr e)
  | Erecord fdl -> Ist.Erecord (List.map field fdl)
  | Ewith (e, fdl) -> Ist.Ewith (expr e, List.map field fdl)
  | Efield (e, x) -> Ist.Efield (expr e, id x)
  | Ematch (e, al) -> Ist.Ematch (tuple e, List.map action al)
  | Elet (p, e1, e2) -> Ist.Elet (pat p, tuple e1, tuple e2)
  | Eif (e1, e2, e3) -> Ist.Eif (expr e1, tuple e2, tuple e3)
  | Eapply (fk, fty, x, e) -> Ist.Eapply (fk, type_expr fty, id x, tuple e)
  | Eseq (e1, e2) -> Ist.Eseq (expr e1, tuple e2)
  | Eobs x -> Ist.Eid (id x)
  | Efree (ty, x) -> Ist.Efree (type_expr ty, id x)

and field (x, e) = id x, tuple e
and action (p, e) = pat p, tuple e

and value = function
  | Eunit -> Ist.Eunit
  | Ebool x -> Ist.Ebool x
  | Eint x -> Ist.Eint (pstring x)
  | Efloat x -> Ist.Efloat (pstring x)
  | Echar x -> Ist.Echar (pstring x)
  | Estring x -> Ist.Estring (pstring x)

