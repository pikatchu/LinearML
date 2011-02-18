open Utils
open Stast

let id (_, x) = x
let pstring (_, x) = x

let rec program bounds mdl = 
  List.rev_map (module_ bounds) mdl

and module_ bounds md = {
    Ist.md_id = id md.md_id ;
    Ist.md_decls = List.map decl md.md_decls ;
    Ist.md_defs = List.map (def bounds) md.md_defs ;
  }

and decl = function
  | Dalgebric x -> Ist.Dalgebric (tdef x)
  | Drecord x -> Ist.Drecord (tdef x)
  | Dval (ll, x, y, v) -> Ist.Dval (ll, id x, type_expr y, v)

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
  | Tapply (x, tyl) -> Ist.Tapply (id x, type_expr_list tyl)
  | Tfun (k, tyl1, tyl2) -> 
      let tyl1 = type_expr_list tyl1 in
      let tyl2 = type_expr_list tyl2 in
      Ist.Tfun (k, tyl1, tyl2)

and type_expr_list (_, tyl) = List.map type_expr tyl

and def bounds (k, x, p, e) = k, id x, pat p, tuple bounds e

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

and tuple bds (_, tpl) = List.map (tuple_pos bds) tpl
and tuple_pos bds (tyl, e) = type_expr_list tyl, expr_ bds (fst tyl) e
and expr bds (ty, e) = [type_expr ty], expr_ bds (fst ty) e

and expr_ bds p = function
  | Eid x -> Ist.Eid (id x)
  | Evalue x -> Ist.Evalue (value x)
  | Evariant (x, e) -> Ist.Evariant (id x, (tuple bds e))
  | Ebinop (x, e1, e2) -> Ist.Ebinop (x, expr bds e1, expr bds e2)
  | Euop (x, e) -> Ist.Euop (x, expr bds e)
  | Erecord fdl -> Ist.Erecord (List.map (field bds) fdl)
  | Ewith (e, fdl) -> Ist.Ewith (expr bds e, List.map (field bds) fdl)
  | Efield (e, x) -> Ist.Efield (expr bds e, id x)
  | Ematch (e, al) -> Ist.Ematch ((tuple bds e), List.map (action bds) al)
  | Elet (p, e1, e2) -> Ist.Elet (pat p, (tuple bds e1), (tuple bds e2))
  | Eif (e1, e2, e3) -> Ist.Eif (expr bds e1, (tuple bds e2), (tuple bds e3))
  | Eapply (fk, fty, x, e) -> 
      let e = (tuple bds e) in
      let fid = snd x in
      if fid = Naming.aset 
      then aset bds p e
      else if fid = Naming.aget 
      then aget bds p e
      else if fid = Naming.aswap 
      then aswap bds p e
      else Ist.Eapply (fk, type_expr fty, id x, e)
  | Eseq (e1, e2) -> Ist.Eseq (expr bds e1, (tuple bds e2))
  | Eobs x -> Ist.Eid (id x)
  | Efree (ty, x) -> Ist.Efree (type_expr ty, id x)
  | Epartial (f, e) -> Ist.Epartial (expr bds f, tuple bds e)
  | Efun (k, pl, e) -> 
      let pl = List.map pat_el pl in
      let e = tuple bds e in
      Ist.Efun (k, pl, e)

and field bds (x, e) = id x, (tuple bds e)
and action bds (p, e) = pat p, (tuple bds e)

and if_low i v1 v2 =
  let z = [Ist.Tprim Tint], Ist.Evalue (Ist.Eint "0") in
  let b = [Ist.Tprim Tbool], Ist.Ebinop (Ast.Elt, i, z) in
  let ty = List.flatten (List.map fst v2) in
  ty, Ist.Eif (b, v2, v1)
    
and if_up i x v1 v2 =
  let b = [Ist.Tprim Tbool], Ist.Ebinop (Ast.Elt, i, x) in
  let ty = List.flatten (List.map fst v1) in
  ty, Ist.Eif (b, v1, v2)

and length t = 
  let link = Ast.Lfun in
  let fty = Ist.Tfun (link, fst t, [Ist.Tprim Tint]) in
  [Ist.Tprim Tint], Ist.Eapply (link, fty, Naming.alength, [t])

and default ty =
  [ty], match ty with
  | Ist.Tprim ty ->
      let d = match ty with
      | Tunit -> Ist.Eunit
      | Tbool -> Ist.Ebool false
      | Tchar -> Ist.Echar "\000"
      | Tint -> Ist.Eint "0"
      | Tfloat -> Ist.Efloat "0.0"
      | Tstring -> Ist.Estring "" in
      Ist.Evalue d
  | _ -> assert false

and aset bds p = function
  | [t ; i ; v] -> 
      let low, up = get_bounds p bds in
      let ty = fst t in
      let e = ty, Ist.Eset (t, i, v) in
      let e = if low then if_low i [e] [t] else e in
      let e = if up then if_up i (length t) [e] [t] else e in
      snd e
  | _ -> assert false

and aget bds p = function
  | [t ; i] -> 
      let low, up = get_bounds p bds in
      let ty = match fst t with
      | [Ist.Tapply (_, [Ist.Tapply (_, [ty])])] -> ty
      | _ -> assert false in
      let e = [ty], Ist.Eget (t, i) in
      let e = if low then if_low i [e] [default ty] else e in
      let e = if up then if_up i (length t) [e] [default ty] else e in
      snd e
  | _ -> assert false

and aswap bds p = function
  | [t ; i ; v] -> 
      let low, up = get_bounds p bds in
      let ty = List.flatten (List.map fst [t;v]) in
      let e = ty, Ist.Eswap (t, i, v) in
      let e = if low then if_low i [e] [t; v] else e in
      let e = if up then if_up i (length t) [e] [t; v] else e in
      snd e
  | _ -> assert false

and get_bounds p bds =
  try BoundCheck.PMap.find p bds 
  with Not_found -> false, false

and value = function
  | Eunit -> Ist.Eunit
  | Ebool x -> Ist.Ebool x
  | Eint x -> Ist.Eint (pstring x)
  | Efloat x -> Ist.Efloat (pstring x)
  | Echar x -> Ist.Echar (pstring x)
  | Estring x -> Ist.Estring (pstring x)

