open Utils
open Est


let rec id t x = try id t (IMap.find x t) with Not_found -> x

let rec def t df = 
  { Est.df_id = id t df.df_id ;
    Est.df_kind = df.df_kind ;
    Est.df_args = ty_idl t df.df_args;
    Est.df_return = ty_idl t df.df_return ;
    Est.df_body = List.map (block t) df.df_body ;
  }

and ty_id t (ty, x) = ty, id t x
and ty_idl t l = List.map (ty_id t) l

and block t bl = {
  Est.bl_id = bl.bl_id ;
  Est.bl_phi = List.map (phi t) bl.bl_phi ;
  Est.bl_eqs = List.map (equation t) bl.bl_eqs ;
  Est.bl_ret = ret t bl.bl_ret ;
}

and phi t (x, ty, l) = id t x, ty, List.map (fun (x, y) -> id t x, y) l

and ret t = function
  | Lreturn l -> Lreturn (ty_idl t l)
  | Return (b, l) -> Return (b, ty_idl t l)
  | Jump x -> Jump x
  | If (c, l1, l2) -> If (ty_id t c, l1, l2)
  | Match (cl, al) -> Match (ty_idl t cl, al)

and equation t (idl, e) = ty_idl t idl, expr t e

and expr t = function
  | Enull -> Enull
  | Eid x -> Eid (ty_id t x)
  | Evalue _ as e -> e
  | Evariant (x, idl) -> Evariant (x, ty_idl t idl)
  | Ebinop (bop, x1, x2) -> Ebinop (bop, ty_id t x1, ty_id t x2)
  | Euop (uop, x) -> Euop (uop, ty_id t x) 
  | Erecord fdl -> Erecord (fields t fdl) 
  | Ewith (x, fdl) -> Ewith (ty_id t x, fields t fdl) 
  | Efield (x, y) -> Efield (ty_id t x, y) 
  | Ematch (l, al) -> Ematch (ty_idl t l, actions t al) 
  | Ecall _ as e -> e
  | Eapply (fk, x, l) -> Eapply (fk, ty_id t x, ty_idl t l)
  | Eseq (x, xl) -> Eseq (ty_id t x, ty_idl t xl)
  | Eif (x1, l1, l2) -> Eif (ty_id t x1, l1, l2)
  | Eis_null x -> Eis_null (ty_id t x)
  | Efree x -> Efree (ty_id t x)
  | Eget (a, i) -> Eget (ty_id t a, ty_id t i)
  | Eset (a, i, v) -> Eset (ty_id t a, ty_id t i, ty_id t v)
  | Eswap (a, i, v) -> Eswap (ty_id t a, ty_id t i, ty_id t v)

and fields t l = List.map (field t) l
and field t (fd, e) = fd, ty_idl t e

and actions t l = List.map (action t) l
and action t (p, e) = pat t p, expr t e

and pat t pel = List.map (pat_el t) pel
and pat_el t (ty, p) = ty, pat_ t p
and pat_ t = function
  | Pany -> Pany
  | Pid x -> Pid (id t x) 
  | Pvariant (x, p) -> Pvariant (x, pat t p)
  | Precord (x, pfl) -> 
      let x = match x with None -> None | Some x -> Some (id t x) in
      let pfl = List.map (pfield t) pfl in
      Precord (x, pfl)
  | Pas (x, pel) -> Pas (id t x, pat_el t pel)

and pfield t (x, p) = x, pat t p
