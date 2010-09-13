open Utils
open Est

let id t x = try IMap.find x t with Not_found -> x

let rec def t df = {
  Est.df_id = id t df.df_id ;
  Est.df_args = ty_idl t df.df_args;
  Est.df_return = ty_idl t df.df_return ;
  Est.df_body = List.map (block t) df.df_body ;
}

and ty_id t (ty, x) = ty, id t x
and ty_idl t l = List.map (ty_id t) l

and block t bl = {
  Est.bl_id = bl.bl_id ;
  Est.bl_phi = [] ;
  Est.bl_eqs = List.map (equation t) bl.bl_eqs ;
  Est.bl_ret = ty_idl t bl.bl_ret ;
}

and equation t eq = 
  match eq with
  | Eq (idl, e) ->
      Eq (ty_idl t idl, expr t e)
  | _ -> assert false

and expr t = function
  | Eid x -> Eid (id t x)
  | Evalue _ as e -> e
  | Evariant (x, idl) -> Evariant (x, ty_idl t idl)
  | Ebinop (bop, x1, x2) -> Ebinop (bop, ty_id t x1, ty_id t x2)
  | Euop (uop, x) -> Euop (uop, ty_id t x) 
  | Erecord fdl -> Erecord (fields t fdl) 
  | Ewith (x, fdl) -> Ewith (ty_id t x, fields t fdl) 
  | Efield (x, y) -> Efield (ty_id t x, y) 
  | Ematch (l, al) -> Ematch (ty_idl t l, actions t al) 
  | Ecall _ as e -> e
  | Eapply (x, l) -> Eapply (id t x, ty_idl t l)
  | Eseq (x, xl) -> Eseq (ty_id t x, ty_idl t xl)
  | Eif (x1, l1, l2) -> Eif (ty_id t x1, l1, l2)

and fields t l = List.map (field t) l
and field t (fd, e) = fd, ty_idl t e

and actions t l = List.map (action t) l
and action t (p, e) = p, expr t e
