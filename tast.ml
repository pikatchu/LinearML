open Utils

type id = Nast.id
type pstring = Nast.pstring

type program = module_ list

and module_ = {
    md_id: id ;
    md_decls: Neast.decl list ;
    md_defs: def list ;
  }

and type_expr = Neast.type_expr
and type_expr_list = Neast.type_expr_list

and def = id * pat * tuple

and pat = type_expr_list * pat_tuple list
and pat_tuple = type_expr_list * pat_el list
and pat_el = type_expr * pat_
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

and tuple = type_expr_list * tuple_pos list
and tuple_pos = type_expr_list * expr_
and expr = type_expr * expr_
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

and value = Nast.value

module FreeVars = struct

  let rec pat s (_, ptl) = List.fold_left pat_tuple s ptl 
  and pat_tuple s (_, pl) = List.fold_left pat_el s pl
  and pat_el s (_, p) = pat_ s p
  and pat_ s = function
    | Pvalue _ 
    | Pany -> s
    | Pid (_, x) -> ISet.add x s 
    | Pvariant (_, p) -> pat s p 
    | Precord pfl -> List.fold_left pat_field s pfl 
    | Pas ((_, x), p) -> 
	let s = ISet.add x s in
	pat s p

  and pat_field s (_, pf) = pat_field_ s pf
  and pat_field_ s = function
    | PFany -> s
    | PFid (_, x) -> ISet.add x s
    | PField (_, p) -> pat s p

  let pat p = pat ISet.empty p

end

module Rename = struct

  let ident t x = 
    try IMap.find x t 
    with Not_found -> x

  let id t (p, x) = 
    p, ident t x
	
  let rec module_ t md = 
    let defs = List.map (def t) md.md_defs in
    { md with md_defs = defs }
      
  and def t (x, pa, e) = id t x, pat t pa, tuple t e

  and type_expr t (p, ty) = (p, type_expr_ t ty)
  and type_expr_ t = function
    | Neast.Tany -> Neast.Tany
    | Neast.Tprim x -> Neast.Tprim x
    | Neast.Tvar x -> Neast.Tvar x
    | Neast.Tid x -> Neast.Tid x
    | Neast.Tapply (x, tyl) -> Neast.Tapply (x, type_expr_list t tyl)
    | Neast.Tfun (tyl1, tyl2) -> 
	Neast.Tfun (type_expr_list t tyl1, type_expr_list t tyl2)

  and type_expr_list t (p, tyl) = p, List.map (type_expr t) tyl

  and pat t (tyl, ptl) = type_expr_list t tyl, List.map (pat_tuple t) ptl
  and pat_tuple t (tyl, pel) = type_expr_list t tyl, List.map (pat_el t) pel 
  and pat_el t (ty, p) = type_expr t ty, pat_ t p 
  and pat_ t = function
  | Pvalue _
  | Pany as x -> x
  | Pid x -> Pid (id t x) 
  | Pvariant (x, p) -> Pvariant (x, pat t p)
  | Precord pfl -> Precord (List.map (pat_field t) pfl) 
  | Pas (x, p) -> Pas (id t x, pat t p)

  and pat_field t (p, pf) = p, pat_field_ t pf
  and pat_field_ t = function
    | PFany -> PFany
    | PFid x -> PFid (id t x)
    | PField (x, p) -> PField (x, pat t p)
      
  and tuple t (tyl, tpl) = type_expr_list t tyl, List.map (tuple_pos t) tpl
  and tuple_pos t (tyl, e) = type_expr_list t tyl, expr_ t e
  and expr t (ty, e) = type_expr t ty, expr_ t e
  and expr_ t = function
    | Eid x -> Eid (id t x)
    | Evalue _ as v -> v
    | Evariant (x, e) -> Evariant (x, tuple t e)
    | Ebinop (bop, e1, e2) -> Ebinop (bop, expr t e1, expr t e2)
    | Euop (uop, e1) -> Euop (uop, expr t e1)
    | Erecord fdl -> Erecord (List.map (field t) fdl)
    | Ewith (e, fdl) -> Ewith (expr t e, List.map (field t) fdl)
    | Efield (e, x) -> Efield (expr t e, x) 
    | Ematch (e, al) -> Ematch (tuple t e, List.map (action t) al)
    | Elet (p, e1, e2) -> Elet (p, tuple t e1, tuple t e2)
    | Eif (e1, e2, e3) -> Eif (expr t e1, tuple t e2, tuple t e3)
    | Eapply (x, e) -> Eapply (id t x, tuple t e)
    | Eseq (e1, e2) -> Eseq (expr t e1, tuple t e2)
    | Eobs x -> Eobs (id t x)
	  
  and field t (x, e) = x, tuple t e
  and action t (p, e) = p, tuple t e

end

module DeadCode = struct

  type t = {
      defs: tuple IMap.t ;
      used: ISet.t ;
    }

  let rec module_ md =
    let defs = List.fold_left add_def IMap.empty md.md_defs in
    let t = { defs = defs ; used = ISet.empty } in
    let t = List.fold_left decl t md.md_decls in
    { md with md_defs = List.filter (used_def t.used) md.md_defs }

  and add_def t ((_, x), _, e) = 
    IMap.add x e t

  and add_decl acc = function
    | Neast.Dval ((_, x), _, _) -> ISet.add x acc
    |  _ -> acc

  and decl t = function
    | Neast.Dval ((_, x), _, _) -> def t x
    |  _ -> t

  and def t x =
    if ISet.mem x t.used
    then t
    else if IMap.mem x t.defs
    then
      let t = { t with used = ISet.add x t.used } in
      let e = IMap.find x t.defs in
      tuple t e
    else t

  and used_def used ((_, x), _, _) = 
    ISet.mem x used

  and tuple acc (_, tpl) = List.fold_left tuple_pos acc tpl 
  and tuple_pos acc (_, e) = expr_ acc e
  and expr acc (_, e) = expr_ acc e
  and expr_ acc = function
  | Eobs (_, x)
  | Eid (_, x) -> 
      if IMap.mem x acc.defs
      then def acc x
      else { acc with used = ISet.add x acc.used }
  | Evalue _ -> acc
  | Evariant (_, e) -> tuple acc e
  | Ebinop (_, e1, e2) -> 
      let acc = expr acc e1 in
      let acc = expr acc e2 in
      acc
  | Euop (_, e) -> expr acc e 
  | Erecord fdl -> fields acc fdl 
  | Ewith (e, fdl) ->
      let acc = expr acc e in
      fields acc fdl
  | Efield (e, _) -> expr acc e
  | Ematch (e, al) -> 
      let acc = tuple acc e in
      actions acc al
  | Elet (_, e1, e2) -> 
      let acc = tuple acc e1 in
      let acc = tuple acc e2 in
      acc
  | Eif (e1, e2, e3) -> 
      let acc = expr acc e1 in
      let acc = tuple acc e2 in
      let acc = tuple acc e3 in
      acc
  | Eapply ((_, x), e) -> 
      let t = tuple acc e in
      def t x
  | Eseq (e1, e2) -> 
      let acc = expr acc e1 in
      let acc = tuple acc e2 in
      acc

  and fields acc fdl = List.fold_left field acc fdl
  and field acc (_, e) = tuple acc e

  and actions acc al = List.fold_left action acc al
  and action acc (_, e) = tuple acc e
end

module Fresh = struct

  let new_id = Ident.fresh

  let id t (p, x) = 
    p, try IMap.find x t with Not_found -> x

  let rec def ((p, x), pa, e) = 
    let y = new_id x in
    let t = IMap.add x y IMap.empty in
    let t = fresh_pat t pa in
    let pa = pat t pa in
    let e = tuple t e in
    (p, y), pa, e

  and fresh_pat t pa = 
    let fv = FreeVars.pat pa in
    let t = ISet.fold (fun x acc -> IMap.add x (new_id x) acc) fv t in
    t

  and pat t (tyl, ptl) = tyl, List.map (pat_tuple t) ptl
  and pat_tuple t (tyl, pel) = tyl, List.map (pat_el t) pel 
  and pat_el t (ty, p) = ty, pat_ t p 
  and pat_ t = function
  | Pvalue _
  | Pany as x -> x
  | Pid x -> Pid (id t x) 
  | Pvariant (x, p) -> Pvariant (x, pat t p)
  | Precord pfl -> Precord (List.map (pat_field t) pfl) 
  | Pas (x, p) -> Pas (id t x, pat t p)

  and pat_field t (p, pf) = p, pat_field_ t pf
  and pat_field_ t = function
    | PFany -> PFany
    | PFid x -> PFid (id t x)
    | PField (x, p) -> PField (x, pat t p)

  and tuple t (tyl, tpl) = tyl, List.map (tuple_pos t) tpl 
  and tuple_pos t (tyl, e) = tyl, expr_ t e
  and expr t (ty, e) = ty, expr_ t e
  and expr_ t = function
  | Eid x -> Eid (id t x)
  | Evalue _ as v -> v
  | Evariant (x, e) -> Evariant (x, tuple t e)
  | Ebinop (bop, e1, e2) -> Ebinop (bop, expr t e1, expr t e2) 
  | Euop (uop, e) -> Euop (uop, expr t e)
  | Erecord fdl -> Erecord (List.map (field t) fdl)
  | Ewith (e, fdl) -> Ewith (expr t e, List.map (field t) fdl)
  | Efield (e, x) -> Efield (expr t e, x) 
  | Ematch (e, pal) -> 
      let e = tuple t e in
      Ematch (e, List.map (action t) pal)

  | Elet (p, e1, e2) -> 
      let t = fresh_pat t p in
      let p = pat t p in
      Elet (p, tuple t e1, tuple t e2) 

  | Eif (e1, e2, e3) -> Eif (expr t e1, tuple t e2, tuple t e3)
  | Eapply (x, e) -> Eapply (id t x, tuple t e) 
  | Eseq (e1, e2) -> Eseq (expr t e1, tuple t e2) 
  | Eobs x -> Eobs (id t x)

  and field t (x, e) = x, tuple t e
      
  and action t (p, e) =
    let t = fresh_pat t p in
    let p = pat t p in
    p, tuple t e

end
