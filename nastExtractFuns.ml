open Utils
open Nast

let rec program mdl = 
  List.map module_ mdl

and module_ md = 
  { md with md_defs = List.fold_right def md.md_defs [] }

and def (id, pl, e) acc = 
  let acc, e = expr acc e in
  (id, pl, e) :: acc
  
and expr acc (p, e) = 
  let acc, e = expr_ p acc e in
  acc, (p, e)

and expr_ p acc = function
  | Ebinop (bop, e1, e2) -> 
      let acc, e1 = expr acc e1 in
      let acc, e2 = expr acc e2 in
      acc, Ebinop (bop, e1, e2)

  | Euop (uop, e) -> 
      let acc, e = expr acc e in
      acc, Euop (uop, e)

  | Etuple el -> 
      let acc, el = lfold expr acc el in
      acc, Etuple el

  | Erecord fdl -> 
      let acc, fdl = lfold field acc fdl in
      acc, Erecord fdl

  | Ewith (e, fdl) ->
      let acc, e = expr acc e in
      let acc, fdl = lfold field acc fdl in
      acc, Ewith (e, fdl)

  | Efield (e, x) -> 
      let acc, e = expr acc e in
      acc, Efield (e, x)

  | Ematch (e, pel) -> 
      let acc, e = expr acc e in
      let acc, pel = lfold pat_expr acc pel in
      acc, Ematch (e, pel)

  | Elet (p, e1, e2) -> 
      let acc, e1 = expr acc e1 in
      let acc, e2 = expr acc e2 in
      acc, Elet (p, e1, e2)

  | Eif (e1, e2, e3) -> 
      let acc, e1 = expr acc e1 in
      let acc, e2 = expr acc e2 in
      let acc, e3 = expr acc e3 in
      acc, Eif (e1, e2, e3)

  | Efun (pl, e) -> 
      let acc, e = expr acc e in
      let x = Ident.make "anonymous" in
      let id = p, x in
      (id, pl, e) :: acc, Eid id

  | Eapply (e, el) -> 
      let acc, e = expr acc e in
      let acc, el = lfold expr acc el in
      acc, Eapply (e, el)

  | Eseq (e1, e2) -> 
      let acc, e1 = expr acc e1 in
      let acc, e2 = expr acc e2 in
      acc, Eseq (e1, e2)

  | Eobs _
  | Ecstr _ 
  | Evalue _ | Eid _ as e -> acc, e

and field acc (id, e) = 
  let acc, e = expr acc e in
  acc, (id, e)

and pat_expr acc (p, e) = 
  let acc, e = expr acc e in
  acc, (p, e)
