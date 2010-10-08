open Utils
open Ist

type env = unit
type acc = unit

let id env x = 
  try IMap.find x env
  with Not_found -> Eid x

let rec program p = 
  List.rev_map module_ p

and module_ md = 
  let env = IMap.empty in
  let acc = IMap.empty in
  let acc, defs = L.lfold def env acc md.md_defs in
  let md = { md with md_defs = defs } in
  md

and def env acc (x, p, e) = 
  let acc, p = pat env acc p in
  let acc, e = tuple env acc e in
  acc, (x, p, e)

and pat env acc ptl = 
  let acc, ptl = L.lfold pat_tuple env acc ptl in
  acc, ptl

and pat_tuple env acc pel = 
  let acc, pel = L.lfold pat_el env acc pel in
  acc, pel

and pat_el env acc (ty, p) = 
  let acc, p = pat_ env acc ty p in
  acc, (ty, p)

and pat_ env acc ty = function
  | Pany | Pid _ 
  | Pvalue _ as x -> acc, x
  | Pvariant (x, p) -> 
      let acc, p = pat env acc p in
      acc, Pvariant (x, p)
  | Precord pfl -> 
      let rid = Ident.tmp() in
      let rexpr = [ty], Eid rid in
      let acc = List.fold_left (pat_field rexpr) acc pfl in
      acc, Pid rid

and pat_field rid acc = function
  | PFany 
  | PFid _ 
  | PField (_, [[_, Pany]]) -> acc
  | PField (x, [l]) -> List.fold_left (make_field rid x) acc l
  | _ -> assert false

and make_field rid x acc p = 
  match p with
  | _, Pid y ->
      let v = Efield (rid, x) in
      IMap.add y v acc
  | _ -> assert false

and tuple env acc l = L.lfold expr env acc l
and expr env acc (ty, e) = 
  let acc, e = expr_ env acc e in
  acc, (ty, e)

and expr_ env acc = function
  | Eid x -> acc, id acc x
  | Evalue _ as e -> acc, e
  | Evariant (x, e) -> 
      let acc, e = tuple env acc e in
      acc, Evariant (x, e)
  | Ebinop (bop, e1, e2) -> 
      let acc, e1 = expr env acc e1 in
      let acc, e2 = expr env acc e2 in
      acc, Ebinop (bop, e1, e2)
  | Euop (uop, e) -> 
      let acc, e = expr env acc e in
      acc, Euop (uop, e)
  | Erecord fdl -> 
      let acc, fdl = L.lfold field env acc fdl in
      acc, Erecord fdl
  | Ewith (e, fdl) -> 
      let acc, fdl = L.lfold field env acc fdl in
      let acc, e = expr env acc e in
      acc, Ewith (e, fdl)
  | Efield (e, x) -> 
      let acc, e = expr env acc e in
      acc, Efield (e, x)
  | Ematch (e, al) -> 
      let acc, e = tuple env acc e in
      let acc, al = L.lfold action env acc al in
      acc, Ematch (e, al)
  | Elet (p, e1, e2) -> 
      let acc, p = pat env acc p in
      let acc, e1 = tuple env acc e1 in
      let acc, e2 = tuple env acc e2 in
      acc, Elet (p, e1, e2)
  | Eif (c, e1, e2) -> 
      let acc, c = expr env acc c in
      let acc, e1 = tuple env acc e1 in
      let acc, e2 = tuple env acc e2 in
      acc, Eif (c, e1, e2)
  | Eapply (x, e) -> 
      let acc, e = tuple env acc e in
      acc, Eapply (x, e)
  | Eseq (e1, e2) -> 
      let acc, e1 = expr env acc e1 in
      let acc, e2 = tuple env acc e2 in
      acc, Eseq (e1, e2)

and field env acc (x, e) = 
  let acc, e = tuple env acc e in
  acc, (x, e)

and action env acc (p, a) =
  let acc, p = pat env acc p in
  let acc, a = tuple env acc a in
  acc, (p, a)
