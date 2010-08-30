open Utils
open Ast
open Stast

type ty = bound * ISet.t

and bound = 
  | Checked
  | Unchecked

module Debug = struct

  let print (b, s) = 
    (match b with
    | Checked -> o "ok, "
    | Unchecked -> o "ko, ") ;
    ISet.iter (fun x -> o (Ident.debug x) ; o " ") s ;
    o "\n"

end

type t = ty IMap.t

let rec program mdl = 
  List.iter module_ mdl 

and module_ md = 
  let t = IMap.empty in
  let _ = List.fold_left def t md.md_defs in
  ()

and def t (_, _, e) = 
  tuple t e
  
and tuple t (_, tpl) = List.fold_left tuple_pos t tpl
and tuple_pos t ((p, _), e) = expr_ t p e
and expr t ((p, _), e) = expr_ t p e
and expr_ t p = function
  | Eid _ -> t
  | Evalue _ -> t
  | Evariant (x, e) -> tuple t e
  | Ebinop (_, e1, e2) -> 
      let t = expr t e1 in
      let t = expr t e2 in
      t
  | Euop (_, e) -> expr t e
  | Erecord fdl -> fields t fdl 
  | Ewith (e, fdl) -> 
      let t = expr t e in
      let t = fields t fdl in
      t
  | Efield (e, _) -> expr t e
  | Ematch (e, al) -> 
      let t = tuple t e in
      let _ = actions e t al in
      t
  | Elet (_, e1, e2) -> 
      let _ = tuple t e1 in
      let t = tuple t e2 in
      t
  | Eif ((_, Ebinop (bop, se1, se2)), e1, e2) ->
      let lr = 
	match bop, snd se1, snd se2 with
	| Elt, Eid (_, x), Eapply ((_, f), (_, [_, Eid (_, y)]))
	| (Egt | Egte), Eapply ((_, f), (_, [_, Eid (_, y)])), Eid (_, x) 
	  when f = Naming.length -> `L (x, `UB y)
	| (Egt | Egte), Eid (_, x), Eapply ((_, f), (_, [_, Eid (_, y)]))
	| Elt, Eapply ((_, f), (_, [_, Eid (_, y)])), Eid (_, x) 
	  when f = Naming.length -> `R (x, `UB y)
	| (Elt | Elte), Eid (_, x), Evalue (Eint (_, "0")) 
	| Egt, Evalue (Eint (_, "0")), Eid (_, x) -> `R (x, `LB)
	| Egt, Eid (_, x), Evalue (Eint (_, "0")) 
	| (Elt | Elte), Evalue (Eint (_, "0")), Eid (_, x) -> `L (x, `LB)
	| _ -> `N in
      let ty = 
	match lr with
	| `L (x, _) | `R (x, _) ->
	    (try IMap.find x t with Not_found -> (Unchecked, ISet.empty))
	| _ -> Unchecked, ISet.empty in
      let t1, t2 = t, t in
      let t1, t2 = match lr with
      | `L (x, `LB) -> IMap.add x (Checked, snd ty) t1, t2
      | `L (x, `UB y) -> IMap.add x (fst ty, ISet.add y (snd ty)) t1, t2
      | `R (x, `LB) -> t1, IMap.add x (Checked, snd ty) t2
      | `R (x, `UB y) -> t1, IMap.add x (fst ty, ISet.add y (snd ty)) t2 
      | `N -> t1, t2 in
      let _ = tuple t1 e1 in
      let _ = tuple t2 e2 in
      t
  | Eif (e1, e2, e3) ->
      let t = expr t e1 in
      let _ = tuple t e2 in
      let _ = tuple t e3 in
      t
  | Eapply ((_, f), (_, [_, Eid (_, y) ; _, Eid (_, x)])) when f = Naming.get ->
      (try match IMap.find x t with
      | Checked, s -> 
	  if ISet.mem y s 
	  then t
	  else (Error.pos p ; failwith "upper bound unchecked")
      | Unchecked, _ -> failwith "Lower bound unchecked"
      with Not_found -> failwith "Unchecked")
  | Eapply (_, e) -> 
      let t = tuple t e in
      t
  | Eseq (e1, e2) -> 
      let t = expr t e1 in
      let t = tuple t e2  in
      t
  | Eobs _ -> t

and fields t l = List.fold_left field t l
and field t (_, e) = tuple t e

and actions el t l = List.fold_left (action el) t l
and action el t (p, e) = 
  let _ = tuple t e in
  t
