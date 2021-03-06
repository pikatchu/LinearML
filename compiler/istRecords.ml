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
open Ist

let alias subst e = 
  IMap.fold (
  fun x ((ty, _) as y) acc ->
    let rty = fst (List.hd acc) in
    [rty, Elet ([[List.hd ty, Pid x]], [y], acc)]
 ) subst e


let rec program p = 
  List.rev_map module_ p

and module_ md = 
  let defs = List.map def md.md_defs in
  let md = { md with md_defs = defs } in
  md

and def (k, x, p, e) = 
  let subst, p = pat IMap.empty p in
  let e = tuple e in
  let e = alias subst e in
  (k, x, p, e)

and pat acc ptl = 
  let acc, ptl = lfold pat_tuple acc ptl in
  acc, ptl

and pat_tuple acc pel = 
  let acc, pel = lfold pat_el acc pel in
  acc, pel

and pat_el acc (ty, p) = 
  let acc, p = pat_ acc ty p in
  acc, (ty, p)

and pat_ acc ty = function
  | Pany | Pid _ 
  | Pvalue _ as x -> acc, x
  | Pvariant (x, p) -> 
      let acc, p = pat acc p in
      acc, Pvariant (x, p)
  | Precord pfl -> 
      let rid = record_id pfl in
      let rexpr = [ty], Eid rid in
      let acc = List.fold_left (pat_field rexpr) acc pfl in
      acc, Pid rid
  | Pas (x, p) -> 
      let acc, p = pat acc p in
      acc, Pas (x, p)

and record_id = function
  | [] -> Ident.tmp() 
  | PFid x :: _ -> x
  | _ :: rl -> record_id rl

and pat_field rid acc = function
  | PFany 
  | PFid _ 
  | PField (_, [[_, Pany]]) -> acc
  | PField (x, [l]) -> List.fold_left (make_field rid x) acc l
  | _ -> assert false

and make_field rid x acc p = 
  match p with
  | _, Pid y ->
      let v = fst rid, Efield (rid, x) in
      IMap.add y v acc
  | _ -> assert false

and tuple l = List.map expr l
and expr (ty, e) = ty, expr_ ty e
and expr_ ty = function
  | Eid _
  | Efree _
  | Evalue _ as e -> e
  | Evariant (x, e) -> 
      let e = tuple e in
      Evariant (x, e)
  | Ebinop (bop, e1, e2) -> 
      let e1 = expr e1 in
      let e2 = expr e2 in
      Ebinop (bop, e1, e2)
  | Euop (uop, e) -> 
      let e = expr e in
      Euop (uop, e)
  | Erecord fdl -> 
      let fdl = List.map field fdl in
      Erecord fdl
  | Ewith (e, fdl) -> 
      let fdl = List.map field fdl in
      let e = expr e in
      Ewith (e, fdl)
  | Efield (e, x) -> 
      let e = expr e in
      Efield (e, x)
  | Ematch (e, al) -> 
      let e = tuple e in
      let al = List.map action al in
      Ematch (e, al)
  | Elet (p, e1, e2) -> 
      let subst, p = pat IMap.empty p in
      let e1 = tuple e1 in
      let e2 = tuple e2 in
      let e = Elet (p, e1, e2) in
      let e = alias subst [ty, e] in
      snd (List.hd e)
  | Eif (c, e1, e2) -> 
      let c = expr c in
      let e1 = tuple e1 in
      let e2 = tuple e2 in
      Eif (c, e1, e2)
  | Eapply (fk, ty, x, e) -> 
      let e = tuple e in
      Eapply (fk, ty, x, e)
  | Eseq (e1, e2) -> 
      let e1 = expr e1 in
      let e2 = tuple e2 in
      Eseq (e1, e2)

and field (x, e) = 
  let e = tuple e in
  (x, e)

and action (p, a) =
  let subst, p = pat IMap.empty p in
  let a = tuple a in
  let a = alias subst a in
  (p, a)
