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
(*open Utils
open Ast

exception Pattern_match_failed of pat * expr

let id t (pos, s) = 
  try SMap.find s t 
  with Not_found -> Error.unbound_name pos s

let rec program mdl = List.fold_left module_ SMap.empty mdl
and module_ env md = List.fold_left def env md.md_defs
and def env = function
  | Dmodule _ -> assert false
  | Dval ((_,id), pl, e) -> SMap.add id (Efun (pl, e)) env
  | _ -> env

and filter env p e = 
  match p, e with
  | Pany, _ -> env
  | Punit, Eunit -> env
  | Pid (_,x), e -> SMap.add x e env
  | Pint n1, Eint n2 when n1 = n2 -> env
  | Pcstr (x1, p), Ecstr (x2, e) when x1 = x2 -> filter_opt env p e
  | Pprod (p1, p2), Ebinop (Comma, e1, e2) -> filter (filter env p1 e1) p2 e2
  | Pstruct pfl, Estruct efl -> filter_fields env (psort pfl) (esort efl)
  | Pcons (p1, p2), Elist (e1 :: e2) -> filter (filter env p1 e1) p2 (Elist e2)
  | Plist pl, Elist el -> filter_list env pl el
  | _ -> raise Exit

and filter_opt env p e = 
  match p, e with
  | None, None -> env
  | Some p, Some e -> filter env p e
  | _ -> failwith "TODO bad constructor" 

and filter_list env l1 l2 = 
  match l1, l2 with
  | [], [] -> env
  | [], _ | _, [] -> raise Exit
  | x :: rl1, y :: rl2 -> filter_list (filter env x y) rl1 rl2

and filter_fields env pl el = 
  match pl, el with
  | [], [] -> env
  | PFany :: _, _ -> env
  | [PFid (_,x)], el -> SMap.add x (Estruct el) env
  | PField ((_,x), p) :: rl1, Ffield ((_,y), e) :: rl2 ->
      let c = String.compare x y in
      if c < 0
      then filter_fields env rl1 el
      else if c > 0
      then filter_fields env pl rl2
      else filter_fields (filter env p e) rl1 rl2
  | _ -> assert false

and action env = function
  | Anone -> Eunit
  | Awhen _ -> assert false
  | Aexpr e -> expr env e

and field env acc = function
  | Frow (_,x) -> 
      (match SMap.find x env with
      | Estruct l -> l @ acc
      | _ -> raise Exit)
  | Ffield (id, e) -> Ffield (id, expr env e) :: acc

and ematch env e pl = 
  match pl with
  | [] -> failwith "Pattern match failed"
  | (p,a) :: rl -> action (filter env p e) a

and expr env = function
 | Eunit 
 | Ebool _
 | Echar _
 | Eint _
 | Eclosure _ 
 | Ecstr (_, None)
 | Estring _ as e -> e
 | Eid (_,x) -> expr env (SMap.find x env)
 | Ecstr (c, Some e) -> Ecstr (c, Some (expr env e))
 | Elist el -> Elist (List.map (expr env) el)
 | Estruct fdl -> Estruct (uniq ef_cmp (List.fold_left (field env) [] fdl))
 | Etyped (e, _) -> expr env e
 | Edot_string (e1, e2) -> dot_string (expr env e1) (expr env e2)
 | Edot_array _ -> failwith "todo dot array"
 | Epath _ (* of expr * id *) -> failwith "TODO Epath"
 | Ematch (e, pal) -> ematch env (expr env e) pal
 | Elet ([p], e1, e2) -> ematch env (expr env e1) [p, Aexpr e2]
 | Elet _ -> failwith "TODO rest of let"
 | Eif (e1, e2, _) when expr env e1 = Ebool true -> expr env e2
 | Eif (_, _, e) -> expr env e
 | Ebinop (Seq, e1, e2) -> ignore (expr env e1) ; expr env e2
 | Ebinop (bop, e1, e2) -> binary_op bop (expr env e1) (expr env e2)
 | Eunop (uop, e) -> unary_op uop (expr env e)
 | Eapply (e1, e2) -> eapply env (expr env e1) (expr env e2)
 | (Efun (pl, b) as e) -> 
     let t = free_vars SSet.empty e in
     let vl = SSet.elements t in
     let el = List.map (fun x -> SMap.find x env) vl in
     let el = List.map (expr env) el in
     Eclosure (e, List.map2 (fun x y -> x,y) vl el)

and eapply env e1 e2 = 
  match e1 with
  | Eclosure (Efun (pl, e), el) -> 
      let env = List.fold_left (fun env (x, y) -> SMap.add x y env) env el in
      expr env (Elet (pl, e2, e))
  | _ -> failwith "Bad application"

and dot_string e1 e2 = 
  match e1, e2 with
  | Estring (_,s), Eint n -> Echar (s.[n])
  | _ -> assert false

and binary_op op e1 e2 = 
  match op, e1, e2 with
  | Eq, _, _ -> Ebool (e1 = e2)
  | Lt, _, _ -> Ebool (e1 < e2)
  | Lte, _, _ -> Ebool (e1 <= e2)
  | Gt, _, _ -> Ebool (e1 > e2)
  | Gte, _, _ -> Ebool (e1 >= e2)
  | Plus, Eint n1, Eint n2 -> Eint (n1 + n2)
  | Minus, Eint n1, Eint n2 -> Eint (n1 - n2)
  | Star, Eint n1, Eint n2 -> Eint (n1 * n2)
  | Comma, e1, e2 -> Ebinop (Comma, e1, e2)
  | Cons, x, Elist l -> Elist (x :: l)
  | Seq, _, _ -> assert false (* is handled by expr *)
  | _ -> raise Exit

and unary_op op e = 
  match op, e with
  | Uminus, Eint n -> Eint (-n)
  | _ -> raise Exit
*)
