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

module Value = struct

  type t = 
    | U
    | V of Ident.t
    | Sum of t list IMap.t
    | Rec of t * t list IMap.t

  let rec unify t1 t2 = 
    match t1, t2 with
    | V x, V y when x = y -> V x
    | Sum m1, Sum m2 -> Sum (imap2 unify_list m1 m2)
    | Rec (r1, m1), Rec (r2, m2) -> 
	let m = imap2 unify_list m1 m2 in
	Rec (unify r1 r2, m)
    | _ -> U

  and unify_list t1 t2 = 
    List.map2 unify t1 t2

  let debug = function
    | U -> o "U"
    | V x -> o (Ident.debug x)
    | Sum _ -> o "Sum"
    | Rec _ -> o "Rec"

end

module Call = struct
  
  type t = Ident.t * Value.t list

  let compare = Pervasives.compare
end

module Analyse = struct
  open Value

  module CMap = Map.Make(Call)

  type env = {
      vals: Value.t IMap.t ;
      mem: Value.t list CMap.t ref ;
      defs: def IMap.t ;
    }

  let add_val x v env = 
    { env with vals = IMap.add x v env.vals }

  let type_expr _ = V (Ident.tmp())
  let type_expr_list tyl = List.map type_expr tyl
      
  let rec def env (_, _, p, e) = 
    let tyl = List.fold_right (fun x acc -> fst x :: acc) (List.hd p) [] in
    let vl = type_expr_list tyl in
    List.iter (fun x -> debug x ; o ", ") vl ;
    print_newline() ;
    let env = pat env p vl in
    let e = tuple env e in
    List.iter (fun x -> debug x ; o ", ") e ;
    print_newline() ;
    e

  and pat env ptl vl =
    match ptl with
    | [l] -> pat_tuple env l vl
    | _ -> env
    
  and pat_tuple env pel vl = 
     List.fold_left2 pat_el env pel vl

  and pat_el env (_, p) v = pat_ env p v
  and pat_ env p v = 
    match p with
    | Pany -> env
    | Pid x -> add_val x v env
    | Pvalue _ -> env
    | Pvariant (x, p) ->
	(try match v with
	| Sum m -> pat env p (IMap.find x m)
	| _ -> env
	with Not_found -> env)
    | Precord pfl -> 
	(match v with
	| Rec (_, m) -> List.fold_left (pat_field m v) env pfl
	| _ -> env)
    | Pas (x, p) -> 
	let env = add_val x v env in
	pat env p [v]

  and pat_field m v env = function
    | PFany -> env
    | PFid x -> add_val x v env 
    | PField (fd, p) -> 
	(try pat env p (IMap.find fd m)
	with Not_found -> env)

  and tuple env el = 
    List.fold_right (
    fun e acc -> expr env e @ acc
   ) el []

  and expr env (_, e) = expr_ env e
  and expr_ env = function
    | Eid x -> [try IMap.find x env.vals with Not_found -> U]
    | Evalue v -> [U]
    | Evariant (x, e) -> 
	let e = tuple env e in
	[Sum (IMap.add x e IMap.empty)]
    | Ebinop _ -> [U]
    | Euop _ -> [U]
    | Erecord fdl ->
	let fdm = List.fold_left (field env) IMap.empty fdl in
	[Rec (V (Ident.tmp()) , fdm)]
    | Ewith (x, fdl) -> 
	let fdm = List.fold_left (field env) IMap.empty fdl in
	let r = List.hd (expr env x) in
	[Rec (r, fdm)]
    | Efield (e, x) -> 
	(match expr env e with
	| [Rec (_, m)] -> (try IMap.find x m with Not_found -> [U])
	| _ -> [U])
    | Ematch (e, al) -> 
	let e = tuple env e in
	let al = List.map (action env e) al in
	(match al with
	| [] -> assert false
	| [x] -> x
	| x :: rl -> List.fold_left unify_list x rl)
    | Elet (p, e1, e2) -> 
	let env = pat env p (tuple env e1) in
	tuple env e2
    | Eif (c, e1, e2) -> 
	let _ = expr env c in
	unify_list (tuple env e1) (tuple env e2)
  | Eapply (_, _, f, e) when f = Naming.aset -> 
      let e = tuple env e in
      (match e with
      | [t ; _ ; _] -> [t]
      | _ -> [U])
    | Eapply (_, fty, f, e) -> 
	let e = tuple env e in
	(try CMap.find (f, e) !(env.mem)
	with Not_found -> 
	  (match fty with
	  | Tfun (_, _, tyl) -> 
	      let vl = type_expr_list tyl in
	      (try
		env.mem := CMap.add (f, e) vl !(env.mem) ;
		let _, _, args, body = IMap.find f env.defs in
		let env = pat env args e in
		let vl = tuple env body in
		env.mem := CMap.add (f, e) vl !(env.mem);
		vl
	      with Not_found -> vl)
	  | _ -> assert false))
    | Eseq (e1, e2) -> 
      let _ = expr env e1 in
      tuple env e2 
    | Efree _ -> [U]

  and field env m (x, e) =
    let e = tuple env e in
    IMap.add x e m

  and action env vl (p, e) =
    let env = pat env p vl in
    tuple env e

end

open Analyse

let rec program mdl = 
  List.iter module_ mdl

and module_ md =
  let defs = List.fold_left (
    fun acc ((_, x, _, _) as df) -> IMap.add x df acc
   ) IMap.empty md.md_defs in
  let env = { vals = IMap.empty; mem = ref CMap.empty ; defs = defs } in
  List.iter (fun x -> ignore (Analyse.def env x)) md.md_defs
