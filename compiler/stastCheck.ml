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
open Stast

type ty = 
  | ATany
  | ATalgebric of (Ident.t * int) list * ty option IMap.t
  | ATrecord of (Ident.t * int) list * ty IMap.t
  | ATprod of ty list
  | ATchoice of ty list

module Cmp = struct

  type t = ty

  let rec compare t1 t2 = 
    match t1, t2 with
    | ATalgebric (_, m1), ATalgebric (_, m2) -> 
	IMap.compare compare_opt m1 m2
    | ATalgebric _, _ -> -1
    | _, ATalgebric _ -> 1
    | ATrecord (_, m1), ATrecord (_, m2) -> 
	let l1 = list_of_imap m1 in 
	let l2 = list_of_imap m2 in 
	compare (ATprod l1) (ATprod l2)
    | ATrecord _, _ -> -1
    | _, ATrecord _ -> 1
    | ATprod tyl1, ATprod tyl2 -> 
	List.fold_left2 (fun c x y ->
	  if c = 0
	  then compare x y
	  else c) 0 tyl1 tyl2
    | ATprod _, _ -> -1
    | _, ATprod _ -> 1
    | ATchoice _, _ 
    | _, ATchoice _ -> assert false
    | ATany, ATany -> 0

  and compare_opt ty1 ty2 = 
    match ty1, ty2 with
    | None, None -> 0
    | Some x1, Some x2 -> compare x1 x2
    | _ -> assert false

end

module TSet = Set.Make (Cmp)

let rec make_any n = 
  if n <= 0
  then []
  else ATany :: (make_any (n-1))
		 
let any n = 
  if n = 0
  then None
  else if n = 1 
  then Some ATany
  else Some (ATprod (make_any n))

let any_field n = 
  if n = 1
  then ATany
  else ATprod (make_any n)


module Print = struct

  let rec is_any = function
  | ATany -> true
  | ATalgebric (_, m) -> IMap.is_empty m
  | ATrecord (_, m) -> 
      IMap.fold (
      fun _ t acc -> 
	is_any t || acc
      ) m false
  | ATchoice tyl
  | ATprod tyl -> 
      List.fold_left (fun acc t ->
	acc || is_any t) false tyl

  let rec type_ o = function
    | ATany -> o "_"
    | ATalgebric (idl, m) -> 
	let l = clist_of_imap m in
	(match l with
	| [] -> o "_"
	| [x] -> variant idl o x
	| l -> o "(" ; print_list o (variant idl) " | " l ; o ")")
    | ATrecord (_, m) -> 
	let l = clist_of_imap m in
	let c = ref false in
	IMap.iter (fun _ t -> if is_any t then c := true) m ;
	o "{ " ; fields o l ; 
	if !c
	then (o " ; _") ;
	o " }"
    | ATprod tl -> 
	o "(" ; print_list o type_ ", " tl ; o ")"
    | ATchoice tl -> 
	print_list o type_ " || " tl

  and variant idl o (x, ty) = 
    let id = Ident.to_string x in
    if id = "List.Empty"
    then o "[]"
    else 
    match ty with
    | None -> o id
    | Some ATany ->
	let n = List.assoc x idl in
	let l = ref [] in
	for i = 1 to n do
	  l := ATany :: !l 
	done ;
	if id = "List.Cons" 
	then (o "(" ; print_list o type_ " :: " !l ; o ")")
	else o "(" ; o id ; o " " ; print_list o type_ " " !l ; o ")"
    | Some (ATprod tyl) -> 
	if id = "List.Cons"
	then (o "(" ; print_list o type_ " :: " tyl ; o ")")
	else (o "(" ; o id ; o " " ; print_list o type_ " " tyl ; o ")")
    | Some ty ->
	o "(" ; o id ; o " " ; type_ o ty ; o ")"

  and fields o l = 
    match l with
    | [] -> ()
    | [x] -> field o x
    | (_, ATany) :: rl -> fields o rl
    | x :: rl -> field o x ; o " ; " ; fields o rl

  and field o (id, ty) =
    o (Ident.to_string id) ; o " = " ; type_ o ty

  let error ty c = 
    let o = output_string c in
    type_ o ty ;
    o "\n"

  let debug ty = 
    let o = output_string stdout in
    type_ o ty ;
    o "\n"

end

let rec max t1 t2 = 
  match t1, t2 with
  | ATany, t | t, ATany -> general t
  | ATalgebric (idl, m1), ATalgebric (_, m2) -> 
      ATalgebric (idl, imap2 (opt2 max) m1 m2)
  | ATrecord (idl, m1), ATrecord (_, m2) -> 
      ATrecord (idl, imap2 max m1 m2)
  | ATprod tl1, ATprod tl2 -> 
      ATprod (List.map2 max tl1 tl2) 
  | ATchoice tl, t 
  | t, ATchoice tl -> List.fold_left max t tl
  | _ -> assert false

and general t = 
  match t with
  | ATany -> ATany
  | ATalgebric (idl, m) ->
      let m = List.fold_left (fun acc (x, n) ->
	try IMap.add x (opt general (IMap.find x m)) acc
	with Not_found -> IMap.add x (any n) acc) m idl in
      ATalgebric (idl, m)
  | ATrecord (idl, m) ->
      let m = List.fold_left (fun acc (x, n) ->
	try IMap.add x (general (IMap.find x m)) acc
	with Not_found -> IMap.add x (any_field n) acc) m idl in
      ATrecord (idl, m)
  | ATprod l -> ATprod (List.map general l)
  | ATchoice l -> List.fold_left max ATany (List.map general l)

let rec expand_map f m gm =
  IMap.fold (fun x t m ->
    try IMap.add x (f t (IMap.find x gm)) m
    with Not_found -> 
      assert false) m m

let rec expand ty gt = 
  match ty, gt with
  | ATany, t -> t
  | ATalgebric (x, m), ATalgebric (_, gm) -> 
      ATalgebric (x, expand_map (opt2 expand) m gm)
  | ATrecord (x, m), ATrecord (_, gm) -> 
      ATrecord (x, expand_map expand m gm)
  | ATprod tl1, ATprod tl2 -> 
      ATprod (List.map2 expand tl1 tl2)
  | _ -> assert false

module Break = struct

  let variant idl x t = 
    ATalgebric (idl, (IMap.add x t IMap.empty))

  let rec type_ acc t = 
    match t with
    | ATany as x -> x :: acc
    | ATalgebric (idl, m) -> 
	IMap.fold (fun x t acc ->
	  match t with
	  | None -> variant idl x t :: acc
	  | Some t -> 
	      let l = type_ [] t in
	      List.fold_right (fun t acc ->
		variant idl x (Some t) :: acc) l acc) m acc

    | ATrecord (idl, m) -> 
	let fdl = clist_of_imap m in
	let names = List.map fst fdl in
	let tl = List.map snd fdl in
	let tll = List.map (type_ []) tl in
	let tll = prod tll in
	List.fold_right (fun tl acc -> 
	  let m = List.fold_right2 IMap.add names tl IMap.empty in
	  ATrecord (idl, m) :: acc) tll acc
      
    | ATprod tl -> 
	let tll = List.map (type_ []) tl in
	let tll = prod tll in
	List.fold_right (fun x acc -> ATprod x :: acc) tll acc

    | ATchoice tyl -> List.fold_left type_ acc tyl


  and prod = function
    | [] -> assert false
    | [tl] -> List.map (fun x -> [x]) tl
    | tl :: rl ->
	let sub = prod rl in
	List.fold_right (fun x acc -> 
	  List.fold_right (fun l acc -> (x :: l) :: acc) sub acc)
	  tl
	  []

  and record ml =
    match ml with
    | [] -> assert false
    | [x, tl] -> List.map (fun t -> IMap.add x t IMap.empty) tl
    | (x, tl) :: rest -> 
	let l = record rest in
	List.fold_right (fun ml acc ->
	  List.fold_right (fun t acc ->
	  IMap.add x t ml :: acc) tl acc) 
	  l []
end

module Pat = struct

  let unit = 	
    let v = Naming.eunit in
    ATalgebric ([v, 0], IMap.add v None IMap.empty)
  
  let rec pat t (_, ptl) = ATchoice (List.map (pat_tuple t) ptl)

  and pat_tuple t (_, pel) = 
    match pel with 
    | [x] -> pat_el t x
    | _ -> ATprod (List.map (pat_el t) pel)

  and pat_el t (ty, p) = pat_ t ty p

  and pat_ t ty = function
    | Pany
    | Pid _ -> ATany
    | Pvalue Eunit -> unit
    | Pvalue _ -> failwith "TODO stastCheck value pattern"
    | Pvariant ((_, x), (_, [])) ->
	ATalgebric (type_expr t ty, IMap.add x None IMap.empty)
    | Pvariant ((_, x), p) -> 
	ATalgebric (type_expr t ty, IMap.add x (Some (pat t p)) IMap.empty)
    | Precord pfl -> 
	let idl = type_expr t ty in
	let m = List.fold_left (fun acc (x, _ ) -> 
	  IMap.add x ATany acc) IMap.empty idl in
	let m = List.fold_left (pat_field t) m pfl in
	ATrecord (idl, m)
    | Pas (_, (_, pl)) ->
	let pl = List.map (
	  function
	    | _, [p] -> pat_el t p
	    | _ -> assert false (* cannot use 'as' on tuples *)
	 ) pl in
	ATchoice pl

  and pat_field t acc (_, pf) = pat_field_ t acc pf
  and pat_field_ t acc = function
    | PFany 
    | PFid _ -> acc
    | PField ((_, x), p) -> IMap.add x (pat t p) acc

  and type_expr t (_, ty) = 
    match ty with
    | Tprim _
    | Tany
    | Tfun _
    | Tvar _ -> assert false
    | Tapply ((_, x), (_, [ty])) when x = Naming.tobs -> 
	type_expr t ty
    | Tid (_, x)
    | Tapply ((_, x), _) -> 
	try IMap.find x t 
	with Not_found -> assert false

  and value = function
    | Eunit -> Tunit
    | Ebool _ -> Tbool
    | Eint _ -> Tint
    | Efloat _ -> Tfloat
    | Echar _ -> Tchar 
    | Estring _ -> Tstring

end


module Env = struct

  let rec make mdl =
    let t = List.fold_left module_ IMap.empty mdl in
    t

  and module_ t md = 
    List.fold_left decl t md.md_decls 

  and decl t = function
    | Drecord td 
    | Dalgebric td -> 
	let l = talgebric t td in
	IMap.add (snd td.td_id) l t
    | _ -> t
	
  and talgebric t td = 
    IMap.fold (fun x t acc -> (x, arity t) :: acc) td.td_map []

  and arity (_, (_, l)) = List.length l

end

let rec program mdl = 
  let t = Env.make mdl in
  List.iter (module_ t) mdl 

and module_ t md =
  List.iter (def t) md.md_defs

and def t (_, x, p, e) = 
  pat t p ;
  tuple t e 

and pat t (((pos, _), _) as p) = 
  check_pattern t pos [p]

and tuple t ((p, _), tpl) = List.iter (tuple_pos t p) tpl 
and tuple_pos t p (_, e) = expr_ t p e
and expr t ((p, _), e) = expr_ t p e
and expr_ t pos = function
  | Eid _ -> ()
  | Evalue _ -> ()
  | Evariant (_, e) -> tuple t e
  | Ebinop (_, e1, e2) -> expr t e1 ; expr t e2
  | Euop (_, e) -> expr t e
  | Erecord fdl -> List.iter (field t) fdl
  | Ewith (e, fdl) -> expr t e ; List.iter (field t) fdl
  | Efield (e, _) -> expr t e
  | Ematch (_, al) ->
      let pl = List.map fst al in
      check_pattern t pos pl
  | Elet (p, e1, e2) -> 
      pat t p ;
      tuple t e1 ;
      tuple t e2 
  | Eif (e1, e2, e3) -> 
      expr t e1 ;
      tuple t e2 ;
      tuple t e3
  | Epartial (e1, e2) -> expr t e1 ; tuple t e2
  | Efun (_, _, _, e) -> tuple t e
  | Eapply (_, _, _, e) -> tuple t e
  | Eseq (e1, e2) -> 
      expr t e1 ;
      tuple t e2
  | Eobs _ -> ()
  | Efree _ -> ()

and field t (_, e) = tuple t e
and action t (_, e) = tuple t e

and check_pattern t pos pl =
  let posl = List.map (fun x -> fst (fst x)) pl in
  let pl = List.map (Pat.pat t) pl in
  let gty = List.fold_left max ATany pl in
  let set = List.fold_left (fun acc t -> 
    TSet.add t acc) TSet.empty (Break.type_ [] gty) in
  let set = List.fold_left2 (remove_list gty) set posl pl in
  if TSet.is_empty set
  then ()
  else Error.not_exhaustive pos (Print.error (TSet.choose set))

and remove_list gty set pos t = 
  let used = ref false in
  let tyl = Break.type_ [] t in
  let tyl = List.map (fun t -> expand t gty) tyl in
  let tyl = List.fold_left Break.type_ [] tyl in
  let set = List.fold_left (fun set ty ->
    if TSet.mem ty set
    then (used := true ; 
	  TSet.remove ty set)
    else set) set tyl in
  if not !used
  then Error.unused pos
  else set
