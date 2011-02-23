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
open Est

module MakeOrigins = struct

  let rec def df = 
    let t = IMap.empty in
    List.fold_left block t df.df_body 

  and block t bl = 
    let t = List.fold_left (phi bl.bl_id) t bl.bl_phi in
    List.fold_left (equation bl.bl_id) t bl.bl_eqs

  and phi orig t (x, _, _) = IMap.add x orig t 
  and equation orig t (idl, _) = 
    List.fold_left (
    fun t (_, x) -> 
      IMap.add x orig t
   ) t idl
  
end

module MakePreds = struct

  let rec def df = 
    let t = IMap.empty in
    List.fold_left block t df.df_body 

  and block t bl = 
    let succs = ret ISet.empty bl.bl_ret in 
    ISet.fold (
    fun x acc ->
      let preds = try IMap.find x acc with Not_found -> ISet.empty in
      let preds = ISet.add bl.bl_id preds in
      IMap.add x preds acc
   ) succs t

  and ret t = function
    | Lreturn _
    | Return _ -> t
    | Jump lbl -> ISet.add lbl t 
    | If (_, x1, x2) -> ISet.add x1 (ISet.add x2 t)
    | Match (_, l) -> 
	List.fold_left (fun t (_, lbl) -> ISet.add lbl t) t l

end

module MakePhi = struct

  let rec def df = 
    let preds = MakePreds.def df in
    let t = MakeOrigins.def df in
    { df with df_body = List.map (block t preds) df.df_body }

  and block t preds bl = 
    let preds = try IMap.find bl.bl_id preds with Not_found -> ISet.empty in
    { bl with bl_phi = List.map (phi t preds) bl.bl_phi }

  and phi t preds (x, ty, vl) = x, ty, List.fold_right (
    fun (x, _) acc ->
      let orig = IMap.find x t in
      if ISet.mem orig preds
      then (x, IMap.find x t) :: acc
      else acc
   ) vl []
end

let rec is_tail l1 l2 = 
  match l1, l2 with
  | [], [] -> true
  | [], _ | _, [] -> false
  | (_, x1) :: rl1, (_, x2) :: rl2 -> 
      (Ident.compare x1 x2 = 0) && is_tail rl1 rl2

let rec program mdl = 
  List.rev_map module_ mdl

and module_ md = 
  { md with md_defs = List.rev_map def md.md_defs }

and def df = 
  let bls = List.fold_left (
    fun acc bl ->
      IMap.add bl.bl_id bl acc
   ) IMap.empty df.df_body in
  let bll = block bls [] (List.hd df.df_body) in
  let _, bll = List.fold_left (
    fun (s, acc) x ->
      if ISet.mem x.bl_id s 
      then s, acc
      else ISet.add x.bl_id s, x :: acc
   ) (ISet.empty, []) bll in 
  let bll = List.rev bll in
  let df = { df with df_body = bll } in
  let df = MakePhi.def df in
  df

and block bls acc bl = 
  let blocks, ret, eqs = equation bls bl.bl_ret acc bl.bl_eqs in
  { bl with 
    bl_eqs = eqs ; 
    bl_ret = ret ;
  } :: blocks

and equation bls ret acc eq = 
  match eq with 
  | [] -> acc, ret, []
  | (idl, Eif (c, l1, l2)) :: rl -> 
      let acc, ret, rl = equation bls ret acc rl in
      let b1 = IMap.find l1 bls in
      let b2 = IMap.find l2 bls in
      let btarget = Ident.tmp() in
      let rl1 = match b1.bl_ret with Lreturn l -> l | _ -> assert false in
      let rl2 = match b2.bl_ret with Lreturn l -> l | _ -> assert false in
      (match ret, rl with
      | Return (_, retl), [] when is_tail retl idl && false (* TODO Fix this *)-> (* this is a tail call *)
	  let b2 = { b2 with bl_ret = Return (true, rl2) } in
	  let acc = block bls acc b2 in
	  let b1 = { b1 with bl_ret = Return (true, rl1) } in
	  let acc = block bls acc b1 in
	  acc, If (c, l1, l2), []
      | Return (_, retl), [] when is_tail retl idl ->
	  let b2 = { b2 with bl_ret = Return (false, rl2) } in
	  let acc = block bls acc b2 in
	  let b1 = { b1 with bl_ret = Return (false, rl1) } in
	  let acc = block bls acc b1 in
	  acc, If (c, l1, l2), []
      | _ ->
	  let phil = make_phi idl b1.bl_id rl1 b2.bl_id rl2 in
	  let b3 = {
	    bl_id = btarget ;
	    bl_phi = phil ;
	    bl_ret = ret ;
	    bl_eqs = rl ;
	  } in
	  let acc = b3 :: acc in
	  let b2 = { b2 with bl_ret = Jump btarget } in
	  let acc = block bls acc b2 in
	  let b1 = { b1 with bl_ret = Jump btarget } in
	  let acc = block bls acc b1 in
	  acc, If (c, l1, l2), [])
  | (idl, Ecall lbl) :: rl -> 
      let acc, ret, eqs = equation bls ret acc rl in
      let b = IMap.find lbl bls in
      let idl' = match b.bl_ret with Lreturn l -> l | _ -> assert false in
      let eqs = List.fold_right2 (
	fun x1 x2 acc ->
	  ([x1], Eid x2) :: acc
       ) idl idl' eqs in
      let btarget = Ident.tmp() in
      let rest = { 
	bl_id = btarget ;
	bl_phi = [] ;
	bl_eqs = eqs ; 
	bl_ret = ret ;
      } in
      let acc = rest :: acc in
      let b = { b with bl_ret = Jump btarget } in
      let acc = block bls acc b in
      acc, Jump lbl, [] 

(*  | (idl, Ecall lbl) :: rl -> 
      let acc, ret, eqs = equation bls ret acc rl in
      let bl = IMap.find lbl bls in
      let idl' = match bl.bl_ret with Lreturn l -> l | _ -> assert false in
      let eqs_rl = List.fold_right2 (
	fun x1 (_, x2) acc ->
	  ([x1], Eid x2) :: acc
       ) idl idl' eqs in
      let acc, ret, eqs = equation bls ret acc bl.bl_eqs in
      acc, ret, eqs @ eqs_rl *)


  | (idl, Ematch (cl, al)) :: rl -> 
      let acc, ret, rl = equation bls ret acc rl in
      let al = List.map (
	function (p, Ecall l) -> p, l | _ -> assert false
       ) al in
      let bl = List.map (fun (_, l) -> l) al in
      let bl = List.map (fun x -> IMap.find x bls) bl in
      (match ret, rl with
      | Return (_, retl), [] when is_tail retl idl -> (* tail call *)
	  let acc = List.fold_left (
	    fun acc b ->
	      let ret = 
		match b.bl_ret with 
		| Lreturn idl -> Return (false, idl)  (* TODO fix this *)
		| _ -> assert false in
	      let b = { b with bl_ret = ret } in
	      block bls acc b
	   ) acc bl in
	  acc, Match (cl, al), []	  
      | _ ->
	  let btarget = Ident.tmp() in
	  let retll = List.map (fun b -> 
	    match b.bl_ret with 
	    | Lreturn l -> List.map (fun (_, x) -> x, b.bl_id) l
	    | _ -> assert false) bl in      
	  let phil = make_phil idl retll in 
	  let b3 = {
	    bl_id = btarget ;
	    bl_phi = phil ;
	    bl_ret = ret ;
	    bl_eqs = rl ;
	  } in
	  let acc = b3 :: acc in
	  let acc = List.fold_left (
	    fun acc b ->
	      let b = { b with bl_ret = Jump btarget } in
	      block bls acc b
	   ) acc bl in
	  acc, Match (cl, al), [])
  | x :: rl ->
      let acc, ret, rl = equation bls ret acc rl in
      acc, ret, x :: rl

and make_phi l bl1 l1 bl2 l2 = 
  match l, l1, l2 with
  | [], [], [] -> []
  | [], _, _
  | _, [], _
  | _, _, [] -> assert false
  | (ty, x) :: rl, (_, x1) :: rl1, (_, x2) :: rl2 ->
      let phi1 = x1, bl1 in
      let phi2 = x2, bl2 in
      (x, ty, [phi1 ; phi2]) :: make_phi rl bl1 rl1 bl2 rl2

and make_phil l bl = 
  match l with
  | [] -> []
  | (ty, x) :: rl -> 
      let l', bl = List.fold_right (
	fun l (acc1, acc2) ->
	  match l with
	  | [] -> assert false
	  | x :: rl -> x :: acc1, rl :: acc2
       ) bl ([], []) in
      let phil = make_phil rl bl in
      (x, ty, l') :: phil

