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


module BlockOccs = struct
  
  let add t x = 
    let n = try IMap.find x t with Not_found -> 0 in
    let n = n+1 in
    IMap.add x n t

  let rec def df = 
    let t = List.fold_left block IMap.empty df.df_body in
    add t ((List.hd df.df_body).bl_id)
      
  and block t bl = 
    let t = List.fold_left equation t bl.bl_eqs in
    let t = ret t bl.bl_ret in
    t
      
  and equation t (_, e) = expr t e 

  and ret t = function
    | Lreturn _ -> assert false
    | Return _ -> t
    | Jump lbl -> add t lbl 
    | If (_, lbl1, lbl2) -> 
	let t = add t lbl1 in
	let t = add t lbl2 in
	t
    | Match (_, al) -> 
	List.fold_left (
	fun t (_, l) ->
	  add t l
       ) t al
	  
  and expr t = function
    | Eif (_, lbl1, lbl2) -> 
	let t = add t lbl1 in
	let t = add t lbl2 in
	t
    | Ecall lbl -> add t lbl
    | _ -> t

end

module Redirect = struct
  
  let add_block t bl = 
    if bl.bl_eqs = [] && bl.bl_phi = []
    then 
      match bl.bl_ret with
      | Jump lbl -> 
	  IMap.add bl.bl_id lbl t
      | _ -> t
    else t

  let get x t = 
    try IMap.find x t
    with Not_found -> x

  let rec def df = 
    let t = List.fold_left add_block IMap.empty df.df_body in
    let body = List.map (block t) df.df_body in
    { df with df_body = body }

  and block t bl = 
    let ret = return t bl.bl_ret in
    { bl with 
      bl_phi = List.map (phi t) bl.bl_phi ;
      bl_ret = ret ;
    }

  and phi t (x, ty, l) = 
    x, ty, List.map (fun (x, lbl) -> x, get lbl t) l
 
  and return t = function
    | Jump lbl -> Jump (get lbl t)
    | If (x, lbl1, lbl2) ->
	If (x, get lbl1 t, get lbl2 t)
    | Match (e, al) -> Match (e, List.map (action t) al) 
    | x -> x

  and action t (p, lbl) = p, get lbl t

end


(*module InlineBlocks = struct

  let get_occur x t = 
    try IMap.find x t with Not_found -> 0

  let add_block acc bl = 
    IMap.add bl.bl_id bl acc

  let rec def df = 
    let t = BlockOccs.def df in
    let bls = List.fold_left add_block IMap.empty df.df_body in
    let body = List.fold_right (block bls t) df.df_body [] in
    { df with df_body = body }

  and block bls t bl acc = 
    let eqs = equation bls t bl.bl_eqs in
    { bl with bl_eqs = eqs } :: acc
				 
  and equation bls t = function
    | [] -> []
    | [Jump lbl] when get_occur lbl t = 1 ->
	(IMap.find lbl bls).bl_eqs 
    | x :: rl -> x :: equation bls t rl
  
end *)

(*module Remove = struct

  let get_occur x t = 
    try IMap.find x t with Not_found -> 0

  let rec def df = 
    let t = BlockOccs.def df in
    let body = List.fold_right (block t) df.df_body [] in
    { df with df_body = body }

  and block t bl acc = 
    if get_occur bl.bl_id t = 0
    then acc
    else bl :: acc  
end
*)

let rec def df = 
  let df = Redirect.def df in
(*  let df = InlineBlocks.def df in
  let df = Remove.def df in *)
  df
