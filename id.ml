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

module StringId = struct 
  type t = string 
  let compare = String.compare
end

module IdSet = Set.Make(StringId)

type env = { 
    mutable sigs:  IdSet.t ;
    mutable cvars: IdSet.t ;
}

open Ast

let rec program l = 
  let env = { sigs = IdSet.empty ; cvars = IdSet.empty } in
  List.iter (handler env) l ;
  env

and handler env (pl, hb) = 
  List.iter (pat env) pl ;
  List.iter (handler_body env) hb

and pat env = function
  | Var s 
  | Neg s -> env.sigs <- IdSet.add s env.sigs 

and instruction env = function
  | Emit s_l -> List.iter (fun x -> env.sigs <- IdSet.add x env.sigs) s_l
  | Call s_l -> List.iter (fun x -> env.cvars <- IdSet.add x env.cvars) s_l

and handler_body env (inst_l, case_l) = 
  List.iter (instruction env) inst_l ;
  List.iter (case env) case_l 

and case env (pat_l, inst_l) = 
  List.iter (pat env) pat_l ;
  List.iter (instruction env) inst_l


module IdMap = Map.Make (StringId)
module TraceId = Map.Make (struct type t = int let compare = (-) end)

let naming id_set = 
  let tab = ref IdMap.empty in
  let back_tab = ref TraceId.empty in
  let i = ref 0 in
  IdSet.iter 
    (fun elt ->
      if not (IdMap.mem elt !tab)
      then 
	(incr i ; 
	 tab := IdMap.add elt !i !tab ; 
	 back_tab := TraceId.add !i elt !back_tab)) 
    id_set ;
  !tab
