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
open Lexing

type t = {
    pos_file: string ;
    pos_start: Lexing.position ;
    pos_end: Lexing.position ;
    pos_history: t list ref ;
  }

let file = ref ""

let none = {
  pos_file = "" ;
  pos_start = dummy_pos ;
  pos_end = dummy_pos ;
  pos_history = ref [] ;
}

let make (lb:Lexing.lexbuf) =
 let pos_start = lexeme_start_p lb in
 let pos_end = lexeme_end_p lb in
 let pos_history = ref [] in
 { pos_file = !file; pos_start = pos_start ; 
   pos_end = pos_end ; pos_history = pos_history }

let btw x1 x2 = 
  if x1.pos_file <> x2.pos_file 
  then failwith "Position in separate files" ;
  if x1.pos_end > x2.pos_end
  then failwith "Invalid positions Pos.btw" ;
  { x1 with pos_end = x2.pos_end }

let string t = 
  let line = t.pos_start.pos_lnum in
  let start = t.pos_start.pos_cnum - t.pos_start.pos_bol in
  let end_ = start + t.pos_end.pos_cnum - t.pos_start.pos_cnum in
  Printf.sprintf "File \"%s\", line %d, characters %d-%d:" 
    t.pos_file line start end_
  
let rec begin_end l = 
  match l with
  | [] -> assert false
  | x :: _ -> fst x, end_ l

and end_ x = 
  match x with
  | [] -> assert false
  | [x] -> fst x
  | _ :: rl -> end_ rl

let list l = 
  let b, e = begin_end l in
  btw b e, l

let push p h = 
  p.pos_history := h :: !(p.pos_history)

let history p = !(p.pos_history)

let compare = Pervasives.compare
