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

type id = Nast.id
type pstring = Nast.pstring

type program = module_ list

and module_ = {
    md_sig: bool;
    md_id: id ;
    md_decls: Neast.decl list ;
    md_defs: def list ;
  }

and type_expr = Neast.type_expr
and type_expr_list = Neast.type_expr_list

and def = Ast.fun_kind * id * pat * tuple

and pat = type_expr_list * pat_tuple list
and pat_tuple = type_expr_list * pat_el list
and pat_el = type_expr * pat_
and pat_ = 
  | Pany 
  | Pid of id
  | Pvalue of value
  | Pvariant of id * pat
  | Precord of pat_field list
  | Pas of id * pat

and pat_field = Pos.t * pat_field_
and pat_field_ = 
  | PFany
  | PFid of id 
  | PField of id * pat

and tuple = type_expr_list * tuple_pos list
and tuple_pos = type_expr_list * expr_
and expr = type_expr * expr_
and expr_ = 
  | Eid of id
  | Evalue of value
  | Evariant of id * tuple
  | Ebinop of Ast.bop * expr * expr
  | Euop of Ast.uop * expr
  | Erecord of (id * tuple) list 
  | Ewith of expr * (id * tuple) list 
  | Efield of expr * id 
  | Ematch of tuple * (pat * tuple) list
  | Elet of pat * tuple * tuple
  | Eif of expr * tuple * tuple
  | Eapply of Ast.fun_kind * type_expr * id * tuple
  | Epartial of expr * tuple
  | Eseq of expr * tuple
  | Eobs of id
  | Efree of type_expr * id
  | Efun of Ast.fun_kind * bool * pat_el list * tuple

and value = Nast.value

module FreeVars = struct

  let rec pat s (_, ptl) = List.fold_left pat_tuple s ptl 
  and pat_tuple s (_, pl) = List.fold_left pat_el s pl
  and pat_el s (_, p) = pat_ s p
  and pat_ s = function
    | Pvalue _ 
    | Pany -> s
    | Pid (_, x) -> ISet.add x s 
    | Pvariant (_, p) -> pat s p 
    | Precord pfl -> List.fold_left pat_field s pfl 
    | Pas ((_, x), p) -> 
	let s = ISet.add x s in
	pat s p

  and pat_field s (_, pf) = pat_field_ s pf
  and pat_field_ s = function
    | PFany -> s
    | PFid (_, x) -> ISet.add x s
    | PField (_, p) -> pat s p

  let pat p = pat ISet.empty p

end

