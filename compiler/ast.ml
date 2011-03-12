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

type id = Pos.t * string
type pstring = Pos.t * string

type fun_kind = Cfun | Lfun

type program = module_ list

and module_ = {
    md_sig: bool ;
    md_id: id ;
    md_defs: def list ;
  }

and type_def = (id * id list) * type_expr

and type_expr = Pos.t * type_expr_
and type_expr_ = 
  | Tany
  | Tvar of id 
  | Tid of id
  | Tapply of type_expr * type_expr list
  | Ttuple of type_expr list
  | Tpath of id * id
  | Tfun of fun_kind * type_expr * type_expr
  | Talgebric of (id * type_expr option) list
  | Trecord of (id * type_expr) list
  | Tabbrev of type_expr
  | Tabs of id list * type_expr
  | Tabstract

and def = 
  | Dmodule of id * id
  | Dlet of id * pat list * expr
  | Dtype of link * (id * type_expr) list
  | Dval of link * id * type_expr * extern_def

and link =
  | Abstract
  | Public
  | Private

and extern_def = 
  | Ext_none
  | Ext_C of pstring (* C function *)
  | Ext_Asm of pstring (* Assembly function *)
  | Ext_I (* Internally defined *)

and tpat = pat * type_expr
and pat = Pos.t * pat_
and pat_ = 
  | Punit
  | Pany 
  | Pid of id
  | Pchar of pstring
  | Pint of pstring
  | Pbool of bool
  | Pfloat of pstring
  | Pstring of pstring
  | Pcstr of id 
  | Pvariant of id * pat
  | Pecstr of id * id
  | Pevariant of id * id * pat
  | Precord of pat_field list
  | Pbar of pat * pat
  | Ptuple of pat list
  | Pas of id * pat

and pat_field = Pos.t * pat_field_
and pat_field_ = 
  | PFany
  | PFid of id 
  | PField of id * pat

and expr = Pos.t * expr_
and expr_ = 
  | Eunit
  | Ebool of bool
  | Eid of id
  | Eint of pstring
  | Efloat of pstring
  | Echar of pstring
  | Estring of pstring
  | Ebinop of bop * expr * expr
  | Euop of uop * expr
  | Etuple of expr list
  | Ecstr of id
  | Eecstr of id * id
  | Eefield of expr * id * id
  | Eextern of id * id
  | Erecord of field list 
  | Efield of expr * id 
  | Ematch of expr * (pat * expr) list
  | Elet of pat * expr * expr
  | Eif of expr * expr * expr 
  | Efun of fun_kind * bool * tpat list * expr 
  | Eapply of expr * expr list
  | Ewith of expr * field list
  | Eseq of expr * expr
  | Eobs of id

and field = 
  | Eflocl of id * expr 
  | Efextr of id * id * expr 

and bop = 
  | Eeq
  | Ediff
  | Elt
  | Elte
  | Egt
  | Egte
  | Eplus
  | Eminus
  | Estar
  | Emod
  | Ediv
  | Eor
  | Eand
  | Eband

and uop =
  | Euminus
