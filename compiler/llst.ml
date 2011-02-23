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

type id = Ident.t
type label = Ident.t
type pstring = string

type program = module_ list

and module_ = {
    md_id: id ;
    md_decls: decl list ;
    md_defs: def list ;
  }

and decl = 
  | Dtype of id * type_expr
  | Dval of Ast.link * id * type_expr * Ast.extern_def

and type_expr =
  | Tany
  | Tprim of type_prim
  | Tid of id
  | Tfun of Ast.fun_kind * type_expr_list * type_expr_list
  | Tstruct of type_expr list
  | Tptr of type_expr

and type_expr_list = type_expr list

and type_prim = Nast.type_prim =
  | Tunit
  | Tbool
  | Tchar
  | Tint
  | Tfloat
  | Tstring

and ty_id = type_expr * id
and ty_idl = ty_id list

and def = {
    df_id: id ;
    df_kind: Ast.fun_kind ;
    df_args: ty_id list ;
    df_body: block list ;
    df_ret: type_expr list ;
  }

and block = {
    bl_id: label ;
    bl_phi: phi list ;
    bl_eqs: equation list ;
    bl_ret: ret ;
  }

and ret =   
  | Return of bool * ty_idl
  | Jump of label
  | If of ty_id * label * label
  | Switch of ty_id * (value * label) list * label

and phi = id * type_expr * (id * label) list

and equation = ty_idl * expr

and expr = 
  | Enull
  | Eid of ty_id
  | Evalue of value
  | Ebinop of Ast.bop * ty_id * ty_id
  | Euop of Ast.uop * ty_id
  | Efield of ty_id * int
  | Eapply of Ast.fun_kind * bool * ty_id * ty_idl
  | Etuple of ty_id option * (int * ty_id) list
  | Egettag of ty_id
  | Eproj of ty_id * int
  | Eptr_of_int of Ident.t
  | Eint_of_ptr of Ident.t
  | Eis_null of ty_id
  | Efree of ty_id
  | Eget of ty_id * ty_id
  | Eset of ty_id * ty_id * ty_id
  | Eswap of ty_id * ty_id * ty_id
  | Epartial of ty_id * ty_idl

and value =
  | Eunit
  | Ebool of bool
  | Eint of pstring
  | Efloat of pstring
  | Echar of pstring
  | Estring of pstring
  | Eiint of int
