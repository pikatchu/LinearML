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
open Llst

let n = ref 0
let space() = 
  let rec aux n = if n = 0 then () else (o " " ; aux (n-1)) in
  aux !n

let nl() = o "\n" ; space()

let push() = n := !n + 2 
let pop() = n := !n - 2
  
let id x = o (Ident.debug x)
let label x = o (Ident.debug x) 
let pstring x = o x

let rec program mdl = 
  List.iter module_ mdl

and module_ md = 
  o "module " ;
  id md.md_id ;
  o ":" ;
  push() ;
  nl() ;
  nl() ;
  List.iter decl md.md_decls ;
  pop() ;
  nl() ;
  o "end" ;
  o " = struct" ;
  push() ;
  nl() ;
  List.iter def md.md_defs ;
  pop() ;
  nl() ;
  o "end" ;
  nl()

and decl = function
  | Dtype (x, ty) -> 
      o "type " ; id x ; o " = " ; type_expr ty ;
      nl () ;
  | Dval (ll, x, ty, v) -> 
      o "val " ; 
      (match ll with 
      | Ast.Abstract -> assert false
      | Ast.Public -> () | Ast.Private -> o "private ") ;
      id x ; o ": " ; type_expr ty ;
      (match v with 
      | Ast.Ext_none -> ()
      | Ast.Ext_C x -> o " = " ; o (snd x)
      | Ast.Ext_Asm x -> o " = (asm)" ; o (snd x)
      | Ast.Ext_I -> o " = (internal)") ;
      nl () ;

and type_expr = function
  | Tany -> o "void*"
  | Tprim tp -> type_prim tp
  | Tid x -> id x 
  | Tptr x -> type_expr x ; o "*"
  | Tfun (k, tyl1, tyl2) -> 
      o "(" ;
      type_expr_list tyl1 ;
      o (match k with Ast.Cfun -> " #" | Ast.Lfun -> " ") ;
      o "-> " ;
      type_expr_list tyl2 ;
      o ")"
  | Tstruct tyl -> 
      o "{ " ; print_list o (fun _ x -> type_expr x) ", " tyl ; o " }"

and type_expr_list l = 
  if l = []
  then o "void"
  else print_list o (fun _ x -> type_expr x) ", " l

and type_prim = function
  | Tunit -> o "unit"
  | Tbool -> o "bool"
  | Tchar -> o "char"
  | Tint  -> o "int"
  | Tfloat -> o "float"
  | Tstring -> o "string"

and def df = 
  id df.df_id ; 
  o " " ; 
  List.iter (fun (ty, x) -> o "(" ; id x ; o ": " ; type_expr ty ; o ") ") df.df_args ;
  o ": " ; type_expr_list df.df_ret ;
  o " = " ;
  push() ;
  List.iter block df.df_body ;
  pop() ;
  nl() ; nl() ;
  
and idl l = o "(" ; print_list o (fun _ (_, x) -> id x) ", " l ; o ")"
and ty_idl l = 
  o "(" ; 
  print_list o (fun _ (ty, x) -> type_expr ty ; o " " ; id x) ", " l; 
  o ")"

and block bl = 
  nl() ;
  id bl.bl_id ;
  o ":" ;
  nl() ;
  push() ; 
  nl() ;
  if bl.bl_phi <> [] then (o "phi: " ; nl() ; List.iter phi bl.bl_phi ; nl()) ;
  List.iter equation bl.bl_eqs ;
  (match bl.bl_ret with
  | Return (tail, l) -> 
      (o "return[" ; 
       o (if tail then "true] " else "false] ") ;
       ty_idl l)
  | Jump x -> o "jump " ; id x
  | If (x, l1, l2) ->
      o "Iif " ; tid x ; o " then jump " ; label l1 ; 
      o " else jump " ; label l2 ;
  | Switch (x, al, default) -> 
      o "switch " ; ty_id x ; push() ; nl() ; List.iter maction al ; pop() ;
      o "default: " ; id default ;
  ) ;
  pop() ;
  nl()

and phi (x, ty, l) = 
  id x ; o ":" ; type_expr ty ; o " <- " ; 
  List.iter (fun (x, lbl) -> o "(" ; id x ; o ", " ; label lbl ; o ") ; ") l ;
  nl()

and equation (idl, e) = 
  print_list o (fun _ (ty, x) -> type_expr ty ; o " " ; id x) ", " idl ; 
  o " = " ;
  expr e ;
  nl()

and ty_id (ty, x) = o "(" ; o (Ident.debug x) ; o ":" ; type_expr ty ; o ") " 

and expr = function
  | Enull -> o "null"
  | Eis_null x -> o "null? " ; ty_id x
  | Eid x -> ty_id x
  | Evalue v -> value v
  | Ebinop (bop, id1, id2) -> binop bop ; o " " ; tid id1 ; o " " ; tid id2 
  | Euop (uop, x) -> unop uop ; o " " ; tid x
  | Etuple (x, l) -> o "{ " ; maybe ty_id x ; o " | " ; 
      print_list o (fun _ (n, x) -> o "[" ; o (soi n) ; o "]=" ; ty_id x) ", " l ; o " }"
  | Efield (x, y) -> tid x ; o "." ; o (soi y)
  | Eapply (fk, b, x, l) -> 
      if b then o "tail " else () ; 
      o "call[" ; 
      (match fk with Ast.Cfun -> o "C] " | Ast.Lfun -> o "L] ") ;
      ty_id x ; o " " ; idl l
  | Egettag x -> o "gettag " ; tid x
  | Eproj (x, n) -> tid x ; o "[" ; o (soi n) ; o "]"
  | Eptr_of_int x -> o "(pointer) " ; id x
  | Eint_of_ptr x -> o "(int) " ; id x
  | Efree x -> o "free " ; id (snd x)
  | Eget (x, y) -> o "get " ; id (snd x) ; id (snd y)
  | Eset (x, y, z) -> o "set " ; id (snd x) ; id (snd y) ; id (snd z)
  | Eswap (x, y, z) -> o "swap " ; id (snd x) ; id (snd y) ; id (snd z)
  | Epartial (f, e) -> o "partial " ; id (snd f) ; ty_idl e

and bounds l u =
  o "[" ; o (string_of_bool l) ;
  o "," ; o (string_of_bool u) ;
  o "] "

and field (x, l) = o (soi x) ; o " = " ; idl l
and action (x, e) = 
  ty_id x ; o " -> " ; expr e ; nl()

and maction (x, lbl) = 
  value x ; o " -> jump " ; id lbl ; nl()

and tid (_, x) = id x

and value = function
  | Eunit -> o "unit"
  | Ebool b -> o (string_of_bool b) 
  | Eint x -> o x
  | Efloat x -> o x
  | Echar x -> o x
  | Estring x -> o x
  | Eiint x -> o (soi x)

and binop = function 
  | Ast.Eeq -> o "eq"
  | Ast.Ediff -> o "diff" 
  | Ast.Elt -> o "lt"
  | Ast.Elte -> o "lte"
  | Ast.Egt -> o "gt"
  | Ast.Egte -> o "gte"
  | Ast.Eplus -> o "plus"
  | Ast.Eminus -> o "minus"
  | Ast.Estar -> o "star"
  | Ast.Emod -> o "mod"
  | Ast.Ediv -> o "div"
  | Ast.Eor -> o "or"
  | Ast.Eand -> o "and"

and unop = function
  | Ast.Euminus -> o "uminus"
