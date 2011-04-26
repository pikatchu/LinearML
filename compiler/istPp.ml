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
open Ist

let o = output_string stdout
let sp = ref 0
let rec spaces n = 
  if n <= 0
  then ()
  else (o " "; spaces (n-1))

let spaces() = spaces !sp
let push() = sp := !sp + 2
let pop() = sp := !sp - 2
let nl() = o "\n"; spaces()

let rec list f sep l = 
  match l with
  | [] -> ()
  | [x] -> f x
  | x :: rl -> f x; o sep; list f sep rl

let id x = o (Ident.debug x)

let rec program mdl = 
  List.iter module_ mdl

and module_ md = 
  o "module ";
  id md.md_id;
  o " = ";
  o (if md.md_sig then "sig" else "struct");
  o "\n";
  push();
  spaces();
  List.iter decl md.md_decls;
  List.iter def md.md_defs;
  pop();
  nl();
  o "end\n";

and decl = function
  | Dalgebric td -> sum td
  | Drecord td -> record td 
  | Dval (l, x, ty, ext) ->
      o "val "; 
      (match l with
      | Ast.Abstract -> assert false
      | Ast.Public -> ()
      | Ast.Private -> o "private ");
      id x; 
      type_expr ty;
      (match ext with
      | Ast.Ext_none -> ()
      | Ast.Ext_C s -> o " = "; o (snd s) 
      | Ast.Ext_Asm s -> o " = asm "; o (snd s)
      | Ast.Ext_I -> o " = internal");
      nl();
      nl()

and sum td = 
  o "type ";
  (match td.td_args with
  | [] -> ()
  | l -> o "("; list id ", " l; o ")");
  id td.td_id;
  o " = ";
  push();
  nl();
  Utils.IMap.iter (
  fun _ (x, tyl) ->
    id x;
    (match tyl with
    | [] -> ()
    | l -> o " of "; type_expr_list l);
    nl()
 ) td.td_map;
  pop();
  nl();
  nl()

and record td = 
  o "type ";
  (match td.td_args with
  | [] -> ()
  | l -> o "("; list id ", " l; o ")");
  id td.td_id;
  o " = ";
  push();
  nl();
  Utils.IMap.iter (
  fun _ (x, tyl) ->
    id x;
    o ": ";
    type_expr_list tyl;
    nl()
 ) td.td_map;
  pop();
  nl();
  nl()

and type_expr = function
  | Tany -> o "_"
  | Tprim p -> type_prim p
  | Tvar x -> id x 
  | Tid x -> id x 
  | Tapply (x, tyl) -> type_expr_list tyl; o " "; id x
  | Tfun (k, tyl1, tyl2) -> 
      o "(";
      type_expr_list tyl1;
      (match k with
      | Ast.Lfun -> o " -> "
      | Ast.Cfun -> o " #-> ");
      type_expr_list tyl2;
      o ")"

and type_expr_list tyl = 
  match tyl with
  | [x] -> type_expr x
  | l -> o "("; list type_expr "," l; o ")"

and type_prim = function
  | Tunit -> o "unit"
  | Tbool -> o "bool"
  | Tchar -> o "char"
  | Tint -> o "int"
  | Tfloat -> o "float"
  | Tstring -> o "string"

and def (k, x, p, e) = 
  o "let ";
  id x; 
  pat p;
  o " = ";
  push();
  nl();
  tuple e

and pat ptl = list pat_tuple "|" ptl
and pat_tuple pel = list pat_el "," pel
and pat_el (_, p) = pat_ p
and pat_ = function 
  | Pany -> o "_"
  | Pid x -> id x
  | Pvalue v -> value v
  | Pvariant (v, p) -> 
      id v; o " "; pat p
  | Precord pfl -> 
      o "{ "; list pat_field "; " pfl; o " }"
  | Pas (x, p) -> o "("; pat p; o " as "; id x; o ")"

and pat_field = function
  | PFany -> o "_"
  | PFid x -> id x
  | PField (x, p) -> 
      id x; o " = "; pat p

and tuple t = 
  match t with
  | [x] -> expr x
  | l -> o "("; list expr ", " l; o ")"

and expr (_, e) = expr_ e
and expr_ = function
  | Eid x -> id x
  | Evalue v -> value v 
  | Evariant (x, t) -> id x; o " "; tuple t
  | Ebinop (bop, e1, e2) -> 
      o "("; expr e1; binop bop; expr e2; o ")"
  | Euop (uop, e) -> unop uop; expr e
  | Erecord fdl -> 
      o "{ ";
      fields fdl;
      o "}"
  | Ewith (e, fdl) -> 
      o "{";
      expr e;
      o " with ";
      fields fdl;
      o "}"
  | Efield (e, x) -> 
      expr e;
      o ".";
      id x
  | Ematch (e, al) -> 
      push();
      nl();
      o "(match ";
      tuple e;
      o " with";
      nl();
      List.iter action al;
      pop();
      nl();
      o ")"
  | Elet (p, e1, e2) -> 
      o "let "; pat p; o " = "; tuple e1; o " in";
      nl();
      tuple e2
  | Eif (e1, e2, e3) ->
      o "if "; expr e1; nl();
      o "then begin"; push(); nl(); tuple e2; nl(); o "end"; pop(); nl();
      o "else begin"; push(); nl(); tuple e3; nl(); o "end"; pop(); nl();
      pop();
      nl()
  | Eapply (tail, _, _, x, e) -> 
      if tail then o "tail ";
      id x; o " "; tuple e
  | Eseq (e1, e2) -> 
      expr e1; o ";"; nl();
      tuple e2
  | Efree (_, x) -> o "free "; id x
  | Eset (e1, e2, e3) -> 
      o "set "; tuple [e1;e2;e3]
  | Eget (e1, e2) -> o "get "; tuple [e1;e2]
  | Eswap (e1, e2, e3) -> 
      o "swap "; tuple [e1;e2;e3]
  | Epartial (e1, e2) -> 
      o "partial "; expr e1 ; tuple e2
  | Efun (k, pel, e) -> 
      o "(fun";
      pat_tuple pel;
      (match k with
      | Ast.Cfun -> o " #-> "
      | Ast.Lfun -> o " -> "
      );
      tuple e;
      o ")"

and fields fdl =
  list 
    (fun (x, e) ->
      id x; o " = "; tuple e
    ) "; " fdl

and action (p, e) =
  o "| ";
  pat p;
  o " -> ";
  push();
  nl();
  tuple e;
  pop();
  nl()

and value = function
  | Eunit -> o "()"
  | Ebool true -> o "true"
  | Ebool false -> o "false"
  | Eint s -> o s 
  | Efloat s -> o s 
  | Echar c -> o c 
  | Estring s -> o s

and binop = function
  | Ast.Eeq -> o " = "
  | Ast.Ediff -> o " <> "
  | Ast.Elt -> o " < "
  | Ast.Elte -> o " <= "
  | Ast.Egt -> o " > "
  | Ast.Egte -> o " >= "
  | Ast.Eplus -> o " + "
  | Ast.Eminus -> o " - "
  | Ast.Estar -> o " * "
  | Ast.Emod -> o " % "
  | Ast.Ediv -> o " / "
  | Ast.Eor -> o " || Ast."
  | Ast.Eand -> o " && "
  | Ast.Eband -> o " & "

and unop = function
  | Ast.Euminus -> o "-"
