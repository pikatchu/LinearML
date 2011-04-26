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
open Ist

type value =
  | Unit
  | Bool of bool
  | Char of char
  | Int of int
  | Float of float
  | String of string
  | Array of value array
  | Variant of id * value list
  | Record of value list IMap.t
  | Fun of pat * tuple
  | Prim1 of (value -> value)
  | Prim2 of (value -> value -> value)

module Print = struct

  let rec value o = function
  | Unit -> o "()"
  | Bool true -> o "true"
  | Bool false -> o "false"
  | Char c ->
      let s = "'.'" in
      s.[1] <- c;
      o s
  | Int n -> o (string_of_int n)
  | Float f -> o (string_of_float f)
  | String s -> o ("\""^String.escaped s^"\"")
  | Array a -> o "[|" ; array o a 0 (Array.length a - 1); o "|]"
  | Variant (x, []) -> o (Ident.to_string x)
  | Variant (x, vl) ->
      o (Ident.to_string x);
      o "(";
      value_list o vl;
      o ")"
  | Record r ->
      o "{";
      IMap.iter (field o) r;
      o "}"
  | Fun _
  | Prim1 _
  | Prim2 _ -> o "fun"

  and array o a i iend =
    if i = iend
    then value o a.(i)
    else begin
      value o a.(i);
      o ";";
      array o a (i+1) iend
    end

  and value_list o vl =
    match vl with
    | [] -> ()
    | [x] -> value o x
    | x :: rl -> value o x ; o ", "; value_list o rl

  and field o s vl =
    o (Ident.to_string s); o " = "; value_list o vl;
    o "; "

end

module Genv = struct

  let make_prims env =
    let env = ref env in
    let register x v =
      env := IMap.add x v !env
    in
    register Naming.bnot (Prim1
    (function
      | Bool b -> Bool (not b)
      | _ -> assert false
   ));
    register Naming.alength (Prim1
    (function
      | Array a -> Int (Array.length a)
      | _ -> assert false
   ));
    register Naming.imake (Prim2
    (fun size v ->
      match size, v with
      | Int size, v -> Array (Array.make size v)
      | _ -> assert false
   ));
    register Naming.imake (Prim2
    (fun size v ->
      match size, v with
      | Int size, v -> Array (Array.make size v)
      | _ -> assert false
   ));
    !env

  let rec program mdl =
    let env = IMap.empty in
    List.fold_left module_ env mdl

  and module_ env md =
    List.fold_left def env md.md_defs

  and def env (_, x, p, t) =
    IMap.add x (Fun (p, t)) env
end

let rec program root_id mdl =
  let env = Genv.program mdl in
  (match root_id with
  | None -> failwith "main not found"
  | Some (_, id) ->
      match IMap.find id env with
      | Fun (_, e) ->
	  let v = tuple env e in
	  let o = output_string stdout in
	  Print.value_list o v
      | _ -> assert false)

and pat env ptl vl =
  match ptl with
  | [] ->
      if vl = []
      then env
      else raise Exit
  | pt :: rl ->
      (try pat_tuple env pt vl
      with Exit -> pat env rl vl)

and pat_tuple env pel vl =
  List.fold_left2 pat_el env pel vl

and pat_el env (_, p) v =
  pat_ env p v

and pat_ env p v =
 match p with
  | Pany -> env
  | Pid x -> IMap.add x v env
  | Pvalue _ -> env
  | Pvariant (x, p) ->
      (match v with
      | Variant (y, vl) when x = y ->
	  pat env p vl
      | _ -> raise Exit)
  | Precord pfl ->
      (match v with
      | Record fds ->
	  List.fold_left (pat_field fds) env pfl
      | _ -> raise Exit)
  | Pas (x, p) ->
      let env = pat env p [v] in
      IMap.add x v env

and pat_field fds env = function
  | PFany -> env
  | PFid x -> IMap.add x (Record fds) env
  | PField (x, p) ->
      let fd = IMap.find x fds in
      pat env p fd

and tuple env el =
  List.flatten (List.map (expr env) el)

and expr env (_, e) = expr_ env e
and expr_ env = function
  | Eid x ->
      (try [IMap.find x env]
      with Not_found ->
	let x = Ident.to_string x in
	Printf.fprintf stderr "Not an interpreted value: %s" x;
	exit 2)
  | Evalue v -> [value v]
  | Evariant (x, e) ->
      let e = tuple env e in
      [Variant (x, e)]
  | Ebinop (bop, e1, e2) ->
      let e1 = List.hd (expr env e1) in
      let e2 = List.hd (expr env e2) in
      [binop bop e1 e2]
  | Euop (uop, e) ->
      let e = List.hd (expr env e) in
      [unop uop e]
  | Erecord fdl ->
      let fields = List.fold_left (field env) IMap.empty fdl in
      [Record fields]
  | Ewith (e, fdl) ->
      let e = expr env e in
      (match e with
      | [Record fds] ->
	  let fields = List.fold_left (field env) fds fdl in
	  [Record fields]
      | _ -> assert false)
  | Efield (e, v) ->
      (match expr env e with
      | [Record fds] -> IMap.find v fds
      | _ -> assert false)
  | Ematch (e, al) ->
      actions env (tuple env e) al
  | Elet (p, e1, e2) ->
      let env = pat env p (tuple env e1) in
      tuple env e2
  | Eif (c, e1, e2) ->
      (match expr env c with
      | [Bool true] -> tuple env e1
      | [Bool false] -> tuple env e2
      | _ -> assert false)
  | Eapply (_, _, _, f, e) ->
      (match IMap.find f env with
      | Fun (p, b) ->
	  let env = pat env p (tuple env e) in
	  tuple env b
      | _ -> assert false)
  | Eseq (e1, e2) ->
      let _ = expr env e1 in
      tuple env e2
  | Efree _ -> [Unit]
  | Eset (e1, e2, e3) ->
      [match expr env e1, expr env e2 with
      | [Array a], [Int i] ->
	  let v = List.hd (expr env e3) in
	  a.(i) <- v ;
	  Unit
      | _ -> assert false]
  | Eget (e1, e2) ->
      [match expr env e1, expr env e2 with
      | [Array a], [Int i] -> a.(i)
      | _ -> assert false]
  | Eswap (e1, e2, e3) ->
      [match expr env e1, expr env e2 with
      | [Array a], [Int i] ->
	  let res = a.(i) in
	  a.(i) <- List.hd (expr env e3) ;
	  res
      | _ -> assert false]
  | Epartial _ -> failwith "TODO partial"
  | Efun (_, pel, e) -> failwith "TODO fun"

and field env acc (x, e) =
  let e = tuple env e in
  IMap.add x e acc

and value = function
  | Eunit -> Unit
  | Ebool b -> Bool b
  | Eint n -> Int (int_of_string n)
  | Efloat f -> Float (float_of_string f)
  | Echar c -> Char (c.[0])
  | Estring s -> String s

and binop bop e1 e2 =
  match bop with
  | Ast.Eeq -> Bool (e1 = e2)
  | Ast.Ediff -> Bool (e1 <> e2)
  | Ast.Elt -> Bool (e1 < e2)
  | Ast.Elte -> Bool (e1 <= e2)
  | Ast.Egt -> Bool (e1 > e2)
  | Ast.Egte -> Bool (e1 >= e2)
  | Ast.Eor
  | Ast.Eand as op ->
      Bool (bool_op op e1 e2)
  | Ast.Eplus
  | Ast.Eminus
  | Ast.Estar
  | Ast.Emod
  | Ast.Ediv as op ->
      Int (int_op op e1 e2)
  | Ast.Eband -> failwith "TODO"

and bool_op op e1 e2 =
  match e1, e2 with
  | Bool b1, Bool b2 ->
      (match op with
      | Ast.Eor -> b1 || b2
      | Ast.Eand -> b1 && b2
      | _ -> assert false
      )
  | _ -> assert false

and int_op op e1 e2 =
  match e1, e2 with
  | Int n1, Int n2 ->
      (match op with
      | Ast.Eplus -> n1 + n2
      | Ast.Eminus -> n1 - n2
      | Ast.Estar -> n1 * n2
      | Ast.Emod -> n1 mod n2
      | Ast.Ediv -> n1 / n2
      | _ -> assert false
      )
  | _ -> assert false

and unop op e =
  match e with
  | Int n -> Int (-n)
  | _ -> assert false

and actions env e al =
  match al with
  | [] -> failwith "pattern-match failed"
  | (p, a) :: rl ->
      (try
	let env = pat env p e in
	tuple env a
      with Exit -> actions env e rl)

