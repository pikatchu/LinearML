(* Module optimizing pattern-match on trees with only two possible 
   cases, one scalar, the other one pointer. 
*)

open Utils
open Ist
open Est

module Env = struct

  let rec program mdl = 
    let t = ISet.empty in
    let t = List.fold_left module_ t mdl in
    t

  and module_ t md = 
    List.fold_left decl t md.md_decls

  and decl t = function
    | Dalgebric td -> 
	if tdef t td
	then ISet.add td.td_id t
	else t
    | _ -> t

  and tdef t td = 
    let vl = IMap.fold (
      fun x (x, args) acc -> (x, args) :: acc
     ) td.td_map [] 
    in
    match vl with
    | [_, [] ; _, _ :: _ ]
    | [_, _ :: _  ; _, []] -> true
    | _ -> false

end

(*let rec program mdl = 
  let t = Env.program mdl in
  List.rev_map (module_ t) mdl

and module_ t md = 
  let defs = List.map (def t) md.md_defs in
  { md with md_defs = defs }

and def t df = 
  let bll = List.map (block t) df.df_body in
  { df with df_body = bll }

and block t bl = 
  let rt = ret t bl.bl_ret in
  { bl with bl_ret = rt }

and ret t = function
  | Lreturn of ty_idl
  | Return of ty_idl
  | Jump of label
  | If of ty_id * label * label
  | Match 
      ([v], 
       [[Pvariant (x, [])], a ;
	[Pvariant (_, 
	   of ty_idl * (pat * label) list

and phi = id * Ist.type_expr * (id * label) list

and equation = ty_idl * expr

and expr = 
  | Eid of id
  | Evalue of Ist.value
  | Evariant of id * ty_idl
  | Ebinop of Ast.bop * ty_id * ty_id
  | Euop of Ast.uop * ty_id
  | Erecord of (id * ty_idl) list 
  | Ewith of ty_id * (id * ty_idl) list 
  | Efield of ty_id * id 
  | Ematch of ty_idl * (pat * expr) list
  | Ecall of label
  | Eapply of id * ty_idl
  | Eseq of ty_id * ty_idl
  | Eif of ty_id * label * label

*)
