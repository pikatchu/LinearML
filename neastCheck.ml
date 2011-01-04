open Utils
open Neast

(*****************************************************************************)
(*     Check that type applications are correct                              *)
(*****************************************************************************)

module TypeApplication: sig
  
  val check: Neast.program -> unit

end = struct

  let add = IMap.add 

  let predef = [
    Naming.tobs, 1;
    Naming.tshared, 1;
    Naming.toption, 1
  ]

  let add_predef acc (x, y) =
    add x (Pos.none, y) acc

  let empty = 
    let acc = IMap.empty in
    let acc = List.fold_left add_predef acc predef in 
    acc

  let get x t = IMap.find x t

  let rec check mdl = 
    let env = () in
    let acc = empty in
    let acc = List.fold_left (module_ env) acc mdl in
    List.iter (check_module acc) mdl

  and module_ env acc md = 
    let acc = List.fold_left (decl env) acc md.md_decls in
    acc

  and check_module env md = 
    List.iter (check_decl env) md.md_decls 

  and decl env acc = function
    | Dabstract (id, idl) -> 
	let p, x = id in
	let arity = List.length idl in
	let acc = add x (p, arity) acc in
	acc	
    | Drecord td
    | Dalgebric td -> 
	let acc = tdecl env acc td in
	acc
    | Dval _ -> acc

  and tdecl env acc td = 
    let p, x = td.td_id in
    let arity = List.length td.td_args in
    let acc = add x (p, arity) acc in
    acc

  and check_decl env = function
    | Dabstract _ -> ()
    | Drecord td
    | Dalgebric td -> tdef env td
    | Dval (_, ty, _) -> type_expr env ty

  and tdef env td = 
    IMap.iter (fun _ (_, tyl) -> type_expr_list env tyl) td.td_map

  and type_expr_list env (_, tyl) = List.iter (type_expr env) tyl
  and type_expr env (pos, ty) = type_expr_ env ty
  and type_expr_ env = function
    | Tany
    | Tprim _   | Tvar _  -> ()
    | Tid (p, x) -> 
	let pdef, arity = get x env in
	if arity <> 0
	then Error.type_arity p x 0 arity pdef
	else ()
    | Tapply ((p, x), ((_, l) as tl)) -> 
	let pdef, arity = get x env in
	let arg_length = List.length l in
	if arity <> arg_length 
	then Error.type_arity p x arg_length arity pdef
	else type_expr_list env tl 
    | Tfun (_, ty1, ty2) -> type_expr_list env ty1 ; type_expr_list env ty2

end 

(*****************************************************************************)
(*     Check that a new record defines all of its fields                     *)
(*****************************************************************************)

module RecordCheck = struct

  let rec program mdl = 
    let t = List.fold_left module_decl IMap.empty mdl in
    List.iter (module_ t) mdl

  and module_decl t md = 
    List.fold_left decl t md.md_decls 

  and module_ t md = 
    List.iter (def t) md.md_defs

  and decl t = function
    | Drecord td -> tdef t td
    | Dabstract _ -> t
    | Dalgebric _ -> t
    | Dval _ -> t

  and tdef t td = 
    let s = IMap.fold (fun x _ acc -> ISet.add x acc) td.td_map ISet.empty in
    ISet.fold (fun x acc -> IMap.add x s acc) s t

  and def t (_, _, e) = tuple t e
  and tuple t (_, e) = List.iter (expr t) e
  and expr t (p, e) = expr_ t p e
  and expr_ t p = function
  | Elet (_, e1, e2) -> tuple t e1 ; tuple t e2
  | Ebinop (_, e1, e2) -> expr t e1 ; expr t e2 
  | Efield (e, _) 
  | Euop (_, e) -> expr t e
  | Erecord [] -> assert false
  | Erecord (((_, x), _) :: _ as fdl) -> 
      List.iter (field t) fdl ;
      let s' = List.fold_left (
	fun acc ((_, x), _) -> ISet.add x acc
       ) ISet.empty fdl in
      let s = IMap.find x t in
      let diff = ISet.diff s s' in
      if ISet.is_empty diff 
      then ()
      else Error.undef_field p (Ident.to_string (ISet.choose diff))
  | Ematch (e, al) -> 
      tuple t e ;
      List.iter (action t) al
  | Eif (e1, e2, e3) -> 
      expr t e1 ; 
      tuple t e2 ; 
      tuple t e3
  | Eapply (_, e) -> tuple t e
  | Ewith (e, fdl) -> 
      List.iter (field t) fdl ;
      expr t e
  | Eseq (e1, e2) -> expr t e1 ; tuple t e2 
  | Evariant (_, e) -> tuple t e
  | Efree _ -> ()
  | Eobs _ -> ()
  | Evalue _ -> ()
  | Eid _ -> ()

  and field t (_, e) = tuple t e
  and action t (_, e) = tuple t e

end

(*****************************************************************************)
(*     Check that no field is of type unit                                   *)
(*****************************************************************************)
module CheckUnit = struct

  let rec program mdl = 
    List.iter module_ mdl 

  and module_ md = 
    List.iter decl md.md_decls

  and decl = function
    | Dalgebric td
    | Drecord td -> tdef td
    | Dabstract _
    | Dval _ -> ()

  and tdef td = 
    IMap.iter (
    fun _ (_, tyl) -> 
      List.iter type_expr (snd tyl)
   ) td.td_map 

  and type_expr (p, ty) = type_expr_ p ty
  and type_expr_ p = function 
    | Tprim Tunit -> Error.field_cannot_be_unit p
    | _ -> ()

end
    
(*****************************************************************************)
(*     Check external signatures                                             *)
(*****************************************************************************)
module CheckExternal = struct
  exception Error of Pos.t

  let rec program mdl = 
    List.iter module_ mdl

  and module_ md = 
    List.iter decl md.md_decls

  and decl = function
    | Dval (_, ty, Some _) -> 
	(try type_expr ty 
	with Error p ->
	  Error.invalid_extern_type (fst ty) p)
    | _ -> ()

  and type_expr (p, ty) = type_expr_ p ty
  and type_expr_ p = function
    | Tany
    | Tprim _ -> () (* TODO no bool ? *)
    | Tvar _
    | Tid _ -> ()
    | Tapply (_, tyl) -> type_expr_list tyl
    | Tfun (Ast.Lfun, _, _) -> raise (Error p) 
    | Tfun (_, tyl1, tyl2) -> type_expr_list tyl1 ; type_expr_list tyl2 

  and type_expr_list (_, l) = List.iter type_expr l

end


(* Entry point *)
let program p = 
  RecordCheck.program p ;
  TypeApplication.check p ;
  CheckUnit.program p ;
  CheckExternal.program p

