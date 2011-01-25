open Utils
open Nast

(*****************************************************************************)
(*   Module that mimics a topological sort  *)
(*   Except that when a cycle is encountered in raises an error  *)
(*   Given a set of type_expr, it checks that no definition in the set is  *)
(*   cyclic. The functions fid, fpath and ferror are past as parameters, to *)
(*   let the caller decide what to do with identifiers or paths. *)
(*   Another way to implement this could have been to build all the *)
(*   dependences as a graph. And then run a "generic" topological sort on *)
(*   this graph. I don't like this options because it doesn't spare much *)
(*   code while allocating a lot more. *)

module CheckTypeCycle: sig

  type status
  type fpath = (status -> id -> status) -> status -> id -> id -> status
  type fid = (status -> id -> status) -> status -> id -> status
  type ferror = id list -> status

  val decls: fpath -> fid -> ferror -> type_expr IMap.t -> unit

end = struct

  type color = 
    | Black
    | White 
    | Gray

  type status = color IMap.t
  type fpath = (status -> id -> status) -> status -> id -> id -> status
  type fid = (status -> id -> status) -> status -> id -> status
  type ferror = id list -> status

  type env = {
      decls: type_expr IMap.t ;
      fpath: fpath ;
      fid: fid ;
      ferror: ferror ;
    }

  let get_status t (_, x) = 
    try IMap.find x t 
    with Not_found -> White

  let rec get_cycle x acc = function
    | [] -> assert false
    | (_, y) as hd :: _ when y = x -> hd :: acc
    | id :: rl -> get_cycle x (id :: acc) rl

  let get_cycle t id = get_cycle (snd id) [id] t

  let rec decls fpath fid ferror t = 
    let env = { decls = t ; fpath = fpath ; fid = fid ; ferror = ferror } in
    ignore (IMap.fold (decl env []) t IMap.empty)

  and decl env path id (p, _) status = 
    tid env [] status (p, id)
	
  and type_expr env path status (_, ty) = 
    type_expr_ env path status ty

  and type_expr_ env path status = function
    | Tany
    | Tabstract
    | Tprim _ | Tvar _ -> status
    | Tpath (x, y) -> env.fpath (tid env path) status x y
    | Tid x -> env.fid (tid env path) status x
    | Tapply (ty, tyl) -> 
	let status = type_expr env path status ty in
	List.fold_left (type_expr env path) status tyl

    | Ttuple tyl -> 
	List.fold_left (type_expr env path) status tyl

    | Tfun (_, ty1, ty2) -> 
	let status = type_expr env path status ty1 in
	type_expr env path status ty2

    | Talgebric vl -> imfold (variant env path) status vl
    | Trecord fl -> imfold (field env path) status fl 
    | Tabbrev ty -> type_expr env path status ty
    | Tabs (idl, ty) -> type_expr env path status ty

  and variant env path status (_, ty_opt) =
    match ty_opt with
    | None -> status
    | Some x -> type_expr env path status x

  and field env path status (_, ty) = 
    type_expr env path status ty

  and tid env path status ((_, x) as id) =
    match get_status status id with
    | _ when not (IMap.mem x env.decls) -> status
    | Black -> status
    | Gray -> env.ferror (get_cycle path id)
    | White -> new_tid env path status id

  and new_tid env path status ((_, x) as id) = 
    let status = IMap.add x Gray status in
    let path = id :: path in
    let p, _ as ty = IMap.find x env.decls in
    let path = (p, x) :: path in
    let status = type_expr env path status ty in
    IMap.add x Black status


end

(*****************************************************************************)
(*     For each module: put all the type abbreviations in a set, check that *)
(*     there are no cycles. *)
(*****************************************************************************)

module Abbrev: sig

  val check: Nast.program -> Nast.type_expr IMap.t IMap.t

end = struct

  let fpath _ status _ _ = status
  let fid k status id = k status id

  let rec check mdl = 
    List.fold_left module_ IMap.empty mdl

  and module_ acc md = 
    let decls = List.fold_left decl IMap.empty md.md_decls in
    CheckTypeCycle.decls fpath fid (Error.cycle "type abbreviation") decls ;
    IMap.add (snd md.md_id) decls acc

  and decl decls = function
    | Dtype tyl -> List.fold_left type_def decls tyl
    | Dval _ -> decls

  and type_def decls (x, ty) = 
    let pos, id = x in
    match ty with
    | p, Tabs (idl, (_, Tabbrev ty)) ->
	IMap.add id (p, Tabs (idl, ty)) decls
    | _, Tabbrev ty -> IMap.add id (pos, snd ty) decls
    | _ -> decls
end

(*****************************************************************************)
(*     Puts all the type definitions of every module in a set.               *)
(*     Then checks that there are no cyclic type definition through modules. *)
(*****************************************************************************)

module ModuleTypes: sig

  val check: Nast.program -> unit

end = struct

  let fpath k st (p1,_) (p2, x) = 
    k st (Pos.btw p1 p2, x)

  let fid _ st _ = st

  let rec check mdl = 
    let decls = List.fold_left module_ IMap.empty mdl in
    CheckTypeCycle.decls fpath fid (Error.cycle "type definition") decls 

  and module_ acc md = 
    List.fold_left decl acc md.md_decls 

  and decl acc = function
    | Dtype tyl -> List.fold_left type_def acc tyl
    | Dval _ -> acc

  and type_def acc (x, ty) = 
    let pos, id = x in
    IMap.add id (pos, snd ty) acc
end

(*****************************************************************************)
(* Module checking the current implementation restrictions                   *)

module CheckRestrict = struct

  let error p = 
    Error.pos p ;
    Printf.printf "Feature not implemented\n" ;
    exit 2

  let rec program mdl = 
    List.iter module_ mdl

  and module_ md = 
    List.iter def md.md_defs

  and def (_, p, e) = 
    List.iter pat p ;
    expr e

  and pat (pos, p) = pat_ pos p
  and pat_ pos = function
    | Pvalue Eunit -> ()
    | Pvalue _ -> error pos
    | Precord pfl -> List.iter pat_field pfl 
    | Pbar _ -> error pos
    | Ptuple l -> List.iter pat l
    | _ -> ()

  and simpl_pat (pos, p) = simpl_pat_ pos p
  and simpl_pat_ pos = function
    | Pid _ -> ()
    | Pany _ -> ()
    | Ptuple l -> List.iter simpl_pat l
    | _ -> error pos

  and pat_field (_, pf) = pat_field_ pf
  and pat_field_ = function
    | PFany
    | PFid _ -> ()
    | PField (_, p) -> simpl_pat p

  and expr (p, e) = expr_ p e
  and expr_ p = function
    | Ebinop (_, e1, e2) -> expr e1 ; expr e2 
    | Euop (_, e) -> expr e 
    | Etuple el -> List.iter expr el 
    | Erecord fdl -> List.iter field fdl 
    | Efield _ -> () (* error p  *)
    | Ematch (e, pel) -> 
	expr e ;
	List.iter action pel
    | Elet (p, e1, e2) -> pat p ; expr e1 ; expr e2
    | Eif (e1, e2, e3) -> expr e1 ; expr e2 ; expr e3
    | Efun (pl, e) -> List.iter pat pl ; expr e
    | Eapply (e, el) -> expr e ; List.iter expr el 
    | Ewith (e, fdl) -> expr e ; List.iter field fdl 
    | Eseq (e1, e2) -> expr e1 ; expr e2
    | Eobs _ 
    | Efree _
    | Ecstr _ | Evalue _ | Eid _ -> ()

  and field (_, e) = expr e
  and action (p, e) = pat p ; expr e
	     
end

let program p = 
  CheckRestrict.program p ;
  ModuleTypes.check p
