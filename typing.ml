open Utils
open Ast

let program _ = ()
      
(*type env = { 
    tenv: etype_expr IMap.t ;
    venv: etype_expr IMap.t ;
    fenv: etype_expr IMap.t ;
    cenv: etype_expr IMap.t ;
    ptenv: bool IMap.t ;
  }

let primitive_types = [
  "int8" ; "int16" ; "int32" ; "int64" ;
  "bool" ; "float" ; "double" ;
]

let empty = 
  let add env x = IMap.add x true env in
  let ptenv = List.fold_left add IMap.empty primitive_types in
  { tenv = IMap.empty ;
    venv = IMap.empty ;
    fenv = IMap.empty ;
    cenv = IMap.empty ;
    ptenv = ptenv ;
  }
*)

(*module ExpandedType = struct

  type ty =
    | ETvar of id
    | ETtuple of ty list
    | ETfun of ty * ty
    | ETalgebric of id
    | ETrecord of id
    | ETexternal of id * id
    | ETabstract of id * ty list

  and tid = id * int

  type env = {
      decl: Ast.decl IMap.t ;
      aenv: ty option IMap.t IMap.t ;
      renv: ty IMap.t IMap.t ;
      tenv: ty IMap.t ;
    }

  let empty decl = {
    decl = decl ;
    aenv = IMap.empty ;
    renv = IMap.empty ;
    tenv = IMap.empty ;
  }

  let rec module_ decl_l = 
    let decls = List.fold_left add_decl IMap.empty decl_l in
    let env = empty decls in
    List.fold_left expand_decl env decl_l

  and add_decl env ty = 
    match ty with
    | Dalgebric ((id, _), _) 
    | Drecord ((id, _), _)
    | Dtype ((id, _), _) -> IMap.add id ty env
    | Dval _ -> env

  and expand_decl env = function
    | Dval _ -> env
    | d -> let env, _ = decl [] env d in env

  and decl path env = function
    | Dalgebric ((id, _), _) when IMap.mem id env.aenv -> 
	env, ETalgebric id

    | Dalgebric ((id, argl), vtl) ->
	let env, vtm = List.fold_left (variant path) (env, IMap.empty) vtl in
	let env = { env with aenv = IMap.add id vtm env.aenv } in
	env, ETalgebric id

    | Drecord ((id, _), _) when IMap.mem id env.renv -> 
	env, ETrecord id

    | Drecord ((id, argl), fdl) ->
	let env, ftm = List.fold_left (field path) (env, IMap.empty) fdl in
	let env = { env with renv = IMap.add id ftm env.renv } in
	env, ETrecord id
	    
    | Dtype ((id, argl), ty) -> 
	if List.mem id path 
	then failwith "cyclic type" ;
	type_expr (id :: path) env ty

    | Dval _ -> assert false

  and variant path (env, acc) (id, arg) = 
    if IMap.mem id acc
    then failwith "Multiple variants" ;
    let env, arg = 
      match arg with 
      | None -> env, None
      | Some arg -> 
	  let env, arg = type_expr path env arg in
	  env, Some arg in
    env, IMap.add id arg acc

  and field path (env, acc) (fid, ty) = 
    if IMap.mem fid acc
    then failwith "Multiple fields" ;
    let env, ty = type_expr path env ty in
    env, IMap.add fid ty acc

  and type_expr path env (_, x) = type_expr_ path env x
  and type_expr_ path env = function
    | Tvar id -> env, ETvar id
    | Tid id -> decl path env (IMap.find id env.decl)
    | Tapply _ -> (*of type_expr * type_expr list *) failwith "TODO"
    | Ttuple tyl -> 
	let env, tyl = List.fold_right (type_expr_acc path) tyl (env, []) in
	env, ETtuple tyl

    | Tpath (id1, id2) -> env, ETexternal (id1, id2)
    | Tfun (ty1, ty2) -> 
	let env, ty1 = type_expr path env ty1 in
	let env, ty2 = type_expr path env ty2 in
	env, ETfun (ty1, ty2)

  and type_expr_acc path ty (env, acc) = 
    let env, ty = type_expr path env ty in
    env, ty :: acc

end *)
(*

let rec decl env (genv, acc) (pos, x) = decl_ env (genv, acc) pos x
and decl_ env (genv, acc) pos = function
  | Dalgebric ((x, args), vl) -> 
      let genv, acc, vl = List.fold_left (variant env) (genv, acc, []) vl in
      let ty = pos, ETalgebric vl in
      let ty = match args with
      | [] -> ty 
      | l -> pos, ETlamb (ty, l) in
      genv, IMap.add (snd x) ty acc, ty

  | Drecord ((x, args), fdl) -> 
      let genv, acc, vl = List.fold_left (field env) (genv, acc, []) fdl in
      let ty = pos, ETrecord vl in
      let ty = match args with
      | [] -> ty 
      | l -> pos, ETlamb (ty, l) in
      genv, IMap.add (snd x) ty acc, ty

  | Dtype ((x, args), ty) -> 
      let genv, acc, ty = type_expr env (genv, acc) ty in
      let ty = match args with [] -> ty | l -> fst ty, ETlamb(ty, l) in
      genv, acc, ty
  | Dval _ -> assert false

and type_expr env (genv, acc) (pos, x) = type_expr_ env (genv, acc) pos x
and type_expr_ env (genv, acc) pos = function
  | Tvar x -> genv, acc, (pos, ETvar (x, 0))
  | Tid (pos, x) -> 
      (try genv, acc, IMap.find x acc with Not_found ->
	let ty = 
	  try IMap.find x env
	  with Not_found -> Error.unbound_name pos x in
	decl env (genv, acc) ty)

  | Tapply (ty, tyl) -> 
      let genv, acc, ty = type_expr env (genv, acc) ty in
      let genv, acc, tyl = List.fold_right (type_expr_acc env) tyl (genv, acc, []) in
      ignore (genv, acc, ty, tyl) ;
      failwith "TODO" 

  | Ttuple tyl ->
      let genv, acc, tyl = List.fold_right (type_expr_acc env) tyl (genv, acc, []) in
      genv, acc, (pos, ETtuple (List.flatten tyl))

  | Tpath ((pos1, x1), x2) -> 
      let sub, sub_acc = try IMap.find x1 genv with _ -> failwith "unbound module" in
      let sub_acc = type_expr sub (genv, sub_acc) (fst x2, (Tid x2)) in
      IMap.add x1 (sub, sub_acc) genv, acc, ty

  | Tfun (ty1, ty2) -> 
      let genv, acc, ty1 = type_expr env (genv, acc) ty1 in
      let genv, acc, ty2 = type_expr env (genv, acc) ty2 in
      genv, acc, (ETfun (ty1, ty2))

and variant env (genv, acc1, acc2) (id, ty) = 
  let acc1, ty = type_expr env (genv, acc1) ty in
  genv, acc1, (id, ty) :: acc2

and field env (genv, acc1, acc2) (id, ty) = 
  let acc1, ty = type_expr env (genv, acc1) ty in
  genv, acc1, (id, ty) :: acc2

and type_expr_acc env ty (genv, acc, l) = 
  let genv, acc, ty = type_expr env (genv,acc) ty in
  genv, acc, ty :: l

*)
(*
let id (_, x) = x
let pstring (_, x) = x

let rec program mdl = 
  let genv = List.fold_left module_header IMap.empty mdl in
  let mdl = List.map (module_ genv) mdl in
  mdl

and module_header genv md = 
  let env = List.fold_left decl_header empty md.md_decls in
  add md.md_name env genv

and decl_header env = function
  | Dalgebric ((x,_), vtl) as t -> 
      let env = List.fold_left (variant_type_header x) env vtl in
      { env with tenv = add x t env.tenv }
  | Drecord ((x,_), ftl) as t ->
      let env = List.fold_left (field_type_header x) env ftl in
      { env with tenv = add x t env.tenv }
  | Dtype (x, _) as t -> 
      { env with tenv = add (fst x) t env.tenv }
  | Dval (id, ty) -> 
      { env with venv = add id ty env.venv }

and field_type_header tid env (id, _) = 
  { env with fenv = add id tid env.fenv }

and variant_type_header tid env (id, _) = 
  { env with cenv = add id tid env.cenv }

and module_ genv md = 
  let _, env = find md.md_name genv in
  List.iter (decl genv env) md.md_decls ;
  let genv, defs, al = List.fold_left def (genv, IMap.empty, []) md.md_defs in
  let alias acc (x,y) = 
    let _, def = find y defs in
    add x def acc in
  let defs = List.fold_left alias defs al in
  IMap.fold (func genv env defs) env.venv []

and decl genv env = function
  | Dalgebric ((_,argl), vtl) -> 
      check_no_repetition argl ;
      List.iter (variant_type genv env) vtl
  | Drecord ((_,argl), ftl) -> 
      check_no_repetition argl ;
      List.iter (field_type genv env) ftl 
  | Dtype ((_, argl), ty) -> 
      check_no_repetition argl ;
      type_expr genv env ty
  | Dval (_, ty) -> type_expr genv env ty

and variant_type genv env (_, ty) = 
  match ty with
  | None -> ()
  | Some ty -> type_expr genv env ty

and field_type genv env (_, ty) = type_expr genv env ty

and type_expr genv env (pos, ty) = type_expr_ genv env pos ty
and type_expr_ genv env pos = function
  | Tvar x -> Tast.Tvar x
  | Tid (_, x) when IMap.mem x env.ptenv -> ()
  | Tid id -> ignore (find id env.tenv)
  | Tapply (ty, tyl) -> 
      check_type_arity genv env pos ty tyl ;
      List.iter (type_expr genv env) tyl
  | Ttuple ty_l -> List.iter (type_expr genv env) ty_l
  | Tpath (id1, id2) -> ignore (find_path id1 id2 genv)
  | Tfun (ty1, ty2) -> 
      type_expr genv env ty1 ;
      type_expr genv env ty2 


and def (genv, acc1, acc2) = function
  | Dmodule (id1, id2) ->
      let _, md = find id2 genv in
      add id1 md genv, acc1, acc2
  | Dlet (x, pl, e)
  | Dletrec (x, pl, e) -> genv, add x (pl, e) acc1, acc2
  | Dalias (x, y) -> genv, acc1, (x, y) :: acc2

and func genv env defs id (pos, ty) acc = 
  let _, (argl, e) = IMap.find id defs in
  let targ, te = func_type env pos ty in
  let targl = tuple_type env targ in
  let tenv = List.fold_left2 pat env.venv argl targl in
  ignore tenv ;
  []
  
and pat env (pos, p) ty = pat_ env pos p ty
and pat_ env pos p ty =
  let ty = expand_type env ty in
  ignore ty
  match p, ty with
  | Pany, _ -> env 
  | Punit
  | Pid of id
  | Pchar of string
  | Pint of string
  | Pbool of bool
  | Pfloat of string
  | Pstring of string
  | Pcstr of id 
  | Pvariant of id * pat
  | Pprod of pat * pat
  | Pstruct of pat_field list
  | Pbar of pat * pat
  | Ptuple of pat list
  | Pderef of id * pat

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
  | Eint of string
  | Efloat of string
  | Eeq of expr * expr
  | Elt of expr * expr
  | Elte of expr * expr
  | Egt of expr * expr
  | Egte of expr * expr
  | Eplus of expr * expr
  | Eminus of expr * expr
  | Estar of expr * expr
  | Eseq of expr * expr
  | Euminus of expr
  | Etuple of expr list
  | Ecstr of id
  | Echar of pstring
  | Estring of pstring
  | Estruct of (id * expr) list 
  | Etyped of expr * type_expr
  | Ederef of expr * expr 
  | Epath of expr * id 
  | Ematch of expr * (pat * expr) list
  | Elet of pat * expr * expr
  | Eletrec of pat * expr * expr
  | Eif of expr * expr * expr 
  | Efun of pat list * expr 
  | Eapply of expr * expr list
*)
