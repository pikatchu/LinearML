open Utils
open Nast

module Debug = struct
  open Tast

  let id o (_, x) = o (Ident.debug x)

  let rec type_expr o (_, ty) = type_expr_ o ty
  and type_expr_ o ty = 
    let k = type_expr o in
    match ty with
    | Tany -> o "Tany"
    | Tunit -> o "Tunit"
    | Tbool -> o "Tbool"
    | Tint32 -> o "Tint32"
    | Tfloat -> o "Tfloat"
    | Tvar x -> o "Tvar" ; o "(" ;  id o x ; o ")"
    | Tid x -> o "Tid" ; o "(" ;  id o x ; o ")"
    | Tapply (ty, tyl) -> o "Tapply" ; o "(" ;  k ty ; o "," ; list o tyl; o ")"
    | Ttuple tyl -> o "Ttuple" ; o "(" ;  list o tyl; o ")"
    | Tpath (id1, id2) -> o "Tpath" ; o "(" ; id o id1 ; o "." ; id o id2 ; o ")"
    | Tfun (ty1, ty2) -> o "Tfun" ; o "(" ;  k ty1 ; o "->" ; k ty2; o ")"
    | Talgebric vl -> o "Talgebric" ; o "[" ; imiter (variant o) vl ; o "]"
    | Trecord fdl -> o "Trecord" ; o "{" ;  imiter (field o) fdl; o "}"
    | Tabbrev ty -> o "Tabbrev" ; o "(" ; k ty ; o ")"
    | Tabs (idl, ty) -> o "Tabs" ; o "(" ; tvar o idl ; o ": " ; k ty; o ")"
    | Tdecl x -> o "Tdecl" ; o "(" ; id o x ; o ")"

  and tvar o = function
    | [] -> assert false
    | [x] -> id o x
    | x :: rl -> id o x ; o "," ; tvar o rl

  and list o = function
    | [] -> ()
    | [x] -> type_expr o x
    | x :: rl -> type_expr o x ; o "," ; list o rl

  and variant o (x, y) = 
    id o x ; o " of " ; 
    (match y with None -> () | Some ty -> type_expr o ty) ;
    o "|"

  and field o (x, y) = id o x ; o ":" ; type_expr o y ; o ";"

  let o = output_string stdout
  let nl o = o "\n"
  let type_expr ty = type_expr o ty ; nl o

end

module Subst = struct

  let rec type_expr env (p, ty) = 
    match ty with
    | Tvar (_, x) when IMap.mem x env -> IMap.find x env
    | _ -> p, type_expr_ env ty

  and type_expr_ env = function
  | Tunit | Tbool | Tpath _
  | Tint32 | Tfloat | Tid _ | Tvar _ as x -> x
  | Tapply (ty, tyl) -> Tapply (type_expr env ty, List.map (type_expr env) tyl)
  | Ttuple tyl -> Ttuple (List.map (type_expr env) tyl)
  | Tfun (ty1, ty2) -> Tfun (type_expr env ty1, type_expr env ty2)
  | Talgebric vl -> Talgebric (IMap.map (variant env) vl)
  | Trecord fdl -> Trecord (IMap.map (field env) fdl)
  | Tabbrev ty -> Tabbrev (type_expr env ty)
  | Tabs (vl, ty) ->
      let xl = List.map snd vl in
      let env = List.fold_right IMap.remove xl env in
      Tabs (vl, type_expr env ty)

  and variant env (id, ty_opt) = 
    id, match ty_opt with 
    | None -> None
    | Some ty -> Some (type_expr env ty)

  and field env (id, ty) = id, type_expr env ty
end

module TupleExpand = struct

  let rec type_expr (p, ty) = 
    match type_expr_ [] (p, ty) with
    | [x] -> x
    | l -> (p, Ttuple (List.rev l))

  and type_expr_ acc (p, ty) = 
    match ty with
    | Tunit | Tbool | Tint32
    | Tfloat | Tvar _ | Tid _ 
    | Tpath _ as x -> (p, x) :: acc
    | Ttuple tyl -> List.fold_left type_expr_ acc tyl
    | Tapply (ty, tyl) -> 
	let tyl = List.map type_expr tyl in
	(p, Tapply (ty, tyl)) :: acc

    | Tfun (ty1, ty2) -> 
	let ty1 = type_expr ty1 in
	let ty2 = type_expr ty2 in
	(p, Tfun (ty1, ty2)) :: acc

    | Talgebric vl -> (p, Talgebric (IMap.map variant vl)) :: acc
    | Trecord fdl -> (p, Trecord (IMap.map field fdl)) :: acc
    | Tabbrev ty -> type_expr_ acc ty
    | Tabs (idl, ty) -> 
	let ty = type_expr ty in
	(p, Tabs (idl, ty)) :: acc

  and variant (id, ty_opt) = 
    match ty_opt with
    | None -> id, None
    | Some ty -> id, Some (type_expr ty)

  and field (id, ty) = id, type_expr ty
end


module ExpandAbbrevs = struct

  let check_abs id (p, ty) = 
    match ty with
    | Tabs (idl, _) -> Error.type_expects_arguments id (List.length idl) p
    | _ -> ()

  let rec program p = 
    let abbr = NastCheck.Abbrev.check p in
    let abbr = IMap.fold (fun _ x acc -> IMap.fold IMap.add x acc) abbr IMap.empty in
    let _, p = lfold (module_ abbr) IMap.empty p in
    p

  and module_ abbr mem md = 
    let mem, decls = lfold (decl abbr) mem md.md_decls in
    mem, { md with md_decls = decls }

  and decl abbr mem = function
    | Dtype tdl -> 
	let mem, tdl = List.fold_left (type_def abbr) (mem, []) tdl in
	mem, Dtype tdl 

    | Dval (id, ty) -> 
	let mem, ty = type_expr abbr mem ty in
	let ty = TupleExpand.type_expr ty in
	mem, Dval (id, ty)

  and type_def abbr (mem, acc) (id, ty) = 
    let mem, ty = type_expr abbr mem ty in
    let ty = TupleExpand.type_expr ty in
    if IMap.mem (snd id) abbr
    then mem, acc
    else mem, (id, ty) :: acc

  and type_expr abbr mem (p, ty) = 
    let mem, ty = type_expr_ abbr mem p ty in
    mem, (p, ty)

  and type_expr_ abbr mem p = function
    | Tunit | Tbool 
    | Tint32 | Tfloat | Tvar _ as x -> mem, x 

    | (Tpath (_, (_, x)) 
    | Tid (_, x)) when IMap.mem x mem -> 
	mem, snd (IMap.find x mem)

    | (Tpath (_, ((_, x) as id)) 
    | Tid ((_, x) as id)) when IMap.mem x abbr ->
	let mem, ty = type_expr abbr mem (IMap.find x abbr) in
	let mem = IMap.add x ty mem in
	check_abs id ty ;
	mem, (snd ty)

    | Tpath _ | Tid _ as x -> mem, x

    | Tapply ((p, Tpath ((p1,_), (p2, x))), ty) when IMap.mem x abbr -> 
	let px = Pos.btw p1 p2 in
	type_expr_ abbr mem p (Tapply ((p, Tid (px, x)), ty))

    | Tapply ((p, Tid (px, x)), tyl) when IMap.mem x abbr -> 
	let mem, tyl = lfold (type_expr abbr) mem tyl in
	let pdef, _ as ty = IMap.find x abbr in
	let args, ty = match ty with _, Tabs (vl, ty) -> vl, ty
	| _ -> Error.not_expecting_arguments px x pdef in
	let mem, ty = type_expr abbr mem ty in
	let size1 = List.length tyl in
	let size2 = List.length args in
	if size1 <> size2
	then Error.type_arity px x size1 size2 pdef ;
	let args = List.map snd args in
	let subst = List.fold_right2 IMap.add args tyl IMap.empty in
	let ty = Subst.type_expr subst ty in
	mem, snd ty

    | Tapply (ty, tyl) -> 
	let mem, ty = type_expr abbr mem ty in
	let mem, tyl = lfold (type_expr abbr) mem tyl in
	mem, Tapply (ty, tyl)

    | Ttuple tyl -> 
	let mem, tyl = lfold (type_expr abbr) mem tyl in
	mem, Ttuple tyl

    | Tfun (ty1, ty2) -> 
	let mem, ty1 = type_expr abbr mem ty1 in
	let mem, ty2 = type_expr abbr mem ty2 in
	mem, Tfun (ty1, ty2)

    | Talgebric vl -> 
	let mem, vl = imlfold (variant abbr) mem vl in
	mem, Talgebric vl 

    | Trecord fdl -> 
	let mem, fdl = imlfold (field abbr) mem fdl in
	mem, Trecord fdl 

    | Tabbrev ty -> 
	let mem, ty = type_expr abbr mem ty in
	mem, snd ty

    | Tabs (idl, ty) -> 
	let mem, ty = type_expr abbr mem ty in
	mem, Tabs (idl, ty)

  and variant abbr mem (id, ty_opt) = 
    match ty_opt with
    | None -> mem, (id, None)
    | Some ty -> 
	let mem, ty = type_expr abbr mem ty in
	mem, (id, Some ty)

  and field abbr mem (id, ty) = 
    let mem, ty = type_expr abbr mem ty in
    mem, (id, ty)

end

(*let rec instantiate (p, ty) = 
  p, match ty with
  | Tabs (vl, ty) -> 
      let id (p, x) = p, Ident.make (Ident.to_string x) in
      let nvl = List.map id vl in
      let bind (_, x) ((p, _) as y) acc = IMap.add x (p, Tvar y) acc in
      let subst = List.fold_right2 bind vl nvl IMap.empty in
      Tabs (nvl, Subst.type_expr subst ty)
  | _ -> ty *)

module Unify = struct
  open Tast

  let rec type_expr (p1, ty1) (p2, ty2) = 
    p1, match ty1, ty2 with
    | Tunit, Tunit -> Tunit
    | Tbool, Tbool -> Tbool
    | Tint32, Tint32 -> Tint32
    | Tfloat, Tfloat -> Tfloat
    | Tvar (_, x1), Tvar (_, x2) when x1 = x2 -> ty1
    | Tpath (_, (_, x1)), Tpath (_, (_, x2))
    | Tid (_, x1), Tid (_, x2) when x1 = x2 -> ty1
    | Tapply (ty1, tyl1), Tapply (ty2, tyl2) -> 
	(* TODO check arity ? *)
	let ty = type_expr ty1 ty2 in
	let tyl = type_expr_list tyl1 tyl2 in
	Tapply (ty, tyl)

    | Ttuple tyl1, Ttuple tyl2 -> Ttuple (type_expr_list tyl1 tyl2)
    | Tfun (targ1, tret1), Tfun (targ2, tret2) -> 
	let targ = type_expr targ1 targ2 in
	let tret = type_expr tret1 tret2 in
	Tfun (targ, tret)

    | Tabs (vl1, ty1), Tabs (vl2, ty2) -> 
	let ty = type_expr ty1 ty2 in
	let vl = type_id_list vl1 vl2 in
	Tabs (vl, ty)

    | Talgebric vl1, Talgebric vl2 -> 
	let vl = IMap.fold (variant vl2) vl1 vl2 in
	Talgebric vl

    | Trecord fdl1, Trecord fdl2 ->
	(* TODO make sure they have the same fields defined *)
	let fdl = IMap.fold field fdl1 fdl2 in
	Trecord fdl

    | Tabbrev _, _ | _, Tabbrev _ -> assert false
    | _ -> 
	Debug.type_expr (p1, ty1) ;
	Debug.type_expr (p2, ty2) ;
	Error.unify p1 p2

  and variant vm x (cstr1, ty1) acc =
    try 
      let cstr2, ty2 = IMap.find x vm in
      assert (snd cstr1 = snd cstr2) ;
      let ty = type_expr_opt ty1 ty2 in
      IMap.add x (cstr1, ty) acc
    with 
    | Not_found -> IMap.add x (cstr1, ty1) acc

  and field x (fd1, ty1) acc = 
    try 
      let fd2, ty2 = IMap.find x acc in
      let ty = type_expr ty1 ty2 in
      IMap.add x (fd1, ty) acc
    with 
    | Not_found -> assert false

  and type_expr_opt ty1 ty2 = 
    match ty1, ty2 with
    | None, None -> None
    | Some ty1, Some ty2 -> Some (type_expr ty1 ty2)
    | _ -> failwith "TODO Unify.type_expr_opt error message"

  and type_expr_list tyl1 tyl2 = 
    match tyl1, tyl2 with
    | [], [] -> []
    | [], _ | _, [] -> 
	(* Tuples and abbreviations have been expanded *)
	(* In case of application arity is checked before unification *)
	assert false
    | x1 :: rl1, x2 :: rl2 -> type_expr x1 x2 :: type_expr_list rl1 rl2

  and type_id_list tyl1 tyl2 = 
    match tyl1, tyl2 with
    | [], [] -> []
    | [], _ | _, [] -> assert false
    | (p1, x1) :: rl1, (p2, x2) :: rl2 ->
	if x1 <> x2 
	then Error.unify p1 p2
	else type_id_list rl1 rl2
end

module Env = struct

  let get_type env (p, x) = try IMap.find x env with Not_found -> 
    Tast.Tfun ((p, Tast.Tunit), (p, Tast.Tint32))

  let add_type env (_, x) ty = IMap.add x ty env

  let rec make mdl = 
    List.fold_left module_ IMap.empty mdl 

  and module_ env md = 
    let env = List.fold_left decl env md.md_decls in
    List.fold_left def env md.md_defs

  and def env = function
  | Dlet (x, (args, e)) -> IMap.add of id * pat list * expr
  | Dletrec of (id * pat list * expr) list
  | Dalias of id * id


end

let id x = x

let rec program mdl = 
  NastCheck.ModuleTypes.check mdl ;
  let mdl = ExpandAbbrevs.program mdl in
  List.map (module_ IMap.empty) mdl 

and module_ env md = {
    Tast.md_id = md.md_id ;
    Tast.md_decls = List.map (decl env) md.md_decls ;
    Tast.md_defs = List.map (def env) md.md_defs ;
  }

and decl env = function
  | Dtype tdl -> Tast.Dtype (List.map (tdef env) tdl)
  | Dval (id, ty) -> Tast.Dval (id, type_expr env ty)

and tdef env (x, ty) = id x, type_expr env ty

and type_expr env (p, ty) = p, type_expr_ env ty
and type_expr_ env = function
  | Tunit -> Tast.Tunit
  | Tbool -> Tast.Tbool
  | Tint32 -> Tast.Tint32
  | Tfloat -> Tast.Tfloat
  | Tvar x -> Tast.Tvar (id x)
  | Tid x -> Tast.Tid (id x)
  | Tpath (x, y) -> Tast.Tpath (id x, id y)
  | Tapply (ty, tyl) -> Tast.Tapply (type_expr env ty, type_expr_list env tyl)
  | Ttuple tyl -> Tast.Ttuple (type_expr_list env tyl)
  | Tfun (ty1, ty2) -> Tast.Tfun (type_expr env ty1, type_expr env ty2)
  | Talgebric vl -> Tast.Talgebric (IMap.map (variant env) vl)
  | Trecord fdl -> Tast.Trecord (IMap.map (field env) fdl)
  | Tabbrev _ -> assert false
  | Tabs (idl, ty) -> Tast.Tabs (List.map id idl, type_expr env ty)

and variant env (x, ty_opt) = 
  match ty_opt with
  | None -> id x, None
  | Some ty -> id x, Some (type_expr env ty)

and field env (x, ty) = id x, type_expr env ty

and type_expr_list env l = List.map (type_expr env) l

and def env = function
  | Dmodule _ -> assert false
  | Dlet (id, pl, e) -> 
      let fty = Env.get_type env id in
      let tyl, rty = fun_type fty in
      let env = simpl_pat_l env tyl pl in
      let ty, _ = expr env e in
      Debug.type_expr ty ;
      Tast.Dlet (id, [], (fst id, Tast.Eunit))
     
  | _ -> failwith "TODO"
(*  | Dletrec of (id * pat list * expr) list
  | Dalias of id * id *)

and fun_type = function
  | Tast.Tfun ((_, Tast.Ttuple ty1), ty2) -> ty1, ty2
  | Tast.Tfun (ty1, ty2) -> [ty1], ty2
  | _ -> failwith "TODO fun_type should be a function"

and simpl_pat_l env tyl1 tyl2 = 
  match tyl1, tyl2 with
  | [], [] -> env
  | [], _ | _, [] -> failwith "TODO simpl_pat_l wrong arity"
  | x1 :: rl1, x2 :: rl2 -> 
      let env = simpl_pat env x1 x2 in
      simpl_pat_l env rl1 rl2

and simpl_pat env (p1, ty) (p2, p) = 
  match ty, p with
  | Tast.Tunit, Punit -> env
  | _, Pany -> env
  | _, Pid x -> Env.add_type env x ty
  | Tast.Ttuple tyl, Ptuple pl -> simpl_pat_l env tyl pl
  | _ -> failwith "either simpl_pat badly typed or assert false ;-)"

(*and pat = Pos.t * pat_
and pat_ = 
  | Punit
  | Pany 
  | Pid of id
  | Pchar of string
  | Pint of string
  | Pbool of bool
  | Pfloat of string
  | Pstring of string
  | Pcstr of id 
  | Pvariant of id * pat
  | Pecstr of id * id
  | Pevariant of id * id * pat
  | Precord of pat_field list
  | Pbar of pat * pat
  | Ptuple of pat list 

and pat_field = Pos.t * pat_field_
and pat_field_ = 
  | PFany
  | PFid of id 
  | PField of id * pat *)

and unify ty1 ty2 = snd (Unify.type_expr ty1 ty2)

and expr env (p, e) = 
  match e with
  | Elet (p, e1, e2) -> 
      let ty, e1 = expr env e1 in
      (* TODO ty must be an expanded tuple *)
      (* TODO not simpl_pat but pat *)
      let env = simpl_pat_l env [ty] [p] in
      expr env e2
  | _ ->
      let ty, e = expr_ env e in
      (p, ty), (p, e)

and expr_ env = function
  | Eunit -> Tast.Tunit, Tast.Eunit
  | Ebool b -> Tast.Tbool, Tast.Ebool b
  | Eid x -> Env.get_type env x, Tast.Eid x
  | Eint n -> Tast.Tint32, Tast.Eint n 
  | Efloat f -> Tast.Tfloat, Tast.Efloat f
  | Eeq (e1, e2) -> 
      let ty1, e1 = expr env e1 in
      let ty2, e2 = expr env e2 in
      ignore (unify ty1 ty2) ;
      Tast.Tbool, Tast.Eeq (e1, e2)

  | Elt (e1, e2) ->
      let ty1, e1 = expr env e1 in
      let ty2, e2 = expr env e2 in
      ignore (unify ty1 ty2) ;
      Tast.Tbool, Tast.Elt (e1, e2)

  | Elte (e1, e2) ->
      let ty1, e1 = expr env e1 in
      let ty2, e2 = expr env e2 in
      ignore (unify ty1 ty2) ;
      Tast.Tbool, Tast.Elte (e1, e2)

  | Egt (e1, e2) ->
      let ty1, e1 = expr env e1 in
      let ty2, e2 = expr env e2 in
      ignore (unify ty1 ty2) ;
      Tast.Tbool, Tast.Egt (e1, e2)

  | Egte (e1, e2) ->
      let ty1, e1 = expr env e1 in
      let ty2, e2 = expr env e2 in
      ignore (unify ty1 ty2) ;
      Tast.Tbool, Tast.Egte (e1, e2)

  | Eplus (e1, e2) -> 
      let ty1, e1 = expr env e1 in
      let ty2, e2 = expr env e2 in
      (* TODO Check numerical ?? *)
      unify ty1 ty2, Tast.Eplus (e1, e2)

  | Eminus (e1, e2) -> 
      let ty1, e1 = expr env e1 in
      let ty2, e2 = expr env e2 in
      (* TODO Check numerical ?? *)
      unify ty1 ty2, Tast.Eminus (e1, e2)
      
  | Estar (e1, e2) -> 
      let ty1, e1 = expr env e1 in
      let ty2, e2 = expr env e2 in
      (* TODO Check numerical ?? *)
      unify ty1 ty2, Tast.Estar (e1, e2)

  | Eseq (e1, e2) -> 
      let ty1, e1 = expr env e1 in
      let ty2, e2 = expr env e2 in
      ignore (unify ty1 (fst e1, Tast.Tunit)) ;
      snd ty2, Tast.Eseq (e1, e2)

  | Etuple el -> 
      let tyl, el = expr_list env el in
      Tast.Ttuple tyl, Tast.Etuple el

  | Ecstr x -> 
      let vm = IMap.add (snd x) (x, None) IMap.empty in
      let ty = Tast.Talgebric vm in
      ty, Tast.Ecstr x

  | Eecstr (md_id, x) -> 
      let vm = IMap.add (snd x) (x, None) IMap.empty in
      let ty = Tast.Talgebric vm in
      ty, Tast.Eecstr (md_id, x)

  | Eif (e1, e2, e3) -> 
      let ty1, e1 = expr env e1 in
      let ty2, e2 = expr env e2 in
      let ty3, e3 = expr env e3 in
      ignore (Unify.type_expr ty1 (fst e1, Tast.Tbool)) ;
      let ty = unify ty2 ty3 in
      ty, Tast.Eif (e1, e2, e3)


and expr_list env el = 
  (* TODO probably more complex than that !! *)
  let l = List.map (expr env) el in
  let tyl = List.map fst l in
  let el = List.map snd l in
  tyl, el


(*  | Eefield of expr * id * id
  | Eextern of id * id
  | Echar of pstring
  | Estring of pstring
  | Erecord of (id * expr) list 
  | Ederef of expr * expr 
  | Efield of expr * id 
  | Ematch of expr * (pat * expr) list

  | Efun of pat list * expr 
  | Eapply of expr * expr list


*)
