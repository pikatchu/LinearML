open Utils
open Neast

type env = type_expr IMap.t

module LocalUtils = struct

  let tany = Pos.none, Tany
  let tprim x = Pos.none, Tprim x
  let tvar x = Pos.none, Tvar (Pos.none, x)
  let tid x = Pos.none, Tid (Pos.none, x)
  let tapply x y = Pos.none, Tapply ((Pos.none, x), (Pos.none, y))
  let tfun x y = Pos.none, Tfun (Ast.Cfun, (Pos.none, x), (Pos.none, y))
  let list l = Pos.none, l

  let o s = 
    output_string stdout s ; 
    print_newline() ; 
    flush stdout

  let is_observed = function
    | (_, Tprim _) -> true
    | (_, Tapply ((_, x), _)) when x = Naming.tobs -> true
    | _ -> false

  let get_true_type = function
    | (_, Tapply ((_, x), (_, [ty1]))) when x = Naming.tobs -> ty1
    | x -> x

  let make_observed (p, ty) = 
    match ty with
    | Tprim _ -> (p, ty)
    | Tapply ((_, x), _) when x = Naming.tobs -> p, ty
    | _ -> p, Tapply ((p, Naming.tobs), (p, [p, ty]))

  let unobserve = function
    | (_, Tapply ((_, x), (_, [y]))) when x = Naming.tobs -> y
    | x -> x

(* TODO move this to stastOfTast *)
  let check_numeric p ty = 
    match ty with
    | _, Tprim (Tint _ | Tfloat _) -> ()
    | _, _ -> Error.expected_numeric p

  let check_bool ((p, ty), _) = 
    match ty with
    | Tprim Tbool -> ()
    | _ -> Error.expected_bool p


  let pos_variant p ty = p, (snd ty)

  let rec has_any b (_, ty) = 
    match ty with
    | Tany -> true
    | Tprim _ -> b
    | Tvar _ -> b
    | Tid _ -> b
    | Tapply (_, l) -> has_any_list b l 
    | Tfun (_, l1, l2) -> has_any_list b l1 || has_any_list b l2

  and has_any_list b (_, l) = 
    List.fold_left has_any b l

  let has_any ty = has_any false ty

end
open LocalUtils

module Print = struct

  let id o (_, x) =
    let x = Ident.to_string x in
    o x

  let def_list o = function
    | [] -> assert false
    | (x, _) :: _ -> 
	let x = Ident.debug x in
	o ("typeof("^x^")")
  
  let rec type_expr o (_, ty) = 
    type_expr_ o ty

  and type_expr_ o = function
    | Tany -> o "_"
    | Tprim ty -> type_prim o ty
    | Tvar x | Tid x -> id o x
    | Tapply (x, tyl) -> 
	type_expr_list o tyl ;
	o " " ; 
	id o x
    | Tfun (k, tyl1, tyl2) -> 
	o "(" ; 
	type_expr_list o tyl1 ; 
	o (match k with Ast.Cfun -> " #" | _ -> " ") ;
	o "-> " ; 
	type_expr_list o tyl2 ; 
	o ")"

  and type_expr_list o (_, l) = 
    match l with
    | [x] -> type_expr o x
    | _ ->
	o "(" ; 
	print_list o type_expr ", " l  ; 
	o ")"

  and type_prim o = function
    | Tunit	-> o "unit"
    | Tbool	-> o "bool"
    | Tchar	-> o "char"
    | Tint	-> o "int"
    | Tfloat	-> o "float"
    | Tstring   -> o "string"

  let debug tyl = 
    type_expr_list (output_string stdout) (Pos.none, tyl) ;
    print_newline()

  let type_expr ty o	    = type_expr o ty ; o "\n"
  let type_expr_ ty o	    = type_expr_ o ty ; o "\n"
  let type_expr_list tyl o  = type_expr_list o tyl ; o "\n"

end

module Type = struct

  let inst_error pl1 ty1 pl2 ty2 = 
    let err = Error.Unify {
      Error.pos1 = pl1 ;
      Error.pos2 = pl2 ;
      Error.print1 = Print.type_expr_ ty1 ;
      Error.print2 = Print.type_expr_ ty2 ; 
    } in
    raise (Error.Type [err])

  let unify_error pty1 pty2 =
    let p1 = fst pty1 in
    let p2 = fst pty2 in
    let pty1 = Print.type_expr pty1 in
    let pty2 = Print.type_expr pty2 in
    let err = Error.Unify {
      Error.pos1 = p1 ;
      Error.pos2 = p2 ;
      Error.print1 = pty1 ;
      Error.print2 = pty2 ;
    } in
    raise (Error.Type [err])

  let rec unify_tvars subst ((_, ty1) as pty1) ((_, ty2) as pty2) =
    match ty1, ty2 with
    | Tany, _ -> subst
    | Tprim _, _ -> subst
    | Tvar x, Tvar y -> 
	(try
	  match IMap.find (snd y) subst with
	  | _, Tvar y when snd x = snd y -> subst
	  | _ -> unify_error pty1 pty2
	with Not_found ->
	  let subst = IMap.add (snd y) pty1 subst in
	  subst)
    | Tid _, _ -> subst
    | Tapply (_, tyl1), Tapply (_, tyl2) -> 
	unify_tvars_list subst tyl1 tyl2
    | Tfun (_, tyl1, tyl2), Tfun (_, tyl3, tyl4) -> 
	let subst = unify_tvars_list subst tyl1 tyl3 in
	unify_tvars_list subst tyl2 tyl4
    | _ -> subst

  and unify_tvars_list subst (_, l1) (_, l2) = unify_tvars_list_ subst l1 l2
  and unify_tvars_list_ subst l1 l2 = 
    match l1, l2 with
    | [], _ | _, [] -> subst
    | x1 :: rl1, x2 :: rl2 -> 
	let subst = unify_tvars subst x1 x2 in
	unify_tvars_list_ subst rl1 rl2

  let rec unify_list env ((p1, _) as l1) ((p2, _) as l2) = 
    try unify_list_ env l1 l2
    with Error.Type err_l ->
      let err = Error.Unify {
	Error.pos1 = p1 ;
	Error.pos2 = p2 ;
	Error.print1 = Print.type_expr_list l1 ;
	Error.print2 = Print.type_expr_list l2 ; 
      } in
      raise (Error.Type (err :: err_l)) 

  and unify_list_ env (p1, tyl1) (p2, tyl2) = 
    if List.length tyl1 <> List.length tyl2
    then Error.arity p1 p2 (List.length tyl1) (List.length tyl2)
    else (p1, List.map2 (unify_el_ env) tyl1 tyl2)
	
  and unify_el env ty1 ty2 = 
    try unify_el_ env ty1 ty2
    with Error.Type _ ->
      let err = Error.Unify {
	Error.pos1 = fst ty1 ;
	Error.pos2 = fst ty2 ;
	Error.print1 = Print.type_expr ty1 ;
	Error.print2 = Print.type_expr ty2 ;
      } in
      raise (Error.Type [err]) 

  and unify_el_ env ty1 ((p, _) as ty2) = 
    p, match ty1, ty2 with
    | (_, Tapply ((_, x) as id, tyl1)), (_, Tapply ((_, y), tyl2)) when x = y -> 
	let tyl = unify_list env tyl1 tyl2 in 
	Tapply (id, tyl)
    | (_, Tfun (k1, tyl1, tyl2)), (_, Tfun (k2, tyl3, tyl4)) when k1 = k2 ->
	let subst = unify_tvars_list IMap.empty tyl3 tyl1 in
	let subst = unify_tvars_list subst tyl4 tyl2 in
	let tyl1 = replace_list ([], ISet.empty) subst env tyl1 in 
	let tyl2 = replace_list ([], ISet.empty) subst env tyl2 in 
	let tyl1 = unify_list_ env tyl1 tyl3 in
	let tyl2 = unify_list_ env tyl2 tyl4 in
	Tfun (k1, tyl1, tyl2)
    | _ -> unify_el_prim env ty1 ty2

  and unify_el_prim env ((p1, ty1) as pty1) ((p2, ty2) as pty2) =
    match ty1, ty2 with
    | Tprim _, (Tany | Tvar _) -> Error.prim_is_not_poly p2
    | (Tany | Tvar _), Tprim _ -> Error.poly_is_not_prim p2
    | Tany, _ -> ty2
    | _, Tany -> ty1
    | Tprim x, Tprim y when x = y -> ty2
    | Tvar (_, x), Tvar (_, y) when (x = y) -> ty2
    | Tid (_, x), Tid (_, y) when x = y -> ty2
    | _ -> unify_error pty1 pty2 

  and inst_list env subst (p1, tyl1) (p2, tyl2) = 
    let size1 = List.length tyl1 in
    let size2 = List.length tyl2 in
    if size1 <> size2
    then Error.arity p1 p2 size1 size2
    else List.fold_left2 (inst env) subst tyl1 tyl2
        
  and inst env subst (pl1, ty1) (pl2, ty2) = 
    match ty1, ty2 with
    | Tprim _, (Tany | Tvar _) -> Error.prim_is_not_poly pl2
    | (Tany | Tvar _), Tprim _ -> Error.poly_is_not_prim pl2
    | Tany, _  -> subst
    | Tprim ty1, Tprim ty2 when ty1 = ty2 -> subst
    | Tvar x, Tapply (y, _)
    | Tapply (y, _), Tvar x when snd y = Naming.tobs -> inst_error pl1 ty1 pl2 ty2
    | Tvar (_, x), Tvar (_, y) when x = y -> subst
    | Tvar v, _ -> inst_var env subst v (pl2, ty2)
    | Tid (_, x), Tid (_, y) when x = y -> subst
    | Tapply ((_, x), tyl1), Tapply ((_, y), tyl2) when x = y ->
	inst_list env subst tyl1 tyl2
    | _, Tany -> subst
    | Tfun (k1, tyl1, tyl3), Tfun (k2, tyl2, tyl4) when k1 = k2 ->
	let subst = inst_list env subst tyl1 tyl2 in
	let subst = inst_list env subst tyl3 tyl4 in
	subst
    | ty1, ty2 -> inst_error pl1 ty1 pl2 ty2

  and inst_var env subst (_, x) (p, ty2) =
    try
      let ty1 = IMap.find x subst in
      let fv = FreeVars.type_expr ISet.empty ty1 in
      if ISet.mem x fv
      then Error.recursive_type p
      else 
	let ty = unify_el env ty1 (p, ty2) in
	IMap.add x ty subst
    with Not_found -> IMap.add x (p, ty2) subst

  and replace path subst env (p, ty) = 
    match ty with
    | Tvar v -> replace_var path subst env v
    | Tapply (x, (p, tyl)) -> 
	let tyl = List.map (replace path subst env) tyl in
	let tyl = p, tyl in
	(p, Tapply (x, tyl))
    | Tfun (k, tyl1, tyl2) -> 
	let tyl1 = replace_list path subst env tyl1 in
	let tyl2 = replace_list path subst env tyl2 in
	(p, Tfun (k, tyl1, tyl2))
    | _ -> (p, ty)

  and replace_var (path, set) subst env (p, x) =
    if ISet.mem x set
    then begin
      match path with
      | (p1, ty1) :: (p2, ty2) :: _ ->
	  inst_error p1 ty1 p2 ty2
      | _ -> assert false
    end
    else try 
      let ty = IMap.find x subst in
      let set = ISet.add x set in
      let path = ty :: path in
      replace (path, set) subst env ty
    with Not_found -> (p, Tvar (p, x))

  and replace_list path subst env (p, tyl) = 
    let tyl = List.map (replace path subst env) tyl in
    let tyl = p, tyl in
    tyl

  let call env rty pty pty2 = 
    let subst = inst_list env IMap.empty rty pty in
    let tyl = replace_list ([], ISet.empty) subst env pty2 in 
    tyl

  let fold_types env tyl = 
    match tyl with
    | [] -> assert false
    | ty :: tyl -> List.fold_left (unify_el env) ty tyl

  let fold_type_lists env tyll = 
    match tyll with
    | [] -> assert false
    | tyl :: rl -> List.fold_left (unify_list env) tyl rl

end

module Env = struct

  let tfree = tfun [tany] [tprim Tunit]

  let tsome = 
    let tmp = Ident.tmp() in
    tfun [tvar tmp] [tapply Naming.toption [tvar tmp]]

  let tnone = tapply Naming.toption [tany]

  let rec make mdl = 
    let env = IMap.empty in
    let env = IMap.add Naming.some tsome env in
    let env = IMap.add Naming.none tnone env in
    let env = List.fold_left module_ env mdl in
    env

  and module_ env md = 
    List.fold_left decl env md.md_decls 

  and decl env = function
    | Dabstract _ -> env
    | Dalgebric tdef
    | Drecord tdef -> algebric env tdef
    | Dval (_, (p, x), (_, ty), _) -> IMap.add x (p, ty) env

  and algebric env tdef =
    IMap.fold (variant tdef.td_args tdef.td_id) tdef.td_map env

  and variant pl tid _ ((p, x), tyl) env = 
    let rty = match pl with
    | [] -> p, Tid tid
    | _ -> 
	let fvs = List.fold_left FreeVars.type_expr ISet.empty (snd tyl) in
	let argl = List.map (tvar fvs) pl in
	let argl = p, argl in
	p, Tapply (tid, argl) in
    match snd tyl with
    | [] -> IMap.add x rty env
    | _ -> 
	let v_ty = p, Tfun (Ast.Lfun, tyl, (p, [rty])) in
	IMap.add x v_ty env
      
  and tvar fvs ((p, x) as id) =
    p, if ISet.mem x fvs 
    then Tvar id
    else Tany
end

let rec program mdl = 
  let env = Env.make mdl in
  List.map (module_ env) mdl
  
and module_ env md = try
  let _ = List.fold_left declare env md.md_decls in
  let defs = List.map (def env) md.md_defs in
  { Tast.md_id = md.md_id ;
    Tast.md_decls = md.md_decls ;
    Tast.md_defs = defs ;
  }
with Error.Type errl -> 
  Error.unify errl
  
and declare env = function
  | Dval (_, x, ty, (Ast.Ext_C _ | Ast.Ext_Asm _)) -> IMap.add (snd x) ty env
  | Dval (_, x, ty, Ast.Ext_none) -> IMap.add (snd x) ty env
  | _ -> env

and def env (fid, p, e) = 
  match IMap.find (snd fid) env with
  | _, Tfun (k, tyl, rty) -> 
      let env, p = pat env p tyl in
      let rty', e = tuple env e in
      let rty = Type.unify_list env rty' rty in
      let e = rty, e in
      (k, fid, p, e)
  | _ -> assert false

and pat env (p1, pl) (p2, tyl) = 
  match pl with
  | [] -> assert false
  | [(p1, l_) as l] -> 
      let size1 = List.length l_ in
      let size2 = List.length tyl in
      if size1 <> size2
      then Error.arity p1 p2 size1 size2 ;
      let env, (tyl, pl) = pat_tuple env l tyl in
      env, (tyl, [pl])

  | ((p1, _) as l) :: rl -> 
      let env, (_, rl) = pat env (p1, rl) (p2, tyl) in
      let env, (tyl, pl) = pat_tuple env l tyl in
      env, (tyl, pl :: rl)

and pat_tuple env (p, l) tyl = 
  let env, (tyl, pl) = pat_tuple_ env l tyl in
  let tyl = p, tyl in
  env, (tyl, (tyl, pl))

and pat_tuple_ env l tyl =
  match l, tyl with
  | [], [] -> env, ([], [])
  | [], _ | _, [] -> assert false
  | p :: rl1, ty :: rl2 ->
      let env, (tyl, pl) = pat_tuple_ env rl1 rl2 in
      let env, ((ty, _) as p) = pat_el env p ty in
      env, (ty :: tyl, p :: pl)

and pat_el env (pos, p) ((hpos, ty)) =
  let pty = pos, ty in 
  let is_obs = is_observed pty in
  let env, (rty, p) = 
    match p with
    | Pany -> env, (pty, Tast.Pany)
    | Pid ((_, x) as id) -> 
	let env = IMap.add x pty env in
	env, (pty, Tast.Pid id)
    | Pvariant (x, (_, [])) -> 
	let pty = get_true_type pty in
	let ty2 = IMap.find (snd x) env in
	let ty2 = pos, (snd ty2) in
	let ty = Type.unify_el env ty2 pty in
	env, (ty, Tast.Pvariant (x, ((pos, []), [])))
    | Pvariant (x, args) ->
      let pty = get_true_type pty in
      let env, rty, args = pat_variant is_obs env x args pty in
      env, (rty, Tast.Pvariant (x, args))
    | Pvalue v -> 
	let pty = get_true_type pty in
	let rty = Type.unify_el env (pos, Tprim (value v)) pty in
	env, (rty, Tast.Pvalue v)
    | Precord pfl -> 
	let pty = get_true_type pty in
	let env, pfl = lfold (pat_field is_obs pty) env pfl in
	let tyl = List.map fst pfl in
	let pfl = List.map snd pfl in
	let ty = Type.fold_types env tyl in 
	env, (ty, Tast.Precord pfl) 
    | Pas (((_, x) as id), p) -> 
	let env = IMap.add x pty env in
	let env, p = pat env p (fst pty, [pty]) in
	env, ((fst pty, ty), Tast.Pas (id, p))
  in
  let rty = if is_obs 
  then make_observed rty
  else rty in
  env, (rty, p)

and pat_field is_obs pty env (p, pf) = 
  let pty = p, snd pty in
  match pf with 
  | PFany -> 
      let pty = if is_obs then make_observed pty else pty in
      env, (pty, (p, Tast.PFany))
  | PFid ((_, x) as id) -> 
      let pty = if is_obs then make_observed pty else pty in
      let env = IMap.add x pty env in
      env, (pty, (p, Tast.PFid id))
  | PField (id, args) ->
      let env, rty, args = pat_variant is_obs env id args pty in
      let rty = if is_obs then make_observed rty else rty in
      env, (rty, (p, Tast.PField (id, args)))

and pat_variant is_obs env x args pty =
  let argty, rty = 
    match IMap.find (snd x) env with
    | _, Tfun (_, tyl, rty) -> tyl, rty
    | _ -> Error.no_argument (fst pty) 
  in
  let pty = fst pty, [pty] in
  let tyl = Type.call env rty pty argty in 
  let obs_tyl = 
    if is_obs 
    then fst tyl, List.map make_observed (snd tyl) 
    else tyl 
  in let env, ((tyl, _) as args) = pat env args obs_tyl in
  let tyl = fst tyl, List.map get_true_type (snd tyl) in
  let rty = apply env (fst pty) x tyl in
  let rty = match rty with 
  | _, [_, x] -> fst pty, x
  | _ -> assert false in
  env, rty, args

and tuple env (p, el) = 
  let el = List.map (tuple_pos env) el in
  let tyl = List.map fst el in
  let tyl = List.map snd tyl in
  let tyl = List.flatten tyl in
  ((p, tyl), el)

and tuple_pos env (p, e) = 
  let (tyl, e) = tuple_ env p e in
  ((p, snd tyl), e)
    
and tuple_ env p = function
  | Eapply (x, el) ->
      let ((tyl, _) as el) = tuple env el in
      let rty = apply env p x tyl in
      let fty = unobserve (IMap.find (snd x) env) in
      let fk = match fty with _, Tfun (k, _, _) -> k | _ -> assert false in
      let res = rty, Tast.Eapply (fk, fty, x, el) in
      res 
  | Eif (e1, el1, el2) -> 
      let e1 = expr env e1 in
      check_bool e1 ;
      let ((tyl1, _) as el1) = tuple env el1 in
      let ((tyl2, _) as el2) = tuple env el2 in
      let tyl = Type.unify_list env tyl1 tyl2 in
      (tyl, Tast.Eif (e1, el1, el2))
  | Elet (argl, e1, e2) -> 
      let ((tyl, _) as e1) = tuple env e1 in
      let env, argl = pat env argl tyl in 
      let ((tyl, _) as e2) = tuple env e2 in
      (tyl, Tast.Elet (argl, e1, e2))
  | Efield (e, ((p, x) as fd_id)) -> 
      let ((ty, _) as e) = expr env e in
      let fdtype = IMap.find x env in 
      let fdtype = p, snd fdtype in
      let tyl = proj env ty fdtype in
      (tyl, Tast.Efield (e, fd_id))
  | Ematch (el, pel) -> 
      let ((tyl, _) as el) = tuple env el in
      let pel = List.map (action env tyl) pel in
      let tyl = List.map fst pel in
      let pel = List.map snd pel in
      let tyl = Type.fold_type_lists env tyl in
      (tyl, Tast.Ematch (el, pel)) 
  | Eseq (((p, _) as e1), e2) -> 
      let (ty1, e1) = expr env e1 in
      let ty1 = Type.unify_el env ty1 (p, Tprim Tunit) in
      let e1 = ty1, e1 in
      let (ty, _ as e2) = tuple env e2 in
      (ty, Tast.Eseq (e1, e2))
  | e ->
      let (ty, e) = expr_ env (p, e) in
      ((p, [ty]), e)

and expr env ((p, _) as e) = 
  let el = tuple env (p, [e]) in
  match snd el with
  | [] -> assert false
  | [(_, [_, ty]), e] -> ((p, ty), e)
  | _ -> Error.no_tuple p

and expr_ env (p, e) =
  match e with    
  | Eid ((_, x) as id) -> 
      let ty = IMap.find x env in
      let ty = p, (snd ty) in
      (ty, Tast.Eid id)
  | Evalue v -> 
      let ty = p, Tprim (value v) in
      (ty, Tast.Evalue v)
  | Evariant ((p1, x), (p2, [])) -> 
      let rty = IMap.find x env in
      let rty = pos_variant p1 rty in
      let argty = p2, [] in
      (rty, Tast.Evariant ((p1, x), (argty, [])))
  | Evariant (x, el) -> 
      let (ty, (x, el)) = variant env (x, el) in
      let ty = pos_variant p ty in
      (ty, Tast.Evariant (x, el))
  | Ebinop (bop, e1, e2) ->
      let ((ty1, _) as e1) = expr env e1 in
      let ((ty2, _) as e2) = expr env e2 in
      (match bop with
      | Ast.Eplus
      | Ast.Eminus
      | Ast.Estar 
      | Ast.Ediv -> 
	  check_numeric p ty1 ;
	  check_numeric p ty2 
      | Ast.Eor | Ast.Eand -> (* TODO check bool *) ()
      | _ -> ()) ;
      let _ = Type.unify_el env ty1 ty2 in
      let ty = binop env bop p ty1 ty2 in
      (ty, Tast.Ebinop (bop, e1, e2))
  | Euop (Ast.Enot, e) ->
      let (ty, _ as e) = expr env e in
      (* TODO check bool *)
      (ty, Tast.Euop (Ast.Euminus, e))
  | Euop (Ast.Euminus, e) -> 
      let (ty, _ as e) = expr env e in
      (* TODO check numeric *)
      (ty, Tast.Euop (Ast.Euminus, e))
  | Erecord fdl -> 
      let fdl = List.map (variant env) fdl in
      let tyl = List.map fst fdl in
      let fdl = List.map snd fdl in
      let ty = Type.fold_types env tyl in
      (ty, Tast.Erecord fdl)
  | Ewith (e, fdl) -> 
      let ((ty1, _) as e) = expr env e in
      let fdl = List.map (variant env) fdl in
      let tyl = List.map fst fdl in
      let fdl = List.map snd fdl in
      let ty = Type.fold_types env tyl in
      let ty = Type.unify_el env ty1 ty in
      (ty, Tast.Ewith (e, fdl))
  | Eobs ((p, x) as id) ->
      let ty = IMap.find x env in
      let ty = p, (snd ty) in
      let obs_ty = make_observed ty in
      (obs_ty, Tast.Eobs id)
  | Efree ((p, x) as id) -> 
      let ty = IMap.find x env in
      let ty = p, (snd ty) in
      ((p, Tprim Tunit), Tast.Efree (ty, id))
  | Eapply (_, _)
  | Eif (_, _, _)
  | Elet (_, _, _)
  | Ematch (_, _)
  | Eseq (_, _)
  | Efield (_, _) -> assert false

and action env tyl (p, e) = 
  let env, p = pat env p tyl in
  let ((tyl, _) as e) = tuple env e in
  (tyl, (p, e))

and variant env (x, el) = 
  let p = Pos.btw (fst x) (fst el) in
  let ((tyl, _) as el) = tuple env el in
  let rty = apply env p x tyl in
  match rty with 
  | _, [rty] -> (rty, (x, el))
  | _ -> assert false

and proj env ty fty = 
  let rty = 
    match unobserve ty, fty with
    | (p1, Tid (_, x1)), (p2, Tfun (_, (_, ty), (_, [_, Tid (_, x2)]))) ->
	if x1 <> x2
	then Error.unify_proj p1 p2 ;
	(p1, ty)
    | (p1, Tapply ((_, x1), argl1)), 
	(p2, Tfun (_, ty, (_, [_, Tapply ((_, x2), argl2)]))) ->
	  if x1 <> x2
	  then Error.unify_proj p1 p2 ;
	  Type.call env argl2 argl1 ty 
    | (p1, _), (p2, _) -> Error.unify_proj p1 p2
  in
  fst rty, List.map make_observed (snd rty)

and binop env bop p ty1 ty2 = 
  match bop with
  | Ast.Eeq 
  | Ast.Ediff
  | Ast.Elt
  | Ast.Elte
  | Ast.Egt
  | Ast.Egte -> (p, Tprim Tbool)
  | Ast.Eplus
  | Ast.Eminus
  | Ast.Estar 
  | Ast.Ediv -> Type.unify_el env ty1 ty2
  | Ast.Eand | Ast.Eor -> (* TODO check bool ty1 ty2 *) (p, Tprim Tbool)

and value = function
  | Nast.Eunit -> Tunit
  | Nast.Ebool _ -> Tbool
  | Nast.Eint _ -> Tint
  | Nast.Efloat _ -> Tfloat
  | Nast.Echar _ -> Tchar
  | Nast.Estring _ -> Tstring

and apply env p (fp, x) tyl = 
  match unobserve (IMap.find x env) with
  | (_, Tfun (_, tyl1, tyl2)) ->
      let ty = Type.call env tyl1 tyl tyl2 in
      let ty = p, List.map (fun (_, x) -> p, x) (snd ty) in
      ty
  | p2, ty -> 
      Print.debug [p2, ty] ;
      Error.expected_function fp (* TODO *)

