open Utils
open Neast

module TMap = Map.Make (CompareType)

type env = {
    tenv: type_expr IMap.t ;
    defs: def IMap.t ;
    decls: bool TMap.t ;
    apply_def_list: apply_def_list ;
  }

and acc = {
    mem: type_expr_list TMap.t ;
  }

and apply_def_list = 
    env -> acc -> Pos.t -> id list -> type_expr_list -> type_expr_list 
	-> acc * type_expr_list


module LocalUtils = struct

  let tany = Pos.none, Tany
  let tprim x = Pos.none, Tprim x
  let tvar x = Pos.none, Tvar (Pos.none, x)
  let tid x = Pos.none, Tid (Pos.none, x)
  let tapply x y = Pos.none, Tapply ((Pos.none, x), (Pos.none, y))
  let tfun x y = Pos.none, Tfun ((Pos.none, x), (Pos.none, y))
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

  let rec tundef (_, tyl) = tundef_ tyl
  and tundef_ tyl = 
    match tyl with
    | [] -> false
    | (_, Tany ) :: _ -> true
    | _ :: rl -> tundef_ rl

  let rec partial_tundef (_, tyl) = partial_tundef_ tyl
  and partial_tundef_ tyl = 
    match tyl with
    | [] -> false
    | (_, Tany ) :: _ -> true
    | (_, Tapply (_, tyl) ) :: rl -> 
	partial_tundef tyl || partial_tundef_ rl
    | _ :: rl -> partial_tundef_ rl

  let check_numeric p ty = 
    match ty with
    | _, Tany
    | _, Tprim (Tint32 _ | Tfloat _) -> ()
    | _, _ -> Error.expected_numeric p

  let check_bool ((p, ty), _) = 
    match ty with
    | Tany | Tprim Tbool -> ()
    | _ -> Error.expected_bool p

  let filter_undef ((x, tyl) as call) rty acc = 
    if partial_tundef tyl
    then acc
    else TMap.add call rty acc

  let rec make_undef p n = 
    if n = 0
    then []
    else (p, Tany) :: make_undef p (n-1)

  let rec pos_variant p ty =
    match ty with
    | _, Tapply (id, (_, argl)) ->
	p, Tapply (id, (p, List.map (fun (_, x) -> p, x) argl)) 
    | _, x -> p, x

  let get_decl acc = function
    | Dval (fid, (_, Tfun (tyl, _))) -> 
	TMap.add (fid, tyl) true acc
    | _ -> acc


end
open LocalUtils

module NormalizeType = struct

  let rec type_expr (p, ty) = p, type_expr_ ty
  and type_expr_ = function
  | Tany 
  | Tdef _
  | Tid _
  | Tprim _ as x -> x
  | Tvar _ -> Tany
  | Tapply (x, tyl) -> Tapply (x, type_expr_list tyl)
  | Tfun (tyl1, tyl2) -> Tfun (type_expr_list tyl1, type_expr_list tyl2)

  and type_expr_list (p, tyl) = p, List.map type_expr tyl

end

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
    | Tdef m -> 
	let l = clist_of_imap m in
	def_list o l

    | Tapply (x, tyl) -> 
	type_expr_list o tyl ;
	o " " ; 
	id o x

    | Tfun (tyl1, tyl2) -> 
	o "(" ; 
	type_expr_list o tyl1 ; 
	o " -> " ; 
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
    | Tint32	-> o "int32"
    | Tfloat	-> o "float"
    | Tstring   -> o "string"

  let debug tyl = 
    type_expr_list (output_string stdout) (Pos.none, tyl) ;
    print_newline()

  let type_expr ty o	    = type_expr o ty ; o "\n"
  let type_expr_ ty o	    = type_expr_ o ty ; o "\n"
  let type_expr_list tyl o  = type_expr_list o tyl ; o "\n"

end

module Unify = struct

  let rec unify_list env acc ((p1, _) as l1) ((p2, _) as l2) = 
    try unify_list_ env acc l1 l2
    with Exit -> 
      let pp1 = Print.type_expr_list l1 in
      let pp2 = Print.type_expr_list l2 in 
      Error.unify p1 p2 pp1 pp2

  and unify_list_ env acc ((p1, tyl1) as l1) ((p2, tyl2) as l2) = 
    let tyl1 = if tundef l1 then make_undef p1 (List.length tyl2) else tyl1 in
    let tyl2 = if tundef l2 then make_undef p2 (List.length tyl1) else tyl2 in
    if List.length tyl1 <> List.length tyl2
    then Error.arity p1 p2 (List.length tyl1) (List.length tyl2)
    else 
      let acc, tyl = lfold2 (unify_el_ env) acc tyl1 tyl2 in
      acc, (p1, tyl)
	
  and unify_el env acc ty1 ty2 = 
    try unify_el_ env acc ty1 ty2
    with Exit -> 
      let pty1 = Print.type_expr ty1 in
      let pty2 = Print.type_expr ty2 in
      Error.unify (fst ty1) (fst ty2) pty1 pty2

  and unify_el_ env acc ty1 ty2 = 
    match ty1, ty2 with
    | (p, Tdef ids), (_, Tfun (tyl, rty))
    | (_, Tfun (tyl, rty)), (p, Tdef ids) ->
	let idl = IMap.fold (fun x _ acc -> (p, x) :: acc) ids [] in
	let acc, rty = env.apply_def_list env acc p idl tyl rty in
	acc, (p, Tfun (tyl, rty))

    | (p1, Tapply ((_, x) as id, tyl1)), (p2, Tapply ((_, y), tyl2)) when x = y -> 
	let tyl1 = p1, snd tyl1 in
	let tyl2 = p2, snd tyl2 in
	let acc, tyl = unify_list env acc tyl1 tyl2 in 
	acc, (p1, Tapply (id, tyl))

    | (p, Tfun (tyl1, tyl2)), (_, Tfun (tyl3, tyl4)) ->
	let acc, tyl1 = unify_list_ env acc tyl1 tyl3 in
	let acc, tyl2 = unify_list_ env acc tyl2 tyl4 in
	acc, (p, Tfun (tyl1, tyl2))
	  
    | (p, _), _ -> 
	let ty = unify_el_prim env acc ty1 ty2 in
	acc, (p, ty)

  and unify_el_prim env acc (p1, ty1) (p2, ty2) =
    match ty1, ty2 with
    | Tany, ty 
    | ty, Tany -> ty
    | Tprim x, Tprim y when x = y -> ty1
    | Tvar (_, x), Tvar (_, y) when x = y -> ty1
    | Tid (_, x), Tid (_, y) when x = y -> ty1
    | Tdef s1, Tdef s2 -> Tdef (IMap.fold IMap.add s1 s2)
    | _ -> raise Exit

  let rec fold_types env acc tyl = 
    match tyl with
    | [] -> assert false
    | ty :: tyl -> 
	List.fold_left 
	  (fun (acc, rty) ty -> 
	    unify_el env acc rty ty
	  ) (acc, ty) tyl

  let rec fold_type_lists env acc tyll = 
    match tyll with
    | [] -> assert false
    | tyl :: rl ->
	List.fold_left 
	  (fun (acc, rty) ty -> 
	    unify_list env acc rty ty 
	  ) (acc, tyl) rl

end

module Instantiate = struct

  let rec inst_list env acc subst (p1, tyl1) (p2, tyl2) = 
    let size1 = List.length tyl1 in
    let size2 = List.length tyl2 in
    if size1 <> size2
    then Error.arity p1 p2 size1 size2
    else List.fold_left2 (inst env) (acc, subst) tyl1 tyl2
        
  and inst env (acc, subst) (pl1, ty1) (pl2, ty2) = 
    match ty1, ty2 with
    | Tany, _  -> acc, subst
    | Tprim ty1, Tprim ty2 when ty1 = ty2 -> acc, subst
    | Tvar (_, x), Tvar (_, y) when x = y -> acc, subst
    | Tvar v, _ -> inst_var env acc subst v (pl2, ty2)
    | Tid (_, x), Tid (_, y) when x = y -> acc, subst
    | Tapply ((_, x), tyl1), Tapply ((_, y), tyl2) when x = y ->
	inst_list env acc subst tyl1 tyl2
    | Tapply ((_, x), tyl1), Tany -> 
	inst_list env acc subst tyl1 (pl2, (make_undef pl1 (List.length (snd tyl1))))
    | _, Tany -> acc, subst
    | Tfun (tyl, rty1), Tdef ids -> 
	let pdef = pl2 in
	let idl = IMap.fold (fun x _ acc -> (pdef, x) :: acc) ids [] in
	let rty = pdef, [pl2, Tany] in
	let acc, rty2 = env.apply_def_list env acc pl2 idl tyl rty in
	inst_list env acc subst rty1 rty2
    | Tfun (tyl1, tyl3), Tfun (tyl2, tyl4) -> 
	let acc, subst = inst_list env acc subst tyl1 tyl2 in
	let acc, subst = inst_list env acc subst tyl3 tyl4 in
	acc, subst
    | ty1, ty2 -> 
	let ty1 = Print.type_expr_ ty1 in
	let ty2 = Print.type_expr_ ty2 in
	Error.unify pl1 pl2 ty1 ty2

  and inst_var env acc subst (_, x) (p, ty2) =
    try 
      let ty1 = IMap.find x subst in
      let fv = FreeVars.type_expr ISet.empty ty1 in
      if ISet.mem x fv
      then Error.recursive_type p
      else if ty2 = Tany
      then acc, subst
      else inst env (acc, subst) ty1 (p, ty2)
    with Not_found -> acc, IMap.add x (p, ty2) subst

  and replace subst env acc (p, ty) = 
    match ty with
    | Tvar v -> replace_var subst env acc v
    | Tapply (x, (p, tyl)) -> 
	let acc, tyl = lfold (replace subst env) acc tyl in
	let tyl = p, tyl in
	acc, (p, Tapply (x, tyl))

    | Tfun (tyl1, tyl2) -> 
	let acc, tyl1 = replace_list subst env acc tyl1 in
	let acc, tyl2 = replace_list subst env acc tyl2 in
	acc, (p, Tfun (tyl1, tyl2))

    | _ -> acc, (p, ty)

  and replace_var subst env acc (p, x) =
    try 
      replace subst env acc (IMap.find x subst)
    with Not_found -> acc, (p, Tvar (p, x))

  and replace_list subst env acc (p, tyl) = 
    let acc, tyl = lfold (replace subst env) acc tyl in
    let tyl = p, tyl in
    acc, tyl

end


module Env = struct

  let tfree = tfun [tany] [tprim Tunit]
  let tget = tfun [tany ; tany] [tany] (* TODO type *)
  let tlength = tfun [tany] [tprim Tint32] (* TODO type *)

  let rec make mdl = 
    let env = IMap.empty in
    let env = IMap.add Naming.free tfree env in
    let env = IMap.add Naming.get tget env in
    let env = IMap.add Naming.length tlength env in
    let env = List.fold_left module_ env mdl in
    env

  and module_ env md = 
    List.fold_left decl env md.md_decls 

  and decl env = function
    | Dalgebric tdef
    | Drecord tdef -> algebric env tdef
    | Dval ((p, x), (_, ty)) -> IMap.add x (p, ty) env

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
	let v_ty = p, Tfun (tyl, (p, [rty])) in
	IMap.add x v_ty env
      
  and tvar fvs ((p, x) as id) =
    p, if ISet.mem x fvs 
    then Tvar id
    else Tany
end

module Usage = struct

  let check_used uset ((p, x), _, _) = 
    if not (ISet.mem x uset) 
    then Error.unused p
    else ()

  let add_decl acc d =
    match d with
    | Dval ((_, x), _) -> ISet.add x acc
    | _ -> acc

  let add_call ((_, x), _) _ y =
    ISet.add x y

  let check acc md = 
    let used = List.fold_left add_decl ISet.empty md.md_decls in
    let used = TMap.fold add_call acc.mem used in
    List.iter (check_used used) md.md_defs ;
end

let empty_env tenv app = {
  tenv = tenv ; 
  defs = IMap.empty ; 
  decls = TMap.empty ;
  apply_def_list = app ;
} 

let rec program mdl = 
  let tenv = Env.make mdl in
  List.map (module_ tenv) mdl
  
and module_ tenv md = 
  let env = empty_env tenv apply_def_list in
  let env = List.fold_left def env md.md_defs in
  let decls = List.fold_left get_decl TMap.empty md.md_decls in
  let env = { env with decls = decls } in
  let acc = { mem = TMap.empty } in
  let acc = List.fold_left (decl env) acc md.md_decls in
(*  TMap.iter (fun ((_, x), args) rty ->
    Ident.print x ;
    Print.debug (snd args) ;
    Print.debug (snd rty) ; ) acc.mem ; *)
  Usage.check acc md ;
  let md = fresh_module env acc md in
  md

and fresh_module env acc md = 
  let ads = acc, [], IMap.empty in
  let _, defs, subst = TMap.fold (typed_def env) acc.mem ads in 
  let md = { 
    Tast.md_id = md.md_id ;
    Tast.md_decls = md.md_decls ;
    Tast.md_defs = defs ;
  } in 
  let md = Tast.Rename.module_ subst md in
  let md = Tast.DeadCode.module_ md in
  md

and def env (((p, x), _, _) as d) =
  let tenv = IMap.add x (p, Tdef (IMap.add x p IMap.empty)) env.tenv in
  let defs = IMap.add x d env.defs in
  { env with tenv = tenv ; defs = defs }

and decl env acc = function
  | Dval (fid, (_, Tfun (tyl, rty))) ->
      let (_, args, e) = IMap.find (snd fid) env.defs in      
      let env, acc, _ = pat env acc args tyl in
      let acc, (rty2, _) = tuple env acc e in
      let acc, rty = Unify.unify_list env acc rty2 rty in
      let acc = { mem = TMap.add (fid, tyl) rty acc.mem } in
      acc
  | Dval _ -> assert false
  | _ -> acc

and typed_def env ((p, f), tyl) rty (acc, defs, subst) =
  let (fid, args, e) = IMap.find f env.defs in
  let env, acc, args = pat env acc args tyl in
  let acc, ((rty2, _) as e) = tuple env acc e in
  let acc, rty = Unify.unify_list env acc rty2 rty in
  let def = fid, args, e in
  if TMap.mem (fid, tyl) env.decls 
  then acc, def :: defs, subst
  else fresh_def acc defs subst def

and fresh_def acc defs subst def = 
  let (_, x), _, _ = def in
  let def = Tast.Fresh.def def in
  let (_, y), _, _ = def in
  acc, def :: defs, IMap.add x y subst

and pat env acc (p1, pl) (p2, tyl) = 
  match pl with
  | [] -> assert false
  | [(p1, l_) as l] -> 
      let tyl = 
	if tundef (p2, tyl)
	then List.map (
	  fun (p, _) -> p, Tany
	 ) l_
	else tyl in
      let size1 = List.length l_ in
      let size2 = List.length tyl in
      if size1 <> size2
      then Error.arity p1 p2 size1 size2 ;
      let env, acc, (tyl, pl) = pat_tuple env acc l tyl in
      env, acc, (tyl, [pl])

  | ((p1, _) as l) :: rl -> 
      let env, acc, (_, rl) = pat env acc (p1, rl) (p2, tyl) in
      let env, acc, (tyl, pl) = pat_tuple env acc l tyl in
      env, acc, (tyl, pl :: rl)

and pat_tuple env acc (p, l) tyl = 
  let env, acc, (tyl, pl) = pat_tuple_ env acc l tyl in
  let tyl = p, tyl in
  env, acc, (tyl, (tyl, pl))

and pat_tuple_ env acc l tyl =
  match l, tyl with
  | [], [] -> env, acc, ([], [])
  | [], _ | _, [] -> assert false
  | p :: rl1, ty :: rl2 ->
      let env, acc, (tyl, pl) = pat_tuple_ env acc rl1 rl2 in
      let env, acc, ((ty, _) as p) = pat_el env acc p ty in
      env, acc, (ty :: tyl, p :: pl)

and pat_el env acc (pos, p) (_, ty) =
  let pty = pos, ty in
  let is_obs = is_observed pty in
  let env, acc, (rty, p) = 
    match p with
    | Pany -> env, acc, (pty, Tast.Pany)
    | Pid ((_, x) as id) -> 
	let env = { env with tenv = IMap.add x pty env.tenv } in
	env, acc, (pty, Tast.Pid id)
    | Pvariant (x, (_, [])) -> 
	let pty = get_true_type pty in
	let ty2 = IMap.find (snd x) env.tenv in
	let ty2 = pos, (snd ty2) in
	let acc, ty = Unify.unify_el env acc ty2 pty in
	env, acc, (ty, Tast.Pvariant (x, ((pos, []), [])))
    | Pvariant (x, args) ->
      let pty = get_true_type pty in
      let env, acc, rty, args = pat_variant is_obs env acc x args pty in
      env, acc, (rty, Tast.Pvariant (x, args))
    | Pvalue v -> 
	let pty = get_true_type pty in
	let acc, rty = Unify.unify_el env acc (pos, Tprim (value v)) pty in
	env, acc, (rty, Tast.Pvalue v)
    | Precord pfl -> 
	let pty = get_true_type pty in
	let (env, acc), pfl = lfold (pat_field is_obs pty) (env, acc) pfl in
	let tyl = List.map fst pfl in
	let pfl = List.map snd pfl in
	let acc, ty = Unify.fold_types env acc tyl in 
	env, acc, (ty, Tast.Precord pfl) 
    | Pas (((_, x) as id), p) -> 
	let env = { env with tenv = IMap.add x pty env.tenv } in
	let env, acc, p = pat env acc p (fst pty, [pty]) in
	env, acc, ((fst pty, ty), Tast.Pas (id, p))
  in
  let rty = if is_obs 
  then make_observed rty
  else rty in
  env, acc, (rty, p)

and pat_field is_obs pty (env, acc) (p, pf) = 
  let pty = p, snd pty in
  match pf with 
  | PFany -> 
      let pty = if is_obs then make_observed pty else pty in
      (env, acc), (pty, (p, Tast.PFany))
  | PFid ((_, x) as id) -> 
      let pty = if is_obs then make_observed pty else pty in
      let env = { env with tenv = IMap.add x pty env.tenv } in
      (env, acc), (pty, (p, Tast.PFid id))
  | PField (id, args) ->
      let env, acc, rty, args = pat_variant is_obs env acc id args pty in
      let rty = if is_obs then make_observed rty else rty in
      (env, acc), (rty, (p, Tast.PField (id, args)))

and pat_variant is_obs env acc x args pty =
  let argty, rty = match IMap.find (snd x) env.tenv with
  | _, Tfun (tyl, rty) -> tyl, rty
  | _ -> assert false (* TODO error no argument expected *) in
  let pty = fst pty, [pty] in
  let acc, subst = Instantiate.inst_list env acc IMap.empty rty pty in
  let acc, tyl = Instantiate.replace_list subst env acc argty in 
  let obs_tyl = 
    if is_obs 
    then fst tyl, List.map make_observed (snd tyl) 
    else tyl 
  in let env, acc, ((tyl, _) as args) = pat env acc args obs_tyl in
  let tyl = fst tyl, List.map get_true_type (snd tyl) in
  let acc, rty = apply env acc (fst pty) x tyl in
  let rty = match rty with 
  | _, [_, x] -> fst pty, x
  | _ -> assert false in
  env, acc, rty, args

and tuple env acc (p, el) = 
  let acc, el = lfold (tuple_pos env) acc el in
  let tyl = List.map fst el in
  let tyl = List.map snd tyl in
  let tyl = List.flatten tyl in
  acc, ((p, tyl), el)

and tuple_pos env acc (p, e) = 
  let acc, (tyl, e) = tuple_ env acc p e in
  acc, ((p, snd tyl), e)
    
and tuple_ env acc p = function
  | Eapply (x, el) ->
      let acc, ((tyl, _) as el) = tuple env acc el in
      let acc, rty = apply env acc p x tyl in
      let res = rty, Tast.Eapply (x, el) in
      acc, res 
  | Eif (e1, el1, el2) -> 
      let acc, e1 = expr env acc e1 in
      check_bool e1 ;
      let acc, ((tyl1, _) as el1) = tuple env acc el1 in
      let acc, ((tyl2, _) as el2) = tuple env acc el2 in
      let acc, tyl = Unify.unify_list env acc tyl1 tyl2 in
      acc, (tyl, Tast.Eif (e1, el1, el2))
  | Elet (argl, e1, e2) -> 
      let acc, ((tyl, _) as e1) = tuple env acc e1 in
      let env, acc, argl = pat env acc argl tyl in 
      let acc, ((tyl, _) as e2) = tuple env acc e2 in
      acc, (tyl, Tast.Elet (argl, e1, e2))
  | Efield (e, ((p, x) as fd_id)) -> 
      let acc, ((ty, _) as e) = expr env acc e in
      let fdtype = IMap.find x env.tenv in 
      let fdtype = p, snd fdtype in
      let acc, tyl = proj env acc ty fdtype in
      acc, (tyl, Tast.Efield (e, fd_id))
  | Ematch (el, pel) -> 
      let acc, ((tyl, _) as el) = tuple env acc el in
      let acc, pel = lfold (action env tyl) acc pel in
      let tyl = List.map fst pel in
      let pel = List.map snd pel in
      let acc, tyl = Unify.fold_type_lists env acc tyl in
      acc, (tyl, Tast.Ematch (el, pel)) 
  | Eseq (((p, _) as e1), e2) -> 
      let acc, (ty1, e1) = expr env acc e1 in
      let acc, ty1 = Unify.unify_el env acc ty1 (p, Tprim Tunit) in
      let e1 = ty1, e1 in
      let acc, (ty, _ as e2) = tuple env acc e2 in
      acc, (ty, Tast.Eseq (e1, e2))
  | e ->
      let acc, (ty, e) = expr_ env acc (p, e) in
      acc, ((p, [ty]), e)

and expr env acc ((p, _) as e) = 
  let acc, el = tuple env acc (p, [e]) in
  match snd el with
  | [] -> assert false
  | [(_, [_, ty]), e] -> acc, ((p, ty), e)
  | _ -> Error.no_tuple p

and expr_ env acc (p, e) =
  match e with    
  | Eid ((_, x) as id) -> 
      let ty = IMap.find x env.tenv in
      let ty = p, (snd ty) in
      acc, (ty, Tast.Eid id)
  | Evalue v -> 
      let ty = p, Tprim (value v) in
      acc, (ty, Tast.Evalue v)
  | Evariant ((p1, x), (p2, [])) -> 
      let rty = IMap.find x env.tenv in
      let rty = pos_variant p1 rty in
      let argty = p2, [] in
      acc, (rty, Tast.Evariant ((p1, x), (argty, [])))
  | Evariant (x, el) -> 
      let acc, (ty, (x, el)) = variant env acc (x, el) in
      let ty = pos_variant p ty in
      acc, (ty, Tast.Evariant (x, el))
  | Ebinop (bop, e1, e2) ->
      let acc, ((ty1, _) as e1) = expr env acc e1 in
      let acc, ((ty2, _) as e2) = expr env acc e2 in
      (match bop with
      | Ast.Eplus
      | Ast.Eminus
      | Ast.Estar -> 
	  check_numeric p ty1 ;
	  check_numeric p ty2 
      | _ -> ()) ;
      let acc, _ = Unify.unify_el env acc ty1 ty2 in
      let acc, ty = binop env acc bop p ty1 ty2 in
      acc, (ty, Tast.Ebinop (bop, e1, e2))
  | Euop (Ast.Euminus, e) -> 
      let acc, (ty, _ as e) = expr env acc e in
      acc, (ty, Tast.Euop (Ast.Euminus, e))
  | Erecord fdl -> 
      let acc, fdl = lfold (variant env) acc fdl in
      let tyl = List.map fst fdl in
      let fdl = List.map snd fdl in
      let acc, ty = Unify.fold_types env acc tyl in
      acc, (ty, Tast.Erecord fdl)
  | Ewith (e, fdl) -> 
      let acc, ((ty1, _) as e) = expr env acc e in
      let acc, fdl = lfold (variant env) acc fdl in
      let tyl = List.map fst fdl in
      let fdl = List.map snd fdl in
      let acc, ty = Unify.fold_types env acc tyl in
      let acc, ty = Unify.unify_el env acc ty ty1 in
      acc, (ty, Tast.Ewith (e, fdl))
  | Eobs ((p, x) as id) ->
      let ty = IMap.find x env.tenv in
      let ty = p, (snd ty) in
      let obs_ty = make_observed ty in
      acc, (obs_ty, Tast.Eobs id)
  | Eapply (_, _)
  | Eif (_, _, _)
  | Elet (_, _, _)
  | Ematch (_, _)
  | Eseq (_, _)
  | Efield (_, _) -> assert false

and action env tyl acc (p, e) = 
  let env, acc, p = pat env acc p tyl in
  let acc, ((tyl, _) as e) = tuple env acc e in
  acc, (tyl, (p, e))

and variant env acc (x, el) = 
  let p = Pos.btw (fst x) (fst el) in
  let acc, ((tyl, _) as el) = tuple env acc el in
  let acc, rty = apply env acc p x tyl in
  match rty with 
  | _, [rty] -> acc, (rty, (x, el))
  | _ -> assert false

and proj env acc ty fty = 
  match unobserve ty, fty with
  | (p1, Tid (_, x1)), (p2, Tfun ((_, ty), (_, [_, Tid (_, x2)]))) ->
      if x1 <> x2
      then Error.unify_proj p1 p2 ;
      acc, (p1, ty)
  | (p1, Tapply ((_, x1), argl1)), 
    (p2, Tfun (ty, (_, [_, Tapply ((_, x2), argl2)]))) ->
      if x1 <> x2
      then Error.unify_proj p1 p2 ;
      let acc, subst = Instantiate.inst_list env acc IMap.empty argl2 argl1 in
      Instantiate.replace_list subst env acc ty
  | (p1, _), (p2, _) -> Error.unify_proj p1 p2

and binop env acc bop p ty1 ty2 = 
  match bop with
  | Ast.Eeq 
  | Ast.Elt
  | Ast.Elte
  | Ast.Egt
  | Ast.Egte -> acc, (p, Tprim Tbool)
  | Ast.Eplus
  | Ast.Eminus
  | Ast.Estar -> Unify.unify_el env acc ty1 ty2

and value = function
  | Nast.Eunit -> Tunit
  | Nast.Ebool _ -> Tbool
  | Nast.Eint _ -> Tint32
  | Nast.Efloat _ -> Tfloat
  | Nast.Echar _ -> Tchar
  | Nast.Estring _ -> assert false

and apply env acc p (fp, x) tyl = 
  match IMap.find x env.tenv with
  | (_, Tfun (tyl1, tyl2)) -> 
      let acc, subst = Instantiate.inst_list env acc IMap.empty tyl1 tyl in
      let acc, rty = Instantiate.replace_list subst env acc tyl2 in
      acc, rty

  | (_, Tdef ids) ->
      let rty = p, [p, Tany] in
      let idl = IMap.fold (fun x _ acc -> (p, x) :: acc) ids [] in
      apply_def_list env acc p idl tyl rty

  | (_, Tany) ->
      let rty = p, [p, Tany] in
      let tenv = IMap.add x (p, Tfun (tyl, rty)) env.tenv in
      let env = { env with tenv = tenv } in
      apply env acc p (fp, x) tyl
      

  | p2, ty -> 
      Print.debug [p2, ty] ;
      Error.expected_function fp (* TODO *)

and apply_def_list env acc pl idl tyl rty = 
  List.fold_left 
    (fun (acc, rty) fid -> 
      apply_def env acc pl fid tyl rty) 
    (acc, rty) 
    idl
    
and apply_def env acc pl fid tyl rty = 
  try 
    let mem_rty = TMap.find (fid, tyl) acc.mem in 
    let acc, rty = Unify.unify_list env acc rty mem_rty in
    acc, rty 
  with Not_found -> 
    let acc = { mem = TMap.add (fid, tyl) rty acc.mem } in
    let acc, rty = apply_def_ env acc fid tyl rty in
    acc, rty
    
and apply_def_ env acc fid tyl rty = 
  let (_, argl, el) = IMap.find (snd fid) env.defs in
  let env, acc, _ = pat env acc argl tyl in 
  let acc, (new_rty, _) = tuple env acc el in
  let acc = { mem = TMap.add (fid, tyl) new_rty acc.mem } in
  Unify.unify_list env acc new_rty rty
