open Utils
open Neast


let o s = output_string stdout s ; print_newline() ; flush stdout

module Debug = struct
  open Neast

  let id o (_, x) = o (Ident.debug x)

  let rec type_expr o (_, ty) = type_expr_ o ty
  and type_expr_ o ty = 
    match ty with
    | Tdef l -> 
	let l = IMap.fold (fun x _ y -> x :: y) l [] in
	o "Tdef(" ; List.iter (fun x -> o (Ident.debug x) ; o " ") l ; o ")"
    | Tundef _ -> o "Tundef"
    | Tany -> o "Tany"
    | Tprim v -> value o v
    | Tvar x -> o "Tvar" ; o "(" ;  id o x ; o ")"
    | Tid x -> o "Tid" ; o "(" ;  id o x ; o ")"
    | Tapply (ty, tyl) -> o "Tapply" ; o "(" ;  id o ty ; o "," ; list o tyl; o ")"
    | Tfun (ty1, ty2) -> o "Tfun" ; o "(" ;  list o ty1 ; o "->" ; list o ty2; o ")"
(*    | Tdecl x -> o "Tdecl" ; o "(" ; id o x ; o ")" *)

  and tvar o = function
    | [] -> assert false
    | [x] -> id o x
    | x :: rl -> id o x ; o "," ; tvar o rl

  and list o (_, x) = list_ o x
  and list_ o = function
    | [] -> assert false
    | [x] -> type_expr o x
    | x :: rl -> type_expr o x ; o "," ; list_ o rl

  and variant o (x, y) = 
    id o x ; o " of " ; 
    list o y ;
    o "|"

  and value o = function
  | Tunit -> o "Tunit"
  | Tbool -> o "Tbool"
  | Tchar -> o "Tchar"
  | Tint32 -> o "Tint32"
  | Tfloat -> o "Tfloat"

  and field o (x, y) = id o x ; o ":" ; list o y ; o ";"

  let o = output_string stdout
  let nl o = o "\n"
  let type_expr ty = type_expr o ty ; nl o
  let type_expr_list ty = list o ty ; nl o
  let id x = id o x ; nl o

end

module Env = struct

  let rec make mdl = 
    let env = List.fold_left module_ IMap.empty mdl in
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
    match pl with
    | [] -> IMap.add x (p, Tfun (tyl, (p, [p, Tid tid]))) env
    | _ -> 
	let fvs = List.fold_left FreeVars.type_expr ISet.empty (snd tyl) in
	let argl = List.map (tvar fvs) pl in
	let argl = p, argl in
	let v_ty = p, Tfun (tyl, (p, [p, Tapply (tid, argl)])) in
	IMap.add x v_ty env

  and tvar fvs ((p, x) as id) =
    p, if ISet.mem x fvs 
    then Tvar id
    else Tany
end
open Neast

module TMap = Map.Make (CompareType)

type env = {
    tenv: type_expr IMap.t ;
    defs: def IMap.t ;
    decls: bool TMap.t ;
    phase2: bool ;
  }

type acc = {
    mem: type_expr_list TMap.t ;
  }

let empty tenv = { 
  tenv = tenv ; 
  defs = IMap.empty ; 
  phase2 = false ; 
  decls = TMap.empty ;
}

let rec tundef (_, tyl) = tundef_ tyl
and tundef_ tyl = 
  match tyl with
  | [] -> false
  | (_, Tundef _) :: _ -> true
  | (_, Tapply (_, l)) :: rl -> tundef l || tundef_ rl
  | _ :: rl -> tundef_ rl

let check_numeric p ty = 
  match ty with
  | _, Tundef | _, Tany
  | _, Tprim (Tint32 _ | Tfloat _) -> ()
  | _, _ -> Error.expected_numeric p

let check_bool ((p, ty), _) = 
  match ty with
  | Tundef | Tany | Tprim Tbool -> ()
  | _ -> Error.expected_bool p

let check_used uset (id, _, _) = 
  if not (ISet.mem (snd id) uset) 
  then Error.unused (fst id) 
  else ()

let filter_undef x rty acc = 
  if tundef rty
  then acc
  else TMap.add x rty acc

let rec program mdl = 
  let tenv = Env.make mdl in
  List.map (module_ tenv) mdl
  
and module_ tenv md = 
  let env = empty tenv in
  let env = List.fold_left def env md.md_defs in
  let decls = List.fold_left get_decl TMap.empty md.md_decls in
  let env = { env with decls = decls } in
  let acc = { mem = TMap.empty } in
  let acc = List.fold_left (decl env) acc md.md_decls in
  let used = ISet.empty in
  let used = IMap.fold (fun x _ acc -> ISet.add x acc) env.defs used in
  let used = TMap.fold (fun ((_, x), _) _ y -> ISet.add x y) acc.mem used in
  List.iter (check_used used) md.md_defs ;
  let mem = TMap.fold filter_undef acc.mem TMap.empty in 
  let acc = { mem = mem } in
  let env = { env with phase2 = true } in
  let acc = List.fold_left (decl env) acc md.md_decls in
  let ads = acc, [], IMap.empty in
  let _, defs, subst = TMap.fold (typed_def env) acc.mem ads in 
  let md = { 
    Tast.md_id = md.md_id ;
    Tast.md_decls = md.md_decls ;
    Tast.md_defs = defs ;
  } in
  Tast.Rename.module_ subst md

and def env (((p, x), al, b) as d) =
  let tenv = IMap.add x (p, Tdef (IMap.add x p IMap.empty)) env.tenv in
  let defs = IMap.add x d env.defs in
  { env with tenv = tenv ; defs = defs }

and decl env acc = function
  | Dval (fid, (_, Tfun (tyl, rty))) ->
      let (_, args, e) = IMap.find (snd fid) env.defs in      
      let env, acc, _ = pat env acc args tyl in
      let acc, (rty2, _) = tuple env acc e in
      if env.phase2 && tundef rty2
      then Error.infinite_loop (fst rty2) ;
      let acc, rty = unify_list env acc rty2 rty in
      let acc = { mem = TMap.add (fid, tyl) rty acc.mem } in
      acc
  | Dval _ -> assert false
  | _ -> acc

and get_decl acc = function
  | Dval (fid, (_, Tfun (tyl, _))) -> 
      TMap.add (fid, tyl) true acc
  | _ -> acc

and typed_def env ((p, f), tyl) rty (acc, defs, subst) = 
  let (fid, args, e) = IMap.find f env.defs in
  let env, acc, args = pat env acc args tyl in
  let acc, ((rty2, _) as e) = tuple env acc e in
  if tundef rty2
  then Error.infinite_loop (fst rty2) ;
  let acc, rty = unify_list env acc rty2 rty in
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
      if List.length l_ <> List.length tyl
      then Error.arity p1 p2 ;
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
  match p with
  | Pany -> env, acc, (pty, Tast.Pany)
  | Pid ((_, x) as id) -> 
      let env = { env with tenv = IMap.add x pty env.tenv } in
      env, acc, (pty, Tast.Pid id)

  | Pvariant (x, (_, [])) -> 
      let acc, (ty2, _) = variant env acc (x, (pos, [])) in
      let ty2 = pos, (snd ty2) in
      let acc, ty = unify_el env acc ty2 pty in
      env, acc, (ty, Tast.Pvariant (x, ((pos, []), [])))

  | Pvariant (x, args) ->
      let env, acc, rty, args = pat_variant env acc x args pty in
      env, acc, (rty, Tast.Pvariant (x, args))

  | Pvalue v -> 
      let acc, rty = unify_el env acc (pos, Tprim (value v)) pty in
      env, acc, (rty, Tast.Pvalue v)
      
  | Precord pfl -> 
      let (env, acc), pfl = lfold (pat_field pty) (env, acc) pfl in
      let tyl = List.map fst pfl in
      let pfl = List.map snd pfl in
      let acc, ty = fold_types env acc tyl in 
      env, acc, (ty, Tast.Precord pfl)

and pat_field pty (env, acc) (p, pf) = 
  let pty = p, snd pty in
  match pf with
  | PFany -> (env, acc), (pty, (p, Tast.PFany))

  | PFid ((_, x) as id) -> 
      let env = { env with tenv = IMap.add x pty env.tenv } in
      (env, acc), (pty, (p, Tast.PFid id))

  | PField (id, args) ->
      let env, acc, rty, args = pat_variant env acc id args pty in
      (env, acc), (rty, (p, Tast.PField (id, args)))

and pat_variant env acc x args pty =
  let argty, rty = match IMap.find (snd x) env.tenv with
  | _, Tfun (tyl, rty) -> tyl, rty
  | _ -> assert false in
  let pty = fst pty, [pty] in 
  let acc, subst = instantiate_list (fst pty) env acc IMap.empty rty pty in
  let acc, tyl = replace_list subst env acc argty in
  let env, acc, ((tyl, _) as args) = pat env acc args tyl in
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
      let acc, e1 = expr env acc e1 in (* TODO check bool *)
      check_bool e1 ;
      let acc, ((tyl1, _) as el1) = tuple env acc el1 in
      let acc, ((tyl2, _) as el2) = tuple env acc el2 in     
      let acc, tyl = unify_list env acc tyl1 tyl2 in
      acc, (tyl, Tast.Eif (e1, el1, el2))

  | Elet (argl, e1, e2) -> 
      let acc, ((tyl, _) as e1) = tuple env acc e1 in
      let env, acc, argl = pat env acc argl tyl in 
      let acc, ((tyl, _) as e2) = tuple env acc e2 in
      acc, (tyl, Tast.Elet (argl, e1, e2))

  | Efield (e, ((_, x) as fd_id)) -> 
      let acc, ((ty, _) as e) = expr env acc e in
      let fdtype = IMap.find x env.tenv in 
      let acc, tyl = proj env acc ty fdtype in
      acc, (tyl, Tast.Efield (e, fd_id))

  | Ematch (el, pel) -> 
      let acc, ((tyl, _) as el) = tuple env acc el in
      let acc, pel = lfold (action env tyl) acc pel in
      let tyl = List.map fst pel in
      let pel = List.map snd pel in
      let acc, tyl = fold_type_lists env acc tyl in
      acc, (tyl, Tast.Ematch (el, pel)) 

  | e ->
      let acc, (ty, e) = expr_ env acc (p, e) in
      acc, ((p, [ty]), e)

and expr env acc ((p, _) as e) = 
  let acc, el = tuple env acc (p, [e]) in
  match snd el with
  | [] -> assert false
  | [(_, [ty]), e] -> acc, (ty, e)
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

  | Evariant (x, el) -> 
      let acc, (ty, (x, el)) = variant env acc (x, el) in
      acc, (ty, Tast.Evariant (x, el))

  | Ebinop (Ast.Eseq, ((p, _) as e1), e2) -> 
      let acc, (ty1, e1) = expr env acc e1 in
      let acc, ty1 = unify_el env acc ty1 (p, Tprim Tunit) in
      let e1 = ty1, e1 in
      let acc, (ty, _ as e2) = expr env acc e2 in
      acc, (ty, Tast.Ebinop (Ast.Eseq, e1, e2))

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
      let acc, _ = unify_el env acc ty1 ty2 in
      let acc, ty = binop env acc bop p ty1 ty2 in
      acc, (ty, Tast.Ebinop (bop, e1, e2))

  | Euop (Ast.Euminus, e) -> 
      let acc, (ty, _ as e) = expr env acc e in
      acc, (ty, Tast.Euop (Ast.Euminus, e))

  | Erecord fdl -> 
      let acc, fdl = lfold (variant env) acc fdl in
      let tyl = List.map fst fdl in
      let fdl = List.map snd fdl in
      let acc, ty = fold_types env acc tyl in
      acc, (ty, Tast.Erecord fdl)

  | Eapply (_, _)
  | Eif (_, _, _)
  | Elet (_, _, _)
  | Ematch (_, _)
  | Efield (_, _) -> assert false

and action env tyl acc (p, e) = 
  let env, acc, p = pat env acc p tyl in
  let acc, ((tyl, _) as e) = tuple env acc e in
  acc, (tyl, (p, e))

and fold_types env acc tyl = 
  match tyl with
  | [] -> assert false
  | ty :: tyl -> 
      List.fold_left 
	(fun (acc, rty) ty -> 
	  unify_el env acc rty ty) 
	(acc, ty)
	tyl

and fold_type_lists env acc tyll = 
  match tyll with
  | [] -> assert false
  | tyl :: rl ->
      List.fold_left 
	(fun (acc, rty) ty -> 
	  unify_list env acc rty ty) 
	(acc, tyl)
	rl

and variant env acc (x, el) = 
  let p = Pos.btw (fst x) (fst el) in
  let acc, ((tyl, _) as el) = tuple env acc el in
  let acc, rty = apply env acc p x tyl in
  match rty with 
  | _, [rty] -> acc, (rty, (x, el))
  | _ -> assert false

and proj env acc ty fty = 
  match ty, fty with
  | (p, Tapply ((_, x1), argl1)), (_, Tfun (ty, (_, [_, Tapply ((_, x2), argl2)]))) ->
      if x1 <> x2
      then failwith "TODO proj" ;
      let acc, subst = instantiate_list p env acc IMap.empty argl2 argl1 in
      replace_list subst env acc ty
  | _ -> failwith "TODO proj"

and binop env acc bop p ty1 ty2 = 
  match bop with
  | Ast.Eeq 
  | Ast.Elt
  | Ast.Elte
  | Ast.Egt
  | Ast.Egte -> acc, (p, Tprim Tbool)
  | Ast.Eplus
  | Ast.Eminus
  | Ast.Estar -> unify_el env acc ty1 ty2
  | Ast.Eseq -> assert false
  | Ast.Ederef -> assert false

and value = function
  | Nast.Eunit -> Tunit
  | Nast.Ebool _ -> Tbool
  | Nast.Eint _ -> Tint32
  | Nast.Efloat _ -> Tfloat
  | Nast.Echar _ -> Tchar
  | Nast.Estring _ -> assert false


and unify_list env acc ((p1, tyl1) as l1) ((p2, tyl2) as l2) = 
  if tundef l1
  then acc, l2
  else if tundef l2
  then acc, l1
  else if List.length tyl1 <> List.length tyl2
  then Error.arity p1 p2
  else 
    let acc, tyl = lfold2 (unify_el env) acc tyl1 tyl2 in
    acc, (p1, tyl)
  
and unify_el env acc ty1 ty2 = 
  match ty1, ty2 with
  | (p, Tdef ids), (_, Tfun (tyl, rty))
  | (_, Tfun (tyl, rty)), (p, Tdef ids) ->
      let idl = IMap.fold (fun x _ acc -> (p, x) :: acc) ids [] in
      let acc, rty = apply_def_list env acc p idl tyl rty in
      acc, (p, Tfun (tyl, rty))

  | (p, Tapply ((_, x) as id, tyl1)), (_, Tapply ((_, y), tyl2)) when x = y -> 
      let acc, tyl = unify_list env acc tyl1 tyl2 in 
      acc, (p, Tapply (id, tyl))

  | (p, Tfun (tyl1, tyl2)), (_, Tfun (tyl3, tyl4)) ->
      let acc, tyl1 = unify_list env acc tyl1 tyl3 in
      let acc, tyl2 = unify_list env acc tyl2 tyl4 in
      acc, (p, Tfun (tyl1, tyl2))
     
  | (p, _), _ -> 
      let ty = unify_el_ env acc ty1 ty2 in
      acc, (p, ty)

and unify_el_ env acc (p1, ty1) (p2, ty2) =
  match ty1, ty2 with
  | Tundef, Tundef -> Tundef
  | Tundef, ty
  | ty, Tundef -> ty
  | Tany, ty 
  | ty, Tany -> ty
  | Tprim x, Tprim y when x = y -> ty1
  | Tvar (_, x), Tvar (_, y) when x = y -> ty1
  | Tid (_, x), Tid (_, y) when x = y -> ty1
  | Tdef s1, Tdef s2 -> Tdef (IMap.fold IMap.add s1 s2)
  | _ -> Error.unify p1 p2 

and apply env acc p (fp, x) tyl = 
  match IMap.find x env.tenv with
  | (_, Tfun (tyl1, tyl2)) -> 
	let acc, subst = instantiate_list p env acc IMap.empty tyl1 tyl in
	let acc, rty = replace_list subst env acc tyl2 in
	if env.phase2 && tundef rty
	then Error.infinite_loop p ;
	acc, rty

  | (_, Tdef ids) -> 
      let rty = p, [p, Tundef] in
      let idl = IMap.fold (fun x _ acc -> (p, x) :: acc) ids [] in
      apply_def_list env acc p idl tyl rty

  | p2, ty -> 
      Debug.type_expr (p2, ty) ;
      Error.expected_function fp (* TODO *)

and apply_def_list env acc pl idl tyl rty = 
  List.fold_left 
    (fun (acc, rty) fid -> 
      apply_def env acc pl fid tyl rty) 
    (acc, rty) 
    idl
    
and apply_def env acc pl fid tyl rty = 
  try 
    let rty = TMap.find (fid, tyl) acc.mem in 
    if env.phase2 && tundef rty
    then Error.infinite_loop pl ;
    acc, rty 
  with Not_found -> 
    let undef = pl, [pl, Tundef] in
    let acc = { mem = TMap.add (fid, tyl) undef acc.mem } in
    let (_, argl, el) = IMap.find (snd fid) env.defs in
    let env, acc, _ = pat env acc argl tyl in 
    let acc, (new_rty, _) = tuple env acc el in
    let acc = { mem = TMap.add (fid, tyl) new_rty acc.mem } in
    unify_list env acc new_rty rty

and instantiate_list papp env acc subst (p1, tyl1) (p2, tyl2) = 
  if List.length tyl1 <> List.length tyl2
  then Error.arity p1 p2
  else List.fold_left2 (instantiate papp env) (acc, subst) tyl1 tyl2
            
and instantiate papp env (acc, subst) (pl1, ty1) (pl2, ty2) = 
  match ty1, ty2 with
  | (Tany | Tundef), _
  | _, (Tany | Tundef) -> acc, subst
  | Tprim ty1, Tprim ty2 when ty1 = ty2 -> acc, subst
  | Tvar (_, x), Tvar (_, y) when x = y -> acc, subst
  | Tvar v, _ -> instantiate_var papp env acc subst v (pl2, ty2)

  | Tid (_, x), Tid (_, y) when x = y -> acc, subst
  | Tapply ((_, x), tyl1), Tapply ((_, y), tyl2) when x = y ->
      instantiate_list papp env acc subst tyl1 tyl2

  | Tfun (tyl, rty1), Tdef ids -> 
      let pdef = pl2 in
      let idl = IMap.fold (fun x _ acc -> (pdef, x) :: acc) ids [] in
      let rty = pdef, [pl2, Tundef] in
      let acc, rty2 = apply_def_list env acc pl2 idl tyl rty in
      instantiate_list papp env acc subst rty1 rty2

  | Tdef _, _ -> assert false
  | Tfun (tyl1, tyl3), Tfun (tyl2, tyl4) -> 
      let acc, subst = instantiate_list papp env acc subst tyl1 tyl2 in
      let acc, subst = instantiate_list papp env acc subst tyl3 tyl4 in
      acc, subst

  | ty1, ty2 -> 
      Debug.type_expr (pl1, ty1) ;
      Debug.type_expr (pl1, ty2) ;
      Error.unify pl1 pl2 (* TODO bad positions *)

and instantiate_var papp env acc subst (_, x) (p, ty2) =
  try 
    let ty1 = IMap.find x subst in
    let fv = FreeVars.type_expr ISet.empty ty1 in
    if ISet.mem x fv
    then Error.recursive_type p
    else instantiate papp env (acc, subst) ty1 (p, ty2)
  with Not_found -> acc, IMap.add x (p, ty2) subst

and replace subst env acc (p, ty) = 
  match ty with
  | Tundef _ as x -> acc, (p, x)
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
  try replace subst env acc (IMap.find x subst)
  with Not_found -> acc, (p, Tvar (p, x))

and replace_list subst env acc (p, tyl) = 
  let acc, tyl = lfold (replace subst env) acc tyl in
  let tyl = p, tyl in
  acc, tyl
