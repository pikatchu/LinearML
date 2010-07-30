open Utils
open Neast


let o s = output_string stdout s ; print_newline() ; flush stdout

module Debug = struct
  open Tast

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


module FreeVars = struct

  let rec type_expr t (_, ty) = type_expr_ t ty

  and type_expr_ t = function
    | Tundef _
    | Tany
    | Tprim _ 
    | Tid _ -> t
    | Tvar (_, x) -> ISet.add x t

    | Tapply (_, (_, tyl)) -> 
	List.fold_left type_expr t tyl

    | Tfun ((_, tyl1), (_, tyl2)) -> 
	let t = List.fold_left type_expr t tyl1 in
	List.fold_left type_expr t tyl2

    | Tdef _ -> assert false

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
    ufail: bool ;
  }

type acc = {
    mem: type_expr_list TMap.t ;
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
  | _, Tprim (Tint32 _ | Tfloat _) -> ()
  | _, _ -> Error.expected_numeric p

let add_used ((_, x), _) _ acc =
  ISet.add x acc

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
  let env = { tenv = tenv ; defs = IMap.empty ; ufail = false } in
  let env = List.fold_left def env md.md_defs in
  let acc = { mem = TMap.empty } in
  let acc = List.fold_left (decl false env) acc md.md_decls in
  let used = TMap.fold add_used acc.mem ISet.empty in
  List.iter (check_used used) md.md_defs ;
  let calls = TMap.fold (fun x _ acc -> x :: acc) acc.mem [] in
  let mem = TMap.fold filter_undef acc.mem TMap.empty in 
  let acc = { mem = mem } in
  let env = { env with ufail = true } in
  let acc = List.fold_left (decl true env) acc md.md_decls in
  let acc = List.fold_left (retype env) acc calls in 
  acc

and def env (((p, x), al, b) as d) = 
  let tenv = IMap.add x (p, Tdef (IMap.add x p IMap.empty)) env.tenv in
  let defs = IMap.add x d env.defs in
  { env with tenv = tenv ; defs = defs }

and retype env acc (fid, ty) = 
  let p = fst fid in
  let acc, _ = apply env acc p fid ty in
  acc

and decl stop env acc = function
  | Dval (fid, (_, Tfun (tyl, rty))) ->
      let p = fst fid in
      let (_, args, _) = IMap.find (snd fid) env.defs in
      let env, acc, _ = pat env acc args tyl in
      let acc, rty2 = apply env acc p fid tyl in
      Debug.type_expr_list rty2 ;
      if stop && tundef rty2
      then Error.infinite_loop (fst rty2) ;
      let acc, _ = unify_list env acc rty2 rty in
      acc
  | Dval _ -> assert false
  | _ -> acc

and pat env acc (p, pl) (p2, tyl) = 
  match pl with
  | [_,l] -> 
      if List.length l <> List.length tyl
      then Error.arity p p2 ;
      let env, acc, tyl = pat_tuple env acc l tyl in
      env, acc, (p, tyl)

  | _ -> failwith "TODO pat"

and pat_tuple env acc l tyl = 
  match l, tyl with
  | [], [] -> env, acc, []
  | [], _ | _, [] -> assert false
  | p :: rl1, ty :: rl2 ->
      let env, acc, tyl = pat_tuple env acc rl1 rl2 in
      let env, acc, ty = pat_el env acc p ty in
      env, acc, ty :: tyl

and pat_el env acc (pos, p) ((posl, ty) as pty) =
  match p with
  | Pany -> env, acc, pty
  | Pid (_, x) -> 
      (* Has to remember where the type comes from *)
      let ty = pos, ty in
      let env = { env with tenv = IMap.add x ty env.tenv } in
      env, acc, ty

  | Pvariant (x, (p, [])) -> 
      let acc, ty2 = variant env acc (x, (p, [])) in
      (* Position of ty2 has to be redefined otherwise it would *)
      (* point to the type definition *)
      let ty2 = pos, (snd ty2) in
      let acc, ty = unify_el env acc ty2 (posl, ty) in
      env, acc, ty

  | Pvariant (x, args) ->
      let argty, rty = match IMap.find (snd x) env.tenv with
      | _, Tfun (tyl, (_, rty)) -> tyl, (pos, rty)
      | _ -> assert false in
      let pty = posl, [pty] in
      let acc, subst = instantiate_list pos env acc IMap.empty rty pty in
      let acc, tyl = replace_list subst env acc argty in
      let env, acc, tyl = pat env acc args tyl in
      let acc, rty = apply env acc pos x tyl in      
      let rty = match rty with 
      | _, [x] -> x
      | _ -> assert false in
      env, acc, rty

  | _ -> failwith "TODO rest of pat_el"
(*  | Pvariant (x, pa) ->  *)
      
(*  | Pvalue of value
  | Precord of pat_field list *)

and expr_list env acc (p, el) = 
  let acc, tyl = expr_list_ env acc el in
  acc, (p, tyl)

and expr_list_ env acc el =
  match el with
  | [] -> acc, []
  | (p, Eapply (x, el)) :: rl ->
      let acc, rl = expr_list_ env acc rl in
      let acc, tyl = expr_list env acc el in
      let acc, rty = apply env acc p x tyl in
      acc, snd rty @ rl

  | (_, Eif (e1, el1, el2)) :: rl -> 
      let acc, rl = expr_list_ env acc rl in
      let acc, _ = expr env acc e1 in (* TODO check bool *)
      let acc, tyl1 = expr_list env acc el1 in
      let acc, tyl2 = expr_list env acc el2 in     
      let acc, tyl = unify_list env acc tyl1 tyl2 in
      acc, snd tyl @ rl

  | (_, Elet (argl, e1, e2)) :: rl -> 
      let acc, rl = expr_list_ env acc rl in
      let acc, tyl = expr_list env acc e1 in
      let env, acc, _ = pat env acc argl tyl in 
      let acc, tyl = expr_list env acc e2 in
      acc, (snd tyl) @ rl

  | (_, Efield (e, (_, x))) :: rl -> 
      let acc, rl = expr_list_ env acc rl in
      let acc, rectype = expr env acc e in
      let fdtype = IMap.find x env.tenv in 
      let acc, tyl = proj env acc rectype fdtype in
      acc, (snd tyl) @ rl

  | (p, Ematch (el, pel)) :: rl -> 
      let acc, rl = expr_list_ env acc rl in
      let acc, tyl = expr_list env acc el in
      let acc, pel = lfold (action env tyl) acc pel in
      let acc, (_, tyl) = fold_type_lists env acc pel in
      acc, tyl @ rl

  | e :: rl ->
      let acc, tyl = expr_list_ env acc rl in
      let acc, ty = expr_ env acc e in
      acc, ty :: tyl

and action env tyl acc (p, e) = 
  let env, acc, _ = pat env acc p tyl in
  expr_list env acc e

and expr env acc ((p, _) as e) = 
  let acc, el = expr_list env acc (p, [e]) in
  match snd el with
  | [] -> assert false
  | [x] -> acc, x
  | _ -> Error.no_tuple p

and expr_ env acc (p, e) =
  match e with
  | Eid (_, x) -> 
      let pl, e = IMap.find x env.tenv in
      acc, (p, e)
  | Evalue v -> acc, (p, Tprim (value v))
  | Evariant (x, el) -> variant env acc (x, el)

  | Ebinop (Ast.Eseq, ((p, _) as e1), e2) -> 
      let acc, ty1 = expr env acc e1 in
      let acc, ty1 = unify_el env acc ty1 (p, Tprim Tunit) in
      expr env acc e2

  | Ebinop (bop, e1, e2) ->
      let acc, ty1 = expr env acc e1 in
      let acc, ty2 = expr env acc e2 in
      (match bop with
      | Ast.Eplus
      | Ast.Eminus
      | Ast.Estar -> 
	  check_numeric p ty1 ;
	  check_numeric p ty2 
      | _ -> ()) ;
      let acc, _ = unify_el env acc ty1 ty2 in
      let acc, ty = binop env acc bop p ty1 ty2 in
      acc, ty

  | Euop (Ast.Euminus, e) -> expr env acc e

  | Erecord fdl -> 
      let acc, fdl = lfold (variant env) acc fdl in
      fold_types env acc fdl

  | _ -> failwith "TODO expr"

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
  let acc, tyl = expr_list env acc el in
  let acc, rty = apply env acc p x tyl in
  match rty with 
  | _, [x] -> acc, x
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
(*      if IMap.mem x acc.fcall
      then begin (* TODO shout if not same call *)
	let prev_tyl = IMap.find x acc.fcall in
	let acc, tyl = unify_list env acc tyl prev_tyl in
	acc, TMap.find (fid, prev_tyl) acc.mfcall
      end
      else begin *)
	let acc, subst = instantiate_list p env acc IMap.empty tyl1 tyl in
	let acc, rty = replace_list subst env acc tyl2 in
	if env.ufail && tundef rty
	then Error.infinite_loop p ;
(*	let fcall = IMap.add x tyl acc.fcall in
	let mfcall = TMap.add (fid, tyl) rty acc.mfcall in 
	let acc = { acc with fcall = fcall ; mfcall = mfcall } in *)
	acc, rty
(*      end *)

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
    if env.ufail && tundef rty
    then Error.infinite_loop pl ;
    acc, rty 
  with Not_found -> 
    let undef = pl, [pl, Tundef] in
    let acc = { mem = TMap.add (fid, tyl) undef acc.mem } in
    let (_, argl, el) = IMap.find (snd fid) env.defs in
    let env, acc, _ = pat env acc argl tyl in 
    let acc, new_rty = expr_list env acc el in
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

  | Tvar _, (Tdef _ | Tfun _) -> Error.unify pl1 pl2 (* Todo 'a is not a function *)

  | Tvar (_, x), Tvar (_, y) when x = y -> acc, subst
  | Tvar v, _ -> instantiate_var papp env acc subst v (pl2, ty2)

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

  | ty1, ty2 -> Error.unify pl1 pl2

and instantiate_var papp env acc subst (p, x) (pl2, ty2) =
  try 
    let ty1 = IMap.find x subst in
    instantiate papp env (acc, subst) ty1 (pl2, ty2)
  with Not_found -> acc, IMap.add x (pl2, ty2) subst

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
