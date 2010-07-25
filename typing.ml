open Utils
open Neast

module Debug = struct
  open Tast

  let id o (_, x) = o (Ident.debug x)

  let rec type_expr o (_, ty) = type_expr_ o ty
  and type_expr_ o ty = 
    let k = type_expr o in
    match ty with
    | Tdef _ -> o "Tdef"
    | Tundef _ -> o "Tundef"
    | Tany -> o "Tany"
    | Tprim v -> value o v
    | Tvar x -> o "Tvar" ; o "(" ;  id o x ; o ")"
    | Tid x -> o "Tid" ; o "(" ;  id o x ; o ")"
    | Tapply (ty, tyl) -> o "Tapply" ; o "(" ;  id o ty ; o "," ; list o tyl; o ")"
    | Tfun (ty1, ty2) -> o "Tfun" ; o "(" ;  list o ty1 ; o "->" ; list o ty2; o ")"
    | Talgebric vl -> o "Talgebric" ; o "[" ; imiter (variant o) vl ; o "]"
    | Trecord fdl -> o "Trecord" ; o "{" ;  imiter (field o) fdl; o "}"
    | Tabs (idl, ty) -> o "Tabs" ; o "(" ; tvar o idl ; o ": " ; k ty; o ")"
(*    | Tdecl x -> o "Tdecl" ; o "(" ; id o x ; o ")" *)

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

end


module FreeVars = struct

  let rec type_expr t (_, ty) = type_expr_ t ty

  and type_expr_ t = function
    | Tundef _
    | Tany
    | Tprim _ 
    | Tid _ -> t
    | Tvar (_, x) -> ISet.add x t

    | Tapply (_, tyl) -> 
	List.fold_left type_expr t tyl

    | Tfun (tyl1, tyl2) -> 
	let t = List.fold_left type_expr t tyl1 in
	List.fold_left type_expr t tyl2


    | Tdef _
    | Talgebric _ 
    | Trecord _ 
    | Tabs _ -> assert false


end

module Env = struct

  let rec make mdl = 
    let env = List.fold_left module_ IMap.empty mdl in
    env

  and module_ env md = 
    List.fold_left decl env md.md_decls 

  and decl env = function
    | Dtype tdl -> List.fold_left type_expr env tdl
    | Dval ((p, x), tyl1, tyl2) -> IMap.add x (p, Tfun (tyl1, tyl2)) env

  and type_expr env ((_, x) as tid, ((_, ty_) as ty)) = 
    match ty_ with
    | Trecord vm 
    | Talgebric vm -> algebric env [] tid vm
    | Tabs (pl, (_, Talgebric vm)) 
    | Tabs (pl, (_, Trecord vm)) -> algebric env pl tid vm
    | _ -> IMap.add x ty env

  and algebric env pl tid vm =
    IMap.fold (variant pl tid) vm env

  and variant pl tid _ ((p, x), tyl) env = 
    match pl with
    | [] -> IMap.add x (p, Tfun (tyl, [fst tid, Tid tid])) env
    | _ -> 
	let fvs = List.fold_left FreeVars.type_expr ISet.empty tyl in
	let argl = List.map (tvar fvs) pl in
	let v_ty = p, Tfun (tyl, [p, Tapply (tid, argl)]) in
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
  }

let rec tundef tyl = 
  match tyl with
  | [] -> false
  | (_, Tundef _) :: _ -> true
  | _ :: rl -> tundef rl

let rec check_undef p tyl =
  match tyl with
  | [] -> ()
  | (_, Tundef) :: _ -> Error.infinite_loop p
  | _ :: rl -> check_undef p rl

let add_used ((_, x), _) _ acc =
  ISet.add x acc

let check_used uset (id, _, _) = 
  if not (ISet.mem (snd id) uset) 
  then Error.unused (fst id) 
  else ()

let filter_undef x rty (acc1, acc2) = 
  if tundef rty
  then x :: acc1, acc2
  else acc1, TMap.add x rty acc2

let rec program mdl = 
  let tenv = Env.make mdl in
  List.map (module_ tenv) mdl
  
and module_ tenv md = 
  let env = { tenv = tenv ; defs = IMap.empty } in
  let env = List.fold_left def env md.md_defs in
  let mem = List.fold_left (decl env) TMap.empty md.md_decls in
  let used = TMap.fold add_used mem ISet.empty in
  List.iter (check_used used) md.md_defs ;
  let undef_l, mem = TMap.fold filter_undef mem ([], TMap.empty) in
  let mem = List.fold_left (retype env) mem undef_l in
  (* Re-type all with function calls solved *)
  let mem = List.fold_left (decl env) mem md.md_decls in
  mem

and def env (((p, x) as id, al, b) as d) = 
  let tenv = IMap.add x (p, Tdef [id]) env.tenv in
  let defs = IMap.add x d env.defs in
  { tenv = tenv ; defs = defs }

and retype env mem (fid, ty) = 
  let mem, rty = apply env mem fid ty in
  let pos, _  = Pos.list rty in
  check_undef pos rty ;
  mem

and decl env mem = function
  | Dtype _ -> mem
  | Dval (id, tyl1, tyl2) ->
      let mem, rty = apply_def env tyl1 (mem, tyl2) id in
      List.iter (Debug.type_expr) rty ;
      mem

and pat env (p, pl) tyl = 
  match pl with
  | [_,l] -> 
      (try List.fold_right2 pat_el l tyl env
      with Invalid_argument _ -> failwith "TODO arity mismatch pat")
  | _ -> failwith "TODO pat"

and pat_el (pos, p) (_, ty) env = 
  let ty = pos, ty in
  match p with
  | Pany -> env
  | Pid (_, x) -> IMap.add x ty env 
  | _ -> failwith "TODO pat"
(*  | Pvalue of value
  | Pvariant of id * pat
  | Precord of pat_field list *)


and expr_list env mem el =
  match el with
  | [] -> mem, []
  | (_, Eapply (x, el)) :: rl
  | (_, Evariant (x, el)) :: rl ->
      let mem, rl = expr_list env mem rl in
      let mem, tyl = expr_list env mem el in
      let mem, rty = apply env mem x tyl in
      mem, rty @ rl

  | (_, Eif (e1, el1, el2)) :: rl -> 
      let mem, rl = expr_list env mem rl in
      let mem, _ = expr env mem e1 in (* TODO check bool *)
      let mem, tyl1 = expr_list env mem el1 in
      let mem, tyl2 = expr_list env mem el2 in     
      let mem, tyl = unify_list env mem tyl1 tyl2 in
      mem, tyl @ rl

  | e :: rl ->
      let mem, tyl = expr_list env mem rl in
      let mem, ty = expr env mem e in
      mem, ty :: tyl

and expr env mem (p, e) =
  match e with
  | Eid (_, x) -> mem, (p, snd (IMap.find x env.tenv))
  | Evalue v -> mem, (p, Tprim (value v))
  | Ebinop (bop, e1, e2) -> 
      let mem, ty1 = expr env mem e1 in
      let mem, ty2 = expr env mem e2 in
      let mem, ty = binop env mem bop p ty1 ty2 in
      mem, ty

  | Euop (Ast.Euminus, e) -> expr env mem e
(*  | Erecord of (id * expr list) list 
  | Efield of expr * id 
  | Ematch of expr list * (pat * expr list) list
  | Elet of pat * expr list * expr list

  | Efun of pat * expr list *)

and binop env mem bop p ty1 ty2 = 
  match bop with
  | Ast.Eeq 
  | Ast.Elt
  | Ast.Elte
  | Ast.Egt
  | Ast.Egte -> mem, (p, Tprim Tbool)
  | Ast.Eplus
  | Ast.Eminus
  | Ast.Estar -> unify_el env mem ty1 ty2
  | Ast.Eseq -> mem, ty2
  | Ast.Ederef -> assert false

and value = function
  | Nast.Eunit -> Tunit
  | Nast.Ebool _ -> Tbool
  | Nast.Eint _ -> Tint32
  | Nast.Efloat _ -> Tfloat
  | Nast.Echar _ -> Tchar
  | Nast.Estring _ -> assert false

and unify_list env mem tyl1 tyl2 = 
  if tundef tyl1
  then mem, tyl2
  else if tundef tyl2
  then mem, tyl1
  else if List.length tyl1 <> List.length tyl2
  then begin
    let p1, _ = Pos.list tyl1 in
    let p2, _ = Pos.list tyl2 in
    Debug.type_expr_list tyl1 ;
    Debug.type_expr_list tyl2 ;
    Error.arity p1 p2
  end
  else lfold2 (unify_el env) mem tyl1 tyl2 
  
and unify_el env mem ty1 ty2 = 
  match ty1, ty2 with
  | (p, Tdef idl), (_, Tfun (tyl, rty))
  | (_, Tfun (tyl, rty)), (p, Tdef idl) ->
      let mem, rty = apply_def_list env tyl (mem, rty) idl in
      mem, (p, Tfun (tyl, rty))

  | (p, Tapply (x, tyl1)), (_, Tapply (y, tyl2)) when x = y -> 
      let mem, tyl = unify_list env mem tyl1 tyl2 in 
      mem, (p, Tapply (x, tyl))

  | (p, Tfun (tyl1, tyl2)), (_, Tfun (tyl3, tyl4)) -> 
      let mem, tyl1 = unify_list env mem tyl1 tyl3 in
      let mem, tyl2 = unify_list env mem tyl2 tyl4 in
      mem, (p, Tfun (tyl1, tyl2))
     
  | (p, _), _ -> 
      let ty = unify_el_ env mem ty1 ty2 in
      mem, (p, ty)

and unify_el_ env mem (p1, ty1) (p2, ty2) =
  match ty1, ty2 with
  | Tundef, Tundef -> Tundef
  | Tundef, ty
  | ty, Tundef -> ty
  | Tany, ty 
  | ty, Tany -> ty
  | Tprim x, Tprim y when x = y -> ty1
  | Tvar x, Tvar y when x = y -> ty1
  | Tid x, Tid y when x = y -> ty1
  | Tdef l1, Tdef l2 -> Tdef (l1 @ l2)

  | Talgebric _, _ | _, Talgebric _
  | Trecord _, _ | _, Trecord _
  | Tabs _, _ | _, Tabs _ -> assert false
  | _ -> Error.unify p1 p2

and apply env mem fid tyl = 
  try mem, TMap.find (fid, tyl) mem
  with Not_found -> apply_fun env mem fid tyl

and apply_fun env mem ((fp, x) as fid) tyl = 
  match IMap.find x env.tenv with
  | (_, Tfun (tyl1, tyl2)) ->
      let _, argl, el = IMap.find x env.defs in
      let subst = instantiate_list IMap.empty tyl1 tyl in
      let rty = replace_list subst tyl2 in
      let mem = TMap.add (fid, tyl) rty mem in
      let tenv = pat env.tenv argl tyl in	
      let env = { env with tenv = tenv } in
      expr_list env mem el

  | (_, Tdef idl) -> 
      let rty = [fp, Tundef] in
      apply_def_list env tyl (mem, rty) idl
  | p2, _ -> Error.expected_function_not fp p2

and apply_def_list env tyl (mem, rty) idl = 
  List.fold_left (apply_def env tyl) (mem, rty) idl
    
and apply_def env tyl (mem, rty) fid = 
  let ((pos_def, _), argl, el) = IMap.find (snd fid) env.defs in
  let tenv = pat env.tenv argl tyl in 
  let env = { env with tenv = tenv } in
  let mem = TMap.add (fid, tyl) rty mem in
  let mem, new_rty = expr_list env mem el in
  let mem = TMap.add (fid, tyl) new_rty mem in
  unify_list env mem new_rty rty
      
and instantiate subst (_, ty1) (p, ty2) = 
  match ty1, ty2 with
  | Tvar (_, x), _ -> IMap.add x (p, ty2) subst
  | Tapply (_, tyl1), Tapply (_, tyl2) -> (* TODO *)
      instantiate_list subst tyl1 tyl2
  | Tfun (tyl1, tyl3), Tfun (tyl2, tyl4) -> 
      let subst = instantiate_list subst tyl1 tyl2 in
      let subst = instantiate_list subst tyl3 tyl4 in
      subst
  | Talgebric _, _ -> assert false
  | Trecord _, _ -> assert false
  | Tabs (_, ty1), Tabs (_, ty2) -> instantiate subst ty1 ty2
  | _, _ -> subst (* TODO *)

and instantiate_list subst tyl1 tyl2 = 
  Printf.printf "%d %d\n" (List.length tyl1) (List.length tyl2) ;
  List.fold_left2 instantiate subst tyl1 tyl2

and replace subst (p, ty) = 
  match ty with
  | Tundef _ as x -> p, x
  | Tvar (_, x) -> (try IMap.find x subst with Not_found -> assert false)
  | Tapply (x, tyl) -> p, Tapply (x, List.map (replace subst) tyl)
  | Tfun (tyl1, tyl2) -> p, Tfun (List.map (replace subst) tyl1, List.map (replace subst) tyl2)
  | Talgebric _ 
  | Trecord _ -> assert false
  | Tabs (l, ty) -> p, Tabs (l, replace subst ty) 
  | _ -> p, ty

and replace_list subst tyl = List.map (replace subst) tyl


