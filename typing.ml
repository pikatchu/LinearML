open Utils
open Nast

type env = {
    types: Tast.type_expr IMap.t ;
    defs: (Nast.pat list * Nast.expr) IMap.t ;
  }

module Expand = struct
  open Tast
  module PSet = Set.Make(Pos)

  type env = {
      types: Tast.type_expr IMap.t ;
      apath: PSet.t ;
      mpath: Tast.id list * ISet.t ;
    }

  let mem_path x (_, s) = 
    ISet.mem x s

  let path x (l,s) = 
    let l = x :: l in
    let s = ISet.add (snd x) s in
    l, s
    
  let module_path env md_id = 
    if ISet.mem (snd md_id) (snd env.mpath)
    then failwith "Cyclic module path" ;
    { env with mpath = path md_id env.mpath }

  let abbrev_path env p = 
    Printf.printf "here\n" ;
    if PSet.mem p env.apath
    then failwith "Cyclic abbrev path" ;
    { env with apath = PSet.add p env.apath }

  let rec is_abbrev env = function
    | Tabbrev _ -> true
    | Tabs (_, ty) 
    | Tinst_abs (_, ty) -> is_abbrev env (snd ty)
    | Tid (_, x) -> is_abbrev env (snd (IMap.find x env.types))
    | _ -> false

  let rec program types = 
    let env = { 
      types = types ;
      apath = PSet.empty ;
      mpath = [], ISet.empty ;
    } in
    IMap.fold (def env) types IMap.empty

  and def env id ty acc = 
    let pos = fst ty in
    let acc, _ = type_expr env acc (pos, Tid (pos, id)) in
    acc

  and type_expr env acc (p, ty) = 
    match ty with
    | Tabbrev ty -> 
	let env = abbrev_path env p in
	type_expr env acc ty
    | Tpath (md_id, x) -> 
	let env = module_path env md_id in
	type_expr env acc (p, (Tid x))
    | _ -> 
	let acc, ty = type_expr_ env p acc ty in
	acc, (p, ty)
      
  and type_expr_ env p acc = function
    | Tunit | Tbool | Tint32
    | Tfloat | Tvar _ | Tlocal _
    | Tinst_var _ as x -> acc, x
    | Tpath _ | Tabbrev _ -> assert false
    | Tid (_, x) when IMap.mem x acc -> 
	acc, snd (IMap.find x acc)
    | Tid (_, x) as tid -> 
	let ty = IMap.find x env.types in
	if is_abbrev env (snd ty)
	then
	  let acc, ty = type_expr env acc ty in
	  let acc = IMap.add x ty acc in
	  acc, snd ty
	else acc, tid
    | Tapply (ty, tyl) -> 
	let acc, ty = type_expr env acc ty in
	let acc, tyl = lfold (type_expr env) acc tyl in
	acc, Tapply(ty, tyl)
    | Ttuple tyl -> 
	let acc, tyl = lfold (type_expr env) acc tyl in
	acc, Ttuple tyl
    | Tfun (ty1, ty2) -> 
	let acc, ty1 = type_expr env acc ty1 in
	let acc, ty2 = type_expr env acc ty2 in
	acc, Tfun (ty1, ty2)
    | Talgebric vl -> 
	let env = { env with apath = PSet.empty } in
	let acc, vl = lfold (variant env) acc vl in
	acc, Talgebric vl
    | Trecord fl -> 
	let acc, fl = lfold (field env) acc fl in
	acc, Trecord fl 
    | Tabs (idl, ty) -> 
	let acc, ty = type_expr env acc ty in
	acc, Tabs (idl, ty)
    | Tinst_abs (idl, ty) -> 
	let acc, ty = type_expr env acc ty in
	acc, Tabs (idl, ty)

  and variant env acc (x,tyo) = 
    match tyo with
    | None -> acc, (x, None)
    | Some ty ->
	let acc, ty = type_expr env acc ty in
	acc, (x, Some ty)

  and field env acc (x, y) = 
    let acc, ty = type_expr env acc y in
    acc, (x, ty)
end

module Type = struct
  open Tast


  let rec unify env ((p1, left) as ty1) ((p2, right) as ty2) = 
    match left, right with
    | Tvar _, ty | ty, Tvar _ -> p1, ty
    | Tunit, Tunit
    | Tbool, Tbool
    | Tint32, Tint32
    | Tfloat, Tfloat -> ty1
    | Tinst_var id1, Tinst_var id2 when snd id1 = snd id2 -> ty1

    | Tid (_, x), _ -> 
	let _, x_ty = IMap.find x env.types in
	unify env (p1, x_ty) ty2

    | _, Tid (_, x) -> 
	let _, x_ty = IMap.find x env.types in
	unify env ty1 (p2, x_ty)

    | Tabbrev (_, ty), _ -> unify env (p1, ty) ty2
    | _, Tabbrev (_, ty) -> unify env ty1 (p2, ty)

    | Ttuple tyl1, Ttuple tyl2 -> p1, Ttuple (unify_tuple env tyl1 tyl2)

(*    | Tapply (Tid x, tyl), ty 
    | ty, Tapply (Tid x, tyl) ->
	(match IMap.find x env.types with
	| Tabs (idl, body) ->
	    let env = assoc env idl tyl in
	    unify env body ty
	| _ -> failwith "TODO typing.ml Tapply expected abs") *)

(*    | Tapply (Tpath (x,y), tyl),  ->
    | Tapply _ -> assert false    
	
    | Tpath of id * id
    | Tfun of type_expr * type_expr
    | Talgebric of (id * type_expr option) list
    | Trecord of (id * type_expr) list *)

  and unify_tuple env tyl1 tyl2 = 
    match tyl1, tyl2 with
    | [], [] -> []
    | [], _
    | _, [] -> failwith "Arity mismatch"
    | (_, Ttuple l1) :: rl1, l2 -> unify_tuple env (l1 @ rl1) l2
    | l1, (_, Ttuple l2) :: rl2 -> unify_tuple env l1 (l2 @ rl2)
    | ty1 :: rl1, ty2 :: rl2 -> 
	unify env ty1 ty2 :: unify_tuple env rl1 rl2

  let unify env ty1 ty2 = snd (unify env ty1 ty2)


  let rec instantiate env (p, ty) = p, instantiate_ env ty
  and instantiate_ env = function
    | Tunit -> Tunit
    | Tbool -> Tbool
    | Tint32 -> Tint32
    | Tfloat -> Tfloat
    | Tvar x -> Tinst_var x 
    | Tabs (x, y) -> Tinst_abs (x, y)
    | Tinst_var _ -> assert false
    | Tinst_abs _ -> assert false
    | Tid x -> Tid x
    | Tapply (ty, tyl) -> 
	Tapply (instantiate env ty, (List.map (instantiate env) tyl))
    | Ttuple tyl -> Ttuple (List.map (instantiate env) tyl)
    | Tpath (id1, id2) -> Tpath (id1, id2)
    | Tfun (ty1, ty2) -> Tfun (instantiate env ty1, instantiate env ty2)
    | Talgebric vl -> Talgebric (List.map (instantiate_variant env) vl)
    | Trecord fl -> Trecord (List.map (instantiate_field env) fl)
    | Tabbrev ty -> Tabbrev (instantiate env ty)
    | Tlocal _ as x -> x

  and instantiate_variant env (id, ty_opt) =
    match ty_opt with
    | None -> id, None
    | Some ty -> id, Some (instantiate env ty)

  and instantiate_field env (id, ty) = id, instantiate env ty

  let instantiate ty = instantiate IMap.empty ty

  let rec type_expr env (p, ty) = p, type_expr_ env ty
  and type_expr_ env = function
    | Nast.Tunit -> Tunit
    | Nast.Tbool -> Tbool
    | Nast.Tint32 -> Tint32
    | Nast.Tfloat -> Tfloat
    | Nast.Tvar x -> Tvar x
    | Nast.Tid x -> Tid x
    | Nast.Tfun (ty1, ty2) -> 
	Tfun (type_expr env ty1, type_expr env ty2)
    | Nast.Tapply (ty, tyl) -> 
	Tast.Tapply (type_expr env ty, List.map (type_expr env) tyl)
    | Nast.Ttuple tyl -> Ttuple (List.map (type_expr env) tyl)
    | Nast.Tpath (id1, id2) -> Tpath (id1, id2) 
    | Nast.Talgebric vl -> Talgebric (List.map (variant env) vl)
    | Nast.Trecord fdl -> Trecord (List.map (field env) fdl)
    | Nast.Tabbrev ty -> Tabbrev (type_expr env ty)

  and variant env (id, ty_opt) = 
    match ty_opt with
    | None -> id, None
    | Some ty -> id, Some (type_expr env ty)

  and field env (id, ty) = id, type_expr env ty

  let rec make mdl = 
    List.fold_left module_ IMap.empty mdl

  and module_ env md =
    List.fold_left decl env md.Nast.md_decls
      
  and decl env = function
    | Nast.Dtype l -> List.fold_left type_def env l 
    | Nast.Dval ((p, id), ty) -> IMap.add id (type_expr env ty) env
	  
  and type_def env (((p, x), idl), ty) =
    match idl with
    | [] -> IMap.add x (type_expr env ty) env
    | l -> IMap.add x (p, Tast.Tabs (l, type_expr env ty)) env

  let find x env = IMap.find x env.types
  let add x ty env = { env with types = IMap.add x ty env.types }

end

let rec program mdl = 
  let types = Type.make mdl in
  let expanded_types = Expand.program types in
  if true then assert false ;
  ignore expanded_types ;
  List.map (module_ types) mdl

and module_ types md = 
  let env = { types = types ; defs = IMap.empty } in
  let decls = List.fold_left (decl env) [] md.md_decls in
  let defs = List.fold_left def_expr IMap.empty md.md_defs in
  let env = { types = types ; defs = defs } in
  let _, def_l = lfold def env md.md_defs in
  {
    Tast.md_id = md.md_id ;
    Tast.md_decls = decls ;
    Tast.md_defs = def_l ;
  }

and def_expr acc = function
  | Dmodule _ -> acc
  | Dlet (x, y, z) -> let_expr acc (x, y, z)
  | Dletrec l -> List.fold_left let_expr acc l
  | Dalias ((_, x1), (_, x2)) -> IMap.add x1 (IMap.find x2 acc) acc

and let_expr acc (x, idl, e) = 
  IMap.add (snd x) (idl, e) acc

and decl env acc = function
  | Dtype tdl -> List.fold_left (type_def env) acc tdl
  | Dval (x, ty) -> (x, Type.type_expr env ty) :: acc

and type_def env acc ((x, argl), ty) = 
  let ty = Type.type_expr env ty in
  match argl with
  | [] -> (x, ty) :: acc
  | l -> (x, (fst x, Tast.Tabs (l, ty))) :: acc

and def env = function
  | Dlet (f, pl, e) -> 
      let _, fun_ty = Type.find (snd f) env in
      begin match fun_ty with
      | Tast.Tfun (args_ty, ret_ty) -> 
	  let args = match pl with [x] -> x | l -> fst f, Ptuple l in
	  let env, (args_ty,_ as args) = pat env args_ty args in
	  let (ret_ty,_ as e) = expr env ret_ty e in
	  let env = Type.add (snd f) (fst f, (Tast.Tfun (args_ty, ret_ty))) env in
	  
	  env, Tast.Dlet (f, [args], e)
      | _ -> failwith "Expected a function"
      end
  | _ -> failwith "TODO def"
(*  | Dalias of id * id
  | Dmodule (id * id) *)
  
and pat_tuple env l1 l2 = 
  match l1, l2 with
  | [], [] -> env, []
  | [], _
  | _, [] -> failwith "wrong arity"
  | l1, (_, Ptuple l) :: rl -> pat_tuple env l1 (l @ rl)
  | (_, Tast.Ttuple l) :: rl, l2 -> pat_tuple env (l @ rl) l2
  | x1 :: rl1, x2 :: rl2 ->
      let env, x = pat env x1 x2 in
      let env, rl = pat_tuple env rl1 rl2 in
      env, x :: rl

and pat env ty (pos, x) = pat_ env ty pos x
and pat_ env ty pos x = 
  match x, ty with
  | Pany, _ -> env, (ty, Tast.Pany)
  | Punit, _ -> failwith "TODO pat unit"
  | Pid x, ty -> 
      Type.add (snd x) ty env, (ty, Tast.Pid x)
  | Ptuple pl, _ -> 
      let env, pl = pat_tuple env [ty] pl in
      let tyl = List.map fst pl in
      env, ((pos, Tast.Ttuple tyl), Tast.Ptuple pl)
  | _ -> failwith "TODO pat"

(*  | Pchar of string
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
 *)


(*and pat_field = Pos.t * pat_field_
and pat_field_ = 
  | PFany
  | PFid of id 
  | PField of id * pat *)


and expr env ty (p, e) = 
  let ty, e = expr_ env ty p e in
  (p, ty), e

and expr_ env ty p e = 
  match snd ty, e with
  | Tast.Tunit, Eunit -> Tast.Tunit, Tast.Eunit
  | Tast.Tbool, Ebool b -> Tast.Tbool, Tast.Ebool b
  | _, Eid x-> 
      let ty2 = Type.find (snd x) env in
      Type.unify env ty ty2, Tast.Eid x
  | Tast.Tint32, Eint s -> Tast.Tint32, Tast.Eint s
  | Tast.Tfloat, Efloat s -> Tast.Tfloat, Tast.Efloat s
  | Tast.Tbool, Eeq (e1, e2) -> comp env (fun x y -> Tast.Eeq (x,y)) e1 e2
  | Tast.Tbool, Elt (e1, e2) -> comp env (fun x y -> Tast.Elt (x,y)) e1 e2
  | Tast.Tbool, Elte (e1, e2) -> comp env (fun x y -> Tast.Elte (x,y)) e1 e2
  | Tast.Tbool, Egt (e1, e2) -> comp env (fun x y -> Tast.Egt (x,y)) e1 e2
  | Tast.Tbool, Egte (e1, e2) -> comp env (fun x y -> Tast.Egte (x,y)) e1 e2
  | _, (Eeq _ | Elt _ | Elte _ | Egt _ | Egte _) -> failwith "Bad type for comp"
  | _, Eplus (e1, e2) -> arith env ty (fun x y -> Tast.Eplus (x,y)) e1 e2
  | _, Eminus (e1, e2) -> arith env ty (fun x y -> Tast.Eminus (x,y)) e1 e2
  | _, Estar (e1, e2) -> arith env ty (fun x y -> Tast.Estar (x,y)) e1 e2

  | _, Eif (e1, e2, e3) -> 
      let e1 = expr env (fst e1, Tast.Tbool) e1 in
      let e2 = expr env ty e2 in
      let e3 = expr env ty e3 in
      snd ty, Tast.Eif (e1, e2, e3)

  | _, Eseq (e1, e2) -> 
      let e1 = expr env (fst e1, Tast.Tunit) e1 in
      let e2 = expr env ty e2 in
      snd ty, Tast.Eseq (e1, e2)

  | _, Euminus e -> snd ty, Tast.Euminus (expr env ty e)
  | Tast.Ttuple tyl, Etuple el -> snd ty, Tast.Etuple (expr_tuple env tyl el)

  | Tast.Tlocal _, Eapply (f, el) -> 
      Printf.printf "TODO properly Eapply typing.ml" ;
      raise Exit

  | _ -> failwith "TODO rest of expr"

and expr_tuple env tyl el = 
  match tyl, el with
  | [], [] -> []
  | [], _ | _, [] -> failwith "arity mismatch expr_tuple"
  | (_, Tast.Ttuple l) :: rl , el -> expr_tuple env (l @ rl) el
  | tyl, (_, Etuple l) :: rl -> expr_tuple env tyl (l @ rl)
  | x1 :: rl1, x2 :: rl2 -> expr env x1 x2 :: expr_tuple env rl1 rl2


(*      
  | Ecstr of id
  | Eecstr of id * id
  | Eefield of expr * id * id
  | Eextern of id * id
  | Echar of pstring
  | Estring of pstring
  | Erecord of (id * expr) list 
  | Ederef of expr * expr 
  | Efield of expr * id 
  | Ematch of expr * (pat * expr) list
  | Elet of pat * expr * expr
  | Eif of expr * expr * expr 
  | Efun of pat list * expr 
  | Eapply of expr * expr list

*)

and comp env f e1 e2 = 
  let (ty, _) as e1 = expr_type env e1 in
  let e2 = expr env ty e2 in
  Tast.Tbool, f e1 e2

and arith env rty f e1 e2 = 
  let e1 = expr env rty e1 in
  let e2 = expr env rty e2 in
  assert (snd rty = Tast.Tint32) ;
  snd rty, f e1 e2
 
and expr_type env (p, e) = 
  let ty, e = expr_type_ env p e in
  (p,ty), e

and expr_type_ env p e = 
  match e with
  | Eunit -> Tast.Tunit, Tast.Eunit
  | Ebool b -> Tast.Tbool, Tast.Ebool b
  | Eid x -> 
      let _, ty = Type.find (snd x) env in
      ty, Tast.Eid x
  | Eint s -> Tast.Tint32, Tast.Eint s
  | Efloat s -> Tast.Tfloat, Tast.Efloat s
  | Eeq (e1, e2) -> comp env (fun x y -> Tast.Eeq (x,y)) e1 e2
  | Elt (e1, e2) -> comp env (fun x y -> Tast.Elt (x,y)) e1 e2
  | Elte (e1, e2) -> comp env (fun x y -> Tast.Elte (x,y)) e1 e2
  | Egt (e1, e2) -> comp env (fun x y -> Tast.Egt (x,y)) e1 e2
  | Egte (e1, e2) -> comp env (fun x y -> Tast.Egte (x,y)) e1 e2
  | Eplus (e1, e2) -> arith_type env (fun x y -> Tast.Eplus (x,y)) e1 e2
  | Eminus (e1, e2) -> arith_type env (fun x y -> Tast.Eminus (x,y)) e1 e2
  | Estar (e1, e2) -> arith_type env (fun x y -> Tast.Estar (x,y)) e1 e2
  | Eif (e1, e2, e3) -> 
      let e1 = expr env (fst e1, Tast.Tbool) e1 in
      let (ty, _) as e2 = expr_type env e2 in
      let e3 = expr env ty e3 in
      snd ty, Tast.Eif (e1, e2, e3)
  | _ -> failwith "TODO rest of expr_type"

and arith_type env f e1 e2 = 
  let (ty, _) as e1 = expr_type env e1 in
  let e2 = expr env ty e2 in
  assert (snd ty = Tast.Tint32) ;
  snd ty, f e1 e2

