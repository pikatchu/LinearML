let rec program mdl = 
  let mdl = ExpandAbbrevs.program mdl in
  let types = Types.make mdl in
  List.map (module_ types) mdl

and module_ types md = 
  let defs, lcl_types = Defs.module_ types md in
  let defs, decls = lfold (decl types lcl_types defs) TMap.empty md.md_decls in
  let defs = TMap.fold (fun _ def acc -> def :: acc) defs [] in
  { Tast.md_id = md.md_id ;
    Tast.md_decls = decls ;
    Tast.md_defs = defs }

and decl types lcl_types defs acc = function
  | Dtype tdl -> 
      acc, Tast.Dtype (List.map (tdef types) tdl)
  | Dval (x, _) -> 
      let ty = IMap.find (snd x) types in
      let acc = def lcl_types defs acc x ty in
      acc, Tast.Dval (x, ty)

and tdef types (x, _) = x, IMap.find (snd x) types

and def types defs acc (_, x) fty =
  let id, pl, e = IMap.find x defs in
  Debug.type_expr fty ;
  let tyl, rty = Types.fun_ fty in
  let pl = TupleExpand.pat_list pl in
  let types, pl = simpl_pat_l types tyl pl in
  let acc, e = expr types acc e in
  ignore (acc, e) ;
  (* TODO fix the empty list *)
  raise Exit (*TMap.add (id, tyl) (id, pl, e) acc*)

and simpl_pat_l env tyl1 pl2 = 
  match tyl1, pl2 with
  | [], [] -> env, []
  | [], _ | _, [] -> failwith "TODO simpl_pat_l wrong arity"
  | x1 :: rl1, x2 :: rl2 -> 
      let env, p = simpl_pat env x1 x2 in
      let env, pl = simpl_pat_l env rl1 rl2 in
      env, p :: pl

and simpl_pat types (p1, ty) (p2, pat) = 
  let ty, pat = match ty, pat with
  | Tast.Tunit, Punit -> types, Tast.Punit
  | _, Pany -> types, Tast.Pany
  | _, Pid (p, x) -> IMap.add x (p, ty) types, Tast.Pid (p, x)
  | _, x -> 
      NDebug.pat x ;
      Debug.type_expr (p1, ty) ;
      failwith "either simpl_pat badly typed or assert false ;-)" in
  ty, (p2, pat)

and unify ty1 ty2 = snd (Unify.type_expr ty1 ty2)

and expr env acc (pos, e) = 
  match e with
  | Elet (p, e1, e2) -> 
(*      let acc, ((_, ty1, _) as e1) = expr env acc e1 in

      let pl = TupleExpand.pat p in 
      let env, pl = simpl_pat_l env [ty1] pl in
      let acc, ((_, ty2, _) as e2) = expr env acc e2 in
      acc, (pos, ty2, Tast.Elet (pl, e1, e2)) *)
      raise Exit

  | _ ->
      let acc, (ty, e) = expr_ env acc e in
      acc, (pos, ty, e)

and expr_ env acc = function
  | Eunit -> acc, (Tast.Tunit, Tast.Eunit)
  | Ebool b -> acc, (Tast.Tbool, Tast.Ebool b)
  | Eid x -> acc, (Env.get_type env x, Tast.Eid x)
  | Eint n -> acc, (Tast.Tint32, Tast.Eint n)
  | Efloat f -> acc, (Tast.Tfloat, Tast.Efloat f)
  | Eeq (e1, e2) -> 
      let acc, ((_, ty1, _) as e1) = expr env acc e1 in
      let acc, ((_, ty2, _) as e2) = expr env acc e2 in
      ignore (unify ty1 ty2) ;
      acc, (Tast.Tbool, Tast.Eeq (e1, e2))

  | Elt (e1, e2) ->
      let acc, ((_, ty1, _) as e1) = expr env acc e1 in
      let acc, ((_, ty2, _) as e2) = expr env acc e2 in
      ignore (unify ty1 ty2) ;
      acc, (Tast.Tbool, Tast.Elt (e1, e2))

  | Elte (e1, e2) ->
      let acc, ((_, ty1, _) as e1) = expr env acc e1 in
      let acc, ((_, ty2, _) as e2) = expr env acc e2 in
      ignore (unify ty1 ty2) ;
      acc, (Tast.Tbool, Tast.Elte (e1, e2))

  | Egt (e1, e2) ->
      let acc, ((_, ty1, _) as e1) = expr env acc e1 in
      let acc, ((_, ty2, _) as e2) = expr env acc e2 in
      ignore (unify ty1 ty2) ;
      acc, (Tast.Tbool, Tast.Egt (e1, e2))

  | Egte (e1, e2) ->
      let acc, ((_, ty1, _) as e1) = expr env acc e1 in
      let acc, ((_, ty2, _) as e2) = expr env acc e2 in
      ignore (unify ty1 ty2) ;
      acc, (Tast.Tbool, Tast.Egte (e1, e2))

  | Eplus (e1, e2) -> 
      let acc, ((_, ty1, _) as e1) = expr env acc e1 in
      let acc, ((_, ty2, _) as e2) = expr env acc e2 in
      (* TODO Check numerical ?? *)
      acc, (unify ty1 ty2, Tast.Eplus (e1, e2))

  | Eminus (e1, e2) -> 
      let acc, ((_, ty1, _) as e1) = expr env acc e1 in
      let acc, ((_, ty2, _) as e2) = expr env acc e2 in
      (* TODO Check numerical ?? *)
      acc, (unify ty1 ty2, Tast.Eminus (e1, e2))
      
  | Estar (e1, e2) -> 
      let acc, ((_, ty1, _) as e1) = expr env acc e1 in
      let acc, ((_, ty2, _) as e2) = expr env acc e2 in
      (* TODO Check numerical ?? *)
      acc, (unify ty1 ty2, Tast.Estar (e1, e2))

  | Eseq (e1, e2) -> 
      let acc, ((_, ty1, _) as e1) = expr env acc e1 in
      let acc, ((_, ty2, _) as e2) = expr env acc e2 in
      ignore (unify ty1 (fst e1, Tast.Tunit)) ;
      acc, (snd ty2, Tast.Eseq (e1, e2))

  | Ecstr x -> 
      let vm = IMap.add (snd x) (x, []) IMap.empty in
      let ty = Tast.Talgebric vm in
      acc, (ty, Tast.Ecstr x)

  | Eecstr (md_id, x) -> 
      let vm = IMap.add (snd x) (x, []) IMap.empty in
      let ty = Tast.Talgebric vm in
      acc, (ty, Tast.Eecstr (md_id, x))

  | Eif (e1, e2, e3) -> 
      let acc, ((_, ty1, _) as e1) = expr env acc e1 in
      let acc, ((_, ty2, _) as e2) = expr env acc e2 in
      let acc, ((_, ty3, _) as e3) = expr env acc e3 in
      ignore (Unify.type_expr ty1 (fst e1, Tast.Tbool)) ;
      let ty = unify ty2 ty3 in
      acc, (ty, Tast.Eif (e1, e2, e3))

(*  | Eapply (e, el) -> 
      let acc, (fty, f) = expr env acc e in
      let acc, (tyl, el) = expr_list env acc el in
      match snd fty with
      | Tast.Tdecl _ -> assert false
      | Tast.Tfun (targl, rty) -> 
	  ignore (Unify.type_expr_list tyl targl) ;
	  acc, (rty, Tast.Eapply (f, el))
      | _ -> failwith "TODO expected function 2" *)



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
