
let id x = x

let rec program mdl = 
  NastCheck.ModuleTypes.check mdl ;
  let mdl = ExpandAbbrevs.program mdl in
  List.map (module_ IMap.empty) mdl 

and module_ env md = 
  {
    Tast.md_id = md.md_id ;
    Tast.md_decls = List.map (decl env) md.md_decls ;
    Tast.md_defs = List.map (def env) md.md_defs ;
  }

and decl env = function
  | Dtype tdl -> Tast.Dtype (List.map (tdef env) tdl)
  | Dval (id, ty) -> Tast.Dval (id, type_expr env ty)

and tdef env (x, ty) = id x, type_expr env ty


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
