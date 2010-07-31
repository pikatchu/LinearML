open Utils

type id = Nast.id
type pstring = Nast.pstring

type program = module_ list

and module_ = {
    md_id: id ;
    md_decls: decl list ;
    md_defs: def list ;
  }

and decl = 
  | Dalgebric of tdef
  | Drecord of tdef
  | Dval of id * type_expr

and tdef = {
    td_id: id ;
    td_args: id list ;
    td_map:  (id * type_expr_list) IMap.t
  }

and type_expr = Pos.t * type_expr_
and type_expr_ = 
  | Tany
  | Tundef
  | Tdef of Pos.t IMap.t
  | Tprim of type_prim
  | Tvar of id 
  | Tid of id
  | Tapply of id * type_expr_list
  | Tfun of type_expr_list * type_expr_list

and type_expr_list = Pos.t * type_expr list

and type_prim = Nast.type_prim =   
  | Tunit
  | Tbool
  | Tchar
  | Tint32
  | Tfloat

and def = id * pat * tuple

and pat = Pos.t * pat_tuple list
and pat_tuple = Pos.t * pat_el list
and pat_el = Pos.t * pat_
and pat_ = 
  | Pany 
  | Pid of id
  | Pvalue of value
  | Pvariant of id * pat
  | Precord of pat_field list

and pat_field = Pos.t * pat_field_
and pat_field_ = 
  | PFany
  | PFid of id 
  | PField of id * pat

and expr = Pos.t * expr_
and expr_ = 
  | Eid of id
  | Evalue of value
  | Evariant of id * tuple
  | Ebinop of Ast.bop * expr * expr
  | Euop of Ast.uop * expr
  | Erecord of (id * tuple) list 
  | Efield of expr * id 
  | Ematch of tuple * (pat * tuple) list
  | Elet of pat * tuple * tuple
  | Eif of expr * tuple * tuple
  | Eapply of id * tuple

and tuple = Pos.t * expr list

and value = Nast.value

module CompareType = struct

  type t = id * type_expr_list

  let (&&&) x1 x2 = 
    let c = x1 () in
    if c = 0
    then x2 ()
    else c

  let rec list cmp (_, l1) (_, l2) () = list_ cmp l1 l2 ()

  and list_ cmp l1 l2 () = 
    match l1, l2 with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | x1 :: rl1, x2 :: rl2 -> 
	cmp x1 x2 &&& list_ cmp rl1 rl2

  let rec compare (id1, ty1) (id2, ty2) = 
    id id1 id2 &&& 
    list ty ty1 ty2

  and id (_, x1) (_, x2) () = 
    Ident.compare x1 x2

  and ty (_, ty1) (_, ty2) () = 
    match ty1, ty2 with
    | Tany, Tany -> 0
    | Tany, _ -> -1
    | _, Tany -> 1

    | Tprim ty1, Tprim ty2 -> prim ty1 ty2
    | Tprim _, _ -> -1
    | _, Tprim _ -> 1

    | Tid x1, Tid x2 -> id x1 x2 ()
    | Tid _, _ -> -1
    | _, Tid _-> 1

    | Tvar x1, Tvar x2 -> id x1 x2 ()
    | Tvar _, _ -> -1
    | _, Tvar _ -> 1

    | Tapply (ty1, tyl1), Tapply (ty2, tyl2) -> 
	id ty1 ty2 &&&
	list ty tyl1 tyl2	  
    | Tapply _, _ -> -1
    |  _, Tapply _ -> 1

    | Tfun (ty1, ty2), Tfun (ty3, ty4) ->
	list ty ty1 ty3 &&&
	list ty ty2 ty4	  
    | Tfun _, _ -> -1
    | _, Tfun _ -> 1

    | Tdef s1, Tdef s2 -> 
	let add x _ acc = ISet.add x acc in
	let set1 = IMap.fold add s1 ISet.empty in
	let set2 = IMap.fold add s2 ISet.empty in
	ISet.compare set1 set2
    | Tdef _, _ -> -1
    | _, Tdef _ -> 1

    | Tundef, Tundef -> 0

  and prim ty1 ty2 = 
    match ty1, ty2 with
    | Tunit, Tunit -> 0
    | Tbool, Tbool -> 0
    | Tint32, Tint32 -> 0
    | Tfloat, Tfloat -> 0
    | _ -> Pervasives.compare ty1 ty2

  and variant (id1, ty1) (id2, ty2) () =
    id id1 id2 &&&
    list ty ty1 ty2

  and field (id1, ty1) (id2, ty2) () = 
    id id1 id2 &&&
    list ty ty1 ty2
    
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
