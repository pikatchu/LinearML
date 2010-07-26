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
  | Dtype of (id * type_expr) list
  | Dval of id * type_expr list * type_expr list

and type_expr = Pos.t * type_expr_
and type_expr_ = 
  | Tany
  | Tundef
  | Tdef of ISet.t
  | Tprim of type_prim
  | Tvar of id 
  | Tid of id
  | Tapply of id * type_expr list
  | Tfun of type_expr list * type_expr list
  | Talgebric of (id * type_expr list) IMap.t
  | Trecord of (id * type_expr list) IMap.t
  | Tabs of id list * type_expr

and type_prim = Nast.type_prim =   
  | Tunit
  | Tbool
  | Tchar
  | Tint32
  | Tfloat

and def = id * pat * expr list

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
  | Evariant of id * expr list
  | Ebinop of Ast.bop * expr * expr
  | Euop of Ast.uop * expr
  | Erecord of (id * expr list) list 
  | Efield of expr * id 
  | Ematch of expr list * (pat * expr list) list
  | Elet of pat * expr list * expr list
  | Eif of expr * expr list * expr list
  | Eapply of id * expr list

and value = Nast.value

module CompareType = struct

  type t = id * type_expr list

  let (&&&) x1 x2 = 
    let c = x1 () in
    if c = 0
    then x2 ()
    else c

  let rec list cmp l1 l2 () = 
    match l1, l2 with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | x1 :: rl1, x2 :: rl2 -> 
	cmp x1 x2 &&& list cmp rl1 rl2

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

    | Talgebric vm1, Talgebric vm2 -> 
	let vl1 = list_of_imap vm1 in
	let vl2 = list_of_imap vm2 in
	list variant vl1 vl2 ()  
    | Talgebric _, _ -> -1
    | _, Talgebric _ -> 1

    | Trecord vm1, Trecord vm2 -> 
	let vl1 = list_of_imap vm1 in
	let vl2 = list_of_imap vm2 in
	list field vl1 vl2 ()
    | Trecord _, _ -> -1
    |  _, Trecord _ -> 1

    | Tabs (idl1, ty1), Tabs (idl2, ty2) -> 
	list id idl1 idl2 &&&
	ty ty1 ty2
    | Tabs _, _ -> -1
    | _, Tabs _ -> 1

    | Tdef s1, Tdef s2 -> ISet.compare s1 s2
    | Tdef _, _ -> -1
    | _, Tdef _ -> 1

    | Tundef, Tundef -> 0
    | Tundef _, _ -> -1
    | _, Tundef _ -> 1

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
