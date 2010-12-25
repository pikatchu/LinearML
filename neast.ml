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
  | Dabstract of id * id list
  | Dval of id * type_expr * pstring option

and tdef = {
    td_id: id ;
    td_args: id list ;
    td_map:  (id * type_expr_list) IMap.t
  }

and type_expr = Pos.t * type_expr_
and type_expr_ = 
  | Tany
  | Tprim of type_prim
  | Tvar of id 
  | Tid of id
  | Tapply of id * type_expr_list
  | Tfun of Ast.fun_kind * type_expr_list * type_expr_list

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
  | Pas of id * pat

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
  | Ewith of expr * (id * tuple) list 
  | Efield of expr * id 
  | Ematch of tuple * (pat * tuple) list
  | Elet of pat * tuple * tuple
  | Eif of expr * tuple * tuple
  | Eapply of id * tuple
  | Eseq of expr * tuple
  | Eobs of id
  | Efree of id

and tuple = Pos.t * expr list

and value = Nast.value


module FreeVars = struct

  let rec type_expr t (_, ty) = type_expr_ t ty

  and type_expr_ t = function
    | Tany
    | Tprim _ 
    | Tid _ -> t
    | Tvar (_, x) -> ISet.add x t
    | Tapply (_, (_, tyl)) -> 
	List.fold_left type_expr t tyl
    | Tfun (_, (_, tyl1), (_, tyl2)) -> 
	let t = List.fold_left type_expr t tyl1 in
	List.fold_left type_expr t tyl2

end
