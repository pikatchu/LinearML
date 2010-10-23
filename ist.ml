open Utils

type id = Ident.t
type pstring = string

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

and type_expr =
  | Tany
  | Tprim of type_prim
  | Tvar of id 
  | Tid of id
  | Tapply of id * type_expr_list
  | Tfun of type_expr_list * type_expr_list

and type_expr_list = type_expr list

and type_prim = Nast.type_prim =
  | Tunit
  | Tbool
  | Tchar
  | Tint32
  | Tfloat
  | Tstring

and def = id * pat * tuple

and pat = pat_tuple list
and pat_tuple = pat_el list
and pat_el = type_expr * pat_
and pat_ = 
  | Pany 
  | Pid of id
  | Pvalue of value
  | Pvariant of id * pat
  | Precord of pat_field list
  | Pas of id * pat

and pat_field =
  | PFany
  | PFid of id 
  | PField of id * pat

and tuple = expr list
and expr = type_expr_list * expr_
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

and value =
  | Eunit
  | Ebool of bool
  | Eint of pstring
  | Efloat of pstring
  | Echar of pstring
  | Estring of pstring


