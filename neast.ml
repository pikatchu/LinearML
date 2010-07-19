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
  | Dval of id * type_expr

and type_expr = Pos.t * type_expr_
and type_expr_ = 
  | Tunit
  | Tbool
  | Tint32
  | Tfloat
  | Tvar of id 
  | Tid of id
  | Tapply of type_expr * type_expr list
  | Tpath of id * id
  | Tfun of type_expr list * type_expr list
  | Talgebric of (id * type_expr list) IMap.t
  | Trecord of (id * type_expr list) IMap.t
  | Tabs of id list * type_expr

and def = id * pat * expr list

and pat = Pos.t * pat_tuple list
and pat_tuple = Pos.t * pat_el list
and pat_el = Pos.t * pat_
and pat_ = 
  | Punit
  | Pany 
  | Pid of id
  | Pchar of string
  | Pint of string
  | Pbool of bool
  | Pfloat of string
  | Pstring of string
  | Pvariant of id * pat
  | Precord of pat_field list

and pat_field = Pos.t * pat_field_
and pat_field_ = 
  | PFany
  | PFid of id 
  | PField of id * pat

and expr = Pos.t * expr_
and expr_ = 
  | Eunit
  | Ebool of bool
  | Eid of id
  | Erid of int * id
  | Eint of string
  | Efloat of string
  | Echar of pstring
  | Estring of pstring
  | Ebinop of Ast.bop * expr * expr
  | Euop of Ast.uop * expr
  | Erecord of (id * expr) list 
  | Efield of expr * id 
  | Ematch of expr * (pat * expr list) list
  | Elet of pat * expr list * expr list
  | Eif of expr * expr list * expr list
  | Efun of pat list * expr list
  | Eapply of expr * expr list

