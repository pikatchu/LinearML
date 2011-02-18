open Utils

type id = Pos.t * Ident.t
type pstring = Pos.t * string

type program = module_ list

and module_ = {
    md_id: id ;
    md_decls: decl list ;
    md_defs: def list ;
  }

and decl = 
  | Dtype of (id * type_expr) list
  | Dval of Ast.link * id * type_expr * Ast.extern_def

and type_expr = Pos.t * type_expr_
and type_expr_ = 
  | Tany
  | Tprim of type_prim
  | Tvar of id 
  | Tid of id
  | Tapply of type_expr * type_expr list
  | Ttuple of type_expr list
  | Tpath of id * id
  | Tfun of Ast.fun_kind * type_expr * type_expr
  | Talgebric of (id * type_expr option) IMap.t
  | Trecord of (id * type_expr) IMap.t
  | Tabbrev of type_expr
  | Tabs of id list * type_expr
  | Tabstract

and type_prim = 
  | Tunit
  | Tbool
  | Tchar
  | Tint
  | Tfloat
  | Tstring

and def = id * pat list * expr

and pat = Pos.t * pat_
and pat_ = 
  | Pany 
  | Pid of id
  | Pvalue of value
  | Pcstr of id 
  | Pvariant of id * pat
  | Pecstr of id * id
  | Pevariant of id * id * pat
  | Precord of pat_field list
  | Pbar of pat * pat
  | Ptuple of pat list
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
  | Ebinop of Ast.bop * expr * expr
  | Euop of Ast.uop * expr
  | Etuple of expr list
  | Ecstr of id
  | Erecord of (id * expr) list 
  | Efield of expr * id 
  | Ematch of expr * (pat * expr) list
  | Elet of pat * expr * expr
  | Eif of expr * expr * expr 
  | Eapply of expr * expr list
  | Ewith of expr * (id * expr) list
  | Eseq of expr * expr
  | Eobs of id
  | Efree of id
  | Epartial of expr list
  | Efun of Ast.fun_kind * (pat * type_expr) list * expr 

and value = 
  | Eunit
  | Ebool of bool
  | Eint of pstring
  | Efloat of pstring
  | Echar of pstring
  | Estring of pstring
    
