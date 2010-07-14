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
  | Ttuple of type_expr list
  | Tpath of id * id
  | Tfun of type_expr * type_expr
  | Talgebric of (id * type_expr option) list
  | Trecord of (id * type_expr) list
  | Tabbrev of type_expr
  | Tabs of id list * type_expr

and def = 
  | Dmodule of id * id
  | Dlet of id * pat list * expr
  | Dletrec of (id * pat list * expr) list
  | Dalias of id * id

and pat = Pos.t * pat_
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
  | PField of id * pat

and expr = Pos.t * expr_
and expr_ = 
  | Eunit
  | Ebool of bool
  | Eid of id
  | Eint of string
  | Efloat of string
  | Eeq of expr * expr
  | Elt of expr * expr
  | Elte of expr * expr
  | Egt of expr * expr
  | Egte of expr * expr
  | Eplus of expr * expr
  | Eminus of expr * expr
  | Estar of expr * expr
  | Eseq of expr * expr
  | Euminus of expr
  | Etuple of expr list
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
