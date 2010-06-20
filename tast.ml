open Utils

type id = string
type pstring = string

type program = module_ list

and module_ = {
    md_name: id ;
    md_tenv: type_expr SMap.t ;
    md_decls: type_expr SMap.t ;
    md_defs: def SMap.t ;
  }

and type_expr = 
  | Tvar of id
  | Tid of id
  | Tapply of type_expr * type_expr list
  | Ttuple of type_expr list
  | Tpath of id * id
  | Tfun of type_expr * type_expr
  | Talgebric of id list * (id * type_expr option) list
  | Trecord of id list * (id * type_expr) list
  | Talias of id list * type_expr

and def = 
  | Dmodule of id * id
  | Dlet of id * pat list * expr
  | Dletrec of id * pat list * expr
  | Dalias of id * id

and pat = type_expr * pat_
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
  | Pprod of pat * pat
  | Pstruct of pat_field list
  | Pbar of pat * pat
  | Ptuple of pat list
  | Pderef of id * pat

and pat_field = 
  | PFany
  | PFid of id 
  | PField of id * pat

and expr = type_expr * expr_
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
  | Echar of pstring
  | Estring of pstring
  | Estruct of (id * expr) list 
  | Eblock of expr list
  | Etyped of expr * type_expr
  | Ederef of expr * expr 
  | Epath of expr * id 
  | Ematch of expr * (pat * expr) list
  | Elet of pat * expr * expr
  | Eletrec of pat * expr * expr
  | Eif of expr * expr * expr 
  | Efun of pat list * expr 
  | Eapply of expr * expr list
