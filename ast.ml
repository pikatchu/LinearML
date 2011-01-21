open Utils

type id = Pos.t * string
type pstring = Pos.t * string

type fun_kind = Cfun | Lfun

type program = module_ list

and module_ = {
    md_id: id ;
    md_defs: def list ;
  }

and type_def = (id * id list) * type_expr

and type_expr = Pos.t * type_expr_
and type_expr_ = 
  | Tany
  | Tvar of id 
  | Tid of id
  | Tapply of type_expr * type_expr list
  | Ttuple of type_expr list
  | Tpath of id * id
  | Tfun of fun_kind * type_expr * type_expr
  | Talgebric of (id * type_expr option) list
  | Trecord of (id * type_expr) list
  | Tabbrev of type_expr
  | Tabs of id list * type_expr
  | Tabstract

and def = 
  | Dmodule of id * id
  | Dlet of id * pat list * expr
  | Dtype of (id * type_expr) list
  | Dval of id * type_expr * pstring option

and pat = Pos.t * pat_
and pat_ = 
  | Punit
  | Pany 
  | Pid of id
  | Pchar of pstring
  | Pint of pstring
  | Pbool of bool
  | Pfloat of pstring
  | Pstring of pstring
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
  | Eunit
  | Ebool of bool
  | Eid of id
  | Eint of pstring
  | Efloat of pstring
  | Echar of pstring
  | Estring of pstring
  | Ebinop of bop * expr * expr
  | Euop of uop * expr
  | Etuple of expr list
  | Ecstr of id
  | Eecstr of id * id
  | Eefield of expr * id * id
  | Eextern of id * id
  | Erecord of field list 
  | Efield of expr * id 
  | Ematch of expr * (pat * expr) list
  | Elet of pat * expr * expr
  | Eif of expr * expr * expr 
  | Efun of pat list * expr 
  | Eapply of expr * expr list
  | Ewith of expr * field list
  | Eseq of expr * expr

and field = 
  | Eflocl of id * expr 
  | Efextr of id * id * expr 

and bop = 
  | Eeq
  | Elt
  | Elte
  | Egt
  | Egte
  | Eplus
  | Eminus
  | Estar

and uop =
  | Euminus
