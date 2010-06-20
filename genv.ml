
type t = {
    globals: Ident.t SMap.t ;
    types: Ident.t SMap.t ;
    cstrs: Ident.t SMap.t ;
  }

let add_id t (pos, s) = SMap.add s (pos, Ident.fresh()) t
let global_id t x = { t with globals = add_id t.globals x }
let type_id t x = { t with types = add_id t.types x }
let cstr_id t x = { t with cstrs = add_id t.cstrs x }
let module_id t x = { t with modules = add_id t.modules x }

let rec program p = 
  let t = module_id t p 
  List.fold_left module_ empty p

and module_ t md = List.fold_left def 
  {
    md_name: id ;
    md_defs: def list ;
  }

and def = 
  | Dmodule of id * id
  | Dval of id * pat list * expr
  | Dtype of id list * id * type_expr

and type_expr = 
  | Tid of id 
  | Tvar of id 
  | Tcstr of id * type_expr option
  | Tpath of id * id 
  | Tapp of type_expr list * type_expr
  | Tstruct of field_type list
  | Tprod of type_expr * type_expr 
  | Tfun of type_expr * type_expr 
  | Tbar of type_expr * type_expr 

and field_type = id * type_expr

and pat = 
  | Punit
  | Pany 
  | Pid of id
  | Pint of id 
  | Pcstr of id * pat option
  | Pprod of pat * pat
  | Pstruct of pat_field list
  | Pcons of pat * pat
  | Plist of pat list

and pat_field = 
  | PFany
  | PFid of id 
  | PField of id * pat

and action = 
  | Anone
  | Awhen of expr * expr
  | Aexpr of expr

and field = 
  | Frow of id
  | Ffield of id * expr

and expr = 
 | Eunit
 | Eid of id
 | Eint of id 
 | Ecstr of id * expr option
 | Estring of id
 | Elist of expr list 
 | Estruct of field list 
 | Etyped of expr * type_expr
 | Edot_string of expr * expr 
 | Edot_array of expr * expr 
 | Epath of expr * id 
 | Ematch of expr * (pat * action) list
 | Elet of pat list * expr * expr 
 | Eif of expr * expr * expr 
 | Efun of pat list * expr 
 | Ebinop of binary_op * expr * expr 
 | Eunop of unary_op * expr 
 | Eapply of expr * expr

and binary_op = 
 | Eq
 | Lt
 | Lte
 | Gt
 | Gte
 | Plus
 | Minus
 | Star
 | Comma
 | Cons
 | Seq

and unary_op = 
 | Uminus
