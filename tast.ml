open Utils

type id = Neast.id
type pstring = Neast.pstring

type program = module_ list

and module_ = {
    md_id: id ;
    md_decls: Neast.decl list ;
    md_defs: def list ;
  }

and type_expr = Neast.type_expr

and def = id * pat * expr list

and pat = Pos.t * pat_tuple list
and pat_tuple = Pos.t * pat_el list
and pat_el = type_expr * (Pos.t * pat_)
and pat_ = 
  | Pany 
  | Pid of id
  | Pvalue of Neast.value
  | Pvariant of id * pat
  | Precord of pat_field list

and pat_field = Pos.t * pat_field_
and pat_field_ = 
  | PFany
  | PFid of id 
  | PField of id * pat

and expr = type_expr list * (Pos.t * expr_)
and expr_ = 
  | Eid of id
  | Evalue of Neast.value
  | Evariant of id * expr list
  | Ebinop of Ast.bop * expr * expr
  | Euop of Ast.uop * expr
  | Erecord of (id * expr list) list 
  | Efield of expr * id 
  | Ematch of expr list * (pat * expr list) list
  | Elet of pat * expr list * expr list
  | Eif of expr * expr list * expr list
  | Eapply of expr * expr list
