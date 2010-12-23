open Utils
open Llst

let n = ref 0
let space() = 
  let rec aux n = if n = 0 then () else (o " " ; aux (n-1)) in
  aux !n

let nl() = o "\n" ; space()

let push() = n := !n + 2 
let pop() = n := !n - 2
  
let id x = o (Ident.debug x)
let ty_id (p, x) = o (Ident.debug x)
let label x = o (Ident.debug x) 
let pstring x = o x

let rec program mdl = 
  List.iter module_ mdl

and module_ md = 
  o "module " ;
  id md.md_id ;
  o ":" ;
  push() ;
  nl() ;
  nl() ;
  List.iter decl md.md_decls ;
  pop() ;
  nl() ;
  o "end" ;
  o " = struct" ;
  push() ;
  nl() ;
  List.iter def md.md_defs ;
  pop() ;
  nl() ;
  o "end" ;
  nl()

and decl = function
  | Dtype (x, ty) -> 
      o "type " ; id x ; o " = " ; type_expr ty ;
      nl () ;
  | Dval (x, ty, v) -> 
      o "val " ; id x ; o ": " ; type_expr ty ;
      (match v with 
      | None -> ()
      | Some x -> o " = " ; o x) ;
      nl () ;

and type_expr = function
  | Tany -> o "void*"
  | Tprim tp -> type_prim tp
  | Tid x -> id x 
  | Tptr x -> type_expr x ; o "*"
  | Tfun (tyl1, tyl2) -> 
      o "(" ;
      type_expr_list tyl1 ;
      o " -> " ;
      type_expr_list tyl2 ;
      o ")"
  | Tstruct tyl -> 
      o "{ " ; print_list o (fun _ x -> type_expr x) ", " tyl ; o " }"

and type_expr_list l = 
  print_list o (fun _ x -> type_expr x) ", " l

and type_prim = function
  | Tunit -> o "unit"
  | Tbool -> o "bool"
  | Tchar -> o "char"
  | Tint32 -> o "int32"
  | Tfloat -> o "float"

and def df = 
  id df.df_id ; 
  o " " ; 
  List.iter (fun (ty, x) -> o "(" ; id x ; o ": " ; type_expr ty ; o ") ") df.df_args ;
  o ": " ; type_expr_list df.df_ret ;
  o " = " ;
  push() ;
  List.iter block df.df_body ;
  pop() ;
  nl() ; nl() ;
  
and idl l = o "(" ; print_list o (fun _ (_, x) -> id x) ", " l ; o ")"

and block bl = 
  nl() ;
  id bl.bl_id ;
  o ":" ;
  nl() ;
  push() ; 
  nl() ;
  if bl.bl_phi <> [] then (o "phi: " ; nl() ; List.iter phi bl.bl_phi ; nl()) ;
  List.iter equation bl.bl_eqs ;
  (match bl.bl_ret with
  | Return (tail, l) -> 
      (o "return[" ; 
       o (if tail then "true] " else "false] ") ;
       List.iter (fun (_, x) -> id x ; o " ") l)  ;
  | Jump x -> o "jump " ; id x
  | If (x, l1, l2) ->
      o "Iif " ; tid x ; o " then jump " ; label l1 ; 
      o " else jump " ; label l2 ;
  | Switch (x, al, default) -> 
      o "switch " ; ty_id x ; push() ; nl() ; List.iter maction al ; pop() ;
      o "default: " ; id default ;
  ) ;
  pop() ;
  nl()

and phi (x, ty, l) = 
  id x ; o ":" ; type_expr ty ; o " <- " ; 
  List.iter (fun (x, lbl) -> o "(" ; id x ; o ", " ; label lbl ; o ") ; ") l ;
  nl()

and equation (idl, e) = 
  print_list o (fun _ (ty, x) -> type_expr ty ; o " " ; id x) ", " idl ; 
  o " = " ;
  expr e ;
  nl()

and expr = function
  | Enull -> o "null"
  | Eis_null x -> o "null? " ; ty_id x
  | Eid x -> ty_id x
  | Evalue v -> value v
  | Ebinop (bop, id1, id2) -> binop bop ; o " " ; tid id1 ; o " " ; tid id2 
  | Euop (uop, x) -> unop uop ; o " " ; tid x
  | Etuple (x, l) -> o "{ " ; maybe ty_id x ; o " | " ; 
      print_list o (fun _ (n, x) -> o "[" ; o (soi n) ; o "]=" ; tid x) ", " l ; o " }"
  | Efield (x, y) -> tid x ; o "." ; o (soi y)
  | Eapply (b, x, l) -> if b then o "tail " else () ; o "call " ; id x ; o " " ; idl l
  | Egettag x -> o "gettag " ; tid x
  | Egetargs x -> o "getargs " ; tid x
  | Eproj (x, n) -> tid x ; o "[" ; o (soi n) ; o "]"
  | Eptr_of_int x -> o "(pointer) " ; id x
  | Eint_of_ptr x -> o "(int) " ; id x
  | Efree x -> o "free " ; id (snd x)

and field (x, l) = o (soi x) ; o " = " ; idl l
and action (x, e) = 
  ty_id x ; o " -> " ; expr e ; nl()

and maction (x, lbl) = 
  value x ; o " -> jump " ; id lbl ; nl()

and tid (_, x) = id x

and value = function
  | Eunit -> o "unit"
  | Ebool b -> o (string_of_bool b) 
  | Eint x -> o x
  | Efloat x -> o x
  | Echar x -> o x
  | Estring x -> o x
  | Eiint x -> o (soi x)

and binop = function 
  | Ast.Eeq -> o "eq"
  | Ast.Elt -> o "lt"
  | Ast.Elte -> o "lte"
  | Ast.Egt -> o "gt"
  | Ast.Egte -> o "gte"
  | Ast.Eplus -> o "plus"
  | Ast.Eminus -> o "minus"
  | Ast.Estar -> o "star"

and unop = function
  | Ast.Euminus -> o "uminus"
