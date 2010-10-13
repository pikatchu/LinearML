open Utils
open Est

let n = ref 0
let space() = 
  let rec aux n = if n = 0 then () else (o " " ; aux (n-1)) in
  aux !n

let nl() = o "\n" ; space()

let push() = n := !n + 2 
let pop() = n := !n - 2
  
let id x = o (Ident.debug x)
let label x = o (Ident.debug x) 
let pstring x = o x

let rec program mdl = 
  List.iter module_ mdl

and module_ md = 
  o "module " ;
  id md.md_id ;
  o " = struct" ;
  push() ;
  nl() ;
  List.iter def md.md_defs ;
  pop() ;
  o "end" ;
  nl()

and def df = 
  id df.df_id ; 
  o " " ; 
  idl df.df_args ;
  o " returns " ; 
  idl df.df_return ;
  o " = " ;
  push() ;
  List.iter block df.df_body ;
  pop() ;
  nl() ; nl() ;
  
and pat pl = print_list o pat_el ", " pl
and pat_el _ p = pat_ (snd p)
and pat_ = function
  | Pany -> o "_"
  | Pid x -> id x 
  | Pvariant (x, p) -> id x ; o "(" ; pat p ; o ")"
  | Precord (ido, pfl) -> 
      o "{ " ; maybe id ido ; List.iter pfield pfl ; o " }"
  | Pas (x, p) -> o "(" ; id x ; o " as " ; pat_ (snd p) ; o ")"

and pfield (x, p) = 
  id x ; o " = " ; pat p ; o " ; "

and idl = List.iter (fun (_, x) -> id x ; o " ")

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
  | Lreturn l -> (o "lreturn " ; List.iter (fun (_, x) -> id x ; o " ") l)  ;
  | Return l -> (o "return " ; List.iter (fun (_, x) -> id x ; o " ") l)  ;
  | Jump x -> o "jump " ; id x
  | If (x, l1, l2) ->
      o "Iif " ; tid x ; o " then jump " ; label l1 ; 
      o " else jump " ; label l2 ;
  | Match (xl, al) -> 
      o "match " ; idl xl ; push() ; nl() ; List.iter maction al ; pop()

  ) ;
  pop() ;
  nl()

and phi (x, _, l) = 
  id x ; o " <- " ; 
  List.iter (fun (x, lbl) -> o "(" ; id x ; o ", " ; label lbl ; o ") ; ") l ;
  nl()

and equation (idl, e) = 
  List.iter (fun (_, x) -> id x) idl ; 
  o " = " ;
  expr e ;
  nl()

and expr = function
  | Eid x -> id x
  | Evalue v -> value v
  | Evariant (x, ty_idl) -> id x ; o "(" ; idl ty_idl ; o ")"
  | Ebinop (bop, id1, id2) -> binop bop ; o " " ; tid id1 ; o " " ; tid id2 
  | Euop (uop, x) -> unop uop ; o " " ; tid x
  | Erecord fdl -> o "{" ; List.iter field fdl ; o "}"
  | Ewith (x, fdl) -> o "{" ; tid x ; List.iter field fdl ; o "}" 
  | Efield (x, y) -> tid x ; o "." ; id y
  | Ematch (xl, al) -> 
      o "match " ; idl xl ; push() ; nl() ;List.iter action al ; pop()
  | Eapply (x, l) -> o "call " ; id x ; o " " ; idl l
  | Eseq _ -> failwith "TODO seq"
  | Ecall x -> o "lcall " ; o (Ident.debug x)
  | Eif (x, l1, l2) -> 
      o "if " ; tid x ; o " then lcall " ; label l1 ; 
      o " else lcall " ; label l2 

and field (x, l) = id x ; o " = " ; idl l
and action (p, e) = 
  pat p ; o " -> " ; expr e ; nl()

and maction (p, lbl) = 
  pat p ; o " -> jump " ; id lbl ; nl()

and tid (_, x) = id x

and value = function
  | Ist.Eunit -> o "unit"
  | Ist.Ebool b -> o (string_of_bool b) 
  | Ist.Eint x -> o x
  | Ist.Efloat x -> o x
  | Ist.Echar x -> o x
  | Ist.Estring x -> o x

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
