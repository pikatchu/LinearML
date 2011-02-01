open Utils

type type_error = 
  | Unify of unify_error
  | Fun_call of Pos.t

and unify_error = {
    pos1: Pos.t ;
    pos2: Pos.t ;
    print1: ((string -> unit) -> unit) ;
    print2: ((string -> unit) -> unit) ;
  }

exception Type of type_error list

let oerr = output_string stderr
let err x = oerr x ; oerr "\n"
let pos x = err (Pos.string x)

let lexing_error lb = 
  err (Pos.string (Pos.make lb)) ;
  err "Error: Lexing error\n" ;
  exit 1

let syntax_error lb = 
  err (Pos.string (Pos.make lb)) ;
  err "Error: Syntax error\n" ;
  exit 2

let multiple_module_def pos1 pos2 = 
  pos pos1 ;
  err "Error: module has multiple definitions" ;
  err "Was previously defined here:" ;
  pos pos2 ;
  exit 3

let unbound_name p id = 
  pos p ;
  err ("Error: Unbound name "^id) ;
  exit 4

let multiple_def p id = 
  pos p ;
  err ("Error: "^id^" is defined multiple times") ;
  exit 5

let type_arity_mismatch p1 p2 (_, id) n1 n2 = 
  pos p1 ;
  err ("Error: trying to apply "^ string_of_int n2^
       " arguments to "^ id) ;
  pos p2 ;
  err (id^" was declared with "^string_of_int n1^
       " arguments") ;
  exit 6

let bad_type_app p = 
  pos p ;
  err ("Error: this type doesn't expect arguments");
  exit 7

let value_function p = 
  pos p ;
  err ("Every value must be a function") ;
  exit 8

let undefined_sig p v = 
  pos p ;
  err ("Value "^v^" has no definition") ;
  exit 9

let cycle kind p id rl = 
  let id = Ident.to_string id in
  pos p ;
  err ("The "^kind^" "^id^" is cyclic\n") ;
  err ("Through this path:") ;
  List.iter (fun (p, _) -> pos p) rl ;
  exit 10

let cycle kind pl =
  match pl with
  | [] -> assert false
  | (p, id) :: rl -> cycle kind p id rl

let type_expects_arguments (p, x) n pdef = 
  let x = Ident.to_string x in
  let n = string_of_int n in
  pos p ;
  err ("The type "^x^" expects "^n^" arguments") ;
  if pdef <> Pos.none
  then begin
  err ("Its definition is given here: ") ;
  pos pdef
  end ;
  exit 2

let not_expecting_arguments px x pdef = 
  let x = Ident.to_string x in
  pos px ;
  err ("The type "^x^" doesn't expect any arguments") ;
  if pdef <> Pos.none
  then begin
    err ("Its definition is given here") ;
    pos pdef ;
  end ;
  exit 2

let no_argument p = 
  pos p ;
  err "No argument expected" ;
  exit 2

let type_arity px x size1 size2 pdef = 
  let x = Ident.to_string x in
  let size1 = string_of_int size1 in
  let size2 = string_of_int size2 in
  pos px ;
  err ("The type "^x^" expects "^size2^" arguments not "^size1) ;
  if pdef <> Pos.none
  then begin
    err ("Its definition is given here") ;
    pos pdef ;
  end ;
  exit 2


let pbar_arity p1 n1 p2 n2 =
  let n1 = string_of_int n1 in
  let n2 = string_of_int n2 in
  pos p1 ;
  err ("This pattern matches a tuple of "^n1^" element(s)") ;
  pos p2 ;
  err ("While this one has "^n2^" element(s)") ;
  err ("They should have the same arity") ;
  exit 2

let no_tuple p =
  pos p ;
  err "Wasn't expecting a tuple" ;
  exit 2

let no_tuple_for_type_app p px =
  pos px ;
  err ("This type is not an abbreviation") ;
  pos p ;
  err "You cannot pass a tuple as argument" ;
  exit 2

let tuple_too_big p = 
  pos p ;
  err "This tuple has more than 100 elements, use a record instead" ;
  exit 2

let not_pointer_type p_id p = 
  pos p ;
  err "This type is not a pointer" ;
  pos p_id ;
  err "It can only be applied to a type defined in the same module" ;
  exit 2


let infinite_loop p = 
  pos p ;
  err "This function call cannot be typed because it doesn't terminate" ;
  exit 2

let arity p1 p2 n1 n2 = 
  pos p1 ;
  err ("Arity mismatch, this expression is of arity "^soi n1) ;
  pos p2 ;
  err ("While this one is "^soi n2) ;
  exit 2

let unused p = 
  pos p ;
  err "Unused" ;
  exit 2

let unify_err p1 p2 fty1 fty2 = 
  let (p1, fty1), (p2, fty2) = 
    if p1 = Pos.none then (p2, fty2), (p1,fty1) else (p1, fty1), (p2, fty2) in
  if p1 == p2 || p2 = Pos.none
  then begin
    pos p1 ;
    err "This expression has type: " ;
    fty1 oerr ;
    err "It should be of type: " ;
    fty2 oerr ;
  end 
  else begin
    pos p1 ;
    err "This expression has type: " ;
    fty1 oerr ;
    err "It should have the same type as " ;
    pos p2 ;
    err "this expression which is of type: " ;
    fty2 oerr ;
    List.iter pos (Pos.history p1) ;
  end

let same_type p1 p2 = 
  pos p1 ;
  err "Because this expression must have the same type" ;
  pos p2 ;
  err "As this expression"

let rec unify err_l = 
  match err_l with
  | [] -> assert false
  | [Unify x] -> unify_err x.pos1 x.pos2 x.print1 x.print2
  | [_] -> assert false
  | Unify x :: rl -> 
      unify rl ;
      same_type x.pos1 x.pos2 
  | Fun_call p :: rl ->
      unify rl ;
      pos p ;
      err "Through this function call"

let unify err_l = unify err_l ; exit 2 

let unify_proj p1 p2 = 
  pos p2 ;
  err "You cannot project this field" ;
  pos p1 ;
  err "out of this expression" ;
  exit 2

let expected_numeric p =
  pos p ;
  err "Expected a numeric type" ;
  exit 2

let expected_function p = 
  pos p ;
  err ("Expected Function") ;
  exit 8


let recursive_type p =
  pos p ;
  err ("Recursive type") ;
  exit 8

let expected_bool p =
  pos p ;
  err "Expected bool" ;
  exit 2

let unused_branch p = 
  pos p ;
  err "This branch is unused" ;
  exit 2

let missing_fields p s = 
  pos p ;
  err "Some fields are missing" ;
  err s ;
  exit 2

let forgot_fields p l =
  pos p ;
  err "Some fields are missing" ;
  List.iter (Printf.fprintf stderr "%s\n") l ;
  exit 2

let useless p = 
  pos p ;
  err "All the fields are already captured" ;
  exit 2

let not_exhaustive p f = 
  pos p ;
  err "This pattern-matching is not exhaustive" ;
  err "Here is an example of a value that is not matched: " ;
  f stderr ;
  exit 2

let not_exhaustive_no_example p = 
  pos p ;
  err "This pattern-matching is not exhaustive" ;
  exit 2

let pat_too_general p f = 
  pos p ;
  err "This pattern is too general" ;
  err "It captures the case: " ;
  f stderr ;
  err "Which has been captured already" ;
  exit 2
  
let both_side_pattern p s = 
  pos p ;
  err ("The variable "^s^" must be defined in every branch of this pattern") ;
  exit 2

let field_no_val p = 
  pos p ;
  err ("You cannot capture this field because its value is undefined") ;
  exit 2

let missing_field p x = 
  let x = Ident.to_string x in
  pos p ;
  err ("You must define the field: "^x) ;
  exit 2

let fd_already_has_value p x = 
  let x = Ident.to_string x in
  pos p ;
  err ("Cannot redefine the value of the field: "^x) ;
  err "Because it has a non-primitive type" ;
  exit 2
  
let field_defined_both_sides p1 p2 x = 
  let x = Ident.to_string x in
  pos p1 ;
  err ("The field "^x^" must present in both this branch") ;
  pos p2 ;
  err "and in this one" ;
  exit 2

let underscore_obs p =
  pos p ;
  err "Underscore can only be used to match an observed value" ;
  exit 2

let obs_only_one p = 
  pos p ;
  err "obs expects only one argument" ;
  exit 2

let obs_expects_id p = 
  pos p ;
  err "obs is only applicable to a variable" ;
  exit 2

let free_expects_id p = 
  pos p ;
  err "free is only applicable to a variable" ;
  exit 2

let obs_not_value p = 
  pos p ;
  err "Bad usage of obs" ;
  exit 2

let free_not_value p = 
  pos p ;
  err "Bad usage of free" ;
  exit 2

let obs_not_allowed p = 
  pos p ;
  err "Illegal usage of observable" ;
  raise Exit 

let forgot_free p = 
  pos p ;
  err "This variable must be used or freed" ;
  exit 2

let forgot_free_branch p1 p2 = 
  pos p1 ;
  err "You forgot to free this variable" ;
  pos p2 ;
  err "In this branch" ;
  exit 2
  
let unused_variable p = 
  pos p ;
  err ("This variable hasn't been used or freed") ;
  exit 2

let already_used p p' = 
  pos p ;
  err "This variable has already been used" ;
  pos p' ;
  err "Previous usage was here" ;
  exit 2

let missing_record_name p = 
  pos p ;
  err "Pattern-matching on a record requires a name (Ex: { y ; myfield = x })";
  exit 2

let multiple_record_name p1 p2 = 
  pos p1 ;
  err "Multiple names for the same record";
  pos p2 ;
  err "Was previously defined here" ;
  exit 2

let internal s = 
  err s ;
  exit 3

let poly_is_not_prim p = 
  pos p ;
  err "You cannot use a primitive type here, a pointer is expected" ;
  exit 2

let prim_is_not_poly p = 
  pos p ;
  err "You cannot use a pointer here, a primitive type is expected" ;
  exit 2


let cannot_free_field p v = 
  pos p ;
  err ("This record cannot be freed because the field ["^(Ident.to_string v)^
       "] still carries a value") ;
  exit 2

let undef_field p fd = 
  pos p ;
  err ("The field "^fd^" is undefined") ;
  exit 2

let type_missing p = 
  pos p ;
  err "Missing type definition" ;
  exit 2

let cannot_free p fty = 
  pos p ;
  err "This expression has type: " ;
  fty oerr ;
  err "You can only free records" ;
  exit 2

let field_cannot_be_unit p = 
  pos p ;
  err "Illegal usage of type unit" ;
  exit 2

let invalid_extern_type p1 p2 = 
  pos p1 ;
  err "Illegal type in external function" ;
  if p2 <> p1
  then (pos p2 ; err "Cannot use this type") ;
  exit 2

let fun_external_and_local p1 p2 p3 = 
  pos p1 ;
  err "External function with a definition" ;
  pos p2 ;
  err "Was declared external here" ;
  pos p3 ;
  err "Definition is here" ;
  exit 2 

let fun_no_def p = 
  pos p ;
  err "This function has no definition" ;
  exit 2

let fun_no_decl p = 
  pos p ;
  err "You must define a signature for this function" ;
  exit 2
