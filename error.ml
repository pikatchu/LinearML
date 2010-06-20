open Utils

let err x = output_string stderr x ; output_string stderr "\n"
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
  err ("Error: "^id^" defined multiple times") ;
  exit 5

let type_arity_mismatch p1 p2 (_, id) n1 n2 = 
  pos p1 ;
  err ("Error: trying to apply "^ string_of_int n2^
       " arguments to "^ id) ;
  pos p2 ;
  err (id^" was declared with "^string_of_int n1^
       " arguments") ;
  exit 6

let application_to_primitive_type p id = 
  pos p ;
  err ("Error: "^id^" is a primitive type without arguments") ;
  exit 7

let expected_function pos1 pos2 = 
  pos pos1 ;
  err ("Expected Function") ;
  pos pos2 ;
  err ("This is not a function") ;
  exit 8

let undefined_sig p v = 
  pos p ;
  err ("Value "^v^" has no definition") ;
  exit 9
    
