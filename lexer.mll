{

open Parser

exception Lexical_error of string

let error msg = raise (Lexical_error msg)

(* Initializing the keyword table *)
let keywords = Hashtbl.create 23  (* small prime number *)
let assoc_keyword = [
  "and"    , (fun lb -> AND) ;
  "as"     , (fun lb -> AS) ;
  "when"   , (fun lb -> WHEN) ;
  "while"  , (fun lb -> WHILE) ;
  "with"   , (fun lb -> WITH) ;
  "match"  , (fun lb -> MATCH (Pos.make lb)) ;
  "let"    , (fun lb -> LET (Pos.make lb)) ;
  "module" , (fun lb -> MODULE) ;
  "struct" , (fun lb -> STRUCT) ;
  "end"    , (fun lb -> END) ;
  "if"     , (fun lb -> IF (Pos.make lb)) ;
  "then"   , (fun lb -> THEN) ;
  "else"   , (fun lb -> ELSE) ;
  "fun"    , (fun lb -> FUN (Pos.make lb)) ;
  "type"   , (fun lb -> TYPE) ;
  "true"   , (fun lb -> TRUE (Pos.make lb)) ;
  "false"  , (fun lb -> FALSE (Pos.make lb)) ;
  "sig"    , (fun lb -> SIG) ;
  "val"    , (fun lb -> VAL) ;
  "of"     , (fun lb -> OF) ;
  "rec"    , (fun lb -> REC) ;
  "for"    , (fun lb -> FOR) ;
  "do"     , (fun lb -> DO) ;
  "done"   , (fun lb -> DONE) ;
  "to"     , (fun lb -> TO) ;
  "begin"  , (fun lb -> BEGIN) ;
  "in"     , (fun lb -> IN) ;
  ]

let _ = 
  let add_keyword (x, y) = Hashtbl.add keywords x y in
  List.iter add_keyword assoc_keyword

let keyword lb = 
  let s = Lexing.lexeme lb in 
  try (Hashtbl.find keywords s) lb 
  with Not_found -> ID (Pos.make lb, s)


let illegal_char c = 
  let code = string_of_int (Char.code c) in
  error ("illegal character: " ^ code) 

}

let digit = ['0'-'9']
let letter = ['a'-'z''A'-'Z''_']
let alphanumeric = digit | letter
let word = ['a'-'z'] alphanumeric*
let qword = ''' word
let cword = ['A'-'Z'] alphanumeric*
let string = '\"' ('\\''\"' | [^'\"'])*'\"'
let ws = [' ' '\t' '\r' '\x0c']
let char = [''']'\\'?[^'''][''']
let float = digit+ '.' digit+


rule token = parse
  (* ignored *)
  | ws+                { token lexbuf }
  | '\n'               { Pos.new_line() ; token lexbuf }
      
  (* comments *)
  | "(*"               { comment lexbuf }
      
  | digit+             { INT (Pos.make lexbuf, Lexing.lexeme lexbuf) }
  | float              { FLOAT (Pos.make lexbuf, Lexing.lexeme lexbuf) }
  | word               { keyword lexbuf } 
  | qword              { TVAR (Pos.make lexbuf, Lexing.lexeme lexbuf) }
  | cword              { CSTR (Pos.make lexbuf, Lexing.lexeme lexbuf) }
  | string             { STRING (Pos.make lexbuf, let s = Lexing.lexeme lexbuf in 
			         String.sub s 1 (String.length s - 2)) }
  | char               { CHAR (Pos.make lexbuf, Lexing.lexeme lexbuf) }

  | "->"               { ARROW }      
  | "<-"               { ASSIGN }
  | ":="               { COLEQ }
  | ":"                { COLON }
  | "::"               { COLONCOLON (Pos.make lexbuf) }
  | '('                { LP (Pos.make lexbuf) }
  | ')'                { RP (Pos.make lexbuf) }      
  | ';'                { SC }
  | ','                { COMMA }
  | '|'                { BAR }
  | '='                { EQ }
  | "=="               { EQEQ }
  | '+'                { PLUS }
  | '-'                { MINUS (Pos.make lexbuf)}
  | '*'                { STAR }
  | '{'                { LCB (Pos.make lexbuf) }
  | '}'                { RCB (Pos.make lexbuf) }
  | '['                { LB (Pos.make lexbuf) }
  | ']'                { RB (Pos.make lexbuf) }
  | '_'                { UNDERSCORE (Pos.make lexbuf) }
  | '.'                { DOT }
  | "<="               { LTE }
  | '<'                { LT }
  | '>'                { GT }
  | ">="               { GTE }
  | '~'                { TILD (Pos.make lexbuf) }

  (* others *)
  | _                  { illegal_char (Lexing.lexeme_char lexbuf 0) }
  | eof                { EOF }


and comment  = parse
  | eof                { error "unterminated comment" }
  | '\n'               { Pos.new_line() ; comment lexbuf }
  | "*)"               { token lexbuf }
  | _                  { comment lexbuf }

