{

open Parser

exception Lexical_error of string

let error msg = raise (Lexical_error msg)

(* Initializing the keyword table *)
let keywords = Hashtbl.create 23  (* small prime number *)
let assoc_keyword = [
  "and"    , (fun lb -> AND (Pos.make lb)) ;
  "as"     , (fun lb -> AS (Pos.make lb)) ;
  "when"   , (fun lb -> WHEN (Pos.make lb)) ;
  "while"  , (fun lb -> WHILE (Pos.make lb)) ;
  "with"   , (fun lb -> WITH (Pos.make lb)) ;
  "match"  , (fun lb -> MATCH (Pos.make lb)) ;
  "let"    , (fun lb -> LET (Pos.make lb)) ;
  "module" , (fun lb -> MODULE (Pos.make lb)) ;
  "struct" , (fun lb -> STRUCT (Pos.make lb)) ;
  "end"    , (fun lb -> END (Pos.make lb)) ;
  "if"     , (fun lb -> IF (Pos.make lb)) ;
  "then"   , (fun lb -> THEN (Pos.make lb)) ;
  "else"   , (fun lb -> ELSE (Pos.make lb)) ;
  "fun"    , (fun lb -> FUN (Pos.make lb)) ;
  "type"   , (fun lb -> TYPE (Pos.make lb)) ;
  "true"   , (fun lb -> TRUE (Pos.make lb)) ;
  "false"  , (fun lb -> FALSE (Pos.make lb)) ;
  "sig"    , (fun lb -> SIG (Pos.make lb)) ;
  "val"    , (fun lb -> VAL (Pos.make lb)) ;
  "of"     , (fun lb -> OF (Pos.make lb)) ;
  "rec"    , (fun lb -> REC (Pos.make lb)) ;
  "for"    , (fun lb -> FOR (Pos.make lb)) ;
  "do"     , (fun lb -> DO (Pos.make lb)) ;
  "done"   , (fun lb -> DONE (Pos.make lb)) ;
  "to"     , (fun lb -> TO (Pos.make lb)) ;
  "begin"  , (fun lb -> BEGIN (Pos.make lb)) ;
  "in"     , (fun lb -> IN (Pos.make lb)) ;
  "not"    , (fun lb -> NOT (Pos.make lb)) ;
  "asm"    , (fun lb -> ASM (Pos.make lb)) ;
  "internal" , (fun lb -> INTERNAL (Pos.make lb)) ;
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
  | '\n'               { Lexing.new_line lexbuf; token lexbuf }
      
  (* comments *)
  | "(*"               { comment 0 lexbuf }
      
  | digit+             { INT (Pos.make lexbuf, Lexing.lexeme lexbuf) }
  | float              { FLOAT (Pos.make lexbuf, Lexing.lexeme lexbuf) }
  | word               { keyword lexbuf } 
  | qword              { TVAR (Pos.make lexbuf, Lexing.lexeme lexbuf) }
  | cword              { CSTR (Pos.make lexbuf, Lexing.lexeme lexbuf) }
  | string             { STRING (Pos.make lexbuf, let s = Lexing.lexeme lexbuf in 
			         String.sub s 1 (String.length s - 2)) }
  | char               { CHAR (Pos.make lexbuf, Lexing.lexeme lexbuf) }

  | "->"               { ARROW (Pos.make lexbuf) }
  | "#->"              { SARROW (Pos.make lexbuf) }
  | "<-"               { ASSIGN (Pos.make lexbuf) }
  | ":="               { COLEQ (Pos.make lexbuf) }
  | ":"                { COLON (Pos.make lexbuf) }
  | '('                { LP (Pos.make lexbuf) }
  | ')'                { RP (Pos.make lexbuf) }      
  | ';'                { SC (Pos.make lexbuf) }
  | ','                { COMMA (Pos.make lexbuf) }
  | '|'                { BAR (Pos.make lexbuf) }
  | '='                { EQ (Pos.make lexbuf) }
  | "<>"               { DIFF (Pos.make lexbuf) }
  | "=="               { EQEQ (Pos.make lexbuf) }
  | "||"               { BARBAR (Pos.make lexbuf) }
  | "&&"               { AMPAMP (Pos.make lexbuf) }
  | '+'                { PLUS (Pos.make lexbuf) }
  | '-'                { MINUS (Pos.make lexbuf)}
  | '*'                { STAR (Pos.make lexbuf) }
  | '/'                { SLASH (Pos.make lexbuf) }
  | '{'                { LCB (Pos.make lexbuf) }
  | '}'                { RCB (Pos.make lexbuf) }
  | '['                { LB (Pos.make lexbuf) }
  | ']'                { RB (Pos.make lexbuf) }
  | '_'                { UNDERSCORE (Pos.make lexbuf) }
  | '.'                { DOT (Pos.make lexbuf) }
  | "<="               { LTE (Pos.make lexbuf) }
  | '<'                { LT (Pos.make lexbuf) }
  | '>'                { GT (Pos.make lexbuf) }
  | ">="               { GTE (Pos.make lexbuf) }
  | '~'                { TILD (Pos.make lexbuf) }

  (* others *)
  | _                  { illegal_char (Lexing.lexeme_char lexbuf 0) }
  | eof                { EOF (Pos.make lexbuf) }


and comment c = parse
  | eof                { error "unterminated comment" }
  | '\n'               { Lexing.new_line lexbuf; comment c lexbuf }
  | "(*"               { comment (c+1) lexbuf }
  | "*)"               { if c = 0 then token lexbuf else comment (c-1) lexbuf }
  | _                  { comment c lexbuf }

