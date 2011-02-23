(*
Copyright (c) 2011, Julien Verlaguet
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:
1. Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the
distribution.

3. Neither the name of Julien Verlaguet nor the names of
contributors may be used to endorse or promote products derived
from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)
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
  "private"  , (fun lb -> PRIVATE (Pos.make lb)) ;
  "abstract" , (fun lb -> ABSTRACT (Pos.make lb)) ;
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

let wsnl = [' ' '\t' '\r' '\x0c' '\n']
let vprivate = "val" wsnl+ "private"
let tprivate = "type" wsnl+ "private"
let not_cend = ([^'*'] | '*' [^')'])+
let noise = [^'a'-'z''(''*']+

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
  | "::"               { COLCOL (Pos.make lexbuf) }
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
  | '!'                { EM (Pos.make lexbuf) }

  (* others *)
  | _                  { illegal_char (Lexing.lexeme_char lexbuf 0) }
  | eof                { EOF (Pos.make lexbuf) }


and comment c = parse
  | eof                { error "unterminated comment" }
  | '\n'               { Lexing.new_line lexbuf; comment c lexbuf }
  | "(*"               { comment (c+1) lexbuf }
  | "*)"               { if c = 0 then token lexbuf else comment (c-1) lexbuf }
  | _                  { comment c lexbuf }

and interface o c pp = parse
  | eof                { () }
  | ws+                { if pp then o (Lexing.lexeme lexbuf) ; 
			 interface o c pp lexbuf }
  | "(**"              { o (Lexing.lexeme lexbuf) ; 
			 interface o (c+1) true lexbuf }
  | tprivate           { interface o c false lexbuf }
  | vprivate           { interface o c false lexbuf }
  | "(*"               { interface o (c+1) false lexbuf }
  | '('                { if pp then o (Lexing.lexeme lexbuf) ; 
			 interface o c pp lexbuf }
  | '*'                { if pp then o (Lexing.lexeme lexbuf) ; 
			 interface o c pp lexbuf }			 
  | "*)"               { if pp then o (Lexing.lexeme lexbuf) ; 
			 interface o (c-1) pp lexbuf }
  | "begin"            { interface o (c+1) false lexbuf }
  | "let"              { interface o c false lexbuf }
  | "val"              { o (Lexing.lexeme lexbuf) ; 
			 interface o c true lexbuf }
  | "module"           { o "module type" ; 
			 interface o c true lexbuf }
  | "struct"           { o "sig" ; 
			 interface o c true lexbuf }
  | "type"             { o (Lexing.lexeme lexbuf) ; 
			 interface o c true lexbuf }
  | "end"              { o "\n" ; if c = 0 
                         then (o (Lexing.lexeme lexbuf) ;
			       interface o c true lexbuf)
	                 else interface o (c-1) pp lexbuf }
  | word               { if pp then o (Lexing.lexeme lexbuf) ; 
			 interface o c pp lexbuf }
  | noise+             { if pp then o (Lexing.lexeme lexbuf) ; 
			 interface o c pp lexbuf }

