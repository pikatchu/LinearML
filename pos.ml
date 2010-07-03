open Lexing

type t = {
    pos_file: string ;
    pos_start: Lexing.position ;
    pos_end: Lexing.position ;
  }

let file = ref ""
let line = ref 0

let none = {
  pos_file = "" ;
  pos_start = dummy_pos ;
  pos_end = dummy_pos ;
}

let new_line() = incr line

let make lb = {
  pos_file = !file ;
  pos_start = lexeme_start_p lb ;
  pos_end = lexeme_end_p lb ;
}

let btw x1 x2 = 
  if x1.pos_file <> x2.pos_file 
  then failwith "Position in separate files" ;
  if x1.pos_end > x2.pos_end
  then failwith "Invalid positions Pos.btw" ;
  { x1 with pos_end = x2.pos_end }

let string t = 
  let line = t.pos_start.pos_lnum in
  let start = t.pos_start.pos_cnum - t.pos_start.pos_bol in
  let end_ = t.pos_end.pos_cnum - t.pos_end.pos_bol in
  Printf.sprintf "File \"%s\", line %d, characters %d-%d:" 
    t.pos_file line start end_
  
let compare = compare
