open Lexing

type t = {
    pos_file: string ;
    pos_start: Lexing.position ;
    pos_end: Lexing.position ;
    pos_history: t list ref ;
  }

let file = ref ""

let none = {
  pos_file = "" ;
  pos_start = dummy_pos ;
  pos_end = dummy_pos ;
  pos_history = ref [] ;
}

let make (lb:Lexing.lexbuf) =
 let pos_start = lexeme_start_p lb in
 let pos_end = lexeme_end_p lb in
 let pos_history = ref [] in
 { pos_file = !file; pos_start = pos_start ; 
   pos_end = pos_end ; pos_history = pos_history }

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
  
let rec begin_end l = 
  match l with
  | [] -> assert false
  | x :: _ -> fst x, end_ l

and end_ x = 
  match x with
  | [] -> assert false
  | [x] -> fst x
  | _ :: rl -> end_ rl

let list l = 
  let b, e = begin_end l in
  btw b e, l

let push p h = 
  p.pos_history := h :: !(p.pos_history)

let history p = !(p.pos_history)
