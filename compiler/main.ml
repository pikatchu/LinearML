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
open Lexing 

let run s = 
  let code = Sys.command s in
  if code <> 0
  then (Printf.fprintf stderr "Error (%d): couldn't run %s\n" code s ;
	exit 2)
  else ()

let remove fnl = 
  List.iter (
  fun s ->
    ignore (run ("rm "^s))
 ) fnl

let check_suffix fn =
  if Filename.check_suffix fn ".lml" ||
  Filename.check_suffix fn ".lmli" then
    ()
  else begin
    Printf.fprintf stderr "Wrong suffix: %s\n" fn ; 
    exit 2
  end

let make_libname s = 
  let dir = Filename.dirname s in
  let name = Filename.basename s in
  if not (Filename.check_suffix name ".lmli")
  then begin
    Printf.fprintf stderr "Error: expected an lmli extension not \"%s\"\n" 
      name ;
    exit 2
  end ;
  assert (String.length name > 3) ;
  if String.sub name 0 3 <> "lib"
  then begin 
    Printf.fprintf stderr 
      "Error: expected a name that starts with lib not \"%s\"\n" 
      name ;
    exit 2
  end ;
  Filename.chop_suffix (Filename.concat dir name) ".lmli"

let add_link cmd s = 
  if Filename.check_suffix s ".lmli"
  then 
    let dir = Filename.dirname s in
    let base = Filename.basename s in
    let lname = Filename.chop_suffix base ".lmli" in
    let lname = String.sub lname 3 (String.length lname - 3) in
    let cmd = cmd ^ " -L" ^ dir ^ " -l" ^ lname ^ " " in
    cmd
  else cmd

let parse acc fn = 
  if not (Sys.file_exists fn)
  then (Printf.fprintf stderr "Couldn't find %s\n" fn ; exit 2) ;
  check_suffix fn ;
  Pos.file := fn ;
  let ic = open_in fn in
  let lb = Lexing.from_channel ic in
  try 
    let mdl = Parser.program Lexer.token lb in
    let acc = mdl @ acc in
    close_in ic ;
    acc
  with 
  | Lexer.Lexical_error _ -> Error.lexing_error lb 
  | Parsing.Parse_error -> Error.syntax_error lb

let output_interface o fn = 
  Pos.file := fn;
  if Filename.check_suffix fn "lml"
  then
    let ic = open_in fn in
    let lb = Lexing.from_channel ic in
    try 
      Lexer.interface o 0 true lb ;
      close_in ic
    with 
    | Lexer.Lexical_error _ -> Error.lexing_error lb 
  else ()
    
let _ = 
  let space n s = String.make n ' ' ^ s in
  let module_l = ref [] in
  let dump_llst = ref false in
  let dump_est = ref false in
  let dump_as = ref false in
  let bounds = ref false in
  let no_stdlib = ref false in
  let no_opt = ref false in
  let root = ref "" in
  let lib = ref "" in
  let oname = ref "a.out" in
  let print_int = ref false in
  Arg.parse 
    ["-root", Arg.String (fun s -> root := s), 
     space 10 "specifies the root module";
     "-bounds", Arg.Unit (fun () -> bounds := true), 
     space 8 "show unchecked bounds";
     "-llst", Arg.Unit (fun () -> dump_llst := true), 
     space 10 "internal";
     "-est", Arg.Unit (fun () -> dump_est := true),
     space 11 "internal";
     "-asm", Arg.Unit (fun () -> dump_as := true), 
     space 11 "internal" ;
     "-no-stdlib", Arg.Unit (fun () -> no_stdlib := true), 
     space 5 "excludes standard library";
     "-no-opt", Arg.Unit (fun () -> no_opt := true), 
     space 8 "disables optimizations" ;
     "-i", Arg.Unit (fun () -> print_int := true), 
     space 13 "print interface and exit" ;
     "-o", Arg.String (fun s -> oname := s), 
     space 13 "outputs executable" ;
     "-lib", Arg.String (fun s -> lib := s), 
     space 11 "creates a library" ;
   ]
    (fun x -> module_l := x :: !module_l)
    (Printf.sprintf "%s files" Sys.argv.(0)) ;
  if !print_int then
    let o = output_string stdout in
    List.iter (output_interface o) !module_l ; exit 0
  else () ;
  let base = if !lib = "" then !oname else make_libname !lib in
  if !lib = "" && !root = ""
  then (Printf.fprintf stderr "Root node missing !\n" ; exit 2) ;
  let ast = List.fold_left parse [] !module_l in
  let ast = if !no_stdlib then ast else parse ast Global.stdlib in
  let nast = Naming.program ast in
  NastCheck.program nast ;
  let neast = NastExpand.program nast in
  NeastCheck.program neast ;
  let types, tast = Typing.program neast in
  let stast = StastOfTast.program types tast in
  StastCheck.program stast ;
  RecordCheck.program stast ;
  LinearCheck.program stast ;
  let benv = BoundCheck.program !bounds stast in
  flush stderr ;
  let ist = IstOfStast.program benv stast in
  let ist = ExtractFuns.program ist in
  let est = EstOfIst.program ist in
  if !dump_est then
    EstPp.program est ;
  let est = EstCompile.program est in
  let est = EstNormalizePatterns.program est in 
  let llst = LlstOfEst.program est in
  let llst = LlstOptim.inline llst in 
  let llst = LlstFree.program llst in  
  let llst = LlstOptim.program llst in 
  if !dump_llst then
    LlstPp.program llst ;   
  let bc = Emit.program base !root !no_opt !dump_as llst in
  let cmd = Global.llc ^ Global.llc_opts ^ bc in
  run cmd ;
  let asm = base ^ ".s" in
  let obj = base ^ ".o" in
  let cmd = Global.cc ^ " -c " ^ asm ^ " -o " ^ obj in
  run cmd ;
  if !lib <> ""
  then
    let clib = base ^ ".a" in
    run (Global.ar ^ " rs " ^ clib ^ " " ^ obj) ;
    let oc = open_out (base ^ ".lmli") in
    let o = output_string oc in
    List.iter (output_interface o) !module_l ;
    close_out oc
  else begin
    let cmd = Global.cc ^ " " ^ obj ^ " -o " ^ base in
    let cmd = 
      if !no_stdlib then cmd else
      cmd ^ " -L"^Global.stdlibdir ^ " -lliml" in
    let cmd = List.fold_left add_link cmd !module_l in
    run cmd
  end ;
  remove [bc ; asm ; obj]

