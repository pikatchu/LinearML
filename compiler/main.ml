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

let parse acc fn = 
  Pos.file := fn ;
  let ic = open_in fn in
  let lb = Lexing.from_channel ic in
  try 
    let acc = Parser.program Lexer.token lb @ acc in
    close_in ic ;
    acc
  with 
  | Lexer.Lexical_error _ -> Error.lexing_error lb 
  | Parsing.Parse_error -> Error.syntax_error lb 
    
let _ = 
  let module_l = ref [] in
  let dump_llst = ref false in
  let dump_est = ref false in
  let dump_as = ref false in
  let bounds = ref false in
  let no_stdlib = ref false in
  let no_opt = ref false in
  let main = ref "" in
  Arg.parse 
    ["-main", Arg.String (fun s -> main := s), "specifies the root module";
     "-bounds", Arg.Unit (fun () -> bounds := true), "show unchecked bounds";
     "-llst", Arg.Unit (fun () -> dump_llst := true), "internal";
     "-est", Arg.Unit (fun () -> dump_est := true), "internal";
     "-asm", Arg.Unit (fun () -> dump_as := true), "internal" ;
     "-no-stdlib", Arg.Unit (fun () -> no_stdlib := true), "excludes standard library";
     "-no-opt", Arg.Unit (fun () -> no_opt := true), "disables optimizations" ;
   ]
    (fun x -> module_l := x :: !module_l)
    (Printf.sprintf "%s files" Sys.argv.(0)) ;
  let ast = List.fold_left parse [] !module_l in
  let ast = if !no_stdlib then ast else List.fold_left parse ast Global.stdlib in
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
  let llst = LlstRemoveUnit.program llst in 
  if !dump_llst then
    LlstPp.program llst ;       
  ignore (Emit.program !main !no_opt !dump_as llst) 

