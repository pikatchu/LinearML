open Lexing 

let o = output_string stderr 

let parse fn = 
  Pos.file := fn ;
  let ic = open_in fn in
  let lb = Lexing.from_channel ic in
  try Parser.program Lexer.token lb
  with 
  | Lexer.Lexical_error _ -> Error.lexing_error lb 
  | Parsing.Parse_error -> Error.syntax_error lb 
    
let _ = 
  let last_arg = (Array.length Sys.argv) - 1  in
  let module_l = ref [] in
  for i = 1 to last_arg do
    let new_module = parse Sys.argv.(i) in
    let nast = Naming.program new_module in
    NastCheck.program nast ;
    let neast = NastExpand.program nast in
    NeastCheck.program neast ;
    let tast = Typing.program neast in
    let stast = StastOfTast.program tast in
    StastCheck.program stast ;
    RecordCheck.program stast ;
    LinearCheck.program stast ;
(*    BoundCheck.program stast ; *)
    let ist = IstOfStast.program stast in
    let est = EstOfIst.program ist in
    let est = EstCompile.program est in
    let est = EstNormalizePatterns.program est in
    let llst = LlstOfEst.program est in
    let llst = LlstOptim.inline llst in
    let llst = LlstFree.program llst in
    let llst = LlstOptim.program llst in
    let llst = LlstRemoveUnit.program llst in
(*    let llst = LlstPullRet.program llst in     *)
(*    LlstPp.program llst ;  *)
    ignore (Emit.program llst) ; 
    module_l := new_module :: !module_l 
  done ;
  !module_l

