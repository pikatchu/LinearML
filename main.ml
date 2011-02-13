open Lexing 

let parse fn = 
  Pos.file := fn ;
  let ic = open_in fn in
  let lb = Lexing.from_channel ic in
  try Parser.program Lexer.token lb
  with 
  | Lexer.Lexical_error _ -> Error.lexing_error lb 
  | Parsing.Parse_error -> Error.syntax_error lb 
    
let _ = 
  let module_l = ref Global.stdlib in
  let dump_llst = ref false in
  let bounds = ref false in
  let main = ref "" in
  Arg.parse 
    ["-main", Arg.String (fun s -> main := s), "specifies the root module";
     "-bounds", Arg.Unit (fun () -> bounds := true), "show unchecked bounds";
     "-llst", Arg.Unit (fun () -> dump_llst := true), "internal";
   ]
    (fun x -> module_l := x :: !module_l)
    (Printf.sprintf "%s files" Sys.argv.(0)) ;
  let ast = List.fold_left (
    fun acc x -> parse x @ acc
   ) [] !module_l in
  let nast = Naming.program ast in
  NastCheck.program nast ;
  let neast = NastExpand.program nast in
  NeastCheck.program neast ;
  let tast = Typing.program neast in
  let stast = StastOfTast.program tast in
  StastCheck.program stast ;
  RecordCheck.program stast ;
  LinearCheck.program stast ;
  let benv = BoundCheck.program !bounds stast in
  let ist = IstOfStast.program benv stast in
  let est = EstOfIst.program ist in
  let est = EstCompile.program est in
  let est = EstNormalizePatterns.program est in 
  let llst = LlstOfEst.program est in
  let llst = LlstOptim.inline llst in 
  let llst = LlstFree.program llst in  
  let llst = LlstOptim.program llst in 
  let llst = LlstRemoveUnit.program llst in 
  if !dump_llst then
    LlstPp.program llst ;       
(*    let llst = LlstPullRet.program llst in     *)
  ignore (Emit.program !main llst) 

