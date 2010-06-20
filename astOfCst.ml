open Ast



let rec program f l = List.map (handler f) l

and handler f (pl, hb)= (List.map (pat f) pl), (List.map (handler_body f) hb)

and pat f = function
  | Var s -> Ast.Var (f s)
  | Neg s -> Ast.Neg (f s)

and instruction f = function
  | Emit s_l -> Ast.Emit (List.map f s_l) 
  | Call s_l -> Ast.Call (List.map f s_l) 

and handler_body f (inst_l, case_l) = 
    (List.map (instruction f) inst_l), (List.map (case f) case_l)

and case f (pat_l, inst_l) = 
    (List.map (pat f) pat_l), (List.map (instruction f) inst_l)
