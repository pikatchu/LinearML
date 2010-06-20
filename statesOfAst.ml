open Ast


let rec program set l = List.iter (handler set) l

and handler set (l,_) = List.iter (pat set) l

and pat set = function
  | Var x
  | Neg x -> set := IdSet.add x !set 


let program l = 
  let empty_set = ref IdSet.empty in
  program empty_set l ;
  !empty_set
