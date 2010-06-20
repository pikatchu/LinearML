
module StringId = struct 
  type t = string 
  let compare = String.compare
end

module IdSet = Set.Make(StringId)

type env = { 
    mutable sigs:  IdSet.t ;
    mutable cvars: IdSet.t ;
}

open Ast

let rec program l = 
  let env = { sigs = IdSet.empty ; cvars = IdSet.empty } in
  List.iter (handler env) l ;
  env

and handler env (pl, hb) = 
  List.iter (pat env) pl ;
  List.iter (handler_body env) hb

and pat env = function
  | Var s 
  | Neg s -> env.sigs <- IdSet.add s env.sigs 

and instruction env = function
  | Emit s_l -> List.iter (fun x -> env.sigs <- IdSet.add x env.sigs) s_l
  | Call s_l -> List.iter (fun x -> env.cvars <- IdSet.add x env.cvars) s_l

and handler_body env (inst_l, case_l) = 
  List.iter (instruction env) inst_l ;
  List.iter (case env) case_l 

and case env (pat_l, inst_l) = 
  List.iter (pat env) pat_l ;
  List.iter (instruction env) inst_l


module IdMap = Map.Make (StringId)
module TraceId = Map.Make (struct type t = int let compare = (-) end)

let naming id_set = 
  let tab = ref IdMap.empty in
  let back_tab = ref TraceId.empty in
  let i = ref 0 in
  IdSet.iter 
    (fun elt ->
      if not (IdMap.mem elt !tab)
      then 
	(incr i ; 
	 tab := IdMap.add elt !i !tab ; 
	 back_tab := TraceId.add !i elt !back_tab)) 
    id_set ;
  !tab
