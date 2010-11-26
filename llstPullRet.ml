open Utils
open Llst

module Returns = struct

  let rec def df = 
    let t = ISet.empty in
    List.fold_left block t df.df_body

  and block t bl = 
    ret t bl.bl_ret

  and ret t = function
    | Return idl -> ty_idl t idl 
    | _ -> t

  and ty_idl t l = List.fold_left (
    fun t (_, x) -> ISet.add x t
   ) t l
end

module Graph = struct

  let add x y t = 
    let l = try IMap.find x t with Not_found -> [] in
    IMap.add x (y :: l) t

  let rec def df = 
    let g = IMap.empty in
    let g = List.fold_left block g df.df_body in
    g

  and block g bl = 
    let g = List.fold_left phi g bl.bl_phi in
    let g = List.fold_left equation g bl.bl_eqs in
    g

  and phi g (x, _, l) = 
    List.fold_left (
    fun g (y, _) ->
      add x y g
   ) g l

  and equation g (l, e) = 
    match l, e with
    | [_, x], Eid y -> add x y g
    | _ -> g

  let rec closure g rets = 
    if ISet.is_empty rets
    then rets
    else
      let next = ISet.fold (
	fun x acc ->
	  try 
	    List.fold_left (
	    fun acc x ->
	      ISet.add x acc
	   ) acc (IMap.find x g)
	  with Not_found -> acc
       ) rets ISet.empty in
      let rest = ISet.diff next rets in
      let next = closure g rest in
      ISet.union rets next

  let invert g = 
    IMap.fold (
    fun y l acc -> 
      List.fold_left (
      fun acc x -> add x y acc
     ) acc l
   ) g IMap.empty
    
end


module FilterOut = struct
  
  let rec def t df = 
    { df with df_body = List.map (block t) df.df_body }

  and block t bl = 
    let phi = List.fold_left (phi t) [] bl.bl_phi in
    let eqs = List.filter (equation t) bl.bl_eqs in
    { bl with bl_eqs = eqs ; bl_phi = phi }

  and equation t (_, e) = 
    match e with
    | Eid x when ISet.mem x t -> false
    | _ -> true

  and phi t acc (x, ty, l) = 
    let l = List.fold_left (
      fun acc (v, lbl) ->
	if ISet.mem v t
	then acc
	else (v, lbl) :: acc
     ) [] l in
    match l with
    | [] -> acc
    | _ -> (x, ty, l) :: acc

      
end

module Cut = struct

  let rec def df = 
    let nbr = List.length df.df_ret in
    let rets = Returns.def df in
    let g = Graph.def df in
    let cands = Graph.closure g rets in
    let cuts, bls = lfold (block nbr cands) ISet.empty df.df_body in
    let cuts = Graph.closure (Graph.invert g) cuts in
    ISet.iter Ident.print cuts ;
    let bls = List.map (FilterOut.block cuts) bls in
    { df with df_body = bls }

  and block n t acc bl = 
    let cut, eqs = List.fold_right (equation n t) bl.bl_eqs (None, []) in
    let bl = { bl with bl_eqs = eqs } in
    match cut with
    | None -> acc, bl
    | Some idl -> 
	List.fold_right (fun (_, x) acc -> ISet.add x acc) idl acc,
	{ bl with bl_ret = Return idl }
    
  and equation n cands (idl, e) (cut, eqs) = 
    if is_cut n cands idl && eqs = []
    then Some idl, [idl, e]
    else cut, (idl, e) :: eqs

  and is_cut n cands idl = 
    List.fold_left (
    fun b (_, x) -> b && ISet.mem x cands
   ) (List.length idl = n) idl

end

let rec program mdl = 
  List.map module_ mdl

and module_ md = 
  { md with md_defs = List.map def md.md_defs }

and def df = 
  let df = Cut.def df in  
  df
