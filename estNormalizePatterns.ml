open Utils
open Ist
open Est

module Env = struct

  let rec program mdl = 
    let t = IMap.empty in
    let t = List.fold_left module_ t mdl in
    t

  and module_ t md = 
    List.fold_left decl t md.md_decls

  and decl t = function
    | Dalgebric td -> tdef t td
    | _ -> t

  and tdef t td = 
    let vl = IMap.fold (
      fun x (_, args) acc ->
	match args with
	| [] -> ISet.add x acc
	| _ -> acc
     ) td.td_map ISet.empty in
    IMap.add td.td_id vl t

end

module EnvCounts = struct

  let rec program mdl = 
    let t = IMap.empty in
    let t = List.fold_left module_ t mdl in
    t

  and module_ t md = 
    List.fold_left decl t md.md_decls

  and decl t = function
    | Dalgebric td -> tdef t td
    | _ -> t

  and tdef t td = 
    let n = IMap.fold (
      fun _ _ acc -> 1 + acc
     ) td.td_map 0 in
    IMap.add td.td_id n t

end

module Normalize = struct

  let rec default = function
    | [] -> None
    | ([_, Pany], a) :: _ -> Some a
    | _ :: rl -> default rl

  let rec type_expr t = function
    | Tany 
    | Tprim _
    | Tvar _ -> None
    | Tapply (x, [ty]) when x = Naming.tobs -> type_expr t ty
    | Tid x 
    | Tapply (x, _) -> (try Some (IMap.find x t) with Not_found -> None)
    | Tfun _ -> None

  let rec pmatch t ty al = 
    match type_expr t ty with
    | None -> al
    | Some vs -> action vs al 

  and action vs al = 
    match al with
    | [] -> []
    | ([_, Pvariant (x, [])], _) as a :: rl ->
	let vs = ISet.remove x vs in
	let rl = action vs rl in
	a :: rl
    | ([ty, Pvariant (_, _)], _) :: rl -> 
	add_cases ty vs (default rl) al
    | ([_, Pany], _) :: _ -> al
    | _ -> assert false

  and add_cases ty vs d al =
    match d with 
    | None -> al
    | Some d -> 
	ISet.fold (
	fun v al ->
	  ([ty, Pvariant (v, [])], d) :: al)
	  vs al

end

module RemoveOption = struct

  let is_option al = 
    let l = List.map fst al in
    try List.iter (
      function 
	| [_, Pvariant (x, _)] when x = Naming.none || x = Naming.some ->
	    raise Exit
	| _ -> ()
     ) l ; false
    with Exit -> true

  let rec make_none al = 
    match al with
    | [] -> assert false
    | ([_, Pvariant (x, [])], lbl) :: _ when x = Naming.none ->
	lbl
    | _ :: rl -> make_none rl

  let rec make_some v t al = 
    match al with
    | [] -> assert false
    | ([_, Pany], lbl) :: _ ->
	t, lbl
    | ([_, Pvariant (x, [ty, Pid y])], lbl) :: _ when x = Naming.some ->
	let casts = try IMap.find lbl t with Not_found -> [] in
	IMap.add lbl (((ty, y), v) :: casts) t, lbl
    | _ :: rl -> make_some v t rl

  let add_cast t bl = 
    if IMap.mem bl.bl_id t
    then 
      let casts = IMap.find bl.bl_id t in
      let eqs = List.fold_right (
	fun (x, y) acc -> ([x], Est.Eid y) :: acc
       ) casts bl.bl_eqs in
      { bl with bl_eqs = eqs }
    else bl
	
  let rec def df = 
    let t = IMap.empty in
    let t, bll = List.fold_right block df.df_body (t, []) in
    let bll = List.map (add_cast t) bll in 
    let df = { df with df_body = bll } in
    df

  and block bl (t, acc) = 
    let work, rt = ret t bl.bl_ret in
    match work with
    | None -> t, bl :: acc
    | Some (t, eqs) ->
	t, { bl with bl_eqs = bl.bl_eqs @ eqs ; bl_ret = rt } :: acc

  and ret t = function
    | Match ([v], al) when is_option al -> 
	let cid = Tprim Tbool, Ident.tmp() in
	let eqs = [[cid], Eis_null v] in
	let lbl1 = make_none al in
	let t, lbl2 = make_some v t al in 
	Some (t, eqs), If (cid, lbl1, lbl2)
    | x -> None, x

  
end

module RemoveUnderscore = struct

  let rec type_expr t = function
    | Tany 
    | Tprim _
    | Tvar _ -> None
    | Tapply (x, [ty]) when x = Naming.tobs -> type_expr t ty
    | Tid x 
    | Tapply (x, _) -> (try Some (IMap.find x t) with Not_found -> None)
    | Tfun _ -> None

  let rec pmatch t ty al = 
    match type_expr t ty with
    | None -> al
    | Some n -> action n 0 al 

  and action total n al = 
    match al with
    | [] -> []
    | ([_, Pvariant (_, _)], _) as a :: rl ->
	let rl = action total (n+1) rl in
	a :: rl
    | [[_, Pany], _] when n = total -> []
    | al -> al

end

type env = {
    noargs: ISet.t IMap.t ;
    counts: int IMap.t ;
  }

let rec program mdl = 
  let noargs = Env.program mdl in
  let counts = EnvCounts.program mdl in
  let t = { noargs = noargs ; counts = counts } in
  List.rev_map (module_ t) mdl 

and module_ t md = 
  let defs = List.map (def t) md.md_defs in
  { md with md_defs = defs }

and def t df = 
  let body = List.map (block t) df.df_body in
  let df = { df with df_body = body } in
  let df = RemoveOption.def df in
  df

and block t bl = 
  let rt = ret t bl.bl_ret in
  { bl with bl_ret = rt }

and ret t = function
  | Lreturn _
  | Return _
  | Jump _
  | If _ as x -> x
  | Match ([ty, _] as c, al) -> 
      let al = Normalize.pmatch t.noargs ty al in
      let al = RemoveUnderscore.pmatch t.counts ty al in 
      let al = List.sort compare_pat al in 
      Match (c, al)
  | Match _ -> assert false

and compare_pat (x, _) (y, _) = 
  match snd (List.hd x), snd (List.hd y) with
  | Pvariant (x, []), Pvariant (y, []) -> Ident.compare x y
  | Pvariant (_, []), _ -> -1
  | _, Pvariant (_, []) -> 1
  | Pvariant (x, _), Pvariant (y, _) -> Ident.compare x y
  | Pvariant (_, _), _ -> -1
  | _, Pvariant (_, _) -> 1
  | x, y -> Pervasives.compare x y


