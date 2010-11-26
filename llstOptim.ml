open Utils
open Llst

module Occ = struct

  let get x t = try IMap.find x t with Not_found -> 0

  let add x t = 
    let n = get x t in
    let n = n+1 in
    IMap.add x n t

  let rec def df = 
    let t = IMap.empty in
    List.fold_left block t df.df_body

  and block t bl = 
    let t = List.fold_left phi t bl.bl_phi in
    let t = ret t bl.bl_ret in
    t

  and ret t = function
  | Return _ -> t
  | Jump lbl -> add lbl t 
  | If (_, lbl1, lbl2) -> 
      let t = add lbl1 t in
      let t = add lbl2 t  in
      t
  | Switch (_, al, d) -> 
      let t = add d t in
      let t = List.fold_left action t al in
      t

  and phi t (_, _, l) = 
    List.fold_left phi_case t l

  and action t (_, lbl) = add lbl t
  and phi_case t (_, lbl) = add lbl t

end



module InlineBlocks = struct

  let rec program mdl = 
    List.rev_map module_ mdl

  and module_ md = 
    let defs = List.map def md.md_defs in
    { md with md_defs = defs }

  and def df = 
    let t = Occ.def df in
    let bls = List.fold_left (
      fun acc bl -> IMap.add bl.bl_id bl acc
     ) IMap.empty df.df_body in
    let suppr = ref ISet.empty in
    let bll = List.map (inline t bls suppr) df.df_body in
    if ISet.is_empty !suppr
    then df
    else 
      let bll = List.filter (fun b -> not (ISet.mem b.bl_id !suppr)) bll in
      { df with df_body = bll }

  and inline t bls suppr bl = 
    match bl.bl_ret with
    | Jump lbl when Occ.get lbl t = 1 && bl.bl_phi = [] -> 
	let tail = IMap.find lbl bls in
	let eqs = bl.bl_eqs @ tail.bl_eqs in
	suppr := ISet.add tail.bl_id !suppr ;
	inline t bls suppr { bl with bl_eqs = eqs ; bl_ret = tail.bl_ret }
    | _ -> bl


end

module Type: sig
  
  type t
  type env

  val program: Llst.program -> env
  val type_expr: env -> Llst.type_expr -> t
  val compare: t -> t -> int

end = struct

  type t = Llst.type_expr
  type env = Llst.type_expr IMap.t

  let rec program mdl = 
    let t = IMap.empty in
    let t = List.fold_left module_decl t mdl in
    t

  and module_decl t md = 
    List.fold_left decl_prim t md.md_decls

  and decl_prim t = function
    | Dtype (x, (Tprim _ as ty)) -> IMap.add x ty t
    | _ -> t

  and type_expr t = function
    | Tany
    | Tprim _ as x -> x
    | Tid x -> (try IMap.find x t with Not_found -> Tany)
    | Tfun _ -> Tany
    | Tstruct tyl -> Tstruct (List.map (type_expr t) tyl)
    | Tptr _ -> Tany

  let compare = Pervasives.compare

end

module Inplace = struct
  module Env = Map.Make (Type)

  let get ty env = 
    try Env.find ty env with Not_found -> []

  let push ty x env = 
    let l = get ty env in
    let l = x :: l in
    Env.add ty l env

  let pop ty env = 
    match get ty env with
    | [] -> env, None
    | x :: rl -> 
	let env = Env.add ty rl env in
	env, Some x

  let rec program mdl = 
    let t = Type.program mdl in
    List.map (module_ t) mdl 

  and module_ t md = 
    { md with md_defs = List.map (def t) md.md_defs }

  and def t df = 
    { df with df_body = List.map (block t) df.df_body } 

  and block t bl = 
    let acc = (Env.empty, ISet.empty, []) in
    let _, dels, eqs = List.fold_left (equation t) acc bl.bl_eqs in
    let eqs = List.rev eqs in
    let eqs = List.filter (suppr_free dels) eqs in
    { bl with bl_eqs = eqs }

  and equation t (env, dels, eqs) ((idl, e) as eq) = 
    match e with
    | Eapply (_, f, [ty, x]) when f = Naming.free -> 
	let ty = Type.type_expr t ty in
	let env = push ty x env in
	(env, dels, eq :: eqs)
    | Etuple (None, vl) ->
	(match idl with
	| [ty, x] -> 
	    let env, v = pop (Type.type_expr t ty) env in
	    (match v with 
	    | None -> env, dels, eq :: eqs
	    | Some vid -> 
		let vid' = Ident.tmp() in
		let v = Some (ty, vid') in
		let eqs = ([ty, vid'], Ecast (ty, vid)) :: eqs in
		let eqs = (idl, Etuple (v, vl)) :: eqs in
		let dels = ISet.add vid dels in
		(env, dels, eqs))
	| _ -> assert false)
    | _ -> env, dels, eq :: eqs

  and suppr_free dels (_, e) = 
    match e with
    | Eapply (_, f, [_, x]) when f = Naming.free -> not (ISet.mem x dels)
    | _ -> true

end 

module LoadStore = struct

  type value = 
    | Id of Ident.t
    | Field of Ident.t * int

  let rec program mdl = 
    let t = Type.program mdl in
    List.map (module_ t) mdl 

  and module_ t md = 
    { md with md_defs = List.map (def t) md.md_defs }

  and def t df = 
    { df with df_body = List.map (block t) df.df_body } 

  and block t bl = 
    let acc = IMap.empty in
    let env, eqs = lfold (equation t) acc bl.bl_eqs in
    { bl with bl_eqs = eqs }

  and eqid = function [_, x] -> x | _ -> assert false

  and equation t env ((idl, e) as eq) = 
    match e with
    | Ecast (_, x)
    | Eid x -> 
	(try 
	  IMap.add (eqid idl) (IMap.find x env) env, eq
	with Not_found -> env, eq)
    | Eproj ((_, x), n)
    | Efield ((_, x), n) -> 
	let v = eqid idl in
	IMap.add v (Field (x, n)) env, eq
    | Etuple (Some v, fdl) ->
	let rid = snd v in
	let fdl = List.filter (filter_field env rid) fdl in
	env, (idl, Etuple (Some v, fdl))
    | _ -> env, eq

  and filter_field env rid (n, (_, v)) = 
    try match IMap.find v env with
    | Field (r', n') -> not (r' = rid && n' = n)
    | _ -> true
    with Not_found -> true

       
end

let program mdl =
  let mdl = Inplace.program mdl in
  let mdl = LoadStore.program mdl in
  mdl

let inline mdl = InlineBlocks.program mdl
