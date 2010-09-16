open Utils
open Ist

module SplitPat = struct

  let rec pat ptl = 
    let ptl = List.fold_right pat_tuple ptl [] in
    ptl 

  and pat_tuple pel acc = 
    match pel with
    | [] -> assert false
    | [x] -> 
	let xl = pat_el x in
	List.fold_right (fun x acc -> [x] :: acc) xl acc
    | x :: rl ->
	let rl = pat_tuple rl [] in
	let x = pat_el x in
	List.fold_right (
	fun x acc ->
	  List.fold_right (
	  fun rl acc -> (x :: rl) :: acc
	 ) rl acc
       ) x acc

  and pat_el (ty, pe) = 
    let pel = pat_ pe in
    List.map (fun x -> ty, x) pel

  and pat_ = function
    | Pany
    | Pvariant (_, [])
    | Pid _ as x -> [x]
    | Pvalue _ -> [Pany] (* only possible value is unit *)
    | Pvariant (x, p) -> 
	let pl = pat p in
	List.map (fun y -> Pvariant (x, [y])) pl 
    | Precord pfl -> 
	let pfid = List.fold_left pf_id None pfl in
	let pfll = List.fold_right pat_field pfl [] in
	let recl = break_record pfll in
	match pfid with
	| None -> List.map (fun x -> Precord x) recl
	| Some x -> List.map (fun l -> Precord (x :: l)) recl

  and break_record pfll = 
    match pfll with
    | [] -> assert false
    | [x, l] -> List.map (fun y -> [PField (x, [y])]) l
    | (x, l) :: rl -> 
	let recl = break_record rl in
	List.fold_right (
	fun recl acc -> 
	  List.fold_right (
	  fun p acc -> 
	    (PField (x, [p]) :: recl) :: acc
	 ) l acc
       ) recl []

  and pf_id acc pf  =
    match pf with
    | PFany
    | PFid _ -> Some pf
    | PField _ -> acc
	
  and pat_field pf acc =
    match pf with
    | PFany
    | PFid _ -> acc 
    | PField (x, p) -> (x, pat p) :: acc
end

module BreakPat = struct
(* If you understand this code, good for you ! because I don't ... *)
  open Est

  let make_idl = List.map (fun (ty, _) -> ty, Ident.tmp())

  let rec partition id s = function
    | [] -> s, None, []
    | ([], _) :: rl2 -> partition id s rl2
    | ((ty, Pvariant (x, l1)) :: rl1, a) :: rl2 -> 
	let s, todo, p = partition id s rl2 in
	s, todo, (match p with
	| [] -> [ty, `V x, [l1], [rl1, a]]
	| (_, `V y, subpl, pl) :: rl when x = y -> 
	    (ty, `V x, l1 :: subpl, (rl1, a) :: pl) :: rl
	| l -> 
	    let rest1, rest2 = 
	      match todo with
	      | None -> [], []
	      | Some a -> 
		  let rest1 = List.map (fun (ty, _) -> ty, Pany) l1 in
		  let l = List.map (fun (x, _) -> x, Pany) rl1 in
		  [rest1], [l, a]  
	    in 
	    (ty, `V x, l1 :: rest1, (rl1, a) :: rest2) :: l)
    | ([ty, Pany], a) :: rl2 ->
	let s, _, p = partition id s rl2 in
	s, None, (ty, `U, [[]], [[], a]) :: p
    | ((ty, Pany) :: rl1, a) :: rl2 ->
	let s, _, p = partition id s rl2 in
	s, Some a, (match p with
	| [] -> [ty, `U, [[]], [rl1, a]]
	| part ->
	    List.map (
	    fun (ty, x, subpl, pl) -> 
	      ty, x, subpl, (rl1, a) :: pl
	   ) part) 
    | ([ty, Pid x], a) :: rl2 -> 
	let s, _, p = partition id s rl2 in
	let s = IMap.add x id s in
	s, None, (ty, `U, [[]], [[], a]) :: p
    | ((ty, Pid x) :: rl1, a) :: rl2 -> 
	let s, _, p = partition id s rl2 in
	let s = IMap.add x id s in
	s, Some a, (match p with
	| [] -> [ty, `U, [[]], [rl1, a]]
	| part ->
	    List.map (
	    fun (ty, x, subpl, pl) -> 
	      ty, x, subpl, (rl1, a) :: pl
	   ) part) 
    | ((_, Precord _) :: _, _) :: _ -> assert false

  let rec pmatch subst idl pal =
    match idl with
    | [] -> assert false
    | id :: rl -> 
	let subst, _, pal = partition (snd id) subst pal in
	let subst, al = 
	  lfold (
	  fun subst (ty, x, subpl, al) -> 
	    let idl = make_idl (List.hd subpl) in
	    let pidl = List.map (fun (ty, x) -> ty, Pid x) idl in
	    if idl = []
	    then 
	      let subst, sub = 
		if rl = []
		then subst, snd (List.hd al)
		else pmatch subst rl al in
	      subst, (make_pat ty x pidl, sub)
	    else 
	      let subst, pal = make_sub (fst id) rl subst subpl al in
	      let subst, sub = pmatch subst idl pal in
	      subst, (make_pat ty x pidl, sub)
	 ) subst pal in
	subst, Ematch ([id], al)

  and make_sub ty idl subst subpl al =
    match subpl, al with
    | [], l -> subst, List.map (fun (_, x) -> [ty, Pany], x) l
    | _, [] -> assert false
    | p :: rl1, (a :: rl2 as al) ->
	let subst, sub = 
	  if idl = []
	  then subst, snd a
	  else pmatch subst idl al in
	let pa = p, sub in
	let subst, sub = make_sub ty idl subst rl1 rl2 in
	subst, pa :: sub
	
  and make_pat ty x pidl = 
    match x with
    | `V x -> [ty, Pvariant (x, pidl)]
    | `U -> [ty, Pany]
    
end

module PatOpt = struct
  open Est

  let rec dummy e = 
    match e with
    | Ematch (x, pal) -> 
	let pal = List.map (fun (x, y) -> x, dummy y) pal in
	let pal = truncate pal in
	(match pal with
	| ((_, Pany) :: _, e) :: _ -> e 
	| _ -> Ematch (x, pal)) 
    | x -> x

  and truncate = function
    | [] -> []
    | ((_, Pany) :: _, _) as last :: _ -> [last]
    | x :: rl  -> x :: truncate rl

  let rec exhaustive t e = e

  let expr t e = 
    let e = dummy e in 
    e
end


type t = {
    blocks: Est.block list ;
    eqs: Est.equation list ;
    subst: Ident.t IMap.t ;
  }

let empty = {
  blocks = [] ;
  eqs = [] ;
  subst = IMap.empty ;
}

let new_id = Ident.tmp
let new_label = Ident.tmp

let rec program mdl = 
  List.rev_map module_ mdl

and module_ md = {
    Est.md_id = md.md_id ;
    Est.md_decls = md.md_decls ;
    Est.md_defs = List.map def md.md_defs ;
  }

and def (x, p, e) = 
  let t = empty in
  let idl1 = make_params p in
  let t, idl2 = tuple t e in
  let fblock = block t.eqs (Est.Return idl2) in 
  let def = {
  Est.df_id = x ;
  Est.df_args = idl1 ;
  Est.df_return = idl2 ;
  Est.df_body = fblock :: t.blocks ;
  } in
  EstSubst.def t.subst def

and make_idl tyl = 
  List.map (fun ty -> (ty, new_id())) tyl

and make_params = function
  | [l] -> 
      List.map (
      fun (ty, x) -> 
	match x with
	| Pvalue (Eunit)
	| Pany -> (ty, new_id())
	| Pid x -> ty, x
	| _ -> assert false) l
  | _ -> assert false

and block eqs retl = {
  Est.bl_id = new_label() ;
  Est.bl_phi = [] ;
  Est.bl_eqs = List.rev eqs ;
  Est.bl_ret = retl ;
}

and pat p lbl = List.map (pat_tuple lbl) p
and pat_tuple lbl pel = List.map pat_el pel, lbl 
and pat_el (ty, p) = ty, pat_ p
and pat_ = function
  | Pany -> Est.Pany
  | Pid x -> Est.Pid x
  | Pvalue _ -> assert false
  | Pvariant (x, []) -> Est.Pvariant (x, [])
  | Pvariant (x, [p]) -> Est.Pvariant (x, List.map pat_el p)
  | Pvariant _ -> assert false
  | Precord pfl -> 
      let id_opt = get_rid pfl in
      let pfl = List.filter (function PField _ -> true | _ -> false) pfl in
      let pfl = List.map (
	function 
	  | PField (x, [p]) -> x, List.map pat_el p
	  | PField _ -> assert false
	  | _ -> assert false
       ) pfl in
      Est.Precord (id_opt, pfl)

and get_rid = function
  | [] -> None
  | PFid x :: _ -> Some x
  | _ :: rl -> get_rid rl

and tuple t el = 
  match el with
  | [] -> t, []
  | (tyl, e) :: rl -> 
      let t, idl1 = tuple t rl in
      let t, idl2 = expr_ t tyl e in
      t, idl2 @ idl1
  
and expr t (tyl, e) = 
  let t, idl = expr_ t tyl e in
  let id = lone idl in
  let id = fst id, snd id in
  t, id

and expr_ t tyl = function
  | Eid x -> t, [lone tyl, x]
(*      let idl = make_idl tyl in
      let t = equation t idl (Est.Eid x) in
      t, idl *)
  | Efield (e, x) -> 
      let idl = make_idl tyl in
      let t, id = expr t e in
      let t = equation t idl (Est.Efield (id, x)) in
      t, idl
  | Ematch (e, al) -> 
      let idl = make_idl tyl in
      let t, eidl = tuple t e in
      let t, al = List.fold_right action al (t, []) in
      let subst, e = BreakPat.pmatch t.subst eidl al in
      let t = { t with subst = subst } in
      let e = PatOpt.expr t e in
      let t, e = ematch 0 t tyl e in
      let t = equation t idl e in
      t, idl
  | Elet (p, e1, e2) -> 
      expr_ t tyl (Ematch (e1, [p, e2]))
  | Eif (e1, e2, e3) -> 
      let t, id1 = expr t e1 in
      let eqs = t.eqs in
      let t' = { t with eqs = [] } in
      let t', idl1 = tuple t' e2 in
      let bl1 = block t'.eqs (Est.Lreturn idl1) in
      let t = { t with blocks = bl1 :: t'.blocks } in
      let t = { t with eqs = [] } in
      let t', idl2 = tuple t e3 in
      let bl2 = block t'.eqs (Est.Lreturn idl2) in
      let t = { t with blocks = bl2 :: t'.blocks } in
      let t = { t with eqs = eqs } in
      let ridl = make_idl tyl in
      let t = equation t ridl (Est.Eif (id1, bl1.Est.bl_id, bl2.Est.bl_id)) in
      t, ridl
  | Eapply (x, e) -> 
      let t, idl1 = tuple t e in
      let idl2 = make_idl tyl in
      let t = equation t idl2 (Est.Eapply (x, idl1)) in
      t, idl2
  | Eseq (e1, e2) -> 
      let t, _ = expr t e1 in
      let t, idl = tuple t e2 in
      t, idl
  | e -> simpl_expr t tyl e

and simpl_expr t tyl e = 
  let x = new_id() in
  let ty = lone tyl in
  let id = ty, x in
  let t, e = simpl_expr_ t ty e in
  let t = equation t [id] e in
  t, [id]
  
and simpl_expr_ t ty = function
  | Evalue v -> t, Est.Evalue v
  | Evariant (x, e') -> 
      let t, idl = tuple t e' in
      t, Est.Evariant (x, idl)
  | Ebinop (bop, e1, e2) -> 
      let t, id1 = expr t e1 in 
      let t, id2 = expr t e2 in
      t, Est.Ebinop (bop, id1, id2)
  | Euop (uop, e) -> 
      let t, id = expr t e in
      t, Est.Euop (uop, id)
  | Erecord fdl -> 
      let t, fdl = lfold field t fdl in
      t, Est.Erecord fdl
  | Ewith (e, fdl) -> 
      let t, id = expr t e in
      let t, fdl = lfold field t fdl in
      t, Est.Ewith (id, fdl)
  | _ -> assert false

and field t (x, e) = 
  let t, idl = tuple t e in
  t, (x, idl)

and action (p, e) (t, acc) = 
  let t, label = make_block t e in
  let pll = SplitPat.pat p in
  let pll = List.fold_right (fun p acc -> pat [p] label :: acc) pll [] in
  let pl = List.flatten pll in
  t, pl @ acc  

and equation t idl e = {
  t with eqs = (idl, e) :: t.eqs
}

and make_block t e = 
  let eqs = t.eqs in
  let t = { t with eqs = [] } in
  let t, idl = tuple t e in
  let bl = block t.eqs (Est.Lreturn idl) in
  let t = { t with blocks = bl :: t.blocks } in
  let t = { t with eqs = eqs } in
  let label = Est.Ecall bl.Est.bl_id in
  t, label
            
and ematch depth t tyl e = 
  match e with
  | Est.Ecall _ -> t, e
  | Est.Ematch (c, al) ->
      let t, al = lfold (fun t (p, a) -> 
	let t, a = ematch (depth+1) t tyl a in
	t, (p, a)) t al in
      let idl = make_idl tyl in
      let ematch = Est.Ematch (c, al) in
      if depth = 0
      then t, ematch
      else
	let bl = block [idl, ematch] (Est.Lreturn idl) in
	let t = { t with blocks = bl :: t.blocks } in
	t, Est.Ecall bl.Est.bl_id
  | _ -> assert false
      
