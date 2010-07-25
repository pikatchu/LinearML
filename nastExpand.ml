open Utils
open Nast

module Subst = struct

  let rec type_expr env (p, ty) = 
    match ty with
    | Tvar (_, x) when IMap.mem x env -> IMap.find x env
    | _ -> p, type_expr_ env ty

  and type_expr_ env = function
  | Tprim _ | Tpath _
  | Tid _ | Tvar _ as x -> x
  | Tapply (ty, tyl) -> Tapply (type_expr env ty, List.map (type_expr env) tyl)
  | Ttuple tyl -> Ttuple (List.map (type_expr env) tyl)
  | Tfun (ty1, ty2) -> Tfun (type_expr env ty1, type_expr env ty2)
  | Talgebric vl -> Talgebric (IMap.map (variant env) vl)
  | Trecord fdl -> Trecord (IMap.map (field env) fdl)
  | Tabbrev ty -> Tabbrev (type_expr env ty)
  | Tabs (vl, ty) ->
      let xl = List.map snd vl in
      let env = List.fold_right IMap.remove xl env in
      Tabs (vl, type_expr env ty)

  and variant env (id, ty_opt) = 
    id, match ty_opt with 
    | None -> None
    | Some ty -> Some (type_expr env ty)

  and field env (id, ty) = id, type_expr env ty
end

module Tuple = struct

  let rec type_expr_tuple ((p, _) as ty) = 
    match List.rev (snd (type_expr p (100, []) ty)) with
    | [x] -> x
    | l -> p, Ttuple l

  and type_expr pos (n, acc) (p, ty) = 
    let type_expr = type_expr pos in
    if n <= 0
    then Error.tuple_too_big pos 
    else match ty with
    | Tprim _
    | Tvar _ | Tid _ 
    | Tpath _ as x -> n-1, (p, x) :: acc
    | Ttuple tyl -> List.fold_left type_expr (n, acc) tyl
    | Tapply (ty, tyl) -> 
	let tyl = List.map type_expr_tuple tyl in
	n-1, (p, Tapply (ty, tyl)) :: acc

    | Tfun (ty1, ty2) -> 
	let ty1 = type_expr_tuple ty1 in
	let ty2 = type_expr_tuple ty2 in
	n-1, (p, Tfun (ty1, ty2)) :: acc

    | Talgebric vl -> n-1, (p, Talgebric (IMap.map variant vl)) :: acc
    | Trecord fdl -> n-1, (p, Trecord (IMap.map field fdl)) :: acc
    | Tabbrev ty -> type_expr (n, acc) ty
    | Tabs (idl, ty) -> 
	let ty = type_expr_tuple ty in
	n-1, (p, Tabs (idl, ty)) :: acc

  and variant (id, ty_opt) = 
    match ty_opt with
    | None -> id, None
    | Some ty -> id, Some (type_expr_tuple ty)

  and field (id, ty) = id, type_expr_tuple ty

end

module Abbrevs: sig

  val program: Nast.program -> Nast.program
end = struct

  let foreign = function Tpath _ -> true | _ -> false

  let check_pointer p_id (p, ty) = 
    match ty with
    | Tid _ | Tpath _ | Tapply _ -> ()
    | _ -> Error.not_pointer_type p_id p

  let check_abs id (p, ty) = 
    match ty with
    | Tabs (idl, _) -> Error.type_expects_arguments id (List.length idl) p
    | _ -> ()

  let rec program p = 
    let abbr = NastCheck.Abbrev.check p in
    let abbr = IMap.fold (fun _ x acc -> IMap.fold IMap.add x acc) abbr IMap.empty in
    let _, p = lfold (module_ abbr) IMap.empty p in
    p

  and module_ abbr mem md = 
    let mem, decls = lfold (decl abbr) mem md.md_decls in
    mem, { md with md_decls = decls }

  and decl abbr mem = function
    | Dtype tdl -> 
	let mem, tdl = List.fold_left (type_def abbr) (mem, []) tdl in
	mem, Dtype tdl 

    | Dval (id, ty) -> 
	let mem, ty = type_expr abbr mem ty in
	let ty = Tuple.type_expr_tuple ty in
	mem, Dval (id, ty)

  and type_def abbr (mem, acc) (id, ty) = 
    let mem, ty = type_expr abbr mem ty in
    let ty = Tuple.type_expr_tuple ty in
    if IMap.mem (snd id) abbr
    then mem, acc
    else mem, (id, ty) :: acc

  and type_expr abbr mem (p, ty) = 
    let mem, ty = type_expr_ abbr mem p ty in
    mem, (p, ty)

  and type_expr_ abbr mem p = function
    | Tprim _ | Tvar _ as x -> mem, x 

    | (Tpath (_, (_, x)) 
    | Tid (_, x)) when IMap.mem x mem -> 
	mem, snd (IMap.find x mem)

    | (Tpath (_, ((_, x) as id)) 
    | Tid ((_, x) as id)) when IMap.mem x abbr ->
	let mem, ty = type_expr abbr mem (IMap.find x abbr) in
	let mem = IMap.add x ty mem in
	check_abs id ty ;
	mem, (snd ty)

    | Tpath _ | Tid _ as x -> mem, x

    | Tapply ((p, Tpath ((p1,_), (p2, x))), ty) when IMap.mem x abbr -> 
	let px = Pos.btw p1 p2 in
	type_expr_ abbr mem p (Tapply ((p, Tid (px, x)), ty))

    | Tapply ((p, Tid (px, x)), tyl) when IMap.mem x abbr -> 
	let mem, tyl = lfold (type_expr abbr) mem tyl in
	let pdef, _ as ty = IMap.find x abbr in
	let args, ty = match ty with _, Tabs (vl, ty) -> vl, ty
	| _ -> Error.not_expecting_arguments px x pdef in
	let mem, ty = type_expr abbr mem ty in
	let size1 = List.length tyl in
	let size2 = List.length args in
	if size1 <> size2
	then Error.type_arity px x size1 size2 pdef ;
	let args = List.map snd args in
	let subst = List.fold_right2 IMap.add args tyl IMap.empty in
	let ty = Subst.type_expr subst ty in
	mem, snd ty

    | Tapply (ty, tyl) -> 
	let mem, ty = type_expr abbr mem ty in
	let mem, tyl = lfold (type_expr abbr) mem tyl in
	if foreign (snd ty)
	then List.iter (check_pointer (fst ty)) tyl ;
	mem, Tapply (ty, tyl)

    | Ttuple tyl -> 
	let mem, tyl = lfold (type_expr abbr) mem tyl in
	mem, Ttuple tyl

    | Tfun (ty1, ty2) -> 
	let mem, ty1 = type_expr abbr mem ty1 in
	let mem, ty2 = type_expr abbr mem ty2 in
	mem, Tfun (ty1, ty2)

    | Talgebric vl -> 
	let mem, vl = imlfold (variant abbr) mem vl in
	mem, Talgebric vl 

    | Trecord fdl -> 
	let mem, fdl = imlfold (field abbr) mem fdl in
	mem, Trecord fdl 

    | Tabbrev ty -> 
	let mem, ty = type_expr abbr mem ty in
	mem, snd ty

    | Tabs (idl, ty) -> 
	let mem, ty = type_expr abbr mem ty in
	mem, Tabs (idl, ty)

  and variant abbr mem (id, ty_opt) = 
    match ty_opt with
    | None -> mem, (id, None)
    | Some ty -> 
	let mem, ty = type_expr abbr mem ty in
	mem, (id, Some ty)

  and field abbr mem (id, ty) = 
    let mem, ty = type_expr abbr mem ty in
    mem, (id, ty)

end

module Pat: sig

  val pat: Nast.pat -> Pos.t * (Pos.t * Nast.pat list) list

end = struct
  open Nast

  let append l1 l2 =
    List.map (fun x -> l1 @ x) l2

  let rec combine l1 l2 = 
    List.fold_right (fun x acc -> 
      append x l2 @ acc) l1 []

  let check b1 b2 = 
    match b1, b2 with
    | [], _ | _, [] -> assert false
    | x1 :: _, x2 :: _ -> 
	(* We don't have to check the rest of the list by construction *)
	let n1 = List.length x1 in
	let n2 = List.length x2 in
	if n1 <> n2
	then 
	  let p1, _ = Pos.list x1 in
	  let p2, _ = Pos.list x2 in
	  Error.pbar_arity p1 n1 p2 n2
	else ()

  let rec pat l = 
    match l with
    | [] -> [[]]
    | (_, Pbar (b1, b2)) :: rl -> 
	let rl = pat rl in
	let b1 = pat [b1] in
	let b2 = pat [b2] in
	check b1 b2 ;
	combine b1 rl @ combine b2 rl

    | (_, Ptuple l) :: rl ->
	let rl = pat rl in
	let l = List.map (fun x -> pat [x]) l in
	List.fold_right combine l rl 

    | x :: rl -> 
	let rl = pat rl in
	append [x] rl

  let add_pos l = 
    Pos.list (List.map Pos.list l)

  let pat p = add_pos (pat [p])
	  
end


let rec program mdl = 
  let mdl = Abbrevs.program mdl in
  List.map module_ mdl

and module_ md = {
  Neast.md_id = md.md_id ;
  Neast.md_decls = List.map decl md.md_decls ;
  Neast.md_defs = List.map (def) md.md_defs ;
}

and decl = function
  | Dtype tdl -> Neast.Dtype (List.map tdef tdl)
  | Dval (x, ty) -> 
      match type_expr ty with
      | _, Neast.Tabs (_, (_, Neast.Tfun (tyl1, tyl2)))
      | _, Neast.Tfun (tyl1, tyl2) -> Neast.Dval (x, tyl1, tyl2)
      | p, _ -> Error.expected_function p

and tdef (id, ty) = (id, type_expr ty)

and type_expr (p, ty) = p, type_expr_ ty
and type_expr_ = function
  | Tprim t -> Neast.Tprim t
  | Tvar x -> Neast.Tvar x
  | Tid x -> Neast.Tid x 
  | Tapply (((_, Tid x) | (_, Tpath (_, x))), tyl) -> 
      Neast.Tapply (x, List.map type_expr tyl)
  | Tapply _ -> assert false
  | Ttuple _ -> assert false
  | Tpath (x, y) -> Neast.Tid y
  | Tfun (ty1, ty2) -> Neast.Tfun (type_expr_tuple ty1, type_expr_tuple ty2)
  | Talgebric vm -> Neast.Talgebric (IMap.map variant vm)
  | Trecord fdm -> Neast.Trecord (IMap.map field fdm) 
  | Tabbrev _ -> assert false
  | Tabs (xl, ty) -> Neast.Tabs (xl, type_expr ty)

and variant (x, ty) =
  x, match ty with
  | None -> []
  | Some ty -> type_expr_tuple ty

and field (x, ty) = 
  x, type_expr_tuple ty

and type_expr_tuple ((_, ty_) as ty) = 
  match ty_ with
  | Ttuple l -> List.map type_expr l
  | _ -> [type_expr ty]

and def (id, pl, e) = 
  let e = expr e [] in 
  let pl = pat_list pl in
  id, pl, e

and pat_list pl = 
  let pos, pl = Pos.list pl in
  pat (pos, Ptuple pl)

and pat p =
  let pos, p = Pat.pat p in
  pos, List.map pat_bar p

and pat_bar (p, x) = p, List.map pat_pos x

and pat_pos (p, x) = p, pat_ x
and pat_ = function
  | Pvalue v -> Neast.Pvalue v
  | Pany -> Neast.Pany
  | Pid x -> Neast.Pid x
  | Pcstr x 
  | Pecstr (_, x) -> Neast.Pvariant (x, (fst x, []))
  | Pevariant (_, x, p)
  | Pvariant (x, p) -> Neast.Pvariant (x, pat p)
  | Precord pfl -> Neast.Precord (List.map pat_field pfl)
  | Pbar _ -> assert false
  | Ptuple _ -> assert false

and pat_field (p, pf) = p, pat_field_ pf
and pat_field_ = function
  | PFany -> Neast.PFany
  | PFid x -> Neast.PFid x
  | PField (x, p) -> Neast.PField (x, pat p)

and expr (p, e) acc = 
  match e with
  | Etuple l -> List.fold_right (expr) l acc
  | _ -> (p, expr_ e) :: acc

and expr_ = function
  | Evalue v -> Neast.Evalue v
  | Eid x -> Neast.Eid x
  | Ecstr x -> Neast.Evariant (x, [])
  | Efield (e, x) -> 
      let e = simpl_expr e in
      Neast.Efield (e, x)

  | Ebinop (bop, e1, e2) ->
      let e1 = simpl_expr e1 in
      let e2 = simpl_expr e2 in
      Neast.Ebinop (bop, e1, e2)

  | Euop (uop, e) ->
      let e = simpl_expr e in
      Neast.Euop (uop, e)

  | Etuple _ -> assert false
  | Erecord fdl -> 
      let fdl = List.map (fun (x, e) -> x, expr e []) fdl in
      Neast.Erecord fdl

  | Elet (p, e1, e2) -> 
      let p = pat p in
      let e1 = expr e1 [] in
      let e2 = expr e2 [] in
      Neast.Elet (p, e1, e2)

  | Eif (e1, e2, e3) -> 
      let e1 = simpl_expr e1 in
      Neast.Eif (e1, expr e2 [], expr e3 [])

  | Efun _ -> assert false
  | Eapply (e, el) -> apply (simpl_expr e) (List.fold_right expr el [])
  | Ematch (e, pel) -> 
      let e = expr e [] in
      let pel = List.map (fun (p, e) -> pat p, expr e []) pel in
      Neast.Ematch (e, pel)

and simpl_expr ((p, _) as e) = 
  match expr e [] with
  | [e] -> e
  | _ -> Error.no_tuple p 

and apply e1 e2 = 
  match snd e1 with
  | Neast.Evariant (x, []) -> Neast.Evariant (x, e2)
  | Neast.Evariant _ -> assert false
  | Neast.Eid id -> Neast.Eapply (id, e2)
  | _ -> Error.expected_function (fst e1)
