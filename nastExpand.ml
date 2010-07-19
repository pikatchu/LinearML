open Utils
open Nast

module Debug = struct
  open Nast
  let rec pat o p = 
    o "(" ; List.iter (pat_tuple o) p ; o ")" 

  and pat_tuple o p = 
    o "[" ; List.iter (pat_ o) p ; o "]" 

  and pat_ o (_, p) = 
    begin match p with
  | Punit -> o "Punit"
  | Pany -> o "Pany" 
  | Pcstr x 
  | Pid x -> o (Ident.to_string (snd x))
  | _ -> assert false end ;
    o " "

  let o = output_string stdout
  let pat p = pat o p ; o "\n"

end

module Subst = struct

  let rec type_expr env (p, ty) = 
    match ty with
    | Tvar (_, x) when IMap.mem x env -> IMap.find x env
    | _ -> p, type_expr_ env ty

  and type_expr_ env = function
  | Tunit | Tbool | Tpath _
  | Tint32 | Tfloat | Tid _ | Tvar _ as x -> x
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

  let rec type_expr (p, ty) = 
    match type_expr_ [] (p, ty) with
    | [x] -> x
    | l -> (p, Ttuple (List.rev l))

  and type_expr_ acc (p, ty) = 
    match ty with
    | Tunit | Tbool | Tint32
    | Tfloat | Tvar _ | Tid _ 
    | Tpath _ as x -> (p, x) :: acc
    | Ttuple tyl -> List.fold_left type_expr_ acc tyl
    | Tapply (ty, tyl) -> 
	let tyl = List.map type_expr tyl in
	(p, Tapply (ty, tyl)) :: acc

    | Tfun (ty1, ty2) -> 
	let ty1 = type_expr ty1 in
	let ty2 = type_expr ty2 in
	(p, Tfun (ty1, ty2)) :: acc

    | Talgebric vl -> (p, Talgebric (IMap.map variant vl)) :: acc
    | Trecord fdl -> (p, Trecord (IMap.map field fdl)) :: acc
    | Tabbrev ty -> type_expr_ acc ty
    | Tabs (idl, ty) -> 
	let ty = type_expr ty in
	(p, Tabs (idl, ty)) :: acc

  and variant (id, ty_opt) = 
    match ty_opt with
    | None -> id, None
    | Some ty -> id, Some (type_expr ty)

  and field (id, ty) = id, type_expr ty

  let rec pat acc ((pos, p) as pp) =
      match p with
      | Ptuple p -> List.fold_left pat acc p
      | _ -> pp :: acc
		   
  let pat_list pl = List.rev (List.fold_left pat [] pl)
  let pat p = List.rev (pat [] p)
end

module Abbrevs: sig

  val program: Nast.program -> Nast.program
end = struct

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
	let ty = Tuple.type_expr ty in
	mem, Dval (id, ty)

  and type_def abbr (mem, acc) (id, ty) = 
    let mem, ty = type_expr abbr mem ty in
    let ty = Tuple.type_expr ty in
    if IMap.mem (snd id) abbr
    then mem, acc
    else mem, (id, ty) :: acc

  and type_expr abbr mem (p, ty) = 
    let mem, ty = type_expr_ abbr mem p ty in
    mem, (p, ty)

  and type_expr_ abbr mem p = function
    | Tunit | Tbool 
    | Tint32 | Tfloat | Tvar _ as x -> mem, x 

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

module Arity: sig

  val make: Nast.program -> (int * int) IMap.t

end  = struct
  
  let rec make mdl = 
    List.fold_left module_ IMap.empty mdl

  and module_ env md = 
    List.fold_left decl env md.md_decls

  and decl env = function
  | Dtype _ -> env
  | Dval (x, ty) -> type_expr env (snd x) ty

  and type_expr env x (_, ty) = 
    match ty with 
    | Tfun (ty1, ty2) -> IMap.add x (arity ty1, arity ty2) env
    | _ -> failwith "TODO expected function type"

(* This works because we expanded all the tuples in *)
(* type definitions at this point *)
  and arity (_, ty) = 
    match ty with
    | Ttuple l -> List.length l
    | _ -> 1

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
	let p1, _ = Pos.list x1 in
	let p2, _ = Pos.list x2 in
	if n1 <> n2
	then Error.pbar_arity p1 n1 p2 n2
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

let check_arity l1 l2 = 
  if List.length (snd l1) <> List.length (snd l2)
  then failwith "TODO bad arity" 
  else ()

let rec program mdl = 
  let mdl = Abbrevs.program mdl in
  let arity = Arity.make mdl in
  List.map (module_ arity) mdl

and module_ arity md = {
  Neast.md_id = md.md_id ;
  Neast.md_decls = List.map decl md.md_decls ;
  Neast.md_defs = List.map (def arity) md.md_defs ;
}

and decl = function
  | Dtype tdl -> Neast.Dtype (List.map tdef tdl)
  | Dval (x, ty) -> Neast.Dval (x, type_expr ty)

and tdef (id, ty) = (id, type_expr ty)

and type_expr (p, ty) = p, type_expr_ ty
and type_expr_ = function
  | Tunit -> Neast.Tunit
  | Tbool -> Neast.Tbool
  | Tint32 -> Neast.Tint32
  | Tfloat -> Neast.Tfloat
  | Tvar x -> Neast.Tvar x
  | Tid x -> Neast.Tid x 
  | Tapply (ty, tyl) -> Neast.Tapply (type_expr ty, List.map type_expr tyl)
  | Ttuple _ -> assert false
  | Tpath (x, y) -> Neast.Tpath (x, y) 
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

and def arity (id, pl, e) = 
  let e = expr arity e in 
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
  | Punit -> Neast.Punit
  | Pany -> Neast.Pany
  | Pid x -> Neast.Pid x
  | Pchar x -> Neast.Pchar x
  | Pint x -> Neast.Pint x
  | Pbool x -> Neast.Pbool x
  | Pfloat x -> Neast.Pfloat x
  | Pstring x -> Neast.Pstring x
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

and expr arity (p, e) = p, expr_ arity e 
and expr_ arity = function
  | Eunit -> Neast.Eunit
  | Ebool x -> Neast.Ebool x
  | Eextern (_, x)
  | Eid x -> Neast.Eid x
  | Eint x -> Neast.Eint x
  | Efloat x -> Neast.Efloat x
  | Echar x -> Neast.Echar x
  | Estring x -> Neast.Estring x
  | Ecstr x -> Neast.Evariant (x, [])
  | Eecstr (_, x) -> Neast.Evariant (x, [])
	(* TODO add check for variant arity *)
  | Efield (e, x) 
  | Eefield (e, _, x) -> Neast.Efield (e, x)

  | Ebinop (bop, e1, e2) ->
      let e1 = expr e1 in
      let e2 = expr e2 in
      Neast.Ebinop (bop, e1, e2)

  | Euop (uop, e) ->
      let e = expr e in
      Neast.Euop e

  | Etuple _ -> assert false
(*  | Erecord of (id * expr) list 
  | Elet of pat * expr * expr
  | Eif of expr * expr * expr 
  | Efun of pat list * expr 
  | Eapply of expr * expr list
  | Ematch of expr * (pat * expr) list
*)

