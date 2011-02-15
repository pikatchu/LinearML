open Utils
open Ist
open Est

(* Module sorting the different kinds of algebric data types *)
(* This is because an algebric data type can be represented as an *)
(* enum, as just a record or as a discriminated union. *)
(* Variants with arguments don't necessarely need a tag *)
(* Variants without arguments can be represented as a null pointer *)

module Pointer: sig

  type t

  val empty: t
  val program: Est.program -> t
  val type_expr: t -> Ist.type_expr -> bool
  
end = struct

  type t = ISet.t

  let empty = ISet.empty

  let rec program mdl = 
    let t = ISet.empty in
    List.fold_left module_ t mdl

  and module_ t md = 
    List.fold_left decl t md.md_decls

  and decl t = function
    | Dalgebric td -> ISet.add td.td_id t
    | _ -> t

  let rec type_expr t = function
    | Tany -> true
    | Tprim _ -> false
    | Tvar _ -> true 
    | Tid x
    | Tapply (x, _) -> not (ISet.mem x t) 
    | Tfun _ -> true
  
end

module PredefTypes = struct
  open Llst

  let (++) acc (x, y) = IMap.add x y acc 

  let make() = IMap.empty

end

module VEnv = struct

  type t = {
      pointers: Pointer.t ;
      is_tagged: ISet.t ;
      is_null: ISet.t ;
      values: int IMap.t ;
      types: Llst.type_expr IMap.t ;
      is_rec: ISet.t ;
    }

  let empty = {
    pointers = Pointer.empty;
    is_tagged = ISet.empty;
    is_null = ISet.singleton Naming.none;
    values = IMap.empty;
    types = IMap.empty ;
    is_rec = ISet.empty ;
  }

  let add b x _ acc = 
    if b 
    then ISet.add x acc 
    else acc

  let update t tag vals ir = { t with
    is_tagged = tag ;
    values = vals ;
    is_rec = ir ;			      
  }

  let rec program mdl = 
    let t = empty in
    let t = { t with pointers = Pointer.program mdl } in
    List.fold_left module_ t mdl

  and module_ t md = 
    List.fold_left decl t md.md_decls

  and decl t = function
    | Dalgebric td -> tdef t td
    | Drecord td -> 
	let n = ref 0 in
	let vals = IMap.fold (
	  fun x (_, tyl) acc -> 
	    let acc = IMap.add x !n acc in
	    incr n ;
	    List.iter (fun _ -> incr n) (List.tl tyl) ;
	    acc
	 ) td.td_map t.values in
	{ t with values = vals }
    | _ -> t

  and tdef t td = 
    let zargs = IMap.fold has_no_args td.td_map 0 in
    let nzargs = IMap.fold has_args td.td_map 0 in
    let is_tagged = 
      if nzargs = 1
      then ISet.add td.td_id t.is_tagged
      else t.is_tagged 
    in
    let is_tagged = IMap.fold (add (nzargs > 1)) td.td_map is_tagged in
    let values = IMap.fold (add_simpl_value (ref 0)) td.td_map t.values in
    let values = IMap.fold (add_cplx_value (ref (-1))) td.td_map values in
    let is_rec = 
      if zargs = 1 && nzargs = 1 && false (* TODO check if this is usefull *)
      then ISet.add td.td_id t.is_rec 
      else t.is_rec in
    let t = update t is_tagged values is_rec in
    t

  and add_simpl_value counter x (_, l) acc = 
    if l = [] then begin
      incr counter ; 
      IMap.add x !counter acc
    end
    else acc

  and add_cplx_value counter x (_, l) acc = 
    if l <> [] then begin
      incr counter ; 
      IMap.add x !counter acc
    end
    else acc

  and has_args _ (_, args) n = 
    if args = []
    then n
    else n+1

  and has_no_args _ (_, args) n = 
    if args = []
    then n+1
    else n
end

module ExtractArgs = struct
  open VEnv

  let rec def t mkty df = 
    List.fold_left (block t mkty) IMap.empty df.df_body 

  and block t mkty acc bl = ret t mkty acc bl.bl_ret

  and ret t mkty acc = function
    | Match ([ty, v], al) -> 
	let ty = mkty ty in
	let v = ty, v in
	List.fold_left (action t mkty v) acc al
    | Match _ -> assert false
    | _ -> acc

  and action t mkty v acc (p, lbl) =
    match p with
    | [_, Pvariant (x, [])] -> acc
    | [ty, Pvariant (x, l)] -> 
	let variant_ty = Llst.Tid x (* IMap.find x t.types in *) in
	let tmp = variant_ty, Ident.tmp() in
	let is_obs = match ty with 
	  Tapply (x, _) -> x = Naming.tobs | _ -> false in
	let eqs = 
	  if is_obs 
	  then [] 
	  else 
	    let dummy = Llst.Tprim Tunit, Ident.tmp() in
	    [[dummy], Llst.Efree v]
	in
	let start = if ISet.mem x t.is_tagged then 1 else 0 in
	let eqs = extract_args mkty tmp start l eqs in
	let eqs = ([variant_ty, snd tmp], Llst.Eid (variant_ty, snd v)) :: eqs in
	IMap.add lbl eqs acc
    | _ -> acc

  and extract_args mkty v n l eqs = 
    match l with
    | [] -> eqs
    | (ty, Pid x) :: rl -> 
	let ty = mkty ty in
	let tid = ty, x in
	let rl = extract_args mkty v (n+1) rl eqs in
	([tid], Llst.Eproj (v, n)) :: rl
    | _ -> assert false
end

open VEnv


let rec program mdl = 
  let t = VEnv.program mdl in
  let tydecls = (PredefTypes.make(), IMap.empty) in
  let types, tdecls = List.fold_left (module_decl t) tydecls mdl in
  List.rev_map (module_ t types tdecls) mdl 

and module_decl t (types, acc) md = 
  let types, decls = List.fold_left (decl t) (types, []) md.md_decls in
  let decls = List.fold_left (decl_alias t) decls md.md_decls in
  types, IMap.add md.md_id decls acc

and module_ t types ty_decls md = 
  let decls = IMap.find md.md_id ty_decls in
  let t = { t with types = types } in
  let defs = List.map (def t) md.md_defs in 
  { Llst.md_id = md.md_id ; Llst.md_decls = decls ; Llst.md_defs = defs }

and decl_alias t acc = function
  | Dalgebric td -> 
      if ISet.mem td.td_id t.is_rec
      then acc
      else Llst.Dtype (td.td_id, Llst.Tptr (Llst.Tprim Tint)) :: acc
  | _ -> acc

and decl t (types, acc) = function
  | Dalgebric td -> make_variants t (types, acc) td
  | Drecord td -> 
      let tyl = IMap.fold (fun _ (_, ty) acc -> ty :: acc) td.td_map [] in
      let tyl = List.fold_left (
	fun acc tyl -> 
	  match tyl with
	  | [] -> assert false 
	  | [x] -> type_expr x :: acc
	  | tyl -> List.rev_append (type_expr_list tyl) acc
       ) [] tyl in
      let ty = Llst.Tptr (Llst.Tstruct tyl) in
      let types = IMap.add td.td_id ty types in
      types, Llst.Dtype (td.td_id, ty) :: acc
  | Dval (ll, x, ty, v) -> 
      let ty = type_expr ty in
      IMap.add x ty types, Llst.Dval (ll, x, ty, v) :: acc

and make_variants t acc td = 
  IMap.fold (make_variant t) td.td_map acc

and make_variant t tag (_, tyl) (types, acc) =
  let tyl = type_expr_list tyl in
  if tyl = []
  then 
    let ty = Llst.Tptr (Llst.Tprim Llst.Tint) in
    let types = IMap.add tag ty types in
    let acc = Llst.Dtype (tag, ty) :: acc in
    types, acc
  else if ISet.mem tag t.is_tagged 
  then 
    let ty = Llst.Tptr (Llst.Tstruct (Llst.Tprim Llst.Tint :: tyl)) in
    let types = IMap.add tag ty types in
    let acc = Llst.Dtype (tag, ty) :: acc in
    types, acc
  else if tag = Naming.some
  then (match tyl with 
    [x] -> 
      let types = IMap.add tag x types in
      let acc = Llst.Dtype (tag, x) :: acc in
      types, acc
  | _ -> assert false)
  else 
    let ty = Llst.Tptr (Llst.Tstruct tyl) in
    let types = IMap.add tag ty types in
    let acc = Llst.Dtype (tag, ty) :: acc in
    types, acc

and type_expr_list l = List.map type_expr l
and type_expr = function
  | Tany -> Llst.Tprim Llst.Tint
  | Tprim ty -> Llst.Tprim ty 
  | Tvar _ -> Llst.Tprim Llst.Tint
  | Tid x -> Llst.Tid x
  | Tapply (x, [ty]) when x = Naming.tobs -> type_expr ty
  | Tapply (x, _) -> Llst.Tid x
  | Tfun (k, tyl1, tyl2) -> 
      let tyl1 = ftype_expr_list tyl1 in
      let tyl2 = ftype_expr_list tyl2 in
      Llst.Tfun (k, tyl1, tyl2)

and ftype_expr = function
  | Tprim Tunit -> Llst.Tprim Tunit
  | Tany | Tprim _
  | Tvar _ | Tid _
  | Tapply _ | Tfun _ -> Llst.Tprim Llst.Tint

and ftype_expr_list l = List.map ftype_expr l

and def t df = 
  let headers = ExtractArgs.def t type_expr df in
  let body = List.fold_right (block t) df.df_body [] in
  let body = List.map (add_header headers) body in
  let args = List.map (fun (ty, x) -> ftype_expr ty, x) df.df_args in
  { 
    Llst.df_id = df.df_id ;
    Llst.df_kind = df.df_kind ;
    Llst.df_args = args ;
    Llst.df_body = body ;
    Llst.df_ret = ftype_expr_list (List.map fst df.df_return) ;
  }
    
and ty_id (ty, x) = type_expr ty, x
and ty_idl l = List.map ty_id l 

and add_header hds bl = 
  let header = try IMap.find bl.Llst.bl_id hds with Not_found -> [] in
  { bl with Llst.bl_eqs = header @ bl.Llst.bl_eqs }

and block t bl acc = 
  let tail, bls, rt = ret [] t bl.bl_ret in
  { 
    Llst.bl_id = bl.bl_id ;
    Llst.bl_phi = List.map phi bl.bl_phi ;
    Llst.bl_eqs = equations t rt bl.bl_eqs tail ;
    Llst.bl_ret = rt ;
  } :: bls @ acc

and ret bls t = function
  | Lreturn _ -> assert false
  | Return (b, l) -> 
      let xl = List.map (fun (ty, x) -> ftype_expr ty, Ident.tmp()) l in
      let vl = ty_idl l in
      let tail = add_casts xl vl [] in
      tail, bls, Llst.Return (b, xl)
  | Jump lbl -> [], bls, Llst.Jump lbl
  | If (x, lbl1, lbl2) -> [], bls, Llst.If (ty_id x, lbl1, lbl2)
  | Match ([ty, x], al) ->
      let v = type_expr ty, x in
      (match al with
      | [] -> assert false	  
      | ([_, Pvariant (x, [])], lbl1) :: rl when ISet.mem x t.is_null -> 
	  let cond = Llst.Tprim Tbool, Ident.tmp() in
	  let tail = [[cond], Llst.Eis_null v] in 
	  let bls, lbl = action2 t v bls [] rl in
	  tail, bls, Llst.If (cond, lbl1, lbl) 
      | l -> action1 t v bls [] l)
  | Match _ -> assert false

and action1 t v bls acc = function
  | [[_, Pvariant (x, [])], lbl] -> 
      let tag = Llst.Tprim Tint, Ident.tmp() in
      let tail = [[tag], Llst.Eint_of_ptr (snd v)] in
      tail, bls, Llst.Switch (tag, List.rev acc, lbl)
  | ([_, Pvariant (x, [])], lbl) :: rl -> 
      let acc = (Llst.Eiint (IMap.find x t.values), lbl) :: acc in
      action1 t v bls acc rl
  | l when acc = [] -> 
      let bls, lbl = action2 t v bls [] l in
      [], bls, Llst.Jump lbl
  | l -> 
      let bls, lbl = action2 t v bls [] l in
      let tag = Llst.Tprim Tint, Ident.tmp() in
      let tail = [[tag], Llst.Eint_of_ptr (snd v)] in
      tail, bls, Llst.Switch (tag, List.rev acc, lbl)

and action2 t v bls acc = function
  | ([_, Pany], lbl) :: _ -> 
      new_switch t v bls acc lbl
  | ([_, Pvariant (x, _)], lbl) :: _ when not (ISet.mem x t.is_tagged) -> 
      new_switch t v bls acc lbl
  | [[_, Pvariant (x, _)], lbl] -> 
      new_switch t v bls acc lbl
  | ([_, Pvariant (x, _)], lbl) :: rl -> 
      let acc = (Llst.Eiint (IMap.find x t.values), lbl) :: acc in
      action2 t v bls acc rl
  | al -> List.iter (fun (p, _) -> EstPp.pat p) al ; assert false

and new_switch t v bls vl def = 
  if vl = []
  then bls, def
  else 
  let tag = Llst.Tprim Tint, Ident.tmp() in
  let lbl = Ident.tmp() in
  let rt = Llst.Switch (tag, List.rev vl, def) in 
  let eqs = [[tag], Llst.Egettag v] in
  { Llst.bl_id = lbl ;
    Llst.bl_phi = [] ;
    Llst.bl_eqs = eqs ;
    Llst.bl_ret =  rt ;
   } :: bls, lbl

and phi (x, ty, l) = x, type_expr ty, l

and equations t ret l acc = 
  match l with
  | [] -> acc
  | [e] -> equation t true ret e acc
  | e :: rl -> 
      let acc = equations t ret rl acc in
      equation t false ret e acc

and equation t is_last ret (idl, e) acc = 
  let idl = ty_idl idl in
  match e with
  | Evariant (x, []) -> 
      if ISet.mem x t.is_null
      then (idl, Llst.Enull) :: acc
      else 
	let v = Llst.Evalue (Llst.Eiint (IMap.find x t.values)) in
	let id = Ident.tmp() in
	let acc = (idl, Llst.Eptr_of_int id) :: acc in 
	let acc = ([Llst.Tprim Tint, id] , v) :: acc in 
	acc
  | Evariant (x, vl) -> 
      if ISet.mem x t.is_tagged
      then 
	let vl = ty_idl vl in
	let xl = match IMap.find x t.types with 
	| Llst.Tptr (Llst.Tstruct tyl) -> 
	    List.map (fun ty -> ty, Ident.tmp()) (List.tl tyl)
	| _ -> assert false in
	let ty = Llst.Tid x in 
	let tag = Llst.Tprim Tint, Ident.tmp() in
	let vid = Ident.tmp() in
	let v = Llst.Etuple (None, tuple 0 (tag :: xl)) in
	let acc = (idl, Llst.Eid (fst (List.hd idl), vid)) :: acc in
	let acc = ([ty, vid], v) :: acc in
	let tag_value = Llst.Evalue (Llst.Eiint (IMap.find x t.values)) in
	let acc = ([tag], tag_value) :: acc in
	let acc = add_casts xl vl acc in
	acc
      else if x = Naming.some
      then 
	let v = ty_id (List.hd vl) in
	(idl, Llst.Eid (Llst.Tid Naming.toption, snd v)) :: acc
      else 
	let vl = ty_idl vl in
	let xl = match IMap.find x t.types with 
	| Llst.Tptr (Llst.Tstruct tyl) -> 
	    List.map (fun ty -> ty, Ident.tmp()) tyl 
	| _ -> assert false in
	let vid = Ident.tmp() in
	let ty = Llst.Tid x in 
	let tyv = ty, vid in
	let fdl = tuple 0 xl in
	let v = Llst.Etuple (None, fdl) in
	let acc = (idl, Llst.Eid (fst (List.hd idl), vid)) :: acc in
	let acc = ([tyv], v) :: acc in
	let acc = add_casts xl vl acc in
	acc
  | Eapply (fk, (ty, x), vl) ->
      let argl = List.map (fun (ty, x) -> ftype_expr ty, Ident.tmp()) vl in 
      let argl' = ty_idl vl in
      let rty = get_rty ty in
      let acc = 
	let acc, xl = 
	  match ret with
	  | Llst.Return (true, _) -> acc, idl
	  | _ -> 
	      let xl = List.map (fun ty -> ty, Ident.tmp()) (ftype_expr_list rty) in
	      let acc = add_casts idl xl acc in
	      acc, xl
	in
	let fid = type_expr ty, x in
	let acc = (xl, Llst.Eapply (fk, false, fid, argl)) :: acc in
	acc
      in
      let acc = add_casts argl argl' acc in
      acc
  | Efield (v, y) -> 
      let v = ty_id v in
      let n = ref (IMap.find y t.values) in
      List.fold_left (
      fun acc x -> 
	let res = [x], Llst.Eproj (v, !n) in
	incr n ;
	res :: acc
     ) acc idl 
  | e -> (idl, expr t idl e) :: acc

and tuple n vl = 
  match vl with
  | [] -> []
  | x :: rl -> (n, x) :: tuple (n+1) rl

and get_rty = function
  | Tfun (_, _, x) -> x 
  | _ -> assert false

and add_casts idl1 idl2 acc = 
  List.fold_right2 (
  fun x y acc -> 
    match fst y with
    | Llst.Tprim Llst.Tunit as u -> ([u, snd x], Llst.Eid y) :: acc
    | _ -> ([x], Llst.Eid y) :: acc
 ) idl1 idl2 acc

and expr t idl = function
  | Enull -> Llst.Enull 
  | Eid (xty, x) -> Llst.Eid (type_expr xty, x)
  | Evalue x -> Llst.Evalue (value x)
  | Euop (uop, x) -> Llst.Euop (uop, ty_id x) 
  | Ebinop (bop, x1, x2) -> Llst.Ebinop (bop, ty_id x1, ty_id x2)
  | Efield _ -> assert false
  | Ecall _ -> assert false
  | Eif _ -> assert false
  | Ematch _ -> assert false
  | Erecord fdl -> Llst.Etuple (None, fields t fdl)
  | Ewith ((ty, x), fdl) -> 
      let ty = type_expr ty in
      Llst.Etuple (Some (ty, x), fields t fdl)
  | Eis_null x -> Llst.Eis_null (ty_id x)
  | Efree x -> Llst.Efree (ty_id x)
  | Eseq _ -> assert false
  | Evariant _ -> assert false
  | Eapply _ -> assert false
  | Eget (a, i) -> Llst.Eget (ty_id a, ty_id i)
  | Eset (a, i, v) -> Llst.Eset (ty_id a, ty_id i, ty_id v)
  | Eswap (a, i, v) -> Llst.Eswap (ty_id a, ty_id i, ty_id v)

and fields t fdl = 
  let tag x = IMap.find x t.values in
  let fdl = List.map (fun (x, y) -> tag x, ty_idl y) fdl in
  let fdl = List.fold_left (fun acc (n, l) -> tuple n l @ acc) [] fdl in
  fdl

and value = function
  | Eunit -> Llst.Eunit
  | Ebool x -> Llst.Ebool x
  | Eint x -> Llst.Eint x
  | Efloat x -> Llst.Efloat x
  | Echar x -> Llst.Echar x
  | Estring x -> Llst.Estring x
