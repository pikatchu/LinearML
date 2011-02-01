open Utils
open Llst

(* Determines all the unit types *)
module UnitTypes = struct
  
  let rec program mdl = 
    let decls = List.fold_left module_ IMap.empty mdl in
    let t = ref IMap.empty in
    IMap.iter (fun x _ -> ignore (type_expr_id decls t x)) decls ;
    IMap.fold (
    fun x ty acc -> 
      match ty with
      | Tprim Tunit -> ISet.add x acc
      | _ -> acc
   ) !t ISet.empty

  and module_ t md = 
    List.fold_left add_decl t md.md_decls

  and add_decl acc = function
    | Dtype (x, ty) -> IMap.add x ty acc
    | _ -> acc

  and type_expr_id decls t x = 
    try IMap.find x !t
    with Not_found ->
      let ty = IMap.find x decls in
      let decls = IMap.remove x decls in
      let ty = type_expr decls t ty in
      t := IMap.add x ty !t ;
      ty

  and type_expr decls t = function
    | Tany 
    | Tprim _ as x -> x
    | Tid x as y -> 
	(try type_expr_id decls t x
	with Not_found -> y)
    | Tfun (k, tyl1, tyl2) -> 
	let tyl1 = type_expr_list decls t tyl1 in
	let tyl2 = type_expr_list decls t tyl2 in
	Tfun (k, tyl1, tyl2)
    | Tstruct tyl -> 
	let tyl = type_expr_list decls t tyl in
	if tyl = []
	then Tprim Tunit
	else Tstruct tyl
    | Tptr ty -> 
	let ty = type_expr decls t ty in
	if ty = Tprim Tunit
	then ty
	else Tptr ty
	    
  and type_expr_list decls t l =
    let l = List.map (type_expr decls t) l in
    List.filter (function Tprim Tunit -> false | _ -> true) l

end

let rec program mdl = 
  let t = UnitTypes.program mdl in
  List.map (module_ t) mdl

and module_ t md = 
  { md with 
    md_decls = List.fold_right (decl t) md.md_decls [] ;
    md_defs = List.map (def t) md.md_defs ;
  }

and decl t de acc = 
  match de with
  | Dtype (x, ty) -> 
      let ty = type_expr t ty in
      if ty = Tprim Tunit
      then acc 
      else (Dtype (x, type_expr t ty)) :: acc
  | Dval (ll, x, ty, ext) -> 
      Dval (ll, x, type_expr t ty, ext) :: acc

and type_expr t = function
  | Tany 
  | Tprim _ as x -> x
  | Tid x when ISet.mem x t -> Tprim Tunit
  | Tid _ as x -> x
  | Tfun (k, tyl1, tyl2) -> 
      let tyl1 = type_expr_list t tyl1 in
      let tyl2 = type_expr_list t tyl2 in
      Tfun (k, tyl1, tyl2)
  | Tstruct tyl -> 
      let tyl = type_expr_list t tyl in
      if tyl = []
      then Tprim Tunit
      else Tstruct tyl
  | Tptr ty -> 
      let ty = type_expr t ty in
      if ty = Tprim Tunit
      then ty
      else Tptr ty
	  
and type_expr_list t l =
  let l = List.map (type_expr t) l in
  List.filter (function Tprim Tunit -> false | _ -> true) l

and ty_id t (ty, x) = 
  let ty = type_expr t ty in
  ty, x

and ty_idl t l = 
  let l = List.map (ty_id t) l in
  List.filter (
  function 
    | (Tprim Tunit, _) -> false
    | _ -> true
 ) l

and def t df = 
  { df with
    df_args = ty_idl t df.df_args ;
    df_body = List.map (block t) df.df_body ;
    df_ret = type_expr_list t df.df_ret ;
  }

and block t bl = 
  let phil = List.filter (
    function (_, Tprim Tunit, _) -> false | _ -> true
   ) bl.bl_phi in
  { bl with
    bl_phi = phil ;
    bl_eqs = List.fold_right (equation t) bl.bl_eqs [] ;
    bl_ret = ret t bl.bl_ret ;
  }

and ret t = function   
  | Return (b, xl) -> Return (b, ty_idl t xl)
  | Jump _ 
  | If _
  | Switch _ as x -> x (* TODO unit case ? *)

and equation t (xl, e) acc = 
  let xl = ty_idl t xl in
  let e = expr t e in
  if xl = []
  then match e with
  | Eapply _ | Efree _ -> (xl, e) :: acc
  | _ -> acc
  else (xl, e) :: acc

and expr t = function
  | Enull -> Enull
  | Eid x -> Eid (ty_id t x)
  | Evalue _ as x -> x
  | Ebinop (bop, x1, x2) -> Ebinop (bop, ty_id t x1, ty_id t x2)
  | Euop (uop, x) -> Euop (uop, ty_id t x)
  | Efield (x, n) -> Efield (ty_id t x, n)
  | Eapply (k, b, x, xl) -> Eapply (k, b, x, ty_idl t xl)
  | Etuple (xopt, fdl) -> 
      let fdl = List.fold_right (field t) fdl [] in
      Etuple (opt (ty_id t) xopt, fdl)
  | Egettag x -> Egettag (ty_id t x)
  | Eproj (x, n) -> Eproj (ty_id t x, n)
  | Eptr_of_int _
  | Eint_of_ptr _ as x -> x
  | Eis_null x -> Eis_null (ty_id t x)
  | Efree x -> Efree (ty_id t x)

and field t (n, x) acc = 
  let x = ty_id t x in
  match fst x with
  | Tprim Tunit -> acc
  | _ -> (n, x) :: acc

