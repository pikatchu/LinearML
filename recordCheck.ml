open Utils
open Stast

type ty = ty_ list
and ty_ =
  | P
  | A
  | Rid of Ident.t
  | R of (field * ty) IMap.t

and field = 
  | Read
  | Write of Pos.t

module Debug = struct

  let rec ty l = List.iter ty_ l
  and ty_ = function
    | P -> o "P" 
    | A -> o "A"
    | Rid x -> o "Rid" 
    | R fdl -> o "{" ; IMap.iter field fdl ; o "}" 

  and field fd (k, v) =
    o (Ident.to_string fd) ; 
    field_kind k ;
    o ": " ;
    ty v ;
    o "; "

  and field_kind = function
    | Read -> o "[R]"
    | Write _ -> o "[W]" 

end

let get_record_type x t = 
  try match IMap.find x t with
  | [x] -> x
  | _ -> assert false
  with Not_found -> A

let rec is_pointer l = 
  let c = List.fold_left (fun acc x -> x = P && acc) true l in
  not c

let rec assign pos t ty1 ty2 = List.map2 (assign_ pos t) ty1 ty2
and assign_ pos t ty1 ty2 = 
  match ty1, ty2 with
  | Rid x, _ -> assign_ pos t (get_record_type x t) ty2
  | _, Rid x -> assign_ pos t ty1 (get_record_type x t)
  | R m1, R m2 -> 
      R (IMap.fold (assign_map pos m2) m1 m1)
  | _ -> assert false

and assign_map pos m2 x (a1, _) m = try
  let a2, t as t2 = IMap.find x m2 in
  match a1, a2 with
  | Read _, Read _ when is_pointer t -> Error.fd_already_has_value pos x
  | _, Write _ -> assert false
  | _-> IMap.add x t2 m
with Not_found -> m
    
module Unify = struct

  exception Error of Ident.t

  let rec unify tyl1 tyl2 = List.map2 unify_ tyl1 tyl2
  and unify_ ty1 ty2 = 
    match ty1, ty2 with
    | P, P -> P
    | P, t | t, P -> t
    | A, _ | _, A -> A
    | Rid _ as ty, _
    | _, (Rid _ as ty) -> ty
    | R m1, R m2 -> R (iimap2 unify_fields m1 m2)

  and unify_fields x (a1, ty1) (a2, ty2) = 
    unify_access x a1 a2 ;
    a1, unify ty1 ty2

  and unify_access x a1 a2 = 
    match a1, a2 with
    | Read _, Read _ -> ()
    | Write p, Read _
    | Read _, Write p -> raise (Error x)
    | Write _, Write _ -> ()

  let rec unify_types (p1, tyl1) (p2, tyl2) = 
    try p1, unify tyl1 tyl2
    with Error x -> Error.field_defined_both_sides p1 p2 x

end

let rec check_type pos tyl = List.iter (check_type_ pos) tyl 
and check_type_ pos = function
  | A
  | P
  | Rid _ -> ()
  | R m -> IMap.iter (check_field pos) m 

and check_field pos x (a, ty) = 
  check_type pos ty ;
  match a with
  | Read _ -> ()
  | Write p -> Error.missing_field pos x

let rec type_expr_list (_, tyl) = List.map type_expr tyl
and type_expr (_, ty) = type_expr_ ty
and type_expr_ = function
  | Tprim _ -> P
  | Tany 
  | Tvar _ | Tfun _ -> A
  | Tapply ((_, x), (_, [ty])) when x = Naming.tobs -> type_expr ty
  | Tid (_, x)
  | Tapply ((_, x), _) -> Rid x

let read_only pos = function
  | Read _ -> ()
  | Write _ -> Error.field_no_val pos

let free_field t pos v (x, ty) = 
  if ty = [P]
  then ()
  else match x with
  | Read -> Error.cannot_free_field pos v
  | _ -> ()

let rec free_ty t pos = function
  | P
  | A -> ()
  | Rid x -> free_ty t pos (get_record_type x t)
  | R m -> IMap.iter (free_field t pos) m 

let free t pos l = List.iter (free_ty t pos) l


module Env: sig

  val make: program -> ty IMap.t
end = struct

  let rec make mdl = 
    List.fold_left module_ IMap.empty mdl

  and module_ t md = 
    List.fold_left decl t md.md_decls
  
  and decl t = function
    | Dalgebric _ -> t
    | Drecord td -> tdef t td
    | Dval _ -> t

  and tdef t td = 
    let m = IMap.map (
      fun (_, ty) -> Read, type_expr_list ty
     ) td.td_map in
    IMap.add (snd td.td_id) [R m] t

end

let rec program mdl = 
  let t = Env.make mdl in
  List.iter (module_ t) mdl

and module_ t md = 
  List.iter (def t) md.md_defs 

and def t (x, ((tyl, _) as p), e) = 
  let tyl = type_expr_list tyl in
  let t = pat t p tyl in
  check_type (fst (fst e)) (tuple t e)

and pat t (_, ptl) tl = List.fold_left (pat_tuple tl) t ptl
and pat_tuple tl t (_, pel) = List.fold_left2 pat_el t pel tl
and pat_el t (_, p) ty = pat_ t p ty
and pat_ t p ty = 
  match p with
  | Pvalue _
  | Pany -> t
  | Pid (_, x) -> IMap.add x [ty] t
  | Pvariant (_, ((tyl, _) as p)) -> pat t p (type_expr_list tyl)
  | Precord pfl -> pat_record t pfl ty
  | Pas ((_, x), p) -> 
      let t = IMap.add x [ty] t in
      pat t p [ty]

and pat_record t pfl = function
  | A
  | P -> assert false
  | R m -> 
      let t, m = List.fold_left pat_field (t, m) pfl in
      let t = List.fold_left (pat_rest m) t pfl in
      t
  | Rid x -> pat_record t pfl (get_record_type x t)

and pat_rest m t (_, pf) = 
  match pf with
  | PFany -> t
  | PFid (_, x) -> IMap.add x [R m] t
  | _ -> t

and pat_field tm (_, pf) = pat_field_ tm pf
and pat_field_ (t, m) pf = 
  match pf with
  | PFany 
  | PFid _ -> t, m
  | PField ((pos, x), p) ->
      let a, ty = IMap.find x m in
      read_only pos a ;
      let t = pat t p ty in
      let t = IMap.add x ty t in
      let m = 
	if is_pointer ty 
	then IMap.add x (Write pos, ty) m 
	else m in
      t, m

and tuple t (_, tpl) = 
  List.fold_right (fun e acc ->
    tuple_pos t e @ acc) tpl []

and tuple_pos t ((p, tyl), e) = expr_ t p tyl e
and expr t ((p, _) as ty, e) = expr_ t p [ty] e 
and expr_ t pos ty = function
  | Eobs (_, x)
  | Eid (_, x) -> 
      (try IMap.find x t with Not_found -> type_expr_list (pos, ty))
  | Evalue _ 
  | Ebinop _
  | Euop _ -> [P]
  | Evariant _ -> List.map type_expr ty
  | Ematch (e, al) -> 
      let pl = List.map (fun (_, ((p, _), _)) -> p) al in
      let ty = tuple t e in
      let tyl = List.map (action t ty) al in
      let tyl = List.map2 (fun x y -> (x, y)) pl tyl in
      snd (List.fold_left Unify.unify_types (List.hd tyl) (List.tl tyl))
  | Elet (p, e1, e2) -> 
      let ty1 = tuple t e1 in
      let t = pat t p ty1 in
      tuple t e2
  | Eif (_, e1, e2) -> 
      let e1 = fst (fst e1), tuple t e1 in
      let e2 = fst (fst e2), tuple t e2 in
      snd (Unify.unify_types e1 e2)
  | Eapply (_, (_, v), e) when v = Naming.free ->
      let ty = tuple t e in
      free t (fst (fst e)) ty ;
      [P]
  | Eapply (_, _, e) -> 
      check_type pos (tuple t e) ;
      List.map type_expr ty 
  | Efield (e, (p, x)) -> 
      let ty = expr t e in
      proj t p ty x
  | Erecord fdl -> 
    let m = List.fold_left (field t) IMap.empty fdl in
    let ty = List.map type_expr ty in
    let fdm = get_fields t ty in
    [R (add_write_only pos fdm m)]
  | Ewith (e, fdl) -> 
      let ty1 = expr t e in
      let m = List.fold_left (field t) IMap.empty fdl in
      let ty2 = [R m] in
      assign pos t ty1 ty2
  | Eseq (e1, e2) -> 
      ignore (expr t e1) ;
      tuple t e2

and field t m ((_, x), e) = 
  IMap.add x (Read, tuple t e) m

and get_fields t ty = 
  match ty with 
  | [Rid x] -> (match get_record_type x t with
    | R m -> m
    | _ -> assert false)
  | [R m] -> m
  | _ -> assert false

and add_write_only pos fdm m = 
  IMap.fold (fun x (_, ty) m ->
    if IMap.mem x m
    then m
    else IMap.add x (Write pos, ty) m) fdm m

and action t ty (p, e) =
  let t = pat t p ty in
  tuple t e

and proj t p ty x =
  match ty with
  | [Rid y] -> proj t p (IMap.find y t) x
  | [R m] -> 
      let a, ty = IMap.find x m in
      read_only p a ;
      ty
  | _ -> assert false
