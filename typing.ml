open Utils
open Nast

module Debug = struct
  open Tast

  let id o (_, x) = o (Ident.debug x)

  let rec type_expr o (_, ty) = type_expr_ o ty
  and type_expr_ o ty = 
    let k = type_expr o in
    match ty with
    | Tany -> o "Tany"
    | Tunit -> o "Tunit"
    | Tbool -> o "Tbool"
    | Tint32 -> o "Tint32"
    | Tfloat -> o "Tfloat"
    | Tvar x -> o "Tvar" ; o "(" ;  id o x ; o ")"
    | Tid x -> o "Tid" ; o "(" ;  id o x ; o ")"
    | Tapply (ty, tyl) -> o "Tapply" ; o "(" ;  k ty ; o "," ; list o tyl; o ")"
    | Tpath (id1, id2) -> o "Tpath" ; o "(" ; id o id1 ; o "." ; id o id2 ; o ")"
    | Tfun (ty1, ty2) -> o "Tfun" ; o "(" ;  list o ty1 ; o "->" ; list o ty2; o ")"
    | Talgebric vl -> o "Talgebric" ; o "[" ; imiter (variant o) vl ; o "]"
    | Trecord fdl -> o "Trecord" ; o "{" ;  imiter (field o) fdl; o "}"
    | Tabs (idl, ty) -> o "Tabs" ; o "(" ; tvar o idl ; o ": " ; k ty; o ")"
    | Tdecl x -> o "Tdecl" ; o "(" ; id o x ; o ")"

  and tvar o = function
    | [] -> assert false
    | [x] -> id o x
    | x :: rl -> id o x ; o "," ; tvar o rl

  and list o = function
    | [] -> ()
    | [x] -> type_expr o x
    | x :: rl -> type_expr o x ; o "," ; list o rl

  and variant o (x, y) = 
    id o x ; o " of " ; 
    list o y ;
    o "|"

  and field o (x, y) = id o x ; o ":" ; list o y ; o ";"

  let o = output_string stdout
  let nl o = o "\n"
  let type_expr ty = type_expr o ty ; nl o

  let rec pat o (_, p) = pat_ o p
  and pat_ o = function
  | Punit -> o "Punit"
  | Pany -> o "Pany"
  | Pid _ -> o "Pid" 
  | Pchar _ -> o "Pchar" 
  | Pint _ -> o "Pint" 
  | Pbool _ -> o "Pbool" 
  | Pfloat _ -> o "Pfloat" 
  | Pstring _ -> o "Pstring" 
  | Pcstr _ -> o "Pcstr" 
  | Pvariant _ -> o "Pvariant" 
  | Pecstr _ -> o "Pecstr" 
  | Pevariant _ -> o "Pevariant" 
  | Precord _ -> o "Precord" 
  | Pbar _ -> o "Pbar" 
  | Ptuple _ ->  o "Ptuple"

  let pat p = pat o p ; nl o

end

module NDebug = struct

  let o = output_string stdout
  let nl o = o "\n"

  let rec pat o p = pat_ o p
  and pat_ o = function
  | Punit -> o "Punit"
  | Pany -> o "Pany"
  | Pid _ -> o "Pid" 
  | Pchar _ -> o "Pchar" 
  | Pint _ -> o "Pint" 
  | Pbool _ -> o "Pbool" 
  | Pfloat _ -> o "Pfloat" 
  | Pstring _ -> o "Pstring" 
  | Pcstr _ -> o "Pcstr" 
  | Pvariant _ -> o "Pvariant" 
  | Pecstr _ -> o "Pecstr" 
  | Pevariant _ -> o "Pevariant" 
  | Precord _ -> o "Precord" 
  | Pbar _ -> o "Pbar" 
  | Ptuple _ ->  o "Ptuple"

  let pat p = pat o p ; nl o

end





(*let rec instantiate (p, ty) = 
  p, match ty with
  | Tabs (vl, ty) -> 
      let id (p, x) = p, Ident.make (Ident.to_string x) in
      let nvl = List.map id vl in
      let bind (_, x) ((p, _) as y) acc = IMap.add x (p, Tvar y) acc in
      let subst = List.fold_right2 bind vl nvl IMap.empty in
      Tabs (nvl, Subst.type_expr subst ty)
  | _ -> ty *)

module Unify = struct
  open Tast

  let rec type_expr (p1, ty1) (p2, ty2) = 
    p1, match ty1, ty2 with
    | Tunit, Tunit -> Tunit
    | Tbool, Tbool -> Tbool
    | Tint32, Tint32 -> Tint32
    | Tfloat, Tfloat -> Tfloat
    | Tvar (_, x1), Tvar (_, x2) when x1 = x2 -> ty1
    | Tpath (_, (_, x1)), Tpath (_, (_, x2))
    | Tid (_, x1), Tid (_, x2) when x1 = x2 -> ty1
    | Tapply (ty1, tyl1), Tapply (ty2, tyl2) -> 
	(* TODO check arity ? *)
	let ty = type_expr ty1 ty2 in
	let tyl = type_expr_list tyl1 tyl2 in
	Tapply (ty, tyl)

    | Tfun (targ1, tret1), Tfun (targ2, tret2) -> 
	let targ = type_expr_list targ1 targ2 in
	let tret = type_expr_list tret1 tret2 in
	Tfun (targ, tret)

    | Tabs (vl1, ty1), Tabs (vl2, ty2) -> 
	let ty = type_expr ty1 ty2 in
	let vl = type_id_list vl1 vl2 in
	Tabs (vl, ty)

    | Talgebric vl1, Talgebric vl2 -> 
	let vl = IMap.fold (variant vl2) vl1 vl2 in
	Talgebric vl

    | Trecord fdl1, Trecord fdl2 ->
	(* TODO make sure they have the same fields defined *)
	let fdl = IMap.fold field fdl1 fdl2 in
	Trecord fdl

    | _ -> 
	Debug.type_expr (p1, ty1) ;
	Debug.type_expr (p2, ty2) ;
	Error.unify p1 p2

  and variant vm x (cstr1, ty1) acc =
    try 
      let cstr2, ty2 = IMap.find x vm in
      assert (snd cstr1 = snd cstr2) ;
      let ty = type_expr_list ty1 ty2 in
      IMap.add x (cstr1, ty) acc
    with 
    | Not_found -> IMap.add x (cstr1, ty1) acc

  and field x (fd1, ty1) acc = 
    try 
      let fd2, ty2 = IMap.find x acc in
      let ty = type_expr_list ty1 ty2 in
      IMap.add x (fd1, ty) acc
    with 
    | Not_found -> assert false

  and type_expr_list tyl1 tyl2 = 
    match tyl1, tyl2 with
    | [], [] -> []
    | [], _ | _, [] -> 
	(* Tuples and abbreviations have been expanded *)
	(* In case of application arity is checked before unification *)
	assert false
    | x1 :: rl1, x2 :: rl2 -> type_expr x1 x2 :: type_expr_list rl1 rl2

  and type_id_list tyl1 tyl2 = 
    match tyl1, tyl2 with
    | [], [] -> []
    | [], _ | _, [] -> assert false
    | (p1, x1) :: rl1, (p2, x2) :: rl2 ->
	if x1 <> x2 
	then Error.unify p1 p2
	else type_id_list rl1 rl2
end

module CompareType = struct
  open Tast

  type t = Nast.id * type_expr list

  let (&&&) x1 x2 = 
    let c = x1 () in
    if c = 0
    then x2 ()
    else c

  let rec list cmp l1 l2 () = 
    match l1, l2 with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | x1 :: rl1, x2 :: rl2 -> 
	cmp x1 x2 &&& list cmp rl1 rl2

  let rec compare (id1, ty1) (id2, ty2) = 
    id id1 id2 &&& 
    list ty ty1 ty2

  and id (_, x1) (_, x2) () = 
    Ident.compare x1 x2

  and ty (_, ty1) (_, ty2) () = 
    match ty1, ty2 with
  | Tany, Tany -> 0
  | Tunit, Tunit -> 0
  | Tbool, Tbool -> 0
  | Tint32, Tint32 -> 0
  | Tfloat, Tfloat -> 0
  | Tpath (_, x1), Tpath (_, x2)
  | Tid x1, Tid x2
  | Tdecl x1, Tdecl x2
  | Tvar x1, Tvar x2 -> id x1 x2 ()
  | Tapply (ty1, tyl1), Tapply (ty2, tyl2) -> 
      ty ty1 ty2 &&&
      list ty tyl1 tyl2

  | Tfun (ty1, ty2), Tfun (ty3, ty4) ->
      list ty ty1 ty3 &&&
      list ty ty2 ty4

  | Talgebric vm1, Talgebric vm2 -> 
      let vl1 = list_of_imap vm1 in
      let vl2 = list_of_imap vm2 in
      list variant vl1 vl2 ()

  | Trecord vm1, Trecord vm2 -> 
      let vl1 = list_of_imap vm1 in
      let vl2 = list_of_imap vm2 in
      list field vl1 vl2 ()

  | Tabs (idl1, ty1), Tabs (idl2, ty2) -> 
      list id idl1 idl2 &&&
      ty ty1 ty2

  | _, _ -> Pervasives.compare ty1 ty2

  and variant (id1, ty1) (id2, ty2) () =
    id id1 id2 &&&
    list ty ty1 ty2

  and field (id1, ty1) (id2, ty2) () = 
    id id1 id2 &&&
    list ty ty1 ty2
    
end

module Env = struct
  open Nast

  let get_type env (p, x) = snd (IMap.find x env)
  let add_type env (_, x) ty = IMap.add x ty env

(*  let rec make mdl = 
    List.fold_left module_ IMap.empty mdl

  and module_ env md = 
    let env = List.fold_left decl env md.md_decls in
    List.fold_left def env md.md_defs 

  and decl env = function
    | Dtype tdl -> List.fold_left tdef env tdl 
    | Dval (x, ty) -> IMap.add x (type_expr ty) env 

  and type_expr (p, ty) = 
    p, type_expr_ ty

  and type_expr_ = function
    | Tunit -> Tast.Tunit
    | Tbool -> Tast.Tbool
    | Tint32 -> Tast.Tint32
    | Tfloat -> Tast.Tfloat
    | Tvar x -> Tast.Tvar x
    | Tid x -> Tast.Tid x

    | Tapply (ty, tyl) -> 
	Tast.Tapply (type_expr ty, List.map type_expr tyl) 

    | Ttuple _ -> assert false 
    | Tpath (x, y) -> Tast.Tpath (x, y) 
    | Tfun (ty1, ty2) -> Tast.Tfun (type_expr ty1, type_expr ty2)
    | Talgebric vm -> Tast.Talgebric (IMap.fold variant vm IMap.empty)
    | Trecord vm -> Tast.Trecord (IMap.fold field vm IMap.empty)
    | Tabbrev _ -> assert false
    | Tabs (idl, ty) -> Tast.Tabs (idl, type_expr ty) *)

end

module Types: sig

  type t = Tast.type_expr IMap.t

  val make: Nast.program -> t
  val fun_: Tast.type_expr -> Tast.type_expr list * Tast.type_expr list

end = struct

  type t = Tast.type_expr IMap.t

  open Nast

  let rec make mdl = 
    List.fold_left module_ IMap.empty mdl

  and module_ env md = 
    List.fold_left decl env md.md_decls

  and decl env = function
    | Dtype tdl -> List.fold_left tdef env tdl
    | Dval ((_, x), ty) -> IMap.add x (type_expr ty) env

  and tdef env ((_, x), ty) =
    IMap.add x (type_expr ty) env

  and type_expr (p, ty) = 
    p, type_expr_ ty

  and type_expr_ = function
    | Tunit -> Tast.Tunit
    | Tbool -> Tast.Tbool
    | Tint32 -> Tast.Tint32
    | Tfloat -> Tast.Tfloat
    | Tvar x -> Tast.Tvar x
    | Tid x -> Tast.Tid x
    | Tpath (x, y) -> Tast.Tpath (x, y)
    | Tapply (ty, tyl) -> Tast.Tapply (type_expr ty, type_expr_list tyl)
    | Tfun (ty1, ty2) -> Tast.Tfun (tuple ty1, tuple ty2)
    | Talgebric vl -> Tast.Talgebric (IMap.map variant vl)
    | Trecord fdl -> Tast.Trecord (IMap.map field fdl)
    | Tabs (idl, ty) -> Tast.Tabs (idl, type_expr ty)
    | Tabbrev _ -> assert false
    | Ttuple _ -> assert false
	  
  and variant (x, ty_opt) = 
    match ty_opt with
    | None -> x, []
    | Some ty -> x, tuple ty
	  
  and field (x, ty) = x, tuple ty

  and tuple ((_, ty_) as ty) = 
    match ty_ with
    | Ttuple l -> List.map type_expr l
    | _ -> [type_expr ty]

  and type_expr_list l = List.map type_expr l

  let fun_ (_, ty) = 
    match ty with
    | Tast.Tfun (tyl1, tyl2) -> tyl1, tyl2
    | _ -> failwith "TODO was expecting function type"
end

module Defs: sig

  type t = Nast.id * Nast.pat list * Nast.expr

  val module_: Types.t -> Nast.module_ -> t IMap.t * Types.t

end = struct

  type t = Nast.id * Nast.pat list * Nast.expr

  let rec module_ types md = 
    let defs = List.fold_left def IMap.empty md.md_defs in
    let types = IMap.fold def_type defs types in
    defs, types
	  
  and def acc (((_, x), _, _) as b) = 
    IMap.add x b acc

  and def_type x (y, _, _) types = 
    IMap.add x (fst y, Tast.Tdecl y) types
end

module TMap = Map.Make (CompareType)

let program _ = ()
