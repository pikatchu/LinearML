open Utils
open Nast

module Abbrev: sig

  val check: Nast.program -> unit

end = struct

  let rec program mdl = 
    List.iter module_ mdl

  and module_ md = 
    let env = List.fold_left decl IMap.empty md.md_decls in
    IMap.iter (check_decl env) env

  and decl env = function
    | Dtype tyl -> List.fold_left type_def env tyl
    | Dval _ -> env

  and type_def env ((x,_), ty) = 
    let pos, id = x in
    match ty with
    | _, Tabbrev ty -> IMap.add id (pos, snd ty) env
    | _ -> env

  and check_decl env id (p, ty) = 
    abbrev env IMap.empty [] (p, id)
	
  and type_expr env set path (_, ty) = type_expr_ env set path ty
  and type_expr_ env set path ty = 
    let k = type_expr env set path in
    let kl = List.iter k in
    match ty with
    | Tunit | Tbool
    | Tint32 | Tfloat | Tvar _ 
    | Tpath _ -> ()
    | Tid x -> tid env set path x
    | Tapply (ty, tyl) -> k ty ; kl tyl
    | Ttuple tyl -> kl tyl
    | Tfun (ty1, ty2) -> k ty1 ; k ty2
    | Talgebric vl -> List.iter (variant k) vl
    | Trecord fl -> kl (List.map snd fl)
    | Tabbrev ty -> k ty

  and variant k (_, ty_opt) =
    match ty_opt with
    | None -> ()
    | Some x -> k x

  and tid env set path ((_, x) as id) = 
    if IMap.mem x set 
    then Error.cyclic_abbrev (List.rev path)
    else if IMap.mem x env
    then abbrev env set path id
    else ()

  and abbrev env set path ((p, x) as id) = 
    let set = IMap.add x p set in
    let path = id :: path in
    let p, _ as ty = IMap.find x env in
    let path = (p, x) :: path in
    type_expr env set path ty

  let check = program

end

module ModuleTypeDep: sig
  
  val program: Nast.program -> (Pos.t * id list IMap.t) IMap.t

end = struct

  let add x y t = 
    let l = try IMap.find x t with _ -> [] in
    IMap.add x (y :: l) t

  let rec program mdl = 
    List.fold_left module_ IMap.empty mdl

  and module_ genv md = 
    let env = List.fold_left decl IMap.empty md.md_decls in
    let p, id = md.md_id in
    IMap.add id (p, env) genv

  and decl env = function
    | Dtype tdl -> List.fold_left type_def env tdl
    | Dval _ -> env

  and type_def env ((_, _), ty) = type_expr env ty

  and type_expr env (_, ty) = type_expr_ env ty
  and type_expr_ env = function
    | Tunit | Tbool | Tint32
    | Tfloat | Tvar _
    | Tid _ -> env
    | Tapply (ty, tyl) -> 
	let env = List.fold_left type_expr env tyl in
	type_expr env ty

    | Ttuple tyl -> List.fold_left type_expr env tyl
    | Tpath ((_,x), y) -> add x y env 
    | Tfun (ty1, ty2) -> 
	let env = type_expr env ty1 in
	type_expr env ty2 

    | Talgebric vl -> List.fold_left variant env vl 
    | Trecord fl -> List.fold_left field env fl 
    | Tabbrev ty -> type_expr env ty

  and variant env (_, ty_opt) = 
    match ty_opt with
    | None -> env
    | Some ty -> type_expr env ty

  and field env (_, ty) =
    type_expr env ty
  
end

module ModuleTypeDepCheck: sig

end = struct

  let rec check deps = 
    let env = IMap.fold type_ deps IMap.empty in
    env

  and type_ x (p, env) acc = 
    IMap.fold IMap.add env acc
    
end



let program p = 
  Abbrev.check p
