open Utils
open Nast

module Expand = struct

  type id = Pos.t * Ident.t
  type pstring = Pos.t * string

  let rec program p = 
    let abbr = NastCheck.Abbrev.check p in
    let abbr = IMap.fold (fun _ x acc -> IMap.fold IMap.add x acc) abbr IMap.empty in
    lfold (module_ abbr) IMap.empty p

  and module_ abbr mem md = 
    let mem, decls = lfold (decl abbr) mem md.md_decls in
    mem, { md with md_decls = decls }

  and decl abbr mem = function
    | Dtype tdl -> 
	let mem, tdl = List.fold_left (type_def abbr) (mem, []) tdl in
	mem, Dtype tdl 
    | x -> mem, x

  and type_def abbr (mem, acc) ((id, idl), ty) = 
    if IMap.mem (snd id) abbr
    then mem, acc
    else 
      let mem, ty = type_expr abbr mem ty in
      mem, ((id, idl), ty) :: acc

  and type_expr abbr mem (p, ty) = 
    let mem, ty = type_expr_ abbr mem p ty in
    mem, (p, ty)

  and type_expr_ abbr mem p = function
  | Tunit | Tbool 
  | Tint32 | Tfloat | Tvar _ as x -> mem, x 

  | (Tpath (_, (_, x)) 
  | Tid (_, x)) when IMap.mem x mem -> 
      mem, snd (IMap.find x mem)

  | (Tpath (_, (_, x)) 
  | Tid (_, x)) when IMap.mem x abbr ->
      let mem, ty = type_expr abbr mem (IMap.find x abbr) in
      let mem = IMap.add x ty mem in
      mem, (snd ty)

  | Tpath _ | Tid _ as x -> mem, x

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
      let mem, vl = lfold (variant abbr) mem vl in
      mem, Talgebric vl 

  | Trecord fdl -> 
      let mem, fdl = lfold (field abbr) mem fdl in
      mem, Trecord fdl 

  | Tabbrev ty -> 
      let mem, ty = type_expr abbr mem ty in
      mem, snd ty

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
