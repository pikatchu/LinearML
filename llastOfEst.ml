open Utils
open Ist
open Est

let rec program mdl = 
  List.rev_map module_ mdl

and module_ md: Llast.module_ = 
  let l = List.map decl md.md_decls in
  (Ident.to_string md.md_id, l)

and decl = function
  | Dalgebric td -> union td
  | Drecord td -> record td
  | Dval (x, Tfun (tyl1, tyl2)) -> 
      let tyl1 = type_expr_list tyl1 in
      let tyl2 = type_expr_list tyl2 in
      if List.length tyl2 > 1 then failwith "TODO" ;
      let rty = List.hd tyl2 in
      Llast.Fun { 
      Llast.flink = 0 ;
      Llast.fname = Ident.to_string x ;
      Llast.fargs = tyl1 ;
      Llast.fbody = [] (* TODO *) ;
      Llast.frett = rty ;
      Llast.fvret = "" (* TODO what ? *) ;
      }
  | Dval _ -> assert false

and record td = 
  let tyl = IMap.fold (
    fun _ (x, tyl) acc ->
      match tyl with
      | [ty] -> type_expr ty :: acc
      | tyl -> Llast.Struct (type_expr_list tyl) :: acc
   ) td.td_map [] in
  let id = Ident.to_string td.td_id in
  Llast.Type (id, Llast.Struct tyl)

and union td = 
  let tyl = IMap.fold (
    fun _ (x, tyl) acc ->
      match tyl with
      | [] -> Llast.Int16 :: acc
      | tyl -> 
	  let tyl = type_expr_list tyl in
	  let tyl = Llast.Int16 :: tyl in
	  Llast.Struct tyl :: acc
   ) td.td_map [] in
  let id = Ident.to_string td.td_id in
  Llast.Type (id, Llast.Union tyl)


and type_expr_list l = List.map type_expr l
and type_expr = function
  | Tany -> Llast.Any
  | Tprim ty -> type_prim ty
  | Tvar _ -> Llast.Any
  | Tapply (x, [ty]) when x = Naming.tobs -> type_expr ty
  | Tapply (x, _) 
  | Tid x -> Llast.Id (Ident.to_string x)
  | Tfun (tyl1, rty) -> 
      Llast.Function (type_expr_list tyl1, type_expr_list rty)

and type_prim = function
  | Tunit -> Llast.Void
  | Tbool -> Llast.Int1
  | Tchar -> Llast.Int8
  | Tint32 -> Llast.Int32
  | Tfloat -> Llast.Float
