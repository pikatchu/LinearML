open Utils
open Llvm
open Llast

let rec program mdl = 
  let ctx = global_context() in
  let builder = builder ctx in
  List.rev_map (module_ ctx builder) mdl

and module_ ctx builder (md_name, dl) = 
  let md = create_module ctx md_name in
  let t = List.fold_left (opaques md ctx) SMap.empty dl in
  let t' = List.fold_left (def_type ctx) t dl in
  List.iter (refine t t') dl ;
  let _ = List.fold_left (def_fun t' md ctx builder) [] dl in
  dump_module md ; o "\n" ;
  t, (md_name, md, dl)

and opaques md ctx t = function
  | Type (x, _) -> 
      let ty = opaque_type ctx in
      assert (define_type_name x ty md) ;
      SMap.add x ty t
  | _ -> t

and def_type ctx t = function
  | Type (x, ty) -> SMap.add x (type_ t ctx ty) t
  | _ -> t

and def_fun t md ctx builder acc = function
  | Fun f -> (function_ t md ctx builder f) :: acc
  | _ -> acc

and refine t t' = function
  | Type (x, _) -> 
      let ty = SMap.find x t' in
      refine_type (SMap.find x t) ty
  | _ -> ()

and function_ t md ctx builder f = 
  let args = Array.of_list f.fargs in
  let args = Array.map (type_ t ctx) args in
  let rett = type_ t ctx f.frett in
  let ftype = function_type rett args in
  declare_function f.fname ftype md

and type_ t ctx = function
  | Any -> pointer_type (i8_type ctx)
  | Id x -> 
      (try SMap.find x t
      with Not_found -> i1_type ctx)
  | Void -> i1_type ctx
  | Int1 -> i1_type ctx
  | Int8 -> i8_type ctx
  | Int16 -> i16_type ctx
  | Int32 -> i32_type ctx
  | Int64 -> i64_type ctx
  | ConstInt -> i32_type ctx
  | Float -> float_type ctx
  | Double -> double_type ctx
  | Union tyl -> union_type ctx (type_list t ctx tyl)
  | Array _ -> assert false
  | Pointer ty -> pointer_type (type_ t ctx ty)
  | Struct tyl -> pointer_type (struct_type ctx (type_list t ctx tyl))
  | Function _ -> assert false

and type_list t ctx l = Array.of_list (List.map (type_ t ctx) l)

