open Llvm
open Llast

let rec program mdl = List.map module_ mdl

and module_ (md_name, fl) = 
  let ctx = global_context () in
  let md = create_module ctx md_name in
  let builder = builder ctx in
  List.map (function_ md ctx builder) fl 

and function_ md ctx builder f = 
  let args = Array.of_list f.fargs in
  let args = Array.map (type_ ctx) args in
  let rett = type_ ctx f.frett in
  let ftype = function_type rett args in
  let mblock = declare_function f.fname ftype md in
  body mblock ctx builder f.fbody

and body mblock ctx builder l = 
  List.map (block mblock ctx builder) l

and type_ ctx = function
  | Int1 -> i1_type ctx
  | Int8 -> i8_type ctx
  | Int16 -> i16_type ctx
  | Int32 -> i32_type ctx
  | Int64 -> i64_type ctx
  | ConstInt -> i32_type ctx
  | Float -> float_type ctx
  | Double -> double_type ctx
  | Array _ -> assert false
  | Pointer _ -> assert false
  | Struct _ -> assert false
  | Function _ -> assert false

and block mblock ctx builder blk = 
  let bb = append_block ctx blk.bname mblock in
  position_at_end bb builder ;
  assert (blk.bdecl = [])   
