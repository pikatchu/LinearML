open Utils
open Llvm
open Llast

module Type = struct

  let rec program ctx mdl = 
    let mds = List.fold_left (module_decl ctx) SMap.empty mdl in
    let mds = List.fold_left (module_refine ctx mds) SMap.empty mdl in
    let t = List.fold_left (module_funs ctx mds) SMap.empty mdl in
    mds, t

  and module_decl ctx acc (md_name, dl) = 
    let md = create_module ctx md_name in
    let t = List.fold_left (opaques md ctx) SMap.empty dl in
    SMap.add md_name (md, t) acc 

  and module_refine ctx mds acc (md_name, dl) = 
    let (md, t) = SMap.find md_name mds in
    let t' = List.fold_left (def_type mds ctx) t dl in
    List.iter (refine t t') dl ;
    SMap.add md_name (md, t') acc

  and module_funs ctx mds acc (md_name, dl) = 
    let (md, tys) = SMap.find md_name mds in
    let fs = List.fold_left (def_fun mds tys md ctx) SMap.empty dl in
    SMap.add md_name (md, tys, fs, dl) acc

  and opaques md ctx t = function
    | Type (x, _) -> 
	let ty = opaque_type ctx in
	assert (define_type_name x ty md) ;
	SMap.add x ty t
    | _ -> t

  and def_type mds ctx t = function
    | Type (x, ty) -> SMap.add x (type_ mds t ctx ty) t
    | _ -> t

  and def_fun mds t md ctx acc = function
    | Fun f -> SMap.add f.fname (function_ mds t md ctx f) acc
    | _ -> acc

  and refine t t' = function
    | Type (x, _) -> 
	let ty = SMap.find x t' in
	refine_type (SMap.find x t) ty
    | _ -> ()

  and function_ mds t md ctx f = 
    let args = Array.of_list f.ftargs in
    let args = Array.map (type_ mds t ctx) args in
    let rett = type_ mds t ctx f.frett in
    let ftype = function_type rett args in
    let fdec = declare_function f.fname ftype md in
    set_linkage f.flink fdec ;
    set_function_call_conv f.fcc fdec ;
    fdec

  and type_path mds x y = 
    let (md, _) = SMap.find x mds in
    match type_by_name md y with
    | None -> assert false
    | Some ty -> ty

  and type_ mds t ctx = function
    | Any -> pointer_type (i8_type ctx)
    | Id x -> SMap.find x t
    | Path (x, y) -> type_path mds x y
    | Void -> i1_type ctx
    | Int1 -> i1_type ctx
    | Int8 -> i8_type ctx
    | Int16 -> i16_type ctx
    | Int32 -> i32_type ctx
    | Int64 -> i64_type ctx
    | ConstInt -> i32_type ctx
    | Float -> float_type ctx
    | Double -> double_type ctx
    | Union tyl -> 
	let tyl = type_list mds t ctx tyl in
	union_type ctx tyl
    | Array ty -> 
	pointer_type (type_ mds t ctx ty)
    | Pointer ty -> 
	let ty = type_ mds t ctx ty in
	pointer_type ty
    | Struct tyl -> 
	let tyl = type_list mds t ctx tyl in
	let st = struct_type ctx tyl in
	st
    | Function _ -> assert false

  and type_list mds t ctx l = 
    let tyl = List.map (type_ mds t ctx) l in
    Array.of_list tyl

end

type env = {
    mds: (llmodule * lltype SMap.t) SMap.t ;
    ctx: llcontext ;
    fmap: llvalue SMap.t ;
    builder: llbuilder ;
    types: lltype SMap.t ;
    malloc: llvalue ;
    bls: Llast.block SMap.t ;
  }

let pervasives ctx = 
  let md = create_module ctx "pervasives" in
  let rty = pointer_type (i8_type ctx) in
  let args = i64_type ctx in
  let fty = function_type rty [|args|] in
  let malloc = declare_function "malloc" fty md in
  set_linkage Linkage.External malloc ; 
  dump_module md ;
  malloc

let rec program mdl = 
  let ctx = global_context() in
  let mds, t = Type.program ctx mdl in
  List.rev_map (module_ mds ctx t) mdl 

and module_ mds ctx t (md_id, md) = 
  let (md, tys, fs, dl) = SMap.find md_id t in
  let builder = builder ctx in
  let malloc = pervasives ctx in
  let env = 
    { mds = mds ;
      ctx = ctx ; 
      fmap = fs ; 
      builder = builder ; 
      types = tys ;
      malloc = malloc ;
      bls = SMap.empty ;
    } in
  List.iter (def env) dl ;
  dump_module md ; o "\n" ;

and def env = function
  | Type _ -> ()
  | Fun f -> ignore (function_ env f)

and function_ env f = 
  let proto = SMap.find f.fname env.fmap in
  let params = params proto in
  let params = Array.to_list params in
  let ins = List.fold_left2 param env.fmap f.fargs params in 
  body env proto ins f.fbody

and param acc x v = 
  SMap.add x v acc

and body env proto params bll = 
  match bll with
  | [] -> assert false
  | x :: rl ->
      let bls = List.fold_left (
	fun acc bl ->
	  SMap.add bl.bname bl acc
       ) SMap.empty rl in
      let env = { env with bls = bls } in
      block env proto params x

and block env proto acc bl = 
  let bb = append_block env.ctx bl.bname proto in
  position_at_end bb env.builder ;
  let acc = List.fold_left (instruction proto bb env) acc bl.bbody in
  let acc = match bl.bret with
  | Noreturn -> acc
  | Return [] -> assert false
  | Return [x] -> 
(* TODO get rid of try *)      
      (try 
       ignore (build_ret (SMap.find x acc) env.builder) ; 
	acc
      with _ -> acc)
  | Return l ->
      let l = List.map (fun x -> SMap.find x acc) l in
      let t = Array.of_list l in
      ignore (build_aggregate_ret t env.builder)  ;
      acc
  | Jmp lbl -> 
      let target = SMap.find lbl env.bls in
      let acc, sub = block env proto acc target in
      position_at_end bb env.builder ;
      ignore (build_br sub env.builder) ;
      acc in 
  acc, bb

and instruction proto bb env acc = function
  | Alias (x, y) -> 
      let y = SMap.find y acc in
      SMap.add x y acc
  | Const (x, ty, v) ->
      let ty = Type.type_ env.mds env.types env.ctx ty in
      let v = const env ty v in
      SMap.add x v acc
  | Binop (x, bop, ty, x1, x2) -> 
      let x1 = SMap.find x1 acc in
      let x2 = SMap.find x2 acc in
      let bop = binop bop in
      let v = bop x1 x2 x env.builder in
      SMap.add x v acc
  | Alloc (x, ty) -> 
      let ty = Type.type_ env.mds env.types env.ctx ty in      
      let v = size_of ty in
      let bl = build_call env.malloc [|v|] "" env.builder in
      let bl = build_bitcast bl (pointer_type ty) x env.builder in
      SMap.add x bl acc
  | VAlloc (x, ty, vty) -> 
      let vty = Type.type_ env.mds env.types env.ctx vty in      
      let v1 = size_of vty in
      let v2 = size_of (i32_type env.ctx) in
      let v = const_add v1 v2 in
      let bl = build_call env.malloc [|v|] "" env.builder in
      SMap.add x bl acc
  | Store (x, y) -> 
      let x = SMap.find x acc in
      let y = SMap.find y acc in
      dump_value x ;
      dump_value y ;
      ignore (build_store y x env.builder) ;   
      acc
  | Get_element_ptr (x, y, n) -> 
      let y = SMap.find y acc in
      let n = const_int (i32_type env.ctx) n in
      let v = build_gep y [|n|] x env.builder in
      SMap.add x v acc
  | Get_field (x, y, n) -> 
      let y = SMap.find y acc in
      let z = const_int (i32_type env.ctx) 0 in
      let n = const_int (i32_type env.ctx) n in
      let v = build_gep y [|z;n|] x env.builder in
      SMap.add x v acc
  | Cast (x, y, ty) -> 
      let ty = Type.type_ env.mds env.types env.ctx ty in      
      let y = SMap.find y acc in
      let v = build_bitcast y ty x env.builder in
      SMap.add x v acc
  | Br (x, l1, l2) -> 
      let b1 = SMap.find l1 env.bls in
      let b2 = SMap.find l2 env.bls in
      let acc, b1 = block env proto acc b1 in 
      let acc, b2 = block env proto acc b2 in
      position_at_end bb env.builder ;
      let x = SMap.find x acc in
      ignore (build_cond_br x b1 b2 env.builder) ;
      acc
  | Call (tail, x, f, l) -> 
      let f = SMap.find f acc in
      let l = List.map (fun v -> SMap.find v acc) l in
      let t = Array.of_list l in
      let v = build_call f t x env.builder in
      set_tail_call tail v ;
      SMap.add x v acc
  | Icmp (x, op, _, v1, v2) -> 
      let cmp = icmp op in
      let v1 = SMap.find v1 acc in
      let v2 = SMap.find v2 acc in
      let v = build_icmp cmp v1 v2 x env.builder in
      SMap.add x v acc

  | Switch _ -> failwith "TODO Switch in emit.ml"
  | Extract_value _ -> failwith "TODO Extract_value in emit.ml"
  | Insert _ -> failwith "TODO Insert in emit.ml"
  | Alloca _ -> failwith "TODO Alloca in emit.ml"
  | Load _ -> failwith "TODO Load in emit.ml"
  | Fcmp _ -> failwith "TODO Fcmp in emit.ml"


(*  
  | Switch of id * (value * label) list * label

  | Extract_value of id * type_ * idx
  | Insert of id * type_ * type_ * idx
  | Alloca of id * type_ 
  | Load of id * type_ * id
  | Get_element_ptr of id * int
  | Icmp of id * icmp * type_ * id * id
  | Fcmp of id * fcmp * type_ * id * id
  | Return of id

*)

and binop = function
  | Add -> build_add
  | Fadd -> build_fadd
  | Sub -> build_sub
  | Fsub -> build_fsub
  | Mul -> build_mul
  | Fmul -> build_fmul 
  | Udiv -> build_udiv 
  | Sdiv -> build_sdiv 
  | Fdiv -> build_fdiv 
  | Urem -> build_urem 
  | Srem -> build_srem 
  | Frem -> build_frem 
  | Shl -> build_shl 
  | Lshr -> build_lshr 
  | Ashr -> build_ashr 
  | And -> build_and
  | Or -> build_or 
  | Xor -> build_xor

and const env ty = function
  | Const_int s -> 
      const_int_of_string ty s 10 (* TODO different radix *)
  | Const_float s -> 
      const_float_of_string ty s
  | Const_enum i ->
      let i = const_int (i16_type env.ctx) i in
      const_union ty i

and icmp = function
  | Llast.Eq -> Llvm.Icmp.Eq 
  | Llast.Ne -> Llvm.Icmp.Ne 
  | Llast.Ugt -> Llvm.Icmp.Ugt 
  | Llast.Uge -> Llvm.Icmp.Uge
  | Llast.Ult -> Llvm.Icmp.Ult 
  | Llast.Ule -> Llvm.Icmp.Ule 
  | Llast.Sgt -> Llvm.Icmp.Sgt 
  | Llast.Sge -> Llvm.Icmp.Sge
  | Llast.Slt -> Llvm.Icmp.Slt 
  | Llast.Sle -> Llvm.Icmp.Sle
