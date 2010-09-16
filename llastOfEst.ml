open Utils
open Ast
open Ist
open Est

module Genv = struct

  let rec program mdl = 
    List.fold_left module_ IMap.empty mdl

  and module_ t md = 
    List.fold_left decl t md.md_decls

  and decl t = function
    | Dalgebric td 
    | Drecord td -> tdef t td
    | Dval _ -> t

  and tdef t td = 
    let i = ref 0 in
    let j = ref 0 in
    IMap.fold (
    fun x (_, tyl) t ->
      if tyl = []
      then (let t = IMap.add x !i t in incr i ; t)
      else (let t = IMap.add x !j t in incr j ; t)
   ) td.td_map t
  
end

type env = {
    pfuns: ISet.t ;
    names: int IMap.t ;
    variants: string IMap.t ;
    blocks: Est.block IMap.t ;
  }

let tmp() = 
  Ident.to_ustring (Ident.tmp())

let rec program mdl = 
  let names = Genv.program mdl in
  List.rev_map (module_ names) mdl

and module_ names md =
  let pfuns = List.fold_left public_funs ISet.empty md.md_decls in
  let l = List.fold_left decl [] md.md_decls in
  let variants = List.fold_left decl_variants IMap.empty md.md_decls in
  let variants, l = IMap.fold def_variant variants (IMap.empty, l) in
  let env = { pfuns = pfuns ; names = names ; 
	      variants = variants ; blocks = IMap.empty } in
  let l = List.fold_left (def env) l md.md_defs in
  (Ident.to_ustring md.md_id, l)

and public_funs acc = function
  | Dval (x, _) -> ISet.add x acc
  | _ -> acc

and decl acc = function
  | Dalgebric td -> union td :: acc
  | Drecord td -> record td :: acc
  | _ -> acc

and decl_variants acc = function
  | Dalgebric td -> variants td acc
  | _ -> acc

and def_variant x ty (acc1, acc2) = 
  let xv = tmp() in
  let acc1 = IMap.add x xv acc1 in
  let acc2 = Llast.Type (xv, ty) :: acc2 in
  acc1, acc2

and make_retty tyl = 
  match tyl with
  | [] -> assert false
  | [x] -> x 
  | tyl -> Llast.Struct tyl

and struct_ tyl = 
  Llast.Pointer (Llast.Struct tyl)

and union td =
  let id = Ident.to_ustring td.td_id in
(*   let tyl = [Llast.Int32; Llast.Any] in *) (* TODO *)
  Llast.Type (id, Llast.Int32)

and variants td acc = 
  IMap.fold variant td.td_map acc

and record td = 
  let id = Ident.to_ustring td.td_id in
  let tyl = IMap.fold field td.td_map [] in
  Llast.Type (id, struct_ tyl)

and field _ (x, tyl) acc =
  match tyl with
  | [ty] -> type_expr ty :: acc
  | tyl -> struct_ (type_expr_list tyl) :: acc
						 
and variant _ (x, tyl) acc = 
  match tyl with
  | []  -> IMap.add x Llast.Int32 acc
  | tyl -> IMap.add x (variant_arg tyl) acc

and variant_arg tyl = 
  let tyl = type_expr_list tyl in
  struct_ tyl

and type_expr_list l = List.map type_expr l
and type_expr = function
  | Tany 
  | Tvar _ -> Llast.Any
  | Tprim ty -> type_prim ty
  | Tapply (x, [ty]) when x = Naming.tobs -> 
      type_expr ty
  | Tapply (x, _) 
  | Tid x -> type_id x
  | Tfun (tyl, rty) -> 
      let tyl = type_expr_list tyl in
      let rty = type_expr_list rty in
      Llast.Function (tyl, rty)

and type_id x = 
  try 
    let md = Ident.origin x in
    Llast.Path (md, Ident.to_ustring x)
  with Not_found -> 
    Llast.Id (Ident.to_ustring x)

and type_prim = function
  | Tunit -> Llast.Void
  | Tbool -> Llast.Int1
  | Tchar -> Llast.Int8
  | Tint32 -> Llast.Int32
  | Tfloat -> Llast.Float

and def env acc df = 
  let public = ISet.mem df.df_id env.pfuns in
  let link = if public
  then Llvm.Linkage.External
  else Llvm.Linkage.Internal in
  let cc = if public 
  then Llvm.CallConv.fast (* TODO make a decision *)
  else Llvm.CallConv.fast in
  let name = Ident.to_ustring df.df_id in
  let argl = List.map snd df.df_args in
  let argl = List.map Ident.to_ustring argl in
  let tyl = List.map fst df.df_args in
  let rty = List.map fst df.df_return in
  let tyl = type_expr_list tyl in
  let rty = type_expr_list rty in
  let rty = make_retty rty in
  let fdef = { 
    Llast.flink = link ;
    Llast.fcc   = cc ;
    Llast.fname = name ;
    Llast.fargs = argl ;
    Llast.ftargs = tyl ;
    Llast.fbody = body env df.df_body ;
    Llast.frett = rty ;
  } in
  Llast.Fun fdef :: acc

and body env = function
  | [] -> assert false
  | l -> List.map (block env) l

and id_list l = 
  let l = List.map snd l in
  List.map Ident.to_ustring l

and block env bl =  
  let bl_id = Ident.to_ustring bl.bl_id in
  let eqs, ret = return env bl.bl_ret in
  let eqs = List.fold_right (equation env) bl.bl_eqs eqs in
  { Llast.bname = bl_id ;
    Llast.bdecl = List.map phi bl.bl_phi ;
    Llast.bbody = eqs ;
    Llast.bret = ret ;
  }

and phi (x, ty, l) = 
  let x = Ident.to_ustring x in
  let l = List.map (fun (x, y) -> Ident.to_ustring x, Ident.to_ustring y) l in
  x, type_expr ty, l

and return env = function
  | Lreturn _ -> assert false
  | Return idl -> [], Llast.Return (id_list idl)
  | Jump lbl -> [], Llast.Jmp (Ident.to_ustring lbl) 
  | If (c, l1, l2) -> 
      let c = Ident.to_ustring (snd c) in
      let l1 = Ident.to_ustring l1 in
      let l2 = Ident.to_ustring l2 in
      [], Llast.Br (c, l1, l2)
  | Match ([_, x], al) -> 
      let x = Ident.to_ustring x in
      let tmp = tmp() in
      let eqs, cases, default = split_match env al in
      let eqs = Llast.Cast (tmp, x, Llast.Int32) :: eqs in
      eqs, Llast.Switch (tmp, cases, default)
  | Match _ -> assert false (* ill-formed match *)

and split_match env = function
  | [] -> assert false
  | [_, lbl] -> [], [], Ident.to_ustring lbl
  | ([_, Pany], lbl) :: _ -> [], [], Ident.to_ustring lbl
  | ([ty, Pvariant (y, [])], lbl) :: rl -> 
      let eqs, cases, default = split_match env rl in
      let x = tmp() in
      let y = IMap.find y env.names in
      let ty = type_expr ty in
      let v = Llast.Const (x, ty, Llast.Const_enum y) in
      v :: eqs, (x, Ident.to_ustring lbl) :: cases, default
  | _ -> failwith "TODO rest of Patterns in llastOfEst"

and equation env (idl, e) acc = 
  equation_ env (idl, e) :: acc
			    
and equation_ env (idl, e) = 
  match idl, e with
  | [_, x], Eid y -> 
      let x = Ident.to_ustring x in
      let y = Ident.to_ustring y in
      Llast.Alias (x, y)
  | [ty, x], Evalue v -> 
      let ty = type_expr ty in
      let x = Ident.to_ustring x in
      let v = value v in
      Llast.Const (x, ty, v)
  | [ty, x], Ebinop (op, (ty1, x1), (ty2, x2)) -> 
      let x = Ident.to_ustring x in
      let ty1 = type_expr ty1 in
      let x1 = Ident.to_ustring x1 in
      let x2 = Ident.to_ustring x2 in
      binop x ty1 x1 x2 op
  | [ty, x], Evariant (y, []) -> 
      let x = Ident.to_ustring x in
      let y = IMap.find y env.names in
      let ty = type_expr ty in
      Llast.Const (x, ty, Llast.Const_enum y)
  | [_, x], Eapply (f, idl) -> 
      let idl = List.map snd idl in
      let x = Ident.to_ustring x in
      let f = Ident.to_ustring f in
      let idl = List.map Ident.to_ustring idl in
      Llast.Call (false, x, f, idl)
  | _ -> failwith "TODO rest of equation in llastOfEst"

(*  
  | Euop of Ast.uop * ty_id
  | Erecord of (id * ty_idl) list 
  | Ewith of ty_id * (id * ty_idl) list 
  | Efield of ty_id * id 
  | Ematch of ty_idl * (pat * expr) list
  | Ecall of label
  | Eapply of id * ty_idl
  | Eseq of ty_id * ty_idl
  | Eif of ty_id * label * label

*)

and pat pel = 
  match pel with
  | [_, x] -> pat_ x
  | _ -> assert false

and pat_ = function
  | Pany -> tmp()
  | Pid x -> Ident.to_ustring x
  | Pvariant _ -> failwith "TODO Pvariant llastOfEst"
  (* | Pvariant of id * pat *)
  | Precord _ -> failwith "TODO Precord llastOfEst"
  (* | Precord of id option * pfield list *)

and variant_args env st idl acc = 
  let i = ref 0 in
  List.fold_left (
  fun acc (ty, y) ->
    let y = Ident.to_ustring y in
    let v = tmp() in
    let ptr = Llast.Get_field (v, st, !i) in
    let store = Llast.Store (v, y) in 
    incr i ;
    ptr :: store :: acc)
    acc idl

and binop res ty x1 x2 = function
  | Eeq | Elt | Elte | Egt | Egte as op -> 
      (match ty with
      | Llast.Int32 -> Llast.Icmp (res, icmp op, ty, x1, x2)
      | Llast.Float -> Llast.Fcmp (res, fcmp op, ty, x1, x2)
      | _ -> assert false)
  | op -> 
      (match ty with
      | Llast.Int32 -> Llast.Binop (res, iarith op, ty, x1, x2)
      | Llast.Float -> Llast.Binop (res, farith op, ty, x1, x2)
      | _ -> assert false)

and icmp = function
  | Eeq		-> Llast.Eq
  | Elt		-> Llast.Slt
  | Elte	-> Llast.Sle
  | Egt		-> Llast.Sgt
  | Egte	-> Llast.Sge
  | _		-> assert false

and fcmp = function
  | Eeq		-> Llast.FUeq
  | Elt		-> Llast.FUlt
  | Elte	-> Llast.FUle
  | Egt		-> Llast.FUgt
  | Egte	-> Llast.FUge
  | _		-> assert false
  
and iarith = function
  | Eplus	-> Llast.Add
  | Eminus	-> Llast.Sub 
  | Estar	-> Llast.Mul
  | _		-> assert false

and farith = function
  | Eplus	-> Llast.Fadd
  | Eminus	-> Llast.Fsub 
  | Estar	-> Llast.Fmul
  | _		-> assert false

      
and value = function
  | Eunit -> Llast.Const_int "0"
  | Ebool true -> Llast.Const_int "1" 
  | Ebool false -> Llast.Const_int "0" 
  | Eint s -> Llast.Const_int s
  | Efloat s -> Llast.Const_float s 
  | Echar _ -> failwith "TODO const char"
  | Estring _ -> failwith "TODO const string"
