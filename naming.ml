open Utils
open Ast

let prim_types = ref SMap.empty
let prim_type s = 
  let id = Ident.make s in
  prim_types := SMap.add s id !prim_types ;
  id

let prim_values = ref SMap.empty
let prim_value s = 
  let id = Ident.make s in
  prim_values := SMap.add s id !prim_values ;
  id

let prim_cstrs = ref SMap.empty
let prim_cstr s = 
  let id = Ident.make s in
  prim_cstrs := SMap.add s id !prim_cstrs ;
  id

let int8	= prim_type "int8"
let int16	= prim_type "int16"
let int32	= prim_type "int32"
let int64	= prim_type "int64"
let bool	= prim_type "bool"
let float	= prim_type "float"
let double	= prim_type "double"
let string      = prim_type "string"
let tobs        = prim_type "obs"
let tshared     = prim_type "shared"
let toption     = prim_type "option"
let tfuture     = prim_type "future"

let malloc      = prim_value "malloc"
let ifree       = prim_value "free"
let spawn       = prim_value "spawn"
let wait        = prim_value "wait"
let print       = prim_value "print"
let print_int   = prim_value "print_int"
let share       = prim_value "share"
let free_shared = prim_value "free_shared"
let clone       = prim_value "clone"
let visit       = prim_value "visit"
let visit_obs   = prim_value "visit_obs"
let eunit       = prim_value "()"
let get         = prim_value "array_get"
let length      = prim_value "array_length"

let some        = prim_cstr "Some"
let none        = prim_cstr "None"

let prim_types  = !prim_types
let prim_values = !prim_values
let prim_cstrs  = !prim_cstrs

module Env:sig

  type t

  val empty: t

  val value: t -> Ast.id -> Nast.id
  val try_value: t -> Ast.id -> Nast.id option
  val field: t -> Ast.id -> Nast.id
  val type_: t -> Ast.id -> Nast.id
  val tvar: t -> Ast.id -> Nast.id
  val cstr: t -> Ast.id -> Nast.id

  val new_value: t -> Ast.id -> t * Nast.id
  val new_decl: t -> Ast.id -> t * Nast.id
  val new_field: t -> Ast.id -> t * Nast.id
  val new_type: t -> Ast.id -> t * Nast.id
  val new_tvar: t -> Ast.id -> t * Nast.id
  val new_cstr: t -> Ast.id -> t * Nast.id

  val add_type: t -> Ast.id -> Nast.id -> t
  val add_value: t -> Ast.id -> Nast.id -> t

  val has_value: t -> Ast.id -> bool

  val alias: t -> Ast.id -> Ast.id -> t

  val pattern_env: t -> t
  val add_env: t -> t -> t
  val check_penv: Pos.t -> t -> t -> unit

  val print_values: t -> unit

end = struct

  type t = {
      values: Ident.t SMap.t ;
      fields: Ident.t SMap.t ;
      types: Ident.t SMap.t ;
      tvars: Ident.t SMap.t ;
      cstrs: Ident.t SMap.t ;
    }

  let empty = {
    values = prim_values ;
    fields = SMap.empty ;
    types = prim_types ;
    tvars = SMap.empty ;
    cstrs = prim_cstrs ;
  }

  let pattern_env t = { t with values = prim_values }
  let add_env t1 t2 = 
    { t1 with values = map_add t1.values t2.values }

  let check_penv p t1 t2 = 
    SMap.iter (fun x _ ->
      if SMap.mem x t2.values
      then ()
      else Error.both_side_pattern p x) t1.values ;
    SMap.iter (fun x _ ->
      if SMap.mem x t1.values
      then ()
      else Error.both_side_pattern p x) t2.values

  let new_id t env (p, x) = 
    let id = Ident.make x in
    if SMap.mem x env
    then Error.multiple_def p x ;
    let env = SMap.add x id env in
    t, env, (p, id)

  let new_value t (p, x) = 
    let id = Ident.make x in
    let values = SMap.add x id t.values in
    { t with values = values }, (p, id) 

  let new_decl t x = 
    let env = t.values in
    let t, env, id = new_id t env x in
    { t with values = env }, id
      
  let new_field t x = 
    let env = t.fields in
    let t, env, id = new_id t env x in
    { t with fields = env }, id

  let new_type t x = 
    let env = t.types in
    let t, env, id = new_id t env x in
    { t with types = env }, id

  let new_tvar t x = 
    let env = t.tvars in
    let t, env, id = new_id t env x in
    { t with tvars = env }, id

  let new_cstr t x = 
    let env = t.cstrs in
    let t, env, id = new_id t env x in
    { t with cstrs = env }, id

  let value t (p, x) =
    try p, SMap.find x t.values
    with Not_found -> Error.unbound_name p x

  let try_value t (p, x) = 
    try Some (p, SMap.find x t.values)
    with Not_found -> None

  let field t (p, x) =
    try p, SMap.find x t.fields
    with Not_found -> Error.unbound_name p x

  let type_ t (p, x) =
    try p, SMap.find x t.types
    with Not_found -> Error.unbound_name p x

  let tvar t (p, x) =
    try p, SMap.find x t.tvars
    with Not_found -> Error.unbound_name p x

  let cstr t (p, x) =
    try p, SMap.find x t.cstrs
    with Not_found -> Error.unbound_name p x

  let add_type t (_, x) (_, id) =
    { t with types = SMap.add x id t.types }

  let add_value t (_, x) (_, id) = 
    { t with values = SMap.add x id t.values }

  let has_value t (_, x) = SMap.mem x t.values

  let alias t x y = 
    let id = value t y in
    add_value t x id

  let print_values penv = 
    SMap.iter (fun x _ -> o x ; o " ") penv.values ;
    o "\n"
end

module Genv: sig

  type t

  val make: Ast.program -> t
  val module_id: t -> Ast.id -> Nast.id
  val sig_: t -> Nast.id -> Env.t
  val alias: t -> Ast.id -> Ast.id -> t

end = struct
    
  type t = { 
      sigs: Env.t IMap.t ;
      module_ids: Ident.t SMap.t ;
    }

  let empty = {
    sigs = IMap.empty ;
    module_ids = SMap.empty ;
  }

  let sig_ t (_, id) = 
    IMap.find id t.sigs

  let module_id t (p, x) =
    try p, SMap.find x t.module_ids
    with Not_found -> Error.unbound_name p x

  let new_module t (_, x) = 
    let id = Ident.make x in
    let t = { t with module_ids = SMap.add x id t.module_ids } in
    t, id

  let alias t id1 id2 =
    let id2 = module_id t id2 in
    let t, id1 = new_module t id1 in
    let sig_ = sig_ t id2 in
    { t with sigs = IMap.add id1 sig_ t.sigs }

  let rec make mdl = 
    List.fold_left module_decl empty mdl

  and module_decl t md =
    let env = List.fold_left decl Env.empty md.md_defs in
    let t, md_id = new_module t md.md_id in
    { t with sigs = IMap.add md_id env t.sigs }

  and decl env = function
    | Dtype tdef_l -> List.fold_left tdef env tdef_l
    | Dval (id, _, _) -> fst (Env.new_decl env id)
    | _ -> env

  and tdef env (id, (_, ty)) = 
    let env, _ = Env.new_type env id in
    type_ id env ty

  and type_ id env = function
    | Tabs (_, (_, ty)) -> type_ id env ty
    | Talgebric vtl -> List.fold_left variant env vtl 
    | Trecord fdl -> List.fold_left field env fdl
    | _ -> env

  and variant env (id, _) = fst (Env.new_cstr env id)
  and field env (id, _) = fst (Env.new_field env id)

end

module FreeVars = struct
  open Ast

  let rec type_expr acc (_, ty) = type_expr_ acc ty
  and type_expr_ acc = function
  | Tid _ 
  | Tabstract
  | Tpath _ -> acc
  | Tvar ((_,v) as x) when not (SMap.mem v acc) -> 
      (* The mem is not necessary but makes the first occurence *)
      (* of the variable as the reference which is nicer        *)
      SMap.add v x acc

  | Tvar _ -> acc
  | Tapply (ty, tyl) -> 
      let acc = type_expr acc ty in
      List.fold_left type_expr acc tyl

  | Ttuple tyl -> List.fold_left type_expr acc tyl
  | Tfun (_, ty1, ty2) -> type_expr (type_expr acc ty1) ty2
  | Tabbrev ty -> type_expr acc ty
  | Talgebric _ 
  | Trecord _ 
  | Tabs _ -> assert false

  let type_expr ty = 
    let vm = type_expr SMap.empty ty in
    SMap.fold (fun _ y acc -> y :: acc) vm []
end

let rec program mdl = 
  let genv = Genv.make mdl in
  List.map (module_ genv) mdl

and module_ genv md = 
  let md_id = Genv.module_id genv md.md_id in
  let sig_ = Genv.sig_ genv md_id in
  let env, decls = List.fold_left (decl genv sig_) (Env.empty, []) md.md_defs in
  let decls = List.rev decls in
  let env = List.fold_left (external_ sig_) Env.empty md.md_defs in
  let env = List.fold_left (def_name sig_) env md.md_defs in
  let acc = genv, env, [] in
  let _, env, defs = List.fold_left (def sig_) acc md.md_defs in
  let defs = List.rev defs in
  { Nast.md_id = md_id ;
    Nast.md_decls = decls ;
    Nast.md_defs = defs ;
  }

and decl genv sig_ (env, acc) = function
  | Dtype tdl -> 
      let env, ty = dtype genv sig_ env tdl in
      let ty = Nast.Dtype ty in
      env, ty :: acc
  | Dval (x, y, z) -> 
      let env, (x, y, z) = dval genv sig_ env x y z in
      let dval = Nast.Dval (x, y, z) in
      env, dval :: acc
  | _ -> env, acc

and dval genv sig_ env id ((p, ty_) as ty) def = 
  match ty_ with 
  | Tfun (_, _, _) ->
      let id = Env.value sig_ id in
      let tvarl = FreeVars.type_expr ty in
      let sub_env, tvarl = lfold Env.new_tvar env tvarl in
      let ty = type_expr genv sig_ sub_env ty in
      (* The declaration of the type variables is implicit *)
      let ty = match tvarl with [] -> ty | l -> p, Nast.Tabs(tvarl, ty) in
      env, (id, ty, def)  
  | _ -> Error.value_function p

and dtype genv sig_ env tdl = 
  let env = List.fold_left (bind_type sig_) env tdl in
  env, (List.map (type_def genv sig_ env) tdl)

and external_ sig_ env = function
  | Dval (x, _, Some _) -> Env.add_value env x (Env.value sig_ x)
  | _ -> env

and bind_type sig_ env (x, _) = 
  let id = Env.type_ sig_ x in
  Env.add_type env x id

and type_def genv sig_ env (id, ty) = 
  let id = Env.type_ env id in
  let ty = type_expr genv sig_ env ty in
  id, ty

and type_expr genv sig_ env (p, ty) = p, type_expr_ genv sig_ env ty
and type_expr_ genv sig_ env x = 
  let k = type_expr genv sig_ env in
  match x with
  | Tvar x -> Nast.Tvar (Env.tvar env x)
  | Tid x -> tid env x
  | Tapply (ty, tyl) -> 
      let tyl = List.map k tyl in
      List.iter check_apply tyl ;
      Nast.Tapply (k ty, tyl)
  | Ttuple tyl -> Nast.Ttuple (List.map k tyl)
  | Tpath (id1, id2) -> 
      let (p1, _) as md_id = Genv.module_id genv id1 in
      let sig_ = Genv.sig_ genv md_id in
      let (p2, v) = Env.type_ sig_ id2 in
      let id2 = Pos.btw p1 p2, v in
      Nast.Tpath (md_id, id2)
  | Tfun (fkind, ty1, ty2) -> Nast.Tfun (fkind, k ty1, k ty2)
  | Talgebric l -> 
      let vl = List.map (tvariant genv sig_ env) l in
      Nast.Talgebric (imap_of_list vl)
  | Trecord l -> 
      let fdl = List.map (tfield genv sig_ env) l in
      Nast.Trecord (imap_of_list fdl)
  | Tabbrev ty -> Nast.Tabbrev (k ty)
  | Tabstract -> Nast.Tabstract
  | Tabs (tvarl, ty) -> 
      let env, tvarl = lfold Env.new_tvar env tvarl in
      Nast.Tabs (tvarl, type_expr genv sig_ env ty)

and check_apply (p, ty) = 
  match ty with
  | Nast.Tprim _ -> Error.poly_is_not_prim p
  | _ -> ()

and tid env (p, x) = tid_ env p x
and tid_ env p = function
  | "unit" -> Nast.Tprim Nast.Tunit
  | "bool" -> Nast.Tprim Nast.Tbool
  | "int32" -> Nast.Tprim Nast.Tint32
  | "float" -> Nast.Tprim Nast.Tfloat
  | "char" -> Nast.Tprim Nast.Tchar
  | x -> Nast.Tid (Env.type_ env (p, x))

and tvariant genv sig_ env (id, ty) = 
  let ty = match ty with 
  | None -> None
  | Some ty -> Some (type_expr genv sig_ env ty) in
  Env.cstr sig_ id, ty

and tfield genv sig_ env (id, ty) = 
  Env.field sig_ id, type_expr genv sig_ env ty  

and def_name sig_ env = function
  | Dlet ((p, _) as x, pl, e) -> 
      (match Env.try_value sig_  x with
      | None -> Error.type_missing p
      | Some id -> Env.add_value env x id)
  | _ -> env

and def sig_ (genv, env, acc) = function
  | Dmodule (id1, id2) -> Genv.alias genv id1 id2, env, acc
  | Dlet (id, pl, e) -> 
      let sub_env, pl = lfold (pat genv sig_) env pl in
      let e = expr genv sig_ sub_env e in
      let id = Env.value env id in
      genv, env, (id, pl, e) :: acc
  | Dtype _
  | Dval _ -> genv, env, acc

and dlet genv sig_ env acc (id, pl, e) = 
  let id = Env.value env id in
  let env, pl = lfold (pat genv sig_) env pl in
  let e = expr genv sig_ env e in
  (id, pl, e) :: acc

and pat genv sig_ env (pos, p) = 
  let env, p = pat_ genv sig_ env pos p in
  env, (pos, p)

and pat_ genv sig_ env pos = function
  | Punit -> env, Nast.Pvalue Nast.Eunit
  | Pany -> env, Nast.Pany
  | Pid x -> 
      let env, x = Env.new_value env x in
      env, Nast.Pid x
  | Pchar x -> env, Nast.Pvalue (Nast.Echar x)
  | Pint x -> env, Nast.Pvalue (Nast.Eint x)
  | Pbool b -> env, Nast.Pvalue (Nast.Ebool b)
  | Pfloat f -> env, Nast.Pvalue (Nast.Efloat f)
  | Pstring s -> env, Nast.Pvalue (Nast.Estring s)
  | Pcstr id -> env, Nast.Pcstr (Env.cstr sig_ id)
  | Pvariant (id, p) -> 
      let env, p = pat genv sig_ env p in
      env, Nast.Pvariant (Env.cstr sig_ id, p)
  | Precord fl -> 
      let env, fl = lfold (pat_field genv sig_) env fl in
      let fid = List.filter (
	function _, Nast.PField _ -> false | _ -> true
       ) fl in
      (match fid with
      | [] -> Error.missing_record_name pos
      | [_] -> ()
      | (p1, _) :: (p2, _) :: _ -> Error.multiple_record_name p1 p2) ;
      env, Nast.Precord fl
  | Pbar (p1, p2) ->  (* TODO this is bad *)
      let penv = Env.pattern_env env in
      let penv1, p1 = pat genv sig_ penv p1 in
      let penv2, p2 = pat genv sig_ penv1 p2 in
      Env.check_penv pos penv1 penv2 ;
      env, Nast.Pbar (p1, p2)
  | Ptuple pl -> 
      let env, pl = lfold (pat genv sig_) env pl in
      env, Nast.Ptuple pl
  | Pevariant (id1, id2, arg) -> 
      let md_id = Genv.module_id genv id1 in
      let md_sig = Genv.sig_ genv md_id in
      let id2 = Env.cstr md_sig id2 in
      let env, arg = pat genv sig_ env arg in
      env, Nast.Pevariant (md_id, id2, arg)
  | Pecstr (md_id, id) -> 
      let md_id = Genv.module_id genv md_id in
      let md_sig = Genv.sig_ genv md_id in
      let id = Env.cstr md_sig id in
      env, Nast.Pecstr (md_id, id)
  | Pas (x, p) -> 
      let env, p = pat genv sig_ env p in
      let env, x = Env.new_value env x in
      env, Nast.Pas (x, p)
      
and pat_field genv sig_ env (p, pf) = 
  let env, pf = pat_field_ genv sig_ env pf in
  env, (p, pf)

and pat_field_ genv sig_ env = function
  | PFany -> env, Nast.PFany
  | PFid x -> 
      let env, x = Env.new_value env x in
      env, Nast.PFid x
  | PField (id, p) -> 
      let env, p = pat genv sig_ env p in
      env, Nast.PField (Env.field sig_ id, p)

and expr genv sig_ env (p, e) = p, expr_ genv sig_ env e
and expr_ genv sig_ env e = 
  let k = expr genv sig_ env in
  match e with
  | Eunit -> Nast.Evalue Nast.Eunit
  | Ebool x -> Nast.Evalue (Nast.Ebool x)
  | Eint x -> Nast.Evalue (Nast.Eint x)
  | Efloat x -> Nast.Evalue (Nast.Efloat x)
  | Echar x -> Nast.Evalue (Nast.Echar x)
  | Estring x -> Nast.Evalue (Nast.Estring x)
  | Eid (p, "obs") -> Error.obs_not_value p
  | Eid (p, "free") -> Error.free_not_value p
  | Eid x -> Nast.Eid (Env.value env x)
  | Ebinop (bop, e1, e2) -> Nast.Ebinop (bop, k e1, k e2)
  | Euop (uop, e) -> Nast.Euop (uop, k e)
  | Etuple el -> Nast.Etuple (List.map k el)
  | Ecstr x -> Nast.Ecstr (Env.cstr sig_ x)
  | Ematch (e, pel) -> 
      let pel = List.map (pat_expr genv sig_ env) pel in
      Nast.Ematch (k e, pel) 
  | Elet (p, e1, e2) -> 
      let env, p = pat genv sig_ env p in
      let e2 = expr genv sig_ env e2 in
      Nast.Elet (p, k e1, e2)
  | Eif (e1, e2, e3) -> Nast.Eif (k e1, k e2, k e3) 
  | Efun (pl, e) -> 
      let env, pl = lfold (pat genv sig_) env pl in
      let e = expr genv sig_ env e in
      Nast.Efun (pl, e)
  | Eapply ((_, Eid (_, "free")), e) ->
      (match e with
      | [_, Eid y] -> Nast.Efree (Env.value env y)
      | (p, _) :: _ -> Error.free_expects_id p
      | _ -> assert false)
  | Eapply ((_, Eid (_, "obs")), e) ->
      (match e with
      | [_, Eid y] -> Nast.Eobs (Env.value env y)
      | (p, _) :: _ -> Error.obs_expects_id p
      | _ -> assert false)
  | Eapply (e, el) -> Nast.Eapply (k e, List.map k el)
  | Erecord fdl -> Nast.Erecord (List.map (field genv sig_ env) fdl)
  | Efield (e, v) -> Nast.Efield (k e, Env.field sig_ v)
  | Eextern (md_id, id2) -> 
      let md_id = Genv.module_id genv md_id in
      let sig_md = Genv.sig_ genv md_id in
      let id2 = Env.value sig_md id2 in
      Nast.Eid id2
  | Eefield (e, id1, id2) -> 
      let id1 = Genv.module_id genv id1 in
      let sig_ = Genv.sig_ genv id1 in
      let id2 = Env.field sig_ id2 in
      Nast.Efield (k e, id2)
  | Eecstr (md_id, id) ->
      let md_id = Genv.module_id genv md_id in
      let sig_md = Genv.sig_ genv md_id in
      let id = Env.cstr sig_md id in      
      Nast.Ecstr id
  | Ewith (e, fdl) -> 
      let e = expr genv sig_ env e in
      Nast.Ewith (e, List.map (field genv sig_ env) fdl)
  | Eseq (e1, e2) -> 
      let e1 = expr genv sig_ env e1 in
      let e2 = expr genv sig_ env e2 in
      Nast.Eseq (e1, e2)

and field genv sig_ env = function
  | Eflocl (id, e) -> 
      Env.field sig_ id, expr genv sig_ env e
  | Efextr (md_id, id, e) -> 
      let md_id = Genv.module_id genv md_id in
      let sig_md = Genv.sig_ genv md_id in
      let id = Env.field sig_md id in      
      id, expr genv sig_ env e

and pat_expr genv sig_ env (p, e) = 
  let env, p = pat genv sig_ env p in
  p, expr genv sig_ env e
