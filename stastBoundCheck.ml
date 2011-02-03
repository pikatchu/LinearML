open Utils

module PSet = Set.Make(Pos)

module Value = struct

  type t = 
    | Undef
    | Array of PSet.t
    | Const of Int64.t
    | Sum of expr list IMap.t
    | Rec of expr list IMap.t
    | Int of bool * PSet.t * PSet.t 

  and expr = 
    | Id of Stast.id
    | Value of t
    | Or of expr * expr
    | And of expr * expr
    | Not of expr
    | Plus of expr * expr
    | Minus of expr * expr
    | Mult of expr * expr
    | Div of expr * expr
    | Lte of expr * expr
    | Gte of expr * expr
    | Lt of expr * expr
    | Gt of expr * expr


  let compare = Pervasives.compare

  let int_of_const n = 
    Int (n >= Int64.zero, PSet.empty, PSet.empty)

  let rec unify env v1 v2 = 
    match v1, v2 with
    | Id x, v | v, Id x -> 
	(try unify env (IMap.find (snd x) env) v
	with Not_found -> Value Undef)
    | Value v1, Value v2 -> Value (unify_value env v1 v2)
    | _ -> Value Undef

  and unify_value env v1 v2 = 
    match v1, v2 with
    | Const n, x 
    | x, Const n -> unify_value env (int_of_const n) x
    | Int (b1, good1, bad1), Int (b2, good2, bad2) -> 
	Int (b1 && b2, PSet.inter good1 good2, PSet.inter bad1 bad2)
    | Sum x1, Sum x2 -> Sum (imap2 (unify_list env) x1 x2)
    | Rec x1, Rec x2 -> Rec (imap2 (unify_list env) x1 x2)
    | Array p1, Array p2 -> Array (PSet.union p1 p2)
    | _ -> Undef

  and unify_list env l1 l2 = 
    match l1, l2 with
    | [], l | l, [] -> l
    | x1 :: rl1, x2 :: rl2 -> 
	unify env x1 x2 :: unify_list env rl1 rl2

  let rec eval env = function
    | Value v -> v
    | Id (_, x) -> 
	(try eval env (IMap.find x env) with Not_found -> Undef)
    | Plus (v1, v2) -> plus (eval env v1) (eval env v2)
    | Minus (v1, v2) -> minus (eval env v1) (eval env v2)
    | Mult (v1, v2) -> mult (eval env v1) (eval env v2)
    | Div (Plus (x1, x2) as v1, (Value (Const n) as v2)) -> 
	if n >= Int64.of_int 2
	then match eval env x1, eval env x2 with
	| Int (b1, good1, _), Int (b2, good2, _) ->
	    Int (b1 && b2, PSet.inter good1 good2, PSet.empty)
	| _ -> div (eval env v1) (eval env v2)
	else div (eval env v1) (eval env v2)
    | Div (v1, v2) -> div (eval env v1) (eval env v2)
    | _ -> Undef

  and plus v1 v2 = 
    match v1, v2 with
    | Const n1, Const n2 -> Const (Int64.add n1 n2)
    | Const n, Int (b, good, bad) 
    | Int (b, good, bad), Const n -> 
	let b = b && n >= Int64.zero in
	let good, bad = 
	  if n < Int64.zero 
	  then PSet.union good bad, PSet.empty
	  else PSet.empty, PSet.empty
	in
	Int (b, good, bad)
    | Int (b1, good1, bad1), Int (b2, good2, bad2) ->
	Int (b1 && b2, PSet.empty, PSet.empty)
    | _ -> Undef

  and minus v1 v2 = 
    match v2 with
    | Const n -> 
	plus v1 (Const (Int64.sub Int64.zero n))
    | _ -> Undef

  and mult v1 v2 = 
    match v1, v2 with
    | Const n1, Const n2 -> Const (Int64.add n1 n2)
    | Const n, Int (b, _, _) 
    | Int (b, _, _), Const n -> Int (b && n >= Int64.zero, PSet.empty, PSet.empty)
    | _ -> Undef

  and div v1 v2 = mult v1 v2

  let get_int env x = try
    match eval env (IMap.find (snd x) env) with
    | Int (b, good, bad) -> b, good, bad
    | Const n -> n >= Int64.zero, PSet.empty, PSet.empty 
    | _ -> false, PSet.empty, PSet.empty 
  with Not_found -> false, PSet.empty, PSet.empty

  let rec lte env x y = 
    match x with
    | Id x -> 
	let lower, good, bad = get_int env x in
	let good, bad = 
	  match eval env y with
	  | Int (_, good', bad') -> 
	      PSet.union good good', PSet.union bad bad'
	  | _ -> good, bad
	in
	IMap.add (snd x) (Value (Int (lower, good, bad))) env
    | _ -> env 

  and gte env x y = 
    match x with
    | Id x -> 
	let lower, good, bad = get_int env x in
	let lower = 
	  match eval env y with
	  | Const n -> lower || n >= Int64.zero
	  | Int (b, _, _) -> lower || b
	  | _ -> lower
	in
	IMap.add (snd x) (Value (Int (lower, good, bad))) env
    | _ -> env 

  and lt env x y = 
    match x with
    | Id x -> 
	let lower, good, bad = get_int env x in
	let good, bad = 
	  match eval env y with
	  | Int (_, good', bad') -> 
	      PSet.union (PSet.union good good') bad', PSet.empty
	  | _ -> good, bad
	in
	IMap.add (snd x) (Value (Int (lower, good, bad))) env
    | _ -> env 

  and gt env x y =
    match x with
    | Id x -> 
	let lower, good, bad = get_int env x in
	let lower = 
	  match eval env y with
	  | Const n -> lower || n >= (Int64.sub Int64.zero Int64.one)
	  | Int (b, _, _) -> lower || b
	  | _ -> lower
	in
	IMap.add (snd x) (Value (Int (lower, good, bad))) env
    | _ -> env 

  let rec if_is_true env = function
    | And (v1, v2) -> 
	let env = if_is_true env v1 in
	let env = if_is_true env v2 in
	env
    | Not t -> if_is_false env t
    | Lte (v1, v2) -> 
	let env = lte env v1 v2 in
	gte env v2 v1
    | Gte (v1, v2) -> 
	let env = gte env v1 v2 in
	lte env v2 v1
    | Lt (v1, v2) -> 
	let env = lt env v1 v2 in
	gt env v2 v1
    | Gt (v1, v2) -> 
	let env = gt env v1 v2 in
	lt env v2 v1
    | _ -> env

  and if_is_false env = function
    | Or (v1, v2) -> 
	let env = if_is_false env v1 in
	let env = if_is_false env v2 in
	env
    | Not t -> if_is_true env t
    | Lte (v1, v2) -> 
	let env = gt env v1 v2 in
	lt env v2 v1
    | Gte (v1, v2) -> 
	let env = lt env v1 v2 in
	gt env v2 v1 
    | Lt (v1, v2) -> 
	let env = gte env v1 v2 in
	lte env v2 v1
    | Gt (v1, v2) -> 
	let env = lte env v1 v2 in
	gte env v2 v1
    | _ -> env

end

open Stast
open Value

module TMap = Map.Make(struct
  type t = Ident.t * Value.t list
  let compare = Pervasives.compare
end
)

type env = {
    values: Value.expr IMap.t ;
    privates: Stast.def IMap.t ;
    mem: Value.expr list TMap.t ref ;
  }

let rec program mdl = 
  List.iter module_ mdl 

and module_ md = 
  let privs = List.fold_left decl ISet.empty md.md_decls in
  let mem = ref TMap.empty in
  let privs = List.fold_left (def_priv privs) IMap.empty md.md_defs in
  List.iter (def privs mem) md.md_defs 

and decl s = function
  | Dval (Ast.Private, (_, x), _, _) -> ISet.add x s 
  | _ -> s

and def_priv privs acc ((_, (_, x), _, _) as def) = 
  if ISet.mem x privs
  then IMap.add x def acc
  else acc

and def privs mem ((_, (_, x), _, _) as df) = 
  if IMap.mem x privs
  then ()
  else 
    let env = { values = IMap.empty ; privates = privs ; mem = mem } in
    def_public env df

and def_private env (_, (_, x), p, e) v = 
  let v = List.map (fun x -> Value x) v in
  let env = pat env p v in
  tuple env e

and def_public env (_, (_, x), p, e) = 
  Ident.print x ;
  let v = type_expr_list (fst p) in
  let env = pat env p v in
  ignore (tuple env e)

and type_expr_list (_, l) = 
  List.map type_expr l

and type_expr (_, ty) =
  match ty with
    | Tapply ((_, x), (_, [ty])) when x = Naming.tobs -> 
	type_expr ty
    | Tid (p, x) ->
	if x = Naming.barray || x = Naming.carray || 
	x = Naming.iarray || x = Naming.farray
	then Value (Array (PSet.singleton p))
	else Value Undef
    | _ -> Value Undef

and pat env (_, p) v = 
  match p with
  | [l] -> pat_tuple env l v
  | _ -> env

and pat_tuple env (_, pel) v = 
  (try List.fold_left2 pat_el env pel v
  with _ -> env)

and pat_el env (_, p) v = pat_ env p v
and pat_ env p v = 
  match p with
  | Pany -> env
  | Pid (_, x) -> { env with values = IMap.add x v env.values }
  | Pvalue _ -> env
  | Pvariant (x, p) -> 
      (try 
	match eval env.values v with
	| Sum m -> 
	    pat env p (IMap.find (snd x) m)
	| _ -> env
      with Not_found -> env)
  | Precord fdl -> 
      (try 
	match eval env.values v with
	| Rec m -> List.fold_left (pat_field m v) env fdl
	| _ -> env
      with Not_found -> env)
  | Pas ((_, x), p) -> 
      let env = { env with values = IMap.add x v env.values } in
      pat env p [v]

and pat_field m v env (_, pf) = pat_field_ m v env pf
and pat_field_ m v env = function
  | PFany -> env
  | PFid (_, x) -> { env with values = IMap.add x v env.values }
  | PField (x, p) -> 
      (try pat env p (IMap.find (snd x) m) with Not_found -> env)

and tuple env (_, tpl) = List.fold_right (tuple_pos env) tpl []
and tuple_pos env (ty, e) acc = 
  let undef = List.map (fun _ -> Value Undef) (snd ty) in
  expr_ env undef e @ acc

and expr env (ty, e) = expr_ env [Value Undef] e
and expr_ env undef = function
  | Eid x -> 
      if IMap.mem (snd x) env.privates
      then def_public env (IMap.find (snd x) env.privates) ;
      [Id x]
  | Evalue v -> [Value (value v)]
  | Evariant (x, e) -> 
      let e = tuple env e in
      [Value (Sum (IMap.add (snd x) e IMap.empty))]
  | Ebinop (bop, e1, e2) -> 
    let e1 = expr env e1 in
    let e2 = expr env e2 in
    (match e1, e2 with
    | [v1], [v2] -> [binop bop v1 v2]
    | _ -> assert false)
  | Euop (uop, e) -> 
      let e = expr env e in
      let e = List.hd e in
      [unop uop e]
  | Erecord fdl ->
      let m = List.fold_left (field env) IMap.empty fdl in
      [Value (Rec m)]
  | Ewith (e, fdl) -> 
      let e = expr env e in
      let e = List.hd e in
      let m = 
	match eval env.values e with
	| Rec m -> m
	| _ -> IMap.empty
      in
      let m = List.fold_left (field env) m fdl in
      [Value (Rec m)]
  | Efield (e, fd) -> 
      let e = expr env e in
      let e = List.hd e in
      (match eval env.values e with
      | Rec m -> IMap.find (snd fd) m
      | _ -> undef)
  | Ematch (e, al) -> 
      let e = tuple env e in
      let al = List.map (action env e) al in
      List.fold_left (unify_list env.values) (List.hd al) (List.tl al)
  | Elet (p, e1, e2) -> 
      let e1 = tuple env e1 in
      let env = pat env p e1 in
      tuple env e2
  | Eif (e1, e2, e3) -> 
      let e1 = expr env e1 in
      let e1 = List.hd e1 in
      let env' = { env with values = if_is_true env.values e1 } in
      let e2 = tuple env' e2 in
      let env' = { env with values = if_is_false env.values e1 } in
      let e3 = tuple env' e3 in
      unify_list env.values e2 e3
  | Eapply (_, _, x, e) ->
      let e = tuple env e in
      if IMap.mem (snd x) env.privates
      then
	let e = List.map (eval env.values) e in
	let call = (snd x, e) in
	(try TMap.find call !(env.mem)
	with Not_found ->
	  env.mem := TMap.add call undef !(env.mem) ;
	  let env' = { env with values = IMap.empty } in
	  let res = def_private env' (IMap.find (snd x) env.privates) e in
	  env.mem := TMap.add call res !(env.mem) ;
	res)
      else undef
  | Eseq (e1, e2) -> 
      ignore (expr env e1) ;
      tuple env e2
  | Eobs x -> [Id x]
  | Efree _ -> undef
  | Eget (x, e) -> 
      let pos = fst (fst e) in
      let e = expr env e in
      check_get env pos x e ; 
      undef
  | Eset (x, e1, e2) -> check_set env x e1 ; id env x
  | Elength (_, x) -> [length env x]

and id env (_, x) = 
  (try [IMap.find x env.values] with Not_found -> [Value Undef])

and value = function
  | Eint (_, n) -> Const (Int64.of_string n)
  | _ -> Undef

and length env x = 
  match eval env.values (Id x) with
  | Array p -> Value (Int (true, PSet.empty, p))
  | _ -> Value Undef

and binop bop v1 v2 = 
  match bop with
  | Ast.Elt -> Lt (v1, v2) 
  | Ast.Elte -> Lte (v1, v2)
  | Ast.Egt -> Gt (v1, v2) 
  | Ast.Egte -> Gte (v1, v2)
  | Ast.Eplus -> Plus (v1, v2)
  | Ast.Eminus -> Minus (v1, v2)
  | Ast.Estar -> Mult (v1, v2)
  | Ast.Ediv -> Div (v1, v2)
  | Ast.Eor -> Or (v1, v2)
  | Ast.Eand -> And (v1, v2)
  | _ -> Value Undef

and unop uop v = 
  match uop with
  | Ast.Euminus -> Minus (Value (Const Int64.zero), v)
  | _ -> Value Undef

and field env m ((_, x), e) = 
  let v = tuple env e in
  IMap.add x v m 

and action env v (p, e) = 
  let env = pat env p v in
  tuple env e

and check_get env p t e =
  let t = eval env.values (Id t) in
  let e = eval env.values (List.hd e) in
  match t, e with
  | Array t, Int (b, good, bad) -> 
      if not b 
      then (Error.pos p ; exit 3) ;
      let bad = PSet.diff t good in
      if PSet.is_empty bad
      then ()
      else (Error.pos p ; Error.pos (PSet.choose bad) ; exit 4) ;
  | _ -> Error.pos p ; exit 5

and check_set _ _ _ = assert false
