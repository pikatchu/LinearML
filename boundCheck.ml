(** Module performing abstract interpretation over indexes *)
(* The aim is to prove that every array access is safe *)
(* Every integer is represented either as a constant or as an interval *)
(* The interval is of the form i = Int of bool * good * bad
   - where bool is true if the integer is positive
   - forall x in good, i < x
   - forall x in bad, i <= x
*)
(* When one writes t.(i), the abstract value of i tells us if the 
   access is safe for the array t
*)

open Utils

module PSet = Set.Make(Pos)
module PMap = Map.Make(Pos)

module Value = struct

  type t = 
    | Undef
    | Array of PSet.t * Int64.t
    | Const of Int64.t
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
	let good = PSet.inter good1 good2 in
	let bad = PSet.inter bad1 bad2 in
	Int (b1 && b2, good, bad)
    | Array (p1, n1), Array (p2, n2) -> Array (PSet.union p1 p2, min n1 n2)
    | _ -> Undef

  and unify_value_list env l1 l2 = 
    match l1, l2 with
    | [], l | l, [] -> l
    | x1 :: rl1, x2 :: rl2 -> 
	unify_value env x1 x2 :: unify_value_list env rl1 rl2

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
    | Int (b, _, _), Const n -> 
	Int (b && n >= Int64.zero, PSet.empty, PSet.empty)
    | _ -> Undef

  and div v1 v2 = 
    match v1, v2 with
    | Const n1, Const n2 -> 
	if n2 = Int64.zero then Undef else Const (Int64.div n1 n2)
    | Int (b, good, bad), Const n -> 
	if n > Int64.zero
	then Int (b, PSet.union good bad, PSet.empty)
	else Undef
    | _ -> Undef

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
	      let good = PSet.union good good' in
	      let bad = PSet.union bad bad' in
	      good, PSet.diff bad good
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
    
module Debug = struct
  open Value

  let t = function
    | Undef -> o "Undef"
    | Array _ -> o "Array"
    | Const _ -> o "Const"
    | Int (x, y, z) -> 
	let y = not (PSet.is_empty y) in
	let z = not (PSet.is_empty z) in
	o (Printf.sprintf "Int(%b, %b, %b)" x y z)

  and expr = function
    | Id _ -> o "Id"
    | Value _ -> o "Value"
    | Or _ -> o "Or"
    | And _ -> o "And"
    | Not _ -> o "Not"
    | Plus _ -> o "Plus"
    | Minus _ -> o "Minus"
    | Mult _ -> o "Mult"
    | Div _ -> o "Div"
    | Lte _ -> o "Lte"
    | Gte _ -> o "Gte"
    | Lt _ -> o "Lt"
    | Gt _ -> o "Gt"

end

open Stast
open Value


module TMap = Map.Make(struct
  type t = Ident.t * Value.t list
  let compare = Pervasives.compare
end
)

type env = {
    show: bool ;
    values: Value.expr IMap.t ;
    privates: Stast.def IMap.t ;
    arrays: (Int64.t * PSet.t ) list ;
    mem: Value.expr list TMap.t ref ;
    checks: (bool * bool) PMap.t ref ;
  }

let empty env = { env with
  values = IMap.empty ;
  arrays = [] ;
}

let add x v env = 
  { env with values = IMap.add x v env.values }

let rec program show mdl = 
  let checks = ref PMap.empty in
  List.iter (module_ show checks) mdl ;
  !checks

and module_ show checks md =
  let privs = List.fold_left decl ISet.empty md.md_decls in
  let mem = ref TMap.empty in
  let privs = List.fold_left (def_priv privs) IMap.empty md.md_defs in
  let env = { 
    show = show ;
    values = IMap.empty; 
    privates = privs; 
    mem = mem;
    arrays = [];
    checks = checks ;
  } in 
  List.iter (def env) md.md_defs 

and decl s = function
  | Dval (Ast.Private, (_, x), _, _) -> ISet.add x s 
  | _ -> s

and def_priv privs acc ((_, (_, x), _, _) as def) = 
  if ISet.mem x privs
  then IMap.add x def acc
  else acc

and def env ((_, (_, x), _, _) as df) = 
  if IMap.mem x env.privates
  then ()
  else def_public env df

and def_private env (_, (pos, x), p, e) v = 
  let v = List.map (fun x -> Value x) v in
  let env = pat env p v in
  let env, e = tuple env e in
  let e = List.map (eval env.values) e in
  List.map (fun x -> Value x) e

and def_public env (_, (pos, x), p, e) = 
  let v = type_expr_list (fst p) in
  let env = pat env p v in
  let _, _ = tuple env e in
  ()

and type_expr_list (_, l) = 
  List.map type_expr l

and type_expr (p, ty) =
  match ty with
    | Tapply ((_, x), (_, [ty])) when x = Naming.tobs -> 
	type_expr ty
    | Tapply ((_, x), _) when x = Naming.array ->
	Value (Array (PSet.singleton p, Int64.max_int))
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
  | Pid (_, x) -> add x v env 
  | Pvalue _ -> env
  | Pvariant _
  | Precord _ -> env
  | Pas ((_, x), p) -> 
      let env = add x v env in
      pat env p [v]

and tuple env (_, tpl) = 
  List.fold_right tuple_pos tpl (env, [])

and tuple_pos (ty, e) (env, acc) = 
  let undef = List.map (fun _ -> Value Undef) (snd ty) in
  let env, l = expr_ env undef ty e in
  env, l @ acc

and expr env (ty, e) = expr_ env [Value Undef] (fst ty, [ty]) e    
and expr_ env undef (p, ty) = function
  | Eid x -> 
      env, if IMap.mem (snd x) env.privates
      then (def_public env (IMap.find (snd x) env.privates) ; undef)
      else (match eval env.values (Id x) with
      | Array _ as x -> [Value x]
      | _ -> [Id x])
  | Evalue v -> env, [Value (value v)]
  | Evariant _ -> env, undef
  | Ebinop (bop, e1, e2) ->
    let env, e1 = expr env e1 in
    let env, e2 = expr env e2 in
    env, (match e1, e2 with
    | [v1], [v2] -> [binop bop v1 v2]
    | _ -> assert false)
  | Euop (uop, e) -> 
      let env, e = expr env e in
      let e = List.hd e in
      env, [unop uop e]
  | Erecord _ 
  | Ewith _
  | Efield _ -> env, undef
  | Ematch (e, al) -> 
      let env, e = tuple env e in
      let env, al = lfold (action e) env al in
      env, (match al with 
      | [] -> assert false 
      | [x] -> x
      | hd :: tl -> List.fold_left (unify_list env.values) hd tl)
  | Elet (p, e1, e2) -> 
      let env, e1 = tuple env e1 in
      let env = pat env p e1 in
      tuple env e2
  | Eif (e1, (((p1, _), _) as e2), (((p2, _), _) as e3)) -> 
      let env, e1 = expr env e1 in
      let e1 = List.hd e1 in
      let vals = env.values in
      let env' = { env with values = if_is_true env.values e1 } in
      let env, e2 = tuple env' e2 in
      let env = { env with values = vals } in
      let vals = env.values in
      let env' = { env with values = if_is_false env.values e1 } in
      let env, e3 = tuple env' e3 in
      let env = { env with values = vals } in
      let res = unify_list env.values e2 e3 in
      env, res
  | Eapply (_, _, (_, f), e) when f = Naming.vassert ->
      let env, e = tuple env e in
      let e = List.hd e in
      let env = { env with values = if_is_true env.values e } in
      env, undef
  | Eapply (_, _, (_, f), (_, (esize :: _) as e)) when 
      f = Naming.amake || f = Naming.imake || f = Naming.fmake ->
      let env, _ = tuple env e in
      let env, size = tuple_pos esize (env, []) in
      let size = const_size env (List.hd size) in
      let ps = PSet.singleton p in
      let env = { env with arrays = (size, ps) :: env.arrays } in
      let env = size_expr env p esize in
      let ty = [Value (Array (ps, size))] in
      env, ty
  | Eapply (_, _, (_, f), (_, [x])) when f = Naming.alength -> 
      let env, x = length env x in
      env, [x]
  | Eapply (_, _, (_, f), (_, [t ; _] as e_expr)) when f = Naming.aget ->
      check_prim (fst t) ;
      let env, e = tuple env e_expr in
      env, (match e with
      | [x ; e] ->
	  check_bound env p x e ; 
	  undef
      | _ -> undef)
  | Eapply (_, _, (_, f), (_, [t ; _ ; _] as e_expr)) when f = Naming.aset -> 
      check_prim (fst t) ;
      let env, e = tuple env e_expr in
      env, (match e with
      | [x ; e ; _] ->
	  check_bound env p x e ; 
	  [Value (eval env.values x)]
      | _ -> undef)
  | Eapply (_, _, (_, f), (_, [t ; _ ; _] as e_expr)) when f = Naming.aswap -> 
      let env, e = tuple env e_expr in
      env, (match e with
      | [x ; e ; _] ->
	  check_bound env p x e ; 
	  [Value (eval env.values x) ; Value Undef]
      | _ -> undef)
  | Epartial (f, el) -> 
      let env, _ = tuple env el in
      let env, _ = expr env f in
      env, undef
  | Eapply (_, _, x, e) ->
      let env, e = tuple env e in
      env, if IMap.mem (snd x) env.privates
      then
	let e = List.map (eval env.values) e in
	let e = List.map (const_to_interval env) e in
	let call = (snd x, e) in
	(try TMap.find call !(env.mem)
	with Not_found ->
	  env.mem := TMap.add call undef !(env.mem) ;
	  let df = IMap.find (snd x) env.privates in
	  let res = def_private (empty env) df e in
	  env.mem := TMap.add call res !(env.mem) ;
	res)
      else undef
  | Eseq (e1, e2) -> 
      let env, _ = expr env e1 in
      tuple env e2
  | Eobs x -> env, [Id x]
  | Efree _ -> env, undef
  | Efun (_, _, p, e) ->
      let tyl = List.map fst p in
      let v = List.map type_expr tyl in
      let env = pat_tuple env ((Pos.none, tyl), p) v in
      tuple env e

and value = function
  | Eint (_, n) -> Const (Int64.of_string n)
  | _ -> Undef

and length env e =
  let e = List.hd (snd (fst e)), snd e in
  let env, e = expr env e in
  let e = List.hd e in
  env, match eval env.values e with
  | Array (p, n) -> Value (Int (true, PSet.empty, p))
  | _ -> Value Undef

and binop bop v1 v2 = 
  match bop with
  | Ast.Eplus -> Plus (v1, v2)
  | Ast.Eminus -> Minus (v1, v2)
  | Ast.Estar -> Mult (v1, v2)
  | Ast.Ediv -> Div (v1, v2)
  | Ast.Elt -> Lt (v1, v2) 
  | Ast.Elte -> Lte (v1, v2)
  | Ast.Egt -> Gt (v1, v2) 
  | Ast.Egte -> Gte (v1, v2)
  | Ast.Eor -> Or (v1, v2)
  | Ast.Eand -> And (v1, v2)
  | _ -> Value Undef

and unop uop v = 
  match uop with
  | Ast.Euminus -> Minus (Value (Const Int64.zero), v)
  | _ -> Value Undef

and field (env, m) ((_, x), e) = 
  let env, v = tuple env e in
  let v = List.map (eval env.values) v in
  env, IMap.add x v m 

and action v env (p, e) =
  let env = pat env p v in
  let env, e = tuple env e in
  env, e

and size_expr env p size = 
  match size with 
  | _, Eid ((_, x) as id) -> 
      (try 
	match eval env.values (Id id) with
	| Const _ -> env
	| Int (c, good, bad) -> 
	    let v = Value (Int (c, good, PSet.add p bad)) in
	    add x v env
	| _ -> 
	    let v = Value (Int (false, PSet.empty, PSet.singleton p)) in
	    add x v env
      with Not_found -> 
	let v = Value (Int (false, PSet.empty, PSet.singleton p)) in
	add x v env
      )
  | _ -> env

and const_size env sz = 
  match eval env.values sz with
  | Const n -> n
  | _ -> Int64.max_int

and const_to_interval env = function
  | Const n -> 
      let lb = n >= Int64.zero in
      let good, bad = List.fold_left (
	fun (good, bad) (m, ps) ->
	  if n < m 
	  then PSet.union good ps, bad
	  else if n = m
	  then good, PSet.union bad ps
	  else good, bad
       ) (PSet.empty, PSet.empty) env.arrays in
      Int (lb, good, bad)
  | x -> x

and check_bound env p t e =
  let t = eval env.values t in
  let e = eval env.values e in
  match t, e with
  | Array (t, n), Const n' ->
      if n' < n 
      then 
	if n' >= Int64.zero
	then ()
	else add_low env p 
      else add_up env p (PSet.choose t)
  | Array (t, n), Int (b, good, bad) -> 
      if not b 
      then add_low env p ;
      let bad = PSet.diff t good in
      if PSet.is_empty bad
      then ()
      else add_up env p (PSet.choose bad)
  | _ -> add_low env p ; add_up env p p

and get_bound env p =
  try PMap.find p !(env.checks) 
  with Not_found -> false, false

and add_low env p = 
  let low, up = get_bound env p in
  if env.show 
  then Error.bound_low p ;
  env.checks := PMap.add p (true, up) !(env.checks)

and add_up env p t = 
  let low, up = get_bound env p in
  if env.show 
  then Error.bound_up p t ;
  env.checks := PMap.add p (low, true) !(env.checks)

and check_prim = function
  | (_, [_, Tapply ((_, x), t)]) when x = Naming.tobs -> check_prim t
  | (_, [_, Tapply (_, (_, [_, Tprim _]))]) -> ()
  | (p, _) -> Error.expected_prim_array p
