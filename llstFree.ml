open Utils


module Usage = struct
  open Llst

  let ty_id acc (_, x) = ISet.add x acc 
  let ty_idl acc l = List.fold_left ty_id acc l
  
  let rec block bl = 
    let acc = ISet.empty in
    let acc = List.fold_left phi acc bl.bl_phi in
    let acc = List.fold_left equation acc bl.bl_eqs in
    let acc = ret acc bl.bl_ret in
    acc

  and ret acc = function
    | Return (_, l) -> ty_idl acc l
    | Jump _ -> acc
    | Switch (x, _, _)
    | If (x, _, _) -> 
	let acc = ty_id acc x in
	acc

  and phi acc (x, _, l) = 
    let acc = ISet.add x acc in
    List.fold_left (
    fun acc (x, _) -> ISet.add x acc
   ) acc l

  and equation acc (_, e) = 
    let acc = expr acc e in
    acc

  and expr acc = function
    | Enull -> acc
    | Egettag x 
    | Egetargs x 
    | Eproj (x, _) 
    | Efree x
    | Eid x 
    | Eis_null x -> ISet.add (snd x) acc
    | Eptr_of_int x
    | Eint_of_ptr x -> ISet.add x acc
    | Evalue _ -> acc
    | Ebinop (_, x1, x2) -> 
	let acc = ty_id acc x1 in
	let acc = ty_id acc x2 in
	acc
    | Euop (_, x) -> ty_id acc x 
    | Efield (x, _) -> ty_id acc x 
    | Eapply (_, _, _, l) -> ty_idl acc l
    | Etuple (v, l) -> 
	let acc = match v with None -> acc | Some v -> ty_id acc v in
	let acc = List.fold_left (
	  fun acc (_, x) -> ty_id acc x
	 ) acc l in
	acc
end

open Llst

type work = 
  | Insert_free of Llst.label * Llst.ty_id
  | Remove_free of Llst.label * Llst.id

let debug_todo todo = 
  List.iter (
  function
    | Remove_free (lbl, id) -> 
	Printf.printf "Remove %s %s\n" (Ident.debug lbl) (Ident.debug id)
    | Insert_free (lbl, (_, id)) -> 
	Printf.printf "Insert %s %s\n" (Ident.debug lbl) (Ident.debug id)
 ) todo

let rec cont acc = function
  | Return _ -> acc
  | Jump lbl -> ISet.add lbl acc
  | If (_, lbl1, lbl2) -> ISet.add lbl1 (ISet.add lbl2 acc)
  | Switch (_, al, _) -> 
      let acc = List.fold_left (
	fun acc (_, lbl) -> ISet.add lbl acc
       ) acc al in
      acc

(* TODO memoize *)
let rec is_used bls usage x lbl = 
  let bl = IMap.find lbl bls in
  let uses = IMap.find bl.bl_id usage in
  ISet.mem x uses || 
  is_used_ret bls usage x bl
    
and is_used_ret bls usage x bl =
  ISet.fold 
    (fun lbl acc -> acc || is_used bls usage x lbl) 
    (cont ISet.empty bl.bl_ret)
    false

let is_branching bl = 
  match bl.bl_ret with
  | If _ | Switch _ -> true
  | _ -> false

(* TODO memoize ? *)
let rec insert bls usage ((_, x) as id) acc lbl =
  if ISet.mem x (IMap.find lbl usage)
  then acc
  else 
(* In general it's better to push the frees within the branches *)
(* TODO do this optimization properly *)
    let bl = IMap.find lbl bls in
    if is_branching bl || is_used bls usage x lbl 
    then insert_ret bls usage id acc bl
    else Insert_free (lbl, id) :: acc

and insert_ret bls usage x acc bl =
  ISet.fold 
    (fun lbl acc -> insert bls usage x acc lbl) 
    (cont ISet.empty bl.bl_ret)
    acc

let rec program mdl = 
  List.map module_ mdl

and module_ md = 
  { md with md_defs = List.map def md.md_defs }

and def df = 
  let bls = List.fold_left (
    fun acc b -> IMap.add b.bl_id b acc
   ) IMap.empty df.df_body in
  let usages = List.fold_left (
    fun acc b -> IMap.add b.bl_id (Usage.block b) acc
   ) IMap.empty df.df_body in
  let todo = List.fold_left (block_todo bls usages) [] df.df_body in
  let rmset = List.fold_left (
    fun acc x -> 
      match x with 
      | Remove_free (_, x) -> ISet.add x acc
      | _ -> acc
   ) ISet.empty todo in
  let body = List.map (block_remove rmset) df.df_body in
  let ins = List.fold_left (
    fun acc x -> 
      match x with
      | Insert_free (lbl, x) ->
	  let xs = try IMap.find lbl acc with Not_found -> IMap.empty in
	  IMap.add lbl (IMap.add (snd x) x xs) acc
      | _ -> acc
   ) IMap.empty todo in
  let body = List.map (block_insert ins) body in 
  { df with df_body = body }

and block_todo bls usage acc bl = 
  List.fold_left (
  fun acc (_, e) -> 
    match e with
    | Efree x ->
	if is_branching bl || is_used_ret bls usage (snd x) bl 
	then
	  let acc = Remove_free (bl.bl_id, snd x) :: acc in
	  let acc = insert_ret bls usage x acc bl in
	  acc
	else acc
    | _ -> acc
 ) acc bl.bl_eqs  

and block_remove rm_set bl = 
  { bl with bl_eqs = List.filter (
    fun (_, e) -> 
      match e with
      | Efree (_, x) -> not (ISet.mem x rm_set)
      | _ -> true
   ) bl.bl_eqs }

and block_insert ins bl = 
  try 
    let xl = IMap.find bl.bl_id ins in
    let eqs = IMap.fold (fun _ v acc -> 
      let dummy = Llst.Tprim Tunit, Ident.tmp() in
      ([dummy], Llst.Efree v) :: acc) xl bl.bl_eqs in
    { bl with bl_eqs = eqs }
  with Not_found -> bl

