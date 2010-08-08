open Utils
open Stast

type ty = 
  | ATempty
  | ATany
  | ATalgebric of (Ident.t * int) list * ty option IMap.t
  | ATrecord of ty IMap.t
  | ATprod of ty list
  | ATchoice of ty list

let rec has_any = function
  | ATempty -> false 
  | ATany -> true
  | ATalgebric (_, m) -> 
      IMap.fold (fun _ t acc -> 
	match t with
	| None -> acc
	| Some t -> has_any t || acc) m false

  | ATrecord m -> 
      IMap.fold (fun _ t acc -> 
	has_any t || acc) m false

  | ATchoice tyl
  | ATprod tyl -> 
      List.fold_left (fun acc t ->
	acc || has_any t) false tyl


module Compare = struct

  let rec type_ t1 t2 = 
    match t1, t2 with
    | ATempty, ATempty -> 0
    | ATempty, _ -> -1
    | _, ATempty -> 1

    | ATalgebric (_, m1), ATalgebric (_, m2) -> 
	IMap.compare type_opt m1 m2
    | ATalgebric _, _ -> -1
    | _, ATalgebric _ -> 1

    | ATrecord m1, ATrecord m2 -> 
	IMap.compare type_ m1 m2
    | ATrecord _, _ -> -1
    | _, ATrecord _ -> 1

    | ATprod tyl1, ATprod tyl2 -> 
	List.fold_left2 (fun c x y ->
	  if c = 0
	  then type_ x y
	  else c) 0 tyl1 tyl2

    | ATany, ATany -> 0
    | ATany, _ -> -1
    | _, ATany -> 1 

(*    | ATprod _, _ -> -1
    | _, ATprod _ -> 1 *)
    | _ -> assert false
	

  and type_opt ty1 ty2 = 
    match ty1, ty2 with
    | None, None -> 0
    | Some x1, Some x2 -> type_ x1 x2
    | _ -> assert false
end

module Print = struct

  let rec type_ o = function
    | ATempty -> o "0"

    | ATany -> o "_"

    | ATalgebric (_, m) -> 
	let l = clist_of_imap m in
	(match l with
	| [] -> o "_"
	| [x] -> variant o x
	| l -> o "(" ; print_list o variant " | " l ; o ")")

    | ATrecord m -> 
	let l = clist_of_imap m in
	o "{" ; print_list o field " ; " l ; o "}"

    | ATprod tl -> 
	o "(" ; print_list o type_ ", " tl ; o ")"

    | ATchoice tl -> 
	print_list o type_ " || " tl

  and variant o (id, ty) = 
    let id = Ident.to_string id in
    match ty with
    | None -> o id
    | Some ty -> 
	o id ; o " " ; type_ o ty

  and field o (id, ty) = 
    o (Ident.to_string id) ; o " = " ; type_ o ty

  let type_ ty = 
    let o = output_string stdout in
    type_ o ty ;
    o "\n"

end

module Includes = struct
 
  let rec type_ ty1 ty2 = 
    match ty1, ty2 with
    | _, ATempty -> true
    | ATempty, _ -> false
    | ATany, _ -> true
    | _, ATany -> false
    | ATalgebric (_, m1), ATalgebric (_, m2) -> 
	IMap.fold (fun x t acc ->
	  try type_opt (IMap.find x m1) t && acc
	  with Not_found -> false) m2 true
	    
    | ATrecord m1, ATrecord m2 ->
	IMap.fold (fun x t acc ->
	  try type_ (IMap.find x m1) t && acc
	  with Not_found -> false) m2 true

    | ATprod tyl1, ATprod tyl2 -> 
	List.fold_left2 (fun acc x1 x2 -> 
	  acc && type_ x1 x2) true tyl1 tyl2

    | _ -> assert false

  and type_opt ty1 ty2 = 
    match ty1, ty2 with
    | None, None -> true
    | Some ty1, Some ty2 -> type_ ty1 ty2
    | _ -> assert false
end

module Break = struct

  let variant idl x t = 
    ATalgebric (idl, (IMap.add x t IMap.empty))

  let rec type_ acc t = 
    match t with
    | ATempty 
    | ATany as x -> x :: acc
    | ATalgebric (idl, m) -> 
	IMap.fold (fun x t acc ->
	  match t with
	  | None -> variant idl x t :: acc
	  | Some t -> 
	      let l = type_ [] t in
	      List.fold_right (fun t acc ->
		variant idl x (Some t) :: acc) l acc) m acc

    | ATrecord m -> 
	let ml = IMap.fold (fun x t acc -> 
	  IMap.add x (type_ [] t) acc) m IMap.empty in
	let ml = IMap.fold (fun x tl acc -> (x, tl) :: acc) ml [] in
	let rl = record ml in
	List.fold_right (fun x acc -> ATrecord x :: acc) rl acc
      
    | ATprod tl -> 
	let tll = List.map (type_ []) tl in
	let tll = prod tll in
	List.fold_right (fun x acc -> ATprod x :: acc) tll acc

    | ATchoice tyl -> List.fold_left type_ acc tyl


  and prod = function
    | [] -> assert false
    | [tl] -> List.map (fun x -> [x]) tl
    | tl :: rl ->
	let sub = prod rl in
	List.fold_right (fun x acc -> 
	  List.fold_right (fun l acc -> (x :: l) :: acc) sub acc)
	  tl
	  []

  and record ml =
    match ml with
    | [] -> assert false
    | [x, tl] -> List.map (fun t -> IMap.add x t IMap.empty) tl
    | (x, tl) :: rest -> 
	let l = record rest in
	List.fold_right (fun ml acc ->
	  List.fold_right (fun t acc ->
	  IMap.add x t ml :: acc) tl acc) 
	  l []
end

module Mergeable = struct

  let compare x y = Compare.type_ x y = 0

(* Two tuples can be merged if all their elements are equal except for *)
(* one or less *)
  let rec type_ ty1 ty2 = 
    match ty1, ty2 with
    | ATempty, _ | _, ATempty -> assert false
    | _, ATany -> true
    | ATany, _ -> false
    | ATrecord m1, ATrecord m2 -> 
	let l1 = list_of_imap m1 in
	let l2 = list_of_imap m2 in
	type_list l1 l2

    | ATalgebric (_, m1), ATalgebric (_, m2) -> 
	let l1, l2 = IMap.fold (fun x t1 (acc1, acc2) ->
	  try t1 :: acc1, IMap.find x m2 :: acc2 
	  with Not_found -> acc1, acc2) m1 ([], []) in
	type_list (filter_opt l1) (filter_opt l2)

    | ATprod tyl1, ATprod tyl2 -> type_list tyl1 tyl2
    | _ -> false

  and type_list tyl1 tyl2 = 
    let acc = List.fold_left2 (fun acc x y -> 
      if y = ATany 
      then acc
      else if x = ATany
      then [x, x ; x, x]
      else if compare x y 
      then acc 
      else (x, y) :: acc) [] tyl1 tyl2 in
    (match acc with
    | [] -> true
    | [x, y] -> type_ x y
    | _ -> false)      

end

module Plus = struct

  let reduce_algebric l m = 
    try List.iter (fun (x, _) ->
      match IMap.find x m with
      | None -> ()
      | Some ATany -> ()
      | _ -> raise Not_found) l ;
      ATany
    with Not_found -> ATalgebric (l, m)

  let reduce_record m = 
    try IMap.iter (fun _ t ->
      if t <> ATany then raise Exit) m ;
      ATany 
    with Exit -> ATrecord m

  let reduce_prod l = 
    try List.iter (fun t ->
      if t <> ATany then raise Exit) l ;
      ATany
    with Exit -> ATprod l

  let rec plus n ty1 ty2 = 
    match ty1, ty2 with
    | ATempty, _ | _, ATempty -> assert false
    | ATany, _ -> ATany
    | t, ATany -> t
    | ATalgebric (x, m1), ATalgebric (_, m2) ->
	reduce_algebric x (plus_algebric n m1 m2)
	  
    | ATrecord m1, ATrecord m2 -> 
	reduce_record (plus_record n m1 m2)

    | ATprod tyl1, ATprod tyl2 -> 
	reduce_prod (List.map2 (plus n) tyl1 tyl2)

    | _ -> assert false

  and plus_opt n ty1 ty2 =
    match ty1, ty2 with
    | None, None -> None
    | Some ty1, Some ty2 -> Some (plus n ty1 ty2)
    | _ -> assert false

  and plus_algebric n m1 m2 = 
    IMap.fold (fun x t2 acc -> 
      try 
	let t = plus_opt n (IMap.find x m1) t2 in
	IMap.add x t acc
      with Not_found -> IMap.add x t2 acc) m2 m1

  and plus_record n m1 m2 = 
    IMap.fold (fun x t2 acc -> 
      let t1 = IMap.find x m1 in
      IMap.add x (plus n t1 t2) acc) m2 m1

  let plus ty1 ty2 = 
    if Mergeable.type_ ty1 ty2
    then
      let ty = plus 0 ty1 ty2 in
      Some ty
    else None

  let rec add_list acc x l = 
    match l with
    | [] -> acc @ [x]
    | y :: rl ->
	if Includes.type_ y x
	then acc @ (y :: rl)
	else match plus y x with
	| None -> add_list (y :: acc) x rl
	| Some x' -> 
	    if Includes.type_ x' x
	    then add_list [] x' (acc @ rl)
	    else 
	      let l = add_list acc x rl in
	      add_list [] x' (acc @ l)

  let rec integrate l (c, acc) x = 
    match l with
    | [] -> true, x :: acc
    | y :: rl -> 
	if Includes.type_ y x
	then c, acc
	else match plus y x with
	| None -> integrate rl (c, acc) x
	| Some _ -> true, add_list [] x acc

  let normalize l = 
    let l = List.fold_left Break.type_ [] l in
    let l = List.sort Compare.type_ l in
    List.fold_left (fun acc x -> 
      add_list [] x acc) [] l

  let add_case acc p t = 
    let acc = 
      if has_any t
      then normalize acc
      else acc in
    let l = Break.type_ [] t in
    let used, acc = List.fold_left (fun (c, acc) x -> 
      integrate acc (c, acc) x) (false, acc) l in
    if used
    then (acc)
    else (Error.unused p)
	    
end
    
module Pat = struct
  
  let rec pat t ptl = ATchoice (List.map (pat_tuple t) ptl)

  and pat_tuple t (_, pel) = 
    match pel with 
    | [x] -> pat_el t x
    | _ -> Plus.reduce_prod (List.map (pat_el t) pel)

  and pat_el t (ty, p) = pat_ t ty p

  and pat_ t ty = function
    | Pany
    | Pid _ -> ATany
    | Pvalue _ -> failwith "TODO"

    | Pvariant ((_, x), (_, [])) ->
	ATalgebric (type_expr t ty, IMap.add x None IMap.empty)

    | Pvariant ((_, x), (_, p)) -> 
	ATalgebric (type_expr t ty, IMap.add x (Some (pat t p)) IMap.empty)

    | Precord pfl -> 
	let m = List.fold_left (pat_field t) IMap.empty pfl in
	ATrecord m

  and pat_field t acc (_, pf) = pat_field_ t acc pf
  and pat_field_ t acc = function
    | PFany 
    | PFid _ -> acc
    | PField ((_, x), (_, p)) -> IMap.add x (pat t p) acc

  and type_expr t (_, ty) = 
    match ty with
    | Tprim _
    | Tany
    | Tfun _
    | Tvar _ -> assert false
    | Tid (_, x)
    | Tapply ((_, x), _) -> try IMap.find x t with Not_found -> assert false

  and value = function
    | Eunit -> Tunit
    | Ebool _ -> Tbool
    | Eint _ -> Tint32 
    | Efloat _ -> Tfloat
    | Echar _ -> Tchar 
    | Estring _ -> failwith "TODO Estring"

end

module Env = struct

  let rec make mdl = 
    List.fold_left module_ IMap.empty mdl

  and module_ t md = 
    List.fold_left decl t md.md_decls 

  and decl t = function
    | Dalgebric td -> 
	let m = talgebric t td in
	IMap.add (snd td.td_id) m t
    | _ -> t
	
  and talgebric t td = 
    IMap.fold (fun x t acc -> (x, arity t) :: acc) td.td_map []

  and arity (_, (_, l)) = List.length l

end

let rec program mdl = 
  let t = Env.make mdl in
  List.iter (module_ t) mdl 

and module_ t md =
  List.iter (def t) md.md_defs

and def t (x, p, e) = 
  ignore (pat t [] p) ;
  tuple t e 

and pat t acc ((p, _), pl) = 
  let tl = Pat.pat t pl in
  let acc = Plus.add_case acc p tl in
  acc

and tuple t (_, tpl) = List.iter (tuple_pos t) tpl 
and tuple_pos t (_, e) = expr_ t e
and expr t (_, e) = expr_ t e
and expr_ t = function
  | Eid _ -> ()
  | Evalue _ -> ()
  | Evariant (_, e) -> tuple t e
  | Ebinop (_, e1, e2) -> expr t e1 ; expr t e2
  | Euop (_, e) -> expr t e
  | Erecord fdl -> List.iter (field t) fdl
  | Efield (e, _) -> expr t e
  | Ematch (_, al) -> 
      let p = List.fold_left (fun acc (p, _) -> pat t acc p) [] al in
      o "TOTAL\n" ;
      List.iter Print.type_ p ;
      ignore p

  | Elet (p, e1, e2) -> 
      ignore (pat t [] p) ;
      tuple t e1 ;
      tuple t e2 

  | Eif (e1, e2, e3) -> 
      expr t e1 ;
      tuple t e2 ;
      tuple t e3

  | Eapply (_, e) -> tuple t e

and field t (_, e) = tuple t e
and action t (_, e) = tuple t e
