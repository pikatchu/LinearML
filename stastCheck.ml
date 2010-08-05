open Utils
open Stast

type ty = 
  | ATany
  | ATval of type_prim
  | ATalgebric of ty IMap.t
  | ATrecord of ty IMap.t
  | ATprod of ty * ty
  | ATchoice of ty * ty

module TSet = Set.Make(struct
  type t = ty
  let compare = compare
end)

module Types = struct


  let rec print o = function
    | ATany -> o "_"
    | ATval ty -> print_type o ty

    | ATalgebric m -> 
	let l = clist_of_imap m in
	(match l with
	| [] -> o "_"
	| [x] -> print_variant o x
	| l -> o "(" ; print_list o print_variant " | " l ; o ")")

    | ATrecord m -> 
	let l = clist_of_imap m in
	o "{" ; print_list o print_field " ; " l ; o "}"

    | ATprod (t1, t2) ->
	print o t1 ; o " * " ; print o t2

    | ATchoice (t1, t2) ->
	print o t1 ; o " || " ; print o t2

  and print_type o = function
    | Tunit -> o "()"
    | Tbool -> o "bool"
    | Tchar -> o "char"
    | Tint32 -> o "int32"
    | Tfloat -> o "float"

  and print_variant o (id, ty) = 
    let id = Ident.to_string id in
    o id ; o " (" ; print o ty ; o ")"

  and print_field o (id, ty) = 
    o (Ident.to_string id) ; o " = " ; print o ty

  let print ty = 
    let o = output_string stdout in
    print o ty ;
    o "\n"
      
  let variant x t = 
      ATalgebric (IMap.add x t IMap.empty)

  let rec break acc t = 
    match t with
    | ATany 
    | ATval _ as x -> x :: acc
    | ATalgebric m -> 
	IMap.fold (fun x t acc ->
	  let l = break [] t in
	  List.fold_right (fun t acc ->
	    variant x t :: acc) l acc) m acc

    | ATrecord m -> 
	let ml = IMap.fold (fun x t acc -> 
	  IMap.add x (break [] t) acc) m IMap.empty in
	let ml = IMap.fold (fun x tl acc -> (x, tl) :: acc) ml [] in
	let rl = break_record ml in
	List.fold_right (fun x acc -> ATrecord x :: acc) rl acc
      
    | ATprod (t1, t2) -> 
	let l1 = break [] t1 in
	let l2 = break [] t2 in
	List.fold_right (fun t1 acc ->
	  List.fold_right (fun t2 acc ->
	    ATprod (t1, t2) :: acc) l2 acc) l1 acc

    | ATchoice (t1, t2) -> 
	let acc = break acc t1 in
	break acc t2

  and break_record ml =
    match ml with
    | [] -> assert false
    | [x, tl] -> List.map (fun t -> IMap.add x t IMap.empty) tl
    | (x, tl) :: rest -> 
	let l = break_record rest in
	List.fold_right (fun ml acc ->
	  List.fold_right (fun t acc ->
	  IMap.add x t ml :: acc) tl acc) 
	  l []

  let rec flatten t = 
    match t with
    | ATprod (ATalgebric m, tl) ->
	let m = IMap.map (fun ty -> ATprod (ty, tl)) m in
	let t = ATalgebric m in
	flatten t

    | ATany
    | ATval _ as x -> x
    | ATalgebric m -> ATalgebric (IMap.map flatten m)
    | ATrecord m -> ATrecord (IMap.map flatten m)
    | ATprod (t1, t2) -> ATprod (flatten t1, flatten t2)
    | ATchoice _ -> assert false

  let rec add t1 t2 = 
    match t1, t2 with
    | ATany, _ -> false, ATany
    | ATval _, ATany -> true, ATany
    | ATval x, ATval _ -> false, ATval x

    | ATalgebric m1, ATalgebric m2 -> 
	let ch, m = add_map false m1 m2 in
	ch, ATalgebric m

    | ATrecord m1, ATrecord m2 -> 
	let ch, m = add_map false m1 m2 in
	ch, ATrecord m

    | ATprod (t1, t2), ATprod (t3, t4) -> 
	let c1, t1 = add t1 t3 in
	let c2, t2 = add t2 t4 in
	c1 || c2, ATprod (t1, t2)

    | _ -> assert false

  and add_map ch m1 m2 = 
    IMap.fold (fun x t1 (changed, acc) -> 
      try
	let t2 = IMap.find x m2 in
	let ch, t = add t1 t2 in
	changed || ch, IMap.add x t acc
      with Not_found -> changed, acc) m2 (ch, m1)

  let rec general t1 t2 = 
    match t1, t2 with
    | ATany, t | t, ATany -> t
    | ATval x, ATval _ -> ATval x
    | ATchoice (t1, t2), x | x, ATchoice (t1, t2) -> 
	general (general t1 t2) x

    | ATalgebric m1, ATalgebric m2 ->
	ATalgebric (general_map m1 m2)

    | ATrecord m1, ATrecord m2 -> 
	ATrecord (general_map m1 m2)

    | ATprod (t1, t2), ATprod (t3, t4) ->
	ATprod (general t1 t3, general t2 t4)
    | _ -> assert false

  and general_map m1 m2 = 
    let m = 
      IMap.fold (fun x t1 m ->
	try 
	  let t2 = IMap.find x m2 in
	  IMap.add x (general t1 t2) m
	with Not_found -> m) m1 m1 in
    IMap.fold (fun x t m ->
      if IMap.mem x m
      then m
      else IMap.add x t m) m2 m

  let rec expand ty gt = 
    match ty, gt with
    | ATany, t -> t
    | ATval x, _ -> ATval x
    | ATalgebric m, ATalgebric gm -> 
	ATalgebric (expand_map m gm)
    | ATrecord m, ATrecord gm -> 
	ATrecord (expand_record m gm)
    | ATprod (t1, t2), ATprod (t3, t4) -> 
	ATprod (expand t1 t3, expand t2 t4)
    | _ -> assert false

  and expand_map m gm =
    IMap.fold (fun x t m ->
      try IMap.add x (expand t (IMap.find x gm)) m
      with Not_found -> assert false) m m

  and expand_record m gm = 
    let m = expand_map m gm in
    IMap.fold (fun x t m ->
      if not (IMap.mem x m)
      then 
	let t = match t with 
	| ATval _ -> ATany 
	| _ -> t in
	IMap.add x t m
      else m) gm m

  let expand gt ty = expand ty gt

  let add t ty =
    let tyl = break [] (flatten ty) in
    List.fold_left (fun (ch, t) ty -> 
      let ch2, t = add t ty in
      ch || ch2, t) (false, t) tyl
end

module CheckRecord = struct

  let rec rest m pfl = 
    List.fold_left (fun acc (_, pf) ->
      match pf with
      | PField ((_, x), _) -> IMap.remove x acc
      | _ -> acc) m pfl 

  let rec find_id = function
    | [] -> None
    | ((p, PFany) | (p, PFid _)) :: _ -> Some p
    | _ :: rl -> find_id rl

  let forgot_fields p rest = 
    let fdl = IMap.fold (fun x _ acc -> x :: acc) rest [] in
    let fdl = List.map Ident.to_string fdl in
    Error.forgot_fields p fdl

  let record p m pfl =
    let rest = rest m pfl in
    let id = find_id pfl in
    match id, IMap.is_empty rest with
    | None, true -> ()
    | None, false -> forgot_fields p rest
    | Some p, true -> Error.useless p
    | Some _, false -> ()
end

module PatGeneral = struct
  open Types

  let rec pat t ptl = 
    match List.map (pat_tuple t) ptl with
    | [] -> assert false
    | t :: tl -> List.fold_left Types.general t tl

  and pat_tuple t (_, pel) = pat_tuple_ t pel
  and pat_tuple_ t = function
    | [] -> assert false
    | [x] -> pat_el t x
    | x :: rl -> ATprod (pat_el t x, pat_tuple_ t rl)

  and pat_el t (ty, p) =
    match p with
    | Pany -> ATany
    | Pid _ -> ATany
    | Pvalue v -> ATval (value v)
    | Pvariant (_, (_, [])) -> type_expr t ty
    | Pvariant ((_, x), p) -> variant t ty x p
    | Precord pfl -> 
	let p, _ as ty = ty in
	let ty = type_expr t ty in
	let m = match ty with ATrecord m -> m | _ -> assert false in
	CheckRecord.record p m pfl ;
	let m = List.fold_left (field t) m pfl in
	ATrecord m

  and variant t ty x (_, p) =
    match type_expr t ty with
    | ATalgebric m -> ATalgebric (IMap.add x (pat t p) m)
    | _ -> assert false

  and field t m (_, pf) = 
    match pf with
    | PFany
    | PFid _ -> m
    | PField ((_, x), (_, p)) -> IMap.add x (pat t p) m

  and value = function
    | Eunit -> Tunit
    | Ebool _ -> Tbool
    | Eint _ -> Tint32 
    | Efloat _ -> Tfloat
    | Echar _ -> Tchar 
    | Estring _ -> failwith "TODO Estring"

  and type_expr t (_, ty) = 
    match ty with
    | Tprim _
    | Tany
    | Tfun _
    | Tvar _ -> assert false
    | Tid (_, x)
    | Tapply ((_, x), _) -> try IMap.find x t with Not_found -> assert false
end

module Pat = struct
  open Types
  
  let rec pat ptl = pat_choice ptl
  and pat_choice = function
    | [] -> assert false
    | [x] -> pat_tuple x
    | x :: rl -> ATchoice (pat_tuple x, pat_choice rl)

  and pat_tuple (_, pel) = pat_tuple_ pel 
  and pat_tuple_ = function
    | [] -> assert false
    | [x] -> pat_el x
    | x :: rl -> ATprod (pat_el x, pat_tuple_ rl)

  and pat_el (_, p) = pat_ p
  and pat_ = function
    | Pany
    | Pid _ -> ATany
    | Pvalue x -> ATval (PatGeneral.value x)

    | Pvariant ((_, x), (_, [])) ->
	ATalgebric (IMap.add x ATany IMap.empty)

    | Pvariant ((_, x), (_, p)) -> 
	ATalgebric (IMap.add x (pat p) IMap.empty)

    | Precord pfl -> 
	let m = List.fold_left pat_field IMap.empty pfl in
	ATrecord m

  and pat_field acc (_, pf) = pat_field_ acc pf
  and pat_field_ acc = function
    | PFany 
    | PFid _ -> acc
    | PField ((_, x), (_, p)) -> IMap.add x (pat p) acc

end

module Env = struct
  open Types

  let rec make mdl = 
    List.fold_left module_ IMap.empty mdl

  and module_ t md = 
    List.fold_left decl t md.md_decls 

  and decl t = function
    | Dalgebric td -> 
	let m = tdef t td in
	IMap.add (snd td.td_id) (ATalgebric m) t

    | Drecord td ->
	let m = tdef t td in
	IMap.add (snd td.td_id) (ATrecord m) t

    | Dval _ -> t
	
  and tdef t td = 
    IMap.map (fun _ -> ATany) td.td_map
end

let rec program mdl = 
  let t = Env.make mdl in
  List.iter (module_ t) mdl 

and module_ t md =
  List.iter (def t) md.md_defs

and def t (x, p, e) = 
  pat t [p] ;
  tuple t e 

and pat t pl = 
  let pl = List.fold_right (fun (_, l) acc -> l @ acc) pl [] in
  let gty = PatGeneral.pat t pl in
  let gtyl = Types.break [] gty in
  let gtys = List.fold_right TSet.add gtyl TSet.empty in
  let ty = Pat.pat pl in
  let acc = Types.break [] ty in
  let acc = List.rev acc in
  let acc = List.map (Types.expand gty) acc in
  let sty = List.fold_left pat_tuple TSet.empty acc in 
  let rest = TSet.diff gtys sty in
  if TSet.is_empty rest
  then ()
  else (Printf.printf "Not_exhaustive\n" ;
	  List.iter Types.print (TSet.elements rest)) ;
  Printf.printf "\n"

and pat_tuple sty ty =
  let tyl = Types.break [] ty in
  let ch, sty = List.fold_left (fun (ch, sty) ty ->
    if TSet.mem ty sty
    then ch, sty
    else true, TSet.add ty sty) (false, sty) tyl in
  if not ch
  then (Printf.printf "Unused branch" ; Types.print ty ; exit 2)
  else sty

(*and pat_ t p = 
  let gty = PatGeneral.pat t p in 
  let ty = Pat.pat p in
  let acc = Types.break [] ty in
  let acc = List.map (Types.expand gty) acc in
  List.iter Types.print acc ;
  Printf.printf "\n"
*)
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
      let p = List.fold_right (fun (p, _) acc -> p :: acc) al [] in
      pat t p

  | Elet (p, e1, e2) -> 
      pat t [p] ;
      tuple t e1 ;
      tuple t e2 

  | Eif (e1, e2, e3) -> 
      expr t e1 ;
      tuple t e2 ;
      tuple t e3

  | Eapply (_, e) -> tuple t e

and field t (_, e) = tuple t e
and action t (_, e) = tuple t e
