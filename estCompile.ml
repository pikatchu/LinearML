open Utils
open Est

let rec program mdl = 
  List.rev_map module_ mdl

and module_ md = 
  { md with md_defs = List.rev_map def md.md_defs }

and def df = 
  let bls = List.fold_left (
    fun acc bl ->
      IMap.add bl.bl_id bl acc
   ) IMap.empty df.df_body in
  let bll = block bls [] (List.hd df.df_body) in
  let _, bll = List.fold_left (
    fun (s, acc) x ->
      if ISet.mem x.bl_id s 
      then s, acc
      else ISet.add x.bl_id s, x :: acc
   ) (ISet.empty, []) bll in 
  let bll = List.rev bll in
  let df = { df with df_body = bll } in
   let df = EstOptim.def df in  
  df

and block bls acc bl = 
  let blocks, ret, eqs = equation bls bl.bl_ret acc bl.bl_eqs in
  { bl with 
    bl_eqs = eqs ; 
    bl_ret = ret ;
  } :: blocks

and equation bls ret acc eq = 
  match eq with 
  | [] -> acc, ret, []
  | (idl, Eif (c, l1, l2)) :: rl -> 
      let acc, ret, rl = equation bls ret acc rl in
      let b1 = IMap.find l1 bls in
      let b2 = IMap.find l2 bls in
      let btarget = Ident.tmp() in
      let rl1 = match b1.bl_ret with Lreturn l -> l | _ -> assert false in
      let rl2 = match b2.bl_ret with Lreturn l -> l | _ -> assert false in
      let phil = make_phi idl b1.bl_id rl1 b2.bl_id rl2 in
      let b3 = {
	bl_id = btarget ;
	bl_phi = phil ;
	bl_ret = ret ;
	bl_eqs = rl ;
      } in
      let acc = b3 :: acc in
      let b2 = { b2 with bl_ret = Jump btarget } in
      let acc = block bls acc b2 in
      let b1 = { b1 with bl_ret = Jump btarget } in
      let acc = block bls acc b1 in
      acc, If (c, l1, l2), []
  | (idl, Ecall lbl) :: rl -> 
      let acc, ret, eqs = equation bls ret acc rl in
      let b = IMap.find lbl bls in
      let idl' = match b.bl_ret with Lreturn l -> l | _ -> assert false in
      let eqs = List.fold_right2 (
	fun x1 (_, x2) acc ->
	  ([x1], Eid x2) :: acc
       ) idl idl' eqs in
      let btarget = Ident.tmp() in
      let rest = { 
	bl_id = btarget ;
	bl_phi = [] ;
	bl_eqs = eqs ; 
	bl_ret = ret ;
      } in
      let acc = rest :: acc in
      let b = { b with bl_ret = Jump btarget } in
      let acc = block bls acc b in
      acc, Jump lbl, []
  | (idl, Ematch (cl, al)) :: rl -> 
      let acc, ret, rl = equation bls ret acc rl in
      let al = List.map (
	function (p, Ecall l) -> p, l | _ -> assert false
       ) al in
      let bl = List.map (fun (_, l) -> l) al in
      let bl = List.map (fun x -> IMap.find x bls) bl in
      let btarget = Ident.tmp() in
      let retll = List.map (fun b -> 
	match b.bl_ret with 
	| Lreturn l -> List.map (fun (_, x) -> x, b.bl_id) l
	| _ -> assert false) bl in
      let phil = make_phil idl retll in 
      let b3 = {
	bl_id = btarget ;
	bl_phi = phil ;
	bl_ret = ret ;
	bl_eqs = rl ;
      } in
      let acc = b3 :: acc in
      let acc = List.fold_left (
	fun acc b ->
	  let b = { b with bl_ret = Jump btarget } in
	  block bls acc b
       ) acc bl in
      acc, Match (cl, al), []
  | x :: rl ->
      let acc, ret, rl = equation bls ret acc rl in
      acc, ret, x :: rl

and make_phi l bl1 l1 bl2 l2 = 
  match l, l1, l2 with
  | [], [], [] -> []
  | [], _, _
  | _, [], _
  | _, _, [] -> assert false
  | (ty, x) :: rl, (_, x1) :: rl1, (_, x2) :: rl2 ->
      let phi1 = x1, bl1 in
      let phi2 = x2, bl2 in
      (x, ty, [phi1 ; phi2]) :: make_phi rl bl1 rl1 bl2 rl2

and make_phil l bl = 
  match l with
  | [] -> []
  | (ty, x) :: rl -> 
      let l', bl = List.fold_right (
	fun l (acc1, acc2) ->
	  match l with
	  | [] -> assert false
	  | x :: rl -> x :: acc1, rl :: acc2
       ) bl ([], []) in
      let phil = make_phil rl bl in
      (x, ty, l') :: phil

(*and expr = 
  | Eid of id
  | Evalue of Ist.value
  | Evariant of id * ty_idl
  | Ebinop of Ast.bop * ty_id * ty_id
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
