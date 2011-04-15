(*
Copyright (c) 2011, Julien Verlaguet
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:
1. Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the
distribution.

3. Neither the name of Julien Verlaguet nor the names of
contributors may be used to endorse or promote products derived
from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)
open Utils
open Stast

module Type = struct

  type t =
    | Safe
    | Fresh
    | Var          of Pos.t * Ident.t
    | Used         of Pos.t
    | As           of Ident.t * status
    | As_root      of Ident.t
    | As_child     of Ident.t
    | Obs          of ISet.t

  and kind = Child | Root
  and status = Pos.t option * Pos.t IMap.t * int

  let print = function
    | Safe -> o "Safe"
    | Fresh -> o "Fresh"
    | Var(_, x) -> o "Var " ; o (Ident.debug x)
    | Used _ -> o "Used"
    | As _ -> o "As"
    | As_root _ -> o "As_root"
    | As_child _ -> o "As_child"
    | Obs s -> o "Obs " ; ISet.iter (fun x -> o (Ident.to_string x)  ; o " ") s 
  
  let rec fresh_ty (p, ty) = fresh_ty_ p ty
  and fresh_ty_ p = function
    | Tprim _ -> Safe
    | Tapply ((_, x), _) when x = Naming.tobs -> Safe
    | _ -> Fresh
	  
  and fresh tyl = List.map fresh_ty tyl

  let rec unify ty1 ty2 = List.map2 unify_ ty1 ty2
  and unify_ ty1 ty2 = 
    match ty1, ty2 with
    | Obs x1, Obs x2 -> Obs (ISet.union x1 x2)
    | ty, _ -> ty

  let unify_list l =
    let hd, tl = hdtl l in
    List.fold_left unify hd tl

  let pany_table = Hashtbl.create 23 
  let make_pany p = 
    try Hashtbl.find pany_table p
    with Not_found -> 
      let id = (p, Ident.tmp()) in
      Hashtbl.add pany_table p id ;
      id
	  
end

module PatVars = struct

  type t = Pos.t IMap.t

  let rec pat (_, p) acc = 
    List.fold_right pat_tuple p acc

  and pat_tuple (_, pel) acc = 
    List.fold_right pat_el pel acc

  and pat_el (ty, p) acc = pat_ (fst ty) p acc
  and pat_ pos p acc = 
    match p with
    | Pany -> pat_ pos (Pid (Type.make_pany pos)) acc
    | Pid (p, x) -> IMap.add x p acc
    | Pvalue _ -> acc
    | Pvariant (_, p) -> pat p acc
    | Precord pfl -> List.fold_right (pat_field pos) pfl acc
    | Pas ((p, x), _) -> IMap.add x p acc

  and pat_field pos (_, pf) acc = pat_field_ pos pf acc
  and pat_field_ pos pf acc = 
    match pf with
    | PFany -> pat_field_ pos (PFid (Type.make_pany pos)) acc
    | PFid (p, x) -> IMap.add x p acc
    | PField (_, p) -> pat p acc

end


module Env: sig

  type t

  val empty: t
  val print: t -> unit
  val get: Ident.t -> t -> Type.t
  val bind: id -> Type.t -> t -> t
  val use: id -> t -> t * Type.t list
  val obs: id -> Type.t -> t -> t * Type.t list
  val partial: t -> Type.t list -> t * Type.t list
  val closure: t -> ISet.t -> t * Type.t list
  val push: t -> t
  val merge: t -> (Pos.t * t) list -> t
  val pop: t -> unit

end = struct
  open Type

  type t = Type.t IMap.t list

  let print t = 
    IMap.iter (
    fun x ty -> 
      Ident.print x; Type.print ty ; o "\n" ;
   ) (List.hd t)
      
  let empty = [IMap.empty]

  let add x ty = function
    | env :: rl ->
	IMap.add x ty env :: rl
    | _ -> assert false 

  let rec get x = function
    | [] -> Safe
    | env :: rl ->
	(try IMap.find x env with Not_found -> get x rl)

  let rec mem x = function
    | [] -> false
    | env :: rl ->
	IMap.mem x env || mem x rl

  let bind (p, x) ty t = 
    match ty with
    | Fresh
    | Used _ -> add x (Var (p, x)) t
    | ty -> add x ty t

  let rec obs (p, x) ty t = 
    match ty with
    | Used p' -> Error.already_used p p'
    | Var (p, y) -> 
	t, [Obs (ISet.singleton y)]
    | Obs y -> 
	t, [Obs (ISet.add x y)]
    | As (ptr, (left, right, _)) ->
	(match left with
	| None -> ()
	| Some p' -> Error.already_used p p') ;
	IMap.iter (fun _ p' -> Error.already_used p p') right ;
	obs (p, x) (get ptr t) t
    | As_root ptr -> obs (p, x) (get ptr t) t
    | As_child ptr -> obs (p, x) (get ptr t) t
    | x -> t, [x]

  let rec use (p, x) t = 
    let ty = get x t in
    match ty with
    | Safe
    | Fresh -> t, [ty] 
    | Var (_, x) -> 
	let t = add x (Used p) t in
	t, [Used p]
    | Used p' -> Error.already_used p p'
    | As_root ptr -> use_root p x ptr t
    | As_child ptr -> use_child p x ptr t
    | As _ -> assert false
    | Obs vset -> 
	ISet.iter (fun x -> use_obs p x t (get x t)) vset ;
	t, [ty]

  and use_root p x ptr t =
    match get ptr t with
    | As (up, (left, right, size)) -> 
	IMap.iter (fun x p' -> Error.already_used p p') right ;	  
	(match left with
	| None -> ()
	| Some p' -> Error.already_used p p') ;
	let left = Some p in
	let t = add ptr (As (up, (left, right, size))) t in
	use (p, up) t
    | _ -> assert false

  and use_child p x ptr t =
    match get ptr t with
    | As (up, (left, right, size)) ->
	(match left with
	| None -> ()
	| Some p' -> Error.already_used p p') ;
	(try 
	  let p' = IMap.find x right in
	  Error.already_used p p' 
	with Not_found ->
	  let right = IMap.add x p right in
	  let size = size - 1 in
	  let ty = As (up, (left, right, size)) in
	  let t = add ptr ty t in
	  if size = 0
	  then use (p, up) t
	  else t, [ty]
	)
    | Used p' -> Error.already_used p p'
    | _ -> use (p, x) t

  and use_obs p x t v = 
    match v with
    | Used p' -> Error.already_used p p'
    | As (root, (left, right, _)) ->
	(match left with
	| None -> ()
	| Some p' -> Error.already_used p p') ;
	IMap.iter (fun _ p' -> Error.already_used p p') right ;
	()
    | As_root ptr
    | As_child ptr -> use_obs p x t (get ptr t)
    | _ -> ()
    

  let push t = IMap.empty :: t
	
  let check_left (_, sub1) (bp, sub2) = 
    IMap.iter (
    fun x p -> 
      if IMap.mem x sub2 
      then ()
      else (Error.forgot_branch p bp)
   ) sub1

  let check sub1 sub2 = 
    check_left sub1 sub2 ;
    check_left sub2 sub1 ;
    sub1

  let just_used t (bp, sub) = 
    bp, IMap.fold (
    fun x ty acc ->
      match ty with
      | Used xp when mem x t -> 
	  IMap.add x xp acc
      | _ -> acc
   ) sub IMap.empty

  let check_unused (_, env) =
    IMap.iter (
    fun x ty ->
      match ty with
      | Var (p, _) -> Error.unused_variable p
      | _ -> ()
   ) env

  let merge t subl = 
    let subl = List.map (fun (p, t) -> p, List.hd t) subl in
    List.iter check_unused subl ;
    let subl = List.map (just_used t) subl in
    let hd, tl = hdtl subl in
    let subl = List.fold_left check hd tl in 
    IMap.fold (fun x p -> add x (Used p)) (snd subl) t

  let pop t = 
    check_unused (Pos.none, List.hd t)

  let closure t vset = 
    let env, t = hdtl t in
    t, [Obs vset]

  let partial t vl = 
    t, [Obs (
    List.fold_left (
    fun acc v ->
      match v with
      | Obs s -> ISet.union acc s 
      | _ -> acc
   ) ISet.empty vl 
   )]

end

module FreeObsVars = struct

  let rec id obs env t (p, x) = 
    match Env.get x env with
    | Type.As_root x -> id obs env t (p, x)
    | Type.As_child x -> id obs env t (p, x)
    | Type.As (x, _) -> id obs env t (p, x)
    | Type.Var _ when obs -> Error.esc_scope p
    | Type.Obs s -> ISet.add x (ISet.union s t)
    | _ -> t

  let rec obs_id obs env t (p, x) =
    match Env.get x env with
    | Type.As_root x -> obs_id obs env t (p, x)
    | Type.As_child x -> obs_id obs env t (p, x)
    | Type.As (x, _) -> obs_id obs env t (p, x)
    | Type.Obs s when not obs -> Error.esc_scope p
    | _ -> ISet.add x t
  
  let rec pat obs t (_, ptl) = 
    List.fold_left (pat_tuple obs) t ptl

  and pat_tuple obs t (_, pel) = 
    List.fold_left (pat_el obs) t pel

  and pat_el obs t (_, p) = pat_ obs t p

  and pat_ obs t = function
    | Pany		-> t
    | Pid (_, x)	-> ISet.remove x t 
    | Pvalue _		-> t
    | Pvariant (_, p)	-> pat obs t p 
    | Precord pfl	-> List.fold_left (pat_field obs) t pfl
    | Pas ((_, x), p)	-> ISet.remove x (pat obs t p)

  and pat_field obs t (_, pf) = pat_field_ obs t pf

  and pat_field_ obs t = function
    | PFany		-> t
    | PFid (_, x)	-> ISet.remove x t
    | PField (_, p)	-> pat obs t p

  and tuple obs env t (_, tpl) = 
    List.fold_left (tuple_pos obs env) t tpl
    
  and tuple_pos obs env t (_, e) = expr_ obs env t e
  and expr obs env t (ty, e) = expr_ obs env t e
  and expr_ obs env t = function
    | Eid x -> id obs env t x
    | Evalue _ -> t
    | Evariant (_, e) -> tuple obs env t e
    | Ebinop (_, e1, e2) -> 
	let t = expr obs env t e1 in
	let t = expr obs env t e2 in
	t
    | Euop (_, e) -> expr obs env t e
    | Erecord fdl -> List.fold_left (field obs env) t fdl 
    | Ewith (e, fdl) -> 
	let t = List.fold_left (field obs env) t fdl in
	expr obs env t e
    | Efield (e, _) -> expr obs env t e
    | Ematch (e, al) -> 
	let t = List.fold_left (action obs env) t al in
	tuple obs env t e
    | Elet (p, e1, e2) ->
	let t = tuple obs env t e1 in
	let t = pat obs t p in
	let t = tuple obs env t e2 in
	t
    | Eif (c, e1, e2) ->
	let t = tuple obs env t e1 in
	let t = tuple obs env t e2 in
	expr obs env t c
    | Eapply (_, _, x, e) -> 
	let t = id obs env t x in
	let t = tuple obs env t e in
	t
    | Eseq (e1, e2) -> 
	let t = expr obs env t e1 in
	let t = tuple obs env t e2 in
	t
    | Eobs x -> obs_id obs env t x
    | Efree _ -> t
    | Epartial (f, e) -> 
	let t = expr obs env t f in
	let t = tuple obs env t e in
	t
    | Efun (_, _, pel, e) ->
	let t = tuple obs env t e in
	let t = List.fold_left (pat_el obs) t pel in
	t

  and field obs env t (_, e) = tuple obs env t e

  and action obs env t (p, e) =
    let t = tuple obs env t e in
    let t = pat obs t p in
    t

end

let rec program mdl = 
  List.iter module_ mdl

and module_ md = 
  List.iter def md.md_defs
  
and def (_, _, ((tyl, _) as p), e) = 
  let vl = Type.fresh (snd tyl) in
  let t = pat Env.empty p vl in
  let t, _ = tuple t e in
  Env.pop t ;
  Hashtbl.clear Type.pany_table

and pat t (_, pl) vl = 
  List.fold_left (pat_tuple vl) t pl

and pat_tuple vl t (_, pel) = 
  List.fold_left2 pat_el t pel vl 

and pat_el t (ty, p) v = 
  pat_ t ty p v

and pat_ t ty p v = 
  match p with
  | Pany -> 
      let v = match ty with _, Tprim _ -> Type.Safe | _ -> v in
      Env.bind (Type.make_pany (fst ty)) v t
  | Pid id -> Env.bind id v t
  | Pvalue _ -> t
  | Pvariant (_, p) -> pat t p (make_value v p)
  | Precord pfl -> List.fold_left (pat_field (fst ty) v) t pfl
  | Pas (x, p) ->
      (match v with
      | Type.Safe | Type.Obs _ ->
	  pat t p (make_value v p)
      | _ ->
	  let up = Ident.fresh (snd x) in
	  let t = Env.bind (fst x, up) v t in
 	  let vars = PatVars.pat p IMap.empty in 
	  let size = IMap.fold (fun _ _ acc -> 1+acc) vars 0 in
	  let left = None in
	  let right = IMap.empty in
	  let ptr = Ident.tmp() in
	  let t = Env.bind (fst x, ptr) (Type.As (up, (left, right, size))) t in
	  let t = Env.bind x (Type.As_root ptr) t in
	  let v = Type.As_child ptr in
	  pat t p (make_value v p))

and pat_field pos v t (_, pf) = pat_field_ pos v t pf
and pat_field_ pos v t = function
  | PFany _ -> Env.bind (Type.make_pany pos) v t
  | PFid x -> Env.bind x v t
  | PField (_, p) -> pat t p (make_value v p)

and make_value v ((_, tyl), pl) =
  let v = 
    match v with
    | Type.Safe 
    | Type.As_child _
    | Type.Obs _ as v -> v
    | _ -> Type.Fresh
  in
  List.map (fun _ -> v) tyl


and tuple t (_, tpl) =   
  (* Everything but identifiers *)
  let t, pvl1 = 
    List.fold_right (
    fun (tyl, e) (t, acc) ->
      match e with
      | Eid _ -> t, (fst tyl, []) :: acc
      | _ ->
	  let t, vl = expr_ t (snd tyl) e in
	  t, (fst tyl, vl) :: acc
   ) tpl (t, []) in
  (* Identifiers *)
  let t, pvl2 = 
    List.fold_right (
    fun (tyl, e) (t, acc) ->
      match e with
      | Eid _ -> 
	  let t, vl = expr_ t (snd tyl) e in
	  t, (fst tyl, vl) :: acc  
      | _ -> t, (fst tyl, []) :: acc
   ) tpl (t, []) in
  let pvl = 
    List.fold_right2 (
    fun x y acc ->
      match x, y with
      | (_, []), v 
      | v, _ -> v :: acc
   ) pvl1 pvl2 [] in
  List.iter (
    fun (p, vl) ->
      List.iter (
      function 
	| Type.Obs v -> 
	    ISet.iter (
	    fun x ->
	      ignore (Env.obs (p, x) (Env.get x t) t)
	   ) v
	| _ -> ()
     ) vl
 ) pvl ;
  let vl = List.flatten (List.map snd pvl) in
  t, vl 

and expr t (ty, e) = expr_ t [ty] e
and expr_ t ty = function
  | Eid x -> 
      (match ty with
      | [_, Tprim _] -> 
	  Env.bind x Type.Safe t, [Type.Safe]
      | _ -> Env.use x t)
  | Evalue _ -> 
      t, [Type.Safe]
  | Evariant (x, e) -> 
      let t, _ = tuple t e in
      t, Type.fresh ty
  | Ebinop (_, e1, e2) -> 
      let t, _ = expr t e1 in
      let t, _ = expr t e2 in
      t, [Type.Safe]
  | Euop (_, e) -> 
      let t, _ = expr t e in
      t, [Type.Safe]
  | Erecord fdl -> 
      let t = List.fold_left field t fdl in
      t, Type.fresh ty
  | Ewith (e, fdl) ->  
      let t = List.fold_left field t fdl in
      let t, _ = expr t e in
      t, Type.fresh ty
  | Efield (e, _) -> proj t e
  | Ematch (e, al) -> 
      let t, vl = tuple t e in
      let t' = Env.push t in
      let tall = List.map (action t' vl) al in
      let tl, all = List.split tall in
      let t = Env.merge t tl in
      t, Type.unify_list all
  | Elet (p, e1, e2) ->
      let t, v = tuple t e1 in
      let t = pat t p v in
      let t, v = tuple t e2 in
      t, v
  | Eif (c, e1, e2) -> 
      let t, _ = expr t c in
      let t' = Env.push t in
      let t1, vl1 = tuple t' e1 in
      let t2, vl2 = tuple t' e2 in
      let pos1 = fst (fst e1) in
      let pos2 = fst (fst e2) in
      let t = Env.merge t [pos1, t1; pos2, t2] in
      t, Type.unify vl1 vl2
  | Eapply (_, _, x, e) ->
      let t, _ = Env.use x t in
      let t, vl = tuple t e in
      apply ty t e vl
  | Eseq (e1, e2) ->
      let t, _ = expr t e1 in
      tuple t e2
  | Eobs x -> 
      Env.obs x (Env.get (snd x) t) t
  | Efree (_, x) -> 
      Env.use x t 
  | Epartial (f, e) -> 
      let t, _ = expr t f in
      let t, vl = tuple t e in
      let t, vl = Env.partial t vl in
      t, vl
  | Efun (_, obs, p, e) as e_ -> 
      let vset = FreeObsVars.expr_ obs t ISet.empty e_ in
      let t = Env.push t in
      let tyl = List.map fst p in
      let tyl = List.fold_right (fun x acc -> x :: acc) tyl [] in
      let t = List.fold_left2 pat_el t p (Type.fresh tyl) in
      let t, _ = tuple t e in
      if obs 
      then Env.closure t vset
      else t, [Type.Fresh]

and field t (_, e) =
  let t, _ = tuple t e in
  t

and action t vl (p, a) =
  let t = pat t p vl in
  let pos = fst (fst a) in
  let t, vl = tuple t a in
  (pos, t), vl

and proj t (_, e) = 
  match e with
  | Eid x -> Env.obs x (Env.get (snd x) t) t
  | Efield (e, _) -> proj t e
  | _ -> assert false

and apply tyl t x vl = 
  let obs_set = List.fold_left (
    fun acc v ->
      match v with
      | Type.Obs s -> ISet.union acc s
      | _ -> acc
   ) ISet.empty vl in
  if ISet.is_empty obs_set
  then t, Type.fresh tyl
  else 
    t, List.map (
    function 
      | _, Tprim _ -> Type.Safe
      | _, Tapply ((_, x), _) when x = Naming.tobs -> Type.Obs obs_set
      | _ -> Type.Fresh
   ) tyl
