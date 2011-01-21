module List = struct

  type 'a t = 
    | Empty
    | Cons of 'a * 'a t

  val rev_append: 'a t * 'a t -> 'a t
  let rev_append acc l = 
    match l with
    | Empty -> acc
    | Cons x rl -> rev_append (Cons x acc) rl

  val rev: 'a t -> 'a t
  let rev l = rev_append Empty l

  val append: 'a t * 'a t -> 'a t
  let append l1 l2 = 
    match l1 with
    | Empty -> l2
    | Cons x rl -> Cons x (append rl l2)

  val flatten: 'a t t -> 'a t
  let flatten l = 
    match l with
    | Empty -> Empty
    | Cons x rl -> append x (flatten rl)

  val map: ('a -> 'b) * 'a t -> 'b t
  let map f l = 
    match l with
    | Empty -> Empty
    | Cons x rl -> Cons (f x) (map f rl)

  val map_acc: ('a * 'b -> 'a * 'c) * 'a * 'b t -> 'a * 'c t
  let map_acc f acc l = 
    match l with
    | Empty -> acc, Empty
    | Cons x rl -> 
	let acc, x = f acc x in
	let acc, rl = map_acc f acc rl in
	acc, Cons x rl

  val fold_left: ('a * 'b -> 'a) * 'a * 'b t -> 'a
  let fold_left f acc l = 
    match l with
    | Empty -> acc
    | Cons x rl ->
	let acc = f acc x in
	fold_left f acc rl

  val fold_right: ('a * 'b -> 'b) * 'a t * 'b -> 'b
  let fold_right f l acc = 
    match l with
    | Empty -> acc
    | Cons x rl -> fold_right f rl (f x acc)
end

module IntList = struct

  type t = 
    | Empty
    | Cons of int * t

  val rev_append: t * t -> t
  let rev_append acc l = 
    match l with
    | Empty -> acc
    | Cons x rl -> rev_append (Cons x acc) rl

  val rev: t -> t
  let rev l = rev_append Empty l

  val append: t * t -> t
  let append l1 l2 = 
    match l1 with
    | Empty -> l2
    | Cons x rl -> Cons x (append rl l2)

  val map_int: (int -> int) * t -> t
  let map_int f l = 
    match l with
    | Empty -> Empty
    | Cons x rl -> Cons (f x) (map_int f rl)

  val release: t -> unit
  let release l = 
    match l with
    | Empty -> ()
    | Cons _ rl -> release rl
end
