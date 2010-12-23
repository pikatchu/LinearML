
module T = struct

  type t = 
    | Empty
    | Cons of int32 * t
    | Lazy of t future

  val rev_append: t * t -> t
  let rev_append l1 l2 = 
    match l1 with
    | Empty -> l2
    | Cons x rl -> rev_append rl (Cons x l2)
    | Lazy l -> rev_append (wait l) l2

  val merge: t * t * t -> t
  let merge acc l1 l2 = 
    match l1, l2 with
    | Lazy l1, l2 -> merge acc (wait l1) l2
    | l1, Lazy l2 -> merge acc l1 (wait l2)
    | Empty, l -> rev_append l acc
    | l, Empty -> rev_append l acc
    | (Cons x1 rl1 as l1), (Cons x2 rl2 as l2) ->
	if x1 > x2
	then merge (Cons x1 acc) rl1 l2
	else merge (Cons x2 acc) l1 rl2

  val split: int32 * t * t * t -> int32 * t * t
  let split n l1 l2 l = 
    match l with
    | Empty -> n, l1, l2
    | Lazy x -> split n l1 l2 (wait x)
    | Cons x Empty -> n, l1, l2
    | Cons x (Cons y rl) -> split (n+1) (Cons x l1) (Cons y l2) rl
    | Cons x (Lazy rl) -> split n l1 l2 (Cons x (wait rl))

  val sort: t -> t
  let sort l = 
    match l with
    | Empty -> Empty
    | Lazy l -> sort (wait l)
    | Cons _ Empty as l -> l
    | Cons x rl as l -> 
	let length1, l1, l2 = split 0 Empty Empty l in
	merge Empty (sort l1) (sort l2)

  val make: t * int32 -> t
  let make acc n = 
    if n = 0
    then acc 
    else make (Cons n acc) (n-1)

  val sum: int32 * t -> int32
  let sum acc l = 
    match l with
    | Empty -> acc
    | Cons n rl -> sum (n + acc) rl
    | Lazy x -> sum acc (wait x)

  val loop: int32 * int32 -> int32
  let loop n acc = 
    if n <= 0
    then acc
    else loop (n-1) (acc + sum 0 (sort (make Empty 2000000)))

  val main: unit -> unit
  let main _ = 
    print_int (loop 1 0)

end
