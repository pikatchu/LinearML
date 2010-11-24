
module T: sig

  type t = 
    | Empty
    | Cons of int32 * t
    | Lazy of t future

  type st = {
      x1: t ;
      x2: t ;
      length1: int32 ;
    }
  val main: 'b obs -> int32
end = struct

  let rec rev_append l1 l2 = 
    match l1 with
    | Empty -> l2
    | Cons x rl -> rev_append rl (Cons x l2)
    | Lazy l -> rev_append (wait l) l2

  let rec merge acc l1 l2 = 
    match l1, l2 with
    | Lazy l1, l2 -> merge acc (wait l1) l2
    | l1, Lazy l2 -> merge acc l1 (wait l2)
    | Empty, l -> rev_append l acc
    | l, Empty -> rev_append l acc
    | (Cons x1 rl1 as l1), (Cons x2 rl2 as l2) ->
	if x1 > x2
	then merge (Cons x1 acc) rl1 l2
	else merge (Cons x2 acc) l1 rl2

  let merge_acc v = 
    let { v ; x1 = x1 ; x2 = x2 } = v in
    free v ;
    merge Empty x1 x2

  let rec split acc l = 
    match l with
    | Empty -> acc
    | Lazy x -> split acc (wait x)
    | Cons x Empty ->
	let { acc ; x1 = l1 ; length1 = length1 } = acc in 
	{ acc with x1 = Cons x l1 }
    | Cons x (Cons y rl) -> 
	let { acc ; x1 = l1 ; x2 = l2 ; length1 = length1 } = acc in
	let length1 = 1 + length1 in
	let acc = { acc with x1 = Cons x l1 ; x2 = Cons y l2 ; length1 = length1 } in
	split acc rl
    | Cons x (Lazy rl) -> split acc (Cons x (wait rl))

  let rec sort l = 
    match l with
    | Empty -> Empty
    | Lazy l -> sort (wait l)
    | Cons _ Empty as l -> l
    | Cons x rl as l -> 
	let acc = { x1 = Empty ; x2 = Empty ; length1 = 0 } in
	let acc = split acc l in
	let { acc ; x1 = l1 ; x2 = l2 ; length1 = length1 } = acc in
	free acc ;
	if length1 >= 100000
	then merge Empty (Lazy (spawn sort l1)) (Lazy (spawn sort l2))
	else merge Empty (sort l1) (sort l2)

  let rec make acc n = 
    if n = 0
    then acc 
    else make (Cons n acc) (n-1)

  let rec sum acc l = 
    match l with
    | Empty -> acc
    | Cons n rl -> sum (n + acc) rl
    | Lazy x -> sum acc (wait x)

(*
  let rec print_list l =
    match l with
    | Empty -> ()
    | Cons n rl -> print_int n ; print_list rl
    | Lazy l -> print_list l 
*)
  let main _ = 
    let acc = merge_acc { x1 = Empty ; x2 = Empty ; length1 = 0 } in
    free acc ;
    print_int (sum 0 (sort (make Empty 2000000))) ;
    0

end
