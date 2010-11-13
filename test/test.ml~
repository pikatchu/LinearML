
module List: sig
  type t = 
    | Empty
    | Cons of int32 * t


  val merge: t * t -> t
end = struct


  let rec merge l1 l2 = 
    match l1, l2 with
    | [], l -> l
    | l, [] -> l
    | (Cons x1 rl1 as l1), (Cons x2 rl2 as l2) ->
	if x1 <= x2
	then x1 :: merge rl1 l2
	else x2 :: merge l1 rl2


end
