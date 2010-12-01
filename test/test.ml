

module T = struct

  type t = 
    | Empty
    | Cons of int32 * t
    | Lazy of t future

  val split: int32 * t * t * t -> int32 * t * t
  let rec split n l1 l2 l = 
    match l with
    | Empty -> n, l1, l2
    | Lazy x -> split n l1 l2 (wait x)
    | Cons x Empty -> n, l1, l2
    | Cons x (Cons y rl) -> split (n+1) (Cons x l1) (Cons y l2) rl
    | Cons x (Lazy rl) -> split n l1 l2 (Cons x (wait rl))

end
