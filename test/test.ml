

module Test: sig

  type 'a t = 
    | Empty
    | Cons of 'a * 'a t

  type 'a t2 = {
      field1: 'a * 'a;
      field2: int32 ;
    }

  val f: 'a t t t2 -> int32

end = struct

  let f t =
    match t with
    | { field1 = (Cons _ _ | Empty), Empty ;  field2 = 0 } -> 1
    | { field1 = Cons (Empty) _, Empty ; _ } -> 2
    | { field1 = Cons (Empty) _, Cons _ _ ; _ } -> 3
    | { field1 = Cons (Empty) _, Cons _ _ ; _ } -> 3
    | { field1 = _, _ ; _ } -> 3

end

