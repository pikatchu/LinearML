

module Test: sig

  type t = 
    | Empty
    | Cons of int32 * t

  val split: t * int32 -> int32 * t

end = struct

  let split x default = 
    match x with
    | Empty -> default, x
    | Cons x l -> x, l


end

