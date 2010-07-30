
module Test: sig

  type t = int32

  val f: 'a -> 'a

end = struct

  let rec f x = 1 + f x

end

