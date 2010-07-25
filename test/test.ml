
module Test:sig

  type 'a t = { field1: 'a }

  type 'a t2 = A of 'a

  val fac: int32 -> (int32 * int32 * int32 * int32)

end = struct

  let f x = x, x

  let rec fac x = 
    if true
    then f x
    else ()

end


