
module T = struct

  type fbox = { v: float }

  val f: 'a -> 'a
  let f x = x

  val main: bool -> fbox
  let main b = 
    if b
    then f { v = 1.0 }
    else f { v = 2.0 }

end
