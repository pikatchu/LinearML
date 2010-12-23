module T = struct

  type 'a bob

  val f: 'a -> 'a bob = "dd"
  val f2: 'a bob -> 'a = "dd3"

  type db = { v: int32 }

  val main: unit -> unit
  let main () = 
    let b1 = f { v = 0 } in
    let b2 = f { v = 1 } in
    let x = f2 b1 in
    let y = f2 b2 in
    free x ; free y 

end
