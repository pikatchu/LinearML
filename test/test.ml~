
module X: sig

  val f: ('a -> 'a) * ('a -> 'a) -> unit
  
end = struct

  let f g h = ()
end

module T: sig

  type t1 = { field1: int32 }

  val main: unit -> unit

end = struct

  let g x = { x with field1 = 0 } 
  let h x = x

  let main() = X.f g h

end
