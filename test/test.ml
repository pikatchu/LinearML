module T = struct

  val f: int32 -> unit
  let f x = print_int x
end

module B = struct

  val main: unit -> unit
  let main () = 
    T.f 0
end
