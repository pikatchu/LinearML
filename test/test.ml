
module T = struct

  val f: int32 -> int32
  let f x = print_int x ; x
end

module B = struct

  val main: unit -> int32
  let main () = 
    let _ = T.f 0 in
    0
end
