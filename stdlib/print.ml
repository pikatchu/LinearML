
module Print = struct

  val c_int32: int32 #-> unit = "print_int32"
  val c_newline: unit #-> unit = "print_newline"

  val int32: int32 -> unit
  let int32 x = c_int32 x

  val newline: unit -> unit
  let newline () = c_newline()
end
