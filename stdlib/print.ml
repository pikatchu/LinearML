
module Print = struct

  val c_int: int #-> unit = "print_int"
  val c_newline: unit #-> unit = "print_newline"

  val int: int -> unit
  let int x = c_int x

  val newline: unit -> unit
  let newline () = c_newline()
end
