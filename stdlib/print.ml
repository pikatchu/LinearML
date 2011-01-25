
module Print = struct

  val c_int: int #-> unit = "print_int"
  val c_newline: unit #-> unit = "print_newline"
  val c_float: float #-> unit = "print_float"
  val c_string: string #-> unit = "print_string"

  val int: int -> unit
  let int x = c_int x

  val newline: unit -> unit
  let newline () = c_newline()

  val float: float -> unit
  let float x = c_float x

  val string: string -> unit
  let string x = c_string x
end
