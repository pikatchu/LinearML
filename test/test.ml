
module T = struct

  type t = 
    | Empty
    | Cons of int32 * t
    | Lazy of t future

  val f: int32 -> unit
  let f x = if x = 0 then print_int 12 else print_int 32

  val main: unit -> unit
  let main() = 
    f 10 ;
    f 0


end
