
module T = struct

  type t = 
    | Empty
    | Cons of int32 * t
    | Lazy of t future


  val main: unit -> unit
  let main _ = 
    print_int (loop 10 0)

end
