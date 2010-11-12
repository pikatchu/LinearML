

module List: sig

  type t = 
    | Empty
    | Cons of int32 * t

  val main: unit -> int32
end = struct

  let rec main t = 
    let n = 1 in
    let y = n + 1 in
    y
end
