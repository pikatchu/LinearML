

module T = struct

  type t = { v: int32 }

  val ping: int32 * t * t -> t * t
  let ping n t1 t2 =
    if n = 0
    then t1, t2
    else pong ping (n-1) t1 t2

  val pong: (int32 * 'a * 'b -> 'a * 'b) * int32 * 'a * 'b -> 'a * 'b
  let pong f n t1 t2 =
    if n = 0
    then t1, t2
    else f (n-1) t1 t2

  val main: unit -> unit
  let main() = 
    let t1, t2 = ping 1000000000 { v = 0 } { v = 0 } in
    free t1 ;
    free t2 
      
end
