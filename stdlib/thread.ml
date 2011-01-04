
module Future = struct

  type 'a t

  val c_make: ('a #-> 'b) * 'a #-> 'a t = "future_make"
  val c_wait: 'a t #-> 'a = "future_wait"
  val c_ready: 'a t obs #-> int32 = "future_ready"

  val make: ('a #-> 'b) * 'a -> 'a t
  let make f x = c_make f x
    
  val wait: 'a t -> 'a
  let wait x = c_wait x

  val ready: 'a t obs -> bool
  let ready x = c_ready x = 0
end
