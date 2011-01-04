
module Array = struct

  type 'a t

  val make: int32 #-> 'a t = "array_make"
  val set: 'a t * int32 * 'a #-> 'a t = "array_set"
  val get__internal: 'a t obs * int32 #-> 'a option = "array_get"

  val get: 'a t * int32 -> 'a t * 'a option 
  let get t n = 
    (* get__internal is dangerous *)
    let v = get__internal (obs t) n in 
    t, v 

  val delete: 'a t * ('a #-> unit) #-> unit = "array_free"
end

