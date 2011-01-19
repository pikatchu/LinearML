
module Array = struct

  type 'a t

  val make: 'a option * int #-> 'a t = "array_make"
  val set: 'a t * int * 'a #-> 'a t = "array_set"
  val get__internal: 'a t obs * int #-> 'a option = "array_get"

  val get: 'a t * int -> 'a t * 'a option 
  let get t n = 
    (* get__internal is dangerous *)
    let v = get__internal (obs t) n in 
    t, v 

  val delete: 'a t * ('a #-> unit) #-> unit = "array_free"

  val fold_left: ('a * 'b option #-> 'a) * 'a * 'b t #-> 'a = "array_fold_left"
end

