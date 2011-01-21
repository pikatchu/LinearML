
module Array = struct

  type 'a t

  val make: int #-> _ t = "array_make"
  val swap__: 'a t obs * int * 'a option #-> 'a option = "array_swap"
  val release: 'a t * ('a #-> unit) #-> unit = "array_free"

  val fold_left: ('a * 'b option #-> 'a) * 'a * 'b t #-> 'a = "array_fold_left"

  val swap: 'a t * int * 'a option -> 'a t * 'a option
  let swap t n x = 
    let res = swap__ (obs t) n x in
    t, res
end

