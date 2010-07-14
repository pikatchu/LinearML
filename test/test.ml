
module Test:sig

  type t1 = int32 * int32
  type 'a t2 = 'a * 'a
  type ('a, 'b) t4 = 'a t2 * 'b t2

  type 'a t = { field1: 'a x }
  and 'a x = 'a * 'a

  val f: 'a t -> 'a t


end = struct



  let f x = x

end
