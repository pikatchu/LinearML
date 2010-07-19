
module Test:sig

  type t1 = int32 * int32
  type 'a t2 = 'a * 'a
  type ('a, 'b) t4 = 'a t2 * 'b t2

  type 'a t = { field1: 'a x }
  and 'a x = 'a * 'a

  type t3 = B | A | C

  val fac: int32 -> int32


end = struct

  let rec fac t = 
    (if t = 0 then 1 else 2, 3) + 1
end
