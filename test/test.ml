
module Test:sig

  type t1 = int32 * int32
  type 'a t2 = 'a * 'a
  type ('a, 'b) t4 = 'a t2 * 'b t2

  type 'a t = { field1: 'a x }
  and 'a x = 'a * 'a

  type t3 = Bob of bool

  val f: t3 -> int32
  val f2: (bool, int32) t4 -> int32


end = struct

  let f x = 
    match x with
    | (Bob x | Bob x) -> x

  let g x = x
  let f2 x = x

end

module Test2: sig

  type t = Test.t1
end = struct
end
