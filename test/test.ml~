
module Test:sig

  type 'a t = 
    | A
    | B of 'a 

  type ('a, 'b) t2 = ('a -> 'b) t

  val fac: unit -> ('a, 'a) t2
  val id: 'a -> 'a

end = struct

  let rec fac x = B (fun x -> x)
    
  let id x = x
end


module Test2: sig
  val f: unit -> unit
end = struct

  let f x = Test.id (x, x)
end
