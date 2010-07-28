
module Test:sig

  type 'a list = 
    | Empty
    | Cons of 'a * 'a list

  val rev: 'a list * 'a list -> 'a list

  val f: ('a -> 'a) -> 'a

end = struct
    
end
