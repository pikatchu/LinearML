
(*
module Maybe = struct

  type 'a t =
    | Nothing
    | Just of 'a
  
  val bind: 'a t * ('a -> 'b t) -> 'b t
  let bind t f =
    match t with
    | Nothing -> Nothing
    | Just x -> f x

  val return: 'a -> 'a t
  let return x = Just x

end

*)

module ContinuationMonad = struct

  type ('a, 'b) t = 'a -> 'b

  val bind: (('a -> 'b) -> 'b) * ('a * ('c -> 'b) -> 'b) * ('c -> 'b) -> 'b
  let bind c f k = c (fun (t: 'l) -> f t k)

  val return: 'a * ('a -> 'b) -> 'b
  let return t f =  f t

end

module Lazy = struct

  type 'a t = unit -> 'a

  val force: 'a t -> 'a
  let force f = f()
end

module LList = struct

  type 'a t = 
    | Empty
    | Cons of 'a * 'a t Lazy.t

  val make: int -> int t
  let make n = 
    if n = 0
    then Empty
    else Cons n (fun () -> make (n-1))
end

