
module T: sig

    type t = 
    | Empty
    | B


  val rev_append: t   -> int32
end = struct

  let rec rev_append l = 
    match obs l with
    | Empty -> 0
    | B -> 
    let x = match l with Empty -> 0 | B -> 1 in
    x


end
