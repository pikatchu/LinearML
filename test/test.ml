
module T = struct

  type ('a, 'b) cple = {
      fst: 'a ;
      snd: 'b ;
    }

  type ibox = { v: int32 }

  type ('a, 'b) tree = 
    | Empty
    | Node of int32 * ('a, 'b) tree * 'a * 'b * ('a, 'b) tree


  val main: unit -> unit
  let main () = 
    let x = Some { v = 0 } in
    match x with
    | None -> print_int 0
    | Some t -> 
	let { t ; ~v } = t in
	free t;
	print_int v

end
