
module Map = struct

  type ('a, 'b) cple = {
      fst: 'a ;
      snd: 'b ;
    }

  type ibox = { v: int32 }

  type ('a, 'b) tree = 
    | Empty
    | Node of int32 * ('a, 'b) tree * 'a * 'b * ('a, 'b) tree

  val add: ('a obs * 'a obs -> int32) * 'a * 'b * ('a, 'b) tree 
    -> ('a, 'b) cple option * ('a, 'b) tree
  let add cmp x v tree =
    match tree with
    | Empty -> None, Node 0 Empty x v Empty
    | Node b t1 x2 v2 t2 ->
	let c = cmp (obs x) (obs x2) in
	let rest, b, t1, t2 = 
	  if c < 0
	  then 
	    let rest, t1 = add cmp x v t1 in
	    rest, b-1, t1, t2
	  else if c > 0
	  then 
	    let rest, t2 = add cmp x v t2 in
	    rest, b+1, t1, t2
	  else Some { fst = x ; snd = v }, b, t1, t2 in
	let t = Node b t1 x2 v2 t2 in
	if b <= 0-2
	then rest, left t
	else if b >= 2
	then rest, right t
	else rest, t

  val left: ('a, 'b) tree -> ('a, 'b) tree
  let left t = t
      
  val right: ('a, 'b) tree -> ('a, 'b) tree
  let right t = t


  val print_tree: ('a, 'b) tree obs -> unit
  let print_tree tree = 
    match tree with
    | Empty -> ()
    | Node b t1 x v t2 ->
	print_int b ;
	print_tree t1 ;
	print_tree t2 

  val make_tree: (int32 -> 'a) * (int32 -> 'b) * int32 -> ('a, 'b) tree
  let make_tree make_key make_value n =
    if n = 0
    then Empty
    else begin
      t1 := make_tree make_key make_value (n-1) ;
      t2 := make_tree make_key make_value (n-1) ;
      Node n t1 (make_key n) (make_value n) t2
    end

  val free_tree: ('a -> unit) * ('b -> unit) * ('a, 'b) tree -> unit
  let free_tree free_key free_value t = 
    match t with
    | Empty -> ()
    | Node _ t1 k v t2 -> 
	free_tree free_key free_value t1 ; 
	free_key k ;
	free_value v ;
	free_tree free_key free_value t2

  val make_ibox: int32 -> ibox
  let make_ibox n = { v = n } 

  val free_ibox: ibox -> unit
  let free_ibox x = 
    free x

  val loop: int32 -> unit
  let rec loop n = 
    if n <= 0
    then ()
    else
      let t = make_tree make_ibox make_ibox 10 in
      free_tree free_ibox free_ibox t ;
      loop (n-1) 

  val main: unit -> unit
  let main() = loop 100000

end
