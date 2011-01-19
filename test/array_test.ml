
module TestArray = struct

  module IB = IntBox

  type ibox = IB.t

  val init: int * ibox Array.t -> ibox Array.t
  let init n t = 
    if n < 0
    then t 
    else init (n-1) (Array.set t n (IB.make n))

  val free_ibox: ibox #-> unit
  let free_ibox x = free x

  val sum: int * int * ibox Array.t -> int
  let sum acc n t = 
    if n < 0
    then (Array.delete t free_ibox; acc)
    else 
      let t, v = Array.get t n in
      match v with
      | None -> sum acc (n-1) t
      | Some ib -> 
	  let v = IB.get (obs ib) in
	  IB.release ib ;
	  sum (acc+v) (n-1) t

  val add_opt: IB.t * IB.t option #-> IB.t 
  let add_opt x y =
    match y with
    | None -> x
    | Some y -> IB.add x y

  val test_fold: unit #-> unit
  let test_fold() = 
    let size = 10000000 in
    let t = Array.make None size in
    t := init (size - 1) t ;
    let total = Array.fold_left add_opt (IB.make 0) t in
    Print.int (IB.get (obs total)) ;
    Print.newline() ;
    IB.release total

end
