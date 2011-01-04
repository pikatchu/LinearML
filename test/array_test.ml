module Test = struct

  type ibox = { v: int32 }

  val init: int32 * ibox Array.t -> ibox Array.t
  let init n t = 
    if n < 0
    then t 
    else init (n-1) (Array.set t n { v = n })

  val free_ibox: ibox #-> unit
  let free_ibox x = free x

  val sum: int32 * int32 * ibox Array.t -> int32
  let sum acc n t = 
    if n < 0
    then (Array.delete t free_ibox; acc)
    else 
      let t, v = Array.get t n in
      match v with
      | None -> sum acc (n-1) t
      | Some { b ; ~v } ->
	  free b ;
	  sum (acc+v) (n-1) t
end
