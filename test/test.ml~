

module Test:sig


  val fac: int32 -> bool * bool

end = struct

  let g x = x, x

  let f x = 
    if x = 0 
    then 1, 1
    else g x

  let rec fac x = 
    let x, _ = f x in
    x, fac x
      
end
