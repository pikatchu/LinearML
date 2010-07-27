

module Test:sig


  val fac: int32 -> 'a

end = struct

  let g x = x, x

  let f x = 
    if x = 0 
    then 1, true
    else g x

  let rec fac x = 
    if true
    then f 1
    else f false
      
end
