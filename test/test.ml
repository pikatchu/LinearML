

module Test:sig


  val fac: 'c -> 'c

end = struct

  let rec map n f x = 
    if n = 0
    then f x
    else map (n-1) f f

  let rec fac x = map 10 (fun x -> x) x
      
end
