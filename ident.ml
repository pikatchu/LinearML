
type t = int

module IMap = Map.Make (struct 
  type t = int 
  let compare = (-) 
end)

let counter = ref 0
let trace = ref IMap.empty

let make x = 
  incr counter ;
  let res = !counter in
  trace := IMap.add !counter x !trace ;
  res

let compare x y = x - y
