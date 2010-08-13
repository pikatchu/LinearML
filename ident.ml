
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
  trace := IMap.add res x !trace ;
  res

let fresh x = 
  incr counter ;
  let res = !counter in
  let name = IMap.find x !trace in
  trace := IMap.add res name !trace ;
  res

let tmp () = make "__tmp"

let compare x y = x - y

let to_string x = 
  try IMap.find x !trace
  with Not_found -> "v"^string_of_int x

let debug x =
  try IMap.find x !trace^"["^string_of_int x^"]"
  with Not_found -> "v["^string_of_int x^"]"

let print x = 
  Printf.printf "%s\n" (debug x)
