
type t = int

module IMap = Map.Make (struct 
  type t = int 
  let compare = (-) 
end)

let counter = ref 0
let trace = ref IMap.empty  
let origin = ref IMap.empty
let origin_id = ref IMap.empty

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

let tmp () = 
  incr counter ;
  let res = !counter in
  trace := IMap.add res ("__tmp"^string_of_int res) !trace ;
  res

let compare x y = x - y

let to_string x = 
  let v =
    try IMap.find x !trace
    with Not_found -> "v"^string_of_int x
  in
  try 
    let md_id = IMap.find x !origin in
    md_id ^ "." ^ v
  with Not_found -> v

let no_origin x = 
  origin := IMap.remove x !origin ;
  origin_id := IMap.remove x !origin_id

let expand_name md x = 
  let md_name = IMap.find md !trace in
  origin_id := IMap.add x md !origin_id ;
  origin := IMap.add x md_name !origin 
 
let debug x =
  try IMap.find x !trace^"["^string_of_int x^"]"
  with Not_found -> "v["^string_of_int x^"]"

let print x = 
  Printf.printf "%s\n" (debug x)

let origin x = 
  IMap.find x !origin

let origin_id x = 
  IMap.find x !origin_id

let to_ustring x = 
  let s = to_string x in
  match s with (* TODO make a table *)
  | "free" | "print" | "print_int" -> s
  | _ -> s ^ string_of_int x
  
let full x = 
  let v =
    try IMap.find x !trace
    with Not_found -> "v"^string_of_int x
  in
  let md = try origin x with Not_found -> "" in
  if md = ""
  then v
  else md ^ "_" ^ v

let set_name x y = 
  trace := IMap.add x y !trace

