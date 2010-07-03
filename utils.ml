
module Sid = struct type t = string let compare = String.compare end
module SMap = Map.Make (Sid)
module SSet = Set.Make (Sid)
module IMap = Map.Make (Ident)
module ISet = Set.Make (Ident)

    
let lfold f acc l = 
  let acc, l = List.fold_left (fun (acc,l) x -> 
    let acc, x = f acc x in
    acc, x :: l) (acc, []) l in
  acc, List.rev l

let rec uniq cmp = function
  | []
  | [_] as l -> l
  | x :: y :: rl when cmp x y = 0 -> x :: uniq cmp rl
  | x :: rl -> x :: uniq cmp rl

let uniq cmp l = uniq cmp (List.sort cmp l)

let union t1 t2 = SMap.fold SMap.add t1 t2

let option f = function None -> None | Some x -> Some (f x)
