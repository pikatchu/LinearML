
module Sid = struct type t = string let compare = String.compare end
module SMap = Map.Make (Sid)
module SSet = Set.Make (Sid)
module IMap = Map.Make (Ident)
module ISet = Set.Make (Ident)

let o = output_string stdout

let imap_of_list l = 
  List.fold_left 
    (fun acc (((_, x) as id), y) -> IMap.add x (id, y) acc) 
    IMap.empty 
    l

let list_of_imap m = 
  IMap.fold (fun _ y acc -> y :: acc) m []

let clist_of_imap m = 
  IMap.fold (fun x y acc -> (x, y) :: acc) m []

let imfold f acc im = 
  IMap.fold (fun x y acc -> f acc y) im acc

let imiter f im = 
  IMap.iter (fun _ x -> f x) im

let imlfold f acc im = 
  IMap.fold (fun x y (acc, im) ->
    let acc, y = f acc y in
    acc, IMap.add x y im) im (acc, IMap.empty)
    
let lfold f acc l = 
  let acc, l = List.fold_left (fun (acc,l) x -> 
    let acc, x = f acc x in
    acc, x :: l) (acc, []) l in
  acc, List.rev l

let lfold2 f acc l1 l2 = 
  let acc, l = List.fold_left2 (fun (acc, l) x1 x2 -> 
    let acc, x = f acc x1 x2 in
    acc, x :: l) (acc, []) l1 l2 in
  acc, List.rev l

let rec uniq cmp = function
  | []
  | [_] as l -> l
  | x :: y :: rl when cmp x y = 0 -> x :: uniq cmp rl
  | x :: rl -> x :: uniq cmp rl

let uniq cmp l = uniq cmp (List.sort cmp l)

let union t1 t2 = SMap.fold SMap.add t1 t2

let option f = function None -> None | Some x -> Some (f x)

let fold_right f acc l = List.fold_right (fun x acc -> f acc x) l acc

let rec print_list o f sep t = 
  match t with
  | [] -> ()
  | [x] -> f o x
  | x :: rl -> f o x ; o sep ; print_list o f sep rl

let rec filter_opt l = 
  match l with
  | [] -> []
  | None :: rl -> filter_opt rl
  | Some x :: rl -> x :: filter_opt rl
