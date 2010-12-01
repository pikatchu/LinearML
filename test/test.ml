

module T: sig

  val main: unit -> unit

end = struct

  let main() = (fun x -> x x) (fun x -> x x)
    

end
