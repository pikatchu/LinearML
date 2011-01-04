

module TestShare = struct

  val show: Int32Box.t obs -> unit
  let show x = 
    Print.int32 (Int32Box.get x) ;
    Print.newline()

  val release: Int32Box.t option -> unit
  let release x = 
    match x with
    | None -> ()
    | Some v -> Int32Box.release v

  val main: unit -> unit
  let main () = 
    let b = Int32Box.make 22 in
    let b1 = Share.make b in
    let b2 = Share.clone (obs b1) in
    show (Share.visit (obs b1)) ;
    show (Share.visit (obs b2)) ;
    release (Share.release b1) ;
    release (Share.release b2) 
end
