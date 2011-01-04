
module TestFuture = struct

(* Dummy thread doing nothing *)
  val run: Int32Box.t #-> Int32Box.t
  let run x = x

  val show: Int32Box.t -> unit
  let show x = 
    Print.int32 (Int32Box.get (obs x)) ;
    Int32Box.release x ;
    Print.newline()

  val main: unit -> unit
  let main () = 
    let b = Int32Box.make 23 in
    let b = Future.make run b in
    show (Future.wait b)

end
