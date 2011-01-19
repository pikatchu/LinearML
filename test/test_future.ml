
module TestFuture = struct

(* Dummy thread doing nothing *)
  val run: IntBox.t #-> IntBox.t
  let run x = x

  val show: IntBox.t -> unit
  let show x = 
    Print.int (IntBox.get (obs x)) ;
    IntBox.release x ;
    Print.newline()

  val main: unit #-> unit
  let main () = 
    let b = IntBox.make 23 in
    let b = Future.make run b in
    show (Future.wait b)

end
