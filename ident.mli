
type t

val make: string -> t
val fresh: t -> t
val tmp: unit -> t
val compare: t -> t -> int
val to_string: t -> string
val debug: t -> string
val print: t -> unit
