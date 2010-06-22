
type t

val make: Pos.t * string -> t
val compare: t -> t -> int
val to_string: t -> string
