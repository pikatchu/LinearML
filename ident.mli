
type t

val foo: t
val make: string -> t
val fresh: t -> t
val tmp: unit -> t
val compare: t -> t -> int
val to_string: t -> string
val debug: t -> string
val print: t -> unit
val expand_name: t -> t -> unit
val origin: t -> string
val origin_id: t -> t
val to_ustring: t -> string
val full: t -> string
val set_name: t -> string -> unit
val no_origin: t -> unit
