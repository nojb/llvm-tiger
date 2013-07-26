type t

val dummy : t

val equal : t -> t -> bool
val compare : t -> t -> int
val make : string -> t
val makeglobal : string -> t
val genid : unit -> t
val to_string : t -> string

open Format

val pp : formatter -> t -> unit
