open Predicate
open MFOTL

val no_mw: bool ref
val monitor: Db.schema -> string -> var list -> formula -> unit
val monitor_string: Db.schema -> string -> var list -> formula -> unit
