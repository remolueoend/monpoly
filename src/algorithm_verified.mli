open Predicate
open MFOTL

type exit_condition = OK | Violation | Error

val no_mw: bool ref
val monitor: Db.schema -> string -> var list -> formula -> exit_condition
