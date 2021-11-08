open MFOTL
open Predicate
open Relation
open Helper

val is_monitorable: Db.schema -> formula -> bool * (formula * string) option
val convert_formula: Db.schema -> formula -> Verified.Monitor.formula

type state
val init: Verified.Monitor.formula -> state
val observe: string -> cst list -> state -> state
val conclude: timestamp -> state -> (int * relation) list * state
