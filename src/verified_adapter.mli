open MFOTL
open Predicate
open Relation
open Helper

val is_monitorable: Db.schema -> formula -> bool * (formula * string) option
val convert_formula: Db.schema -> formula -> Verified.Monitor.formula

type db
val empty_db: db
val insert_into_db: Table.schema -> string list -> db -> db

type state
val init: Verified.Monitor.formula -> state
val step: MFOTL.timestamp -> db -> state -> (int * MFOTL.timestamp * relation) list * state
