open MFOTL
open Predicate
open Relation
open Helper

val is_monitorable: Db.schema -> formula -> bool * (formula * string) option
val convert_formula: Db.schema -> formula -> Verified.Monitor.formula
val convert_db: monpolyData -> (Verified.Monitor.char list * Verified.Monitor.event_data list) Verified.Monitor.set * Verified.Monitor.nat
val convert_violations: (Verified.Monitor.nat * Verified.Monitor.event_data option list Verified.Monitor.set) list -> (int * relation) list
