open MFOTL
open Predicate
open Relation
open Helper

val is_monitorable: formula -> bool * (formula * string) option
val convert_formula: formula -> Verified.Monitor.event_data Verified.Monitor.formula
val convert_db: monpolyData -> (Verified.Monitor.char list * Verified.Monitor.event_data list) Verified.Monitor.set * Verified.Monitor.nat
val convert_violations: (Verified.Monitor.nat * Verified.Monitor.event_data option list) Verified.Monitor.set -> (int * relation) list
