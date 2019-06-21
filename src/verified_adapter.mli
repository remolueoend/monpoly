open MFOTL
open Predicate
open Relation
open Helper

val convert_formula: formula -> cst Verified.Monitor.formula
val convert_db: monpolyData -> (Verified.Monitor.char list * cst list) Verified.Monitor.set * Verified.Monitor.nat
val convert_violations: (Verified.Monitor.nat * Predicate.cst option list) Verified.Monitor.set -> (int * relation) list
val domain_ceq: cst Verified.Monitor.ceq
val domain_ccompare: cst Verified.Monitor.ccompare
val domain_equal: cst Verified.Monitor.equal
