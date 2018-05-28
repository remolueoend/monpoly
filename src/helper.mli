open MFOTL
open Predicate
open Db

type sconstraint = { relname: string; values: Predicate.cst list list }

type constraintSet

val is_empty: constraintSet -> bool
val add: sconstraint -> constraintSet -> constraintSet
val singleton: sconstraint -> constraintSet

type commandParameter = 
    | ConstraintSet of constraintSet
    | Argument of string

type dataTuple    = { ts: MFOTL.timestamp; db: Db.db; }
type commandTuple = { c: string;  parameters: commandParameter option; }

type parser_feed =
    | CommandTuple of commandTuple
    | DataTuple    of dataTuple
    | ErrorTuple   of string

type monpolyData    = { tp: int; ts: MFOTL.timestamp; db: Db.db; }
type monpolyCommand = { c: string; parameters: commandParameter option}


type monpoly_feed =
    | MonpolyCommand of commandTuple
    | MonpolyData    of monpolyData
    | MonpolyError   of string