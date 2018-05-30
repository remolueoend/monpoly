open MFOTL
open Predicate
open Db

type constraintSet

type listTuple     = { left: string list list; right: string list list }

type sconstraint   = { relname: string; values: (constraintSet list * constraintSet list)}

type constraintRelation = sconstraint list

val empty: constraintSet
val is_empty: constraintSet -> bool
val add: cst -> constraintSet -> constraintSet
val singleton: cst -> constraintSet
val find_opt: cst -> constraintSet -> cst option

type splitParameters = (string * constraintRelation)

type commandParameter = 
    | SplitParameters of splitParameters
    | Argument        of string

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