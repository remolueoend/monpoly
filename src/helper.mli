open MFOTL
open Predicate
open Db

type constraintSet

type valueTuple = (string list * int list)

type sconstraint   = { values: constraintSet; partitions: int list}

type constraintRelation = sconstraint list

type splitParameters = {keys: string list; constraints: constraintRelation}


val empty: constraintSet
val is_empty: constraintSet -> bool
val add: cst -> constraintSet -> constraintSet
val singleton: cst -> constraintSet
val find_opt: cst -> constraintSet -> cst option

(* Enables using the compare function in EExists to project away unwanted free vars *)
val pvars_to_rel: string list -> Relation.relation
val rel_to_pvars: Relation.relation -> string list

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