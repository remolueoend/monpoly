open MFOTL
open Predicate
open Db

type sconstraint = { relname: string; values: Predicate.cst list list }

module Constraint_Set = Set.Make (
  struct type t = sconstraint
   let compare = Pervasives.compare
  end)

include Constraint_Set

type constraintSet = Constraint_Set.t

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

let is_empty set =
    Constraint_Set.is_empty set

let add c set =
    Constraint_Set.add c set
    
let singleton c =
    Constraint_Set.singleton c