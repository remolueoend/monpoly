open MFOTL
open Predicate
open Log_parser
open Db

exception Type_error of string

module Constraint_Set = Set.Make (
  struct type t = cst
   let compare = Pervasives.compare
  end)

include Constraint_Set

type constraintSet = Constraint_Set.t

type valueTuple = (string list * int list)

type sconstraint   = { values: cst list list; partitions: int list}

type constraintRelation = sconstraint list

type splitParameters = {keys: string list; constraints: constraintRelation; num_partitions: int }

type commandParameter = 
    | SplitParameters of splitParameters
    | Argument of string

type dataTuple    = { ts: MFOTL.timestamp; db: Db.db; }
type commandTuple = { c: string;  parameters: commandParameter option; }

type parser_feed =
    | CommandTuple of commandTuple
    | DataTuple    of dataTuple
    | ErrorTuple   of string

type monpolyData    = { tp: int; ts: MFOTL.timestamp; db: Db.db;       }
type monpolyCommand = { c: string; parameters: commandParameter option }

type monpoly_feed =
    | MonpolyCommand of commandTuple
    | MonpolyData    of monpolyData
    | MonpolyError   of string

type 'a atree =
    | ALNode of 'a
    | AINode of ('a * int * int)  
    
type ('a, 'b) stree =  ('a, 'b option) Sliding.node atree    


(*let split_constraints cs l = 

    let get_e (a, b) = if l then a else b in
    map (fun c -> { relname = c.relname; values = get_e c.values }) cs*)

let pvars_to_rel pvars = 
    Relation.singleton (List.map (fun v -> Str v) pvars)

let rel_to_pvars rel   =
    List.map (fun e -> match e with
        | Str   s   -> s
        | Float f   -> raise (Type_error ("rel_to_pvars helper funtion only accepts strings"))
        | Int   i   -> raise (Type_error ("rel_to_pvars helper funtion only accepts strings")))
    (Relation.min_elt rel) 


let empty = Constraint_Set.empty

let map f set =
    Constraint_Set.map f set
    
let is_empty set =
    Constraint_Set.is_empty set

let add c set =
    Constraint_Set.add c set
    
let singleton c =
    Constraint_Set.singleton c

let find_opt e set =
    Constraint_Set.find_opt e set

let get_max csrel = 
    let max = ref 0 in
    List.iter (fun cs -> List.iter (fun p -> if p > !max then max := p;) cs.partitions) csrel;
    !max