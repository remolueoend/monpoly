

open Libmonpoly.MFOTL
open Libmonpoly.Predicate

type genformula

module IntMap : Map.S with type key = int
module Set : Set.S with type elt = string

val generate_formula: ?signature:Set.t IntMap.t -> ?max_lb:int -> ?max_interval:int -> ?past_only:bool -> ?all_rels:bool -> ?aggr:bool -> ?foo:bool -> ?ndi:bool -> ?max_const:int -> ?qtl:bool -> int -> int -> (Set.t IntMap.t * genformula)

val string_of_genformula_qtl: genformula -> string

val string_of_genformula: genformula -> string
val string_of_sig: Set.t IntMap.t -> string
