

open MFOTL
open Predicate

type genformula

module IntMap : Map.S with type key = int
module Set : Set.S with type elt = string

val formula_gen: ?signature:(Set.t * IntMap.key) list -> ?max_lb:int -> ?max_interval:int -> ?past_only:bool -> int -> int -> (Set.t IntMap.t * genformula) Random_generator.gen

val string_of_genformula: genformula -> string