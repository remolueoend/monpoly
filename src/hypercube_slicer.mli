open Predicate
open Domain_set

type hypercube_slicer = {
  formula: Mformula.mformula;
  heavy:  heavy array;
  shares: int array array;
  seeds: int array array;
  strides: int array array;
  degree: int;
}

val create_slicer: Mformula.mformula -> heavy array -> int array array -> int array array -> hypercube_slicer

val add_slices_of_valuation: hypercube_slicer -> Tuple.tuple -> Predicate.var list -> int array