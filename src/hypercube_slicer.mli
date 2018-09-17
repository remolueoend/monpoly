open Predicate
open Domain_set

type var_id

type hypercube_slicer = {
  formula: Mformula.mformula;
  variables_in_order: var_id array;
  heavy:  heavy array;
  shares: int array array;
  seeds: int array array;
  strides: int array array;
  degree: int;
}

val convert_heavy: Mformula.mformula -> heavy_unproc array -> heavy array

val create_slicer: Mformula.mformula -> heavy array -> int array array -> int array array -> hypercube_slicer

val add_slices_of_valuation: hypercube_slicer -> Tuple.tuple -> Predicate.var list -> int array
val return_shares: hypercube_slicer -> Predicate.cst option array -> int array

val convert_slicing_tuple: hypercube_slicer -> string list -> string list -> Predicate.cst option array