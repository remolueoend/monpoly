open Predicate

type share = int array

type domain = 
  | Some of cst
  | None

type domain_set
type heavy = int * domain_set

type hypercube_slicer = {
  formula: MFOTL.formula;
  heavy:  heavy array;
  shares: share array;
  seed: int
}