type share = int array

type integral_value = int
type string_value   = string

type domain = 
  | IntegralValue of integral_value
  | StringValue   of string_value

type domain_set
type heavy = int * domain_set

type hypercube_slicer = {
  formula: MFOTL.formula;
  heavy:  heavy array;
  shares: share array;
  seed: int
}