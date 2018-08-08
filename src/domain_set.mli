type domain
type domain_set

type heavy = int * domain_set

type split_save_parameters = (string * heavy array * int array array * int array array)

val domain_empty: domain_set
val contains_cst: Predicate.cst -> domain_set -> bool