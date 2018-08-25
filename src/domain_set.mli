type domain
type domain_set

type heavy = int * domain_set
type heavy_unproc = int * string list

type split_save_parameters = (heavy_unproc array * int array array * int array array)

type formula_pred = { pvar: Predicate.var; ptcst: Predicate.tcst} 

val predicates: formula_pred list ref


val domain_empty: domain_set
val domain_of_string: Predicate.tcst -> string -> domain
val domain_set_from_list_basic: string list -> domain_set
val domain_set_from_list: Predicate.tcst -> string list -> domain_set
val contains_cst: Predicate.cst -> domain_set -> bool