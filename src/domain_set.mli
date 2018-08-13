type domain
type domain_set

type heavy = int * domain_set

type split_save_parameters = (heavy array * int array array * int array array)

val domain_empty: domain_set
val domain_of_string: Predicate.tcst -> string -> domain
val domain_set_from_list: Predicate.tcst -> string list -> domain_set
val contains_cst: Predicate.cst -> domain_set -> bool