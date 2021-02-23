type int_map 

val singleton: Predicate.cst -> int -> int_map
val choose: int_map -> Predicate.cst  * int
val iter:  (Predicate.cst -> int -> unit) -> int_map -> unit

val find: Predicate.cst -> int_map -> int
val remove: Predicate.cst -> int_map -> int_map
val add: Predicate.cst -> int -> int_map -> int_map
val update: Predicate.cst -> (int option -> int option) -> int_map -> int_map

val sum: int_map -> int
