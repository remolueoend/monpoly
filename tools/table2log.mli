open Predicate

val log2table: string -> (string -> int list -> unit) -> unit

val read_query: string -> string * (string * tcst) list

val print_res: out_channel -> (string * tcst) list -> string array array -> unit


val update: (string option array -> string array) -> (string * tcst) list -> string option array -> unit 
val mysql_write: out_channel -> unit 
