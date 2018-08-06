val finalize_hash: int -> int -> int
val string_hash: string -> int -> int
val mix_last: int -> int -> int
val mix: int -> int -> int

(* Helper classes, abstracting away Int32 conversion to match Scala int *)
val logor: int -> int -> int
val logxor: int -> int -> int
val logand: int -> int -> int
val shift_left: int -> int -> int
val shift_right: int -> int -> int
val shift_right_logical: int -> int -> int