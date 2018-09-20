val finalize_hash: int32 -> int -> int32
val string_hash: string -> int32 -> int32
val mix_last: int32 -> int32 -> int32
val mix: int -> int -> int32

(* Helper classes, abstracting away Int32 conversion to match Scala int *)
val logor: int -> int -> int
val logxor: int -> int -> int
val logand: int -> int -> int
val shift_left: int -> int -> int
val shift_right: int -> int -> int
val shift_right_logical: int -> int -> int