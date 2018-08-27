open Helper
open Extformula
open Mformula

val print_ef: Extformula.extformula -> unit
val comb_m: mformula -> mformula -> mformula
val combine_neval: (int * MFOTL.timestamp) Extformula.NEval.dllist -> (int * MFOTL.timestamp) Extformula.NEval.dllist -> (int * MFOTL.timestamp) Extformula.NEval.dllist

val split_formula: Helper.splitParameters -> Mformula.mformula -> Mformula.mformula array
val split_with_slicer: (Tuple.tuple -> Predicate.var list -> int array) -> int -> Mformula.mformula -> Mformula.mformula array