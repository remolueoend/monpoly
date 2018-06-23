open Helper
open Extformula
open Mformula

val comb_e: Extformula.extformula -> Extformula.extformula -> Extformula.extformula

val combine_neval: (int * MFOTL.timestamp) Extformula.NEval.dllist -> (int * MFOTL.timestamp) Extformula.NEval.dllist -> (int * MFOTL.timestamp) Extformula.NEval.dllist

val split_formula: Helper.splitParameters -> string -> int -> MFOTL.timestamp -> Extformula.extformula -> bool -> (int * MFOTL.timestamp) Extformula.NEval.dllist -> mformula array