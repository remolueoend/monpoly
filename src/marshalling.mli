open Extformula
open Mformula

(*val marshal: string -> int -> MFOTL.timestamp -> Extformula.extformula -> bool -> (int * MFOTL.timestamp) Extformula.NEval.dllist -> unit
val unmarshal: string -> int * MFOTL.timestamp * Extformula.extformula * bool * (int * MFOTL.timestamp) Extformula.NEval.dllist * int * int * bool
val merge_formulas: string list -> int * MFOTL.timestamp * Extformula.extformula * bool * (int * MFOTL.timestamp) Extformula.NEval.dllist * int * int * bool*)

val ext_to_m: Extformula.extformula ->  (int * MFOTL.timestamp) Extformula.NEval.dllist -> (int * MFOTL.timestamp) array * mformula
val m_to_ext: mformula -> (int * MFOTL.timestamp) Extformula.NEval.dllist -> Extformula.extformula