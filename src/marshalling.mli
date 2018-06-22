
open Dllist
open Predicate
open MFOTL
open Tuple
open Relation
open Sliding
open Ext_formula

(* Immutable version of types used in eformula *)
type mozinfo = { moztree: (int, relation) Sliding.stree;
                 mozlast: int;
                 mozauxrels: (int * timestamp * relation) Dllist.dllist}

type moinfo  = { motree: (timestamp, relation) Sliding.stree;
                 molast: int;
                 moauxrels: (timestamp * relation) Dllist.dllist}

type msainfo = { msres: relation;
                 msarel2: relation option;
                 msaauxrels: (timestamp * relation) Mqueue.t}
type msinfo  = { msrel2: relation option;
                 msauxrels: (timestamp * relation) Mqueue.t}

type mezinfo = { mezlastev :  int;
                 meztree   :  (int , relation) Sliding.stree;
                 mezlast   :  int;
                 mezauxrels:  (int * timestamp * relation) Dllist.dllist}

type meinfo  = { melastev :  int;
                 metree   :  (timestamp, relation) Sliding.stree;
                 melast   :  int;
                 meauxrels:  (timestamp * relation) Dllist.dllist}

type muinfo  = { mulast   :  int;
                 mufirst  :  bool;
                 mures    :  relation;
                 murel2   :  relation option;
                 mraux    :  (int * timestamp * (int * relation) Sk.dllist) Sj.dllist;
                 msaux    :  (int * relation) Sk.dllist}
type muninfo = { mlast1   :  int;
                 mlast2   :  int;
                 mlistrel1:  (int * timestamp * relation) Dllist.dllist;
                 mlistrel2:  (int * timestamp * relation) Dllist.dllist;}

(* Immutable version of eformula used for marshalling *)
type mformula =
  | MRel of relation
  | MPred of predicate * comp_one * info
  | MNeg of mformula
  | MAnd of comp_two * mformula * mformula * ainfo
  | MOr of comp_two * mformula * mformula * ainfo
  | MExists of comp_one * mformula
  | MAggreg of comp_one * mformula
  | MAggOnce of mformula * interval * agg_once_state *
                (agg_once_state -> (tuple * tuple * cst) list -> unit) *
                (agg_once_state -> relation -> (tuple * tuple * cst) list) *
                (agg_once_state -> relation)
  | MAggMMOnce of mformula * interval * aggMM_once_state *
                  (aggMM_once_state -> timestamp -> unit) *
                  (aggMM_once_state -> timestamp -> relation -> unit) *
                  (aggMM_once_state -> relation)
  | MPrev of interval * mformula * pinfo
  | MNext of interval * mformula * ninfo
  | MSinceA of comp_two * interval * mformula * mformula * sainfo
  | MSince of comp_two * interval * mformula * mformula * sinfo
  | MOnceA of interval * mformula * oainfo
  | MOnceZ of interval * mformula * mozinfo
  | MOnce of interval * mformula  * moinfo
  | MNUntil of comp_two * interval * mformula * mformula * muninfo
  | MUntil of comp_two * interval * mformula * mformula * muinfo
  | MEventuallyZ of interval * mformula * mezinfo
  | MEventually of interval * mformula * meinfo

type state = (int * timestamp * bool * mformula * (int * timestamp) array * int * int * bool)

(*val marshal: string -> int -> MFOTL.timestamp -> Ext_formula.extformula -> bool -> (int * MFOTL.timestamp) Ext_formula.NEval.dllist -> unit
val unmarshal: string -> int * MFOTL.timestamp * Ext_formula.extformula * bool * (int * MFOTL.timestamp) Ext_formula.NEval.dllist * int * int * bool
val merge_formulas: string list -> int * MFOTL.timestamp * Ext_formula.extformula * bool * (int * MFOTL.timestamp) Ext_formula.NEval.dllist * int * int * bool*)

val ext_to_m: Ext_formula.extformula ->  (int * MFOTL.timestamp) Ext_formula.NEval.dllist -> (int * MFOTL.timestamp) array * mformula
val m_to_ext: mformula -> (int * MFOTL.timestamp) Ext_formula.NEval.dllist -> Ext_formula.extformula

val comb_e: Ext_formula.extformula -> Ext_formula.extformula -> Ext_formula.extformula

val combine_neval: (int * MFOTL.timestamp) Ext_formula.NEval.dllist -> (int * MFOTL.timestamp) Ext_formula.NEval.dllist -> (int * MFOTL.timestamp) Ext_formula.NEval.dllist

val split_formula: Helper.splitParameters -> string -> int -> MFOTL.timestamp -> Ext_formula.extformula -> bool -> (int * MFOTL.timestamp) Ext_formula.NEval.dllist -> mformula array