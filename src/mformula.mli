open Extformula
open Predicate
open Relation
open Tuple
open MFOTL

(* Immutable version of types used in eformula *)
type mozinfo = { mozauxrels: (int * timestamp * relation) Dllist.dllist}

type moinfo  = { moauxrels: (timestamp * relation) Dllist.dllist}

type msainfo = { msres: relation;
                 msarel2: relation option;
                 msaauxrels: (timestamp * relation) Mqueue.t}
type msinfo  = { msrel2: relation option;
                 msauxrels: (timestamp * relation) Mqueue.t}

type mezinfo = { mezlastev: Neval.cell;
                 mezauxrels: (int * timestamp * relation) Dllist.dllist}

type meinfo  = { melastev: Neval.cell;
                 meauxrels: (timestamp * relation) Dllist.dllist}

type muinfo  = { mulast   :  Neval.cell;
                 mufirst  :  bool;
                 mures    :  relation;
                 murel2   :  relation option;
                 mraux    :  (int * timestamp * (int * relation) Sk.dllist) Sj.dllist;
                 msaux    :  (int * relation) Sk.dllist}
type muninfo = { mlast1   :  Neval.cell;
                 mlast2   :  Neval.cell;
                 mlistrel1:  (int * timestamp * relation) Dllist.dllist;
                 mlistrel2:  (int * timestamp * relation) Dllist.dllist;}

(* Immutable version of eformula used for marshalling *)
type mformula =
  | MRel of relation
  | MPred of predicate * comp_one * info
  | MLet of predicate * comp_one * mformula * mformula * Neval.cell
  | MNeg of mformula
  | MAnd of comp_two * mformula * mformula * ainfo
  | MOr of comp_two * mformula * mformula * ainfo
  | MExists of comp_one * mformula
  | MAggreg of agg_info * Aggreg.aggregator * mformula
  | MAggOnce of agg_info * Aggreg.once_aggregator * mformula
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

type state = (timestamp * bool * mformula * Neval.queue * Neval.cell * int * bool)

val free_vars: mformula -> Predicate.var list
val predicates: mformula -> Predicate.predicate list
