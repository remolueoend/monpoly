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
  | MRel of relation * int
  | MPred of predicate * comp_one * info * int
  | MLet of predicate * comp_one * mformula * mformula * Neval.cell * int
  | MNeg of mformula * int
  | MAnd of comp_two * mformula * mformula * ainfo * int
  | MOr of comp_two * mformula * mformula * ainfo * int
  | MExists of comp_one * mformula * int
  | MAggreg of agg_info * Aggreg.aggregator * mformula * int
  | MAggOnce of agg_info * Aggreg.once_aggregator * mformula * int
  | MPrev of interval * mformula * pinfo * int
  | MNext of interval * mformula * ninfo * int
  | MSinceA of comp_two * interval * mformula * mformula * sainfo * int
  | MSince of comp_two * interval * mformula * mformula * sinfo * int
  | MOnceA of interval * mformula * oainfo * int
  | MOnceZ of interval * mformula * mozinfo * int
  | MOnce of interval * mformula  * moinfo * int
  | MNUntil of comp_two * interval * mformula * mformula * muninfo * int
  | MUntil of comp_two * interval * mformula * mformula * muinfo * int
  | MEventuallyZ of interval * mformula * mezinfo * int
  | MEventually of interval * mformula * meinfo * int

val free_vars: mformula -> Predicate.var list
val predicates: mformula -> Predicate.predicate list
