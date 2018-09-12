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

type mezinfo = { mezauxrels:  (int * timestamp * relation) Dllist.dllist}

type meinfo  = { meauxrels:  (timestamp * relation) Dllist.dllist}


(*  IMPORTANT/TODO
    The int pointers in the marshalled states can only be used if we work under the assumption that:
    1. Each split state marshals the whole formula (given by implementation)
    2. Each Monpoly instance receives all timepoints, without filtering at the source (dependent on the scope of the project)

    If 2. is no longer given by the project, the pointers will be different for different Monpoly instances and can no longer just be combined when merging
*)
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

type state = (timestamp * bool * mformula * (int * timestamp) array * int * bool)

(* For each formula, returns list of relevant free variables according to sub structure *)
let free_vars f =
  let pvars p = Predicate.pvars p in
  let rec get_pred = function
  | MRel           (_)                    -> []
  | MPred          (p, _, _)              -> pvars p
  | MNeg           (f1)                   -> get_pred f1
  | MAnd           (_, f1, f2, _)         -> Misc.union (get_pred f1) (get_pred f2)
  | MOr            (_, f1, f2, _)         -> Misc.union (get_pred f1) (get_pred f2)
  (* Utilize comp to map away unwanted elements of pvars *)
  | MExists        (comp, f1)             -> Helper.rel_to_pvars (comp (Helper.pvars_to_rel(get_pred f1))   )
  | MAggreg        (_, f1)                -> get_pred f1
  | MAggOnce       (f1, _, _, _, _, _)    -> get_pred f1
  | MAggMMOnce     (f1, _, _, _, _, _)    -> get_pred f1
  | MPrev          (_, f1, _)             -> get_pred f1
  | MNext          (_, f1, _)             -> get_pred f1
  | MSinceA        (_, _, f1, f2, _)      -> Misc.union (get_pred f1) (get_pred f2)
  | MSince         (_, _, f1, f2, _)      -> Misc.union (get_pred f1) (get_pred f2)
  | MOnceA         (_, f1, _)             -> get_pred f1
  | MOnceZ         (_, f1, _)             -> get_pred f1
  | MOnce          (_, f1, _)             -> get_pred f1
  | MNUntil        (_, _, f1, f2, _)      -> Misc.union (get_pred f1) (get_pred f2)
  | MUntil         (_, _, f1, f2, _)      -> Misc.union (get_pred f1) (get_pred f2)
  | MEventuallyZ   (_, f1, _)             -> get_pred f1
  | MEventually    (_, f1, _)             -> get_pred f1
  in
  get_pred f

  (* For each formula, returns list of relevant free variables according to sub structure *)
let predicates f =
  print_endline "Retrieving predicates";
  let rec get_pred = function
  | MRel           (_)                    -> []
  | MPred          (p, _, _)              -> p :: []
  | MNeg           (f1)                   -> get_pred f1
  | MAnd           (_, f1, f2, _)         -> Misc.union (get_pred f1) (get_pred f2)
  | MOr            (_, f1, f2, _)         -> Misc.union (get_pred f1) (get_pred f2)
  (* Utilize comp to map away unwanted elements of pvars *)
  | MExists        (comp, f1)             -> get_pred f1
  | MAggreg        (_, f1)                -> get_pred f1
  | MAggOnce       (f1, _, _, _, _, _)    -> get_pred f1
  | MAggMMOnce     (f1, _, _, _, _, _)    -> get_pred f1
  | MPrev          (_, f1, _)             -> get_pred f1
  | MNext          (_, f1, _)             -> get_pred f1
  | MSinceA        (_, _, f1, f2, _)      -> Misc.union (get_pred f1) (get_pred f2)
  | MSince         (_, _, f1, f2, _)      -> Misc.union (get_pred f1) (get_pred f2)
  | MOnceA         (_, f1, _)             -> get_pred f1
  | MOnceZ         (_, f1, _)             -> get_pred f1
  | MOnce          (_, f1, _)             -> get_pred f1
  | MNUntil        (_, _, f1, f2, _)      -> Misc.union (get_pred f1) (get_pred f2)
  | MUntil         (_, _, f1, f2, _)      -> Misc.union (get_pred f1) (get_pred f2)
  | MEventuallyZ   (_, f1, _)             -> get_pred f1
  | MEventually    (_, f1, _)             -> get_pred f1
  in
  get_pred f