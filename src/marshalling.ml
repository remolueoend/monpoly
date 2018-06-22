
(*
  SAVING AND LOADING STATE
*)

open Dllist
open Misc
open Predicate
open MFOTL
open Tuple
open Relation
open Log
open Sliding
open Helper
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

let ext_to_m ff neval =
  let eze2m ezinf =
      let ilast = if ezinf.ezlastev == NEval.void then -2
      else (* note that neval is not empty in this case *)
  	if not (NEval.is_last neval ezinf.ezlastev) && NEval.get_next neval ezinf.ezlastev == NEval.get_first_cell neval then
  	  (* in this case inf.last does not point to an element of
  	     neval; however, it points to the first element of neval *)
  	  -1
  	else NEval.get_index ezinf.ezlastev neval
    in
    let mezlast = if ezinf.ezlast == Dllist.void then -1 else Dllist.get_index ezinf.ezlast ezinf.ezauxrels in
    assert(ilast < NEval.length neval);
      {mezlastev = ilast;
       meztree = ezinf.eztree;
       mezlast = mezlast;
       mezauxrels = ezinf.ezauxrels}
  in
  let ee2m einf =
    let ilast = if einf.elastev == NEval.void then -2
    else (* note that neval is not empty in this case *)
	if not (NEval.is_last neval einf.elastev) && NEval.get_next neval einf.elastev == NEval.get_first_cell neval then
	  (* in this case inf.last does not point to an element of
	     neval; however, it points to the first element of neval *)
	  -1
  else NEval.get_index einf.elastev neval
    in
    let melast = if einf.elast == Dllist.void then -1 else Dllist.get_index einf.elast einf.eauxrels in
    assert(ilast < NEval.length neval);
    {melastev = ilast;
     metree = einf.etree;
     melast = melast;
     meauxrels = einf.eauxrels}
  in
  let mue2m uinf =
    let ilast =
      if uinf.ulast == NEval.void then -2
      else if not (NEval.is_last neval uinf.ulast) && NEval.get_next neval uinf.ulast == NEval.get_first_cell neval then -1
      else NEval.get_index uinf.ulast neval
    in
    assert(ilast < NEval.length neval);
        {mulast = ilast;
         mufirst = uinf.ufirst;
         mures = uinf.ures;
         murel2 = uinf.urel2;
         (* TODO: transform these too *)
         mraux = uinf.raux;
         msaux = uinf.saux;
        }
  in
  let mune2m uninf =
    let ilast1 = if uninf.last1 == NEval.void then -2
        else (* note that neval is not empty in this case *)
        if not (NEval.is_last neval uninf.last1) && NEval.get_next neval uninf.last1 == NEval.get_first_cell neval then
          (* in this case inf.last does not point to an element of
             neval; however, it points to the first element of neval *)
          -1
        else NEval.get_index uninf.last1 neval
    in
    let ilast2 = if uninf.last2 == NEval.void then -2
        else (* note that neval is not empty in this case *)
        if not (NEval.is_last neval uninf.last2) && NEval.get_next neval uninf.last2 == NEval.get_first_cell neval then
          (* in this case inf.last does not point to an element of
             neval; however, it points to the first element of neval *)
          -1
        else NEval.get_index uninf.last2 neval
    in
        {
          mlast1 = ilast1;
          mlast2 = ilast2;
          mlistrel1 = uninf.listrel1;
          mlistrel2 = uninf.listrel2;
        }
  in
  let o2m oinf =
    let molast = if oinf.olast = Dllist.void then -1 else Dllist.get_index oinf.olast oinf.oauxrels in
    { motree = oinf.otree; molast = molast; moauxrels = oinf.oauxrels }
  in
  let oz2m ozinf =
    let mozlast = if ozinf.ozlast = Dllist.void then -1 else Dllist.get_index ozinf.ozlast ozinf.ozauxrels in
    { moztree = ozinf.oztree; mozlast = mozlast; mozauxrels = ozinf.ozauxrels}
  in
  let a = NEval.to_array neval in
  let rec e2m = function
    | ERel           (rel)                                                -> MRel           (rel)
    | EPred          (pred, c1, inf)                                      -> MPred          (pred, c1, inf)
    | ENeg           (ext)                                                -> MNeg           (e2m ext)
    | EAnd           (c2, ext1, ext2, ainf)                               -> MAnd           (c2, (e2m ext1), (e2m ext2), ainf)
    | EOr            (c2, ext1, ext2, ainf)                               -> MOr            (c2, (e2m ext1), (e2m ext2), ainf)
    | EExists        (c1, ext)                                            -> MExists        (c1, (e2m ext))
    | EAggreg        (c1, ext)                                            -> MAggreg        (c1, (e2m ext))
    | EAggOnce       (ext, dt, agg, update_old, update_new, get_result)   -> MAggOnce       ((e2m ext), dt, agg, update_old, update_new, get_result)
    | EAggMMOnce     (ext, dt, aggMM, update_old, update_new, get_result) -> MAggMMOnce     ((e2m ext), dt, aggMM, update_old, update_new, get_result)
    | EPrev          (dt, ext, pinf)                                      -> MPrev          (dt, (e2m ext), pinf)
    | ENext          (dt, ext, ninf)                                      -> MNext          (dt, (e2m ext), ninf)
    | ESinceA        (c2, dt, ext1, ext2, sainf)                          -> MSinceA        (c2, dt, (e2m ext1), (e2m ext2), sainf)
    | ESince         (c2, dt, ext1, ext2, sinf)                           -> MSince         (c2, dt, (e2m ext1), (e2m ext2), sinf)
    | EOnceA         (dt, ext, oainf)                                     -> MOnceA         (dt, (e2m ext), oainf)
    | EOnceZ         (dt, ext, ozinf)                                     -> MOnceZ         (dt, (e2m ext), (oz2m ozinf))
    | EOnce          (dt, ext, oinf)                                      -> MOnce          (dt, (e2m ext), (o2m oinf))
    | ENUntil        (c1, dt, ext1, ext2, uninf)                          -> MNUntil        (c1, dt, (e2m ext1), (e2m ext2), (mune2m uninf))
    | EUntil         (c1, dt, ext1, ext2, uinf)                           -> MUntil         (c1, dt, (e2m ext1), (e2m ext2), (mue2m uinf))
    | EEventuallyZ   (dt, ext, ezinf)                                     -> MEventuallyZ   (dt, (e2m ext), (eze2m ezinf))
    | EEventually    (dt, ext, einf)                                      -> MEventually    (dt, (e2m ext), (ee2m einf))
  in a, e2m ff


let m_to_ext mf neval =
  let mez2e mezinf =
    let cell =
      if      mezinf.mezlastev = -2 then NEval.void
      else if mezinf.mezlastev = -1 then NEval.new_cell (-1,MFOTL.ts_invalid) neval
      else                               NEval.get_cell_at_index mezinf.mezlastev neval
    in
    let ezlast =
       if mezinf.mezlast = -1 then Dllist.void
       else Dllist.get_cell_at_index mezinf.mezlast mezinf.mezauxrels
    in
    let f = fun (j,_,rel) -> (j,rel) in
    (* Pass void as last element, forcing rebuild over whole list *)
    let tree_list = Helper.convert_dll mezinf.mezauxrels Dllist.void f in
    let meztree   = Sliding.build_rl_tree_from_seq Relation.union tree_list in
    {ezlastev   = cell;
     eztree     = meztree;
     ezlast     = ezlast;
     ezauxrels  = mezinf.mezauxrels}
  in
  let me2e meinf =
    let cell =
      if      meinf.melastev = -2  then NEval.void
      else if meinf.melastev = -1  then NEval.new_cell (-1,MFOTL.ts_invalid) neval
      else                              NEval.get_cell_at_index meinf.melastev neval
    in
    let elast =
      if meinf.melast = -1 then Dllist.void
      else Dllist.get_cell_at_index meinf.melast meinf.meauxrels
    in
    (* Pass void as last element, forcing rebuild over whole list *)
    let tree_list = Helper.convert_dll meinf.meauxrels Dllist.void (fun x -> x) in
    let metree    = Sliding.build_rl_tree_from_seq Relation.union tree_list in
    {elastev    = cell;
     etree      = metree;
     elast      = elast;
     eauxrels   = meinf.meauxrels}
  in
  let mu2e muinf =
    let cell =
      if      muinf.mulast = -2 then NEval.void
      else if muinf.mulast = -2 then NEval.new_cell (-1,MFOTL.ts_invalid) neval
      else                           NEval.get_cell_at_index muinf.mulast neval
    in
    {ulast  = cell;
     ufirst = muinf.mufirst;
     ures   = muinf.mures;
     urel2  = muinf.murel2;
     raux   = muinf.mraux;
     saux   = muinf.msaux;
    }
  in
  let mun2e muninf =
     let cell1 =
          if      muninf.mlast1 = -2 then NEval.void
          else if muninf.mlast1 = -2 then NEval.new_cell (-1,MFOTL.ts_invalid)  neval
          else                            NEval.get_cell_at_index muninf.mlast1 neval
    in
     let cell2 =
          if      muninf.mlast2 = -2 then NEval.void
          else if muninf.mlast2 = -2 then NEval.new_cell (-1,MFOTL.ts_invalid) neval
          else                            NEval.get_cell_at_index muninf.mlast2 neval
    in
    {last1 = cell1;
     last2 = cell2;
     listrel1 = muninf.mlistrel1;
     listrel2 = muninf.mlistrel2;
    }
  in
  let mo2e moinf =
    let olast =
      if moinf.molast = -1 then Dllist.void
      else Dllist.get_cell_at_index moinf.molast moinf.moauxrels
    in
    (* Pass void as last element, forcing rebuild over whole list *)
    let tree_list = Helper.convert_dll moinf.moauxrels Dllist.void (fun x -> x) in
    let otree = Sliding.build_rl_tree_from_seq Relation.union tree_list in
    { otree = otree; olast = olast; oauxrels = moinf.moauxrels }
  in
  let moz2e mozinf =
    let ozlast =
      if mozinf.mozlast = -1 then Dllist.void
      else Dllist.get_cell_at_index mozinf.mozlast mozinf.mozauxrels
    in
    let f = fun (j,_,rel) -> (j,rel) in
    (* Converts dlllist to normal list, using structure of get_new_elements *)
    (* Pass void as last element, forcing rebuild over whole list *)
    let tree_list = Helper.convert_dll mozinf.mozauxrels Dllist.void f in
    (* Build tree from whole auxrels relation list *)
    let oztree = Sliding.build_rl_tree_from_seq Relation.union tree_list in
    (* Last element is still saved, should ensure that the tree can be reused wholly*)
    { oztree = oztree; ozlast = ozlast; ozauxrels = mozinf.mozauxrels }
  in
  let rec m2e = function
    | MRel           (rel)                                                    ->      ERel           (rel)
    | MPred          (pred, c1, inf)                                          ->      EPred          (pred, c1, inf)
    | MNeg           (mf)                                                     ->      ENeg           ((m2e mf))
    | MAnd           (c2, mf1, mf2, ainf)                                     ->      EAnd           (c2, (m2e mf1), (m2e mf2), ainf)
    | MOr            (c2, mf1, mf2, ainf)                                     ->      EOr            (c2, (m2e mf1), (m2e mf2), ainf)
    | MExists        (c1, mf)                                                 ->      EExists        (c1, (m2e mf))
    | MAggreg        (c1, mf)                                                 ->      EAggreg        (c1, (m2e mf))
    | MAggOnce       (mf, dt, agg, update_old, update_new, get_result)        ->      EAggOnce       ((m2e mf), dt, agg, update_old, update_new, get_result)
    | MAggMMOnce     (mf, dt, aggMM, update_old, update_new, get_result)      ->      EAggMMOnce     ((m2e mf), dt, aggMM, update_old, update_new, get_result)
    | MPrev          (dt, mf, pinf)                                           ->      EPrev          (dt, (m2e mf), pinf)
    | MNext          (dt, mf, ninf)                                           ->      ENext          (dt, (m2e mf), ninf)
    | MSinceA        (c2, dt, mf1, mf2, sainf)                                ->      ESinceA        (c2, dt, (m2e mf1), (m2e mf2), sainf)
    | MSince         (c2, dt, mf1, mf2, sinf)                                 ->      ESince         (c2, dt, (m2e mf1), (m2e mf2), sinf)
    | MOnceA         (dt, mf, oainf)                                          ->      EOnceA         (dt, (m2e mf), oainf)
    | MOnceZ         (dt, mf, ozinf)                                          ->      EOnceZ         (dt, (m2e mf), (moz2e ozinf))
    | MOnce          (dt, mf, oinf)                                           ->      EOnce          (dt, (m2e mf), (mo2e oinf))
    | MNUntil        (c1, dt, mf1, mf2, muninf)                               ->      ENUntil        (c1, dt, (m2e mf1), (m2e mf2), (mun2e muninf))
    | MUntil         (c1, dt, mf1, mf2, muinf)                                ->      EUntil         (c1, dt, (m2e mf1), (m2e mf2), (mu2e muinf))
    | MEventuallyZ   (dt, mf, mezinf)                                         ->      EEventuallyZ   (dt, (m2e mf), (mez2e mezinf))
    | MEventually    (dt, mf, meinf)                                          ->      EEventually    (dt, (m2e mf), (me2e  meinf))
  in m2e mf

(* END SAVING AND LOADING STATE *)


exception Type_error of string

(* SPLITTING & COMBINING STATE *)

let rel_u r1 r2 = Relation.union r1 r2

let combine_queues1 q1 q2 =  
  let tmp = Queue.create() in
  let nq = Queue.create() in
  Queue.iter (fun e ->
    let i, ts, r1 = e in
    let _, _,  r2 = Queue.pop q2 in
    Queue.add (i, ts, (rel_u r1 r2)) tmp;
  ) q1;
  (* Need to reverse the queue *)
  Queue.iter (fun _ -> Queue.add (Queue.pop tmp) nq) tmp;
  nq

let combine_queues2 q1 q2 =  
  let tmp = Queue.create() in
  let nq = Queue.create() in
  Queue.iter (fun e ->
    let ts, r1 = e in
    let _,  r2 = Queue.pop q2 in
    Queue.add (ts, (rel_u r1 r2)) tmp;
  ) q1;
  (* Need to reverse the queue *)
  Queue.iter (fun _ -> Queue.add (Queue.pop tmp) nq) tmp;
  nq

let combine_mq q1 q2 =
  Mqueue.update (fun e ->
  let ts, r1  = e in
  let _,  r2  = Mqueue.pop q2 in (ts, (rel_u r1 r2))) q1;
  q1

let combine_dll1 l1 l2 =  
  let res = Dllist.empty() in
    Dllist.iter (fun e ->
      let i, ts, r1 = e in
      let _, _,  r2 = Dllist.pop_first l2 in
      Dllist.add_last (i, ts, (rel_u r1 r2)) res
    ) l1;
    res

let combine_dll2 l1 l2 =  
  let res = Dllist.empty() in
    Dllist.iter (fun e ->
      let ts, r1 = e in
      let _,  r2 = Dllist.pop_first l2 in
      Dllist.add_last (ts, (rel_u r1 r2)) res
    ) l1;
    res   

let combine_info  inf1 inf2 =
  combine_queues1 inf1 inf2

let combine_ainfo ainf1 ainf2 =
  let urel = match (ainf1.arel, ainf2.arel) with
  | (Some r1, Some r2) -> Some (rel_u r1 r2)
  | (None, None) -> None
  | _ -> raise (Type_error ("Mismatched states in ainfo"))
  in
  { arel = urel; }

let combine_agg  agg1 agg2 =
  let other_rels = combine_queues2 agg1.other_rels agg2.other_rels in
  {tw_rels = agg1.tw_rels; other_rels = other_rels; mset = agg1.mset; hres = agg1.hres }

let combine_aggMM agg1 agg2 =
  let non_tw_rels = combine_queues2 agg1.non_tw_rels agg2.non_tw_rels in
  {non_tw_rels = non_tw_rels; tbl = agg1.tbl }

let combine_sainfo sainf1 sainf2 =
  let sarel2 = match (sainf1.sarel2, sainf2.sarel2) with
  | (Some r1, Some r2) -> Some (rel_u r1 r2)
  | (None, None) -> None
  | _ -> raise (Type_error ("Mismatched states in ainfo"))
  in
  (* Verify correctness *)
  let saauxrels = combine_mq sainf1.saauxrels sainf2.saauxrels in
  {sres = (rel_u sainf1.sres sainf2.sres); sarel2 = sarel2; saauxrels = saauxrels}

let combine_sinfo sinf1 sinf2  =
  let srel2 = match (sinf1.srel2, sinf2.srel2) with
  | (Some r1, Some r2) -> Some (rel_u r1 r2)
  | (None, None) -> None
  | _ -> raise (Type_error ("Mismatched states in ainfo"))
  in
  (* Verify correctness *)
  let sauxrels = combine_mq sinf1.sauxrels sinf2.sauxrels in
  {srel2 = srel2; sauxrels = sauxrels}

let combine_muninfo uninf1 uninf2 =
    (* Verify correctness *)
  let listrel1 = combine_dll1 uninf1.listrel1 uninf2.listrel1 in 
  let listrel2 = combine_dll1 uninf1.listrel2 uninf2.listrel2 in 
  { last1 = uninf1.last1; last2 = uninf1.last2; listrel1 = listrel1;  listrel2 = listrel2 }

let combine_muinfo uinf1 uinf2 =
  (* Helper function to combine raux and saux fields *)
  let sklist l1 l2 =
    let nl = Sk.empty() in
    Sk.iter (fun e ->
      let i, r1 = e in
      (* Verify correctness *)
      let _, r2 = Sk.pop_first l2 in
      Sk.add_last (i, (rel_u r1 r2)) nl
    ) l1;
    nl
  in
  let raux =
    let nl = Sj.empty() in
    Sj.iter (fun e ->
      let (i, ts, l1) = e in
      let (_, _,  l2) = Sj.pop_first uinf2.raux in
      Sj.add_last (i, ts, (sklist l1 l2)) nl
    ) uinf1.raux;
    nl
  in
  let urel2 = match (uinf1.urel2, uinf2.urel2) with
  | (Some r1, Some r2) -> Some (rel_u r1 r2)
  | (None, None) -> None
  | _ -> raise (Type_error ("Mismatched states in ainfo"))
  in
  { ulast = uinf1.ulast; ufirst = uinf1.ufirst; ures = (rel_u uinf1.ures uinf2.ures);
    urel2 = urel2; raux = raux; saux = (sklist uinf1.saux uinf2.saux) }

let combine_ozinfo ozinf1 ozinf2 =
  (* Discuss this at meeting *)

  (* Need to get index, and get cell for that index on new combined auxrels
     Would work better with mformula, however that might have issues with neval indices for different reasons
    *)
  let index = Dllist.get_index ozinf1.ozlast ozinf1.ozauxrels in
  let ozauxrels = combine_dll1 ozinf1.ozauxrels ozinf2.ozauxrels in
  let ozlast = Dllist.get_cell_at_index index ozauxrels in

  (*Should this be done on each union or rather at the end? *)
  let f = fun (j,_,rel) -> (j,rel) in
  let tree_list = Helper.convert_dll ozauxrels Dllist.void f in 
  {oztree = Sliding.build_rl_tree_from_seq Relation.union tree_list; ozlast = ozlast; ozauxrels = ozauxrels }

let combine_oainfo oainf1 oainf2 =
  let oaauxrels = combine_mq oainf1.oaauxrels oainf2.oaauxrels in
  { ores = (rel_u oainf1.ores oainf2.ores); oaauxrels = oaauxrels }
  
let combine_oinfo oinf1 oinf2 =
  (* Verify, see combine_ozinfo *)
  let index = Dllist.get_index oinf1.olast oinf1.oauxrels in
  let oauxrels = combine_dll2 oinf1.oauxrels oinf2.oauxrels in
  let olast = Dllist.get_cell_at_index index oauxrels in

  let tree_list = Helper.convert_dll oauxrels Dllist.void (fun x -> x) in 
  {otree = Sliding.build_rl_tree_from_seq Relation.union tree_list; olast = olast; oauxrels = oauxrels }

let combine_ezinfo ezinf1 ezinf2 =
  (* Verify, see combine_ozinfo *)
  let index = Dllist.get_index ezinf1.ezlast ezinf2.ezauxrels in
  let ezauxrels = combine_dll1 ezinf1.ezauxrels ezinf2.ezauxrels in
  let ezlast = Dllist.get_cell_at_index index ezauxrels in

  let f = fun (j,_,rel) -> (j,rel) in
  let tree_list = Helper.convert_dll ezauxrels Dllist.void f in 
  {ezlastev = ezinf1.ezlastev; eztree = Sliding.build_rl_tree_from_seq Relation.union tree_list; ezlast = ezlast; ezauxrels = ezauxrels }

let combine_einfo einf1 einf2 =
   (* Verify, see combine_ozinfo *)
   let index = Dllist.get_index einf1.elast einf2.eauxrels in
   let eauxrels = combine_dll2 einf1.eauxrels einf2.eauxrels in
   let elast = Dllist.get_cell_at_index index eauxrels in
 
   let tree_list = Helper.convert_dll eauxrels Dllist.void (fun x -> x) in 
  {elastev = einf1.elastev; etree = Sliding.build_rl_tree_from_seq Relation.union tree_list; elast = elast; eauxrels = eauxrels }

let rec comb_e f1 f2  =
  match (f1,f2) with
    | (ERel  (rel1),          ERel(rel2))
      -> ERel (Relation.union rel1 rel2)
    | (EPred (p, comp, inf1), EPred(_, _, inf2))
      -> EPred(p, comp, combine_info inf1 inf2)
    | (ENeg  (f11), ENeg(f21))
      -> ENeg (comb_e f11 f21)
    | (EAnd  (c, f11, f12, ainf1), EAnd(_, f21, f22, ainf2))
      -> EAnd (c, comb_e f11 f21, comb_e f12 f22, (combine_ainfo ainf1 ainf2))
    | (EOr   (c, f11, f12, ainf1), EOr (_, f21, f22, ainf2))
      -> EOr  (c, comb_e f11 f21, comb_e f12 f22, (combine_ainfo ainf1 ainf2))
    | (EExists (c, f11), EExists(_,f21))
      -> EExists        (c, comb_e f11 f21)
    | (EAggreg (c, f11), EAggreg(_,f21))
      -> EAggreg        (c, comb_e f11 f21)
    | (EAggOnce (f11, dt, agg1, update_old, update_new, get_result), EAggOnce (f21, _, agg2, _, _, _))
      -> EAggOnce  (comb_e f11 f21, dt, combine_agg agg1 agg2, update_old, update_new, get_result)
    | (EAggMMOnce (f11, dt, aggMM1, update_old, update_new, get_result), EAggMMOnce (f21, _, aggMM2, _, _, _))
      -> EAggMMOnce (comb_e f11 f21, dt, combine_aggMM aggMM1 aggMM2, update_old, update_new, get_result)
    | (EPrev (dt, f11, pinf1), EPrev ( _, f21, pinf2))
      -> EPrev          (dt, comb_e f11 f21, pinf1)
    | (ENext (dt, f11, ninf1), ENext ( _, f21, ninf2))
      -> ENext          (dt, comb_e f11 f21, ninf1)
    | (ESinceA (c2, dt, f11, f12, sainf1), ESinceA( _, _, f21, f22, sainf2))
      -> ESinceA        (c2, dt, comb_e f11 f21, comb_e f12 f22, combine_sainfo sainf1 sainf2)
    | (ESince (c2, dt, f11, f12, sinf1), ESince( _, _, f21, f22, sinf2))
      -> ESince         (c2, dt, comb_e f11 f21, comb_e f12 f22, combine_sinfo sinf1 sinf2)
    | (EOnceA (dt, f11, oainf1), EOnceA ( _, f21, oainf2))
      -> EOnceA         (dt, comb_e f11 f21, combine_oainfo oainf1 oainf2)
    | (EOnceZ (dt, f11, ozinf1), EOnceZ ( _, f21, ozinf2))
      -> EOnceZ         (dt, comb_e f11 f21, combine_ozinfo ozinf1 ozinf2)
    | (EOnce (dt, f11, oinf1), EOnce ( _, f21, oinf2))
      -> EOnce        (dt, comb_e f11 f21, combine_oinfo oinf1 oinf2)
    | (ENUntil (c1, dt, f11, f12, muninf1), ENUntil  ( _, _, f21, f22, muninf2))
      -> ENUntil        (c1, dt, comb_e f11 f21, comb_e f12 f22, combine_muninfo muninf1 muninf2)
    | (EUntil (c1, dt, f11, f12, muinf1), EUntil ( _, _, f21, f22, muinf2))
      -> EUntil         (c1, dt, comb_e f11 f21, comb_e f12 f22, combine_muinfo muinf1 muinf2)
    | (EEventuallyZ (dt, f11, ezinf1), EEventuallyZ (_, f21, ezinf2))
      -> EEventuallyZ   (dt, comb_e f11 f21, combine_ezinfo ezinf1 ezinf2)
    | (EEventually (dt, f11, einf1), EEventually (_, f21, einf2))
      -> EEventually   (dt, comb_e f11 f21, combine_einfo einf1 einf2)
    | _ -> raise (Type_error ("Mismatched formulas in combine_states")) 

(* END COMBINING STATES *)


(* SPLITTING STATE *)
let get_predicate f =
  let pvars p = Predicate.pvars p in
  let rec get_pred = function
    (* Equal, Less, LessEq all mapped to free vars;  ForAll not used *)
  | MRel           (_)                    -> raise (Type_error ("Predicate function should not be entering ERel"))
  | MPred          (p, _, _)              -> pvars p
  | MNeg           (f1)                   -> get_pred f1
  | MAnd           (_, f1, f2, _)         -> Misc.union (get_pred f1) (get_pred f2)
  | MOr            (_, f1, f2, _)         -> Misc.union (get_pred f1) (get_pred f2)
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

let get_predicate2 f1 f2 =
  Misc.union (get_predicate f1) (get_predicate f2)

let list_to_string l =
  let str = ref "" in
  let append s = str := !str ^ s ^ ", " in
  List.iter (fun s -> append s ) l;
  !str

let int_list_to_string l =
  let str = ref "" in
  let append s = str := !str ^ (string_of_int s) ^ ", " in
  List.iter (fun s -> append s ) l;
  !str

let int_arr_to_string l =
  let str = ref "" in
  let append s = str := !str ^ (string_of_int s) ^ ", " in
  Array.iter (fun s -> append s ) l;
  !str
  

let pred_list_to_string l =
  let str = ref "" in
  let append s = str := !str ^ (Predicate.string_of_cst false s) ^ ", " in
  List.iter (fun s -> append s ) l;
  !str

let split_debug f op =
  Printf.printf "Predicate Names: (%s) for formula: '%s' \n" (list_to_string (get_predicate f)) op

let split_debug2 f1 f2 op =
  Printf.printf "Predicate Names: (%s) for formula: '%s' \n" (list_to_string (get_predicate2 f1 f2)) op

let get_1 (a,_) = a
let get_2 (_,b) = b

let comb_preds preds1 preds2 = List.append preds1 preds2

let check_tuple t vl =
  (*Printf.printf "Tlength: %d; VLength: %d \n" (List.length t) (List.length vl);*)
  (* Lists always have same length due to filtering in split function *)
  let eval = List.mapi (fun i e -> List.exists (fun e2 -> (List.nth t i) = e2) e) vl in
  List.fold_right (fun a agg -> (a || agg)) eval false

let split_state mapping mf size =
  let split rel preds =
    let res = Array.make size Relation.empty in
    (* Iterate over relation, adding tuples to relations of partitions where they are relevant *)
    Relation.iter (fun t -> let parts = mapping t preds in Array.iter (fun p -> res.(p) <- Relation.add t res.(p)) parts) rel;
    res
  in

  let split_queue1 q p =
    let res = Array.init size (fun i -> Queue.create()) in 
    Queue.iter (
      fun e -> 
      let i, ts, r  = e in
      let states = split r p in 
      Array.iteri (fun index s -> Queue.add (i, ts, s) res.(index)) states
    ) q;
    res
  in  
  let split_queue2 q p =
    let res = Array.init size (fun i -> Queue.create()) in 
    Queue.iter (
    fun e -> 
      let ts, r  = e in
      let states = split r p in 
      Array.iteri (fun index s -> Queue.add (ts, s) res.(index)) states
    ) q;   
    res
  in  
  let split_mqueue q p =
    let res = Array.init size (fun i -> Mqueue.create()) in 
    Mqueue.iter (
    fun e -> 
      let ts, r  = e in
      let states = split r p in 
      Array.iteri (fun index s -> Mqueue.add (ts, s) res.(index)) states
    ) q;    
    res
  in  
  let split_dll1 l p = 
    let res = Array.init size (fun i -> Dllist.empty()) in 
    Dllist.iter (
      fun e -> let i, ts, r  = e in
      let states = split r p in 
      Array.iteri (fun index s -> Dllist.add_last (i, ts, s) res.(index)) states
    ) l;
    res
  in
  let split_dll2 l p = 
    let res = Array.init size (fun i -> Dllist.empty()) in 
    Dllist.iter (
      fun e -> let ts, r  = e in
      let states = split r p in 
      Array.iteri (fun index s -> Dllist.add_last (ts, s) res.(index)) states
    ) l;
    res
  in
  let split_info inf p =
    split_queue1 inf p
  in
  let split_ainfo ainf p =
    let arr = Array.make size { arel = None } in 
    let res = match ainf.arel with
    | Some r -> let states = (split r p) in Array.map (fun s -> {arel = Some s}) states
    | None -> arr
    in
    res
  in
  let split_agg  agg p =
    let res = split_queue2 agg.other_rels p in
    Array.map (fun e ->   {tw_rels = agg.tw_rels; other_rels = e; mset = agg.mset; hres = agg.hres }) res   
  in
  let split_aggMM agg p =
    let res = split_queue2 agg.non_tw_rels p in      
    Array.map (fun e -> {non_tw_rels = e; tbl = agg.tbl }) res
  in
  let split_sainfo sainf p =
    let arr = Array.init size (fun i -> None) in 
    let sarels = match sainf.sarel2 with
    | Some r -> let states = (split r p) in Array.map (fun s ->  Some s) states
    | None -> arr
    in
    let queues = split_mqueue sainf.saauxrels p in    
    let sres = split sainf.sres p in 
    Array.mapi (fun i e ->  {sres = e; sarel2 = sarels.(i); saauxrels = queues.(i)}) sres
  in
  let split_sinfo sinf p =
    let arr = Array.init size (fun i -> None) in 
    let srels = match sinf.srel2 with
    | Some r -> let states = (split r p) in Array.map (fun s ->  Some s) states
    | None -> arr
    in
    let queues = split_mqueue sinf.sauxrels p in    
    Array.map2 (fun srel2 nq -> {srel2 = srel2; sauxrels = nq}) srels queues
  in
  let split_oainfo oainf p =
    let queues = split_mqueue oainf.oaauxrels p in   
    let ores = split oainf.ores p in 
    Array.map2 (fun ores nq ->  {ores = ores; oaauxrels = nq}) ores queues
  in
  let split_mozinfo mozinf p =
    print_endline "Splitting mozinfo:";
    let dllists = Array.init size (fun i -> Dllist.empty()) in 
      Dllist.iter (
        fun e -> let i, ts, r  = e in
        let states = split r p in 
        Array.iteri (fun index s -> Dllist.add_last (i, ts, s) dllists.(index)) states
      ) mozinf.mozauxrels;
    Printf.printf "%d \n" mozinf.mozlast;
    Array.iteri (fun index l -> Printf.printf "%d: " index; Dllist.iter (fun e -> let i,ts,r = e in Relation.print_rel "'" r) l; print_endline "") dllists;
    (* TODO: handle tree by either getting rid of it for mformulas and reconstructing or actually splitting it aswell *)
    Array.map (fun e -> {moztree = mozinf.moztree; mozlast = mozinf.mozlast; mozauxrels = e }) dllists
  in
  let split_moinfo moinf p =
    let dllists = split_dll2 moinf.moauxrels p in
    (* TODO: handle tree by either getting rid of it for mformulas and reconstructing or actually splitting it aswell *)
    Array.map (fun e -> {motree = moinf.motree; molast = moinf.molast; moauxrels = e }) dllists
  in
  let split_muninfo muninf p =
    let listrels1 = split_dll1 muninf.mlistrel1 p in
    let listrels2 = split_dll1 muninf.mlistrel2 p in
    Array.map2 (fun listrel1 listrel2 -> { mlast1 = muninf.mlast1; mlast2 = muninf.mlast2; mlistrel1 = listrel1;  mlistrel2 = listrel2 }) listrels1 listrels2
  in
  let split_muinfo muinf p =
    (* Helper function for raux and saux fields, creates split Sk.dllist *)
    let sklist l =
      let sklists = Array.init size (fun i -> Sk.empty()) in 
      Sk.iter (fun e ->
        let i, r = e in
        let states = split r p in 
        Array.iteri (fun index s -> Sk.add_last (i, s) sklists.(i)) states
      ) l;
      sklists
    in
    let mraux = Array.init size (fun i -> Sj.empty()) in 
      Sj.iter (fun e ->
        let (i, ts, l) = e in
        let lists = sklist l in
        Array.iteri (fun index l -> Sj.add_last (i, ts, l) mraux.(i)) lists
      ) muinf.mraux;
    let arr = Array.make size None in 
    let murels = match muinf.murel2 with
    | Some r -> let states = (split r p) in Array.map (fun s ->  Some s) states
    | None -> arr
    in
    let msaux = sklist muinf.msaux in
    let mures = split muinf.mures p in
    Array.mapi (fun i e -> 
    { mulast = muinf.mulast; mufirst = muinf.mufirst; mures = mures.(i);
      murel2 = e; mraux = mraux.(i); msaux = msaux.(i) })
    murels   
  in
  let split_mezinfo mezinf p =
    let dllists = split_dll1 mezinf.mezauxrels p in
    (* TODO: handle tree by either getting rid of it for mformulas and reconstructing or actually splitting it aswell *)
    Array.map (fun e -> {mezlastev = mezinf.mezlastev; meztree = mezinf.meztree; mezlast = mezinf.mezlast; mezauxrels = e }) dllists
  in
  let split_meinfo meinf p =
    let dllists = split_dll2 meinf.meauxrels p in
    (* TODO: handle tree by either getting rid of it for mformulas and reconstructing or actually splitting it aswell *)
    Array.map (fun e -> {melastev = meinf.melastev; metree = meinf.metree; melast = meinf.melast; meauxrels = e }) dllists
  in
  let p1 f1 = get_predicate f1 in
  let p2 f1 f2 = get_predicate2 f1 f2 in
  let rec split_f = function
    (* Don't think MRel is relevant *)
    | MRel           (rel)                                      -> Array.make size (MRel(rel)) 
    | MPred          (p, comp, inf)                             -> let arr = split_info inf [Predicate.get_name p] in Array.map (fun e -> MPred(p, comp, e)) arr
    | MNeg           (f1)                                       -> Array.map (fun e -> MNeg(e)) (split_f f1)                                                             
    | MAnd           (c, f1, f2, ainf)                          -> let a1 = (split_f f1) in let a2 = (split_f f2) in  Array.mapi (fun i e -> MAnd(c, a1.(i), a2.(i), e)) (split_ainfo ainf (p2 f1 f2))
    | MOr            (c, f1, f2, ainf)                          -> let a1 = (split_f f1) in let a2 = (split_f f2) in  Array.mapi (fun i e -> MOr (c, a1.(i), a2.(i), e)) (split_ainfo ainf (p2 f1 f2))
    | MExists        (c, f1)                                    -> Array.map (fun e -> MExists(c, e)) (split_f f1)                                                                    
    | MAggreg        (c, f1)                                    -> Array.map (fun e -> MAggreg(c, e)) (split_f f1)  
    | MAggOnce       (f1, dt, agg, upd_old, upd_new, get_res)   -> let a1 = (split_f f1) in  Array.mapi (fun i e -> MAggOnce(a1.(i), dt, e, upd_old, upd_new, get_res)) (split_agg agg (p1 f1))   
    | MAggMMOnce     (f1, dt, aggMM, upd_old, upd_new, get_res) -> let a1 = (split_f f1) in  Array.mapi (fun i e -> MAggMMOnce(a1.(i), dt, e, upd_old, upd_new, get_res)) (split_aggMM aggMM (p1 f1))
    | MPrev          (dt, f1, pinf)                             -> Array.map (fun e -> MPrev(dt, e, pinf)) (split_f f1)
    | MNext          (dt, f1, ninf)                             -> Array.map (fun e -> MNext(dt, e, ninf)) (split_f f1)
    | MSinceA        (c2, dt, f1, f2, sainf)                    -> let a1 = (split_f f1) in let a2 = (split_f f2) in  Array.mapi (fun i e -> MSinceA(c2, dt, a1.(i), a2.(i), e)) (split_sainfo sainf (p2 f1 f2))
    | MSince         (c2, dt, f1, f2, sinf)                     -> let a1 = (split_f f1) in let a2 = (split_f f2) in  Array.mapi (fun i e -> MSince(c2, dt, a1.(i), a2.(i), e)) (split_sinfo sinf (p2 f1 f2))
    | MOnceA         (dt, f1, oainf)                            -> let a1 = (split_f f1) in Array.mapi (fun i e -> MOnceA(dt, a1.(i), e)) (split_oainfo oainf (p1 f1))                      
    | MOnceZ         (dt, f1, ozinf)                            -> let a1 = (split_f f1) in Array.mapi (fun i e -> MOnceZ(dt, a1.(i), e)) (split_mozinfo ozinf (p1 f1))                                
    | MOnce          (dt, f1, oinf)                             -> let a1 = (split_f f1) in Array.mapi (fun i e -> MOnce(dt, a1.(i), e)) (split_moinfo oinf (p1 f1)) 
    | MNUntil        (c1, dt, f1, f2, muninf)                   -> let a1 = (split_f f1) in let a2 = (split_f f2) in Array.mapi (fun i e -> MNUntil(c1, dt, a1.(i), a2.(i), e)) (split_muninfo muninf (p2 f1 f2))   
    | MUntil         (c1, dt, f1, f2, muinf)                    -> let a1 = (split_f f1) in let a2 = (split_f f2) in Array.mapi (fun i e -> MUntil(c1, dt, a1.(i), a2.(i), e)) (split_muinfo muinf (p2 f1 f2))   
    | MEventuallyZ   (dt, f1, mezinf)                           -> let a1 = (split_f f1) in Array.mapi (fun i e -> MEventuallyZ(dt, a1.(i), e)) (split_mezinfo mezinf (p1 f1))            
    | MEventually    (dt, f1, meinf)                            -> let a1 = (split_f f1) in Array.mapi (fun i e -> MEventually(dt, a1.(i), e)) (split_meinfo meinf (p1 f1))
    in
  split_f mf
    

let split_formula sconsts dumpfile i lastts ff closed neval =
  let numparts = (sconsts.num_partitions+1) in

  let keys = sconsts.keys in
  let constraints = sconsts.constraints in
  let a, mf = ext_to_m ff neval in

  let split_paramater_function t p = 
    Printf.printf "Tuple: %s    -> " (pred_list_to_string t);
    let pos = List.map (fun p -> try Misc.get_pos p keys with e -> -1 ) p in
    (* columns not in cs.keys are filtered -> so ignored for checking tuples *)
    let pos = List.filter (fun e -> e >= 0) pos in
    (* If no specified keys are in the predicate list, return all partitions *)
    if List.length pos = 0 then let res = Array.make numparts 0 in Array.mapi (fun i e -> i) res else
    (* Else we create a mapping to reorder our partition input values *)
    let mapping t = List.map (fun e -> List.nth t e) pos in
    let output = Array.of_list (List.flatten (List.map (fun cs -> if check_tuple t (mapping cs.values) then cs.partitions else []) constraints)) in
    Printf.printf "Partitions: %s \n" (int_arr_to_string output);
    output
  in  
  split_state split_paramater_function mf numparts


(* END SPLITTING STATE *)

let files_to_list f = 
  String.split_on_char ',' f   
  
  
let combine_neval nv1 nv2 =
  (* What should be done with the i *)
  let rec combine l nl c : unit = 
    let e = NEval.pop_first l in 
    let i, ts = e in 
    (* l1 list element ts is < l2 ts2, pop from l2 and add to new list *)
    if c < ts then 
      NEval.add_last e nl
    (* if timestamp already contained, skip *)
    else if c = ts then () 
    (* otherwise readd popped element *)
    else NEval.add_first e l;
    if c < ts then combine l nl c
  in
  let n = NEval.empty() in
  NEval.iter (fun e -> 
    let _, ts = e in 
    combine nv2 n ts;
  ) nv1;
  n

let rec print_ef = function
  | ERel           (rel)                                      -> print_endline "Rel" 
  | EPred          (p, comp, inf)                             -> print_endline "Pred"
  | ENeg           (f1)                                       -> print_endline "Neg";print_ef f1
  | EAnd           (c, f1, f2, ainf)                          -> print_endline "And";print_ef f1; print_ef f2
  | EOr            (c, f1, f2, ainf)                          -> print_endline "Or";print_ef f1; print_ef f2
  | EExists        (c, f1)                                    -> print_endline "Exists";print_ef f1
  | EAggreg        (c, f1)                                    -> print_endline "Aggreg";print_ef f1
  | EAggOnce       (f1, dt, agg, upd_old, upd_new, get_res)   -> print_endline "AggOnce";print_ef f1
  | EAggMMOnce     (f1, dt, aggMM, upd_old, upd_new, get_res) -> print_endline "AggMMOnce";print_ef f1
  | EPrev          (dt, f1, pinf)                             -> print_endline "Prev";print_ef f1
  | ENext          (dt, f1, ninf)                             -> print_endline "Next";print_ef f1
  | ESinceA        (c2, dt, f1, f2, sainf)                    -> print_endline "SinceA";print_ef f1;print_ef f2
  | ESince         (c2, dt, f1, f2, sinf)                     -> print_endline "Since";print_ef f1;print_ef f2
  | EOnceA         (dt, f1, oainf)                            -> print_endline "OnceA";print_ef f1
  | EOnceZ         (dt, f1, ozinf)                            -> print_endline "OnceZ";print_ef f1
  | EOnce          (dt, f1, oinf)                             -> print_endline "Once";print_ef f1
  | ENUntil        (c1, dt, f1, f2, muninf)                   -> print_endline "NUntil";print_ef f1;print_ef f2
  | EUntil         (c1, dt, f1, f2, muinf)                    -> print_endline "Until";print_ef f1;print_ef f2
  | EEventuallyZ   (dt, f1, mezinf)                           -> print_endline "EventuallyZ";print_ef f1
  | EEventually    (dt, f1, meinf)                            -> print_endline "Eventually";print_ef f1