
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
open Extformula
open Mformula

type state = (int * timestamp * bool * mformula * (int * timestamp) array * int * int * bool)

let ext_to_m ff neval =
  let eze2m ezinf =
      {mezauxrels = ezinf.ezauxrels}
  in
  let ee2m einf =
      {meauxrels = einf.eauxrels}
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
    { moauxrels = oinf.oauxrels }
  in
  let oz2m ozinf =
    { mozauxrels = ozinf.ozauxrels}
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
  let mez2e dt mezinf =
   (* contents of inf:
       elastev: 'a NEval.cell  last cell of neval for which f2 is evaluated
       eauxrels: info          the auxiliary relations (up to elastev)
    *)
    let _, cell =
      if NEval.is_empty neval then [], NEval.void
      else begin (*TODO*)
        let _, tsl = NEval.get_first neval in 
        Helper.get_new_elements neval NEval.void (fun (_, tsr) -> MFOTL.in_interval (MFOTL.ts_minus tsr tsl) dt) (fun x -> x)
    end
    in
    let tree_list, ezlast =
      if Dllist.is_empty mezinf.mezauxrels then [], Dllist.void
      else begin(*TODO*)
      let f = fun (j,_,rel) -> (j,rel) in
      let _, tsq = Dllist.get_data cell in
      let cond = fun (_,tsj,_) -> MFOTL.in_left_ext (MFOTL.ts_minus tsj tsq) dt in
      Helper.get_new_elements mezinf.mezauxrels Dllist.void cond f
    end
    in
    let meztree   = Sliding.build_rl_tree_from_seq Relation.union tree_list in
    {ezlastev   = cell;
     eztree     = meztree;
     ezlast     = ezlast;
     ezauxrels  = mezinf.mezauxrels}
  in
  let me2e dt meinf =
    (* contents of inf:
       elastev: 'a NEval.cell  last cell of neval for which f2 is evaluated
       eauxrels: info          the auxiliary relations (up to elastev)
    *)
    let _, cell =
      if NEval.is_empty neval then [], NEval.void
      else begin (*TODO*)
        let _, tsl = NEval.get_first neval in 
        Helper.get_new_elements neval NEval.void (fun (_, tsr) -> MFOTL.in_interval (MFOTL.ts_minus tsr tsl) dt) (fun x -> x)
    end
    in
    let tree_list, elast =
      if Dllist.is_empty meinf.meauxrels then [], Dllist.void
      else begin(*TODO*)
      let _, tsq = Dllist.get_data cell in
      let cond = fun (tsj,_) -> MFOTL.in_left_ext (MFOTL.ts_minus tsj tsq) dt in
      Helper.get_new_elements meinf.meauxrels Dllist.void cond (fun x -> x)
    end
    in
    (* Pass void as last element, forcing rebuild over whole list *)
    let tree_list, _ = Helper.get_new_elements meinf.meauxrels elast (fun x -> true) (fun x -> x) in
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
  let mo2e dt moinf =
    (* TODO: verify correctness *)
    let moauxrels = moinf.moauxrels in
    let rebuild =
      if Dllist.is_empty moauxrels then [], Dllist.void
      else begin 
      let (tsl, arel) = Dllist.get_first moauxrels in
      let cond = fun (tsr,_) ->  MFOTL.in_interval (MFOTL.ts_minus tsr tsl) dt in
      Helper.get_new_elements moauxrels Dllist.void cond (fun x -> x)
    end
    in
    let tree_list, olast = rebuild in
    { otree = Sliding.build_rl_tree_from_seq Relation.union tree_list; olast = olast; oauxrels = moinf.moauxrels }
  in
  let moz2e dt mozinf =
    (* TODO: verify correctness *)
    let mozauxrels = mozinf.mozauxrels in
    let rebuild =
      if Dllist.is_empty mozauxrels then [], Dllist.void
      else begin
      let (_, tsl, arel) = Dllist.get_first mozauxrels in
      let f = fun (j,_,rel) -> (j,rel) in
      let cond = fun (_,tsr,_) ->  MFOTL.in_interval (MFOTL.ts_minus tsr tsl) dt in
      Helper.get_new_elements mozauxrels Dllist.void cond f
    end
    in
    let tree_list, ozlast = rebuild in
    { oztree = Sliding.build_rl_tree_from_seq Relation.union tree_list; ozlast = ozlast; ozauxrels = mozinf.mozauxrels }
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
    | MOnceZ         (dt, mf, ozinf)                                          ->      EOnceZ         (dt, (m2e mf), (moz2e dt ozinf))
    | MOnce          (dt, mf, oinf)                                           ->      EOnce          (dt, (m2e mf), (mo2e dt oinf))
    | MNUntil        (c1, dt, mf1, mf2, muninf)                               ->      ENUntil        (c1, dt, (m2e mf1), (m2e mf2), (mun2e muninf))
    | MUntil         (c1, dt, mf1, mf2, muinf)                                ->      EUntil         (c1, dt, (m2e mf1), (m2e mf2), (mu2e muinf))
    | MEventuallyZ   (dt, mf, mezinf)                                         ->      EEventuallyZ   (dt, (m2e mf), (mez2e dt mezinf))
    | MEventually    (dt, mf, meinf)                                          ->      EEventually    (dt, (m2e mf), (me2e  dt meinf))
  in m2e mf

(* END SAVING AND LOADING STATE *)