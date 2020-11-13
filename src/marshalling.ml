
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

(*
  Converts the extformula to an mformula by recursing through the structure and reducing state information. The resulting
  formula thus has the same structure but minified state information.
  Main changes:
    - Once & Eventually have all pointers and trees removed
    - Record fields containing cell are replaced with integers pointing at the cell index / encoding void.

  neval dllist is converted to an array representation.
 *)
let ext_to_m ff neval =
  let el2m linf =
    if linf.llast == NEval.void then -2
    else if not (NEval.is_last neval linf.llast) && NEval.get_next neval linf.llast == NEval.get_first_cell neval then -1
    else NEval.get_index linf.llast neval
  in
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
    { moauxrels = oinf.oauxrels; }
  in
  let oz2m ozinf =
    { mozauxrels = ozinf.ozauxrels}
  in
  let a = NEval.to_array neval in
  let rec e2m = function
    | ERel           (rel)                                                  -> MRel         (rel)
    | EPred          (pred, c1, inf)                                        -> MPred        (pred, c1, inf)
    | ELet           (pred, c1, ext1, ext2, linf)                           -> MLet         (pred, c1, e2m ext1, e2m ext2, el2m linf)
    | ENeg           (ext)                                                  -> MNeg         (e2m ext)
    | EAnd           (c2, ext1, ext2, ainf)                                 -> MAnd         (c2, (e2m ext1), (e2m ext2), ainf)
    | EOr            (c2, ext1, ext2, ainf)                                 -> MOr          (c2, (e2m ext1), (e2m ext2), ainf)
    | EExists        (c1, ext)                                              -> MExists      (c1, (e2m ext))
    | EAggreg        (c1, ext)                                              -> MAggreg      (c1, (e2m ext))
    | EAggOnce       (ext, intv, agg, update_old, update_new, get_result)   -> MAggOnce     ((e2m ext), intv, agg, update_old, update_new, get_result)
    | EAggMMOnce     (ext, intv, aggMM, update_old, update_new, get_result) -> MAggMMOnce   ((e2m ext), intv, aggMM, update_old, update_new, get_result)
    | EPrev          (intv, ext, pinf)                                      -> MPrev        (intv, (e2m ext), pinf)
    | ENext          (intv, ext, ninf)                                      -> MNext        (intv, (e2m ext), ninf)
    | ESinceA        (c2, intv, ext1, ext2, sainf)                          -> MSinceA      (c2, intv, (e2m ext1), (e2m ext2), sainf)
    | ESince         (c2, intv, ext1, ext2, sinf)                           -> MSince       (c2, intv, (e2m ext1), (e2m ext2), sinf)
    | EOnceA         (intv, ext, oainf)                                     -> MOnceA       (intv, (e2m ext), oainf)
    | EOnceZ         (intv, ext, ozinf)                                     -> MOnceZ       (intv, (e2m ext), (oz2m ozinf))
    | EOnce          (intv, ext, oinf)                                      -> MOnce        (intv, (e2m ext), (o2m oinf))
    | ENUntil        (c1, intv, ext1, ext2, uninf)                          -> MNUntil      (c1, intv, (e2m ext1), (e2m ext2), (mune2m uninf))
    | EUntil         (c1, intv, ext1, ext2, uinf)                           -> MUntil       (c1, intv, (e2m ext1), (e2m ext2), (mue2m uinf))
    | EEventuallyZ   (intv, ext, ezinf)                                     -> MEventuallyZ (intv, (e2m ext), (eze2m ezinf))
    | EEventually    (intv, ext, einf)                                      -> MEventually  (intv, (e2m ext), (ee2m einf))
  in a, e2m ff

(*
  Restores an mformula to its extformula representation by reconstructing the full state information,
  including optimization structures such as sliding trees.
*)
let m_to_ext mf neval = 
  let rec get_lastev crt cond =
    if not (NEval.is_last neval crt) then
      let e = NEval.get_next neval crt in
      if cond (NEval.get_data e) && not (NEval.is_last neval e) then
        get_lastev e cond
      else
        e  
    else crt   
  in    

  let ml2e mlast =
    let llast =
      if      mlast = -2 then NEval.void
      else if mlast = -2 then NEval.new_cell (-1,MFOTL.ts_invalid)  neval
      else                    NEval.get_cell_at_index mlast neval
    in
    {llast = llast}
  in
  let mez2e intv mezinf =
   (* contents of inf:
       ezlastev: 'a NEval.cell  last cell of neval for which f2 is evaluated
       ezauxrels: info          the auxiliary relations (up to ezlastev)
    *)
    (* Retrieves last evaluated cell by taking the subformula interval and retrieving the last element
       of neval which lies within it.
       Returns void if neval is empty. *)
    let cell =
      if NEval.is_empty neval then NEval.void
      else begin 
        let (_, tsq) = NEval.get_first neval in
        get_lastev (NEval.get_first_cell neval) (fun (_, tsj) -> MFOTL.in_left_ext (MFOTL.ts_minus tsj tsq) intv)
    end
    in
    (* if auxrels is empty or ezlastev is void return invalid tree, forcing reevaluation in the algorithm *)
    let return_empty =
      let eztree = LNode {l = -1; r = -1; res = Some (Relation.empty)} in
      let ezlast = Dllist.void in
      {ezlastev = cell; eztree = eztree; ezlast = ezlast; ezauxrels  = mezinf.mezauxrels}
    in
    if not (Dllist.is_empty mezinf.mezauxrels) && not (cell = NEval.void) then
      (* If auxrels contains elements, rebuild tree and restore ezlast by getting all elements of auxrels
         where the timepoint is smaller than that of ezlastev
         Note: We are presuming that all monpoly instances have synchronized timepoints. *)
      let (tpq, tsq) = NEval.get_data cell in
      let (tpj, tsj, _) = Dllist.get_first mezinf.mezauxrels in
      (* Catch case where auxrels contains exactly one element with same tp as ezlast *)
      if ((tpj - tpq) < 0) then
        let tree_list, ezlast =
          let f = fun (j,_,rel) -> (j,rel) in
          let cond = fun (tpj,_,_) -> (tpj - tpq) < 0 in
          Helper.get_new_elements mezinf.mezauxrels Dllist.void cond f
        in
        let meztree   = Sliding.build_rl_tree_from_seq Relation.union tree_list in
        {ezlastev = cell; eztree = meztree; ezlast = ezlast; ezauxrels  = mezinf.mezauxrels}
      else return_empty
    else begin
      return_empty
    end
  in
  let me2e intv meinf =
    (* contents of inf:
       elastev: 'a NEval.cell  last cell of neval for which f2 is evaluated
       eauxrels: info          the auxiliary relations (up to elastev)
    *)
    let meauxrels = meinf.meauxrels in
    (* Retrieves last evaluated cell by taking the subformula interval and retrieving the last element
      of neval which lies within it.
      Returns void if neval is empty. *)
    let cell =
      if NEval.is_empty neval then NEval.void
      else begin
        let _, tsq = NEval.get_first neval in
        get_lastev (NEval.get_first_cell neval) (fun (_, tsj) -> MFOTL.in_left_ext (MFOTL.ts_minus tsj tsq) intv)
    end
    in
    (* if auxrels is empty or elastev is void return invalid tree, forcing reevaluation in the algorithm *)
    let return_empty =
      let metree = LNode {l = MFOTL.ts_invalid; r = MFOTL.ts_invalid; res = Some (Relation.empty)} in
      let elast = Dllist.void in
      {elastev = cell; etree = metree; elast = elast;eauxrels = meinf.meauxrels}
    in
    if not(Dllist.is_empty meauxrels) && cell != NEval.void then
     (* If auxrels contains elements, rebuild tree and restore elast by getting all elements of auxrels
         where the timestamp is smaller than that of elastev *)
      let (_, tsq) = NEval.get_data cell in
      let (tsj, _) = Dllist.get_first meauxrels in
      (* Catch case where auxrels contains exactly one element with same ts as elast *)
      if ((MFOTL.ts_minus tsj tsq) < 0.0) then
        let tree_list, elast =
          let cond = fun (tsj,_) -> (MFOTL.ts_minus tsj tsq) < 0.0 in
          Helper.get_new_elements meinf.meauxrels Dllist.void cond (fun x -> x)
        in
        let einf = {elastev = cell; etree = Sliding.build_rl_tree_from_seq Relation.union tree_list; elast = elast;eauxrels = meinf.meauxrels} in
        einf
      else return_empty
    else begin
      return_empty
    end
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
  let mo2e intv moinf =
    let moauxrels = moinf.moauxrels in
    let (tsq, rel) = Dllist.get_last moauxrels in
    (*Consider interval [a,b): Retrieves tree relevant list of auxrels elements, aswell as olast by setting the break condition to hold until
      the first element whose timestamp does not have distance "a" from the last auxrel element's timestamp.
      - ozlast thus is the last element in auxrels which has distance a from the last element from auxrels
      - tree [list] contains all auxrel elements up to and including olast.*)
    if not (Dllist.is_empty moauxrels) then
      let tree_list, olast =
        let cond = fun (tsj,_) -> (MFOTL.in_right_ext (MFOTL.ts_minus tsq tsj) intv) in
        Helper.get_new_elements moauxrels Dllist.void cond (fun x -> x)
    in
    let oinf = { otree = Sliding.build_rl_tree_from_seq Relation.union tree_list; olast = olast; oauxrels = moauxrels } in
    oinf
    else begin
      (* If auxrels is empty, set tree to be invalid, forcing reevaluation in the algorithm *)
      let otree = LNode {l = MFOTL.ts_invalid; r = MFOTL.ts_invalid; res = Some (Relation.empty)} in
      let olast = Dllist.void in
      { otree = otree; olast = olast; oauxrels = moinf.moauxrels }
    end
  in
  let moz2e intv mozinf =
    let mozauxrels = mozinf.mozauxrels in
    if not (Dllist.is_empty mozauxrels) then
      (* Retrieves tree relevant list of auxrels elements, aswell as ozlast by setting the break condition to hold until
         the first element not in the left extent of the interval. 
         - ozlast thus is the last element of auxrels within the interval
         - tree [list] contains all auxrel elements up to and including ozlast.*)
      let tree_list, ozlast  =
        let (_, tsq, arel) = Dllist.get_first mozauxrels in
        let f = fun (j,_,rel) -> (j,rel) in
        let cond = fun (_,tsj,_) -> MFOTL.in_left_ext (MFOTL.ts_minus tsj tsq) intv in
        Helper.get_new_elements mozauxrels Dllist.void cond f
      in 
      { oztree = Sliding.build_rl_tree_from_seq Relation.union tree_list; ozlast = ozlast; ozauxrels = mozinf.mozauxrels }
    else begin
     (* If auxrels is empty, set tree to be invalid, forcing reevaluation in the algorithm *)
      let oztree = LNode {l = -1; r = -1; res = Some (Relation.empty)} in
      let ozlast = Dllist.void in
      { oztree = oztree; ozlast = ozlast; ozauxrels = mozinf.mozauxrels }
    end
   in
  let rec m2e = function
    | MRel           (rel)                                                 -> ERel         (rel)
    | MPred          (pred, c1, inf)                                       -> EPred        (pred, c1, inf)
    | MLet           (pred, c1, mf1, mf2, mlast)                           -> ELet         (pred, c1, m2e mf1, m2e mf2, ml2e mlast)
    | MNeg           (mf)                                                  -> ENeg         ((m2e mf))
    | MAnd           (c2, mf1, mf2, ainf)                                  -> EAnd         (c2, (m2e mf1), (m2e mf2), ainf)
    | MOr            (c2, mf1, mf2, ainf)                                  -> EOr          (c2, (m2e mf1), (m2e mf2), ainf)
    | MExists        (c1, mf)                                              -> EExists      (c1, (m2e mf))
    | MAggreg        (c1, mf)                                              -> EAggreg      (c1, (m2e mf))
    | MAggOnce       (mf, intv, agg, update_old, update_new, get_result)   -> EAggOnce     ((m2e mf), intv, agg, update_old, update_new, get_result)
    | MAggMMOnce     (mf, intv, aggMM, update_old, update_new, get_result) -> EAggMMOnce   ((m2e mf), intv, aggMM, update_old, update_new, get_result)
    | MPrev          (intv, mf, pinf)                                      -> EPrev        (intv, (m2e mf), pinf)
    | MNext          (intv, mf, ninf)                                      -> ENext        (intv, (m2e mf), ninf)
    | MSinceA        (c2, intv, mf1, mf2, sainf)                           -> ESinceA      (c2, intv, (m2e mf1), (m2e mf2), sainf)
    | MSince         (c2, intv, mf1, mf2, sinf)                            -> ESince       (c2, intv, (m2e mf1), (m2e mf2), sinf)
    | MOnceA         (intv, mf, oainf)                                     -> EOnceA       (intv, (m2e mf), oainf)
    | MOnceZ         (intv, mf, ozinf)                                     -> EOnceZ       (intv, (m2e mf), (moz2e intv ozinf))
    | MOnce          (intv, mf, oinf)                                      -> EOnce        (intv, (m2e mf), (mo2e intv oinf))
    | MNUntil        (c1, intv, mf1, mf2, muninf)                          -> ENUntil      (c1, intv, (m2e mf1), (m2e mf2), (mun2e muninf))
    | MUntil         (c1, intv, mf1, mf2, muinf)                           -> EUntil       (c1, intv, (m2e mf1), (m2e mf2), (mu2e muinf))
    | MEventuallyZ   (intv, mf, mezinf)                                    -> EEventuallyZ (intv, (m2e mf), (mez2e intv mezinf))
    | MEventually    (intv, mf, meinf)                                     -> EEventually  (intv, (m2e mf), (me2e  intv meinf))
  in m2e mf

(* END SAVING AND LOADING STATE *)
