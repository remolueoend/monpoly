
(*
  SAVING AND LOADING STATE
*)

open Dllist
open Misc
open Predicate
open MFOTL
open Tuple
open Relation
open Sliding
open Helper
open Extformula
open Mformula

(*
  Converts the extformula to an mformula by recursing through the structure and reducing state information. The resulting
  formula thus has the same structure but minified state information.
  Main changes:
    - Once & Eventually have all pointers and trees removed

  neval dllist is converted to an array representation.
 *)
let ext_to_m ff =
  let el2m linf = linf.llast
  in
  let eze2m ezinf =
    {mezlastev = ezinf.ezlastev; mezauxrels = ezinf.ezauxrels}
  in
  let ee2m einf =
    {melastev = einf.elastev; meauxrels = einf.eauxrels}
  in
  let mue2m uinf =
    {mulast = uinf.ulast;
     mufirst = uinf.ufirst;
     mures = uinf.ures;
     murel2 = uinf.urel2;
     (* TODO: transform these too *)
     mraux = uinf.raux;
     msaux = uinf.saux;
    }
  in
  let mune2m uninf =
    {
      mlast1 = uninf.last1;
      mlast2 = uninf.last2;
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
  let rec e2m = function
    | ERel           (rel, loc)                         -> MRel         (rel, loc)
    | EPred          (pred, c1, inf, loc)               -> MPred        (pred, c1, inf, loc)
    | ELet           (pred, c1, ext1, ext2, linf, loc)  -> MLet         (pred, c1, e2m ext1, e2m ext2, el2m linf, loc)
    | ENeg           (ext, loc)                         -> MNeg         (e2m ext, loc)
    | EAnd           (c2, ext1, ext2, ainf, loc)        -> MAnd         (c2, (e2m ext1), (e2m ext2), ainf, loc)
    | EOr            (c2, ext1, ext2, ainf, loc)        -> MOr          (c2, (e2m ext1), (e2m ext2), ainf, loc)
    | EExists        (c1, ext, loc)                     -> MExists      (c1, (e2m ext), loc)
    | EAggreg        (inf, comp, ext, loc)              -> MAggreg      (inf, comp, (e2m ext), loc)
    | EAggOnce       (inf, state, ext, loc)             -> MAggOnce     (inf, state, (e2m ext), loc)
    | EPrev          (intv, ext, pinf, loc)             -> MPrev        (intv, (e2m ext), pinf, loc)
    | ENext          (intv, ext, ninf, loc)             -> MNext        (intv, (e2m ext), ninf, loc)
    | ESinceA        (c2, intv, ext1, ext2, sainf, loc) -> MSinceA      (c2, intv, (e2m ext1), (e2m ext2), sainf, loc)
    | ESince         (c2, intv, ext1, ext2, sinf, loc)  -> MSince       (c2, intv, (e2m ext1), (e2m ext2), sinf, loc)
    | EOnceA         (intv, ext, oainf, loc)            -> MOnceA       (intv, (e2m ext), oainf, loc)
    | EOnceZ         (intv, ext, ozinf, loc)            -> MOnceZ       (intv, (e2m ext), (oz2m ozinf), loc)
    | EOnce          (intv, ext, oinf, loc)             -> MOnce        (intv, (e2m ext), (o2m oinf), loc)
    | ENUntil        (c1, intv, ext1, ext2, uninf, loc) -> MNUntil      (c1, intv, (e2m ext1), (e2m ext2), (mune2m uninf), loc)
    | EUntil         (c1, intv, ext1, ext2, uinf, loc)  -> MUntil       (c1, intv, (e2m ext1), (e2m ext2), (mue2m uinf), loc)
    | EEventuallyZ   (intv, ext, ezinf, loc)            -> MEventuallyZ (intv, (e2m ext), (eze2m ezinf), loc)
    | EEventually    (intv, ext, einf, loc)             -> MEventually  (intv, (e2m ext), (ee2m einf), loc)
  in e2m ff

(*
  Restores an mformula to its extformula representation by reconstructing the full state information,
  including optimization structures such as sliding trees.
*)
let m_to_ext mf =
  let ml2e mlast = {llast = mlast}
  in
  let mez2e intv mezinf =
   (* contents of inf:
       ezlastev: 'a Neval.cell  last cell of neval for which f2 is evaluated
       ezauxrels: info          the auxiliary relations (up to ezlastev)
    *)
    (* if auxrels is empty or ezlastev is void return invalid tree, forcing reevaluation in the algorithm *)
    let return_empty =
      let eztree = LNode {l = -1; r = -1; res = Some (Relation.empty)} in
      let ezlast = Dllist.void in
      {ezlastev = mezinf.mezlastev; eztree = eztree; ezlast = ezlast; ezauxrels  = mezinf.mezauxrels}
    in
    if not (Dllist.is_empty mezinf.mezauxrels) && Neval.is_valid mezinf.mezlastev then
      (* If auxrels contains elements, rebuild tree and restore ezlast by getting all elements of auxrels
         where the timepoint is smaller than that of ezlastev
         Note: We are presuming that all monpoly instances have synchronized timepoints. *)
      let (tpq, tsq) = Neval.get_data mezinf.mezlastev in
      let (tpj, tsj, _) = Dllist.get_first mezinf.mezauxrels in
      (* Catch case where auxrels contains exactly one element with same tp as ezlast *)
      if ((tpj - tpq) < 0) then
        let tree_list, ezlast =
          let f = fun (j,_,rel) -> (j,rel) in
          let cond = fun (tpj,_,_) -> (tpj - tpq) < 0 in
          Helper.get_new_elements mezinf.mezauxrels Dllist.void cond f
        in
        let eztree =
          if tree_list = [] then
            LNode {l = -1; r = -1; res = Some (Relation.empty)}
          else
            Sliding.build_rl_tree_from_seq Relation.union tree_list
        in
        {ezlastev = mezinf.mezlastev; eztree; ezlast; ezauxrels  = mezinf.mezauxrels}
      else return_empty
    else begin
      return_empty
    end
  in
  let me2e intv meinf =
    (* contents of inf:
       elastev: 'a Neval.cell  last cell of neval for which f2 is evaluated
       eauxrels: info          the auxiliary relations (up to elastev)
    *)
    let meauxrels = meinf.meauxrels in
    (* if auxrels is empty or elastev is void return invalid tree, forcing reevaluation in the algorithm *)
    let return_empty =
      let metree = LNode {l = MFOTL.ts_invalid; r = MFOTL.ts_invalid; res = Some (Relation.empty)} in
      let elast = Dllist.void in
      {elastev = meinf.melastev; etree = metree; elast = elast;eauxrels = meinf.meauxrels}
    in
    if not(Dllist.is_empty meauxrels) && Neval.is_valid meinf.melastev then
     (* If auxrels contains elements, rebuild tree and restore elast by getting all elements of auxrels
         where the timestamp is smaller than that of elastev *)
      let (_, tsq) = Neval.get_data meinf.melastev in
      let (tsj, _) = Dllist.get_first meauxrels in
      (* Catch case where auxrels contains exactly one element with same ts as elast *)
      if Z.(tsj - tsq < zero) then
        let tree_list, elast =
          let cond = fun (tsj,_) -> Z.(tsj - tsq < zero) in
          Helper.get_new_elements meinf.meauxrels Dllist.void cond (fun x -> x)
        in
        let etree =
          if tree_list = [] then
            LNode {l = MFOTL.ts_invalid; r = MFOTL.ts_invalid; res = Some (Relation.empty)}
          else
            Sliding.build_rl_tree_from_seq Relation.union tree_list
        in
        {elastev = meinf.melastev; etree; elast; eauxrels = meinf.meauxrels}
      else return_empty
    else begin
      return_empty
    end
  in
  let mu2e muinf =
    {ulast  = muinf.mulast;
     ufirst = muinf.mufirst;
     ures   = muinf.mures;
     urel2  = muinf.murel2;
     raux   = muinf.mraux;
     saux   = muinf.msaux;
    }
  in
  let mun2e muninf =
    {last1 = muninf.mlast1;
     last2 = muninf.mlast2;
     listrel1 = muninf.mlistrel1;
     listrel2 = muninf.mlistrel2;
    }
  in
  let mo2e intv moinf =
    let moauxrels = moinf.moauxrels in
    (*Consider interval [a,b): Retrieves tree relevant list of auxrels elements, aswell as olast by setting the break condition to hold until
      the first element whose timestamp does not have distance "a" from the last auxrel element's timestamp.
      - ozlast thus is the last element in auxrels which has distance a from the last element from auxrels
      - tree [list] contains all auxrel elements up to and including olast.*)
    if not (Dllist.is_empty moauxrels) then
      begin
        let (tsq, rel) = Dllist.get_last moauxrels in
        let tree_list, olast =
          let cond = fun (tsj,_) -> (MFOTL.in_right_ext Z.(tsq - tsj) intv) in
          Helper.get_new_elements moauxrels Dllist.void cond (fun x -> x)
        in
        { otree =
            if tree_list = [] then
              LNode {l = MFOTL.ts_invalid; r = MFOTL.ts_invalid; res = Some (Relation.empty)}
            else
              Sliding.build_rl_tree_from_seq Relation.union tree_list;
          olast = olast;
          oauxrels = moauxrels }
      end
    else
      begin
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
        let cond = fun (_,tsj,_) -> MFOTL.in_left_ext Z.(tsj - tsq) intv in
        Helper.get_new_elements mozauxrels Dllist.void cond f
      in
      { oztree =
          if tree_list = [] then
            LNode {l = -1; r = -1; res = Some (Relation.empty)}
          else
            Sliding.build_rl_tree_from_seq Relation.union tree_list;
        ozlast = ozlast;
        ozauxrels = mozinf.mozauxrels }
    else begin
     (* If auxrels is empty, set tree to be invalid, forcing reevaluation in the algorithm *)
      let oztree = LNode {l = -1; r = -1; res = Some (Relation.empty)} in
      let ozlast = Dllist.void in
      { oztree = oztree; ozlast = ozlast; ozauxrels = mozinf.mozauxrels }
    end
   in
  let rec m2e = function
    | MRel           (rel, loc)                        -> ERel         (rel, loc)
    | MPred          (pred, c1, inf, loc)              -> EPred        (pred, c1, inf, loc)
    | MLet           (pred, c1, mf1, mf2, mlast, loc)  -> ELet         (pred, c1, m2e mf1, m2e mf2, ml2e mlast, loc)
    | MNeg           (mf, loc)                         -> ENeg         ((m2e mf), loc)
    | MAnd           (c2, mf1, mf2, ainf, loc)         -> EAnd         (c2, (m2e mf1), (m2e mf2), ainf, loc)
    | MOr            (c2, mf1, mf2, ainf, loc)         -> EOr          (c2, (m2e mf1), (m2e mf2), ainf, loc)
    | MExists        (c1, mf, loc)                     -> EExists      (c1, (m2e mf), loc)
    | MAggreg        (inf, comp, mf, loc)              -> EAggreg      (inf, comp, (m2e mf), loc)
    | MAggOnce       (inf, state, mf, loc)             -> EAggOnce     (inf, state, (m2e mf), loc)
    | MPrev          (intv, mf, pinf, loc)             -> EPrev        (intv, (m2e mf), pinf, loc)
    | MNext          (intv, mf, ninf, loc)             -> ENext        (intv, (m2e mf), ninf, loc)
    | MSinceA        (c2, intv, mf1, mf2, sainf, loc)  -> ESinceA      (c2, intv, (m2e mf1), (m2e mf2), sainf, loc)
    | MSince         (c2, intv, mf1, mf2, sinf, loc)   -> ESince       (c2, intv, (m2e mf1), (m2e mf2), sinf, loc)
    | MOnceA         (intv, mf, oainf, loc)            -> EOnceA       (intv, (m2e mf), oainf, loc)
    | MOnceZ         (intv, mf, ozinf, loc)            -> EOnceZ       (intv, (m2e mf), (moz2e intv ozinf), loc)
    | MOnce          (intv, mf, oinf, loc)             -> EOnce        (intv, (m2e mf), (mo2e intv oinf), loc)
    | MNUntil        (c1, intv, mf1, mf2, muninf, loc) -> ENUntil      (c1, intv, (m2e mf1), (m2e mf2), (mun2e muninf), loc)
    | MUntil         (c1, intv, mf1, mf2, muinf, loc)  -> EUntil       (c1, intv, (m2e mf1), (m2e mf2), (mu2e muinf), loc)
    | MEventuallyZ   (intv, mf, mezinf, loc)           -> EEventuallyZ (intv, (m2e mf), (mez2e intv mezinf), loc)
    | MEventually    (intv, mf, meinf, loc)            -> EEventually  (intv, (m2e mf), (me2e  intv meinf), loc)
  in m2e mf

(* END SAVING AND LOADING STATE *)
