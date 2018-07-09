(*
  This file contains the implementation for splitting and merging monpoly formula state information.
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
open Marshalling
open Mformula

type state = (int * timestamp * bool * mformula * (int * timestamp) array * int * int * bool)

exception Type_error of string

(* SPLITTING & COMBINING STATE *)

let rel_u r1 r2 = Relation.union r1 r2


(* In combination function we assume that:
   - for lists timepoints & timestamps are sorted in monotonic ascending order from head to tail
   - for queues timepoints & timestamps are sorted in monotonic ascending order from least recently added to most recently added

  All queue and list combination functions follow the same schema. 
  
  We compare the first elements of both structures according to either just their timestamp or their timestamp & timepoint combination
  and add an element to the new structure according to the comparison.
  If the elements are equal, we merge their states and remove elements from both structures, while adding one new element to the new structure.
  If the element of structure one is has a smaller ts / ts & tp combination we add that element to the new structure while removing it from the old.
  If the element of structure two is has a smaller ts / ts & tp combination we add that element to the new structure while removing it from the old.
  We recursively do this over both structures until one/both are empty. If only one is empty the leftovers are added to the new structure.
*)

let rec comb_q1 q1 q2 nq =
  if Queue.is_empty q1 && Queue.is_empty q2 then ()
  else if not (Queue.is_empty q1) && Queue.is_empty q2 then Queue.iter (fun e -> Queue.add e nq) q1
  else if Queue.is_empty q1 && not (Queue.is_empty q2) then Queue.iter (fun e -> Queue.add e nq) q2
  else begin
    let e1 = Queue.peek q1 in
    let i1, ts1, r1 = e1 in 
    let e2 = Queue.peek q2 in
    let i2, ts2, r2 = e2 in
    if ts1 < ts2 then begin 
      ignore(Queue.pop q1);
      Queue.add e1 nq
    end  
    else if ts1 = ts2 then begin
      if i1 < i2 then begin
        ignore(Queue.pop q1);
        Queue.add e1 nq
      end    
      else if i1 = i2 then begin
        ignore(Queue.pop q1);
        ignore(Queue.pop q2);
        Queue.add (i1, ts1, (rel_u r1 r2)) nq
      end
      else begin 
        ignore(Queue.pop q2);
        Queue.add e2 nq 
      end
    end  
    else begin
      ignore(Queue.pop q2);
      Queue.add e2 nq
    end;
    comb_q1 q1 q2 nq
  end

let rec comb_q2 q1 q2 nq =
  if Queue.is_empty q1 && Queue.is_empty q2 then ()
  else if not (Queue.is_empty q1) && Queue.is_empty q2 then Queue.iter (fun e -> Queue.add e nq) q1
  else if Queue.is_empty q1 && not (Queue.is_empty q2) then Queue.iter (fun e -> Queue.add e nq) q2
  else begin
    let e1 = Queue.peek q1 in
    let ts1, r1 = e1 in 
    let e2 = Queue.peek q2 in
    let ts2, r2 = e2 in
    if ts1 < ts2 then begin 
      ignore(Queue.pop q1);
      Queue.add e1 nq
    end  
    else if ts1 = ts2 then begin
      ignore(Queue.pop q1);
      ignore(Queue.pop q2);
      Queue.add (ts1, (rel_u r1 r2)) nq
    end  
    else begin 
      ignore(Queue.pop q2);
      Queue.add e2 nq;
    end;
    comb_q2 q1 q2 nq
  end  


  let rec comb_dll1 l1 l2 nl f =
    if Dllist.is_empty l1 && Dllist.is_empty l2 then ()
    else if not (Dllist.is_empty l1) && Dllist.is_empty l2 then Dllist.iter (fun e -> Dllist.add_last e nl) l1
    else if Dllist.is_empty l1 && not (Dllist.is_empty l2) then Dllist.iter (fun e -> Dllist.add_last e nl) l2
    else begin
      let e1 = Dllist.pop_first l1 in
      let i1, ts1, r1 = e1 in 
      let e2 = Dllist.pop_first l2 in
      let i2, ts2, r2 = e2 in
      if ts1 < ts2 then begin 
        ignore(Dllist.add_first e2 l2);
        Dllist.add_last e1 nl
      end  
      else if ts1 = ts2 then begin
        if i1 < i2 then begin
          ignore(Dllist.add_first e2 l2);
          Dllist.add_last e1 nl
        end    
        else if i1 = i2 then begin
          Dllist.add_last (i1, ts1, (f r1 r2)) nl
        end
        else begin 
          ignore(Dllist.add_first e1 l1);
          Dllist.add_last e2 nl
        end
      end  
      else begin 
        ignore(Dllist.add_first e1 l1);
        Dllist.add_last e2 nl;
      end;
      comb_dll1 l1 l2 nl f 
    end

let rec comb_dll2 l1 l2 nl =
  if Dllist.is_empty l1 && Dllist.is_empty l2 then ()
  else if not (Dllist.is_empty l1) && Dllist.is_empty l2 then Dllist.iter (fun e -> Dllist.add_last e nl) l1
  else if Dllist.is_empty l1 && not (Dllist.is_empty l2) then Dllist.iter (fun e -> Dllist.add_last e nl) l2
  else begin
    let e1 = Dllist.pop_first l1 in
    let ts1, r1 = e1 in 
    let e2 = Dllist.pop_first l2 in
    let ts2, r2 = e2 in
    if ts1 < ts2 then begin 
      ignore(Dllist.add_first e2 l2);
      Dllist.add_last e1 nl
    end  
    else if ts1 = ts2 then begin
      Dllist.add_last (ts1, (rel_u r1 r2)) nl
    end  
    else begin 
      ignore(Dllist.add_first e1 l1);
      Dllist.add_last e2 nl
    end;
    comb_dll2 l1 l2 nl
  end

let rec comb_mq q1 q2 nq =
  if Mqueue.is_empty q1 && Mqueue.is_empty q2 then ()
  else if not (Mqueue.is_empty q1) && Mqueue.is_empty q2 then Mqueue.iter (fun e -> Mqueue.add e nq) q1
  else if Mqueue.is_empty q1 && not (Mqueue.is_empty q2) then Mqueue.iter (fun e -> Mqueue.add e nq) q2
  else begin
    let e1 = Mqueue.peek q1 in
    let ts1, r1 = e1 in 
    let e2 = Mqueue.peek q2 in
    let ts2, r2 = e2 in
    if ts1 < ts2 then begin 
      ignore(Mqueue.pop q1);
      Mqueue.add e1 nq
    end  
    else if ts1 = ts2 then begin
      ignore(Mqueue.pop q1);
      ignore(Mqueue.pop q2);
      Mqueue.add (ts1, (rel_u r1 r2)) nq
    end  
    else begin 
      ignore(Mqueue.pop q2);
      Mqueue.add e2 nq
    end;
    comb_mq q1 q2 nq
  end

let combine_queues1 q1 q2 =  
  let nq = Queue.create() in
  comb_q1 q1 q2 nq;
  nq

let combine_queues2 q1 q2 =  
  let nq = Queue.create() in
  comb_q2 q1 q2 nq;
  nq

let combine_mq q1 q2 =
  let nq = Mqueue.create() in 
  comb_mq q1 q2 nq;
  nq

let combine_dll1 l1 l2 =  
  let res = Dllist.empty() in
  comb_dll1 l1 l2 res rel_u;
  res

let combine_dll2 l1 l2 =  
  let res = Dllist.empty() in
  comb_dll2 l1 l2 res;
  res


(* 
 State combination functions
 - Essentially just call the above combination functions and return the combined state
 *)
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
  let saauxrels = combine_mq sainf1.saauxrels sainf2.saauxrels in
  {sres = (rel_u sainf1.sres sainf2.sres); sarel2 = sarel2; saauxrels = saauxrels}

let combine_sinfo sinf1 sinf2  =
  let srel2 = match (sinf1.srel2, sinf2.srel2) with
  | (Some r1, Some r2) -> Some (rel_u r1 r2)
  | (None, None) -> None
  | _ -> raise (Type_error ("Mismatched states in ainfo"))
  in
  let sauxrels = combine_mq sinf1.sauxrels sinf2.sauxrels in
  {srel2 = srel2; sauxrels = sauxrels}

let combine_muninfo muninf1 muninf2 =
  let mlistrel1 = combine_dll1 muninf1.mlistrel1 muninf2.mlistrel1 in 
  let mlistrel2 = combine_dll1 muninf1.mlistrel2 muninf2.mlistrel2 in 
  { mlast1 = muninf1.mlast1; mlast2 = muninf1.mlast2; mlistrel1 = mlistrel1; mlistrel2 = mlistrel2 }

let combine_muinfo muinf1 muinf2 =
  (* Helper function to combine raux and saux fields *)
  let sklist l1 l2 =
    let nl = Sk.empty() in
    comb_dll2 l1 l2 nl;
    nl
  in
  let mraux =
    let nl = Sj.empty() in
    comb_dll1 muinf1.mraux muinf2.mraux nl sklist;
    nl
  in
  let murel2 = match (muinf1.murel2, muinf2.murel2) with
  | (Some r1, Some r2) -> Some (rel_u r1 r2)
  | (None, None) -> None
  | _ -> raise (Type_error ("Mismatched states in ainfo"))
  in
  { mulast = muinf1.mulast; mufirst = muinf1.mufirst; mures = (rel_u muinf1.mures muinf2.mures);
    murel2 = murel2; mraux = mraux; msaux = (sklist muinf1.msaux muinf2.msaux) }

let combine_ozinfo ozinf1 ozinf2 =
  let mozauxrels = combine_dll1 ozinf1.mozauxrels ozinf2.mozauxrels in { mozauxrels = mozauxrels }

let combine_oainfo oainf1 oainf2 =
  let oaauxrels = combine_mq oainf1.oaauxrels oainf2.oaauxrels in
  { ores = (rel_u oainf1.ores oainf2.ores); oaauxrels = oaauxrels }
  
let combine_oinfo moinf1 moinf2 =
  let moauxrels = combine_dll2 moinf1.moauxrels moinf2.moauxrels in
  { moauxrels = moauxrels; }

let combine_ezinfo mezinf1 mezinf2 =
  let mezauxrels = combine_dll1 mezinf1.mezauxrels mezinf2.mezauxrels in
  {mezauxrels = mezauxrels }

let combine_einfo meinf1 meinf2 =
  let meauxrels = combine_dll2 meinf1.meauxrels meinf2.meauxrels in
  {meauxrels = meauxrels}

(*
  Combine two mformulas recursively. We must assume they have the same structure. 
  If they do not, we raise an error.
 *)
let rec comb_m f1 f2  =
  match (f1,f2) with
    | (MRel  (rel1),          MRel(rel2))
      -> MRel (Relation.union rel1 rel2)
    | (MPred (p, comp, inf1), MPred(_, _, inf2))
      -> MPred(p, comp, combine_info inf1 inf2)
    | (MNeg  (f11), MNeg(f21))
      -> MNeg (comb_m f11 f21)
    | (MAnd  (c, f11, f12, ainf1), MAnd(_, f21, f22, ainf2))
      -> MAnd (c, comb_m f11 f21, comb_m f12 f22, (combine_ainfo ainf1 ainf2))
    | (MOr   (c, f11, f12, ainf1), MOr (_, f21, f22, ainf2))
      -> MOr  (c, comb_m f11 f21, comb_m f12 f22, (combine_ainfo ainf1 ainf2))
    | (MExists (c, f11), MExists(_,f21))
      -> MExists        (c, comb_m f11 f21)
    | (MAggreg (c, f11), MAggreg(_,f21))
      -> MAggreg        (c, comb_m f11 f21)
    | (MAggOnce (f11, dt, agg1, update_old, update_new, get_result), MAggOnce (f21, _, agg2, _, _, _))
      -> MAggOnce  (comb_m f11 f21, dt, combine_agg agg1 agg2, update_old, update_new, get_result)
    | (MAggMMOnce (f11, dt, aggMM1, update_old, update_new, get_result), MAggMMOnce (f21, _, aggMM2, _, _, _))
      -> MAggMMOnce (comb_m f11 f21, dt, combine_aggMM aggMM1 aggMM2, update_old, update_new, get_result)
    | (MPrev (dt, f11, pinf1), MPrev ( _, f21, pinf2))
      -> MPrev          (dt, comb_m f11 f21, pinf1)
    | (MNext (dt, f11, ninf1), MNext ( _, f21, ninf2))
      -> MNext          (dt, comb_m f11 f21, ninf1)
    | (MSinceA (c2, dt, f11, f12, sainf1), MSinceA( _, _, f21, f22, sainf2))
      -> MSinceA        (c2, dt, comb_m f11 f21, comb_m f12 f22, combine_sainfo sainf1 sainf2)
    | (MSince (c2, dt, f11, f12, sinf1), MSince( _, _, f21, f22, sinf2))
      -> MSince         (c2, dt, comb_m f11 f21, comb_m f12 f22, combine_sinfo sinf1 sinf2)
    | (MOnceA (dt, f11, oainf1), MOnceA ( _, f21, oainf2))
      -> MOnceA         (dt, comb_m f11 f21, combine_oainfo oainf1 oainf2)
    | (MOnceZ (dt, f11, ozinf1), MOnceZ ( _, f21, ozinf2))
      -> MOnceZ         (dt, comb_m f11 f21, combine_ozinfo ozinf1 ozinf2)
    | (MOnce (dt, f11, oinf1), MOnce ( _, f21, oinf2))
      -> MOnce        (dt, comb_m f11 f21, combine_oinfo oinf1 oinf2)
    | (MNUntil (c1, dt, f11, f12, muninf1), MNUntil  ( _, _, f21, f22, muninf2))
      -> MNUntil        (c1, dt, comb_m f11 f21, comb_m f12 f22, combine_muninfo muninf1 muninf2)
    | (MUntil (c1, dt, f11, f12, muinf1), MUntil ( _, _, f21, f22, muinf2))
      -> MUntil         (c1, dt, comb_m f11 f21, comb_m f12 f22, combine_muinfo muinf1 muinf2)
    | (MEventuallyZ (dt, f11, ezinf1), MEventuallyZ (_, f21, ezinf2))
      -> MEventuallyZ   (dt, comb_m f11 f21, combine_ezinfo ezinf1 ezinf2)
    | (MEventually (dt, f11, einf1), MEventually (_, f21, einf2))
      -> MEventually   (dt, comb_m f11 f21, combine_einfo einf1 einf2)
    | _ -> raise (Type_error ("Mismatched formulas in combine_states")) 

(* END COMBINING STATES *)


(* SPLITTING STATE *)

(* For each formula, returns list of relevant free variables according to sub structure *)
let get_predicate f =
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

(*
  split_state function splits an mformula.
  - mapping: A function mapping a tuple to a partition array (int array)
  - mf:      mformula to be split
  - size:    Number of partitions

  Returns an array of the size [size] each containing a split mformula with the index representing a partition.
*)
let split_state mapping mf size =

  (* split function splits a relation according to the list of free variables and the "split_state" mapping
     - rel:   Relation.relation to be split
     - preds: free vars representing the column keys of [rel]
     
     Returns an array of size [size], each containing a split of the relation, the array index representing the partition.
   *)
  let split rel preds =
    let res = Array.make size Relation.empty in
    (* Iterate over relation, adding tuples to relations of partitions where they are relevant *)
    Relation.iter (fun t -> let parts = mapping t preds in Array.iter (fun p -> res.(p) <- Relation.add t res.(p)) parts) rel;
    res
  in


  (* Split functions for queues and lists all work in a similar fashion:
     1. Create array of size [size], each element containing an empty structure
     2. Iterate over state structure:
        i. split state in each element
        ii. iterate over resulting split array according to the index
             - add each element to the array created in 1 using the index
     This results in an array of split structures.
  *)

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

  (*
    State splitting functions.
    - Call the above structure splitting function to split the structures in the state, then return an array of split states.
   *)

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
    let dllists = split_dll1 mozinf.mozauxrels p in
    Array.map (fun e -> {mozauxrels = e }) dllists
  in
  let split_moinfo moinf p =
    let dllists = split_dll2 moinf.moauxrels p in
    Array.map (fun e -> { moauxrels = e }) dllists
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
    Array.map (fun e -> { mezauxrels = e }) dllists
  in
  let split_meinfo meinf p =
    let dllists = split_dll2 meinf.meauxrels p in
    Array.map (fun e -> { meauxrels = e }) dllists
  in
  let p1 f1 = get_predicate f1 in
  let p2 f1 f2 = get_predicate2 f1 f2 in
  (* Recursive split call: At each step 
     - call split on the subformula(s), resulting in array(s)
     - get the relevant list of free vars and split the state, resulting in an array 
     - create and return an array of formulas:
          each index containing the relevant part of the state and relevant split of the subformula(s) *)
  let rec split_f = function
    (* TODO: MRel *)
    | MRel           (rel)                                      -> Array.make size (MRel(rel)) 
    | MPred          (p, comp, inf)                             -> let arr = split_info inf (pvars p) in Array.map (fun e -> MPred(p, comp, e)) arr
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
    

let check_tuple t vl =
  (* Lists always have same length due to filtering in split function *)
  let eval = List.mapi (fun i e -> List.exists (fun e2 -> (List.nth t i) = e2) e) vl in
  List.fold_right (fun a agg -> (a || agg)) eval false  

(* Split function for use with the manual split call *)
let split_according_to_lists keys num_partitions constraints t p = 
  let pos = List.map (fun k -> try Misc.get_pos k p with e -> -1 ) keys in
  (* columns not in cs.keys are filtered -> so ignored for checking tuples *)
  let pos = List.filter (fun e -> e >= 0) pos in
  (* If no specified keys are in the predicate list, return all partitions *)
  if List.length pos = 0 then let res = Array.make num_partitions 0 in Array.mapi (fun i e -> i) res else
  (* Else we create a mapping to reorder our partition input values *)
  let mapping t = List.map (fun e -> List.nth t e) pos in
  let output = Array.of_list (List.flatten (List.map (fun cs -> if check_tuple t (mapping cs.values) then cs.partitions else []) constraints)) in
  output  

(* Split function for use with the experiment set up *)  
let split_according_to_modulo keys num_partitions t p  = 
  let pos = List.map (fun k -> try Misc.get_pos k p with e -> -1 ) keys in
  (* columns not in cs.keys are filtered -> so ignored for checking tuples *)
  let pos = List.filter (fun e -> e >= 0) pos in
  (* If no specified keys are in the predicate list, return all partitions *)
  if List.length pos = 0 then let res = Array.make num_partitions 0 in Array.mapi (fun i e -> i) res else
  (* Else we create a mapping to reorder our partition input values *)
  let map t = List.map (fun e -> List.nth t e) pos in

  let t = int_of_cst (List.hd (map t)) in
  (*if t mod 3 = 0 then [|0; 1|]
  else begin*)
    if t mod 2 = 0 then [|0|]
    else [|1|]
  (*end*)

  
(* Splits formula according to:
    - the keys and the number of partitions specified in sconts
    - the mapping from tuple -> partitions it defines
 *)  
let split_formula sconsts dumpfile i lastts mf closed neval =
  let numparts = (sconsts.num_partitions+1) in

  let keys = sconsts.keys in

  let mapping = split_according_to_modulo keys numparts in
  split_state mapping mf numparts


(* END SPLITTING STATE *) 

(* Combines two neval lists according to the timestamp and timepoints of their elements,
   see the combination functions at the top for a more detailed explanation *)
let combine_neval nv1 nv2 =
  let nl = NEval.empty() in
  let rec combine l1 l2 = 
    if Dllist.is_empty l1 && Dllist.is_empty l2 then ()
    else if not (Dllist.is_empty l1) && Dllist.is_empty l2 then Dllist.iter (fun e -> Dllist.add_last e nl) l1
    else if Dllist.is_empty l1 && not (Dllist.is_empty l2) then Dllist.iter (fun e -> Dllist.add_last e nl) l2
    else begin
      let e1 = Dllist.pop_first l1 in
      let i1, ts1 = e1 in 
      let e2 = Dllist.pop_first l2 in
      let i2, ts2 = e2 in
      if ts1 < ts2 then begin 
        ignore(Dllist.add_first e2 l2);
        Dllist.add_last e1 nl
      end  
      else if ts1 = ts2 then begin
        if i1 < i2 then begin
          ignore(Dllist.add_first e2 l2);
          Dllist.add_last e1 nl
        end    
        else if i1 = i2 then begin
          Dllist.add_last (i1, ts1) nl
        end
        else begin 
          ignore(Dllist.add_first e1 l1);
          Dllist.add_last e2 nl
        end
      end  
      else begin 
        ignore(Dllist.add_first e1 l1);
        Dllist.add_last e2 nl
      end;
      combine l1 l2
    end
  in  
  combine nv1 nv2;
  nl

let rec print_ef = function
  | ERel           (rel)                                      -> Printf.printf "Rel:"; Relation.print_rel "" rel; print_endline "";
  | EPred          (p, comp, inf)                             -> print_endline "Pred:"; Queue.iter(fun e-> let _,_,r = e in Relation.print_rel "" r) inf; print_endline "";
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