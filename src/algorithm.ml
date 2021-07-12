(*
 * This file is part of MONPOLY.
 *
 * Copyright (C) 2011 Nokia Corporation and/or its subsidiary(-ies).
 * Contact:  Nokia Corporation (Debmalya Biswas: debmalya.biswas@nokia.com)
 *
 * Copyright (C) 2012 ETH Zurich.
 * Contact:  ETH Zurich (Eugen Zalinescu: eugen.zalinescu@inf.ethz.ch)
 *
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, version 2.1 of the
 * License.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library. If not, see
 * http://www.gnu.org/licenses/lgpl-2.1.html.
 *
 * As a special exception to the GNU Lesser General Public License,
 * you may link, statically or dynamically, a "work that uses the
 * Library" with a publicly distributed version of the Library to
 * produce an executable file containing portions of the Library, and
 * distribute that executable file under terms of your choice, without
 * any of the additional requirements listed in clause 6 of the GNU
 * Lesser General Public License. By "a publicly distributed version
 * of the Library", we mean either the unmodified Library as
 * distributed by Nokia, or a modified version of the Library that is
 * distributed under the conditions defined in clause 3 of the GNU
 * Lesser General Public License. This exception does not however
 * invalidate any other reasons why the executable file might be
 * covered by the GNU Lesser General Public License.
 *)



(** This module implements the monitoring algorithm. This algorithm is
    described in the paper "Runtime Monitoring of Metric First-order
    Temporal Properties" by David Basin, Felix Klaedtke, Samuel
    Muller, and Birgit Pfitzmann, presented at FSTTCS'08.


    This is the MONPOLY's main module, all other modules can be seen
    as "helper" modules. The module's entry point is normally the
    [monitor] function. This function checks that the given formula is
    monitorable and then calls the [check_log] function which
    iteratively reads each log entry. To be able to incrementally
    process the entries, the input formula is first extended with
    additional information for each subformula, by calling the
    [add_ext] function.  Also, a queue [neval] of not-yet evaluated
    indexes of log entries is maintained.

    The function [check_log] reads each log entry, calls [add_index]
    to update the extended formula with the new information from the
    entry at index [i], adds index [i] to the queue of not-yet
    evaluated indexes, and finally calls [process_index] to process
    this entry.

    The function [process_index] iterativelly tries to evaluate the
    formula at each index (calling the function [eval]) from the queue
    of not-yet evaluated indexes. It stops when the formula cannot be
    evaluated or when the formula has been evaluated at all indexes in
    the queue. The function [eval] performs a bottom-up evaluation of
    the formula.
*)


open Dllist
open Misc
open Perf
open Predicate
open MFOTL
open Tuple
open Relation
open Table
open Db
open Log
open Sliding
open Helper

open Marshalling
open Splitting
open Extformula
open Mformula
open Hypercube_slicer

module Sk = Dllist
module Sj = Dllist

let resumefile = ref ""
let dumpfile = ref ""
let combine_files = ref ""
let lastts = ref MFOTL.ts_invalid
let slicer_heavy_unproc : (int * string list) array ref= ref [|(0, [])|]
let slicer_shares = ref [|[||]|]
let slicer_seeds  = ref [|[||]|]

(* For the sake of clarity, think about merging these types and all
   related functions. Some fields will be redundant, but we will not lose
   that much. *)

let crt_ts = ref MFOTL.ts_invalid
let crt_tp = ref (-1)

let make_db db =
  Db.make_db (List.map (fun (s,r) -> Table.make_table s r) db)

let mqueue_add_last auxrels tsq rel2 =
  if Mqueue.is_empty auxrels then
    Mqueue.add (tsq,rel2) auxrels
  else
    let tslast, rellast =  Mqueue.get_last auxrels in
    if tslast = tsq then
      Mqueue.update_last (tsq, Relation.union rellast rel2) auxrels
    else
      Mqueue.add (tsq,rel2) auxrels

let dllist_add_last auxrels tsq rel2 =
  if Dllist.is_empty auxrels then
    Dllist.add_last (tsq,rel2) auxrels
  else
    let tslast, rellast = Dllist.get_last auxrels in
    if tslast = tsq then
      let _ = Dllist.pop_last auxrels in
      Dllist.add_last (tsq, Relation.union rellast rel2) auxrels
    else
      Dllist.add_last (tsq,rel2) auxrels

(* [saauxrels] consists of those relations that are outside of the
   relevant time window *)
let update_since_all intv tsq inf comp rel1 rel2 =
  inf.sres <- comp inf.sres rel1;
  let auxrels = inf.saauxrels in
  let rec elim () =
    if not (Mqueue.is_empty auxrels) then
      let (tsj,relj) = Mqueue.top auxrels in
      if MFOTL.in_right_ext (MFOTL.ts_minus tsq tsj) intv then
        begin
          ignore (Mqueue.pop auxrels);
          inf.sres <- Relation.union inf.sres (comp relj rel1);
          elim ()
        end
  in
  elim ();

  Mqueue.update_and_delete
    (fun (tsj, relj) -> (tsj, comp relj rel1))
    (fun (_,relj) -> Relation.is_empty relj) (* delete the current node if newrel is empty *)
    auxrels;

  if not (Relation.is_empty rel2) then
    begin
      if MFOTL.in_right_ext MFOTL.ts_null intv then
        inf.sres <- Relation.union inf.sres rel2;
      mqueue_add_last auxrels tsq rel2
    end;

  inf.sres



let update_since intv tsq auxrels comp discard rel1 rel2 =
  let rec elim_old_auxrels () =
    (* remove old elements that felt out of the interval *)
    if not (Mqueue.is_empty auxrels) then
      let (tsj,relj) = Mqueue.top auxrels in
      if not (MFOTL.in_left_ext (MFOTL.ts_minus tsq tsj) intv) then
        begin
          ignore(Mqueue.pop auxrels);
          elim_old_auxrels()
        end
  in
  elim_old_auxrels ();

  let res = ref Relation.empty in
  Mqueue.update_and_delete
    (fun (tsj,relj) ->
       let newrel = comp relj rel1 in
       if (not discard) && MFOTL.in_right_ext (MFOTL.ts_minus tsq tsj) intv then
         res := Relation.union !res newrel;
       (tsj,newrel)
    )
    (* delete the current node if newrel is empty *)
    (fun (_,relj) -> Relation.is_empty relj)
    auxrels;

  if not (Relation.is_empty rel2) then
    begin
      if (not discard) && MFOTL.in_right_ext MFOTL.ts_null intv then
        res := Relation.union !res rel2;
      mqueue_add_last auxrels tsq rel2
    end;

  !res


let update_once_all intv tsq inf =
  let auxrels = inf.oaauxrels in
  let rec comp () =
    if not (Mqueue.is_empty auxrels) then
      let (tsj,relj) = Mqueue.top auxrels in
      if MFOTL.in_right_ext (MFOTL.ts_minus tsq tsj) intv then
        begin
          ignore (Mqueue.pop auxrels);
          inf.ores <- Relation.union inf.ores relj;
          comp ()
        end
  in
  comp ()

(* Remark: we could remove all auxrels that are covered by the tree and
   gain some memory (sooner). However detecting [lw] would be harder. *)
let update_once_zero intv q tsq inf rel2 discard =
  let auxrels = inf.ozauxrels in

  let rec elim_old_ozauxrels () =
    (* remove old elements that fell out of the interval *)
    if not (Dllist.is_empty auxrels) then
      let (_, tsj, arel) = Dllist.get_first auxrels in
      if not (MFOTL.in_left_ext (MFOTL.ts_minus tsq tsj) intv) then
        begin
          if inf.ozlast != Dllist.void && inf.ozlast == Dllist.get_first_cell auxrels then
            inf.ozlast <- Dllist.void;
          ignore(Dllist.pop_first auxrels);
          elim_old_ozauxrels()
        end
  in
  elim_old_ozauxrels ();

  if not (Relation.is_empty rel2) then
    Dllist.add_last (q,tsq,rel2) inf.ozauxrels;

  if Dllist.is_empty auxrels || discard then
    Relation.empty
  else
    let cond = fun _ -> true in
    let f = fun (j,_,rel) -> (j,rel) in
    let subseq, new_last = get_new_elements auxrels inf.ozlast cond f in
    let lw,_,_ = Dllist.get_first auxrels in
    let rw =
      if subseq = [] then
        let j,_,_ = Dllist.get_data inf.ozlast in j
      else
        begin
          assert (new_last != Dllist.void);
          inf.ozlast <- new_last;
          let rw = fst (List.hd subseq) in
          assert (rw = let j,_,_ = Dllist.get_data new_last in j);
          rw
        end
    in
    if Misc.debugging Dbg_eval then
      begin
        Printf.printf "[update_once_zero] lw = %d rw = %d " lw rw;
        Misc.printnl_list "subseq = " print_auxel subseq;
      end;
    let newt = Sliding.slide string_of_int Relation.union subseq (lw, rw) inf.oztree in
    inf.oztree <- newt;
    Sliding.stree_res newt


let update_once intv tsq inf discard =
  let auxrels = inf.oauxrels in
  let rec elim_old_oauxrels () =
    (* remove old elements that fell out of the interval *)
    if not (Dllist.is_empty auxrels) then
      let (tsj,_) = Dllist.get_first auxrels in
      if not (MFOTL.in_left_ext (MFOTL.ts_minus tsq tsj) intv) then
        begin
          if inf.olast != Dllist.void && inf.olast == Dllist.get_first_cell auxrels then
            inf.olast <- Dllist.void;
          ignore(Dllist.pop_first auxrels);
          elim_old_oauxrels()
        end
  in
  elim_old_oauxrels ();

  (* In the following we distiguish between the new window and the new
     elements: the new window may contain old elements (the old and new
     windows may overlap). *)

  if Dllist.is_empty auxrels || discard then
    Relation.empty
  else
    let lw = fst (Dllist.get_first auxrels) in
    if MFOTL.in_right_ext (MFOTL.ts_minus tsq lw) intv then
      (* the new window is not empty *)
      let cond = fun (tsj,_) -> MFOTL.in_right_ext (MFOTL.ts_minus tsq tsj) intv in
      let subseq, new_last = get_new_elements auxrels inf.olast cond (fun x -> x) in
      let rw =
        if subseq = [] then
          fst (Dllist.get_data inf.olast)
        else
          begin
            assert (new_last != Dllist.void);
            inf.olast <- new_last;
            let rw = fst (List.hd subseq) in
            assert (rw = fst (Dllist.get_data new_last));
            rw
          end
      in
      if Misc.debugging Dbg_eval then
        begin
          Printf.printf "[update_once] lw = %s rw = %s "
            (MFOTL.string_of_ts lw)
            (MFOTL.string_of_ts rw);
          Misc.printnl_list "subseq = " print_sauxel subseq;
        end;
      let newt = Sliding.slide MFOTL.string_of_ts Relation.union subseq (lw, rw) inf.otree in
      inf.otree <- newt;
      Sliding.stree_res newt
    else
      begin
        (* the new window is empty,
           because not even the oldest element satisfies the constraint *)
        inf.otree <- LNode {l = MFOTL.ts_invalid;
                            r = MFOTL.ts_invalid;
                            res = Some (Relation.empty)};
        inf.olast <- Dllist.void;
        Relation.empty
      end





let update_old_until q tsq i intv inf discard  =
  (* eliminate those entries (q-1,reli) from rels;
     return the tuples which hold at q *)
  let elim_old j rels =
    assert(j>=q-1);
    if not (Sk.is_empty rels) then
      let (k,relk) = Sk.get_first rels in
      if k=q-1 then
        begin
          ignore(Sk.pop_first rels);
          if not (Sk.is_empty rels) then
            let (k',relk') = Sk.pop_first rels in
            assert(k'>=q && j>=q);
            let newrelk' = Relation.union relk relk' in
            Sk.add_first (k',newrelk') rels;
            if k'=q then
              newrelk'
            else
              relk
          else
          if (j>q-1) then
            begin
              Sk.add_first (k+1,relk) rels;
              relk
            end
          else
            Relation.empty
        end
      else
        begin
          assert(k>q-1);
          if k=q then
            relk
          else
            Relation.empty
        end
    else (* Sk.is_empty rels = true *)
      Relation.empty
  in


  let rec elim_old_raux () =
    (* remove old elements that fell out of the interval *)
    if not (Sj.is_empty inf.raux) then
      let (j,tsj,_) = Sj.get_first inf.raux in
      if j<q || not (MFOTL.in_right_ext (MFOTL.ts_minus tsj tsq) intv) then
        begin
          ignore(Sj.pop_first inf.raux);
          elim_old_raux()
        end
  in

  elim_old_raux ();

  Sj.iter (
    fun (j,tsj,rrels) ->
      assert(j>=q);
      assert(MFOTL.in_right_ext (MFOTL.ts_minus tsj tsq) intv);
      let relq = elim_old j rrels in
      if (not discard) && not (Relation.is_empty relq) then
        inf.ures <- Relation.union inf.ures relq;
      if Misc.debugging Dbg_eval then
        Relation.print_reln "[update_aux] res: " inf.ures;
  ) inf.raux;

  (* saux holds elements (k,relk) for the last seen index,
     i.e. [i] *)
  assert(i>=q-1);
  if i=q-1 then
    Sk.clear inf.saux
  else
    ignore(elim_old i inf.saux)


(* Auxiliary functions for the f1 Until_I f2 case.

   The saux list contains tuples (k,Sk) (ordered incrementally by k),
   with q <= k <= i, such that the tuples in Sk satisfy f1
   continuously between k and i, and k is minimal (that is, if a tuple
   is in Sk it will not also be in Sk' with k'>k.)

   The raux list contains tuples (j,tj,Lj) (ordered incrementaly by
   j), with q <= j <= i, where Lj is a list of tuples (k,Rk) (ordered
   incrementaly by k), with q <= k <= j, such that the tuples in Rk
   satisfy f2 at j and satisfy f1 continuously between k and j-1, and
   k is minimal (that is, if a tuple is in Rk it will not also be in
   Rk' with j>=k'>k.)

   NOTE: The iteration through raux to eliminate those tuples <k,Sk>
   with k<q (ie. k=q-1) seems unnecessary. If a tuple in Sk satisfies
   f1 continuously from k to j, then it also satisfies f1 continuously
   from q to j.
*)


let combine2 comp j rels rel2 =
  let nrels = Sk.empty() in
  let curr_rel2 = ref rel2 in
  Sk.iter
    (fun (k,rel) ->
       let nrel = comp !curr_rel2 rel in
       if not (Relation.is_empty nrel) then
         Sk.add_last (k,nrel) nrels;
       curr_rel2 := Relation.diff !curr_rel2 nrel;
    ) rels;
  if not (Relation.is_empty !curr_rel2) then
    Sk.add_last (j,!curr_rel2) nrels;
  nrels

let get_relq q rels =
  if not (Sj.is_empty rels) then
    let (k,relk) = Sj.get_first rels in
    if k = q then Some relk
    else None
  else
    None

let update_until q tsq i tsi intv rel1 rel2 inf comp discard =
  if Misc.debugging Dbg_eval then
    print_uinf "[update_until] inf: " inf;
  assert(i >= q);
  let nsaux = combine2 Relation.inter i inf.saux rel1 in
  if (MFOTL.in_right_ext (MFOTL.ts_minus tsi tsq) intv) &&
     not (Relation.is_empty rel2) then
    begin
      let rrels = combine2 comp i inf.saux rel2 in
      Sj.add_last (i,tsi,rrels) inf.raux;
      if not discard then
        match get_relq q rrels with
        | Some rel -> inf.ures <- Relation.union inf.ures rel
        | None -> ()
    end;
  inf.saux <- nsaux


let elim_old_eventually q tsq intv inf =
  let auxrels = inf.eauxrels in

  let rec elim_old_eauxrels () =
    (* remove old elements that fell out of the interval *)
    if not (Dllist.is_empty auxrels) then
      let (tsj, _) = Dllist.get_first auxrels in
      if not (MFOTL.in_right_ext (MFOTL.ts_minus tsj tsq) intv) then
        begin
          if inf.elast != Dllist.void && inf.elast == Dllist.get_first_cell auxrels then
            inf.elast <- Dllist.void;
          ignore(Dllist.pop_first auxrels);
          elim_old_eauxrels()
        end
  in

  elim_old_eauxrels ()


let warn_if_empty_aggreg {op; default} {Aggreg.empty_rel; Aggreg.rel} =
  if empty_rel then
    (match op with
    | Avg | Med | Min | Max ->
      let op_str = MFOTL.string_of_agg_op op in
      let default_str = string_of_cst default in
      let msg = Printf.sprintf "WARNING: %s applied on empty relation! \
                                Resulting value is %s, by (our) convention.\n"
        op_str default_str
      in
      prerr_string msg
    | Cnt | Sum -> ());
  rel


let add_let_index f n rels =
  let rec update = function
    | EPred (p, comp, inf) ->
      if Predicate.get_name p = n then
        List.iter (fun (i,tsi,rel) -> Queue.add (i,tsi, comp rel) inf) rels
      else ()

    | ELet (p, comp, f1, f2, inf) ->
      update f1;
      if Predicate.get_name p = n then () else update f2

    | ERel _ -> ()

    | ENeg f1
    | EExists (_,f1)
    | EAggOnce (_,_,f1)
    | EAggreg (_,_,f1)
    | ENext (_,f1,_)
    | EPrev (_,f1,_)
    | EOnceA (_,f1,_)
    | EOnceZ (_,f1,_)
    | EOnce (_,f1,_)
    | EEventuallyZ (_,f1,_)
    | EEventually (_,f1,_) ->
      update f1

    | EAnd (_,f1,f2,_)
    | EOr (_,f1,f2,_)
    | ESinceA (_,_,f1,f2,_)
    | ESince (_,_,f1,f2,_)
    | ENUntil (_,_,f1,f2,_)
    | EUntil (_,_,f1,f2,_) ->
      update f1;
      update f2
  in
  update f



(* Arguments:
   - [f] the current formula
   - [crt] the current evaluation point (an neval cell)
   - [discard] a boolean; if true then the result is not used
               (only a minimal amount of computation should be done);
               it should not be propagated for temporal subformulas
               (pitfall: possible source of bugs)
*)
let rec eval f crt discard =
  let (q,tsq) = Neval.get_data crt in

  if Misc.debugging Dbg_eval then
    begin
      print_extf "\n[eval] evaluating formula\n" f;
      Printf.printf "at (%d,%s) with discard=%b\n%!"
        q (MFOTL.string_of_ts tsq) discard
    end;

  match f with
  | ERel rel -> Some rel

  | EPred (p,_,inf) ->
    if Misc.debugging Dbg_eval then
      begin
        print_string "[eval,Pred] ";
        Predicate.print_predicate p;
        print_predinf  ": " inf
      end;

    if Queue.is_empty inf
    then None
    else begin
      let (cq,ctsq,rel) = Queue.pop inf in
      assert (cq = q && ctsq = tsq);
      Some rel
    end

  | ELet (p, comp, f1, f2, inf) ->
      let rec eval_f1 rels =
        if Neval.is_last inf.llast then
          rels
        else
          let crt1 = Neval.get_next inf.llast in
          match eval f1 crt1 false with
          | Some rel ->
            inf.llast <- crt1;
            let (i, tsi) = Neval.get_data crt1 in
            eval_f1 ((i, tsi, comp rel) :: rels)
          | None -> rels
      in
      add_let_index f2 (Predicate.get_name p) (List.rev (eval_f1 []));
      eval f2 crt discard

  | ENeg f1 ->
    (match eval f1 crt discard with
     | Some rel ->
       let res =
         if Relation.is_empty rel then (* false? *)
           Relation.singleton (Tuple.make_tuple [])
         else
           Relation.empty (* true *)
       in
       Some res
     | None -> None
    )

  | EExists (comp,f1) ->
    (match eval f1 crt discard with
     | Some rel -> Some (comp rel)
     | None -> None
    )

  | EAnd (comp,f1,f2,inf) ->
    (* we have to store rel1, if f2 cannot be evaluated *)
    let eval_and rel1 =
      if Relation.is_empty rel1 then
        (match eval f2 crt true with
         | Some _ ->
           inf.arel <- None;
           Some rel1
         | None ->
           inf.arel <- Some rel1;
           None
        )
      else
        (match eval f2 crt discard with
         | Some rel2 ->
           inf.arel <- None;
           Some (comp rel1 rel2)
         | None ->
           inf.arel <- Some rel1;
           None
        )
    in
    (match inf.arel with
     | Some rel1 -> eval_and rel1
     | None ->
       (match eval f1 crt discard with
        | Some rel1 -> eval_and rel1
        | None -> None
       )
    )

  | EAggreg (inf, comp, f) ->
    (match eval f crt discard with
     | Some rel ->
       Some (if discard then Relation.empty
         else warn_if_empty_aggreg inf (comp rel))
     | None -> None
    )

  | EOr (comp, f1, f2, inf) ->
    (* we have to store rel1, if f2 cannot be evaluated *)
    (match inf.arel with
     | Some rel1 ->
       (match eval f2 crt discard with
        | Some rel2 ->
          inf.arel <- None;
          Some (comp rel1 rel2)
        | None -> None
       )
     | None ->
       (match eval f1 crt discard with
        | Some rel1 ->
          (match eval f2 crt discard with
           | Some rel2 -> Some (comp rel1 rel2)
           | None ->
             inf.arel <- Some rel1;
             None
          )
        | None -> None
       )
    )

  | EPrev (intv,f1,inf) ->
    if Misc.debugging Dbg_eval then
      Printf.printf "[eval,Prev] inf.plast=%s\n%!" (Neval.string_of_cell inf.plast);

    if q = 0 then
      Some Relation.empty
    else
      begin
        let pcrt = Neval.get_next inf.plast in
        let pq, ptsq = Neval.get_data pcrt in
        assert(pq = q-1);
        match eval f1 pcrt discard with
        | Some rel1 ->
          inf.plast <- pcrt;
          if MFOTL.in_interval (MFOTL.ts_minus tsq ptsq) intv then
            Some rel1
          else
            Some Relation.empty
        | None -> None
      end

  | ENext (intv,f1,inf) ->
    if Misc.debugging Dbg_eval then
      Printf.printf "[eval,Next] inf.init=%b\n%!" inf.init;

    if inf.init then
      begin
        match eval f1 crt discard with
        | Some _ -> inf.init <- false
        | _ -> ()
      end;

    if Neval.is_last crt then
      None
    else
      begin
        let ncrt = Neval.get_next crt in
        let nq, ntsq = Neval.get_data ncrt in
        assert (nq = q+1);
        match eval f1 ncrt discard with
        | Some rel1 ->
          if MFOTL.in_interval (MFOTL.ts_minus ntsq tsq) intv then
            Some rel1
          else
            Some Relation.empty
        | None -> None
      end

  | ESinceA (comp,intv,f1,f2,inf) ->
    if Misc.debugging Dbg_eval then
      Printf.printf "[eval,SinceA] q=%d\n%!" q;

    let eval_f1 rel2 comp2 =
      (match eval f1 crt false with
       | Some rel1 ->
         inf.sarel2 <- None;
         Some (comp2 rel1 rel2)
       | None ->
         inf.sarel2 <- Some rel2;
         None
      )
    in

    let update_sauxrels = update_since_all intv tsq inf comp in

    (match inf.sarel2 with
     | Some rel2 -> eval_f1 rel2 update_sauxrels
     | None ->
       (match eval f2 crt false with
        | None -> None
        | Some rel2 -> eval_f1 rel2 update_sauxrels
       )
    )

  | ESince (comp,intv,f1,f2,inf) ->
    if Misc.debugging Dbg_eval then
      Printf.printf "[eval,Since] q=%d\n" q;

    let eval_f1 rel2 comp2 =
      (match eval f1 crt false with
       | Some rel1 ->
         inf.srel2 <- None;
         Some (comp2 rel1 rel2)
       | None ->
         inf.srel2 <- Some rel2;
         None
      )
    in

    let update_sauxrels = update_since intv tsq inf.sauxrels comp discard in

    (match inf.srel2 with
     | Some rel2 -> eval_f1 rel2 update_sauxrels
     | None ->
       (match eval f2 crt false with
        | None -> None
        | Some rel2 -> eval_f1 rel2 update_sauxrels
       )
    )


  | EOnceA ((c,_) as intv, f2, inf) ->
    (match eval f2 crt false with
     | None -> None
     | Some rel2 ->
       if Misc.debugging Dbg_eval then
         Printf.printf "[eval,OnceA] q=%d\n" q;

       if c = CBnd MFOTL.ts_null then
         begin
           inf.ores <- Relation.union inf.ores rel2;
           Some inf.ores
         end
       else
         begin
           if not (Relation.is_empty rel2) then
             mqueue_add_last inf.oaauxrels tsq rel2;

           update_once_all intv tsq inf;
           Some inf.ores
         end
    )

  | EAggOnce (inf, state, f) ->
    (match eval f crt false with
     | Some rel ->
       state#update tsq rel;
       Some (if discard then Relation.empty
         else warn_if_empty_aggreg inf state#get_result)
     | None -> None
    )

  (* We distinguish between whether the left margin of [intv] is
     zero or not, as we need to have two different ways of
     representing the margins of the windows in the tree: when 0
     is not included we can use the timestamps and merge
     relations at equal timestamps; otherwise, when 0 is not
     included, we need to use the timepoints. *)
  | EOnceZ (intv,f2,inf) ->
    (match eval f2 crt false with
     | None -> None
     | Some rel2 ->
       if Misc.debugging Dbg_eval then
         Printf.printf "[eval,OnceZ] q=%d\n" q;

       Some (update_once_zero intv q tsq inf rel2 discard)
    )

  | EOnce (intv,f2,inf) ->
    (match eval f2 crt false with
     | None -> None
     | Some rel2 ->
       if Misc.debugging Dbg_eval then
         Printf.printf "[eval,Once] q=%d\n" q;

       if not (Relation.is_empty rel2) then
         dllist_add_last inf.oauxrels tsq rel2;

       Some (update_once intv tsq inf discard)
    )

  | EUntil (comp,intv,f1,f2,inf) ->
    (* contents of inf:  (f = f1 UNTIL_intv f2)
       ulast:        last cell of neval for which both f1 and f2 are evaluated
       ufirst:       boolean flag indicating if we are at the first
                     iteration after the evaluation of f (i.e. q was
                     just moved); in this case we remove auxiliary
                     relations at old q
       ures:         the current partial result (for f)
       urel2:        the evaluation of f2 at ulast
       raux, saux:   the auxiliary relations
    *)

    if Misc.debugging Dbg_eval then
      begin
        let str = Printf.sprintf "[eval,Until] q=%d inf: " q in
        print_uinf str inf
      end;

    if inf.ufirst then
      begin
        inf.ufirst <- false;
        let (i,_) = Neval.get_data inf.ulast in
        update_old_until q tsq i intv inf discard;
        if Misc.debugging Dbg_eval then
          print_uinf "[eval,Until,after_update] inf: " inf
      end;

    (* we first evaluate f2, and then f1 *)

    let rec evalf1 i tsi rel2 ncrt =
      (match eval f1 ncrt false with
       | Some rel1 ->
         update_until q tsq i tsi intv rel1 rel2 inf comp discard;
         inf.urel2 <- None;
         inf.ulast <- ncrt;
         evalf2 ()
       | None ->
         inf.urel2 <- (Some rel2);
         None
      )

    and evalf2 () =
      if Neval.is_last inf.ulast then
        None
      else
        let ncrt = Neval.get_next inf.ulast in
        let (i,tsi) = Neval.get_data ncrt in
        if not (MFOTL.in_left_ext (MFOTL.ts_minus tsi tsq) intv) then
          (* we have the lookahead, we can compute the result *)
          begin
            if Misc.debugging Dbg_eval then
              Printf.printf "[eval,Until] evaluation possible q=%d tsq=%s\n"
                q (MFOTL.string_of_ts tsq);
            let res = inf.ures in
            inf.ures <- Relation.empty;
            inf.ufirst <- true;
            Some res
          end
        else
          begin
            (match inf.urel2 with
             | Some rel2 -> evalf1 i tsi rel2 ncrt
             | None ->
               (match eval f2 ncrt false with
                | None -> None
                | Some rel2 -> evalf1 i tsi rel2 ncrt
               )
            )
          end
    in
    evalf2()

  | ENUntil (comp,intv,f1,f2,inf) ->
    (* contents of inf:  (f = NOT f1 UNTIL_intv f2)
       ulast1:       last cell of neval for which f1 is evaluated
       ulast2:       last cell of neval for which f2 is evaluated
       listrel1:     list of evaluated relations for f1
       listrel2:     list of evaluated relations for f2

       NOTE: a possible optimization would be to not store empty relations
    *)

    (* evaluates the subformula f as much as possible *)
    let rec eval_subf f list last  =
      if Neval.is_last last then
        last
      else
        let ncrt = Neval.get_next last in
        match eval f ncrt false with
        | None -> last
        | Some rel ->
          (* store the result and try the next time point *)
          let i, tsi = Neval.get_data ncrt in
          Dllist.add_last (i, tsi, rel) list;
          eval_subf f list ncrt
    in

    (* evaluate the two subformulas *)
    inf.last1 <- eval_subf f1 inf.listrel1 inf.last1;
    inf.last2 <- eval_subf f2 inf.listrel2 inf.last2;

    (* checks whether the position to be evaluated is beyond the interval *)
    let has_lookahead last =
      let ncrt =
        if Neval.is_last last then
          last
        else
          Neval.get_next last
      in
      let _, tsi = Neval.get_data ncrt in
      not (MFOTL.in_left_ext (MFOTL.ts_minus tsi tsq) intv)
    in

    if has_lookahead inf.last1 && has_lookahead inf.last2 then
      (* we have the lookahead for both f1 and f2 (to be consistent with Until),
        we can compute the result

        NOTE: we could evaluate earlier with respect to f1, also in Until *)
      begin
        (* we iteratively compute the union of the relations [f1]_j
          with q <= j <= j0-1, where j0 is the first index which
          satisfies the temporal constraint relative to q *)
        let f1union = ref Relation.empty in
        let crt1_j = ref (Dllist.get_first_cell inf.listrel1) in
        let rec iter1 () =
          let j,tsj,relj = Dllist.get_data !crt1_j in
          if j < q then
            begin (* clean up from previous evaluation *)
              assert (j = q-1);
              ignore(Dllist.pop_first inf.listrel1);
              crt1_j := Dllist.get_next inf.listrel1 !crt1_j;
              iter1 ()
            end
          else if not (MFOTL.in_right_ext (MFOTL.ts_minus tsj tsq) intv) then
            begin
              f1union := Relation.union !f1union relj;
              if not (Dllist.is_last inf.listrel1 !crt1_j) then
                begin
                  crt1_j := Dllist.get_next inf.listrel1 !crt1_j;
                  iter1 ()
                end
            end
        in
        iter1 ();

        (* we now iterate through the remaining indexes, updating the
          union, and also computing the result *)
        let res = ref Relation.empty in
        let crt2_j = ref (Dllist.get_first_cell inf.listrel2) in
        let rec iter2 () =
          let j2,tsj2,rel2 = Dllist.get_data !crt2_j in
          if j2 < q || not (MFOTL.in_right_ext (MFOTL.ts_minus tsj2 tsq) intv) then
            begin (* clean up from previous evaluation *)
              ignore(Dllist.pop_first inf.listrel2);
              if not (Dllist.is_last inf.listrel2 !crt2_j) then
                begin
                  crt2_j := Dllist.get_next inf.listrel2 !crt2_j;
                  iter2 ()
                end
            end
          else
            begin
              let j1,tsj1,rel1 = Dllist.get_data !crt1_j in
              assert(j1 = j2);
              if MFOTL.in_left_ext (MFOTL.ts_minus tsj2 tsq) intv then
                begin
                  let resj = comp rel2 !f1union in
                  res := Relation.union !res resj;
                  f1union := Relation.union !f1union rel1;
                  let is_last1 = Dllist.is_last inf.listrel1 !crt1_j in
                  let is_last2 = Dllist.is_last inf.listrel2 !crt2_j in
                  if (not is_last1) && (not is_last2) then
                    begin
                      crt1_j := Dllist.get_next inf.listrel1 !crt1_j;
                      crt2_j := Dllist.get_next inf.listrel2 !crt2_j;
                      iter2 ()
                    end
                end
            end
        in
        iter2();
        Some !res
      end
    else
      None





  | EEventuallyZ (intv,f2,inf) ->
    (* contents of inf:
       elastev: Neval.cell  last cell of neval for which f2 is evaluated
       eauxrels: info       the auxiliary relations (up to elastev)
    *)
    if Misc.debugging Dbg_eval then
      print_ezinf "[eval,EventuallyZ] inf: " inf;

    let rec ez_update () =
      if Neval.is_last inf.ezlastev then
        None
      else
        let ncrt = Neval.get_next inf.ezlastev in
        let (i,tsi) = Neval.get_data ncrt in
        (* Printf.printf "[eval,Eventually] e_update: ncrt.i = %d\n%!" i; *)
        if not (MFOTL.in_left_ext (MFOTL.ts_minus tsi tsq) intv) then
          (* we have the lookahead, we can compute the result *)
          begin
            if Misc.debugging Dbg_eval then
              Printf.printf "[eval,EventuallyZ] evaluation possible q=%d tsq=%s tsi=%s\n%!"
                q (MFOTL.string_of_ts tsq) (MFOTL.string_of_ts tsi);

            let auxrels = inf.ezauxrels in
            if Dllist.is_empty auxrels then
              Some Relation.empty
            else if discard then
              begin
                let lw, _, _ = Dllist.get_first auxrels in
                if lw = q then (* at next iteration this first element will be too old *)
                  begin
                    if inf.ezlast != Dllist.void && inf.ezlast == Dllist.get_first_cell auxrels then
                      inf.ezlast <- Dllist.void;
                    ignore(Dllist.pop_first auxrels);
                  end;
                Some Relation.empty
              end
            else
              begin
                if inf.ezlast != Dllist.void && inf.ezlast == Dllist.get_first_cell auxrels then
                  (* TODO: when can such a case occur? *)
                  inf.ezlast <- Dllist.void;

                let lw, _, _ = Dllist.get_first auxrels in
                assert (lw >= q); (* TODO: when lw > q *)
                let cond = fun (_,tsj,_) -> MFOTL.in_left_ext (MFOTL.ts_minus tsj tsq) intv in
                let f = fun (j,_,rel) -> (j,rel) in
                let subseq, new_last = get_new_elements auxrels inf.ezlast cond f in
                let rw =
                  if subseq = [] then
                    (* TODO: why j? when does this case occur? *)
                    let j, _, _  = Dllist.get_data inf.ezlast in j
                  else
                    begin
                      assert (new_last != Dllist.void);
                      inf.ezlast <- new_last;
                      let rw = fst (List.hd subseq) in
                      assert (rw = let j, _, _ = Dllist.get_data new_last in j);
                      rw
                    end
                in

                if Misc.debugging Dbg_eval then
                  begin
                    Printf.printf "[eval,EventuallyZ] lw = %d rw = %d " lw rw;
                    Misc.printnl_list "subseq = " print_auxel subseq;
                  end;

                let newt = Sliding.slide string_of_int Relation.union subseq (lw, rw) inf.eztree in

                if lw = q then (* at next iteration this first element will be too old *)
                  begin
                    if new_last == Dllist.get_first_cell auxrels then
                      inf.ezlast <- Dllist.void;
                    ignore(Dllist.pop_first auxrels);
                  end;

                inf.eztree <- newt;
                Some (Sliding.stree_res newt)
              end
          end
        else (* we don't have the lookahead -> we cannot compute the result *)
          begin
            match eval f2 ncrt false with
            | None -> None
            | Some rel2 ->
              (* we update the auxiliary relations *)
              if not (Relation.is_empty rel2) then
                Dllist.add_last (i,tsi,rel2) inf.ezauxrels;
              inf.ezlastev <- ncrt;
              ez_update ()
          end
    in
    ez_update ()


  | EEventually (intv,f2,inf) ->
    (* contents of inf:
       elastev:  Neval.cell  last cell of neval for which f2 is evaluated
       eauxrels: info        the auxiliary relations (up to elastev)
    *)
    if Misc.debugging Dbg_eval then
      print_einfn "[eval,Eventually] inf: " inf;

    (* we could in principle do this update less often: that is, we
       can do after each evaluation, but we need to find out the
       value of ts_{q+1} *)
    elim_old_eventually q tsq intv inf;

    let rec e_update () =
      if Neval.is_last inf.elastev then
        None
      else
        let ncrt = Neval.get_next inf.elastev in
        let (i,tsi) = Neval.get_data ncrt in
        (* Printf.printf "[eval,Eventually] e_update: ncrt.i = %d\n%!" i; *)
        if not (MFOTL.in_left_ext (MFOTL.ts_minus tsi tsq) intv) then
          (* we have the lookahead, we can compute the result *)
          begin
            if Misc.debugging Dbg_eval then
              Printf.printf "[eval,Eventually] evaluation possible q=%d tsq=%s tsi=%s\n%!"
                q (MFOTL.string_of_ts tsq) (MFOTL.string_of_ts tsi);

            let auxrels = inf.eauxrels in
            if Dllist.is_empty auxrels || discard then
              Some Relation.empty
            else
              let lw, _ = Dllist.get_first auxrels in
              if MFOTL.in_left_ext (MFOTL.ts_minus lw tsq) intv then
                (* the new window is not empty *)
                let cond = fun (tsj,_) -> MFOTL.in_left_ext (MFOTL.ts_minus tsj tsq) intv in
                let subseq, new_last = get_new_elements auxrels inf.elast cond (fun x -> x) in
                let rw =
                  if subseq = [] then
                    fst (Dllist.get_data inf.elast)
                  else
                    begin
                      assert (new_last != Dllist.void);
                      inf.elast <- new_last;
                      let rw = fst (List.hd subseq) in
                      assert (rw = fst (Dllist.get_data new_last));
                      rw
                    end
                in
                if Misc.debugging Dbg_eval then
                  begin
                    Printf.printf "[eval,Eventually] lw = %s rw = %s "
                      (MFOTL.string_of_ts lw)
                      (MFOTL.string_of_ts rw);
                    Misc.printnl_list "subseq = " print_sauxel subseq;
                  end;
                let newt = Sliding.slide MFOTL.string_of_ts Relation.union subseq (lw, rw) inf.etree in
                inf.etree <- newt;
                Some (Sliding.stree_res newt)
              else
                begin
                  (* the new window is empty,
                     because not even the oldest element satisfies the constraint *)
                  inf.etree <- LNode {l = MFOTL.ts_invalid;
                                      r = MFOTL.ts_invalid;
                                      res = Some (Relation.empty)};
                  inf.elast <- Dllist.void;
                  Some Relation.empty
                end
          end
        else
          begin
            match eval f2 ncrt false with
            | None -> None
            | Some rel2 ->
              (* we update the auxiliary relations *)
              if (MFOTL.in_right_ext (MFOTL.ts_minus tsi tsq) intv) &&
                 not (Relation.is_empty rel2) then
                dllist_add_last inf.eauxrels tsi rel2;
              inf.elastev <- ncrt;
              e_update ()
          end
    in
    e_update ()

let add_index f i tsi db =
  let rec update lets = function
    | EPred (p, comp, inf) ->
      if List.mem (Predicate.get_name p) lets
      then ()
      else
        let rel =
          (try
             let t = Db.get_table db p in
             Table.get_relation t
           with Not_found ->
           match Predicate.get_name p with
           | "tp" -> Relation.singleton (Tuple.make_tuple [Int i])
           | "ts" -> Relation.singleton (Tuple.make_tuple [Float tsi])
           | "tpts" ->
             Relation.singleton (Tuple.make_tuple [Int i; Float tsi])
           | _ -> Relation.empty
          )
        in
        let rel = comp rel in
        Queue.add (i,tsi,rel) inf

    | ELet (p, comp, f1, f2, inf) ->
      update lets f1;
      update (Predicate.get_name p :: lets) f2

    | ERel _ -> ()

    | ENeg f1
    | EExists (_,f1)
    | EAggOnce (_,_,f1)
    | EAggreg (_,_,f1)
    | ENext (_,f1,_)
    | EPrev (_,f1,_)
    | EOnceA (_,f1,_)
    | EOnceZ (_,f1,_)
    | EOnce (_,f1,_)
    | EEventuallyZ (_,f1,_)
    | EEventually (_,f1,_) ->
      update lets f1

    | EAnd (_,f1,f2,_)
    | EOr (_,f1,f2,_)
    | ESinceA (_,_,f1,f2,_)
    | ESince (_,_,f1,f2,_)
    | ENUntil (_,_,f1,f2,_)
    | EUntil (_,_,f1,f2,_) ->
      update lets f1;
      update lets f2
  in
  update [] f

let process_index ff posl last i =
  if !Misc.verbose then
    Printf.printf "At time point %d:\n%!" i;

  let rec eval_loop () =
    let crt = Neval.get_next !last in
    let (q, tsq) = Neval.get_data crt in
    if tsq < MFOTL.ts_max then
      match eval ff crt false with
      | Some rel ->
        show_results posl i q tsq rel;
        last := crt;
        if !Misc.stop_at_first_viol && not (Relation.is_empty rel) then false
        else if Neval.is_last crt then true
        else eval_loop ()
      | None -> true
    else false
  in
  eval_loop ()

let add_ext neval f =
  let neval0 = Neval.get_last neval in
  let rec add_ext = function
  | Pred p ->
    EPred (p, Relation.eval_pred p, Queue.create())

  | Let (p, f1, f2) ->
    let attr1 = MFOTL.free_vars f1 in
    let attrp = Predicate.pvars p in
    let new_pos = List.map snd (Table.get_matches attr1 attrp) in
    let comp = Relation.reorder new_pos in
    ELet (p, comp, add_ext f1, add_ext f2, {llast = neval0})

  | Equal (t1, t2) ->
    let rel = Relation.eval_equal t1 t2 in
    ERel rel

  | Neg (Equal (t1, t2)) ->
    let rel = Relation.eval_not_equal t1 t2 in
    ERel rel

  | Neg f -> ENeg (add_ext f)

  | Exists (vl, f1) ->
    let ff1 = add_ext f1 in
    let attr1 = MFOTL.free_vars f1 in
    let pos = List.map (fun v -> Misc.get_pos v attr1) vl in
    let pos = List.sort Stdlib.compare pos in
    let comp = Relation.project_away pos in
    EExists (comp,ff1)

  | Or (f1, f2) ->
    let ff1 = add_ext f1 in
    let ff2 = add_ext f2 in
    let attr1 = MFOTL.free_vars f1 in
    let attr2 = MFOTL.free_vars f2 in
    let comp =
      if attr1 = attr2 then
        Relation.union
      else
        let matches = Table.get_matches attr2 attr1 in
        let new_pos = List.map snd matches in
        (* first reorder rel2 *)
        (fun rel1 rel2 ->
           let rel2' = Relation.reorder new_pos rel2 in
           Relation.union rel1 rel2'
        )
    in
    EOr (comp, ff1, ff2, {arel = None})

  | And (f1, f2) ->
    let attr1 = MFOTL.free_vars f1 in
    let attr2 = MFOTL.free_vars f2 in
    let ff1 = add_ext f1 in
    let f2_is_special = Rewriting.is_special_case attr1 attr2 f2 in
    let ff2 =
      if f2_is_special then ERel Relation.empty
      else match f2 with
        | Neg f2' -> add_ext f2'
        | _ -> add_ext f2
    in
    let comp =
      if f2_is_special then
        if Misc.subset attr2 attr1 then
          let filter_cond = Tuple.get_filter attr1 f2 in
          fun rel1 _ -> Relation.filter filter_cond rel1
        else
          let process_tuple = Tuple.get_tf attr1 f2 in
          fun rel1 _ ->
            Relation.fold
              (fun t res -> Relation.add (process_tuple t) res)
              rel1 Relation.empty
      else
        match f2 with
        | Neg _ ->
          if attr1 = attr2 then
            fun rel1 rel2 -> Relation.diff rel1 rel2
          else
            begin
              assert(Misc.subset attr2 attr1);
              let posl = List.map (fun v -> Misc.get_pos v attr1) attr2 in
              fun rel1 rel2 -> Relation.minus posl rel1 rel2
            end

        | _ ->
          let matches1 = Table.get_matches attr1 attr2 in
          let matches2 = Table.get_matches attr2 attr1 in
          if attr1 = attr2 then
            fun rel1 rel2 -> Relation.inter rel1 rel2
          else if Misc.subset attr1 attr2 then
            fun rel1 rel2 -> Relation.natural_join_sc1 matches2 rel1 rel2
          else if Misc.subset attr2 attr1 then
            fun rel1 rel2 -> Relation.natural_join_sc2 matches1 rel1 rel2
          else
            fun rel1 rel2 -> Relation.natural_join matches1 matches2 rel1 rel2
    in
    EAnd (comp, ff1, ff2, {arel = None})

  | Aggreg (t_y, y, op, x, glist, Once (intv, f)) ->
    let t_y = match t_y with TCst a -> a | _ -> failwith "Internal error" in
    let default = MFOTL.aggreg_default_value op t_y in
    let attr = MFOTL.free_vars f in
    let posx = Misc.get_pos x attr in
    let posG = List.map (fun z -> Misc.get_pos z attr) glist in
    let state =
      match op with
      | Cnt -> Aggreg.cnt_once default intv 0 posG
      | Min -> Aggreg.min_once default intv 0 posx posG
      | Max -> Aggreg.max_once default intv 0 posx posG
      | Sum -> Aggreg.sum_once default intv 0 posx posG
      | Avg -> Aggreg.avg_once default intv 0 posx posG
      | Med -> Aggreg.med_once default intv 0 posx posG
    in
    EAggOnce ({op; default}, state, add_ext f)

  | Aggreg (t_y, y, op, x, glist, f)  ->
    let t_y = match t_y with TCst a -> a | _ -> failwith "Internal error" in
    let default = MFOTL.aggreg_default_value op t_y in
    let attr = MFOTL.free_vars f in
    let posx = Misc.get_pos x attr in
    let posG = List.map (fun z -> Misc.get_pos z attr) glist in
    let comp =
      match op with
      | Cnt -> Aggreg.cnt default 0 posG
      | Sum -> Aggreg.sum default 0 posx posG
      | Min -> Aggreg.min default 0 posx posG
      | Max -> Aggreg.max default 0 posx posG
      | Avg -> Aggreg.avg default 0 posx posG
      | Med -> Aggreg.med default 0 posx posG
    in
    EAggreg ({op; default}, comp, add_ext f)

  | Prev (intv, f) ->
    let ff = add_ext f in
    EPrev (intv, ff, {plast = neval0})

  | Next (intv, f) ->
    let ff = add_ext f in
    ENext (intv, ff, {init = true})

  | Since (intv,f1,f2) ->
    let attr1 = MFOTL.free_vars f1 in
    let attr2 = MFOTL.free_vars f2 in
    let ef1, neg =
      (match f1 with
       | Neg f1' -> f1',true
       | _ -> f1,false
      )
    in
    let comp =
      if neg then
        let posl = List.map (fun v -> Misc.get_pos v attr2) attr1 in
        assert(Misc.subset attr1 attr2);
        fun relj rel1 -> Relation.minus posl relj rel1
      else
        let matches2 = Table.get_matches attr2 attr1 in
        fun relj rel1 -> Relation.natural_join_sc2 matches2 relj rel1
    in
    let ff1 = add_ext ef1 in
    let ff2 = add_ext f2 in
    if snd intv = Inf then
      let inf = {sres = Relation.empty; sarel2 = None; saauxrels = Mqueue.create()} in
      ESinceA (comp,intv,ff1,ff2,inf)
    else
      let inf = {srel2 = None; sauxrels = Mqueue.create()} in
      ESince (comp,intv,ff1,ff2,inf)

  | Once ((_, Inf) as intv, f) ->
    let ff = add_ext f in
    EOnceA (intv,ff,{ores = Relation.empty;
                     oaauxrels = Mqueue.create()})

  | Once (intv,f) ->
    let ff = add_ext f in
    if fst intv = CBnd MFOTL.ts_null then
      EOnceZ (intv,ff,{oztree = LNode {l = -1;
                                       r = -1;
                                       res = Some (Relation.empty)};
                       ozlast = Dllist.void;
                       ozauxrels = Dllist.empty()})
    else
      EOnce (intv,ff,{otree = LNode {l = MFOTL.ts_invalid;
                                     r = MFOTL.ts_invalid;
                                     res = Some (Relation.empty)};
                      olast = Dllist.void;
                      oauxrels = Dllist.empty()})

  | Until (intv,f1,f2) ->
    let attr1 = MFOTL.free_vars f1 in
    let attr2 = MFOTL.free_vars f2 in
    let ef1, neg =
      (match f1 with
       | Neg f1' -> f1',true
       | _ -> f1,false
      )
    in
    let ff1 = add_ext ef1 in
    let ff2 = add_ext f2 in
    if neg then
      let comp =
        let posl = List.map (fun v -> Misc.get_pos v attr2) attr1 in
        assert(Misc.subset attr1 attr2);
        fun relj rel1 -> Relation.minus posl relj rel1
      in
      let inf = {
        last1 = neval0;
        last2 = neval0;
        listrel1 = Dllist.empty();
        listrel2 = Dllist.empty()}
      in
      ENUntil (comp,intv,ff1,ff2,inf)
    else
      let comp =
        let matches2 = Table.get_matches attr2 attr1 in
        fun relj rel1 -> Relation.natural_join_sc2 matches2 relj rel1
      in
      let inf = {ulast = neval0;
                 ufirst = false;
                 ures = Relation.empty;
                 urel2 = None;
                 raux = Sj.empty();
                 saux = Sk.empty()}
      in
      EUntil (comp,intv,ff1,ff2,inf)


  | Eventually (intv,f) ->
    let ff = add_ext f in
    if fst intv = CBnd MFOTL.ts_null then
      EEventuallyZ (intv,ff,{eztree = LNode {l = -1;
                                             r = -1;
                                             res = Some (Relation.empty)};
                             ezlast = Dllist.void;
                             ezlastev = neval0;
                             ezauxrels = Dllist.empty()})
    else
      EEventually (intv,ff,{etree = LNode {l = MFOTL.ts_invalid;
                                           r = MFOTL.ts_invalid;
                                           res = Some (Relation.empty)};
                            elast = Dllist.void;
                            elastev = neval0;
                            eauxrels = Dllist.empty()})

  | _ -> failwith "[add_ext] internal error"
  in
  add_ext f, ref neval0

(*
  STATE MANAGEMENT CALLS
  - (Un-)Marshalling, Splitting, Merging
 *)

let split_state_msg = "Split state"
let saved_state_msg = "Saved state"
let slicing_parameters_updated_msg = "Slicing parameters updated"
let restored_state_msg = "Loaded state"
let combined_state_msg = "Loaded state"
let get_index_prefix_msg = "Current timepoint:"

 (*
  Helper function used in "marshal" and "split_and_save" functions.
  Saves state to specified dumpfile
 *)
let dump_to_file dumpfile value =
  let ch = open_out_bin dumpfile in
  Marshal.to_channel ch value [Marshal.Closures];
  close_out ch

(*
  Helper function used in "unmarshal" and "merge_formulas" functions.
  Reads state from specified dumpfile and converts neval array to dllist
*)
let read_m_from_file file =
  let ch = open_in_bin file in
  let value = (Marshal.from_channel ch : state) in
  close_in ch;
  value


(* Converts extformula to mformula form used for storage. Saves formula + state in specified dumpfile. *)
let marshal dumpfile ff posl neval lastev =
  let mf = Marshalling.ext_to_m ff in
  let value : state = (!Log.last_ts,posl,mf,neval,!lastev,!Log.tp,!Log.last) in
  (*Printf.printf "Log TP to restore: %d \n" !Log.tp;*)
  dump_to_file dumpfile value

(*
  Reads mformula + state from specified dumpfile and restores it to extformula form with full state
  information using m_to_ext function.
*)
let unmarshal resumefile =
  let (last_ts,posl,mf,neval,lastev,tp,last) = read_m_from_file resumefile in
  let ff = Marshalling.m_to_ext mf in
  (last_ts,posl,ff,neval,ref lastev,tp,last)


let create_empty_db =
  Db.make_db []

let add_empty_db ff neval =
  crt_tp := !Log.tp -1;
  lastts := !Log.last_ts;
  ignore (Neval.append (!crt_tp, !lastts) neval);
  add_index ff !crt_tp !lastts create_empty_db

let catch_up_on_filtered_tp posl i ff neval last =
  let rec eval_loop () =
    let crt = Neval.get_next !last in
    match eval ff crt false with
    | Some rel ->
      let (q, tsq) = Neval.get_data crt in
      show_results posl i q tsq rel;
      last := crt;
      if Neval.is_last crt then () else eval_loop ()
    | None -> ()
  in
  (*print_extf "Before catching up \n" ff;*)
  if (!crt_tp < (!Log.tp-1) && (!Log.tp) > 0) then begin
    add_empty_db ff neval;
    eval_loop ()
  end
  (*print_extf "After catching up \n" ff*)

let split_save filename ff posl i neval last =
  let heavy_unproc = !slicer_heavy_unproc in
  let shares = !slicer_shares in
  let seeds = !slicer_seeds in

  catch_up_on_filtered_tp posl i ff neval last;

  let mf = Marshalling.ext_to_m ff in
  let heavy = Hypercube_slicer.convert_heavy mf heavy_unproc in
  let slicer = Hypercube_slicer.create_slicer mf heavy shares seeds in
  let result = Splitting.split_with_slicer (Hypercube_slicer.add_slices_of_valuation slicer) slicer.degree mf in

  let format_filename index =
    Printf.sprintf "%s-%d.bin" filename index
  in

  Array.iteri (fun index mf ->
    let value : state = (!Log.last_ts,posl,mf,neval,!last,!Log.tp,!Log.last) in
    dump_to_file (format_filename index) value
  ) result;
  Printf.printf "%s\n%!" saved_state_msg
  (*Printf.printf "%s to file with substr: %s \n%!" saved_state_msg filename*)

(*
   Split formula according to split constraints (sconsts). Resulting splits will be stored to files
   with names of index prepended with dumpfile variable.
*)
let split_and_save  sconsts dumpfile posl i ff neval last =
  catch_up_on_filtered_tp posl i ff neval last;
  let mf = Marshalling.ext_to_m ff in
  let result = Splitting.split_formula sconsts mf in

  Array.iteri (fun index mf ->
  let value : state = (!Log.last_ts,posl,mf,neval,!last,!Log.tp,!Log.last) in
  dump_to_file (dumpfile ^ (string_of_int index)) value) result;
  Printf.printf "%s\n%!" saved_state_msg

(* Convert comma separated filenames to list of strings *)
let files_to_list f =
  String.split_on_char ',' f

(*
  Merge states contained in list of dumpfiles. Assumption is made that formulas are identical and
  only states differ.
  In the fold operation, always two mformulas are combined using recursion, with one being formula
  being the accumulator which is initialized as the first element of the list. The rest of the list
  is then folded over.
 *)
let merge_formulas files =
  if List.length files == 1 then unmarshal (List.hd files)
  else
    let (last_ts, posl, mf, neval, lastev, tp, last) =
      List.fold_right (fun s (last_ts1,posl,mf1,neval,lastev,tp1,last) ->
        let (last_ts,_,mf2,_,_,tp,_) = read_m_from_file s in

        if (MFOTL.ts_minus last_ts1 last_ts) = 0. then failwith "[merge_formulas] last_ts mismatch";
        if tp1 <> tp then failwith "[merge_formulas] tp mismatch";

        let comb_mf = Splitting.comb_m lastev mf1 mf2 in
        (last_ts,posl, comb_mf, neval, lastev, tp,last)
      ) (List.tl files) (read_m_from_file (List.hd files))
    in
    let ff = Marshalling.m_to_ext mf in
    (last_ts, posl, ff, neval, ref lastev, tp, last)

(* MONITORING FUNCTION *)

(* Checks if the parameter for the exit command is set *)
let checkExitParam p = match p with
  | Argument str ->
    dumpfile := str;
    true
  | _ -> false

(* Checks if the parameters for the split command are set *)
let checkSplitParam p = match p with
  | SplitParameters sp ->
    dumpfile := "partition-";
    true
  | _ -> false

(* The arguments are:
   lexbuf - the lexer buffer (holds current state of the scanner)
   ff - the extended MFOTL formula
   posl - permutation of free variable positions, for output
   neval - the queue of no-yet evaluted indexes/entries
   i - the index of current entry in the log file
   ([i] may be different from the current time point when
   filter_empty_tp is enabled)
*)

let set_slicer_parameters c p =
  match p with
  | SplitSave sp ->
    let heavy, shares, seeds = sp in
    slicer_heavy_unproc := heavy;
    slicer_shares := shares;
    slicer_seeds := seeds;
    Printf.printf "%s\n%!" slicing_parameters_updated_msg
  | _ ->  Printf.printf "%s: Wrong parameters specified, continuing at timepoint %d\n%!" c !tp

let rec check_log lexbuf ff posl neval i last =
  let finish () =
    if Misc.debugging Dbg_perf then
      Perf.check_log_end i !lastts
  in
  let rec loop ffl i =
    if Misc.debugging Dbg_perf then
      Perf.check_log i !lastts;

    let get_constraints_split_state p = match p with
      (* Other case already handled by check split param *)
      | SplitParameters sp -> sp
      | _ -> raise (Type_error ("Unsupported parameter to get_constraints"))
    in
    match Log.get_next_entry lexbuf with
    | MonpolyCommand {c; parameters} ->
        let process_command = function
            | "print" ->
               print_extf "Current extended formula:\n" ff;
               print_newline ();
               loop ffl i
            | "terminate" ->
               Printf.printf "Terminated at timepoint: %d \n%!" !tp
            | "print_and_exit" ->
               print_extf "Current extended formula:\n" ff;
               print_newline ();
               Printf.printf "Terminated at timepoint: %d \n%!" !tp
            | "get_pos"   ->
               Printf.printf "Current timepoint: %d \n%!" !tp;
               loop ffl i
            | "save_state" ->
              (match parameters with
              | Some (Argument filename) ->
                catch_up_on_filtered_tp posl !crt_tp ff neval last;
                marshal filename ff posl neval last;
                Printf.printf "%s\n%!" saved_state_msg;
                loop ffl i
              | None ->
                Printf.printf "%s: No filename specified\n%!" c;
                loop ffl i
              | _ ->
                print_endline "Unsupported parameters to save_state";
                loop ffl i
              )
            | "set_slicer" ->
              (match parameters with
              | Some p -> set_slicer_parameters c p
              | None -> Printf.printf "%s: No parameters specified, continuing at timepoint %d\n%!" c !tp
              );
              loop ffl i
            | "split_save" ->
              (match parameters with
              | Some p ->
                if checkExitParam p then begin
                  split_save !dumpfile ff posl !crt_tp neval last;
                  loop ffl i
                end else begin
                  Printf.printf "%s: Invalid parameters supplied, continuing with index %d\n%!" c i;
                  loop ffl i
                end
              | None ->
                Printf.printf "%s: No parameters specified, continuing at timepoint %d\n%!" c !tp;
                loop ffl i
              )
            | "save_and_exit" ->
              (match parameters with
              | Some p ->
                if checkExitParam p then begin
                  catch_up_on_filtered_tp posl !crt_tp ff neval last;
                  marshal !dumpfile ff posl neval last;
                  Printf.printf "%s\n%!" saved_state_msg
                end
                else Printf.printf "%s: Invalid parameters supplied at index %d\n%!" c i
              | None -> Printf.printf "%s: No filename specified at timepoint %d\n%!" c !tp
              )
            | "split_state" ->
              (match parameters with
              | Some p ->
                if checkSplitParam p then
                  split_and_save (get_constraints_split_state p)
                    !dumpfile posl !crt_tp ff neval last
                else
                  Printf.printf "%s: Invalid parameters supplied at index %d\n%!" c i
              | None -> Printf.printf "%s: No parameters specified at timepoint %d\n%!" c !tp
              )
            | _ ->
                Printf.printf "UNRECOGNIZED COMMAND: %s\n%!" c;
                loop ffl i
        in
        process_command c;
    | MonpolyData {tp; ts; db} ->
      if ts >= !lastts then
        begin
          crt_tp := tp;
          crt_ts := ts;
          add_index ff tp ts db;
          ignore (Neval.append (tp, ts) neval);
          let cont = process_index ff posl last tp in
          lastts := ts;
          if cont then
            loop ffl (i + 1)
          else
            finish ()
        end
      else
      if !Misc.stop_at_out_of_order_ts then
        let msg = Printf.sprintf "[Algorithm.check_log] Error: OUT OF ORDER TIMESTAMP: %s \
                                  (last_ts: %s)" (MFOTL.string_of_ts ts) (MFOTL.string_of_ts !lastts) in
        failwith msg
      else
        begin
          Printf.eprintf "[Algorithm.check_log] skipping OUT OF ORDER TIMESTAMP: %s \
                          (last_ts: %s)\n%!"
            (MFOTL.string_of_ts ts) (MFOTL.string_of_ts !lastts);
          loop ffl i
        end
    | MonpolyTestTuple st -> finish ()
    | MonpolyError s -> finish ()
  in
  loop ff i


let monitor_lexbuf lexbuf fv f =
  (* compute permutation for output tuples *)
  let fv_pos = List.map snd (Table.get_matches (MFOTL.free_vars f) fv) in
  assert (List.length fv_pos = List.length fv);
  let neval = Neval.create () in
  let extf, last = add_ext neval f in
  check_log lexbuf extf fv_pos neval 0 last

let monitor_string log fv f =
  (let lexbuf = Lexing.from_string log in
   lastts := MFOTL.ts_invalid;
   crt_tp := -1;
   crt_ts := MFOTL.ts_invalid;
   Log.tp := 0;
   Log.skipped_tps := 0;
   Log.last := false;
   monitor_lexbuf lexbuf fv f;
   Lexing.flush_input lexbuf;)

let monitor logfile =
  let lexbuf = Log.log_open logfile in
  monitor_lexbuf lexbuf


let test_filter logfile f =
  let lexbuf = Log.log_open logfile in
  let rec loop f i =
    match Log.get_next_entry lexbuf with
    | MonpolyData {tp;ts;db;} ->
      loop f tp
    | MonpolyError s ->
      Printf.printf "%s, processed %d time points\n" s (i - 1)
    | MonpolyCommand {c} ->
          let process_command c = match c with
              | "terminate" ->
                Printf.printf "Command: %s, processed %d time points\n" c (i - 1)
              | "get_pos"   ->
                Printf.printf "%s %d \n" get_index_prefix_msg !tp;
                loop f i
              | _ ->
                Printf.printf "UNREGONIZED COMMAND: %s\n" c;
                loop f i
          in
          process_command c;
      | _ ->
        Printf.printf "%s, processed %d time points\n" "Unrecognized type" (i - 1)
  in
  loop f 0

(* Unmarshals formula & state from resume file and then starts processing logfile.
   Note: The whole logfile is read from the start, with old timestamps being skipped  *)
let resume logfile =
  let (last_ts,posl,ff,neval,lastev,tp,last) = unmarshal !resumefile in

  (*print_neval "Neval \n" neval;
  print_extf "State \n" ff;*)
  lastts := last_ts;
  Log.tp := tp;
  Log.skipped_tps := 0;
  Log.last := last;
  let lexbuf = Log.log_open logfile in
  Printf.printf "%s\n%!" restored_state_msg;
  check_log lexbuf ff posl neval 0 lastev

(* Combines states from files which are marshalled from an identical extformula. Same as resume
   the log file then processed from the beginning *)
let combine logfile =
  let files = files_to_list !combine_files in
  let (last_ts,posl,ff,neval,lastev,tp,last) = merge_formulas files in

  (*print_neval "Combined neval \n" neval;
  print_extf "Combined formula \n" ff;*)

  lastts := last_ts;
  Log.tp := tp;
  Log.skipped_tps := 0;
  Log.last := last;

  let lexbuf = Log.log_open logfile in
  Printf.printf "%s\n%!" combined_state_msg;
  check_log lexbuf ff posl neval 0 lastev


(* Testing slicer *)
let test_tuple_split slicer size tuple dest =
  let parts = slicer tuple in
  Array.iter2 (fun i1 i2 ->
   Printf.printf "%d, %d\n" i1 i2;
     if i1 <> i2 then failwith "Mismatch between slicing result and groundtruth"
   ) parts dest

let test_slicer ff evaluation  =
  let heavy_unproc = !slicer_heavy_unproc in
  let shares = !slicer_shares in
  let seeds = !slicer_seeds in

  let mf = Marshalling.ext_to_m ff in
  let heavy = Hypercube_slicer.convert_heavy mf heavy_unproc in
  let slicer = Hypercube_slicer.create_slicer mf heavy shares seeds in

  let rec test_entries i =
    if Dllist.is_empty evaluation <> true then
      let elem = Dllist.pop_first evaluation in
      let tuple = convert_slicing_tuple slicer elem.vars elem.tuple in
      let () = test_tuple_split (Hypercube_slicer.return_shares slicer) slicer.degree tuple elem.output in
      test_entries i
    else
      print_endline "All entries tested"
  in
    test_entries 0

let rec test_log lexbuf ff evaluation =
  let rec loop ffl =
    let set_slicer c params = match params with
      | Some p -> set_slicer_parameters c p
      | None -> Printf.printf "%s: No parameters specified, continuing at timepoint %d\n%!" c !tp;
    in
    match Log.get_next_entry lexbuf with
    | MonpolyCommand {c; parameters} ->
        let process_command = function
            | "set_slicer" ->
                set_slicer c parameters;
                loop ffl
            | "test_slicer" -> test_slicer ff evaluation;
                loop ffl
            | _ ->
                Printf.printf "UNRECOGNIZED COMMAND: %s\n%!" c;
                loop ffl
        in
        process_command c;
    | MonpolyTestTuple st ->
          Dllist.add_last st evaluation;
          loop ffl
    | _ -> ()
  in
  loop ff


let run_test testfile formula =
  let lexbuf = Log.log_open testfile in
  let neval = Neval.create () in
  let extf, _ = add_ext neval formula in
  Printf.printf "Testing slicing configurations\n";
  test_log lexbuf extf (Dllist.empty())
