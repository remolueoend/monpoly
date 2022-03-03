(*
 * This file is part of MONPOLY.
 *
 * Copyright (C) 2011 Nokia Corporation and/or its subsidiary(-ies).
 * Contact:  Nokia Corporation (Debmalya Biswas: debmalya.biswas@nokia.com)
 *
 * Copyright (C) 2012, 2021 ETH Zurich.
 * Contact:  ETH Zurich (Joshua Schneider: joshua.schneider@inf.ethz.ch)
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

open Predicate

type result = {empty_rel: bool; rel: Relation.relation}

let empty_result empty_val group_posl =
  if group_posl = [] then
    {empty_rel = true; rel = Relation.singleton (Tuple.make_tuple [empty_val])}
  else
    {empty_rel = false; rel = Relation.empty}

let nonempty_result rel = {empty_rel = false; rel}

type aggregator = Relation.relation -> result

let comp_aggreg empty_val init update post result_pos group_posl rel =
  if Relation.is_empty rel then empty_result empty_val group_posl
  else
    begin
      let map = Hashtbl.create 1000 (* TODO(JS): why this value? *) in
      Relation.iter
        (fun tuple ->
           let gtuple = Tuple.projections group_posl tuple in
           try
             let old_agg_value = Hashtbl.find map gtuple in
             let new_agg_value = update old_agg_value tuple in
             Hashtbl.replace map gtuple new_agg_value;
           with
           | Not_found ->
             Hashtbl.add map gtuple (init tuple);
        ) rel;
      let new_rel = ref Relation.empty in
      Hashtbl.iter
        (fun gtuple v ->
          let rtuple = Tuple.insert result_pos gtuple (post v) in
          new_rel := Relation.add rtuple !new_rel
        ) map;
      nonempty_result !new_rel
    end

let cnt empty_val result_pos group_posl =
  let init _t = Z.one in
  let update ov _nt = Z.succ ov in
  let post c = Int c in
  comp_aggreg empty_val init update post result_pos group_posl

let min empty_val result_pos arg_pos group_posl =
  let init t = Tuple.get_at_pos t arg_pos in
  let update ov nt = min ov (Tuple.get_at_pos nt arg_pos) in
  comp_aggreg empty_val init update (fun x -> x) result_pos group_posl

let max empty_val result_pos arg_pos group_posl =
  let init t = Tuple.get_at_pos t arg_pos in
  let update ov nt = max ov (Tuple.get_at_pos nt arg_pos) in
  comp_aggreg empty_val init update (fun x -> x) result_pos group_posl

let sum empty_val result_pos arg_pos group_posl =
  let init t = Tuple.get_at_pos t arg_pos in
  let update ov nt = plus ov (Tuple.get_at_pos nt arg_pos) in
  comp_aggreg empty_val init update (fun x -> x) result_pos group_posl

let avg empty_val result_pos arg_pos group_posl =
  let init t = (Tuple.get_at_pos t arg_pos, 1) in
  let update (os, oc) nt = (plus os (Tuple.get_at_pos nt arg_pos), oc + 1) in
  let post (s, c) = Float (float_of_cst s /. float_of_int c) in
  comp_aggreg empty_val init update post result_pos group_posl

let med empty_val result_pos arg_pos group_posl =
  let init t = ([Tuple.get_at_pos t arg_pos], 1) in
  let update (ol, oc) nt = (Tuple.get_at_pos nt arg_pos :: ol, oc + 1) in
  let post (l, c) =
    let sorted = List.sort Stdlib.compare l in
    Misc.median sorted c Predicate.average
  in
  comp_aggreg empty_val init update post result_pos group_posl


class type window_aggregator =
  object
    method add_rel: MFOTL.timestamp -> Relation.relation -> unit
    method evict_until: MFOTL.timestamp -> unit
    method get_result: result
  end

class comm_group_aggregator init add remove post intv empty_val
  result_pos group_posl =
  object
    val tw_rels = Queue.create ()
    (* TODO(JS): why these values? *)
    val mset = Hashtbl.create 1000
    val acc = Hashtbl.create 100

    method add_rel ts rel =
      if not (MFOTL.infinite_interval intv) then
        Queue.push (ts, rel) tw_rels;
      Relation.iter
        (fun tuple ->
          try
            let m = Hashtbl.find mset tuple in
            Hashtbl.replace mset tuple (m + 1)
          with Not_found ->
            Hashtbl.add mset tuple 1;
            let gtuple = Tuple.projections group_posl tuple in
            try
              let old_agg_value = Hashtbl.find acc gtuple in
              let new_agg_value = add old_agg_value tuple in
              Hashtbl.replace acc gtuple new_agg_value
            with Not_found ->
              Hashtbl.add acc gtuple (init tuple)
        ) rel

    method evict_until ts =
      let evict tuple =
        let m = Hashtbl.find mset tuple in
        if m > 1 then
          Hashtbl.replace mset tuple (m - 1)
        else
          begin
            Hashtbl.remove mset tuple;
            let gtuple = Tuple.projections group_posl tuple in
            let old_agg_value = Hashtbl.find acc gtuple in
            match remove old_agg_value tuple with
            | None -> Hashtbl.remove acc gtuple
            | Some new_agg_value -> Hashtbl.replace acc gtuple new_agg_value
          end
      in
      let rec loop () =
        if not (Queue.is_empty tw_rels) then
          let (tsr, rel) = Queue.top tw_rels in
          let diff = MFOTL.ts_minus ts tsr in
          if not (MFOTL.in_left_ext diff intv) then
            begin
              ignore (Queue.pop tw_rels);
              Relation.iter evict rel;
              loop ()
            end
      in
      loop ()

    method get_result =
      if Hashtbl.length acc = 0 then empty_result empty_val group_posl
      else
        begin
          let res = ref Relation.empty in
          Hashtbl.iter
            (fun gtuple v ->
              let rtuple = Tuple.insert result_pos gtuple (post v) in
              res := Relation.add rtuple !res
            ) acc;
          nonempty_result !res
        end
  end

class once_aggregator (window: window_aggregator) intv =
  object
    val non_tw_rels = Queue.create ()

    method update ts rel =
      window#evict_until ts;
      if not (Relation.is_empty rel) then
        Queue.push (ts, rel) non_tw_rels;
      let rec consider_new_rels () =
        if not (Queue.is_empty non_tw_rels) then
          begin
            let (tsr, rel) = Queue.top non_tw_rels in
            let diff = MFOTL.ts_minus ts tsr in
            if not (MFOTL.in_left_ext diff intv) then
              begin
                (* relation already too old for the new time window *)
                ignore (Queue.pop non_tw_rels);
                consider_new_rels ()
              end
            else if MFOTL.in_interval diff intv then
              begin
                (* relation in the interval, so we process it *)
                ignore (Queue.pop non_tw_rels);
                window#add_rel tsr rel;
                consider_new_rels ()
              end
            (* else, that is, if not (MFOTL.in_right_ext diff intv),
               the relation is too new, so we stop and consider it next time *)
          end
      in
      consider_new_rels ()

    method get_result = window#get_result
  end

let cnt_once empty_val intv result_pos group_posl =
  let init _t = Z.one in
  let add ov _nt = Z.succ ov in
  let remove ov _dt = if Z.equal ov Z.one then None else Some (Z.pred ov) in
  let post x = Int x in
  let window = new comm_group_aggregator init add remove post intv empty_val
    result_pos group_posl in
  new once_aggregator window intv

let sum_avg_once post empty_val intv result_pos arg_pos group_posl =
  let init t = (Tuple.get_at_pos t arg_pos, 1) in
  let add (os, oc) nt = (plus os (Tuple.get_at_pos nt arg_pos), oc + 1) in
  let remove (os, oc) dt =
    if oc = 1 then None
    else Some (minus os (Tuple.get_at_pos dt arg_pos), oc - 1)
  in
  let window = new comm_group_aggregator init add remove post intv empty_val
    result_pos group_posl in
  new once_aggregator window intv

let sum_once = sum_avg_once (fun (s, _) -> s)

let avg_once = sum_avg_once (fun (s, c) ->
  Float (float_of_cst s /. float_of_int c))


exception Break

(* The following precondition should hold: [len] is the sum of all values in
   [mset] *)
let mset_median fmed (mset, len) =
  assert (len <> 0);
  assert (len = Intmap.sum mset);
  let mid = if len mod 2 = 0 then (len / 2) - 1 else len / 2 in
  let flag = ref false in
  let crt = ref 0 in
  let med = ref (fst (Intmap.choose mset)) in
  let prev = ref !med in
  try
    Intmap.iter
      (fun c m ->
        if !flag then
          begin med := fmed !prev c; raise Break end
        else
        if mid < !crt + m then (* c is the (left) median *)
          if len mod 2 = 0 then
            if mid = !crt + m - 1 then
              begin flag := true;  prev := c end
            else
              begin med := fmed c c; raise Break end
          else begin med := fmed c c; raise Break end
        else
          crt := !crt + m
      ) mset;
    failwith "[mset_median] internal error"
  with Break -> !med

let med_once empty_val intv result_pos arg_pos group_posl =
  let init t = (Intmap.singleton (Tuple.get_at_pos t arg_pos) 1, 1) in
  let add (old_mset, oc) nt =
    let arg = Tuple.get_at_pos nt arg_pos in
    let new_mset = Intmap.update arg
      (function
        | None -> Some 1
        | Some m -> Some (m + 1)
      ) old_mset
    in
    (new_mset, oc + 1)
  in
  let remove (old_mset, oc) dt =
    if oc = 1 then None
    else
      let arg = Tuple.get_at_pos dt arg_pos in
      let new_mset = Intmap.update arg
        (function
          | None -> None
          | Some m when m = 1 -> None
          | Some m -> Some (m - 1)
        ) old_mset
      in
      Some (new_mset, oc - 1)
  in
  let post x = mset_median Predicate.average x in
  let window = new comm_group_aggregator init add remove post intv empty_val
    result_pos group_posl in
  new once_aggregator window intv


class mono_aggregator is_better intv empty_val result_pos arg_pos group_posl =
  (* is_better x y returns 1 if x better than y, 0 if they are equal, and -1
     otherwise.
     for Min: x is better than y iff x < y
     for Max: x is better than y iff x > y *)
  object
    (* TODO(JS): why this value? *)
    val table = Hashtbl.create 100

    method add_rel ts rel =
      (* The invariant is:
         if (tsq,v) is before (tsq',v')
         then tsq >= tsq', v' is better or equal than v, and
         we don't have equality in both cases;

         The first condition is ensured by default, as timestamps are
         non-decreasing. We have to enforce the second and third
         consitions. *)
      let rec update_list_new new_val dllist =
        if Dllist.is_empty dllist then
          Dllist.add_first (ts, new_val) dllist
        else
          begin
            let (ts', crt_val) = Dllist.get_first dllist in
            let comp = is_better new_val crt_val in
            if comp > 0 then
              begin
                ignore (Dllist.pop_first dllist);
                update_list_new new_val dllist
              end
            else if comp = 0 then
              begin
                if ts <> ts' then
                  begin
                    ignore (Dllist.pop_first dllist);
                    Dllist.add_first (ts, new_val) dllist
                  end
                  (* else: same element appears previously, no need to update *)
              end
            else
              Dllist.add_first (ts, new_val) dllist
          end
      in
      Relation.iter
        (fun tuple ->
           let gtuple = Tuple.projections group_posl tuple in
           let arg = Tuple.get_at_pos tuple arg_pos in
           try
             let dllist = Hashtbl.find table gtuple in
             update_list_new arg dllist
           with Not_found ->
             let dllist = Dllist.singleton (ts, arg) in
             Hashtbl.add table gtuple dllist;
        ) rel

    method evict_until ts =
      let rec update_list_old dllist =
        if not (Dllist.is_empty dllist) then
          let ts', _ = Dllist.get_last dllist in
          let diff = MFOTL.ts_minus ts ts' in
          if not (MFOTL.in_left_ext diff intv) then
            begin
              ignore (Dllist.pop_last dllist);
              update_list_old dllist
            end
      in
      Hashtbl.filter_map_inplace
        (fun _ dllist ->
          update_list_old dllist;
          if Dllist.is_empty dllist then None else Some dllist
        ) table

    method get_result =
      if Hashtbl.length table = 0 then empty_result empty_val group_posl
      else
        begin
          let res = ref Relation.empty in
          Hashtbl.iter
            (fun gtuple dllist ->
              let _, agg_val = Dllist.get_last dllist in
              let rtuple = Tuple.insert result_pos gtuple agg_val in
              res := Relation.add rtuple !res
            ) table;
          nonempty_result !res
        end
  end

let min_once empty_val intv result_pos arg_pos group_posl =
  let is_better x y = -(Stdlib.compare x y) in
  let window = new mono_aggregator is_better intv empty_val
    result_pos arg_pos group_posl in
  new once_aggregator window intv

let max_once empty_val intv result_pos arg_pos group_posl =
  let is_better x y = Stdlib.compare x y in
  let window = new mono_aggregator is_better intv empty_val
    result_pos arg_pos group_posl in
  new once_aggregator window intv

let prerr_bool b =
  if b then
    prerr_string "true"
  else
    prerr_string "false"
let prerr_state (oaggr:once_aggregator):unit =
  prerr_string "empty_rel=";
  prerr_bool oaggr#get_result.empty_rel;
  prerr_string "; rel=";
  Relation.prerr_rel "" oaggr#get_result.rel
