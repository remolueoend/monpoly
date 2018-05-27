(*
 * This file is part of MONPOLY.
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



open MFOTL
open Predicate
open Misc

let enabled = ref false

(* ------------------------ *)
(* --- predicate filter --- *)
let predicate_filter = ref []

let rec print_preds = function
  | [] -> Printf.printf "\n"
  | h :: t ->
    Printf.printf "%s, " h;
    print_preds t

let get_predicates f =
  let rec get_preds preds = function
    | Equal (t1,t2)
    | Less (t1,t2)
    | LessEq (t1,t2) -> preds
    | Pred p ->  p :: preds
    | Neg f
    | Exists (_,f)
    | ForAll (_,f)
    | Aggreg (_,_,_,_,f)
    | Prev (_,f)
    | Next (_,f)
    | Eventually (_,f)
    | Once (_,f)
    | Always (_,f)
    | PastAlways (_,f) -> get_preds preds f
    | And (f1,f2)
    | Or (f1,f2)
    | Implies (f1,f2)
    | Equiv (f1,f2)
    | Since (_,f1,f2)
    | Until (_,f1,f2) -> (get_preds preds f1) @ (get_preds preds f2)
  in
  get_preds [] f

let set_pred_names f =
  predicate_filter := List.map Predicate.get_name (get_predicates f);
  if Misc.debugging Dbg_filter then
    begin
      Printf.printf "--- predicate_filter: ---\n";
      print_preds !predicate_filter
    end

let rel_OK p =
  List.mem p !predicate_filter

(* -------------------- *)
(* --- tuple filter --- *)

(* type Tuple_filter = (pred * int * term) list *)
let tuple_filter_csts = ref []
let tuple_filter_is_cst = ref []

type tuple_filter_stage1 =
  | Is_var
  | Is_cst of cst


let remove_duplicates l =
  let rec go acc = function
    | [] -> acc
    | h :: t ->
      if List.mem h acc
      then go acc t
      else go (h :: acc) t
  in go [] l

let get_tuple_filter f =
  let rec tuples_from_args p i = function  (* args *)
    | [] -> []
    | h :: t -> match h with
      | Var(_) -> (p,i,Is_var) :: (tuples_from_args p (i+1) t)
      | Cst(c) -> (p,i,Is_cst(c)) :: (tuples_from_args p (i+1) t)
      | _ -> failwith "[Filter_rel.tuples_from_args] internal error"
  in
  let rec get_tuples tuples = function (* formula *)
    | Equal (t1,t2)
    | Less (t1,t2)
    | LessEq (t1,t2) -> tuples
    | Pred p ->  (tuples_from_args (get_name p) 0 (get_args p)) @ tuples
    | Neg f
    | Exists (_,f)
    | ForAll (_,f)
    | Aggreg (_,_,_,_,f)
    | Prev (_,f)
    | Next (_,f)
    | Eventually (_,f)
    | Once (_,f)
    | Always (_,f)
    | PastAlways (_,f) -> get_tuples tuples f
    | And (f1,f2)
    | Or (f1,f2)
    | Implies (f1,f2)
    | Equiv (f1,f2)
    | Since (_,f1,f2)
    | Until (_,f1,f2) -> get_tuples (get_tuples tuples f1) f2
  in
  (* filter out from stage1 filter
     all (p,i) instances which occur as variables somewhere within the formula
  *)
  let filter_is_var filter_stage1 =
    (* filter out variables and convert to stage2 type *)
    let remove_is_var l =
      List.filter
        (fun (p,i,a) -> match a with
           | Is_var -> false
           | Is_cst(c) -> not (List.mem (p,i,Is_var) filter_stage1)
        ) l
    in
    let rec convert_type = function
      | [] -> []
      | (p,i,a) :: t -> match a with
        | Is_var -> failwith "[Filter_rel.convert_type] impossible"
        | Is_cst(c) -> (p,i,c) :: (convert_type t)
    in
    convert_type (remove_is_var (remove_duplicates filter_stage1))
  in
  filter_is_var (get_tuples [] f)

let is_cst_from_csts csts =
  remove_duplicates (List.map (fun (p,i,c) -> (p,i)) csts)

let rec print_csts = function
  | [] -> ()
  | (p,i,c) :: t ->
    Printf.printf "(%s,%d," p i;
    Predicate.print_cst true c;
    Printf.printf ")\n";
    print_csts t

let rec print_is_cst = function
  | [] -> ()
  | (p,i) :: t ->
    Printf.printf "(%s,%d)\n" p i;
    print_is_cst t

let set_tuples f =
  tuple_filter_csts := get_tuple_filter f;
  tuple_filter_is_cst := is_cst_from_csts !tuple_filter_csts;
  if Misc.debugging Dbg_filter then
    begin
      Printf.printf "--- tuple_filter: is_cst ---\n";
      print_is_cst !tuple_filter_is_cst;
      Printf.printf "--- tuple_filter: csts ---\n";
      print_csts !tuple_filter_csts;
      Printf.printf "--- ---\n";
      Printf.printf "%!"
    end

let tuple_OK pred tuple =
  (* for all (pred,i) entries in filter_is_cst there must be
   * a matching cst in filter_csts
  *)
  let rec process_csts pred tuple_cst filter_csts =
    match filter_csts with
    | [] -> false
    | (p,_,c) :: filter_tail ->
      if p = pred && tuple_cst = c then
        true
      else
        process_csts pred tuple_cst filter_tail
  in
  let rec process_is_cst pred tuple filter_is_cst filter_csts =
    match filter_is_cst with
    | [] -> true
    | (p,i) :: filter_tail ->
      if p = pred then
        process_csts pred (List.nth tuple i) filter_csts &&
        process_is_cst pred tuple filter_tail filter_csts
      else
        process_is_cst pred tuple filter_tail filter_csts
  in
  process_is_cst pred (Tuple.get_constants tuple) !tuple_filter_is_cst !tuple_filter_csts

let debug_tuple_csts_OK pred tuple =
  let res = tuple_OK pred tuple in
  Printf.printf "filter: pred %s tuple" pred;
  Tuple.print_tuple tuple;
  Printf.printf " ->";
  if res
  then Printf.printf "true"
  else Printf.printf "false"
  ;
  Printf.printf "\n";
  res

(* ------------------- *)
(* --- all filters --- *)
let enable f =
  enabled := true;
  set_pred_names f;
  set_tuples f;
  if Misc.debugging Misc.Dbg_all then
    Printf.eprintf "[Filter_rel.enable] Enabled\n"

let get_all_filters _ =
  (!predicate_filter, !tuple_filter_is_cst, !tuple_filter_csts)

let set_all_filters (f1, f2, f3) =
  predicate_filter := f1;
  tuple_filter_is_cst := f2;
  tuple_filter_csts := f3;
  if Misc.debugging Dbg_filter then
    begin
      Printf.printf "--- predicate_filter: ---\n";
      print_preds !predicate_filter;
      Printf.printf "--- tuple_filter: is_cst ---\n";
      print_is_cst !tuple_filter_is_cst;
      Printf.printf "--- tuple_filter: csts ---\n";
      print_csts !tuple_filter_csts;
      Printf.printf "--- ---\n";
      Printf.printf "%!"
    end
