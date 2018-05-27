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



open Unix
open Predicate

type timestamp = float
type tsdiff = timestamp
type bound = OBnd of tsdiff | CBnd of tsdiff | Inf
type interval = bound * bound

type agg_op = Cnt | Min | Max | Sum | Avg | Med

type formula =
  | Equal of (term * term)
  | Less of (term * term)
  | LessEq of (term * term)
  | Pred of predicate
  | Neg of formula
  | And of (formula * formula)
  | Or of (formula * formula)
  | Implies of (formula * formula)
  | Equiv of (formula * formula)
  | Exists of (var list * formula)
  | ForAll of (var list * formula)
  | Aggreg of (var * agg_op * var * var list * formula)
  | Prev of (interval * formula)
  | Next of (interval * formula)
  | Eventually of (interval * formula)
  | Once of (interval * formula)
  | Always of (interval * formula)
  | PastAlways of (interval * formula)
  | Since of (interval * formula * formula)
  | Until of (interval * formula * formula)

let unixts = ref false

let ts_of_string err_place str =
  try
    float_of_string str
  with Failure _ ->
    let msg = Printf.sprintf "[%s, MFOTL.ts_of_string] Cannot convert %s into a timestamp" err_place str in
    failwith msg

let ts_of_cst c =
  match c with
  | Int _ -> failwith "[MFOTL.ts_of_cst] conversion not possible"
  | Str s -> float_of_string s
  | Float f -> f
let cst_of_ts t = Str (string_of_float t)
let tsdiff_of_cst = ts_of_cst
let cst_of_tsdiff = cst_of_ts

let ts_plus t1 t2 = t1 +. t2
let ts_minus t1 t2 = t1 -. t2
let ts_invalid = -1.
let ts_null = 0.
let ts_max = max_float


let ts_of_string2 err_place str =
  try
    int_of_string str
  with Failure _ ->
    (* a way of avoiding the problem of too big integers *)
    let lens = String.length str in
    let lenm = String.length (string_of_int max_int) in
    let str =
      if lens >= lenm then
        let d = lens-lenm+1 in
        String.sub str d (lens-d)
      else
        str
    in
    try
      int_of_string str
    with Failure _ ->
      let msg = Printf.sprintf "[%s, MFOTL.ts_of_string] Cannot convert %s into a timestamp" err_place str in
      failwith msg



(* TODO: these function names are not intuitive, because one usually
   does not think in terms of the interval I labelling a temporal
   operator, but instead, in terms of the time window that it defines.
   So update these, with something like, left_of_timewindow,
   right_of_timewindow, in_timewindow.
*)

(* Tests that [v] is in the extension to the right of [intv] *)
let in_right_ext v intv =
  match intv with
  | CBnd b, _ -> v >= b
  | OBnd b, _ -> v > b
  | Inf, _ -> false

(* Tests that [v] is in the extension to the left of [intv] *)
let in_left_ext v intv =
  match intv with
  | _, CBnd b -> v <= b
  | _, OBnd b -> v < b
  | _, Inf -> true

let in_interval v intv =
  in_right_ext v intv && in_left_ext v intv



let direct_subformulas = function
  | Equal (t1,t2) -> []
  | Less (t1,t2) -> []
  | LessEq (t1,t2) -> []
  | Pred p -> []
  | Neg f -> [f]
  | And (f1,f2) -> [f1;f2]
  | Or (f1,f2) -> [f1;f2]
  | Implies (f1,f2) -> [f1;f2]
  | Equiv (f1,f2) -> [f1;f2]
  | Exists (v,f) -> [f]
  | ForAll (v,f) -> [f]
  | Aggreg (_,_,_,_,f) -> [f]
  | Prev (intv,f) -> [f]
  | Next (intv,f) -> [f]
  | Eventually (intv,f) -> [f]
  | Once (intv,f) -> [f]
  | Always (intv,f) -> [f]
  | PastAlways (intv,f) -> [f]
  | Since (intv,f1,f2) -> [f1;f2]
  | Until (intv,f1,f2) -> [f1;f2]


(** returns the list of all subformulas of [f], including [f] *)
let rec subformulas f =
   f::(List.concat (List.map subformulas (direct_subformulas f)))

(** returns the list of all temporal subformulas of [f] *)
let rec temporal_subformulas f =
  match f with
  | Prev (intv,f') -> f::(temporal_subformulas f')
  | Next (intv,f') -> f::(temporal_subformulas f')
  | Eventually (intv,f') -> f::(temporal_subformulas f')
  | Once (intv,f') -> f::(temporal_subformulas f')
  | Always (intv,f') -> f::(temporal_subformulas f')
  | PastAlways (intv,f') -> f::(temporal_subformulas f')
  | Since (intv,f1,f2) -> f::((temporal_subformulas f1) @ (temporal_subformulas f2))
  | Until (intv,f1,f2) -> f::((temporal_subformulas f1) @ (temporal_subformulas f2))
  | _ -> List.concat (List.map temporal_subformulas (direct_subformulas f))


let is_temporal = function
  | Prev (intv,f) -> true
  | Next (intv,f) -> true
  | Since (intv,f1,f2) -> true
  | Until (intv,f1,f2) -> true
  | Eventually (intv,f) -> true
  | Once (intv,f) -> true
  | Always (intv,f) -> true
  | PastAlways (intv,f) -> true
  | _ -> false


let rec free_vars = function
  | Equal (t1,t2)
  | Less (t1,t2)
  | LessEq (t1,t2) ->
    Misc.union (Predicate.tvars t1) (Predicate.tvars t2)
  | Pred p -> Predicate.pvars p
  | Neg f -> free_vars f
  | And (f1,f2) -> Misc.union (free_vars f1) (free_vars f2)
  | Or (f1,f2) -> Misc.union (free_vars f1) (free_vars f2)
  | Implies (f1,f2) -> Misc.union (free_vars f1) (free_vars f2)
  | Equiv (f1,f2) -> Misc.union (free_vars f1) (free_vars f2)
  | Exists (vl,f) -> List.filter (fun x -> not (List.mem x vl)) (free_vars f)
  | ForAll (vl,f) -> List.filter (fun x -> not (List.mem x vl)) (free_vars f)
  | Aggreg (y,op,x,glist,f) -> y :: glist
  | Prev (intv,f) -> free_vars f
  | Next (intv,f) -> free_vars f
  | Eventually (intv,f) -> free_vars f
  | Once (intv,f) -> free_vars f
  | Always (intv,f) -> free_vars f
  | PastAlways (intv,f) -> free_vars f
  | Since (intv,f1,f2) -> Misc.union (free_vars f1) (free_vars f2)
  | Until (intv,f1,f2) -> Misc.union (free_vars f1) (free_vars f2)


let string_of_ts ts =
  if !unixts then
    let tm = Unix.gmtime ts in
    Printf.sprintf "%d-%d-%d %d:%d:%d"
      tm.tm_year tm.tm_mon tm.tm_mday
      tm.tm_hour tm.tm_min tm.tm_sec
  else
    if ts = ts_max then
      "MaxTS"
    else
      Printf.sprintf "%F" ts

let print_ts ts =
  print_string (string_of_ts ts)

let print_interval (a,b) =
  (match a with
   | OBnd a -> Printf.printf "(%.0f," a
   | CBnd a -> Printf.printf "[%.0f," a
   | Inf -> Printf.printf "(*,");
  match b with
  | OBnd b -> Printf.printf "%.0f)" b
  | CBnd b -> Printf.printf "%.0f]" b
  | Inf -> Printf.printf "*)"

let string_of_agg_op = function
  | Cnt -> "CNT"
  | Min -> "MIN"
  | Max -> "MAX"
  | Sum -> "SUM"
  | Avg -> "AVG"
  | Med -> "MED"

(* we always put parantheses for binary operators like "(f1 AND f2)", and around unary
ones only if they occur on the left-hand side of a binary operator: like "((NOT f1) AND f2)"*)
let print_formula str f =
  let rec print_f_rec top par f =
    (match f with
     | Equal (t1,t2) ->
       Predicate.print_term t1;
       print_string " = ";
       Predicate.print_term t2

     | Less (t1,t2) ->
       Predicate.print_term t1;
       print_string " < ";
       Predicate.print_term t2

     | LessEq (t1,t2) ->
       Predicate.print_term t1;
       print_string " <= ";
       Predicate.print_term t2

     | Pred p ->
       Predicate.print_predicate p;

     | _ ->
       if par && not top then
         print_string "(";
       (match f with
        | Neg f ->
          print_string "NOT ";
          print_f_rec false false f;

        | Exists (vl,f) ->
          print_string "EXISTS ";
          Misc.print_list_ext "" "" ", "
            Predicate.print_term
            (List.map (fun v -> Var v) vl);
          print_string ". ";
          print_f_rec false false f;

        | ForAll (vl,f) ->
          print_string "FORALL ";
          Misc.print_list_ext "" "" ", "
            Predicate.print_term
            (List.map (fun v -> Var v) vl);
          print_string ". ";
          print_f_rec false false f;

        | Aggreg (y,op,x,glist,f) ->
          Predicate.print_term (Var y);
          print_string " <- ";
          print_string (string_of_agg_op op);
          print_string " ";
          Predicate.print_term (Var x);
          if glist <> [] then
            begin
              print_string "; ";
              Misc.print_list_ext "" "" "," (fun z -> Predicate.print_term (Var z)) glist;
            end;
          print_string " ";
          print_f_rec false false f;

        | Prev (intv,f) ->
          print_string "PREVIOUS";
          print_interval intv; print_string " ";
          print_f_rec false false f

        | Next (intv,f) ->
          print_string "NEXT";
          print_interval intv; print_string " ";
          print_f_rec false false f

        | Eventually (intv,f) ->
          print_string "EVENTUALLY";
          print_interval intv; print_string " ";
          print_f_rec false false f

        | Once (intv,f) ->
          print_string "ONCE";
          print_interval intv; print_string " ";
          print_f_rec false false f

        | Always (intv,f) ->
          print_string "ALWAYS";
          print_interval intv; print_string " ";
          print_f_rec false false f

        | PastAlways (intv,f) ->
          print_string "PAST_ALWAYS";
          print_interval intv; print_string " ";
          print_f_rec false false f
        | _ ->
          if not par && not top then
            print_string "(";
          (match f with
           | And (f1,f2) ->
             print_f_rec false true f1;
             print_string " AND ";
             print_f_rec false false f2

           | Or (f1,f2) ->
             print_f_rec false true f1;
             print_string " OR ";
             print_f_rec false false f2

           | Implies (f1,f2) ->
             print_f_rec false true f1;
             print_string " IMPLIES ";
             print_f_rec false false f2

           | Equiv (f1,f2) ->
             print_f_rec false true f1;
             print_string " EQUIV ";
             print_f_rec false false f2

           | Since (intv,f1,f2) ->
             print_f_rec false true f1;
             print_string " SINCE";
             print_interval intv; print_string " ";
             print_f_rec false false f2

           | Until (intv,f1,f2) ->
             print_f_rec false true f1;
             print_string " UNTIL";
             print_interval intv; print_string " ";
             print_f_rec false false f2
           | _ -> failwith "[print_formula] impossible"
          );
          if not par && not top then
            print_string ")"
       );
       if par && not top then
         print_string ")";
    )
  in
  print_string str;
  print_f_rec true false f

let printnl_formula str f =
  print_formula str f;
  print_newline()


