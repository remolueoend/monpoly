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



open Predicate
open MFOTL

let enabled = ref false

type label =
  | LTrue
  | LFalse
  | LEvRel

type 'a labeled =
    'a * label list

type lformula =
  | LEqual of (term * term)
  | LLess of (term * term)
  | LLessEq of (term * term)
  | LSubstring of (term * term)
  | LMatches of (term * term)
  | LPred of predicate
  | LNeg of lformula labeled
  | LAnd of (lformula labeled * lformula labeled)
  | LOr of (lformula labeled * lformula labeled)
  (* | LImplies of (lformula labeled * lformula labeled) *)
  (* | LEquiv of (lformula labeled * lformula labeled) *)
  | LExists of (var list * lformula labeled)
  | LForAll of (var list * lformula labeled)
  | LAggreg of (var * agg_op * var * var list * lformula labeled)
  | LPrev of (interval * lformula labeled)
  | LNext of (interval * lformula labeled)
  | LEventually of (interval * lformula labeled)
  | LOnce of (interval * lformula labeled)
  | LAlways of (interval * lformula labeled)
  | LPastAlways of (interval * lformula labeled)
  | LSince of (interval * lformula labeled * lformula labeled)
  | LUntil of (interval * lformula labeled * lformula labeled)


let has_label l labels =
  List.mem l labels

let add_label l labels =
  if has_label l labels
  then
    labels
  else
    l :: labels

let string_of_label = function
  | LTrue -> "(True)"
  | LFalse -> "(False)"
  | LEvRel -> "(EvRel)"

let rec string_of_labels = function
| [] -> ""
| h :: t -> string_of_label h ^ ", " ^ string_of_labels t

let print_labels l = Printf.printf "%s" (string_of_labels l)

let eprint_labels l = Printf.eprintf "%s" (string_of_labels l)

let intv_contains_zero = function
  | Z.(CBnd (zero),_) ->
    (* Printf.printf "contains zero\n"; *)
    true
  | _ ->
    (* Printf.printf "excludes zero\n"; *)
    false

let add_labels (lf : lformula) : label list =
  let labels = ref [] in
  (* single operator rules: LFalse, LTrue *)
  (match lf with
   | LEqual (_,_)
   | LLess (_,_)
   | LLessEq (_,_)
   | LSubstring (_, _) 
   | LMatches (_, _) -> ()
   | LPred _ ->
     labels := add_label LFalse !labels
   | LNeg (f1, l1) -> begin
       if (has_label LTrue l1) then
         labels := add_label LFalse !labels
       else ();
       if (has_label LFalse l1) then
         labels := add_label LTrue !labels
       else ()
     end
   | LAnd ((f1, l1), (f2, l2)) -> begin
       if (has_label LTrue l1) && (has_label LTrue l2) then
         labels := add_label LTrue !labels
       else ();
       if (has_label LFalse l1) || (has_label LFalse l2) then
         labels := add_label LFalse !labels
       else ()
     end
   | LOr ((f1, l1), (f2, l2)) -> begin
       if (has_label LTrue l1) || (has_label LTrue l2) then
         labels := add_label LTrue !labels
       else ();
       if (has_label LFalse l1) && (has_label LFalse l2) then
         labels := add_label LFalse !labels
       else ()
     end
   | LExists (v, (f1, l1))
   | LForAll (v, (f1, l1)) -> labels := l1
   | LEventually (intv, (f1, l1))
   | LOnce (intv, (f1, l1))
   | LAlways (intv, (f1, l1))
   | LPastAlways (intv, (f1, l1)) -> ()
   | LSince (intv, (f1, l1), (f2, l2))
   | LUntil (intv, (f1, l1), (f2, l2)) -> ()
   | _ -> ());
  (* single operator rules: LEvRel *)
  (match lf with
   | LEqual (_,_)
   | LLess (_,_)
   | LLessEq (_,_)
   | LSubstring (_,_)
   | LMatches (_,_)
   | LPred _ ->
     labels := add_label LEvRel !labels
   | LNeg (f1, l1)
   | LExists (_, (f1, l1))
   | LForAll (_, (f1, l1)) -> begin
       if (has_label LEvRel l1) then
         labels := add_label LEvRel !labels
       else ()
     end
   | LAnd ((f1, l1), (f2, l2))
   | LOr ((f1, l1), (f2, l2)) -> begin
       if (has_label LEvRel l1) && (has_label LEvRel l2) then
         labels := add_label LEvRel !labels
       else ()
     end
   | LEventually (intv, (f1, l1))
   | LOnce (intv, (f1, l1)) -> begin
       if (has_label LEvRel l1) && (has_label LFalse l1) then
         labels := add_label LEvRel !labels
       else ()
     end
   | LAlways (intv, (f1, l1))
   | LPastAlways (intv, (f1, l1)) -> begin
       if (has_label LEvRel l1) && (has_label LTrue l1) then
         labels := add_label LEvRel !labels
       else ()
     end
   | LSince (intv, (f1, l1), (f2, l2))
   | LUntil (intv, (f1, l1), (f2, l2)) -> begin
       if (has_label LEvRel l1) && (has_label LEvRel l2) &&
          (has_label LTrue l1) && (has_label LFalse l2) then
         labels := add_label LEvRel !labels
       else ()
     end
   | _ -> ());
  (* multiple operator rules: LEvRel *)
  (match lf with
   | LEventually (intv1, ((LOnce (intv2, (f1, l1))), _))
   | LOnce (intv1, ((LEventually (intv2, (f1, l1))), _)) ->
     if (intv_contains_zero intv1) && (intv_contains_zero intv2) &&
        (has_label LFalse l1) && (has_label LEvRel l1)
     then
       labels := add_label LEvRel !labels
     else ()
   | LAlways (intv1, ((LPastAlways (intv2, (f1, l1))), _))
   | LPastAlways (intv1, ((LAlways (intv2, (f1, l1))), _)) ->
     if (intv_contains_zero intv1) && (intv_contains_zero intv2) &&
        (has_label LTrue l1) && (has_label LEvRel l1)
     then
       labels := add_label LEvRel !labels
     else ()
   | _ -> ());
  (* --- debugging code ---*)
  (* print_formula "add_labels: " lf; *)
  (* print_string " --> "; *)
  (* print_labels !labels; *)
  (* print_newline(); *)
  (* --- end of debugging code ---*)
  !labels


(** recursively analyze and label a formula
    1) on the way down, build a labeled_formula from the formula
    2) on the way up add labels
    Input formula must be normalized (no Implies or Equiv)
*)
let rec go_down (f : MFOTL.formula) : lformula labeled =
  let lf : lformula =  match f with
    | Equal (t1,t2) -> LEqual (t1,t2)
    | Less (t1,t2) -> LLess (t1,t2)
    | LessEq (t1,t2) -> LLessEq (t1,t2)
    | Substring (t1,t2) -> LSubstring(t1, t2)
    | Matches (t1,t2,_) -> LMatches(t1, t2)
    | Pred p -> LPred p
    | Neg f -> LNeg (go_down f)
    | And (f1,f2) -> LAnd ((go_down f1), (go_down f2))
    | Or (f1,f2) -> LOr ((go_down f1), (go_down f2))
    | Exists (vl,f) -> LExists (vl, (go_down f))
    | ForAll (vl,f) -> LForAll (vl, (go_down f))
    | Aggreg (_,y,op,x,glist,f) -> LAggreg (y,op,x,glist, go_down f)
    | Prev (i,f) -> LPrev (i, (go_down f))
    | Next (i,f) -> LNext (i, (go_down f))
    | Eventually (intv,f) -> LEventually (intv, (go_down f))
    | Once (intv,f) -> LOnce (intv, (go_down f))
    | Always (intv,f) -> LAlways (intv, (go_down f))
    | PastAlways (intv,f) -> LPastAlways (intv, (go_down f))
    | Since (i,f1,f2) -> LSince (i, (go_down f1), (go_down f2))
    | Until (i,f1,f2) -> LUntil (i, (go_down f1), (go_down f2))
    | Implies (f1,f2) -> failwith "[Filter_empty_tp.go_down] formula contains Implies"
    (* (\* rewrite p => q to ~p or q *\) *)
    (* LOr ((go_down (Neg f1)), (go_down f2)) *)
    | Equiv (f1,f2) -> failwith "[Filter_empty_tp.go_down] formula contains Equiv"
    | Let (_,_,_) -> failwith "[Filter_empty_tp] LET not supported; use -unfold_let full or -nofilteremptytp"
    | LetPast (_,_,_) -> failwith "[Filter_empty_tp] LETPAST not supported; use -verified"
    | Frex (_,_) -> failwith "[Filter_empty_tp] MATCHF not supported; use -nofilteremptytp"
    | Prex (_,_) -> failwith "[Filter_empty_tp] MATCHP not supported; use -nofilteremptytp"
  in
  let l = add_labels lf
  in
  (lf, l)

(* The labeling rules do not support LET. Hence we unfold every LET before
   computing the labels, which is sound because unfolding preserves the
   semantics. However, a problem can arise if a defined predicate is not used.
   Then, unfolding removes the defining formula completely, even if it contains
   operators that are incompatible with filtering empty tps (Prev/Next).
   Therefore, we perform an additional check, without unfolding, to detect such
   operators. *)
let go_down f = go_down (Rewriting.expand_let Rewriting.ExpandAll f)

let is_prev_or_next = function
  | Prev _ -> true
  | Next _ -> true
  | _ -> false

let has_prev_or_next f =
  let tsf = MFOTL.temporal_subformulas f in
  List.exists is_prev_or_next tsf

let is_filterable_empty_tp f =
  let (lf, l) = go_down f in
  (* --- debugging code ---*)
  if Misc.debugging Misc.Dbg_filter then begin
    Printf.eprintf "Filter_empty_tp labels: ";
    eprint_labels l;
    Printf.eprintf "\n%!"
  end;
  (* --- end of debugging code ---*)
  (* LFalse - formula is false on empty tp *)
  (* LEvRel - formula is not affected by addition/removal of empty tp *)
  (has_label LFalse l) && (has_label LEvRel l) && not (has_prev_or_next f)

let enable f =
  enabled := is_filterable_empty_tp f;
  if Misc.debugging Misc.Dbg_all then
    if !enabled then
      Printf.eprintf "[Filter_empty_tp.enable] Enabled\n%!"
    else
      Printf.eprintf "[Filter_empty_tp.enable] Disabled\n%!"

let fc_check_filterable_empty_tp f =
  let (lf, l) = go_down f in
  Printf.printf "Filter_empty_tp labels: ";
  print_labels l;
  Printf.printf "\n";
  Printf.printf "Properties: ";
  let filterable = (has_label LFalse l) && (has_label LEvRel l) &&
    not (has_prev_or_next f) in
  if filterable then
    (* LFalse - formula is false on empty tp *)
    (* LEvRel - formula is not affected by addition/removal of empty tp *)
    Printf.printf "(filterable_empty_tp)";
  Printf.printf "\n\n";

