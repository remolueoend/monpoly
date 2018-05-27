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

let print_label = function
  | LTrue -> Printf.printf "(True)"
  | LFalse -> Printf.printf "(False)"
  | LEvRel -> Printf.printf "(EvRel)"

let rec print_labels = function
  | [] -> ()
  | h :: t -> print_label h;
    Printf.printf ", ";
    print_labels t

let intv_contains_zero = function
  | CBnd (0.0),_ ->
    (* Printf.printf "contains zero\n"; *)
    true
  | _ ->
    (* Printf.printf "excludes zero\n"; *)
    false

(* --- debugging code ------------------------------------------------- *)
let print_formula str f =
  let rec print_f_rec top par f =
    if top then
      print_string "(";
    (match f with
     | LEqual (t1,t2) ->
       Predicate.print_term t1;
       print_string " = ";
       Predicate.print_term t2
     | LLess (t1,t2) ->
       Predicate.print_term t1;
       print_string " < ";
       Predicate.print_term t2
     | LLessEq (t1,t2) ->
       Predicate.print_term t1;
       print_string " <= ";
       Predicate.print_term t2
     | LPred p ->
       Predicate.print_predicate p;
     | _ ->
       if par && not top then
         print_string "(";
       (match f with
        | LNeg (f,_) ->
          print_string "NOT ";
          print_f_rec false false f;
        | LExists (vl,(f,_)) ->
          print_string "EXISTS ";
          Misc.print_list_ext "" "" ", "
            Predicate.print_term
            (List.map (fun v -> Var v) vl);
          print_string ".";
          print_f_rec false false f;
        | LForAll (vl,(f,_)) ->
          print_string "FORALL ";
          Misc.print_list_ext "" "" ", "
            Predicate.print_term
            (List.map (fun v -> Var v) vl);
          print_string ".";
          print_f_rec false false f;
        | LPrev (intv,(f,_)) ->
          print_string "PREVIOUS";
          print_interval intv; print_string " ";
          print_f_rec false false f
        | LNext (intv,(f,_)) ->
          print_string "NEXT";
          print_interval intv; print_string " ";
          print_f_rec false false f
        | LEventually (intv,(f,_)) ->
          print_string "EVENTUALLY";
          print_interval intv; print_string " ";
          print_f_rec false false f
        | LOnce (intv,(f,_)) ->
          print_string "ONCE";
          print_interval intv; print_string " ";
          print_f_rec false false f
        | LAlways (intv,(f,_)) ->
          print_string "ALWAYS";
          print_interval intv; print_string " ";
          print_f_rec false false f
        | LPastAlways (intv,(f,_)) ->
          print_string "PAST_ALWAYS";
          print_interval intv; print_string " ";
          print_f_rec false false f
        | _ ->
          if not par && not top then
            print_string "(";
          (match f with
           | LAnd ((f1,_),(f2,_)) ->
             print_f_rec false true f1;
             print_string " AND ";
             print_f_rec false false f2
           | LOr ((f1,_),(f2,_)) ->
             print_f_rec false true f1;
             print_string " OR ";
             print_f_rec false false f2
           | LSince (intv,(f1,_),(f2,_)) ->
             print_f_rec false true f1;
             print_string " SINCE";
             print_interval intv; print_string " ";
             print_f_rec false false f2
           | LUntil (intv,(f1,_),(f2,_)) ->
             print_f_rec false true f1;
             print_string " UNTIL";
             print_interval intv; print_string " ";
             print_f_rec false false f2
           | _ ->failwith "[print_formula] impossible"
          );
          if not par && not top then
            print_string ")"
       );
       if par && not top then
         print_string ")";
    );
    if top then
      print_string ")";
  in
  print_string str;
  print_f_rec true false f

let printnl_formula str f =
  print_formula str f;
  print_newline()
(* --- end of debugging code ------------------------------------------ *)

let add_labels (lf : lformula) : label list =
  let labels = ref [] in
  (* single operator rules: LFalse, LTrue *)
  (match lf with
   | LEqual (_,_)
   | LLess (_,_)
   | LLessEq (_,_) -> ()
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
    | Pred p -> LPred p
    | Neg f -> LNeg (go_down f)
    | And (f1,f2) -> LAnd ((go_down f1), (go_down f2))
    | Or (f1,f2) -> LOr ((go_down f1), (go_down f2))
    | Exists (vl,f) -> LExists (vl, (go_down f))
    | ForAll (vl,f) -> LForAll (vl, (go_down f))
    | Aggreg (y,op,x,glist,f) -> LAggreg (y,op,x,glist, go_down f)
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
  in
  let l = add_labels lf
  in
  (lf, l)

let is_filterable_empty_tp f =
  let (lf, l) = go_down f in
  (* --- debugging code ---*)
  if Misc.debugging Misc.Dbg_filter then begin
    Printf.printf "Filter_empty_tp labels: ";
    print_labels l;
    Printf.printf "\n"
  end;
  (* --- end of debugging code ---*)
  if (has_label LFalse l) && (has_label LEvRel l) then
    (* LFalse - formula is false on empty tp *)
    (* LEvRel - formula is not affected by addition/removal of empty tp *)
    true
  else
    false

let enable f =
  enabled := is_filterable_empty_tp f;
  if Misc.debugging Misc.Dbg_all then
    if !enabled then
      Printf.eprintf "[Filter_empty_tp.enable] Enabled\n"
    else
      Printf.eprintf "[Filter_empty_tp.enable] Disabled\n"

let fc_check_filterable_empty_tp f =
  let (lf, l) = go_down f in
  Printf.printf "Filter_empty_tp labels: ";
  print_labels l;
  Printf.printf "\n";
  Printf.printf "Properties: ";
  if (has_label LFalse l) && (has_label LEvRel l) then
    (* LFalse - formula is false on empty tp *)
    (* LEvRel - formula is not affected by addition/removal of empty tp *)
    Printf.printf "(filterable_empty_tp)";
  Printf.printf "\n\n";

