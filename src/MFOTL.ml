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
  | Frex of (interval * regex)
  | Prex of (interval * regex)
and regex = 
  | Wild
  | Test of formula
  | Concat of (regex * regex)
  | Plus of (regex * regex)
  | Star of regex
  


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


(** returns the list of all direct subformulas of f, ignoring the regexes *)
let rec direct_subformulas = function
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
  | Frex (intv,r) -> direct_re_subformulas r
  | Prex (intv,r) -> direct_re_subformulas r
and direct_re_subformulas = function 
  | Wild -> []
  | Test f -> [f]
  | Concat (r1,r2) 
  | Plus (r1,r2) -> (direct_re_subformulas r1) @ (direct_re_subformulas r2)
  | Star r -> (direct_re_subformulas r) 


(** returns the list of all subformulas of [f], including [f], ignoring the regexes *)
let rec subformulas f =
   f::(List.concat (List.map subformulas (direct_subformulas f)))


let predicates f = List.filter (fun x -> match x with Pred _ -> true | _ -> false) (subformulas f)

(** returns the list of all temporal subformulas of [f], ignoring regexes *)
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
  | Frex (intv,r) -> f::(temporal_re_subformulas r)
  | Prex (intv,r) -> f::(temporal_re_subformulas r)
  | _ -> List.concat (List.map temporal_subformulas (direct_subformulas f))
and temporal_re_subformulas = function
  | Wild -> []
  | Test f -> temporal_subformulas f
  | Concat (r1,r2) 
  | Plus (r1,r2) -> (temporal_re_subformulas r1) @ (temporal_re_subformulas r2)
  | Star r -> (temporal_re_subformulas r)



let is_temporal = function
  | Prev (intv,f) -> true
  | Next (intv,f) -> true
  | Since (intv,f1,f2) -> true
  | Until (intv,f1,f2) -> true
  | Eventually (intv,f) -> true
  | Once (intv,f) -> true
  | Always (intv,f) -> true
  | PastAlways (intv,f) -> true
  | Frex (intv,r) -> true
  | Prex (intv,r) -> true
  | _ -> false

let is_regular = function
  | Frex (intv,r) 
  | Prex (intv,r) -> true
  | _ -> false

let rec is_mfodl = function 
  | Equal (t1,t2) 
  | Less (t1,t2) 
  | LessEq (t1,t2) -> false
  | Pred p -> false
  | Neg f -> is_mfodl f
  | And (f1,f2) 
  | Or (f1,f2) 
  | Implies (f1,f2)
  | Equiv (f1,f2) -> is_mfodl f1 || is_mfodl f2
  | Exists (v,f) 
  | ForAll (v,f) -> is_mfodl f
  | Aggreg (_,_,_,_,f) -> is_mfodl f
  | Prev (intv,f) 
  | Next (intv,f) 
  | Eventually (intv,f) 
  | Once (intv,f)
  | Always (intv,f)
  | PastAlways (intv,f) -> is_mfodl f
  | Since (intv,f1,f2) -> is_mfodl f1 || is_mfodl f2
  | Until (intv,f1,f2) -> is_mfodl f1 || is_mfodl f2
  | Frex (intv,r) 
  | Prex (intv,r) -> true



let rec free_vars = function
  | Equal (t1,t2)
  | Less (t1,t2)
  | LessEq (t1,t2) ->
    Misc.union (Predicate.tvars t1) (Predicate.tvars t2)
  | Pred p -> Predicate.pvars p
  | Neg f -> free_vars f
  | And (f1,f2) 
  | Or (f1,f2) 
  | Implies (f1,f2) 
  | Equiv (f1,f2) -> Misc.union (free_vars f1) (free_vars f2)
  | Exists (vl,f) 
  | ForAll (vl,f) -> List.filter (fun x -> not (List.mem x vl)) (free_vars f)
  | Aggreg (y,op,x,glist,f) -> y :: glist
  | Prev (intv,f) 
  | Next (intv,f) 
  | Eventually (intv,f) 
  | Once (intv,f) 
  | Always (intv,f) 
  | PastAlways (intv,f) -> free_vars f
  | Since (intv,f1,f2) 
  | Until (intv,f1,f2) -> Misc.union (free_vars f2) (free_vars f1)
  | Frex (intv,r)
  | Prex (intv,r) -> free_re_vars r
and free_re_vars = function 
  | Wild -> []
  | Test f -> free_vars f
  | Concat (r1,r2) 
  | Plus (r1,r2) -> Misc.union (free_re_vars r1) (free_re_vars r2)
  | Star r -> (free_re_vars r)


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

let string_of_interval (a,b) =
  (match a with
    | OBnd a -> Printf.sprintf "(%.0f," a
    | CBnd a -> Printf.sprintf "[%.0f," a
    | Inf -> Printf.sprintf "(*,") 
  ^
  (match b with
  | OBnd b -> Printf.sprintf "%.0f)" b
  | CBnd b -> Printf.sprintf "%.0f]" b
  | Inf -> Printf.sprintf "*)")

let print_interval (a,b) =
  Printf.printf "%s" (string_of_interval (a,b))

let string_of_agg_op = function
  | Cnt -> "CNT"
  | Min -> "MIN"
  | Max -> "MAX"
  | Sum -> "SUM"
  | Avg -> "AVG"
  | Med -> "MED"


let rec type_of_fma = function
  | Equal (t1,t2) -> "Eq"
  | Less (t1,t2) -> "Less"
  | LessEq (t1,t2) -> "LessEq"
  | Pred p -> "Pred"
  | Neg f -> "Neg"
  | And (f1,f2) -> "And"
  | Or (f1,f2) -> "Or"
  | Implies (f1,f2) -> "Implies"
  | Equiv (f1,f2) -> "Equiv"
  | Exists (vl,f) -> "Exists"
  | ForAll (vl,f) -> "Forall"
  | Aggreg (y,op,x,glist,f) -> "Agggreg"
  | Prev (intv,f) -> "Prev"
  | Next (intv,f) -> "Next"
  | Eventually (intv,f) -> "Eventually"
  | Once (intv,f) -> "Once"
  | Always (intv,f) -> "Always"
  | PastAlways (intv,f) -> "PastAlways"
  | Since (intv,f1,f2) -> "Since"
  | Until (intv,f1,f2) -> "Unitl"
  | Frex (intv,f1) -> "Frex"
  | Prex (intv,f1) -> "Prex"

(* we always put parantheses for binary operators like "(f1 AND f2)", and around unary
ones only if they occur on the left-hand side of a binary operator: like "((NOT f1) AND f2)"*)
let string_of_formula str g =
  let rec string_f_rec top par h =
    (match h with
      | Equal (t1,t2) ->
        Predicate.string_of_term t1 ^ " = " ^ Predicate.string_of_term t2
      | Less (t1,t2) ->
        Predicate.string_of_term t1 ^ " < " ^ Predicate.string_of_term t2
      | LessEq (t1,t2) ->
        Predicate.string_of_term t1 ^ " <= " ^ Predicate.string_of_term t2
      | Pred p -> Predicate.string_of_predicate p
      | _ ->
        (if par && not top then "(" else "")
        ^ 
        (match h with
        | Neg f ->
          "NOT " ^ string_f_rec false false f

        | Exists (vl,f) ->
          "EXISTS " 
          ^ 
          (Misc.string_of_list_ext "" "" ", " Predicate.string_of_term (List.map (fun v -> Var v) vl))
          ^
          ". "
          ^
          (string_f_rec false false f)

        | ForAll (vl,f) ->
          "FORALL "
          ^
          (Misc.string_of_list_ext "" "" ", " Predicate.string_of_term (List.map (fun v -> Var v) vl))
          ^
          ". "
          ^
          (string_f_rec false false f)

        | Aggreg (y,op,x,glist,f) ->
          (Predicate.string_of_term (Var y))
          ^
          " <- "
          ^
          (string_of_agg_op op)
          ^
          " "
          ^
          (Predicate.string_of_term (Var x))
          ^
          (if glist <> [] then
              "; "
              ^
              (Misc.string_of_list_ext "" "" "," (fun z -> Predicate.string_of_term (Var z)) glist)
          else "")
          ^
          " "
          ^
          (string_f_rec false false f)

        | Prev (intv,f) ->
          "PREVIOUS"
          ^
          (string_of_interval intv)
          ^
          " "
          ^
          (string_f_rec false false f)

        | Next (intv,f) ->
          "NEXT"
          ^
          (string_of_interval intv)
          ^
          " "
          ^
          (string_f_rec false false f)

        | Eventually (intv,f) ->
          "EVENTUALLY"
          ^
          (string_of_interval intv)
          ^
          " "
          ^
          (string_f_rec false false f)

        | Once (intv,f) ->
          "ONCE"
          ^
          (string_of_interval intv)
          ^
          " "
          ^
          (string_f_rec false false f)

        | Always (intv,f) ->
          "ALWAYS"
          ^
          (string_of_interval intv)
          ^
          " "
          ^
          (string_f_rec false false f)

        | PastAlways (intv,f) ->
          "PAST_ALWAYS"
          ^
          (string_of_interval intv)
          ^
          " "
          ^
          (string_f_rec false false f)

        | Frex (intv, r) -> 
          "|>"
          ^
          (string_of_interval intv)
          ^
          (string_r_rec false false r)

        | Prex (intv, r) -> 
          "<|"
          ^
          (string_of_interval intv)
          ^
          (string_r_rec false false r)

        | _ ->
          (if not par && not top then "(" else "")
          ^
          (match h with
            | And (f1,f2) ->
              (string_f_rec false true f1)
              ^
              " AND " 
              ^
              (string_f_rec false true f2)

            | Or (f1,f2) ->
              (string_f_rec false true f1)
              ^
              " OR "
              ^
              (string_f_rec false false f2)

            | Implies (f1,f2) ->
              (string_f_rec false true f1)
              ^
              " IMPLIES "
              ^
              (string_f_rec false false f2)

            | Equiv (f1,f2) ->
              (string_f_rec false true f1)
              ^
              " EQUIV "
              ^
              (string_f_rec false false f2)

            | Since (intv,f1,f2) ->
              (string_f_rec false true f1)
              ^ 
              " SINCE"
              ^
              (string_of_interval intv)
              ^
              " "
              ^
              (string_f_rec false false f2)

            | Until (intv,f1,f2) ->
              (string_f_rec false true f1)
              ^
              " UNTIL"
              ^
              (string_of_interval intv)
              ^
              " "
              ^
              (string_f_rec false false f2)
            | _ -> failwith "[print_formula] impossible"
          )
          ^
          (if not par && not top then ")" else "")
        ) 
        ^
        (if par && not top then ")" else "")
    )
  and string_r_rec top par h = 
  (match h with
    | Wild -> "."
    | _ ->
        (if par && not top then "(" else "")
        ^ 
        (match h with
          | Test f -> 
            (string_f_rec false false f)
            ^
            "?"
          | Star r -> 
            (string_r_rec false false r)
            ^
            "*"

          | _ -> 
            (if not par && not top then "(" else "")
            ^
            (match h with
              | Concat (r1,r2) -> 
                (string_r_rec false true r1)
                ^
                " "
                ^
                (string_r_rec false false r2)

              | Plus (r1,r2) -> 
                (string_r_rec false true r1)
                ^
                " + "
                ^
                (string_r_rec false false r2)

              | _ -> failwith "[print_formula] impossible"
            )
            ^
            (if not par && not top then ")" else "")
          ) 
          ^
          (if par && not top then ")" else "")
  )
  in
  str ^ (string_f_rec true false g)

  (* Fully parenthesize an MFOTL formula *)
  let string_of_parenthesized_formula str g =
    let rec string_f_rec top par h =
      (match h with
        | Equal (t1,t2) ->
          "(" ^ (Predicate.string_of_term t1) ^ " = " ^ (Predicate.string_of_term t2) ^ ")"
        | Less (t1,t2) ->
          "(" ^ (Predicate.string_of_term t1) ^ " < " ^ (Predicate.string_of_term t2) ^ ")"
        | LessEq (t1,t2) ->
          "(" ^ (Predicate.string_of_term t1) ^ " <= " ^ (Predicate.string_of_term t2) ^ ")"
        | Pred p -> Predicate.string_of_predicate p
        | _ ->
           
          (match h with
          | Neg f ->
            "(" ^
            "NOT " ^ (string_f_rec false false f)
            ^ ")"
  
          | Exists (vl,f) ->
            "(" ^
            "EXISTS " 
            ^ 
            (Misc.string_of_list_ext "" "" ", " Predicate.string_of_term (List.map (fun v -> Var v) vl) )
            ^
            ". "
            ^
            (string_f_rec false false f)
            ^ ")"
  
          | ForAll (vl,f) ->
            "(" ^
            "FORALL "
            ^
            (Misc.string_of_list_ext "" "" ", " Predicate.string_of_term (List.map (fun v -> Var v) vl))
            ^
            ". "
            ^
            (string_f_rec false false f)
            ^ ")"
  
          | Aggreg (y,op,x,glist,f) ->
            "(" ^
            (Predicate.string_of_term (Var y))
            ^
            " <- "
            ^
            (string_of_agg_op op)
            ^
            " "
            ^
            (Predicate.string_of_term (Var x))
            ^
            (if glist <> [] then
                "; "
                ^
                (Misc.string_of_list_ext "" "" "," (fun z -> Predicate.string_of_term (Var z)) glist)
            else "")
            ^
            " "
            ^
            (string_f_rec false false f)
            ^ ")"
  
          | Prev (intv,f) ->
            "(" ^
            "PREVIOUS"
            ^
            (string_of_interval intv)
            ^
            " "
            ^
            (string_f_rec false false f)
            ^ ")"
  
          | Next (intv,f) ->
            "(" ^
            "NEXT"
            ^
            (string_of_interval intv)
            ^
            " "
            ^
            (string_f_rec false false f)
            ^ ")"
  
          | Eventually (intv,f) ->
            "(" ^
            "EVENTUALLY"
            ^
            (string_of_interval intv)
            ^
            " "
            ^
            (string_f_rec false false f)
            ^ ")"
  
          | Once (intv,f) ->
            "(" ^
            "ONCE"
            ^
            (string_of_interval intv)
            ^
            " "
            ^
            (string_f_rec false false f)
            ^ ")"
  
          | Always (intv,f) ->
            "(" ^
            "ALWAYS"
            ^
            (string_of_interval intv)
            ^
            " "
            ^
            (string_f_rec false false f)
            ^ ")"
  
          | PastAlways (intv,f) ->
            "(" ^
            "PAST_ALWAYS"
            ^
            (string_of_interval intv)
            ^
            " "
            ^
            (string_f_rec false false f)
            ^ ")"

          | Frex (intv, r) -> 
            "(" ^
            "|>"
            ^
            (string_of_interval intv)
            ^
            (string_r_rec false false r)
            ^ ")"

          | Prex (intv, r) -> 
            "(" ^
            "<|"
            ^
            (string_of_interval intv)
            ^
            (string_r_rec false false r)
            ^ ")"
            
          | _ ->
 
            (match h with
              | And (f1,f2) ->
                "(" ^
                (string_f_rec false true f1)
                ^
                " AND " 
                ^
                (string_f_rec false true f2)
                ^ ")"
  
              | Or (f1,f2) ->
                "(" ^
                (string_f_rec false true f1)
                ^
                " OR "
                ^
                (string_f_rec false false f2)
                ^ ")"
  
              | Implies (f1,f2) ->
                "(" ^
                (string_f_rec false true f1)
                ^
                " IMPLIES "
                ^
                (string_f_rec false false f2)
                ^ ")"
  
              | Equiv (f1,f2) ->
                "(" ^
                (string_f_rec false true f1)
                ^
                " EQUIV "
                ^
                (string_f_rec false false f2)
                ^ ")"
  
              | Since (intv,f1,f2) ->
                "(" ^
                (string_f_rec false true f1)
                ^ 
                " SINCE"
                ^
                (string_of_interval intv)
                ^
                " "
                ^
                (string_f_rec false false f2)
                ^ ")"
  
              | Until (intv,f1,f2) ->
                "(" ^
                (string_f_rec false true f1)
                ^
                " UNTIL"
                ^
                (string_of_interval intv)
                ^
                " "
                ^
                (string_f_rec false false f2)
                ^ ")"
              | _ -> failwith "[print_formula] impossible"
            )
            
          ) 
      )
      and string_r_rec top par h = 
      (match h with
        | Wild -> "(" ^ "." ^ ")"
        | _ ->
            (match h with
              | Test f -> 
                "(" ^
                (string_f_rec false false f)
                ^
                "?"
                ^ ")"

              | Star r -> 
                "(" ^
                (string_r_rec false false r)
                ^
                "*"
                ^ ")"
    
              | _ -> 
                (match h with
                  | Concat (r1,r2) -> 
                    "(" ^
                    (string_r_rec false true r1)
                    ^
                    " "
                    ^
                    (string_r_rec false false r2)
                    ^ ")"
    
                  | Plus (r1,r2) -> 
                    "(" ^
                    (string_r_rec false true r1)
                    ^
                    " + "
                    ^
                    (string_r_rec false false r2)
                    ^ ")"
    
                  | _ -> failwith "[print_formula] impossible"
                )
          )
      )
      in
    str ^ (string_f_rec true false g)

let print_formula str f =
  print_string (string_of_formula str f)

let printnl_formula str f =
  print_formula str f;
  print_newline()
