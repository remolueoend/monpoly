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



(** This module defines MFOTL formulas; it also defines timestamps,
    intervals, and interval bounds.
*)

open Predicate


type timestamp = Z.t
(** The type of timestamps. *)

type tsdiff = Z.t
  (** The type of differences between timestamps. Only used for
  clarity reasons in the types of some functions in other
  modules. *)

val unixts: bool ref
  (** [true] if timestamps represent Unix times *)

(** The type of interval bounds. *)
type bound =
  | OBnd of tsdiff (** opened bound *)
  | CBnd of tsdiff (** closed bound *)
  | Inf (** no bound *)

(** The type of intervals. *)
type interval = bound * bound

(** The type of aggregation operators. *)
type agg_op = Cnt | Min | Max | Sum | Avg | Med

(** The type of MFOTL formulas. *)
type formula =
  | Equal of (term * term)
  | Less of (term * term)
  | LessEq of (term * term)
  | Substring of (term * term)
  | Matches of (term * term * term option list)
  | Pred of predicate
  | Let of (predicate * formula * formula)
  | LetPast of (predicate * formula * formula)
  | Neg of formula
  | And of (formula * formula)
  | Or of (formula * formula)
  | Implies of (formula * formula)
  | Equiv of (formula * formula)
  | Exists of (var list * formula)
  | ForAll of (var list * formula)
  | Aggreg of (tsymb * var * agg_op * var * var list * formula)
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

(** Operations on timestamps: *)

val ts_null: timestamp
(* TODO: Timestamps are unbounded. ts_max is therefore an arbitrary (large)
   value. We should avoid using it. *)
val ts_max: timestamp
val ts_invalid: timestamp
val ts_plus: tsdiff -> tsdiff -> tsdiff
val ts_minus: timestamp -> timestamp -> tsdiff


(** Checking interval membership of timestamp (differences): *)

val in_left_ext: tsdiff -> interval -> bool
val in_right_ext: tsdiff -> interval -> bool
val in_interval: tsdiff -> interval -> bool

val infinite_interval: interval -> bool
val init_interval: interval -> interval


(** Default values for aggregations on empty sets: *)
val aggreg_default_value: agg_op -> tcst -> cst


(** Operations on formulas: *)

val map: (formula -> formula) -> (regex -> regex) -> formula -> formula

val direct_subformulas: formula -> formula list
  (** [direct_subformulas f] returns the list of all direct subformulas of [f]; hence not 
       all subformulas of [f], and not including [f]. Regexes are ignored *)

val temporal_subformulas: formula -> formula list
  (** [temporal_subformulas f] returns the list of all temporal subformulas of
      [f], ignoring regexes *)

val is_temporal: formula -> bool
  (** [is_temporal f] returns [true] if the main connective of [f] is
      temporal. *)

val is_mfodl: formula -> bool
  (** [is_mfodl f] returns [true] if the formula contains future or past match operators *)

val free_vars: formula -> var list
  (** [free_vars f] returns the list of free variables of [f]. *)

val fresh_var_mapping: string list -> var list -> string list * (var * string) list

val substitute_vars: (Predicate.var * Predicate.var Predicate.eterm) list -> formula -> formula
 (** [substitute_vars m f] is a capture avoiding substitution f[m]  *)

val count_pred_uses: Predicate.predicate -> formula -> int
  (** [count_pred_uses p f] counts how often the predicate [p] is used within [f] *)

(** Conversion functions: *)

val ts_of_string: string -> timestamp

(** Pretty-printing functions: *)

val string_of_ts: timestamp -> string
val print_ts: timestamp -> unit
val prerr_ts: timestamp -> unit
val string_of_interval: interval -> string
val print_interval: interval -> unit
val prerr_interval: interval -> unit
val string_of_agg_op: agg_op -> string
val string_of_formula: string -> formula -> string
val print_formula: string -> formula -> unit
val printnl_formula: string -> formula -> unit
val prerr_formula: string -> formula -> unit
val prerrnl_formula: string -> formula -> unit
val string_of_parenthesized_formula: string -> formula -> string
