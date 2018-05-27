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


type timestamp = float
(** The type of timestamps. *)

type tsdiff = float
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


(** Operations on timestamps: *)

val ts_null: timestamp
val ts_max: timestamp
val ts_invalid: timestamp
val ts_plus: tsdiff -> tsdiff -> tsdiff
val ts_minus: timestamp -> timestamp -> tsdiff


(** Checking interval memebrship of timestamp (differences): *)

val in_left_ext: tsdiff -> interval -> bool
val in_right_ext: tsdiff -> interval -> bool
val in_interval: tsdiff -> interval -> bool



(** Operations on formulas: *)

val direct_subformulas: formula -> formula list
  (** [direct_subformulas f] returns the list of all direct subformulas of [f]; hence not the
      of all subformulas of [f], and not including [f]. *)

val is_temporal: formula -> bool
  (** [is_temporal f] returns [true] if the main connective of [f] is
      temporal. *)

val free_vars: formula -> var list
  (** [free_vars f] returns the list of free variables of [f]. *)


(** Conversion functions: *)

val ts_of_string: string -> string -> timestamp
val cst_of_tsdiff: tsdiff -> cst
val tsdiff_of_cst: cst -> tsdiff
val string_of_agg_op: agg_op -> string

(** Pretty-printing functions: *)

val string_of_ts: timestamp -> string
val print_ts: timestamp -> unit
val print_interval: interval -> unit
val print_formula: string -> formula -> unit
val printnl_formula: string -> formula -> unit
