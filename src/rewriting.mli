(*
 * This file is part of MONPOLY.
 *
 * Copyright (C) 2011 Nokia Corporation and/or its subsidiary(-ies).
 * Contact:  Nokia Corporation (Debmalya Biswas: debmalya.biswas@nokia.com)
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



(** This module provides rewriting operations on MFOTL formulas.

    We follow here the procedure described in Samuel Mueller's PhD
    thesis "Theory and Applications of Runtime Monitoring Metric
    First-order Temporal Logic", Section 5.3 "Syntactical
    Approximation \[of the class of TSF domain independent formulas\]
    based on Rewriting".

*)

open Predicate
open MFOTL
open Db

type expand_mode = ExpandAll | ExpandNonshared

val no_rw: bool ref
val unfold_let: expand_mode option ref
  (** Flags corresponding to the command-line options -no_rw and -unfold_let. *)

val is_special_case: (var list) -> formula -> bool
(** Returns [true] if the formula does not need to be evaluated
    independently. *)

val is_monitorable: formula -> bool * (formula * string) option

val check_formula: schema -> formula -> bool * formula * (var * tcst) list
(** Returns [true, pf, vtypes] if the formula is monitorable by our
    implementation, where [pf] is a formula equivalent with input
    formula and [vtypes] is the list of free variables of [pf]
    together with their types *)

val check_syntax: schema -> formula -> ((var * tcst) list  * formula)

val check_let: formula -> bool

val expand_let: expand_mode -> formula -> formula

val is_future: formula -> bool
(** Returns [true] if formula contains future operators *)
