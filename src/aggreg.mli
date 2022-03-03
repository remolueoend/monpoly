(*
 * This file is part of MONPOLY.
 *
 * Copyright (C) 2021 ETH Zurich.
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

type result = {empty_rel: bool; rel: Relation.relation}

type aggregator = Relation.relation -> result

val cnt: Predicate.cst -> int -> int list -> aggregator
val min: Predicate.cst -> int -> int -> int list -> aggregator
val max: Predicate.cst -> int -> int -> int list -> aggregator
val sum: Predicate.cst -> int -> int -> int list -> aggregator
val avg: Predicate.cst -> int -> int -> int list -> aggregator
val med: Predicate.cst -> int -> int -> int list -> aggregator

class type once_aggregator =
  object
    method update: MFOTL.timestamp -> Relation.relation -> unit
    method get_result: result
  end

val cnt_once: Predicate.cst -> MFOTL.interval -> int -> int list ->
  once_aggregator

val min_once: Predicate.cst -> MFOTL.interval -> int -> int -> int list ->
  once_aggregator

val max_once: Predicate.cst -> MFOTL.interval -> int -> int -> int list ->
  once_aggregator

val sum_once: Predicate.cst -> MFOTL.interval -> int -> int -> int list ->
  once_aggregator

val avg_once: Predicate.cst -> MFOTL.interval -> int -> int -> int list ->
  once_aggregator

val med_once: Predicate.cst -> MFOTL.interval -> int -> int -> int list ->
  once_aggregator

val prerr_state: once_aggregator -> unit
