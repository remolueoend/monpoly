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



(** This module defines tuples and provides operations over them.

    Tuples are sequences of values (constants) from the domain.  A
    position in a tuple is an index in the sequence, starting with 0.
*)

open Predicate
open MFOTL



type tuple = cst list
  (** Tuples are currently implemented as lists of constants
      (see {!type:Predicate.cst}). *)

val compare: tuple -> tuple -> int
  (** [compare x y] returns [0] if [x] is equal to [y], a negative
      integer if [x] is less than [y], and a positive integer if [x]
      is greater than [y]. It is currently an alias to
      {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Stdlib.html}Stdlib.compare},
      hence it using the lexicographic ordering. *)

exception Type_error of string

val make_tuple: cst list -> tuple
  (** [make_tuple] builds a tuple from a list of constants. *)

val make_tuple2: string list -> (string * tcst) list -> tuple
(** [make_tuple] builds a tuple from a list of strings and a list of
    tuple types. *)

val get_constants: tuple -> cst list


val get_at_pos: tuple -> int -> cst
(** [get_at_pos pos t] returns the value at position [pos] in [t] *)

val add_first: tuple -> cst -> tuple
  (** [add_first t v] builds a new tuple by adding the value [v] at the
      beginning of [t] *)

val insert: int -> tuple -> cst -> tuple
(** [insert pos t v] builds a new tuple by inserting the value [v] at position
    [pos] in [t] *)

(* val duplicate_pos: int -> tuple -> tuple *)
(*   (\** [duplicate_pos pos t] builds a new tuple by adding the value at *)
(*       position [pos] in [t] to the end of [t]. *\) *)



val projections: int list -> tuple -> tuple
(** [projections posl t] builds a new tuple by keeping from [t] only
    the values at positions in the [posl] list (the order of the
    remaining values is preserved). *)

val project_away: int list -> tuple -> tuple
(** [project_away posl t] builds a new tuple by removing from [t] the
    values at positions in the [posl] list (the order of the remaining
    values is preserved). *)


val satisfiesp: term list -> tuple -> bool * tuple
  (** [satisfiesp p t] returns [(true,t')] if the tuple [t] satisfies
      the predicate [p], and [(false,[])] otherwise. In the former
      case, [t'] consists of the values assigned to the variables in
      [p], in the order these variables appear therein.

      For instance, [satisfies p t] where [p] represents the formula
      [P(x,"b",y,x)] returns [(true;["a";"c"])] for
      [t=["a";"b";"c";"a"]], and [(false,[])] for
      [t=["a";"b";"c";"d"]].
  *)

(* val satisfiesf1: (cst -> bool) -> int -> tuple -> bool *)
(*   (\** [satisfiesf1 f pos t] returns [f v] where [v] is the value at *)
(*       position [pos] in [t]. *\) *)

(* val satisfiesf2: (cst -> cst -> bool) -> int -> int -> tuple -> bool *)
(*   (\** [satisfiesf1 f pos1 pos2 t] returns [f v1 v2] where [v1] and *)
(*       [v2] are the values at positions [pos1] and respectively [pos2] *)
(*       in [t]. *\) *)


val get_filter: (var list) -> formula -> tuple -> bool
val get_tf: (var list) -> formula -> tuple -> tuple option


exception Not_joinable
  (** [Not_joinable] is raised when two tuples are not joinable (see
      {!Tuple.join}). *)

val join: (int * cst) list -> tuple -> tuple -> tuple
  (** [join posvall t1 t2] builds a new tuple by joining the tuples
      [t1] and [t2]. The list [posvall] consists of pairs of positions
      and values, indicating what the values at the corresponding
      positions in [t2] should be. In other words, if [(pos,val)]
      appears in [posvall], then [t2] should have value [val] at
      position [pos]. If this is not the case then the {!Not_joinable}
      exception is raised. The result is obtained by prepending [t1] to
      the what remains of [t2] after ignoring the values at the
      positions appearing in [posvall].
      (The list of positions in [posvall] is assumed to be ordered
      ascendingly.)

      For instance, for [posvall = [(0,"b");(1,"c");(3,"a")]],
      [t1=["a";"c";"b"]], and [t2 = ["b";"c";"d";"a"]], the result is
      [["a";"c";"b";"d"]].
  *)

val join_unchecked: (int * int) list -> tuple -> tuple -> tuple

(** Pretty-printing functions: *)

val string_of_tuple: tuple -> string
(* val output_tuple: out_channel -> tuple -> unit *)
val print_tuple: tuple -> unit
val prerr_tuple: tuple -> unit
