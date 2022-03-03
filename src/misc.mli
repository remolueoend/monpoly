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



(** This module defines miscellaneous helper functions for other
    modules.
*)

open Dllist

(** Type for identifying which debugging information should be ouput,
    if any. *)
type dbg =
  | Dbg_all
  | Dbg_eval
  | Dbg_monitorable
  | Dbg_log
  | Dbg_perf
  | Dbg_filter
  | Dbg_parsing
  | Dbg_typing

val usr2: bool ref
val alrm: bool ref
  (** Flags used when measuring performance *)

val verbose: bool ref
val checkf: bool ref
val verified: bool ref
val new_last_ts: bool ref
val ignore_parse_errors: bool ref
val stop_at_out_of_order_ts: bool ref
val stop_at_first_viol: bool ref
  (** Flags corresponding to the command-line options: -verbose, -check,
      -verified, -no_new_last_ts, -ignore_errors, -stop_at_out_of_order_ts,
      -stop_at_last_viol. *)

val str_cache: bool ref
  (** Flag corresponding to the -strcache option. *)

val split_debug: string -> unit
(** [split_debug str] parses the string [str] into a list of debugging
    units used when calling {!debugging}. *)

val debugging: dbg -> bool
(** [debugging d] returns [true] if debugging is activated for
    the debuggin unit [d]. *)



val map_interval: (int -> 'a) -> int -> int -> 'a list
  (** [map_interval f m n] returns the list [[f m; f (m+1); ...; f n]]. *)

val median: 'a list -> int -> ('a -> 'a -> 'a) -> 'a
(** [median l len f] returns the median of the list [l], where [len]
    is the length of the list and [f] is a binary function which is
    applied to the "middle" elments of [l] when [len] is even. *)

val elim_elem: 'a -> 'a  list -> 'a list
val add_in_sorted: 'a -> 'a list -> 'a list


val union: 'a list -> 'a list -> 'a list
(** [append2 l1 l2] appends the elements of [l2] not in [l1] to
    [l1]. The order of elements in [l1] and [l2] is preserved. *)

val diff: 'a list -> 'a list -> 'a list
  (** [diff l1 l2] returns the elements in [l1] which are not in
      [l2]. The order of elements in [l1] is preserved. *)

val inter: 'a list -> 'a list -> 'a list
  (** [inter l1 l2] returns the elements in [l1] which are also in
      [l2]. The order of elements in [l1] is preserved. *)

val subset: 'a list -> 'a list -> bool
  (** [subset l1 l2] tests whether the list [l1] (seen as a set) is a
      subset of the list [l2] (seen as a set). *)

val conjunction: bool list -> bool
  (** [conjunction [b1; ...; bn]]  is equivalent with [b1 && ... && bn]. *)


val contains_duplicates: 'a list -> bool
  (** [duplicates_exists l] checks whether [l] contains duplicates
      (elements which appears twice in the list) *)

val remove_duplicates: 'a list -> 'a list
  (** [remove_duplicates l] removes duplicates from [l]. The order of
      elements in [l] is preserved. *)


val sublists: 'a list -> int list -> 'a list list
  (** [sublists l lenl] returns a list of lists [l'] which when
      appended form [l], and whose lengths are equal with the elements
      of [lenl] respectively (that is, [List.map List.length l' =
      lenl]).

      For instance, [get_sublists [0;3;1] [a;b;c;d] =
      [[];[a;b;c];[d]]].
  *)


val get_last: 'a list -> 'a
  (** [get_last l] returns the last element of [l]. *)

val split_at_last: 'a list -> 'a list * 'a
  (** [split_at_last (l@[a]) = (l,a)]. Raises an exception if the
      input list is empty. *)

val split_at_lastbutone: 'a list -> 'a list * 'a * 'a
  (** [split_at_lastbutone (l@[a;b]) = (l,a,b)]. Raises an exception
      if the length of the input list is less than two. *)


val get_pos: 'a -> 'a list -> int
  (** [get_pos pos l] returns the elements at position [pos] in
      [l]. *)

val get_pos_no_e: 'a -> 'a list -> int
(** [get_pos pos l] returns the elements at position [pos] in
    [l]. without throwing an exception *)


val remove_positions: int list -> 'a list -> 'a list
  (** [remove_positions posl l] removes the elements at positions in
      [posl] from the list [l]. The order of elements in [l] is
      preserved. *)

val get_positions: int list -> 'a list -> 'a list
  (** [get_positions posl l] keeps only the elements at positions in
      [posl] from the list [l]. The order of elements in [l] is
      preserved. *)

val zip: 'a list -> 'b list -> ('a * 'b) list
  (** [zip l1 l2] creates a list of pair of elements of l1 l2, positionwise.Algorithm
      The length of the resulting list is the minimum of the lengths of lists l1 and l2
  *)

val replace: ('a * 'a) list -> 'a list -> 'a list

(** Pretty-printing functions: *)

val print_spaces: int -> unit

val string_of_list_ext: string -> string -> string -> ('a -> string) -> 'a list -> string
val string_of_list: ('a -> string) -> 'a list -> string
val string_of_list2: ('a -> string) -> 'a list -> string
val string_of_list3: ('a -> string) -> 'a list -> string
val string_of_list4: ('a -> string) -> 'a list -> string

val output_list_ext: out_channel -> string -> string -> string -> (out_channel -> 'a -> unit) -> 'a list -> unit
val print_list_ext: string -> string -> string -> ('a -> unit) -> 'a list -> unit

val output_list: out_channel -> (out_channel -> 'a -> unit) -> 'a list -> unit
val output_list4: out_channel -> (out_channel -> 'a -> unit) -> 'a list -> unit
val print_list: ('a -> unit) -> 'a list -> unit
val print_list2: ('a -> unit) -> 'a list -> unit
val print_list3: ('a -> unit) -> 'a list -> unit
val print_list4: ('a -> unit) -> 'a list -> unit
val printnl_list: string -> ('a -> unit) -> 'a list -> unit
val prerr_list: ('a -> unit) -> 'a list -> unit
val prerrnl_list: string -> ('a -> unit) -> 'a list -> unit

val print_queue: ('a -> unit) -> 'a Queue.t -> unit
val print_mqueue: ('a -> unit) -> 'a Mqueue.t -> unit
val prerr_queue: ('a -> unit) -> 'a Queue.t -> unit
val prerr_mqueue: ('a -> unit) -> 'a Mqueue.t -> unit


(** Functions for reporting memory consumption: *)

val mem_current: unit -> string
val mem_max: unit -> string
val mem_all: unit -> unit

val nsplit: string -> string -> string list
