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

(* This file is a modification of queue.mli from OCaml's standard
 * library, which had the following copyright:
 *)
(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)


(** First-in first-out queues.

   This module implements queues (FIFOs), with in-place modification.
*)

type 'a t
(** The type of queues containing elements of type ['a]. *)


exception Empty
(** Raised when {!Queue.take} or {!Queue.peek} is applied to an empty queue. *)


val create : unit -> 'a t
(** Return a new queue, initially empty. *)

val add : 'a -> 'a t -> unit
(** [add x q] adds the element [x] at the end of the queue [q]. *)

val push : 'a -> 'a t -> unit
(** [push] is a synonym for [add]. *)

val take : 'a t -> 'a
(** [take q] removes and returns the first element in queue [q],
   or raises [Empty] if the queue is empty. *)

val pop : 'a t -> 'a
(** [pop] is a synonym for [take]. *)

val peek : 'a t -> 'a
(** [peek q] returns the first element in queue [q], without removing
   it from the queue, or raises [Empty] if the queue is empty. *)

val top : 'a t -> 'a
(** [top] is a synonym for [peek]. *)

val get_last : 'a t -> 'a
(** [get_last q] returns the last element in queue [q], without removing
   it from the queue, or raises [Empty] if the queue is empty. *)

val clear : 'a t -> unit
(** Discard all elements from a queue. *)

val copy : 'a t -> 'a t
(** Return a copy of the given queue. *)

val is_empty : 'a t -> bool
(** Return [true] if the given queue is empty, [false] otherwise. *)

val length : 'a t -> int
(** Return the number of elements in a queue. *)

val iter : ('a -> unit) -> 'a t -> unit
(** [iter f q] applies [f] in turn to all elements of [q],
   from the least recently entered to the most recently entered.
   The queue itself is unchanged. *)

val iter_while : ('a -> unit) -> ('a -> bool) -> 'a t -> unit
(** [iter f stop q] applies [f] in turn to elements of [q], from the
    least recently entered to the most recently entered, as long as
    the current element satisfies [cond]; that is, the iteration stops
    on the first element which does not satisfy [cond]. The queue
    itself is unchanged. *)

val update : ('a -> 'a) -> 'a t -> unit
(** [update f q] applies [f] in turn to all elements of [q],
    from the least recently entered to the most recently entered.
    The queue is changed. *)

val update_last : 'a -> 'a t -> unit
(** [update_last x q] replaces the last element of [q] by [x]. *)

val update_and_delete : ('a -> 'a) -> ('a -> bool) -> 'a t -> unit
(** [update f cond_del q] applies [f] in turn to all elements of [q],
    from the least recently entered to the most recently entered.  It
    deletes the current element when [cond_del (f c)] is satisfied,
    where [c] is the contents of the current element.  The queue is
    changed. *)

val fold : ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b
  (** [fold f accu q] is equivalent to [List.fold_left f accu l],
      where [l] is the list of [q]'s elements. The queue remains
      unchanged. *)

val transfer : 'a t -> 'a t -> unit
(** [transfer q1 q2] adds all of [q1]'s elements at the end of
   the queue [q2], then clears [q1]. It is equivalent to the
   sequence [iter (fun x -> add x q2) q1; clear q1], but runs
   in constant time. *)
