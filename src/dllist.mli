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

(* The implementation of some of the functions in this file are based
 * on queue.ml from OCaml's standard library, which had the following
 * copyright:
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


(** This module implements doubly linked lists. *)

type 'a cell
type 'a dllist

exception End_of_dllist


val void: 'a cell

(* list creation *)
val empty: unit -> 'a dllist
val singleton: 'a -> 'a dllist

val is_empty: 'a dllist -> bool
val length: 'a dllist -> int

val get_first: 'a dllist -> 'a
val get_last: 'a dllist -> 'a

val get_first_cell: 'a dllist -> 'a cell
val get_last_cell: 'a dllist -> 'a cell
val get_next: 'a dllist -> 'a cell -> 'a cell
val get_prev: 'a dllist -> 'a cell -> 'a cell
val get_data: 'a cell -> 'a
val get_index: 'a cell -> 'a dllist -> int
val get_cell_at_index: int -> 'a dllist -> 'a cell

val is_first: 'a dllist -> 'a cell -> bool
val is_last: 'a dllist -> 'a cell -> bool


val pop_first: 'a dllist -> 'a
val pop_last: 'a dllist -> 'a

val add_first: 'a -> 'a dllist -> unit
val add_last: 'a -> 'a dllist -> unit

val clear: 'a dllist -> unit

(* iterate from head to tail *)
val iter: ('a -> unit) -> 'a dllist -> unit

val iterrev_cond_delete : ('a -> bool) -> ('a -> unit) -> ('a -> bool) -> 'a dllist -> unit

val to_array: 'a dllist -> 'a array
val from_array: 'a array -> 'a dllist

val new_cell: 'a -> 'a dllist -> 'a cell
