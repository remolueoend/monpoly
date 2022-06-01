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

(** This module contains helper function for performance
    evaluation. *)

open MFOTL

val show_results: int -> MFOTL.timestamp -> unit
val check_log: int -> MFOTL.timestamp -> unit
val check_log_end: int -> MFOTL.timestamp -> unit
val dump_stats: float -> unit

val add_profile_group: int -> string -> unit
val begin_profile: unit -> unit
val profile_enter: int -> unit
val profile_exit: int -> 'a -> 'a
val end_profile: unit -> unit

(* New profiling infrastructure *)

(* Timestamps: *)
val tag_enter_main_loop: int
val tag_exit_main_loop: int
val tag_enter_read_tp: int
val tag_exit_read_tp: int
val tag_enter_eval_root: int
val tag_exit_eval_root: int
val tag_enter_compute: int  (* loc = extformula node *)
val tag_exit_compute: int  (* loc = extformula node *)

(* Integer data: *)
val tag_log_tp: int
val tag_eval_index: int  (* loc = extformula node *)
val tag_eval_size: int  (* loc = extformula node *)

(* String data: *)
val tag_extformula: int

val profile_enabled: bool ref
val enable_profile: string -> unit
val finalize_profile: unit -> unit
val profile_int: int -> int -> int -> unit
val profile_time: int -> int -> unit
val profile_string: int -> string -> unit
