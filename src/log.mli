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


(** This module is an interface to the log parser. *)

open MFOTL
open Helper
open Db
open Log_parser

val log_open : string -> Lexing.lexbuf
(** [log_open f] opens file [f] and returns the initial state of the
    corresponding log scanner. *)

val get_signature_string : string -> schema
(** [get_signature s] returns the schema defined in the signature string
    [s]. *)

val get_signature : string -> schema
(** [get_signature f] returns the schema defined in the signature file
    [f]. *)

val get_next_entry : Lexing.lexbuf -> monpoly_feed
(** [get_next_entry lexbuf] reads the current entry in the log file
    corresponding to the scanner [lexbuf]. It returns [None] when the
    end of the log is reached. *)

val tp : int ref
val skipped_tps : int ref
val last : bool ref
