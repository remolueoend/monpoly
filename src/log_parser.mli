(*
 * This file is part of MONPOLY.
 *
 * Copyright (C) 2021 ETH Zurich.
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

val parse_signature: string -> Db.schema
val parse_signature_file: string -> Db.schema

exception Stop_parser

module type Consumer = sig
  type t
  val begin_tp: t -> MFOTL.timestamp -> unit
  val tuple: t -> Table.schema -> string list -> unit
  val end_tp: t -> unit
  val command: t -> string -> Helper.commandParameter option -> unit
  val end_log: t -> unit
  val parse_error: t -> Lexing.position -> string -> unit
end

(*TODO(JS): move to Misc*)
val string_of_position: Lexing.position -> string

module Make(C: Consumer): sig
  val parse: Db.schema -> Lexing.lexbuf -> C.t -> bool
  val parse_file: Db.schema -> string -> C.t -> bool
end
