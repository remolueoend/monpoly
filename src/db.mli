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



(** This modules defines databases and logs. *)

open Predicate
open MFOTL
open Table


type schema = Table.schema list
    (** A databases schema is a set of table schemas. *)

val base_schema: schema
val add_predicate: string -> (string * tcst) list -> schema -> schema

type db
  (** A database consists of a set of tables. (It is currently
      implemented as a list of tables.) *)


type log = (timestamp * db) list
    (** A log represents a temporal structure. It consists of a list
  of timestamped databases (with the same schema). *)

val get_table: db -> predicate -> table
  (** [get_table db p] returns the table in [db] with the same name as
      the predicate [p]. Raises [Not_found] if no such table exists. *)

val make_db: table list -> db
  (** [make db tbl] builds a database from the list of tables
      [tbl]. *)

val get_tables: db -> table list
  (** [get_table db] returns the list of tables in [db] *)

val add_table: db -> table -> db
  (** [add_table db tb] adds table [tb] to the database [db]. *)

val dump_db: db -> unit
  (** [print_db db] prints all tables in database [db]. *)

val is_empty: db -> bool
  (** [is_empty db] returns true if database [db] is empty. *)
