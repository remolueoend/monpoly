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



open Predicate
open MFOTL
open Table

(* A database schema is a set of relation schemas. *)

type schema = Table.schema list

let base_schema =
  [("tp", ["i", TInt]);
   ("ts", ["t", TInt]);
   ("tpts", [("i", TInt); ("t", TInt)]);]

let add_predicate p l s =
  if List.mem_assoc p s
  then failwith (Printf.sprintf "[Db.add_predicate] Predicate %s was defined\
    \ more than once in the signature." p)
  else
    begin
      (*TODO(JS): Do this more cleanly.*)
      Domain_set.predicates := Domain_set.convert_predicate (p, l)
        :: !Domain_set.predicates;
      (p, l)::s
    end

type db = table list

type log = (timestamp * db) list

let get_table db p =
  List.find (fun t ->
      let (name,_) = Table.get_schema t in
      (Predicate.get_name p) = name
    ) db


let make_db db = db

let get_tables db = db

let add_table db t = t::db

let rec dump_db = function
  | [] -> ()
  | t::db ->
    Table.dump_table t;
    dump_db db

let is_empty = function
  | [] -> true
  | _ -> false
