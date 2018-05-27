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
open Relation

(* A table schema consists of a name and of a name and a type for each column *)
type schema = var * (string * tcst) list

type table = schema * relation


let get_schema (s,rel) = s

let get_relation (s,rel) = rel

let make_schema n a = (n,a)

let make_table s r = (s,r)

let empty_table s =
  (s,Relation.empty)


let get_matches attr1 attr2 =
  let rec matches crtpos = function
    | x::t ->
      (try
         let pos1 = Misc.get_pos x attr1 in
         (crtpos,pos1)::(matches (crtpos+1) t)
       with Not_found ->
         matches (crtpos+1) t
      )
    | [] -> []
  in
  matches 0 attr2


let print_schema str (name, attr_list) =
  print_string str;
  Predicate.print_var name;
  Misc.print_list
    (fun (v, t) ->
       print_string (v ^ ":");
       Predicate.print_tcst t
    )
    attr_list

let print_table (s,rel) =
  print_schema "" s;
  print_newline();
  Relation.print_bigrel rel;
  print_newline()

let dump_table (s,rel) =
  let name,_ = s in
  print_string name;
  Relation.print_rel4 " " rel;
  print_newline()





