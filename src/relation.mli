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



(**
    This module defines relations and provides operations over them.

    Relations are sets of tuples of the same length. Currently,
    relations are implemented using the
    {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.html}Set}
    module from the standard library. (The ordering of tuples is given
    by the {!Tuple.compare} function, hence it's lexicographic.)

    This module has an unnamed perspective of relations. Hence,
    columns are identified by their position (from 0 to the number of
    columns minus 1). On the contrary, the {!module:Table} module has
    a named perspective and therein columns are identified by
    attributes.
*)

open Tuple
open Predicate




type relation
  (** The type of relations. *)




val make_relation: tuple list -> relation
  (** Builds a relation from a list of tuples. *)


val map: (tuple -> tuple) -> relation -> relation
  (** [map f rel] returns the relation formed by those tuples [f t]
      with [t] in [rel]. *)

val is_empty: relation -> bool
  (** [is_empty rel] returns true if the relation is empty (has no tuples). *)


val natural_join: (int * int) list -> relation -> relation -> relation
  (** [natural_join matches rel1 rel2] returns the natural join of
      relations [rel1] and [rel2]. The parameter [matches] gives the
      columns which should match in the two relations in form of a
      list of tuples [(pos2,pos1)]: column [pos2] in [rel2] should
      match column [pos1] in [rel1].
  *)

val nested_loop_join: (int * int) list -> relation -> relation -> relation
val hash_join_with_cards: (int * int) list -> int -> relation ->
  int -> relation -> relation

val natural_join_sc1: (int * int) list -> relation -> relation -> relation
(** [natural_join] special case 1: attr1 are included in attr2 *)

val natural_join_sc2: (int * int) list -> relation -> relation -> relation
(** [natural_join] special case 2: attr2 are included in attr1 *)

val cross_product: relation -> relation -> relation
  (** The cross product of the arguments. *)

val minus: int list -> relation -> relation -> relation
  (** [reldiff rel1 rel2] returns the set difference between [rel1]
      and the the natural join of [rel1] and [rel2]. *)

val reorder: int list -> relation -> relation

val project_away: int list -> relation -> relation
  (** [project_away posl rel] removes the columns in [posl] from
      [rel]. *)

val eval_pred: predicate -> (relation -> relation)
(* val selectp: predicate -> relation -> relation *)
  (** [satisfiesp p rel] returns the set of tuples from [rel] which
      satisfy predicate [p].  *)

val eval_equal: term -> term -> relation
val eval_not_equal: term -> term -> relation







(** Inherited from
    {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.Make.html}Set.Make} (with [elt=Tuple.tuple]): *)

(* TODO: Think about restricting some of these? *)
val empty : relation (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALempty}Set.S.empty} *)
val is_empty : relation -> bool (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALis_empty}Set.S.is_empty} *)
val mem : tuple -> relation -> bool (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALmem}Set.S.mem} *)
val add : tuple -> relation -> relation (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALadd}Set.S.add} *)
val singleton : tuple -> relation (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALsingleton}Set.S.singleton} *)
val remove : tuple -> relation -> relation (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALremove}Set.S.remove} *)
val union : relation -> relation -> relation (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALunion}Set.S.union} *)
val inter : relation -> relation -> relation (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALinter}Set.S.inter} *)
val diff : relation -> relation -> relation (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALdiff}Set.S.diff} *)
val compare : relation -> relation -> int (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALcompare}Set.S.compare} *)
val equal : relation -> relation -> bool (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALequal}Set.S.equal} *)
val subset : relation -> relation -> bool (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALsubset}Set.S.subset} *)
val iter : (tuple -> unit) -> relation -> unit (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALiter}Set.S.iter} *)
val fold : (tuple -> 'a -> 'a) -> relation -> 'a -> 'a (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALfold}Set.S.fold} *)
val for_all : (tuple -> bool) -> relation -> bool (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALfor_all}Set.S.for_all} *)
val exists : (tuple -> bool) -> relation -> bool (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALexists}Set.S.exists} *)
val filter : (tuple -> bool) -> relation -> relation (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALfilter}Set.S.filter} *)
val partition : (tuple -> bool) -> relation -> relation * relation (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALpartition}Set.S.partition} *)
val cardinal : relation -> int (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALcardinal}Set.S.cardinal} *)
val elements : relation -> tuple list (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALelements}Set.S.elements} *)
val min_elt : relation -> tuple (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALmin_elt}Set.S.min_elt} *)
val max_elt : relation -> tuple (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALmax_elt}Set.S.max_elt} *)
val choose : relation -> tuple (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALchoose}Set.S.choose} *)
val split : tuple -> relation -> relation * bool * relation (** see {{:http://caml.inria.fr/pub/docs/manual-ocaml/libref/Set.S.html#VALsplit}Set.S.split} *)





(** Pretty-printing functions: *)

(* val output_rel4: out_channel -> string -> relation -> unit *)

val print_rel: string -> relation -> unit
val print_rel4: string -> relation -> unit
val print_reln: string -> relation -> unit
val print_bigrel: relation -> unit
val print_orel: relation option -> unit
val prerr_rel: string -> relation -> unit
val prerr_reln: string -> relation -> unit
