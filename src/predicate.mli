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



(** This module defines variables, constants, terms, and predicates. *)


(** The type of variable and predicate names. They are represented by
    strings. *)
type var = string


(** Constants are nonnegative integers or strings. *)
type cst =
  | Int of Z.t
  | Str of string
  | Float of float
  | Regexp of (string * Str.regexp)

(** Three (constant) types are supported: integers, strings and floats *)
type tcst = TInt | TStr | TFloat | TRegexp

(** Two type classes exists: Numeric and Any*) 
type tcl = TNum | TAny 
(** Type can be a symbolic type (from one of the two supported classes) or a constant type *) 
type tsymb = TSymb of (tcl * int) | TCst of tcst


(** A term is either a variable or a constant. *)
type 'a eterm =
  | Var of 'a
  | Cst of cst
  | F2i of 'a eterm
  | I2f of 'a eterm
  | I2s of 'a eterm
  | S2i of 'a eterm
  | F2s of 'a eterm
  | S2f of 'a eterm
  | DayOfMonth of 'a eterm
  | Month of 'a eterm
  | Year of 'a eterm
  | FormatDate of 'a eterm
  | R2s of 'a eterm
  | S2r of 'a eterm
  | Plus of 'a eterm * 'a eterm
  | Minus of 'a eterm * 'a eterm
  | UMinus of 'a eterm
  | Mult of 'a eterm * 'a eterm
  | Div of 'a eterm * 'a eterm
  | Mod of 'a eterm * 'a eterm

type term = var eterm

val substitute_vars: ('a * 'a eterm) list -> 'a eterm -> 'a eterm

val eval_eterm: ('a -> cst) -> 'a eterm -> cst
val eval_term: (var * cst) list -> term -> cst
val eval_gterm: term -> cst

val plus: cst -> cst -> cst
val minus: cst -> cst -> cst
val average: cst -> cst -> cst

val cst_eq: cst -> cst -> bool

val float_of_cst: cst -> float

(** A predicate consists of a name and a list of term arguments. It is
    thus an atomic formula. *)
type predicate = var * int * term list

val cst_of_str: tcst -> string -> cst
(** Converts a string to a cst given its type *)

(** Converts a string to a cst by trying conversion to float, int, string until no exception is thrown *)
val cst_of_str_basic: string -> cst

val make_predicate: var * term list -> predicate
  (** [make_predicate n args] creates a predicate with name [n] and
      arguments [args]. *)


val get_info: predicate -> var * int * term list
  (** [get_info p] returns the name of predicate [p], its arity, and
  its arguments *)

val get_name: predicate -> var
  (** [get_name p] returns the name of predicate [p] *)

val get_args: predicate -> term list
(** [get_args p] returns the arguments of predicate [p] *)


val tvars: term -> var list
(** [tvars t] returns [[v]] if the term [t] is the variable [v], and
    the empty list if [t] is a constant. *)

val pvars: predicate -> var list
  (** [pvars p] returns the list of variable arguments of predicate [p]
      (their order is preserved). *)


val cst_smaller: cst -> cst -> bool
(** [cst_smaller c c'] returns true iff [c<c'], where [<] is the
    built-in OCaml comparison function. [cst_smaller] fails if the two
    constants are not of the same type. *)

val type_of_cst: cst -> tcst
(** [type_of_cst c] returns the type of constant [c]. *)

val int_of_cst: cst -> int
(** Conversion from constants of integer type to integers. *)

(** Pretty-printing functions: *)

val print_var: var -> unit
val print_tcst: tcst -> unit
val string_of_var: var -> string
val string_of_cst: cst -> string
val print_cst: cst -> unit
val prerr_cst: cst -> unit
(* val output_cst: out_channel -> cst -> unit *)
val string_of_term: term -> string
val print_term: term -> unit
val string_of_predicate: predicate -> string
val print_predicate: predicate -> unit
val prerr_predicate: predicate -> unit
val print_vartypes_list: (var * tcst) list -> unit
