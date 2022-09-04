(* This module implements data structures and function to parse, typecheck and compile extended MFOTL formulas. *)

open Predicate

(** constant types *)
type tcst = Signature_ast.ty

(** type classes *)
type tcl = TNum | TAny | TOrd | TRecord of (string * ty) list

(** usually the type of a term: either a symbolic or constant type *)
and ty = TSymb of (tcl * int) | TCst of tcst | TNever

(** represents a single custom product sort *)
type sort = {inline: bool; fields: (string * tcst) list}

(** Γ: symbol table *)
type symbol_table = (string * ty ref) list

and cst_bool = True | False

(** constant terms *)
and cst =
  | Int of Z.t
  | Str of string
  | Float of float
  (* (string used to produce the regexp, the compiled regexp) because Str library doesn't provide regexp to string functionality *)
  | Regexp of (string * Str.regexp)
  | Record of (string * (string * cplx_term) list)
  | Bool of cst_bool
  | Null

(** Δ: predicate schema *)
and predicate_schema = ((string * int) * ty ref list) list

(** T: custom sorts (=types)  *)
and custom_sorts = (var * sort) list

and cplx_term =
  | Var of var
  | Cst of cst
  | F2i of cplx_term
  | I2f of cplx_term
  | I2s of cplx_term
  | S2i of cplx_term
  | F2s of cplx_term
  | S2f of cplx_term
  | R2s of cplx_term
  | S2r of cplx_term
  | DayOfMonth of cplx_term
  | Month of cplx_term
  | Year of cplx_term
  | FormatDate of cplx_term
  | Plus of cplx_term * cplx_term
  | Minus of cplx_term * cplx_term
  | UMinus of cplx_term
  | Mult of cplx_term * cplx_term
  | Div of cplx_term * cplx_term
  | Mod of cplx_term * cplx_term
  | Proj of cplx_term * string

(** Stores the inferred type information per subformula *)
and type_context =
  { predicates: predicate_schema
  ; sorts: custom_sorts
  ; vars: symbol_table
  ; new_type_symbol: tcl -> ty }

type cplx_predicate = var * int * cplx_term list

(** A formula consists of an annotation and its AST *)
type 'a cplx_formula = 'a * 'a formula_ast

and 'a formula_ast =
  | Equal of (cplx_term * cplx_term)
  | Less of (cplx_term * cplx_term)
  | LessEq of (cplx_term * cplx_term)
  | Substring of (cplx_term * cplx_term)
  | Matches of (cplx_term * cplx_term * cplx_term option list)
  | Pred of cplx_predicate
  | Let of (cplx_predicate * 'a cplx_formula * 'a cplx_formula)
  | LetPast of (cplx_predicate * 'a cplx_formula * 'a cplx_formula)
  | Neg of 'a cplx_formula
  | And of ('a cplx_formula * 'a cplx_formula)
  | Or of ('a cplx_formula * 'a cplx_formula)
  | Implies of ('a cplx_formula * 'a cplx_formula)
  | Equiv of ('a cplx_formula * 'a cplx_formula)
  | Exists of (var list * 'a cplx_formula)
  | ForAll of (var list * 'a cplx_formula)
  | Aggreg of (var * MFOTL.agg_op * var * var list * 'a cplx_formula)
  | Prev of (MFOTL.interval * 'a cplx_formula)
  | Next of (MFOTL.interval * 'a cplx_formula)
  | Eventually of (MFOTL.interval * 'a cplx_formula)
  | Once of (MFOTL.interval * 'a cplx_formula)
  | Always of (MFOTL.interval * 'a cplx_formula)
  | PastAlways of (MFOTL.interval * 'a cplx_formula)
  | Since of (MFOTL.interval * 'a cplx_formula * 'a cplx_formula)
  | Until of (MFOTL.interval * 'a cplx_formula * 'a cplx_formula)
  | Frex of (MFOTL.interval * 'a regex)
  | Prex of (MFOTL.interval * 'a regex)

and 'a regex =
  | Wild
  | Test of 'a cplx_formula
  | Concat of ('a regex * 'a regex)
  | Plus of ('a regex * 'a regex)
  | Star of 'a regex

val compile_tcst : tcst -> Predicate.tcst
(** compiles a constant CMFOLD type to a constant MFOLD type. *)

val get_predicate_args : cplx_predicate -> cplx_term list
(** returns the complex-typed arguments of the given predicate. *)

val typecheck_formula :
  Signature_ast.signatures -> unit cplx_formula -> type_context cplx_formula
(** Transforms an non-annotated formula to a formula annotated with type information, stored in a type_context instance. *)

val compile_formula :
  Signature_ast.signatures -> type_context cplx_formula -> MFOTL.formula
(** Transforms a given CMFOLD formula to a MFOLD formula. *)

val print_formula_details : type_context cplx_formula -> MFOTL.formula -> unit
(** Pretty-prints some basic information about the given MFODL formula to stdout. *)

(** Module responsible for validating and reporting monitorability checks. *)
module Monitorability : sig
  val is_monitorable :
    type_context cplx_formula -> bool * (type_context cplx_formula * var) option
  (** returns whether the given formula is monitorable. Returns a verdict plus an optional reason in case of rejection. *)

  val print_results :
    MFOTL.formula -> bool * ('a cplx_formula * var) option -> unit
  (** Pretty-prints the rejection reason of a monitorability check to stdout. *)
end