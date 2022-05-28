(* This module implements data structures and function to parse, typecheck and compile extended MFOTL formulas. *)

open Predicate

type cst =
  | Int of Z.t
  | Str of string
  | Float of float
  (* (string used to produce the regexp, the compiled regexp) because Str library doesn't provide regexp to string functionality *)
  | Regexp of (string * Str.regexp)

type tcst = Signature_ast.ty

type tcl = TNum | TAny | TPartial of (var * tsymb) list
and tsymb = TSymb of (tcl * int) | TCst of tcst | TBot

(** Γ *)
type symbol_table = (cplx_term * tsymb) list

(** Δ *)
and predicate_schema = ((var * int) * tsymb list) list

(** T *)
and type_context = (var * (bool * (var * tcst) list)) list

and context = predicate_schema * type_context * symbol_table

and 'a cplx_eterm =
  | Var of 'a
  | Cst of cst
  | F2i of 'a cplx_eterm
  | I2f of 'a cplx_eterm
  | I2s of 'a cplx_eterm
  | S2i of 'a cplx_eterm
  | F2s of 'a cplx_eterm
  | S2f of 'a cplx_eterm
  | DayOfMonth of 'a cplx_eterm
  | Month of 'a cplx_eterm
  | Year of 'a cplx_eterm
  | FormatDate of 'a cplx_eterm
  | R2s of 'a cplx_eterm
  | S2r of 'a cplx_eterm
  | Plus of 'a cplx_eterm * 'a cplx_eterm
  | Minus of 'a cplx_eterm * 'a cplx_eterm
  | UMinus of 'a cplx_eterm
  | Mult of 'a cplx_eterm * 'a cplx_eterm
  | Div of 'a cplx_eterm * 'a cplx_eterm
  | Mod of 'a cplx_eterm * 'a cplx_eterm
  | Proj of 'a cplx_eterm * string

and cplx_term = var cplx_eterm

type cplx_predicate = var * int * cplx_term list

type cplx_formula =
  | Equal of (cplx_term * cplx_term)
  | Less of (cplx_term * cplx_term)
  | LessEq of (cplx_term * cplx_term)
  | Substring of (cplx_term * cplx_term)
  | Matches of (cplx_term * cplx_term * cplx_term option list)
  | Pred of cplx_predicate
  | Let of (cplx_predicate * cplx_formula * cplx_formula)
  | LetPast of (cplx_predicate * cplx_formula * cplx_formula)
  | Neg of cplx_formula
  | And of (cplx_formula * cplx_formula)
  | Or of (cplx_formula * cplx_formula)
  | Implies of (cplx_formula * cplx_formula)
  | Equiv of (cplx_formula * cplx_formula)
  | Exists of (var list * cplx_formula)
  | ForAll of (var list * cplx_formula)
  | Aggreg of
      (tsymb * var * MFOTL.agg_op * cplx_term * cplx_term list * cplx_formula)
  | Prev of (MFOTL.interval * cplx_formula)
  | Next of (MFOTL.interval * cplx_formula)
  | Eventually of (MFOTL.interval * cplx_formula)
  | Once of (MFOTL.interval * cplx_formula)
  | Always of (MFOTL.interval * cplx_formula)
  | PastAlways of (MFOTL.interval * cplx_formula)
  | Since of (MFOTL.interval * cplx_formula * cplx_formula)
  | Until of (MFOTL.interval * cplx_formula * cplx_formula)
  | Frex of (MFOTL.interval * regex)
  | Prex of (MFOTL.interval * regex)

and regex =
  | Wild
  | Test of cplx_formula
  | Concat of (regex * regex)
  | Plus of (regex * regex)
  | Star of regex

val compile_tcst : tcst -> Predicate.tcst
val get_predicate_args : cplx_predicate -> cplx_term list

val typecheck_formula :
  Signature_ast.signatures -> cplx_formula -> context * cplx_formula * bool
(** type checks a complex formula given matching signature definitions.
    Returns a triple consiting of:
    1) The type checking context consisting of predicate schema, symbol table and type context.
    2) A possibly updated version of the input formula.
    3) A boolean flag indicating the monitorability (safety) of the input formula. *)

val compile_formula :
  Signature_ast.signatures -> cplx_formula -> MFOTL.formula * bool
(** compiles a MFOTL formula from a complex formula and the parsed signature definitions.
    Returns the compiled formula and a flag indicating the monitoriability of the formula. *)
