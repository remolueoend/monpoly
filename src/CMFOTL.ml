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

open Unix
open Predicate

type cst =
  | Int of Z.t
  | Str of string
  | Float of float
  (* (string used to produce the regexp, the compiled regexp) because Str library doesn't provide regexp to string functionality *)
  | Regexp of (string * Str.regexp)
  (* reference to another instance encoded as an integer *)
  | Ref of int

type tcst = TInt | TStr | TFloat | TRegexp | TRef of string

type tcl = TNum | TAny | TRecord of (var * tsymb) list
and tsymb = TSymb of (tcl * int) | TCst of tcst | TBot

type table_schema = var * (string * tcst) list
type db_schema = table_schema list

let type_of_cst = function
  | Int _ -> TInt
  | Str _ -> TStr
  | Float _ -> TFloat
  | Regexp _ -> TRegexp
  (* TODO: what should be the ctor name? *)
  | Ref _ -> TRef "void"

type 'a cplx_eterm =
  | Var of 'a
  | Cst of cst
  | F2i of 'a cplx_eterm
  | I2f of 'a cplx_eterm
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

type cplx_term = var cplx_eterm

(* predicate = name, arity, and list of arguments *)
type cplx_predicate = var * int * cplx_term list

let get_predicate_args ((name, ar, args) : cplx_predicate) = args

let pvars (p : cplx_predicate) =
  let rec get_vars assign res args =
    match args with
    | [] -> List.rev res
    | term :: args' -> (
      match term with
      | Var x -> (
        try
          let _ = List.assoc x assign in
          get_vars assign res args'
        with Not_found -> get_vars ((x, ()) :: assign) (x :: res) args' )
      | _ -> get_vars assign res args' ) in
  get_vars [] [] (get_predicate_args p)

let rec tvars = function
  | Var v -> [v]
  | Cst c -> []
  | F2i t
   |I2f t
   |DayOfMonth t
   |Month t
   |Year t
   |FormatDate t
   |UMinus t
   |R2s t
   |S2r t ->
      tvars t
  | Plus (t1, t2) | Minus (t1, t2) | Mult (t1, t2) | Div (t1, t2) | Mod (t1, t2)
    ->
      tvars t1 @ tvars t2
  | Proj (t1, _) -> tvars t1

type cplx_formula =
  | Equal of (cplx_term * cplx_term)
  | Less of (cplx_term * cplx_term)
  | LessEq of (cplx_term * cplx_term)
  | Substring of (cplx_term * cplx_term)
  | Matches of (cplx_term * cplx_term)
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
  | Aggreg of (tsymb * var * MFOTL.agg_op * var * var list * cplx_formula)
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

let unixts = ref false

let rec free_vars = function
  | Equal (t1, t2)
   |Less (t1, t2)
   |LessEq (t1, t2)
   |Matches (t1, t2)
   |Substring (t1, t2) ->
      Misc.union (tvars t1) (tvars t2)
  | Pred p -> pvars p
  | Let (_, _, f) -> free_vars f
  | LetPast (_, _, f) -> free_vars f
  | Neg f -> free_vars f
  | And (f1, f2) | Or (f1, f2) | Implies (f1, f2) | Equiv (f1, f2) ->
      Misc.union (free_vars f1) (free_vars f2)
  | Exists (vl, f) | ForAll (vl, f) ->
      List.filter (fun x -> not (List.mem x vl)) (free_vars f)
  | Aggreg (rty, y, op, x, glist, f) -> y :: glist
  | Prev (intv, f)
   |Next (intv, f)
   |Eventually (intv, f)
   |Once (intv, f)
   |Always (intv, f)
   |PastAlways (intv, f) ->
      free_vars f
  | Since (intv, f1, f2) | Until (intv, f1, f2) ->
      Misc.union (free_vars f2) (free_vars f1)
  | Frex (intv, r) | Prex (intv, r) -> free_re_vars r

and free_re_vars = function
  | Wild -> []
  | Test f -> free_vars f
  | Concat (r1, r2) | Plus (r1, r2) ->
      Misc.union (free_re_vars r1) (free_re_vars r2)
  | Star r -> free_re_vars r

let rec is_mfodl = function
  | Equal (t1, t2)
   |Less (t1, t2)
   |LessEq (t1, t2)
   |Substring (t1, t2)
   |Matches (t1, t2) ->
      false
  | Pred p -> false
  | Let (_, f1, f2) -> is_mfodl f1 || is_mfodl f2
  | LetPast (_, f1, f2) -> is_mfodl f1 || is_mfodl f2
  | Neg f -> is_mfodl f
  | And (f1, f2) | Or (f1, f2) | Implies (f1, f2) | Equiv (f1, f2) ->
      is_mfodl f1 || is_mfodl f2
  | Exists (v, f) | ForAll (v, f) -> is_mfodl f
  | Aggreg (_, _, _, _, _, f) -> is_mfodl f
  | Prev (intv, f)
   |Next (intv, f)
   |Eventually (intv, f)
   |Once (intv, f)
   |Always (intv, f)
   |PastAlways (intv, f) ->
      is_mfodl f
  | Since (intv, f1, f2) -> is_mfodl f1 || is_mfodl f2
  | Until (intv, f1, f2) -> is_mfodl f1 || is_mfodl f2
  | Frex (intv, r) | Prex (intv, r) -> true

(* STRING FUNCTIONS *)
let rec string_of_tcst = function
  | TFloat -> "TFloat"
  | TInt -> "TInt"
  | TStr -> "TStr"
  | TRegexp -> "TRegexp"
  | TRef _ -> "TRef"

let rec string_of_cst c =
  let format_string s =
    if s = "" then "\"\""
    else if s.[0] = '\"' && s.[String.length s - 1] = '\"' then s
    else "\"" ^ s ^ "\"" in
  match c with
  | Int i -> Z.to_string i
  | Float f -> Printf.sprintf "%g" f
  | Str s -> format_string s
  | Regexp (p, _) -> Printf.sprintf "r%s" (format_string p)
  | Ref ref -> Printf.sprintf "ref[%i]" ref

let rec string_of_term term =
  let add_paren str = "(" ^ str ^ ")" in
  let rec t2s b term =
    let b', str =
      match term with
      | Var v -> (true, v)
      | Cst c -> (true, string_of_cst c)
      | F2i t -> (false, "f2i(" ^ t2s true t ^ ")")
      | I2f t -> (false, "i2f(" ^ t2s true t ^ ")")
      | R2s t -> (false, "r2s(" ^ t2s true t ^ ")")
      | S2r t -> (false, "s2r(" ^ t2s true t ^ ")")
      | Year t -> (false, "YEAR(" ^ t2s true t ^ ")")
      | Month t -> (false, "MONTH(" ^ t2s true t ^ ")")
      | DayOfMonth t -> (false, "DAY_OF_MONTH(" ^ t2s true t ^ ")")
      | FormatDate t -> (false, "FORMAT_DATE(" ^ t2s true t ^ ")")
      | UMinus t -> (false, "-" ^ t2s' t)
      | Plus (t1, t2) -> (false, t2s' t1 ^ " + " ^ t2s' t2)
      | Minus (t1, t2) -> (false, t2s' t1 ^ " - " ^ t2s' t2)
      | Mult (t1, t2) -> (false, t2s' t1 ^ " * " ^ t2s' t2)
      | Div (t1, t2) -> (false, t2s' t1 ^ " / " ^ t2s' t2)
      | Mod (t1, t2) -> (false, t2s' t1 ^ " mod " ^ t2s' t2)
      | Proj (t1, f) -> (false, Printf.sprintf "%s[%s]" (string_of_term t1) f)
    in
    (* we don't add parentheses for the top-most operator, nor around
       constants and variables *)
    if b || b' then str else add_paren str
  and t2s' term = t2s false term in
  t2s true term

let string_of_predicate (p, ar, args) =
  string_of_var p ^ Misc.string_of_list string_of_term args

(* we always put parantheses for binary operators like "(f1 AND f2)", and around unary
   ones only if they occur on the left-hand side of a binary operator: like "((NOT f1) AND f2)"*)
let string_of_formula str g =
  let pps = String.split_on_char '\n' str in
  let padding =
    if pps == [] then ""
    else String.map (fun s -> ' ') (List.nth pps (List.length pps - 1)) in
  let rec string_f_rec top par h =
    match h with
    | Equal (t1, t2) -> string_of_term t1 ^ " = " ^ string_of_term t2
    | Less (t1, t2) -> string_of_term t1 ^ " < " ^ string_of_term t2
    | LessEq (t1, t2) -> string_of_term t1 ^ " <= " ^ string_of_term t2
    | Substring (t1, t2) ->
        string_of_term t1 ^ " SUBSTRING " ^ string_of_term t2
    | Matches (t1, t2) -> string_of_term t1 ^ " MATCHES " ^ string_of_term t2
    | Pred p -> string_of_predicate p
    | _ ->
        (if par && not top then "(" else "")
        ^ ( match h with
          | Neg f -> "NOT " ^ string_f_rec false false f
          | Exists (vl, f) ->
              "EXISTS "
              ^ Misc.string_of_list_ext "" "" ", " string_of_term
                  (List.map (fun v -> Var v) vl)
              ^ ". " ^ string_f_rec false false f
          | ForAll (vl, f) ->
              "FORALL "
              ^ Misc.string_of_list_ext "" "" ", " string_of_term
                  (List.map (fun v -> Var v) vl)
              ^ ". " ^ string_f_rec false false f
          | Aggreg (rty, y, op, x, glist, f) ->
              string_of_term (Var y) ^ " <- " ^ MFOTL.string_of_agg_op op ^ " "
              ^ string_of_term (Var x)
              ^ ( if glist <> [] then
                  "; "
                  ^ Misc.string_of_list_ext "" "" ","
                      (fun z -> string_of_term (Var z))
                      glist
                else "" )
              ^ " " ^ string_f_rec false false f
          | Prev (intv, f) ->
              "PREVIOUS"
              ^ MFOTL.string_of_interval intv
              ^ " " ^ string_f_rec false false f
          | Next (intv, f) ->
              "NEXT"
              ^ MFOTL.string_of_interval intv
              ^ " " ^ string_f_rec false false f
          | Eventually (intv, f) ->
              "EVENTUALLY"
              ^ MFOTL.string_of_interval intv
              ^ " " ^ string_f_rec false false f
          | Once (intv, f) ->
              "ONCE"
              ^ MFOTL.string_of_interval intv
              ^ " " ^ string_f_rec false false f
          | Always (intv, f) ->
              "ALWAYS"
              ^ MFOTL.string_of_interval intv
              ^ " " ^ string_f_rec false false f
          | PastAlways (intv, f) ->
              "PAST_ALWAYS"
              ^ MFOTL.string_of_interval intv
              ^ " " ^ string_f_rec false false f
          | Frex (intv, r) ->
              "|>" ^ MFOTL.string_of_interval intv ^ string_r_rec false false r
          | Prex (intv, r) ->
              "<|" ^ MFOTL.string_of_interval intv ^ string_r_rec false false r
          | _ ->
              (if (not par) && not top then "(" else "")
              ^ ( match h with
                | And (f1, f2) ->
                    string_f_rec false true f1 ^ " AND "
                    ^ string_f_rec false true f2
                | Or (f1, f2) ->
                    string_f_rec false true f1 ^ " OR "
                    ^ string_f_rec false false f2
                | Implies (f1, f2) ->
                    string_f_rec false true f1 ^ " IMPLIES "
                    ^ string_f_rec false false f2
                | Equiv (f1, f2) ->
                    string_f_rec false true f1 ^ " EQUIV "
                    ^ string_f_rec false false f2
                | Let (p, f1, f2) ->
                    "LET" ^ " "
                    ^ string_f_rec false true (Pred p)
                    ^ " = " ^ string_f_rec false true f1 ^ "\n" ^ padding ^ "IN"
                    ^ " "
                    ^ string_f_rec false false f2
                | LetPast (p, f1, f2) ->
                    "LETPAST" ^ " "
                    ^ string_f_rec false true (Pred p)
                    ^ " = " ^ string_f_rec false true f1 ^ "\n" ^ padding ^ "IN"
                    ^ " "
                    ^ string_f_rec false false f2
                | Since (intv, f1, f2) ->
                    string_f_rec false true f1 ^ " SINCE"
                    ^ MFOTL.string_of_interval intv
                    ^ " "
                    ^ string_f_rec false false f2
                | Until (intv, f1, f2) ->
                    string_f_rec false true f1 ^ " UNTIL"
                    ^ MFOTL.string_of_interval intv
                    ^ " "
                    ^ string_f_rec false false f2
                | _ -> failwith "[print_formula] impossible" )
              ^ if (not par) && not top then ")" else "" )
        ^ if par && not top then ")" else ""
  and string_r_rec top par h =
    match h with
    | Wild -> "."
    | _ ->
        (if par && not top then "(" else "")
        ^ ( match h with
          | Test f -> string_f_rec false false f ^ "?"
          | Star r -> string_r_rec false false r ^ "*"
          | _ ->
              (if (not par) && not top then "(" else "")
              ^ ( match h with
                | Concat (r1, r2) ->
                    string_r_rec false true r1 ^ " "
                    ^ string_r_rec false false r2
                | Plus (r1, r2) ->
                    string_r_rec false true r1 ^ " + "
                    ^ string_r_rec false false r2
                | _ -> failwith "[print_formula] impossible" )
              ^ if (not par) && not top then ")" else "" )
        ^ if par && not top then ")" else "" in
  str ^ string_f_rec true false g

(* Fully parenthesize an MFOTL formula *)
let string_of_parenthesized_formula str g =
  let pps = String.split_on_char '\n' str in
  let padding =
    if pps == [] then ""
    else String.map (fun s -> ' ') (List.nth pps (List.length pps - 1)) in
  let rec string_f_rec top par h =
    match h with
    | Equal (t1, t2) ->
        "(" ^ string_of_term t1 ^ " = " ^ string_of_term t2 ^ ")"
    | Less (t1, t2) -> "(" ^ string_of_term t1 ^ " < " ^ string_of_term t2 ^ ")"
    | LessEq (t1, t2) ->
        "(" ^ string_of_term t1 ^ " <= " ^ string_of_term t2 ^ ")"
    | Substring (t1, t2) ->
        "(" ^ string_of_term t1 ^ " SUBSTRING " ^ string_of_term t2 ^ ")"
    | Matches (t1, t2) ->
        "(" ^ string_of_term t1 ^ " MATCHES " ^ string_of_term t2 ^ ")"
    | Pred p -> string_of_predicate p
    | _ -> (
      match h with
      | Neg f -> "(" ^ "NOT " ^ string_f_rec false false f ^ ")"
      | Exists (vl, f) ->
          "(" ^ "EXISTS "
          ^ Misc.string_of_list_ext "" "" ", " string_of_term
              (List.map (fun v -> Var v) vl)
          ^ ". " ^ string_f_rec false false f ^ ")"
      | ForAll (vl, f) ->
          "(" ^ "FORALL "
          ^ Misc.string_of_list_ext "" "" ", " string_of_term
              (List.map (fun v -> Var v) vl)
          ^ ". " ^ string_f_rec false false f ^ ")"
      | Aggreg (rty, y, op, x, glist, f) ->
          "(" ^ string_of_term (Var y) ^ " <- " ^ MFOTL.string_of_agg_op op
          ^ " " ^ string_of_term (Var x)
          ^ ( if glist <> [] then
              "; "
              ^ Misc.string_of_list_ext "" "" ","
                  (fun z -> string_of_term (Var z))
                  glist
            else "" )
          ^ " " ^ string_f_rec false false f ^ ")"
      | Prev (intv, f) ->
          "(" ^ "PREVIOUS"
          ^ MFOTL.string_of_interval intv
          ^ " " ^ string_f_rec false false f ^ ")"
      | Next (intv, f) ->
          "(" ^ "NEXT"
          ^ MFOTL.string_of_interval intv
          ^ " " ^ string_f_rec false false f ^ ")"
      | Eventually (intv, f) ->
          "(" ^ "EVENTUALLY"
          ^ MFOTL.string_of_interval intv
          ^ " " ^ string_f_rec false false f ^ ")"
      | Once (intv, f) ->
          "(" ^ "ONCE"
          ^ MFOTL.string_of_interval intv
          ^ " " ^ string_f_rec false false f ^ ")"
      | Always (intv, f) ->
          "(" ^ "ALWAYS"
          ^ MFOTL.string_of_interval intv
          ^ " " ^ string_f_rec false false f ^ ")"
      | PastAlways (intv, f) ->
          "(" ^ "PAST_ALWAYS"
          ^ MFOTL.string_of_interval intv
          ^ " " ^ string_f_rec false false f ^ ")"
      | Frex (intv, r) ->
          "(" ^ "|>"
          ^ MFOTL.string_of_interval intv
          ^ string_r_rec false false r ^ ")"
      | Prex (intv, r) ->
          "(" ^ "<|"
          ^ MFOTL.string_of_interval intv
          ^ string_r_rec false false r ^ ")"
      | _ -> (
        match h with
        | And (f1, f2) ->
            "(" ^ string_f_rec false true f1 ^ " AND "
            ^ string_f_rec false true f2 ^ ")"
        | Or (f1, f2) ->
            "(" ^ string_f_rec false true f1 ^ " OR "
            ^ string_f_rec false false f2
            ^ ")"
        | Implies (f1, f2) ->
            "(" ^ string_f_rec false true f1 ^ " IMPLIES "
            ^ string_f_rec false false f2
            ^ ")"
        | Equiv (f1, f2) ->
            "(" ^ string_f_rec false true f1 ^ " EQUIV "
            ^ string_f_rec false false f2
            ^ ")"
        | Let (p, f1, f2) ->
            "(" ^ "LET" ^ " "
            ^ string_f_rec false true (Pred p)
            ^ " = " ^ string_f_rec false true f1 ^ "\n" ^ padding ^ "IN" ^ " "
            ^ string_f_rec false false f2
            ^ ")"
        | Since (intv, f1, f2) ->
            "(" ^ string_f_rec false true f1 ^ " SINCE"
            ^ MFOTL.string_of_interval intv
            ^ " "
            ^ string_f_rec false false f2
            ^ ")"
        | Until (intv, f1, f2) ->
            "(" ^ string_f_rec false true f1 ^ " UNTIL"
            ^ MFOTL.string_of_interval intv
            ^ " "
            ^ string_f_rec false false f2
            ^ ")"
        | _ -> failwith "[print_formula] impossible" ) )
  and string_r_rec top par h =
    match h with
    | Wild -> "(" ^ "." ^ ")"
    | _ -> (
      match h with
      | Test f -> "(" ^ string_f_rec false false f ^ "?" ^ ")"
      | Star r -> "(" ^ string_r_rec false false r ^ "*" ^ ")"
      | _ -> (
        match h with
        | Concat (r1, r2) ->
            "(" ^ string_r_rec false true r1 ^ " "
            ^ string_r_rec false false r2
            ^ ")"
        | Plus (r1, r2) ->
            "(" ^ string_r_rec false true r1 ^ " + "
            ^ string_r_rec false false r2
            ^ ")"
        | _ -> failwith "[print_formula] impossible" ) ) in
  str ^ string_f_rec true false g

(* TYPE CHECKING *)
let rec check_let = function
  | Let (p, f1, f2) ->
      let n, a, ts = p in
      let check_params =
        List.for_all (fun t -> match t with Var _ -> true | _ -> false) ts in
      if not check_params then
        let string_of_terms =
          List.fold_left (fun s v -> s ^ " " ^ string_of_term v) "" in
        let str =
          Printf.sprintf
            "[Rewriting.check_let] LET %s's parameters %s must be variables" n
            (string_of_terms ts) in
        failwith str
      else () ;
      let prms = List.flatten (List.map tvars ts) in
      let fv1 = free_vars f1 in
      if List.length fv1 != a then
        let str =
          Printf.sprintf
            "[Rewriting.check_let] LET %s's arity %n must match the number of \
             free variables of %s "
            n a (string_of_formula "" f1) in
        failwith str
      else () ;
      if not (Misc.subset fv1 prms && Misc.subset prms fv1) then
        let string_of_vars =
          List.fold_left (fun s v -> s ^ " " ^ string_of_var v) "" in
        let str =
          Printf.sprintf
            "[Rewriting.check_let] LET %s's parameters %s do not coincide with \
             free variables %s of %s"
            n (string_of_vars prms) (string_of_vars fv1)
            (string_of_formula "" f1) in
        failwith str
      else () ;
      check_let f1 && check_let f2
  | LetPast (p, f1, f2) ->
      let n, a, ts = p in
      let check_params =
        List.for_all (fun t -> match t with Var _ -> true | _ -> false) ts in
      if not check_params then
        let string_of_terms =
          List.fold_left (fun s v -> s ^ " " ^ string_of_term v) "" in
        let str =
          Printf.sprintf
            "[Rewriting.check_let] LETPAST %s's parameters %s must be variables"
            n (string_of_terms ts) in
        failwith str
      else () ;
      let prms = List.flatten (List.map tvars ts) in
      let fv1 = free_vars f1 in
      if List.length fv1 != a then
        let str =
          Printf.sprintf
            "[Rewriting.check_let] LETPAST %s's arity %n must match the number \
             of free variables of %s "
            n a (string_of_formula "" f1) in
        failwith str
      else () ;
      if not (Misc.subset fv1 prms && Misc.subset prms fv1) then
        let string_of_vars =
          List.fold_left (fun s v -> s ^ " " ^ string_of_var v) "" in
        let str =
          Printf.sprintf
            "[Rewriting.check_let] LetPast %s's parameters %s do not coincide \
             with free variables %s of %s"
            n (string_of_vars prms) (string_of_vars fv1)
            (string_of_formula "" f1) in
        failwith str
      else () ;
      check_let f1 && check_let f2
  | Equal _ | Less _ | LessEq _ | Pred _ | Substring _ | Matches _ -> true
  | Neg f
   |Exists (_, f)
   |ForAll (_, f)
   |Aggreg (_, _, _, _, _, f)
   |Prev (_, f)
   |Once (_, f)
   |PastAlways (_, f)
   |Next (_, f)
   |Always (_, f)
   |Eventually (_, f) ->
      check_let f
  | Prex (_, r) | Frex (_, r) -> check_re_let r
  | And (f1, f2)
   |Or (f1, f2)
   |Implies (f1, f2)
   |Equiv (f1, f2)
   |Since (_, f1, f2)
   |Until (_, f1, f2) ->
      check_let f1 && check_let f2

and check_re_let = function
  | Wild -> true
  | Test f -> check_let f
  | Concat (r1, r2) | Plus (r1, r2) -> check_re_let r1 && check_re_let r2
  | Star r -> check_re_let r

let rec check_intervals =
  let check_interval intv =
    let check_bound b =
      match b with MFOTL.OBnd a | CBnd a -> Z.(a >= zero) | _ -> true in
    let check_lb_ub lb ub =
      match (lb, ub) with
      | MFOTL.Inf, _ -> false
      | CBnd a, MFOTL.CBnd b -> a <= b
      | CBnd a, OBnd b | OBnd a, CBnd b | OBnd a, OBnd b -> a < b
      | (_ as l), Inf -> l <> Inf in
    let lb, ub = intv in
    check_bound lb && check_bound ub && check_lb_ub lb ub in
  function
  | Equal _ | Less _ | LessEq _ | Pred _ | Substring _ | Matches _ -> true
  | Neg f | Exists (_, f) | ForAll (_, f) | Aggreg (_, _, _, _, _, f) ->
      check_intervals f
  | And (f1, f2)
   |Or (f1, f2)
   |Implies (f1, f2)
   |Equiv (f1, f2)
   |Let (_, f1, f2) ->
      check_intervals f1 && check_intervals f2
  | LetPast (_, f1, f2) -> check_intervals f1 && check_intervals f2
  | Eventually (intv, f)
   |Always (intv, f)
   |Prev (intv, f)
   |Next (intv, f)
   |Once (intv, f)
   |PastAlways (intv, f) ->
      check_interval intv && check_intervals f
  | Since (intv, f1, f2) | Until (intv, f1, f2) ->
      check_interval intv && check_intervals f1 && check_intervals f2
  | Frex (intv, r) | Prex (intv, r) ->
      check_interval intv && check_re_intervals r

and check_re_intervals = function
  | Wild -> true
  | Test f -> check_intervals f
  | Concat (r1, r2) | Plus (r1, r2) ->
      check_re_intervals r1 && check_re_intervals r2
  | Star r -> check_re_intervals r

let rec check_bounds =
  let check_bound intv =
    let _, b = intv in
    match b with MFOTL.Inf -> false | _ -> true in
  function
  | Equal _ | Less _ | LessEq _ | Pred _ | Substring _ | Matches _ -> true
  | Neg f
   |Exists (_, f)
   |ForAll (_, f)
   |Aggreg (_, _, _, _, _, f)
   |Prev (_, f)
   |Next (_, f)
   |Once (_, f)
   |PastAlways (_, f) ->
      check_bounds f
  | Prex (intv, r) -> check_re_bounds r
  | And (f1, f2)
   |Or (f1, f2)
   |Implies (f1, f2)
   |Equiv (f1, f2)
   |Since (_, f1, f2)
   |Let (_, f1, f2) ->
      check_bounds f1 && check_bounds f2
  | LetPast (_, f1, f2) -> check_bounds f1 && check_bounds f2
  | Eventually (intv, f) | Always (intv, f) ->
      check_bound intv && check_bounds f
  | Frex (intv, r) -> check_bound intv && check_re_bounds r
  | Until (intv, f1, f2) ->
      check_bound intv && check_bounds f1 && check_bounds f2

and check_re_bounds = function
  | Wild -> true
  | Test f -> check_bounds f
  | Concat (r1, r2) | Plus (r1, r2) -> check_re_bounds r1 && check_re_bounds r2
  | Star r -> check_re_bounds r

let rec check_aggregations = function
  | Aggreg (ytyp, y, op, x, g, f) as a ->
      let sf = check_aggregations f in
      let ffv = free_vars f in
      let check = sf && (not (List.mem y g)) && List.mem x ffv in
      if check then check
      else
        failwith
          ( "[Rewriting.check_aggregations] Aggregation "
          ^ string_of_formula "" a ^ " is not well formed. " ^ "Variable " ^ y
          ^ " may not be among the group variables and variable " ^ x
          ^ " must be among the free variables of " ^ string_of_formula "" f )
  | Equal _ | Less _ | LessEq _ | Pred _ | Substring _ | Matches _ -> true
  | Neg f
   |Exists (_, f)
   |ForAll (_, f)
   |Prev (_, f)
   |Once (_, f)
   |PastAlways (_, f)
   |Next (_, f)
   |Always (_, f)
   |Eventually (_, f) ->
      check_aggregations f
  | Prex (_, r) | Frex (_, r) -> check_re_aggregations r
  | Let (_, f1, f2)
   |LetPast (_, f1, f2)
   |And (f1, f2)
   |Or (f1, f2)
   |Implies (f1, f2)
   |Equiv (f1, f2)
   |Since (_, f1, f2)
   |Until (_, f1, f2) ->
      check_aggregations f1 && check_aggregations f2

and check_re_aggregations = function
  | Wild -> true
  | Test f -> check_aggregations f
  | Concat (r1, r2) | Plus (r1, r2) ->
      check_re_aggregations r1 && check_re_aggregations r2
  | Star r -> check_re_aggregations r

let check_wff (f : cplx_formula) =
  (* we check that all LET bindings are well-formed *)
  let cl = check_let f in
  let ci = check_intervals f in
  let cb = check_bounds f in
  let ca = check_aggregations f in
  (* we then check that it contains wf intervals *)
  if not ci then
    failwith
      "[Rewriting.check_wff] The formula contains a negative or empty interval" ;
  (* we then check that it is a bounded future formula *)
  if not cb then
    failwith
      "[Rewriting.check_wff] The formula contains an unbounded future temporal \
       operator. It is hence not monitorable." ;
  cl && ci && cb && ca

let ( << ) f g x = f (g x)

let merge_types sch vars =
  List.append (List.map snd vars) (List.flatten (List.map snd sch))

let new_type_symbol cls sch vs =
  let all = merge_types sch vs in
  let maxtype =
    ( List.fold_left (fun a e -> max a e) 0
    << List.map (fun x -> match x with TSymb (_, a) -> a | _ -> -1)
    << List.filter (fun x -> match x with TSymb _ -> true | _ -> false) )
      all in
  TSymb (cls, maxtype + 1)

exception IncompatibleTypes of tsymb * tsymb

(** Returns the meet of the two given types.
    Raises an IncompatibleTypes exception whenever the meet of the two types is the bottom type. *)
let rec type_meet sch vs (t1 : tsymb) (t2 : tsymb) : tsymb =
  match (t1, t2) with
  | (TCst (TRef a) as t1), TCst (TRef b) -> if compare a b = 0 then t1 else TBot
  | (TCst a as t1), TCst b -> if a = b then t1 else TBot
  | (TCst a as t1), TSymb (TAny, _) -> t1
  | (TSymb (TAny, n1) as t1), (TSymb (TAny, n2) as t2) ->
      if n1 <= n2 then t1 else t2
  | TSymb (TAny, _), t2 -> t2
  | t1, TSymb (TAny, _) -> t1
  | TSymb (TRecord fs1, _), TSymb (TRecord fs2, _) ->
      merge_records sch vs fs1 fs2
  | TCst (TRef ctor), TSymb (TRecord fs, _) -> cast_record sch vs ctor fs
  | TSymb (TRecord fs, _), TCst (TRef ctor) -> cast_record sch vs ctor fs
  | _ -> TBot
(** Accepts the fields of two symbolic record types and returns their meet.
    Raises an IncompatibleTypes exception whenever the meet of the types of a common field
    are incompatible, i.e. equal to bottom type. *)
and merge_records sch vs (t1_fields : (var * tsymb) list)
    (t2_fields : (var * tsymb) list) : tsymb =
  match (t1_fields, t2_fields) with
  | [], t2_fields -> new_type_symbol (TRecord t2_fields) sch vs
  | (f1_name, f1_ty) :: t1_fields, t2_fields -> (
    match List.assoc_opt f1_name t2_fields with
    | Some f2_ty ->
        let meet = type_meet sch vs f1_ty f2_ty in
        let new_ty =
          if meet <> TBot then meet else raise (IncompatibleTypes (f1_ty, f2_ty))
        in
        merge_records sch vs t1_fields ((f1_name, new_ty) :: t2_fields)
    | None -> merge_records sch vs t1_fields ((f1_name, f1_ty) :: t2_fields) )

(** Casts (the fields of) a symbolic record type to a constant reference type
    of the given constructor.
    Raises an InvalidTypes exception whenever the reference type is not more specific
    than the symbolic type described by the given fields. *)
and cast_record sch vs (ctor : var) (fs : (var * tsymb) list) : tsymb = ()

let more_spec_type sch vs t1 t2 = type_meet sch vs t1 t2

let rec string_of_type = function
  | TCst TInt -> "Int"
  | TCst TFloat -> "Float"
  | TCst TStr -> "String"
  | TCst TRegexp -> "Regexp"
  | TCst (TRef ref) -> Printf.sprintf "Ref[%s]" ref
  | TSymb (TNum, a) -> "(Num t" ^ string_of_int a ^ ") =>  t" ^ string_of_int a
  | TSymb (TRecord fs, a) ->
      Printf.sprintf "(TRecord {%s} t%i) => t%i"
        ( List.map (fun (n, t) -> n ^ ":" ^ string_of_type t) fs
        |> String.concat ", " )
        a a
  | TSymb (_, a) -> "t" ^ string_of_int a
  | TBot -> "Never"

(** Given that v:t1 and v:t2 for some v,
   check which type is more specific and update Γ accordingly *)
let propagate_constraints t1 t2 t sch vars =
  let update_schs oldt1 oldt2 meet =
    List.map (fun t -> if t = oldt1 || t = oldt2 then meet else t) in
  let update_vars oldt1 oldt2 meet =
    List.map (fun (v, t) ->
        if t = oldt1 || t = oldt2 then (v, meet) else (v, t) ) in
  try
    let meet = type_meet sch vars t1 t2 in
    ( List.map (fun (n, vs) -> (n, update_schs t1 t2 meet vs)) sch
    , update_vars t1 t2 meet vars )
  with IncompatibleTypes (t1, t2) ->
    let err_str =
      Printf.sprintf
        "Actual type %s of %s is not compatible with expected type %s"
        (string_of_type t2) (string_of_term t) (string_of_type t1) in
    failwith err_str

let string_of_delta sch =
  if List.length sch > 0 then
    let string_of_types ts =
      if List.length ts > 0 then
        let ft = List.hd ts in
        List.fold_left
          (fun a e -> a ^ ", " ^ string_of_type e)
          (string_of_type ft) (List.tl ts)
      else "()" in
    let fp, fs = List.hd sch in
    List.fold_left
      (fun a (p, ts) -> a ^ ", " ^ fst p ^ ":(" ^ string_of_types ts ^ ")")
      (fst fp ^ ":(" ^ string_of_types fs ^ ")")
      (List.tl sch)
  else "_"

let string_of_gamma vars =
  if List.length vars > 0 then
    let fv, ft = List.hd vars in
    List.fold_left
      (fun a (v, t) -> a ^ ", " ^ v ^ ":" ^ string_of_type t)
      (fv ^ ":" ^ string_of_type ft)
      (List.tl vars)
  else "_"

(*
Type judgement is of the form (Δ;Γ) ⊢ t::τ  
where Δ is the predicate schema
      Γ is the symbol table containing variable types
      t term and 
      τ is a type

Parameters:
(sch, vars) are (Δ,Γ)
typ is the type of t as expected by the caller
t is the term

Returns a triple (Δ',Γ', typ') where Δ' and Γ' are the new Δ and Γ
and typ' is the inferred type of t.
Fails of expected (typ) and inferred (typ') types do not match.
*)
let type_check_term_debug d (sch, vars) typ term =
  let rec type_check_term (sch, vars) typ (term : cplx_term) =
    let _ =
      if d then (
        Printf.eprintf "[Rewriting.type_check_term] (%s; %s) ⊢ "
          (string_of_delta sch) (string_of_gamma vars) ;
        Printf.eprintf "%s" (string_of_term term) ;
        Printf.eprintf ": %s" (string_of_type typ) ;
        Printf.eprintf "\n%!" )
      else () in
    match term with
    | Var v as tt ->
        if List.mem_assoc v vars then
          let vtyp = List.assoc v vars in
          let sch, newvars = propagate_constraints typ vtyp tt sch vars in
          (sch, newvars, List.assoc v vars)
        else (sch, (v, typ) :: vars, typ)
    | Cst c as tt ->
        let ctyp = TCst (type_of_cst c) in
        let sch, newvars = propagate_constraints typ ctyp tt sch vars in
        (sch, newvars, ctyp)
    | F2i t as tt ->
        let sch, vars = propagate_constraints (TCst TInt) typ tt sch vars in
        let s, v, t_typ = type_check_term (sch, vars) (TCst TFloat) t in
        let s, v = propagate_constraints (TCst TFloat) t_typ t s v in
        (s, v, TCst TInt)
    | I2f t as tt ->
        let sch, vars = propagate_constraints (TCst TFloat) typ tt sch vars in
        let s, v, t_typ = type_check_term (sch, vars) (TCst TInt) t in
        let s, v = propagate_constraints (TCst TInt) t_typ t s v in
        (s, v, TCst TFloat)
    | FormatDate t as tt ->
        let sch, vars = propagate_constraints (TCst TStr) typ tt sch vars in
        let s, v, t_typ = type_check_term (sch, vars) (TCst TFloat) t in
        let s, v = propagate_constraints (TCst TFloat) t_typ t s v in
        (s, v, TCst TStr)
    | Year t as tt ->
        let sch, vars = propagate_constraints (TCst TInt) typ tt sch vars in
        let s, v, t_typ = type_check_term (sch, vars) (TCst TFloat) t in
        let s, v = propagate_constraints (TCst TFloat) t_typ t s v in
        (s, v, TCst TInt)
    | Month t as tt ->
        let sch, vars = propagate_constraints (TCst TInt) typ tt sch vars in
        let s, v, t_typ = type_check_term (sch, vars) (TCst TFloat) t in
        let s, v = propagate_constraints (TCst TFloat) t_typ t s v in
        (s, v, TCst TInt)
    | DayOfMonth t as tt ->
        let sch, vars = propagate_constraints (TCst TInt) typ tt sch vars in
        let s, v, t_typ = type_check_term (sch, vars) (TCst TFloat) t in
        let s, v = propagate_constraints (TCst TFloat) t_typ t s v in
        (s, v, TCst TInt)
    | R2s t as tt ->
        let sch, vars = propagate_constraints (TCst TStr) typ tt sch vars in
        let s, v, t_typ = type_check_term (sch, vars) (TCst TRegexp) t in
        let s, v = propagate_constraints (TCst TRegexp) t_typ t s v in
        (s, v, TCst TStr)
    | S2r t as tt ->
        let sch, vars = propagate_constraints (TCst TRegexp) typ tt sch vars in
        let s, v, t_typ = type_check_term (sch, vars) (TCst TStr) t in
        let s, v = propagate_constraints (TCst TStr) t_typ t s v in
        (s, v, TCst TRegexp)
    | UMinus t as tt ->
        let exp_typ = new_type_symbol TNum sch vars in
        let sch, vars = propagate_constraints exp_typ typ tt sch vars in
        let s, v, t_typ = type_check_term (sch, vars) exp_typ t in
        let s, v = propagate_constraints exp_typ t_typ t s v in
        let exp_typ = more_spec_type sch vars t_typ exp_typ in
        (s, v, exp_typ)
    | (Plus (t1, t2) | Minus (t1, t2) | Mult (t1, t2) | Div (t1, t2)) as tt ->
        let exp_typ = new_type_symbol TNum sch vars in
        let sch, vars = propagate_constraints exp_typ typ tt sch vars in
        let s1, v1, t1_typ = type_check_term (sch, vars) exp_typ t1 in
        let s1, v1 = propagate_constraints exp_typ t1_typ t1 s1 v1 in
        let exp_typ = more_spec_type sch vars t1_typ exp_typ in
        let s2, v2, t2_typ = type_check_term (s1, v1) exp_typ t2 in
        let s2, v2 = propagate_constraints exp_typ t2_typ t2 s2 v2 in
        let exp_typ = more_spec_type sch vars t2_typ exp_typ in
        (s2, v2, exp_typ)
    | Mod (t1, t2) as tt ->
        let exp_typ = TCst TInt in
        let sch, vars = propagate_constraints exp_typ typ tt sch vars in
        let s1, v1, t1_typ = type_check_term (sch, vars) exp_typ t1 in
        let s1, v1 = propagate_constraints exp_typ t1_typ t1 s1 v1 in
        let s2, v2, t2_typ = type_check_term (s1, v1) exp_typ t2 in
        let s2, v2 = propagate_constraints exp_typ t2_typ t2 s2 v2 in
        (s2, v2, exp_typ)
    | Proj (t1, f) as tt -> (
        let exp_tt_typ = new_type_symbol TAny sch vars in
        let sch', vars' = propagate_constraints exp_tt_typ typ tt sch vars in
        let exp_t1_typ =
          new_type_symbol (TRecord [(f, exp_tt_typ)]) sch' vars' in
        let sch', vars', t1_ty = type_check_term (sch, vars) exp_t1_typ t1 in
        match t1_ty with
        | TCst (TRef ctor) -> ()
        | _ ->
            let err = Printf.sprintf in
            (sch', vars', exp_tt_typ) ) in
  type_check_term (sch, vars) typ term

(*
Type judgement is of the form (Δ;Γ) ⊢ ϕ wff  
where Δ is the predicate schema
      Γ is the symbol table containing variable types
      ϕ formula 

Parameters:
  (sch, vars) are (Δ,Γ)
  ϕ is an CMFOTL formula

Returns a pair (Δ',Γ') where Δ' and Γ' are the new Δ and Γ
Fails if ϕ is not a well formed formula
*)
let type_check_formula_debug d (sch, vars) =
  let rec type_check_formula (sch, vars) (f : cplx_formula) =
    let _ =
      if d then (
        Printf.eprintf "[Rewriting.type_check_formula] (%s; %s) ⊢ "
          (string_of_delta sch) (string_of_gamma vars) ;
        Printf.eprintf "%s" (string_of_formula "" f) ;
        Printf.eprintf "\n%!" )
      else () in
    match f with
    | (Equal (t1, t2) | Less (t1, t2) | LessEq (t1, t2)) as f ->
        let exp_typ = new_type_symbol TAny sch vars in
        let s1, v1, t1_typ = type_check_term_debug d (sch, vars) exp_typ t1 in
        let s1, v1 = propagate_constraints exp_typ t1_typ t1 s1 v1 in
        let exp_typ = more_spec_type sch vars t1_typ exp_typ in
        let s2, v2, t2_typ = type_check_term_debug d (s1, v1) exp_typ t2 in
        let s2, v2 = propagate_constraints exp_typ t2_typ t2 s2 v2 in
        let s2, v2 = propagate_constraints t1_typ t2_typ t2 s2 v2 in
        (s2, v2, f)
    | Substring (t1, t2) as f ->
        let exp_typ = TCst TStr in
        (* Define constant *)
        let s1, v1, t1_typ = type_check_term_debug d (sch, vars) exp_typ t1 in
        (* Type check t1 *)
        let s1, v1 = propagate_constraints exp_typ t1_typ t1 s1 v1 in
        (* Propagate constraints t1, exp *)
        let s2, v2, t2_typ = type_check_term_debug d (s1, v1) exp_typ t2 in
        (* Type check t2 *)
        let s2, v2 = propagate_constraints exp_typ t2_typ t2 s2 v2 in
        (* Propagate constraints t2, exp *)
        (s2, v2, f)
    | Matches (t1, t2) as f ->
        let exp_typ_1 = TCst TStr in
        (* Define constant *)
        let s1, v1, t1_typ = type_check_term_debug d (sch, vars) exp_typ_1 t1 in
        (* Type check t1 *)
        let s1, v1 = propagate_constraints exp_typ_1 t1_typ t1 s1 v1 in
        (* Propagate constraints t1, exp *)
        let exp_typ_2 = TCst TRegexp in
        (* Define constant *)
        let s2, v2, t2_typ = type_check_term_debug d (s1, v1) exp_typ_2 t2 in
        (* Type check t2 *)
        let s2, v2 = propagate_constraints exp_typ_2 t2_typ t2 s2 v2 in
        (* Propagate constraints t2, exp *)
        (s2, v2, f)
    | Pred p as f ->
        let name, arity, _ = p in
        let exp_typ_list =
          if List.mem_assoc (name, arity) sch then List.assoc (name, arity) sch
          else
            failwith
              ( "[Rewriting.check_syntax] unknown predicate " ^ name ^ "/"
              ^ string_of_int arity ^ " in input formula" ) in
        let t_list = get_predicate_args p in
        if List.length t_list = List.length exp_typ_list then
          let idx m =
            let rec i n = if m == n then [] else n :: i (n + 1) in
            i 0 in
          let indices = idx (List.length t_list) in
          let s, v =
            List.fold_left
              (fun (s, v) i ->
                let exp_t = List.nth (List.assoc (name, arity) s) i in
                let t = List.nth t_list i in
                let s1, v1, t1 = type_check_term_debug d (s, v) exp_t t in
                propagate_constraints exp_t t1 t s1 v1 )
              (sch, vars) indices in
          (* let ts = zip exp_typ_list t_list in
             let (s,v,_) =
               List.fold_left
                 (fun (s,v,_) (exp_t,t) ->
                     let (s1,v1,t1) = type_check_term_debug d (s,v) exp_t t in
                     let (s1,v1) = propagate_constraints exp_t t1 t s1 v1 in
                     (s1,v1,t1)
                 ) (sch, vars, (TCst TInt)) ts in *)
          (s, v, f)
        else
          failwith
            ( "[Rewriting.check_syntax] wrong arity for predicate " ^ name
            ^ " in input formula" )
    | Let (p, f1, f2) ->
        let n, a, ts = p in
        let new_vars =
          List.map
            (fun v -> match v with Var t -> t | _ -> failwith "Internal error")
            ts in
        (* We allow only variables here with check_let *)
        let new_typed_vars =
          List.fold_left
            (fun vrs vr ->
              (vr, new_type_symbol TAny sch (List.append vars vrs)) :: vrs )
            [] new_vars in
        let s1, v1, f1 = type_check_formula (sch, new_typed_vars) f1 in
        assert (List.length v1 = List.length new_typed_vars) ;
        let new_sig = List.map (fun v -> (v, List.assoc v v1)) new_vars in
        let new_sig = List.map (fun (_, t) -> t) new_sig in
        let shadowed_pred, rest = List.partition (fun (p, _) -> (n, a) = p) s1 in
        let delta = ((n, a), new_sig) :: rest in
        let s2, v2, f2 = type_check_formula (delta, vars) f2 in
        let new_delta = List.filter (fun (p, _) -> not ((n, a) = p)) s2 in
        (shadowed_pred @ new_delta, v2, Let (p, f1, f2))
    | LetPast (p, f1, f2) ->
        let n, a, ts = p in
        let new_vars =
          List.map
            (fun v -> match v with Var t -> t | _ -> failwith "Internal error")
            ts in
        (* We allow only variables here with check_let *)
        let new_typed_vars =
          List.fold_left
            (fun vrs vr ->
              (vr, new_type_symbol TAny sch (List.append vars vrs)) :: vrs )
            [] new_vars in
        let new_sig = List.rev_map (fun (_, t) -> t) new_typed_vars in
        let s1, v1, f1 =
          type_check_formula (((n, a), new_sig) :: sch, new_typed_vars) f1 in
        assert (List.length v1 = List.length new_typed_vars) ;
        let new_sig = List.map (fun v -> (v, List.assoc v v1)) new_vars in
        let new_sig = List.map (fun (_, t) -> t) new_sig in
        let shadowed_pred, rest = List.partition (fun (p, _) -> (n, a) = p) s1 in
        let delta = ((n, a), new_sig) :: rest in
        let s2, v2, f2 = type_check_formula (delta, vars) f2 in
        let new_delta = List.filter (fun (p, _) -> not ((n, a) = p)) s2 in
        (shadowed_pred @ new_delta, v2, LetPast (p, f1, f2))
    | Neg f ->
        let s, v, f = type_check_formula (sch, vars) f in
        (s, v, Neg f)
    | Prev (intv, f) ->
        let s, v, f = type_check_formula (sch, vars) f in
        (s, v, Prev (intv, f))
    | Next (intv, f) ->
        let s, v, f = type_check_formula (sch, vars) f in
        (s, v, Next (intv, f))
    | Eventually (intv, f) ->
        let s, v, f = type_check_formula (sch, vars) f in
        (s, v, Eventually (intv, f))
    | Once (intv, f) ->
        let s, v, f = type_check_formula (sch, vars) f in
        (s, v, Once (intv, f))
    | Always (intv, f) ->
        let s, v, f = type_check_formula (sch, vars) f in
        (s, v, Always (intv, f))
    | PastAlways (intv, f) ->
        let s, v, f = type_check_formula (sch, vars) f in
        (s, v, PastAlways (intv, f))
    | And (f1, f2) ->
        let s1, v1, f1 = type_check_formula (sch, vars) f1 in
        let s2, v2, f2 = type_check_formula (s1, v1) f2 in
        (s2, v2, And (f1, f2))
    | Or (f1, f2) ->
        let s1, v1, f1 = type_check_formula (sch, vars) f1 in
        let s2, v2, f2 = type_check_formula (s1, v1) f2 in
        (s2, v2, Or (f1, f2))
    | Implies (f1, f2) ->
        let s1, v1, f1 = type_check_formula (sch, vars) f1 in
        let s2, v2, f2 = type_check_formula (s1, v1) f2 in
        (s2, v2, Implies (f1, f2))
    | Equiv (f1, f2) ->
        let s1, v1, f1 = type_check_formula (sch, vars) f1 in
        let s2, v2, f2 = type_check_formula (s1, v1) f2 in
        (s2, v2, Equiv (f1, f2))
    | Since (intv, f1, f2) ->
        let s1, v1, f1 = type_check_formula (sch, vars) f1 in
        let s2, v2, f2 = type_check_formula (s1, v1) f2 in
        (s2, v2, Since (intv, f1, f2))
    | Until (intv, f1, f2) ->
        let s1, v1, f1 = type_check_formula (sch, vars) f1 in
        let s2, v2, f2 = type_check_formula (s1, v1) f2 in
        (s2, v2, Until (intv, f1, f2))
    | Exists (v, f) ->
        let shadowed_vars, reduced_vars =
          List.partition (fun (vr, _) -> List.mem vr v) vars in
        let new_vars =
          List.fold_left
            (fun vrs vr ->
              (vr, new_type_symbol TAny sch (List.append shadowed_vars vrs))
              :: vrs )
            reduced_vars v in
        let s1, v1, f = type_check_formula (sch, new_vars) f in
        let unshadowed_vars =
          List.filter (fun (vr, _) -> not (List.mem vr v)) v1 in
        (s1, unshadowed_vars @ shadowed_vars, Exists (v, f))
    | ForAll (v, f) ->
        let shadowed_vars, reduced_vars =
          List.partition (fun (vr, _) -> List.mem vr v) vars in
        let new_vars =
          List.fold_left
            (fun vrs vr ->
              (vr, new_type_symbol TAny sch (List.append shadowed_vars vrs))
              :: vrs )
            reduced_vars v in
        let s1, v1, f = type_check_formula (sch, new_vars) f in
        let unshadowed_vars =
          List.filter (fun (vr, _) -> not (List.mem vr v)) v1 in
        (s1, unshadowed_vars @ shadowed_vars, ForAll (v, f))
    | Aggreg (rty, r, op, x, gs, f) -> (
        let zs = List.filter (fun v -> not (List.mem v gs)) (free_vars f) in
        let shadowed_vars, reduced_vars =
          List.partition (fun (vr, _) -> List.mem vr zs) vars in
        let vars' =
          List.fold_left
            (fun vrs vr ->
              (vr, new_type_symbol TAny sch (List.append shadowed_vars vrs))
              :: vrs )
            reduced_vars zs in
        let type_check_aggregation exp_typ1 exp_typ2 =
          let s1, v1, _ =
            type_check_term_debug d (sch, vars') exp_typ2 (Var x) in
          (* Type check variable x *)
          let s2, v2, f = type_check_formula (s1, v1) f in
          (* Type check formula f *)
          let reduced_vars =
            List.filter (fun (v, _) -> List.mem_assoc v reduced_vars) v2 in
          (* Get the updated types for gs vars *)
          let vars = shadowed_vars @ reduced_vars in
          (* Restore the top-level vars with updated vars *)
          let s3, v3, _ = type_check_term_debug d (sch, vars) exp_typ1 (Var r) in
          (* Type check variable r *)
          let s3, v3 =
            if
              exp_typ1 = exp_typ2
              (* If the expected types of r and x are the same *)
            then
              propagate_constraints (List.assoc x v2) (List.assoc r v3) (Var r)
                s3 v3
              (* and have compatible types, propagate the more specific type *)
            else (s3, v3) in
          (s3, v3, Aggreg (List.assoc r v3, r, op, x, gs, f)) in
        let exp_typ = new_type_symbol TAny sch vars' in
        let exp_num_typ = new_type_symbol TNum sch vars' in
        match op with
        | Min | Max -> type_check_aggregation exp_typ exp_typ
        | Cnt -> type_check_aggregation (TCst TInt) exp_typ
        | Sum -> type_check_aggregation exp_num_typ exp_num_typ
        | Avg | Med -> type_check_aggregation (TCst TFloat) exp_num_typ )
    | Frex (intv, r) ->
        let s, v, r = type_check_re_formula (sch, vars) r in
        (s, v, Frex (intv, r))
    | Prex (intv, r) ->
        let s, v, r = type_check_re_formula (sch, vars) r in
        (s, v, Prex (intv, r))
  and type_check_re_formula (sch, vars) = function
    | Wild -> (sch, vars, Wild)
    | Test f ->
        let s, v, f = type_check_formula (sch, vars) f in
        (s, v, Test f)
    | Concat (r1, r2) ->
        let s1, v1, r1 = type_check_re_formula (sch, vars) r1 in
        let s2, v2, r2 = type_check_re_formula (s1, v1) r2 in
        (s2, v2, Concat (r1, r2))
    | Plus (r1, r2) ->
        let s1, v1, r1 = type_check_re_formula (sch, vars) r1 in
        let s2, v2, r2 = type_check_re_formula (s1, v1) r2 in
        (s2, v2, Plus (r1, r2))
    | Star r ->
        let s, v, r = type_check_re_formula (sch, vars) r in
        (s, v, Star r) in
  type_check_formula (sch, vars)

let first_debug = ref true

let rec check_syntax (db_schema : db_schema) (f : cplx_formula) =
  let lift_type t = TCst t in
  let sch =
    List.map
      (fun (t, l) ->
        ((t, List.length l), List.map (fun (_, t) -> lift_type t) l) )
      db_schema in
  let debug = !first_debug && Misc.debugging Dbg_typing in
  let fvs =
    List.fold_left
      (fun vrs vr -> (vr, new_type_symbol TAny sch vrs) :: vrs)
      [] (free_vars f) in
  let s, v, f = type_check_formula_debug debug (sch, fvs) f in
  if debug then (
    Printf.eprintf
      "[Rewriting.type_check] The final type judgement is (%s; %s) ⊢ "
      (string_of_delta s) (string_of_gamma v) ;
    Printf.eprintf "%s" (string_of_formula "" f) ;
    Printf.eprintf "\n%!" )
  else () ;
  first_debug := false ;
  (List.map (fun (v, t) -> (v, match t with TCst a -> a | _ -> TFloat)) v, f)

let typecheck_formula (s : db_schema) (f : cplx_formula) =
  (* Remember the order of variables in the input formula. This order is used
     for output, regardless of any transformations that follow. *)
  let orig_fv = free_vars f in
  (* Check well-formedness of the formula *)
  ignore (check_wff f) ;
  (* We first infer and check types *)
  let fvtypes, f = check_syntax s f in
  let fvtypes = List.map (fun v -> (v, List.assoc v fvtypes)) orig_fv in
  ()

(* COMPILE FUNCTIONS *)
let compile_cst (cst : cst) : Predicate.cst =
  match cst with
  | Int v -> Int v
  | Float v -> Float v
  | Str v -> Str v
  | Regexp v -> Regexp v
  | Ref r -> Int (Z.of_int r)

let compile_tcst (tcst : tcst) : Predicate.tcst =
  match tcst with
  | TInt -> TInt
  | TFloat -> TFloat
  | TStr -> TStr
  | TRegexp -> TRegexp
  | TRef _ -> TInt
