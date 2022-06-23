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
open Signature_ast

(* COMMON HELPERS (may be moved to other module?) *)

(** Same as :: operator, but does not add duplicates to the list. *)
let ( ^:: ) v l = if List.mem v l then l else v :: l

(** Returns the first entry of a given triple. *)
let t_fst (a, _, _) = a

(** Returns the second entry of a given triple. *)
let t_snd (_, b, _) = b

(** Returns the third entry of a given triple. *)
let t_thd (_, _, c) = c

(* DATA STRUCTURES *)

type cst =
  | Int of Z.t
  | Str of string
  | Float of float
  (* (string used to produce the regexp, the compiled regexp) because Str library doesn't provide regexp to string functionality *)
  | Regexp of (string * Str.regexp)
  | Record of (string * (string * cst) list)

type tcst = Signature_ast.ty

type tcl = TNum | TAny | TPartial of (var * tsymb) list
and tsymb = TSymb of (tcl * int) | TCst of tcst | TBot

type table_schema = var * (string * tcst) list
type db_schema = table_schema list

let type_of_cst = function
  | Int _ -> TInt
  | Str _ -> TStr
  | Float _ -> TFloat
  | Regexp _ -> TRegexp
  | Record (ctor, _) -> TRef ctor

(** Γ *)
type symbol_table = (cplx_term * tsymb ref) list

(** Δ *)
and predicate_schema = ((var * int) * tsymb list ref) list

(** T
    a map from sort name to inline-flag and sort fields. *)
and tctxt = (var * (bool * (var * tcst) list)) list

and type_context2 = predicate_schema * tctxt * symbol_table

and cplx_term =
  | Var of var
  | Cst of cst
  | F2i of cplx_term
  | I2f of cplx_term
  | I2s of cplx_term
  | S2i of cplx_term
  | F2s of cplx_term
  | S2f of cplx_term
  | DayOfMonth of cplx_term
  | Month of cplx_term
  | Year of cplx_term
  | FormatDate of cplx_term
  | R2s of cplx_term
  | S2r of cplx_term
  | Plus of cplx_term * cplx_term
  | Minus of cplx_term * cplx_term
  | UMinus of cplx_term
  | Mult of cplx_term * cplx_term
  | Div of cplx_term * cplx_term
  | Mod of cplx_term * cplx_term
  | Proj of cplx_term * string

and type_context =
  { predicates: predicate_schema
  ; sorts: tctxt
  ; vars: symbol_table
  ; new_type_symbol: tcl -> tsymb }

let create_type_context (sch : predicate_schema) (sorts : tctxt)
    (vars : symbol_table) (tsymb_id : int ref) : type_context =
  { predicates= sch
  ; sorts
  ; vars
  ; new_type_symbol=
      (fun cls ->
        incr tsymb_id ;
        TSymb (cls, !tsymb_id) ) }

(** returns the predicate schema of a given type context *)
let t_preds (c : type_context) = c.predicates

(** returns the custom sorts of a given type context *)
let t_tctxt (c : type_context) = c.sorts

(** returns the symbol table of a given type context *)
let t_vars (c : type_context) = c.vars

module TermSet = Set.Make (struct
  type t = cplx_term

  let compare = compare
end)

(* predicate = name, arity, and list of arguments *)
type cplx_predicate = var * int * cplx_term list

let get_predicate_args ((name, ar, args) : cplx_predicate) = args

let rec tvars : cplx_term -> var list = function
  | Var v -> [v]
  | Cst c -> []
  | F2i t
   |I2f t
   |I2s t
   |S2i t
   |F2s t
   |S2f t
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

let pvars (p : cplx_predicate) =
  List.fold_left
    (fun acc a ->
      List.fold_left
        (fun acc v -> if List.mem v acc then acc else v :: acc)
        acc (tvars a) )
    [] (get_predicate_args p)

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
  | Aggreg of
      (tsymb * var * MFOTL.agg_op * cplx_term * cplx_term list * 'a cplx_formula)
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

(** returns the AST of a formula *)
let f_ast = snd

(** returns the formula annotations *)
let f_annot = fst

(** Accepts a variable 'var' and returns a set of terms depending on 'var'.
    The returned terms are either of type Var or Proj.
    Example: get_var_usage r (Request(r) AND r.user.name = "" AND EXISTS r . Report(r) AND r.reason = "")
    -> [r, r.user.name]. *)
let rec get_var_usage ((_, f) : 'a cplx_formula) (var : var) : TermSet.t =
  let rec term_usage = function
    | Cst _ -> TermSet.empty
    | Var v ->
        if compare v var = 0 then TermSet.singleton (Var v) else TermSet.empty
    | F2i t1
     |I2f t1
     |I2s t1
     |S2i t1
     |F2s t1
     |S2f t1
     |DayOfMonth t1
     |Month t1
     |Year t1
     |FormatDate t1
     |R2s t1
     |S2r t1
     |UMinus t1 ->
        term_usage t1
    | Plus (t1, t2)
     |Minus (t1, t2)
     |Mult (t1, t2)
     |Div (t1, t2)
     |Mod (t1, t2) ->
        TermSet.union (term_usage t1) (term_usage t2)
    | Proj (base, _) as p ->
        if term_usage base = TermSet.empty then TermSet.empty
        else TermSet.singleton p in
  match f with
  | Equal (t1, t2) | Less (t1, t2) | LessEq (t1, t2) | Substring (t1, t2) ->
      TermSet.union (term_usage t1) (term_usage t2)
  | Matches (t1, t2, tl) ->
      let terms =
        List.fold_left
          (fun acc o -> match o with Some t -> t :: acc | None -> acc)
          [] tl in
      List.fold_left
        (fun acc s -> TermSet.union acc s)
        TermSet.empty
        (term_usage t1 :: term_usage t2 :: List.map term_usage terms)
  | Pred (_, n, args) ->
      List.fold_left
        (fun acc a -> TermSet.union acc (term_usage a))
        TermSet.empty args
  | Neg f1 -> get_var_usage f1 var
  | And (f1, f2) | Or (f1, f2) | Implies (f1, f2) | Equiv (f1, f2) ->
      TermSet.union (get_var_usage f1 var) (get_var_usage f2 var)
  | Exists (vs, f1) | ForAll (vs, f1) ->
      (* do not visit nested scope if var is shadowed: *)
      if not (List.mem var vs) then get_var_usage f1 var else TermSet.empty
  | Let (p, f1, f2) | LetPast (p, f1, f2) ->
      (* free variables in f1 (body of LET) have to be arguments to p by definition,
         and therefore always shadow variables from outer scope. *)
      get_var_usage f2 var
  | Prev (_, f1)
   |Next (_, f1)
   |Eventually (_, f1)
   |Once (_, f1)
   |Always (_, f1)
   |PastAlways (_, f1) ->
      get_var_usage f1 var
  (* TODO is this really the correct behavior? *)
  | Since (_, f1, f2) | Until (_, f1, f2) ->
      TermSet.union (get_var_usage f1 var) (get_var_usage f2 var)
  | Frex _ | Prex _ -> TermSet.empty
  (* TODO handle these cases *)
  | Aggreg _ -> TermSet.empty

let unixts = ref false

(** Returns a list of free variables in the given formula.
    One can provide an optional tvars function to be used,
    returning the free variables for a given term. Default is `tvars`. *)
let rec free_vars ?(tvars = tvars) ((_, f) : 'a cplx_formula) =
  match f with
  | Equal (t1, t2) | Less (t1, t2) | LessEq (t1, t2) | Substring (t1, t2) ->
      Misc.union (tvars t1) (tvars t2)
  | Matches (t1, t2, tl) ->
      let fv = Misc.union (tvars t1) (tvars t2) in
      List.fold_left
        (fun s t -> match t with None -> s | Some t -> Misc.union s (tvars t))
        fv tl
  | Pred p -> pvars p
  | Let (_, _, f) -> free_vars ~tvars f
  | LetPast (_, _, f) -> free_vars ~tvars f
  | Neg f -> free_vars ~tvars f
  | And (f1, f2) | Or (f1, f2) | Implies (f1, f2) | Equiv (f1, f2) ->
      Misc.union (free_vars ~tvars f1) (free_vars ~tvars f2)
  | Exists (vl, f) | ForAll (vl, f) ->
      List.filter (fun x -> not (List.mem x vl)) (free_vars ~tvars f)
  | Aggreg (rty, y, op, x, glist, f) ->
      y :: (List.map tvars glist |> List.flatten)
  | Prev (intv, f)
   |Next (intv, f)
   |Eventually (intv, f)
   |Once (intv, f)
   |Always (intv, f)
   |PastAlways (intv, f) ->
      free_vars ~tvars f
  | Since (intv, f1, f2) | Until (intv, f1, f2) ->
      Misc.union (free_vars ~tvars f2) (free_vars ~tvars f1)
  | Frex (intv, r) | Prex (intv, r) -> free_re_vars ~tvars r

and free_re_vars ?(tvars = tvars) = function
  | Wild -> []
  | Test f -> free_vars ~tvars f
  | Concat (r1, r2) | Plus (r1, r2) ->
      Misc.union (free_re_vars ~tvars r1) (free_re_vars ~tvars r2)
  | Star r -> free_re_vars ~tvars r

let rec is_mfodl ((_, f) : 'a cplx_formula) =
  match f with
  | Equal (t1, t2)
   |Less (t1, t2)
   |LessEq (t1, t2)
   |Substring (t1, t2)
   |Matches (t1, t2, _) ->
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

let rec string_of_tcst (tctxt : tctxt) = function
  | TFloat -> "TFloat"
  | TInt -> "TInt"
  | TStr -> "TStr"
  | TRegexp -> "TRegexp"
  | TRef ctor -> (
    (* print their structure instead of teir ctor name for inline type *)
    match List.assoc ctor tctxt with
    | false, _ -> Printf.sprintf "%s" ctor
    | true, fields ->
        "{"
        ^ ( List.map
              (fun (name, typ) -> name ^ ": " ^ string_of_tcst tctxt typ)
              fields
          |> String.concat ", " )
        ^ "}" )

let rec string_of_cst c =
  let format_string s =
    if s = "" then "\"\""
    else if s.[0] = '\"' && s.[String.length s - 1] = '\"' then s
    else "\"" ^ s ^ "\"" in
  match c with
  | Int i -> Z.to_string i
  | Float f -> Printf.sprintf "%f" f
  | Str s -> format_string s
  | Regexp (p, _) -> Printf.sprintf "r%s" (format_string p)
  | Record (ctor, fields) ->
      Printf.sprintf "%s {%s}" ctor
        ( List.map (fun (n, v) -> n ^ ": " ^ string_of_cst v) fields
        |> String.concat ", " )

let rec string_of_type (tctxt : tctxt) = function
  | TCst t -> string_of_tcst tctxt t
  | TSymb (TNum, a) -> "(Num t" ^ string_of_int a ^ ") =>  t" ^ string_of_int a
  | TSymb (TPartial fs, a) ->
      Printf.sprintf "t%i{%s}" a
        ( List.map (fun (n, t) -> n ^ ":" ^ string_of_type tctxt t) fs
        |> String.concat ", " )
  | TSymb (TAny, a) -> "t" ^ string_of_int a
  | TBot -> "Never"

let rec string_of_term term =
  let add_paren str = "(" ^ str ^ ")" in
  let rec t2s b term =
    let b', str =
      match term with
      | Var v -> (true, v)
      | Cst c -> (true, string_of_cst c)
      | F2i t -> (false, "f2i(" ^ t2s true t ^ ")")
      | I2f t -> (false, "i2f(" ^ t2s true t ^ ")")
      | I2s t -> (false, "i2s(" ^ t2s true t ^ ")")
      | S2i t -> (false, "s2i(" ^ t2s true t ^ ")")
      | F2s t -> (false, "f2s(" ^ t2s true t ^ ")")
      | S2f t -> (false, "s2f(" ^ t2s true t ^ ")")
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
      | Proj (t1, f) -> (false, Printf.sprintf "%s.%s" (string_of_term t1) f)
    in
    (* we don't add parentheses for the top-most operator, nor around
       constants and variables *)
    if b || b' then str else add_paren str
  and t2s' term = t2s false term in
  t2s true term

let string_of_predicate (p, ar, args) =
  string_of_var p ^ Misc.string_of_list string_of_term args

let string_of_opt_term = function None -> "_" | Some t -> string_of_term t

(* we always put parantheses for binary operators like "(f1 AND f2)", and around unary
   ones only if they occur on the left-hand side of a binary operator: like "((NOT f1) AND f2)"*)
let string_of_formula str ((fdata, g) : 'a cplx_formula) =
  let pps = String.split_on_char '\n' str in
  let padding =
    if pps == [] then ""
    else String.map (fun s -> ' ') (List.nth pps (List.length pps - 1)) in
  let rec string_f_rec top par ((fdata, h) : 'a cplx_formula) =
    match h with
    | Equal (t1, t2) -> string_of_term t1 ^ " = " ^ string_of_term t2
    | Less (t1, t2) -> string_of_term t1 ^ " < " ^ string_of_term t2
    | LessEq (t1, t2) -> string_of_term t1 ^ " <= " ^ string_of_term t2
    | Substring (t1, t2) ->
        string_of_term t1 ^ " SUBSTRING " ^ string_of_term t2
    | Matches (t1, t2, tl) ->
        string_of_term t1 ^ " MATCHES " ^ string_of_term t2
        ^
        if tl = [] then ""
        else Misc.string_of_list_ext " (" ")" ", " string_of_opt_term tl
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
              ^ string_of_term x
              ^ ( if glist <> [] then
                  "; "
                  ^ Misc.string_of_list_ext "" "" ","
                      (fun z -> string_of_term (Var z))
                      (List.map string_of_term glist)
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
                    ^ string_f_rec false true (fdata, Pred p)
                    ^ " = " ^ string_f_rec false true f1 ^ "\n" ^ padding ^ "IN"
                    ^ " "
                    ^ string_f_rec false false f2
                | LetPast (p, f1, f2) ->
                    "LETPAST" ^ " "
                    ^ string_f_rec false true (fdata, Pred p)
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
  str ^ string_f_rec true false (fdata, g)

(* Fully parenthesize an MFOTL formula *)
let string_of_parenthesized_formula str ((fdata, g) : 'a cplx_formula) =
  let pps = String.split_on_char '\n' str in
  let padding =
    if pps == [] then ""
    else String.map (fun s -> ' ') (List.nth pps (List.length pps - 1)) in
  let rec string_f_rec top par ((fdata, h) : 'a cplx_formula) =
    match h with
    | Equal (t1, t2) ->
        "(" ^ string_of_term t1 ^ " = " ^ string_of_term t2 ^ ")"
    | Less (t1, t2) -> "(" ^ string_of_term t1 ^ " < " ^ string_of_term t2 ^ ")"
    | LessEq (t1, t2) ->
        "(" ^ string_of_term t1 ^ " <= " ^ string_of_term t2 ^ ")"
    | Substring (t1, t2) ->
        "(" ^ string_of_term t1 ^ " SUBSTRING " ^ string_of_term t2 ^ ")"
    | Matches (t1, t2, tl) ->
        "(" ^ string_of_term t1 ^ " MATCHES " ^ string_of_term t2
        ^ ( if tl = [] then ""
          else Misc.string_of_list_ext " (" ")" ", " string_of_opt_term tl )
        ^ ")"
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
          ^ " " ^ string_of_term x
          ^ ( if glist <> [] then
              "; "
              ^ Misc.string_of_list_ext "" "" ","
                  (fun z -> string_of_term (Var z))
                  (List.map string_of_term glist)
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
            ^ string_f_rec false true (fdata, Pred p)
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
  str ^ string_f_rec true false (fdata, g)

let string_of_delta (tctxt : tctxt) (sch : predicate_schema) : string =
  if List.length sch > 0 then
    let string_of_types ts =
      if List.length ts > 0 then
        let ft = List.hd ts in
        List.fold_left
          (fun a e -> a ^ ", " ^ string_of_type tctxt e)
          (string_of_type tctxt ft) (List.tl ts)
      else "()" in
    let fp, fs = List.hd sch in
    List.fold_left
      (fun a (p, ts) -> a ^ ", " ^ fst p ^ "(" ^ string_of_types !ts ^ ")")
      (fst fp ^ "(" ^ string_of_types !fs ^ ")")
      (List.tl sch)
  else "_"

let string_of_gamma (tctxt : tctxt) (vars : symbol_table) =
  if List.length vars > 0 then
    let fv, ft = List.hd vars in
    List.fold_left
      (fun a (v, t) ->
        a ^ ", " ^ string_of_term v ^ ":" ^ string_of_type tctxt !t )
      (string_of_term fv ^ ":" ^ string_of_type tctxt !ft)
      (List.tl vars)
  else "_"

(** Returns the type of the given term derived from the provided symbol table.
    Only implemented for constants, variables and projections. *)
let rec type_of_term (ctx : type_context) (t : cplx_term) : tcst =
  let tctxt, vars = (ctx.sorts, ctx.vars) in
  let concrete_ty = function
    | TCst t -> t
    | ty ->
        failwith
        @@ Printf.sprintf
             "type_of_term: Expected %s to be of concrete type, found %s"
             (string_of_term t) (string_of_type tctxt ty) in
  match t with
  | Var v -> (
    match List.assoc_opt (Var v) vars with
    | Some tsymb -> concrete_ty !tsymb
    | None ->
        failwith
        @@ Printf.sprintf "Cannov find var %s in symbol table %s" v
             (string_of_gamma tctxt vars) )
  | Proj (base, field) ->
      let base_ctor =
        match type_of_term ctx base with
        | TRef ctor -> ctor
        | t ->
            failwith
            @@ Printf.sprintf
                 "type_of_term: exptected base to be TRef, found %s"
                 (string_of_ty t) in
      let base_fields = List.assoc base_ctor tctxt |> snd in
      List.assoc field base_fields
  | Cst (Int _) -> TInt
  | Cst (Str _) -> TStr
  | Cst (Float _) -> TFloat
  | Cst (Regexp _) -> TRegexp
  | t ->
      failwith
      @@ Printf.sprintf "type_of_term: not implemented for %s"
           (string_of_term t)

(* TYPE CHECKING *)

(** Returns true iff the given term is either a variable
    or a chain of projections:
    Example 0: projection_base r -> true
    Example 1: projection_base r.user -> true
    Example 2: projection_base r.user.name -> true *)
let rec is_var_or_proj = function
  | Var _ -> true
  | Proj (b, _) -> is_var_or_proj b
  | _ -> false

(** Returns the base of (a chain of) projections:
    Example 0: projection_base r -> r
    Example 1: projection_base r.user -> r.
    Example 2: projection_base r.user.name -> r. *)
let rec projection_base (t : cplx_term) : var =
  match t with
  | Var v -> v
  | Proj (b, _) -> projection_base b
  | _ ->
      failwith
      @@ Printf.sprintf
           "[CMFOTL.projection_base]: expected projection, got '%s'"
           (string_of_term t)

let rec check_let ((fdata, f) : 'a cplx_formula) =
  match f with
  | Let (p, f1, f2) ->
      let n, a, ts = p in
      let check_params =
        List.for_all (fun t -> match t with Var _ -> true | _ -> false) ts in
      if not check_params then
        let string_of_terms =
          List.fold_left (fun s v -> s ^ " " ^ string_of_term v) "" in
        let str =
          Printf.sprintf
            "[Typecheck.check_let] LET %s's parameters %s must be variables" n
            (string_of_terms ts) in
        failwith str
      else () ;
      let prms = List.flatten (List.map tvars ts) in
      let fv1 = free_vars f1 in
      if List.length fv1 != a then
        let str =
          Printf.sprintf
            "[Typecheck.check_let] LET %s's arity %n must match the number of \
             free variables of %s "
            n a (string_of_formula "" f1) in
        failwith str
      else () ;
      if not (Misc.subset fv1 prms && Misc.subset prms fv1) then
        let string_of_vars =
          List.fold_left (fun s v -> s ^ " " ^ string_of_var v) "" in
        let str =
          Printf.sprintf
            "[Typecheck.check_let] LET %s's parameters %s do not coincide with \
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
            "[Typecheck.check_let] LETPAST %s's parameters %s must be variables"
            n (string_of_terms ts) in
        failwith str
      else () ;
      let prms = List.flatten (List.map tvars ts) in
      let fv1 = free_vars f1 in
      if List.length fv1 != a then
        let str =
          Printf.sprintf
            "[Typecheck.check_let] LETPAST %s's arity %n must match the number \
             of free variables of %s "
            n a (string_of_formula "" f1) in
        failwith str
      else () ;
      if not (Misc.subset fv1 prms && Misc.subset prms fv1) then
        let string_of_vars =
          List.fold_left (fun s v -> s ^ " " ^ string_of_var v) "" in
        let str =
          Printf.sprintf
            "[Typecheck.check_let] LetPast %s's parameters %s do not coincide \
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
  let check ((_, f) : 'a cplx_formula) =
    match f with
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
        check_interval intv && check_re_intervals r in
  check

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
  let check ((_, f) : 'a cplx_formula) =
    match f with
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
        check_bound intv && check_bounds f1 && check_bounds f2 in
  check

and check_re_bounds = function
  | Wild -> true
  | Test f -> check_bounds f
  | Concat (r1, r2) | Plus (r1, r2) -> check_re_bounds r1 && check_re_bounds r2
  | Star r -> check_re_bounds r

let rec check_aggregations ((fdata, f) : 'a cplx_formula) =
  match f with
  | Aggreg (ytyp, y, op, x, g, f) as a ->
      let sf = check_aggregations f in
      let ffv = free_vars f in
      let check =
        sf
        (* the term grouping over has to be a var or projection: *)
        && is_var_or_proj x
        (* each group-by term has to be a var or projection: *)
        && List.for_all is_var_or_proj g
        (* the resulting var cannot be part of the group-by vars: *)
        && (not (List.mem (Var y) g))
        (* the base of x has to be part of the free variables in the sub-formula *)
        && List.mem (projection_base x) ffv
        (* the base of each group-by term has to be part
           of the free variables in the sub-formula *)
        && List.for_all (fun g' -> List.mem (projection_base g') ffv) g in
      if check then check
      else
        failwith
          ( "[Typecheck.check_aggregations] Aggregation "
          ^ string_of_formula "" (fdata, a)
          ^ " is not well formed. " ^ "Variable " ^ y
          ^ " may not be among the group variables and variable "
          ^ string_of_term x ^ " must be among the free variables of "
          ^ string_of_formula "" f )
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

let check_wff (f : 'a cplx_formula) =
  (* we check that all LET bindings are well-formed *)
  let cl = check_let f in
  let ci = check_intervals f in
  let cb = check_bounds f in
  let ca = check_aggregations f in
  (* we then check that it contains wf intervals *)
  if not ci then
    failwith
      "[Typecheck.check_wff] The formula contains a negative or empty interval" ;
  (* we then check that it is a bounded future formula *)
  if not cb then
    failwith
      "[Typecheck.check_wff] The formula contains an unbounded future temporal \
       operator. It is hence not monitorable." ;
  cl && ci && cb && ca

let ( << ) f g x = f (g x)

let merge_types (sch : predicate_schema) (vars : symbol_table) =
  let rec merge_tsymb (tsymb : tsymb) : tsymb list =
    match tsymb with
    | TSymb (TPartial fields, _) ->
        (* TODO: is this recursion really necessary? *)
        (* tsymb :: List.map snd fields |> List.map merge_tsymb |> List.flatten *)
        [tsymb]
    | _ -> [tsymb] in
  List.append
    (List.map (fun v -> !(snd v)) vars |> List.map merge_tsymb |> List.flatten)
    ( List.map (fun s -> !(snd s)) sch
    |> List.flatten |> List.map merge_tsymb |> List.flatten )

exception IncompatibleTypes of tsymb * tsymb

(* compares two types for structural equality.
   Returns either true of false (no order). *)
let rec compare_tcst (tctxt : tctxt) t1 t2 =
  match (t1, t2) with
  | TRef ctor1, TRef ctor2 ->
      let (_, fs1), (_, fs2) =
        (List.assoc ctor1 tctxt, List.assoc ctor2 tctxt) in
      (* compare fields recursively. They are allowed to be in different order. *)
      if List.length fs1 <> List.length fs2 then false
      else
        List.for_all
          (fun (f1, t1) ->
            match List.assoc_opt f1 fs2 with
            | None -> false
            | Some t2 -> compare_tcst tctxt t1 t2 )
          fs1
  | t1, t2 -> compare t1 t2 = 0

(** Returns the meet of the two given types.
    Raises an IncompatibleTypes exception whenever the meet of the two types is the bottom type. *)
let rec type_meet (ctx : type_context) (t1 : tsymb) (t2 : tsymb) : tsymb =
  let tctxt = ctx.sorts in
  match (t1, t2) with
  (* the meet of two constant types can only exist if they are structurally equal.
     if both are TRef types, we return the named typed in favor of any inline type: *)
  | (TCst (TRef c1 as ref1) as t1), (TCst (TRef c2 as ref2) as t2) ->
      let c1_inline, _ = List.assoc c1 tctxt in
      let ttt =
        if compare_tcst tctxt ref1 ref2 then if c1_inline then t2 else t1
        else raise (IncompatibleTypes (t1, t2)) in
      ttt
  | (TCst a as t1), TCst b ->
      if compare_tcst tctxt a b then t1 else raise (IncompatibleTypes (t1, t2))
  (* the meet of two TAny instances is the one with the lower index *)
  | (TSymb (TAny, n1) as t1), (TSymb (TAny, n2) as t2) ->
      if n1 <= n2 then t1 else t2
  (* the meet of TAny with any type t is always type t *)
  | TSymb (TAny, _), t | t, TSymb (TAny, _) -> t
  (* the meet of two partial types is their merged partial type *)
  | TSymb (TPartial fs1, _), TSymb (TPartial fs2, _) ->
      merge_records ctx fs1 fs2
  (* the meet between a ref type and a partial type is the ref type,
     as long as the partial type can be casted. *)
  | TCst (TRef ctor), TSymb (TPartial partial_fields, _)
   |TSymb (TPartial partial_fields, _), TCst (TRef ctor) -> (
    match List.assoc_opt ctor tctxt with
    | None -> failwith ("Unknown record type: " ^ ctor)
    | Some (_, ref_fields) ->
        let success = cast_to_record ctx ref_fields partial_fields in
        if success then TCst (TRef ctor) else raise (IncompatibleTypes (t1, t2))
    )
  (* for any other case, we assume the meet is the bottom type *)
  | _ -> raise (IncompatibleTypes (t1, t2))

(** Accepts the fields of two symbolic record types and returns their meet.
    Raises an IncompatibleTypes exception whenever the meet of the types of a common field
    are incompatible, i.e. equal to bottom type. *)
and merge_records (ctx : type_context) (t1_fields : (var * tsymb) list)
    (t2_fields : (var * tsymb) list) : tsymb =
  (* works similar to the merge function of a merge-sort. Assumes fields to be sorted by name. *)
  let rec merge = function
    | [], [] -> []
    | [], t2_fields -> t2_fields
    | t1_fields, [] -> t1_fields
    | ((n1, t1) :: f1s as t1_fields), ((n2, t2) :: f2s as t2_fields) -> (
      match compare n1 n2 with
      | -1 -> (n1, t1) :: merge (f1s, t2_fields)
      | 1 -> (n2, t2) :: merge (t1_fields, f2s)
      | 0 ->
          let meet = type_meet ctx t1 t2 in
          (n1, meet) :: merge (f1s, f2s)
      | _ -> failwith "[CMFOTL:merge_records]: invalid state" ) in
  let sort_fields (n1, _) (n2, _) = compare n1 n2 in
  let t1_fields = List.sort sort_fields t1_fields in
  let t2_fields = List.sort sort_fields t2_fields in
  ctx.new_type_symbol (TPartial (merge (t1_fields, t2_fields)))

(** Tries to cast a partial record type to a given list of fields.
    Raises an error if the record fields do not describe a subtype of the partial type
    described by its fields. *)
and cast_to_record (ctx : type_context) (fields : (var * tcst) list)
    (fs : (var * tsymb) list) : bool =
  (* raise if reference type is missing a field: *)
  if List.exists (fun (name, _) -> List.assoc_opt name fields = None) fs then
    false
  else (
    (* try to find the meet of each field.
       Because all (recursive) fields of a TRef type are constant types,
       the field type of the TRef type is always the meet of both of them. *)
    List.iter
      (fun (name, ty) ->
        match List.assoc_opt name fs with
        | None -> ()
        | Some sty -> ignore (type_meet ctx (TCst ty) sty) )
      fields ;
    true )

let more_spec_type ctx t1 t2 = type_meet ctx t1 t2

let propagate_to_predicate_schema (t1 : tsymb) (t2 : tsymb) (meet : tsymb)
    (sch : predicate_schema) : unit =
  List.iter
    (fun (n, args) ->
      let new_args =
        List.map (fun typ -> if typ = t1 || typ = t2 then meet else typ) !args
      in
      args := new_args )
    sch

let propagate_to_symbol_table (t1 : tsymb) (t2 : tsymb) (meet : tsymb)
    (vars : symbol_table) : unit =
  let rec propagate_to_tsymb (tsymb : tsymb) : tsymb =
    if tsymb = t1 || tsymb = t2 then meet
    else
      match tsymb with
      | TSymb (TPartial fields, i) ->
          let new_fields =
            List.map (fun (name, typ) -> (name, propagate_to_tsymb typ)) fields
          in
          TSymb (TPartial new_fields, i)
      | _ -> tsymb in
  List.iter (fun (name, typ) -> typ := propagate_to_tsymb !typ) vars

(** Given that v:t1 and v:t2 for some v,
   check which type is more specific and update Γ accordingly *)
let propagate_constraints t1 t2 (t : cplx_term) (ctx : type_context) : unit =
  try
    let meet = type_meet ctx t1 t2 in
    propagate_to_predicate_schema t1 t2 meet ctx.predicates ;
    propagate_to_symbol_table t1 t2 meet ctx.vars
  with IncompatibleTypes (t1, t2) ->
    let err_str =
      Printf.sprintf
        "Type error while evaluating term '%s': Actual type %s is not \
         compatible with expected type %s"
        (string_of_term t)
        (string_of_type ctx.sorts t2)
        (string_of_type ctx.sorts t1) in
    failwith err_str

(** Validates all terms in the given symbol table for concrete types.
    Raises a type error if any term of symbolic type has been found.
    An optional predicate name is printed if provided. *)
let rec check_unresolved_terms (pred : string option) (free_vars : var list)
    (vars : symbol_table) : unit =
  let unresolved_vars =
    List.filter
      (fun (v, t) ->
        match (v, !t) with
        | Var v, TSymb st -> List.mem v free_vars
        | _ -> false )
      vars
    |> List.map fst in
  if List.length unresolved_vars > 0 then
    let terms_as_str =
      List.map string_of_term unresolved_vars |> String.concat ", " in
    let msg =
      Printf.sprintf
        "Type Error: Following terms%s could not be resolved to a type: %s"
        (match pred with Some n -> " in predicate '" ^ n ^ "'" | None -> "")
        terms_as_str in
    failwith msg

(*
Type judgement is of the form (Δ;T;Γ) ⊢ t::τ  
where Δ is the predicate schema
      T is the type context
      Γ is the symbol table containing variable types
      t term and 
      τ is a type

Parameters:
(sch, tctxt, vars) are (Δ,T,Γ)
typ is the type of t as expected by the caller
t is the term

Returns a triple (Δ',Γ', typ') where Δ' and Γ' are the new Δ and Γ
and typ' is the inferred type of t.
Fails of expected (typ) and inferred (typ') types do not match.
*)
let type_check_term_debug (d : bool) (ctx : type_context) (typ : tsymb)
    (term : cplx_term) =
  let rec type_check_term (ctx : type_context) typ term : tsymb =
    let sch, tctxt, vars = (ctx.predicates, ctx.sorts, ctx.vars) in
    if d then (
      Printf.eprintf "[Typecheck.type_check_term] \n%!Δ: %s\n%!Γ: %s\n%!⊢ "
        (string_of_delta tctxt sch)
        (string_of_gamma tctxt vars) ;
      Printf.eprintf "%s" (string_of_term term) ;
      Printf.eprintf ": %s" (string_of_type tctxt typ) ;
      Printf.eprintf "\n%!\n%!" ) ;
    match term with
    | Var v as tt ->
        if List.mem_assoc tt vars then (
          let vtyp = !(List.assoc tt vars) in
          propagate_constraints typ vtyp tt ctx ;
          vtyp )
        else
          failwith
          @@ Printf.sprintf
               "[type_check_term_debug]: invalid state: missing variable %s in \
                symbol table %s for term %s"
               v
               (string_of_gamma tctxt vars)
               (string_of_term term)
    | Cst c as tt ->
        let ctyp = TCst (type_of_cst c) in
        propagate_constraints typ ctyp tt ctx ;
        ctyp
    | F2i t as tt ->
        propagate_constraints (TCst TInt) typ tt ctx ;
        let t_typ = type_check_term ctx (TCst TFloat) t in
        propagate_constraints (TCst TFloat) t_typ t ctx ;
        TCst TInt
    | I2f t as tt ->
        propagate_constraints (TCst TFloat) typ tt ctx ;
        let t_typ = type_check_term ctx (TCst TInt) t in
        propagate_constraints (TCst TInt) t_typ t ctx ;
        TCst TFloat
    | I2s t as tt ->
        propagate_constraints (TCst TStr) typ tt ctx ;
        let t_typ = type_check_term ctx (TCst TInt) t in
        propagate_constraints (TCst TInt) t_typ t ctx ;
        TCst TStr
    | S2i t as tt ->
        propagate_constraints (TCst TInt) typ tt ctx ;
        let t_typ = type_check_term ctx (TCst TStr) t in
        propagate_constraints (TCst TStr) t_typ t ctx ;
        TCst TInt
    | F2s t as tt ->
        propagate_constraints (TCst TStr) typ tt ctx ;
        let t_typ = type_check_term ctx (TCst TFloat) t in
        propagate_constraints (TCst TFloat) t_typ t ctx ;
        TCst TStr
    | S2f t as tt ->
        propagate_constraints (TCst TFloat) typ tt ctx ;
        let t_typ = type_check_term ctx (TCst TStr) t in
        propagate_constraints (TCst TStr) t_typ t ctx ;
        TCst TFloat
    | FormatDate t as tt ->
        propagate_constraints (TCst TStr) typ tt ctx ;
        let t_typ = type_check_term ctx (TCst TFloat) t in
        propagate_constraints (TCst TFloat) t_typ t ctx ;
        TCst TStr
    | Year t as tt ->
        propagate_constraints (TCst TInt) typ tt ctx ;
        let t_typ = type_check_term ctx (TCst TFloat) t in
        propagate_constraints (TCst TFloat) t_typ t ctx ;
        TCst TInt
    | Month t as tt ->
        propagate_constraints (TCst TInt) typ tt ctx ;
        let t_typ = type_check_term ctx (TCst TFloat) t in
        propagate_constraints (TCst TFloat) t_typ t ctx ;
        TCst TInt
    | DayOfMonth t as tt ->
        propagate_constraints (TCst TInt) typ tt ctx ;
        let t_typ = type_check_term ctx (TCst TFloat) t in
        propagate_constraints (TCst TFloat) t_typ t ctx ;
        TCst TInt
    | R2s t as tt ->
        propagate_constraints (TCst TStr) typ tt ctx ;
        let t_typ = type_check_term ctx (TCst TRegexp) t in
        propagate_constraints (TCst TRegexp) t_typ t ctx ;
        TCst TStr
    | S2r t as tt ->
        propagate_constraints (TCst TRegexp) typ tt ctx ;
        let t_typ = type_check_term ctx (TCst TStr) t in
        propagate_constraints (TCst TStr) t_typ t ctx ;
        TCst TRegexp
    | UMinus t as tt ->
        let exp_typ = ctx.new_type_symbol TNum in
        propagate_constraints exp_typ typ tt ctx ;
        let t_typ = type_check_term ctx exp_typ t in
        propagate_constraints exp_typ t_typ t ctx ;
        let exp_typ = type_meet ctx t_typ exp_typ in
        exp_typ
    | (Plus (t1, t2) | Minus (t1, t2) | Mult (t1, t2) | Div (t1, t2)) as tt ->
        let exp_typ = ctx.new_type_symbol TNum in
        propagate_constraints exp_typ typ tt ctx ;
        let t1_typ = type_check_term ctx exp_typ t1 in
        propagate_constraints exp_typ t1_typ t1 ctx ;
        let exp_typ = type_meet ctx t1_typ exp_typ in
        let t2_typ = type_check_term ctx exp_typ t2 in
        propagate_constraints exp_typ t2_typ t2 ctx ;
        let exp_typ = type_meet ctx t2_typ exp_typ in
        exp_typ
    | Mod (t1, t2) as tt ->
        let exp_typ = TCst TInt in
        propagate_constraints exp_typ typ tt ctx ;
        let t1_typ = type_check_term ctx exp_typ t1 in
        propagate_constraints exp_typ t1_typ t1 ctx ;
        let t2_typ = type_check_term ctx exp_typ t2 in
        propagate_constraints exp_typ t2_typ t2 ctx ;
        exp_typ
    | Proj (t1, f) as tt ->
        let exp_tt_typ = ctx.new_type_symbol TAny in
        propagate_constraints exp_tt_typ typ tt ctx ;
        let exp_t1_typ = ctx.new_type_symbol (TPartial [(f, typ)]) in
        let t1_ty = type_check_term ctx exp_t1_typ t1 in
        propagate_constraints t1_ty exp_t1_typ t1 ctx ;
        let t1_ty = type_meet ctx t1_ty exp_t1_typ in
        let f_ty =
          match t1_ty with
          | TSymb (TPartial fields, _) -> List.assoc f fields
          | TCst (TRef ctor) ->
              let _, fields = List.assoc ctor tctxt in
              TCst (List.assoc f fields)
          | _ -> failwith "typecheck_term: invalid state" in
        propagate_constraints typ f_ty tt ctx ;
        let f_ty = type_meet ctx typ f_ty in
        f_ty in
  type_check_term ctx typ term

(*
Type judgement is of the form (Δ;T;Γ) ⊢ ϕ wff  
where Δ is the predicate schema
      T is the type context
      Γ is the symbol table containing variable types
      ϕ formula 

Parameters:
  (sch, tctxt, vars) are (Δ,T,Γ)
  ϕ is an CMFOTL formula

Returns a pair (Δ',Γ') where Δ' and Γ' are the new Δ and Γ
Fails if ϕ is not a well formed formula
*)
let type_check_formula_debug (d : bool) =
  let rec type_check_formula (f : type_context cplx_formula) : unit =
    let ctx, fast = f in
    let sch, tctxt, vars = (ctx.predicates, ctx.sorts, ctx.vars) in
    if d then (
      Printf.eprintf "[Typecheck.typecheck_formula] \n%!Δ: %s\n%!Γ: %s\n%!⊢ "
        (string_of_delta tctxt sch)
        (string_of_gamma tctxt vars) ;
      Printf.eprintf "%s" (string_of_formula "" f) ;
      Printf.eprintf "\n%!\n%!" ) ;
    match fast with
    | Equal (t1, t2) | Less (t1, t2) | LessEq (t1, t2) ->
        let exp_typ = ctx.new_type_symbol TAny in
        let t1_typ = type_check_term_debug d ctx exp_typ t1 in
        propagate_constraints exp_typ t1_typ t1 ctx ;
        let exp_typ = type_meet ctx t1_typ exp_typ in
        let t2_typ = type_check_term_debug d ctx exp_typ t2 in
        propagate_constraints exp_typ t2_typ t2 ctx ;
        propagate_constraints t1_typ t2_typ t2 ctx
    | Substring (t1, t2) ->
        (* Define constant *)
        let exp_typ = TCst TStr in
        (* Type check t1 *)
        let t1_typ = type_check_term_debug d ctx exp_typ t1 in
        (* Propagate constraints t1, exp *)
        propagate_constraints exp_typ t1_typ t1 ctx ;
        (* Type check t2 *)
        let t2_typ = type_check_term_debug d ctx exp_typ t2 in
        (* Propagate constraints t2, exp *)
        propagate_constraints exp_typ t2_typ t2 ctx
    | Matches (t1, t2, tl) ->
        (* Define constant *)
        let exp_typ_1 = TCst TStr in
        (* Type check t1 *)
        let t1_typ = type_check_term_debug d ctx exp_typ_1 t1 in
        (* Propagate constraints t1, exp *)
        propagate_constraints exp_typ_1 t1_typ t1 ctx ;
        (* Define constant *)
        let exp_typ_2 = TCst TRegexp in
        (* Type check t2 *)
        let t2_typ = type_check_term_debug d ctx exp_typ_2 t2 in
        (* Propagate constraints t2, exp *)
        propagate_constraints exp_typ_2 t2_typ t2 ctx ;
        let exp_typ_group = TCst TStr in
        List.iter
          (fun t ->
            match t with
            | None -> ()
            | Some t ->
                let t_typ = type_check_term_debug d ctx exp_typ_group t in
                propagate_constraints exp_typ_group t_typ t ctx )
          tl
    | Pred p ->
        let name, arity, _ = p in
        let exp_typ_list =
          if List.mem_assoc (name, arity) sch then
            !(List.assoc (name, arity) sch)
          else
            failwith
              ( "[Typecheck.typecheck_formula] unknown predicate " ^ name ^ "/"
              ^ string_of_int arity ^ " in input formula" ) in
        let t_list = get_predicate_args p in
        if List.length t_list <> List.length exp_typ_list then
          failwith
            ( "[Typecheck.typecheck_formula] wrong arity for predicate " ^ name
            ^ " in input formula" ) ;
        let idx m =
          let rec i n = if m == n then [] else n :: i (n + 1) in
          i 0 in
        let indices = idx (List.length t_list) in
        List.iter
          (fun i ->
            let exp_t = List.nth !(List.assoc (name, arity) sch) i in
            let t = List.nth t_list i in
            let t1 = type_check_term_debug d ctx exp_t t in
            propagate_constraints exp_t t1 t ctx )
          indices
    | Let (p, f1, f2) | LetPast (p, f1, f2) ->
        let n, a, ts = p in
        type_check_formula f1 ;
        let v1 = f_annot f1 |> t_vars in
        (* throw if at least one variable in the symbol table of the predicate
           body is unresolved (= has still a symbolic type): *)
        let pred_args =
          List.map
            (fun t -> match t with Var v -> v | _ -> failwith "invalid state")
            ts in
        check_unresolved_terms (Some n) pred_args v1 ;
        (* TODO: re-enable after refactoring symbol table: *)
        (* assert (List.length v1 = List.length new_typed_vars) ; *)
        let new_sig = List.map (fun v -> (v, !(List.assoc v v1))) ts in
        let new_sig = List.map (fun (_, t) -> t) new_sig in
        (* this is a reference to the old predicate schema of this LET predicate in the inner formula.sorts
           we replace its value with the updated (type-checked) schema: *)
        let old_sch = f_annot f2 |> t_preds |> List.assoc (n, a) in
        old_sch := new_sig ;
        type_check_formula f2
    | Neg f -> type_check_formula f
    | Prev (intv, f) -> type_check_formula f
    | Next (intv, f) -> type_check_formula f
    | Eventually (intv, f) -> type_check_formula f
    | Once (intv, f) -> type_check_formula f
    | Always (intv, f) -> type_check_formula f
    | PastAlways (intv, f) -> type_check_formula f
    | And (f1, f2) -> type_check_formula f1 ; type_check_formula f2
    | Or (f1, f2) -> type_check_formula f1 ; type_check_formula f2
    | Implies (f1, f2) -> type_check_formula f1 ; type_check_formula f2
    | Equiv (f1, f2) -> type_check_formula f1 ; type_check_formula f2
    | Since (intv, f1, f2) -> type_check_formula f1 ; type_check_formula f2
    | Until (intv, f1, f2) -> type_check_formula f ; type_check_formula f
    | Exists (l, f) | ForAll (l, f) ->
        type_check_formula f ;
        check_unresolved_terms None l (f_annot f).vars
    | Aggreg (rty, r, op, x, gs, f) ->
        failwith "[type_check_formula_debug] Aggreg not implemented yet."
        (* let gs_vars = List.map projection_base gs in
           (* free vars in sub-formula and not part of group-by terms *)
           let zs = List.filter (fun v -> not (List.mem v gs_vars)) (free_vars f) in
           let zs_terms = List.map (fun z -> Var z) zs in
           let shadowed_vars, reduced_vars =
             List.partition (fun (vr, _) -> List.mem vr zs_terms) vars in
           let vars' =
             List.fold_left
               (fun vrs vr -> (vr, new_type_symbol TAny) :: vrs)
               reduced_vars zs_terms in
           let type_check_aggregation exp_typ1 exp_typ2 =
             (* Type check variable x *)
             let _ =
               type_check_term_debug d (sch, tctxt, vars') exp_typ2 x in
             (* Type check formula f *)
             let s2, v2, f = type_check_formula (s1, tctxt, v1) f in
             (* Get the updated types for gs vars *)
             let reduced_vars =
               List.filter (fun (v, _) -> List.mem_assoc v reduced_vars) v2 in
             (* Restore the top-level vars with updated vars *)
             let vars = shadowed_vars @ reduced_vars in
             (* Type check variable r *)
             let s3, v3, _ =
               type_check_term_debug d (sch, tctxt, vars) exp_typ1 (Var r) in
             let s3, v3 =
               if
                 exp_typ1 = exp_typ2
                 (* If the expected types of r and x are the same *)
               then
                 propagate_constraints (List.assoc x v2) (List.assoc (Var r) v3)
                   (Var r) (s3, tctxt, v3)
                 (* and have compatible types, propagate the more specific type *)
               else (s3, v3) in
             ( s3
             , v3
             , ((s3, tctxt, v3), Aggreg (List.assoc (Var r) v3, r, op, x, gs, f))
             ) in
           let exp_typ = new_type_symbol TAny in
           let exp_num_typ = new_type_symbol TNum in
           match op with
           | Min | Max -> type_check_aggregation exp_typ exp_typ
           | Cnt -> type_check_aggregation (TCst TInt) exp_typ
           | Sum -> type_check_aggregation exp_num_typ exp_num_typ
           | Avg | Med -> type_check_aggregation (TCst TFloat) exp_num_typ ) *)
    | Frex (intv, r) -> type_check_re_formula r
    | Prex (intv, r) -> type_check_re_formula r
  and type_check_re_formula = function
    | Wild -> ()
    | Test f -> type_check_formula f
    | Concat (r1, r2) | Plus (r1, r2) ->
        type_check_re_formula r1 ; type_check_re_formula r2
    | Star r -> type_check_re_formula r in
  type_check_formula

let first_debug = ref true

(** internal module for validating the monitorability of an extended formula. *)

module Monitorability = struct
  let msg_PRED =
    "In subformulas p(t1,...,tn) each term ti should be a variable or a \
     constant."

  let msg_EQUAL =
    "In input formulas psi of the form t1 = t2 the terms t1 and t2 should be \
     variables or constants and at least one should be a constant."

  let msg_LESS =
    "Formulas of the form t1 < t2, t1 <= t2, t1 SUBSTRING t2, and t1 MATCHES \
     t2 are currently considered not monitorable."

  let msg_NOT_EQUAL =
    "In subformulas psi of the form NOT (t1 = t2) the terms t1 and t2 should \
     be either the same variable x or some constants (except when psi is part \
     of subformulas of the form phi AND NOT psi, or phi AND NOT psi)."

  let msg_NOT =
    "Subformulas of the form NOT psi should contain no free variables (except \
     when they are part of subformulas of the form phi AND NOT psi, NOT psi \
     SINCE_I phi, or NOT psi UNTIL_I phi)."

  let msg_ANDRELOP =
    "In subformulas of the form psi AND t1 op t2 or psi AND NOT t1 op t2, with \
     op among =, <, <=, either the variables of the terms t1 and t2 are among \
     the free variables of psi or the formula is of the form psi AND x = t or \
     psi AND x = t, and the variables of the term t are among the free \
     variables of psi."

  let msg_SUBSET =
    format_of_string
      "In subformulas of the form phi AND NOT psi, psi SINCE_I phi, and psi \
       UNTIL_I phi, the free variables of psi (%s) should be among the free \
       variables of phi (%s)."

  let msg_OR =
    "In subformulas of the form phi OR psi, phi and psi should have the same \
     set of free variables."

  (** returns an extension of free variables used for validating the monitorability
    of extended formulas. The mapping is the same as `tvars`, except for the case of
    complex variables/projections: In these cases, the set of all recursive fields
    as variables are returned instead.

    Example: mtvars ctx r.user -> ["r.user.name"; "r.user.address", ...]*)
  let rec mtvars (ctx : type_context) = function
    | Cst c -> []
    | F2i t
     |I2f t
     |I2s t
     |S2i t
     |F2s t
     |S2f t
     |DayOfMonth t
     |Month t
     |Year t
     |FormatDate t
     |UMinus t
     |R2s t
     |S2r t ->
        mtvars ctx t
    | Plus (t1, t2)
     |Minus (t1, t2)
     |Mult (t1, t2)
     |Div (t1, t2)
     |Mod (t1, t2) ->
        mtvars ctx t1 @ mtvars ctx t2
    | (Var _ as t) | (Proj _ as t) -> (
        let ty = type_of_term ctx t in
        match ty with
        | TInt | TFloat | TStr | TRegexp -> [string_of_term t]
        | TRef ctor ->
            let fields = List.assoc ctor ctx.sorts |> snd in
            List.map (fun (fname, _) -> mtvars ctx (Proj (t, fname))) fields
            |> List.flatten )

  (* In these special cases, no evaluation is needed for the formula [f2]. *)
  let is_special_case (ctx : type_context) fv1 (f : 'a cplx_formula) =
    match snd f with
    | Equal (t1, t2) -> (
      match (t1, t2) with
      | Var x, t when Misc.subset (mtvars ctx t) fv1 -> true
      | t, Var x when Misc.subset (mtvars ctx t) fv1 -> true
      (* TODO: is this valid for projections:
         Use new mtvars, but still cover projections *)
      | Proj (b, _), t when Misc.subset (mtvars ctx t) fv1 -> true
      | t, Proj (b, _) when Misc.subset (mtvars ctx t) fv1 -> true
      | _ -> Misc.subset (free_vars ~tvars:(mtvars ctx) f) fv1 )
    | Matches (t1, t2, tl) ->
        Misc.subset (mtvars ctx t1) fv1
        && Misc.subset (mtvars ctx t2) fv1
        && List.for_all
             (function
               | None -> true
               | Some (Var _) -> true
               | Some t -> Misc.subset (mtvars ctx t) fv1 )
             tl
    | Less (_, _)
     |LessEq (_, _)
     |Substring (_, _)
     |Neg (_, Equal (_, _))
     |Neg (_, Less (_, _))
     |Neg (_, LessEq (_, _))
     |Neg (_, Substring (_, _))
     |Neg (_, Matches (_, _, _)) ->
        Misc.subset (free_vars ~tvars:(mtvars ctx) f) fv1
    | _ -> false

  let is_and_relop ((_, f) : 'a cplx_formula) =
    match f with
    | Equal (_, _)
     |Less (_, _)
     |LessEq (_, _)
     |Substring (_, _)
     |Matches (_, _, _)
     |Neg (_, Equal (_, _))
     |Neg (_, Less (_, _))
     |Neg (_, LessEq (_, _))
     |Neg (_, Substring (_, _))
     |Neg (_, Matches (_, _, _)) ->
        true
    | _ -> false

  (** This function tells us beforehand whether a formula is monitorable
    by MonPoly. It should thus exactly correspond to the
    implementation of the Algorithm module.

    Remark: There are a few formulae that are not TSF safe-range
    (according strictly to the given definition), but which are
    monitorable; and we could accept even a few more: see
    examples/test4.mfotl. However, there are many formulae which are
    TSF safe range but not monitorable since our propagation function
    is still quite limited.
  *)
  let rec is_monitorable (f : type_context cplx_formula) =
    let ctx = f_annot f in
    match snd f with
    | Equal (t1, t2) -> (
      match (t1, t2) with
      | Var _, Cst _ | Cst _, Var _ | Cst _, Cst _ -> (true, None)
      (* TODO: is it correct to return always false for projections?
         e.g. `u.url = "..."` by itself *)
      | Proj _, Cst _ | Cst _, Proj _ -> (false, Some (f, msg_EQUAL))
      | _ -> (false, Some (f, msg_EQUAL)) )
    | Less _ | LessEq _ | Substring _ | Matches _ -> (false, Some (f, msg_LESS))
    | Neg (_, Equal (t1, t2)) -> (
      match (t1, t2) with
      | Var x, Var y when x = y -> (true, None)
      (* TODO: is this valid for projections?
         Required for same case as above: Constraints guarantee that the expanded variables
         will be equal, covering the variable case above. *)
      | Proj (xb, xf), Proj (yb, yf) when xb = yb && xf = yf -> (true, None)
      | Cst _, Cst _ -> (true, None)
      | _ -> (false, Some (f, msg_NOT_EQUAL)) )
    | Pred p ->
        let tlist = get_predicate_args p in
        if
          List.for_all
            (* TODO: is this valid for projections?
               Required for: isBad(r.url) *)
              (fun t ->
              match t with Var _ | Cst _ | Proj _ -> true | _ -> false )
            tlist
        then (true, None)
        else (false, Some (f, msg_PRED))
    | Let (p, f1, f2) ->
        let is_mon1, r1 = is_monitorable f1 in
        if not is_mon1 then (is_mon1, r1) else is_monitorable f2
    | LetPast (p, f1, f2) ->
        let is_mon1, r1 = is_monitorable f1 in
        if not is_mon1 then (is_mon1, r1) else is_monitorable f2
    | Neg f1 ->
        if free_vars ~tvars:(mtvars ctx) f1 = [] then is_monitorable f1
        else (false, Some (f, msg_NOT))
    | And (f1, f2) -> (
        let is_mon1, r1 = is_monitorable f1 in
        if not is_mon1 then (is_mon1, r1)
        else
          let fv1 = free_vars ~tvars:(mtvars ctx) f1 in
          if is_and_relop f2 then
            if is_special_case ctx fv1 f2 then (true, None)
            else (false, Some (f, msg_ANDRELOP))
          else
            match snd f2 with
            | Neg f2' ->
                let fv2 = free_vars ~tvars:(mtvars ctx) f2 in
                if not (Misc.subset fv2 fv1) then
                  ( false
                  , Some
                      ( f
                      , Printf.sprintf msg_SUBSET (String.concat "," fv2)
                          (String.concat "," fv1) ) )
                else is_monitorable f2'
            | _ -> is_monitorable f2 )
    | Or (f1, f2) ->
        let fv1 = free_vars ~tvars:(mtvars ctx) f1 in
        let fv2 = free_vars ~tvars:(mtvars ctx) f2 in
        if (not (Misc.subset fv1 fv2)) || not (Misc.subset fv2 fv1) then
          (false, Some (f, msg_OR))
        else
          let is_mon1, r1 = is_monitorable f1 in
          if not is_mon1 then (is_mon1, r1) else is_monitorable f2
    | Exists (_, f1)
     |Aggreg (_, _, _, _, _, f1)
     |Prev (_, f1)
     |Next (_, f1)
     |Eventually (_, f1)
     |Once (_, f1) ->
        is_monitorable f1
    | Since (intv, f1, f2) | Until (intv, f1, f2) ->
        let is_mon2, msg2 = is_monitorable f2 in
        if not is_mon2 then (is_mon2, msg2)
        else
          let fv1 = free_vars ~tvars:(mtvars ctx) f1 in
          let fv2 = free_vars ~tvars:(mtvars ctx) f2 in
          if not (Misc.subset fv1 fv2) then
            ( false
            , Some
                ( f
                , Printf.sprintf msg_SUBSET (String.concat "," fv2)
                    (String.concat "," fv1) ) )
          else
            let f1' = match snd f1 with Neg f1' -> f1' | _ -> f1 in
            is_monitorable f1'
    | Frex (intv, f) ->
        failwith
          "[Rewriting.is_monitorable] The future match operator |.|> can be \
           used only with the -verified flag set"
    | Prex (intv, f) ->
        failwith
          "[Rewriting.is_monitorable] The past match operator <|.| can be used \
           only with the -verified flag set"
    (* These operators should have been eliminated *)
    | Implies _ | Equiv _ | ForAll _ | Always _ | PastAlways _ ->
        failwith
          "[Rewriting.is_monitorable] The operators IMPLIES, EQUIV, FORALL, \
           ALWAYS and PAST_ALWAYS should have been eliminated when the -no_rw \
           option is not present. If the -no_rw option is present, make sure \
           to eliminate these operators yourself."

  let print_reason str reason =
    match reason with
    | Some (f, msg) ->
        Printf.eprintf "%s, because of the subformula: %s\n%!%s\n%!" str
          (string_of_formula "" f) msg
    | None -> failwith "[Rewriting.print_reason] internal error"

  let print_results is_mon reason =
    if !Misc.verbose || !Misc.checkf then
      if is_mon then Printf.eprintf "The extended formula is monitorable.\n%!"
      else print_reason "The extended formula is NOT monitorable" reason
    else if not is_mon then
      Printf.eprintf
        "The extended formula is NOT monitorable. Use the -check or -verbose \
         flags.\n\
         %!"
end

(** initializes the type annotations for all sub formulas in the given formula.
    All free variables of a sub-formula are initialized with TAny.
    the predicate schema and tctxt are set to the given values.
    *)
let init_type_context (tsymb_id : int ref) (sch : predicate_schema)
    (tctxt : tctxt) (f : unit cplx_formula) : type_context cplx_formula =
  let new_type_symbol (cls : tcl) =
    incr tsymb_id ;
    TSymb (cls, !tsymb_id) in
  let filter_vars (vars : symbol_table) (f : var -> bool) : symbol_table =
    List.filter
      (fun (v, _) -> match v with Var v -> f v | _ -> failwith "remove")
      vars in
  (* free variables ranging over the whole formula: *)
  let global_vars : symbol_table =
    List.fold_left
      (fun vrs vr -> (Var vr, ref (new_type_symbol TAny)) :: vrs)
      [] (free_vars f) in
  let rec aux (ctx : type_context) (f : unit cplx_formula) :
      type_context cplx_formula =
    let local_vars = free_vars f in
    let filtered_vars =
      List.filter
        (fun (v, _) ->
          match v with
          | Var n -> List.mem n local_vars
          | _ -> failwith "remove after symbol_table refactoring" )
        ctx.vars in
    let fctxt =
      create_type_context ctx.predicates tctxt filtered_vars tsymb_id in
    let rec aux_regex (regex : unit regex) : type_context regex =
      match regex with
      | Wild as r -> r
      | Concat (r1, r2) -> Concat (aux_regex r1, aux_regex r2)
      | Plus (r1, r2) -> Plus (aux_regex r1, aux_regex r2)
      | Star r1 -> Star (aux_regex r1)
      | Test f -> Test (fctxt, aux fctxt f |> snd) in
    match snd f with
    | (Equal _ as f)
     |(Less _ as f)
     |(LessEq _ as f)
     |(Substring _ as f)
     |(Matches _ as f) ->
        (fctxt, f)
    | Neg f -> (fctxt, Neg (aux fctxt f))
    | And (f1, f2) -> (fctxt, And (aux fctxt f1, aux fctxt f2))
    | Or (f1, f2) -> (fctxt, Or (aux fctxt f1, aux fctxt f2))
    | Implies (f1, f2) -> (fctxt, Implies (aux fctxt f1, aux fctxt f2))
    | Equiv (f1, f2) -> (fctxt, Equiv (aux fctxt f1, aux fctxt f2))
    | Prev (i, f) -> (fctxt, Prev (i, aux fctxt f))
    | Next (i, f) -> (fctxt, Next (i, aux fctxt f))
    | Eventually (i, f) -> (fctxt, Eventually (i, aux fctxt f))
    | Once (i, f) -> (fctxt, Once (i, aux fctxt f))
    | Always (i, f) -> (fctxt, Always (i, aux fctxt f))
    | PastAlways (i, f) -> (fctxt, PastAlways (i, aux fctxt f))
    | Since (i, f1, f2) -> (fctxt, Since (i, aux fctxt f1, aux fctxt f2))
    | Until (i, f1, f2) -> (fctxt, Until (i, aux fctxt f1, aux fctxt f2))
    | Pred _ as p -> (fctxt, p)
    | Frex (i, r) -> (fctxt, Frex (i, aux_regex r))
    | Prex (i, r) -> (fctxt, Prex (i, aux_regex r))
    | Exists (l, f) ->
        let non_shadowed = filter_vars ctx.vars (fun v -> not (List.mem v l)) in
        let new_vars =
          non_shadowed
          @ List.fold_left
              (fun vrs vr -> (Var vr, ref (new_type_symbol TAny)) :: vrs)
              [] l in
        ( fctxt
        , Exists (l, aux (create_type_context sch tctxt new_vars tsymb_id) f) )
    | ForAll (l, f) ->
        let non_shadowed = filter_vars ctx.vars (fun v -> not (List.mem v l)) in
        let new_vars =
          non_shadowed
          @ List.fold_left
              (fun vrs vr -> (Var vr, ref (new_type_symbol TAny)) :: vrs)
              [] l in
        ( fctxt
        , Exists (l, aux (create_type_context sch tctxt new_vars tsymb_id) f) )
    | Let ((name, arity, targs), body, f) ->
        let arg_names =
          List.map
            (fun t -> match t with Var v -> v | _ -> failwith "invalid state")
            targs in
        let arg_types = List.map (fun a -> new_type_symbol TAny) arg_names in
        let new_vars =
          List.map2 (fun n t -> (Var n, ref t)) arg_names arg_types in
        let non_shadowed = List.filter (fun ((n, _), _) -> n <> name) sch in
        let new_sch = ((name, arity), ref arg_types) :: non_shadowed in
        ( fctxt
        , Let
            ( (name, arity, targs)
            , aux (create_type_context sch tctxt new_vars tsymb_id) body
            , aux (create_type_context new_sch tctxt ctx.vars tsymb_id) f ) )
    | LetPast ((name, arity, targs), body, f) ->
        let arg_names =
          List.map
            (fun t -> match t with Var v -> v | _ -> failwith "invalid state")
            targs in
        let arg_types = List.map (fun a -> new_type_symbol TAny) arg_names in
        let new_vars =
          List.map2 (fun n t -> (Var n, ref t)) arg_names arg_types in
        let new_sch = ((name, arity), ref arg_types) :: sch in
        ( fctxt
        , LetPast
            ( (name, arity, targs)
            , aux (create_type_context sch tctxt new_vars tsymb_id) body
            , aux (create_type_context new_sch tctxt ctx.vars tsymb_id) f ) )
    | Aggreg (rty, r, op, x, gs, f) ->
        failwith "init_type_context: Aggreg not implemented yet" in
  let typed_formula =
    aux (create_type_context sch tctxt global_vars tsymb_id) f in
  typed_formula

(** type checks a complex formula given matching signature definitions.
    Returns a triple consiting of:
    1) The type checking context consisting of predicate schema, symbol table and type context.
    2) A possibly updated version of the input formula.
    3) A boolean flag indicating the monitorability (safety) of the input formula. *)
let rec typecheck_formula (signatures : signatures) (f : unit cplx_formula) :
    type_context cplx_formula * bool =
  let debug = !first_debug && Misc.debugging Dbg_typing in
  (* first of all check well-formedness of formula: *)
  ignore @@ ignore (check_wff f) ;
  let lift_type t = TCst t in
  (* create Δ *)
  let sch : predicate_schema =
    List.fold_left
      (fun acc decl ->
        match decl with
        | Predicate {elt= name, args; _} ->
            let lifted_args =
              extr_nodes args |> List.map (fun {atyp; _} -> lift_type atyp)
            in
            ((name, List.length args), ref lifted_args) :: acc
        | ProductSort (attrs, {elt= name, fields; _}) ->
            (* do not add inline records to predicate schema: *)
            if not attrs.inline then
              let rec_pred = ((name, 1), ref [TCst (TRef name)]) in
              rec_pred :: acc
            else acc )
      [] signatures in
  (* create T *)
  let tctxt : tctxt =
    List.fold_left
      (fun acc decl ->
        match decl with
        | Predicate _ -> acc
        | ProductSort (attrs, {elt= name, fields; _}) ->
            ( name
            , ( attrs.inline
              , extr_nodes fields
                |> List.map (fun {fname; ftyp} -> (fname, ftyp)) ) )
            :: acc )
      [] signatures in
  let tsymb_index = ref 0 in
  let f = init_type_context tsymb_index sch tctxt f in
  type_check_formula_debug debug f ;
  let ctx = f_annot f in
  (* Make sure all variables in the symbol table have been resolved
     to a concrete type. *)
  check_unresolved_terms None (free_vars f) ctx.vars ;
  if debug then (
    Printf.eprintf
      "[Typecheck.typecheck_formula] The final type judgement is (%s; %s) ⊢ "
      (string_of_delta tctxt sch)
      (string_of_gamma tctxt ctx.vars) ;
    Printf.eprintf "%s" (string_of_formula "" f) ;
    Printf.eprintf "\n%!" ) ;
  first_debug := false ;
  (* check and print monitorablity results: *)
  let is_mon, reason = Monitorability.is_monitorable f in
  if not is_mon then Monitorability.print_results is_mon reason ;
  (f, is_mon)

(* COMPILE FUNCTIONS *)

let compile_tcst (tcst : tcst) : Predicate.tcst =
  match tcst with
  | TInt -> TInt
  | TFloat -> TFloat
  | TStr -> TStr
  | TRegexp -> TRegexp
  | TRef _ -> TInt

(** The full path of a given projection term.
    Example: The term r.user.name maps to the string 'r_user_name' *)
let rec projection_path = function
  | Var v -> v
  | Proj (t, f) -> Printf.sprintf "%s_%s" (projection_path t) f
  | t ->
      failwith
      @@ Printf.sprintf "[CMFOTL.projection_path]: Invalid term detected: %s"
           (string_of_term t)

let cplx_conjunction (fdata : 'a) (fs : 'a cplx_formula list) : 'a cplx_formula
    =
  List.fold_left (fun acc f -> (fdata, And (acc, f))) (List.hd fs) (List.tl fs)

let conjunction (fs : MFOTL.formula list) : MFOTL.formula =
  List.fold_left (fun acc f -> MFOTL.And (acc, f)) (List.hd fs) (List.tl fs)

(** Accpets a variable name of a free complex variable and
      expands it based on its usage in the given formula.
      It returns a new conjunction and a set of new variables introduced
      by the expansion. *)
let expand_cplx_var (f : 'a cplx_formula) (ctx : type_context) (var : var) :
    MFOTL.formula * var list =
  let tctxt = ctx.sorts in
  let get_ref_type t =
    let ty = type_check_term_debug false ctx (TSymb (TAny, -1)) t in
    match ty with
    | TCst (TRef r) -> r
    | _ ->
        failwith
        @@ Printf.sprintf "could not find ref type of %s: is of type %s"
             (string_of_term t) (string_of_type tctxt ty) in
  let usages = get_var_usage f var |> TermSet.elements in
  (* list of triples: (ctor, Record, prefix) *)
  let required_expansions =
    List.fold_right
      (fun u acc ->
        match u with
        | (Var _ as b) | Proj (b, _) ->
            let ctor = get_ref_type b in
            let record = List.assoc ctor tctxt |> snd in
            (ctor, record, projection_path b) ^:: acc
        | _ -> acc )
      usages [] in
  let expansions =
    List.map
      (fun (ctor, record, prefix) ->
        let new_vars = List.map (fun (n, _) -> prefix ^ "_" ^ n) record in
        let new_pred =
          MFOTL.Pred
            ( ctor
            , List.length new_vars + 1
            , Var prefix :: List.map (fun v -> Predicate.Var v) new_vars ) in
        (new_pred, new_vars) )
      required_expansions in
  let new_preds, new_vars = List.split expansions in
  (conjunction new_preds, List.flatten new_vars)

(** returns a list of free complex variable names in the given symbol table.
    If the provided accept_list is not empty, only variables contained in this list are returned. *)
let free_ref_vars (vars : symbol_table) (accept_list : var list) =
  let filter_var v = List.length accept_list = 0 || List.mem v accept_list in
  List.fold_left
    (fun acc (t, ty) ->
      match (t, !ty) with
      | Var v, TCst (TRef _) -> if filter_var v then v :: acc else acc
      | _ -> acc )
    [] vars

(** accepts two sides of an equality and returns a formula comparing both sides
    recursively/structurally. The returned formula  replaces the original equality. *)
let expand_structural_equality (ctx : type_context) (left : cplx_term)
    (right : cplx_term) : 'a cplx_formula =
  let rec terms left right =
    let left_ty, right_ty = (type_of_term ctx left, type_of_term ctx right) in
    if compare left_ty right_ty <> 0 then
      failwith
      @@ Printf.sprintf
           "expand_structural_equality: type %s of %s is not equal to type %s \
            of %s"
           (string_of_term left) (string_of_ty left_ty) (string_of_term right)
           (string_of_ty right_ty) ;
    match left_ty with
    | TRef ctor ->
        let fields = List.assoc ctor ctx.sorts |> snd in
        List.map
          (fun (name, _) -> terms (Proj (left, name)) (Proj (right, name)))
          fields
        |> List.flatten
    | _ -> [(ctx, Equal (left, right))] in
  cplx_conjunction ctx (terms left right)

(** pre-processes the given complex formula before the actual compilation step.
    Should be run once before compiling on the input formula. *)
let rec preprocess_formula (f : type_context cplx_formula) : 'a cplx_formula =
  let fdata, fast = f in
  match fast with
  | Equal (t1, t2) -> expand_structural_equality fdata t1 t2
  | Let (p, f1, f2) ->
      (fdata, Let (p, preprocess_formula f1, preprocess_formula f2))
  | LetPast (p, f1, f2) ->
      (fdata, LetPast (p, preprocess_formula f1, preprocess_formula f2))
  | Neg f -> (fdata, Neg (preprocess_formula f))
  | And (f1, f2) -> (fdata, And (preprocess_formula f1, preprocess_formula f2))
  | Or (f1, f2) -> (fdata, Or (preprocess_formula f1, preprocess_formula f2))
  | Implies (f1, f2) ->
      (fdata, Implies (preprocess_formula f1, preprocess_formula f2))
  | Equiv (f1, f2) ->
      (fdata, Equiv (preprocess_formula f1, preprocess_formula f2))
  | Exists (vl, f) -> (fdata, Exists (vl, preprocess_formula f))
  | ForAll (vl, f) -> (fdata, ForAll (vl, preprocess_formula f))
  | Aggreg (rty, y, op, x, glist, f) ->
      (fdata, Aggreg (rty, y, op, x, glist, preprocess_formula f))
  | Prev (intv, f) -> (fdata, Prev (intv, preprocess_formula f))
  | Next (intv, f) -> (fdata, Next (intv, preprocess_formula f))
  | Eventually (intv, f) -> (fdata, Eventually (intv, preprocess_formula f))
  | Once (intv, f) -> (fdata, Once (intv, preprocess_formula f))
  | Always (intv, f) -> (fdata, Always (intv, preprocess_formula f))
  | PastAlways (intv, f) -> (fdata, PastAlways (intv, preprocess_formula f))
  | Since (intv, f1, f2) ->
      (fdata, Since (intv, preprocess_formula f1, preprocess_formula f2))
  | Until (intv, f1, f2) ->
      (fdata, Until (intv, preprocess_formula f1, preprocess_formula f2))
  | f -> (fdata, fast)

let rec postprocess_formula (f : MFOTL.formula) : MFOTL.formula =
  match f with
  | Let (p, f1, f2) -> Let (p, postprocess_formula f1, postprocess_formula f2)
  | LetPast (p, f1, f2) ->
      LetPast (p, postprocess_formula f1, postprocess_formula f2)
  | Neg f -> Neg (postprocess_formula f)
  | And (f1, And (f2, f3)) ->
      And
        ( postprocess_formula
            (And (postprocess_formula f1, postprocess_formula f2))
        , postprocess_formula f3 )
  | And (f1, f2) -> And (postprocess_formula f1, postprocess_formula f2)
  | Or (f1, f2) -> Or (postprocess_formula f1, postprocess_formula f2)
  | Implies (f1, f2) -> Implies (postprocess_formula f1, postprocess_formula f2)
  | Equiv (f1, f2) -> Equiv (postprocess_formula f1, postprocess_formula f2)
  | Exists (vl, f) -> Exists (vl, postprocess_formula f)
  | ForAll (vl, f) -> ForAll (vl, postprocess_formula f)
  | Aggreg (rty, y, op, x, glist, f) ->
      Aggreg (rty, y, op, x, glist, postprocess_formula f)
  | Prev (intv, f) -> Prev (intv, postprocess_formula f)
  | Next (intv, f) -> Next (intv, postprocess_formula f)
  | Eventually (intv, f) -> Eventually (intv, postprocess_formula f)
  | Once (intv, f) -> Once (intv, postprocess_formula f)
  | Always (intv, f) -> Always (intv, postprocess_formula f)
  | PastAlways (intv, f) -> PastAlways (intv, postprocess_formula f)
  | Since (intv, f1, f2) ->
      Since (intv, postprocess_formula f1, postprocess_formula f2)
  | Until (intv, f1, f2) ->
      Until (intv, postprocess_formula f1, postprocess_formula f2)
  | f -> f

let compile_cst (cst : cst) : Predicate.cst =
  match cst with
  | Int v -> Int v
  | Float v -> Float v
  | Str v -> Str v
  | Regexp v -> Regexp v
  | Record _ -> failwith "invalid state"

let rec compile_term (input : cplx_term) : Predicate.term =
  match input with
  | Var v -> Var v
  | Cst c -> Cst (compile_cst c)
  | F2i t -> F2i (compile_term t)
  | I2f t -> I2f (compile_term t)
  | I2s t -> I2s (compile_term t)
  | S2i t -> S2i (compile_term t)
  | F2s t -> F2s (compile_term t)
  | S2f t -> S2f (compile_term t)
  | DayOfMonth t -> DayOfMonth (compile_term t)
  | Month t -> Month (compile_term t)
  | Year t -> Year (compile_term t)
  | FormatDate t -> FormatDate (compile_term t)
  | R2s t -> R2s (compile_term t)
  | S2r t -> S2r (compile_term t)
  | Plus (t1, t2) -> Plus (compile_term t1, compile_term t2)
  | Minus (t1, t2) -> Minus (compile_term t1, compile_term t2)
  | UMinus t -> UMinus (compile_term t)
  | Mult (t1, t2) -> Mult (compile_term t1, compile_term t2)
  | Div (t1, t2) -> Div (compile_term t1, compile_term t2)
  | Mod (t1, t2) -> Mod (compile_term t1, compile_term t2)
  | Proj (t, field) -> Var (projection_path t ^ "_" ^ field)

let compile_predicate (ctx : type_context) ((name, arity, args) : cplx_predicate)
    : predicate =
  (name, arity, List.map (fun t -> compile_term t) args)

(* compiles the given formula and expands all complex free variables.
   The given filter is used to only expand a certain set of free variables. If the filter is empty,
   all free variables in the formula's scope are expanded. *)
let rec compile_formula_scope (var_filter : var list) (f : 'a cplx_formula) :
    MFOTL.formula =
  let ctx = f_annot f in
  let free_cplx_vars = free_ref_vars ctx.vars var_filter in
  let _, new_vars_list =
    List.map (expand_cplx_var f ctx) free_cplx_vars |> List.split in
  (* Compile the given input formula and wrap it with an EXISTS quantifier,
     binding all variables introduced by the expansion above: *)
  let new_vars = List.flatten new_vars_list in
  let compiled = _compile_formula ctx f f in
  if List.length new_vars = 0 then compiled
  else MFOTL.Exists (new_vars, compiled)

(** compiles a given complex formula to an MFOTL compatible formula under the given typecheck context.
    f_scope describes the current variable scope. *)
and _compile_formula (ctx : type_context) (f_scope : 'a cplx_formula)
    (input : 'a cplx_formula) : MFOTL.formula =
  match snd input with
  | Equal (t1, t2) -> MFOTL.Equal (compile_term t1, compile_term t2)
  | Less (t1, t2) -> Less (compile_term t1, compile_term t2)
  | LessEq (t1, t2) -> LessEq (compile_term t1, compile_term t2)
  | Substring (t1, t2) -> Substring (compile_term t1, compile_term t2)
  | Matches (t1, t2, tl) ->
      Matches
        ( compile_term t1
        , compile_term t2
        , List.map
            (function Some t -> Some (compile_term t) | None -> None)
            tl )
  | Pred (name, arity, args) -> (
    match List.assoc_opt name ctx.sorts with
    (* no type predicate -> only compile arguments: *)
    | None -> Pred (name, arity, List.map compile_term args)
    (* type predicate: Expand it and introduce new predicates based on the complex argument's
       usage in the current formula scope.
       example: predicate Request(r) and r.user.name in current scope:
       Request(r, r_url, r_user, ...) AND User(r_user, r_user_name, ...) *)
    | Some (_, fields) ->
        let var_name =
          match args with
          | [Var v] -> v
          | ts ->
              let msg =
                Printf.sprintf
                  "Expected predicate '%s' to accept a single variable \
                   argument, but found %s"
                  name
                  (List.map string_of_term ts |> String.concat ",") in
              failwith msg in
        let expansions, _ =
          List.map (expand_cplx_var f_scope ctx) [var_name] |> List.split in
        conjunction expansions )
  | Let (p, f1, f2) ->
      let n, a, ts = p in
      let arg_vars =
        List.fold_left
          (fun acc t -> match t with Var v -> v :: acc | _ -> acc)
          [] ts in
      Let
        ( compile_predicate ctx p
        , compile_formula_scope arg_vars f1
        , _compile_formula ctx f_scope f2 )
  | LetPast (p, f1, f2) ->
      let n, a, ts = p in
      let arg_vars =
        List.fold_left
          (fun acc t -> match t with Var v -> v :: acc | _ -> acc)
          [] ts in
      LetPast
        ( compile_predicate ctx p
        , compile_formula_scope arg_vars f1
        , _compile_formula ctx f_scope f2 )
  | Neg f -> Neg (_compile_formula ctx f_scope f)
  | And (f1, f2) ->
      And (_compile_formula ctx f_scope f1, _compile_formula ctx f_scope f2)
  | Or (f1, f2) ->
      Or (_compile_formula ctx f_scope f1, _compile_formula ctx f_scope f2)
  | Implies (f1, f2) ->
      Implies (_compile_formula ctx f_scope f1, _compile_formula ctx f_scope f2)
  | Equiv (f1, f2) ->
      Equiv (_compile_formula ctx f_scope f1, _compile_formula ctx f_scope f2)
  | Exists (l, f) -> Exists (l, compile_formula_scope l f)
  | ForAll (l, f) -> ForAll (l, compile_formula_scope l f)
  | Aggreg (rty, r, op, x, gs, f) ->
      (* let sch, _, vars = ctx in
         let gs_vars = List.map projection_base gs in
         (* free vars in sub-formula and not part of group-by terms *)
         let zs = List.filter (fun v -> not (List.mem v gs_vars)) (free_vars f) in
         let zs_terms = List.map (fun z -> Var z) zs in
         let shadowed_vars, reduced_vars =
           List.partition (fun (vr, _) -> List.mem vr zs_terms) vars in
         let new_vars =
           List.fold_left
             (fun vrs vr ->
               (vr, new_type_symbol TAny sch (List.append shadowed_vars vrs))
               :: vrs )
             reduced_vars zs_terms in
         let x = _compile_formula (s, tctxt, v) f in *)
      failwith "not implemented"
  | Prev (i, f) -> Prev (i, _compile_formula ctx f_scope f)
  | Next (i, f) -> Next (i, _compile_formula ctx f_scope f)
  | Eventually (i, f) -> Eventually (i, _compile_formula ctx f_scope f)
  | Once (i, f) -> Once (i, _compile_formula ctx f_scope f)
  | Always (i, f) -> Always (i, _compile_formula ctx f_scope f)
  | PastAlways (i, f) -> PastAlways (i, _compile_formula ctx f_scope f)
  | Since (i, f1, f2) ->
      Since (i, _compile_formula ctx f_scope f1, _compile_formula ctx f_scope f2)
  | Until (i, f1, f2) ->
      Since (i, _compile_formula ctx f_scope f1, _compile_formula ctx f_scope f2)
  | Frex (i, r) -> Frex (i, compile_regex ctx f_scope r)
  | Prex (i, r) -> Prex (i, compile_regex ctx f_scope r)

and compile_regex (ctx : type_context) (scope : 'a cplx_formula)
    (input : 'a regex) : MFOTL.regex =
  match input with
  | Wild -> Wild
  | Test f -> Test (_compile_formula ctx scope f)
  | Concat (r1, r2) ->
      Concat (compile_regex ctx scope r1, compile_regex ctx scope r2)
  | Plus (r1, r2) ->
      Plus (compile_regex ctx scope r1, compile_regex ctx scope r2)
  | Star r -> Star (compile_regex ctx scope r)

(** compiles a MFOTL formula from a complex formula and the parsed signature definitions.
    Returns the compiled formula and a flag indicating the monitoriability of the formula. *)
let compile_formula (signatures : signatures) (f : type_context cplx_formula) :
    MFOTL.formula =
  let f = preprocess_formula f in
  let output = compile_formula_scope [] f in
  let output = postprocess_formula output in
  if Misc.debugging Dbg_rewriting then
    Printf.eprintf
      "\n%!\n%![Rewriting.compile_formula] The compilation output is %s\n%!\n%!"
      (MFOTL.string_of_formula "" output) ;
  output
