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

(* COMMON HELPERS (may be moved to another module?) *)

(** function composition operator *)
let ( << ) f g a = f (g a)

(** Same as :: operator, but does not add duplicates to the list. *)
let ( ^:: ) v l = if List.mem v l then l else v :: l

(** Accepts a list of lists and flattens them by removing any duplicates.
    Uses sort_unique with compare, hence the output will be sorted. *)
let flatten_unique l = List.flatten l |> List.sort_uniq compare

(** filters a list of optional values by removing all None entries. *)
let filter_some l =
  List.fold_right
    (fun v acc -> match v with Some v -> v :: acc | None -> acc)
    l []

(* DATA STRUCTURES *)
type tcst = Signature_ast.ty

type tcl = TNum | TAny | TOrd | TRecord of (string * ty) list
and ty = TSymb of (tcl * int) | TCst of tcst | TNever

(** represents a single custom product sort *)
type sort = {inline: bool; fields: (string * tcst) list}

(** Γ *)
type symbol_table = (string * ty ref) list

and cst_bool = True | False

and cst =
  | Int of Z.t
  | Str of string
  | Float of float
  (* (string used to produce the regexp, the compiled regexp) because Str library doesn't provide regexp to string functionality *)
  | Regexp of (string * Str.regexp)
  | Record of (string * (string * cplx_term) list)
  | Bool of cst_bool
  | Null

(** Δ *)
and predicate_schema = ((string * int) * ty ref list) list

(** T *)
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

and type_context =
  { predicates: predicate_schema
  ; sorts: custom_sorts
  ; vars: symbol_table
  ; new_type_symbol: tcl -> ty }

let type_of_cst = function
  | Int _ -> TInt
  | Str _ -> TStr
  | Float _ -> TFloat
  | Regexp _ -> TRegexp
  | Record (ctor, _) -> TRef ctor
  | Bool _ -> TBool
  | Null -> TNull

module TermSet = Set.Make (struct
  type t = cplx_term

  let compare = compare
end)

(* predicate = name, arity, and list of arguments *)
type cplx_predicate = string * int * cplx_term list

let get_predicate_args ((name, ar, args) : cplx_predicate) = args

(** assigns a new type to an existing variable in the given symbol table. *)
let update_var_ty (vars : symbol_table) (var : var) (new_ty : ty) : unit =
  List.iter (fun (v, tyr) -> if v == var then tyr := new_ty) vars

(** returns the free variables in a given term *)
let rec tvars : cplx_term -> var list = function
  | Var v -> [v]
  | Cst (Record (_, cfields)) ->
      List.map (fun (_, v) -> tvars v) cfields |> List.flatten
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

(** returns the AST of a formula *)
let f_ast = snd

(** returns the formula annotations *)
let f_annot = fst

(** calls the given visitor function for the given formula
    and every contained subformula top down. *)
let rec walk_formula (visitor : 'a cplx_formula -> unit) (f : 'a cplx_formula) =
  visitor f ;
  match f_ast f with
  | Equal _ | Less _ | LessEq _ | Substring _ | Matches _ | Pred _ -> ()
  | Let (_, b, f) | LetPast (_, b, f) ->
      walk_formula visitor b ; walk_formula visitor f
  | Neg f -> walk_formula visitor f
  | And (f1, f2) | Or (f1, f2) | Implies (f1, f2) | Equiv (f1, f2) ->
      walk_formula visitor f1 ; walk_formula visitor f2
  | Exists (_, f) | ForAll (_, f) -> walk_formula visitor f
  | Aggreg (_, _, _, _, f) -> walk_formula visitor f
  | Prev (_, f)
   |Next (_, f)
   |Eventually (_, f)
   |Once (_, f)
   |Always (_, f)
   |PastAlways (_, f) ->
      walk_formula visitor f
  | Since (_, f1, f2) | Until (_, f1, f2) ->
      walk_formula visitor f1 ; walk_formula visitor f2
  | Frex (_, r) | Prex (_, r) -> walk_regex visitor r

and walk_regex (visitor : 'a cplx_formula -> unit) = function
  | Wild -> ()
  | Star r -> walk_regex visitor r
  | Plus (r1, r2) | Concat (r1, r2) ->
      walk_regex visitor r1 ; walk_regex visitor r2
  | Test f -> walk_formula visitor f

(** Accepts a variable 'var' and returns a set of terms depending on 'var'.
    The returned terms are either of type Var or Proj.
    Example: get_var_usage r (Request(r) AND r.user.name = "" AND EXISTS r . Report(r) AND r.reason = "")
    -> [r, r.user.name]. *)
let rec var_usage ((_, f) : 'a cplx_formula) (var : var) : TermSet.t =
  let rec term_usage = function
    | Cst _ -> TermSet.empty
    | Var v -> if v = var then TermSet.singleton (Var v) else TermSet.empty
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
  let var_usage_re r =
    match r with
    | Wild | Concat _ | Plus _ | Star _ -> TermSet.empty
    | Test f -> var_usage f var in
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
  | Neg f1 -> var_usage f1 var
  | And (f1, f2) | Or (f1, f2) | Implies (f1, f2) | Equiv (f1, f2) ->
      TermSet.union (var_usage f1 var) (var_usage f2 var)
  | Exists (vs, f1) | ForAll (vs, f1) ->
      (* do not visit nested scope if var is shadowed: *)
      if not (List.mem var vs) then var_usage f1 var else TermSet.empty
  | Let (p, f1, f2) | LetPast (p, f1, f2) ->
      (* free variables in f1 (body of LET) have to be arguments to p by definition,
         and therefore always shadow variables from outer scope. *)
      var_usage f2 var
  | Prev (_, f1)
   |Next (_, f1)
   |Eventually (_, f1)
   |Once (_, f1)
   |Always (_, f1)
   |PastAlways (_, f1) ->
      var_usage f1 var
  | Since (_, f1, f2) | Until (_, f1, f2) ->
      TermSet.union (var_usage f1 var) (var_usage f2 var)
  | Frex (_, r) | Prex (_, r) -> var_usage_re r
  | Aggreg (s, _, _, gs, f) ->
      TermSet.of_list
        (List.map (fun v -> Var v) gs @ if s = var then [Var s] else [])

(** Returns a list of free variables in the given formula.
    One can provide an optional tvars function to be used,
    returning the free variables for a given term. Default is `tvars`. *)
let rec free_vars
    ?(tvars : 'a -> cplx_term -> var list = fun (_ : 'a) t -> tvars t)
    ((annot, f) : 'a cplx_formula) =
  match f with
  | Equal (t1, t2) | Less (t1, t2) | LessEq (t1, t2) | Substring (t1, t2) ->
      Misc.union (tvars annot t1) (tvars annot t2)
  | Matches (t1, t2, tl) ->
      let fv = Misc.union (tvars annot t1) (tvars annot t2) in
      List.fold_left
        (fun s t ->
          match t with None -> s | Some t -> Misc.union s (tvars annot t) )
        fv tl
  | Pred p ->
      List.map (fun t -> tvars annot t) (get_predicate_args p) |> flatten_unique
  | Let (_, _, f) -> free_vars ~tvars f
  | LetPast (_, _, f) -> free_vars ~tvars f
  | Neg f -> free_vars ~tvars f
  | And (f1, f2) | Or (f1, f2) | Implies (f1, f2) | Equiv (f1, f2) ->
      Misc.union (free_vars ~tvars f1) (free_vars ~tvars f2)
  | Exists (vl, f) | ForAll (vl, f) ->
      List.filter (fun x -> not (List.mem x vl)) (free_vars ~tvars f)
  | Aggreg (y, op, x, glist, f) -> y :: glist
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

and free_re_vars ?(tvars = fun (_ : 'a) t -> tvars t) = function
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
  | Aggreg (_, _, _, _, f) -> is_mfodl f
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

let rec string_of_tcst (sorts : custom_sorts) = function
  | TFloat -> "Float"
  | TInt -> "Int"
  | TStr -> "String"
  | TRegexp -> "Regexp"
  | TBool -> "Bool"
  | TNull -> "Null"
  | TRef ctor -> (
    (* print their structure instead of teir ctor name for inline type *)
    match List.assoc ctor sorts with
    | {inline= false; _} -> Printf.sprintf "%s" ctor
    | {fields; _} ->
        "{"
        ^ ( List.map
              (fun (name, typ) -> name ^ ": " ^ string_of_tcst sorts typ)
              fields
          |> String.concat ", " )
        ^ "}" )

let rec string_of_tsymb (sorts : custom_sorts) = function
  | TCst t -> string_of_tcst sorts t
  | TSymb (TNum, a) -> "(Num t" ^ string_of_int a ^ ") =>  t" ^ string_of_int a
  | TSymb (TOrd, a) -> "(TOrd t" ^ string_of_int a ^ ") =>  t" ^ string_of_int a
  | TSymb (TRecord fs, a) ->
      Printf.sprintf "t%i{%s}" a
        ( List.map (fun (n, t) -> n ^ ":" ^ string_of_tsymb sorts t) fs
        |> String.concat ", " )
  | TSymb (TAny, a) -> "t" ^ string_of_int a
  | TNever -> "Never"

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
  | Bool t -> ( match t with True -> "true" | False -> "false" )
  | Null -> "null"
  | Record (ctor, fields) ->
      Printf.sprintf "%s {%s}" ctor
        ( List.map (fun (n, v) -> n ^ ": " ^ string_of_term v) fields
        |> String.concat ", " )

and string_of_term term =
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
let string_of_formula str ?(string_of_annot : 'a -> string = fun _ -> "")
    ((fdata, g) : 'a cplx_formula) =
  let pps = String.split_on_char '\n' str in
  let padding =
    if pps == [] then ""
    else String.map (fun s -> ' ') (List.nth pps (List.length pps - 1)) in
  let rec string_f_rec top par ((fdata, h) : 'a cplx_formula) =
    let str =
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
            | Aggreg (y, op, x, glist, f) ->
                string_of_term (Var y) ^ " <- " ^ MFOTL.string_of_agg_op op
                ^ " " ^ x
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
                "|>"
                ^ MFOTL.string_of_interval intv
                ^ string_r_rec false false r
            | Prex (intv, r) ->
                "<|"
                ^ MFOTL.string_of_interval intv
                ^ string_r_rec false false r
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
                      ^ " = " ^ string_f_rec false true f1 ^ "\n" ^ padding
                      ^ "IN" ^ " "
                      ^ string_f_rec false false f2
                  | LetPast (p, f1, f2) ->
                      "LETPAST" ^ " "
                      ^ string_f_rec false true (fdata, Pred p)
                      ^ " = " ^ string_f_rec false true f1 ^ "\n" ^ padding
                      ^ "IN" ^ " "
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
          ^ if par && not top then ")" else "" in
    let annot = string_of_annot fdata in
    if String.length annot > 0 then str ^ " [" ^ annot ^ "]" else str
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
let string_of_parenthesized_formula str
    ?(string_of_annot : 'a -> string = fun _ -> "")
    ((fdata, g) : 'a cplx_formula) =
  let pps = String.split_on_char '\n' str in
  let padding =
    if pps == [] then ""
    else String.map (fun s -> ' ') (List.nth pps (List.length pps - 1)) in
  let rec string_f_rec top par ((fdata, h) : 'a cplx_formula) =
    let str =
      match h with
      | Equal (t1, t2) ->
          "(" ^ string_of_term t1 ^ " = " ^ string_of_term t2 ^ ")"
      | Less (t1, t2) ->
          "(" ^ string_of_term t1 ^ " < " ^ string_of_term t2 ^ ")"
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
        | Aggreg (y, op, x, glist, f) ->
            "(" ^ string_of_term (Var y) ^ " <- " ^ MFOTL.string_of_agg_op op
            ^ " " ^ x
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
          | _ -> failwith "[print_formula] impossible" ) ) in
    let annot = string_of_annot fdata in
    if String.length annot > 0 then str ^ " [" ^ annot ^ "]" else str
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

let string_of_delta (sorts : custom_sorts) (sch : predicate_schema) : string =
  if List.length sch > 0 then
    let string_of_types ts =
      if List.length ts > 0 then
        let ft = List.hd ts in
        List.fold_left
          (fun a e -> a ^ ", " ^ string_of_tsymb sorts !e)
          (string_of_tsymb sorts !ft)
          (List.tl ts)
      else "()" in
    let fp, fs = List.hd sch in
    List.fold_left
      (fun a (p, ts) -> a ^ ", " ^ fst p ^ "(" ^ string_of_types ts ^ ")")
      (fst fp ^ "(" ^ string_of_types fs ^ ")")
      (List.tl sch)
  else "_"

let string_of_gamma (sorts : custom_sorts) (vars : symbol_table) =
  if List.length vars > 0 then
    let fv, ft = List.hd vars in
    List.fold_left
      (fun a (v, t) -> a ^ ", " ^ v ^ ":" ^ string_of_tsymb sorts !t)
      (fv ^ ":" ^ string_of_tsymb sorts !ft)
      (List.tl vars)
  else "_"

(* TYPE CHECKING *)

(** Returns the variable identifier of the given term
    or throws if the term is not a variable. *)
let expect_var = function
  | Var v -> v
  | t -> failwith @@ Printf.sprintf "Expected Var, got %s" (string_of_term t)

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
   |Aggreg (_, _, _, _, f)
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
    | Neg f | Exists (_, f) | ForAll (_, f) | Aggreg (_, _, _, _, f) ->
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
     |Aggreg (_, _, _, _, f)
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
  | Aggreg (y, op, x, g, f) as a ->
      let sf = check_aggregations f in
      let ffv = free_vars f in
      let check =
        sf
        (* the resulting var cannot be part of the group-by vars: *)
        && (not (List.mem y g))
        (* the base of x has to be part of the free variables in the sub-formula *)
        && List.mem x ffv in
      if check then check
      else
        failwith
          ( "[Typecheck.check_aggregations] Aggregation "
          ^ string_of_formula "" (fdata, a)
          ^ " is not well formed. " ^ "Variable " ^ y
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

let check_wff (f : 'a cplx_formula) =
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

exception IncompatibleTypes of ty * ty

module TypeMap = Map.Make (struct
  type t = ty

  let compare = compare
end)

(** describes the 'more-precise' relation of a subset of all types.
    All product-related types are not included, because their 'more-precise
    relation depends dynamically on their structure. *)
let type_lattice =
  [ (TCst TBool, TAny); (TCst TNull, TAny); (TCst TInt, TNum)
  ; (TCst TFloat, TNum); (TCst TStr, TOrd); (TCst TRegexp, TOrd)
  ; (TSymb (TNum, 0), TOrd); (TSymb (TOrd, 0), TAny) ]
  |> List.to_seq |> TypeMap.of_seq

(** returns whether ty1 is more precise than t2 based on the 'type_lattice' relation.
    If one of the two types is not part of the type_lattice relation the result is always false. *)
let rec is_more_precise (ty1 : ty) (ty2 : ty) : bool =
  let gen = function TSymb (cls, _) -> TSymb (cls, 0) | t -> t in
  if TypeMap.mem (gen ty1) type_lattice then
    let next = TSymb (TypeMap.find (gen ty1) type_lattice, 0) in
    next = gen ty2 || is_more_precise next ty2
  else false

(* compares two types for structural equality.
   Returns either true of false (no order). *)
let rec compare_tcst (sorts : custom_sorts) t1 t2 =
  match (t1, t2) with
  | TRef ctor1, TRef ctor2 ->
      let {fields= fs1; _}, {fields= fs2; _} =
        (List.assoc ctor1 sorts, List.assoc ctor2 sorts) in
      (* compare fields recursively. They are allowed to be in different order. *)
      if List.length fs1 <> List.length fs2 then false
      else
        List.for_all
          (fun (f1, t1) ->
            match List.assoc_opt f1 fs2 with
            | None -> false
            | Some t2 -> compare_tcst sorts t1 t2 )
          fs1
  | t1, t2 -> t1 = t2

(** Returns the meet of the two given types.
    Raises an IncompatibleTypes exception whenever the meet of the two types is the bottom type. *)
let rec type_meet (tctxt : type_context) (t1 : ty) (t2 : ty) : ty =
  (* first use the more-precise relation whenever possible and return
     the more precise type of the two: *)
  if is_more_precise t1 t2 then t1
  else if is_more_precise t2 t1 then t2
  else
    let sorts = tctxt.sorts in
    match (t1, t2) with
    (* the meet of two constant types can only exist if they are structurally equal.
       if both are TRef types, we return the named typed in favor of any inline type: *)
    | (TCst (TRef c1 as ref1) as t1), (TCst (TRef c2 as ref2) as t2) ->
        let ttt =
          if compare_tcst sorts ref1 ref2 then
            if (List.assoc c1 sorts).inline then t2 else t1
          else raise (IncompatibleTypes (t1, t2)) in
        ttt
    | (TCst a as t1), TCst b ->
        if compare_tcst sorts a b then t1 else raise (IncompatibleTypes (t1, t2))
    (* for two symbolic types of equal type class, return the one with lower identifier: *)
    | TSymb (cls1, n1), TSymb (cls2, n2) when cls1 = cls2 ->
        TSymb (cls1, min n1 n2)
    (* the meet of TAny with any type t is always type t *)
    | TSymb (TAny, _), t | t, TSymb (TAny, _) -> t
    (* the meet of two partial types is their merged partial type *)
    | TSymb (TRecord fs1, _), TSymb (TRecord fs2, _) ->
        merge_records tctxt fs1 fs2
    (* the meet between a ref type and a partial type is the ref type,
       as long as the partial type can be casted. *)
    | TCst (TRef ctor), TSymb (TRecord partial_fields, _)
     |TSymb (TRecord partial_fields, _), TCst (TRef ctor) -> (
      match List.assoc_opt ctor sorts with
      | None -> failwith ("Unknown record type: " ^ ctor)
      | Some {fields= ref_fields; _} ->
          let success = cast_to_record tctxt ref_fields partial_fields in
          if success then TCst (TRef ctor)
          else raise (IncompatibleTypes (t1, t2)) )
    (* for any other case, we assume the meet is the bottom type *)
    | _ -> raise (IncompatibleTypes (t1, t2))

(** Accepts the fields of two symbolic record types and returns their meet.
    Raises an IncompatibleTypes exception whenever the meet of the types of a common field
    are incompatible, i.e. equal to bottom type. *)
and merge_records (tctxt : type_context) (t1_fields : (var * ty) list)
    (t2_fields : (var * ty) list) : ty =
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
          let meet = type_meet tctxt t1 t2 in
          (n1, meet) :: merge (f1s, f2s)
      | _ -> failwith "[CMFOTL:merge_records]: invalid state" ) in
  let sort_fields (n1, _) (n2, _) = compare n1 n2 in
  let t1_fields = List.sort sort_fields t1_fields in
  let t2_fields = List.sort sort_fields t2_fields in
  tctxt.new_type_symbol (TRecord (merge (t1_fields, t2_fields)))

(** Tries to cast a partial record type to a given list of fields.
    Raises an error if the record fields do not describe a subtype of the partial type
    described by its fields. *)
and cast_to_record (tctxt : type_context) (fields : (var * tcst) list)
    (fs : (var * ty) list) : bool =
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
        | Some sty -> ignore (type_meet tctxt (TCst ty) sty) )
      fields ;
    true )

(** Given that v:t1 and v:t2 for some v,
   checks which type is more specific and updates the symbol table
   of the given formula and all its subformulas. *)
let propagate_type_constraints (t1 : ty) (t2 : ty) (t : cplx_term)
    (f : type_context cplx_formula) =
  let tctxt = f_annot f in
  let rec collect_constraints (meet : ty) (ty : ty) : (ty * ty) list =
    if meet = ty then []
    else
      match (meet, ty) with
      | TCst (TRef ctor), TSymb (TRecord fields, _) ->
          let meet_fields = (List.assoc ctor tctxt.sorts).fields in
          List.fold_left
            (fun acc (f, ftyp) ->
              acc @ collect_constraints (TCst (List.assoc f meet_fields)) ftyp
              )
            [(ty, meet)]
            fields
      | TSymb (TRecord meet_fields, _), TSymb (TRecord fields, _) ->
          List.fold_left
            (fun acc (f, ftyp) ->
              acc @ collect_constraints (List.assoc f meet_fields) ftyp )
            [(ty, meet)]
            fields
      | _ -> [(ty, meet)] in
  let meet =
    try type_meet tctxt t1 t2
    with IncompatibleTypes (t1, t2) ->
      let err_str =
        Printf.sprintf
          "Type error while evaluating term '%s': Actual type %s is not \
           compatible with expected type %s"
          (string_of_term t)
          (string_of_tsymb tctxt.sorts t2)
          (string_of_tsymb tctxt.sorts t1) in
      failwith err_str in
  let constraints = collect_constraints meet t1 @ collect_constraints meet t2 in
  let rec propagate_to_record (fields : (var * ty) list) : (var * ty) list =
    List.map
      (fun (f, ftyp) ->
        match ftyp with
        | TSymb (TRecord nested_fields, i) ->
            (f, TSymb (TRecord (propagate_to_record nested_fields), i))
        | _ -> (f, ftyp) )
      fields in
  let propagate_to_tsymb (typ : ty ref) : unit =
    match List.assoc_opt !typ constraints with
    | Some new_ty -> typ := new_ty
    | _ -> (
      match !typ with
      | TSymb (TRecord fields, i) ->
          let new_fields = propagate_to_record fields in
          typ := TSymb (TRecord new_fields, i)
      | _ -> () ) in
  let propagate_to_formula (f : type_context cplx_formula) : unit =
    let vars = (f_annot f).vars in
    List.iter (fun (_, ty) -> propagate_to_tsymb ty) vars in
  walk_formula propagate_to_formula f

(** Validates all variables in the symbol tables of the given formula and all
    its subformulas for concrete types.
    Raises a type error if any variable of symbolic type has been found. *)
let check_unresolved_vars (f : type_context cplx_formula) : unit =
  let check_formula f =
    let unresolved_vars =
      List.filter
        (fun (v, t) -> match (v, !t) with v, TSymb st -> true | _ -> false)
        (f_annot f).vars in
    if List.length unresolved_vars > 0 then
      let vars_as_str =
        String.concat ", "
          (List.map
             (fun (v, t) -> v ^ ":" ^ string_of_tsymb (f_annot f).sorts !t)
             unresolved_vars ) in
      let msg =
        Printf.sprintf
          "Type Error: The variables %s in subformula '%s' could not be \
           resolved to a concrete type"
          vars_as_str (string_of_formula "" f) in
      failwith msg in
  walk_formula check_formula f

(*
Type judgement is of the form (Δ;T;Γ) ⊢ t::τ  
where Δ is the predicate schema
      T is the type context
      Γ is the symbol table containing variable types
      t term and 
      τ is a type

Parameters:
tctxt is (Δ,T,Γ)
typ is the type of t as expected by the caller
t is the term

Propagates the new type information to the given type context
or raises a type exception if the given term is not castable to typ.
*)
let type_check_term_debug (d : bool) (root : type_context cplx_formula)
    (tctxt : type_context) (typ : ty) (term : cplx_term) =
  let rec type_check_term (tctxt : type_context) typ term : ty =
    let sch, sorts, vars = (tctxt.predicates, tctxt.sorts, tctxt.vars) in
    if d then (
      Printf.eprintf "[Typecheck.type_check_term] \n%!Δ: %s\n%!Γ: %s\n%!⊢ "
        (string_of_delta sorts sch)
        (string_of_gamma sorts vars) ;
      Printf.eprintf "%s" (string_of_term term) ;
      Printf.eprintf ": %s\n%!" (string_of_tsymb sorts typ) ) ;
    match term with
    | Var v as tt ->
        if List.mem_assoc v vars then (
          let vtyp = !(List.assoc v vars) in
          propagate_type_constraints typ vtyp tt root ;
          type_meet tctxt typ vtyp )
        else
          failwith
          @@ Printf.sprintf
               "[type_check_term_debug]: invalid state: missing variable %s in \
                symbol table %s for term %s"
               v
               (string_of_gamma sorts vars)
               (string_of_term term)
    | Cst (Record (ctor, cfields)) ->
        let sort_name, {fields= sort_fields; _} =
          match
            List.find_opt
              (fun (name, {inline; _}) -> name = ctor && not inline)
              tctxt.sorts
          with
          | Some s -> s
          | None ->
              failwith @@ Printf.sprintf "Unknown sort %s of constant" ctor
        in
        let cfield_names = List.map fst cfields in
        let sort_field_names = List.map fst sort_fields in
        let missing_fields =
          List.filter (fun f -> List.mem f cfield_names) sort_field_names in
        let unknown_fields =
          List.filter (fun f -> List.mem f sort_field_names) cfield_names in
        if not (List.length missing_fields > 0) then
          failwith
          @@ Printf.sprintf "Missing fields %s in constant of type %s"
               (String.concat ", " missing_fields)
               ctor ;
        if not (List.length unknown_fields > 0) then
          failwith
          @@ Printf.sprintf "Unknown fields %s in constant of type %s"
               (String.concat ", " missing_fields)
               ctor ;
        List.iter
          (fun (cfield, v) ->
            let sort_field = List.find (fun (n, _) -> n = cfield) sort_fields in
            let _ = type_check_term tctxt (TCst (snd sort_field)) v in
            () )
          cfields ;
        TCst (TRef ctor)
    | Cst c as tt ->
        let ctyp = type_of_cst c in
        propagate_type_constraints typ (TCst ctyp) tt root ;
        TCst ctyp
    | F2i t as tt ->
        propagate_type_constraints (TCst TInt) typ tt root ;
        let t_typ = type_check_term tctxt (TCst TFloat) t in
        propagate_type_constraints (TCst TFloat) t_typ t root ;
        TCst TInt
    | I2f t as tt ->
        propagate_type_constraints (TCst TFloat) typ tt root ;
        let t_typ = type_check_term tctxt (TCst TInt) t in
        propagate_type_constraints (TCst TInt) t_typ t root ;
        TCst TFloat
    | I2s t as tt ->
        propagate_type_constraints (TCst TStr) typ tt root ;
        let t_typ = type_check_term tctxt (TCst TInt) t in
        propagate_type_constraints (TCst TInt) t_typ t root ;
        TCst TStr
    | S2i t as tt ->
        propagate_type_constraints (TCst TInt) typ tt root ;
        let t_typ = type_check_term tctxt (TCst TStr) t in
        propagate_type_constraints (TCst TStr) t_typ t root ;
        TCst TInt
    | F2s t as tt ->
        propagate_type_constraints (TCst TStr) typ tt root ;
        let t_typ = type_check_term tctxt (TCst TFloat) t in
        propagate_type_constraints (TCst TFloat) t_typ t root ;
        TCst TStr
    | S2f t as tt ->
        propagate_type_constraints (TCst TFloat) typ tt root ;
        let t_typ = type_check_term tctxt (TCst TStr) t in
        propagate_type_constraints (TCst TStr) t_typ t root ;
        TCst TFloat
    | FormatDate t as tt ->
        propagate_type_constraints (TCst TStr) typ tt root ;
        let t_typ = type_check_term tctxt (TCst TFloat) t in
        propagate_type_constraints (TCst TFloat) t_typ t root ;
        TCst TStr
    | Year t as tt ->
        propagate_type_constraints (TCst TInt) typ tt root ;
        let t_typ = type_check_term tctxt (TCst TFloat) t in
        propagate_type_constraints (TCst TFloat) t_typ t root ;
        TCst TInt
    | Month t as tt ->
        propagate_type_constraints (TCst TInt) typ tt root ;
        let t_typ = type_check_term tctxt (TCst TFloat) t in
        propagate_type_constraints (TCst TFloat) t_typ t root ;
        TCst TInt
    | DayOfMonth t as tt ->
        propagate_type_constraints (TCst TInt) typ tt root ;
        let t_typ = type_check_term tctxt (TCst TFloat) t in
        propagate_type_constraints (TCst TFloat) t_typ t root ;
        TCst TInt
    | R2s t as tt ->
        propagate_type_constraints (TCst TStr) typ tt root ;
        let t_typ = type_check_term tctxt (TCst TRegexp) t in
        propagate_type_constraints (TCst TRegexp) t_typ t root ;
        TCst TStr
    | S2r t as tt ->
        propagate_type_constraints (TCst TRegexp) typ tt root ;
        let t_typ = type_check_term tctxt (TCst TStr) t in
        propagate_type_constraints (TCst TStr) t_typ t root ;
        TCst TRegexp
    | UMinus t as tt ->
        let exp_typ = tctxt.new_type_symbol TNum in
        propagate_type_constraints exp_typ typ tt root ;
        let t_typ = type_check_term tctxt exp_typ t in
        propagate_type_constraints exp_typ t_typ t root ;
        let exp_typ = type_meet tctxt t_typ exp_typ in
        exp_typ
    | (Plus (t1, t2) | Minus (t1, t2) | Mult (t1, t2) | Div (t1, t2)) as tt ->
        let exp_typ = tctxt.new_type_symbol TNum in
        propagate_type_constraints exp_typ typ tt root ;
        let t1_typ = type_check_term tctxt exp_typ t1 in
        propagate_type_constraints exp_typ t1_typ t1 root ;
        let exp_typ = type_meet tctxt t1_typ exp_typ in
        let t2_typ = type_check_term tctxt exp_typ t2 in
        propagate_type_constraints exp_typ t2_typ t2 root ;
        let exp_typ = type_meet tctxt t2_typ exp_typ in
        exp_typ
    | Mod (t1, t2) as tt ->
        let exp_typ = TCst TInt in
        propagate_type_constraints exp_typ typ tt root ;
        let t1_typ = type_check_term tctxt exp_typ t1 in
        propagate_type_constraints exp_typ t1_typ t1 root ;
        let t2_typ = type_check_term tctxt exp_typ t2 in
        propagate_type_constraints exp_typ t2_typ t2 root ;
        exp_typ
    | Proj (t1, f) as tt ->
        let exp_tt_typ = tctxt.new_type_symbol TAny in
        propagate_type_constraints exp_tt_typ typ tt root ;
        let exp_t1_typ = tctxt.new_type_symbol (TRecord [(f, typ)]) in
        let t1_ty = type_check_term tctxt exp_t1_typ t1 in
        propagate_type_constraints t1_ty exp_t1_typ t1 root ;
        let t1_ty = type_meet tctxt t1_ty exp_t1_typ in
        let f_ty =
          match t1_ty with
          | TSymb (TRecord fields, _) -> List.assoc f fields
          | TCst (TRef ctor) ->
              let {fields; _} = List.assoc ctor sorts in
              TCst (List.assoc f fields)
          | _ -> failwith "typecheck_term: invalid state" in
        propagate_type_constraints typ f_ty tt root ;
        let f_ty = type_meet tctxt typ f_ty in
        f_ty in
  let ret_ty = type_check_term tctxt typ term in
  if d then Printf.eprintf "→ %s\n\n%!" (string_of_tsymb tctxt.sorts ret_ty) ;
  ret_ty

(*
Type judgement is of the form (Δ;T;Γ) ⊢ ϕ wff  
where Δ is the predicate schema
      T is the type context
      Γ is the symbol table containing variable types
      ϕ formula 

Parameters:
  formula ϕ and its type context (Δ,T,Γ)

Propagates the new type information to the formula's type_context type context
or raises a type exception if the formula is not well typed.
*)
let type_check_formula_debug (d : bool) (root : type_context cplx_formula) =
  let rec type_check_formula (f : type_context cplx_formula) : unit =
    let tctxt, fast = f in
    let sch, sorts, vars = (tctxt.predicates, tctxt.sorts, tctxt.vars) in
    if d then (
      Printf.eprintf "[Typecheck.typecheck_formula] \n%!Δ: %s\n%!Γ: %s\n%!⊢ "
        (string_of_delta sorts sch)
        (string_of_gamma sorts vars) ;
      Printf.eprintf "%s" (string_of_formula "" f) ;
      Printf.eprintf "\n%!\n%!" ) ;
    match fast with
    | Equal (t1, t2) ->
        let exp_typ = tctxt.new_type_symbol TAny in
        let t1_typ = type_check_term_debug d root tctxt exp_typ t1 in
        propagate_type_constraints exp_typ t1_typ t1 root ;
        let exp_typ = type_meet tctxt t1_typ exp_typ in
        let t2_typ = type_check_term_debug d root tctxt exp_typ t2 in
        propagate_type_constraints exp_typ t2_typ t2 root ;
        propagate_type_constraints t1_typ t2_typ t2 root
    | Less (t1, t2) | LessEq (t1, t2) ->
        let exp_typ = tctxt.new_type_symbol TOrd in
        let t1_typ = type_check_term_debug d root tctxt exp_typ t1 in
        propagate_type_constraints exp_typ t1_typ t1 root ;
        let exp_typ = type_meet tctxt t1_typ exp_typ in
        let t2_typ = type_check_term_debug d root tctxt exp_typ t2 in
        propagate_type_constraints exp_typ t2_typ t2 root ;
        propagate_type_constraints t1_typ t2_typ t2 root
    | Substring (t1, t2) ->
        (* Define constant *)
        let exp_typ = TCst TStr in
        (* Type check t1 *)
        let t1_typ = type_check_term_debug d root tctxt exp_typ t1 in
        (* Propagate constraints t1, exp *)
        propagate_type_constraints exp_typ t1_typ t1 root ;
        (* Type check t2 *)
        let t2_typ = type_check_term_debug d root tctxt exp_typ t2 in
        (* Propagate constraints t2, exp *)
        propagate_type_constraints exp_typ t2_typ t2 root
    | Matches (t1, t2, tl) ->
        (* Define constant *)
        let exp_typ_1 = TCst TStr in
        (* Type check t1 *)
        let t1_typ = type_check_term_debug d root tctxt exp_typ_1 t1 in
        (* Propagate constraints t1, exp *)
        propagate_type_constraints exp_typ_1 t1_typ t1 root ;
        (* Define constant *)
        let exp_typ_2 = TCst TRegexp in
        (* Type check t2 *)
        let t2_typ = type_check_term_debug d root tctxt exp_typ_2 t2 in
        (* Propagate constraints t2, exp *)
        propagate_type_constraints exp_typ_2 t2_typ t2 root ;
        let exp_typ_group = TCst TStr in
        List.iter
          (fun t ->
            match t with
            | None -> ()
            | Some t ->
                let t_typ = type_check_term_debug d root tctxt exp_typ_group t in
                propagate_type_constraints exp_typ_group t_typ t root )
          tl
    | Pred p ->
        let name, arity, _ = p in
        let exp_typ_list =
          if List.mem_assoc (name, arity) sch then List.assoc (name, arity) sch
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
            let exp_ty = List.nth exp_typ_list i in
            let t = List.nth t_list i in
            let t1 = type_check_term_debug d root tctxt !exp_ty t in
            propagate_type_constraints !exp_ty t1 t root )
          indices
    | Let (p, body, in_f) | LetPast (p, body, in_f) ->
        (* first typecheck the body: this update the body's symbol table and the argument types in
           the predicate schema (linked by reference) *)
        type_check_formula body ;
        (* now typecheck the right hand side formula *)
        type_check_formula in_f
    | Neg f -> type_check_formula f
    | Prev (intv, f)
     |Next (intv, f)
     |Eventually (intv, f)
     |Once (intv, f)
     |Always (intv, f)
     |PastAlways (intv, f) ->
        type_check_formula f
    | And (f1, f2) | Or (f1, f2) | Implies (f1, f2) | Equiv (f1, f2) ->
        type_check_formula f1 ; type_check_formula f2
    | Since (intv, f1, f2) | Until (intv, f1, f2) ->
        type_check_formula f1 ; type_check_formula f2
    | Exists (l, f) | ForAll (l, f) -> type_check_formula f
    | Aggreg (r, op, x, gs, f) -> (
        let f_ctx = f_annot f in
        let typecheck_aggregation exp_ret_ty exp_agg_ty =
          type_check_formula f ;
          (* typecheck x under the type context of the inner formula: *)
          let agg_ty = type_check_term_debug d root f_ctx exp_agg_ty (Var x) in
          (* TODO zumstegr: allow gs to be of complex type by correctly binding their scopes *)
          if
            List.exists
              (fun g ->
                match !(List.assoc g f_ctx.vars) with
                | TCst (TRef _) -> true
                | _ -> false )
              gs
          then
            failwith
              "[type_check_formula_debug] group-by terms of complex type are \
               not supported yet." ;
          (* typecheck the return variable under the current context: *)
          let ret_ty = type_check_term_debug d root tctxt exp_ret_ty (Var r) in
          (* if _expected_ type of aggregation variable and return type are the same
             (e.g. SUM: both TNum), we propagate the more specific _actual_ type for r. *)
          if exp_agg_ty = exp_ret_ty then
            propagate_type_constraints agg_ty ret_ty (Var r) root ;
          () in
        let exp_any_typ = tctxt.new_type_symbol TAny in
        let exp_num_typ = tctxt.new_type_symbol TNum in
        let exp_ord_typ = tctxt.new_type_symbol TOrd in
        match op with
        | Min | Max -> typecheck_aggregation exp_ord_typ exp_ord_typ
        | Cnt -> typecheck_aggregation (TCst TInt) exp_any_typ
        | Sum -> typecheck_aggregation exp_num_typ exp_num_typ
        | Avg | Med -> typecheck_aggregation (TCst TFloat) exp_num_typ )
    | Frex (intv, r) -> type_check_re_formula r
    | Prex (intv, r) -> type_check_re_formula r
  and type_check_re_formula = function
    | Wild -> ()
    | Test f -> type_check_formula f
    | Concat (r1, r2) | Plus (r1, r2) ->
        type_check_re_formula r1 ; type_check_re_formula r2
    | Star r -> type_check_re_formula r in
  type_check_formula

(** Returns the type of the given term derived from the provided symbol table.
    Requires all variables in the given type context to be resolved. *)
let rec type_of_term (tctxt : type_context) (t : cplx_term) : tcst =
  let get_tcst ty =
    match ty with
    | TCst ty -> ty
    | TSymb _ | TNever ->
        failwith
        @@ Printf.sprintf
             "type_of_term: Expected %s to be of concrete type, found %s"
             (string_of_term t)
             (string_of_tsymb tctxt.sorts ty) in
  match t with
  | Var v -> get_tcst !(List.assoc v tctxt.vars)
  | Cst c -> type_of_cst c
  | F2i _ | S2i _ | Year _ | Month _ | DayOfMonth _ -> TInt
  | I2f _ | S2f _ -> TFloat
  | I2s _ | F2s _ | R2s _ | FormatDate _ -> TStr
  | S2r _ -> TRegexp
  | Plus (t1, _)
   |Minus (t1, _)
   |UMinus t1
   |Mult (t1, _)
   |Div (t1, _)
   |Mod (t1, _) ->
      type_of_term tctxt t1
  | Proj (t, f) -> (
    match type_of_term tctxt t with
    | TRef ctor ->
        let {fields; _} = List.assoc ctor tctxt.sorts in
        List.assoc f fields
    | typ ->
        failwith
        @@ Printf.sprintf
             "[type_of_term]: expected %s to be a record value, but it is of \
              type %s"
             (string_of_term t) (string_of_ty typ) )

(** returns all leaf fields of a given term.
    Example 1: record_leaves r.user -> r.user.name, r.user.address.city, r.user.address.street
    Example 2: record_leaves Client {name: "n", address: {street: "s", city: "c"}} -> "c", "s", "n"
    Example 3: record_leaves Client {name: "n", address: a} -> a.city, a.street, "n" *)
let record_leaves (tctxt : type_context) (t : cplx_term) : cplx_term list =
  let rec leaves t ty =
    match t with
    | Cst (Record (ctor, cfields)) ->
        List.map (fun (n, v) -> leaves v (type_of_term tctxt v)) cfields
        |> List.flatten
    | _ -> (
      match ty with
      | TRef ctor ->
          let {fields; _} = List.assoc ctor tctxt.sorts in
          List.map (fun (fname, ftyp) -> leaves (Proj (t, fname)) ftyp) fields
          |> List.flatten
      | _ -> [t] ) in
  leaves t (type_of_term tctxt t)

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

    Example: mtvars tctxt r.user -> ["r.user.name"; "r.user.address", ...]*)
  let rec mtvars (tctxt : type_context) (term : cplx_term) : var list =
    let aux =
      match term with
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
          mtvars tctxt t
      | Plus (t1, t2)
       |Minus (t1, t2)
       |Mult (t1, t2)
       |Div (t1, t2)
       |Mod (t1, t2) ->
          mtvars tctxt t1 @ mtvars tctxt t2
      | (Var _ as t) | (Proj _ as t) -> (
          let ty = type_of_term tctxt t in
          match ty with
          | TInt | TFloat | TStr | TRegexp | TBool | TNull -> [string_of_term t]
          | TRef ctor ->
              let {fields; _} = List.assoc ctor tctxt.sorts in
              let subfields =
                List.map
                  (fun (fname, _) -> mtvars tctxt (Proj (t, fname)))
                  fields
                |> List.flatten in
              string_of_term t :: subfields ) in
    let res = aux in
    (* Printf.eprintf "MTVARS: %s -> %s\n" (string_of_term term)
       (String.concat "," res) ; *)
    res

  (* In these special cases, no evaluation is needed for the formula [f2]. *)
  let is_special_case (tctxt : type_context) fv1 (f : 'a cplx_formula) =
    match snd f with
    | Equal (t1, t2) -> (
      match (t1, t2) with
      | Var x, t when Misc.subset (mtvars tctxt t) fv1 -> true
      | t, Var x when Misc.subset (mtvars tctxt t) fv1 -> true
      | Proj (b, _), t when Misc.subset (mtvars tctxt t) fv1 -> true
      | t, Proj (b, _) when Misc.subset (mtvars tctxt t) fv1 -> true
      | _ -> Misc.subset (free_vars ~tvars:mtvars f) fv1 )
    | Matches (t1, t2, tl) ->
        Misc.subset (mtvars tctxt t1) fv1
        && Misc.subset (mtvars tctxt t2) fv1
        && List.for_all
             (function
               | None -> true
               | Some (Var _) -> true
               | Some t -> Misc.subset (mtvars tctxt t) fv1 )
             tl
    | Less (_, _)
     |LessEq (_, _)
     |Substring (_, _)
     |Neg (_, Equal (_, _))
     |Neg (_, Less (_, _))
     |Neg (_, LessEq (_, _))
     |Neg (_, Substring (_, _))
     |Neg (_, Matches (_, _, _)) ->
        Misc.subset (free_vars ~tvars:mtvars f) fv1
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
    let tctxt = f_annot f in
    match snd f with
    | Equal (t1, t2) -> (
      match (t1, t2) with
      | Var _, Cst _ | Cst _, Var _ | Cst _, Cst _ -> (true, None)
      | Proj _, Cst _ | Cst _, Proj _ -> (false, Some (f, msg_EQUAL))
      | _ -> (false, Some (f, msg_EQUAL)) )
    | Less _ | LessEq _ | Substring _ | Matches _ -> (false, Some (f, msg_LESS))
    | Neg (_, Equal (t1, t2)) -> (
      match (t1, t2) with
      | Var x, Var y when x = y -> (true, None)
      | Proj (xb, xf), Proj (yb, yf) when xb = yb && xf = yf -> (true, None)
      | Cst _, Cst _ -> (true, None)
      | _ -> (false, Some (f, msg_NOT_EQUAL)) )
    | Pred p ->
        let tlist = get_predicate_args p in
        if
          List.for_all
            (fun t -> match t with Var _ | Cst _ | Proj _ -> true | _ -> false)
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
        if free_vars ~tvars:mtvars f1 = [] then is_monitorable f1
        else (false, Some (f, msg_NOT))
    | And (f1, f2) -> (
        let is_mon1, r1 = is_monitorable f1 in
        if not is_mon1 then (is_mon1, r1)
        else
          let fv1 = free_vars ~tvars:mtvars f1 in
          if is_and_relop f2 then
            if is_special_case tctxt fv1 f2 then (true, None)
            else (false, Some (f, msg_ANDRELOP))
          else
            match snd f2 with
            | Neg f2' ->
                let fv2 = free_vars ~tvars:mtvars f2 in
                if not (Misc.subset fv2 fv1) then
                  ( false
                  , Some
                      ( f
                      , Printf.sprintf msg_SUBSET (String.concat "," fv2)
                          (String.concat "," fv1) ) )
                else is_monitorable f2'
            | _ -> is_monitorable f2 )
    | Or (f1, f2) ->
        let fv1 = free_vars ~tvars:mtvars f1 in
        let fv2 = free_vars ~tvars:mtvars f2 in
        if (not (Misc.subset fv1 fv2)) || not (Misc.subset fv2 fv1) then
          (false, Some (f, msg_OR))
        else
          let is_mon1, r1 = is_monitorable f1 in
          if not is_mon1 then (is_mon1, r1) else is_monitorable f2
    | Exists (_, f1)
     |Aggreg (_, _, _, _, f1)
     |Prev (_, f1)
     |Next (_, f1)
     |Eventually (_, f1)
     |Once (_, f1) ->
        is_monitorable f1
    | Since (intv, f1, f2) | Until (intv, f1, f2) ->
        let is_mon2, msg2 = is_monitorable f2 in
        if not is_mon2 then (is_mon2, msg2)
        else
          let fv1 = free_vars ~tvars:mtvars f1 in
          let fv2 = free_vars ~tvars:mtvars f2 in
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
        Printf.eprintf "%s, because of the subformula:\n  %s\n%!%s\n%!" str
          (string_of_formula "" f) msg
    | None -> failwith "[Rewriting.print_reason] internal error"

  let print_results (f : MFOTL.formula) (is_mon, reason) =
    if !Misc.verbose || !Misc.checkf then
      if is_mon then Printf.eprintf "The analyzed formula is monitorable.\n%!"
      else (
        print_reason "The analyzed formula is NOT monitorable" reason ;
        (* NOTE zumstegr: safe-range and TSF safe-range checks have not yet been ported to CMFODL formulas *)
        let is_sr = Rewriting.is_saferange f in
        if is_sr then
          prerr_endline
            "However, the input (and also the analyzed) formula is safe-range, \n\
             hence one should be able to rewrite it into a monitorable formula."
        else prerr_endline "The analyzed formula is neither safe-range." ;
        let is_tsfsr = Rewriting.is_tsfsaferange f in
        if is_tsfsr then
          prerr_endline "By the way, the analyzed formula is TSF safe-range."
        else
          prerr_endline
            "By the way, the analyzed formula is not TSF safe-range." )
    else if not is_mon then
      Printf.eprintf
        "The analyzed formula is NOT monitorable. Use the -check or -verbose \
         flags.\n\
         %!"
end

let print_formula_details (f : type_context cplx_formula) (c : MFOTL.formula) =
  let tctxt = f_annot f in
  let complex_str = string_of_formula "" f |> String.trim in
  let compiled_str = MFOTL.string_of_formula "" c |> String.trim in
  if compare compiled_str complex_str <> 0 then
    Printf.eprintf "The input formula is:\n  %s\n%!" compiled_str ;
  Printf.eprintf "The analyzed formula is:\n  %s\n%!" compiled_str ;
  Printf.eprintf "The sequence of free variables is: (%s)\n%!"
    (List.map fst tctxt.vars |> String.concat ",")

(** initializes the type annotations for all sub formulas in the given formula.
    All free variables of a sub-formula are initialized with TAny.
    the predicate schema and sorts are set to the given values.
    *)
let rec init_typed_formula (tctxt : type_context) (f : 'a cplx_formula) :
    type_context cplx_formula =
  let self = init_typed_formula in
  (* TODO zumstegr: if the symbol table of a sub-formula contains only a subset of all
     free variables of its scope, the constraint propagation won't be able
     to update the type of variables not part of the symbol table.
     we therefore include all free variables from the parent formula for now,
     until the constraint propagation has been improved. *)
  (* let local_vars f =
     List.filter (fun (v, _) -> List.mem v (free_vars f)) tctxt.vars in *)
  let local_vars f = tctxt.vars in
  let l_ctx f = {tctxt with vars= local_vars f} in
  let rec aux_regex (regex : 'a regex) : type_context regex =
    match regex with
    | Wild as r -> r
    | Concat (r1, r2) -> Concat (aux_regex r1, aux_regex r2)
    | Plus (r1, r2) -> Plus (aux_regex r1, aux_regex r2)
    | Star r1 -> Star (aux_regex r1)
    | Test f -> Test (tctxt, self (l_ctx f) f |> snd) in
  match snd f with
  | (Equal _ as f)
   |(Less _ as f)
   |(LessEq _ as f)
   |(Substring _ as f)
   |(Matches _ as f) ->
      (tctxt, f)
  | Neg f -> (tctxt, Neg (self (l_ctx f) f))
  | And (f1, f2) -> (tctxt, And (self (l_ctx f1) f1, self (l_ctx f2) f2))
  | Or (f1, f2) -> (tctxt, Or (self (l_ctx f1) f1, self (l_ctx f2) f2))
  | Implies (f1, f2) -> (tctxt, Implies (self (l_ctx f1) f1, self (l_ctx f2) f2))
  | Equiv (f1, f2) -> (tctxt, Equiv (self (l_ctx f1) f1, self (l_ctx f2) f2))
  | Prev (i, f) -> (tctxt, Prev (i, self (l_ctx f) f))
  | Next (i, f) -> (tctxt, Next (i, self (l_ctx f) f))
  | Eventually (i, f) -> (tctxt, Eventually (i, self (l_ctx f) f))
  | Once (i, f) -> (tctxt, Once (i, self (l_ctx f) f))
  | Always (i, f) -> (tctxt, Always (i, self (l_ctx f) f))
  | PastAlways (i, f) -> (tctxt, PastAlways (i, self (l_ctx f) f))
  | Since (i, f1, f2) ->
      (tctxt, Since (i, self (l_ctx f1) f1, self (l_ctx f2) f2))
  | Until (i, f1, f2) ->
      (tctxt, Until (i, self (l_ctx f1) f1, self (l_ctx f2) f2))
  | Pred _ as p -> (tctxt, p)
  | Frex (i, r) -> (tctxt, Frex (i, aux_regex r))
  | Prex (i, r) -> (tctxt, Prex (i, aux_regex r))
  | Exists (l, f) ->
      let non_shadowed =
        List.filter (fun (v, _) -> not (List.mem v l)) (local_vars f) in
      let new_vars =
        non_shadowed
        @ List.map (fun v -> (v, ref (tctxt.new_type_symbol TAny))) l in
      (tctxt, Exists (l, self {tctxt with vars= new_vars} f))
  | ForAll (l, f) ->
      let non_shadowed =
        List.filter (fun (v, _) -> not (List.mem v l)) (local_vars f) in
      let new_vars =
        non_shadowed
        @ List.map (fun v -> (v, ref (tctxt.new_type_symbol TAny))) l in
      (tctxt, ForAll (l, self {tctxt with vars= new_vars} f))
  | Let ((name, arity, targs), body, f) ->
      let arg_names = List.map expect_var targs in
      (* introduce a new reference for each argument type
         and re-use it in the body's symbol table: *)
      let arg_types =
        List.map (fun a -> ref (tctxt.new_type_symbol TAny)) arg_names in
      let new_vars = List.map2 (fun n t -> (n, t)) arg_names arg_types in
      let non_shadowed =
        List.filter (fun ((n, _), _) -> n <> name) tctxt.predicates in
      let new_sch = ((name, arity), arg_types) :: non_shadowed in
      ( tctxt
      , Let
          ( (name, arity, targs)
          , self {tctxt with vars= new_vars} body
          , self {tctxt with predicates= new_sch} f ) )
  | LetPast ((name, arity, targs), body, f) ->
      let arg_names =
        List.map
          (fun t -> match t with Var v -> v | _ -> failwith "invalid state")
          targs in
      let arg_types =
        List.map (fun a -> ref (tctxt.new_type_symbol TAny)) arg_names in
      let new_vars = List.map2 (fun n t -> (n, t)) arg_names arg_types in
      let new_sch = ((name, arity), arg_types) :: tctxt.predicates in
      ( tctxt
      , LetPast
          ( (name, arity, targs)
          , self {tctxt with vars= new_vars} body
          , self {tctxt with predicates= new_sch} f ) )
  | Aggreg (r, op, x, gs, f) ->
      let zs = List.filter (fun v -> not (List.mem v gs)) (free_vars f) in
      (* symbol table of inner formula consists of gs variables inherited from outer symbol table,
         plus new free variables introduced by the inner formula itself (possibly shadowing free vars from outside). *)
      let new_vars =
        List.filter (fun (v, _) -> List.mem v gs) tctxt.vars
        @ List.map (fun v -> (v, ref (tctxt.new_type_symbol TAny))) zs in
      (tctxt, Aggreg (r, op, x, gs, self {tctxt with vars= new_vars} f))

(** returns an initial type context for the given formula.
    the predicate schema is initialized with the native predicates (tp, ts, ..)
    plus the custom sorts defined in the signatures.
    The custom sorts are loaded from the signatures.
    The symbol table is filled with the global variables of f, initialized to TAny. *)
let initial_type_context (signatures : signatures) (f : unit cplx_formula) :
    type_context =
  let tsymb_id = ref 0 in
  let new_type_symbol (cls : tcl) =
    incr tsymb_id ;
    TSymb (cls, !tsymb_id) in
  let native_predicates : predicate_schema =
    [ (("tp", 1), [ref (TCst TInt)]); (("ts", 1), [ref (TCst TInt)])
    ; (("tpts", 2), [ref (TCst TInt); ref (TCst TInt)]) ] in
  (* create initial Δ *)
  let sch : predicate_schema =
    List.fold_left
      (fun acc decl ->
        match decl with
        | Predicate {elt= name, args; _} ->
            let lifted_args =
              extr_nodes args |> List.map (fun {atyp; _} -> ref (TCst atyp))
            in
            ((name, List.length args), lifted_args) :: acc
        | ProductSort (attrs, {elt= name, fields; _}) ->
            (* do not add inline records to predicate schema: *)
            if not attrs.inline then
              let rec_pred = ((name, 1), [ref (TCst (TRef name))]) in
              rec_pred :: acc
            else acc )
      [] signatures in
  (* create T *)
  let sorts : custom_sorts =
    List.fold_left
      (fun acc decl ->
        match decl with
        | Predicate _ -> acc
        | ProductSort (attrs, {elt= name, fields; _}) ->
            ( name
            , { inline= attrs.inline
              ; fields=
                  extr_nodes fields
                  |> List.map (fun {fname; ftyp} -> (fname, ftyp)) } )
            :: acc )
      [] signatures in
  (* create initial Γ *)
  let globals =
    List.map
      (fun v -> (v, ref (new_type_symbol TAny)))
      (free_vars f |> List.sort compare) in
  {predicates= sch @ native_predicates; sorts; vars= globals; new_type_symbol}

(** type checks a complex formula given matching signature definitions.
    Returns a triple consiting of:
    1) The type checking context consisting of predicate schema, symbol table and type context.
    2) A possibly updated version of the input formula.
    3) A boolean flag indicating the monitorability (safety) of the input formula. *)
let rec typecheck_formula (signatures : signatures) (f : unit cplx_formula) :
    type_context cplx_formula =
  let debug = Misc.debugging Dbg_typing in
  (* first of all check well-formedness of formula: *)
  ignore @@ ignore (check_wff f) ;
  let init_ctx = initial_type_context signatures f in
  let f = init_typed_formula init_ctx f in
  type_check_formula_debug debug f f ;
  let tctxt = f_annot f in
  (* Make sure all variables in all symbol tables have been resolved
     to a concrete type. *)
  check_unresolved_vars f ;
  (* TODO zumstegr: output would actually be useful, but currently breaks all tests. *)
  if debug && false then (
    Printf.eprintf
      "[Typecheck.typecheck_formula] The final type judgement is (%s; %s) ⊢ "
      (string_of_delta tctxt.sorts tctxt.predicates)
      (string_of_gamma tctxt.sorts tctxt.vars) ;
    Printf.eprintf "%s"
      (string_of_parenthesized_formula ""
         ~string_of_annot:(fun tctxt -> string_of_gamma tctxt.sorts tctxt.vars)
         f ) ;
    Printf.eprintf "\n%!" ) ;
  f

(* COMPILE FUNCTIONS *)

(** returns the base of a given projection or variable:
    Example 1: projection_base r.user -> r
    Example 2: projection_base u -> u 
    Throws an error if the given term is neither a projection or a variable.
    *)
let rec projection_base = function
  | Var v -> v
  | Proj (base, field) -> projection_base base
  | t ->
      failwith
      @@ Printf.sprintf
           "[projection_base]: Given term %s is neither a variable nor a \
            projection"
           (string_of_term t)

(** replaces the given variable or projection with a new one in the given formula.
    Shadowed variables in nested scopes won't be updated. *)
let rec replace_var (old : cplx_term) (n : cplx_term) (f : 'a cplx_formula) :
    'a cplx_formula =
  let base = projection_base old in
  let replace t_old = if old = t_old then n else t_old in
  let rec replace_term_re r =
    match r with
    | Wild | Concat _ | Plus _ | Star _ -> r
    | Test f -> Test (replace_var old n f) in
  let fdata, fast = f in
  let new_fast =
    match fast with
    | Equal (t1, t2) -> Equal (replace t1, replace t2)
    | Less (t1, t2) -> Less (replace t1, replace t2)
    | LessEq (t1, t2) -> LessEq (replace t1, replace t2)
    | Substring (t1, t2) -> Substring (replace t1, replace t2)
    | Matches (t1, t2, i) -> Matches (replace t1, replace t2, i)
    | Pred (name, arity, args) -> Pred (name, arity, List.map replace args)
    (* only free variables in LETs are its args and therefore shadow every outer var in body *)
    | Let (p, f1, f2) -> Let (p, f1, replace_var old n f2)
    | LetPast (p, f1, f2) -> LetPast (p, f1, replace_var old n f2)
    | Neg f -> Neg (replace_var old n f)
    | And (f1, f2) -> And (replace_var old n f1, replace_var old n f2)
    | Or (f1, f2) -> Or (replace_var old n f1, replace_var old n f2)
    | Implies (f1, f2) -> Implies (replace_var old n f1, replace_var old n f2)
    | Equiv (f1, f2) -> Equiv (replace_var old n f1, replace_var old n f2)
    (* do not replace terms if their base is shadowed in a nested scope: *)
    | Exists (vs, f) ->
        if not (List.mem base vs) then Exists (vs, replace_var old n f)
        else fast
    | ForAll (vs, f) ->
        if not (List.mem base vs) then ForAll (vs, replace_var old n f)
        else fast
    | Aggreg (_, _, _, _, _) -> fast
    | Prev (intv, f) -> Prev (intv, replace_var old n f)
    | Next (intv, f) -> Next (intv, replace_var old n f)
    | Eventually (intv, f) -> Eventually (intv, replace_var old n f)
    | Once (intv, f) -> Once (intv, replace_var old n f)
    | Always (intv, f) -> Always (intv, replace_var old n f)
    | PastAlways (intv, f) -> PastAlways (intv, replace_var old n f)
    | Since (intv, f1, f2) ->
        Since (intv, replace_var old n f1, replace_var old n f2)
    | Until (intv, f1, f2) ->
        Until (intv, replace_var old n f1, replace_var old n f2)
    | Frex (intv, r) -> Frex (intv, replace_term_re r)
    | Prex (intv, r) -> Prex (intv, replace_term_re r) in
  (fdata, new_fast)

(** replaces the arguments in the usage of the given predicate with a new argument list.
    new_args will be called with the list of original arguments.
    shadowed predicates in LET statements won't be updated. *)
let rec replace_pred_args (p : cplx_predicate) (new_arg_tys : ty ref list)
    (new_args : cplx_term list -> cplx_term list) (f : type_context cplx_formula)
    : type_context cplx_formula =
  let rec replace_pred_re r =
    match r with
    | Wild | Concat _ | Plus _ | Star _ -> r
    | Test f -> Test (replace_pred_args p new_arg_tys new_args f) in
  let old_name, old_arity, _ = p in
  let fast = f_ast f in
  let tctxt = f_annot f in
  (* replace the old predicate schema with the new one: *)
  let new_sch =
    ((old_name, old_arity), new_arg_tys)
    :: List.remove_assoc (old_name, old_arity) tctxt.predicates in
  let new_fast =
    match fast with
    | Equal _ | Less _ | LessEq _ | Substring _ | Matches _ -> fast
    | Pred (name, arity, args) ->
        if name = old_name && arity = old_arity then
          let na = new_args args in
          Pred (name, List.length na, na)
        else fast
    (* do not replace pred in f if it is shadowed (same name and arity) *)
    | Let ((name, arity, args), b, f) ->
        if name == old_name && arity == old_arity then
          Let
            ((name, arity, args), replace_pred_args p new_arg_tys new_args b, f)
        else
          Let
            ( (name, arity, args)
            , replace_pred_args p new_arg_tys new_args b
            , replace_pred_args p new_arg_tys new_args f )
    | LetPast ((name, arity, args), b, f) ->
        if name == old_name && arity == old_arity then
          LetPast
            ((name, arity, args), replace_pred_args p new_arg_tys new_args b, f)
        else
          LetPast
            ( (name, arity, args)
            , replace_pred_args p new_arg_tys new_args b
            , replace_pred_args p new_arg_tys new_args f )
    | Neg f -> Neg (replace_pred_args p new_arg_tys new_args f)
    | And (f1, f2) ->
        And
          ( replace_pred_args p new_arg_tys new_args f1
          , replace_pred_args p new_arg_tys new_args f2 )
    | Or (f1, f2) ->
        Or
          ( replace_pred_args p new_arg_tys new_args f1
          , replace_pred_args p new_arg_tys new_args f2 )
    | Implies (f1, f2) ->
        Implies
          ( replace_pred_args p new_arg_tys new_args f1
          , replace_pred_args p new_arg_tys new_args f2 )
    | Equiv (f1, f2) ->
        Equiv
          ( replace_pred_args p new_arg_tys new_args f1
          , replace_pred_args p new_arg_tys new_args f2 )
    | Exists (vs, f) -> Exists (vs, replace_pred_args p new_arg_tys new_args f)
    | ForAll (vs, f) -> ForAll (vs, replace_pred_args p new_arg_tys new_args f)
    | Aggreg (_, _, _, _, _) -> fast
    | Prev (intv, f) -> Prev (intv, replace_pred_args p new_arg_tys new_args f)
    | Next (intv, f) -> Next (intv, replace_pred_args p new_arg_tys new_args f)
    | Eventually (intv, f) ->
        Eventually (intv, replace_pred_args p new_arg_tys new_args f)
    | Once (intv, f) -> Once (intv, replace_pred_args p new_arg_tys new_args f)
    | Always (intv, f) ->
        Always (intv, replace_pred_args p new_arg_tys new_args f)
    | PastAlways (intv, f) ->
        PastAlways (intv, replace_pred_args p new_arg_tys new_args f)
    | Since (intv, f1, f2) ->
        Since
          ( intv
          , replace_pred_args p new_arg_tys new_args f1
          , replace_pred_args p new_arg_tys new_args f2 )
    | Until (intv, f1, f2) ->
        Until
          ( intv
          , replace_pred_args p new_arg_tys new_args f1
          , replace_pred_args p new_arg_tys new_args f2 )
    | Frex (intv, r) -> Frex (intv, replace_pred_re r)
    | Prex (intv, r) -> Prex (intv, replace_pred_re r) in
  ({tctxt with predicates= new_sch}, new_fast)

let compile_tcst (tcst : tcst) : Predicate.tcst =
  match tcst with
  | TInt -> TInt
  | TFloat -> TFloat
  | TStr -> TStr
  | TRegexp -> TRegexp
  | TBool -> TInt (* booleans are encoded as false=0, true=1 *)
  | TNull -> TInt (* null is encoded as 0 *)
  | TRef _ -> TInt

let compile_tcl (tcl : tcl) : Predicate.tcl =
  match tcl with
  | TNum -> TNum
  | TAny -> TAny
  (* TOrd + TRecord = TAny *)
  | TOrd -> TAny
  | TRecord _ -> failwith "[compile_tcl] Cannot compile TRecord"

let compile_tsymb (tsymb : ty) : Predicate.tsymb =
  match tsymb with
  | TSymb (s, i) -> TSymb (compile_tcl s, i)
  | TCst c -> TCst (compile_tcst c)
  | TNever -> failwith "[compile_tsymb] Cannot compile TBot"

(** compiles a projection to a unique variable name.
    Example: The term r.user.name maps to the string 'r_user_name' *)
let rec compile_projection = function
  | Var v -> v
  | Proj (t, f) -> Printf.sprintf "%s-%s" (compile_projection t) f
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
let expand_cplx_var (f : type_context cplx_formula) (var : var) :
    (MFOTL.formula * var list) option =
  let tctxt = f_annot f in
  let type_ctor t =
    let ty = type_of_term tctxt t in
    match ty with
    | TRef r -> r
    | _ ->
        failwith
        @@ Printf.sprintf "could not find ref type of %s: is of type %s"
             (string_of_term t)
             (string_of_tcst tctxt.sorts ty) in
  let usages = var_usage f var |> TermSet.elements in
  (* list of triples: (ctor, Record, prefix) *)
  let required_expansions =
    List.fold_right
      (fun u acc ->
        match u with
        | (Var _ as b) | Proj (b, _) ->
            let ctor = type_ctor b in
            let {fields; _} = List.assoc ctor tctxt.sorts in
            (ctor, fields, compile_projection b) ^:: acc
        | _ -> acc )
      usages [] in
  let expansions =
    List.map
      (fun (ctor, record, prefix) ->
        let new_vars =
          List.map
            (fun (n, _) -> compile_projection (Proj (Var prefix, n)))
            record in
        let new_pred =
          MFOTL.Pred
            ( ctor
            , List.length new_vars + 1
            , Var prefix :: List.map (fun v -> Predicate.Var v) new_vars ) in
        (new_pred, new_vars) )
      required_expansions in
  let new_preds, new_vars = List.split expansions in
  if List.length expansions > 0 then
    Some (conjunction new_preds, List.flatten new_vars)
  else None

(** accepts two sides of an equality and returns a formula comparing both sides
    recursively/structurally. The returned formula  replaces the original equality. *)
let expand_structural_equality (tctxt : type_context) (left : cplx_term)
    (right : cplx_term) : 'a cplx_formula =
  let left_ty, right_ty = (type_of_term tctxt left, type_of_term tctxt right) in
  if compare left_ty right_ty <> 0 then
    failwith
    @@ Printf.sprintf
         "expand_structural_equality: type %s of %s is not equal to type %s of \
          %s"
         (string_of_term left) (string_of_ty left_ty) (string_of_term right)
         (string_of_ty right_ty) ;
  let leaves =
    List.combine (record_leaves tctxt left) (record_leaves tctxt right) in
  let equal_terms = List.map (fun (l, r) -> (tctxt, Equal (l, r))) leaves in
  cplx_conjunction tctxt equal_terms

(** expands the complex arguments of a given predicate, by extending its arguments list,
    updating the usage of the original arguments in the body and predicate usages in the in_f formula accordingly.
    Each complex argument is replaced by its leaves accessed in the body of the LET statement.
    This function also makes sure to update the type annotations of the predicate schema
    in the affected formulas. *)
let rec expand_predicate_params (p : cplx_predicate)
    (body : type_context cplx_formula) (in_f : type_context cplx_formula) =
  let name, _, args = p in
  (* extends a parameter of a predicate and returnn
     the new body and a list of expanded parameters: *)
  let expand_param body (arg : var) =
    (* get the used leaves and their types of an argument in the LET body: *)
    let usages = var_usage body arg in
    let leaves = record_leaves (f_annot body) (Var arg) |> TermSet.of_list in
    let used_leaves = TermSet.inter usages leaves |> TermSet.elements in
    let leave_tys =
      List.map (fun t -> type_of_term (f_annot body) t) used_leaves in
    (* replace all used leaves by their new (flattened) variable in the body of the LET: *)
    let new_body =
      List.fold_left
        (fun b l -> replace_var l (Var (compile_projection l)) b)
        body used_leaves in
    (new_body, List.combine used_leaves leave_tys) in
  (* expands a single argument passed to the given parameter.
     param is the leaf used inside the body, arg is the term passed as argument: *)
  let rec expand_arg arg param =
    match param with
    | Var _ -> arg
    | Proj (b, f) -> (
      match arg with
      | Var _ | Proj _ -> Proj (expand_arg arg b, f)
      | Cst (Record (_, fs)) -> (
        match expand_arg arg b with
        | Cst (Record (_, fs)) -> List.assoc f fs
        | _ -> failwith "[expand_arg] invalid state 0" )
      | _ -> failwith "[expand_arg] invalid state 1" )
    | _ -> failwith "[expand_arg] invalid state 2" in
  let new_body, leaves =
    (* fold over all arguments to gather new LET body and all accessed leaves: *)
    List.fold_right
      (fun arg (b, l) ->
        let new_body, new_leaves = expand_param b (expect_var arg) in
        (new_body, new_leaves :: l) )
      args (body, []) in
  (* gather new symbol table initialized with the concrete types of the new arguments.
     re-init the type context of the body and type check it afterwards: *)
  let new_pred_vars =
    List.flatten leaves
    |> List.map (fun (p, ty) -> (compile_projection p, ref (TCst ty))) in
  let new_body =
    init_typed_formula {(f_annot body) with vars= new_pred_vars} new_body in
  if Misc.debugging Dbg_rewriting then
    Printf.eprintf
      "Expanding predicate %s with leave arguments %s and new body: %s\n%!" name
      (List.map fst new_pred_vars |> String.concat ",")
      (string_of_formula "" new_body) ;
  type_check_formula_debug (Misc.debugging Dbg_typing) new_body new_body ;
  let new_param_tys = List.map (fun (_, t) -> t) new_pred_vars in
  (* replace the predicate usages in in_f by replacing the single argument by a new list of leaf arguments:  *)
  let new_f_in =
    replace_pred_args p new_param_tys
      (fun args ->
        List.map2
          (fun arg pl -> List.map (fun (p, _) -> expand_arg arg p) pl)
          args leaves
        |> List.flatten )
      in_f in
  let new_args = List.map (fun (v, _) -> Var v) new_pred_vars in
  ( (name, List.length new_args, new_args)
  , preprocess_formula new_body
  , preprocess_formula new_f_in )

(** pre-processes the given complex formula before the actual compilation step.
    Should be run once before compiling on the input formula. *)
and preprocess_formula (f : type_context cplx_formula) : 'a cplx_formula =
  let fdata, fast = f in
  match fast with
  | Equal (t1, t2) -> expand_structural_equality fdata t1 t2
  | Let (p, f1, f2) ->
      ( fdata
      , Let
          (expand_predicate_params p (preprocess_formula f1)
             (preprocess_formula f2) ) )
  | LetPast (p, f1, f2) ->
      ( fdata
      , LetPast
          (expand_predicate_params p (preprocess_formula f1)
             (preprocess_formula f2) ) )
  | Neg f -> (fdata, Neg (preprocess_formula f))
  | And (f1, f2) -> (fdata, And (preprocess_formula f1, preprocess_formula f2))
  | Or (f1, f2) -> (fdata, Or (preprocess_formula f1, preprocess_formula f2))
  | Implies (f1, f2) ->
      (fdata, Implies (preprocess_formula f1, preprocess_formula f2))
  | Equiv (f1, f2) ->
      (fdata, Equiv (preprocess_formula f1, preprocess_formula f2))
  | Exists (vl, f) -> (fdata, Exists (vl, preprocess_formula f))
  | ForAll (vl, f) -> (fdata, ForAll (vl, preprocess_formula f))
  | Aggreg (y, op, x, glist, f) ->
      (fdata, Aggreg (y, op, x, glist, preprocess_formula f))
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
  | Bool v -> (
    match v with False -> Int (Z.of_int 0) | True -> Int (Z.of_int 1) )
  | Null -> Int (Z.of_int 0)
  | Record _ ->
      failwith
        "invalid state: Constant records must be expanded before compilation"

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
  | Proj _ as p -> Var (compile_projection p)

let compile_predicate (tctxt : type_context)
    ((name, arity, args) : cplx_predicate) : predicate =
  (name, arity, List.map (fun t -> compile_term t) args)

(* compiles the given formula and expands all complex free variables part of the given var_filter. *)
let rec compile_formula_scope (var_filter : var list)
    (f : type_context cplx_formula) : MFOTL.formula =
  let tctxt = f_annot f in
  let filtered_cplx_vars =
    List.fold_left
      (fun acc (t, ty) ->
        match (t, !ty) with
        | v, TCst (TRef _) -> if List.mem v var_filter then v :: acc else acc
        | _ -> acc )
      [] tctxt.vars in
  let _, new_vars_list =
    List.map (expand_cplx_var f) filtered_cplx_vars |> filter_some |> List.split
  in
  (* Compile the given input formula and wrap it with an EXISTS quantifier,
     binding all variables introduced by the expansion above: *)
  let new_vars = List.flatten new_vars_list in
  let compiled = _compile_formula f f in
  if List.length new_vars = 0 then compiled
  else MFOTL.Exists (new_vars, compiled)

(** compiles a given complex formula to an MFOTL compatible formula under the given typecheck context.
    f_scope describes the current variable scope. *)
and _compile_formula (f_scope : 'a cplx_formula) (input : 'a cplx_formula) :
    MFOTL.formula =
  let tctxt = f_annot input in
  match f_ast input with
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
    match List.assoc_opt name tctxt.sorts with
    (* no type predicate -> only compile arguments: *)
    | None -> Pred (name, arity, List.map compile_term args)
    (* type predicate: Expand it and introduce new predicates based on the complex argument's
       usage in the current formula scope.
       example: predicate Request(r) and r.user.name in current scope:
       Request(r, r_url, r_user, ...) AND User(r_user, r_user_name, ...) *)
    | Some {fields; _} ->
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
          List.map (expand_cplx_var f_scope) [var_name]
          |> filter_some |> List.split in
        conjunction expansions )
  | Let (p, f1, f2) ->
      let n, a, ts = p in
      let arg_vars =
        List.fold_left
          (fun acc t -> match t with Var v -> v :: acc | _ -> acc)
          [] ts in
      Let
        ( compile_predicate tctxt p
        , compile_formula_scope arg_vars f1
        , _compile_formula f_scope f2 )
  | LetPast (p, f1, f2) ->
      let n, a, ts = p in
      let arg_vars =
        List.fold_left
          (fun acc t -> match t with Var v -> v :: acc | _ -> acc)
          [] ts in
      LetPast
        ( compile_predicate tctxt p
        , compile_formula_scope arg_vars f1
        , _compile_formula f_scope f2 )
  | Neg f -> Neg (_compile_formula f_scope f)
  | And (f1, f2) ->
      And (_compile_formula f_scope f1, _compile_formula f_scope f2)
  | Or (f1, f2) -> Or (_compile_formula f_scope f1, _compile_formula f_scope f2)
  | Implies (f1, f2) ->
      Implies (_compile_formula f_scope f1, _compile_formula f_scope f2)
  | Equiv (f1, f2) ->
      Equiv (_compile_formula f_scope f1, _compile_formula f_scope f2)
  | Exists (l, f) -> Exists (l, compile_formula_scope l f)
  | ForAll (l, f) -> ForAll (l, compile_formula_scope l f)
  | Aggreg (r, op, x, gs, f) ->
      let sz = List.filter (fun v -> not (List.mem v gs)) (free_vars f) in
      let expanded_gs =
        List.map (fun g -> record_leaves tctxt (Var g)) gs
        |> List.flatten
        |> List.map compile_projection in
      let compiled_f = compile_formula_scope sz f in
      Aggreg
        ( compile_tsymb !(List.assoc r tctxt.vars)
        , r
        , op
        , x
        , expanded_gs
        , compiled_f )
  | Prev (i, f) -> Prev (i, _compile_formula f_scope f)
  | Next (i, f) -> Next (i, _compile_formula f_scope f)
  | Eventually (i, f) -> Eventually (i, _compile_formula f_scope f)
  | Once (i, f) -> Once (i, _compile_formula f_scope f)
  | Always (i, f) -> Always (i, _compile_formula f_scope f)
  | PastAlways (i, f) -> PastAlways (i, _compile_formula f_scope f)
  | Since (i, f1, f2) ->
      Since (i, _compile_formula f_scope f1, _compile_formula f_scope f2)
  | Until (i, f1, f2) ->
      Until (i, _compile_formula f_scope f1, _compile_formula f_scope f2)
  | Frex (i, r) -> Frex (i, compile_regex f_scope r)
  | Prex (i, r) -> Prex (i, compile_regex f_scope r)

and compile_regex (scope : type_context cplx_formula)
    (input : type_context regex) : MFOTL.regex =
  match input with
  | Wild -> Wild
  | Test f -> Test (_compile_formula scope f)
  | Concat (r1, r2) -> Concat (compile_regex scope r1, compile_regex scope r2)
  | Plus (r1, r2) -> Plus (compile_regex scope r1, compile_regex scope r2)
  | Star r -> Star (compile_regex scope r)

(** compiles a MFOTL formula from a complex formula and the parsed signature definitions.
    Returns the compiled formula and a flag indicating the monitoriability of the formula. *)
let compile_formula (signatures : signatures) (f : type_context cplx_formula) :
    MFOTL.formula =
  let f = preprocess_formula f in
  if Misc.debugging Dbg_rewriting then
    Printf.eprintf "[compile_formula] Formula after preprocessing: \n%s\n%!"
      (string_of_formula "" f) ;
  let output = compile_formula_scope (free_vars f) f in
  let output = postprocess_formula output in
  if Misc.debugging Dbg_rewriting then
    Printf.eprintf
      "\n%!\n%![compile_formula] The compilation output is %s\n%!\n%!"
      (MFOTL.string_of_formula "" output) ;
  output
