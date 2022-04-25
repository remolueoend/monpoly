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



open Misc

exception Type_error of string

type var = string
type cst =
  | Int of Z.t
  | Str of string
  | Float of float
  | Regexp of (string * Str.regexp) (* (string used to produce the regexp, the compiled regexp) because Str library doesn't provide regexp to string functionality *)

type tcst = TInt | TStr | TFloat | TRegexp
type tcl = TNum | TAny
type tsymb = TSymb of (tcl * int) | TCst of tcst

(* type term =  *)
(*   | Var of var *)
(*   | Cst of cst *)
(*   | Plus of term * term *)
(* user defined function symbol *)
(* | FSymb of (string * term list * (cst list -> cst)) *)

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


(* predicate = name, arity, and list of arguments *)
type predicate = var * int * term list

(* restriction hints
   we assume that rigid predicates are binary
   hence a restiction hint is a pair of positions
*)
type rhint = int * int

let make_predicate (name,args) =
  (name, List.length args, args)


let get_info p = p
let get_name (name,ar,args) = name
let get_args (name,ar,args) = args

let type_of_cst = function
  | Int _ -> TInt
  | Str _ -> TStr
  | Float _ -> TFloat
  | Regexp _ -> TRegexp

let cst_of_str t v = 
  match t with
  | TInt   -> (try Int (Z.of_string v) with Failure _ -> raise (Type_error ("Expecting int for type TInt [cst_of_ts]")))
  | TStr   -> Str v
  | TFloat -> (try Float (float_of_string v) with Failure _ -> raise (Type_error ("Expecting float for type TFloat [cst_of_ts]")))
  | TRegexp -> (try Regexp (v, Str.regexp v) with Failure _ -> raise (Type_error ("Expecting regexp for type TRegexp [cst_of_ts]")))

let cst_of_str_basic v = 
  if (Str.string_match (Str.regexp "^\".+\"$") v 0) then begin
    Str (Str.global_replace (Str.regexp "\"") "" v)
  end else begin
    try Int (Z.of_string v) with Failure _ ->
    try Float (float_of_string v) with Failure _ -> 
    Str v
  end

(* TODO: whould we return a set instead? *)
let rec tvars = function
  | Var v -> [v]
  | Cst c -> []
  | F2i t
  | I2f t
  | I2s t
  | S2i t
  | F2s t
  | S2f t
  | DayOfMonth t
  | Month t
  | Year t
  | FormatDate t
  | UMinus t
  | R2s t
  | S2r t -> tvars t
  | Plus (t1, t2)
  | Minus (t1, t2)
  | Mult (t1, t2)
  | Div (t1, t2)
  | Mod (t1, t2)
    -> (tvars t1) @ (tvars t2)

let substitute_vars m = 
  let subst v = if List.mem_assoc v m then List.assoc v m else Var v in
  let rec substitute_vars_rec = function 
  | Var v -> subst v
  | Cst c as t -> t
  | F2i t -> F2i (substitute_vars_rec t)
  | I2f t -> I2f (substitute_vars_rec t)
  | I2s t -> I2s (substitute_vars_rec t)
  | S2i t -> S2i (substitute_vars_rec t)
  | F2s t -> F2s (substitute_vars_rec t)
  | S2f t -> S2f (substitute_vars_rec t)
  | Month t -> Month (substitute_vars_rec t)
  | DayOfMonth t -> DayOfMonth (substitute_vars_rec t)
  | Year t -> Year (substitute_vars_rec t)
  | FormatDate t -> FormatDate (substitute_vars_rec t)
  | R2s t -> R2s (substitute_vars_rec t)
  | S2r t -> S2r (substitute_vars_rec t)
  | UMinus t -> UMinus (substitute_vars_rec t)
  | Plus (t1, t2) -> Plus (substitute_vars_rec t1, substitute_vars_rec t2)
  | Minus (t1, t2) -> Minus (substitute_vars_rec t1, substitute_vars_rec t2)
  | Mult (t1, t2) -> Mult (substitute_vars_rec t1, substitute_vars_rec t2)
  | Div (t1, t2) -> Div (substitute_vars_rec t1, substitute_vars_rec t2)
  | Mod (t1, t2) -> Mod (substitute_vars_rec t1, substitute_vars_rec t2) 
  in
  substitute_vars_rec 

let safe_gmtime t =
  Unix.gmtime (if t > 4102444800.0 then 4102444800.0 else t)

let eval_eterm f t =
  let rec eval = function
    | Cst c -> c
    | Var x -> f x
    | I2f t -> (match eval t with
        | Int c -> Float (Z.to_float c)
        | _ -> failwith "[Predicate.eval_eterm, i2f] wrong types")
    | F2i t -> (match eval t with
        | Float c ->
            (* TODO(JS): Unclear what the correct behavior should be in case of
               infinities/nan. The code below approximates the previous
               implementation (int_of_float) where the type was Int instead of
               Z.t. Overflow caused an unspecified result, which was 0 in
               practice. *)
            try Int (Z.of_float c)
            with Z.Overflow -> Int Z.zero
        | _ -> failwith "[Predicate.eval_eterm, f2i] wrong types")
    | I2s t -> (match eval t with
        | Int c -> Str (Z.to_string c)
        | _ -> failwith "[Predicate.eval_eterm, i2s] wrong types")
    | S2i t -> (match eval t with
        | Str c ->
            (* TODO(JS): Should be a partial function; see also F2i above. *)
            try Int (Z.of_string c)
            with Invalid_argument _ -> Int Z.zero
        | _ -> failwith "[Predicate.eval_eterm, s2i] wrong types")
    | F2s t -> (match eval t with
        | Float c -> Str (Float.to_string c)
        | _ -> failwith "[Predicate.eval_eterm, i2s] wrong types")
    | S2f t -> (match eval t with
        | Str c ->
            (* TODO(JS): Should be a partial function; see also F2i above. *)
            try Float (Float.of_string c)
            with Failure _ -> Float 0.
        | _ -> failwith "[Predicate.eval_eterm, s2f] wrong types")
    | DayOfMonth t -> (match eval t with
        | Float t -> Int (Z.of_int (safe_gmtime t).tm_mday)
        | _ -> failwith "[Predicate.eval_eterm, DayOfMonth] wrong types")
    | Month t -> (match eval t with
        | Float t -> Int (Z.of_int ((safe_gmtime t).tm_mon+1))
        | _ -> failwith "[Predicate.eval_eterm, Month] wrong types")
    | Year t -> (match eval t with
        | Float t -> Int (Z.of_int ((safe_gmtime t).tm_year+1900))
        | _ -> failwith "[Predicate.eval_eterm, year] wrong types")
    | FormatDate t -> (match eval t with
        | Float t -> 
            let tm = safe_gmtime t in
            Str (Printf.sprintf "%04d-%02d-%02d" (tm.tm_year + 1900) (tm.tm_mon + 1) tm.tm_mday)
        | _ -> failwith "[Predicate.eval_eterm, Month] wrong types")
    | R2s t -> (match eval t with
        | Regexp (p, r) -> Str p
        | _ -> failwith "[Predicate.eval_eterm, r2s] wrong types")
    | S2r t -> (match eval t with
        | Str s -> Regexp (s, try Str.regexp s
            with _ -> failwith ("[Predicate.eval_eterm, s2r] Invalid Regexp '" ^ s ^ "'"))
        | _ -> failwith "[Predicate.eval_eterm, r2s] wrong types")
    | Plus (t1, t2) ->
      (match eval t1, eval t2 with
       | Int c1, Int c2 -> Int Z.(c1 + c2)
       | Float c1, Float c2 -> Float (c1 +. c2)
       | _ -> failwith "[Predicate.eval_eterm, +] wrong types")
    | Minus (t1, t2) ->
      (match eval t1, eval t2 with
       | Int c1, Int c2 -> Int Z.(c1 - c2)
       | Float c1, Float c2 -> Float (c1 -. c2)
       | _ -> failwith "[Predicate.eval_eterm, binary -] wrong types")
    | Mult (t1, t2) ->
      (match eval t1, eval t2 with
       | Int c1, Int c2 -> Int Z.(c1 * c2)
       | Float c1, Float c2 -> Float (c1 *. c2)
       | _ -> failwith "[Predicate.eval_eterm, *] wrong types")
    | Div (t1, t2) ->
      (match eval t1, eval t2 with
       | Int c1, Int c2 -> Int Z.(c1 / c2)
       | Float c1, Float c2 -> Float (c1 /. c2)
       | _ -> failwith "[Predicate.eval_eterm, /] wrong types")
    | Mod (t1, t2) ->
      (match eval t1, eval t2 with
       | Int c1, Int c2 -> Int Z.(c1 mod c2)
       | _ -> failwith "[Predicate.eval_eterm, mod] wrong types")
    | UMinus t ->
      (match eval t with
       | Int c -> Int Z.(- c)
       | Float c -> Float (-. c)
       | _ -> failwith "[Predicate.eval_eterm, unary -] wrong type")
  in
  eval t


let eval_term assign =
  eval_eterm (fun x -> List.assoc x assign)

(* evaluate ground term *)
let eval_gterm t = eval_term [] t

let plus a b =
  match a, b with
  | Int x, Int y -> Int Z.(x+y)
  | Float x, Float y -> Float (x+.y)
  | _ -> failwith "[Predicate.plus] type error"

let minus a b =
  match a, b with
  | Int x, Int y -> Int Z.(x-y)
  | Float x, Float y -> Float (x-.y)
  | _ -> failwith "[Predicate.minus] type error"

let average a b =
  match a, b with
  | Int x, Int y -> Float ((Z.to_float x +. Z.to_float y) /. 2.)
  | Float x, Float y -> Float ((x+.y)/.2.)
  | _ -> failwith "[Predicate.avg] type error"

let float_of_cst = function
  | Int x -> Z.to_float x
  | Float x -> x
  | _ -> failwith "[Predicate.float_of_cst] type error"


(* TODO: should we return a set instead? *)
(* Note. This function must compute the variables in the order
   in which they are assigned by the function Tuple.satisfiesp. *)
let pvars (p:predicate) =
  let rec get_vars assign res args =
    match args with
    | [] -> List.rev res
    | term :: args' ->
      (match term with
       | Var x ->
         (try
            let _ = List.assoc x assign in
            get_vars assign res args'
          with Not_found ->
            get_vars ((x, ()) :: assign) (x :: res) args'
         )
       | _ -> get_vars assign res args'
      )
  in
  get_vars [] [] (get_args p)


let cst_eq c c' =
  match c, c' with
  | Int a, Int a'     -> Z.equal a a'
  | Str a, Str a'     -> String.equal a a'
  | Float f, _ -> failwith "comparing float"
  | _, Float f -> failwith "comparing float"
  | _ -> failwith "[Predicate.cst_eq] incomparable constants"

let cst_smaller c c' =
  match c,c' with
  | Int a, Int a' -> Z.lt a a'
  | Str a, Str a' -> a < a'
  | _ -> failwith "[Predicate.cst_smaller] incomparable constants"

let cst_smaller_eq c c' =
  match c,c' with
  | Int a, Int a' -> Z.leq a a'
  | Str a, Str a' -> a <= a'
  | _ -> failwith "[Predicate.cst_smaller_eq] incomparable constants"


let int_of_cst = function
  | Int n -> Z.to_int n
  | _ -> failwith "[Predicate.int_of_cst]"

let print_var = print_string

let print_tcst t =
  match t with
  | TInt -> print_string "int"
  | TStr -> print_string "string"
  | TFloat -> print_string "float"
  | TRegexp -> print_string "regexp"

let string_of_var var =
  var

let rec string_of_cst c =
  let format_string s =
    if s = "" then "\"\""
      else
        if (s.[0] = '\"' && s.[(String.length s)-1] = '\"') then
          s
        else "\"" ^ s ^ "\""

  in match c with
  | Int i -> Z.to_string i
  | Float f -> Printf.sprintf "%g" f
  | Str s -> format_string s
  | Regexp (p, _) -> Printf.sprintf "r%s" (format_string p)

let print_cst c = print_string (string_of_cst c)
let prerr_cst c = prerr_string (string_of_cst c)



let rec string_of_term term =
  let add_paren str = "(" ^ str ^ ")" in
  let rec t2s b term =
    let b', str = match term with
      | Var v -> true, v
      | Cst c -> true, string_of_cst c
      | F2i t ->  false, "f2i(" ^ (t2s true t) ^ ")"
      | I2f t ->  false, "i2f(" ^ (t2s true t) ^ ")"
      | I2s t ->  false, "i2s(" ^ (t2s true t) ^ ")"
      | S2i t ->  false, "s2i(" ^ (t2s true t) ^ ")"
      | F2s t ->  false, "f2s(" ^ (t2s true t) ^ ")"
      | S2f t ->  false, "s2f(" ^ (t2s true t) ^ ")"
      | R2s t ->  false, "r2s(" ^ (t2s true t) ^ ")"
      | S2r t ->  false, "s2r(" ^ (t2s true t) ^ ")"
      | Year t ->  false, "YEAR(" ^ (t2s true t) ^ ")"
      | Month t ->  false, "MONTH(" ^ (t2s true t) ^ ")"
      | DayOfMonth t ->  false, "DAY_OF_MONTH(" ^ (t2s true t) ^ ")"
      | FormatDate t ->  false, "FORMAT_DATE(" ^ (t2s true t) ^ ")"
      | UMinus t ->  false, "-" ^ (t2s' t)
      | Plus (t1, t2) -> false, (t2s' t1) ^ " + " ^ (t2s' t2)
      | Minus (t1, t2) -> false, (t2s' t1) ^ " - " ^ (t2s' t2)
      | Mult (t1, t2) -> false, (t2s' t1) ^ " * " ^ (t2s' t2)
      | Div (t1, t2) -> false, (t2s' t1) ^ " / " ^ (t2s' t2)
      | Mod (t1, t2) -> false, (t2s' t1) ^ " mod " ^ (t2s' t2)
    in
    (* we don't add parentheses for the top-most operator, nor around
       constants and variables *)
    if b || b' then str else add_paren str
  and
    t2s' term = t2s false term
  in
  t2s true term

let print_term t = print_string (string_of_term t)
let prerr_term t = prerr_string (string_of_term t)


let string_of_predicate (p,ar,args) =
  string_of_var p ^ Misc.string_of_list string_of_term args

let print_predicate (p,ar,args) =
  print_var p;
  Misc.print_list print_term args

let prerr_predicate (p,ar,args) =
  prerr_string p;
  Misc.prerr_list prerr_term args

let print_vartypes_list vartypes_list =
  Misc.print_list_ext "" "" ", "
    (fun (v,t) ->
       print_string (v ^ ":");
       match t with
       | TInt -> print_string "int"
       | TStr -> print_string "string"
       | TFloat -> print_string "float"
       | TRegexp -> print_string "regexp"
    )
    vartypes_list;
  print_newline()
