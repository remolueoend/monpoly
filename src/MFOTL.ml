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

type timestamp = Z.t
type tsdiff = timestamp
type bound = OBnd of tsdiff | CBnd of tsdiff | Inf
type interval = bound * bound

type agg_op = Cnt | Min | Max | Sum | Avg | Med


type formula =
  | Equal of (term * term)
  | Less of (term * term)
  | LessEq of (term * term)
  | Substring of (term * term)
  | Matches of (term * term * term option list)
  | Pred of predicate
  | Let of (predicate * formula * formula)
  | LetPast of (predicate * formula * formula)
  | Neg of formula
  | And of (formula * formula)
  | Or of (formula * formula)
  | Implies of (formula * formula)
  | Equiv of (formula * formula)
  | Exists of (var list * formula)
  | ForAll of (var list * formula)
  | Aggreg of (tsymb * var * agg_op * var * var list * formula)
  | Prev of (interval * formula)
  | Next of (interval * formula)
  | Eventually of (interval * formula)
  | Once of (interval * formula)
  | Always of (interval * formula)
  | PastAlways of (interval * formula)
  | Since of (interval * formula * formula)
  | Until of (interval * formula * formula)
  | Frex of (interval * regex)
  | Prex of (interval * regex)
and regex = 
  | Wild
  | Test of formula
  | Concat of (regex * regex)
  | Plus of (regex * regex)
  | Star of regex
  


let unixts = ref false

let ts_of_string str =
  try
    Z.of_string str
  with Failure _ ->
    let msg = Printf.sprintf "[MFOTL.ts_of_string] Cannot convert %s into a timestamp" str in
    failwith msg

let ts_plus t1 t2 = Z.add t1 t2
let ts_minus t1 t2 = Z.sub t1 t2
let ts_invalid = Z.minus_one
let ts_null = Z.zero
let ts_max = Z.pow (Z.of_int 2) 64

(* TODO: these function names are not intuitive, because one usually
   does not think in terms of the interval I labelling a temporal
   operator, but instead, in terms of the time window that it defines.
   So update these, with something like, left_of_timewindow,
   right_of_timewindow, in_timewindow.
*)

(* Tests that [v] is in the extension to the right of [intv] *)
let in_right_ext v intv =
  match intv with
  | CBnd b, _ -> v >= b
  | OBnd b, _ -> v > b
  | Inf, _ -> false

(* Tests that [v] is in the extension to the left of [intv] *)
let in_left_ext v intv =
  match intv with
  | _, CBnd b -> v <= b
  | _, OBnd b -> v < b
  | _, Inf -> true

let in_interval v intv =
  in_right_ext v intv && in_left_ext v intv

let infinite_interval (_, b) = (b = Inf)

let init_interval (_, b) = (CBnd Z.zero, b)

let aggreg_default_value op t = match op, t with
  | Min, TFloat -> Float infinity
  | Max, TFloat -> Float neg_infinity
  | _, TFloat -> Float 0.
  | _, TInt -> Int Z.zero
  | _, TStr -> Str ""
  | _, TRegexp -> Regexp ("", Str.regexp "")


let map mapf mapr =
let rec formula_map = function
  | Equal (_,_)
  | Less (_,_)
  | LessEq (_,_) 
  | Matches (_,_,_)
  | Substring (_,_) 
  | Pred _ as f -> mapf f
  | Let (p,f1,f2) -> 
    let f1 = formula_map f1 in
    let f2 = formula_map f2 in
    mapf (Let (p,f1,f2))
  | LetPast (p,f1,f2) -> 
    let f1 = formula_map f1 in
    let f2 = formula_map f2 in
    mapf (LetPast (p,f1,f2))
  | Neg f -> mapf (Neg (formula_map f))
  | And (f1,f2) ->
    let f1 = formula_map f1 in
    let f2 = formula_map f2 in
    mapf (And (f1,f2))
  | Or (f1,f2) -> 
    let f1 = formula_map f1 in
    let f2 = formula_map f2 in
    mapf (Or (f1,f2))
  | Implies (f1,f2) -> 
    let f1 = formula_map f1 in
    let f2 = formula_map f2 in
    mapf (Implies (f1,f2))
  | Equiv (f1,f2) -> 
    let f1 = formula_map f1 in
    let f2 = formula_map f2 in
    mapf (Equiv (f1,f2))
  | Exists (v,f) -> mapf (Exists (v,formula_map f))
  | ForAll (v,f) -> mapf (ForAll (v,formula_map f))
  | Aggreg (rty,r,op,x,gs,f) -> mapf (Aggreg (rty,r,op,x,gs,formula_map f))
  | Prev (intv,f) -> mapf (Prev (intv,formula_map f))
  | Next (intv,f) -> mapf (Next (intv,formula_map f))
  | Eventually (intv,f) -> mapf (Eventually (intv,formula_map f))
  | Once (intv,f) -> mapf (Once (intv,formula_map f))
  | Always (intv,f)     -> mapf (Always (intv,formula_map f))
  | PastAlways (intv,f) -> mapf (PastAlways (intv,formula_map f))
  | Since (intv,f1,f2) -> 
    let f1 = formula_map f1 in
    let f2 = formula_map f2 in
    mapf (Since (intv,f1,f2))
  | Until (intv,f1,f2) -> 
    let f1 = formula_map f1 in
    let f2 = formula_map f2 in
    mapf (Until (intv,f1,f2))
  | Frex (intv,r) -> mapf (Frex (intv,(formula_re_map r)))
  | Prex (intv,r) -> mapf (Prex (intv,(formula_re_map r)))
and formula_re_map = function 
  | Wild -> mapr Wild
  | Test f -> mapr (Test (formula_map f))
  | Concat (r1,r2) ->
    let r1 = formula_re_map r1 in
    let r2 = formula_re_map r2 in
    mapr (Concat (r1,r2))
  | Plus (r1,r2) -> 
    let r1 = formula_re_map r1 in
    let r2 = formula_re_map r2 in
    mapr (Plus (r1,r2))
  | Star r -> mapr (Star (formula_re_map r)) 
in
formula_map


(** returns the list of all direct subformulas of f, ignoring the regexes *)
let rec direct_subformulas = function
  | Equal (t1,t2) -> []
  | Less (t1,t2) -> []
  | LessEq (t1,t2) -> []
  | Matches (t1,t2,tl) -> []
  | Substring (t1, t2) -> []
  | Pred p -> []
  | Let (p,f1,f2) -> [f1;f2]
  | LetPast (p,f1,f2) -> [f1;f2]
  | Neg f -> [f]
  | And (f1,f2) -> [f1;f2]
  | Or (f1,f2) -> [f1;f2]
  | Implies (f1,f2) -> [f1;f2]
  | Equiv (f1,f2) -> [f1;f2]
  | Exists (v,f) -> [f]
  | ForAll (v,f) -> [f]
  | Aggreg (_,_,_,_,_,f) -> [f]
  | Prev (intv,f) -> [f]
  | Next (intv,f) -> [f]
  | Eventually (intv,f) -> [f]
  | Once (intv,f) -> [f]
  | Always (intv,f) -> [f]
  | PastAlways (intv,f) -> [f]
  | Since (intv,f1,f2) -> [f1;f2]
  | Until (intv,f1,f2) -> [f1;f2]
  | Frex (intv,r) -> direct_re_subformulas r
  | Prex (intv,r) -> direct_re_subformulas r
and direct_re_subformulas = function 
  | Wild -> []
  | Test f -> [f]
  | Concat (r1,r2) 
  | Plus (r1,r2) -> (direct_re_subformulas r1) @ (direct_re_subformulas r2)
  | Star r -> (direct_re_subformulas r) 


(** returns the list of all subformulas of [f], including [f], ignoring the regexes *)
let rec subformulas f =
   f::(List.concat (List.map subformulas (direct_subformulas f)))


let predicates f = List.filter (fun x -> match x with Pred _ -> true | _ -> false) (subformulas f)

(** returns the list of all temporal subformulas of [f], ignoring regexes *)
let rec temporal_subformulas f =
  match f with
  | Prev (intv,f') -> f::(temporal_subformulas f')
  | Next (intv,f') -> f::(temporal_subformulas f')
  | Eventually (intv,f') -> f::(temporal_subformulas f')
  | Once (intv,f') -> f::(temporal_subformulas f')
  | Always (intv,f') -> f::(temporal_subformulas f')
  | PastAlways (intv,f') -> f::(temporal_subformulas f')
  | Since (intv,f1,f2) -> f::((temporal_subformulas f1) @ (temporal_subformulas f2))
  | Until (intv,f1,f2) -> f::((temporal_subformulas f1) @ (temporal_subformulas f2))
  | Frex (intv,r) -> f::(temporal_re_subformulas r)
  | Prex (intv,r) -> f::(temporal_re_subformulas r)
  | _ -> List.concat (List.map temporal_subformulas (direct_subformulas f))
and temporal_re_subformulas = function
  | Wild -> []
  | Test f -> temporal_subformulas f
  | Concat (r1,r2) 
  | Plus (r1,r2) -> (temporal_re_subformulas r1) @ (temporal_re_subformulas r2)
  | Star r -> (temporal_re_subformulas r)



let is_temporal = function
  | Prev (intv,f) -> true
  | Next (intv,f) -> true
  | Since (intv,f1,f2) -> true
  | Until (intv,f1,f2) -> true
  | Eventually (intv,f) -> true
  | Once (intv,f) -> true
  | Always (intv,f) -> true
  | PastAlways (intv,f) -> true
  | Frex (intv,r) -> true
  | Prex (intv,r) -> true
  | _ -> false

let is_regular = function
  | Frex (intv,r) 
  | Prex (intv,r) -> true
  | _ -> false

let rec is_mfodl = function 
  | Equal (t1,t2) 
  | Less (t1,t2) 
  | LessEq (t1,t2) 
  | Substring (t1,t2)
  | Matches (t1,t2,_) -> false
  | Pred p -> false
  | Let (_,f1,f2) -> is_mfodl f1 || is_mfodl f2
  | LetPast (_,f1,f2) -> is_mfodl f1 || is_mfodl f2
  | Neg f -> is_mfodl f
  | And (f1,f2) 
  | Or (f1,f2) 
  | Implies (f1,f2)
  | Equiv (f1,f2) -> is_mfodl f1 || is_mfodl f2
  | Exists (v,f) 
  | ForAll (v,f) -> is_mfodl f
  | Aggreg (_,_,_,_,_,f) -> is_mfodl f
  | Prev (intv,f) 
  | Next (intv,f) 
  | Eventually (intv,f) 
  | Once (intv,f)
  | Always (intv,f)
  | PastAlways (intv,f) -> is_mfodl f
  | Since (intv,f1,f2) -> is_mfodl f1 || is_mfodl f2
  | Until (intv,f1,f2) -> is_mfodl f1 || is_mfodl f2
  | Frex (intv,r) 
  | Prex (intv,r) -> true



let rec free_vars = function
  | Equal (t1,t2)
  | Less (t1,t2)
  | LessEq (t1,t2)
  | Substring (t1,t2) ->
    Misc.union (Predicate.tvars t1) (Predicate.tvars t2)
  | Matches (t1,t2,tl) ->
    let fv = Misc.union (Predicate.tvars t1) (Predicate.tvars t2) in
    List.fold_left (fun s t ->
      match t with
      | None -> s
      | Some t -> Misc.union s (Predicate.tvars t)) fv tl
  | Pred p -> Predicate.pvars p
  | Let (_,_,f) -> free_vars f
  | LetPast (_,_,f) -> free_vars f
  | Neg f -> free_vars f
  | And (f1,f2) 
  | Or (f1,f2) 
  | Implies (f1,f2) 
  | Equiv (f1,f2) -> Misc.union (free_vars f1) (free_vars f2)
  | Exists (vl,f) 
  | ForAll (vl,f) -> List.filter (fun x -> not (List.mem x vl)) (free_vars f)
  | Aggreg (rty,y,op,x,glist,f) -> y :: glist
  | Prev (intv,f) 
  | Next (intv,f) 
  | Eventually (intv,f) 
  | Once (intv,f) 
  | Always (intv,f) 
  | PastAlways (intv,f) -> free_vars f
  | Since (intv,f1,f2) 
  | Until (intv,f1,f2) -> Misc.union (free_vars f2) (free_vars f1)
  | Frex (intv,r)
  | Prex (intv,r) -> free_re_vars r
and free_re_vars = function 
  | Wild -> []
  | Test f -> free_vars f
  | Concat (r1,r2) 
  | Plus (r1,r2) -> Misc.union (free_re_vars r1) (free_re_vars r2)
  | Star r -> (free_re_vars r)

let fresh_var fv =
  let rec fresh_var_rec v = 
    let var = "_x" ^ (string_of_int v) in
    if List.exists (fun x -> x=var) fv
    then
      fresh_var_rec (v+1)
    else var
  in
  fresh_var_rec 1

let fresh_var_mapping fv vs = 
    List.fold_left 
      (fun (fvs, m) rn -> 
        let fv = fresh_var fvs 
        in (fv::fvs, (rn, fv)::m)
      ) 
      (fv,[]) 
    vs


let rec substitute_vars m = 
  let m = List.filter (fun (v,t) -> match t with | Var a -> a!=v | _ -> true ) m in
  function 
  | Equal (t1, t2) -> Equal (Predicate.substitute_vars m t1, Predicate.substitute_vars m t2)
  | Less  (t1, t2) -> Less (Predicate.substitute_vars m t1, Predicate.substitute_vars m t2)
  | LessEq (t1, t2) -> LessEq (Predicate.substitute_vars m t1, Predicate.substitute_vars m t2)
  | Matches (t1, t2, tl) -> Matches
      (Predicate.substitute_vars m t1,
      Predicate.substitute_vars m t2,
      List.map (Option.map (Predicate.substitute_vars m)) tl)
  | Substring (t1, t2) -> Substring (Predicate.substitute_vars m t1, Predicate.substitute_vars m t2)

  | Pred (p) -> 
    let (n,a,ts) = Predicate.get_info p in
    Pred (Predicate.make_predicate (n,List.map (Predicate.substitute_vars m) ts))
    
  | Let (p, f1, f2) -> Let (p, f1, substitute_vars m f2)
  | LetPast (p, f1, f2) -> LetPast (p, f1, substitute_vars m f2)

  | Neg f -> Neg (substitute_vars m f)
  | Exists (v, f) -> 
      let fv = free_vars f in
      let tvars = List.flatten (List.map (fun (_,t) -> Predicate.tvars t) m) in
      let bv_rename = List.filter (fun x -> List.mem x tvars) v in
      let (_,fresh_var_map) = fresh_var_mapping (Misc.union fv tvars) bv_rename in
      Exists (
        Misc.replace fresh_var_map v,
        let no_bv =  (List.filter (fun (x,_) -> not (List.mem x v)) m) in
        let fresh_var_map = List.map (fun (a, b) -> (a, Var b)) fresh_var_map in
        substitute_vars (no_bv@fresh_var_map) f)
  | ForAll (v, f) -> 
      let fv = free_vars f in
      let tvars = List.flatten (List.map (fun (_,t) -> Predicate.tvars t) m) in
      let bv_rename = List.filter (fun x -> List.mem x tvars) v in
      let (_,fresh_var_map) = fresh_var_mapping (Misc.union fv tvars) bv_rename in
      ForAll (
        Misc.replace fresh_var_map v,
        let no_bv =  (List.filter (fun (x,_) -> not (List.mem x v)) m) in
        let fresh_var_map = List.map (fun (a, b) -> (a, Var b)) fresh_var_map in
        substitute_vars (no_bv@fresh_var_map) f) 
  | Aggreg (rty, y, op, x, g, f) ->
      let fv = free_vars f in
      let bvars = Misc.diff fv g in
      let tvars = List.flatten (List.map (fun (_,t) -> Predicate.tvars t) m) in
      let bv_rename = Misc.inter tvars bvars in
      let (_,fresh_var_map) = fresh_var_mapping (Misc.union fv tvars) bv_rename in
      let no_bv = (List.filter (fun (x,_) -> not (List.mem x bvars)) m) in
      let m' = no_bv @ List.map (fun (a, b) -> (a, Var b)) fresh_var_map in

      (* Temporaries for substitution of y and/or g by non-variables *)
      let avoid_vars = Misc.union (y :: g) tvars in
      let tmp_y = fresh_var avoid_vars in
      let (_, tmp_gm) = fresh_var_mapping (tmp_y :: avoid_vars) g in

      (* Note: We could continue the substitution with the original m' and
         instead remove the variables that are replaced by constants from g.
         However, if g was nonempty but becomes empty after the substitution,
         the semantics changes! To prevent this we must add a fake grouping
         variable, which must occur in f, etc. Possible, but not simpler. *)
      let m'' = List.map (fun (v, t) ->
        match t with
        | Var _ -> (v, t)
        | _ ->
            (match List.assoc_opt v tmp_gm with
            | None -> (v, t)
            | Some tmp -> (v, Var tmp))
        ) m' in

      let subst m v = try List.assoc v m with Not_found -> Var v in
      let unvar tmp = function
        | Var x -> (x, [])
        | t -> (tmp, [(tmp, t)])
      in
      let (y, y_constrs) = unvar tmp_y (subst m y) in
      let x = try List.assoc x fresh_var_map with Not_found -> x in
      let (g, g_constrss) = List.split
        (List.map (fun (x, tmp) -> unvar tmp (subst m' x)) tmp_gm) in
      let f_agg = Aggreg (rty, y,op,x,g, substitute_vars m'' f) in

      let constrs = y_constrs @ List.flatten g_constrss in
      let f_agg = List.fold_left (fun f (v, t) ->
        And (f, Equal (Var v, t))) f_agg constrs in
      if constrs = [] then
        f_agg
      else
        Exists (List.map fst constrs, f_agg)
  | Prev (i, f) -> Prev (i,substitute_vars m f)
  | Next (i, f) -> Next (i,substitute_vars m f)
  | Once (i, f) -> Once (i, substitute_vars m f)
  | PastAlways (i, f) -> PastAlways (i, substitute_vars m f)
  | Eventually (i, f) -> Eventually (i, substitute_vars m f)
  | Always (i, f) -> Always (i, substitute_vars m f)

  | Prex (i, r) -> Prex (i, substitute_re_vars m r)
  | Frex (i, r) -> Frex (i, substitute_re_vars m r)

  | And (f1, f2) -> And (substitute_vars m f1, substitute_vars m f2)
  | Or (f1, f2) -> Or (substitute_vars m f1, substitute_vars m f2)
  | Implies (f1, f2) -> Implies (substitute_vars m f1, substitute_vars m f2)
  | Equiv (f1, f2) ->  Equiv (substitute_vars m f1, substitute_vars m f2)
  | Since (i, f1, f2) -> Since (i, substitute_vars m f1, substitute_vars m f2)
  | Until (i, f1, f2) -> Until (i, substitute_vars m f1, substitute_vars m f2)
and substitute_re_vars m = function
  | Wild -> Wild 
  | Test f -> Test (substitute_vars m f)
  | Concat (r1,r2) -> Concat ((substitute_re_vars m r1), (substitute_re_vars m r2))
  | Plus (r1,r2) -> Plus (substitute_re_vars m r1, (substitute_re_vars m r2))
  | Star r -> Star (substitute_re_vars m r) 

let same_pred p1 p2 =
  let (n1, a1, _) = get_info p1 in
  let (n2, a2, _) = get_info p2 in
  n1 = n2 && a1 = a2

let count_pred_uses pred f =
  let rec go = function
    | Equal _
    | Less _
    | LessEq _
    | Matches _
    | Substring _ -> 0

    | Pred p -> if same_pred p pred then 1 else 0

    | Let (p, f1, f2) ->
        let c1 = go f1 in
        let c2 = if same_pred p pred then 0 else go f2 in
        c1 + c2
    | LetPast (p, f1, f2) ->
        if same_pred p pred then 0 else go f1 + go f2

    | Neg f
    | Exists (_, f)
    | ForAll (_, f)
    | Aggreg (_, _, _, _, _, f)
    | Prev (_, f)
    | Next (_, f)
    | Once (_, f)
    | PastAlways (_, f)
    | Eventually (_, f)
    | Always (_, f) -> go f

    | Prex (_, r)
    | Frex (_, r) -> go_re r

    | And (f1, f2)
    | Or (f1, f2)
    | Implies (f1, f2)
    | Equiv (f1, f2)
    | Since (_, f1, f2)
    | Until (_, f1, f2) -> go f1 + go f2
  and go_re = function
    | Wild -> 0
    | Test f -> go f
    | Concat (r1, r2)
    | Plus (r1, r2) -> go_re r1 + go_re r2
    | Star r -> go_re r
  in
  go f



let string_of_ts ts =
  if !unixts then
    let tm = Unix.gmtime (Z.to_float ts) in
    Printf.sprintf "%d-%d-%d %d:%d:%d"
      tm.tm_year tm.tm_mon tm.tm_mday
      tm.tm_hour tm.tm_min tm.tm_sec
  else
    if ts = ts_max then
      "MaxTS"
    else
      Z.to_string ts

let print_ts ts = print_string (string_of_ts ts)
let prerr_ts ts = prerr_string (string_of_ts ts)

let string_of_interval (a,b) =
  (match a with
    | OBnd a -> Printf.sprintf "(%s," (Z.to_string a)
    | CBnd a -> Printf.sprintf "[%s," (Z.to_string a)
    | Inf -> Printf.sprintf "(*,") 
  ^
  (match b with
  | OBnd b -> Printf.sprintf "%s)" (Z.to_string b)
  | CBnd b -> Printf.sprintf "%s]" (Z.to_string b)
  | Inf -> Printf.sprintf "*)")

let print_interval (a,b) = Printf.printf "%s" (string_of_interval (a,b))
let prerr_interval (a,b) = Printf.eprintf "%s" (string_of_interval (a,b))

let string_of_agg_op = function
  | Cnt -> "CNT"
  | Min -> "MIN"
  | Max -> "MAX"
  | Sum -> "SUM"
  | Avg -> "AVG"
  | Med -> "MED"


let rec type_of_fma = function
  | Equal (t1,t2) -> "Eq"
  | Less (t1,t2) -> "Less"
  | LessEq (t1,t2) -> "LessEq"
  | Substring (t1, t2) -> "Substring"
  | Matches (t1, t2, tl) -> "Matches"
  | Pred p -> "Pred"
  | Let (p,f1,f2) -> "Let"
  | LetPast (p,f1,f2) -> "LetPast"
  | Neg f -> "Neg"
  | And (f1,f2) -> "And"
  | Or (f1,f2) -> "Or"
  | Implies (f1,f2) -> "Implies"
  | Equiv (f1,f2) -> "Equiv"
  | Exists (vl,f) -> "Exists"
  | ForAll (vl,f) -> "Forall"
  | Aggreg (rty,y,op,x,glist,f) -> "Agggreg"
  | Prev (intv,f) -> "Prev"
  | Next (intv,f) -> "Next"
  | Eventually (intv,f) -> "Eventually"
  | Once (intv,f) -> "Once"
  | Always (intv,f) -> "Always"
  | PastAlways (intv,f) -> "PastAlways"
  | Since (intv,f1,f2) -> "Since"
  | Until (intv,f1,f2) -> "Unitl"
  | Frex (intv,f1) -> "Frex"
  | Prex (intv,f1) -> "Prex"

let string_of_opt_term = function
  | None -> "_"
  | Some t -> Predicate.string_of_term t

(* we always put parantheses for binary operators like "(f1 AND f2)", and around unary
ones only if they occur on the left-hand side of a binary operator: like "((NOT f1) AND f2)"*)
let string_of_formula str g =
  let pps = String.split_on_char '\n' str in
  let padding = if pps==[] then "" else String.map (fun s -> ' ') (List.nth pps ((List.length pps)-1)) in
  let rec string_f_rec top par h =
    (match h with
      | Equal (t1,t2) ->
        Predicate.string_of_term t1 ^ " = " ^ Predicate.string_of_term t2
      | Less (t1,t2) ->
        Predicate.string_of_term t1 ^ " < " ^ Predicate.string_of_term t2
      | LessEq (t1,t2) ->
        Predicate.string_of_term t1 ^ " <= " ^ Predicate.string_of_term t2
      | Substring (t1,t2) ->
        Predicate.string_of_term t1 ^ " SUBSTRING " ^ Predicate.string_of_term t2
      | Matches (t1,t2,tl) ->
        Predicate.string_of_term t1 ^ " MATCHES " ^ Predicate.string_of_term t2
        ^
        (if tl = [] then ""
          else Misc.string_of_list_ext " (" ")" ", " string_of_opt_term tl)
      | Pred p -> Predicate.string_of_predicate p
      | _ ->
        (if par && not top then "(" else "")
        ^ 
        (match h with
        | Neg f ->
          "NOT " ^ string_f_rec false false f

        | Exists (vl,f) ->
          "EXISTS " 
          ^ 
          (Misc.string_of_list_ext "" "" ", " Predicate.string_of_term (List.map (fun v -> Var v) vl))
          ^
          ". "
          ^
          (string_f_rec false false f)

        | ForAll (vl,f) ->
          "FORALL "
          ^
          (Misc.string_of_list_ext "" "" ", " Predicate.string_of_term (List.map (fun v -> Var v) vl))
          ^
          ". "
          ^
          (string_f_rec false false f)

        | Aggreg (rty,y,op,x,glist,f) ->
          (Predicate.string_of_term (Var y))
          ^
          " <- "
          ^
          (string_of_agg_op op)
          ^
          " "
          ^
          (Predicate.string_of_term (Var x))
          ^
          (if glist <> [] then
              "; "
              ^
              (Misc.string_of_list_ext "" "" "," (fun z -> Predicate.string_of_term (Var z)) glist)
          else "")
          ^
          " "
          ^
          (string_f_rec false false f)

        | Prev (intv,f) ->
          "PREVIOUS"
          ^
          (string_of_interval intv)
          ^
          " "
          ^
          (string_f_rec false false f)

        | Next (intv,f) ->
          "NEXT"
          ^
          (string_of_interval intv)
          ^
          " "
          ^
          (string_f_rec false false f)

        | Eventually (intv,f) ->
          "EVENTUALLY"
          ^
          (string_of_interval intv)
          ^
          " "
          ^
          (string_f_rec false false f)

        | Once (intv,f) ->
          "ONCE"
          ^
          (string_of_interval intv)
          ^
          " "
          ^
          (string_f_rec false false f)

        | Always (intv,f) ->
          "ALWAYS"
          ^
          (string_of_interval intv)
          ^
          " "
          ^
          (string_f_rec false false f)

        | PastAlways (intv,f) ->
          "PAST_ALWAYS"
          ^
          (string_of_interval intv)
          ^
          " "
          ^
          (string_f_rec false false f)

        | Frex (intv, r) -> 
          "|>"
          ^
          (string_of_interval intv)
          ^
          (string_r_rec false false r)

        | Prex (intv, r) -> 
          "<|"
          ^
          (string_of_interval intv)
          ^
          (string_r_rec false false r)

        | _ ->
          (if not par && not top then "(" else "")
          ^
          (match h with
            | And (f1,f2) ->
              (string_f_rec false true f1)
              ^
              " AND " 
              ^
              (string_f_rec false true f2)

            | Or (f1,f2) ->
              (string_f_rec false true f1)
              ^
              " OR "
              ^
              (string_f_rec false false f2)

            | Implies (f1,f2) ->
              (string_f_rec false true f1)
              ^
              " IMPLIES "
              ^
              (string_f_rec false false f2)

            | Equiv (f1,f2) ->
              (string_f_rec false true f1)
              ^
              " EQUIV "
              ^
              (string_f_rec false false f2)

            | Let (p,f1,f2) ->
              "LET"
              ^
              " "
              ^
              (string_f_rec false true (Pred p))
              ^
              " = "
              ^
              (string_f_rec false true f1)
              ^
              "\n"
              ^ 
              padding
              ^
              "IN"
              ^
              " "
              ^
              (string_f_rec false false f2)  

            | LetPast (p,f1,f2) ->
              "LETPAST"
              ^
              " "
              ^
              (string_f_rec false true (Pred p))
              ^
              " = "
              ^
              (string_f_rec false true f1)
              ^
              "\n"
              ^ 
              padding
              ^
              "IN"
              ^
              " "
              ^
              (string_f_rec false false f2)  

            | Since (intv,f1,f2) ->
              (string_f_rec false true f1)
              ^ 
              " SINCE"
              ^
              (string_of_interval intv)
              ^
              " "
              ^
              (string_f_rec false false f2)

            | Until (intv,f1,f2) ->
              (string_f_rec false true f1)
              ^
              " UNTIL"
              ^
              (string_of_interval intv)
              ^
              " "
              ^
              (string_f_rec false false f2)
            | _ -> failwith "[print_formula] impossible"
          )
          ^
          (if not par && not top then ")" else "")
        ) 
        ^
        (if par && not top then ")" else "")
    )
  and string_r_rec top par h = 
  (match h with
    | Wild -> "."
    | _ ->
        (if par && not top then "(" else "")
        ^ 
        (match h with
          | Test f -> 
            (string_f_rec false false f)
            ^
            "?"
          | Star r -> 
            (string_r_rec false false r)
            ^
            "*"

          | _ -> 
            (if not par && not top then "(" else "")
            ^
            (match h with
              | Concat (r1,r2) -> 
                (string_r_rec false true r1)
                ^
                " "
                ^
                (string_r_rec false false r2)

              | Plus (r1,r2) -> 
                (string_r_rec false true r1)
                ^
                " + "
                ^
                (string_r_rec false false r2)

              | _ -> failwith "[print_formula] impossible"
            )
            ^
            (if not par && not top then ")" else "")
          ) 
          ^
          (if par && not top then ")" else "")
  )
  in
  str ^ (string_f_rec true false g)

(* Fully parenthesize an MFOTL formula *)
let string_of_parenthesized_formula str g =
  let pps = String.split_on_char '\n' str in
  let padding = if pps==[] then "" else String.map (fun s -> ' ') (List.nth pps ((List.length pps)-1)) in
  let rec string_f_rec top par h =
    (match h with
      | Equal (t1,t2) ->
        "(" ^ (Predicate.string_of_term t1) ^ " = " ^ (Predicate.string_of_term t2) ^ ")"
      | Less (t1,t2) ->
        "(" ^ (Predicate.string_of_term t1) ^ " < " ^ (Predicate.string_of_term t2) ^ ")"
      | LessEq (t1,t2) ->
        "(" ^ (Predicate.string_of_term t1) ^ " <= " ^ (Predicate.string_of_term t2) ^ ")"
      | Substring (t1,t2) ->
        "(" ^ (Predicate.string_of_term t1) ^ " SUBSTRING " ^ (Predicate.string_of_term t2) ^ ")"
      | Matches (t1,t2,tl) ->
        "(" ^ (Predicate.string_of_term t1) ^ " MATCHES " ^ (Predicate.string_of_term t2)
        ^
        (if tl = [] then ""
          else Misc.string_of_list_ext " (" ")" ", " string_of_opt_term tl)
        ^ ")"
      | Pred p -> Predicate.string_of_predicate p
      | _ ->
         
        (match h with
        | Neg f ->
          "(" ^
          "NOT " ^ (string_f_rec false false f)
          ^ ")"

        | Exists (vl,f) ->
          "(" ^
          "EXISTS " 
          ^ 
          (Misc.string_of_list_ext "" "" ", " Predicate.string_of_term (List.map (fun v -> Var v) vl) )
          ^
          ". "
          ^
          (string_f_rec false false f)
          ^ ")"

        | ForAll (vl,f) ->
          "(" ^
          "FORALL "
          ^
          (Misc.string_of_list_ext "" "" ", " Predicate.string_of_term (List.map (fun v -> Var v) vl))
          ^
          ". "
          ^
          (string_f_rec false false f)
          ^ ")"

        | Aggreg (rty,y,op,x,glist,f) ->
          "(" ^
          (Predicate.string_of_term (Var y))
          ^
          " <- "
          ^
          (string_of_agg_op op)
          ^
          " "
          ^
          (Predicate.string_of_term (Var x))
          ^
          (if glist <> [] then
              "; "
              ^
              (Misc.string_of_list_ext "" "" "," (fun z -> Predicate.string_of_term (Var z)) glist)
          else "")
          ^
          " "
          ^
          (string_f_rec false false f)
          ^ ")"

        | Prev (intv,f) ->
          "(" ^
          "PREVIOUS"
          ^
          (string_of_interval intv)
          ^
          " "
          ^
          (string_f_rec false false f)
          ^ ")"

        | Next (intv,f) ->
          "(" ^
          "NEXT"
          ^
          (string_of_interval intv)
          ^
          " "
          ^
          (string_f_rec false false f)
          ^ ")"

        | Eventually (intv,f) ->
          "(" ^
          "EVENTUALLY"
          ^
          (string_of_interval intv)
          ^
          " "
          ^
          (string_f_rec false false f)
          ^ ")"

        | Once (intv,f) ->
          "(" ^
          "ONCE"
          ^
          (string_of_interval intv)
          ^
          " "
          ^
          (string_f_rec false false f)
          ^ ")"

        | Always (intv,f) ->
          "(" ^
          "ALWAYS"
          ^
          (string_of_interval intv)
          ^
          " "
          ^
          (string_f_rec false false f)
          ^ ")"

        | PastAlways (intv,f) ->
          "(" ^
          "PAST_ALWAYS"
          ^
          (string_of_interval intv)
          ^
          " "
          ^
          (string_f_rec false false f)
          ^ ")"

        | Frex (intv, r) -> 
          "(" ^
          "|>"
          ^
          (string_of_interval intv)
          ^
          (string_r_rec false false r)
          ^ ")"

        | Prex (intv, r) -> 
          "(" ^
          "<|"
          ^
          (string_of_interval intv)
          ^
          (string_r_rec false false r)
          ^ ")"
          
        | _ ->

          (match h with
            | And (f1,f2) ->
              "(" ^
              (string_f_rec false true f1)
              ^
              " AND " 
              ^
              (string_f_rec false true f2)
              ^ ")"

            | Or (f1,f2) ->
              "(" ^
              (string_f_rec false true f1)
              ^
              " OR "
              ^
              (string_f_rec false false f2)
              ^ ")"

            | Implies (f1,f2) ->
              "(" ^
              (string_f_rec false true f1)
              ^
              " IMPLIES "
              ^
              (string_f_rec false false f2)
              ^ ")"

            | Equiv (f1,f2) ->
              "(" ^
              (string_f_rec false true f1)
              ^
              " EQUIV "
              ^
              (string_f_rec false false f2)
              ^ ")"

              | Let (p,f1,f2) ->
              "("
              ^
              "LET"
              ^
              " "
              ^
              (string_f_rec false true (Pred p))
              ^
              " = "
              ^
              (string_f_rec false true f1)
              ^
              "\n"
              ^
              padding
              ^ 
              "IN"
              ^
              " "
              ^
              (string_f_rec false false f2)
              ^ ")"

            | Since (intv,f1,f2) ->
              "(" ^
              (string_f_rec false true f1)
              ^ 
              " SINCE"
              ^
              (string_of_interval intv)
              ^
              " "
              ^
              (string_f_rec false false f2)
              ^ ")"

            | Until (intv,f1,f2) ->
              "(" ^
              (string_f_rec false true f1)
              ^
              " UNTIL"
              ^
              (string_of_interval intv)
              ^
              " "
              ^
              (string_f_rec false false f2)
              ^ ")"
            | _ -> failwith "[print_formula] impossible"
          )
          
        ) 
    )
    and string_r_rec top par h = 
    (match h with
      | Wild -> "(" ^ "." ^ ")"
      | _ ->
          (match h with
            | Test f -> 
              "(" ^
              (string_f_rec false false f)
              ^
              "?"
              ^ ")"

            | Star r -> 
              "(" ^
              (string_r_rec false false r)
              ^
              "*"
              ^ ")"
  
            | _ -> 
              (match h with
                | Concat (r1,r2) -> 
                  "(" ^
                  (string_r_rec false true r1)
                  ^
                  " "
                  ^
                  (string_r_rec false false r2)
                  ^ ")"
  
                | Plus (r1,r2) -> 
                  "(" ^
                  (string_r_rec false true r1)
                  ^
                  " + "
                  ^
                  (string_r_rec false false r2)
                  ^ ")"
  
                | _ -> failwith "[print_formula] impossible"
              )
        )
    )
    in
  str ^ (string_f_rec true false g)

let print_formula str f = print_string (string_of_formula str f)
let prerr_formula str f = prerr_string (string_of_formula str f)

let printnl_formula str f =
  print_formula str f;
  print_newline()

let prerrnl_formula str f =
  prerr_formula str f;
  prerr_newline()
