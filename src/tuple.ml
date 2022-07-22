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
open Predicate
open MFOTL

type tuple = cst list


(* String interning *)

module StringHash: (Hashtbl.HashedType with type t = string) = struct
  type t = string
  let equal = (=)
  let hash = Hashtbl.hash
end

module StringCache = Weak.Make(StringHash)

let string_cache = StringCache.create 256

let cached x =
  if !Misc.str_cache then
    try StringCache.find string_cache x
    with Not_found -> (StringCache.add string_cache x; x)
  else x


(* compare two tuples *)
let compare t1 t2 = compare t1 t2
  (* this is Stdlib.compare: [2]>[1;4] (as 2>1), [2]<[3;4] (as 2<3),
     and [2]<[2;4] (as []<l for any non-empty l) *)

(*** operations on tuples ***)

let make_tuple x = x

exception Type_error of string

let make_tuple2 sl tl =
  let pos = ref 0 in
  List.map2
    (fun s (_, t) ->
       incr pos;
       match t with
       | TInt ->
         (try Int (Z.of_string s)
          with Invalid_argument _ ->
            raise (Type_error ("Expected type int for field number "
                               ^ (string_of_int !pos))))
       | TStr -> Str (cached s)
       | TFloat ->
         (try Float (float_of_string s)
          with Failure _ ->
            raise (Type_error ("Expected type float for field number "
                               ^ (string_of_int !pos))))
       | TRegexp ->
         let s = (
           let len = String.length s in
           if (len < 3 || s.[0] <> 'r' || s.[1] <> '\"' || s.[len-1] <> '\"') then
             raise (Type_error ("Invalid regexp for field number " ^ (string_of_int !pos)))
           else String.sub s 2 (len-3)
         ) in 
         (try Regexp (s, Str.regexp s)
          with _ ->
            raise (Type_error ("Regexp compilation failed for field number "
                               ^ (string_of_int !pos))))
    )
    sl tl

let get_constants tuple = tuple

let get_at_pos = List.nth

let add_first tuple v = v :: tuple
let add_last tuple v = tuple @ [v]

let rec insert pos t v =
  if pos <= 0 then v :: t
  else
    match t with
    | [] -> raise Not_found
    | x :: t' -> x :: insert (pos-1) t' v

let duplicate_pos pos tuple =
  let v = get_at_pos tuple pos in
  add_last tuple v

let project_away = Misc.remove_positions
let projections = Misc.get_positions


(*** OLD ***)
(* let satisfiesp p t =  *)
(*   (\* we use same idea as Samuel: assign values to variables *\) *)
(*   let rec satisf assign t a =  *)
(*     match t,a with *)
(*       | [],[] ->  *)
(*   true, List.rev (snd (List.split assign)) *)
(*       | ht::tt,ah::at ->  *)
(*   (match ah with *)
(*     | Var x -> *)
(*       (try *)
(*          let v = List.assoc x assign in *)
(*          if v = ht then *)
(*      satisf assign tt at *)
(*          else *)
(*      (false,[]) *)
(*        with Not_found ->  *)
(*          satisf ((x,ht)::assign) tt at) *)
(*     | Cst v ->  *)
(*       if v = ht then *)
(*         satisf assign tt at  *)
(*       else *)
(*         (false,[]) *)
(*   ) *)
(*       | _ -> failwith "[Tuple.satisfiesp] The arity of [p] and the length of [t] differ." *)
(*   in  *)
(*   satisf [] t (Predicate.get_args p) *)


let rec check_constr assign = function
  | [] -> true
  | (c, sterm) :: rest ->
    (c = Predicate.eval_term assign sterm) && (check_constr assign rest)


(* We assume that terms are simplified: the only ground terms are *)
(* constants. TODO: do we really? Anyhow, terms should be simplified. *)
let satisfiesp arg_list tuple =
  let rec satisf assign res crt_tuple args constr =
    match crt_tuple, args with
    | [], [] ->
      if check_constr assign constr then
        true, List.rev res
      else
        false, []

    | c :: rest, term :: args' ->
      (match term with
       | Var x ->
         (try
            let c' = List.assoc x assign in
            if c = c' then
              satisf assign res rest args' constr
            else
              false, []
          with Not_found ->
            satisf ((x, c) :: assign) (c :: res) rest args' constr
         )

       | Cst c' ->
         if c = c' then
           satisf assign res rest args' constr
         else
           false, []

       | _ -> satisf assign res rest args' ((c, term) :: constr)
      )
    | _ -> failwith "[Tuple.satisfiesp] The arity of [p] and the length of [t] differ."
  in
  satisf [] [] tuple arg_list []


let satisfiesf1 f pos tuple =
  f (get_at_pos tuple pos)


let satisfiesf2 f pos1 pos2 tuple =
  f (get_at_pos tuple pos1) (get_at_pos tuple pos2)



let eval_term_on_tuple tuple =
  Predicate.eval_eterm (get_at_pos tuple)

let satisfiesf2 cond term1 term2 tuple =
  cond (eval_term_on_tuple tuple term1) (eval_term_on_tuple tuple term2)


let rec get_pos_term attr = function
  | Var x -> Var (Misc.get_pos x attr)
  | Cst c -> Cst c
  | I2f t -> I2f (get_pos_term attr t)
  | F2i t -> F2i (get_pos_term attr t)
  | I2s t -> I2s (get_pos_term attr t)
  | S2i t -> S2i (get_pos_term attr t)
  | F2s t -> F2s (get_pos_term attr t)
  | S2f t -> S2f (get_pos_term attr t)
  | Month t -> Month (get_pos_term attr t)
  | DayOfMonth t -> DayOfMonth (get_pos_term attr t)
  | Year t -> Year (get_pos_term attr t)
  | FormatDate t -> FormatDate (get_pos_term attr t)
  | R2s t -> R2s (get_pos_term attr t)
  | S2r t -> S2r (get_pos_term attr t)
  | UMinus t -> UMinus (get_pos_term attr t)
  | Plus (t1, t2) -> Plus (get_pos_term attr t1, get_pos_term attr t2)
  | Minus (t1, t2) -> Minus (get_pos_term attr t1, get_pos_term attr t2)
  | Mult (t1, t2) -> Mult (get_pos_term attr t1, get_pos_term attr t2)
  | Div (t1, t2) -> Div (get_pos_term attr t1, get_pos_term attr t2)
  | Mod (t1, t2) -> Mod (get_pos_term attr t1, get_pos_term attr t2)


let substring cs1 cs2 =
  let s1, s2 = match cs1, cs2 with 
    | Str s1, Str s2 -> s1, s2 
    | _ -> failwith "[Tuple.substring] internal error, expected strings"
  in
  let l1 = String.length s1
  and l2 = String.length s2 in
  let rec aux i =
    i >= 0 && (
      let sub = String.sub s2 i l1 in
      String.equal sub s1 || aux (i - 1)
    )
  in
  l1 <= l2 && aux (l2 - l1)

type 'a group_op = SkipGroup | GetGroup | EqGroupInt of int | EqGroupExt of 'a

let map_group_op f = function
  | SkipGroup -> SkipGroup
  | GetGroup -> GetGroup
  | EqGroupInt i -> EqGroupInt i
  | EqGroupExt x -> EqGroupExt (f x)

let compile_group_ops attr vl =
  let rec go extr out = function
    | [] -> List.rev out
    | None::vl -> go extr (SkipGroup::out) vl
    | (Some (Var v))::vl when List.mem v extr ->
      let j = Misc.get_pos v extr in
      go extr ((EqGroupInt j)::out) vl
    | (Some (Var v))::vl when not (List.mem v attr) ->
      go (v::extr) (GetGroup::out) vl
    | (Some t)::vl ->
      let t' = get_pos_term attr t in
      go extr ((EqGroupExt t')::out) vl
  in
  go [] [] vl

let matches cs cr gl =
  let s, r = match cs, cr with
    | Str s, Regexp (_, r) -> s, r
    | _ -> failwith "[Tuple.matches] internal error"
  in try
    let _ = Str.search_forward r s 0 in
    let rec go i out = function
      | [] -> Some (List.rev_map (fun x -> Str x) out)
      | SkipGroup :: l -> go (i+1) out l
      | GetGroup :: l ->
        let g = Str.matched_group i s in
        go (i+1) (g::out) l
      | EqGroupInt j :: l ->
        let g = Str.matched_group i s in
        if g = List.nth out j then go (i+1) out l else None
      | EqGroupExt (Str g') :: l ->
        let g = Str.matched_group i s in
        if g = g' then go (i+1) out l else None
      | _ -> failwith "[Tuple.matches] internal error"
    in
    go 1 [] gl (* first group has index 1 *)
  (* Note: matched_group may raise Not_found too, namely if the match does not
     involve the group expression at all. For now, the semantics is as follows:
     wildcards (_ in formula syntax, SkipGroup here) always match, even if the
     corresponding group does not exist, whereas variables require that the
     group exist for the formula to be satisfied. *)
  with Not_found -> None

let rec get_filter attr formula =
  match formula with
  | Neg f ->
    let filter = get_filter attr f in
    (fun t -> not (filter t))
  | Matches (t1, t2, tl) ->
    let pos_t1 = get_pos_term attr t1 in
    let pos_t2 = get_pos_term attr t2 in
    let ops = compile_group_ops attr tl in
    (fun tuple ->
      let cs = eval_term_on_tuple tuple pos_t1 in
      let cr = eval_term_on_tuple tuple pos_t2 in
      let gl = List.map (map_group_op (eval_term_on_tuple tuple)) ops in
      Option.is_some (matches cs cr gl))
  | _ ->
    let pos_t1, pos_t2 =
      match formula with
      | Equal (t1, t2)
      | Less (t1, t2)
      | LessEq (t1, t2)
      | Substring (t1, t2)
        -> get_pos_term attr t1, get_pos_term attr t2
      | _ -> failwith "[Tuple.get_filter, pos] internal error"
    in
    let cond =
      match formula with
      | Equal (t1, t2) -> (=)
      | Less (t1, t2) -> (<)
      | LessEq (t1, t2) -> (<=)
      | Substring (t1, t2) -> substring
      | _ -> failwith "[Tuple.get_filter, cond] internal error"
    in
    satisfiesf2 cond pos_t1 pos_t2

(* return a transformation function on tuples *)
let get_tf attr = function
  | Equal (t1, t2) ->
    let f t =
      let pos_term = get_pos_term attr t in
      (fun tuple ->
         let c = eval_term_on_tuple tuple pos_term in
         Some (add_last tuple c))
    in
    (match t1, t2 with
     | Var x, t when not (List.mem x attr) -> f t
     | t, Var x when not (List.mem x attr) -> f t
     | _ -> failwith "[Tuple.get_processing_func, equal] internal error"
    )
  | Matches (t1, t2, tl) ->
    let pos_t1 = get_pos_term attr t1 in
    let pos_t2 = get_pos_term attr t2 in
    let ops = compile_group_ops attr tl in
    (fun tuple ->
      let cs = eval_term_on_tuple tuple pos_t1 in
      let cr = eval_term_on_tuple tuple pos_t2 in
      let gl = List.map (map_group_op (eval_term_on_tuple tuple)) ops in
      Option.map (fun l -> tuple @ l) (matches cs cr gl))
  | _ -> failwith "[Tuple.get_processing_func, formula] internal error"



exception Not_joinable


let join posval t1 t2 =
  let rec join' crtpos pv t =
    match pv,t with
    | (hp,hv)::tpv, ht::tt ->
      if hp = crtpos then
        if hv = ht then
          join' (crtpos+1) tpv tt
        else
          raise Not_joinable
      else
        ht::(join' (crtpos+1) pv tt)
    | [],_ -> t
    | _,[] -> failwith "[Tuple.join] bad posval list"
  in
  t1 @ (join' 0 posval t2)

(* Does not check equality of shared positions! *)
let join_unchecked matches t1 t2 =
  let rec sel crtpos pp t =
    match pp, t with
    | (pos2, _)::ppt, c::tt ->
        if pos2 = crtpos then
          sel (crtpos+1) ppt tt
        else
          c :: sel (crtpos+1) pp tt
    | [], _ -> t
    | _, [] -> failwith "[Tuple.join_unchecked] bad matches list"
  in
  t1 @ sel 0 matches t2

(* the result should be the same as [join t1 t2] *)
(* [join'] just checks that values in [t1] are correspct with respect
   to [posval], but does not select elements, while [join''] does not
   check anything, just selects positions that don't appear in [pos] *)
let join_rev pos2 posval t2 t1 =
  let rec check crtpos pv t =
    match pv,t with
    | (hp, hv)::tpv, ht::tt ->
      if hp = crtpos then
        if hv = ht then
          check (crtpos+1) tpv tt
        else
          raise Not_joinable
      else
        check (crtpos+1) pv tt
    | [], _ -> ()
    | _, [] -> failwith "[Tuple.join] bad posval list"
  in
  let rec sel crtpos pl t =
    match pl,t with
    | hp::tpv, ht::tt ->
      if hp = crtpos then
        sel (crtpos+1) tpv tt
      else
        ht :: (sel (crtpos+1) pl tt)
    | [], _ -> t
    | _, [] -> failwith "[Tuple.join_rev] bad pos list"
  in
  check 0 posval t1;
  t1 @ (sel 0 pos2 t2)



(** printing functions **)

let string_of_tuple = Misc.string_of_list string_of_cst
let print_tuple = Misc.print_list print_cst
let prerr_tuple = Misc.prerr_list prerr_cst
