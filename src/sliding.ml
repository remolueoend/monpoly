(*
 * This file is part of MONPOLY.
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
open MFOTL

(* This module should be a functor: 'a should be an OrderedType *)

type 'a tree =
  | LNode of 'a
  | INode of ('a * ('a tree) * ('a tree))

type ('a, 'b) node = {l: 'a; r: 'a; res: 'b}
type ('a, 'b) stree =  ('a, 'b option) node tree


let stree_bounds = function
  | LNode a | INode (a,_,_) -> a.l, a.r

let stree_res = function
  | LNode a | INode (a,_,_) ->
    match a.res with
    | Some v -> v
    | None -> failwith "[stree_res] empty node"

let prerr_node f g a =
  match a.res with
  | None -> Printf.eprintf "(%s,%s -> *)" (f a.l) (f a.r)
  | Some v ->
    Printf.eprintf "(%s,%s -> " (f a.l) (f a.r);
    g v;
    prerr_string ")"


let prerr_stree f g str t =
  prerr_endline str;
  let rec print indent t =
    prerr_string indent;
    match t with
    | LNode a ->
      prerr_node f g a;
      prerr_newline ()
    | INode (a,l,r) ->
      prerr_node f g a;
      prerr_newline ();
      let new_indent = " " ^ indent in
      print new_indent l;
      print new_indent r
  in
  print " " t

let prerr_stree_int str t = prerr_stree string_of_int str t

let prerr_list f str seq =
  prerr_string str;
  let rec print = function
    | [] -> ()
    | [a] -> f a
    | h::t -> f h; prerr_string ", "; print t
  in
  prerr_string "[";
  print seq;
  prerr_string "]\n"

let prerr_list_int = prerr_list prerr_int






let discharge_res t =
  match t with
  | LNode a -> LNode {l = a.l; r = a.r; res = None}
  | INode (a, tl, tr) -> INode ({l = a.l; r = a.r; res = None}, tl, tr)

let build_bin_tree op tl tr (lw, rw) =
  let ltl, rtl = stree_bounds tl in
  let ltr, rtr = stree_bounds tr in
  assert (ltl = lw);
  assert (rtr = rw);
  assert (ltl <= rtl);
  assert (ltr <= rtr);
  let new_tl = discharge_res tl in
  INode ({l = lw; r = rw; res = Some (op (stree_res tl) (stree_res tr))}, new_tl, tr)

let combine op tl tr =
  let ltl, _ = stree_bounds tl in
  let _, rtr = stree_bounds tr in
  let new_tl = discharge_res tl in
  INode ({l = ltl; r = rtr; res = Some (op (stree_res tl) (stree_res tr))}, new_tl, tr)


(* returns a list of trees, the head being on the left *)
let rec reusable_subtrees (lw, rw) t =
  let lt, rt = stree_bounds t in
  (* if Misc.debugging Dbg_eval then *)
  (*   Printf.eprintf "[reusable_subtrees] tree: (%s,%s)  window: (%s, %s)\n%!" *)
  (*     (MFOTL.string_of_ts lt) *)
  (*     (MFOTL.string_of_ts rt) *)
  (*     (MFOTL.string_of_ts lw) *)
  (*     (MFOTL.string_of_ts rw); *)
  assert (lt <= lw);
  assert (rt = rw);
  if lt = lw then (* we already have the tree *)
    [t]
  else
    match t with
    | LNode _ -> failwith "[reusable_subtrees] impossible"
    | INode (_, tl, tr) ->
      let ltr, rtr = stree_bounds tr in
      (* Printf.printf "[reusable_subtrees] right tree: (%d,%d)\n" ltr rtr; *)
      assert (rtr = rw);
      if ltr <= lw then (* same situation as when this function was called: retry *)
        reusable_subtrees (lw, rw) tr
      else
        let _, rtl = stree_bounds tl in
        tr :: (reusable_subtrees (lw, rtl) tl)


let build_rl_tree_from_seq op seq =
  let rec build tr = function
    | [] -> tr
    | (i, v) :: rest ->
      let tl = LNode {l = i; r = i; res = Some v} in
      let t = combine op tl tr in
      build t rest
  in
  assert (seq <> []);
  let i, v = List.hd seq in
  let t0 = LNode {l = i; r = i; res = Some v} in
  build t0 (List.tl seq)


(* let build_rl_tree_from_seq op seq =  *)
(*   let build (i, v) tr =  *)
(*     combine op (LNode {l = i; r = i; res = Some v}) tr *)
(*   in     *)
(*   let i, v = List.hd seq in *)
(*   let t0 = LNode {l = i; r = i; res = Some v} in *)
(*   List.fold_right build (List.tl seq) t0 *)


let build_rl_tree op t_list =
  let rec build = function
    | [] -> failwith "[build_rl_tree] error"
    | [t] -> t
    | tr :: tl :: rest ->
      let t = combine op tl tr in
      if rest = [] then
        t
      else
        build (t :: rest)
  in
  build t_list

(* [t] is the tree that stores the intermediate results
   [w] is the window
   returns number of operations performed and the new tree *)
let slide f op seq (lw, rw) t =
  let lt, rt = stree_bounds t in
  if Misc.debugging Dbg_eval then
    Printf.eprintf "[slide] (lt,rt) = (%s,%s) (lw,rw) = (%s,%s)\n%!" (f lt) (f rt) (f lw) (f rw);
  assert(rt <= rw);
  if rt < lw then (* [t] is useless: discard it *)
    build_rl_tree_from_seq op seq
  else
    let t_list  = reusable_subtrees (lw, rt) t in
    if rt < rw then
      let tr = build_rl_tree_from_seq op seq in
      (* print_stree_int "[slide] tr: " tr; *)
      build_rl_tree op (tr :: t_list)
    else (* rt = rw *)
      build_rl_tree op t_list





