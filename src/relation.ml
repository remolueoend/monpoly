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
open Tuple
open Predicate
open MFOTL


module Tuple_set = Set.Make (
  struct type t = tuple
   let compare = Tuple.compare
  end)

include Tuple_set

type relation = Tuple_set.t


(*** printing functions ***)


let print_rel str rel =
  print_string str;
  let rel' = Tuple_set.elements rel in
  Misc.print_list Tuple.print_tuple rel'


let print_rel4 str rel =
  print_string str;
  let rel' = Tuple_set.elements rel in
  Misc.print_list4 Tuple.print_tuple rel'


let print_reln str rel =
  print_rel str rel;
  print_newline()


let print_bigrel rel =
  let rel' = Tuple_set.elements rel in
  Misc.print_list3 Tuple.print_tuple rel'

let print_orel = function
  | None -> print_string "N"
  | Some rel -> print_rel "S" rel




(********************************)


let make_relation list =
  let rec make acc = function
  | [] -> acc
  | h::t -> make (Tuple_set.add h acc) t
  in make Tuple_set.empty list


let map f rel =
  let res = ref (Tuple_set.empty) in
    Tuple_set.iter
      (fun t ->
   res := Tuple_set.add (f t) !res
      )
      rel


let map f rel =
  Tuple_set.fold (fun t rel' -> Tuple_set.add (f t) rel') rel Tuple_set.empty






(********************************)

let is_empty rel =
  Tuple_set.is_empty rel


(*******************************************************************)
(*** rigid predicates ***)

let trel = make_relation [Tuple.make_tuple []]
let frel = Tuple_set.empty

let eval_equal t1 t2 =
  match t1,t2 with
  | Var x, Cst c
  | Cst c, Var x -> make_relation [Tuple.make_tuple [c]]
  | Cst c, Cst c' when c = c' -> trel
  | Cst c, Cst c' -> frel
  | _ -> failwith "[Relation.eval_equal] (x=y)"

let eval_not_equal t1 t2 =
  match t1,t2 with
  | Var x, Var y when x = y -> frel
  | Cst c, Cst c' when c = c' -> frel
  | Cst c, Cst c' -> trel
  | _ -> failwith "[Relation.eval_not_equal] (x <> y)"



(**********************************************************************)


(** [matches] gives the columns which should match in the two
    relations in form of a list of tuples [(pos2,pos1)]: column [pos2] in
    [rel2] should match column [pos1] in [rel1] *)
let natural_join matches1 matches2 rel1 rel2 =
  let joinrel = ref Tuple_set.empty in
  let process_rel_tuple join_fun matches rel2 t1 =
    (* For each tuple in [rel1] we compute the columns (i.e. positions)
       in rel2 for which there should be matching values and the values
       tuples in rel2 should have at these columns.

       For instance, for [matches] = [(0,1);(1,2);(3,0)] and t1 =
       [6;7;9] we obtain [(0,7);(1,9);(3,6)]. That is, from [rel2] we
       will select all tuples which have 7 on position 0, 9 on
       position 1, and 6 on position 3.  *)
    let pv = List.map
      (fun (pos2, pos1) -> (pos2, Tuple.get_at_pos t1 pos1))
      matches
    in
      Tuple_set.iter
  (fun t2 ->
     try
       let t = join_fun pv t1 t2 in
         joinrel := Tuple_set.add t !joinrel
     with
         Not_joinable -> ()
  )
  rel2
  in
  if Tuple_set.cardinal rel1 < Tuple_set.cardinal rel2 then
    let join_fun = Tuple.join in
    Tuple_set.iter (process_rel_tuple join_fun matches1 rel2) rel1
  else
    begin
      let pos2 = List.map fst matches1 in
      let join_fun = Tuple.join_rev pos2 in
      Tuple_set.iter (process_rel_tuple join_fun matches2 rel1) rel2
    end;
  !joinrel


let in_t2_not_in_t1 t2 matches =
  let len  = List.length (Tuple.get_constants t2) in
  (* these are the positions in t2 which also appear in t1 *)
  let t2_pos = List.map snd matches in
  let rec get_aux pos =
    if pos = len then []
    else if not (List.mem pos t2_pos) then
      let v = Tuple.get_at_pos t2 pos in
      v :: (get_aux (pos+1))
    else
      get_aux (pos+1)
  in
  get_aux 0




(* Misc.subset attr1 attr2 *)
(* Note that free_vars in (f1 AND f2) are ordered according to f1 not
   to f2!  Thus, for instance, for p(x,y) AND q(z,y,x) the fields
   should be ordered by (x,y,z).
*)
let natural_join_sc1 matches rel1 rel2 =
  let joinrel = ref Tuple_set.empty in
  Tuple_set.iter (fun t2 ->
    let t1_list =
      List.map
  (fun (pos1, pos2) ->
    (* x is at pos1 in t1 and at pos2 in t2 *)
    Tuple.get_at_pos t2 pos2)
  matches
    in
    let t1 = Tuple.make_tuple t1_list in
    if Tuple_set.mem t1 rel1 then

      let t2_list = in_t2_not_in_t1 t2 matches in
      let t2' = Tuple.make_tuple (t1_list @ t2_list) in
      joinrel := Tuple_set.add t2' !joinrel
  ) rel2;
  !joinrel

(* Misc.subset attr2 attr1 *)
let natural_join_sc2 matches rel1 rel2 =
  let joinrel = ref Tuple_set.empty in
  Tuple_set.iter (fun t1 ->
    let t2 = Tuple.make_tuple (
      List.map
  (* x is at pos2 in t2 and at pos1 in t1 *)
  (fun (pos2, pos1) -> Tuple.get_at_pos t1 pos1)
  matches)
    in
    if Tuple_set.mem t2 rel2 then
      joinrel := Tuple_set.add t1 !joinrel
  ) rel1;
  !joinrel



let cross_product rel1 rel2 =
  natural_join [] [] rel1 rel2



let reorder new_pos rel =
  let new_rel = ref Tuple_set.empty in
  Tuple_set.iter (fun t ->
    let t' = Tuple.projections new_pos t in
    new_rel := Tuple_set.add t' !new_rel
  ) rel;
  !new_rel

(* not set difference, but the diff operator as defined in Abiteboul, page 89 *)
let minus posl rel1 rel2 =
  Tuple_set.filter
    (fun t ->
      let t' = (Tuple.projections posl t) in
      not (Tuple_set.mem t' rel2)
    )
    rel1




(* given the "predicate formula" [p] and a relation [rel] ("having the
   same signature" as [p]), obtain the relation containing those
   tuples of [rel] which satisfy [p] *)
let selectp p rel =
  let res = ref Tuple_set.empty in
    Tuple_set.iter
      (fun t ->
   let b,t' = Tuple.satisfiesp p t in
   if b then
     res := add t' !res
      ) rel;
    !res




(* Note: [proj] \cup [sel] = all positions and [proj] \cap [sel] = \emptyset
   special case when sel=[]? yes, then selectp is the identity function
   special case when proj=[]? no

   The approach below seems useless, because we have to iterate anyhow
   through all tuples and transform them individually (unless sel=[]).
   And then positions do not help us, see function [Tuple.satisfiesp].
*)
let no_constraints tlist =
  let rec iter vars = function
    | [] -> true
    | (Var x) :: tlist ->
      if List.mem x vars then
        false (* there are constraints *)
      else (* new variable, we record its position *)
        iter (x :: vars) tlist

    | _ :: tlist -> false  (* there are constraints *)
  in
  iter [] tlist


(* Given a predicate [f]=[p(t_1,\dots,t_n)], [eval_pred] returns a
   function from relations to relations; this function transforms
   [|p(x_1,\dots,x_n)|] into [|p(t_1,\dots,t_n)|]
*)
let eval_pred p =
  let tlist = Predicate.get_args p in
  if no_constraints tlist then
    fun rel -> rel
  else
    fun rel ->
      let res = ref Tuple_set.empty in
      Tuple_set.iter
        (fun t ->
           let b, t' = Tuple.satisfiesp tlist t in
           if b then
             res := add t' !res;
        ) rel;
      !res


(* the columns in [posl] are eliminated *)
let project_away posl rel =
  map (Tuple.project_away posl) rel
