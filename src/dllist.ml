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

(* The implementation of some of the functions in this file are based
 * on queue.ml from OCaml's standard library, which had the following
 * copyright:
 *)
(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)


type 'a cell = {
  data: 'a;
  mutable prev: 'a cell;
  mutable next: 'a cell
}

type 'a dllist = {
  mutable length: int;
  mutable tail: 'a cell
}

exception Empty_dllist

let void = Obj.magic None

let empty () = {
  length = 0;
  tail = void
}

let clear l =
  l.length <- 0;
  l.tail <- void

let is_empty l =
  l.length = 0

let length l =
  l.length


let get_first l =
  if l.length = 0 then
    raise Empty_dllist
  else
    l.tail.next.data

let get_last l =
  if l.length = 0 then
    raise Empty_dllist
  else
    l.tail.data

let get_first_cell l =
  if l.length = 0 then
    raise Empty_dllist
  else
    l.tail.next

let get_last_cell l =
  if l.length = 0 then
    raise Empty_dllist
  else
    l.tail



let is_first l cell =
  if l.length = 0 then
    raise Empty_dllist;
  cell == l.tail.next

let is_last l cell =
  if l.length = 0 then
    raise Empty_dllist;
  cell == l.tail


exception End_of_dllist

let get_next l cell =
  if is_last l cell then
    raise End_of_dllist;
  cell.next

let get_prev l cell =
  if is_first l cell then
    raise End_of_dllist;
  cell.prev

let get_data cell =
  cell.data



let pop_first l =
  if l.length = 0 then raise Empty_dllist;
  l.length <- l.length - 1;
  let tail = l.tail in
  let head = tail.next in
  if head == tail then
    l.tail <- void
  else
    (tail.next <- head.next;
     head.next.prev <- tail);
  head.data


let pop_last l =
  if l.length = 0 then raise Empty_dllist;
  l.length <- l.length - 1;
  let tail = l.tail in
  let head = tail.next in
  let data = tail.data in
  if head == tail then
    l.tail <- void
  else
    (head.prev <- tail.prev;
     tail.prev.next <- head;
     l.tail <- tail.prev);
  data


let add_first x l =
  l.length <- l.length + 1;
  if l.length = 1 then
    let rec cell = {
      data = x;
      next = cell;
      prev = cell
    } in
    l.tail <- cell
  else
    let tail = l.tail in
    let head = tail.next in
    let cell =
      {data = x;
       next = head;
       prev = tail}
    in
    (tail.next <- cell;
     head.prev <- cell)



let add_last x l =
  l.length <- l.length + 1;
  if l.length = 1 then
    let rec cell =
      {data = x;
       next = cell;
       prev = cell}
    in
    l.tail <- cell
  else
    let tail = l.tail in
    let head = tail.next in
    let cell =
      {data = x;
       next = head;
       prev = tail}
    in
    (tail.next <- cell;
     head.prev <- cell;
     l.tail <- cell)

(* "special" function:
   it returns a new cell which points to the first element
*)
let new_cell x l =
  let first = get_first_cell l in
  let rec cell =
    {data = x;
     next = first;
     prev = cell
    }
  in cell

let singleton x =
  let l  = empty () in
  add_last x l;
  l


let iter f l =
  if l.length > 0 then
    let tail = l.tail in
    let rec iter cell =
      f cell.data;
      if cell != tail then
        iter cell.next
    in
    iter tail.next


let get_index cell l =
  if l.length > 0 then
    let i = ref 0 in
    let tail = l.tail in
    let rec iter crt =
      if cell != crt then
        begin
          incr i;
          if crt != tail then
            iter crt.next
        end
    in
    iter tail.next;
    !i
  else
    failwith "[Dllist.get_index] empty list"

let get_cell_at_index i l =
  if l.length > 0 then
    let j = ref 0 in
    let tail = l.tail in
    let rec iter crt =
      if i <> !j then
        begin
          incr j;
          if crt != tail then
            iter crt.next
          else
            crt
        end
      else
        crt
    in
    let cell = iter tail.next in
    if !j = l.length then
      failwith "[Dllist.get_cell_at_index] index out of bounds"
    else
      cell
  else
    raise Empty_dllist


let iterrev_cond_delete iter_cond f del_cond l =
  if l.length > 0 then
    let tail = l.tail in
    let head = tail.next in
    let rec iter cell =
      if iter_cond cell.data then
        begin
          f cell.data;

          if del_cond cell.data then
            begin
              l.length <- l.length - 1;
              if l.length = 0 then
                l.tail <- void
              else
                begin
                  cell.next.prev <- cell.prev;
                  cell.prev.next <- cell.next
                end
            end;

          if cell != head then
            iter cell.prev
        end
    in
    iter tail

let to_array list =
  let len = list.length in
  if len = 0 then
    [||]
  else
    let a = Array.make len (get_data (get_first_cell list)) in
    let i = ref 0 in
    iter (fun d ->
        a.(!i) <- d;
        incr i;
      ) list;
    a

let from_array a =
  let l = empty () in
  for i = 1 to Array.length a do
    add_last a.(i-1) l
  done;
  l


(*
  let print_dllist f l =
  iter f l;
  print_newline()

  let list_print = print_dllist (fun x -> print_int x; print_string " ")

  let create_dlist n =
  let l = empty () in
  let rec create i =
  if i>n then
  ()
  else
  begin
  if i mod 2 = 0 then
  add_first i l
  else
  add_last i l;
  create (i+1)
  end
  in
  create 0;
  list_print l;
(*
  for i = 0 to n/2 do
  ignore(pop_first l)
  done;
  list_print l;
  for i = n/2 + 1 to n do
  ignore(pop_last l)
  done;
  list_print l
*)
     l

let _ =
  let l = create_dlist 20 in

  let first = get_first_cell l in
  let curr = ref first in
    for i = 1 to 50
    do
      Printf.printf "%d \n%!" (get_data !curr);
      curr := get_next !curr;
      if not (!curr == first) then
  print_string "different\n"
      else
  print_string "equal"
    done
*)
