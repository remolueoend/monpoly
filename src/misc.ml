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

(* Stolen from ocaml-extlib *)
exception Invalid_string

let find_from str pos sub =
  let sublen = String.length sub in
  if sublen = 0 then
    0
  else
    let found = ref 0 in
    let len = String.length str in
    try
      for i = pos to len - sublen do
        let j = ref 0 in
        while String.unsafe_get str (i + !j) = String.unsafe_get sub !j do
          incr j;
          if !j = sublen then begin found := i; raise Exit; end;
        done;
      done;
      raise Invalid_string
    with
      Exit -> !found

let nsplit str sep =
  if str = "" then []
  else if sep = "" then raise Invalid_string
  else
    let rec loop acc pos =
      if pos > String.length str then
        List.rev acc
      else
        let i = try find_from str pos sep with Invalid_string -> String.length str in
        loop (String.sub str pos (i - pos) :: acc) (i + String.length sep)
    in
    loop [] 0
(* End Theft *)


let usr2 = ref false
let alrm = ref false

let verbose = ref false
let checkf = ref false

let verified = ref false

let new_last_ts = ref true

let ignore_parse_errors = ref false
let stop_at_out_of_order_ts = ref false
let stop_at_first_viol = ref false

let str_cache = ref false


type dbg =
  | Dbg_all (* this is enabled when at least one of the below is enabled *)
  | Dbg_eval
  | Dbg_monitorable
  | Dbg_log
  | Dbg_perf
  | Dbg_filter
  | Dbg_parsing
  | Dbg_typing


let debugl = ref []

let split_debug debugstr =
  let debuglist = nsplit debugstr "," in
  debugl :=
    List.map (fun str -> match str with
        | "eval" -> Dbg_eval
        | "perf" -> Dbg_perf
        | "log" -> Dbg_log
        | "parsing" -> Dbg_parsing
        | "typing" -> Dbg_typing
        | "monitorable" -> Dbg_monitorable
        | "filter" -> Dbg_filter
        | _ -> failwith "[Misc.split_debug] unrecognized debug option"
      ) debuglist

let debugging dbg =
  (dbg = Dbg_all && !debugl <> [])
  || List.mem dbg !debugl


(*** Miscellaneous functions (all functions involve lists) ***)



let map_interval f m n =
  let rec gen' n l =
    if n<m then
      l
    else
      gen' (n-1) ((f n)::l)
  in
  gen' n []

(* assumption: [len] is the length of the list *)
let median l len f =
  let m = if len mod 2 = 0 then (len / 2) - 1 else len / 2 in
  let rec median_aux l n =
    match l with
    | [] -> failwith "[Misc.median] internal error"
    | h::l ->
      if m = n then
        if len mod 2 = 0 then
          f h (List.hd l)
        else
          f h h
      else median_aux l (n+1)
  in
  median_aux l 0

(* eliminate element [x] from list [l] *)
let rec elim_elem x = function
  | [] -> failwith "[Misc.elim_elem] element not found"
  | h :: t -> if h = x then t else h :: (elim_elem x t)


(* add element [x] in the sorted list [l] *)
let rec add_in_sorted x = function
  | [] -> [x]
  | h :: t ->
    if Stdlib.compare x h < 0
    then x :: h :: t
    else h :: (add_in_sorted x t)


(** Pretty-printing functions *)

let rec print_spaces l =
  if l<=0 then
    ()
  else
    begin
      print_string " ";
      print_spaces (l-1)
    end


let string_of_list_ext lm rm del f = function
  | [] -> lm ^ rm
  | [a] -> lm ^ (f a) ^ rm
  | l ->
    let rec printaux = function
      | [a] -> (f a) ^ rm
      | h::t -> (f h) ^ del ^ (printaux t)
      | _ -> failwith "[string_of_list_ext] impossible"
    in
    lm ^ (printaux l)

let string_of_list f l = string_of_list_ext "(" ")" ","  f l
let string_of_list2 f l = string_of_list_ext "| " " |" " | " f l
let string_of_list3 f l = string_of_list_ext "" "\n" "\n" f l
let string_of_list4 f l = string_of_list_ext "" "" " "  f l


let output_list_ext ch lm rm del f = function
  | [] -> output_string ch (lm^rm)
  | [a] -> output_string ch lm; f ch a; output_string ch rm
  | l ->
    output_string ch lm;
    let rec outputaux = function
      | [a] -> f ch a; output_string ch rm
      | h::t ->
        f ch h;
        output_string ch del;
        outputaux t
      | _ ->
        failwith "[outputaux] impossible"
    in
    outputaux l

let print_list_ext lm rm del f =
  let g _ x = f x in
  output_list_ext stdout lm rm del g

let output_list ch f l = output_list_ext ch "(" ")" ","  f l
let output_list4 ch f l = output_list_ext ch "" "" " "  f l

let print_list f l = print_list_ext "(" ")" ","  f l
let print_list2 f l = print_list_ext "| " " |" " | " f l
let print_list3 f l = print_list_ext "" "\n" "\n" f l
let print_list4 f l = print_list_ext "" "" " "  f l

let prerr_list f l = output_list stderr (fun _ -> f) l

let printnl_list str f l =
  print_string str;
  print_list f l;
  print_newline()

let prerrnl_list str f l =
  prerr_string str;
  prerr_list f l;
  prerr_newline()


let print_queue print_el q =
  let lq = ref [] in
  Queue.iter (fun el -> lq := el::!lq) q;
  lq := List.rev !lq;
  print_list print_el !lq

let prerr_queue prerr_el q =
  let lq = ref [] in
  Queue.iter (fun el -> lq := el::!lq) q;
  lq := List.rev !lq;
  prerr_list prerr_el !lq

let print_mqueue print_el q =
  let lq = ref [] in
  Mqueue.iter (fun el -> lq := el::!lq) q;
  lq := List.rev !lq;
  print_list print_el !lq

let prerr_mqueue prerr_el q =
  let lq = ref [] in
  Mqueue.iter (fun el -> lq := el::!lq) q;
  lq := List.rev !lq;
  prerr_list prerr_el !lq



(** Functions implementing operations which are similar with set
    operations. Note that if one of the input lists (usually the first
    one) does not represent a set, the output list may not represent
    neither. *)


(* [append2 l1 l2] appends l2 to l1 such that no new elements are added *)
(* the order of elements is preserved *)
(*
let append2 l1 l2 =
  let rec different acc = function
    | h::t ->
  if List.mem h l1 then
    different acc t
  else
    different (h::acc) t
    | [] -> acc
  in
    l1 @ (List.rev (different [] l2))
*)

let union l1 l2 = l1 @ (List.filter (fun x -> not (List.mem x l1)) l2)

let diff l1 l2 = List.filter (fun x -> not (List.mem x l2)) l1

let rec subset l1 l2 =
  match l1 with
  | h::t -> (List.mem h l2) && (subset t l2)
  | [] -> true

let rec inter l1 = function
  | [] -> []
  | h::t ->
    if List.mem h l1 then
      h::(inter l1 t)
    else
      inter l1 t


let rec contains_duplicates = function
  | [] -> false
  | h::t -> (List.mem h t) || (contains_duplicates t)


let remove_duplicates l =
  let rec rm acc = function
    | [] -> List.rev acc
    | h::t ->
      if List.mem h t then
        rm acc t
      else
        rm (h::acc) t
  in
  rm [] l




let conjunction l = List.fold_left (&&) true l




(* split a list in two at certain position *)
(* split_at_n 1 [a;b;c] = [a],[b;c] *)
let split_at_n n l =
  let rec split first n = function
    | [] ->
      if n=0 then
        first,[]
      else
        failwith "[split_after_n] n is bigger than the length of the list"
    | (h::t) as l ->
      if n=0 then
        first,l
      else
        split (first@[h]) (n-1) t
  in
  split [] n l


(* from a list of lengths and a list produce a list of lists, each
   inner list having the right length *)
(* example: sublists [0;3;1] [a;b;c;d] = [[];[a;b;c];[d]] *)
let rec sublists list = function
  | len::t ->
    let sublist,rest = split_at_n len list in
    sublist::(sublists rest t)
  | [] -> []





(* from l@[j] obtain j *)
let get_last l =
  List.hd (List.rev l)

(* from l@[j] obtain (l,j) *)
let split_at_last l =
  let revl = List.rev l in
    List.rev (List.tl revl), List.hd revl

(* from l@[j;j'] obtain (l,j,j') *)
let split_at_lastbutone l =
  let lrev = List.rev l in
  let llrev = List.tl lrev in
  List.rev (List.tl llrev), (List.hd llrev), List.hd lrev



(* get the position of element e in list l; first position is 0 *)
let get_pos e l =
  let rec get_pos' e i = function
    | h::t -> if h=e then i else get_pos' e (i+1) t
    | [] -> raise Not_found
  in get_pos' e 0 l

let get_pos_no_e e l =
  let rec get_pos' e i = function
    | h::t -> if h=e then i else get_pos' e (i+1) t
    | [] -> -1
  in get_pos' e 0 l




(* the result is the list [l] without the elements of positions in [posl]
   assumes [posl] is a ascending list of valid position is [l] *)
let remove_positions posl l =
  let rec rm crt acc posl l =
    match l,posl with
    | h::t, hp::tp ->
      if hp = crt then
        rm (crt+1) acc tp t
      else
        rm (crt+1) (h::acc) posl t
    | _,[] -> (List.rev acc) @ l
    | [],_ -> failwith "[Misc.remove_positions] position not found"
  in
  rm 0 [] posl l


(* the result is the list [l] containing only the elements of
   positions in [posl] *)
let get_positions posl l =
  List.map (List.nth l) posl

let rec zip l1 l2 = match l1, l2 with
  | x::xs , y::ys -> (x,y):: zip xs ys
  | _ -> []

let replace m = 
  let rec replace_acc a = function
    | [] -> List.rev a
    | x::xs -> 
      let n = if List.mem_assoc x m then (List.assoc x m) else x in
      replace_acc (n::a) xs
  in
  replace_acc []

    






(*** Apparently these functions are not used anymore ***)



(*
let remove_at_pos pos l =
  let rec remove_pos' i first = function
    | h::t ->
      if i=pos then
        first@t
      else
        remove_pos' (i+1) (first@[h]) t
    | [] -> failwith "[Misc.remove_pos] position not found"
  in remove_pos' 0 [] l



(* delete the elements which satisfy the predicate p *)
let delete p l = List.filter (fun x -> not (p x)) l



(* returns true iff t1 is a (non-strict) prefix of t2 *)
let rec prefix_of l1 l2 =
  match l1,l2 with
  | [],_ -> true
  | h1::t1,h2::t2 when h1=h2 -> prefix_of t1 t2
  | _ -> false


let filter2 f l =
  let rec filter2' acc = function
    | [] -> List.rev acc
    | h::t ->
      let b,h' = f h in
      if b then
        filter2' (h'::acc) t
      else
        filter2' acc t
  in
  filter2' [] l


(* equivalent with: List.map g (List.filter f l)) *)
let rec filter_map f g = function
  | h::t ->
    if f h then
      (g h)::(filter_map f g t)
    else
      filter_map f g t
  | [] -> []


(* equivalent with:
   let l1,l2 = List.partition p l in
   (List.map g l1), l2
*)
let partition_map p f l =
  let rec part res = function
    | [] -> res,[]
    | h::t ->
      if p h then
        part ((f h)::res) t
      else
        let l1, l2 = part res t in
        l1, h::l2
  in
  part [] l
*)


(* return current memory usage *)
let mem_usage mem_str =
  let p = Unix.getpid() in
  let file = "/proc/" ^ (string_of_int p) ^ "/status" in
  let ic = open_in file in
  (* let re = Str.regexp "VmSize: +[0-9]+ kB" in *)
  let re = Str.regexp (mem_str ^ ":[^0-9]+\\([0-9]+\\) kB") in
  let rec find_mem ic =
    try
      let line = input_line ic in
      if Str.string_match re line 0 then
        begin
          close_in ic;
          Str.matched_group 1 line
        end
      else
        find_mem ic
    with End_of_file ->
      close_in ic;
      ""
  in find_mem ic

let mem_current () = mem_usage "VmSize"
(* let mem_max () = mem_usage "VmPeak" *)

(* return maximum memory usage *)
let mem_max () =
  let p = Unix.getpid() in
  let file = "/proc/" ^ (string_of_int p) ^ "/status" in
  let ic = open_in file in
  (* let re = Str.regexp "VmSize: +[0-9]+ kB" in *)
  let re = Str.regexp "VmPeak:[^0-9]+\\([0-9]+\\) kB" in
  let rec find_mem ic =
    try
      let line = input_line ic in
      if Str.string_match re line 0 then
        begin
          close_in ic;
          Str.matched_group 1 line
        end
      else
        find_mem ic
    with End_of_file ->
      close_in ic;
      ""
  in find_mem ic

(* dump memory usage statistics *)
let mem_all () =
  let p = Unix.getpid() in
  let file = "/proc/" ^ (string_of_int p) ^ "/status" in
  let ic = open_in file in
  try
    while true; do
      let line = input_line ic in
      Printf.eprintf "%s\n%!" line
    done
  with End_of_file ->
    close_in ic
