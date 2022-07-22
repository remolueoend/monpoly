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
open Misc
open MFOTL

let start_time = Unix.time()
let last_time_q = ref start_time
let last_time_i = ref start_time

let min_diff = 0.
let q_step = ref 1000
let i_step = 1000
let next_alarm = 300

let _ =
  (* prerr_endline ("Current working directory: " ^ Sys.getcwd ()); *)
  try
    let ch = open_in "perf.conf" in
    q_step := int_of_string (input_line ch);
    (* Printf.eprintf "[Perf] New value for q_step: %d\n%!" !q_step; *)
    close_in ch
  with _ -> () (* prerr_endline e *)

let show_results q tsq =
  if q mod !q_step = 0 then
    begin
      let now = Unix.time() in
      let diff = now -. !last_time_q in
      (* if diff >= min_diff then *)
      begin
        let times = Unix.times() in
        Printf.eprintf "show_results: loop %6d @%s (%2.2f  %5.0f s) \
                        (u:%.0f s:%.0f t:%.0f mem:%s kB)\n%!"
          q (MFOTL.string_of_ts tsq)   diff (now -. start_time)
          times.tms_utime times.tms_stime
          (times.tms_utime +. times.tms_stime)
          (Misc.mem_current ());
        last_time_q := now
      end
    end;

  if !Misc.alrm then
    begin
      Misc.alrm := false;
      ignore(Unix.alarm next_alarm);
      Printf.eprintf "show_results: loop %6d @%s (after 5min) \n%!" q (MFOTL.string_of_ts tsq);
    end



let check_log i last_ts =
  if i mod i_step = 0 then
    begin
      Printf.eprintf "check_log: loop %6d" i;
      Printf.eprintf " @%s" (MFOTL.string_of_ts last_ts);
      let now = Unix.time() in
      let times = Unix.times() in
      Printf.eprintf " (%2.0f  %5.0f s) (u:%.0f s:%.0f t:%.0f mem:%s kB)\n%!"
        (now -. !last_time_i) (now -. start_time)
        times.tms_utime times.tms_stime (times.tms_utime +. times.tms_stime)
        (Misc.mem_current ());
      last_time_i := now
    end

let check_log i last_ts = ()

let check_log_end i last_ts =
  Printf.eprintf "check_log: last loop %6d" i;
  Printf.eprintf " @%s" (MFOTL.string_of_ts last_ts);
  let now = Unix.time() in
  Printf.eprintf " (%2.0f  %5.0f s) \n%!" (now -. !last_time_i) (now -. start_time)

let dump_stats starttime =
  let now = Unix.time() in
  let diff = now -. starttime in
  Printf.eprintf "===STATS=== time: %.0f\n" diff;
  let times = Unix.times() in
  Printf.eprintf "===STATS=== times: (u:%.0f s:%.0f t:%.0f)\n"
    times.tms_utime times.tms_stime
    (times.tms_utime +. times.tms_stime);
  Printf.eprintf "===STATS=== mem: %s kB\n" (Misc.mem_max ())


type profile_state = {
  mutable ps_enter_global: float;
  mutable ps_enter: float array;
  mutable ps_acc: float array;
  mutable ps_groups: (int * string) list;
}

let profile_state = {
  ps_enter_global = 0.0;
  ps_enter = [||];
  ps_acc = [||];
  ps_groups = [];
}

let add_profile_group i s =
  profile_state.ps_groups <- (i, s) :: profile_state.ps_groups

let begin_profile () =
  if profile_state.ps_enter_global > 0.0 then
    failwith "[Perf.begin_profile] Profiling has already been started";
  let n = List.fold_left (fun a (i, _) -> max a i) 0 profile_state.ps_groups
    + 1 in
  profile_state.ps_enter <- Array.make n 0.0;
  profile_state.ps_acc <- Array.make n 0.0;
  profile_state.ps_enter_global <- Sys.time ()

let profile_enter i = profile_state.ps_enter.(i) <- Sys.time ()

let profile_exit i x =
  let now = Sys.time () in
  let diff = now -. profile_state.ps_enter.(i) in
  profile_state.ps_acc.(i) <- profile_state.ps_acc.(i) +. diff;
  x

let end_profile () =
  let now = Sys.time () in
  let total_time = now -. profile_state.ps_enter_global in
  let total_label = "total" in
  let label_len = List.fold_left (fun a (_, s) -> max a (String.length s))
    (String.length total_label) profile_state.ps_groups in
  let pad s = s ^ String.make (label_len - String.length s) ' ' in
  Printf.eprintf "=== Performance profile ===\n";
  Printf.eprintf "%s %10.6f\n" (pad total_label) total_time;
  for i = 0 to Array.length profile_state.ps_acc - 1 do
    match List.assoc_opt i profile_state.ps_groups with
    | Some s ->
        let time = profile_state.ps_acc.(i) in
        let frac = (time /. total_time) *. 100.0 in
        Printf.eprintf "%s %10.6f %4.1f%%\n" (pad s) time frac
    | None -> ()
  done;
  Printf.eprintf "===========================\n"


(* New profiling infrastructure *)

let loc_main_loop = -1
let loc_read_tp = -2
let loc_eval_root = -3

let tag_enter = 1
let tag_exit = 2
let tag_eval_result = 64
let tag_extformula = 128

let profile_enabled = ref false
let filename = ref ""
let pbuf = ref None

let enable_profile outfile =
  assert (not !profile_enabled);
  profile_enabled := true;
  filename := outfile;
  pbuf := Some (Buffer.create 1000000)

let finalize_profile () =
  match !pbuf with
  | None -> ()
  | Some buf ->
      let ch = open_out_bin !filename in
      Buffer.output_buffer ch buf;
      close_out ch

let profile_int ~tag ~tp ~loc x =
  match !pbuf with
  | None -> ()
  | Some buf ->
      Buffer.add_uint8 buf tag;
      Buffer.add_int32_le buf (Int32.of_int tp);
      Buffer.add_int32_le buf (Int32.of_int loc);
      Buffer.add_int32_le buf (Int32.of_int x)

let profile_time ~tag ~tp ~loc =
  match !pbuf with
  | None -> ()
  | Some buf ->
      let now = Sys.time() in
      Buffer.add_uint8 buf tag;
      Buffer.add_int32_le buf (Int32.of_int tp);
      Buffer.add_int32_le buf (Int32.of_int loc);
      Buffer.add_int64_le buf (Int64.bits_of_float now)

let profile_enter ~tp ~loc = profile_time ~tag:tag_enter ~tp ~loc
let profile_exit ~tp ~loc = profile_time ~tag:tag_exit ~tp ~loc

let profile_string ~tag x =
  match !pbuf with
  | None -> ()
  | Some buf ->
      Buffer.add_uint8 buf tag;
      Buffer.add_int32_le buf (Int32.of_int (String.length x));
      Buffer.add_string buf x
