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


open Libmonpoly
open Misc
open Predicate
open MFOTL
open Formula_parser
open Lexing
open Algorithm
open Rewriting

let usage_string =
  "Usage: monpoly -sig <file> -formula <file> [-negate] [-log <file>]
               [-help] [-version] [-debug <unit>] [-verbose] [-no_rw]
               [-check] [-sigout] [-unix] [-mem] [-nonewlastts] [-verified]
               [-no_mw] [-nofilterrel] [-nofilteremptytp] [-stats]
               [-ignore_parse_errors] [-stop_at_out_of_order_ts]
               [-stop_at_first_viol] [-load <file>]"

let print_usage_and_exit () =
  prerr_endline usage_string;
  exit 2


let formulafile = ref ""

let analyze_formulafile () =
  let ic = open_in !formulafile in
  try
    let f = Formula_parser.formula Formula_lexer.token (Lexing.from_channel ic) in
    if Misc.debugging Dbg_all then
      Printf.eprintf "[Main.main] The formula file was parsed correctly.\n%!";
    f
  with e -> Printf.eprintf "[Main.main] Failed to parse formula file\n%!"; raise e





let logfile = ref ""
let sigfile = ref ""
let debug = ref ""

let negate = ref false
let inc = ref false
let memarg = ref false
let sigout = ref false
let statsarg = ref false

let nofilteremptytpopt = ref false
let nofilterrelopt = ref false

(* Printexc.record_backtrace true;; *)

let starttime = Unix.time()


let sigusr1_handler =
  (Sys.Signal_handle
     (fun _ ->
        prerr_endline "SIGUSR1 handler: exiting...";
        exit 0))

let sigusr2_handler =
  (Sys.Signal_handle
     (fun _ -> Misc.usr2 := true ))

let sigalrm_handler =
  (Sys.Signal_handle
     (fun _ -> Misc.alrm := true ))


let displayver = ref false

let print_banner () =
  let banner =
    match Build_info.V1.version () with
    | None -> "MonPoly (development build)"
    | Some v -> "MonPoly, version " ^ Build_info.V1.Version.to_string v
  in
  print_endline banner

let main () =
  Sys.set_signal Sys.sigusr1 sigusr1_handler;
  Sys.set_signal Sys.sigusr2 sigusr2_handler;
  Sys.set_signal Sys.sigalrm sigalrm_handler;

  Misc.split_debug !debug;

  if !displayver then
    print_banner ()
  else if !formulafile = "" then
    print_usage_and_exit ()
  else
    (* read formula file *)
    let f = analyze_formulafile () in
    let f = if !negate then Neg f else f in
    if !sigfile = "" then
      print_usage_and_exit ()
    else
      begin
        (* read signature file *)
        let sign = Log_parser.parse_signature_file !sigfile in
        let _ = if is_mfodl f then Misc.verified := true else () in

        let is_mon, pf, vartypes = check_formula sign f in
        let fv = List.map fst vartypes in
        if !sigout then
          Predicate.print_vartypes_list vartypes
        else if is_mon && not !Misc.checkf then
          begin
            (* By default, that is without user specification (see option
              -nonewlastts), we add a new maximal timestamp for future formulas;
              that is, we assume that no more events will happen in the
              future. For past-only formulas we never add such a timestamp. *)
            if not (Rewriting.is_future pf) then
              Misc.new_last_ts := false;
            if not !nofilterrelopt then
              Filter_rel.enable pf;
            if not !nofilteremptytpopt && not !Misc.verified then
              Filter_empty_tp.enable pf;
            if !Algorithm.resumefile <> "" then
              Algorithm.resume sign !logfile
            else if !Algorithm.combine_files <> "" then
              Algorithm.combine sign !logfile
            else if !Misc.verified then
              Algorithm_verified.monitor sign !logfile fv pf
            else
              Algorithm.monitor sign !logfile fv pf
          end
      end

let set_unfold_let = function
  | "no" -> Rewriting.unfold_let := None
  | "full" -> Rewriting.unfold_let := Some (Rewriting.ExpandAll)
  | "smart" -> Rewriting.unfold_let := Some (Rewriting.ExpandNonshared)
  | _ -> ()  (* impossible *)

let _ =
  Arg.parse [
    "-sig", Arg.Set_string sigfile, "\t\tChoose the signature file";
    "-formula", Arg.Set_string formulafile, "\tChoose the formula file";
    "-negate", Arg.Set negate, "\tAnalyze the negation of the input formula";
    "-log", Arg.Set_string logfile, "\t\tChoose the log file";
    "-version", Arg.Set displayver, "\tDisplay the version (and exit)";
    "-debug", Arg.Set_string debug, "\tChoose aspect to debug, among 'eval', 'perf', 'log', 'parsing', 'typing' 'monitorable', 'filter' (select multple using commas)";
    "-verbose", Arg.Set Misc.verbose, "\tTurn on verbose mode";
    "-check", Arg.Set Misc.checkf, "\tCheck if formula is monitorable (and exit)";
    "-no_rw", Arg.Set Rewriting.no_rw, "\tNo formula rewrite";
    "-sigout", Arg.Set sigout, "\tShow the output signature (and exit)";
    "-unix", Arg.Set MFOTL.unixts, "\tTimestamps represent Unix time";
    "-mem", Arg.Set memarg, "\t\tShow maximum memory usage on stderr";
    "-nonewlastts", Arg.Clear Misc.new_last_ts, "\tDo not add a last maximal timestamp";
    "-nofilterrel", Arg.Set nofilterrelopt, "\tDisable filter_rel module";
    "-nofilteremptytp", Arg.Set nofilteremptytpopt, "\tDisable filter_empty_tp module";
    "-stats", Arg.Set statsarg, "\t\tShow stats at the end of stdout";
    "-ignore_parse_errors", Arg.Set Misc.ignore_parse_errors, "\tIgnore log parse errors";
    "-stop_at_out_of_order_ts", Arg.Set Misc.stop_at_out_of_order_ts, "\tStop monitoring when out-of-order timestamps encountered, otherwise issue warning";
    "-stop_at_first_viol", Arg.Set Misc.stop_at_first_viol, "\tStop at first encountered violation";
    "-load", Arg.Set_string Algorithm.resumefile, "\tLoad monitor state from file";
    "-combine", Arg.Set_string Algorithm.combine_files, "\tComma separated partition files to combine";
    "-verified", Arg.Set Misc.verified, "\tRun the Monpoly's verified kernel";
    "-no_mw", Arg.Set Algorithm_verified.no_mw, "\tNo multi-way join (only with the verified kernel)";
    "-unfold_let", Arg.Symbol (["no"; "full"; "smart"], set_unfold_let),
      "\tWhether and how LET expressions in the formula should be unfolded (default 'no')";
    "-strcache", Arg.Set Misc.str_cache, "\tUse string cache to reduce memory usage";
    "-profile", Arg.String Perf.enable_profile, "\tWrite profile events to the given file";
  ]
    (fun _ -> print_usage_and_exit ())
    usage_string;
  if Misc.debugging Dbg_perf then
    ignore(Unix.alarm 600);
  main ();
  Perf.finalize_profile ();
  if !memarg then
    prerr_endline (Misc.mem_max ());
  if !statsarg then
    Perf.dump_stats starttime



