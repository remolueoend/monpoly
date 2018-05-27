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



open Lexing
open Helper
open Misc
open Predicate
open Log_parser
open Filter_empty_tp

let logfile = ref ""


let test lexbuf =
  let len = String.length lexbuf.lex_buffer in
  Printf.printf "len=%d buffer_len=%d\n" len  lexbuf.lex_buffer_len;
  Printf.printf "lex_abs_pos = %d\n\
                 lex_start_pos = %d\n\
                 lex_curr_pos = %d\n\
                 lex_last_pos = %d\n\
                 lex_last_action = %d\n\
                 lex_start_p: pos_lnum = %d, pos_bol = %d, pos_cnum = %d\n\
                 lex_curr_p: pos_lnum = %d, pos_bol = %d, pos_cnum = %d\n"
    lexbuf.lex_abs_pos
    lexbuf.lex_start_pos
    lexbuf.lex_curr_pos
    lexbuf.lex_last_pos
    lexbuf.lex_last_action
    lexbuf.lex_start_p.pos_lnum lexbuf.lex_start_p.pos_bol lexbuf.lex_start_p.pos_cnum
    lexbuf.lex_curr_p.pos_lnum lexbuf.lex_curr_p.pos_bol lexbuf.lex_curr_p.pos_cnum




(* It seems we have:
     start_p.pos_cnum = abs_pos + start_pos
     curr_p.pos_cnum = abs_pos + curr_pos

   [abs_pos] seems to be an absolute position in the stream
   (unless [flush_input] has been called...)

   [start_pos] and [curr_pos] are relative positions (within
   [lex_buffer]) and delimit the current lexeme

   See also lexing.ml

   We could also try to mark the character [cnum] as in:
     line prefix  current token  rest of line
                                ^

   Note that the returned [line] omits the prefix if the current token
   is not at the beginning of the line.
*)
let show_error lexbuf =
  (* test lexbuf; *)
  let start = lexbuf.lex_start_p in
  let curr = lexbuf.lex_curr_p in
  let lnum = curr.pos_lnum in
  let snum = start.pos_cnum - start.pos_bol in
  let cnum = curr.pos_cnum - curr.pos_bol in
  let token = Lexing.lexeme lexbuf in
  let rest = String.sub lexbuf.lex_buffer lexbuf.lex_start_pos lexbuf.lex_buffer_len in
  let line_end_pos =
    try
      String.index_from rest 0 '\n'
    with
    | Not_found -> (String.length rest) - 1
  in
  let line = String.sub rest 0 line_end_pos in
  (* Note: [line] is only a suffix (startintg at index [snum]) of the
     line number [lnum] *)
  lnum, snum, cnum, token, line


let get_signature_lexbuf lexbuf =
  try
    let sign = Log_parser.signature Log_lexer.token lexbuf in
    if Misc.debugging Dbg_all then
      Printf.eprintf "[Log.get_sign] The signature file was parsed correctly.\n";
    if (List.mem_assoc "tp" sign || List.mem_assoc "ts" sign || List.mem_assoc "tp" sign) then
      failwith "[Log.get_sign] The predicates tp, ts, tpts are predefined and \
                should not be declared in the signature file."
    else
      let predefined_predicates =
  [("tp", ["i", TInt]);
   ("ts", ["t", TInt]);
   ("tpts", [("i", TInt); ("t", TInt)]);]
      in predefined_predicates @ sign
  with e ->
    Printf.eprintf
      "[Log.get_sign_from_file] Failed to parse signature file. Error at line %d:\n%s\n"
      lexbuf.lex_start_p.pos_lnum
      lexbuf.lex_buffer;
    raise e

let get_signature_string s =
  let lexbuf = Lexing.from_string s in
  get_signature_lexbuf lexbuf

let get_signature sigfile =
  let ic = open_in sigfile in
  let lexbuf = Lexing.from_channel ic in
  get_signature_lexbuf lexbuf


let log_open logfile =
  let ic =
    if logfile = "" then
      stdin
    else
      open_in logfile
  in
  Lexing.from_channel ic




let update lexbuf =
  if Misc.debugging Dbg_log then
    Printf.eprintf "[Log.update] curr=%d\n%!" lexbuf.lex_curr_pos;
  if lexbuf.lex_curr_pos > 0 then
    lexbuf.lex_curr_pos <- lexbuf.lex_curr_pos - 1

let skipped_tps = ref 0
let last = ref false
let tp = ref 0

let get_next_entry lexbuf =
  let rec get_next lexbuf =
    let log_entry =
      try
        Log_parser.tsdb Log_lexer.token lexbuf
      with e ->
        let lnum, snum, cnum, token, line = show_error lexbuf in
        Printf.eprintf
          "[Log.get_next_entry] Failed to parse log file. \
           Error at line %d, character %d. Current token is: %s. \
           Suffix of line %d starting from index %d is: %s.\n%!"
          lnum cnum token lnum snum line;
        raise e
    in
    match log_entry with
    | DataTuple {ts; db; } when ts = MFOTL.ts_invalid ->
      let lnum, snum, cnum, token, line = show_error lexbuf in
      Printf.eprintf
        "[Log.get_next_entry] Ignoring the current time point due to parse error. \
         Error at line %d, character %d. Current token is: %s. \
         Suffix of line %d starting from index %d is: %s.\n%!"
        lnum cnum token lnum snum line;
      update lexbuf;
      get_next lexbuf

    | DataTuple {ts; db; } ->
      update lexbuf;
      incr tp;
      if !Filter_empty_tp.enabled && Db.is_empty db then
        begin (* skip empty db *)
          incr skipped_tps;
          get_next lexbuf
        end
      else
         MonpolyData {tp = !tp - 1; ts; db; }

    | CommandTuple { c; split } ->
        MonpolyCommand { c; split }

    | ErrorTuple s ->
      if Misc.debugging Dbg_filter then
        Printf.eprintf "Filter_empty_tp: skipped: %d, notskipped: %d\n"
          !skipped_tps (!tp - !skipped_tps);

      if not !last && !Misc.new_last_ts then
        begin
          last := true;
           MonpolyData { tp = !tp; ts = MFOTL.ts_max; db = Db.make_db []; }
        end
      else
        MonpolyError s

  in get_next lexbuf
