(*
 * This file is part of MONPOLY.
 *
 * Copyright (C) 2021 ETH Zurich.
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

type token = Log_parser.token

exception Stop_parser

module type Consumer = sig
  type t
  val begin_tp: t -> MFOTL.timestamp -> unit
  val tuple: t -> Table.schema -> string list -> unit
  val end_tp: t -> unit
end

type parsebuf = {
  pb_lexbuf: Lexing.lexbuf;
  mutable pb_token: token;
  mutable pb_schema: Table.schema;
}

let init_parsebuf lexbuf = {
  pb_lexbuf = lexbuf;
  pb_token = Log_lexer.token lexbuf;
  pb_schema = ("", []);
}

let next pb = pb.pb_token <- Log_lexer.token pb.pb_lexbuf

let str_of_token = Log_parser.(function
  | AT -> "AT"
  | LPA -> "LPA"
  | RPA -> "RPA"
  | LCB -> "LCB"
  | RCB -> "RCB"
  | COM -> "COM"
  | SEP -> "SEP"
  | STR s -> "STR(" ^ s ^ ")"
  | EOF -> "EOF"
  | CMD -> "CMD"
  | EOC -> "EOC"
  | ERR -> "ERR")

module Make(C: Consumer) = struct
  let parse dbs lexbuf ctxt =
    let pb = init_parsebuf lexbuf in
    let fail () = failwith "[Simple_log_parser] Parse error" in
    let debug msg =
      if Misc.debugging Misc.Dbg_log then
        Printf.eprintf "[Simple_log_parser] %s with token=%s\n" msg
          (str_of_token pb.pb_token)
      else ()
    in
    let rec parse_init () =
      debug "init";
      match pb.pb_token with
      | EOF -> ()
      | AT -> next pb; parse_ts ()
      | _ -> fail ()
    and parse_ts () =
      debug "ts";
      match pb.pb_token with
      | STR s ->
          next pb;
          C.begin_tp ctxt (MFOTL.ts_of_string "Simple_log_parser" s);
          parse_db ()
      | _ -> fail ()
    and parse_db () =
      debug "db";
      match pb.pb_token with
      | STR s ->
          next pb;
          pb.pb_schema <- (s, try List.assoc s dbs with Not_found -> fail ());
          (match pb.pb_token with
          | LPA -> next pb; parse_tuple ()
          | _ -> C.tuple ctxt pb.pb_schema []; parse_db ())
      | AT ->
          next pb;
          C.end_tp ctxt;
          parse_ts ()
      | SEP ->
          next pb;
          C.end_tp ctxt;
          parse_init ()
      | EOF -> C.end_tp ctxt
      | _ -> fail ()
    and parse_tuple () =
      debug "tuple";
      match pb.pb_token with
      | RPA ->
          next pb;
          C.tuple ctxt pb.pb_schema [];
          parse_db ()
      | STR s ->
          next pb;
          parse_tuple_cont [s]
      | _ -> fail ()
    and parse_tuple_cont l =
      debug "tuple_cont";
      match pb.pb_token with
      | RPA ->
          next pb;
          C.tuple ctxt pb.pb_schema (List.rev l);
          (match pb.pb_token with
          | LPA -> next pb; parse_tuple ()
          | _ -> parse_db ())
      | COM ->
          next pb;
          (match pb.pb_token with
          | STR s ->
              next pb;
              parse_tuple_cont (s::l)
          | _ -> fail ())
      | _ -> fail ()
    in
    try parse_init (); true with Stop_parser -> false
end
