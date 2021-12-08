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

exception Stop_parser

module type Consumer = sig
  type t
  val begin_tp: t -> MFOTL.timestamp -> unit
  val tuple: t -> Table.schema -> string list -> unit
  val end_tp: t -> unit
  val command: t -> string -> Helper.commandParameter option -> unit
  val end_log: t -> unit
  val parse_error: t -> Lexing.position -> string -> unit
end

let string_of_position p = Lexing.(
  Printf.sprintf "%s:%d:%d" p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol + 1))

let string_of_token (t: Log_lexer.token) =
  match t with
  | AT -> "'@'"
  | LPA -> "'('"
  | RPA -> "')'"
  | LCB -> "'{'"
  | RCB -> "'}'"
  | COM -> "','"
  | SEP -> "';'"
  | STR s -> "\"" ^ String.escaped s ^ "\""
  | EOF -> "<EOF>"
  | CMD -> "'>'"
  | EOC -> "'<'"
  | ERR -> "<unrecognized>"

type parsebuf = {
  pb_lexbuf: Lexing.lexbuf;
  mutable pb_token: Log_lexer.token;
  mutable pb_schema: Table.schema;
}

let init_parsebuf lexbuf = {
  pb_lexbuf = lexbuf;
  pb_token = Log_lexer.token lexbuf;
  pb_schema = ("", []);
}

let next pb = pb.pb_token <- Log_lexer.token pb.pb_lexbuf

(* Utility parsers *)

exception Local_error of string

let expect pb t = if pb.pb_token = t then next pb
  else raise (Local_error ("Expected " ^ string_of_token t ^ " but saw "
    ^ string_of_token pb.pb_token))

let parse_string pb =
  match pb.pb_token with
  | STR s -> next pb; s
  | t -> raise (Local_error ("Expected a string but saw " ^ string_of_token t))

let parse_int pb =
  let s = parse_string pb in
  try int_of_string s
  with Failure _ -> raise (Local_error ("Expected an integer but saw \""
    ^ String.escaped s ^ "\""))

let parse_tuple pb =
  let rec more l =
    match pb.pb_token with
    | COM ->
        next pb;
        let s = parse_string pb in
        more (s::l)
    | RPA -> next pb; List.rev l
    | t -> raise (Local_error ("Expected ',' or ')' but saw "
        ^ string_of_token t))
  in
  expect pb LPA;
  match pb.pb_token with
  | RPA -> next pb; []
  | STR s -> next pb; more [s]
  | t -> raise (Local_error ("Expected a string or ')' but saw "
      ^ string_of_token t))


(* Signature *)

let get_type = function
  | "int" -> Predicate.TInt
  | "string" -> Predicate.TStr
  | "float" -> Predicate.TFloat
  | "regexp" -> Predicate.TRegexp
  | t -> raise (Local_error ("Unknown type " ^ t))

let convert_types l = List.map
  (fun str ->
    match Misc.nsplit str ":" with
    | [] -> failwith "[Log_parser.convert_types] internal error"
    | [type_str] -> "", get_type type_str
    | var_name :: type_str :: _ -> var_name, get_type type_str
  ) l

let rec parse_predicates pb dbschema =
  match pb.pb_token with
  | EOF -> dbschema
  | STR s ->
      next pb;
      let l = parse_tuple pb in
      let l = convert_types l in
      parse_predicates pb (Db.add_predicate s l dbschema)
  | t -> raise (Local_error ("Expected a string but saw " ^ string_of_token t))

let parse_signature_pb pb =
  try parse_predicates pb Db.base_schema
  with Local_error msg -> failwith ("Error while parsing signature: " ^ msg)

let parse_signature s =
  let lexbuf = Lexing.from_string s in
  parse_signature_pb (init_parsebuf lexbuf)

(*TODO(JS): Should close ic after parsing.*)
let parse_signature_file fname =
  let ic = open_in fname in
  let lexbuf = Lexing.from_channel ic in
  Lexing.set_filename lexbuf fname;
  parse_signature_pb (init_parsebuf lexbuf)

(* Slicing specification *)

let parse_int_tuple pb =
  let t = parse_tuple pb in
  try List.map int_of_string t
  with Failure _ -> raise (Local_error "Expected a tuple of integers")

let parse_heavy pb =
  expect pb LPA;
  let i = parse_int pb in
  expect pb COM;
  let t = parse_tuple pb in
  expect pb RPA;
  (i, t)

let parse_heavies pb =
  let rec more l =
    match pb.pb_token with
    | COM ->
        next pb;
        let h = parse_heavy pb in
        more (h::l)
    | _ -> List.rev l
  in
  expect pb LCB;
  let h0 = parse_heavy pb in
  let hl = more [h0] in
  expect pb RCB;
  Array.of_list hl

let parse_slices pb =
  let rec more l =
    match pb.pb_token with
    | COM ->
        next pb;
        let t = Array.of_list (parse_int_tuple pb) in
        more (t::l)
    | _ -> List.rev l
  in
  expect pb LCB;
  let t0 = Array.of_list (parse_int_tuple pb) in
  let tl = more [t0] in
  expect pb RCB;
  Array.of_list tl

let parse_slicing_params pb =
  expect pb LCB;
  let heavies = parse_heavies pb in
  expect pb COM;
  let shares = parse_slices pb in
  expect pb COM;
  let seeds = parse_slices pb in
  expect pb RCB;
  (heavies, shares, seeds)

let parse_command_params pb =
  match pb.pb_token with
  | LCB ->
      let p = parse_slicing_params pb in
      expect pb EOC;
      Some (Helper.SplitSave p)
  | STR s ->
      next pb;
      expect pb EOC;
      Some (Helper.Argument s)
  | EOC -> next pb; None
  | t -> raise (Local_error ("Expected a string, '{' or '<' but saw "
      ^ string_of_token t))

(* Main log parser *)

module Make(C: Consumer) = struct
  let parse db_schema lexbuf ctxt =
    let pb = init_parsebuf lexbuf in
    let debug msg =
      if Misc.debugging Misc.Dbg_log then
        Printf.eprintf "[Log_parser] state %s with token=%s\n" msg
          (string_of_token pb.pb_token)
      else ()
    in
    let rec parse_init () =
      debug "init";
      match pb.pb_token with
      | EOF -> ()
      | AT -> next pb; parse_ts ()
      | CMD -> next pb; parse_command ()
      | t -> fail ("Expected '@' or '>' but saw " ^ string_of_token t)
    and parse_ts () =
      debug "ts";
      match pb.pb_token with
      | STR s ->
          let ts =
            try Some (MFOTL.ts_of_string s)
            with Failure _ -> None
          in
          (match ts with
          | Some ts ->
              C.begin_tp ctxt ts;
              next pb;
              parse_db ()
          | None -> fail ("Cannot convert " ^ s ^ " into a timestamp"))
      | t -> fail ("Expected a time-stamp but saw " ^ string_of_token t)
    and parse_db () =
      debug "db";
      match pb.pb_token with
      | STR s ->
          (match List.assoc_opt s db_schema with
          | Some tl ->
              pb.pb_schema <- (s, tl);
              next pb;
              (match pb.pb_token with
              | LPA -> next pb; parse_tuple ()
              | _ -> C.tuple ctxt pb.pb_schema []; parse_db ())
          | None -> fail ("Predicate " ^ s
              ^ " was not defined in the signature."))
      | AT ->
          next pb;
          C.end_tp ctxt;
          parse_ts ()
      | SEP ->
          next pb;
          C.end_tp ctxt;
          parse_init ()
      | CMD ->
          next pb;
          C.end_tp ctxt;
          parse_command ()
      | EOF -> C.end_tp ctxt
      | t -> fail ("Expected a predicate, '@', ';', or '>' but saw "
          ^ string_of_token t)
    and parse_tuple () =
      debug "tuple";
      match pb.pb_token with
      | RPA ->
          parse_tuple_cont []
      | STR s ->
          next pb;
          parse_tuple_cont [s]
      | t -> fail ("Expected a tuple field or ')' but saw " ^ string_of_token t)
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
          | t -> fail ("Expected a tuple field but saw " ^ string_of_token t))
      | t -> fail ("Expected ',' or ')' but saw " ^ string_of_token t)
    and parse_command () =
      debug "command";
      match pb.pb_token with
      | STR name ->
          next pb;
          let err, params =
            try None, parse_command_params pb
            with Local_error msg -> Some msg, None
          in
          (match err with
          | None -> C.command ctxt name params; parse_init ()
          | Some msg -> fail msg)
      | t -> fail ("Expected a command name but saw " ^ string_of_token t)
    and fail msg =
      C.parse_error ctxt pb.pb_lexbuf.Lexing.lex_start_p msg;
      recover ()
    and recover () =
      debug "recover";
      next pb;
      match pb.pb_token with
      | AT -> next pb; parse_ts ()
      | SEP -> next pb; parse_init ()
      | CMD -> next pb; parse_command ()
      | EOF -> ()
      | _ -> next pb; recover ()
    in
    try
      parse_init ();
      C.end_log ctxt;
      true
    with Stop_parser -> false

  let parse_file dbschema fname ctxt =
    let ic =
      if fname = "" then
        stdin
      else
        open_in fname
    in
    let lexbuf = Lexing.from_channel ic in
    Lexing.set_filename lexbuf fname;
    parse dbschema lexbuf ctxt
end
