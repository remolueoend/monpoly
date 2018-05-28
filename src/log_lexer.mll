(*
 * This file is part of MONPOLY.
 *
 * Copyright © 2011 Nokia Corporation and/or its subsidiary(-ies).
 * Contact:  Nokia Corporation (Debmalya Biswas: debmalya.biswas@nokia.com)
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



{
open Misc
open Lexing
open Log_parser

let f str lexbuf =
  if Misc.debugging Dbg_log then
    let lxm = Lexing.lexeme lexbuf in
    let show = match lxm with
      | "\n" -> "\\n"
      | "\r" -> "\\r"
      | "\t" -> "\\t"
      | _ -> lxm
    in
    begin
      Printf.printf "[Log_lexer]  %s is -%s- with " str show;
      Printf.printf "abs=%d len=%d start=%d curr=%d last=%d start_p=%d curr_p=%d\n%!"
        lexbuf.lex_abs_pos lexbuf.lex_buffer_len lexbuf.lex_start_pos lexbuf.lex_curr_pos lexbuf.lex_last_pos
        lexbuf.lex_start_p.pos_cnum lexbuf.lex_curr_p.pos_cnum
    end
  else
    ()

let strip str =
  let len = String.length str in
  if str.[0] = '\"' && str.[len-1] = '\"' then
    String.sub str 1 (len-2)
  else
    str

let new_line lexbuf =
  let lcp = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { lcp with
      pos_lnum = lcp.pos_lnum + 1;
      pos_bol = lcp.pos_cnum;
    }
}

let lc = ['a'-'z']
let uc = ['A'-'Z']
let letter = uc | lc
let digit = ['0'-'9']
let integer = digit*
let string = (letter | digit | '_' | '[' | ']' | '/' | ':' | '-' | '.' | '!')* | '"'[^'"']*'"'

rule
  token = parse
  | [' ' '\t' ]              { f "white space" lexbuf; token lexbuf }
  | "\n" | "\r" | "\r\n"     { f "line break" lexbuf; new_line lexbuf; token lexbuf }
  | "@"                      { f "TS"  lexbuf; AT }
  | ">"                      { f "CMD" lexbuf; CMD }
  | "<"                      { f "CMD" lexbuf; EOC }
  | "("                      { f "LPA" lexbuf; LPA }
  | ")"                      { f "RPA" lexbuf; RPA }
  | "{"                      { f "LBC" lexbuf; LCB }
  | "}"                      { f "RCB" lexbuf; RCB }
  | ","                      { f "COM" lexbuf; COM }

  | string as lxm            { f "STR" lexbuf; STR (strip lxm) }

  | "#"                      { f "#" lexbuf; line_comment lexbuf }

  | eof                      { f "EOF" lexbuf; EOF }

  | _                        { f "ERR" lexbuf;
                               if !Misc.ignore_parse_errors then
                                 ERR
                               else
                                 failwith "Illegal character in log file."
                             }

and
  line_comment = parse
  | ['\n' '\r']              { f "end comment" lexbuf; new_line lexbuf; token lexbuf }
  | _                        { f "any" lexbuf; line_comment lexbuf }
  | eof                      { f "eof" lexbuf; EOF }
