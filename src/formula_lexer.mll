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
  open Formula_parser
  open Misc

  let f str lexbuf =
    if Misc.debugging Dbg_parsing then
      Printf.eprintf "[Formula_lexer] lexbuf is %s ---%s---\n" str (Lexing.lexeme lexbuf)
    else
      ()

  let my_int_of_string str =
    try
      int_of_string str
    with Failure _ -> failwith "[formula_lexer, int_of_string]"

  let get_ts lxm =
    Scanf.sscanf lxm "%d%c" (fun n -> fun c -> (n,c))
}

let lc = ['a'-'z']
let uc = ['A'-'Z']
let letter = uc | lc
let digit = ['0'-'9']
let integer = ('-')? digit+
let rational = ('-')? digit+ '.' digit*
let unit =  digit+ letter
let any_string = (letter | digit | '_' | '-' | '/' | ':' | '\'' | '\"')*
let string = (letter | digit | '_') any_string
let quoted_string = '"' ([^ '"' '\\'] | '\\' _)* '"'

rule
  token = parse
  | [' ' '\t' '\n' '\r']        { f "white space" lexbuf; token lexbuf }

  | "+"                         { f "PLUS" lexbuf; PLUS }
  | "-"                         { f "MINUS" lexbuf; MINUS }
  | "."                         { f "DOT" lexbuf; DOT }
  | "*"                         { f "STAR" lexbuf; STAR }
  | "/"                         { f "SLASH" lexbuf; SLASH }
  | "("                         { f "LPA" lexbuf; LPA }
  | ")"                         { f "RPA" lexbuf; RPA }
  | "["                         { f "LSB" lexbuf; LSB }
  | "]"                         { f "RSB" lexbuf; RSB }
  | "|>" | "▷" 
  | "FORWARD" | "MATCHF"        { f "FREX" lexbuf; FREX }
  | "<|" | "◁" 
  | "BACKWARD" | "MATCHP"       { f "PREX" lexbuf; PREX }
  | "|"                         { f "BAR" lexbuf; BAR }
  | ","                         { f "COM" lexbuf; COM }
  | ";"                         { f "SC" lexbuf; SC }
  | "?"                         { f "QM" lexbuf; QM }
  | "_"                         { f "LD" lexbuf; LD }
  | "<-"                        { f "LARROW" lexbuf; LARROW }
  | "<="                        { f "LESSEQ" lexbuf; LESSEQ }
  | "SUBSTRING"                 { f "SUBSTRING" lexbuf; SUBSTRING }
  | "MATCHES"                   { f "MATCHES" lexbuf; MATCHES }
  | "r2s"                       { f "R2S" lexbuf; R2S }
  | "s2r"                       { f "S2R" lexbuf; S2R }
  | "<"                         { f "LESS" lexbuf; LESS }
  | ">="                        { f "GTREQ" lexbuf; GTREQ }
  | ">"                         { f "GTR" lexbuf; GTR }
  | "="                         { f "EQ" lexbuf; EQ }
  | "MOD"                       { f "MOD" lexbuf; MOD }
  | "f2i"                       { f "F2I" lexbuf; F2I }
  | "i2f"                       { f "I2F" lexbuf; I2F }
  | "i2s"                       { f "I2S" lexbuf; I2S }
  | "s2i"                       { f "S2I" lexbuf; S2I }
  | "f2s"                       { f "F2S" lexbuf; F2S }
  | "s2f"                       { f "S2F" lexbuf; S2F }
  | "DAY_OF_MONTH"              { f "DAY_OF_MONTH" lexbuf; DAY_OF_MONTH }
  | "MONTH"                     { f "MONTH" lexbuf; MONTH }
  | "YEAR"                      { f "YEAR" lexbuf; YEAR }
  | "FORMAT_DATE"               { f "FORMAT_DATE" lexbuf; FORMAT_DATE }
  | "FALSE"                     { f "FALSE" lexbuf; FALSE }
  | "TRUE"                      { f "TRUE" lexbuf; TRUE }
  | "LET"                       { f "LET" lexbuf; LET }
  | "LETPAST"                   { f "LETPAST" lexbuf; LETPAST }
  | "IN"                        { f "IN" lexbuf; IN }
  | "NOT"                       { f "NOT" lexbuf; NOT }
  | "AND"                       { f "AND" lexbuf; AND }
  | "OR"                        { f "OR" lexbuf; OR }
  | "IMPLIES"                   { f "IMPL" lexbuf; IMPL }
  | "EQUIV"                     { f "EQUIV" lexbuf; EQUIV }
  | "EXISTS"                    { f "EX" lexbuf; EX }
  | "FORALL"                    { f "FORALL" lexbuf; FA }
  | "PREV"                      { f "PREV" lexbuf; PREV }
  | "PREVIOUS"                  { f "PREVIOUS" lexbuf; PREV }
  | "NEXT"                      { f "NEXT" lexbuf; NEXT }
  | "EVENTUALLY"                { f "EVENTUALLY" lexbuf; EVENTUALLY }
  | "SOMETIMES"                 { f "EVENTUALLY" lexbuf; EVENTUALLY }
  | "ONCE"                      { f "ONCE" lexbuf; ONCE }
  | "ALWAYS"                    { f "ALWAYS" lexbuf; ALWAYS }
  | "PAST_ALWAYS"               { f "PAST_ALWAYS" lexbuf; PAST_ALWAYS }
  | "HISTORICALLY"              { f "PAST_ALWAYS" lexbuf; PAST_ALWAYS }
  | "SINCE"                     { f "SINCE" lexbuf; SINCE }
  | "UNTIL"                     { f "UNTIL" lexbuf; UNTIL }
  | "CNT"                       { f "CNT" lexbuf; CNT }
  | "MIN"                       { f "MIN" lexbuf; MIN }
  | "MAX"                       { f "MAX" lexbuf; MAX }
  | "SUM"                       { f "SUM" lexbuf; SUM }
  | "AVG"                       { f "AVG" lexbuf; AVG }
  | "MED"                       { f "MED" lexbuf; MED }

  | unit as lxm                 { f "TU" lexbuf; TU (get_ts lxm)}
  | integer as lxm              { f "INT" lexbuf; INT (Z.of_string lxm) }
  | rational as lxm             { f "RAT" lexbuf; RAT (float_of_string lxm) }
  | quoted_string as lxm        { f "STR_CST" lexbuf; STR_CST lxm }
  | 'r' quoted_string as lxm    { f "REGEXP" lexbuf; REGEXP_CST lxm }
  | string as lxm               { f "STR" lexbuf; STR lxm }

  | "(*"                        { f "multi-line comment" lexbuf; comment lexbuf }
  | "#"                         { f "line comment" lexbuf; line_comment lexbuf}

  | eof                         { f "EOF" lexbuf; EOF }



and
  line_comment = parse
  | ['\n' '\r']                 { f "new line" lexbuf; token lexbuf }
  | _                           { f "lcomment(*)"lexbuf; line_comment lexbuf }
  | eof                         { f "lcomment(EOF)" lexbuf; EOF }

and
  comment = parse
  | "*)"                        { f "end of comment" lexbuf; token lexbuf }
  | _                           { f "comment(*)" lexbuf; comment lexbuf }
  | eof                         { f "comment(EOF)" lexbuf; failwith "comment not ended" }
