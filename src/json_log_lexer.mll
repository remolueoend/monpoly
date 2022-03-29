{
  open Lexing
  open Range
  
  exception Lexer_error of Range.t * string
  
  type token = AT | TS of Z.t | JSON of string | EOF

  let newline lexbuf =
    lexbuf.lex_curr_p <- { (lexeme_end_p lexbuf) with
      pos_lnum = (lexeme_end_p lexbuf).pos_lnum + 1;
      pos_bol = (lexeme_end lexbuf) }
      
  let get_ts_of_string lexbuf str =
    try
      Z.of_string str
    with Failure s ->
      raise (Lexer_error (Range.lex_range lexbuf, Printf.sprintf "Failed to parse timestamp: %s" s))
    
  (* Boilerplate to define exceptional cases in the lexer. *)
  let unexpected_char lexbuf (c:char) : 'a =
    raise (Lexer_error (Range.lex_range lexbuf,
        Printf.sprintf "Unexpected character: '%c'" c))
}

let digit = ['0'-'9']
let newline = '\n' | ('\r' '\n') | '\r'
let whitespace = ['\t' ' ']

rule
  token = parse
  | eof                                { EOF }
  | "@"                                { AT }
  | (digit)+ as ts                     { TS (get_ts_of_string lexbuf ts) }
  | whitespace+                        { token lexbuf }
  | newline                            { newline lexbuf; token lexbuf }
  | "{" ([^ '\n' '\r'])+ "}" as json   { JSON json }