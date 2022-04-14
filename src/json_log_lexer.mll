{
  open Lexing
  open Range
  
  exception Lexer_error of Range.t * string
  
  type token =
  | AT 
  | TS of Z.t 
  | JSON of string 
  | CMD 
  | EOC 
  | LPA
  | RPA
  | LCB 
  | RCB 
  | COM 
  | STR of string 
  | EOF

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
        
  let f str lexbuf =
  if Misc.debugging Misc.Dbg_log then
    let lxm = Lexing.lexeme lexbuf in
    let show = match lxm with
      | "\n" -> "\\n"
      | "\r" -> "\\r"
      | "\t" -> "\\t"
      | _ -> lxm
    in
    begin
      Printf.eprintf "[Log_lexer]  %s is -%s- with " str show;
      Printf.eprintf "abs=%d len=%d start=%d curr=%d last=%d start_p=%d curr_p=%d\n%!"
        lexbuf.lex_abs_pos lexbuf.lex_buffer_len lexbuf.lex_start_pos lexbuf.lex_curr_pos lexbuf.lex_last_pos
        lexbuf.lex_start_p.pos_cnum lexbuf.lex_curr_p.pos_cnum
    end
  else
    ()
}

let lc = ['a'-'z']
let uc = ['A'-'Z']
let letter = uc | lc
let digit = ['0'-'9']
let cmd_str = (letter | digit | '_' | '[' | ']' | '/' | ':' | '-' | '.' | '!')+
let newline = '\n' | ('\r' '\n') | '\r'
let whitespace = ['\t' ' ']

rule
  token = parse
  | eof                                { f "EOF" lexbuf; EOF }
  | ">"                                { f "CMD" lexbuf; CMD }
  | "<"                                { f "EOC" lexbuf; EOC }
  | "@"                                { f "AT"  lexbuf; AT  }
  | "("                                { f "LPA" lexbuf; LPA }
  | ")"                                { f "RPA" lexbuf; RPA }
  | "{"                                { f "LBC" lexbuf; LCB }
  | "}"                                { f "RCB" lexbuf; RCB }
  | ","                                { f "COM" lexbuf; COM }
  | (digit)+ as ts                     { f ("TS: " ^ ts) lexbuf; TS (get_ts_of_string lexbuf ts) }
  | whitespace+                        { token lexbuf }
  | newline                            { f "newline" lexbuf; newline lexbuf; token lexbuf }
  | "{" ([^ '\n' '\r'])+ "}" as json   { f "JSON" lexbuf; JSON json }
  | cmd_str as s                        { f "STR" lexbuf; STR s }