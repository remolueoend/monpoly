{
  open Lexing
  open Signature_parser
  open Range
  
  exception Lexer_error of Range.t * string

  let newline lexbuf =
    lexbuf.lex_curr_p <- { (lexeme_end_p lexbuf) with
      pos_lnum = (lexeme_end_p lexbuf).pos_lnum + 1;
      pos_bol = (lexeme_end lexbuf) }
    
  (* Boilerplate to define exceptional cases in the lexer. *)
  let unexpected_char lexbuf (c:char) : 'a =
    raise (Lexer_error (Range.lex_range lexbuf,
        Printf.sprintf "Unexpected character: '%c'" c))
        
  let reserved_words = [
    (* keywords *)
    ("int", TINT);
    ("string", TSTRING);
    ("float", TFLOAT);
    ("regexp", TREGEXP);
    ("event", EVENT);
    
    (* symbol *)
    ("(", LPA);
    (")", RPA);
    ("{", LCB);
    ("}", RCB);
    (",", COM);
    (";", SEP);
    (":", COL);
  ]
  
  (* generate symbol table id -> token for all reserved words listed above *)
  let (symbol_table : (string, Signature_parser.token) Hashtbl.t) = Hashtbl.create 1024
  let _  =
    List.iter (fun (str, t) -> Hashtbl.add symbol_table str t) reserved_words
  
  (* either returns an existing token from the symbol table matching its identifer
     or returns a new IDENT token *)
  let create_token lexbuf =
    let str = lexeme lexbuf in
    try (Hashtbl.find symbol_table str)
    with _ -> IDENT str
    
  let start_lex = ref (Range.start_of_range Range.norange)
  let start_pos_of_lexbuf lexbuf : pos =
    (Range.pos_of_lexpos (lexeme_start_p lexbuf))
    
  let lex_long_range lexbuf : Range.t =
    let end_p = lexeme_end_p lexbuf in
    mk_range end_p.pos_fname (!start_lex) (pos_of_lexpos end_p)  

}

let lc = ['a'-'z']
let uc = ['A'-'Z']
let letter = uc | lc
let digit = ['0'-'9']
let newline = '\n' | ('\r' '\n') | '\r'
let whitespace = ['\t' ' ']

rule
  token = parse
  | eof { EOF }
  | "#"                            { line_comment lexbuf}
  | "(*"                           { start_lex := start_pos_of_lexbuf lexbuf; comments 0 lexbuf }
  | whitespace+                    { token lexbuf }
  | newline                        { newline lexbuf; token lexbuf }
  | "(" | ")" | "{" | "}"
  | "," | ";" | ":"                { create_token lexbuf }
  | letter (digit | letter | '_')* { create_token lexbuf }
  | _ as c                         { unexpected_char lexbuf c }
and comments level = parse
  | "*)" { if level = 0 then token lexbuf
	   else comments (level-1) lexbuf }
  | "(*" { comments (level+1) lexbuf}
  | [^ '\n'] { comments level lexbuf }
  | "\n" { newline lexbuf; comments level lexbuf }
  | eof	 { raise (Lexer_error (lex_long_range lexbuf,
             Printf.sprintf "unclosed comment")) }
and line_comment = parse
  | ['\n' '\r']                 { token lexbuf }
  | _                           { line_comment lexbuf }
  | eof                         { EOF }