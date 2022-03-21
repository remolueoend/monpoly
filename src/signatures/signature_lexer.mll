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
    ("bool", TBOOL);
    
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
  | whitespace+                    { token lexbuf }
  | newline                        { newline lexbuf; token lexbuf }
  | "(" | ")" | "{" | "}"
  | "," | ";" | ":"                { create_token lexbuf }
  | letter (digit | letter | '_')* { create_token lexbuf }
  | _ as c                         { unexpected_char lexbuf c }