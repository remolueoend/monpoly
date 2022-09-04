open Lexing

(* Helper module to handle location information of the lexer *)

type pos = int * int (* Line number and column *)

type t = string * pos * pos

let mk_pos line col : pos = (line, col)
let start_of_range ((_, s, _) : t) = s
let mk_range f s e : t = (f, s, e)
let valid_pos ((l, c) : pos) = l >= 0 && c >= 0

let string_of_range ((f, (sl, sc), (el, ec)) : t) =
  Printf.sprintf "%s:[%d.%d-%d.%d]" f sl sc el ec

let norange = ("__internal", (0, 0), (0, 0))

(* Creates a Range.pos from the Lexing.position data *)
let pos_of_lexpos (p : position) : pos =
  mk_pos p.pos_lnum (p.pos_cnum - p.pos_bol)

let mk_lex_range (p1 : position) (p2 : position) : t =
  mk_range p1.pos_fname (pos_of_lexpos p1) (pos_of_lexpos p2)

(* Expose the lexer state as a Range.t value *)
let lex_range lexbuf : t =
  mk_lex_range (lexeme_start_p lexbuf) (lexeme_end_p lexbuf)
