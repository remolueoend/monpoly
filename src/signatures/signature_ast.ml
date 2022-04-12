(*
This module consists of data structures describing the declaration of signatures
in a signature file. They can be constructed using functions located at `./signatures.ml`
*)


(** represents a token with a location (for better error reporting) *)
type 'a node = {elt: 'a; loc: Range.t}
let extr_node ({elt; _} : 'a node) : 'a = elt
let extr_nodes (nodes : 'a node list) : 'a list = List.map extr_node nodes
let no_node (elt : 'a) : 'a node = {elt; loc= ("", (0, 0), (0, 0))}

type ty = TInt | TStr | TFloat | TRegexp | TRef of string

(** returns a new node for the given start- & end position, wrapping the given element. *)
let loc (startpos : Lexing.position) (endpos : Lexing.position) (elt : 'a) :
    'a node =
  {elt; loc= Range.mk_lex_range startpos endpos}

type record_field = {fname: string; ftyp: ty}
type record_decl = string * record_field node list
type pred_arg = {aname: string; atyp: ty}
type pred_decl = string * pred_arg node list

(** represents a top level declaration in a signature.
    Either a predicate (e.g. q(int, string)) or a complex type. *)
type decl = Predicate of pred_decl node | Record of record_decl node

(** top level type of a signature file: Represents a flat list of declarations. *)
type signatures = decl list
