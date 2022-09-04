(** represents a token with a location (for better error reporting) *)
type 'a node = {elt: 'a; loc: Range.t}

val loc : Lexing.position -> Lexing.position -> 'a -> 'a node
(** returns a node containing an element and its given start and end position.
	Used for storing the position of parsed tokens. *)

type record_field = {fname: string; ftyp: ty}
and record_decl = string * record_field node list
and pred_arg = {aname: string; atyp: ty}
and pred_decl = string * pred_arg node list
and ty = TInt | TStr | TFloat | TRegexp | TRef of string | TBool | TNull

(** Describes several attributes of a record declared in a signature:
    1. inline: tags records which have been declared as inline types in the signature file
       and have been extracted.
    2. event: tags  predicates which are considered when matching against top-level JSON log entries. *)
type product_attrs = {inline: bool; event: bool}

(** represents a top level declaration in a signature.
    Either a predicate (e.g. q(int, string)) or a record type *)
type decl =
  | Predicate of pred_decl node
  | ProductSort of product_attrs * record_decl node

(** top level type of a signature file: Represents a flat list of declarations. *)
type signatures = decl list

val string_of_ty : ty -> string
val extr_nodes : 'a node list -> 'a list

(** This module and its types represent the AST of a signature file content.
	It usually needs to be transpiled before used, e.g. by calling `transpile_signature`. *)
module ParseTree : sig
  type record_field = {fname: string; ftyp: ty}
  and record_decl = string * record_field node list
  and pred_arg = {aname: string; atyp: ty}
  and pred_decl = string * pred_arg node list

  and ty =
    | TInt
    | TStr
    | TFloat
    | TRegexp
    | TBool
    | TNull
    | TRef of string
    | TInline of record_field list

  type decl =
    | Predicate of pred_decl node
    (* the first element is true whenever the record is an event predicate. *)
    | Record of (bool * record_decl node)

  type signatures = decl list
end

val transpile_signatures : ParseTree.signatures -> signatures
(** transforms a parsed signature AST to a signature *)

val string_of_decl : decl -> string