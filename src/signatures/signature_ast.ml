open Range

(** represents a token with a location (for better error reporting) *)
type 'a node = { elt : 'a; loc : Range.t }

type native_ty =
| TBool
| TFloat
| TInt
| TString

(** represents a type which is either native (int, string, ...) or complex (referencing the name of its constructor) *)
type ty =
| Native of native_ty
| Complex of string

type record_field = { fname : string; ftyp : ty }
type record_decl = string * record_field list
type pred_arg = {aname: string; atyp: native_ty}
type pred_decl = string * pred_arg list

(** represents a top level declaration in a signature.
    Either a predicate (e.g. q(int, string)) or a complex type. *)
type decl =
| Predicate of pred_decl node
| Record of record_decl node

(** top level type of a signature file: Represents a flat list of declarations. *)
type signatures = decl list

(** returns a new node for the givne start- & end position, wrapping the given element. *)
let loc (startpos:Lexing.position) (endpos:Lexing.position) (elt:'a) : 'a node =
  { elt ; loc=Range.mk_lex_range startpos endpos }
  
(** functions for stringifying AST types *)
let rec string_of_ty ty =
  match ty with
  | Complex cty -> cty
  | Native nty ->
    match nty with
    | TBool -> "TBool"
    | TFloat -> "TFloat"
    | TInt -> "TInt"
    | TString -> "TString"
  
let string_of_record ((id, fields): record_decl) =
  let field_to_str ({fname; ftyp}) = Printf.sprintf "%s: %s" fname (string_of_ty ftyp) in
  let fields_to_str = List.map field_to_str fields |> String.concat ", " in
  Printf.sprintf "%s = {%s}" id fields_to_str
  
let string_of_predicate ((id, args): pred_decl) =
  let arg_to_str ({aname; atyp}) =
    let ty_str = string_of_ty (Native atyp) in
    if String.length aname = 0 then Printf.sprintf "%s" ty_str else Printf.sprintf "%s: %s" aname ty_str
  in
  let args_to_str = List.map arg_to_str args |> String.concat ", " in
  Printf.sprintf "%s(%s)" id args_to_str
  
let string_of_signature signature =
  match signature with
  | Predicate n -> string_of_predicate n.elt
  | Record n -> string_of_record n.elt