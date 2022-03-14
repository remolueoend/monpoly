open Range

(** represents a token with a location (for better error reporting) *)
type 'a node = { elt : 'a; loc : Range.t }

type ty =
| TBool
| TFloat
| TInt
| TRef of rty
| TString
and rty =
| RRecord of string

type field = { fname : string; ftyp : ty }

type decl =
| Predicate of (string * (field list)) node
| Record of (string * (field list)) node

type signatures = decl list

(** returns a new node for the givne start- & end position, wrapping the given element. *)
let loc (startpos:Lexing.position) (endpos:Lexing.position) (elt:'a) : 'a node =
  { elt ; loc=Range.mk_lex_range startpos endpos }
  
(** functions for stringifying AST types *)
let rec string_of_ty ty =
  match ty with
  | TBool -> "TBool"
  | TFloat -> "TFloat"
  | TInt -> "TInt"
  | TString -> "TString"
  | TRef ty -> Printf.sprintf "Ctor[%s]" (string_of_rty ty)
and string_of_rty ty =
  match ty with
  | RRecord id -> Printf.sprintf "%s" id
  
let string_of_record ({elt=(id, fields); _}: (string * (field list)) node) =
  let field_to_str ({fname; ftyp}) = Printf.sprintf "%s: %s" fname (string_of_ty ftyp) in
  let fields_to_str = List.map field_to_str fields |> String.concat ", " in
  Printf.sprintf "%s = {%s}" id fields_to_str
  
let string_of_predicate ({elt=(id, fields); _}) =
  let arg_to_str ({fname; ftyp}) =
    let ty_str = string_of_ty ftyp in
    if String.length fname = 0 then Printf.sprintf "%s" ty_str else Printf.sprintf "%s: %s" fname ty_str
  in
  let args_to_str = List.map arg_to_str fields |> String.concat ", " in
  Printf.sprintf "%s(%s)" id args_to_str
  
let string_of_signature signature =
  match signature with
  | Predicate n -> string_of_predicate n
  | Record n -> string_of_record n