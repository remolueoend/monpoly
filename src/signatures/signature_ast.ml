open Range

(** is raised if the same type is declared multiple times. Contains the name of the type. *)
exception DuplicateType of string
(** Gets raised if a reference to an unknown type was found.
    Contains the location (Ctor and field name) of the reference and the name of the unknown type. *)
exception UnknownType of string * string * string

(** represents a token with a location (for better error reporting) *)
type 'a node = { elt : 'a; loc : Range.t }
let dum_node (elt : 'a) : 'a node = {elt=elt; loc=("", (0, 0), (0, 0))}

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


module TypeSet = Set.Make(String)
(** Typechecks a list of signature declarations. It makes sure that:
    1. No type is declared twice 
    2. All references to complex types are valid *)
let typecheck (signatures: signatures) : unit =
  (* collect the constructor names of all declared complex types: *)
  let reg_type decl set =
    let reg name = if TypeSet.mem name set then raise (DuplicateType name) else TypeSet.add name set in
    match decl with
    | Predicate {elt=(name, _); _} -> reg name
    | Record {elt=(name, _); _} -> reg name
  in
  let type_set = List.fold_right reg_type signatures TypeSet.empty in
  (* iterate over all fields of record types and lookup their complex types:  *)
  signatures |> List.iter (function 
  | Predicate _ -> ()
  | Record {elt=(name, fields); _} -> fields |> List.iter (fun {fname; ftyp} ->
    match ftyp with
    | Native _ -> ()
    | Complex ctor -> if TypeSet.mem ctor type_set = false then raise (UnknownType (name, fname, ctor))
    )
  )

  
(* **** STRING_OF FUNCTIONS FOR AST OBJECTS **** *)
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
  
  
(* **** INLINE TESTS **** *)
let%test "typecheck throws on duplicated types" =
  let decls = [
    Record ( dum_node ("DuplicatedType", []));
    Record ( dum_node ("DuplicatedType", []))
  ] in
  try typecheck decls; false
  with DuplicateType ctor -> String.compare ctor "DuplicatedType" = 0

let%test_unit "typecheck can resolve type references" =
  let decls = [
    Record ( dum_node ("SomeType", [{fname="f1"; ftyp=Complex "AnotherType"}]));
    Record ( dum_node ("AnotherType", []))
  ] in
  typecheck decls

let%test "throws if unknown type reference is detected" =
  let decls = [
    Record ( dum_node ("SomeType", [{fname="f1"; ftyp=Complex "UnknownType"}]));
    Record ( dum_node ("AnotherType", []))
  ] in
  try typecheck decls; false
  with UnknownType (p, f, ctor) -> compare p "SomeType" = 0 && 
                                   compare f "f1" = 0 &&
                                   compare ctor "UnknownType" = 0