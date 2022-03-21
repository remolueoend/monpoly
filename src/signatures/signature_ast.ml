open Range

(** is raised if the same type is declared multiple times. Contains the name of the type. *)
exception DuplicateType of string
(** Gets raised if a reference to an unknown type was found. *)
exception UnknownType of string

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
type record_decl = string * record_field node list
type pred_arg = {aname: string; atyp: native_ty}
type pred_decl = string * pred_arg node list

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
  let reg_type set decl =
    let reg name loc = if TypeSet.mem name set
      then raise (DuplicateType (Printf.sprintf "Duplicated type %s at %s" name (string_of_range loc)))
      else TypeSet.add name set in
    match decl with
    | Predicate {elt=(name, _); loc} -> reg name loc
    | Record {elt=(name, _); loc} -> reg name loc
  in
  let type_set = List.fold_left reg_type TypeSet.empty signatures in
  (* iterate over all fields of record types and lookup their complex types:  *)
  signatures |> List.iter (function 
  | Predicate _ -> ()
  | Record {elt=(name, fields); _} -> fields |> List.iter (fun {elt={fname; ftyp}; loc} ->
    match ftyp with
    | Native _ -> ()
    | Complex ctor -> if TypeSet.mem ctor type_set = false then raise (UnknownType (Printf.sprintf "Unknown type %s at %s" ctor (string_of_range loc)))
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
  let field_to_str {elt={fname; ftyp};_} = Printf.sprintf "%s: %s" fname (string_of_ty ftyp) in
  let fields_to_str = List.map field_to_str fields |> String.concat ", " in
  Printf.sprintf "%s = {%s}" id fields_to_str
  
let string_of_predicate ((id, args): pred_decl) =
  let arg_to_str {elt={aname; atyp}; _} =
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
let%test_module "typecheck tests" = (module struct

  exception AssertException of string

  let assert_str (actual: string) (expected : string) : unit =
    if compare actual expected = 0
      then ()
      else raise (AssertException (Printf.sprintf "Expected: %s\nActual: %s" expected actual))

  let%test_unit "typecheck throws on duplicated types" =
    let decls = [
      Record ( dum_node ("SomeType", []));
      Record ( {elt=("SomeType", []); loc=mk_range "f.sig" (mk_pos 1 1) (mk_pos 1 10) });
    ] in
    try typecheck decls; raise (AssertException "Test did not throw")
    with DuplicateType msg -> assert_str msg "Duplicated type SomeType at f.sig:[1.1-1.10]"

  let%test_unit "typecheck can resolve type references" =
    let decls = [
      Record ( dum_node ("SomeType", [dum_node {fname="f1"; ftyp=Complex "AnotherType"}]));
      Record ( dum_node ("AnotherType", []))
    ] in
    typecheck decls

  let%test_unit "throws if unknown type reference is detected" =
    let decls = [
      Record ( dum_node ("SomeType", [{elt={fname="f1"; ftyp=Complex "TypeA"}; loc=("f.sig", mk_pos 2 42, mk_pos 2 45)}]));
      Record ( dum_node ("AnotherType", []))
    ] in
    try typecheck decls; raise (AssertException "Test did not throw")
    with UnknownType msg -> assert_str msg "Unknown type TypeA at f.sig:[2.42-2.45]"
end)