(*
This module consists of data structures describing the declaration of signatures
in a signature file. They can be constructed using functions located at `./signatures.ml`
*)

(** represents a token with a location (for better error reporting) *)
type 'a node = {elt: 'a; loc: Range.t}

let extr_node ({elt; _} : 'a node) : 'a = elt
let extr_nodes (nodes : 'a node list) : 'a list = List.map extr_node nodes
let no_node (elt : 'a) : 'a node = {elt; loc= ("", (0, 0), (0, 0))}

(** returns a new node for the given start- & end position, wrapping the given element. *)
let loc (startpos : Lexing.position) (endpos : Lexing.position) (elt : 'a) :
    'a node =
  {elt; loc= Range.mk_lex_range startpos endpos}

type record_field = {fname: string; ftyp: ty}
and record_decl = string * record_field node list
and pred_arg = {aname: string; atyp: ty}
and pred_decl = string * pred_arg node list
and ty = TInt | TStr | TFloat | TRegexp | TRef of string

(** represents a top level declaration in a signature.
    Either a predicate (e.g. q(int, string)) or a record type (named or inlined) *)
type decl = Predicate of pred_decl node | Record of bool * record_decl node

(** top level type of a signature file: Represents a flat list of declarations. *)
type signatures = decl list

(** The types of this module are the results of parsing the signature file.
    The signatures used throughout the application need to be transpiled fist:
    1. INLINE TYPES:
       All inline types are extracted and stored in the resulting signatures
       as named types. *)
module ParseTree = struct
  type record_field = {fname: string; ftyp: ty}
  and record_decl = string * record_field node list
  and pred_arg = {aname: string; atyp: ty}
  and pred_decl = string * pred_arg node list

  and ty =
    | TInt
    | TStr
    | TFloat
    | TRegexp
    | TRef of string
    | TInline of record_field list

  type decl = Predicate of pred_decl node | Record of record_decl node
  type signatures = decl list
end

(** transpiles signatures from ParseTree.signatures to Signature_ast.signatures. *)
let transpile_signatures (s : ParseTree.signatures) : signatures =
  let sort_fields =
    let open ParseTree in
    List.sort (fun {fname= f1; _} {fname= f2; _} -> compare f1 f2) in
  let transpile_ty (ty : ParseTree.ty) : ty =
    match ty with
    | TInt -> TInt
    | TStr -> TStr
    | TFloat -> TFloat
    | TRegexp -> TRegexp
    | TRef ctor -> TRef ctor
    | TInline _ -> failwith "not valid" in
  (* Transforms every field in the given list and returns:
      1. A new list of fields in the same order replacing the given ones.
      2. A list of generated signatures which need to be attached to the existing ones,
         where all fields are ordered alphabetically. *)
  let rec extract_inline_types (pref : string)
      (fields : ParseTree.record_field node list) :
      record_field node list * signatures =
    List.fold_right
      (fun ({elt= {fname; ftyp}; loc} : ParseTree.record_field node) (fs, s) ->
        match ftyp with
        | TInline in_fields ->
            let extr_type_name = pref ^ "_" ^ fname in
            let extr_type_fields, new_sigs =
              extract_inline_types extr_type_name
                (List.map no_node (sort_fields in_fields)) in
            let extracted_decl : record_decl =
              (extr_type_name, extr_type_fields) in
            let new_field = no_node {fname; ftyp= TRef extr_type_name} in
            ( new_field :: fs
            , s @ (Record (true, no_node extracted_decl) :: new_sigs) )
        | _ -> ({elt= {fname; ftyp= transpile_ty ftyp}; loc} :: fs, s) )
      fields ([], []) in
  List.fold_left
    (fun acc (s : ParseTree.decl) ->
      match s with
      | Predicate {elt= name, args; loc} ->
          Predicate
            { elt=
                ( name
                , List.map
                    (fun ({elt= {aname; atyp}; loc} : ParseTree.pred_arg node) ->
                      {elt= {aname; atyp= transpile_ty atyp}; loc} )
                    args )
            ; loc }
          :: acc
      | Record {elt= name, fields; loc} ->
          let new_fields, sigs = extract_inline_types name fields in
          sigs @ (Record (false, {elt= (name, new_fields); loc}) :: acc) )
    [] s

(* **** STRING_OF FUNCTIONS FOR AST OBJECTS **** *)
let string_of_ty = function
  | TInt -> "TInt"
  | TStr -> "TStr"
  | TFloat -> "TFloat"
  | TRegexp -> "TRegexp"
  | TRef ctor -> ctor

let string_of_record (inline : bool) ((id, fields) : record_decl) =
  let field_to_str {elt= {fname; ftyp}; _} =
    Printf.sprintf "%s: %s" fname (string_of_ty ftyp) in
  let fields_to_str = List.map field_to_str fields |> String.concat ", " in
  let prefix = if inline then "[inline] " else "" in
  Printf.sprintf "%s%s = {%s}" prefix id fields_to_str

let string_of_predicate ((id, args) : pred_decl) =
  let arg_to_str {elt= {aname; atyp}; _} =
    let ty_str = string_of_ty atyp in
    if String.length aname = 0 then Printf.sprintf "%s" ty_str
    else Printf.sprintf "%s: %s" aname ty_str in
  let args_to_str = List.map arg_to_str args |> String.concat ", " in
  Printf.sprintf "%s(%s)" id args_to_str

let string_of_signature signature =
  match signature with
  | Predicate n -> string_of_predicate n.elt
  | Record (inline, {elt; _}) -> string_of_record inline elt