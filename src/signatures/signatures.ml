(*
This module provides functions and data structures to handle signature declarations
from signature files.
*)

open Range
open Signature_ast

(* is raised if the same type is declared multiple times. Contains the name of the type. *)
exception DuplicateType of string

(* Gets raised if a reference to an unknown type was found. *)
exception UnknownType of string

let extr_node ({elt; _} : 'a node) : 'a = elt
let extr_nodes (nodes : 'a node list) : 'a list = List.map extr_node nodes
let no_node (elt : 'a) : 'a node = {elt; loc= ("", (0, 0), (0, 0))}

(** Returns the constructor/predicate name of the given declaration *)
let decl_name = function
  | Predicate {elt= name, _; _} -> name
  | Record {elt= name, _; _} -> name

(** Stores a map from declaration name to type declaration *)
module SignTable = struct
  type t = (string, decl) Hashtbl.t

  (** returns a new signature table from the given list of declarations *)
  let of_signatures (decls : decl list) : t =
    List.map (fun d -> (decl_name d, d)) decls |> List.to_seq |> Hashtbl.of_seq

  (** Returns the record declaration with the given constructor name from the given signature table.
    Raises an error if the ctor could not be found or does not describe a record type. *)
  let find_record_decl (signs : t) (ctor : string) : record_decl =
    match Hashtbl.find signs ctor with
    | Predicate _ ->
        failwith
        @@ Printf.sprintf "[find_record_decl]: %s is not a record type" ctor
    | Record {elt; _} -> elt

  (** returns whether or not the given json object matches the given record type declaration. 
    Assumes that the fields of the json object are sorted alphanumerically.
    TODO: return an actual tuple containing the matching values as an option *)
  let rec match_json (signs : t) ((record_name, record_fields) : record_decl)
      (json : Yojson.Basic.t) : bool =
    let open Yojson.Basic in
    match json with
    | `Assoc json_fields ->
        if List.length json_fields <> List.length record_fields then false
        else
          List.combine json_fields record_fields
          |> List.for_all (fun ((jf_name, jf_val), {elt= {fname; ftyp}; _}) ->
                 compare jf_name fname = 0
                 &&
                 match (jf_val, ftyp) with
                 | `Int _, Native TInt -> true
                 | `Float _, Native TFloat -> true
                 | `String _, Native TStr -> true
                 | `Assoc fs, Complex ctor ->
                     match_json signs (find_record_decl signs ctor) (`Assoc fs)
                 | _ -> false )
    | _ -> false

  (** Returns a signature declaration for the given JSON object.
    Raises an error if either the given JSON object is not a record
    or no matching type declaration could be found.
    This function requires the signature declarations passed as table AND list *)
  let get_signature_from_json (signatures : signatures) (table : t)
      (json : Yojson.Basic.t) : record_decl option =
    let open Yojson.Basic in
    match json with
    | `Assoc _ -> (
        let first =
          List.find_opt
            (fun d ->
              match d with
              | Record {elt; _} -> match_json table elt json
              | _ -> false )
            signatures in
        match first with
        | Some (Record {elt; _}) -> Some elt
        | None -> None
        | _ -> failwith "invalid match case" )
    | t -> raise @@ UnknownType (Printf.sprintf "Unsupported JSON root type: %s" (to_string t))
end

module TypeSet = Set.Make (String)

(** Typechecks a list of signature declarations. It makes sure that:
    1. No type is declared twice 
    2. All references to complex types are valid *)
let typecheck (signatures : signatures) : unit =
  (* collect the constructor names of all declared complex types: *)
  let reg_type set decl =
    let reg name loc =
      if TypeSet.mem name set then
        raise
          (DuplicateType
             (Printf.sprintf "Duplicated type %s at %s" name
                (string_of_range loc) ) )
      else TypeSet.add name set in
    match decl with
    | Predicate {elt= name, _; loc} -> reg name loc
    | Record {elt= name, _; loc} -> reg name loc in
  let type_set = List.fold_left reg_type TypeSet.empty signatures in
  (* make sure all complex type references are valid *)
  let typecheck_ty (loc : Range.t) = function
    | Native _ -> ()
    | Complex ctor ->
        if TypeSet.mem ctor type_set = false then
          raise
            (UnknownType
               (Printf.sprintf "Unknown type %s at %s" ctor
                  (string_of_range loc) ) ) in
  (* iterate over all fields of record types and lookup their complex types:  *)
  let typecheck_record_decl ((_, fields) : record_decl) : unit =
    List.iter (fun {elt= {ftyp; _}; loc} -> typecheck_ty loc ftyp) fields in
  (* iterate over all signature declarations and check them separately *)
  List.iter
    (function
      | Predicate _ -> ()
      | Record {elt= name, fields; _} -> typecheck_record_decl (name, fields) )
    signatures

(** Returns a new DB schema for a given list of signature declarations *)
let to_db_schema (signatures : signatures) : Db.schema =
  List.fold_left
    (fun schema signature ->
      match signature with
      | Predicate {elt= name, args; _} ->
          Db.add_predicate name
            (extr_nodes args |> List.map (fun {aname; atyp} -> (aname, atyp)))
            schema
      | Record {elt= name, fields; _} ->
          let cols =
            List.map
              (fun {elt= {fname; ftyp}; _} ->
                match ftyp with
                | Native t -> (fname, t)
                | Complex _ -> (fname, TInt) )
              fields in
          Db.add_predicate name (("id", TInt) :: cols) schema )
    Db.base_schema signatures

(** accepts the path to a signature file and returns a new DB schema for the specificed
    signature declarations in the given file. *)
let parse_signature_file (fname : string) : signatures =
  let ic = open_in fname in
  let lexbuf = Lexing.from_channel ic in
  let schema =
    try
      Lexing.set_filename lexbuf fname ;
      let signatures =
        Signature_parser.signatures Signature_lexer.token lexbuf in
      let _ = typecheck signatures in
      signatures
    with Signature_parser.Error ->
      failwith
      @@ Printf.sprintf "Parse error at: %s"
           (Range.string_of_range (Range.lex_range lexbuf)) in
  close_in ic ; schema

(* **** STRING_OF FUNCTIONS FOR AST OBJECTS **** *)
let rec string_of_ty ty =
  match ty with
  | Complex cty -> cty
  | Native nty -> (
    match nty with
    | TFloat -> "TFloat"
    | TInt -> "TInt"
    | TStr -> "TStr"
    | TRegexp -> "TRegexp" )

let string_of_record ((id, fields) : record_decl) =
  let field_to_str {elt= {fname; ftyp}; _} =
    Printf.sprintf "%s: %s" fname (string_of_ty ftyp) in
  let fields_to_str = List.map field_to_str fields |> String.concat ", " in
  Printf.sprintf "%s = {%s}" id fields_to_str

let string_of_predicate ((id, args) : pred_decl) =
  let arg_to_str {elt= {aname; atyp}; _} =
    let ty_str = string_of_ty (Native atyp) in
    if String.length aname = 0 then Printf.sprintf "%s" ty_str
    else Printf.sprintf "%s: %s" aname ty_str in
  let args_to_str = List.map arg_to_str args |> String.concat ", " in
  Printf.sprintf "%s(%s)" id args_to_str

let string_of_signature signature =
  match signature with
  | Predicate n -> string_of_predicate n.elt
  | Record n -> string_of_record n.elt

(* **** INLINE TESTS **** *)
(* let%test_module "typecheck tests" =
   ( module struct
     exception AssertException of string

     let assert_str (actual : string) (expected : string) : unit =
       if compare actual expected = 0 then ()
       else
         raise
           (AssertException
              (Printf.sprintf "Expected: %s\nActual: %s" expected actual) )

     let%test_unit "typecheck throws on duplicated types" =
       let decls =
         [ Record (no_node ("SomeType", []))
         ; Record
             { elt= ("SomeType", [])
             ; loc= mk_range "f.sig" (mk_pos 1 1) (mk_pos 1 10) } ] in
       try
         typecheck decls ;
         raise (AssertException "Test did not throw")
       with DuplicateType msg ->
         assert_str msg "Duplicated type SomeType at f.sig:[1.1-1.10]"

     let%test_unit "typecheck can resolve type references" =
       let decls =
         [ Record
             (no_node
                ("SomeType", [no_node {fname= "f1"; ftyp= Complex "AnotherType"}]) )
         ; Record (no_node ("AnotherType", [])) ] in
       typecheck decls

     let%test_unit "throws if unknown type reference is detected" =
       let decls =
         [ Record
             (no_node
                ( "SomeType"
                , [ { elt= {fname= "f1"; ftyp= Complex "TypeA"}
                    ; loc= ("f.sig", mk_pos 2 42, mk_pos 2 45) } ] ) )
         ; Record (no_node ("AnotherType", [])) ] in
       try
         typecheck decls ;
         raise (AssertException "Test did not throw")
       with UnknownType msg ->
         assert_str msg "Unknown type TypeA at f.sig:[2.42-2.45]"
   end ) *)
