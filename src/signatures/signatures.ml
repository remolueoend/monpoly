(*
This module provides functions and data structures to handle signature declarations
from signature files.
*)

open Range
open Signature_ast
open CMFOTL

(* is raised if the same type is declared multiple times. Contains the name of the type. *)
exception DuplicateType of string * string

(* Gets raised if a reference to an unknown type was found. *)
exception UnknownType of string * string

(* Gets raised whenever a cyclic type structure is encountered, which is currently not supported. *)
exception RecursiveType of string * string

(* Gets raised whenever a record field is of a type marked as top level. This is currently not supported. *)
exception NestedTopLevelType of string * string * string

(* Gets raised whenever the type of a predicate argument is not valid (e.g. not of primitive type). *)
exception InvalidPredicateArgsType of string * string * string

(** Returns the constructor/predicate name of the given declaration *)
let decl_name = function
  | Predicate {elt= name, _; _} -> name
  | ProductSort (_, {elt= name, _; _}) -> name

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
    | ProductSort (_, {elt; _}) -> elt

  (** returns whether or not the given json object matches the given record type declaration. 
    Assumes that the fields of the json object are sorted alphanumerically. *)
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
                 | `Int _, TInt -> true
                 | `Float _, TFloat -> true
                 | `String _, TStr -> true
                 | `Assoc fs, TRef ctor ->
                     match_json signs (find_record_decl signs ctor) (`Assoc fs)
                 | _ -> false )
    | _ -> false

  (** Returns a signature declaration for the given JSON object.
    Raises an error if either the given JSON object is not a record
    or no matching type declaration could be found.
    Only signatures declared as events are considered.
    This function requires the signature declarations passed as table AND list *)
  let signature_from_json (signatures : signatures) (table : t)
      (json : Yojson.Basic.t) : record_decl option =
    let open Yojson.Basic in
    match json with
    | `Assoc _ -> (
        let first =
          List.find_opt
            (fun d ->
              match d with
              | ProductSort ({event= true; _}, {elt; _}) ->
                  match_json table elt json
              | _ -> false )
            signatures in
        match first with
        | Some (ProductSort (_, {elt; _})) -> Some elt
        | _ -> None )
    | t ->
        failwith
        @@ Printf.sprintf "Unsupported JSON root type: %s" (to_string t)
end

module TypeMap = Map.Make (String)
module TypeSet = Set.Make (String)
module TypeDeps = Map.Make (String)

(** Typechecks a list of signature declarations. It makes sure that:
    1. No type is declared twice.
    2. All references to complex types are valid.
    3. No field of any sort is of a top-level type (no nested top-level types allowed).
    4. Arguments of predicates are of primitive types.
    5. No recursive record types. *)
let typecheck (signatures : signatures) : unit =
  let string_of_deps deps =
    TypeDeps.fold
      (fun n d acc ->
        (n ^ ": " ^ (TypeSet.elements d |> String.concat ",")) :: acc )
      deps []
    |> String.concat "\n" in
  (* returns true whenever the provided type dependency graph is cyclic. *)
  let rec is_cyclic (deps : TypeSet.t TypeDeps.t) : bool =
    (* Printf.eprintf "====:\n%s\n" (string_of_deps deps) ; *)
    if TypeDeps.is_empty deps then false
    else
      match
        (* find first type which has no dependents. If none can be found, graph is cyclic: *)
        TypeDeps.filter (fun _ d -> TypeSet.is_empty d) deps
        |> TypeDeps.find_first_opt (fun _ -> true)
      with
      | None -> true
      | Some (next, _) ->
          (* remove type from all its dependents and remove type from graph itself: *)
          let deps' =
            TypeDeps.filter_map
              (fun t d ->
                if next == t then None else Some (TypeSet.remove next d) )
              deps in
          is_cyclic deps' in
  (* collect the constructor names of all declared complex types: *)
  let reg_type set decl =
    let reg name attrs loc =
      if TypeMap.mem name set then
        raise (DuplicateType (name, string_of_range loc))
      else TypeMap.add name attrs set in
    match decl with
    | ProductSort (attrs, {elt= name, _; loc}) -> reg name attrs loc
    | _ -> set in
  let type_map = List.fold_left reg_type TypeMap.empty signatures in
  (* valideates the type of a field, i.e. the type is known and not a top-level type.
     if field type is a record type, add an entry to the target type in the dependency graph. *)
  let typecheck_field deps (loc : Range.t) sort_name fname = function
    | TRef ctor -> (
      match TypeMap.find_opt ctor type_map with
      | Some {event= true; _} ->
          raise (NestedTopLevelType (sort_name, fname, string_of_range loc))
      | Some _ ->
          TypeDeps.update ctor
            (function
              | Some srcs -> Some (TypeSet.add sort_name srcs)
              | None -> Some (TypeSet.singleton sort_name) )
            deps
      | None -> raise (UnknownType (ctor, string_of_range loc)) )
    | _ -> deps in
  (* make sure all predicate arguments are of primitive type *)
  let typecheck_predicate_decl name args =
    List.iter
      (fun {elt= {aname; atyp}; loc} ->
        match atyp with
        | TRef _ ->
            raise (InvalidPredicateArgsType (name, aname, string_of_range loc))
        | TInt | TFloat | TStr | TRegexp -> () )
      args in
  (* typecheck all fields of a record type and build up type dependencies.  *)
  let typecheck_record_decl deps ((sort_name, fields) : record_decl) =
    List.fold_left
      (fun deps {elt= {ftyp; fname}; loc} ->
        typecheck_field deps loc sort_name fname ftyp )
      deps fields in
  (* iterate over all signature declarations and build up type dependencies.
     The generated dependency graph is stored as a map from record type -> set of dependent types. *)
  let init_deps =
    TypeMap.bindings type_map
    |> List.map (fun (n, _) -> (n, TypeSet.empty))
    |> List.to_seq |> TypeDeps.of_seq in
  let deps =
    List.fold_left
      (fun deps s ->
        match s with
        | Predicate {elt= name, args; _} ->
            typecheck_predicate_decl name args ;
            deps
        | ProductSort (_, {elt= name, fields; _}) ->
            typecheck_record_decl deps (name, fields) )
      init_deps signatures in
  if is_cyclic deps then raise (RecursiveType ("", "")) ;
  ()

(** Returns a new DB schema for a given list of signature declarations *)
let to_dbschema (signatures : signatures) : Db.schema =
  List.fold_left
    (fun schema signature ->
      match signature with
      | Predicate {elt= name, args; _} ->
          Db.add_predicate name
            ( extr_nodes args
            |> List.map (fun {aname; atyp} -> (aname, compile_tcst atyp)) )
            schema
      | ProductSort (_, {elt= name, fields; _}) ->
          let cols =
            List.map
              (fun {elt= {fname; ftyp}; _} -> (fname, compile_tcst ftyp))
              fields in
          Db.add_predicate name (("id", TInt) :: cols) schema )
    Db.base_schema signatures

(** parses the signature file at the given path. *)
let parse_signature_file (fname : string) : signatures =
  let ic = open_in fname in
  let lexbuf = Lexing.from_channel ic in
  let schema =
    try
      Lexing.set_filename lexbuf fname ;
      let parsed_signatures =
        Signature_parser.signatures Signature_lexer.token lexbuf in
      let signatures = Signature_ast.transpile_signatures parsed_signatures in
      (let _ = typecheck signatures in
       if Misc.debugging Dbg_signatures then
         Printf.eprintf "[Signatures]: Parsed signatures after transpiling:\n%!" ;
       List.iter
         (fun d -> Printf.eprintf "%s\n%!" (string_of_decl d))
         signatures ) ;
      signatures
    with Signature_parser.Error ->
      failwith
      @@ Printf.sprintf "Parse error at: %s"
           (Range.string_of_range (Range.lex_range lexbuf)) in
  close_in ic ; schema

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
