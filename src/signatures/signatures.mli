open Signature_ast

(** Signature table module: provides functions to work with parsed signature definitions. *)
module SignTable : sig
  type t = (string, decl) Hashtbl.t

  val of_signatures : signatures -> t
  (** returns a new signature table from the given list of declarations *)

  val find_record_decl : t -> string -> record_decl
  (** Returns the record declaration with the given constructor name from the given signature table.
    Raises an error if the ctor could not be found or does not describe a record type. *)

  val signature_from_json :
    signatures -> t -> Yojson.Basic.t -> record_decl option
  (** Returns a signature declaration for the given JSON object.
    Raises an error if either the given JSON object is not a record
    or no matching type declaration could be found.
    Only signatures declared as events are considered.
    This function requires the signature declarations passed as table AND list *)
end

val parse_signature_file : string -> signatures
(** Returns the parsed signatures from a given signature file path. *)

val to_dbschema : signatures -> Db.schema
(** Returns a new DB schema for a given list of signature declarations *)
