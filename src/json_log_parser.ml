open Signatures

let ts_path : string option ref = ref None

type parsebuf =
  { pb_lexbuf: Lexing.lexbuf
  ; signature_table: SignTable.t
  ; mutable pb_token: Json_log_lexer.token
  ; mutable pb_schema: Table.schema
  ; mutable id_index: int }

let init_parsebuf lexbuf signatures =
  { pb_lexbuf= lexbuf
  ; signature_table= SignTable.of_signatures signatures
  ; pb_token= Json_log_lexer.token lexbuf
  ; pb_schema= ("", [])
  ; id_index= 0 }

let string_of_token (t : Json_log_lexer.token) =
  match t with
  | AT -> "'@'"
  | TS ts -> Z.to_string ts
  | JSON json -> "\"" ^ String.escaped json ^ "\""
  | EOF -> "<EOF>"

(** Parses the given json record by registering each found DB tuple recursively
    using the provided `reg_tuple` function. The returned integer is equal to the unique instance ID
    assigned to the top-level record instance.
    `reg_tuple` is called with the name of the signature declaration and the list of values.

    This function mutates `pb.id_index`. *)
let rec parse_record (pb : parsebuf) (reg_tuple : string -> string list -> unit)
    ((ctor, rec_fields) : Signature_ast.record_decl) (json : Yojson.Basic.t) :
    string =
  let open Signature_ast in
  let open Yojson.Basic in
  let json_fields =
    match json with
    | `Assoc value -> value
    | _ -> failwith "Invalid json value type" in
  let get_field_value ({fname; ftyp} : record_field) : string =
    let json_value = List.assoc fname json_fields in
    match ftyp with
    | Native _ -> json_value |> Yojson.Basic.to_string
    | Complex ctor ->
        parse_record pb reg_tuple
          (SignTable.find_record_decl pb.signature_table ctor)
          json_value in
  let tuple_values = List.map get_field_value (extr_nodes rec_fields) in
  let inst_id = Int.to_string pb.id_index in
  pb.id_index <- pb.id_index + 1 ;
  reg_tuple ctor (inst_id :: tuple_values) ;
  inst_id

let next pb = pb.pb_token <- Json_log_lexer.token pb.pb_lexbuf

(** Creates a parser which is capable of parsing log files consisting of
    lines of JSON strings. *)
module Make (C : Log_parser.Consumer) = struct
  let parse (dbschema : Db.schema) (lexbuf : Lexing.lexbuf) (ctxt : C.t)
      signatures : bool =
    let pb = init_parsebuf lexbuf signatures in
    let debug msg =
      if Misc.debugging Misc.Dbg_log then
        Printf.eprintf "[Json_log_parser] state %s with token=%s\n" msg
          (string_of_token pb.pb_token)
      else () in
    let fail msg =
      debug "fail" ;
      C.parse_error ctxt pb.pb_lexbuf.Lexing.lex_start_p msg ;
      if Misc.debugging Misc.Dbg_log then
        Printf.eprintf "[Json_log_parser] failed with message %s" msg
      else () ;
      failwith "parser failed" in
    let rec parse_init () =
      debug "init" ;
      match pb.pb_token with
      | EOF -> parse_eof ()
      | AT -> next pb ; parse_ts ()
      (* TODO: allow JSON without @timestamp: | JSON _ -> parse_json () *)
      | t -> fail ("Expected '@' or JSON but saw " ^ string_of_token t)
    and parse_ts () =
      debug "ts" ;
      match pb.pb_token with
      | TS ts -> C.begin_tp ctxt ts ; next pb ; parse_json ()
      | t -> fail ("Expected timestamp but saw " ^ string_of_token t)
    and parse_json () =
      let open Yojson.Basic in
      debug "json" ;
      pb.id_index <- 0 ;
      match pb.pb_token with
      | JSON str ->
          let json = sort (Yojson.Basic.from_string str) in
          let signature_decl =
            SignTable.get_signature_from_json signatures pb.signature_table json
          in
          let _ =
            match signature_decl with
            | None -> ()
            | Some decl ->
                ignore
                @@ parse_record pb
                     (fun ctor values ->
                       C.tuple ctxt (ctor, List.assoc ctor dbschema) values )
                     decl json in
          C.end_tp ctxt ; next pb ; parse_init ()
      | t -> fail ("Expected JSON but saw " ^ string_of_token t)
    and parse_eof () = debug "EOF" ; () in
    parse_init () ; true
end
