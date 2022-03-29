open Signatures

let ts_path : string option ref = ref None

type parsebuf =
  { pb_lexbuf: Lexing.lexbuf
  ; signature_table: SignTable.t
  ; mutable pb_token: Json_log_lexer.token
  ; mutable pb_schema: Table.schema }

let init_parsebuf lexbuf signatures =
  { pb_lexbuf= lexbuf
  ; signature_table= SignTable.of_signatures signatures
  ; pb_token= Json_log_lexer.token lexbuf
  ; pb_schema= ("", []) }

let string_of_token (t : Json_log_lexer.token) =
  match t with
  | AT -> "'@'"
  | TS ts -> Z.to_string ts
  | JSON json -> "\"" ^ String.escaped json ^ "\""
  | EOF -> "<EOF>"

let json_ast_from_token (json_str : string) : Yojson.Basic.t =
  let parsed : Yojson.Basic.t = Yojson.Basic.from_string json_str in
  if Misc.debugging Misc.Dbg_log then
    Printf.eprintf "[Json_log_parser]: parsed JSON: %s\n"
    @@ Yojson.Basic.to_string parsed
  else () ;
  parsed

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
      let _ =
        match pb.pb_token with
        | JSON str -> (
            let json = json_ast_from_token str in
            let rec_decl =
              SignTable.get_record_decl_from_json (sort json) signatures
                pb.signature_table in
            match rec_decl with
            | None -> Printf.eprintf "[Json_log_parser] No matching type found"
            | Some decl ->
                Printf.eprintf "[Json_log_parser] Found matching type: %s"
                  (Signatures.string_of_record decl) )
        | t -> fail ("Expected JSON but saw " ^ string_of_token t) in
      C.end_tp ctxt ; next pb ; parse_init ()
    and parse_eof () = debug "EOF" ; () in
    parse_init () ; true
end
