open Signatures

let ts_path : string option ref = ref None

type parsebuf =
  { pb_lexbuf: Lexing.lexbuf
  ; signature_table: SignTable.t
  ; mutable pb_token: Json_log_lexer.token
  ; mutable pb_schema: Table.schema
  ; mutable id_index: int
  ; mutable input_line: int }

let init_parsebuf lexbuf signatures =
  { pb_lexbuf= lexbuf
  ; signature_table= SignTable.of_signatures signatures
  ; pb_token= Json_log_lexer.token lexbuf
  ; pb_schema= ("", [])
  ; id_index= 0
  ; input_line= 0 }

let string_of_token (t : Json_log_lexer.token) =
  match t with
  | AT -> "'@'"
  | TS ts -> Z.to_string ts
  | JSON json -> "\"" ^ String.escaped json ^ "\""
  | LPA -> "'('"
  | RPA -> "')'"
  | LCB -> "'{'"
  | RCB -> "'}'"
  | COM -> "','"
  | STR s -> "\"" ^ String.escaped s ^ "\""
  | CMD -> "'>'"
  | EOC -> "'<'"
  | EOF -> "<EOF>"

exception Local_error of string

let next pb = pb.pb_token <- Json_log_lexer.token pb.pb_lexbuf

let expect pb t =
  if pb.pb_token = t then next pb
  else
    raise
      (Local_error
         ( "Expected " ^ string_of_token t ^ " but saw "
         ^ string_of_token pb.pb_token ) )

let parse_string pb =
  match pb.pb_token with
  | STR s -> next pb ; s
  | t -> raise (Local_error ("Expected a string but saw " ^ string_of_token t))

let parse_int pb =
  let s = parse_string pb in
  try int_of_string s
  with Failure _ ->
    raise
      (Local_error ("Expected an integer but saw \"" ^ String.escaped s ^ "\""))

let parse_tuple pb =
  let rec more l =
    match pb.pb_token with
    | COM ->
        next pb ;
        let s = parse_string pb in
        more (s :: l)
    | RPA -> next pb ; List.rev l
    | t ->
        raise (Local_error ("Expected ',' or ')' but saw " ^ string_of_token t))
  in
  expect pb LPA ;
  match pb.pb_token with
  | RPA -> next pb ; []
  | STR s ->
      next pb ;
      more [s]
  | t ->
      raise
        (Local_error ("Expected a string or ')' but saw " ^ string_of_token t))

let parse_int_tuple pb =
  let t = parse_tuple pb in
  try List.map int_of_string t
  with Failure _ -> raise (Local_error "Expected a tuple of integers")

let parse_heavy pb =
  expect pb LPA ;
  let i = parse_int pb in
  expect pb COM ;
  let t = parse_tuple pb in
  expect pb RPA ; (i, t)

let parse_heavies pb =
  let rec more l =
    match pb.pb_token with
    | COM ->
        next pb ;
        let h = parse_heavy pb in
        more (h :: l)
    | _ -> List.rev l in
  expect pb LCB ;
  let h0 = parse_heavy pb in
  let hl = more [h0] in
  expect pb RCB ; Array.of_list hl

let parse_slices pb =
  let rec more l =
    match pb.pb_token with
    | COM ->
        next pb ;
        let t = Array.of_list (parse_int_tuple pb) in
        more (t :: l)
    | _ -> List.rev l in
  expect pb LCB ;
  let t0 = Array.of_list (parse_int_tuple pb) in
  let tl = more [t0] in
  expect pb RCB ; Array.of_list tl

let parse_slicing_params pb =
  expect pb LCB ;
  let heavies = parse_heavies pb in
  expect pb COM ;
  let shares = parse_slices pb in
  expect pb COM ;
  let seeds = parse_slices pb in
  expect pb RCB ; (heavies, shares, seeds)

let parse_command_params pb =
  match pb.pb_token with
  | LCB ->
      let p = parse_slicing_params pb in
      expect pb EOC ; Some (Helper.SplitSave p)
  | STR s -> next pb ; expect pb EOC ; Some (Helper.Argument s)
  | EOC -> next pb ; None
  | t ->
      raise
        (Local_error
           ("Expected a string, '{' or '<' but saw " ^ string_of_token t) )

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
    | TRef ctor ->
        parse_record pb reg_tuple
          (SignTable.find_record_decl pb.signature_table ctor)
          json_value
    | _ -> ( match json_value with `String s -> s | v -> to_string v ) in
  let tuple_values = List.map get_field_value (extr_nodes rec_fields) in
  let inst_id = Int.to_string pb.id_index in
  pb.id_index <- pb.id_index + 1 ;
  if Misc.debugging Dbg_parsing then
    Printf.eprintf "[Json_log_parser]: registering tuple: %s(%s)\n%!" ctor
      (String.concat "," (inst_id :: tuple_values)) ;
  reg_tuple ctor (inst_id :: tuple_values) ;
  inst_id

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
    let begin_tp ts =
      if Misc.debugging Misc.Dbg_log then
        Printf.eprintf "[Json_log_parser] Begin TP %s\n%!" (Z.to_string ts) ;
      C.begin_tp ctxt ts in
    let end_tp () =
      if Misc.debugging Misc.Dbg_log then
        Printf.eprintf "[Json_log_parser] End TP\n%!" ;
      C.end_tp ctxt in
    let rec parse_init () =
      debug "init" ;
      pb.input_line <- pb.input_line + 1 ;
      match pb.pb_token with
      | EOF -> parse_eof ()
      | CMD -> next pb ; parse_command ()
      | AT -> next pb ; parse_ts ()
      | t -> fail ("Expected '@' but saw " ^ string_of_token t)
    and parse_line () =
      debug "line" ;
      pb.input_line <- pb.input_line + 1 ;
      match pb.pb_token with
      | EOF -> parse_eof ()
      | CMD -> next pb ; parse_command ()
      | AT -> next pb ; parse_ts ()
      | JSON _ -> parse_json ()
      | t -> fail ("Expected '@' or JSON but saw " ^ string_of_token t)
    and parse_ts () =
      debug "ts" ;
      match pb.pb_token with
      | TS ts ->
          begin_tp ts ;
          pb.id_index <- 0 ;
          next pb ;
          parse_json ()
      | t -> fail ("Expected timestamp but saw " ^ string_of_token t)
    and parse_json () =
      let open Yojson.Basic in
      debug "json" ;
      match pb.pb_token with
      | EOF -> end_tp () ; parse_eof ()
      | JSON str -> (
        try
          let json = sort (Yojson.Basic.from_string ~lnum:pb.input_line str) in
          let signature_decl =
            SignTable.signature_from_json signatures pb.signature_table json
          in
          ( match signature_decl with
          | None ->
              Printf.eprintf
                "[JSON_log_parser|WARN]: Line %i did not match any signature.\n\
                 %!"
                pb.input_line
          | Some decl ->
              ignore
              @@ parse_record pb
                   (fun ctor values ->
                     C.tuple ctxt (ctor, List.assoc ctor dbschema) values )
                   decl json ) ;
          next pb ;
          (match pb.pb_token with AT -> end_tp () | _ -> ()) ;
          parse_line ()
        with Yojson.Json_error msg -> fail msg )
      | t -> fail ("Expected JSON but saw " ^ string_of_token t)
    and parse_command () =
      debug "command" ;
      match pb.pb_token with
      | STR name -> (
          next pb ;
          let err, params =
            try (None, parse_command_params pb)
            with Local_error msg -> (Some msg, None) in
          match err with
          | None -> C.command ctxt name params ; parse_line ()
          | Some msg -> fail msg )
      | t -> fail ("Expected a command name but saw " ^ string_of_token t)
    and parse_eof () = debug "EOF" in
    parse_init () ; C.end_log ctxt ; true
end
