open Predicate


let ts_start = 1262246349  (* 30-12-2009 *)
let ts_end   = 1262246394  (* 31-12-2009 *)
let ts1 =       946684800  (* 01-01-2000 *)
let oneday = 24 * 60 * 60 
let years = int_of_string Sys.argv.(3)
let span = years * 356 * oneday
let delta = span / 25000


let print_ts ch ts =
  output_string ch ("@" ^ (string_of_int ts) ^ "\n")

let oldts = ref ts1

let tf_tuple t = 
  let csts = Tuple.get_constants t in
  let new_csts = 
    List.map (fun c ->
      match c with
	| Int n -> Int (n mod 1000)
	| x -> x
    )
      csts
  in
  Tuple.make_tuple new_csts



let tf_table table = 
  let s = Table.get_schema table in
  let rel = Table.get_relation table in
  let newrel = Relation.map tf_tuple rel in
  Table.make_table s newrel

let tf db = 
  let tables = Db.get_tables db in
  let newtables = List.map tf_table tables in
  Db.make_db newtables

let rec transf lexbuf = 
  match (Log.get_next_entry lexbuf) with
    | Some (ts,db) -> 
      let d = Random.int (2 * delta) in
      assert (d >= 0);
      let newts = !oldts + d in
      assert (newts >= !oldts);
      print_ts stdout newts;
      oldts := newts;
      Db.dump_db (tf db);
      transf lexbuf

    | None -> ()


let _ = 
  let s = Sys.argv.(1) in
  let f = Sys.argv.(2) in
  let _ = Log.get_signature s in
  let lexbuf = Log.log_open f in
  transf lexbuf   
