open Misc 
open Postgresql
open Unix
open Log2table


let log_file = ref ""
let query_file = ref ""
let query_name = ref ""
let output_file = ref ""
let debug = ref ""
let db_name = ref ""




let insert_cmd tbl_name values = 
  "INSERT INTO " ^ tbl_name ^ " VALUES " ^ values

let delete_cmd v tbl_name = 
  "DELETE FROM " ^ tbl_name ^ " WHERE tp < " ^ (string_of_int v)



let sql_exec (c:connection) sql_cmd =   
  let _ = c#exec ~expect:[Command_ok] sql_cmd in
  ()



let read_tuple ch pred tp ts = 
  let cts = 
    match pred with
      | "trans" -> Scanf.fscanf ch "(%d, %d, %d)\n" (fun x y z -> [x; y; z]) 
      | "auth" -> Scanf.fscanf ch "(%d, %d)\n" (fun x y -> [x; y]) 
      | "report" -> Scanf.fscanf ch "(%d)\n" (fun x -> [x]) 
      |	_ -> failwith "[main_loop] unknown predicate name" 
  in
  Misc.string_of_list string_of_int (tp :: ts :: cts)


(* two options: run the query and update the tables after each
   time-point or time-stamp -> now for each time-point *)

let main_loop conn log out t_list tbl_names ts_delta query = 
  let tp = ref 0 in
  try 
    while true do
      let ts, pred = Scanf.fscanf log "@@%d %s " (fun x y -> (x,y)) in
      let tbl_name = "tbl_" ^ pred in
      let tuple = read_tuple log pred !tp ts in
      sql_exec conn (insert_cmd tbl_name tuple);
      let res = conn#exec ~expect:[Tuples_ok] query in
      Log2table.print_res out t_list res#get_all;
      List.iter (fun tbl -> sql_exec conn (delete_cmd ts_delta tbl)) tbl_names;
      incr tp
    done
  with End_of_file -> ()


let main () =
  Misc.split_debug !debug;

  let tbl_names = ["tbl_trans"; "tbl_auth"; "tbl_report"; "tbl_time"] in
  let ts_delta = 
    match !query_name with
      | "P2" -> 6
      | "P3" -> 21
      | "P4" -> 36
      | _ -> failwith "unknow policy name"
  in
  let log = open_in !log_file in
  let query, t_list = Log2table.read_query !query_file in
  let out = 
    if !output_file = "" then 
      Pervasives.stdout
    else
      open_out !output_file
  in

  let dbopt = if !db_name = "" then "" else "dbname=" ^ !db_name in 
  let conn = new connection ~conninfo:dbopt () in

  main_loop conn log out t_list tbl_names ts_delta query;

(*
  let d, d' = get_time () in
  Printf.eprintf "Query executed in %.2fs (%.2fs).\n%!" d d';
  Printf.eprintf "There are %d violations.\n" res#ntuples;
  
  Log2table.print_res out t_list res#get_all;
  let d, d' = get_time () in
  Printf.eprintf "Output written in %.2fs (%.2fs).\n%!" d d';
*)
  
  conn#finish



let usage_string = 
  "Usage: pgsql_test [-log <file>] [-query <file>] [-output <file>] [-debug <level>]"

let _ = 
  Arg.parse [
    "-log", Arg.Set_string log_file, "\t\tChoose the log file";
    "-query_name", Arg.Set_string query_name, "\tGive query name (P2, P3, P4)";
    "-query", Arg.Set_string query_file, "\tChoose query file";
    "-output", Arg.Set_string output_file, "\tChoose output file";
    "-debug", Arg.Set_string debug, "\tChoose unit to debug";
    "-db", Arg.Set_string db_name, "\tChoose database";
  ]
    (fun _ -> ())
    usage_string;
  try main () with
  | Error e -> prerr_endline (string_of_error e)
  | e -> prerr_endline (Printexc.to_string e)
