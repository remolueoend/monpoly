open Misc
open Postgresql
open Unix
open Table2log


let log_file = ref ""
let query_file = ref ""
let output_file = ref ""
let debug = ref ""
let db_name = ref ""



let insert_cmd tbl_name values = 
  "INSERT INTO " ^ tbl_name ^ " VALUES " ^ values

let insert (c:connection) tbl_name cts = 
  let values = Misc.string_of_list string_of_int cts in
  let sql_cmd = insert_cmd tbl_name values in
  let _ = c#exec ~expect:[Command_ok] sql_cmd in
  ()


    


let last_time = ref (Unix.gettimeofday())
let last_times = ref 0.0

let get_time () = 
  let times = Unix.times() in
  let now = Unix.gettimeofday() in
  let times_curr = times.tms_utime +. times.tms_stime +. times.tms_cutime +. times.tms_cstime in
  let diffs = times_curr -. !last_times in
  let diff = now -. !last_time in (* wall clock! *)
  last_time := now;
  last_times := times_curr;
  diffs, diff



let main () =
  Misc.split_debug !debug;

  let dbopt = if !db_name = "" then "" else "dbname=" ^ !db_name in 
  let conn = new connection ~conninfo:dbopt () in

  if !log_file <> "" then
    begin
      let insert' tbl_name cts = insert conn tbl_name cts in
      Table2log.log2table !log_file insert';
      let d, d' = get_time () in
      Printf.eprintf "log read, tables created in %.2fs (%.2fs).\n%!" d d';
    end;
  
  if !query_file <> "" then
    begin
      let query, t_list = Table2log.read_query !query_file in
      let out = 
	if !output_file = "" then 
	  Pervasives.stdout
	else
	  open_out !output_file
      in

      let res = conn#exec ~expect:[Tuples_ok] query in
      let d, d' = get_time () in
      Printf.eprintf "Query executed in %.2fs (%.2fs).\n%!" d d';
      Printf.eprintf "There are %d violations.\n" res#ntuples;

      Table2log.print_res out t_list res#get_all;
      let d, d' = get_time () in
      Printf.eprintf "Output written in %.2fs (%.2fs).\n%!" d d';
    end;

  conn#finish



let usage_string = 
  "Usage: pgsql_test [-log <file>] [-query <file>] [-output <file>] [-debug <level>]"

let _ = 
  Arg.parse [
    "-log", Arg.Set_string log_file, "\t\tChoose the log file";
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
