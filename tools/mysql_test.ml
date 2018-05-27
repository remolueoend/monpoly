open Misc
open Mysql
open Unix
open Table2log


let log_file = ref ""
let query_file = ref ""
let output_file = ref ""
let debug = ref ""
let db_name = ref ""



let ml2values t = 
  Mysql.values (List.map Mysql.ml2int t)

let insert_cmd tbl_name values = 
  "INSERT INTO " ^ tbl_name ^ " VALUES " ^ values

let insert myd tbl_name cts = 
  ignore(Mysql.exec myd (insert_cmd tbl_name (ml2values cts)));
  match Mysql.errmsg myd with
    | Some str -> print_endline str
    | None -> ()






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

  let mydb = {dbhost = None; 
	      dbname = Some !db_name; 
	      dbport = None; 
	      dbpwd = None; 
	      dbuser = None;} 
  in
  let myd = Mysql.connect mydb in

  (* ignore(Mysql.exec myd "set @@max_heap_table_size=1073741824"); *)
  (* let _ = Mysql.exec myd "select @@max_heap_table_size" in *)
  (*
    (match Mysql.fetch res with
    | Some a -> let Some v = a.(0) in Printf.printf "max_heap_table_size=%s\n%!" v
    | None -> print_endline "no results");
  *)

  if !log_file <> "" then
    begin
      Table2log.log2table !log_file (insert myd);
      let d, d' = get_time () in
      Printf.printf "log read, tables created in %.2fs (%.2fs).\n%!" d d';
    end;
  
  if !query_file <> "" then
    let query, t_list = read_query !query_file in
    let out = 
      if !output_file = "" then 
	Pervasives.stdout
      else
	open_out !output_file
    in

    let res = Mysql.exec myd query in
    (match Mysql.errmsg myd with
      | Some str -> print_endline str
      | None -> ()
    );
    let d, d' = get_time () in
    Printf.printf "query executed in %.2fs (%.2fs).\n%!" d d';
    Printf.printf "There are %s violations.\n" (Int64.to_string (Mysql.size res));



    (* Mysql.iter res ~f:(print_row out); *)
    (* Table2log.print_res out t_list res#get_all; *)

    let no_null = Array.map 
      (fun x -> match x with 
	| None -> failwith "result contains NULL" 
	| Some s -> s) 
    in
    Mysql.iter res ~f:(Table2log.update no_null t_list);
    Table2log.mysql_write out;
    
    let d, d' = get_time () in
    Printf.printf "output written in %.2fs (%.2fs).\n%!" d d';
    ()


let usage_string = 
  "Usage: mysql_test -db <name> -sig <file> -log <file> -query <file> [-debug <level>]"

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
  main ();



(*
let test () = 
  let cmd = "SELECT VERSION(), CURRENT_DATE" in
  let res = Mysql.exec myd cmd in
  match Mysql.fetch res with
    | Some a -> Printf.printf "returned a row with %d fields\n" (Array.length a)
    | None -> print_endline "no results"
*)
