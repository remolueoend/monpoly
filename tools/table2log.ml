open Predicate 
open Tuple
open Relation
open Table
open Db
open Log


let open_log log_file = 
  (* let _ = Log.get_signature sig_file in *)
  Log.log_open log_file

let read_log insert lexbuf = 
  Misc.new_last_ts := false;
  let rec read lexbuf = 
    match (Log.get_next_entry lexbuf) with
      | MonpolyData {tp; ts; db} -> 
	let ts = int_of_float ts in
	insert "tbl_Time" (tp :: [ts]);
	let tables = Db.get_tables db in
	ignore (
	  List.map (fun tab -> 
	    let (tname, _) = Table.get_schema tab in
	    let rel = Table.get_relation tab in
	    let tuples = Relation.elements rel in
	    assert ((List.length tuples) = 1);
	    ignore (
	      List.map (fun t -> 
		let cts = tp :: ts :: List.map 
		  (fun x -> 
		    match x with
		      | Int c -> c 
		      | _ -> failwith "[read_log]"
		  ) 
		  (Tuple.get_constants t) 
		in
		insert ("tbl_" ^ tname) cts
	      ) tuples; );
	  ) tables);
	
	read lexbuf

      | _ -> ()
  in 
  read lexbuf

let log2table log_file insert = 
  let lexbuf = open_log log_file in
  read_log insert lexbuf



let read_vt_line line = 
  let vt_list = Str.split (Str.regexp "[ \t]*,[ \t]*") line in
  let p = Str.regexp ":" in
  List.map 
    (fun vt -> 
      match Str.split p vt with
	| [x; "int"] -> (x, TInt)
	| [x; "string"] -> (x, TStr)
	| _ -> failwith "[read_vt_file] unknown type"
    )
    vt_list


let read_query query_file =
  let ch = open_in query_file in
  let first = ref true in
  let t_list = ref [] in
  let rec read str = 
    try 
      let line = input_line ch in
      if !first && String.length line >=3 && String.sub line 0 3 =  "-- " then 
	let vt_line = String.sub line 3 ((String.length line) - 3) in
	t_list := read_vt_line vt_line;
	first := false;
	read ""
      else
	read (str ^ " " ^ line)
    with End_of_file -> str
  in
  read "", !t_list



module Tuple_set = Set.Make (
  struct type t = Tuple.tuple
	 let compare = Tuple.compare
  end)

module Db_map = Map.Make (
  struct type t = int * int
	 let compare = Pervasives.compare
  end)


let strip str = 
  Str.replace_first (Str.regexp "^[ ]+") "" str

let put t_list db row = 
  (* Printf.printf "%s %s\n" row.(0) row.(1); *)
  let k = int_of_string (strip row.(0)), int_of_string row.(1) in
  let str_list = Array.to_list (Array.sub row 2 (Array.length row - 2)) in
  let t = Tuple.make_tuple2 str_list t_list in
  let old_set = 
    if Db_map.mem k db then
      Db_map.find k db 
    else
      Tuple_set.empty
  in
  let new_set = Tuple_set.add t old_set in
  Db_map.add k new_set db 

let write out k s = 
  let tp, ts = k in
  Printf.fprintf out "@%d (time-point %d): " ts tp;
  output_string out (Misc.string_of_list4 Tuple.string_of_tuple (Tuple_set.elements s));
  output_string out "\n"


(* This works well for PostgreSQL *)
let print_res out t_list all =
  let db_all = Array.fold_left (put t_list) Db_map.empty all in
  Db_map.iter (write out) db_all


(* For MySQL we do ugly tricks *)
let db = ref (Db_map.empty) 

let update no_null t_list a = 
  let a' = no_null a in
  db := put t_list !db a'
   
let mysql_write out = 
  Db_map.iter (write out) !db




let query_file = ref ""
let input_file = ref ""
let output_file = ref ""

let read_input k ch_in = 
  let c = ref 0 in
  let all = ref [] in
  try 
    while true do
      let line = input_line ch_in in
      incr c;
      if !c > 2 then
	let list = Str.split (Str.regexp "[ \t]*|[ \t]*") line in
	if k = List.length list then
	  let a = Array.of_list list in
	  all := a :: !all;	
      (* ignore(List.map (fun x -> print_string (x ^ " ")) list); *)
    done;
    Array.of_list !all
  with End_of_file -> Array.of_list !all

let main () = 
  let out = 	
    if !output_file = "" then 
      Pervasives.stdout
    else
      open_out !output_file 
  in
  let query, t_list = read_query !query_file in
  let k = List.length t_list in
  let ch_in = open_in !input_file in
  let all = read_input (k+2) ch_in in  
  print_res out t_list all


let usage_string = 
  "Usage: table2log [-query <file>] [-input <file>] [-output <file>]"

let _ = 
  Arg.parse [
    "-query", Arg.Set_string query_file, "\tChoose query file";
    "-input", Arg.Set_string input_file, "\tChoose input file";
    "-output", Arg.Set_string output_file, "\tChoose output file";
  ]
    (fun _ -> ())
    usage_string;
  try main () with  
  | e -> prerr_endline (Printexc.to_string e)
