open Predicate 
open Tuple
open Relation
open Table
open Db
open Log

(* count the number of events for each predicate and each timestamp *)

(* at most: 10 predicates, 2000 time-stamps *)
let nb_pred = 10
let nb_ts = int_of_string Sys.argv.(3)
let max_ts = ref 0 

let tbl = Hashtbl.create 10 
let count = Array.make_matrix nb_pred nb_ts 0 

(* nb of predicates actually encountered: *)
let cp = ref 0

let open_log sig_file log_file = 
  let _ = Log.get_signature sig_file in
  Log.log_open log_file

let read_log lexbuf = 
  Misc.new_last_ts := false;
  let rec read lexbuf = 
    match (Log.get_next_entry lexbuf) with
      | Some (tp,ts,db) -> 
	let ts = int_of_float ts in
	if ts > !max_ts then
	  max_ts := ts;
	let tables = Db.get_tables db in
	List.iter (fun t -> 
	  let p, _ = Table.get_schema t in
	  let rel = Table.get_relation t in
	  let c = Relation.cardinal rel in
	  let h = 
	    if Hashtbl.mem tbl p then 
	      Hashtbl.find tbl p 
	    else
	      begin
		Hashtbl.add tbl p !cp;
		incr cp;
		!cp - 1
	      end
	  in
	  count.(h).(ts) <- count.(h).(ts) + c;
	) tables;  
	read lexbuf
    
      | None -> ()
  in 
  read lexbuf

let write () = 
  Hashtbl.iter (fun p h -> Printf.printf "%s -> %d, " p h) tbl;
  print_string "\n";
  for ts = 0 to !max_ts do
    Printf.printf "%d  " ts;
    for p = 0 to !cp - 1 do
      Printf.printf "%d " count.(p).(ts);
    done;
    print_endline "";
  done



    
let _ = 
  let lexbuf = open_log Sys.argv.(1) Sys.argv.(2) in
  read_log lexbuf;
  write ()












