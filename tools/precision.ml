open Lexing
open Log

let sigfile = ref ""
let infile = ref ""
let d = ref 0
let dd = ref 0.

let get_table s db = 
  try 
    Db.get_table db (fst s)
  with Not_found -> Table.make_table s (Relation.empty)

let merge sign db1 db2 = 
  Db.make_db
    (List.filter (fun t -> not (Relation.is_empty (Table.get_relation t)))
       (List.map 
	  (fun s -> 
	    let table1 = get_table s db1 in
	    let table2 = get_table s db2 in
	    Table.make_table s 
	      (Relation.union 
		 (Table.get_relation table1)
		 (Table.get_relation table2)
	      )
	  ) 
	  sign
       )
    )

let print_tsdb ts db = 
  Printf.printf "@%s\n" (MFOTL.string_of_ts (float_of_int ts));
  Db.dump_db db

let main sign = 
  let lexbuf = Log.log_open !infile in
  let nextts = ref 0. in
  let i = ref 0 in
  let rec read_entries accdb = 
    match Log.get_next_entry lexbuf with
      | Some(ts,db) -> 
	if ts < !nextts then
	  let newdb = merge sign accdb db in
	  read_entries newdb
	else
	  begin
	    (* output accumulated db *)
	    print_tsdb !i accdb;
	    while ts >= !nextts do
	      incr i;
	      nextts := !nextts +. !dd
	    done;
	    read_entries db
	  end
	
      | None -> print_tsdb !i accdb;
  in
  match Log.get_next_entry lexbuf with
    | None -> ()
    | Some(ts,db) -> 
      nextts := ts +. !dd;  
      read_entries db




let usage_string = 
  "Usage: precision -sig <file> -in <file> -tu <d>"

let main () = 
  if !sigfile = "" then 
    print_endline ("No signature file given.\n" ^ usage_string)
  else
    let sign = Log.get_signature !sigfile in
    if !d <= 0 then
      print_endline ("Need to specify the new time unit (a positive integer).\n" ^ 
			usage_string)
    else
      begin
	dd := float_of_int !d;
	main sign
      end
      
let _ =
  Arg.parse 
    ["-sig", Arg.Set_string sigfile, "\t\tSpecify the signature file";
     "-tu", Arg.Set_int d, "\t\tSpecify time unit multiplier";
     "-in", Arg.Set_string infile, "\t\tSpecify input file";
    ]
    (fun _ -> ())
    usage_string;
  main ()
