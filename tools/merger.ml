open MFOTL
open Lexing
open Log

let sigfile = ref ""
let checkopt = ref false
let mergeopt = ref false
let collapseopt = ref false
let sortopt = ref false
let interleaveopt = ref false
let insertfile = ref ""
let rm = ref (-1.0) (* right margin of future interval, for computing the lookahead 
		     (and the density of events in the time window) *)
let infiles = ref []

let rec open_infiles = function
  | [] -> []
  | filename :: rest ->
      let lexing = log_open filename in
        match Log.get_next_entry lexing with
          | Some (_,ts,db) -> (open_infiles rest) @ [(lexing, (ts, db))]
          | None -> (open_infiles rest)

let rec min_ts = function
  | [] -> raise (Invalid_argument "merger.ml:min_ts: empty list")
  | (_,(ts,_)) :: [] -> ts
  | (_,(ts,_)) :: rest -> min ts (min_ts rest)

let rec merge = function
  | [] -> ()
  | inputs ->
      let min_ts = min_ts inputs in
        Printf.printf "@%.0f\n" min_ts;
        let rec loop inputs_old inputs_new =
          match inputs_old with
            | [] -> inputs_new
            | (lexing, (ts,db)) :: rest ->
                assert(min_ts <= ts);
                if (ts = min_ts) then begin
                  Db.dump_db db;
                  match Log.get_next_entry lexing with
                    | None -> loop rest inputs_new
                    | Some (_,ts,db) -> 
			  loop rest (inputs_new @ [(lexing, (ts,db))])
                end else
                  loop rest ((lexing, (ts,db)) :: inputs_new)
        in
        let inputs = loop inputs [] in
          Printf.printf "\n";
          merge inputs

(* collapsing merge - For now a predicate may occur multiple times in
   a single entry. The current version of the parser copes with this
   well, but the log file is slightly larger. Ideally, the tuples for
   each predicate should be collected together, so that each predicate
   would be output only once per entry.
*)
let rec collapse = function
  | [] -> ()
  | inputs ->
      let min_ts = min_ts inputs in
        Printf.printf "@%.0f\n" min_ts;
        let rec loop inputs_old inputs_new =
          match inputs_old with
            | [] -> inputs_new
            | (lexing, (ts,db)) :: rest ->
                assert(min_ts <= ts);
                if (ts = min_ts) then begin
                  Db.dump_db db;
                  match Log.get_next_entry lexing with
                    | None -> loop rest inputs_new
                    | Some(_,ts,db) -> 
			loop ((lexing, (ts,db)) :: rest) inputs_new
                end else
                  loop rest ((lexing, (ts,db)) :: inputs_new)
        in
        let inputs = loop inputs [] in
          Printf.printf "\n";
          collapse inputs


(* an interleaving is produced (so no merging is done): the ordering
   of equal timestamps is given by the ordering of logfiles at the
   command line *)
let interleave inputs = 
  let rec inter_rec mints inputs =     
    let rec loop crtinputs new_inputs =
      match crtinputs with
        | [] -> List.rev new_inputs
        | (lexing, (ts,db)) :: rest ->
          assert(mints <= ts);
          if (ts = mints) then 
	    begin
	      Printf.printf "@%.0f\n" mints;
              Db.dump_db db;
	      print_string "\n";
              match Log.get_next_entry lexing with
		| None -> loop rest new_inputs
		| Some(_,nts,ndb) -> 
		  loop  ((lexing, (nts,ndb)) :: rest) new_inputs
            end 
	  else
            loop rest ((lexing, (ts,db)) :: new_inputs)
    in
    let new_inputs = loop inputs [] in
    if new_inputs <> [] then
      let mints = min_ts new_inputs in
      inter_rec mints new_inputs
  in
  let mints = min_ts inputs in
  inter_rec mints inputs


let insert filename =
  let lexing = log_open filename in
    (* let pred = get_schema "insert" in *)
  let pred = Predicate.make_predicate ("insert",[]) in
  let rec loop lexing =
    match Log.get_next_entry lexing with
      | None -> ()
      | Some(_,ts,db) -> 
          begin
          try
            let table = Db.get_table db pred in
            let rel = Table.get_relation table in
              if not (Relation.is_empty rel) then begin
                Printf.printf "@%.0f\n" ts;
                Db.dump_db (Db.make_db [table]);
                Printf.printf "\n";
              end
          with e ->
            ()
          end;
	  loop lexing
  in
    loop lexing

let check filename = 
  let lexbuf = Log.log_open filename in  
  let prev = ref min_float in
  let rec check_curr () =
    match Log.get_next_entry lexbuf with
      | Some(_,ts,_) -> 
	  if (compare !prev ts) <= 0 then
	    begin
	      prev := ts;
	      check_curr ()
	    end
	  else
	    begin
	      Printf.printf "Problem at timestamp %f (previous is %f) in log file %s.\n%!" ts !prev filename;
	      false
	    end
      | None -> true
  in
    check_curr()

let check_all () = 
  Printf.printf "Starting checking...\n%!";
  ignore (
    List.map 
      (fun str -> 
	 Printf.printf "Checking file %s...\n%!" str;
	 if check str then
	   Printf.printf "The log file %s is OK.\n%!" str
      )
      !infiles
  )


let lookahead filename intv = 
  let lexbuf = Log.log_open filename in  
  let i = ref 0 in
  let q = ref 0 in
  let tsq = ref MFOTL.ts_invalid in
  let tslist = Queue.create() in
    
    (* initilization *)
    (match Log.get_next_entry lexbuf with
       | Some(_,ts,_) -> 
	   tsq := ts
       | _ -> ()
    );
    
    let rec loop () =
      match Log.get_next_entry lexbuf with
	| Some(_,ts,_) -> 	  
	    incr i;
	    Queue.add ts tslist;
	    (* Printf.printf "new i=%d   new ts=%Ld   tslist = " !i ts;
	       Misc.print_queue MFOTL.print_ts tslist; print_newline(); *)
	    while !q < !i && not (MFOTL.in_left_ext (MFOTL.ts_minus ts !tsq) intv) do
	      (* Printf.printf "la=%d q=%d tsq=%Ld\n%!" (!i - 1 - !q) !q !tsq; *)
	      Printf.printf "%d\n" (!i - 1 - !q);
	      incr q;
	      tsq := Queue.pop tslist
	    done;	    
	    loop ()
	| _ -> ()
    in
      loop();
      Printf.printf "Last i=%d q=%d (tsq=%f)\n%!" !i !q !tsq


let lookahead_all () = 
  ignore (
    List.map 
      (fun str -> 
	 Printf.printf "input file: %s\n%!" str; 
	 lookahead str (CBnd 0., CBnd !rm)
      )
      !infiles
  )

let sort filename =
  let lexbuf = Log.log_open filename in  
  let rec read_log list = 
    match Log.get_next_entry lexbuf with
      | Some(_,ts,db) -> read_log ((ts,db) :: list)
      | None -> List.rev list
  in
  let compare (ts1,db1) (ts2,db2) =
    if ts1 < ts2 then -1
    else if ts1 = ts2 then 0
    else 1
  in
  let rec print_log = function
    | (ts,db)::rest ->
        Printf.printf "@%.0f\n" ts;
        Db.dump_db db;
        Printf.printf "\n";
        print_log rest
    | [] -> ()
  in
  let log = read_log [] in
    (* Printf.printf "list len: %d\n" (List.length log); *)
  let log = List.stable_sort compare log in
    print_log log

let usage_string = 
  "Usage: merger -sig <file> [-check] [-lookahead d] [-sort | -merge | -collapse] <infile>*"

let main () = 
  if !sigfile = "" then begin
    print_endline "No signature file given.";
    print_endline usage_string
  end else
    begin
      ignore(Log.get_signature !sigfile);
      if !checkopt then
	check_all();
      if !rm >= 0.0 then
	lookahead_all ();      
      if !sortopt then
        match !infiles with
          | [filename] -> sort filename
          | [] | _::_ -> print_endline "At most one file can be sorted."
      else if !insertfile <> "" then
	insert !insertfile
      else
	let inputs = open_infiles !infiles in
	if !mergeopt then	
	  merge inputs
      else if !collapseopt then
	  collapse inputs
      else if !interleaveopt then
	  interleave inputs
    end
      
let _ =
  Arg.parse 
    ["-sig", Arg.Set_string sigfile, "\t\tChoose the signature file";
     "-check", Arg.Set checkopt, "\t\tCheck the input files for monotonicity.";
     "-sort", Arg.Set sortopt, "\t\tSort the input file (stable sort).";
     "-lookahead", Arg.Set_float rm, "\t\tCompute lookahead";
     "-merge", Arg.Set mergeopt, "\t\tInterleave input files";
     "-collapse", Arg.Set collapseopt, "\t\tCollapse-merge input files";
     "-interleave", Arg.Set interleaveopt, "\t\tInterleave input files";
     "-insert_only", Arg.Set_string insertfile, "\t\tKeep only insert db1, db2"
    ]
    (fun str -> infiles := str :: !infiles)
    usage_string;
  main ()
