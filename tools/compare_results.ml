open Predicate 

let verboseopt = ref false
let ignore_tp = ref false
let tuplelen = ref 0
let infiles = ref []

let l1 = ref 0
let l2 = ref 0


let my_input_line f i = 
  if i=1 then
    incr l1
  else
    incr l2;
(*
  if i=1 && !l1 mod 100 = 0  then
    Printf.printf "We have read %d lines from file %d\n%!" !l1 i
  else if i=2 && !l2 mod 100 = 0  then
    Printf.printf "We have read %d lines from file %d\n%!" !l2 i;
*)
  input_line f
	  
let scan_tuple len = 
  function s -> 
    Printf.printf "Analyzing string -%s-\n%!" s;
    match len with
      | 1 -> Scanf.sscanf s "(%s) " (fun a1 -> Tuple.make_tuple [Str a1])
      | 2 -> Scanf.sscanf s "(%s,%s) " 
	  (fun a1 a2 -> 					      
	     Printf.printf "We have read -%s- and -%s- \n%!" a1 a2;
	     Tuple.make_tuple [Str a1; Str a2])
      | 3 -> Scanf.sscanf s "(%s,%s,%s) " 
	(fun a1 a2 a3 -> Tuple.make_tuple [Str a1; Str a2; Str a3])
      | _ -> failwith "[scan_tuple] need to add a new case..."


(* TODO: eliminate the pattern matching... *)
(* let scan_tuple2 len =  *)
(*   function s ->  *)
(*     (\* Printf.printf "Analyzing string -%s-\n%!" s; *\) *)
(*     let pattern = *)
(* 	match len with *)
(* 	  | 1 -> " *| *\\([^ |]*\\\) *| *" *)
(* 	  | 2 -> " *| *\\([^ |]*\\\) *| *\\([^ |]*\\\) *| *" *)
(* 	  | 3 -> " *| *\\([^ |]*\\\) *| *\\([^ |]*\\\) *| *\\([^ |]*\\\) *| *" *)
(* 	  | 4 -> " *| *\\([^ |]*\\\) *| *\\([^ |]*\\\) *| *\\([^ |]*\\\) *| *\\([^ |]*\\\) *| *" *)
(* 	  | _ -> failwith "[scan_tuple] need to add a new case..." *)
(*     in *)
(*     let regexp = Str.regexp pattern in *)
(*       if Str.string_match regexp s 0 then *)
(*       	match len with *)
(* 	  | 1 ->  *)
(* 	      let a1 = Str.matched_group 1 s in *)
(* 		Tuple.make_tuple [Str a1] *)
(* 	  | 2 -> *)
(* 	      let a1 = Str.matched_group 1 s in *)
(* 	      let a2 = Str.matched_group 2 s in *)
(* 		Tuple.make_tuple [Str a1; Str a2] *)
(* 	  | 3 -> *)
(* 	      let a1 = Str.matched_group 1 s in *)
(* 	      let a2 = Str.matched_group 2 s in *)
(* 	      let a3 = Str.matched_group 3 s in *)
(* 		Tuple.make_tuple [Str a1; Str a2; Str a3] *)
(* 	  | 4 -> *)
(* 	      let a1 = Str.matched_group 1 s in *)
(* 	      let a2 = Str.matched_group 2 s in *)
(* 	      let a3 = Str.matched_group 3 s in *)
(* 	      let a4 = Str.matched_group 4 s in *)
(* 		Tuple.make_tuple [Str a1; Str a2; Str a3; Str a4] *)

(* 	  | _ -> failwith "[scan_tuple] need to add a new case..." *)
(*       else *)
(* 	raise (Scanf.Scan_failure "none") *)

let scan_relation f i scan_tuple = 
  let s = ref "" in
  let rec scan_rel crel =
    try 
      s := "";
      while !s = "" || !s = "\r" do
	s := my_input_line f i
      done;
      let t = scan_tuple !s in
	(* Tuple.print_tuple t; print_newline(); *)
	scan_rel (Relation.add t crel) 
    with
      | Scanf.Scan_failure str -> 
	  (* Printf.printf "[scan_tuple] Failure for string -%s- : %s\n%!" !s str; *)
	  !s,crel
      | End_of_file -> "", crel
  in
    scan_rel Relation.empty



let compare_results fscan_tuple file1 file2 =
  if !verboseopt then
    Printf.printf "compare: Comparing files %s and %s\n%!" file1 file2;

  let f1 = open_in file1 in
  let f2 = open_in file2 in

  let same = ref true in

  (* Scanning.from_file f *)
  let rec scan_files s1 s2 = 
    let scan_indexes f i s = 
      (try 
	 let str = 
	   if s = "" then
	     begin
	       let line = ref (my_input_line f i) in
		 while !line = "" do
		   line := my_input_line f i
		 done;
		 !line
	     end
	   else
	     s
	 in
	   (* Scanf.sscanf str "q = %d; i = %d " (fun q i -> (q,i)) *)
	 print_endline str;
	 Scanf.sscanf str "@%d (time-point %d): " (fun q i -> (q,i))
       with
	 | End_of_file -> (-1,-1)
	 (* | (Scanf.Scan_failure _ ) as e -> 
	    Printf.printf "Problem at line %d in log file %d\n%!" 
	       (if i=1 then !l1 else !l2) i; 
	     raise e *)
      )
    in
    let (q1,i1) = scan_indexes f1 1 s1 in
    let (q2,i2) = scan_indexes f2 2 s2 in
    (*  Printf.printf "We are at %d (q1 = %d i1 = %d) and %d (q2 = %d i2 = %d) \n%!" 
	!l1 q1 i1 !l2 q2 i2; *)
      if q1 = q2 && (!ignore_tp || i1 = i2) then
	begin
	  if q1 <> (-1) then
	    begin
	      let s1,rel1 = scan_relation f1 1 fscan_tuple in
	      let s2,rel2 = scan_relation f2 2 fscan_tuple in
		if Relation.equal rel1 rel2 then
		  scan_files s1 s2
		else
		  same := false;
	    end
	end
      else
	same := false
  in
    scan_files "" "";
    if !verboseopt then
      if !same then
	Printf.printf "compare: Same results\n%!"
      else
	Printf.printf "compare: Result files differ\n%!";
    if not !same then
      exit 1
	
  


let usage_string = 
  "Usage: compare [-v] [-ignore_tp] -tuple_len len results_file1 results_file2"

let main () = 
  if !tuplelen > 0 then
    if List.length !infiles = 2 then
      compare_results (scan_tuple !tuplelen) (List.hd !infiles) (List.hd (List.tl !infiles))
    else
      begin
	print_endline "We can only compare exactly 2 result files."
      end
  else
    print_endline usage_string
      
let _ =
  Arg.parse 
    ["-v", Arg.Set verboseopt, "\t\tVerbose output";
     "-v", Arg.Set ignore_tp, "\t\tIgnore time-points";
     "-tuple_len", Arg.Set_int tuplelen, "\t\tGive tuple length"]
    (fun str -> infiles := !infiles @ [str])
    usage_string;
  main ()
