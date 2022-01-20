(********************************************************************
  Log generator for the policies (P1)-(P4) from the following paper:
    David Basin, Felix Klaedtke, Samuel Müller. 
    Policy Monitoring in First-Order Temporal Logic. 
    CAV'10.

  The main goal is to control the event rate and the violation rate.

  Author: Eugen Zalinescu (eugen.zalinescu@inf.ethz.ch)
  Copyright (C) 2011-2013 ETHZ
  Version 0.4

*********************************************************************

  Prerequisites: OCaml compiler (see http://caml.inria.fr/)
  Compile with, for instance: 
    ocamlopt -o gen_log PrioQueue.ml gen_log.ml

  Sample usage: 
    ./gen_log -policy P2 -event_rate 16000 -time_span 300 > P2.log

  Use ./gen_log --help (and see code) for other parameters.
*********************************************************************)


open PrioQueue


(*** global parameters ***)
let ver = "0.4"
let debug = ref false
let verbose = ref false
let no_prelude = ref false
let one_ts = ref false
(* Remark: by default, we consider one tuple per entry; when [one_ts]
   is [true], then there is a single time-stamp per time-point *)
let one_line = ref true

let policy = ref "P1"
let sindex = ref (-1)

(* on average, 5% of all tuples generate a violation *)
let violation_prob = 0.05
let violation_rate = int_of_float (violation_prob *. 100.)

(* average number of events per second *)
let event_rate = ref 100

(* time span of a log file *)
let time_span = ref 60 

(* the first ts in the log file *)
let first_ts = ref 32

(* the amount threshold for P2 and P3 *)
let thr = 2000

(* default values for max value of parameters t and c in P2-P4 *)
let t_size = ref 0
let c_size = ref 0



(*** helpful types and functions ***)

let print_ts ts =
  print_string ("@" ^ (string_of_int ts) ^ " ")

let printn_ts ts =
  print_string ("@" ^ (string_of_int ts) ^ "\n")

type tparam = 
  | One of int
  | Two of int * int
  | Three of int * int * int

let print_event p param =
  match param with
    | One x -> print_string (Printf.sprintf "%s (%d)\n" p x)
    | Two (x,y) -> print_string (Printf.sprintf "%s (%d,%d)\n" p x y)
    | Three (x,y,z) -> print_string (Printf.sprintf "%s (%d,%d,%d)\n" p x y z)    

let print_event_nl p param =
  match param with
    | One x -> print_string (Printf.sprintf "%s (%d)\n\n" p x)
    | Two (x,y) -> print_string (Printf.sprintf "%s (%d,%d)\n\n" p x y)
    | Three (x,y,z) -> print_string (Printf.sprintf "%s (%d,%d,%d)\n\n" p x y z)    

let prev_ts = ref (-1)

let print_entry ts pred param = 
  let print_event = if !one_line then print_event else print_event_nl in
  let print_ts = if !one_line then print_ts else printn_ts in
  assert (!prev_ts <= ts);
  if !one_ts then
    begin
      if !prev_ts < ts then
	begin
	  printn_ts ts;
	  prev_ts := ts
	end;
    end
  else
    print_ts ts;
  print_event pred param


let print_entry1 pred entry = 
  let ts, param = entry in
  print_entry ts pred param

let print_entry2 ts ev = 
  let pred, param = ev in
  print_entry ts pred param


(* The number of events per entry depends on the event_rate. We use a
   variable [var] (a percentage) in order to vary the number of events
   at different time-stamps. For instance, when rate = 500 and var =
   10, there will between 450 and 550 events per time unit.
*)
let nb_of_events rate var = 
  let delta = 
    if rate * var / 100 > 0 then
      Random.int (rate * var / 100) 
    else
      0
  in
  if Random.bool () then
    rate + delta
  else
    rate - delta





let merge print_entry_1 print_entry_2 log1 log2 = 
  let rec merger log1 log2 = 
    match log1, log2 with
      | [], [] -> ()
      | h1 :: tail1, [] -> 
	  print_entry_1 h1;
	  merger tail1 log2
      | [], h2 :: tail2 -> 
	  print_entry_2 h2;
	  merger log1 tail2 
      | h1 :: tail1, h2 :: tail2 -> 
	let ts1,_ = h1 in
	let ts2,_ = h2 in
	if ts1 <= ts2 then
	  begin
	    print_entry_1 h1;
	    merger tail1 log2
	  end
	else
	  begin
	    print_entry_2 h2;
	    merger log1 tail2 
	  end
  in merger log1 log2  





let iof = int_of_float
let foi = float_of_int



(*
  The "approve" policy (P1) is: 
  publish(a,r) IMPLIES acc(a) AND ONCE[0,10] EXISTS ?m.(mgr(m,a) AND approve(m,r))
  
  There can be 4 types of violations:
  1. r is published but not approved
  2. r is published but approved too long ago
  3. there is no manager of a
  4. a is not an accountant

  The event rate for this policy is given by the publish events.
*)

module MgrSet = Set.Make ( 
  struct
    let compare = Stdlib.compare
    type t = int * int
  end )

module AccSet = Set.Make ( 
  struct
    let compare = Stdlib.compare
    type t = int
  end )

let tw_P1 = 11
let mgr_sets = Array.make tw_P1 MgrSet.empty
let acc_sets =  Array.make tw_P1 AccSet.empty

(***
   The computation of the rate r is done as follows:
     t * e = (1/2) * (m + a) + 2 * t * r - (1/4) * p_v * t * e +  t * e / 10 
   where 
     t = time_span
     e = event_rate
     r = (publish) rate
     m = mgr_size
     a = asize
     p_v = violation_prob
***)
let params_P1 () = 
  let rsize = max (50 * !event_rate) 4 in
  let asize = max (!event_rate / 10) 4 in
  let msize = 10 in

  (* this is a fairly good approximation *)
  let mgr_size = asize * msize in
  let rate = max 
    ((foi (!time_span * !event_rate) *. (9./.10. +. violation_prob /. 4.) -. 
       (0.5 *. (foi (mgr_size + asize))) )
    /. 
    (2. *. foi (!time_span))) 1. 
  in
  (* 1 in [vrate] is a violation *)
  let vrate = rate /. ((foi !event_rate) *. violation_prob) in 
  (* one 10th of events are changes to mgr and acc relations *)
  let mgr_rate = (!event_rate / 10) in
  let var = 10 in
  rsize, msize, asize, (iof rate), (iof vrate), mgr_rate, var



let gen_publish_param ts_rel rsize asize =
  let a_list = AccSet.elements acc_sets.(ts_rel) in
  let a_len = AccSet.cardinal acc_sets.(ts_rel) in
  let a = 
    if a_len > 0 then
      let i = Random.int a_len in
      List.nth a_list i
    else
      1 + Random.int rsize 
  in
  let r = 1 + Random.int rsize in
  (a,r)

let get_mgr ts_rel msize a = 
  let mgrs = MgrSet.filter (fun (m,a') -> a = a') mgr_sets.(ts_rel) in
  if MgrSet.is_empty mgrs then
    msize
  else 
    let (m,_) = 
      if Random.bool () then
	MgrSet.min_elt mgrs
      else
	MgrSet.max_elt mgrs
    in 
    m

let tp = ref 0 

(* here we only generate start events *)
let relations_start asize msize = 
  let log_a = ref [] in (* acc_start events *)
  let log_m = ref [] in (* mgr_start events *)

  let acc_set = ref AccSet.empty in
  let mgr_set = ref MgrSet.empty in

  let a = ref 0 in
  while !a < asize do
    let ts = Random.int 20 in
    log_a := (ts, One !a) :: !log_a;
    acc_set := AccSet.add !a !acc_set;
    incr tp;
    for m = 0 to msize - 1 do
      let ts' = Random.int 20 in
      log_m := (ts', Two (m,!a)) :: !log_m;
      mgr_set := MgrSet.add (m,!a) !mgr_set;
      incr tp;
    done;
    a := !a + 2;
  done;
  for a = 0 to asize - 1 do
    let ts' = Random.int 20 in
    log_m := (ts', Two (msize,a)) :: !log_m;
    mgr_set := MgrSet.add (msize,a) !mgr_set;
  done;

  for ts = 20 to 20 + tw_P1 - 1 do
    acc_sets.(ts mod tw_P1) <- !acc_set;
    mgr_sets.(ts mod tw_P1) <- !mgr_set;
  done;

  log_a := List.sort compare !log_a;
  log_m := List.sort compare !log_m;

  let print_entry_a = print_entry1 "acc_S" in  
  let print_entry_m = print_entry1 "mgr_S" in

  merge print_entry_a print_entry_m !log_a !log_m

  
let tmpfile = 
  if !debug then
    open_out "P1.info"
  else
    stdout


let gen_log_P1 () = 
  let rsize, msize, asize, rate, vrate, mgr_rate, var = params_P1 () in
  let tw = tw_P1 in 
  let etw = tw + 1 in

  let ev_array = Array.make etw (Queue.create()) in
  for i = 1 to tw do
    ev_array.(i) <- Queue.create()
  done;

  if not !no_prelude then
    relations_start asize msize;

  for ts = !first_ts to !first_ts + !time_span - 1 do
    let nbe = nb_of_events rate var in

    for j = 1 to nbe do
      
      incr tp;      
      let a, r = gen_publish_param (ts mod tw) rsize asize in       
      
      (* There is 1 in 100/vrate probability that there is a violation
	 corresponding to this publish event. 0 encodes a violation. *)
      let viol = Random.int vrate in
      (* the remaining probability of violating the policy is 1/4 *)
      let violation_type = 1 + Random.int 4 in

      if viol <> 0 || violation_type <> 1 then	
	(* there is a corresponding approval event *)
	begin
	  let ts_app = 
	    if viol = 0 && violation_type = 2 then
	      ts - tw (* approval not recent enough *)
	    else
	      ts - (Random.int tw)
	  in

	  let m = 
	    if viol = 0 && violation_type = 3 then	    
	      msize + 1 (* a has no manager *)
	    else
	      get_mgr (ts_app mod tw) msize a
	  in

	  let a = 
	    if viol = 0 && violation_type = 4 then
	      asize (* a not an accountant *)
	    else
	      a
	  in
	  
	  Queue.add ("approve", Two (m,r)) ev_array.(ts_app mod etw);
	  Queue.add ("publish", Two (a,r)) ev_array.(ts mod etw);
	  let vstr = if viol = 0 then "violation: " else "" in
	  if !debug then
	    Printf.fprintf tmpfile "@%d (time-point %d) (%d,%d) -> %s @%d approve(%d,%d)\n" ts !tp a r vstr ts_app m r;
	end
      else (* we do not generate a new approve event *)
	begin
	  Queue.add ("publish", Two (a,r)) ev_array.(ts mod etw);
	  if !debug then
	    Printf.fprintf tmpfile "@%d (time-point %d) (%d,%d) -> violation\n" ts !tp a r
	end

    done;
    
    let ts' = ts - tw in
    Queue.iter (print_entry2 ts') ev_array.(ts' mod etw);
    Queue.clear (ev_array.(ts' mod etw));
    
    let ts' = ts + 1 in
    acc_sets.(ts' mod tw) <- acc_sets.(ts mod tw);
    mgr_sets.(ts' mod tw) <- mgr_sets.(ts mod tw);

    let nbe = nb_of_events (mgr_rate / 4) var in
    for i = 1 to nbe do
      let a = Random.int asize in
      acc_sets.(ts' mod tw) <- AccSet.add a acc_sets.(ts' mod tw);
      Queue.add ("acc_S", One (a)) ev_array.(ts' mod etw);
    done;
    let nbe = nb_of_events (mgr_rate / 4) var in
    for i = 1 to nbe do
      let a = Random.int asize in
      acc_sets.(ts' mod tw) <- AccSet.remove a acc_sets.(ts' mod tw);
      Queue.add  ("acc_F", One (a)) ev_array.(ts' mod etw);
    done;
    let nbe = nb_of_events (mgr_rate / 4) var in
    for i = 1 to nbe do
      let m = Random.int msize in
      let a = Random.int asize in
      mgr_sets.(ts' mod tw) <- MgrSet.add (m, a) mgr_sets.(ts' mod tw);
      Queue.add  ("mgr_S", Two (m, a)) ev_array.(ts' mod etw);
    done;
    let nbe = nb_of_events (mgr_rate / 4) var in
    for i = 1 to nbe do
      let m = Random.int msize in
      let a = Random.int asize in
      mgr_sets.(ts' mod tw) <- MgrSet.remove (m, a) mgr_sets.(ts' mod tw);
      Queue.add  ("mgr_F", Two (m, a)) ev_array.(ts' mod etw);
    done;

  done;

  let ts = !first_ts + !time_span in
  for i = ts - tw to ts do 
    Queue.iter (print_entry2 i) ev_array.(i mod etw);
  done






(* The policy (P2) is: trans(?c,?t,?a) AND 2000 < ?a IMPLIES
   EVENTUALLY[0,6) report(?t)

   The policy (P3) is:
   trans(?c,?t,?a) AND 2000 < ?a  IMPLIES  ONCE[2,21) EXISTS ?e. auth(?e,?t)

 
   Let e be the event rate, t be the trans_rate, v be the violation prob.

   Suspicious transactions are those for which a > th. There are t/5
   suspicious transactions per time unit, because max(a) = 2500 and th
   = 2000. A good transaction is a transaction with a <= th, or one
   which is reported/authorized. Let g be the ratio between good &
   suspicious transactions and suspicious transactions. We have two
   equations:

   e = t + t/5 * g 
   (each event is either a transaction or an auth/report corresponding
   to a good and suspicious transaction)
   
   v*e = t/5 * (1-g)
   (a violation is a suspicious transaction which is not good)

   We know e and v, and we need to determine t and g. We get t = e *
   (v+1) / 1.2, that is t = 0.875 e. And g = 5 * (e - t) / t. That is,
   g = 0.7142857.   
*)
let trans_params () = 
  let tsize = if !t_size <> 0 then !t_size else 10 * !event_rate in
  let csize = if !c_size <> 0 then !c_size else !event_rate in
  let esize = !event_rate / 10 in

  let e = foi !event_rate in
  let t = e *. (1. +. violation_prob) /. 1.2 in
  let g = 5. *. (e -. t) /. t in
  assert (t = 0.875 *. e);
  assert (abs_float (g -. 0.7142857) <= 0.0001);
  let trans_rate = truncate t in
  let gs_trans_rate = iof (100. *. g) in

  let ts_start = !first_ts in
  let var = 10 in 
  (tsize, csize, esize, trans_rate, gs_trans_rate, ts_start, var)




let gen_trans_event tsize csize = 
  let c = 1 + Random.int csize in
  let t = 1 + Random.int tsize in
  let a = 1 + Random.int (5 * thr / 4) in
  (c,t,a)


(* the events in the priority queue are dumped whenever the
   corresponding timestamps are too old (smaller than current time
   stamp minus delta) *)
let rec write_old ts pqueue delta = 
  if PrioQueue.is_empty pqueue then 
    pqueue
  else
    let (min_ts, ev) = PrioQueue.top pqueue in
    if min_ts <= ts - delta then
      begin
	print_entry2 min_ts ev;
	let (_, _, new_pqueue) = PrioQueue.extract pqueue in
	write_old ts new_pqueue delta
      end
    else
      pqueue

let rec write_all pqueue = 
  if not (PrioQueue.is_empty pqueue) then 
    let (ts, ev, new_pqueue) = PrioQueue.extract pqueue in
    print_entry2 ts ev;
    write_all new_pqueue


let gen_trans_events (tsize, csize, esize, trans_rate, gs_trans_rate, ts_start, var) = 
  let pqueue = ref PrioQueue.empty in
  for ts = ts_start to ts_start + !time_span do
    let nb_trans = nb_of_events trans_rate var in
    for i = 1 to nb_trans do      
      let c, t, a = gen_trans_event tsize csize in
      if a > thr && Random.int 100 < gs_trans_rate then 
	(* no violation *)
	let ts_a = max 0 (ts - 2 - (Random.int 19)) in (* use ts_start instead of 0? *)
	let ts_r = ts + 1 + (Random.int 5) in
        let e = 1 + Random.int esize in
	pqueue := PrioQueue.insert !pqueue ts ("trans", Three (c,t,a));
	if !policy = "P3" then
	  pqueue := PrioQueue.insert !pqueue ts_a ("auth", Two (e,t))
	else
	  pqueue := PrioQueue.insert !pqueue ts_r ("report", One (t))
      else
	pqueue := PrioQueue.insert !pqueue ts ("trans", Three (c,t,a))	  
    done;
    pqueue := write_old ts !pqueue 20;
  done;
  write_all !pqueue


let gen_log_P234 () = 
  gen_trans_events (trans_params ())



(*** Main function ***)

let gen_logs gen = 
  if !sindex = -1 then
    gen 1
  else
    gen !sindex
    
let gen_log gen i = 
  Random.init i;
  gen ()





    


let main () = 
  if !verbose then
    Printf.eprintf "On average, the number of events should be %d \
                   and the number of violations should be %d.\n" 
      (!event_rate * !time_span) 
      (!event_rate * !time_span * violation_rate / 100);
    
  match !policy with 
    | "P1" -> gen_logs (gen_log gen_log_P1)
    | "P2" | "P3" | "P4" -> gen_logs (gen_log gen_log_P234)
    | _ -> failwith "[main] unknown policy name"


  
let usage_string = "Usage: gen_log [options]"

let print_version () = 
  print_endline ("gen_log, version " ^ ver);
  exit 0

let _ = 
  Arg.parse [
    "-policy", Arg.Set_string policy, "\t\tChoose the policy (P1-P4)";
    "-time_span", Arg.Set_int time_span, "\t\tSet the time span";
    "-event_rate", Arg.Set_int event_rate, "\t\tSet the event rate";
    "-seed_index", Arg.Set_int sindex, "\t\tSet the seed index";
    "-tsize", Arg.Set_int t_size, "\t\tSet the maximum transaction identifier";
    "-csize", Arg.Set_int c_size, "\t\tSet the maximum client identifier";
    "-first_ts", Arg.Set_int first_ts, "\t\tSet the first timestamp";
    "-no_prelude", Arg.Set no_prelude, "\t\tSkip the preliminary phase for P1";
    "-one_ts", Arg.Set one_ts, "\t\tOne time stamp per time point";
    "-more_lines", Arg.Clear one_line, "\t\tTimestamp and event(s) on different lines";
    "-v", Arg.Set verbose, "\t\t\tSet verbose mode";
    "-debug", Arg.Set debug, "\t\tSet debug mode";
    "-version", Arg.Unit print_version, "\t\tPrint version and exit";
    ]
    (fun _ -> ())
    usage_string;
  main ()
