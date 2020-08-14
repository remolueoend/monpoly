(********************************************************************
  Generator for random monitorable policies 

  The main goal is to generate formulas that exercise different special cases of Monpoly.

  Author: Srdjan Krstic (srdan.krstic@inf.ethz.ch)
  Copyright (C) 2019 ETHZ
  Version 0.1

*********************************************************************

  Prerequisites: OCaml compiler (see http://caml.inria.fr/)
  Compile with, for instance: 
    ocamlopt -o gen_fma random_generator.ml gen_log.ml

  Sample usage: 
    ./gen_fma -size 5 -sig ./predicates.sig -free_vars 4 

  Use ./gen_fma --help (and see code) for other parameters.
*********************************************************************)

open Formula_generator


(*** global parameters ***)
let ver = "1.1"
let debug = ref false

let size = ref 10
let free_vars = ref 3
let sig_string = ref "" 
let sig_string_cmp = ref "" 
let sig_file = ref "" 
let out_file = ref ""
let out_file_cmp = ref ""
let max_lb = ref 5
let max_interval = ref 20
let past_only = ref false
let all_rels = ref false
let qtl = ref false
let fo_only = ref false
let ndi = ref false
let max_const = ref 42
let aggregations = ref false;;

(* Printexc.record_backtrace true;; *)




open IntMap

(* TODO: Parse the standard sig file *)
(* P,4 | q, 3 | r,2 *)
let parse_sig s =
  let ss = 
      List.map (fun p -> 
        List.map (fun str -> 
          String.trim str) 
      (String.split_on_char ',' p)) 
    (String.split_on_char '|' s) in
  if s = "" then empty else
  if List.for_all (fun x -> List.length x == 2) ss then
    List.fold_left (fun map (p::num) -> 
      let arity = int_of_string (List.hd num) in 
      let oldSet = try find arity map with Not_found -> Set.empty in 
      add arity (Set.add p oldSet) map) empty ss
  else 
    let _ = Printf.printf "Malformed sig: %s" s in
    empty

let main () = 
  if !qtl then 
  begin
    past_only:=true;
    max_lb:=-1;
    aggregations:=false;
  end;
  let ssig = if sig_string = sig_string_cmp then "" else !sig_string in
  let sigmap = parse_sig ssig in
  let (sigout,fma) = generate_formula ~signature:sigmap ~max_lb:!max_lb ~max_interval:!max_interval ~past_only:!past_only ~all_rels:!all_rels ~aggr:!aggregations ~foo:!fo_only ~ndi:!ndi ~max_const:!max_const ~qtl:!qtl !free_vars !size in
  let output_str = Printf.sprintf "SIGNATURE:\n%s\nMFOTL FORMULA:\n%s\n" (string_of_sig sigout) (string_of_genformula fma) in
  let output_str = output_str ^ if !qtl then Printf.sprintf "\nQTL FORMULA:\n%s\n" (string_of_genformula_qtl fma) else "" in
  if out_file = out_file_cmp then
    Printf.printf "%s" output_str
  else
    let sig_file = open_out (!out_file^".sig") in 
    Printf.fprintf sig_file "%s" (string_of_sig sigout);
    let fma_file = open_out (!out_file^".mfotl") in 
    Printf.fprintf fma_file "%s\n" (string_of_genformula fma);
    if !qtl then
      let qtl_file = open_out (!out_file^".qtl") in 
      Printf.fprintf qtl_file "%s\n" (string_of_genformula_qtl fma)
    

  
let usage_string = "gen_fma -- Generator of monitorable MFOTL formulas\n\n" ^
                   "Monitorable fragment is defined operationally: MFOTL" ^
                   "formulas accepted by the MONPOLY monitoring tool without rewriting (using the -no_rw flag)\n\n" ^
                   "Usage: gen_fma [options]\n"

let print_version () = 
  print_endline ("gen_log, version " ^ ver);
  exit 0

let _ = 
  Arg.parse [
    "-size", Arg.Set_int size, "\t\tChoose the size of the random MFOTL formula (Default: 10)";
    "-free_vars", Arg.Set_int free_vars, "\t\tChoose the number of free variables in the random MFOTL formula (Default: 3)";
    "-sig", Arg.Set_string sig_string, "\t\t\tSignature as an immediate parameter (Default: nothing; the generator picks a random signature)";
    "-sig_file", Arg.Set_string sig_file, "\t\tSignature as a file (Default: nothing; the generator picks a random signature)";
    "-output", Arg.Set_string out_file, "\t\tOutput file names suffixed with .sig and .mfotl by the generator (Default: nothing; the generator writes on standard output";
    "-max_lb", Arg.Set_int max_lb, "\t\tSet the maximum value for the left bound of the intervals; use a negative number for FOTL formulas (Default: 5)";
    "-max_interval", Arg.Set_int max_interval, "\tSet the maximum size of the intervals; ignored if -max_lb is negative (Default: 20)";
    "-past_only", Arg.Set past_only, "\t\tGenerate past-only formulas (Default: false)";
    "-all_rels", Arg.Set all_rels, "\t\tGenerate all rigid predicates -- as opposed to only equalities (Default: false)";
    "-qtl", Arg.Set qtl, "\t\t\tGenerate a QTL formula (and its equivalent MFOTL counterpart). Note that, this sets -max_lb to -1, -past_only, unsets -aggr, and outputs an additional qtl formula (Default: false)";
    "-debug", Arg.Set debug, "\t\tSet debug mode (Default: false)";
    "-aggr", Arg.Set aggregations, "\t\tGenerate aggregation operators (Default: false)";
    "-fo_only", Arg.Set fo_only, "\t\tGenerate only first-order operators (Default: false)";
    "-non-di", Arg.Set ndi, "\t\tGenerate arbitrary formulas (as opposed to domain independent) (Default: false)";
    "-max_const", Arg.Set_int max_const, "\tSet the maximum constant value occuring in the formula (Default: 42)";
    "-version", Arg.Unit print_version, "\t\tPrint version and exit";
    ]
    (fun _ -> ())
    usage_string;
  main ()
  