(*
 * Implements the labeling algorithm to check whether formula can be
 * monitored on a log filtered for empty timepoints.
 *)

open Misc
open Predicate
open MFOTL
open Formula_parser
open Lexing

let usage_string = 
  "Usage: fc_filter_empty_tp [-negate] -formula <file>"

let formulafile = ref ""
let negate = ref false

let analyse_formulafile ic = 
  Formula_parser.formula Formula_lexer.token (Lexing.from_channel ic)

let main () = 
  if !formulafile = "" then
    print_endline usage_string
  else
    begin
      let ic = open_in !formulafile in
      let f = try analyse_formulafile ic
      with e -> Printf.printf "Failed to parse formula file\n"; raise e
      in
        let f = if !negate then Neg f else f in
        let nf = Rewriting.normalize f in
        MFOTL.printnl_formula "The input formula is: " f;
        MFOTL.printnl_formula "The normalized formula is: " nf;
        Filter_empty_tp.fc_check_filterable_empty_tp nf;
    end

let _ = 
  Arg.parse 
    ["-formula", Arg.Set_string formulafile, "\tChoose the formula(s) file"; 
     "-negate", Arg.Set negate, "\tThe formula needs to be negated";
    ]
    (fun _ -> ())
    usage_string;
  main ()
