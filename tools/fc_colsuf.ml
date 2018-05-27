(*
 * Implements the labeling algorithm to check whether formula is
 * collapse-sufficient.
 *)

open Misc
open Predicate
open MFOTL
open Formula_parser
open Lexing

let usage_string = 
  "Usage: fc [-negate] -formula <file>"

let formulafile = ref ""   
let negate = ref false

let analyse_formulafile ic = 
  Formula_parser.formula Formula_lexer.token (Lexing.from_channel ic)

type label = 
  | Invfa
  | Invnfa
  | Invex
  | Invnex

type 'a labeled = 
    'a * label list

type lformula =
  | LEqual of (term * term)
  | LLess of (term * term)
  | LPred of predicate
  | LNeg of lformula labeled
  | LAnd of (lformula labeled * lformula labeled)
  | LOr of (lformula labeled * lformula labeled)
  (* | LImplies of (lformula labeled * lformula labeled) *)
  (* | LEquiv of (lformula labeled * lformula labeled) *)
  | LExists of (var list * lformula labeled)
  | LForAll of (var list * lformula labeled)
  | LPrev of (interval * lformula labeled)
  | LNext of (interval * lformula labeled)
  | LEventually of (interval * lformula labeled)
  | LOnce of (interval * lformula labeled)
  | LAlways of (interval * lformula labeled)
  | LPastAlways of (interval * lformula labeled)
  | LSince of (interval * lformula labeled * lformula labeled)
  | LUntil of (interval * lformula labeled * lformula labeled)


let has_label l labels = 
  List.mem l labels

let add_label l labels = 
  if has_label l labels
  then
    labels
  else
    l :: labels

let print_label = function
  | Invfa -> Printf.printf "(|= V)"
  | Invnfa -> Printf.printf "(|z V)"
  | Invex -> Printf.printf "(|= E)"
  | Invnex -> Printf.printf "(|z E)"

let rec print_labels = function
  | [] -> ()
  | h :: t -> print_label h;
    Printf.printf ", ";
    print_labels t

let print_labels_smart labels =
  if has_label Invfa labels then
    print_label Invfa
  else if has_label Invex labels then
    print_label Invex
  else ();
  Printf.printf ", ";
  if has_label Invnfa labels then
    print_label Invnfa
  else if has_label Invnex labels then
    print_label Invnex
  else ()

let print_properties labels =
  (* we have a negated formula, so
     (C1) needs Invnfa (orig formula needs Invfa)
     (C2) needs Invex  (orig formula needs Invnex)
  *)
  if has_label Invnfa labels then
    Printf.printf "(C1), "
  else ();
  if has_label Invex labels then
    Printf.printf "(C2)"
  else ()

let intv_contains_zero = function
  | CBnd (0.0),_ ->
    (* Printf.printf "contains zero\n"; *)
    true
  | _ ->
    (* Printf.printf "excludes zero\n"; *)
    false

let add_labels (lf : lformula) : label list =
  let labels = ref [] in
  (* single operator rules *)
  (match lf with
    | LEqual (_,_)
    | LLess (_,_) ->
      labels := add_label Invfa !labels;
      labels := add_label Invnfa !labels
    | LPred _ ->
      labels := add_label Invex !labels;
      labels := add_label Invnfa !labels
    | LNeg (f1, l1) ->
      if (has_label Invfa l1) then
        labels := add_label Invnfa !labels
      else ();
      if (has_label Invex l1) then
        labels := add_label Invnex !labels
      else ();
      if (has_label Invnfa l1) then
        labels := add_label Invfa !labels
      else ();
      if (has_label Invnex l1) then
        labels := add_label Invex !labels
      else ()
    | LAnd ((f1, l1), (f2, l2)) ->
      if (has_label Invfa l1) && (has_label Invfa l2) then
        labels := add_label Invfa !labels
      else ();
      if ((has_label Invfa l1) && (has_label Invex l2)) ||
        ((has_label Invfa l2) && (has_label Invex l1)) then
        labels := add_label Invex !labels
      else ();
      if (has_label Invnfa l1) && (has_label Invnfa l2) then
        labels := add_label Invnfa !labels
      else ();
      if ((has_label Invnex l1) && (has_label Invnex l2)) then
        labels := add_label Invnex !labels
      else ()
    | LOr ((f1, l1), (f2, l2)) ->
      if (has_label Invfa l1) && (has_label Invfa l2) then
        labels := add_label Invfa !labels
      else ();
      if ((has_label Invex l1) && (has_label Invex l2)) then
        labels := add_label Invex !labels
      else ();
      if (has_label Invnfa l1) && (has_label Invnfa l2) then
        labels := add_label Invnfa !labels
      else ();
      if ((has_label Invnfa l1) && (has_label Invnex l2)) ||
        ((has_label Invnfa l2) && (has_label Invnex l1)) then
        labels := add_label Invnex !labels
      else ()
    | LExists (v, (f1, l1)) -> 
      labels := l1
    | LForAll (v, (f1, l1)) -> 
      labels := l1
    | LEventually (intv, (f1, l1))
    | LOnce (intv, (f1, l1)) -> 
      if (has_label Invfa l1) then
        labels := add_label Invfa !labels
      else ();
      if (has_label Invex l1) then
        if intv_contains_zero intv then
          labels := add_label Invex !labels
        else
          labels := add_label Invfa !labels
      else ();
      if (has_label Invnfa l1) then
        labels := add_label Invnfa !labels
      else ()
    | LAlways (intv, (f1, l1))
    | LPastAlways (intv, (f1, l1)) -> 
      if (has_label Invfa l1) then
        labels := add_label Invfa !labels
      else ();
      if (has_label Invnfa l1) then
        labels := add_label Invnfa !labels
      else ();
      if (has_label Invnex l1) then
        if intv_contains_zero intv then
          labels := add_label Invnex !labels
        else
          labels := add_label Invnfa !labels
      else ()
    | LSince (intv, (f1, l1), (f2, l2)) ->
      if (has_label Invfa l1) && (has_label Invfa l2) then
        labels := add_label Invfa !labels
      else ();
      if (has_label Invnfa l1) && (has_label Invnfa l2) then
        labels := add_label Invnfa !labels
      else ();
      if (has_label Invnex l1) && (has_label Invnfa l2) then
        labels := add_label Invnex !labels
      else ()
    | LUntil (intv, (f1, l1), (f2, l2)) ->
      if (has_label Invfa l1) && (has_label Invfa l2) then
        labels := add_label Invfa !labels
      else ();
      if (has_label Invnfa l1) && (has_label Invnfa l2) then
        labels := add_label Invnfa !labels
      else ();
      if (has_label Invnex l1) && (has_label Invnfa l2) then
        labels := add_label Invnex !labels
      else ()
    | _ -> ());

  (* multiple operator rules *)
  (match lf with
    | LEventually (intv1, ((LOnce (intv2, (f1, l1))), _))
    | LOnce (intv1, ((LEventually (intv2, (f1, l1))), _)) ->
      if (has_label Invex l1) &&
        (intv_contains_zero intv1) && (intv_contains_zero intv2)
      then
        labels := add_label Invfa !labels
      else ()
    | LAlways (intv1, ((LPastAlways (intv2, (f1, l1))), _))
    | LPastAlways (intv1, ((LAlways (intv2, (f1, l1))), _)) ->
      if (has_label Invnex l1) &&
        (intv_contains_zero intv1) && (intv_contains_zero intv2)
      then
        labels := add_label Invnfa !labels
      else ()
    | LAnd( (LSince (intv1, (f1, l1), (f2, l2)), _),
            ((LAlways (intv3, (f3, l3))), _))
    | LAnd( ((LAlways (intv3, (f3, l3))), _),
            (LSince (intv1, (f1, l1), (f2, l2)), _)) ->
      if (has_label Invnex l1) && (has_label Invnfa l2) &&
        (not (intv_contains_zero intv1)) && (intv_contains_zero intv3)
      then
        labels := add_label Invnfa !labels
      else ()
    | LAnd( (LUntil (intv1, (f1, l1), (f2, l2)), _),
            ((LPastAlways (intv3, (f3, l3))), _))
    | LAnd( ((LPastAlways (intv3, (f3, l3))), _),
            (LUntil (intv1, (f1, l1), (f2, l2)), _)) ->
      if (has_label Invnex l1) && (has_label Invnfa l2) &&
        (not (intv_contains_zero intv1)) && (intv_contains_zero intv3)
      then
        labels := add_label Invnfa !labels
      else ()
    | LAnd( ((LPastAlways (intv1, (f1, l1))), _),
            (LAlways (intv2, (f2, l2)), _))
    | LAnd( ((LAlways (intv1, (f1, l1))), _),
            (LPastAlways (intv2, (f2, l2)), _)) ->
      if (has_label Invnex l1) && (has_label Invnex l2) &&
        (intv_contains_zero intv1) && (intv_contains_zero intv2)
        && (f1 = f2)
      then
        labels := add_label Invnfa !labels
      else ()
    | LOr( ((LOnce (intv1, (f1, l1))), _),
            (LEventually (intv2, (f2, l2)), _))
    | LOr( ((LEventually (intv1, (f1, l1))), _),
            (LOnce (intv2, (f2, l2)), _)) ->
      if (has_label Invex l1) && (has_label Invex l2) &&
        (intv_contains_zero intv1) && (intv_contains_zero intv2)
        && (f1 = f2)
      then
        labels := add_label Invfa !labels
      else ()
    | _ -> ());

  (* invariant weakening rules *)
  if (has_label Invfa !labels) then
    labels := add_label Invex !labels
  else ();
  if (has_label Invnfa !labels) then
    labels := add_label Invnex !labels
  else ();
  !labels

(** recursively analyze and label a formula
    1) on the way down, build a labeled_formula from the formula
    2) on the way up add labels
    Input formula must be normalized (no Implies or Equiv)
*)
let rec go_down (f : MFOTL.formula) : lformula labeled =
  let lf : lformula =  match f with
    | Equal (t1,t2) -> LEqual (t1,t2)
    | Less (t1,t2) -> LLess (t1,t2)
    | Pred p -> LPred p
    | Neg f -> LNeg (go_down f)
    | And (f1,f2) -> LAnd ((go_down f1), (go_down f2))
    | Or (f1,f2) -> LOr ((go_down f1), (go_down f2))
    | Exists (v,f) -> LExists (v, (go_down f))
    | ForAll (v,f) -> LForAll (v, (go_down f))
    | Prev (i,f) -> LPrev (i, (go_down f))
    | Next (i,f) -> LNext (i, (go_down f))
    | Eventually (intv,f) -> LEventually (intv, (go_down f))
    | Once (intv,f) -> LOnce (intv, (go_down f))
    | Always (intv,f) -> LAlways (intv, (go_down f))
    | PastAlways (intv,f) -> LPastAlways (intv, (go_down f))
    | Since (i,f1,f2) -> LSince (i, (go_down f1), (go_down f2))
    | Until (i,f1,f2) -> LUntil (i, (go_down f1), (go_down f2))
    | Implies (f1,f2) -> failwith "fc.ml:go_down: formula contains Implies"
      (* (\* rewrite p => q to ~p or q *\) *)
      (* LOr ((go_down (Neg f1)), (go_down f2)) *)
    | Equiv (f1,f2) -> failwith "fc.ml:go_down: formula contains Equiv"
    | _ -> failwith "fc.ml:go_down: not yet"
  in
  let l = add_labels lf
  in
  (lf, l)

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
        let lf, l = go_down nf in
        Printf.printf "Labels: ";
        print_labels_smart l;
        Printf.printf "\n";
        Printf.printf "Properties: ";
        print_properties l;
        Printf.printf "\n\n";
    end


let _ = 
  Arg.parse 
    ["-formula", Arg.Set_string formulafile, "\tChoose the formula(s) file"; 
     "-negate", Arg.Set negate, "\tThe formula needs to be negated";
    ]
    (fun _ -> ())
    usage_string;
  main ()
