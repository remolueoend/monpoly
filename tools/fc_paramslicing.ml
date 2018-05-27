(*
 * Implements the labeling algorithm to check whether formula can be
 * monitored on a log slices by parameter.
 *)

open Misc
open Predicate
open MFOTL
open Formula_parser
open Lexing

let usage_string = 
  "Usage: fc-paramslicing [-negate] -formula <file> -param <variable>"

let formulafile = ref ""
let negate = ref false
let param = ref ""

let analyse_formulafile ic = 
  Formula_parser.formula Formula_lexer.token (Lexing.from_channel ic)

type label = 
  | PT
  | PF
  | PE

type 'a labeled = 
    'a * label list

type lformula =
  | LEqual of (term * term)
  | LLess of (term * term)
  | LPred of predicate
  | LNeg of lformula labeled
  (* | LAnd of (lformula labeled * lformula labeled) *)
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
  | PT -> Printf.printf "PT"
  | PF -> Printf.printf "PF"
  | PE -> Printf.printf "PE"

let rec print_labels = function
  | [] -> ()
  | h :: t -> print_label h;
    Printf.printf ", ";
    print_labels t

let print_labels_sorted labels =
  if has_label PT labels then
    print_label PT;
  if has_label PF labels then
    print_label PF;
  if has_label PE labels then
    print_label PE

let print_properties labels =
  (* we have a negated formula, so
     (C1) needs Invnfa (orig formula needs Invfa)
     (C2) needs Invex  (orig formula needs Invnex)
  *)
  if (has_label PF labels) || (has_label PE labels) then
    Printf.printf "(param-slicable)"

let intv_contains_zero = function
  | CBnd (0.0),_ ->
    (* Printf.printf "contains zero\n"; *)
    true
  | _ ->
    (* Printf.printf "excludes zero\n"; *)
    false

let pred_contains_param (param : var) (p : predicate) =
  let rec contains_param = function
    | [] -> false
    | Var v :: t -> 
      if (v = param) then
        true
      else
        contains_param t
    | _ :: t -> contains_param t
  in 
  let ret = contains_param (get_args p)
  in
  (* Printf.printf "contains_param(): param: %s, p: %s, ret: " *)
  (*   param (get_name p); *)
  (* if ret then *)
  (*     Printf.printf "true\n" *)
  (* else *)
  (*     Printf.printf "false\n"; *)
  ret


let add_labels (param: var) (lf : lformula) : label list =
  let labels = ref [] in
  (* single operator rules *)
  (match lf with
    | LEqual (_,_)
    | LLess (_,_) ->
      labels := add_label PE !labels;
    | LPred p ->
      (* distinguish whether sliced variable is present *)
      if (pred_contains_param param p) then
        labels := add_label PF !labels
      else 
        labels := add_label PE !labels
    | LNeg (f1, l1) ->
      if (has_label PT l1) then
        labels := add_label PF !labels
      else ();
      if (has_label PF l1) then
        labels := add_label PT !labels
      else ();
      if (has_label PE l1) then
        labels := add_label PE !labels
      else ();
    | LOr ((f1, l1), (f2, l2)) ->
      if (has_label PT l1) || (has_label PT l2) then
        labels := add_label PT !labels
      else ();
      if ((has_label PF l1) && (has_label PF l2)) then
        labels := add_label PF !labels
      else ();
      if ((has_label PE l1) && (has_label PE l2)) then
        labels := add_label PE !labels
      else ()
    | LExists (v, (f1, l1))
    | LForAll (v, (f1, l1)) -> 
      labels := l1
    | LPrev (intv, (f1, l1))
    | LNext (intv, (f1, l1)) ->
      if has_label PF l1 then
        labels := add_label PF !labels
      else ();
      if has_label PE l1 then
        labels := add_label PE !labels
      else ()
    | LEventually (intv, (f1, l1))
    | LOnce (intv, (f1, l1))
    | LAlways (intv, (f1, l1))
    | LPastAlways (intv, (f1, l1)) -> 
      labels := l1
    | LSince (intv, (f1, l1), (f2, l2))
    | LUntil (intv, (f1, l1), (f2, l2)) ->
      if (has_label PT l2) then
        labels := add_label PT !labels
      else ();
      if (has_label PF l2) then
        labels := add_label PF !labels
      else ();
      if (has_label PE l1) && (has_label PE l2) then
        labels := add_label PE !labels
      else ());
  !labels

(** recursively analyze and label a formula
    1) on the way down, build a labeled_formula from the formula
    2) on the way up add labels
    Input formula must be normalized (no Implies or Equiv)
*)
let rec go_down (param : var) (f : MFOTL.formula) : lformula labeled =
  let lf : lformula =  match f with
    | Equal (t1,t2) -> LEqual (t1,t2)
    | Less (t1,t2) -> LLess (t1,t2)
    | Pred p -> LPred p
    | Neg f -> LNeg (go_down param f)
    (* | And (f1,f2) -> LAnd ((go_down f1), (go_down f2)) *)
    | And (f1,f2) -> LNeg(go_down param (Or ((Neg f1), (Neg f2))))
    | Or (f1,f2) -> LOr ((go_down param f1), (go_down param f2))
    | Exists (vl,f) -> LExists (vl, (go_down param f))
    | ForAll (vl,f) -> LForAll (vl, (go_down param f))
    | Prev (i,f) -> LPrev (i, (go_down param f))
    | Next (i,f) -> LNext (i, (go_down param f))
    | Eventually (intv,f) -> LEventually (intv, (go_down param f))
    | Once (intv,f) -> LOnce (intv, (go_down param f))
    | Always (intv,f) -> LAlways (intv, (go_down param f))
    | PastAlways (intv,f) -> LPastAlways (intv, (go_down param f))
    | Since (i,f1,f2) -> LSince (i, (go_down param f1), (go_down param f2))
    | Until (i,f1,f2) -> LUntil (i, (go_down param f1), (go_down param f2))
    | Implies (f1,f2) -> failwith "fc.ml:go_down: formula contains Implies"
      (* (\* rewrite p => q to ~p or q *\) *)
      (* LOr ((go_down (Neg f1)), (go_down f2)) *)
    | Equiv (f1,f2) -> failwith "fc.ml:go_down: formula contains Equiv"
    | _ -> failwith "fc.ml:go_down: not yet"
  in
  let l = add_labels param lf
  in
  (lf, l)

let main () = 
  if !formulafile = "" then
    print_endline usage_string
  else if !param = "" then
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
        let lf, l = go_down !param nf in
        Printf.printf "Labels: ";
        print_labels_sorted l;
        Printf.printf "\n";
        Printf.printf "Properties: ";
        print_properties l;
        Printf.printf "\n\n";
    end


let _ = 
  Arg.parse 
    ["-formula", Arg.Set_string formulafile, "\tChoose the formula(s) file"; 
     "-negate", Arg.Set negate, "\tThe formula needs to be negated";
     "-param", Arg.Set_string param, "\tVariable for which we parametrize";
    ]
    (fun _ -> ())
    usage_string;
  main ()
