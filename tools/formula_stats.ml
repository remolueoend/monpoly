open Libmonpoly
open MFOTL

module Pred_set = Set.Make (struct
  type t = string * int
  let compare = Stdlib.compare
end)

type result = {
  log_preds: Pred_set.t;
  conn: int;
  height: int;
  ntemp: int;
  temp_height: int;
  nlet: int;
}

let print_result r =
  Printf.printf "log_predicates:  %4d\n" (Pred_set.cardinal r.log_preds);
  Printf.printf "connectives:     %4d\n" r.conn;
  Printf.printf "temporal_conns:  %4d\n" r.ntemp;
  if r.nlet = 0 then
    begin
      Printf.printf "height:          %4d\n" r.height;
      Printf.printf "temporal_height: %4d\n" r.temp_height
    end
  else
    Printf.printf "let_bindings:    %4d\n" r.nlet

let result_of_pred lets (n, a, _) = {
  log_preds = if List.mem (n, a) lets then Pred_set.empty
    else Pred_set.singleton (n, a);
  conn = 0;
  height = 0;
  ntemp = 0;
  temp_height = 0;
  nlet = 0;
}

let result_of_atom = {
  log_preds = Pred_set.empty;
  conn = 0;
  height = 0;
  ntemp = 0;
  temp_height = 0;
  nlet = 0;
}

let lift_unary ~temporal r = { r with
  conn = r.conn + 1;
  height = r.height + 1;
  ntemp = if temporal then r.ntemp + 1 else r.ntemp;
  temp_height = if temporal then r.temp_height + 1 else r.temp_height;
}

let combine ~temporal l r = {
  log_preds = Pred_set.union l.log_preds r.log_preds;
  conn = l.conn + r.conn + 1;
  height = max l.height r.height + 1;
  ntemp = l.ntemp + r.ntemp + (if temporal then 1 else 0);
  temp_height = max l.temp_height r.temp_height + (if temporal then 1 else 0);
  nlet = l.nlet + r.nlet;
}

let lift_let l r = {
  log_preds = Pred_set.union l.log_preds r.log_preds;
  conn = l.conn + r.conn;
  height = max l.height r.height;
  ntemp = l.ntemp + r.ntemp;
  temp_height = max l.temp_height r.temp_height;
  nlet = l.nlet + r.nlet + 1;
}

let rec analyze lets f =
  let rec go = function
  | Equal _
  | Less _
  | LessEq _
  | Substring _
  | Matches _ -> result_of_atom
  | Pred p -> result_of_pred lets p
  | Let ((n, a, _), f1, f2) -> lift_let (go f1) (analyze ((n, a)::lets) f2)
  | LetPast ((n, a, _), f1, f2) ->
      let lets' = (n, a)::lets in
      lift_let (analyze lets' f1) (analyze lets' f2)
  | Neg f -> lift_unary ~temporal:false (go f)
  | And (f1, f2)
  | Or (f1, f2)
  | Implies (f1, f2)
  | Equiv (f1, f2) -> combine ~temporal:false (go f1) (go f2)
  | Exists (_, f)
  | ForAll (_, f)
  | Aggreg (_, _, _, _, _, f) -> lift_unary ~temporal:false (go f)
  | Prev (_, f)
  | Next (_, f)
  | Eventually (_, f)
  | Once (_, f)
  | Always (_, f)
  | PastAlways (_, f) -> lift_unary ~temporal:true (go f)
  | Since (_, f1, f2)
  | Until (_, f1, f2) -> combine ~temporal:true (go f1) (go f2)
  | Frex (_, r)
  | Prex (_, r) -> failwith "[analyze] not supported"
  in go f

let formulafile = ref ""
let sigfile = ref "" 

let analyse_formulafile ic = 
  let ic = open_in !formulafile in
  Formula_parser.formula Formula_lexer.token (Lexing.from_channel ic) 

let main () = 
  let sign = Log_parser.parse_signature_file !sigfile in
  let f = analyse_formulafile !formulafile in
  Rewriting.unfold_let := None;
  let _, pf_orig, _ = Rewriting.check_formula sign f in
  Rewriting.unfold_let := Some (Rewriting.ExpandAll);
  let _, pf_unfolded, _ = Rewriting.check_formula sign f in
  print_string "# without unfolding\n";
  print_result (analyze [] pf_orig);
  print_string "\n# with unfolding\n";
  print_result (analyze [] pf_unfolded)

let usage_string = "Usage: formula_stats -sig <file> -formula <file> [-no_rw]"

let _ = 
  Arg.parse [
    "-sig", Arg.Set_string sigfile, "\t\tChoose the signature file";
    "-formula", Arg.Set_string formulafile, "\tChoose the formula file"; 
    "-no_rw", Arg.Set Rewriting.no_rw, "\tNo formula rewrite";
    ]
    (fun _ -> ())
    usage_string;
  main ();
