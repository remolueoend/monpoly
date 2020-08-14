(********************************************************************
  MFOTL to SQL translation

  Author: Eugen Zalinescu (eugen.zalinescu@inf.ethz.ch)
  Copyright (C) 2013 ETHZ
  Version 0.1

*********************************************************************)


open Predicate
open MFOTL

(* We follow more or less the book "Foundations of Databases" 
   by Abiteboul, Hull, and Vianu. *)

type col = int 
type 'c col_eq = 'c * 'c
type 'c col_minus = 'c * 'c
type 'c col_expr = 'c col_minus (* only this is needed (for now?) *)

(* selection constraints *)
type 'c sel_constraint = 
  | Eq_Col of 'c * 'c
  | Eq_Val of 'c * cst
  | Eq_Null of 'c
  | NEq_Col of 'c * 'c
  | NEq_Val of 'c * cst
  | Less_Col of 'c * 'c
  | Less_Col_Val of 'c * cst
  | Less_Val_Col of cst * 'c
  | LEq_Col of 'c * 'c
  | LEq_Col_Val of 'c * cst
  | Leq_Val_Col of cst * 'c
  | Less_ColExpr_Val of ('c col_expr) * cst
  | Less_Val_ColExpr of cst * ('c col_expr)
  | LEq_ColExpr_Val of ('c col_expr) * cst
  | LEq_Val_ColExpr of cst * ('c col_expr)


(* expressions in (unnamed) relational algebra *)
type ra_expr = 
  | TCst of cst (* a unary table with one element *)
  | Table of string  (* name *)
  | Sel of col sel_constraint * ra_expr (* atomic selection, subsumed by generalized selection *)
  | Proj of col list * ra_expr (* the columns on which the projection is made *)
  | CrossProd of ra_expr * ra_expr 
  | Union of ra_expr * ra_expr
  | Diff of ra_expr * ra_expr
  | Inter of ra_expr * ra_expr
  | GSel of col sel_constraint list * ra_expr
  | EquiJoin of col col_eq list * ra_expr * ra_expr
  (* btw, the last 3 operators can be expressed in terms of the previous ones *) 
  | AntiJoin of col col_eq list * ra_expr * ra_expr (* only introduced because some RDBMSs do not support Diff *)

(* TODO: add function to check well-definedness *)

(* TODO: add function to transform expressions into normal form *)



(*** some auxiliary functions ***)

let tbl_time = "time"

let id = fun x -> x

let shift x = x + 2

let apply_shift = List.map shift

let string_of_list del f l = 
  let rec enum = function
    | [] -> ""
    | [h] -> f h 
    | h :: t -> (f h) ^ del ^ (enum t)
  in
  enum l


(* all integers between [m] and [n] *)
let all_ints m n =
  let rec f i acc = 
    if i < m then
      acc
    else
      f (i-1) (i :: acc)
  in
  f n []


let all_pos l = 
  let rec allpos i = function
    | [] -> []
    | _ :: t -> i :: allpos (i+1) t
  in
  allpos 0 l

let all_pos' l = 
  [0; 1] @ apply_shift (all_pos l)

let get_matches fv1 fv2 = 
  let rec matches crtpos = function
    | x :: t -> 
      (try
	 let pos2 = Misc.get_pos x fv2 in
	 (crtpos, pos2) :: (matches (crtpos + 1) t) 
       with Not_found -> 
	 matches (crtpos + 1) t
      )
    | [] -> []
  in
  matches 0 fv1


(* we return a cuple of selection constraints and of columns on which
   the table will be projected *)
(* we add 2 to each column: the first two columns are the timepoint and the timestamp *)
let get_constraints terms = 
  let rec get assign (constr, proj) pos = function
    | [] -> constr, proj
    | (Var x) :: rest ->      
      if List.mem_assoc x assign then
	(* we have seen this variable before; add a constraint *)
	let posx = List.assoc x assign in
	get 
	  assign 
	  (constr @ [Eq_Col (shift posx, shift pos)], proj)
	  (pos + 1) 
	  rest 
      else
	(* it is a new variable; we will project on it; remember it *)
	get 
	  ((x, pos) :: assign) 
	  (constr, proj @ [shift pos])
	  (pos + 1) 
	  rest 

    | (Cst c) :: rest -> 
      get assign (Eq_Val (shift pos, c) :: constr, proj) (pos + 1) rest 

    | _ -> failwith "[string_of_cst] function symbols not supported yet"
  in
  get [] ([], []) 0 terms




(* we follow the structure of Rewriting.is_monitorable *)
(* TODO: add assertions *)
let  mfotl2ra set_support f = 
  let rec tf = function
    | Pred p -> 
      let name, _, args = Predicate.get_info p in
      let constr, projs = get_constraints args in
      if projs = apply_shift (all_pos args) then
	if constr = [] then
	  Table name
	else
	  GSel (constr, Table name)
      else
	if constr = [] then
	  Proj ([0; 1] @ projs, Table name)
	else
	  Proj ([0; 1] @ projs, (GSel (constr, Table name)))

    | Neg f ->
      assert (MFOTL.free_vars f = []);
      let e = tf f in
      Diff (Table tbl_time, e)

    | And (f1, f2) -> 
      let fv1 = MFOTL.free_vars f1 in
      let e1 = tf f1 in
      (match f2 with
	| Equal (Var x, Var y) ->
	  if x = y then
	    e1
	  else
	    let bx = List.mem x fv1 in
	    let by = List.mem y fv1 in
	    if bx && by then (* hence both x and y are free in f1 *)
	      let posx = Misc.get_pos x fv1 in
	      let posy = Misc.get_pos y fv1 in
	      Sel (Eq_Col (shift posx, shift posy), e1)
	    else if bx then
	      let posx = Misc.get_pos x fv1 in
	      Proj ((all_pos' fv1) @ [shift posx], e1)
	    else if by then
	      let posy = Misc.get_pos y fv1 in
	      Proj ((all_pos' fv1) @ [shift posy], e1)
	    else 
	      failwith "[tf] f1 AND (x=y)"

	| Equal (Var x, Cst c)
	| Equal (Cst c, Var x) ->
	  if List.mem x fv1 then 
	  (* we select those tuples who's value of [x] is [c] *)
	    let posx = Misc.get_pos x fv1 in
	    Sel (Eq_Val (shift posx, c), e1)
	  else (* we add a new column in which all values are [c] *)
	    CrossProd (e1, TCst c)

	| Less (Cst c, Var y) -> 
	  let posy = Misc.get_pos y fv1 in
	  Sel (Less_Val_Col (c, shift posy), e1)

	| Less (Var x, Cst c) ->
	  let posx = Misc.get_pos x fv1 in
	  Sel (Less_Col_Val (shift posx, c), e1)

	| Less (Var x, Var y) ->
	  let posx = Misc.get_pos x fv1 in
	  let posy = Misc.get_pos y fv1 in
	  Sel (Less_Col (shift posx, shift posy), e1)

	| Neg (Equal (Var x, Var y)) -> 
	  let posx = Misc.get_pos x fv1 in
	  let posy = Misc.get_pos y fv1 in
	  Sel (NEq_Col (shift posx, shift posy), e1)

	| Neg (Equal (Var x, Cst c))
	| Neg (Equal (Cst c, Var x)) ->
	  let posx = Misc.get_pos x fv1 in
	  Sel (NEq_Val (shift posx, c), e1)

	| Neg (Less (Var x, Var y)) -> 
	  if x = y then (* then the formula f1 AND f2 is equiv. with f1 *)
	    e1
	  else
	    if List.mem x fv1 && List.mem y fv1 then
	      (* hence both x and y are free in f1 *)
	      let posx = Misc.get_pos x fv1 in
	      let posy = Misc.get_pos y fv1 in
	      Sel (LEq_Col (shift posy, shift posx), e1)
	    else
	      failwith "[mfotl2ra] f1 AND (NOT (x<y))"

	| Neg (Less (Cst c, Var y)) when (List.mem y fv1) ->
	  let posy = Misc.get_pos y fv1 in
	  Sel (LEq_Col_Val (shift posy, c), e1)

	| Neg f2' -> 
	  let e2 = tf f2' in
	  let fv2 = MFOTL.free_vars f2 in
	  assert (Misc.subset fv2 fv1);
	  let matches = get_matches fv1 fv2 in
	  let matches' = [(0, 0); (1, 1)] @ List.map (fun (x, y) -> (shift x, shift y)) matches in
	  if set_support then
	    if fv1 = fv2 then	     
	      Diff (e1, e2)
	    else	      
	      Diff (e1, (EquiJoin (matches', e1, e2)))
	  else
	    AntiJoin (matches', e1, e2)
	      
	| _ -> 
	  let e2 = tf f2 in
	  let fv2 = MFOTL.free_vars f2 in
	  if set_support && fv1 = fv2 then
	    Inter (e1, e2)
	  else
	    let matches = get_matches fv1 fv2 in
	    let matches' = [(0, 0); (1, 1)] @ List.map (fun (x, y) -> (shift x, shift y)) matches in	    
	    EquiJoin (matches', e1, e2)
      )
	
    | Or (f1, f2) -> Union (tf f1, tf f2)

    | Exists (xl, f) -> 
      let x = match xl with
	| [y] -> y
	| _ -> failwith "[mfotl2ra] cannot handles EX x,y.f yet"
      in
      let e = tf f in 
      let fv = MFOTL.free_vars f in 
      let rec pos i = function
	| [] -> []
	| h :: t -> 
	  let rest = pos (i+1) t in
	  if h = x then rest else i :: rest
      in
      let pos_proj = apply_shift (pos 0 fv) in
      Proj ([0; 1] @ pos_proj, e)

    | Once (intv, f) ->
      let e = tf f in
      let n = List.length (MFOTL.free_vars f) in
      (* the first two columns are the timepoint and the timestamp columns in Time,
	 the 3rd and 4th columns are the timepoint and the timestamp columns in [e] *)
      let proj = [0; 1] @ (all_ints 4 (n+3)) in
      let (l,r) = intv in
      let cst_of_ts ts = Int (int_of_float ts) in
      let bigger_than_l = function
	| CBnd a -> LEq_Val_ColExpr (cst_of_ts a, (1, 3))
	| OBnd a -> Less_Val_ColExpr (cst_of_ts a, (1, 3))
	| Inf -> failwith "[bigger_than_l] l <> Inf"
      in
      let smaller_than_r = function
	| CBnd b -> [LEq_ColExpr_Val ((1, 3), cst_of_ts b)]
	| OBnd b -> [Less_ColExpr_Val ((1, 3), cst_of_ts b)]
	| Inf -> []
      in
      let constraints = [LEq_Col (2, 0); bigger_than_l l] @ (smaller_than_r r) in
      Proj (proj, GSel (constraints, CrossProd ((Table tbl_time), e)))

    | Eventually (intv, f) -> 
      let e = tf f in
      let n = List.length (MFOTL.free_vars f) in
      (* the first two columns are the timepoint and the timestamp columns in Time,
	 the 3rd and 4th columns are the timepoint and the timestamp columns in [e] *)
      let proj = [0; 1] @ (all_ints 4 (n+3)) in
      let (l,r) = intv in
      let cst_of_ts ts = Int (int_of_float ts) in
      let bigger_than_l = function
	| CBnd a -> LEq_Val_ColExpr (cst_of_ts a, (3, 1))
	| OBnd a -> Less_Val_ColExpr (cst_of_ts a, (3, 1))
	| Inf -> failwith "[bigger_than_l] l <> Inf"
      in
      let smaller_than_r = function
	| CBnd b -> [LEq_ColExpr_Val ((3, 1), cst_of_ts b)]
	| OBnd b -> [Less_ColExpr_Val ((3, 1), cst_of_ts b)]
	| Inf -> []
      in
      let constraints = [LEq_Col (0, 2); bigger_than_l l] @ (smaller_than_r r) in
      Proj (proj, GSel (constraints, CrossProd ((Table tbl_time), e)))

    | Since (intv, Neg f1, f2) ->
      let fv1 = MFOTL.free_vars f1 in
      let fv2 = MFOTL.free_vars f2 in
      (* assert(Misc.subset fv1 fv2 && Misc.subset fv2 fv1); *)
      assert(Misc.subset fv1 fv2);
      let e1 = tf f1 in
      let e2 = tf f2 in
      let n = List.length fv1 in

      (* the first two columns are the timepoint and the timestamp columns in Time,
       the 3rd and 4th columns are the timepoint and the timestamp columns in [e] *)
      let (l,r) = intv in
      let cst_of_ts ts = Int (int_of_float ts) in
      let bigger_than_l = function
	| CBnd a -> LEq_Val_ColExpr (cst_of_ts a, (1, 3))
	| OBnd a -> Less_Val_ColExpr (cst_of_ts a, (1, 3))
	| Inf -> failwith "[bigger_than_l] l <> Inf"
      in
      let smaller_than_r = function
	| CBnd b -> [LEq_ColExpr_Val ((1, 3), cst_of_ts b)]
	| OBnd b -> [Less_ColExpr_Val ((1, 3), cst_of_ts b)]
	| Inf -> []
      in
      let constraints = [LEq_Col (2, 0); bigger_than_l l] @ (smaller_than_r r) in
      let e2' = GSel (constraints, CrossProd ((Table tbl_time), e2)) in
      let e1_time = GSel (constraints, CrossProd ((Table tbl_time), (Table tbl_time))) in
      let constraints' = [LEq_Col (4, 0); Less_Col (2, 4)] in
      let proj' = [0; 1; 2; 3] @ (all_ints 6 (n+5)) in
      let e1' = Proj (proj', GSel (constraints', CrossProd (e1_time, e1))) in
      let proj = [0; 1] @ (all_ints 4 (n+3)) in
      Proj (proj, Diff (e2', e1'))

    (* | Since (intv, f1, f2) ->  TODO *)
    (* need to rewrite \forall k. f1 as \neg\exists k.\neg f1 and push
       f2 inside the negation... *)

    | _ -> failwith "[mfotl2ra] either not possible or not yet implemented"
  in tf f


(** Pretty-printing RA expressions **)

let string_of_cst = function
  | Int n -> string_of_int n
  | Str s -> "'" ^ s ^ "'"
  | _ -> "[string_of_cst] function symbols not supported yet"

let string_of_sel f = function
  | Eq_Col (col, col') -> (f col) ^ " = " ^ (f col')
  | Eq_Val (col, c) -> (f col) ^ " = " ^ (string_of_cst c)
  | Eq_Null col -> (f col) ^ " IS NULL"
  | NEq_Col (col, col') -> (f col) ^ " <> " ^ (f col')
  | NEq_Val (col, c) -> (f col) ^ " <> " ^ (string_of_cst c)
  | Less_Col (col, col') -> (f col) ^ " < " ^ (f col')
  | Less_Col_Val (col, c) -> (f col) ^ " < " ^ (string_of_cst c)
  | Less_Val_Col (c, col) -> (string_of_cst c) ^ " < " ^ (f col)
  | LEq_Col (col, col') -> (f col) ^ " <= " ^ (f col')
  | LEq_Col_Val (col, c) -> (f col) ^ " <= " ^ (string_of_cst c)
  | Leq_Val_Col (c, col) -> (string_of_cst c) ^ " <= " ^ (f col)
  | Less_ColExpr_Val ((col, col'), c) -> (f col) ^ " - " ^ (f col') ^ " < " ^ (string_of_cst c) 
  | Less_Val_ColExpr (c, (col, col')) -> (string_of_cst c) ^ " < " ^ (f col) ^ " - " ^ (f col')
  | LEq_ColExpr_Val ((col, col'), c) -> (f col) ^ " - " ^ (f col') ^ " <= " ^ (string_of_cst c) 
  | LEq_Val_ColExpr (c, (col, col')) -> (string_of_cst c) ^ " <= " ^ (f col) ^ " - " ^ (f col')

let rec pr_string_of_ra ppf = function
  | TCst c -> 
    Format.fprintf ppf "@[<2>TCst %s@]" (string_of_cst c)

  | Table t -> 
    Format.fprintf ppf "@[<2>Table %s@]" t

  | Sel (sel, e) -> 
    Format.fprintf ppf "@[<2>Sel %s@\n%a@]" 
      (string_of_sel string_of_int sel) 
      pr_string_of_ra e

  | Proj (projs, e) -> 
    Format.fprintf ppf "@[<2>Proj %s@\n%a@]" 
      (string_of_list ", " string_of_int projs) 
      pr_string_of_ra e

  | CrossProd (e1, e2) -> 
    Format.fprintf ppf "@[<2>CrossProd@\n%a@\n%a@]" 
      pr_string_of_ra e1
      pr_string_of_ra e2

  | Union (e1, e2) -> 
    Format.fprintf ppf "@[<2>Union@\n%a@\n%a@]" 
      pr_string_of_ra e1
      pr_string_of_ra e2

  | Diff (e1, e2) -> 
    Format.fprintf ppf "@[<2>Diff@\n%a@\n%a@]" 
      pr_string_of_ra e1
      pr_string_of_ra e2

  | Inter (e1, e2) -> 
    Format.fprintf ppf "@[<2>Inter@\n%a@\n%a@]" 
      pr_string_of_ra e1
      pr_string_of_ra e2

  | GSel (sels, e) -> 
    Format.fprintf ppf "@[<2>GSel %s@\n%a@]" 
      (string_of_list ", " (string_of_sel string_of_int) sels)
      pr_string_of_ra e

  | EquiJoin (cols, e1, e2) -> 
    Format.fprintf ppf "@[<2>EquiJoin %s@\n%a@\n%a@]" 
      (string_of_list ", " (fun (x, y) -> (string_of_int x) ^ " = " ^ (string_of_int y)) cols) 
      pr_string_of_ra e1
      pr_string_of_ra e2

  | AntiJoin (cols, e1, e2) -> 
    Format.fprintf ppf "@[<2>AntiJoin %s@\n%a@\n%a@]" 
      (string_of_list ", " (fun (x, y) -> (string_of_int x) ^ " = " ^ (string_of_int y)) cols) 
      pr_string_of_ra e1
      pr_string_of_ra e2

(* let string_of_ra e =  *)
(*   pr_string_of_ra Format.str_formatter e; *)
(*   Format.print_flush(); *)
(*   (\* Format.print_newline (); *\) *)
(*   let s = Buffer.contents Format.stdbuf in *)
(*   Buffer.clear Format.stdbuf; *)
(*   s *)

let print_ra e = 
  pr_string_of_ra Format.std_formatter e







(*** unnamed RA to named RA ***)

type orig = S | L | R (* from left or right child, or from (it)self *)
type att_name = orig * string

(* expressions in (unnamed) relational algebra *)
type nra_expr = 
  | NTCst of att_name list * cst 
  | NTable of att_name list * string
  | NSel of att_name list * att_name sel_constraint * nra_expr 
  | NProj of att_name list * nra_expr 
  | NCrossProd of att_name list * nra_expr * nra_expr 
  | NUnion of att_name list * nra_expr * nra_expr
  | NDiff of att_name list * nra_expr * nra_expr
  | NInter of att_name list * nra_expr * nra_expr
  | NGSel of att_name list * att_name sel_constraint list * nra_expr
  | NEquiJoin of att_name list * att_name col_eq list * nra_expr * nra_expr
  | NAntiJoin of att_name list * att_name col_eq list * nra_expr * nra_expr
  | NRename of att_name list * nra_expr


let get_atts e = 
  match e with
    | NRename (a, _)
    | NTCst (a, _)
    | NTable (a, _)
    | NSel (a, _, _) 
    | NProj (a, _) 
    | NCrossProd (a, _, _) 
    | NUnion (a, _, _) 
    | NDiff (a, _, _) 
    | NInter (a, _, _) 
    | NGSel (a, _, _)
    | NEquiJoin (a, _, _, _)
    | NAntiJoin (a, _, _, _) -> a


let atts_mem x atts =
  List.mem (snd x) (List.map snd atts)

let tf_sel atts sel = 
  let nb = List.length atts in
  let nth_in n = 
    assert (n < nb);
    List.nth atts n 
  in
  match sel with
    | Eq_Col (pos, pos') -> Eq_Col (nth_in pos, nth_in pos')
    | Eq_Val (pos, c) -> Eq_Val (nth_in pos, c)
    | Eq_Null pos -> Eq_Null (nth_in pos)
    | NEq_Col (pos, pos') -> NEq_Col (nth_in pos, nth_in pos')
    | NEq_Val (pos, c) -> NEq_Val (nth_in pos, c)
    | Less_Col (pos, pos') -> Less_Col (nth_in pos, nth_in pos')
    | Less_Col_Val (pos, c) -> Less_Col_Val (nth_in pos, c)
    | Less_Val_Col (c, pos) -> Less_Val_Col (c, nth_in pos)
    | LEq_Col (pos, pos') -> LEq_Col (nth_in pos, nth_in pos')
    | LEq_Col_Val (pos, c) -> LEq_Col_Val (nth_in pos, c)
    | Leq_Val_Col (c, pos) -> Leq_Val_Col (c, nth_in pos)
    | Less_ColExpr_Val ((pos, pos'), c) -> Less_ColExpr_Val ((nth_in pos, nth_in pos'), c)
    | Less_Val_ColExpr (c, (pos, pos')) -> Less_Val_ColExpr (c, (nth_in pos, nth_in pos'))
    | LEq_ColExpr_Val ((pos, pos'), c) -> LEq_ColExpr_Val ((nth_in pos, nth_in pos'), c)
    | LEq_Val_ColExpr (c, (pos, pos')) -> LEq_Val_ColExpr (c, (nth_in pos, nth_in pos'))


let tf_projs atts projs = 
  let n = List.length atts in
  (* print_endline ("[tf_projs] atts: " ^ string_of_list ", " id atts); *)
  List.map (fun i -> 
    assert (i < n);
    List.nth atts i
  ) projs

let tf_eq_cols atts1 atts2 eq_cols = 
  let n1 = List.length atts1 in
  let n2 = List.length atts1 in
  List.map (fun (i1, i2) -> 
    assert (i1 < n1);
    assert (i2 < n2);
    List.nth atts1 i1, List.nth atts2 i2
  ) eq_cols


let ra2nra e atts = 
  let c = ref 0 in
  let rec trans e = 
    match e with
      | TCst a -> 
	NTCst ([S, "x" ^ (incr c; string_of_int !c)], a)

      | Table t -> 
	let att_names = List.map (fun (name, _) -> (S, name)) (List.assoc t atts) in
	(* print_endline ("[trans, Table] " ^ t ^ " a: " ^ string_of_list ", " id att_names); *)
	NTable (att_names, t)

      | Sel (sel, e) -> 
	let e' = trans e in
	let a = get_atts e' in
	(* print_endline ("[trans, Sel] a: " ^ string_of_list ", " id a); *)
	NSel (a, tf_sel a sel, e')

      | Proj (projs, e) -> 
	let e' = trans e in
	let a = get_atts e' in
	let a' = tf_projs a projs in
	(* print_endline ("[trans, Proj] a: " ^ string_of_list ", " id a); *)
	(* print_endline ("[trans, Proj] a': " ^ string_of_list ", " id a'); *)
	NProj (a', e')

      | CrossProd (e1, e2) -> 
	let e1' = trans e1 in
	let atts1 = get_atts e1' in
	let e2' = trans e2 in
	let atts2 = get_atts e2' in
	let atts2' = 
	  let rec rename_duplicates = function
	    | [] -> []
	    | (o, a) as h :: rest -> 
	      if atts_mem h atts1 then
		(o, (a ^ "_bis")) :: (rename_duplicates rest)
	      else
		h :: rename_duplicates rest 
	  in
	  rename_duplicates atts2 
	in
	(* print_endline ("[trans, CrossProd] a1: " ^ string_of_list ", " id a1); *)
	(* print_endline ("[trans, CrossProd] a2': " ^ string_of_list ", " id a2'); *)
	let upd_atts1 = List.map (fun (_, a) -> (L, a)) atts1 in
	let upd_atts2 = List.map (fun (_, a) -> (R, a)) atts2' in
	NCrossProd (upd_atts1 @ upd_atts2, e1', NRename (atts2', e2'))

      | Union (e1, e2) -> 
	let e1' = trans e1 in
	let a1 = get_atts e1' in
	let e2' = trans e2 in
	let a2 = get_atts e2' in
	assert (List.length a1 = List.length a2);
	NUnion (a1, e1', e2')

      | Diff (e1, e2) -> 
	let e1' = trans e1 in
	let a1 = get_atts e1' in
	let e2' = trans e2 in
	let a2 = get_atts e2' in
	(* print_endline ("[trans, Diff] a1: " ^ string_of_list ", " id a1); *)
	(* print_endline ("[trans, Diff] a2: " ^ string_of_list ", " id a2); *)
	assert (List.length a1 = List.length a2);
	NDiff (a1, e1', e2')

      | Inter (e1, e2) -> 
	let e1' = trans e1 in
	let a1 = get_atts e1' in
	let e2' = trans e2 in
	let a2 = get_atts e2' in
	assert (List.length a1 = List.length a2);
	NInter (a1, e1', e2')

      | GSel (sel, e) -> 
	let e' = trans e in
	let a = get_atts e' in
	(* print_endline ("[trans, GSel] a: " ^ string_of_list ", " id a); *)
	NGSel (a, List.map (tf_sel a) sel, e')

      | EquiJoin (eq_cols, e1, e2) -> 
	let e1' = trans e1 in
	let atts1 = get_atts e1' in
	let e2' = trans e2 in
	let atts2 = get_atts e2' in
	let n_eq_cols = tf_eq_cols atts1 atts2 eq_cols in
	let ncols2 = List.map snd n_eq_cols in
	let a1 = List.map snd atts1 in
	let atts2', new_atts2 = 
	  let rec elim_and_rename = function
	    | [] -> [], []
	    | (o, a) as h :: rest -> 
	      let all_atts2, not_in_atts1 = elim_and_rename rest in
	      if List.mem h ncols2 then (* this column is matched, hence also in a1 *)
		h :: all_atts2, not_in_atts1
	      else
		if List.mem a a1 then 
		  let renamed_h = (o, a ^ "_bis") in
		  renamed_h :: all_atts2, renamed_h :: not_in_atts1
		else
		  h :: all_atts2, h :: not_in_atts1
	  in	
	  elim_and_rename atts2
	in
	let upd_atts1 = List.map (fun (_, a) -> (L, a)) atts1 in
	let upd_atts2 = List.map (fun (_, a) -> (R, a)) new_atts2 in
	(* print_endline ("[trans, EquiJoin] atts1: " ^ string_of_list ", " f atts1); *)
	(* print_endline ("[trans, EquiJoin] atts2: " ^ string_of_list ", " f atts2); *)
	(* print_endline ("[trans, EquiJoin] atts2': " ^ string_of_list ", " f atts2'); *)
	NEquiJoin (upd_atts1 @ upd_atts2, n_eq_cols, e1', NRename (atts2', e2'))

      | AntiJoin (eq_cols, e1, e2) -> 
	(* failwith "[ra2nra] AntiJoin translation not implemented yet" *)
	let e1' = trans e1 in
	let atts1 = get_atts e1' in
	let e2' = trans e2 in
	let atts2 = get_atts e2' in
	let n_eq_cols = tf_eq_cols atts1 atts2 eq_cols in
	let ncols2 = List.map snd n_eq_cols in
	let atts2', new_atts2 = 
	  let rec elim_and_rename = function
	    | [] -> [], []
	    | (o,a) as h :: rest -> 
	      let all_atts2, not_in_atts1 = elim_and_rename rest in
	      if List.mem h ncols2 then (* this column is matched, hence also in atts1 *)
		h :: all_atts2, not_in_atts1
	      else
		if List.mem h atts1 then 
		  let renamed_h = (o, a ^ "_bis") in
		  renamed_h :: all_atts2, renamed_h :: not_in_atts1
		else
		  h :: all_atts2, h :: not_in_atts1
	  in	
	  elim_and_rename atts2
	in
	let upd_atts1 = List.map (fun (_, a) -> (L, a)) atts1 in
	let upd_atts2 = List.map (fun (_, a) -> (R, a)) new_atts2 in
	(* print_endline ("[trans, AntiJoin] atts1: " ^ string_of_list ", " id atts1); *)
	(* print_endline ("[trans, AntiJoin] atts2: " ^ string_of_list ", " id atts2); *)
	(* print_endline ("[trans, AntiJoin] atts2': " ^ string_of_list ", " id atts2'); *)
	NAntiJoin (upd_atts1 @ upd_atts2, n_eq_cols, e1', NRename (atts2', e2'))

  in 
  trans e

(** Pretty-printing named RA expressions **)

let string_of_orig = function
  | L -> "L"
  | R -> "R"
  | S -> "S"

let string_of_oatt (o, a) = 
  (string_of_orig o) ^ "." ^ a

let string_of_atts atts = 
  "[" ^ (string_of_list ", " string_of_oatt atts) ^ "]"



let rec pr_string_of_nra ppf = function
  | NRename (a, e) -> 
    Format.fprintf ppf "@[<2>NRename %s@\n%a@]" 
      (string_of_atts a) 
      pr_string_of_nra e

  | NTCst (a, c) -> 
    Format.fprintf ppf "@[<2>NTCst %s %s@]" 
      (string_of_atts a) (string_of_cst c)

  | NTable (a, t) -> 
    Format.fprintf ppf "@[<2>NTable %s %s@]" 
      (string_of_atts a) t

  | NSel (a, sel, e) -> 
    Format.fprintf ppf "@[<2>NSel %s %s@\n%a@]" 
      (string_of_atts a)
      (string_of_sel string_of_oatt sel)
      pr_string_of_nra e

  | NProj (projs, e) -> 
    Format.fprintf ppf "@[<2>NProj %s@\n%a@]" 
      (string_of_atts projs)
      pr_string_of_nra e

  | NCrossProd (a, e1, e2) -> 
    Format.fprintf ppf "@[<2>NCrossProd %s@\n%a@\n%a@]" 
      (string_of_atts a)
      pr_string_of_nra e1
      pr_string_of_nra e2

  | NUnion (a, e1, e2) -> 
    Format.fprintf ppf "@[<2>NUnion %s@\n%a@\n%a@]" 
      (string_of_atts a)
      pr_string_of_nra e1
      pr_string_of_nra e2

  | NDiff (a, e1, e2) -> 
        Format.fprintf ppf "@[<2>NDiff %s@\n%a@\n%a@]" 
      (string_of_atts a)
      pr_string_of_nra e1
      pr_string_of_nra e2

  | NInter (a, e1, e2) -> 
    Format.fprintf ppf "@[<2>NInter %s@\n%a@\n%a@]" 
      (string_of_atts a)
      pr_string_of_nra e1
      pr_string_of_nra e2

  | NGSel (a, sels, e) -> 
    Format.fprintf ppf "@[<2>NGSel %s %s@\n%a@]" 
      (string_of_atts a)
      (string_of_list ", " (string_of_sel string_of_oatt) sels)
      pr_string_of_nra e

  | NEquiJoin (a, cols, e1, e2) -> 
    Format.fprintf ppf "@[<2>NEquiJoin %s %s@\n%a@\n%a@]" 
      (string_of_atts a)
      (string_of_list ", " 
	 (fun (x, y) -> 
	    (string_of_oatt x) ^ " = " ^ (string_of_oatt y))
	 cols) 
      pr_string_of_nra e1
      pr_string_of_nra e2

  | NAntiJoin (a, cols, e1, e2) -> 
    Format.fprintf ppf "@[<2>NAntiJoin %s %s@\n%a@\n%a@]" 
      (string_of_atts a)
      (string_of_list ", " 
	 (fun (x, y) -> 
	    (string_of_oatt x) ^ " = " ^ (string_of_oatt y))
	 cols) 
      pr_string_of_nra e1
      pr_string_of_nra e2


let print_nra e = 
  pr_string_of_nra Format.std_formatter e


(*** RA to SQL ***)


type col_name = string
type tbl_name = string
type col_spec = tbl_name * col_name * col_name option (* last argument is used for renaming *)

type sql_table_ref  = (* a table reference always has a name *)
  | SQL_table_name of tbl_name
  | SQL_subquery of tbl_name * sql_query 
  | SQL_join of tbl_name * (col_spec * col_spec) list * sql_table_ref * sql_table_ref
  | SQL_left_join of tbl_name * (col_spec * col_spec) list * sql_table_ref * sql_table_ref
and 
sql_query = 
  | SQL_value of cst
  | SQL_select of col_spec list * bool * col_spec sel_constraint list * sql_table_ref list
  | SQL_union of sql_query * sql_query 
  | SQL_diff of sql_query * sql_query 
  | SQL_inter of sql_query * sql_query 


type transf_aux = 
  | Aux_tables of col_spec list * bool * col_spec sel_constraint list * sql_table_ref list
  | Aux_query of sql_query



let aux2query = function
  | Aux_query q -> q
  | Aux_tables (cols, b, sels, tblsl) -> SQL_select (cols, b, sels, tblsl)

let new_name c = 
  incr c;
  ("T" ^ string_of_int !c)

let aux2subquery c aux = 
  let q = aux2query aux in
  SQL_subquery (new_name c, q) 


let get_name = function
  | SQL_table_name t
  | SQL_subquery (t, _)
  | SQL_join (t, _, _, _)
  | SQL_left_join (t, _, _, _)
    -> t

let get_tbl_name o tbl_names = 
  match tbl_names  with
    | [name1; name2] -> 
	(match o with
	  | L -> name1
	  | R -> name2
	  | S -> ""
	)
    | _ -> ""

let sel_map f = function
  | Eq_Col (col, col') -> Eq_Col (f col, f col')
  | Eq_Val (col, c) -> Eq_Val (f col, c)
  | Eq_Null col -> Eq_Null (f col)
  | NEq_Col (col, col') -> NEq_Col (f col, f col')
  | NEq_Val (col, c) -> NEq_Val (f col, c)
  | Less_Col (col, col') -> Less_Col (f col, f col')
  | Less_Col_Val (col, c) -> Less_Col_Val (f col, c)
  | Less_Val_Col (c, col) -> Less_Val_Col (c, f col)
  | LEq_Col (col, col') -> LEq_Col (f col, f col')
  | LEq_Col_Val (col, c) -> LEq_Col_Val (f col, c)
  | Leq_Val_Col (c, col) -> Leq_Val_Col (c, f col)
  | Less_ColExpr_Val ((col, col'), c) -> 
      Less_ColExpr_Val ((f col, f col'), c)
  | Less_Val_ColExpr (c, (col, col')) -> 
      Less_Val_ColExpr (c, (f col, f col'))
  | LEq_ColExpr_Val ((col, col'), c) -> 
      LEq_ColExpr_Val ((f col, f col'), c)
  | LEq_Val_ColExpr (c, (col, col')) -> 
      LEq_Val_ColExpr (c, (f col, f col'))

	      
    
(* idea: selections and projections accumulate *)
let nra2sql e = 
  let c = ref 0 in
  let rec transf = function
    | NTCst (_, c) -> Aux_query (SQL_value c)

    | NTable (atts, name) -> 
      let tbl_name = "tbl_" ^ name in
      let cols = List.map (fun (orig, a) -> (tbl_name, a, None)) atts in
      Aux_tables (cols, true, [], [SQL_table_name tbl_name])

    | NSel (a, sel, e) -> 
	transf (NGSel (a, [sel], e))

    | NGSel (_, sels, e) ->
	(match transf e with
	   | Aux_tables (proj, b, lower_sels, tbls) ->
	       let tbl_names = List.map get_name tbls in
	       let sels' = List.map 
		 (sel_map (fun (o, a) -> (get_tbl_name o tbl_names, a, None)))
		 sels 
	       in
	       Aux_tables (proj, b, sels' @ lower_sels, tbls)

	   | Aux_query q -> 
	       (* let tbl_name = new_name c in *)
	       let sels' = List.map (sel_map (fun (o, a) -> ("", a, None))) sels in
	       Aux_tables ([], true, sels', [SQL_subquery (new_name c, q)])
	)

    | NProj (projs, e) ->	
	(match transf e with
	   | Aux_tables (cols, _, sels, tbls) -> 
	       let tbl_names = 
		 match tbls with
		   | [SQL_join (_, _, sq1, sq2)] -> [get_name sq1; get_name sq2]
		   | [SQL_left_join (_, _, sq1, sq2)] -> [get_name sq1; get_name sq2]
		   | _ -> List.map get_name tbls 
	       in
	       let projs' = List.map 
		 (fun (o, a) -> (get_tbl_name o tbl_names, a, None)) 
		 projs 
	       in
	       Aux_tables (projs', false, sels, tbls)

	   | Aux_query q -> 
	     let projs' = List.map (fun (o, a) -> ("", a, None)) projs in
	     Aux_tables (projs', false, [], [SQL_subquery (new_name c, q)])
	)

    | NUnion (_, e1, e2) ->
	(* build now the queries and then take the union *)
	let q1 = aux2query (transf e1) in
	let q2 = aux2query (transf e2) in
	Aux_query (SQL_union (q1, q2))

    | NDiff (_, e1, e2) ->
	(* build now the queries and then take the union *)
	let q1 = aux2query (transf e1) in
	let q2 = aux2query (transf e2) in
	Aux_query (SQL_diff (q1, q2))

    | NInter (_, e1, e2) ->
	(* build now the queries and then take the union *)
	let q1 = aux2query (transf e1) in
	let q2 = aux2query (transf e2) in
	Aux_query (SQL_inter (q1, q2))

    | NCrossProd (atts, e1, e2) ->
	let sq1 = aux2subquery c (transf e1) in
	let sq2 = aux2subquery c (transf e2) in
	(* let a1 = get_atts e1 in *)
	let atts' = List.map 
	  (fun (o, a) -> 
	     match o with
	       | L -> (get_name sq1), a, None
	       | R -> (get_name sq2), a, None
	       | S -> failwith "[nra2sql, NCrossProd] impossible"
	  )
	  atts
	in
	Aux_tables (atts', true, [], [sq1; sq2])

    | NEquiJoin (atts, cols, e1, e2) -> 
	let atts', sq1, sq2 = transf_join c atts e1 e2 in
	let tbl1, tbl2 = get_name sq1, get_name sq2 in
	let cols' = List.map 
	  (fun ((o1, a1), (o2, a2)) -> (tbl1, a1, None), (tbl2, a2, None)) 
	  cols 
	in
	Aux_tables (atts', false, [], [SQL_join (new_name c, cols', sq1, sq2)])

    | NAntiJoin (atts, cols, e1, e2) -> 
	let atts', sq1, sq2 = transf_join c atts e1 e2 in
	let tbl1, tbl2 = get_name sq1, get_name sq2 in
	let (_, aname) = List.hd (get_atts e2) in
	let a = (tbl2, aname, None) in
	(* assert (List.mem a atts'); *)
	let cols' = List.map 
	  (fun ((o1, a1), (o2, a2)) -> (tbl1, a1, None), (tbl2, a2, None)) 
	  cols 
	in
	Aux_tables (atts', false, [Eq_Null a], [SQL_left_join (new_name c, cols', sq1, sq2)])

    | NRename (atts, e) ->
	(match transf e with
	   | Aux_query q -> transf e (* failwith "[nra2sql] renaming unclear" *)
	   | Aux_tables (cols, _, sels, tbls) -> 
	       let old_atts = get_atts e in
	       let att_names = List.map snd old_atts in
	       let cols' = List.map 
		 (fun (tn, x, x') ->
		    match x' with
		      | None -> 			  
			  if List.mem x att_names then
			    let pos = Misc.get_pos x att_names in
			    let new_x = List.nth atts pos in
			    if x = snd new_x then
			      (tn, x, None)
			    else
			      (tn, x, Some (snd new_x))
			  else
			    (tn, x, None)
		      | Some new_x -> 
			  if List.mem x att_names then
			    failwith "[nra2sql] double renaming"
			  else
			    if x = new_x then
			      (tn, x, None)
			    else
			      (tn, x, Some new_x)
		 ) cols 
	       in
	       Aux_tables (cols', false, sels, tbls)
	)	  
  and 
      transf_join c atts e1 e2 =
    let sq1 = aux2subquery c (transf e1) in
    let sq2 = aux2subquery c (transf e2) in
    let atts1 = get_atts e1 in
    let atts2 = get_atts e2 in
    let atts' = List.map 
      (fun a -> 
	 let orig, aname = a in
	 match orig with
	   | L -> 
	       assert (atts_mem a atts1);
	       (get_name sq1), aname, None
	   | R ->
	       assert (atts_mem a atts2);
	       (get_name sq2), aname, None
	   | S -> 
	       if atts_mem a atts1 then	  
		 (get_name sq1), aname, None
	       else 
		 (get_name sq2), aname, None
      )
      atts 
    in
    atts', sq1, sq2
  in
  aux2query (transf e)











(** Pretty-printing SQL queries **)

let string_of_col_spec no_tbl (tn, x, x') =
  let str = 
    match x' with
      | None -> x
      | Some new_x -> x ^ " AS " ^ new_x
  in
  if tn = "" || no_tbl then
    str
  else
    tn ^ "." ^ str


let is_table tbl_refs = 
  match tbl_refs with
    | [SQL_table_name _] -> true
    | _ -> false

let rec pr_string_of_query ppf = function
  | SQL_value c -> (* TODO: we need to give a name to the column *)
    Format.fprintf ppf "@[ SELECT %s @]" (string_of_cst c)

  | SQL_select (cols, all, sels, tbls) ->
    (* assert (cols <> []); *)
    assert (tbls <> []);
    let string_of_cols = string_of_col_spec (is_table tbls) in
    let cols_str = string_of_list ", " string_of_cols cols  in
    let sels_str = string_of_list  " AND " 
      (string_of_sel string_of_cols) 
      sels 
    in
    let select_str = 
      if cols_str = "" || all then "SELECT *" else "SELECT " ^ cols_str
    in
    Format.fprintf ppf "@[@[%s@]@ @[FROM %a@]" select_str pr_string_of_table_refs tbls;
    if sels_str = "" then
      Format.fprintf ppf "@]"
    else
      Format.fprintf ppf "@ WHERE %s@]" sels_str

  | SQL_union (q1, q2) ->
    Format.fprintf ppf "@[  (%a)@\nUNION@\n  (%a)@]" 
      pr_string_of_query q1
      pr_string_of_query q2

  | SQL_diff (q1, q2) ->
    Format.fprintf ppf "@[  (%a)@\nEXCEPT@\n  (%a)@]" 
      pr_string_of_query q1
      pr_string_of_query q2

  | SQL_inter (q1, q2) ->
    Format.fprintf ppf "@[  (%a)@\nINTERSECT@\n  (%a)@]" 
      pr_string_of_query q1
      pr_string_of_query q2

and pr_string_of_table_ref ppf = function
  | SQL_table_name name -> Format.fprintf ppf "%s" name

  | SQL_subquery (name, q) ->
    Format.fprintf ppf "@[(%a) AS %s@]" 
      pr_string_of_query q name

  | SQL_join (name, eq_cols, tbl1, tbl2) ->
    (* let t1 = get_name tbl1 in *)
    (* let t2 = get_name tbl2 in *)
    let cols_str = string_of_list 
      " AND " 
      (fun ((t1,x,_), (t2,y,_)) -> t1 ^ "." ^ x ^ " = " ^ t2 ^ "." ^ y) 
      eq_cols 
    in
    let fmt = 
      match tbl1, tbl2 with
	| SQL_table_name _,  SQL_table_name _ -> 
	  format_of_string "@[%a@ JOIN@ %a@ @[ON %s@]@]" 
	| SQL_table_name _, _ -> 
	  format_of_string "@[%a@ JOIN@\n  %a@ @[ON %s@]@]" 
	| _, SQL_table_name _ -> 
	  format_of_string "@[  %a@\nJOIN@ %a@ @[ON %s@]@]" 
	| _ -> format_of_string 
	  "@[  %a@\nJOIN@\n  %a@ @[ON %s@]@]"
    in
    Format.fprintf ppf fmt
      pr_string_of_table_ref tbl1
      pr_string_of_table_ref tbl2
      cols_str

  | SQL_left_join (name, eq_cols, tbl1, tbl2) ->
    let cols_str = string_of_list 
      " AND " 
      (fun ((t1,x,_), (t2,y,_)) -> t1 ^ "." ^ x ^ " = " ^ t2 ^ "." ^ y) 
      eq_cols 
    in
    let fmt = 
      match tbl1, tbl2 with
	| SQL_table_name _,  SQL_table_name _ -> 
	  format_of_string "@[%a@ LEFT JOIN@ %a@ @[ON %s@]@]" 
	| SQL_table_name _, _ -> 
	  format_of_string "@[%a@ LEFT JOIN@\n  %a@ @[ON %s@]@]" 
	| _, SQL_table_name _ -> 
	  format_of_string "@[  %a@\nLEFT JOIN@ %a@ @[ON %s@]@]" 
	| _ -> format_of_string 
	  "@[  %a@\nLEFT JOIN@\n  %a@ @[ON %s@]@]"
    in
    Format.fprintf ppf fmt
      pr_string_of_table_ref tbl1
      pr_string_of_table_ref tbl2
      cols_str

and pr_string_of_table_refs ppf = function
  | [t] -> Format.fprintf ppf "%a" pr_string_of_table_ref t
  | [t1; t2] -> 
    Format.fprintf ppf "%a,@;<1 5>%a" 
      pr_string_of_table_ref t1
      pr_string_of_table_ref t2
  | _ -> failwith "[pr_string_of_table_refs] internal error"

(* let string_of_query q =  *)
(*   pr_string_of_query Format.str_formatter q; *)
(*   Format.print_flush(); *)
(*   let s = Buffer.contents Format.stdbuf in *)
(*   Buffer.clear Format.stdbuf; *)
(*   s *)


let print_query q = 
  pr_string_of_query Format.std_formatter q






(*** Usage ***)


let usage_string = "mfotl2sql -sig <sig_file> -formula <formula_file> [-negate] [-no_set_support] [-debug <unit>]"

let formulafile = ref ""
let sigfile = ref "" 
let negate = ref false
let no_set_support = ref false
let debug = ref ""
let debug_tf = ref false

let analyse_formulafile ic = 
  let ic = open_in !formulafile in
  Formula_parser.formula Formula_lexer.token (Lexing.from_channel ic) 

let main () = 
  Misc.split_debug !debug;
  let attr = Log.get_signature !sigfile in
  let f = analyse_formulafile !formulafile in
  let f = if !negate then Neg f else f in
  let is_mon, pf, vt_list = Rewriting.check_formula false attr f in
  if is_mon then
    let all_attr = 
      (tbl_time, ("tp", TInt) :: ("ts", TInt) :: []) ::
	List.map 
	(fun (p, atts) -> 
	  (p, ("tp", TInt) :: ("ts", TInt) :: atts)
	) 
	attr 
    in
    let ra_e = mfotl2ra (not !no_set_support) pf in
    if !debug_tf then
      begin
	print_ra ra_e;Format.print_newline();Format.print_newline();
      end;
    let nra_e = ra2nra ra_e all_attr in
    if !debug_tf then
      begin
	print_nra nra_e;Format.print_newline();Format.print_newline();
      end;
    let q = nra2sql nra_e in
    print_string "-- ";
    Predicate.print_vartypes_list vt_list;
    print_query q;
    Format.print_newline();Format.print_newline()


let _ = 
  Arg.parse [
    "-sig", Arg.Set_string sigfile, "\t\tChoose the signature file";
    "-formula", Arg.Set_string formulafile, "\tChoose the formula file"; 
    "-negate", Arg.Set negate, "\tAnalyze the negation of the input formula";
    "-no_set_support", Arg.Set no_set_support, "\tDo not use EXCEPT nor INTER";
    "-debug", Arg.Set_string debug, "\tChoose unit to debug";
    "-debug_tf", Arg.Set debug_tf, "\tDebug this module";
    ]
    (fun _ -> ())
    usage_string;
  main ();
