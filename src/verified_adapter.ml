open MFOTL
open Verified.Monitor
open Predicate
open Relation
open Helper

exception UnsupportedFragment of string

let (<<) f g x = f(g(x))
let nat_of_int = nat_of_integer << Z.of_int
let nat_of_int64 = nat_of_integer << Z.of_int64
let nat_of_float = nat_of_integer << Z.of_float 
let enat_of_float f = Enat (nat_of_float f)
let int_of_nat = Z.to_int << integer_of_nat (* Problem? *)
let float_of_nat = Z.to_float << integer_of_nat (* Problem? *)
let int_of_enat = function
  | Enat n -> Z.to_int (integer_of_nat n)
  | Infinity_enat -> failwith "[int_of_enat] internal error"

let filterWith f p = List.map f << List.filter p
let deoptionalize  =
  let is_some = function Some _ -> true | _ -> false in
  List.map (function | Some x -> x | None -> assert false) << List.filter (is_some)

let index_of =
  let rec index_of_rec c x lst = match lst with
      | [] -> raise(Failure "Not Found")
      | hd::tl -> if (hd=x) then c else index_of_rec (c+1) x tl  in
  index_of_rec 0

let convert_cst = function
  | Int x -> EInt (Int_of_integer (Z.of_int x))
  | Str x -> EString (explode x)
  | Float x -> EFloat x

let convert_var fvl bvl a = nat_of_int (try (index_of a bvl)
    with Failure s -> (List.length bvl) + (try index_of a fvl
        with Failure s -> List.length fvl))

let convert_term fvl bvl = function
  | Cst c -> Const (convert_cst c)
  | Var a -> Var (convert_var fvl bvl a)
  | x -> let msg = "Unsupported term " ^ (string_of_term x) in
    raise (UnsupportedFragment msg)

let convert_interval (l,r) =
    let lm = match l with
    | OBnd a -> (a+.1.)
    | CBnd a -> a
    | Inf -> let msg = "Unsupported interval " ^ (string_of_interval (l,r)) in
              raise (UnsupportedFragment msg) in
    let um = match r with
    | OBnd a -> Some (a-.1.)
    | CBnd a ->  Some a
    | Inf -> None in
    match um with
    | None -> interval (nat_of_float lm) Infinity_enat
    | Some um ->  if lm <= um then
                  interval (nat_of_float lm) (enat_of_float um)
                  else let msg = "Unsupported interval " ^ (string_of_interval (l,r)) in
                  raise (UnsupportedFragment msg)

let convert_agg_op op t =
  let default_value = convert_cst (MFOTL.aggreg_default_value op t) in
  match op with
  | Avg -> average_agg
  | Cnt -> count_agg
  | Med -> median_agg
  | Min -> min_agg default_value
  | Max -> max_agg default_value
  | Sum -> sum_agg default_value

let convert_formula dbschema f =
  let fvl = MFOTL.free_vars f in
  let truth = Equal (Cst (Int 0), Cst (Int 0)) in
  let rec createExists n f = match n with
  | 0 -> f
  | n -> createExists (n-1) (Exists f)
  in
  let rec convert_formula_vars bvl = function
  | Equal (t1,t2) -> Eq (convert_term fvl bvl t1, convert_term fvl bvl t2)
  | Pred (p,_,tl) -> Pred (explode p, List.map (fun t -> convert_term fvl bvl t) tl)
  | Neg f -> Neg (convert_formula_vars bvl f)
  | And (f1,f2) -> (match (f1, f2) with
    | (Neg sf1, Neg sf2) -> convert_formula_vars bvl (Neg (Or (sf1, sf2)))
    | (Neg sf1,     sf2) -> convert_formula_vars bvl (Neg (Or (Neg sf2, sf1)))
    | (    sf1, Neg sf2) -> convert_formula_vars bvl (Neg (Or (Neg sf1, sf2)))
    | (    sf1,     sf2) -> convert_formula_vars bvl (Neg (Or (Neg sf1, Neg sf2))))
  | Or (f1,f2) -> Or (convert_formula_vars bvl f1, convert_formula_vars bvl f2)
  | Implies (f1,f2) -> convert_formula_vars bvl (Or ((Neg f1), f2))
  | Equiv (f1,f2) -> convert_formula_vars bvl (And (Implies (f1,f2),Implies(f2,f2)))
  | Exists (v,f) -> createExists (List.length v) (convert_formula_vars (v@bvl) f)
  | ForAll (v,f) -> convert_formula_vars bvl (Neg (Exists (v,(Neg f))))
  | Aggreg (y,op,x,glist,f) as ff ->
      let t_y = List.assoc y (Rewriting.check_syntax dbschema ff) in
      let attr = MFOTL.free_vars f in
      let bound = Misc.diff attr glist in
      let bvl_f = bound @ bvl in
      let posx = Misc.get_pos x
        (List.filter (fun x -> List.mem x attr) (Misc.remove_duplicates (bvl_f @ fvl))) in
      let comp = (fun t -> List.nth t posx) in
      let f' = convert_formula_vars bvl_f f in
      Agg (convert_var fvl bvl y, convert_agg_op op t_y,
        nat_of_int (List.length bound), comp, f')
  | Prev (intv,f) -> Prev ((convert_interval intv), (convert_formula_vars bvl f))
  | Next (intv,f) -> Next ((convert_interval intv), (convert_formula_vars bvl f))
  | Since (intv,f1,f2) -> Since (convert_formula_vars bvl f1,convert_interval intv,convert_formula_vars bvl f2)
  | Until (intv,f1,f2) -> Until (convert_formula_vars bvl f1,convert_interval intv,convert_formula_vars bvl f2)
  | Eventually (intv,f) -> convert_formula_vars bvl (Until (intv,truth,f))
  | Once (intv,f) -> convert_formula_vars bvl (Since (intv,truth,f))
  | Always (intv,f) -> convert_formula_vars bvl (Neg (Eventually (intv,(Neg f))))
  | PastAlways (intv,f) -> convert_formula_vars bvl (Neg (Once (intv,(Neg f))))
  | Frex (intv, r) -> MatchF (convert_interval intv, convert_re_vars bvl r)
  | Prex (intv, r) -> MatchP (convert_interval intv, convert_re_vars bvl r)
  | Less (t1,t2) as fma -> let msg = "Unsupported formula " ^ (MFOTL.string_of_formula "" fma) in
                           raise (UnsupportedFragment msg)
  | LessEq (t1,t2) as fma -> let msg = "Unsupported formula " ^ (MFOTL.string_of_formula "" fma) in
                           raise (UnsupportedFragment msg)
  and convert_re_vars bvl = function
  | Wild -> wild
  | Test f -> Test (convert_formula_vars bvl f)
  | Concat (r1,r2) -> Times (convert_re_vars bvl r1, convert_re_vars bvl r2)
  | Plus (r1,r2) -> Plus (convert_re_vars bvl r1, convert_re_vars bvl r2)
  | Star r -> Star (convert_re_vars bvl r)
  in convert_formula_vars [] f

let unorderedFlatMap m = 
  let rec flatmap_rec acc = function 
  | [] -> acc
  | x::xs -> List.rev_append (m x) acc in
  flatmap_rec [] 

let convert_db md =
  let add_builtin xs (name, tup) = (explode name, List.map convert_cst tup) :: xs in
  let convert_table t =
    let (name,_) = (Table.get_schema t) in
    List.map (fun tup -> (explode name, List.map convert_cst tup))
      (Relation.elements (Table.get_relation t))
  in
  let db_events = unorderedFlatMap convert_table (Db.get_tables md.db) in
  let all_events = List.fold_left add_builtin db_events
    ["tp", [Int md.tp]; "ts", [Float md.ts]; "tpts", [Int md.tp; Float md.ts]]
  in
  (mk_db all_events, nat_of_float md.ts)

let cst_of_event_data = function
  | EInt (Int_of_integer x) -> Int (Z.to_int x)  (* PARTIAL *)
  | EFloat x -> Float x
  | EString x -> Str (implode x)

let convert_tuple xs = Tuple.make_tuple (List.map cst_of_event_data (deoptionalize xs))

(* (Verified.Monitor.nat * Verified.Monitor.event_data option list) Verified.Monitor.set -> (timestamp * relation) *)
let convert_violations vs =
  let vsl = match vs with
    | RBT_set rbt -> rbt
    | _ -> failwith "Impossible!" in
  let hm = Hashtbl.create 100 in
  rbt_fold (fun (ctp, tuple) _ ->             
             let tp = int_of_nat ctp in
             let new_tuple = convert_tuple tuple in
             begin 
              try
                let rel = Hashtbl.find hm tp in
                Hashtbl.add hm tp (Relation.add new_tuple rel);
              with Not_found -> Hashtbl.add hm tp (Relation.make_relation [new_tuple]);
             end) vsl ();
 Hashtbl.fold (fun k v l -> (k,v)::l) hm []



let is_monitorable dbschema f =
  let s = (Verified.Monitor.mmonitorable_exec_e << convert_formula dbschema) f in
  (s, (if s then None else Some (f, "MFODL formula is not monitorable")))
