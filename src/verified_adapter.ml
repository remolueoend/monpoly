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
  | Int x -> EInt (Z.of_int x)
  | Str x -> EString (explode x)
  | Float x -> EFloat x

let convert_var fvl bvl a = nat_of_int (try (index_of a bvl)
    with Failure s -> (List.length bvl) + (try index_of a fvl
        with Failure s -> List.length fvl))

let convert_term fvl bvl =
  let rec convert = function
    | Cst c -> Const (convert_cst c)
    | Var a -> Var (convert_var fvl bvl a)
    | F2i t -> F2i (convert t)
    | I2f t -> I2f (convert t)
    | Plus (t1, t2) -> Plus (convert t1, convert t2)
    | Minus (t1, t2) -> Minus (convert t1, convert t2)
    | UMinus t -> UMinus (convert t)
    | Mult (t1, t2) -> Mult (convert t1, convert t2)
    | Div (t1, t2) -> Div (convert t1, convert t2)
    | Mod (t1, t2) -> Mod (convert t1, convert t2)
  in
  convert

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

let convert_agg_op = function
  | Cnt -> Agg_Cnt
  | Min -> Agg_Min
  | Max -> Agg_Max
  | Sum -> Agg_Sum
  | Avg -> Agg_Avg
  | Med -> Agg_Med

let convert_formula dbschema f =
  let free_vars = MFOTL.free_vars f in
  let truth = Equal (Cst (Int 0), Cst (Int 0)) in
  let rec createExists n f = match n with
  | 0 -> f
  | n -> createExists (n-1) (Exists f)
  in
  let rec convert_formula_vars fvl bvl = function
  | Equal (t1,t2) -> Eq (convert_term fvl bvl t1, convert_term fvl bvl t2)
  | Less (t1,t2) -> Less (convert_term fvl bvl t1, convert_term fvl bvl t2)
  | LessEq (t1,t2) -> LessEq (convert_term fvl bvl t1, convert_term fvl bvl t2)
  | Pred (p,_,tl) -> Pred (explode p, List.map (fun t -> convert_term fvl bvl t) tl)
  | Let (p,f1,f2) -> let (n,a,ts) = Predicate.get_info p in
                     Let (explode n, nat_of_int 0, convert_formula_vars (MFOTL.free_vars f1) [] f1, convert_formula_vars fvl bvl f2)
  | Neg f -> Neg (convert_formula_vars fvl bvl f)
  | And (f1,f2) -> And (convert_formula_vars fvl bvl f1, convert_formula_vars fvl bvl f2)
  | Or (f1,f2) -> Or (convert_formula_vars fvl bvl f1, convert_formula_vars fvl bvl f2)
  | Implies (f1,f2) -> convert_formula_vars fvl bvl (Or ((Neg f1), f2))
  | Equiv (f1,f2) -> convert_formula_vars fvl bvl (And (Implies (f1,f2),Implies(f2,f2)))
  | Exists (v,f) -> createExists (List.length v) (convert_formula_vars fvl (v@bvl) f)
  | ForAll (v,f) -> convert_formula_vars fvl bvl (Neg (Exists (v,(Neg f))))
  | Aggreg (t_y, y,op,x,glist,f) ->
      let t_y = match t_y with TCst a -> a | _ -> failwith "Internal error" in
      let attr = MFOTL.free_vars f in
      let bound = Misc.diff attr glist in
      let bvl_f = bound @ bvl in
      Agg (convert_var fvl bvl y,
        (convert_agg_op op, convert_cst (aggreg_default_value op t_y)),
        nat_of_int (List.length bound),
        convert_term fvl bvl_f (Var x),
        convert_formula_vars fvl bvl_f f)
  | Prev (intv,f) -> Prev ((convert_interval intv), (convert_formula_vars fvl bvl f))
  | Next (intv,f) -> Next ((convert_interval intv), (convert_formula_vars fvl bvl f))
  | Since (intv,f1,f2) -> Since (convert_formula_vars fvl bvl f1,convert_interval intv,convert_formula_vars fvl bvl f2)
  | Until (intv,f1,f2) -> Until (convert_formula_vars fvl bvl f1,convert_interval intv,convert_formula_vars fvl bvl f2)
  | Eventually (intv,f) -> convert_formula_vars fvl bvl (Until (intv,truth,f))
  | Once (intv,f) -> convert_formula_vars fvl bvl (Since (intv,truth,f))
  | Always (intv,f) -> convert_formula_vars fvl bvl (Neg (Eventually (intv,(Neg f))))
  | PastAlways (intv,f) -> convert_formula_vars fvl bvl (Neg (Once (intv,(Neg f))))
  | Frex (intv, r) -> MatchF (convert_interval intv, convert_re_vars fvl bvl r)
  | Prex (intv, r) -> MatchP (convert_interval intv, convert_re_vars fvl bvl r)
  and convert_re_vars fvl bvl = function
  | Wild -> wild
  | Test f -> Test (convert_formula_vars fvl bvl f)
  | Concat (r1,r2) -> Times (convert_re_vars fvl bvl r1, convert_re_vars fvl bvl r2)
  | Plus (r1,r2) -> Plusa (convert_re_vars fvl bvl r1, convert_re_vars fvl bvl r2)
  | Star r -> Star (convert_re_vars fvl bvl r)
  in convert_formula_vars free_vars [] f

let unorderedFlatMap m =
  let rec flatmap_rec acc = function
  | [] -> acc
  | x::xs -> flatmap_rec (List.rev_append (m x) acc) xs in
  flatmap_rec []

let convert_db md =
  let rbt_single x = RBT_set (rbt_insert x rbt_empty) in
  let add_builtin xs (name, tup) =
    (explode name, rbt_single (List.map convert_cst tup)) :: xs in
  let convert_table t =
    let (name,_) = (Table.get_schema t) in
    (explode name, RBT_set (Relation.fold (fun v -> rbt_insert (List.map convert_cst v))
      (Table.get_relation t) rbt_empty)) in
  let db_events = List.map convert_table (Db.get_tables md.db) in
  let all_events = List.fold_left add_builtin db_events
    ["tp", [Int md.tp]; "ts", [Float md.ts]; "tpts", [Int md.tp; Float md.ts]]
  in
  (mk_db all_events, nat_of_float md.ts)

let cst_of_event_data = function
  | EInt x -> Int (Z.to_int x)  (* PARTIAL *)
  | EFloat x -> Float x
  | EString x -> Str (implode x)

let convert_tuple xs = Tuple.make_tuple (List.map cst_of_event_data (deoptionalize xs))

(* (Verified.nat * Verified.event_data option list Verified.set) list -> (int * relation) list *)
let convert_violations =
  List.map (fun (tp, rbt) ->
  let v = match rbt with
    | RBT_set r -> r
    | _ -> failwith "Impossible!" in
    ((int_of_nat tp),
     Relation.make_relation
      (rbt_fold (fun t l -> (convert_tuple t) :: l) v [] )))

let is_monitorable dbschema f =
  let s = (mmonitorable_exec << convert_formula dbschema) f in
  (s, (if s then None else Some (f, "MFODL formula is not monitorable")))
