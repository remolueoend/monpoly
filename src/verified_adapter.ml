open MFOTL
open Verified.Monitor
open Predicate
open Relation
open Helper

exception UnsupportedFragment of string

let (<<) f g x = f(g(x))
let nat_of_int = nat_of_integer << Z.of_int
let nat_of_int64 = nat_of_integer << Z.of_int64
let nat_of_float f = if (float_of_int max_int) < f then (nat_of_int64 Int64.max_int) else (nat_of_int64 << Int64.of_float) f
let enat_of_float f = Enat ((nat_of_int64 << Int64.of_float) f)
let int_of_nat = Z.to_int << integer_of_nat (* Problem? *)
let float_of_nat = Z.to_float << integer_of_nat (* Problem? *)
let int_of_enat = function
  | Enat n -> Z.to_int (integer_of_nat n)
  | Infinity_enat -> failwith "[int_of_enat] internal error"
let equal_nata m n = Z.equal (integer_of_nat m) (integer_of_nat n)

let filterWith f p = List.map f << List.filter p
let deoptionalize  =
  let is_some = function Some _ -> true | _ -> false in
  List.map (function | Some x -> x | None -> assert false) << List.filter (is_some)

let index_of =
  let rec index_of_rec c x lst = match lst with
      | [] -> raise(Failure "Not Found")
      | hd::tl -> if (hd=x) then c else index_of_rec (c+1) x tl  in
  index_of_rec 0

let cst_eq = function
| (Int a, Int b) -> a = b
| (Str a, Str b) -> a = b
| (Float a, Float b) -> a = b
| _ -> false

let cst_ord a b =
  let c = Pervasives.compare a b in
  if c < 0 then Lt else if c > 0 then Gt else Eqa

(* FIXME: Quick & dirty. Some of the type classes have assumptions! *)
let domain_ceq = { ceq = Some (fun a b -> cst_eq (a, b)) }
let domain_ccompare = { ccompare = Some cst_ord }
let domain_equal = { equal = (fun a b -> cst_eq (a, b)) }
let domain_set_impl = { set_impl = Phantom Set_RBT }

let convert_var fvl bvl a = nat_of_int (try (index_of a bvl)
    with Failure s -> (List.length bvl) + (try index_of a fvl
        with Failure s -> List.length fvl))

let convert_term fvl bvl = function
  | Cst c -> Const c
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

let eval_sum = function
  | [] -> Float 0.
  | x :: xs -> List.fold_left (fun a b -> match a, b with
      | Int a, Int b -> Int (a + b)
      | Float a, Float b -> Float (a +. b)
      | _ -> failwith "[eval_sum] internal error") x xs

let eval_avg = function
  | [] -> Float 0.
  | _ as xs ->
    let s = match eval_sum xs with
      | Float s -> s
      | Int s -> float_of_int s
      | _ -> failwith "[eval_avg] internal error"
    in
    Float (s /. float_of_int (List.length xs))

let eval_med = function
  | [] -> Float 0.
  | _ as xs ->
      let fmed a b =
        match a, b with
        | Int x, Int y -> Int ((x+y)/2)
        | Float x, Float y -> Float ((x+.y)/.2.)
        | _ -> failwith "[eval_med] type error"
      in
      let sorted = List.sort Pervasives.compare xs in
      Misc.median sorted (List.length sorted) fmed

let eval_cnt xs = Int (List.fold_left (fun a _ -> a + 1) 0 xs)

let eval_min = function
  | [] -> Float 0.
  | x :: xs -> List.fold_left min x xs

let eval_max = function
  | [] -> Float 0.
  | x :: xs -> List.fold_left max x xs

let rec replicate x n xs = if n <= 0 then xs else replicate x (n-1) (x::xs)

let list_of_multiset = function
  | RBT_set rbt ->
    let xs = rbt_multiset domain_ccompare rbt in
    List.fold_left (fun xa (x, c) -> replicate x (int_of_enat c) xa) [] xs
  | _ -> failwith "[convert_multiset] internal error"

let convert_agg_op = function
  | Avg -> (fun m -> eval_avg (list_of_multiset m))
  | Cnt -> (fun m -> eval_cnt (list_of_multiset m))
  | Med -> (fun m -> eval_med (list_of_multiset m))
  | Min -> (fun m -> eval_min (list_of_multiset m))
  | Max -> (fun m -> eval_max (list_of_multiset m))
  | Sum -> (fun m -> eval_sum (list_of_multiset m))

let convert_formula f =
  let fvl = MFOTL.free_vars f in
  let truth = Equal ((Cst (Int 1)), (Cst (Int 1)))  in
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
  | Aggreg (y,op,x,glist,f) ->
    let attr = MFOTL.free_vars f in
    let bound = Misc.diff attr glist in
    let bvl_f = bound @ bvl in
    let posx = Misc.get_pos x
      (List.filter (fun x -> List.mem x attr) (bvl_f @ fvl)) in
    let comp = (fun t -> List.nth t posx) in
    let f' = convert_formula_vars bvl_f f in
    Agg (convert_var fvl bvl y, convert_agg_op op,
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
  | Wild -> Wild
  | Test f -> Test (convert_formula_vars bvl f)
  | Concat (r1,r2) -> Times (convert_re_vars bvl r1, convert_re_vars bvl r2)
  | Plus (r1,r2) -> Plus (convert_re_vars bvl r1, convert_re_vars bvl r2)
  | Star r -> Star (convert_re_vars bvl r) 
  in convert_formula_vars [] f


let convert_db md =
  let convert_relations db =
    mk_db (domain_ceq, domain_ccompare) (List.flatten
                  (List.map
                    (fun t ->
                      let (name,_) = (Table.get_schema t) in
                      List.map (fun tup -> (explode name,tup)) (Relation.elements (Table.get_relation t)))
                    (Db.get_tables db))) in
  (convert_relations md.db, nat_of_float md.ts)

(* (Verified.Monitor.nat * Predicate.cst option list) Verified.Monitor.set -> (timestamp * relation) *)
let convert_violations vs =
  let vsl = match vs with
    | RBT_set rbt -> List.map (fun (tp, rel) -> (int_of_nat tp, rel)) (rbt_verdict domain_ccompare rbt)
    | _ -> failwith "Impossible!" in
  let qtps = List.sort_uniq (fun x y -> x - y) (List.map fst vsl) in
  let qmap tp = List.filter (fun (tp', _) -> tp = tp') vsl in
  List.map
    (fun qtp -> (qtp, Relation.make_relation ((List.map (Tuple.make_tuple<<deoptionalize<<snd) (qmap qtp)))))
    qtps


let is_monitorable f = let s = (Verified.Monitor.mmonitorable_exec (domain_ccompare,domain_equal) << convert_formula) f
                in (s, (if s then None else Some (f, "MFODL formula is not monitorable")))
