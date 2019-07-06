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

let convert_term fvl bvl = function
  | Cst c -> Const c
  | Var a -> Var (nat_of_integer (Z.of_int (try (index_of a bvl)
                  with Failure s -> (List.length bvl) + (try index_of a fvl
                      with Failure s -> List.length fvl))))
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






let convert_formula f =
  let fvl = MFOTL.free_vars f in
  let truth = Equal ((Cst (Int 1)), (Cst (Int 1)))  in
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
  | Exists (v,f) -> Exists (convert_formula_vars (v@bvl) f)
  | ForAll (v,f) -> convert_formula_vars bvl (Neg (Exists (v,(Neg f))))
  | Aggreg (_,_,_,_,f) as fma -> let msg = "Unsupported formula " ^ (MFOTL.string_of_formula "" fma) in
                          raise (UnsupportedFragment msg)
  | Prev (intv,f) -> Prev ((convert_interval intv), (convert_formula_vars bvl f))
  | Next (intv,f) -> Next ((convert_interval intv), (convert_formula_vars bvl f))
  | Since (intv,f1,f2) -> Since (convert_formula_vars bvl f1,convert_interval intv,convert_formula_vars bvl f2)
  | Until (intv,f1,f2) -> Until (convert_formula_vars bvl f1,convert_interval intv,convert_formula_vars bvl f2)
  | Eventually (intv,f) -> convert_formula_vars bvl (Until (intv,truth,f))
  | Once (intv,f) -> convert_formula_vars bvl (Since (intv,truth,f))
  | Always (intv,f) -> convert_formula_vars bvl (Neg (Eventually (intv,(Neg f))))
  | PastAlways (intv,f) -> convert_formula_vars bvl (Neg (Once (intv,(Neg f))))
  | Less (t1,t2) as fma -> let msg = "Unsupported formula " ^ (MFOTL.string_of_formula "" fma) in
                           raise (UnsupportedFragment msg)
  | LessEq (t1,t2) as fma -> let msg = "Unsupported formula " ^ (MFOTL.string_of_formula "" fma) in
  raise (UnsupportedFragment msg) in
  convert_formula_vars [] f


let convert_db md =
  let convert_relations db =
    db_code (domain_ceq, domain_ccompare) (List.flatten
                  (List.map
                    (fun t ->
                      let (name,_) = (Table.get_schema t) in
                      List.map (fun tup -> (explode name,tup)) (Relation.elements (Table.get_relation t)))
                    (Db.get_tables db))) in
  (convert_relations md.db, nat_of_float md.ts)

(* (Verified.Monitor.nat * Predicate.cst option list) Verified.Monitor.set -> (timestamp * relation) *)
let convert_violations vs =
  let vsl = match vs with
    | RBT_set rbt -> List.map (fun (tp, rel) -> (int_of_nat tp, rel)) (verdict_code domain_ccompare rbt)
    | _ -> failwith "Impossible!" in
  let qtps = List.sort_uniq (fun x y -> x - y) (List.map fst vsl) in
  let qmap tp = List.filter (fun (tp', _) -> tp = tp') vsl in
  List.map
    (fun qtp -> (qtp, Relation.make_relation ((List.map (Tuple.make_tuple<<deoptionalize<<snd) (qmap qtp)))))
    qtps
