(* 
Generate these formulas as base cases:

| ERel           (EQ + optionally LT | GT | LEQ | GEQ)
| EPred          (From a random singature, or optionally with a specific signature)
| ENeg           
| EAnd           
| EOr            
| EExists        
| EPrev          (optionally non-metric)
| ENext          (suppressed with for past-only formulas, optionally non-metric)
| ESinceA        (optionally non-metric)
| ESince         (optionally non-metric)
| EOnceA         (optionally non-metric)
| EOnceZ         (optionally non-metric)
| EOnce          (optionally non-metric)
| ENUntil        (suppressed with for past-only formulas, optionally non-metric)
| EUntil         (suppressed with for past-only formulas, optionally non-metric)
| EEventuallyZ   (suppressed with for past-only formulas, optionally non-metric)
| EEventually    (suppressed with for past-only formulas, optionally non-metric)
| EAggreg        (if aggregations enabled)
| EAggOnce       (if aggregations enabled)
| EAggMMOnce     (if aggregations enabled)
*)

open QCheck
open Libmonpoly
open MFOTL
open Predicate

module Set = Set.Make(struct type t = string let compare = Stdlib.compare end)
module IntMap = Map.Make(struct type t = int let compare = Stdlib.compare end)
open IntMap

type relop = LT | GT | LEQ | GEQ | EQ 

type aggrop = AVG | MIN | MAX | MED | CNT | SUM 

type genformula = 
  | GRel          of (relop * term * term)
  | GPred         of predicate
  | GNeg          of genformula
  | GOr           of (genformula * genformula)
  | GSAndSUB      of (genformula * genformula)
  | GSAnd         of (genformula * genformula)
  | GNAndEQ       of (genformula * genformula)
  | GNAnd         of (genformula * genformula)
  | GAnd          of (genformula * genformula)
  | GAndEQ        of (genformula * genformula)
  | GAndSUB1      of (genformula * genformula)
  | GAndSUB2      of (genformula * genformula)
  | GExists       of (var list * genformula)
  | GPrev         of (interval * genformula)
  | GNext         of (interval * genformula)
  | GOnce         of (interval * genformula)
  | GOnceA        of (interval * genformula)
  | GOnceZ        of (interval * genformula)
  | GEventually   of (interval * genformula)
  | GEventuallyZ  of (interval * genformula)
  | GSince        of (interval * genformula * genformula)
  | GSinceA       of (interval * genformula * genformula)  
  | GNSince       of (interval * genformula * genformula)
  | GNSinceA      of (interval * genformula * genformula)  
  | GUntil        of (interval * genformula * genformula)
  | GNUntil       of (interval * genformula * genformula)
  | GAggOnce      of (var * aggrop * var * var list * interval * genformula)
  | GAggMMOnce    of (var * aggrop * var * var list * interval * genformula)
  | GAggAvg       of (var * aggrop * var * var list * genformula)
  | GAggMed       of (var * aggrop * var * var list * genformula)
  | GAgg          of (var * aggrop * var * var list * genformula)

let gRel         r t1 t2      = GRel         (r ,t1, t2) 
let gPred        p            = GPred        p 
let gNeg         f            = GNeg         f 
let gOr          f1 f2        = GOr          (f1, f2) 
let gSAndSUB     f1 f2        = GSAndSUB     (f1, f2) 
let gSAnd        f1 f2        = GSAnd        (f1, f2) 
let gNAndEQ      f1 f2        = GNAndEQ      (f1, f2) 
let gNAnd        f1 f2        = GNAnd        (f1, f2) 
let gAnd         f1 f2        = GAnd         (f1, f2) 
let gAndEQ       f1 f2        = GAndEQ       (f1, f2) 
let gAndSUB1     f1 f2        = GAndSUB1     (f1, f2) 
let gAndSUB2     f1 f2        = GAndSUB2     (f1, f2) 
let gExists      v f          = GExists      (v, f) 
let gPrev        i f          = GPrev        (i, f) 
let gNext        i f          = GNext        (i, f) 
let gOnce        i f          = GOnce        (i, f) 
let gOnceA       i f          = GOnceA       (i, f) 
let gOnceZ       i f          = GOnceZ       (i, f) 
let gEventually  i f          = GEventually  (i, f) 
let gEventuallyZ i f          = GEventuallyZ (i, f) 
let gSince       i f1 f2      = GSince       (i, f1, f2) 
let gSinceA      i f1 f2      = GSinceA      (i, f1, f2) 
let gNSince      i f1 f2      = GNSince      (i, f1, f2) 
let gNSinceA     i f1 f2      = GNSinceA     (i, f1, f2) 
let gUntil       i f1 f2      = GUntil       (i, f1, f2) 
let gNUntil      i f1 f2      = GNUntil      (i, f1, f2) 
let gAggOnce     r a v gs i f = GAggOnce     (r, a, v, gs, i, f)
let gAggMMOnce   r a v gs i f = GAggMMOnce   (r, a, v, gs, i, f)
let gAggAvg      r a v gs f   = GAggAvg      (r, a, v, gs, f)
let gAggMed      r a v gs f   = GAggMed      (r, a, v, gs, f)
let gAgg         r a v gs f   = GAgg         (r, a, v, gs, f)

let aggr_op = function 
| MAX -> Max
| MIN -> Min
| CNT -> Cnt
| AVG -> Avg
| MED -> Med
| SUM -> Sum


let aggr_op_type = function 
| MAX -> TCst TInt
| MIN -> TCst TInt
| CNT -> TCst TInt
| AVG -> TCst TFloat
| MED -> TCst TFloat
| SUM -> TCst TInt

let rec formula_of_genformula = function
| GRel         (rop,t1,t2) -> 
  (match rop with 
    | LT  -> Less   (t1,t2) | GT  -> Less   (t2,t1)  
    | LEQ -> LessEq (t1,t2) | GEQ -> LessEq (t2,t1) 
    | EQ  -> Equal  (t1,t2))
| GPred        p           -> Pred p
| GNeg         f           -> Neg (formula_of_genformula f)
| GOr          (f1, f2)    -> Or (formula_of_genformula f1, formula_of_genformula f2)       
| GNAndEQ      (f1, f2)
| GNAnd        (f1, f2)    -> And (formula_of_genformula f1, Neg (formula_of_genformula f2))
| GSAndSUB     (f1, f2)
| GSAnd        (f1, f2)
| GAnd         (f1, f2)
| GAndEQ       (f1, f2)
| GAndSUB1     (f1, f2)
| GAndSUB2     (f1, f2)    -> And (formula_of_genformula f1, formula_of_genformula f2)
| GExists      (v, f)      -> Exists (v, formula_of_genformula f)
| GPrev        (i, f)      -> Prev (i, formula_of_genformula f)
| GNext        (i, f)      -> Next (i, formula_of_genformula f)
| GOnce        (i, f)
| GOnceA       (i, f)
| GOnceZ       (i, f)      -> Once (i, formula_of_genformula f)
| GEventually  (i, f)
| GEventuallyZ (i, f)      -> Eventually (i, formula_of_genformula f)
| GSince       (i, f1, f2)
| GSinceA      (i, f1, f2) -> Since (i, formula_of_genformula f1, formula_of_genformula f2)
| GNSince      (i, f1, f2)
| GNSinceA     (i, f1, f2) -> Since (i, Neg (formula_of_genformula f1), formula_of_genformula f2)
| GUntil       (i, f1, f2) -> Until (i, formula_of_genformula f1, formula_of_genformula f2)
| GNUntil      (i, f1, f2) -> Until (i, Neg (formula_of_genformula f1), formula_of_genformula f2)
| GAggOnce     (r, a, v, gs, i, f) 
| GAggMMOnce   (r, a, v, gs, i, f) -> Aggreg ((aggr_op_type a), r, (aggr_op a), v, gs, Once (i, formula_of_genformula f))
| GAggAvg      (r, a, v, gs, f)
| GAggMed      (r, a, v, gs, f) 
| GAgg         (r, a, v, gs, f) -> Aggreg ((aggr_op_type a), r, (aggr_op a), v, gs, formula_of_genformula f)

(* TODO: Print floats where necessary (e.g., result of AVG and MED) *)
let rec string_of_arity = function
| 0 -> ""
| 1 -> "int"
| n -> "int, " ^ (string_of_arity (n-1))

let string_of_sig map =
  List.fold_left (fun str (a,set) -> str ^ List.fold_left (fun subs p -> subs ^ p ^ "(" ^ (string_of_arity a) ^ ")\n"  ) "" (Set.elements set)) "" (IntMap.bindings map)

let mapSnd f (a,b) = (a,f b)

(* Fully parenthesize an MFOTL formula *)
let string_of_parenthesized_formula_qtl str g =
let check_interval = function
| (CBnd lb, Inf) when lb = Z.zero -> ""
(* | (OBnd 0., Inf) -> "" *)
| _ -> failwith "Unsupported: metric operators" in
let rec string_f_rec top par h =
  (match h with
    | Equal (t1,t2) ->
      "(" ^ string_of_term t1 ^ " = " ^ string_of_term t2 ^ ")"
    | Less (t1,t2) ->
      "(" ^ string_of_term t1 ^ " < " ^ string_of_term t2 ^ ")"
    | LessEq (t1,t2) ->
      "(" ^ string_of_term t1 ^ " <= " ^ string_of_term t2 ^ ")"
    | Pred p -> string_of_predicate p
    | _ ->
        
      (match h with
      | Neg f ->
        "(" ^
        "! " ^ string_f_rec false false f
        ^ ")"

      | Exists (vl,f) ->
        "(" ^
        "Exists " 
        ^ 
        Misc.string_of_list_ext "" "" ", " Predicate.string_of_term (List.map (fun v -> Var v) vl) 
        ^
        ". "
        ^
        string_f_rec false false f
        ^ ")"

      | ForAll (vl,f) ->
        "(" ^
        "Forall "
        ^
        Misc.string_of_list_ext "" "" ", " Predicate.string_of_term (List.map (fun v -> Var v) vl)
        ^
        ". "
        ^
        string_f_rec false false f
        ^ ")"

      | Aggreg (_,y,op,x,glist,f) -> failwith "Unsupported: aggregation operators"
      | Prev (intv,f) ->
        check_interval intv ^
        "(" ^
        "@ "
        ^
        string_f_rec false false f
        ^ ")"

      | Next (intv,f) 
      | Always (intv,f) 
      | Eventually (intv,f) -> failwith "Unsupported: future operators"
        
      | Once (intv,f) ->
        check_interval intv ^
        "(" ^
        "P "
        ^
        string_f_rec false false f
        ^ ")"

      | PastAlways (intv,f) ->
        check_interval intv ^
        "(" ^
        "H "
        ^
        string_f_rec false false f
        ^ ")"
        
      | _ ->
        
        (match h with
          | And (f1,f2) ->
            "(" ^
            string_f_rec false true f1
            ^
            " & " 
            ^
            string_f_rec false true f2
            ^ ")"

          | Or (f1,f2) ->
            "(" ^
            string_f_rec false true f1
            ^
            " | "
            ^
            string_f_rec false false f2
            ^ ")"

          | Implies (f1,f2) ->
            "(" ^
            string_f_rec false true f1
            ^
            " -> "
            ^
            string_f_rec false false f2
            ^ ")"

          | Equiv (f1,f2) -> string_f_rec false false (And ((Implies (f1, f2)), (Implies (f2, f1))))

          | Since (intv,f1,f2) ->
            check_interval intv ^
            "(" ^
            string_f_rec false true f1
            ^ 
            " S "
            ^
            string_f_rec false false f2
            ^ ")"

          | Until (intv,f1,f2) -> failwith "Unsupported: future operators"

          | _ -> failwith "[print_formula] internal error"
        )
        
      ) 
      
  )
in
str ^ string_f_rec true false g

let string_of_genformula f = string_of_parenthesized_formula "" (formula_of_genformula f)

let string_of_genformula_qtl f = string_of_parenthesized_formula_qtl "prop random : " (formula_of_genformula (gNeg f))

(* Returns a generator for non-empty float intervals with integer bounds 

*)
let interval_gen_bound max_lb max_delta =
    let lb = Gen.int_bound (max max_lb 0) in
    let delta = Gen.int_bound max_delta in
    let ival = Gen.map2 (fun l d -> (l, l + d)) lb delta in
    let lp = Gen.bool in
    let rp = Gen.bool in
    Gen.map3
    (fun (a,b) l r ->
      let a, b = Z.of_int a, Z.of_int b in
      if b <= a then (CBnd a, CBnd a) 
      else
        match (l,r) with 
          | (true,true)   -> (CBnd a, CBnd b)
          | (true, false)  -> (CBnd a, OBnd b)
          | (false,true)  -> (OBnd a, CBnd b)
          | _             -> (OBnd a, OBnd b)
    ) 
    ival lp rp
  
  let interval_gen_inf max_lb =
    let noint = Gen.return (CBnd Z.zero, Inf) in
    if (max_lb == -1) then noint else
      let lb = Gen.int_bound max_lb in
      let lp = Gen.bool in
      Gen.map2 (fun a l ->
      let a = Z.of_int a in
      match l with 
        | true   -> (CBnd a, Inf)
        | _      -> (OBnd a, Inf)
      ) 
      lb lp

let interval_gen max_lb max_delta = 
  Gen.oneof [interval_gen_bound max_lb max_delta; 
             interval_gen_inf max_lb]

let (<<) f g x = f(g(x))
let (--) i j = 
  let rec aux n acc =
    if n < i then acc else aux (n-1) (n :: acc)
  in aux j []

let (>>=) = Random_generator.bind'

let rec powerset = function
      | [] -> [[]]
      | x :: xs -> 
         let ps = powerset xs in
         ps @ List.map (fun ss -> x :: ss) ps

let random_subset = Gen.oneofl << powerset 

(* 
   (random_bounded_subset n s) generates a random nonempty subset of s with cardinality no greater than n.
    Since Verimon does not support var1 = var2 formulas this is used with n=1
    to pick variables for constraints of the form var = const
*)
let random_bounded_subset n = 
  assert (n > 0);
  Gen.oneofl << List.filter (fun x -> let l = List.length x in 1<=l && l <= n) << powerset 

let shuffle l =
  let a = Array.of_list l in
  let swap a i j =
    let t = a.(i) in
    a.(i) <- a.(j);
    a.(j) <- t in
  let _ = Array.iteri (fun i _ -> swap a i (Random.int (i+1))) a in
  Array.to_list a


let var_op f vs1 vs2 = Set.elements (f (Set.of_list vs1) (Set.of_list vs2))

let rel_gen v all_rels max_const = 
  let rel  = if all_rels then Gen.oneofl [LT ; GT ; LEQ ; GEQ ; EQ] else Gen.return EQ in 
  let cons1 = Gen.int_bound max_const in 
  let cons2 = Gen.int_bound max_const in 
  cons1 >>= (fun c1 -> 
  cons2 >>= (fun c2 -> 
      rel >>= (fun r -> 
      (fun s -> match (List.length v) with
        | 2 ->  gRel r (Var (List.hd v)) (Var (List.hd (List.tl v)))
        | 1 ->  gRel r (Var (List.hd v)) (Cst (Int (Z.of_int c1)))
        | 0 ->  gRel r (Cst (Int (Z.of_int c1))) (Cst (Int (Z.of_int c2)))
        | _ -> failwith "Rigid predicates can have up to 2 variables"
      ))))

let predicate_gen map vs =
  let vs = List.map (fun e -> Var e) vs in 
  let predNum = Set.cardinal (List.fold_left Set.union Set.empty (List.map snd (IntMap.bindings map))) in
  let freshPred = "P" ^ string_of_int predNum in
  let oldSet = try find (List.length vs) map with Not_found -> Set.empty in 
  let newSet = Set.add freshPred oldSet in 
  let updatedMap = add (List.length vs) newSet map in
  let shuffled_Vars = Gen.shuffle_l vs in
  shuffled_Vars >>= (fun vs -> 
  Gen.map (fun (m,p) -> (m, make_predicate (p, shuffle vs))) 
  (Gen.oneofl ((updatedMap, freshPred) :: (List.map (fun e -> (map,e)) (Set.elements oldSet)))))

let formula_gen signature max_lb max_interval past_only all_rels aggr foo ndi max_const qtl varnum size = 
  let fq = if past_only || qtl then 0 else 1 in
  let mq = if (max_lb < 0) then 0 else 1 in
  let aq = if aggr then 1 else 0 in
  let tq = if foo then 0 else 1 in 
  let max_interval = max 0 max_interval in
  let size = max 0 size in
  let varnum = max 0 varnum in
  let vars = List.map (fun e -> "x" ^ string_of_int e) (1 -- varnum) in
  let rec toplvlq fg = function
  | [] -> fg
  | v::vs -> toplvlq (Random_generator.map (fun (m,f) -> (m,gExists [v] f)) fg) vs
  in
  let result = Random_generator.fix (
  fun go (predmap, vars, size) -> match size with 
    | 0 -> 
      let vnum = if ndi then 2 else 1 in
      if (List.length vars) <= vnum then
      let predbool = Gen.bool in
      predbool >>= (fun b ->
        if b then 
          (* let twovars = random_bounded_subset vnum vars in *)
          Gen.map (fun e -> (predmap,e)) (rel_gen vars all_rels max_const)
        else
          Gen.map (mapSnd gPred) (predicate_gen predmap vars)
      )
      else 
      Gen.map (mapSnd gPred) (predicate_gen predmap vars)
    | n -> 
      let aq = min aq (List.length vars) in
      let oq = min (n-1) 1 in 
      let sq = min (List.length vars) 1 in
      let new_bound_variable vs = "y" ^ string_of_int
        ((List.fold_left 
          max 
          0
          (List.map 
            (fun s -> int_of_string (String.sub s 1 ((String.length s)-1))) 
            (List.filter 
              (fun x -> String.contains x 'y') 
              vs)))+1) in
      let new_bound_variables num vars = 
        if num = 0 then [] else
        List.filter (fun b -> String.contains b 'y') 
          (List.fold_left (fun a _ -> let b = new_bound_variable a in (b::a) ) vars (1 -- num)) in
      (* Exists *)
      let new_bv = new_bound_variable vars in
      (* Aggr *)
      let num_bvs = Random.int 3 in (* TODO: parametrize *)
      let num_bvs = if List.length vars = 0 then max 1 num_bvs else num_bvs in
      let new_bvs = new_bound_variables num_bvs vars in 
      let result_var = Gen.oneofl vars in 
      (* let group_vars = Gen.map (fun r -> Set.diff (Set.of_list vars) (Set.singleton r)) result_var in *)
      let aggr_free_vars = var_op Set.union vars new_bvs in
      let aggr_var = Gen.oneofl aggr_free_vars in
      let aggr_gen_all = Gen.oneofl [MAX ; MIN ; CNT ; SUM ; AVG ; MED] in
      let aggr_gen_mm = Gen.oneofl [MAX ; MIN] in
      let aggr_gen_mmcs = Gen.oneofl [MAX ; MIN ; CNT ; SUM] in
      let side = Gen.bool in
      let noint = Gen.return (CBnd Z.zero, Inf) in
      let interval = if qtl then noint else interval_gen max_lb max_interval in
      let interval_bound = if qtl then noint else interval_gen_bound max_lb max_interval in
      let interval_inf = if qtl then noint else interval_gen_inf max_lb in
      let interval_zero = if qtl then noint else interval_gen 0 max_interval in
      let interval_zero_bound = if qtl then noint else interval_gen_bound 0 max_interval in
      let bound_vars = List.filter (fun b -> String.contains b 'y') vars in
      let vars_sub1 = Gen.map (fun v -> Set.elements (Set.union (Set.of_list v) (Set.of_list bound_vars))) (random_subset vars) in
      let vars_sub2 = Gen.map (fun v -> Set.elements (Set.union (Set.of_list v) (Set.of_list bound_vars))) (random_subset vars) in
      let fv_cover v1 v2 vars = 
        Set.elements (Set.union (Set.of_list v2) (Set.diff (Set.of_list vars) (Set.of_list v1))) in 
      let m = Random.int n in
      let unarybind f vars =
        let twovars = random_bounded_subset 1 vars in
        twovars >>= (fun v -> 
        let sf = rel_gen v all_rels max_const in 
        (go (predmap, vars, (n-1))) >>= 
            (fun (newMap,sf1) -> 
              sf >>= (fun sf2 ->
                  (fun s -> (newMap, f sf1 sf2))))) in 
      let metricunarybind f intr =
        (go (predmap, vars, (n-1))) >>= 
            (fun (newMap,sf) -> 
                (intr >>= (fun i -> (fun s -> (newMap, f i sf))))) in 
      let binarybind f vars1 vars2 = 
        (go (predmap, vars1, m)) >>= 
            (fun (newMap,lf) -> 
                (go (newMap, vars2, (n - 1 - m)))  >>= 
                    (fun (newestMap,rf) -> 
                        if not qtl then
                        (fun s -> (newestMap, (f lf rf)))
                        else side >>= 
                          (fun left -> 
                            if left then 
                            (fun s -> (newestMap, (f (gOnce (CBnd Z.zero, Inf) lf) rf)))
                            else 
                            (fun s -> (newestMap, (f lf (gOnce (CBnd Z.zero, Inf) rf))))
                          )
                    )) 
                        in
      let metricbinarybind f intr vars1 vars2 = 
        (go (predmap, vars1, m)) >>= 
            (fun (newMap,lf) -> 
                (go (newMap, vars2, (n - 1 - m)))  >>= 
                    (fun (newestMap,rf) -> 
                        intr >>= 
                            (fun i -> 
                                (fun s -> (newestMap, (f i lf rf)))))) in
    (* Monitrable formulas *)
    if not ndi then  
      Gen.frequency [
        1, binarybind gOr          vars vars;
        1, binarybind gNAndEQ      vars vars;
        1, vars_sub1 >>= (fun v1 -> binarybind gNAnd vars v1);
       sq, unarybind gSAndSUB     vars;
       (* sq, unarybind gSAnd        vars;  *)
        1, vars_sub1 >>= (fun v1 -> vars_sub2 >>= (fun v2 -> let v2' = fv_cover v1 v2 vars in binarybind gAnd v1 v2'));
        1, binarybind gAndEQ       vars vars;
        1, vars_sub1 >>= (fun v1 -> binarybind gAndSUB1     v1 vars);
        1, vars_sub1 >>= (fun v1 -> binarybind gAndSUB2     vars v1);
        1, (go (predmap, (new_bv :: vars), (n-1))) >>= (fun (newMap,sf) -> (fun s -> (newMap, gExists [new_bv] sf)));
       tq, metricunarybind gPrev        interval;
    fq*tq, metricunarybind gNext        interval_bound;
       tq, metricunarybind gOnce        interval;
    mq*tq, metricunarybind gOnceA       interval_inf;
    mq*tq, metricunarybind gOnceZ       interval_zero;
    fq*tq, metricunarybind gEventually  interval_bound;
    fq*tq, metricunarybind gEventuallyZ interval_zero_bound;
       tq, vars_sub1 >>= (fun v1 -> metricbinarybind gSince      interval v1 vars);
    mq*tq, vars_sub1 >>= (fun v1 -> metricbinarybind gSinceA     interval_inf v1 vars);
    mq*tq, vars_sub1 >>= (fun v1 -> metricbinarybind gNSince     interval v1 vars);
    mq*tq, vars_sub1 >>= (fun v1 -> metricbinarybind gNSinceA    interval_inf v1 vars);
    fq*tq, vars_sub1 >>= (fun v1 -> metricbinarybind gUntil      interval_bound v1 vars);
    fq*tq, vars_sub1 >>= (fun v1 -> metricbinarybind gNUntil     interval_bound v1 vars);
       aq, (go (predmap, aggr_free_vars, (n-1))) >>= 
                (fun (newMap, sf) -> result_var >>= 
                  (fun r -> aggr_var >>= 
                    (fun a -> fun s -> (newMap, gAggAvg r AVG a (var_op Set.diff vars [r]) sf))));
       aq, (go (predmap, aggr_free_vars, (n-1))) >>= 
                (fun (newMap, sf) -> result_var >>= 
                  (fun r -> aggr_var >>= 
                    (fun a -> fun s -> (newMap, gAggMed r MED a (var_op Set.diff vars [r]) sf))));
       aq, (go (predmap, aggr_free_vars, (n-1))) >>= 
                (fun (newMap, sf) -> result_var >>= 
                  (fun r -> aggr_var >>= 
                    (fun a -> aggr_gen_mmcs >>=
                      (fun op -> fun s -> (newMap, gAgg r op a (var_op Set.diff vars [r]) sf)))));
 aq*oq*tq, (go (predmap, aggr_free_vars, (n-2))) >>= 
                (fun (newMap, sf) -> result_var >>= 
                  (fun r -> aggr_var >>= 
                    (fun a -> aggr_gen_mm >>=
                      (fun op -> interval >>= 
                        (fun i -> fun s -> (newMap, gAggMMOnce r op a (var_op Set.diff vars [r]) i sf))))));
 aq*oq*tq, (go (predmap, aggr_free_vars, (n-2))) >>= 
                (fun (newMap, sf) -> result_var >>= 
                  (fun r -> aggr_var >>= 
                    (fun a -> aggr_gen_all >>=
                      (fun op -> interval >>= 
                        (fun i -> fun s -> (newMap, gAggOnce r op a (var_op Set.diff vars [r]) i sf))))))
      ]
      else 
      (* Arbitrary formulas *)
      Gen.frequency [
        1, (go (predmap, vars, (n-1))) >>= (fun (newMap,sf1) -> (fun s -> (newMap, gNeg sf1)));
        1, vars_sub1 >>= (fun v1 -> vars_sub2 >>= (fun v2 -> let v2' = fv_cover v1 v2 vars in binarybind gAnd v1 v2'));
        1, vars_sub1 >>= (fun v1 -> vars_sub2 >>= (fun v2 -> let v2' = fv_cover v1 v2 vars in binarybind gOr v1 v2'));
        1, (go (predmap, (new_bv :: vars), (n-1))) >>= (fun (newMap,sf) -> (fun s -> (newMap, gExists [new_bv] sf)));
       tq, metricunarybind gPrev        interval;
    fq*tq, metricunarybind gNext        interval_bound;
       tq, metricunarybind gOnce        interval;
    mq*tq, metricunarybind gOnceA       interval_inf;
    mq*tq, metricunarybind gOnceZ       interval_zero;
    fq*tq, metricunarybind gEventually  interval_bound;
    fq*tq, metricunarybind gEventuallyZ interval_zero_bound;
       tq, vars_sub1 >>= (fun v1 -> vars_sub2 >>= (fun v2 -> let v2' = fv_cover v1 v2 vars in metricbinarybind gSince      interval v1 v2'));
    mq*tq, vars_sub1 >>= (fun v1 -> vars_sub2 >>= (fun v2 -> let v2' = fv_cover v1 v2 vars in metricbinarybind gSinceA     interval_inf v1 v2'));
    mq*tq, vars_sub1 >>= (fun v1 -> vars_sub2 >>= (fun v2 -> let v2' = fv_cover v1 v2 vars in metricbinarybind gNSince     interval v1 v2'));
    mq*tq, vars_sub1 >>= (fun v1 -> vars_sub2 >>= (fun v2 -> let v2' = fv_cover v1 v2 vars in metricbinarybind gNSinceA    interval_inf v1 v2'));
    fq*tq, vars_sub1 >>= (fun v1 -> vars_sub2 >>= (fun v2 -> let v2' = fv_cover v1 v2 vars in metricbinarybind gUntil      interval_bound v1 v2'));
    fq*tq, vars_sub1 >>= (fun v1 -> vars_sub2 >>= (fun v2 -> let v2' = fv_cover v1 v2 vars in metricbinarybind gNUntil     interval_bound v1 v2'));
       aq, (go (predmap, aggr_free_vars, (n-1))) >>= 
                (fun (newMap, sf) -> result_var >>= 
                  (fun r -> aggr_var >>= 
                    (fun a -> fun s -> (newMap, gAggAvg r AVG a (var_op Set.diff vars [r]) sf))));
       aq, (go (predmap, aggr_free_vars, (n-1))) >>= 
                (fun (newMap, sf) -> result_var >>= 
                  (fun r -> aggr_var >>= 
                    (fun a -> fun s -> (newMap, gAggMed r MED a (var_op Set.diff vars [r]) sf))));
       aq, (go (predmap, aggr_free_vars, (n-1))) >>= 
                (fun (newMap, sf) -> result_var >>= 
                  (fun r -> aggr_var >>= 
                    (fun a -> aggr_gen_mmcs >>=
                      (fun op -> fun s -> (newMap, gAgg r op a (var_op Set.diff vars [r]) sf)))));
 aq*oq*tq, (go (predmap, aggr_free_vars, (n-2))) >>= 
                (fun (newMap, sf) -> result_var >>= 
                  (fun r -> aggr_var >>= 
                    (fun a -> aggr_gen_mm >>=
                      (fun op -> interval >>= 
                        (fun i -> fun s -> (newMap, gAggMMOnce r op a (var_op Set.diff vars [r]) i sf))))));
 aq*oq*tq, (go (predmap, aggr_free_vars, (n-2))) >>= 
                (fun (newMap, sf) -> result_var >>= 
                  (fun r -> aggr_var >>= 
                    (fun a -> aggr_gen_all >>=
                      (fun op -> interval >>= 
                        (fun i -> fun s -> (newMap, gAggOnce r op a (var_op Set.diff vars [r]) i sf))))))
      ]
      ) (signature, vars, size) in
      if qtl then toplvlq result vars
      else result
  
  let generate_formula ?(signature = empty) ?(max_lb = -1) ?(max_interval=10) ?(past_only=false) ?(all_rels=false) ?(aggr=false) ?(foo=false) ?(ndi=false) ?(max_const=42) ?(qtl=false) varnum size = List.hd (Gen.generate ~n:1 (formula_gen signature max_lb max_interval past_only all_rels aggr foo ndi max_const qtl varnum size))

    (* TODO: check binary temporal ops for qtl  *)
    (* TODO: other special AND case *)
