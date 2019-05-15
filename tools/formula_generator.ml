(* 
Generate these formulas as base cases:

| ERel         
| EPred        
| ENeg         
| EAnd         
| EOr          
| EExists
| EPrev        
| ENext        
| ESinceA      
| ESince       
| EOnceA       
| EOnceZ       
| EOnce        
| ENUntil      
| EUntil       
| EEventuallyZ 
| EEventually   
*)

open QCheck
open MFOTL
open Predicate

module Set = Set.Make(struct type t = string let compare = Pervasives.compare end)
module IntMap = Map.Make(struct type t = int let compare = Pervasives.compare end)
open IntMap

type relop = LT | GT | LEQ | GEQ | EQ 

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

let gRel         r t1 t2 = GRel         (r ,t1, t2) 
let gPred        p       = GPred        p 
let gNeg         f       = GNeg         f 
let gOr          f1 f2   = GOr          (f1, f2) 
let gSAndSUB     f1 f2   = GSAndSUB     (f1, f2) 
let gSAnd        f1 f2   = GSAnd        (f1, f2) 
let gNAndEQ      f1 f2   = GNAndEQ      (f1, f2) 
let gNAnd        f1 f2   = GNAnd        (f1, f2) 
let gAnd         f1 f2   = GAnd         (f1, f2) 
let gAndEQ       f1 f2   = GAndEQ       (f1, f2) 
let gAndSUB1     f1 f2   = GAndSUB1     (f1, f2) 
let gAndSUB2     f1 f2   = GAndSUB2     (f1, f2) 
let gExists      v f     = GExists      (v, f) 
let gPrev        i f     = GPrev        (i, f) 
let gNext        i f     = GNext        (i, f) 
let gOnce        i f     = GOnce        (i, f) 
let gOnceA       i f     = GOnceA       (i, f) 
let gOnceZ       i f     = GOnceZ       (i, f) 
let gEventually  i f     = GEventually  (i, f) 
let gEventuallyZ i f     = GEventuallyZ (i, f) 
let gSince       i f1 f2 = GSince       (i, f1, f2) 
let gSinceA      i f1 f2 = GSinceA      (i, f1, f2) 
let gNSince      i f1 f2 = GNSince      (i, f1, f2) 
let gNSinceA     i f1 f2 = GNSinceA     (i, f1, f2) 
let gUntil       i f1 f2 = GUntil       (i, f1, f2) 
let gNUntil      i f1 f2 = GNUntil      (i, f1, f2) 

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


let rec string_of_arity = function
| 0 -> ""
| 1 -> "int"
| n -> "int, " ^ (string_of_arity (n-1))

let string_of_sig map =
  List.fold_left (fun str (a,set) -> List.fold_left (fun subs p -> subs ^ p ^ "(" ^ (string_of_arity a) ^ ")"  ) "" (Set.elements set)) "" (IntMap.bindings map)

let mapSnd f (a,b) = (a,f b)

(* TODO: parethesize *)
let string_of_genformula f = string_of_formula "" (formula_of_genformula f)

let interval_gen_bound max_lb max_delta =
  let lb = Gen.int_bound max_lb in
  let delta = Gen.int_bound max_delta in
  let ival = Gen.map2 (fun l d -> (l, (l + d))) lb delta in
  let lp = Gen.bool in
  let rp = Gen.bool in
  Gen.map3 (fun (a,b) l r -> 
  let (x,y) = (float_of_int a, float_of_int b) in
  match (l,r) with 
    | (true,true)   -> (CBnd x, CBnd y)
    | (true, false)  -> (CBnd x, OBnd y)
    | (false,true)  -> (OBnd x, CBnd y)
    | _             -> (OBnd x, OBnd y)
  ) 
  ival lp rp
  
  let interval_gen_inf max_lb =
    let lb = Gen.int_bound max_lb in
    let lp = Gen.bool in
    Gen.map2 (fun a l -> 
    let x = float_of_int a in
    match l with 
      | true   -> (CBnd x, Inf)
      | _      -> (OBnd x, Inf)
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

let rec superset = function
      | [] -> [[]]
      | x :: xs -> 
         let ps = superset xs in
         ps @ List.map (fun ss -> x :: ss) ps

let random_subset = Gen.oneofl << superset 

let shuffle l =
  let a = Array.of_list l in
  let swap a i j =
    let t = a.(i) in
    a.(i) <- a.(j);
    a.(j) <- t in
  let _ = Array.iteri (fun i _ -> swap a i (Random.int (i+1))) a in
  Array.to_list a


let predicate_gen map vs =
  let vs = List.map (fun e -> Var e) vs in 
  let predNum = Set.cardinal (List.fold_left Set.union Set.empty (List.map snd (IntMap.bindings map))) in
  let freshPred = "P" ^ string_of_int predNum in
  let oldSet = try find (List.length vs) map with Not_found -> Set.empty in 
  let newSet = Set.add freshPred oldSet in 
  let updatedMap = add (List.length vs) newSet map in
  let shuffled_Vars = Gen.shuffle_l vs in
  shuffled_Vars >>= (fun vs -> 
  Gen.map (fun (m,p) -> (m,make_predicate (p, shuffle vs))) 
  (Gen.oneofl ((updatedMap, freshPred) :: (List.map (fun e -> (map,e)) (Set.elements oldSet)))))


  
    
(* TODO: sig gen *)
let formula_gen signature max_lb max_interval past_only varnum size = 
  let fq = if past_only then 0 else 1 in
  let mq = if max_lb == -1 then 0 else 1 in 
  let vars = List.map (fun e -> "x" ^ string_of_int e) (1 -- varnum) in
  let preds = signature in
  Random_generator.fix (fun go (predmap,vars,size) -> match size with 
    | 0 -> Gen.map (mapSnd gPred) (predicate_gen predmap vars)
    | n -> 
    let noint = Gen.return (CBnd 0., Inf) in
      let bound_variable = "y" ^ string_of_int ((List.length (List.filter (fun x -> String.contains x 'y') vars))+1) in
      let interval = if (max_lb == -1) then noint else interval_gen max_lb max_interval in
      let interval_bound = interval_gen_bound max_lb max_interval in
      let interval_inf = interval_gen_inf max_lb in
      let interval_zero = interval_gen 0 max_interval in
      let interval_zero_bound = interval_gen_bound 0 max_interval in
      let vars_sub1 = random_subset vars in
      let vars_sub2 = random_subset vars in
      let m = Random.int n in
      let metricunarybind f intr =
        (go (predmap, vars, (n-1))) >>= 
            (fun (newMap,sf) -> 
              (intr >>= (fun i -> (fun s -> (newMap, f i sf))))) in 
      let binarybind f vars1 vars2 = 
        (go (predmap, vars1, m)) >>= 
            (fun (predmap',lf) -> 
              (go (predmap', vars2, (n - 1 - m)))  >>= 
                  (fun (predmap'',rf) -> 
                      (fun s -> (predmap'', (f lf rf))))) in
      let metricbinarybind f intr vars1 vars2 = 
        (go (predmap, vars1, m)) >>= 
            (fun (predmap',lf) -> 
              (go (predmap', vars2, (n - 1 - m)))  >>= 
                  (fun (predmap'',rf) -> 
                      intr >>= 
                      (fun i -> 
                      (fun s -> (predmap'', (f i lf rf)))))) in
      Gen.frequency [
        1, binarybind gOr          vars vars;
        1, binarybind gNAndEQ      vars vars;
        1, vars_sub1 >>= (fun v1 -> binarybind gNAnd vars v1);
        (* 1, bindbind gSAndSUB     vars vars; *)
        (* 1, bindbind gSAnd        vars vars; *)
        1, vars_sub1 >>= (fun v1 -> vars_sub2 >>= (fun v2 -> binarybind gAnd v1 v2));
        1, binarybind gAndEQ       vars vars;
        1, vars_sub1 >>= (fun v1 -> binarybind gAndSUB1     v1 vars);
        1, vars_sub1 >>= (fun v1 -> binarybind gAndSUB2     vars v1);
        1, (go (predmap, (bound_variable :: vars), (n-1))) >>= (fun (newMap,sf) -> (fun s -> (newMap, gExists [bound_variable] sf)));
        1, metricunarybind gPrev        interval;
       fq, metricunarybind gNext        interval_bound;
        1, metricunarybind gOnce        interval;
       mq, metricunarybind gOnceA       interval_inf;
       mq, metricunarybind gOnceZ       interval_zero;
       fq, metricunarybind gEventually  interval_bound;
       fq, metricunarybind gEventuallyZ interval_zero_bound;
        1, metricbinarybind gSince      interval vars vars;
       mq, metricbinarybind gSinceA     interval_inf vars vars;
       mq, metricbinarybind gNSince     interval vars vars;
       mq, metricbinarybind gNSinceA    interval_inf vars vars;
       fq, metricbinarybind gUntil      interval_bound vars vars;
       fq, metricbinarybind gNUntil     interval_bound vars vars;       
      ]
  ) (preds,vars,size)
  
  
  let generate_formula ?(signature = empty) ?(max_lb = -1) ?(max_interval=10) ?(past_only=false) varnum size = List.hd (Gen.generate ~n:1 (formula_gen signature max_lb max_interval past_only varnum size))

    (* TODO: no future, no intervals, temporal boolean ops *)
