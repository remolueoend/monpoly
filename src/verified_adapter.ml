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
  | Infinity_enat -> failwith "[int_of_enat] Infinity"

let index_of x =
  let rec index_of_rec c = function
    | [] -> raise(Failure "Not Found")
    | hd::tl -> if (hd=x) then c else index_of_rec (c+1) tl
  in
  index_of_rec 0

let convert_cst = function
  | Int x -> EInt (Z.of_int x)
  | Str x -> EString x
  | Float x -> EFloat x
  | ZInt x -> EInt x
  | Regexp _ -> raise (UnsupportedFragment "Unsupported regular expression constant")

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
    | _ -> failwith "[convert_term] unsupported term"
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

(* These must be synchronized with Log.get_signature_lexbuf *)
let special_predicates = ["tp"; "ts"; "tpts"]

let convert_special_predicate fvl bvl = function
  | ("tp", _, [t]) -> TP (convert_term fvl bvl t)
  | ("ts", _, [t]) -> TS (convert_term fvl bvl t)
  | ("tpts", _, [t1; t2]) -> And (TP (convert_term fvl bvl t1), TS (convert_term fvl bvl t2))
  | _ -> failwith "[convert_special_predicate] internal error"

let convert_formula dbschema f =
  let free_vars = MFOTL.free_vars f in
  let truth = Equal (Cst (Int 0), Cst (Int 0)) in
  let rec createExists n f = match n with
  | 0 -> f
  | n -> createExists (n-1) (Exists f)
  in
  let rec convert_formula_vars fvl bvl lets = function
  | Equal (t1,t2) -> Eq (convert_term fvl bvl t1, convert_term fvl bvl t2)
  | Less (t1,t2) -> Less (convert_term fvl bvl t1, convert_term fvl bvl t2)
  | LessEq (t1,t2) -> LessEq (convert_term fvl bvl t1, convert_term fvl bvl t2)
  | Pred p ->
      let (n, a, tl) = p in
      if List.mem n special_predicates && not (List.mem (n, a) lets) then
        convert_special_predicate fvl bvl p
      else
        Pred (n, List.map (convert_term fvl bvl) tl)
  | Let (p,f1,f2) ->
      let (n,a,ts) = Predicate.get_info p in
      let fvl1 = List.flatten (List.map Predicate.tvars ts) in
      let lets2 = (n, a) :: lets in
      Let (n, convert_formula_vars fvl1 [] lets f1, convert_formula_vars fvl bvl lets2 f2)
  | LetPast (p,f1,f2) ->
      let (n,a,ts) = Predicate.get_info p in
      let fvl1 = List.flatten (List.map Predicate.tvars ts) in
      let lets' = (n, a) :: lets in
      LetPast (n, convert_formula_vars fvl1 [] lets' f1, convert_formula_vars fvl bvl lets' f2)
  | Neg f -> Neg (convert_formula_vars fvl bvl lets f)
  | And (f1,f2) -> And (convert_formula_vars fvl bvl lets f1, convert_formula_vars fvl bvl lets f2)
  | Or (f1,f2) -> Or (convert_formula_vars fvl bvl lets f1, convert_formula_vars fvl bvl lets f2)
  | Implies (f1,f2) -> convert_formula_vars fvl bvl lets (Or ((Neg f1), f2))
  | Equiv (f1,f2) -> convert_formula_vars fvl bvl lets (And (Implies (f1,f2),Implies(f2,f2)))
  | Exists (v,f) -> createExists (List.length v) (convert_formula_vars fvl (v@bvl) lets f)
  | ForAll (v,f) -> convert_formula_vars fvl bvl lets (Neg (Exists (v,(Neg f))))
  | Aggreg (t_y, y,op,x,glist,f) ->
      let t_y = match t_y with TCst a -> a | _ -> failwith "Internal error" in
      let attr = MFOTL.free_vars f in
      let bound = Misc.diff attr glist in
      let bvl_f = bound @ bvl in
      Agg (convert_var fvl bvl y,
        (convert_agg_op op, convert_cst (aggreg_default_value op t_y)),
        nat_of_int (List.length bound),
        convert_term fvl bvl_f (Var x),
        convert_formula_vars fvl bvl_f lets f)
  | Prev (intv,f) -> Prev ((convert_interval intv), (convert_formula_vars fvl bvl lets f))
  | Next (intv,f) -> Next ((convert_interval intv), (convert_formula_vars fvl bvl lets f))
  | Since (intv,f1,f2) -> Since (convert_formula_vars fvl bvl lets f1,convert_interval intv,convert_formula_vars fvl bvl lets f2)
  | Until (intv,f1,f2) -> Until (convert_formula_vars fvl bvl lets f1,convert_interval intv,convert_formula_vars fvl bvl lets f2)
  | Eventually (intv,f) -> convert_formula_vars fvl bvl lets (Until (intv,truth,f))
  | Once (intv,f) -> convert_formula_vars fvl bvl lets (Since (intv,truth,f))
  | Always (intv,f) -> convert_formula_vars fvl bvl lets (Neg (Eventually (intv,(Neg f))))
  | PastAlways (intv,f) -> convert_formula_vars fvl bvl lets (Neg (Once (intv,(Neg f))))
  | Frex (intv, r) -> MatchF (convert_interval intv, convert_re_vars fvl bvl lets r)
  | Prex (intv, r) -> MatchP (convert_interval intv, convert_re_vars fvl bvl lets r)
  | _ -> failwith "[convert_term] unsupported formula"
and convert_re_vars fvl bvl lets = function
  | Wild -> wild
  | Test f -> Test (convert_formula_vars fvl bvl lets f)
  | Concat (r1,r2) -> Times (convert_re_vars fvl bvl lets r1, convert_re_vars fvl bvl lets r2)
  | Plus (r1,r2) -> Plusa (convert_re_vars fvl bvl lets r1, convert_re_vars fvl bvl lets r2)
  | Star r -> Star (convert_re_vars fvl bvl lets r)
  in convert_formula_vars free_vars [] [] f

let make_tuple tl sl =
  let pos = ref 0 in
  List.map2
    (fun (_, t) s ->
      incr pos;
      Some (match t with
      | TInt ->
        (try EInt (Z.of_string s)
         with Invalid_argument _ ->
           raise (Tuple.Type_error ("Expected type int for field number "
                                    ^ (string_of_int !pos))))
      | TStr -> EString s
      | TFloat ->
        (try EFloat (float_of_string s)
         with Failure _ ->
           raise (Tuple.Type_error ("Expected type float for field number "
                                    ^ (string_of_int !pos))))
      | TRegexp -> raise (Tuple.Type_error "Unsupported regular expression type")
      )
    )
    tl sl

type db = ((string * nat), (((event_data option) list) set list)) mapping

let empty_db = empty_db

let insert_into_db (n, tl) sl db =
  let a = nat_of_int (List.length tl) in
  insert_into_db (n, a) (make_tuple tl sl) db

type state =
  (((nat *
      (nat *
        (bool list *
          (bool list *
            ((nat * ((event_data option) list) set) queue *
              ((nat * ((event_data option) list) set) queue *
                (((event_data option) list) set *
                  ((((event_data option) list), nat) mapping *
                    (((event_data option) list), nat) mapping)))))))) *
     aggaux option),
    ((nat *
       (nat queue *
         ((((event_data option) list) set * (nat, nat) sum) queue *
           (nat *
             (bool list *
               (bool list *
                 (((event_data option) list) set *
                   ((((event_data option) list), nat) mapping *
                     ((nat, (((event_data option) list), (nat, nat) sum)
                              mapping)
                        mapping *
                       ((nat, nat) mapping *
                         (((event_data option) list) set list *
                           nat))))))))))) *
      aggaux option),
    unit)
    mstate_ext

let init cf = minit_safe cf

let cst_of_event_data = function
  | EInt x -> (try Int (Z.to_int x) with Z.Overflow -> ZInt x)
  | EFloat x -> Float x
  | EString x -> Str x

let convert_tuple l = Tuple.make_tuple (List.filter_map (Option.map cst_of_event_data) l)

let rbt_set_fold f s x = match s with
  | RBT_set r -> rbt_fold f r x
  | _ -> failwith "[rbt_set_fold] unexpected set representation"

let convert_violations =
  List.map (fun (tp, (ts, v)) -> (int_of_nat tp, float_of_nat ts,
    rbt_set_fold (fun t rel -> Relation.add (convert_tuple t) rel) v Relation.empty))

let step t db st =
  let (vs, st') = mstep (db, nat_of_float t) st in
  (convert_violations vs, st')

let is_monitorable dbschema f =
  let s = (mmonitorable_exec << convert_formula dbschema) f in
  (s, (if s then None else Some (f, "MFODL formula is not monitorable")))
