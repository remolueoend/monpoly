open MFOTL
open Verified.Monitor
open Predicate
open Relation
open Helper

exception UnsupportedFragment of string

let unsupported msg = raise (UnsupportedFragment msg)

let int_of_nat n = Z.to_int (integer_of_nat n)
let nat_of_int i = nat_of_integer (Z.of_int i)
let enat_of_integer i = Enat (nat_of_integer i)

let convert_cst = function
  | Int x -> EInt x
  | Str x -> EString x
  | Float x -> EFloat x
  | Regexp _ -> unsupported "Regular expression constant are not supported"

let convert_var fvl bvl a = nat_of_int (try (Misc.get_pos a bvl)
    with Not_found -> (List.length bvl) + (try Misc.get_pos a fvl
        with Not_found -> List.length fvl))

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
    | t -> unsupported ("Unsupported term " ^ string_of_term t)
  in
  convert

let convert_interval (l,r) =
    let lm = match l with
    | OBnd a -> Z.(a + one)
    | CBnd a -> a
    | Inf -> unsupported ("Unsupported interval " ^ (string_of_interval (l,r)))
    in
    let um = match r with
    | OBnd a -> Some Z.(a - one)
    | CBnd a ->  Some a
    | Inf -> None in
    match um with
    | None -> interval (nat_of_integer lm) Infinity_enat
    | Some um ->
        if lm <= um
        then interval (nat_of_integer lm) (enat_of_integer um)
        else unsupported ("Unsupported interval " ^ (string_of_interval (l,r)))

let convert_agg_op = function
  | Cnt -> Agg_Cnt
  | Min -> Agg_Min
  | Max -> Agg_Max
  | Sum -> Agg_Sum
  | Avg -> Agg_Avg
  | Med -> Agg_Med

(* These must be synchronized with Db.base_schema *)
let special_predicates = ["tp"; "ts"; "tpts"]

let convert_special_predicate fvl bvl = function
  | ("tp", _, [t]) -> TP (convert_term fvl bvl t)
  | ("ts", _, [t]) -> TS (convert_term fvl bvl t)
  | ("tpts", _, [t1; t2]) -> And (TP (convert_term fvl bvl t1), TS (convert_term fvl bvl t2))
  | _ -> failwith "[convert_special_predicate] internal error"

let convert_formula dbschema f =
  let free_vars = MFOTL.free_vars f in
  let truth = Equal (Cst (Int Z.zero), Cst (Int Z.zero)) in
  (* First |free_vars| type variables are reserved for the free variables. *)
  let tvar_ctr = ref (List.length free_vars - 1) in
  let create_tvar () =
    incr tvar_ctr;
    Verified.Monitor.TAny (nat_of_int !tvar_ctr)
  in

  let rec convert_formula_vars fvl bvl lets = function
  | Equal (t1,t2) -> Eq (convert_term fvl bvl t1, convert_term fvl bvl t2)
  | Less (t1,t2) -> Less (convert_term fvl bvl t1, convert_term fvl bvl t2)
  | LessEq (t1,t2) -> LessEq (convert_term fvl bvl t1, convert_term fvl bvl t2)
  | Pred p ->
      let (n, a, tl) = p in
      if List.mem n special_predicates && not (List.mem (n, a) lets)
      then convert_special_predicate fvl bvl p
      else Pred (n, List.map (convert_term fvl bvl) tl)
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
  | Exists (v,f) ->
      let rec wrap f = function
      | 0 -> f
      | n -> wrap (Exists (create_tvar (), f)) (n-1)
      in
      wrap (convert_formula_vars fvl (v@bvl) lets f) (List.length v)
  | ForAll (v,f) -> convert_formula_vars fvl bvl lets (Neg (Exists (v,(Neg f))))
  | Aggreg (_,y,op,x,glist,f) ->
      let attr = MFOTL.free_vars f in
      let bound = Misc.diff attr glist in
      let bvl_f = bound @ bvl in
      Agg (convert_var fvl bvl y,
        (convert_agg_op op, create_tvar ()),
        List.init (List.length bound) (fun _ -> create_tvar ()),
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
  | f -> unsupported (string_of_formula "Unsupported formula " f)
and convert_re_vars fvl bvl lets = function
  | Wild -> wild
  | Test f -> Test (convert_formula_vars fvl bvl lets f)
  | Concat (r1,r2) -> Times (convert_re_vars fvl bvl lets r1, convert_re_vars fvl bvl lets r2)
  | Plus (r1,r2) -> Plusa (convert_re_vars fvl bvl lets r1, convert_re_vars fvl bvl lets r2)
  | Star r -> Star (convert_re_vars fvl bvl lets r)
  in convert_formula_vars free_vars [] [] f

let convert_tuple (pname, tl) sl =
  let pos = ref 0 in
  let type_error tname =
    let msg = Printf.sprintf ("[convert_tuple] Expected type %s for\
      \ predicate %s, field number %d") tname pname !pos in
    failwith msg
  in
  try List.map2
    (fun (_, t) s ->
      incr pos;
      Some (match t with
      | TInt ->
        (try EInt (Z.of_string s)
         with Invalid_argument _ -> type_error "int")
      | TStr -> EString s
      | TFloat ->
        (try EFloat (float_of_string s)
         with Failure _ -> type_error "float")
      | TRegexp -> unsupported "Regular expressions constants are not supported"
      )
    )
    tl sl
  with Invalid_argument _ ->
    let msg = Printf.sprintf "[convert_tuple] Wrong tuple length for\
      \ predicate %s (expected: %d, actual: %d)"
      pname (List.length tl) (List.length sl) in
    failwith msg

type db = ((string * nat), (((event_data option) list) set list)) mapping
type tyssig = string * nat -> (tysym list) option

let empty_db = empty_db

let insert_into_db ((pname, tl) as schema) sl db =
  let a = nat_of_int (List.length tl) in
  insert_into_db (pname, a) (convert_tuple schema sl) db

let convert_into_tysym ty = 
  match ty with
    TInt -> Verified.Monitor.TCst (Verified.Monitor.TInt)
  | TFloat -> Verified.Monitor.TCst (Verified.Monitor.TFloat)
  | TStr -> Verified.Monitor.TCst (Verified.Monitor.TString)
  | TRegexp -> unsupported "Regular expressions constants are not supported"

let rec convert_schema_into_sig sch = 
  match sch with
    (pname, tl) :: rest -> (fun k -> if k = (pname, nat_of_int (List.length tl))
                                      then Some (List.map convert_into_tysym (List.map snd tl))
                                      else (convert_schema_into_sig rest) k)
  | [] -> (fun k -> None)

let type_check_formula dbschema f =
  type_check (convert_schema_into_sig dbschema) f

type state =
  (((nat *
      (nat *
        (bool list *
          (bool list *
            ((nat * ((event_data option) list) set) queue *
              ((nat * ((event_data option) list) set) queue *
                (((event_data option) list) set *
                  (event_data wf_table *
                    ((((event_data option) list), nat) mapping *
                      (event_data wf_table *
                        (((event_data option) list), nat)
                          mapping)))))))))) *
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
                         ((event_data option) list) set list)))))))))) *
      aggaux option),
    unit)
    mstate_ext

let init cf = minit_safe cf

let cst_of_event_data = function
  | EInt x -> Int x
  | EFloat x -> Float x
  | EString x -> Str x

let unconvert_tuple l =
  List.filter_map (Option.map cst_of_event_data) l |> Tuple.make_tuple

let set_fold f s x = match s with
  | RBT_set r -> rbt_fold f r x
  | _ -> failwith "[set_fold] unexpected set representation"

let unconvert_violations =
  let add_tuple t = Relation.add (unconvert_tuple t) in
  let ucv_rel rel = set_fold add_tuple rel Relation.empty in
  let ucv (tp, (ts, v)) = (int_of_nat tp, integer_of_nat ts, ucv_rel v) in
  List.map ucv

let step t db st =
  let (vs, st') = mstep (db, nat_of_integer t) st in
  (unconvert_violations vs, st')

let is_monitorable dbschema f =
  let s = mmonitorable_exec (convert_formula dbschema f) in
  (s, (if s then None else Some (f, "MFODL formula is not monitorable")))
