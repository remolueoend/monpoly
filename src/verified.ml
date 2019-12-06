module Uint32 : sig
  val less : int32 -> int32 -> bool
  val less_eq : int32 -> int32 -> bool
  val set_bit : int32 -> Z.t -> bool -> int32
  val shiftl : int32 -> Z.t -> int32
  val shiftr : int32 -> Z.t -> int32
  val shiftr_signed : int32 -> Z.t -> int32
  val test_bit : int32 -> Z.t -> bool
end = struct

(* negative numbers have their highest bit set, 
   so they are greater than positive ones *)
let less x y =
  if Int32.compare x Int32.zero < 0 then
    Int32.compare y Int32.zero < 0 && Int32.compare x y < 0
  else Int32.compare y Int32.zero < 0 || Int32.compare x y < 0;;

let less_eq x y =
  if Int32.compare x Int32.zero < 0 then
    Int32.compare y Int32.zero < 0 && Int32.compare x y <= 0
  else Int32.compare y Int32.zero < 0 || Int32.compare x y <= 0;;

let set_bit x n b =
  let mask = Int32.shift_left Int32.one (Z.to_int n)
  in if b then Int32.logor x mask
     else Int32.logand x (Int32.lognot mask);;

let shiftl x n = Int32.shift_left x (Z.to_int n);;

let shiftr x n = Int32.shift_right_logical x (Z.to_int n);;

let shiftr_signed x n = Int32.shift_right x (Z.to_int n);;

let test_bit x n =
  Int32.compare 
    (Int32.logand x (Int32.shift_left Int32.one (Z.to_int n)))
    Int32.zero
  <> 0;;

end;; (*struct Uint32*)

module Bits_Integer : sig
  val shiftl : Z.t -> Z.t -> Z.t
  val shiftr : Z.t -> Z.t -> Z.t
  val test_bit : Z.t -> Z.t -> bool
end = struct

(* We do not need an explicit range checks here,
   because Big_int.int_of_big_int raises Failure 
   if the argument does not fit into an int. *)
let shiftl x n = Z.shift_left x (Z.to_int n);;

let shiftr x n = Z.shift_right x (Z.to_int n);;

let test_bit x n =  Z.testbit x (Z.to_int n);;

end;; (*struct Bits_Integer*)

module Monitor : sig
  type nat
  val integer_of_nat : nat -> Z.t
  type 'a equal = {equal : 'a -> 'a -> bool}
  val equal : 'a equal -> 'a -> 'a -> bool
  type 'a ceq = {ceq : ('a -> 'a -> bool) option}
  val ceq : 'a ceq -> ('a -> 'a -> bool) option
  type ('a, 'b) phantom = Phantom of 'b
  type set_impla = Set_Choose | Set_Collect | Set_DList | Set_RBT | Set_Monada
  type 'a set_impl = {set_impl : ('a, set_impla) phantom}
  val set_impl : 'a set_impl -> ('a, set_impla) phantom
  type ordera = Eqa | Lt | Gt
  type 'a ccompare = {ccompare : ('a -> 'a -> ordera) option}
  val ccompare : 'a ccompare -> ('a -> 'a -> ordera) option
  type ('b, 'a) mapping_rbt
  type 'a set_dlist
  type 'a set = Collect_set of ('a -> bool) | DList_set of 'a set_dlist |
    RBT_set of ('a, unit) mapping_rbt | Set_Monad of 'a list |
    Complement of 'a set
  val nat_of_integer : Z.t -> nat
  type 'a trm = Var of nat | Const of 'a
  type char
  type enat = Enat of nat | Infinity_enat
  type i
  type 'a regex = Wild | Test of 'a formula | Plus of 'a regex * 'a regex |
    Times of 'a regex * 'a regex | Star of 'a regex
  and 'a formula = Pred of char list * 'a trm list | Eq of 'a trm * 'a trm |
    Neg of 'a formula | Or of 'a formula * 'a formula | Ands of 'a formula list
    | Exists of 'a formula |
    Agg of nat * (('a * enat) set -> 'a) * nat * ('a list -> 'a) * 'a formula |
    Prev of i * 'a formula | Next of i * 'a formula |
    Since of 'a formula * i * 'a formula | Until of 'a formula * i * 'a formula
    | MatchF of i * 'a regex | MatchP of i * 'a regex
  type safety
  type modality
  type 'a mformula
  type ('a, 'b) mstate_ext
  val mstep :
    'a ceq * 'a ccompare * 'a equal * 'a set_impl ->
      (char list * 'a list) set * nat ->
        ('a, unit) mstate_ext ->
          (nat * ('a option) list) set * ('a, unit) mstate_ext
  val interval : nat -> enat -> i
  val mmonitorable_exec : 'a ccompare * 'a equal -> 'a formula -> bool
  val minit_safe :
    'a ceq * 'a ccompare * 'a equal -> 'a formula -> ('a, unit) mstate_ext
  val mk_db :
    'a ceq * 'a ccompare ->
      (char list * 'a list) list -> (char list * 'a list) set
  val explode : string -> char list
  val convert_multiway : 'a ccompare * 'a equal -> 'a formula -> 'a formula
  val rbt_verdict :
    'a ccompare ->
      ((nat * ('a option) list), unit) mapping_rbt ->
        (nat * ('a option) list) list
  val rbt_multiset :
    'a ccompare -> (('a * enat), unit) mapping_rbt -> ('a * enat) list
end = struct

type nat = Nat of Z.t;;

let rec integer_of_nat (Nat x) = x;;

let rec equal_nata m n = Z.equal (integer_of_nat m) (integer_of_nat n);;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_nat = ({equal = equal_nata} : nat equal);;

type num = One | Bit0 of num | Bit1 of num;;

let one_nata : nat = Nat (Z.of_int 1);;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_nat = ({one = one_nata} : nat one);;

let rec times_nata m n = Nat (Z.mul (integer_of_nat m) (integer_of_nat n));;

type 'a times = {times : 'a -> 'a -> 'a};;
let times _A = _A.times;;

type 'a power = {one_power : 'a one; times_power : 'a times};;

let times_nat = ({times = times_nata} : nat times);;

let power_nat = ({one_power = one_nat; times_power = times_nat} : nat power);;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec min _A a b = (if less_eq _A a b then a else b);;

let rec less_eq_nat m n = Z.leq (integer_of_nat m) (integer_of_nat n);;

let rec less_nat m n = Z.lt (integer_of_nat m) (integer_of_nat n);;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

let rec inf_nata x = min ord_nat x;;

type 'a inf = {inf : 'a -> 'a -> 'a};;
let inf _A = _A.inf;;

let inf_nat = ({inf = inf_nata} : nat inf);;

let rec max _A a b = (if less_eq _A a b then b else a);;

let rec sup_nata x = max ord_nat x;;

type 'a sup = {sup : 'a -> 'a -> 'a};;
let sup _A = _A.sup;;

let sup_nat = ({sup = sup_nata} : nat sup);;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

let preorder_nat = ({ord_preorder = ord_nat} : nat preorder);;

let order_nat = ({preorder_order = preorder_nat} : nat order);;

type 'a semilattice_sup =
  {sup_semilattice_sup : 'a sup; order_semilattice_sup : 'a order};;

type 'a semilattice_inf =
  {inf_semilattice_inf : 'a inf; order_semilattice_inf : 'a order};;

type 'a lattice =
  {semilattice_inf_lattice : 'a semilattice_inf;
    semilattice_sup_lattice : 'a semilattice_sup};;

let semilattice_sup_nat =
  ({sup_semilattice_sup = sup_nat; order_semilattice_sup = order_nat} :
    nat semilattice_sup);;

let semilattice_inf_nat =
  ({inf_semilattice_inf = inf_nat; order_semilattice_inf = order_nat} :
    nat semilattice_inf);;

let lattice_nat =
  ({semilattice_inf_lattice = semilattice_inf_nat;
     semilattice_sup_lattice = semilattice_sup_nat}
    : nat lattice);;

let ceq_nata : (nat -> nat -> bool) option = Some equal_nata;;

type 'a ceq = {ceq : ('a -> 'a -> bool) option};;
let ceq _A = _A.ceq;;

let ceq_nat = ({ceq = ceq_nata} : nat ceq);;

type ('a, 'b) phantom = Phantom of 'b;;

type set_impla = Set_Choose | Set_Collect | Set_DList | Set_RBT | Set_Monada;;

let set_impl_nata : (nat, set_impla) phantom = Phantom Set_RBT;;

type 'a set_impl = {set_impl : ('a, set_impla) phantom};;
let set_impl _A = _A.set_impl;;

let set_impl_nat = ({set_impl = set_impl_nata} : nat set_impl);;

type 'a linorder = {order_linorder : 'a order};;

let linorder_nat = ({order_linorder = order_nat} : nat linorder);;

let finite_UNIV_nata : (nat, bool) phantom = Phantom false;;

let zero_nat : nat = Nat Z.zero;;

let card_UNIV_nata : (nat, nat) phantom = Phantom zero_nat;;

type 'a finite_UNIV = {finite_UNIV : ('a, bool) phantom};;
let finite_UNIV _A = _A.finite_UNIV;;

type 'a card_UNIV =
  {finite_UNIV_card_UNIV : 'a finite_UNIV; card_UNIVa : ('a, nat) phantom};;
let card_UNIVa _A = _A.card_UNIVa;;

let finite_UNIV_nat = ({finite_UNIV = finite_UNIV_nata} : nat finite_UNIV);;

let card_UNIV_nat =
  ({finite_UNIV_card_UNIV = finite_UNIV_nat; card_UNIVa = card_UNIV_nata} :
    nat card_UNIV);;

let cEnum_nat :
  (nat list * (((nat -> bool) -> bool) * ((nat -> bool) -> bool))) option
  = None;;

type 'a cenum =
  {cEnum :
     ('a list * ((('a -> bool) -> bool) * (('a -> bool) -> bool))) option};;
let cEnum _A = _A.cEnum;;

let cenum_nat = ({cEnum = cEnum_nat} : nat cenum);;

type ordera = Eqa | Lt | Gt;;

let rec eq _A a b = equal _A a b;;

let rec comparator_of (_A1, _A2)
  x y = (if less _A2.order_linorder.preorder_order.ord_preorder x y then Lt
          else (if eq _A1 x y then Eqa else Gt));;

let rec compare_nat x = comparator_of (equal_nat, linorder_nat) x;;

let ccompare_nata : (nat -> nat -> ordera) option = Some compare_nat;;

type 'a ccompare = {ccompare : ('a -> 'a -> ordera) option};;
let ccompare _A = _A.ccompare;;

let ccompare_nat = ({ccompare = ccompare_nata} : nat ccompare);;

let ord_integer = ({less_eq = Z.leq; less = Z.lt} : Z.t ord);;

let rec minus_nat
  m n = Nat (max ord_integer Z.zero
              (Z.sub (integer_of_nat m) (integer_of_nat n)));;

let rec proper_interval_nat
  no x1 = match no, x1 with no, None -> true
    | None, Some x -> less_nat zero_nat x
    | Some x, Some y -> less_nat one_nata (minus_nat y x);;

let rec cproper_interval_nata x = proper_interval_nat x;;

type 'a cproper_interval =
  {ccompare_cproper_interval : 'a ccompare;
    cproper_interval : 'a option -> 'a option -> bool};;
let cproper_interval _A = _A.cproper_interval;;

let cproper_interval_nat =
  ({ccompare_cproper_interval = ccompare_nat;
     cproper_interval = cproper_interval_nata}
    : nat cproper_interval);;

let rec equal_order x0 x1 = match x0, x1 with Lt, Gt -> false
                      | Gt, Lt -> false
                      | Eqa, Gt -> false
                      | Gt, Eqa -> false
                      | Eqa, Lt -> false
                      | Lt, Eqa -> false
                      | Gt, Gt -> true
                      | Lt, Lt -> true
                      | Eqa, Eqa -> true;;

type ('a, 'b) generator = Generator of (('b -> bool) * ('b -> 'a * 'b));;

let rec generator (Generator x) = x;;

let rec fst (x1, x2) = x1;;

let rec has_next g = fst (generator g);;

let rec snd (x1, x2) = x2;;

let rec next g = snd (generator g);;

let rec sorted_list_subset_fusion
  less eq g1 g2 s1 s2 =
    (if has_next g1 s1
      then (let (x, s1a) = next g1 s1 in
             has_next g2 s2 &&
               (let (y, s2a) = next g2 s2 in
                 (if eq x y then sorted_list_subset_fusion less eq g1 g2 s1a s2a
                   else less y x &&
                          sorted_list_subset_fusion less eq g1 g2 s1 s2a)))
      else true);;

let rec list_all_fusion
  g p s =
    (if has_next g s
      then (let (x, sa) = next g s in p x && list_all_fusion g p sa)
      else true);;

type color = R | B;;

type ('a, 'b) rbt = Empty |
  Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt;;

let rec rbt_keys_next
  = function ((k, t) :: kts, Empty) -> (k, (kts, t))
    | (kts, Branch (c, l, k, v, r)) -> rbt_keys_next ((k, r) :: kts, l);;

let rec rbt_has_next = function ([], Empty) -> false
                       | (vb :: vc, va) -> true
                       | (v, Branch (vb, vc, vd, ve, vf)) -> true;;

let rbt_keys_generator :
  ('a, (('a * ('a, 'b) rbt) list * ('a, 'b) rbt)) generator
  = Generator (rbt_has_next, rbt_keys_next);;

let rec lt_of_comp
  acomp x y = (match acomp x y with Eqa -> false | Lt -> true | Gt -> false);;

type ('b, 'a) mapping_rbt = Mapping_RBT of ('b, 'a) rbt;;

type 'a set_dlist = Abs_dlist of 'a list;;

type 'a set = Collect_set of ('a -> bool) | DList_set of 'a set_dlist |
  RBT_set of ('a, unit) mapping_rbt | Set_Monad of 'a list |
  Complement of 'a set;;

let rec list_of_dlist _A (Abs_dlist x) = x;;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let rec dlist_all _A x xc = list_all x (list_of_dlist _A xc);;

let rec impl_ofa _B (Mapping_RBT x) = x;;

let rec rbt_init x = ([], x);;

let rec init _A xa = rbt_init (impl_ofa _A xa);;

let rec filtera
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filtera p xs else filtera p xs);;

let rec collect _A
  p = (match cEnum _A with None -> Collect_set p
        | Some (enum, _) -> Set_Monad (filtera p enum));;

let rec list_member
  equal x1 y = match equal, x1, y with
    equal, x :: xs, y -> equal x y || list_member equal xs y
    | equal, [], y -> false;;

let rec the (Some x2) = x2;;

let rec memberc _A xa = list_member (the (ceq _A)) (list_of_dlist _A xa);;

let rec equal_optiona _A x0 x1 = match x0, x1 with None, Some x2 -> false
                           | Some x2, None -> false
                           | Some x2, Some y2 -> eq _A x2 y2
                           | None, None -> true;;

let rec rbt_comp_lookup
  c x1 k = match c, x1, k with c, Empty, k -> None
    | c, Branch (uu, l, x, y, r), k ->
        (match c k x with Eqa -> Some y | Lt -> rbt_comp_lookup c l k
          | Gt -> rbt_comp_lookup c r k);;

let rec lookupc _A xa = rbt_comp_lookup (the (ccompare _A)) (impl_ofa _A xa);;

let rec equal_unita u v = true;;

let equal_unit = ({equal = equal_unita} : unit equal);;

let rec memberb _A t x = equal_optiona equal_unit (lookupc _A t x) (Some ());;

let rec member (_A1, _A2)
  x xa1 = match x, xa1 with
    x, Set_Monad xs ->
      (match ceq _A1
        with None ->
          failwith "member Set_Monad: ceq = None"
            (fun _ -> member (_A1, _A2) x (Set_Monad xs))
        | Some eq -> list_member eq xs x)
    | xa, Complement x -> not (member (_A1, _A2) xa x)
    | x, RBT_set rbt -> memberb _A2 rbt x
    | x, DList_set dxs -> memberc _A1 dxs x
    | x, Collect_set a -> a x;;

let rec subset_eq (_A1, _A2, _A3)
  x0 c = match x0, c with
    RBT_set rbt1, RBT_set rbt2 ->
      (match ccompare _A3
        with None ->
          failwith "subset RBT_set RBT_set: ccompare = None"
            (fun _ -> subset_eq (_A1, _A2, _A3) (RBT_set rbt1) (RBT_set rbt2))
        | Some c ->
          (match ceq _A2
            with None ->
              sorted_list_subset_fusion (lt_of_comp c)
                (fun x y -> equal_order (c x y) Eqa) rbt_keys_generator
                rbt_keys_generator (init _A3 rbt1) (init _A3 rbt2)
            | Some eq ->
              sorted_list_subset_fusion (lt_of_comp c) eq rbt_keys_generator
                rbt_keys_generator (init _A3 rbt1) (init _A3 rbt2)))
    | Complement a1, Complement a2 -> subset_eq (_A1, _A2, _A3) a2 a1
    | Collect_set p, Complement a ->
        subset_eq (_A1, _A2, _A3) a (collect _A1 (fun x -> not (p x)))
    | Set_Monad xs, c -> list_all (fun x -> member (_A2, _A3) x c) xs
    | DList_set dxs, c ->
        (match ceq _A2
          with None ->
            failwith "subset DList_set1: ceq = None"
              (fun _ -> subset_eq (_A1, _A2, _A3) (DList_set dxs) c)
          | Some _ -> dlist_all _A2 (fun x -> member (_A2, _A3) x c) dxs)
    | RBT_set rbt, b ->
        (match ccompare _A3
          with None ->
            failwith "subset RBT_set1: ccompare = None"
              (fun _ -> subset_eq (_A1, _A2, _A3) (RBT_set rbt) b)
          | Some _ ->
            list_all_fusion rbt_keys_generator (fun x -> member (_A2, _A3) x b)
              (init _A3 rbt));;

let rec less_eq_set (_A1, _A2, _A3) = subset_eq (_A1, _A2, _A3);;

let rec equal_seta (_A1, _A2, _A3, _A4)
  a b = less_eq_set (_A1, _A2, _A3) a b && less_eq_set (_A1, _A2, _A3) b a;;

let rec equal_set (_A1, _A2, _A3, _A4) =
  ({equal = equal_seta (_A1, _A2, _A3, _A4)} : 'a set equal);;

let rec uminus_set = function Complement b -> b
                     | Collect_set p -> Collect_set (fun x -> not (p x))
                     | a -> Complement a;;

let rec balance
  x0 s t x3 = match x0, s, t, x3 with
    Branch (R, a, w, x, b), s, t, Branch (R, c, y, z, d) ->
      Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, d))
    | Branch (R, Branch (R, a, w, x, b), s, t, c), y, z, Empty ->
        Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Branch (R, Branch (R, a, w, x, b), s, t, c), y, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, a, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (R, Empty, w, x, Branch (R, b, s, t, c)), y, z, Empty ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Branch (R, Branch (B, va, vb, vc, vd), w, x, Branch (R, b, s, t, c)), y,
        z, Empty
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Empty))
    | Branch (R, Empty, w, x, Branch (R, b, s, t, c)), y, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, Empty, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (R, Branch (B, ve, vf, vg, vh), w, x, Branch (R, b, s, t, c)), y,
        z, Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, Branch (B, ve, vf, vg, vh), w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Empty, w, x, Branch (R, b, s, t, Branch (R, c, y, z, d)) ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, d))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, b, s, t, Branch (R, c, y, z, d))
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, d))
    | Empty, w, x, Branch (R, Branch (R, b, s, t, c), y, z, Empty) ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Empty, w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, va, vb, vc, vd))
        -> Branch
             (R, Branch (B, Empty, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Empty)
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Empty))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, ve, vf, vg, vh))
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, ve, vf, vg, vh)))
    | Empty, s, t, Empty -> Branch (B, Empty, s, t, Empty)
    | Empty, s, t, Branch (B, va, vb, vc, vd) ->
        Branch (B, Empty, s, t, Branch (B, va, vb, vc, vd))
    | Empty, s, t, Branch (v, Empty, vb, vc, Empty) ->
        Branch (B, Empty, s, t, Branch (v, Empty, vb, vc, Empty))
    | Empty, s, t, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty) ->
        Branch
          (B, Empty, s, t,
            Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
    | Empty, s, t, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)) ->
        Branch
          (B, Empty, s, t,
            Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
    | Empty, s, t,
        Branch
          (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi))
        -> Branch
             (B, Empty, s, t,
               Branch
                 (v, Branch (B, ve, vj, vk, vl), vb, vc,
                   Branch (B, vf, vg, vh, vi)))
    | Branch (B, va, vb, vc, vd), s, t, Empty ->
        Branch (B, Branch (B, va, vb, vc, vd), s, t, Empty)
    | Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh) ->
        Branch (B, Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh))
    | Branch (B, va, vb, vc, vd), s, t, Branch (v, Empty, vf, vg, Empty) ->
        Branch
          (B, Branch (B, va, vb, vc, vd), s, t,
            Branch (v, Empty, vf, vg, Empty))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty)
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm))
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm)))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch
          (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm))
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch
                 (v, Branch (B, vi, vn, vo, vp), vf, vg,
                   Branch (B, vj, vk, vl, vm)))
    | Branch (v, Empty, vb, vc, Empty), s, t, Empty ->
        Branch (B, Branch (v, Empty, vb, vc, Empty), s, t, Empty)
    | Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t, Empty ->
        Branch
          (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t,
            Empty)
    | Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t, Empty ->
        Branch
          (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t,
            Empty)
    | Branch
        (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        s, t, Empty
        -> Branch
             (B, Branch
                   (v, Branch (B, vf, vg, vh, vi), vb, vc,
                     Branch (B, ve, vj, vk, vl)),
               s, t, Empty)
    | Branch (v, Empty, vf, vg, Empty), s, t, Branch (B, va, vb, vc, vd) ->
        Branch
          (B, Branch (v, Empty, vf, vg, Empty), s, t,
            Branch (B, va, vb, vc, vd))
    | Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
               Branch (B, va, vb, vc, vd))
    | Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
               Branch (B, va, vb, vc, vd))
    | Branch
        (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)),
        s, t, Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch
                   (v, Branch (B, vj, vk, vl, vm), vf, vg,
                     Branch (B, vi, vn, vo, vp)),
               s, t, Branch (B, va, vb, vc, vd));;

let rec rbt_comp_ins
  c f k v x4 = match c, f, k, v, x4 with
    c, f, k, v, Empty -> Branch (R, Empty, k, v, Empty)
    | c, f, k, v, Branch (B, l, x, y, r) ->
        (match c k x with Eqa -> Branch (B, l, x, f k y v, r)
          | Lt -> balance (rbt_comp_ins c f k v l) x y r
          | Gt -> balance l x y (rbt_comp_ins c f k v r))
    | c, f, k, v, Branch (R, l, x, y, r) ->
        (match c k x with Eqa -> Branch (R, l, x, f k y v, r)
          | Lt -> Branch (R, rbt_comp_ins c f k v l, x, y, r)
          | Gt -> Branch (R, l, x, y, rbt_comp_ins c f k v r));;

let rec paint c x1 = match c, x1 with c, Empty -> Empty
                | c, Branch (uu, l, k, v, r) -> Branch (c, l, k, v, r);;

let rec rbt_comp_insert_with_key c f k v t = paint B (rbt_comp_ins c f k v t);;

let rec rbt_comp_insert c = rbt_comp_insert_with_key c (fun _ _ nv -> nv);;

let rec insertb _A
  xc xd xe =
    Mapping_RBT (rbt_comp_insert (the (ccompare _A)) xc xd (impl_ofa _A xe));;

let rec comp_sunion_with
  c f asa bs = match c, f, asa, bs with
    c, f, (ka, va) :: asa, (k, v) :: bs ->
      (match c k ka with Eqa -> (ka, f ka va v) :: comp_sunion_with c f asa bs
        | Lt -> (k, v) :: comp_sunion_with c f ((ka, va) :: asa) bs
        | Gt -> (ka, va) :: comp_sunion_with c f asa ((k, v) :: bs))
    | c, f, [], bs -> bs
    | c, f, asa, [] -> asa;;

type compare = LT | GT | EQ;;

let rec skip_red = function Branch (R, l, k, v, r) -> l
                   | Empty -> Empty
                   | Branch (B, va, vb, vc, vd) -> Branch (B, va, vb, vc, vd);;

let rec skip_black
  t = (let ta = skip_red t in
        (match ta with Empty -> ta | Branch (R, _, _, _, _) -> ta
          | Branch (B, l, _, _, _) -> l));;

let rec compare_height
  sx s t tx =
    (match (skip_red sx, (skip_red s, (skip_red t, skip_red tx)))
      with (Empty, (Empty, (_, Empty))) -> EQ
      | (Empty, (Empty, (_, Branch (_, _, _, _, _)))) -> LT
      | (Empty, (Branch (_, _, _, _, _), (Empty, _))) -> EQ
      | (Empty, (Branch (_, _, _, _, _), (Branch (_, _, _, _, _), Empty))) -> EQ
      | (Empty,
          (Branch (_, sa, _, _, _),
            (Branch (_, ta, _, _, _), Branch (_, txa, _, _, _))))
        -> compare_height Empty sa ta (skip_black txa)
      | (Branch (_, _, _, _, _), (Empty, (Empty, Empty))) -> GT
      | (Branch (_, _, _, _, _), (Empty, (Empty, Branch (_, _, _, _, _)))) -> LT
      | (Branch (_, _, _, _, _), (Empty, (Branch (_, _, _, _, _), Empty))) -> EQ
      | (Branch (_, _, _, _, _),
          (Empty, (Branch (_, _, _, _, _), Branch (_, _, _, _, _))))
        -> LT
      | (Branch (_, _, _, _, _), (Branch (_, _, _, _, _), (Empty, _))) -> GT
      | (Branch (_, sxa, _, _, _),
          (Branch (_, sa, _, _, _), (Branch (_, ta, _, _, _), Empty)))
        -> compare_height (skip_black sxa) sa ta Empty
      | (Branch (_, sxa, _, _, _),
          (Branch (_, sa, _, _, _),
            (Branch (_, ta, _, _, _), Branch (_, txa, _, _, _))))
        -> compare_height (skip_black sxa) sa ta (skip_black txa));;

let rec plus_nat m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

let rec suc n = plus_nat n one_nata;;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (suc n) xs
                     | n, [] -> n;;

let rec size_list x = gen_length zero_nat x;;

let rec nat_of_integer k = Nat (max ord_integer Z.zero k);;

let rec apfst f (x, y) = (f x, y);;

let rec map_prod f g (a, b) = (f a, g b);;

let rec divmod_nat
  m n = (let k = integer_of_nat m in
         let l = integer_of_nat n in
          map_prod nat_of_integer nat_of_integer
            (if Z.equal k Z.zero then (Z.zero, Z.zero)
              else (if Z.equal l Z.zero then (Z.zero, k)
                     else (fun k l -> if Z.equal Z.zero l then (Z.zero, l) else
                            Z.div_rem (Z.abs k) (Z.abs l))
                            k l)));;

let rec rbtreeify_g
  n kvs =
    (if equal_nata n zero_nat || equal_nata n one_nata then (Empty, kvs)
      else (let (na, r) = divmod_nat n (nat_of_integer (Z.of_int 2)) in
             (if equal_nata r zero_nat
               then (let (t1, (k, v) :: kvsa) = rbtreeify_g na kvs in
                      apfst (fun a -> Branch (B, t1, k, v, a))
                        (rbtreeify_g na kvsa))
               else (let (t1, (k, v) :: kvsa) = rbtreeify_f na kvs in
                      apfst (fun a -> Branch (B, t1, k, v, a))
                        (rbtreeify_g na kvsa)))))
and rbtreeify_f
  n kvs =
    (if equal_nata n zero_nat then (Empty, kvs)
      else (if equal_nata n one_nata
             then (let (k, v) :: kvsa = kvs in
                    (Branch (R, Empty, k, v, Empty), kvsa))
             else (let (na, r) = divmod_nat n (nat_of_integer (Z.of_int 2)) in
                    (if equal_nata r zero_nat
                      then (let (t1, (k, v) :: kvsa) = rbtreeify_f na kvs in
                             apfst (fun a -> Branch (B, t1, k, v, a))
                               (rbtreeify_g na kvsa))
                      else (let (t1, (k, v) :: kvsa) = rbtreeify_f na kvs in
                             apfst (fun a -> Branch (B, t1, k, v, a))
                               (rbtreeify_f na kvsa))))));;

let rec rbtreeify kvs = fst (rbtreeify_g (suc (size_list kvs)) kvs);;

let rec gen_entries
  kvts x1 = match kvts, x1 with
    kvts, Branch (c, l, k, v, r) -> gen_entries (((k, v), r) :: kvts) l
    | (kv, t) :: kvts, Empty -> kv :: gen_entries kvts t
    | [], Empty -> [];;

let rec entries x = gen_entries [] x;;

let rec folda
  f xa1 x = match f, xa1, x with
    f, Branch (c, lt, k, v, rt), x -> folda f rt (f k v (folda f lt x))
    | f, Empty, x -> x;;

let rec rbt_comp_union_with_key
  c f t1 t2 =
    (match compare_height t1 t1 t2 t2
      with LT -> folda (rbt_comp_insert_with_key c (fun k v w -> f k w v)) t1 t2
      | GT -> folda (rbt_comp_insert_with_key c f) t2 t1
      | EQ -> rbtreeify (comp_sunion_with c f (entries t1) (entries t2)));;

let rec joina _A
  xc xd xe =
    Mapping_RBT
      (rbt_comp_union_with_key (the (ccompare _A)) xc (impl_ofa _A xd)
        (impl_ofa _A xe));;

let rec list_insert
  equal x xs = (if list_member equal xs x then xs else x :: xs);;

let rec inserta _A
  xb xc = Abs_dlist (list_insert (the (ceq _A)) xb (list_of_dlist _A xc));;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec foldc _A x xc = fold x (list_of_dlist _A xc);;

let rec union _A = foldc _A (inserta _A);;

let rec id x = (fun xa -> xa) x;;

let rec is_none = function Some x -> false
                  | None -> true;;

let rec inter_list _A
  xb xc =
    Mapping_RBT
      (fold (fun k -> rbt_comp_insert (the (ccompare _A)) k ())
        (filtera
          (fun x ->
            not (is_none
                  (rbt_comp_lookup (the (ccompare _A)) (impl_ofa _A xb) x)))
          xc)
        Empty);;

let rec filterc _A
  xb xc = Mapping_RBT (rbtreeify (filtera xb (entries (impl_ofa _A xc))));;

let rec comp_sinter_with
  c f uv uu = match c, f, uv, uu with
    c, f, (ka, va) :: asa, (k, v) :: bs ->
      (match c k ka with Eqa -> (ka, f ka va v) :: comp_sinter_with c f asa bs
        | Lt -> comp_sinter_with c f ((ka, va) :: asa) bs
        | Gt -> comp_sinter_with c f asa ((k, v) :: bs))
    | c, f, [], uu -> []
    | c, f, uv, [] -> [];;

let rec map_option f x1 = match f, x1 with f, None -> None
                     | f, Some x2 -> Some (f x2);;

let rec map_filter
  f x1 = match f, x1 with f, [] -> []
    | f, x :: xs ->
        (match f x with None -> map_filter f xs
          | Some y -> y :: map_filter f xs);;

let rec rbt_comp_inter_with_key
  c f t1 t2 =
    (match compare_height t1 t1 t2 t2
      with LT ->
        rbtreeify
          (map_filter
            (fun (k, v) ->
              map_option (fun w -> (k, f k v w)) (rbt_comp_lookup c t2 k))
            (entries t1))
      | GT ->
        rbtreeify
          (map_filter
            (fun (k, v) ->
              map_option (fun w -> (k, f k w v)) (rbt_comp_lookup c t1 k))
            (entries t2))
      | EQ -> rbtreeify (comp_sinter_with c f (entries t1) (entries t2)));;

let rec meet _A
  xc xd xe =
    Mapping_RBT
      (rbt_comp_inter_with_key (the (ccompare _A)) xc (impl_ofa _A xd)
        (impl_ofa _A xe));;

let rec filterb _A xb xc = Abs_dlist (filtera xb (list_of_dlist _A xc));;

let rec comp f g = (fun x -> f (g x));;

let rec inf_seta (_A1, _A2)
  g ga = match g, ga with
    RBT_set rbt1, Set_Monad xs ->
      (match ccompare _A2
        with None ->
          failwith "inter RBT_set Set_Monad: ccompare = None"
            (fun _ -> inf_seta (_A1, _A2) (RBT_set rbt1) (Set_Monad xs))
        | Some _ -> RBT_set (inter_list _A2 rbt1 xs))
    | RBT_set rbt, DList_set dxs ->
        (match ccompare _A2
          with None ->
            failwith "inter RBT_set DList_set: ccompare = None"
              (fun _ -> inf_seta (_A1, _A2) (RBT_set rbt) (DList_set dxs))
          | Some _ ->
            (match ceq _A1
              with None ->
                failwith "inter RBT_set DList_set: ceq = None"
                  (fun _ -> inf_seta (_A1, _A2) (RBT_set rbt) (DList_set dxs))
              | Some _ -> RBT_set (inter_list _A2 rbt (list_of_dlist _A1 dxs))))
    | RBT_set rbt1, RBT_set rbt2 ->
        (match ccompare _A2
          with None ->
            failwith "inter RBT_set RBT_set: ccompare = None"
              (fun _ -> inf_seta (_A1, _A2) (RBT_set rbt1) (RBT_set rbt2))
          | Some _ -> RBT_set (meet _A2 (fun _ _ -> id) rbt1 rbt2))
    | DList_set dxs1, Set_Monad xs ->
        (match ceq _A1
          with None ->
            failwith "inter DList_set Set_Monad: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) (DList_set dxs1) (Set_Monad xs))
          | Some eq -> DList_set (filterb _A1 (list_member eq xs) dxs1))
    | DList_set dxs1, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "inter DList_set DList_set: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) (DList_set dxs1) (DList_set dxs2))
          | Some _ -> DList_set (filterb _A1 (memberc _A1 dxs2) dxs1))
    | DList_set dxs, RBT_set rbt ->
        (match ccompare _A2
          with None ->
            failwith "inter DList_set RBT_set: ccompare = None"
              (fun _ -> inf_seta (_A1, _A2) (DList_set dxs) (RBT_set rbt))
          | Some _ ->
            (match ceq _A1
              with None ->
                failwith "inter DList_set RBT_set: ceq = None"
                  (fun _ -> inf_seta (_A1, _A2) (DList_set dxs) (RBT_set rbt))
              | Some _ -> RBT_set (inter_list _A2 rbt (list_of_dlist _A1 dxs))))
    | Set_Monad xs1, Set_Monad xs2 ->
        (match ceq _A1
          with None ->
            failwith "inter Set_Monad Set_Monad: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) (Set_Monad xs1) (Set_Monad xs2))
          | Some eq -> Set_Monad (filtera (list_member eq xs2) xs1))
    | Set_Monad xs, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "inter Set_Monad DList_set: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) (Set_Monad xs) (DList_set dxs2))
          | Some eq -> DList_set (filterb _A1 (list_member eq xs) dxs2))
    | Set_Monad xs, RBT_set rbt1 ->
        (match ccompare _A2
          with None ->
            failwith "inter Set_Monad RBT_set: ccompare = None"
              (fun _ -> inf_seta (_A1, _A2) (RBT_set rbt1) (Set_Monad xs))
          | Some _ -> RBT_set (inter_list _A2 rbt1 xs))
    | Complement ba, Complement b -> Complement (sup_seta (_A1, _A2) ba b)
    | g, RBT_set rbt2 ->
        (match ccompare _A2
          with None ->
            failwith "inter RBT_set2: ccompare = None"
              (fun _ -> inf_seta (_A1, _A2) g (RBT_set rbt2))
          | Some _ ->
            RBT_set
              (filterc _A2 (comp (fun x -> member (_A1, _A2) x g) fst) rbt2))
    | RBT_set rbt1, g ->
        (match ccompare _A2
          with None ->
            failwith "inter RBT_set1: ccompare = None"
              (fun _ -> inf_seta (_A1, _A2) (RBT_set rbt1) g)
          | Some _ ->
            RBT_set
              (filterc _A2 (comp (fun x -> member (_A1, _A2) x g) fst) rbt1))
    | h, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "inter DList_set2: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) h (DList_set dxs2))
          | Some _ ->
            DList_set (filterb _A1 (fun x -> member (_A1, _A2) x h) dxs2))
    | DList_set dxs1, h ->
        (match ceq _A1
          with None ->
            failwith "inter DList_set1: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) (DList_set dxs1) h)
          | Some _ ->
            DList_set (filterb _A1 (fun x -> member (_A1, _A2) x h) dxs1))
    | i, Set_Monad xs -> Set_Monad (filtera (fun x -> member (_A1, _A2) x i) xs)
    | Set_Monad xs, i -> Set_Monad (filtera (fun x -> member (_A1, _A2) x i) xs)
    | j, Collect_set a -> Collect_set (fun x -> a x && member (_A1, _A2) x j)
    | Collect_set a, j -> Collect_set (fun x -> a x && member (_A1, _A2) x j)
and sup_seta (_A1, _A2)
  ba b = match ba, b with
    ba, Complement b -> Complement (inf_seta (_A1, _A2) (uminus_set ba) b)
    | Complement ba, b -> Complement (inf_seta (_A1, _A2) ba (uminus_set b))
    | b, Collect_set a -> Collect_set (fun x -> a x || member (_A1, _A2) x b)
    | Collect_set a, b -> Collect_set (fun x -> a x || member (_A1, _A2) x b)
    | Set_Monad xs, Set_Monad ys -> Set_Monad (xs @ ys)
    | DList_set dxs1, Set_Monad ws ->
        (match ceq _A1
          with None ->
            failwith "union DList_set Set_Monad: ceq = None"
              (fun _ -> sup_seta (_A1, _A2) (DList_set dxs1) (Set_Monad ws))
          | Some _ -> DList_set (fold (inserta _A1) ws dxs1))
    | Set_Monad ws, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "union Set_Monad DList_set: ceq = None"
              (fun _ -> sup_seta (_A1, _A2) (Set_Monad ws) (DList_set dxs2))
          | Some _ -> DList_set (fold (inserta _A1) ws dxs2))
    | RBT_set rbt1, Set_Monad zs ->
        (match ccompare _A2
          with None ->
            failwith "union RBT_set Set_Monad: ccompare = None"
              (fun _ -> sup_seta (_A1, _A2) (RBT_set rbt1) (Set_Monad zs))
          | Some _ -> RBT_set (fold (fun k -> insertb _A2 k ()) zs rbt1))
    | Set_Monad zs, RBT_set rbt2 ->
        (match ccompare _A2
          with None ->
            failwith "union Set_Monad RBT_set: ccompare = None"
              (fun _ -> sup_seta (_A1, _A2) (Set_Monad zs) (RBT_set rbt2))
          | Some _ -> RBT_set (fold (fun k -> insertb _A2 k ()) zs rbt2))
    | DList_set dxs1, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "union DList_set DList_set: ceq = None"
              (fun _ -> sup_seta (_A1, _A2) (DList_set dxs1) (DList_set dxs2))
          | Some _ -> DList_set (union _A1 dxs1 dxs2))
    | DList_set dxs, RBT_set rbt ->
        (match ccompare _A2
          with None ->
            failwith "union DList_set RBT_set: ccompare = None"
              (fun _ -> sup_seta (_A1, _A2) (RBT_set rbt) (DList_set dxs))
          | Some _ ->
            (match ceq _A1
              with None ->
                failwith "union DList_set RBT_set: ceq = None"
                  (fun _ -> sup_seta (_A1, _A2) (RBT_set rbt) (DList_set dxs))
              | Some _ ->
                RBT_set (foldc _A1 (fun k -> insertb _A2 k ()) dxs rbt)))
    | RBT_set rbt, DList_set dxs ->
        (match ccompare _A2
          with None ->
            failwith "union RBT_set DList_set: ccompare = None"
              (fun _ -> sup_seta (_A1, _A2) (RBT_set rbt) (DList_set dxs))
          | Some _ ->
            (match ceq _A1
              with None ->
                failwith "union RBT_set DList_set: ceq = None"
                  (fun _ -> sup_seta (_A1, _A2) (RBT_set rbt) (DList_set dxs))
              | Some _ ->
                RBT_set (foldc _A1 (fun k -> insertb _A2 k ()) dxs rbt)))
    | RBT_set rbt1, RBT_set rbt2 ->
        (match ccompare _A2
          with None ->
            failwith "union RBT_set RBT_set: ccompare = None"
              (fun _ -> sup_seta (_A1, _A2) (RBT_set rbt1) (RBT_set rbt2))
          | Some _ -> RBT_set (joina _A2 (fun _ _ -> id) rbt1 rbt2));;

let rec inf_set (_A1, _A2) = ({inf = inf_seta (_A1, _A2)} : 'a set inf);;

let rec sup_set (_A1, _A2) = ({sup = sup_seta (_A1, _A2)} : 'a set sup);;

let rec less_set (_A1, _A2, _A3)
  a b = less_eq_set (_A1, _A2, _A3) a b &&
          not (less_eq_set (_A1, _A2, _A3) b a);;

let rec ord_set (_A1, _A2, _A3) =
  ({less_eq = less_eq_set (_A1, _A2, _A3); less = less_set (_A1, _A2, _A3)} :
    'a set ord);;

let rec preorder_set (_A1, _A2, _A3) =
  ({ord_preorder = (ord_set (_A1, _A2, _A3))} : 'a set preorder);;

let rec order_set (_A1, _A2, _A3) =
  ({preorder_order = (preorder_set (_A1, _A2, _A3))} : 'a set order);;

let rec semilattice_sup_set (_A1, _A2, _A3) =
  ({sup_semilattice_sup = (sup_set (_A2, _A3));
     order_semilattice_sup = (order_set (_A1, _A2, _A3))}
    : 'a set semilattice_sup);;

let rec semilattice_inf_set (_A1, _A2, _A3) =
  ({inf_semilattice_inf = (inf_set (_A2, _A3));
     order_semilattice_inf = (order_set (_A1, _A2, _A3))}
    : 'a set semilattice_inf);;

let rec lattice_set (_A1, _A2, _A3) =
  ({semilattice_inf_lattice = (semilattice_inf_set (_A1, _A2, _A3));
     semilattice_sup_lattice = (semilattice_sup_set (_A1, _A2, _A3))}
    : 'a set lattice);;

let rec list_all2_fusion
  p g1 g2 s1 s2 =
    (if has_next g1 s1
      then has_next g2 s2 &&
             (let (x, s1a) = next g1 s1 in
              let (y, s2a) = next g2 s2 in
               p x y && list_all2_fusion p g1 g2 s1a s2a)
      else not (has_next g2 s2));;

let rec set_eq (_A1, _A2, _A3)
  a b = match a, b with
    RBT_set rbt1, RBT_set rbt2 ->
      (match ccompare _A3
        with None ->
          failwith "set_eq RBT_set RBT_set: ccompare = None"
            (fun _ -> set_eq (_A1, _A2, _A3) (RBT_set rbt1) (RBT_set rbt2))
        | Some c ->
          (match ceq _A2
            with None ->
              list_all2_fusion (fun x y -> equal_order (c x y) Eqa)
                rbt_keys_generator rbt_keys_generator (init _A3 rbt1)
                (init _A3 rbt2)
            | Some eq ->
              list_all2_fusion eq rbt_keys_generator rbt_keys_generator
                (init _A3 rbt1) (init _A3 rbt2)))
    | Complement a, Complement b -> set_eq (_A1, _A2, _A3) a b
    | a, b ->
        less_eq_set (_A1, _A2, _A3) a b && less_eq_set (_A1, _A2, _A3) b a;;

let rec ceq_seta (_A1, _A2, _A3)
  = (match ceq _A2 with None -> None
      | Some _ -> Some (set_eq (_A1, _A2, _A3)));;

let rec ceq_set (_A1, _A2, _A3) =
  ({ceq = ceq_seta (_A1, _A2, _A3)} : 'a set ceq);;

let set_impl_seta : ('a set, set_impla) phantom = Phantom Set_Choose;;

let set_impl_set = ({set_impl = set_impl_seta} : 'a set set_impl);;

let rec of_phantom (Phantom x) = x;;

let rec finite_UNIV_seta _A = Phantom (of_phantom (finite_UNIV _A));;

let rec power _A
  a n = (if equal_nata n zero_nat then one _A.one_power
          else times _A.times_power a (power _A a (minus_nat n one_nata)));;

let rec card_UNIV_seta _A
  = Phantom
      (let c = of_phantom (card_UNIVa _A) in
        (if equal_nata c zero_nat then zero_nat
          else power power_nat (nat_of_integer (Z.of_int 2)) c));;

let rec finite_UNIV_set _A =
  ({finite_UNIV = finite_UNIV_seta _A} : 'a set finite_UNIV);;

let rec card_UNIV_set _A =
  ({finite_UNIV_card_UNIV = (finite_UNIV_set _A.finite_UNIV_card_UNIV);
     card_UNIVa = card_UNIV_seta _A}
    : 'a set card_UNIV);;

let rec set_less_eq_aux_Compl_fusion
  less proper_interval g1 g2 ao s1 s2 =
    (if has_next g1 s1
      then (if has_next g2 s2
             then (let (x, s1a) = next g1 s1 in
                   let (y, s2a) = next g2 s2 in
                    (if less x y
                      then proper_interval ao (Some x) ||
                             set_less_eq_aux_Compl_fusion less proper_interval
                               g1 g2 (Some x) s1a s2
                      else (if less y x
                             then proper_interval ao (Some y) ||
                                    set_less_eq_aux_Compl_fusion less
                                      proper_interval g1 g2 (Some y) s1 s2a
                             else proper_interval ao (Some y))))
             else true)
      else true);;

let rec compl_set_less_eq_aux_fusion
  less proper_interval g1 g2 ao s1 s2 =
    (if has_next g1 s1
      then (let (x, s1a) = next g1 s1 in
             (if has_next g2 s2
               then (let (y, s2a) = next g2 s2 in
                      (if less x y
                        then not (proper_interval ao (Some x)) &&
                               compl_set_less_eq_aux_fusion less proper_interval
                                 g1 g2 (Some x) s1a s2
                        else (if less y x
                               then not (proper_interval ao (Some y)) &&
                                      compl_set_less_eq_aux_fusion less
proper_interval g1 g2 (Some y) s1 s2a
                               else not (proper_interval ao (Some y)))))
               else not (proper_interval ao (Some x)) &&
                      compl_set_less_eq_aux_fusion less proper_interval g1 g2
                        (Some x) s1a s2))
      else (if has_next g2 s2
             then (let (y, s2a) = next g2 s2 in
                    not (proper_interval ao (Some y)) &&
                      compl_set_less_eq_aux_fusion less proper_interval g1 g2
                        (Some y) s1 s2a)
             else not (proper_interval ao None)));;

let rec set_less_eq_aux_Compl
  less proper_interval ao xs ys = match less, proper_interval, ao, xs, ys with
    less, proper_interval, ao, x :: xs, y :: ys ->
      (if less x y
        then proper_interval ao (Some x) ||
               set_less_eq_aux_Compl less proper_interval (Some x) xs (y :: ys)
        else (if less y x
               then proper_interval ao (Some y) ||
                      set_less_eq_aux_Compl less proper_interval (Some y)
                        (x :: xs) ys
               else proper_interval ao (Some y)))
    | less, proper_interval, ao, xs, [] -> true
    | less, proper_interval, ao, [], ys -> true;;

let rec compl_set_less_eq_aux
  less proper_interval ao x3 x4 = match less, proper_interval, ao, x3, x4 with
    less, proper_interval, ao, x :: xs, y :: ys ->
      (if less x y
        then not (proper_interval ao (Some x)) &&
               compl_set_less_eq_aux less proper_interval (Some x) xs (y :: ys)
        else (if less y x
               then not (proper_interval ao (Some y)) &&
                      compl_set_less_eq_aux less proper_interval (Some y)
                        (x :: xs) ys
               else not (proper_interval ao (Some y))))
    | less, proper_interval, ao, x :: xs, [] ->
        not (proper_interval ao (Some x)) &&
          compl_set_less_eq_aux less proper_interval (Some x) xs []
    | less, proper_interval, ao, [], y :: ys ->
        not (proper_interval ao (Some y)) &&
          compl_set_less_eq_aux less proper_interval (Some y) [] ys
    | less, proper_interval, ao, [], [] -> not (proper_interval ao None);;

let rec lexord_eq_fusion
  less g1 g2 s1 s2 =
    (if has_next g1 s1
      then has_next g2 s2 &&
             (let (x, s1a) = next g1 s1 in
              let (y, s2a) = next g2 s2 in
               less x y ||
                 not (less y x) && lexord_eq_fusion less g1 g2 s1a s2a)
      else true);;

let rec remdups_sorted
  less x1 = match less, x1 with
    less, x :: y :: xs ->
      (if less x y then x :: remdups_sorted less (y :: xs)
        else remdups_sorted less (y :: xs))
    | less, [x] -> [x]
    | less, [] -> [];;

let rec quicksort_acc
  less ac x2 = match less, ac, x2 with
    less, ac, x :: v :: va -> quicksort_part less ac x [] [] [] (v :: va)
    | less, ac, [x] -> x :: ac
    | less, ac, [] -> ac
and quicksort_part
  less ac x lts eqs gts xa6 = match less, ac, x, lts, eqs, gts, xa6 with
    less, ac, x, lts, eqs, gts, z :: zs ->
      (if less x z then quicksort_part less ac x lts eqs (z :: gts) zs
        else (if less z x then quicksort_part less ac x (z :: lts) eqs gts zs
               else quicksort_part less ac x lts (z :: eqs) gts zs))
    | less, ac, x, lts, eqs, gts, [] ->
        quicksort_acc less (eqs @ x :: quicksort_acc less ac gts) lts;;

let rec quicksort less = quicksort_acc less [];;

let rec gen_keys
  kts x1 = match kts, x1 with
    kts, Branch (c, l, k, v, r) -> gen_keys ((k, r) :: kts) l
    | (k, t) :: kts, Empty -> k :: gen_keys kts t
    | [], Empty -> [];;

let rec keys x = gen_keys [] x;;

let rec keysa _A xa = keys (impl_ofa _A xa);;

let rec csorted_list_of_set (_A1, _A2)
  = function
    Set_Monad xs ->
      (match ccompare _A2
        with None ->
          failwith "csorted_list_of_set Set_Monad: ccompare = None"
            (fun _ -> csorted_list_of_set (_A1, _A2) (Set_Monad xs))
        | Some c -> remdups_sorted (lt_of_comp c) (quicksort (lt_of_comp c) xs))
    | DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "csorted_list_of_set DList_set: ceq = None"
              (fun _ -> csorted_list_of_set (_A1, _A2) (DList_set dxs))
          | Some _ ->
            (match ccompare _A2
              with None ->
                failwith "csorted_list_of_set DList_set: ccompare = None"
                  (fun _ -> csorted_list_of_set (_A1, _A2) (DList_set dxs))
              | Some c -> quicksort (lt_of_comp c) (list_of_dlist _A1 dxs)))
    | RBT_set rbt ->
        (match ccompare _A2
          with None ->
            failwith "csorted_list_of_set RBT_set: ccompare = None"
              (fun _ -> csorted_list_of_set (_A1, _A2) (RBT_set rbt))
          | Some _ -> keysa _A2 rbt);;

let rec emptya _A = Mapping_RBT Empty;;

let rec empty _A = Abs_dlist [];;

let rec set_empty_choose (_A1, _A2)
  = (match ccompare _A2
      with None ->
        (match ceq _A1 with None -> Set_Monad []
          | Some _ -> DList_set (empty _A1))
      | Some _ -> RBT_set (emptya _A2));;

let rec set_empty (_A1, _A2)
  = function Set_Choose -> set_empty_choose (_A1, _A2)
    | Set_Monada -> Set_Monad []
    | Set_RBT -> RBT_set (emptya _A2)
    | Set_DList -> DList_set (empty _A1)
    | Set_Collect -> Collect_set (fun _ -> false);;

let rec bot_set (_A1, _A2, _A3)
  = set_empty (_A1, _A2) (of_phantom (set_impl _A3));;

let rec top_set (_A1, _A2, _A3) = uminus_set (bot_set (_A1, _A2, _A3));;

let rec le_of_comp
  acomp x y = (match acomp x y with Eqa -> true | Lt -> true | Gt -> false);;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec lexordp_eq
  less xs ys = match less, xs, ys with
    less, x :: xs, y :: ys ->
      less x y || not (less y x) && lexordp_eq less xs ys
    | less, x :: xs, [] -> false
    | less, xs, [] -> null xs
    | less, [], ys -> true;;

let rec finitea _A = finitea _A;;

let rec finite (_A1, _A2, _A3)
  = function
    Collect_set p ->
      of_phantom (finite_UNIV _A1) ||
        failwith "finite Collect_set" (fun _ -> finitea _A1 (Collect_set p))
    | Set_Monad xs -> true
    | Complement a ->
        (if of_phantom (finite_UNIV _A1) then true
          else (if finitea _A1 a then false
                 else failwith "finite Complement: infinite set"
                        (fun _ -> finitea _A1 (Complement a))))
    | RBT_set rbt ->
        (match ccompare _A3
          with None ->
            failwith "finite RBT_set: ccompare = None"
              (fun _ -> finite (_A1, _A2, _A3) (RBT_set rbt))
          | Some _ -> true)
    | DList_set dxs ->
        (match ceq _A2
          with None ->
            failwith "finite DList_set: ceq = None"
              (fun _ -> finite (_A1, _A2, _A3) (DList_set dxs))
          | Some _ -> true);;

let rec set_less_aux_Compl_fusion
  less proper_interval g1 g2 ao s1 s2 =
    (if has_next g1 s1
      then (let (x, s1a) = next g1 s1 in
             (if has_next g2 s2
               then (let (y, s2a) = next g2 s2 in
                      (if less x y
                        then proper_interval ao (Some x) ||
                               set_less_aux_Compl_fusion less proper_interval g1
                                 g2 (Some x) s1a s2
                        else (if less y x
                               then proper_interval ao (Some y) ||
                                      set_less_aux_Compl_fusion less
proper_interval g1 g2 (Some y) s1 s2a
                               else proper_interval ao (Some y))))
               else proper_interval ao (Some x) ||
                      set_less_aux_Compl_fusion less proper_interval g1 g2
                        (Some x) s1a s2))
      else (if has_next g2 s2
             then (let (y, s2a) = next g2 s2 in
                    proper_interval ao (Some y) ||
                      set_less_aux_Compl_fusion less proper_interval g1 g2
                        (Some y) s1 s2a)
             else proper_interval ao None));;

let rec compl_set_less_aux_fusion
  less proper_interval g1 g2 ao s1 s2 =
    has_next g1 s1 &&
      (has_next g2 s2 &&
        (let (x, s1a) = next g1 s1 in
         let (y, s2a) = next g2 s2 in
          (if less x y
            then not (proper_interval ao (Some x)) &&
                   compl_set_less_aux_fusion less proper_interval g1 g2 (Some x)
                     s1a s2
            else (if less y x
                   then not (proper_interval ao (Some y)) &&
                          compl_set_less_aux_fusion less proper_interval g1 g2
                            (Some y) s1 s2a
                   else not (proper_interval ao (Some y))))));;

let rec set_less_aux_Compl
  less proper_interval ao x3 x4 = match less, proper_interval, ao, x3, x4 with
    less, proper_interval, ao, x :: xs, y :: ys ->
      (if less x y
        then proper_interval ao (Some x) ||
               set_less_aux_Compl less proper_interval (Some x) xs (y :: ys)
        else (if less y x
               then proper_interval ao (Some y) ||
                      set_less_aux_Compl less proper_interval (Some y) (x :: xs)
                        ys
               else proper_interval ao (Some y)))
    | less, proper_interval, ao, x :: xs, [] ->
        proper_interval ao (Some x) ||
          set_less_aux_Compl less proper_interval (Some x) xs []
    | less, proper_interval, ao, [], y :: ys ->
        proper_interval ao (Some y) ||
          set_less_aux_Compl less proper_interval (Some y) [] ys
    | less, proper_interval, ao, [], [] -> proper_interval ao None;;

let rec compl_set_less_aux
  less proper_interval ao xs ys = match less, proper_interval, ao, xs, ys with
    less, proper_interval, ao, x :: xs, y :: ys ->
      (if less x y
        then not (proper_interval ao (Some x)) &&
               compl_set_less_aux less proper_interval (Some x) xs (y :: ys)
        else (if less y x
               then not (proper_interval ao (Some y)) &&
                      compl_set_less_aux less proper_interval (Some y) (x :: xs)
                        ys
               else not (proper_interval ao (Some y))))
    | less, proper_interval, ao, xs, [] -> false
    | less, proper_interval, ao, [], ys -> false;;

let rec lexord_fusion
  less g1 g2 s1 s2 =
    (if has_next g1 s1
      then (if has_next g2 s2
             then (let (x, s1a) = next g1 s1 in
                   let (y, s2a) = next g2 s2 in
                    less x y ||
                      not (less y x) && lexord_fusion less g1 g2 s1a s2a)
             else false)
      else has_next g2 s2);;

let rec lexordp
  less xs ys = match less, xs, ys with
    less, x :: xs, y :: ys -> less x y || not (less y x) && lexordp less xs ys
    | less, xs, [] -> false
    | less, [], ys -> not (null ys);;

let rec comp_of_ords
  le lt x y = (if lt x y then Lt else (if le x y then Eqa else Gt));;

let rec ccompare_seta (_A1, _A2, _A3, _A4)
  = (match ccompare _A3.ccompare_cproper_interval with None -> None
      | Some _ ->
        Some (comp_of_ords (cless_eq_set (_A1, _A2, _A3, _A4))
               (cless_set (_A1, _A2, _A3, _A4))))
and cless_set (_A1, _A2, _A3, _A4)
  a b = match a, b with
    Complement (RBT_set rbt1), RBT_set rbt2 ->
      (match ccompare _A3.ccompare_cproper_interval
        with None ->
          failwith "cless_set (Complement RBT_set) RBT_set: ccompare = None"
            (fun _ ->
              cless_set (_A1, _A2, _A3, _A4) (Complement (RBT_set rbt1))
                (RBT_set rbt2))
        | Some c ->
          finite (_A1, _A2, _A3.ccompare_cproper_interval)
            (top_set (_A2, _A3.ccompare_cproper_interval, _A4)) &&
            compl_set_less_aux_fusion (lt_of_comp c) (cproper_interval _A3)
              rbt_keys_generator rbt_keys_generator None
              (init _A3.ccompare_cproper_interval rbt1)
              (init _A3.ccompare_cproper_interval rbt2))
    | RBT_set rbt1, Complement (RBT_set rbt2) ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_set RBT_set (Complement RBT_set): ccompare = None"
              (fun _ ->
                cless_set (_A1, _A2, _A3, _A4) (RBT_set rbt1)
                  (Complement (RBT_set rbt2)))
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval)
                  (top_set (_A2, _A3.ccompare_cproper_interval, _A4))
              then set_less_aux_Compl_fusion (lt_of_comp c)
                     (cproper_interval _A3) rbt_keys_generator
                     rbt_keys_generator None
                     (init _A3.ccompare_cproper_interval rbt1)
                     (init _A3.ccompare_cproper_interval rbt2)
              else true))
    | RBT_set rbta, RBT_set rbt ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_set RBT_set RBT_set: ccompare = None"
              (fun _ ->
                cless_set (_A1, _A2, _A3, _A4) (RBT_set rbta) (RBT_set rbt))
          | Some c ->
            lexord_fusion (fun x y -> lt_of_comp c y x) rbt_keys_generator
              rbt_keys_generator (init _A3.ccompare_cproper_interval rbta)
              (init _A3.ccompare_cproper_interval rbt))
    | Complement a, Complement b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_set Complement Complement: ccompare = None"
              (fun _ ->
                cless_set (_A1, _A2, _A3, _A4) (Complement a) (Complement b))
          | Some _ -> lt_of_comp (the (ccompare_seta (_A1, _A2, _A3, _A4))) b a)
    | Complement a, b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_set Complement1: ccompare = None"
              (fun _ -> cless_set (_A1, _A2, _A3, _A4) (Complement a) b)
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval) a &&
                  finite (_A1, _A2, _A3.ccompare_cproper_interval) b
              then finite (_A1, _A2, _A3.ccompare_cproper_interval)
                     (top_set (_A2, _A3.ccompare_cproper_interval, _A4)) &&
                     compl_set_less_aux (lt_of_comp c) (cproper_interval _A3)
                       None
                       (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                         a)
                       (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                         b)
              else failwith "cless_set Complement1: infinite set"
                     (fun _ ->
                       cless_set (_A1, _A2, _A3, _A4) (Complement a) b)))
    | a, Complement b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_set Complement2: ccompare = None"
              (fun _ -> cless_set (_A1, _A2, _A3, _A4) a (Complement b))
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval) a &&
                  finite (_A1, _A2, _A3.ccompare_cproper_interval) b
              then (if finite (_A1, _A2, _A3.ccompare_cproper_interval)
                         (top_set (_A2, _A3.ccompare_cproper_interval, _A4))
                     then set_less_aux_Compl (lt_of_comp c)
                            (cproper_interval _A3) None
                            (csorted_list_of_set
                              (_A2, _A3.ccompare_cproper_interval) a)
                            (csorted_list_of_set
                              (_A2, _A3.ccompare_cproper_interval) b)
                     else true)
              else failwith "cless_set Complement2: infinite set"
                     (fun _ ->
                       cless_set (_A1, _A2, _A3, _A4) a (Complement b))))
    | a, b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_set: ccompare = None"
              (fun _ -> cless_set (_A1, _A2, _A3, _A4) a b)
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval) a &&
                  finite (_A1, _A2, _A3.ccompare_cproper_interval) b
              then lexordp (fun x y -> lt_of_comp c y x)
                     (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                       a)
                     (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                       b)
              else failwith "cless_set: infinite set"
                     (fun _ -> cless_set (_A1, _A2, _A3, _A4) a b)))
and cless_eq_set (_A1, _A2, _A3, _A4)
  a b = match a, b with
    Complement (RBT_set rbt1), RBT_set rbt2 ->
      (match ccompare _A3.ccompare_cproper_interval
        with None ->
          failwith "cless_eq_set (Complement RBT_set) RBT_set: ccompare = None"
            (fun _ ->
              cless_eq_set (_A1, _A2, _A3, _A4) (Complement (RBT_set rbt1))
                (RBT_set rbt2))
        | Some c ->
          finite (_A1, _A2, _A3.ccompare_cproper_interval)
            (top_set (_A2, _A3.ccompare_cproper_interval, _A4)) &&
            compl_set_less_eq_aux_fusion (lt_of_comp c) (cproper_interval _A3)
              rbt_keys_generator rbt_keys_generator None
              (init _A3.ccompare_cproper_interval rbt1)
              (init _A3.ccompare_cproper_interval rbt2))
    | RBT_set rbt1, Complement (RBT_set rbt2) ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith
              "cless_eq_set RBT_set (Complement RBT_set): ccompare = None"
              (fun _ ->
                cless_eq_set (_A1, _A2, _A3, _A4) (RBT_set rbt1)
                  (Complement (RBT_set rbt2)))
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval)
                  (top_set (_A2, _A3.ccompare_cproper_interval, _A4))
              then set_less_eq_aux_Compl_fusion (lt_of_comp c)
                     (cproper_interval _A3) rbt_keys_generator
                     rbt_keys_generator None
                     (init _A3.ccompare_cproper_interval rbt1)
                     (init _A3.ccompare_cproper_interval rbt2)
              else true))
    | RBT_set rbta, RBT_set rbt ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_eq_set RBT_set RBT_set: ccompare = None"
              (fun _ ->
                cless_eq_set (_A1, _A2, _A3, _A4) (RBT_set rbta) (RBT_set rbt))
          | Some c ->
            lexord_eq_fusion (fun x y -> lt_of_comp c y x) rbt_keys_generator
              rbt_keys_generator (init _A3.ccompare_cproper_interval rbta)
              (init _A3.ccompare_cproper_interval rbt))
    | Complement a, Complement b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_eq_set Complement Complement: ccompare = None"
              (fun _ ->
                le_of_comp (the (ccompare_seta (_A1, _A2, _A3, _A4)))
                  (Complement a) (Complement b))
          | Some _ -> cless_eq_set (_A1, _A2, _A3, _A4) b a)
    | Complement a, b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_eq_set Complement1: ccompare = None"
              (fun _ -> cless_eq_set (_A1, _A2, _A3, _A4) (Complement a) b)
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval) a &&
                  finite (_A1, _A2, _A3.ccompare_cproper_interval) b
              then finite (_A1, _A2, _A3.ccompare_cproper_interval)
                     (top_set (_A2, _A3.ccompare_cproper_interval, _A4)) &&
                     compl_set_less_eq_aux (lt_of_comp c) (cproper_interval _A3)
                       None
                       (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                         a)
                       (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                         b)
              else failwith "cless_eq_set Complement1: infinite set"
                     (fun _ ->
                       cless_eq_set (_A1, _A2, _A3, _A4) (Complement a) b)))
    | a, Complement b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_eq_set Complement2: ccompare = None"
              (fun _ -> cless_eq_set (_A1, _A2, _A3, _A4) a (Complement b))
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval) a &&
                  finite (_A1, _A2, _A3.ccompare_cproper_interval) b
              then (if finite (_A1, _A2, _A3.ccompare_cproper_interval)
                         (top_set (_A2, _A3.ccompare_cproper_interval, _A4))
                     then set_less_eq_aux_Compl (lt_of_comp c)
                            (cproper_interval _A3) None
                            (csorted_list_of_set
                              (_A2, _A3.ccompare_cproper_interval) a)
                            (csorted_list_of_set
                              (_A2, _A3.ccompare_cproper_interval) b)
                     else true)
              else failwith "cless_eq_set Complement2: infinite set"
                     (fun _ ->
                       cless_eq_set (_A1, _A2, _A3, _A4) a (Complement b))))
    | a, b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cless_eq_set: ccompare = None"
              (fun _ -> cless_eq_set (_A1, _A2, _A3, _A4) a b)
          | Some c ->
            (if finite (_A1, _A2, _A3.ccompare_cproper_interval) a &&
                  finite (_A1, _A2, _A3.ccompare_cproper_interval) b
              then lexordp_eq (fun x y -> lt_of_comp c y x)
                     (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                       a)
                     (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval)
                       b)
              else failwith "cless_eq_set: infinite set"
                     (fun _ -> cless_eq_set (_A1, _A2, _A3, _A4) a b)));;

let rec ccompare_set (_A1, _A2, _A3, _A4) =
  ({ccompare = ccompare_seta (_A1, _A2, _A3, _A4)} : 'a set ccompare);;

let rec fold_fusion
  g f s b =
    (if has_next g s then (let (x, sa) = next g s in fold_fusion g f sa (f x b))
      else b);;

let rec length_last_fusion
  g s = (if has_next g s
          then (let (x, sa) = next g s in
                 fold_fusion g (fun xa (n, _) -> (plus_nat n one_nata, xa)) sa
                   (one_nata, x))
          else (zero_nat, failwith "undefined"));;

let rec gen_length_fusion
  g n s =
    (if has_next g s then gen_length_fusion g (suc n) (snd (next g s)) else n);;

let rec length_fusion g = gen_length_fusion g zero_nat;;

let rec card_UNIV _A = card_UNIVa _A;;

let rec proper_interval_set_Compl_aux_fusion _A
  less proper_interval g1 g2 ao n s1 s2 =
    (if has_next g1 s1
      then (let (x, s1a) = next g1 s1 in
             (if has_next g2 s2
               then (let (y, s2a) = next g2 s2 in
                      (if less x y
                        then proper_interval ao (Some x) ||
                               proper_interval_set_Compl_aux_fusion _A less
                                 proper_interval g1 g2 (Some x)
                                 (plus_nat n one_nata) s1a s2
                        else (if less y x
                               then proper_interval ao (Some y) ||
                                      proper_interval_set_Compl_aux_fusion _A
less proper_interval g1 g2 (Some y) (plus_nat n one_nata) s1 s2a
                               else proper_interval ao (Some x) &&
                                      (let m =
 minus_nat (of_phantom (card_UNIV _A)) n in
not (equal_nata (minus_nat m (length_fusion g2 s2a))
      (nat_of_integer (Z.of_int 2))) ||
  not (equal_nata (minus_nat m (length_fusion g1 s1a))
        (nat_of_integer (Z.of_int 2)))))))
               else (let m = minus_nat (of_phantom (card_UNIV _A)) n in
                     let (len_x, xa) = length_last_fusion g1 s1 in
                      not (equal_nata m len_x) &&
                        (if equal_nata m (plus_nat len_x one_nata)
                          then not (proper_interval (Some xa) None)
                          else true))))
      else (if has_next g2 s2
             then (let (_, _) = next g2 s2 in
                   let m = minus_nat (of_phantom (card_UNIV _A)) n in
                   let (len_y, y) = length_last_fusion g2 s2 in
                    not (equal_nata m len_y) &&
                      (if equal_nata m (plus_nat len_y one_nata)
                        then not (proper_interval (Some y) None) else true))
             else less_nat (plus_nat n one_nata) (of_phantom (card_UNIV _A))));;

let rec proper_interval_Compl_set_aux_fusion
  less proper_interval g1 g2 ao s1 s2 =
    has_next g1 s1 &&
      (has_next g2 s2 &&
        (let (x, s1a) = next g1 s1 in
         let (y, s2a) = next g2 s2 in
          (if less x y
            then not (proper_interval ao (Some x)) &&
                   proper_interval_Compl_set_aux_fusion less proper_interval g1
                     g2 (Some x) s1a s2
            else (if less y x
                   then not (proper_interval ao (Some y)) &&
                          proper_interval_Compl_set_aux_fusion less
                            proper_interval g1 g2 (Some y) s1 s2a
                   else not (proper_interval ao (Some x)) &&
                          (has_next g2 s2a || has_next g1 s1a)))));;

let rec exhaustive_above_fusion
  proper_interval g y s =
    (if has_next g s
      then (let (x, sa) = next g s in
             not (proper_interval (Some y) (Some x)) &&
               exhaustive_above_fusion proper_interval g x sa)
      else not (proper_interval (Some y) None));;

let rec proper_interval_set_aux_fusion
  less proper_interval g1 g2 s1 s2 =
    has_next g2 s2 &&
      (let (y, s2a) = next g2 s2 in
        (if has_next g1 s1
          then (let (x, s1a) = next g1 s1 in
                 (if less x y then false
                   else (if less y x
                          then proper_interval (Some y) (Some x) ||
                                 (has_next g2 s2a ||
                                   not (exhaustive_above_fusion proper_interval
 g1 x s1a))
                          else proper_interval_set_aux_fusion less
                                 proper_interval g1 g2 s1a s2a)))
          else has_next g2 s2a || proper_interval (Some y) None));;

let rec length_last
  = function
    x :: xs ->
      fold (fun xa (n, _) -> (plus_nat n one_nata, xa)) xs (one_nata, x)
    | [] -> (zero_nat, failwith "undefined");;

let rec proper_interval_set_Compl_aux _A
  less proper_interval ao n x4 x5 = match less, proper_interval, ao, n, x4, x5
    with
    less, proper_interval, ao, n, x :: xs, y :: ys ->
      (if less x y
        then proper_interval ao (Some x) ||
               proper_interval_set_Compl_aux _A less proper_interval (Some x)
                 (plus_nat n one_nata) xs (y :: ys)
        else (if less y x
               then proper_interval ao (Some y) ||
                      proper_interval_set_Compl_aux _A less proper_interval
                        (Some y) (plus_nat n one_nata) (x :: xs) ys
               else proper_interval ao (Some x) &&
                      (let m = minus_nat (of_phantom (card_UNIV _A)) n in
                        not (equal_nata (minus_nat m (size_list ys))
                              (nat_of_integer (Z.of_int 2))) ||
                          not (equal_nata (minus_nat m (size_list xs))
                                (nat_of_integer (Z.of_int 2))))))
    | less, proper_interval, ao, n, x :: xs, [] ->
        (let m = minus_nat (of_phantom (card_UNIV _A)) n in
         let (len_x, xa) = length_last (x :: xs) in
          not (equal_nata m len_x) &&
            (if equal_nata m (plus_nat len_x one_nata)
              then not (proper_interval (Some xa) None) else true))
    | less, proper_interval, ao, n, [], y :: ys ->
        (let m = minus_nat (of_phantom (card_UNIV _A)) n in
         let (len_y, ya) = length_last (y :: ys) in
          not (equal_nata m len_y) &&
            (if equal_nata m (plus_nat len_y one_nata)
              then not (proper_interval (Some ya) None) else true))
    | less, proper_interval, ao, n, [], [] ->
        less_nat (plus_nat n one_nata) (of_phantom (card_UNIV _A));;

let rec proper_interval_Compl_set_aux
  less proper_interval ao uu uv = match less, proper_interval, ao, uu, uv with
    less, proper_interval, ao, uu, [] -> false
    | less, proper_interval, ao, [], uv -> false
    | less, proper_interval, ao, x :: xs, y :: ys ->
        (if less x y
          then not (proper_interval ao (Some x)) &&
                 proper_interval_Compl_set_aux less proper_interval (Some x) xs
                   (y :: ys)
          else (if less y x
                 then not (proper_interval ao (Some y)) &&
                        proper_interval_Compl_set_aux less proper_interval
                          (Some y) (x :: xs) ys
                 else not (proper_interval ao (Some x)) &&
                        (if null ys then not (null xs) else true)));;

let rec exhaustive_above
  proper_interval x xa2 = match proper_interval, x, xa2 with
    proper_interval, x, y :: ys ->
      not (proper_interval (Some x) (Some y)) &&
        exhaustive_above proper_interval y ys
    | proper_interval, x, [] -> not (proper_interval (Some x) None);;

let rec proper_interval_set_aux
  less proper_interval xs x3 = match less, proper_interval, xs, x3 with
    less, proper_interval, x :: xs, y :: ys ->
      (if less x y then false
        else (if less y x
               then proper_interval (Some y) (Some x) ||
                      (not (null ys) ||
                        not (exhaustive_above proper_interval x xs))
               else proper_interval_set_aux less proper_interval xs ys))
    | less, proper_interval, [], y :: ys ->
        not (null ys) || proper_interval (Some y) None
    | less, proper_interval, xs, [] -> false;;

let rec exhaustive_fusion
  proper_interval g s =
    has_next g s &&
      (let (x, sa) = next g s in
        not (proper_interval None (Some x)) &&
          exhaustive_above_fusion proper_interval g x sa);;

let rec list_remdups
  equal x1 = match equal, x1 with
    equal, x :: xs ->
      (if list_member equal xs x then list_remdups equal xs
        else x :: list_remdups equal xs)
    | equal, [] -> [];;

let rec length _A xa = size_list (list_of_dlist _A xa);;

let rec card (_A1, _A2, _A3)
  = function
    Complement a ->
      (let aa = card (_A1, _A2, _A3) a in
       let s = of_phantom (card_UNIV _A1) in
        (if less_nat zero_nat s then minus_nat s aa
          else (if finitea _A1.finite_UNIV_card_UNIV a then zero_nat
                 else failwith "card Complement: infinite"
                        (fun _ -> card (_A1, _A2, _A3) (Complement a)))))
    | Set_Monad xs ->
        (match ceq _A2
          with None ->
            failwith "card Set_Monad: ceq = None"
              (fun _ -> card (_A1, _A2, _A3) (Set_Monad xs))
          | Some eq -> size_list (list_remdups eq xs))
    | RBT_set rbt ->
        (match ccompare _A3
          with None ->
            failwith "card RBT_set: ccompare = None"
              (fun _ -> card (_A1, _A2, _A3) (RBT_set rbt))
          | Some _ -> size_list (keysa _A3 rbt))
    | DList_set dxs ->
        (match ceq _A2
          with None ->
            failwith "card DList_set: ceq = None"
              (fun _ -> card (_A1, _A2, _A3) (DList_set dxs))
          | Some _ -> length _A2 dxs);;

let rec is_UNIV (_A1, _A2, _A3)
  = function
    RBT_set rbt ->
      (match ccompare _A3.ccompare_cproper_interval
        with None ->
          failwith "is_UNIV RBT_set: ccompare = None"
            (fun _ -> is_UNIV (_A1, _A2, _A3) (RBT_set rbt))
        | Some _ ->
          of_phantom (finite_UNIV _A1.finite_UNIV_card_UNIV) &&
            exhaustive_fusion (cproper_interval _A3) rbt_keys_generator
              (init _A3.ccompare_cproper_interval rbt))
    | a -> (let aa = of_phantom (card_UNIV _A1) in
            let b = card (_A1, _A2, _A3.ccompare_cproper_interval) a in
             (if less_nat zero_nat aa then equal_nata aa b
               else (if less_nat zero_nat b then false
                      else failwith "is_UNIV called on infinite type and set"
                             (fun _ -> is_UNIV (_A1, _A2, _A3) a))));;

let rec is_emptya _A
  xa = (match impl_ofa _A xa with Empty -> true
         | Branch (_, _, _, _, _) -> false);;

let rec nulla _A xa = null (list_of_dlist _A xa);;

let rec is_empty (_A1, _A2, _A3)
  = function Complement a -> is_UNIV (_A1, _A2, _A3) a
    | RBT_set rbt ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "is_empty RBT_set: ccompare = None"
              (fun _ -> is_empty (_A1, _A2, _A3) (RBT_set rbt))
          | Some _ -> is_emptya _A3.ccompare_cproper_interval rbt)
    | DList_set dxs ->
        (match ceq _A2
          with None ->
            failwith "is_empty DList_set: ceq = None"
              (fun _ -> is_empty (_A1, _A2, _A3) (DList_set dxs))
          | Some _ -> nulla _A2 dxs)
    | Set_Monad xs -> null xs;;

let rec cproper_interval_seta (_A1, _A2, _A3, _A4)
  x0 x1 = match x0, x1 with
    Some (Complement (RBT_set rbt1)), Some (RBT_set rbt2) ->
      (match ccompare _A3.ccompare_cproper_interval
        with None ->
          failwith
            "cproper_interval (Complement RBT_set) RBT_set: ccompare = None"
            (fun _ ->
              cproper_interval_seta (_A1, _A2, _A3, _A4)
                (Some (Complement (RBT_set rbt1))) (Some (RBT_set rbt2)))
        | Some c ->
          finite (_A1.finite_UNIV_card_UNIV, _A2, _A3.ccompare_cproper_interval)
            (top_set (_A2, _A3.ccompare_cproper_interval, _A4)) &&
            proper_interval_Compl_set_aux_fusion (lt_of_comp c)
              (cproper_interval _A3) rbt_keys_generator rbt_keys_generator None
              (init _A3.ccompare_cproper_interval rbt1)
              (init _A3.ccompare_cproper_interval rbt2))
    | Some (RBT_set rbt1), Some (Complement (RBT_set rbt2)) ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith
              "cproper_interval RBT_set (Complement RBT_set): ccompare = None"
              (fun _ ->
                cproper_interval_seta (_A1, _A2, _A3, _A4) (Some (RBT_set rbt1))
                  (Some (Complement (RBT_set rbt2))))
          | Some c ->
            finite
              (_A1.finite_UNIV_card_UNIV, _A2, _A3.ccompare_cproper_interval)
              (top_set (_A2, _A3.ccompare_cproper_interval, _A4)) &&
              proper_interval_set_Compl_aux_fusion _A1 (lt_of_comp c)
                (cproper_interval _A3) rbt_keys_generator rbt_keys_generator
                None zero_nat (init _A3.ccompare_cproper_interval rbt1)
                (init _A3.ccompare_cproper_interval rbt2))
    | Some (RBT_set rbt1), Some (RBT_set rbt2) ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cproper_interval RBT_set RBT_set: ccompare = None"
              (fun _ ->
                cproper_interval_seta (_A1, _A2, _A3, _A4) (Some (RBT_set rbt1))
                  (Some (RBT_set rbt2)))
          | Some c ->
            finite
              (_A1.finite_UNIV_card_UNIV, _A2, _A3.ccompare_cproper_interval)
              (top_set (_A2, _A3.ccompare_cproper_interval, _A4)) &&
              proper_interval_set_aux_fusion (lt_of_comp c)
                (cproper_interval _A3) rbt_keys_generator rbt_keys_generator
                (init _A3.ccompare_cproper_interval rbt1)
                (init _A3.ccompare_cproper_interval rbt2))
    | Some (Complement a), Some (Complement b) ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cproper_interval Complement Complement: ccompare = None"
              (fun _ ->
                cproper_interval_seta (_A1, _A2, _A3, _A4) (Some (Complement a))
                  (Some (Complement b)))
          | Some _ ->
            cproper_interval_seta (_A1, _A2, _A3, _A4) (Some b) (Some a))
    | Some (Complement a), Some b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cproper_interval Complement1: ccompare = None"
              (fun _ ->
                cproper_interval_seta (_A1, _A2, _A3, _A4) (Some (Complement a))
                  (Some b))
          | Some c ->
            finite
              (_A1.finite_UNIV_card_UNIV, _A2, _A3.ccompare_cproper_interval)
              (top_set (_A2, _A3.ccompare_cproper_interval, _A4)) &&
              proper_interval_Compl_set_aux (lt_of_comp c)
                (cproper_interval _A3) None
                (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval) a)
                (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval) b))
    | Some a, Some (Complement b) ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cproper_interval Complement2: ccompare = None"
              (fun _ ->
                cproper_interval_seta (_A1, _A2, _A3, _A4) (Some a)
                  (Some (Complement b)))
          | Some c ->
            finite
              (_A1.finite_UNIV_card_UNIV, _A2, _A3.ccompare_cproper_interval)
              (top_set (_A2, _A3.ccompare_cproper_interval, _A4)) &&
              proper_interval_set_Compl_aux _A1 (lt_of_comp c)
                (cproper_interval _A3) None zero_nat
                (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval) a)
                (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval) b))
    | Some a, Some b ->
        (match ccompare _A3.ccompare_cproper_interval
          with None ->
            failwith "cproper_interval: ccompare = None"
              (fun _ ->
                cproper_interval_seta (_A1, _A2, _A3, _A4) (Some a) (Some b))
          | Some c ->
            finite
              (_A1.finite_UNIV_card_UNIV, _A2, _A3.ccompare_cproper_interval)
              (top_set (_A2, _A3.ccompare_cproper_interval, _A4)) &&
              proper_interval_set_aux (lt_of_comp c) (cproper_interval _A3)
                (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval) a)
                (csorted_list_of_set (_A2, _A3.ccompare_cproper_interval) b))
    | Some a, None -> not (is_UNIV (_A1, _A2, _A3) a)
    | None, Some b -> not (is_empty (_A1, _A2, _A3) b)
    | None, None -> true;;

let rec cproper_interval_set (_A1, _A2, _A3, _A4) =
  ({ccompare_cproper_interval =
      (ccompare_set (_A1.finite_UNIV_card_UNIV, _A2, _A3, _A4));
     cproper_interval = cproper_interval_seta (_A1, _A2, _A3, _A4)}
    : 'a set cproper_interval);;

let rec equal_lista _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_lista _A x22 y22
    | [], [] -> true;;

let rec equal_list _A = ({equal = equal_lista _A} : ('a list) equal);;

let rec equality_list
  eq_a x1 x2 = match eq_a, x1, x2 with
    eq_a, x :: xa, y :: ya -> eq_a x y && equality_list eq_a xa ya
    | eq_a, x :: xa, [] -> false
    | eq_a, [], y :: ya -> false
    | eq_a, [], [] -> true;;

let rec ceq_lista _A
  = (match ceq _A with None -> None | Some eq_a -> Some (equality_list eq_a));;

let rec ceq_list _A = ({ceq = ceq_lista _A} : ('a list) ceq);;

let set_impl_lista : (('a list), set_impla) phantom = Phantom Set_Choose;;

let set_impl_list = ({set_impl = set_impl_lista} : ('a list) set_impl);;

let finite_UNIV_lista : (('a list), bool) phantom = Phantom false;;

let card_UNIV_lista : (('a list), nat) phantom = Phantom zero_nat;;

let finite_UNIV_list =
  ({finite_UNIV = finite_UNIV_lista} : ('a list) finite_UNIV);;

let card_UNIV_list =
  ({finite_UNIV_card_UNIV = finite_UNIV_list; card_UNIVa = card_UNIV_lista} :
    ('a list) card_UNIV);;

let cEnum_list :
  (('a list) list *
    ((('a list -> bool) -> bool) * (('a list -> bool) -> bool))) option
  = None;;

let cenum_list = ({cEnum = cEnum_list} : ('a list) cenum);;

let rec comparator_list
  comp_a x1 x2 = match comp_a, x1, x2 with
    comp_a, x :: xa, y :: ya ->
      (match comp_a x y with Eqa -> comparator_list comp_a xa ya | Lt -> Lt
        | Gt -> Gt)
    | comp_a, x :: xa, [] -> Gt
    | comp_a, [], y :: ya -> Lt
    | comp_a, [], [] -> Eqa;;

let rec ccompare_lista _A
  = (match ccompare _A with None -> None
      | Some comp_a -> Some (comparator_list comp_a));;

let rec ccompare_list _A =
  ({ccompare = ccompare_lista _A} : ('a list) ccompare);;

let rec cproper_interval_lista _A xso yso = failwith "undefined";;

let rec cproper_interval_list _A =
  ({ccompare_cproper_interval = (ccompare_list _A);
     cproper_interval = cproper_interval_lista _A}
    : ('a list) cproper_interval);;

type 'a trm = Var of nat | Const of 'a;;

let rec equal_trm _A x0 x1 = match x0, x1 with Var x1, Const x2 -> false
                       | Const x2, Var x1 -> false
                       | Const x2, Const y2 -> eq _A x2 y2
                       | Var x1, Var y1 -> equal_nata x1 y1;;

let rec ceq_trma _A = Some (equal_trm _A);;

let rec ceq_trm _A = ({ceq = ceq_trma _A} : 'a trm ceq);;

let set_impl_trma : ('a trm, set_impla) phantom = Phantom Set_RBT;;

let set_impl_trm = ({set_impl = set_impl_trma} : 'a trm set_impl);;

let rec comparator_trm
  comp_a x1 x2 = match comp_a, x1, x2 with
    comp_a, Const x, Const ya -> comp_a x ya
    | comp_a, Const x, Var y -> Gt
    | comp_a, Var x, Const ya -> Lt
    | comp_a, Var x, Var y -> comparator_of (equal_nat, linorder_nat) x y;;

let rec ccompare_trma _A
  = (match ccompare _A with None -> None
      | Some comp_a -> Some (comparator_trm comp_a));;

let rec ccompare_trm _A = ({ccompare = ccompare_trma _A} : 'a trm ccompare);;

let rec equal_bool p pa = match p, pa with p, true -> p
                     | p, false -> not p
                     | true, p -> p
                     | false, p -> not p;;

type char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;;

let rec equal_chara
  (Chara (x1, x2, x3, x4, x5, x6, x7, x8))
    (Chara (y1, y2, y3, y4, y5, y6, y7, y8)) =
    equal_bool x1 y1 &&
      (equal_bool x2 y2 &&
        (equal_bool x3 y3 &&
          (equal_bool x4 y4 &&
            (equal_bool x5 y5 &&
              (equal_bool x6 y6 && (equal_bool x7 y7 && equal_bool x8 y8))))));;

let equal_char = ({equal = equal_chara} : char equal);;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

type 'a zero_neq_one =
  {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero};;

let rec of_bool _A = function true -> one _A.one_zero_neq_one
                     | false -> zero _A.zero_zero_neq_one;;

let one_integera : Z.t = (Z.of_int 1);;

let zero_integer = ({zero = Z.zero} : Z.t zero);;

let one_integer = ({one = one_integera} : Z.t one);;

let zero_neq_one_integer =
  ({one_zero_neq_one = one_integer; zero_zero_neq_one = zero_integer} :
    Z.t zero_neq_one);;

let rec integer_of_char
  (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
    Z.add (Z.mul
            (Z.add
              (Z.mul
                (Z.add
                  (Z.mul
                    (Z.add
                      (Z.mul
                        (Z.add
                          (Z.mul
                            (Z.add
                              (Z.mul
                                (Z.add
                                  (Z.mul (of_bool zero_neq_one_integer b7)
                                    (Z.of_int 2))
                                  (of_bool zero_neq_one_integer b6))
                                (Z.of_int 2))
                              (of_bool zero_neq_one_integer b5))
                            (Z.of_int 2))
                          (of_bool zero_neq_one_integer b4))
                        (Z.of_int 2))
                      (of_bool zero_neq_one_integer b3))
                    (Z.of_int 2))
                  (of_bool zero_neq_one_integer b2))
                (Z.of_int 2))
              (of_bool zero_neq_one_integer b1))
            (Z.of_int 2))
      (of_bool zero_neq_one_integer b0);;

let rec nat_of_char c = Nat (integer_of_char c);;

let rec less_eq_char c1 c2 = less_eq_nat (nat_of_char c1) (nat_of_char c2);;

let rec less_char c1 c2 = less_nat (nat_of_char c1) (nat_of_char c2);;

let ord_char = ({less_eq = less_eq_char; less = less_char} : char ord);;

let preorder_char = ({ord_preorder = ord_char} : char preorder);;

let order_char = ({preorder_order = preorder_char} : char order);;

let ceq_chara : (char -> char -> bool) option = Some equal_chara;;

let ceq_char = ({ceq = ceq_chara} : char ceq);;

let linorder_char = ({order_linorder = order_char} : char linorder);;

let rec compare_char x = comparator_of (equal_char, linorder_char) x;;

let ccompare_chara : (char -> char -> ordera) option = Some compare_char;;

let ccompare_char = ({ccompare = ccompare_chara} : char ccompare);;

let rec equal_option _A = ({equal = equal_optiona _A} : ('a option) equal);;

let rec equality_option
  eq_a x1 x2 = match eq_a, x1, x2 with eq_a, Some x, Some y -> eq_a x y
    | eq_a, Some x, None -> false
    | eq_a, None, Some y -> false
    | eq_a, None, None -> true;;

let rec ceq_optiona _A
  = (match ceq _A with None -> None
      | Some eq_a -> Some (equality_option eq_a));;

let rec ceq_option _A = ({ceq = ceq_optiona _A} : ('a option) ceq);;

let rec comparator_option
  comp_a x1 x2 = match comp_a, x1, x2 with comp_a, Some x, Some y -> comp_a x y
    | comp_a, Some x, None -> Gt
    | comp_a, None, Some y -> Lt
    | comp_a, None, None -> Eqa;;

let rec ccompare_optiona _A
  = (match ccompare _A with None -> None
      | Some comp_a -> Some (comparator_option comp_a));;

let rec ccompare_option _A =
  ({ccompare = ccompare_optiona _A} : ('a option) ccompare);;

type mregex = MWild | MEps | MTestPos of nat | MTestNeg of nat |
  MPlus of mregex * mregex | MTimes of mregex * mregex | MStar of mregex;;

let rec equal_mregexa
  x0 x1 = match x0, x1 with MTimes (x61, x62), MStar x7 -> false
    | MStar x7, MTimes (x61, x62) -> false
    | MPlus (x51, x52), MStar x7 -> false
    | MStar x7, MPlus (x51, x52) -> false
    | MPlus (x51, x52), MTimes (x61, x62) -> false
    | MTimes (x61, x62), MPlus (x51, x52) -> false
    | MTestNeg x4, MStar x7 -> false
    | MStar x7, MTestNeg x4 -> false
    | MTestNeg x4, MTimes (x61, x62) -> false
    | MTimes (x61, x62), MTestNeg x4 -> false
    | MTestNeg x4, MPlus (x51, x52) -> false
    | MPlus (x51, x52), MTestNeg x4 -> false
    | MTestPos x3, MStar x7 -> false
    | MStar x7, MTestPos x3 -> false
    | MTestPos x3, MTimes (x61, x62) -> false
    | MTimes (x61, x62), MTestPos x3 -> false
    | MTestPos x3, MPlus (x51, x52) -> false
    | MPlus (x51, x52), MTestPos x3 -> false
    | MTestPos x3, MTestNeg x4 -> false
    | MTestNeg x4, MTestPos x3 -> false
    | MEps, MStar x7 -> false
    | MStar x7, MEps -> false
    | MEps, MTimes (x61, x62) -> false
    | MTimes (x61, x62), MEps -> false
    | MEps, MPlus (x51, x52) -> false
    | MPlus (x51, x52), MEps -> false
    | MEps, MTestNeg x4 -> false
    | MTestNeg x4, MEps -> false
    | MEps, MTestPos x3 -> false
    | MTestPos x3, MEps -> false
    | MWild, MStar x7 -> false
    | MStar x7, MWild -> false
    | MWild, MTimes (x61, x62) -> false
    | MTimes (x61, x62), MWild -> false
    | MWild, MPlus (x51, x52) -> false
    | MPlus (x51, x52), MWild -> false
    | MWild, MTestNeg x4 -> false
    | MTestNeg x4, MWild -> false
    | MWild, MTestPos x3 -> false
    | MTestPos x3, MWild -> false
    | MWild, MEps -> false
    | MEps, MWild -> false
    | MStar x7, MStar y7 -> equal_mregexa x7 y7
    | MTimes (x61, x62), MTimes (y61, y62) ->
        equal_mregexa x61 y61 && equal_mregexa x62 y62
    | MPlus (x51, x52), MPlus (y51, y52) ->
        equal_mregexa x51 y51 && equal_mregexa x52 y52
    | MTestNeg x4, MTestNeg y4 -> equal_nata x4 y4
    | MTestPos x3, MTestPos y3 -> equal_nata x3 y3
    | MEps, MEps -> true
    | MWild, MWild -> true;;

let equal_mregex = ({equal = equal_mregexa} : mregex equal);;

let rec comparator_mregex
  x0 x1 = match x0, x1 with MStar x, MStar yf -> comparator_mregex x yf
    | MStar x, MTimes (yd, ye) -> Gt
    | MStar x, MPlus (yb, yc) -> Gt
    | MStar x, MTestNeg ya -> Gt
    | MStar x, MTestPos y -> Gt
    | MStar x, MEps -> Gt
    | MStar x, MWild -> Gt
    | MTimes (x, xa), MStar yf -> Lt
    | MTimes (x, xa), MTimes (yd, ye) ->
        (match comparator_mregex x yd with Eqa -> comparator_mregex xa ye
          | Lt -> Lt | Gt -> Gt)
    | MTimes (x, xa), MPlus (yb, yc) -> Gt
    | MTimes (x, xa), MTestNeg ya -> Gt
    | MTimes (x, xa), MTestPos y -> Gt
    | MTimes (x, xa), MEps -> Gt
    | MTimes (x, xa), MWild -> Gt
    | MPlus (x, xa), MStar yf -> Lt
    | MPlus (x, xa), MTimes (yd, ye) -> Lt
    | MPlus (x, xa), MPlus (yb, yc) ->
        (match comparator_mregex x yb with Eqa -> comparator_mregex xa yc
          | Lt -> Lt | Gt -> Gt)
    | MPlus (x, xa), MTestNeg ya -> Gt
    | MPlus (x, xa), MTestPos y -> Gt
    | MPlus (x, xa), MEps -> Gt
    | MPlus (x, xa), MWild -> Gt
    | MTestNeg x, MStar yf -> Lt
    | MTestNeg x, MTimes (yd, ye) -> Lt
    | MTestNeg x, MPlus (yb, yc) -> Lt
    | MTestNeg x, MTestNeg ya -> comparator_of (equal_nat, linorder_nat) x ya
    | MTestNeg x, MTestPos y -> Gt
    | MTestNeg x, MEps -> Gt
    | MTestNeg x, MWild -> Gt
    | MTestPos x, MStar yf -> Lt
    | MTestPos x, MTimes (yd, ye) -> Lt
    | MTestPos x, MPlus (yb, yc) -> Lt
    | MTestPos x, MTestNeg ya -> Lt
    | MTestPos x, MTestPos y -> comparator_of (equal_nat, linorder_nat) x y
    | MTestPos x, MEps -> Gt
    | MTestPos x, MWild -> Gt
    | MEps, MStar yf -> Lt
    | MEps, MTimes (yd, ye) -> Lt
    | MEps, MPlus (yb, yc) -> Lt
    | MEps, MTestNeg ya -> Lt
    | MEps, MTestPos y -> Lt
    | MEps, MEps -> Eqa
    | MEps, MWild -> Gt
    | MWild, MStar yf -> Lt
    | MWild, MTimes (yd, ye) -> Lt
    | MWild, MPlus (yb, yc) -> Lt
    | MWild, MTestNeg ya -> Lt
    | MWild, MTestPos y -> Lt
    | MWild, MEps -> Lt
    | MWild, MWild -> Eqa;;

let rec less_eq_mregex x = le_of_comp comparator_mregex x;;

let rec less_mregex x = lt_of_comp comparator_mregex x;;

let ord_mregex = ({less_eq = less_eq_mregex; less = less_mregex} : mregex ord);;

let preorder_mregex = ({ord_preorder = ord_mregex} : mregex preorder);;

let order_mregex = ({preorder_order = preorder_mregex} : mregex order);;

let ceq_mregexa : (mregex -> mregex -> bool) option = Some equal_mregexa;;

let ceq_mregex = ({ceq = ceq_mregexa} : mregex ceq);;

let set_impl_mregexa : (mregex, set_impla) phantom = Phantom Set_RBT;;

let set_impl_mregex = ({set_impl = set_impl_mregexa} : mregex set_impl);;

let linorder_mregex = ({order_linorder = order_mregex} : mregex linorder);;

let cEnum_mregex :
  (mregex list *
    (((mregex -> bool) -> bool) * ((mregex -> bool) -> bool))) option
  = None;;

let cenum_mregex = ({cEnum = cEnum_mregex} : mregex cenum);;

let ccompare_mregexa : (mregex -> mregex -> ordera) option
  = Some comparator_mregex;;

let ccompare_mregex = ({ccompare = ccompare_mregexa} : mregex ccompare);;

type enat = Enat of nat | Infinity_enat;;

let rec equal_enat x0 x1 = match x0, x1 with Enat nat, Infinity_enat -> false
                     | Infinity_enat, Enat nat -> false
                     | Enat nata, Enat nat -> equal_nata nata nat
                     | Infinity_enat, Infinity_enat -> true;;

let ceq_enata : (enat -> enat -> bool) option = Some equal_enat;;

let ceq_enat = ({ceq = ceq_enata} : enat ceq);;

let set_impl_enata : (enat, set_impla) phantom = Phantom Set_RBT;;

let set_impl_enat = ({set_impl = set_impl_enata} : enat set_impl);;

let rec less_enat x0 q = match x0, q with Infinity_enat, q -> false
                    | Enat m, Infinity_enat -> true
                    | Enat m, Enat n -> less_nat m n;;

let ccompare_enata : (enat -> enat -> ordera) option
  = Some (fun x y ->
           (if equal_enat x y then Eqa
             else (if less_enat x y then Lt else Gt)));;

let ccompare_enat = ({ccompare = ccompare_enata} : enat ccompare);;

let rec equality_prod eq_a eq_b (x, xa) (y, ya) = eq_a x y && eq_b xa ya;;

let rec ceq_proda _A _B
  = (match ceq _A with None -> None
      | Some eq_a ->
        (match ceq _B with None -> None
          | Some eq_b -> Some (equality_prod eq_a eq_b)));;

let rec ceq_prod _A _B = ({ceq = ceq_proda _A _B} : ('a * 'b) ceq);;

let rec set_impl_choose2
  x y = match x, y with Set_Monada, Set_Monada -> Set_Monada
    | Set_RBT, Set_RBT -> Set_RBT
    | Set_DList, Set_DList -> Set_DList
    | Set_Collect, Set_Collect -> Set_Collect
    | x, y -> Set_Choose;;

let rec set_impl_proda _A _B
  = Phantom
      (set_impl_choose2 (of_phantom (set_impl _A)) (of_phantom (set_impl _B)));;

let rec set_impl_prod _A _B =
  ({set_impl = set_impl_proda _A _B} : ('a * 'b) set_impl);;

let rec finite_UNIV_proda _A _B
  = Phantom (of_phantom (finite_UNIV _A) && of_phantom (finite_UNIV _B));;

let rec card_UNIV_proda _A _B
  = Phantom
      (times_nata (of_phantom (card_UNIVa _A)) (of_phantom (card_UNIVa _B)));;

let rec finite_UNIV_prod _A _B =
  ({finite_UNIV = finite_UNIV_proda _A _B} : ('a * 'b) finite_UNIV);;

let rec card_UNIV_prod _A _B =
  ({finite_UNIV_card_UNIV =
      (finite_UNIV_prod _A.finite_UNIV_card_UNIV _B.finite_UNIV_card_UNIV);
     card_UNIVa = card_UNIV_proda _A _B}
    : ('a * 'b) card_UNIV);;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec product x0 uu = match x0, uu with [], uu -> []
                  | x :: xs, ys -> map (fun a -> (x, a)) ys @ product xs ys;;

let rec cEnum_prod _A _B
  = (match cEnum _A with None -> None
      | Some (enum_a, (enum_all_a, enum_ex_a)) ->
        (match cEnum _B with None -> None
          | Some (enum_b, (enum_all_b, enum_ex_b)) ->
            Some (product enum_a enum_b,
                   ((fun p ->
                      enum_all_a (fun x -> enum_all_b (fun y -> p (x, y)))),
                     (fun p ->
                       enum_ex_a (fun x -> enum_ex_b (fun y -> p (x, y))))))));;

let rec cenum_prod _A _B = ({cEnum = cEnum_prod _A _B} : ('a * 'b) cenum);;

let rec comparator_prod
  comp_a comp_b (x, xa) (y, ya) =
    (match comp_a x y with Eqa -> comp_b xa ya | Lt -> Lt | Gt -> Gt);;

let rec ccompare_proda _A _B
  = (match ccompare _A with None -> None
      | Some comp_a ->
        (match ccompare _B with None -> None
          | Some comp_b -> Some (comparator_prod comp_a comp_b)));;

let rec ccompare_prod _A _B =
  ({ccompare = ccompare_proda _A _B} : ('a * 'b) ccompare);;

let rec cproper_interval_proda _A _B
  x0 x1 = match x0, x1 with None, None -> true
    | None, Some (y1, y2) ->
        cproper_interval _A None (Some y1) || cproper_interval _B None (Some y2)
    | Some (x1, x2), None ->
        cproper_interval _A (Some x1) None || cproper_interval _B (Some x2) None
    | Some (x1, x2), Some (y1, y2) ->
        cproper_interval _A (Some x1) (Some y1) ||
          (lt_of_comp (the (ccompare _A.ccompare_cproper_interval)) x1 y1 &&
             (cproper_interval _B (Some x2) None ||
               cproper_interval _B None (Some y2)) ||
            not (lt_of_comp (the (ccompare _A.ccompare_cproper_interval)) y1
                  x1) &&
              cproper_interval _B (Some x2) (Some y2));;

let rec cproper_interval_prod _A _B =
  ({ccompare_cproper_interval =
      (ccompare_prod _A.ccompare_cproper_interval _B.ccompare_cproper_interval);
     cproper_interval = cproper_interval_proda _A _B}
    : ('a * 'b) cproper_interval);;

type ('b, 'a) alist = Alist of ('b * 'a) list;;

type i = Abs_I of (nat * enat);;

type 'a regex = Wild | Test of 'a formula | Plus of 'a regex * 'a regex |
  Times of 'a regex * 'a regex | Star of 'a regex
and 'a formula = Pred of char list * 'a trm list | Eq of 'a trm * 'a trm |
  Neg of 'a formula | Or of 'a formula * 'a formula | Ands of 'a formula list |
  Exists of 'a formula |
  Agg of nat * (('a * enat) set -> 'a) * nat * ('a list -> 'a) * 'a formula |
  Prev of i * 'a formula | Next of i * 'a formula |
  Since of 'a formula * i * 'a formula | Until of 'a formula * i * 'a formula |
  MatchF of i * 'a regex | MatchP of i * 'a regex;;

type safety = Safe | Unsafe;;

type ('a, 'b) mapping = Assoc_List_Mapping of ('a, 'b) alist |
  RBT_Mapping of ('a, 'b) mapping_rbt | Mapping of ('a -> 'b option);;

type modality = Past | Future;;

type 'a mformula = MRel of (('a option) list) set |
  MPred of char list * 'a trm list |
  MAnd of
    'a mformula * bool * 'a mformula *
      ((('a option) list) set list * (('a option) list) set list)
  | MAnds of
      nat set list * nat set list * 'a mformula list *
        ((('a option) list) set list) list
  | MOr of
      'a mformula * 'a mformula *
        ((('a option) list) set list * (('a option) list) set list)
  | MNeg of 'a mformula | MExists of 'a mformula |
  MAgg of
    bool * nat * (('a * enat) set -> 'a) * nat * ('a list -> 'a) * 'a mformula
  | MPrev of i * 'a mformula * bool * (('a option) list) set list * nat list |
  MNext of i * 'a mformula * bool * nat list |
  MSince of
    bool * 'a mformula * i * 'a mformula *
      ((('a option) list) set list * (('a option) list) set list) * nat list *
      (nat * (('a option) list) set) list
  | MUntil of
      bool * 'a mformula * i * 'a mformula *
        ((('a option) list) set list * (('a option) list) set list) * nat list *
        (nat * ((('a option) list) set * (('a option) list) set)) list
  | MMatchP of
      i * mregex * mregex list * 'a mformula list *
        ((('a option) list) set list) list * nat list *
        (nat * (mregex, (('a option) list) set) mapping) list
  | MMatchF of
      i * mregex * mregex list * 'a mformula list *
        ((('a option) list) set list) list * nat list *
        (nat * ((('a option) list) set list * (('a option) list) set)) list;;

type ('b, 'a) comp_fun_idem = Abs_comp_fun_idem of ('b -> 'a -> 'a);;

type 'a semilattice_set = Abs_semilattice_set of ('a -> 'a -> 'a);;

type ('a, 'b) mstate_ext = Mstate_ext of nat * 'a mformula * nat * 'b;;

let rec list_ex p x1 = match p, x1 with p, [] -> false
                  | p, x :: xs -> p x || list_ex p xs;;

let rec dlist_ex _A x xc = list_ex x (list_of_dlist _A xc);;

let rec rBT_Impl_rbt_ex
  p x1 = match p, x1 with
    p, Branch (c, l, k, v, r) ->
      p k v || (rBT_Impl_rbt_ex p l || rBT_Impl_rbt_ex p r)
    | p, Empty -> false;;

let rec ex _A xb xc = rBT_Impl_rbt_ex xb (impl_ofa _A xc);;

let rec bex (_A1, _A2)
  x0 p = match x0, p with
    RBT_set rbt, p ->
      (match ccompare _A2
        with None ->
          failwith "Bex RBT_set: ccompare = None"
            (fun _ -> bex (_A1, _A2) (RBT_set rbt) p)
        | Some _ -> ex _A2 (fun k _ -> p k) rbt)
    | DList_set dxs, p ->
        (match ceq _A1
          with None ->
            failwith "Bex DList_set: ceq = None"
              (fun _ -> bex (_A1, _A2) (DList_set dxs) p)
          | Some _ -> dlist_ex _A1 p dxs)
    | Set_Monad xs, p -> list_ex p xs;;

let rec nth
  (x :: xs) n =
    (if equal_nata n zero_nat then x else nth xs (minus_nat n one_nata));;

let rec upt i j = (if less_nat i j then i :: upt (suc i) j else []);;

let rec zip xs ys = match xs, ys with x :: xs, y :: ys -> (x, y) :: zip xs ys
              | xs, [] -> []
              | [], ys -> [];;

let rec rBT_Impl_rbt_all
  p x1 = match p, x1 with
    p, Branch (c, l, k, v, r) ->
      p k v && (rBT_Impl_rbt_all p l && rBT_Impl_rbt_all p r)
    | p, Empty -> true;;

let rec all _A xb xc = rBT_Impl_rbt_all xb (impl_ofa _A xc);;

let rec ball (_A1, _A2)
  x0 p = match x0, p with
    RBT_set rbt, p ->
      (match ccompare _A2
        with None ->
          failwith "Ball RBT_set: ccompare = None"
            (fun _ -> ball (_A1, _A2) (RBT_set rbt) p)
        | Some _ -> all _A2 (fun k _ -> p k) rbt)
    | DList_set dxs, p ->
        (match ceq _A1
          with None ->
            failwith "Ball DList_set: ceq = None"
              (fun _ -> ball (_A1, _A2) (DList_set dxs) p)
          | Some _ -> dlist_all _A1 p dxs)
    | Set_Monad xs, p -> list_all p xs;;

let rec foldb _A x xc = folda (fun a _ -> x a) (impl_ofa _A xc);;

let rec bind (_A1, _A2) (_B1, _B2, _B3)
  x0 f = match x0, f with
    RBT_set rbt, f ->
      (match ccompare _A2
        with None ->
          failwith "bind RBT_set: ccompare = None"
            (fun _ -> bind (_A1, _A2) (_B1, _B2, _B3) (RBT_set rbt) f)
        | Some _ ->
          foldb _A2 (comp (sup_seta (_B1, _B2)) f) rbt
            (bot_set (_B1, _B2, _B3)))
    | DList_set dxs, f ->
        (match ceq _A1
          with None ->
            failwith "bind DList_set: ceq = None"
              (fun _ -> bind (_A1, _A2) (_B1, _B2, _B3) (DList_set dxs) f)
          | Some _ ->
            foldc _A1 (comp (sup_seta (_B1, _B2)) f) dxs
              (bot_set (_B1, _B2, _B3)))
    | Set_Monad xs, f -> fold (comp (sup_seta (_B1, _B2)) f) xs (Set_Monad []);;

let rec drop
  n x1 = match n, x1 with n, [] -> []
    | n, x :: xs ->
        (if equal_nata n zero_nat then x :: xs
          else drop (minus_nat n one_nata) xs);;

let rec maps f x1 = match f, x1 with f, [] -> []
               | f, x :: xs -> f x @ maps f xs;;

let rec fun_upda equal f aa b a = (if equal aa a then b else f a);;

let rec balance_right
  a k x xa3 = match a, k, x, xa3 with
    a, k, x, Branch (R, b, s, y, c) ->
      Branch (R, a, k, x, Branch (B, b, s, y, c))
    | Branch (B, a, k, x, b), s, y, Empty ->
        balance (Branch (R, a, k, x, b)) s y Empty
    | Branch (B, a, k, x, b), s, y, Branch (B, va, vb, vc, vd) ->
        balance (Branch (R, a, k, x, b)) s y (Branch (B, va, vb, vc, vd))
    | Branch (R, a, k, x, Branch (B, b, s, y, c)), t, z, Empty ->
        Branch (R, balance (paint R a) k x b, s, y, Branch (B, c, t, z, Empty))
    | Branch (R, a, k, x, Branch (B, b, s, y, c)), t, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, balance (paint R a) k x b, s, y,
               Branch (B, c, t, z, Branch (B, va, vb, vc, vd)))
    | Empty, k, x, Empty -> Empty
    | Branch (R, va, vb, vc, Empty), k, x, Empty -> Empty
    | Branch (R, va, vb, vc, Branch (R, ve, vf, vg, vh)), k, x, Empty -> Empty
    | Empty, k, x, Branch (B, va, vb, vc, vd) -> Empty
    | Branch (R, ve, vf, vg, Empty), k, x, Branch (B, va, vb, vc, vd) -> Empty
    | Branch (R, ve, vf, vg, Branch (R, vi, vj, vk, vl)), k, x,
        Branch (B, va, vb, vc, vd)
        -> Empty;;

let rec balance_left
  x0 s y c = match x0, s, y, c with
    Branch (R, a, k, x, b), s, y, c ->
      Branch (R, Branch (B, a, k, x, b), s, y, c)
    | Empty, k, x, Branch (B, a, s, y, b) ->
        balance Empty k x (Branch (R, a, s, y, b))
    | Branch (B, va, vb, vc, vd), k, x, Branch (B, a, s, y, b) ->
        balance (Branch (B, va, vb, vc, vd)) k x (Branch (R, a, s, y, b))
    | Empty, k, x, Branch (R, Branch (B, a, s, y, b), t, z, c) ->
        Branch (R, Branch (B, Empty, k, x, a), s, y, balance b t z (paint R c))
    | Branch (B, va, vb, vc, vd), k, x,
        Branch (R, Branch (B, a, s, y, b), t, z, c)
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), k, x, a), s, y,
               balance b t z (paint R c))
    | Empty, k, x, Empty -> Empty
    | Empty, k, x, Branch (R, Empty, vb, vc, vd) -> Empty
    | Empty, k, x, Branch (R, Branch (R, ve, vf, vg, vh), vb, vc, vd) -> Empty
    | Branch (B, va, vb, vc, vd), k, x, Empty -> Empty
    | Branch (B, va, vb, vc, vd), k, x, Branch (R, Empty, vf, vg, vh) -> Empty
    | Branch (B, va, vb, vc, vd), k, x,
        Branch (R, Branch (R, vi, vj, vk, vl), vf, vg, vh)
        -> Empty;;

let rec combine
  xa0 x = match xa0, x with Empty, x -> x
    | Branch (v, va, vb, vc, vd), Empty -> Branch (v, va, vb, vc, vd)
    | Branch (R, a, k, x, b), Branch (R, c, s, y, d) ->
        (match combine b c
          with Empty -> Branch (R, a, k, x, Branch (R, Empty, s, y, d))
          | Branch (R, b2, t, z, c2) ->
            Branch (R, Branch (R, a, k, x, b2), t, z, Branch (R, c2, s, y, d))
          | Branch (B, b2, t, z, c2) ->
            Branch (R, a, k, x, Branch (R, Branch (B, b2, t, z, c2), s, y, d)))
    | Branch (B, a, k, x, b), Branch (B, c, s, y, d) ->
        (match combine b c
          with Empty -> balance_left a k x (Branch (B, Empty, s, y, d))
          | Branch (R, b2, t, z, c2) ->
            Branch (R, Branch (B, a, k, x, b2), t, z, Branch (B, c2, s, y, d))
          | Branch (B, b2, t, z, c2) ->
            balance_left a k x (Branch (B, Branch (B, b2, t, z, c2), s, y, d)))
    | Branch (B, va, vb, vc, vd), Branch (R, b, k, x, c) ->
        Branch (R, combine (Branch (B, va, vb, vc, vd)) b, k, x, c)
    | Branch (R, a, k, x, b), Branch (B, va, vb, vc, vd) ->
        Branch (R, a, k, x, combine b (Branch (B, va, vb, vc, vd)));;

let rec rbt_comp_del
  c x xa2 = match c, x, xa2 with c, x, Empty -> Empty
    | c, x, Branch (uu, a, y, s, b) ->
        (match c x y with Eqa -> combine a b
          | Lt -> rbt_comp_del_from_left c x a y s b
          | Gt -> rbt_comp_del_from_right c x a y s b)
and rbt_comp_del_from_left
  c x xa2 y s b = match c, x, xa2, y, s, b with
    c, x, Branch (B, lt, z, v, rt), y, s, b ->
      balance_left (rbt_comp_del c x (Branch (B, lt, z, v, rt))) y s b
    | c, x, Empty, y, s, b -> Branch (R, rbt_comp_del c x Empty, y, s, b)
    | c, x, Branch (R, va, vb, vc, vd), y, s, b ->
        Branch (R, rbt_comp_del c x (Branch (R, va, vb, vc, vd)), y, s, b)
and rbt_comp_del_from_right
  c x a y s xa5 = match c, x, a, y, s, xa5 with
    c, x, a, y, s, Branch (B, lt, z, v, rt) ->
      balance_right a y s (rbt_comp_del c x (Branch (B, lt, z, v, rt)))
    | c, x, a, y, s, Empty -> Branch (R, a, y, s, rbt_comp_del c x Empty)
    | c, x, a, y, s, Branch (R, va, vb, vc, vd) ->
        Branch (R, a, y, s, rbt_comp_del c x (Branch (R, va, vb, vc, vd)));;

let rec rbt_comp_delete c k t = paint B (rbt_comp_del c k t);;

let rec delete _A
  xb xc =
    Mapping_RBT (rbt_comp_delete (the (ccompare _A)) xb (impl_ofa _A xc));;

let rec list_remove1
  equal x xa2 = match equal, x, xa2 with
    equal, x, y :: xs ->
      (if equal x y then xs else y :: list_remove1 equal x xs)
    | equal, x, [] -> [];;

let rec removea _A
  xb xc = Abs_dlist (list_remove1 (the (ceq _A)) xb (list_of_dlist _A xc));;

let rec insert (_A1, _A2)
  xa x1 = match xa, x1 with
    xa, Complement x -> Complement (remove (_A1, _A2) xa x)
    | x, RBT_set rbt ->
        (match ccompare _A2
          with None ->
            failwith "insert RBT_set: ccompare = None"
              (fun _ -> insert (_A1, _A2) x (RBT_set rbt))
          | Some _ -> RBT_set (insertb _A2 x () rbt))
    | x, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "insert DList_set: ceq = None"
              (fun _ -> insert (_A1, _A2) x (DList_set dxs))
          | Some _ -> DList_set (inserta _A1 x dxs))
    | x, Set_Monad xs -> Set_Monad (x :: xs)
    | x, Collect_set a ->
        (match ceq _A1
          with None ->
            failwith "insert Collect_set: ceq = None"
              (fun _ -> insert (_A1, _A2) x (Collect_set a))
          | Some eq -> Collect_set (fun_upda eq a x true))
and remove (_A1, _A2)
  x xa1 = match x, xa1 with
    x, Complement a -> Complement (insert (_A1, _A2) x a)
    | x, RBT_set rbt ->
        (match ccompare _A2
          with None ->
            failwith "remove RBT_set: ccompare = None"
              (fun _ -> remove (_A1, _A2) x (RBT_set rbt))
          | Some _ -> RBT_set (delete _A2 x rbt))
    | x, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "remove DList_set: ceq = None"
              (fun _ -> remove (_A1, _A2) x (DList_set dxs))
          | Some _ -> DList_set (removea _A1 x dxs))
    | x, Collect_set a ->
        (match ceq _A1
          with None ->
            failwith "remove Collect: ceq = None"
              (fun _ -> remove (_A1, _A2) x (Collect_set a))
          | Some eq -> Collect_set (fun_upda eq a x false));;

let rec image (_A1, _A2) (_B1, _B2, _B3)
  h x1 = match h, x1 with
    h, RBT_set rbt ->
      (match ccompare _A2
        with None ->
          failwith "image RBT_set: ccompare = None"
            (fun _ -> image (_A1, _A2) (_B1, _B2, _B3) h (RBT_set rbt))
        | Some _ ->
          foldb _A2 (comp (insert (_B1, _B2)) h) rbt (bot_set (_B1, _B2, _B3)))
    | g, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "image DList_set: ceq = None"
              (fun _ -> image (_A1, _A2) (_B1, _B2, _B3) g (DList_set dxs))
          | Some _ ->
            foldc _A1 (comp (insert (_B1, _B2)) g) dxs
              (bot_set (_B1, _B2, _B3)))
    | f, Complement (Complement b) -> image (_A1, _A2) (_B1, _B2, _B3) f b
    | f, Collect_set a ->
        failwith "image Collect_set"
          (fun _ -> image (_A1, _A2) (_B1, _B2, _B3) f (Collect_set a))
    | f, Set_Monad xs -> Set_Monad (map f xs);;

let rec foldl f a x2 = match f, a, x2 with f, a, [] -> a
                | f, a, x :: xs -> foldl f (f a x) xs;;

let rec foldr f x1 = match f, x1 with f, [] -> id
                | f, x :: xs -> comp (f x) (foldr f xs);;

let rec map_of _A
  x0 k = match x0, k with
    (l, v) :: ps, k -> (if eq _A l k then Some v else map_of _A ps k)
    | [], k -> None;;

let rec filter (_A1, _A2) p a = inf_seta (_A1, _A2) a (Collect_set p);;

let rec comp_fun_idem_apply (Abs_comp_fun_idem x) = x;;

let rec set_fold_cfi (_A1, _A2)
  f b x2 = match f, b, x2 with
    f, b, RBT_set rbt ->
      (match ccompare _A2
        with None ->
          failwith "set_fold_cfi RBT_set: ccompare = None"
            (fun _ -> set_fold_cfi (_A1, _A2) f b (RBT_set rbt))
        | Some _ -> foldb _A2 (comp_fun_idem_apply f) rbt b)
    | f, b, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "set_fold_cfi DList_set: ceq = None"
              (fun _ -> set_fold_cfi (_A1, _A2) f b (DList_set dxs))
          | Some _ -> foldc _A1 (comp_fun_idem_apply f) dxs b)
    | f, b, Set_Monad xs -> fold (comp_fun_idem_apply f) xs b
    | f, b, Collect_set p ->
        failwith "set_fold_cfi not supported on Collect_set"
          (fun _ -> set_fold_cfi (_A1, _A2) f b (Collect_set p))
    | f, b, Complement a ->
        failwith "set_fold_cfi not supported on Complement"
          (fun _ -> set_fold_cfi (_A1, _A2) f b (Complement a));;

let rec sup_cfi _A
  = Abs_comp_fun_idem (sup _A.semilattice_sup_lattice.sup_semilattice_sup);;

let rec sup_setb (_A1, _A2, _A3, _A4, _A5)
  a = (if finite
            ((finite_UNIV_set _A1),
              (ceq_set (_A2, _A3, _A4.ccompare_cproper_interval)),
              (ccompare_set (_A1, _A3, _A4, _A5)))
            a
        then set_fold_cfi
               ((ceq_set (_A2, _A3, _A4.ccompare_cproper_interval)),
                 (ccompare_set (_A1, _A3, _A4, _A5)))
               (sup_cfi (lattice_set (_A2, _A3, _A4.ccompare_cproper_interval)))
               (bot_set (_A3, _A4.ccompare_cproper_interval, _A5)) a
        else failwith "Sup: infinite"
               (fun _ -> sup_setb (_A1, _A2, _A3, _A4, _A5) a));;

let rec set_option (_A1, _A2, _A3)
  = function None -> bot_set (_A1, _A2, _A3)
    | Some x2 -> insert (_A1, _A2) x2 (bot_set (_A1, _A2, _A3));;

let rec join1 _A
  = function ([], []) -> Some []
    | (None :: xs, None :: ys) ->
        map_option (fun a -> None :: a) (join1 _A (xs, ys))
    | (Some x :: xs, None :: ys) ->
        map_option (fun a -> Some x :: a) (join1 _A (xs, ys))
    | (None :: xs, Some y :: ys) ->
        map_option (fun a -> Some y :: a) (join1 _A (xs, ys))
    | (Some x :: xs, Some y :: ys) ->
        (if eq _A x y then map_option (fun a -> Some x :: a) (join1 _A (xs, ys))
          else None)
    | (Some v :: vc, []) -> None
    | (vb :: vc, []) -> None
    | ([], vb :: vc) -> None;;

let rec join (_A1, _A2, _A3)
  a x1 b = match a, x1, b with
    a, false, b ->
      filter
        ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
        (fun aa ->
          ball ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2)))
            b (fun ba ->
                not (equal_optiona (equal_list (equal_option _A3))
                      (join1 _A3 (aa, ba)) (Some aa))))
        a
    | a, true, b ->
        sup_setb
          (finite_UNIV_list, cenum_list, (ceq_list (ceq_option _A1)),
            (cproper_interval_list (ccompare_option _A2)), set_impl_list)
          (image
            ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
            ((ceq_set
               (cenum_list, (ceq_list (ceq_option _A1)),
                 (cproper_interval_list
                   (ccompare_option _A2)).ccompare_cproper_interval)),
              (ccompare_set
                (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                  (cproper_interval_list (ccompare_option _A2)),
                  set_impl_list)),
              set_impl_set)
            (fun aa ->
              sup_setb
                (finite_UNIV_list, cenum_list, (ceq_list (ceq_option _A1)),
                  (cproper_interval_list (ccompare_option _A2)), set_impl_list)
                (image
                  ((ceq_list (ceq_option _A1)),
                    (ccompare_list (ccompare_option _A2)))
                  ((ceq_set
                     (cenum_list, (ceq_list (ceq_option _A1)),
                       (cproper_interval_list
                         (ccompare_option _A2)).ccompare_cproper_interval)),
                    (ccompare_set
                      (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                        (cproper_interval_list (ccompare_option _A2)),
                        set_impl_list)),
                    set_impl_set)
                  (fun ba ->
                    set_option
                      ((ceq_list (ceq_option _A1)),
                        (ccompare_list (ccompare_option _A2)), set_impl_list)
                      (join1 _A3 (aa, ba)))
                  b))
            a);;

let rec fvi_trm
  b x1 = match b, x1 with
    b, Var x ->
      (if less_eq_nat b x
        then insert (ceq_nat, ccompare_nat) (minus_nat x b)
               (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata))
        else set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata))
    | b, Const uu ->
        set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata);;

let rec set_aux (_A1, _A2)
  = function Set_Monada -> (fun a -> Set_Monad a)
    | Set_Choose ->
        (match ccompare _A2
          with None ->
            (match ceq _A1 with None -> (fun a -> Set_Monad a)
              | Some _ ->
                foldl (fun s x -> insert (_A1, _A2) x s)
                  (DList_set (empty _A1)))
          | Some _ ->
            foldl (fun s x -> insert (_A1, _A2) x s) (RBT_set (emptya _A2)))
    | impl ->
        foldl (fun s x -> insert (_A1, _A2) x s) (set_empty (_A1, _A2) impl);;

let rec set (_A1, _A2, _A3)
  xs = set_aux (_A1, _A2) (of_phantom (set_impl _A3)) xs;;

let rec fvi (_A1, _A2)
  b x1 = match b, x1 with
    b, Pred (r, ts) ->
      sup_setb
        (finite_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
          set_impl_nat)
        (image ((ceq_trm _A2), (ccompare_trm _A1))
          ((ceq_set
             (cenum_nat, ceq_nat,
               cproper_interval_nat.ccompare_cproper_interval)),
            (ccompare_set
              (finite_UNIV_nat, ceq_nat, cproper_interval_nat, set_impl_nat)),
            set_impl_set)
          (fvi_trm b)
          (set ((ceq_trm _A2), (ccompare_trm _A1), set_impl_trm) ts))
    | b, Eq (t1, t2) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi_trm b t1) (fvi_trm b t2)
    | b, Neg phi -> fvi (_A1, _A2) b phi
    | b, Or (phi, psi) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi (_A1, _A2) b phi)
          (fvi (_A1, _A2) b psi)
    | b, Ands phi_s ->
        (let xs = map (fvi (_A1, _A2) b) phi_s in
          sup_setb
            (finite_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
              set_impl_nat)
            (image
              ((ceq_set
                 (cenum_nat, ceq_nat,
                   cproper_interval_nat.ccompare_cproper_interval)),
                (ccompare_set
                  (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                    set_impl_nat)))
              ((ceq_set
                 (cenum_nat, ceq_nat,
                   cproper_interval_nat.ccompare_cproper_interval)),
                (ccompare_set
                  (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                    set_impl_nat)),
                set_impl_set)
              (fun x -> x)
              (set ((ceq_set
                      (cenum_nat, ceq_nat,
                        cproper_interval_nat.ccompare_cproper_interval)),
                     (ccompare_set
                       (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                         set_impl_nat)),
                     set_impl_set)
                xs)))
    | b, Exists phi -> fvi (_A1, _A2) (suc b) phi
    | ba, Agg (y, omega, b, f, phi) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi (_A1, _A2) (plus_nat ba b) phi)
          (if less_eq_nat ba y
            then insert (ceq_nat, ccompare_nat) (minus_nat y ba)
                   (set_empty (ceq_nat, ccompare_nat)
                     (of_phantom set_impl_nata))
            else set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata))
    | b, Prev (i, phi) -> fvi (_A1, _A2) b phi
    | b, Next (i, phi) -> fvi (_A1, _A2) b phi
    | b, Since (phi, i, psi) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi (_A1, _A2) b phi)
          (fvi (_A1, _A2) b psi)
    | b, Until (phi, i, psi) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi (_A1, _A2) b phi)
          (fvi (_A1, _A2) b psi)
    | b, MatchF (i, r) -> fvi_regex (_A1, _A2) b r
    | b, MatchP (i, r) -> fvi_regex (_A1, _A2) b r
and fvi_regex (_A1, _A2)
  b x1 = match b, x1 with
    b, Wild -> set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)
    | b, Test phi -> fvi (_A1, _A2) b phi
    | b, Plus (r, s) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi_regex (_A1, _A2) b r)
          (fvi_regex (_A1, _A2) b s)
    | b, Times (r, s) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi_regex (_A1, _A2) b r)
          (fvi_regex (_A1, _A2) b s)
    | b, Star r -> fvi_regex (_A1, _A2) b r;;

let rec semilattice_set_apply (Abs_semilattice_set x) = x;;

let rec rBT_Impl_fold1
  f x1 = match f, x1 with
    f, Branch (ca, Branch (c, l, ka, va, ra), k, v, r) ->
      folda (fun kb _ -> f kb) r
        (f k (rBT_Impl_fold1 f (Branch (c, l, ka, va, ra))))
    | f, Branch (c, Empty, k, v, r) -> folda (fun ka _ -> f ka) r k
    | f, Empty -> failwith "undefined";;

let rec fold1 _A x xc = rBT_Impl_fold1 x (impl_ofa _A xc);;

let rec tla = function [] -> []
              | x21 :: x22 -> x22;;

let rec tl _A xa = Abs_dlist (tla (list_of_dlist _A xa));;

let rec hda (x21 :: x22) = x21;;

let rec hd _A xa = hda (list_of_dlist _A xa);;

let rec set_fold1 (_A1, _A2, _A3)
  f x1 = match f, x1 with
    f, RBT_set rbt ->
      (match ccompare _A2
        with None ->
          failwith "set_fold1 RBT_set: ccompare = None"
            (fun _ -> set_fold1 (_A1, _A2, _A3) f (RBT_set rbt))
        | Some _ ->
          (if is_emptya _A2 rbt
            then failwith "set_fold1 RBT_set: empty set"
                   (fun _ -> set_fold1 (_A1, _A2, _A3) f (RBT_set rbt))
            else fold1 _A2 (semilattice_set_apply f) rbt))
    | f, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "set_fold1 DList_set: ceq = None"
              (fun _ -> set_fold1 (_A1, _A2, _A3) f (DList_set dxs))
          | Some _ ->
            (if nulla _A1 dxs
              then failwith "set_fold1 DList_set: empty set"
                     (fun _ -> set_fold1 (_A1, _A2, _A3) f (DList_set dxs))
              else foldc _A1 (semilattice_set_apply f) (tl _A1 dxs)
                     (hd _A1 dxs)))
    | f, Set_Monad (x :: xs) -> fold (semilattice_set_apply f) xs x
    | f, Collect_set p ->
        failwith "set_fold1: Collect_set"
          (fun _ -> set_fold1 (_A1, _A2, _A3) f (Collect_set p))
    | f, Complement a ->
        failwith "set_fold1: Complement"
          (fun _ -> set_fold1 (_A1, _A2, _A3) f (Complement a));;

let rec max_sls _A
  = Abs_semilattice_set (max _A.order_linorder.preorder_order.ord_preorder);;

let rec maxa (_A1, _A2, _A3, _A4)
  a = set_fold1 (_A1, _A2, _A3) (max_sls _A4) a;;

let rec nfv (_A1, _A2)
  phi = maxa (ceq_nat, ccompare_nat, lattice_nat, linorder_nat)
          (insert (ceq_nat, ccompare_nat) zero_nat
            (image (ceq_nat, ccompare_nat) (ceq_nat, ccompare_nat, set_impl_nat)
              suc (fvi (_A1, _A2) zero_nat phi)));;

let rec fun_upd _A f a b = (fun x -> (if eq _A x a then b else f x));;

let rec membera _A x0 y = match x0, y with [], y -> false
                     | x :: xs, y -> eq _A x y || membera _A xs y;;

let rec mTimesR
  r s = image (ceq_mregex, ccompare_mregex)
          (ceq_mregex, ccompare_mregex, set_impl_mregex)
          (fun ra -> MTimes (ra, s)) r;;

let rec lpd
  = function
    MWild ->
      insert (ceq_mregex, ccompare_mregex) MEps
        (set_empty (ceq_mregex, ccompare_mregex) (of_phantom set_impl_mregexa))
    | MEps ->
        set_empty (ceq_mregex, ccompare_mregex) (of_phantom set_impl_mregexa)
    | MTestPos phi ->
        set_empty (ceq_mregex, ccompare_mregex) (of_phantom set_impl_mregexa)
    | MTestNeg phi ->
        set_empty (ceq_mregex, ccompare_mregex) (of_phantom set_impl_mregexa)
    | MPlus (r, s) -> sup_seta (ceq_mregex, ccompare_mregex) (lpd r) (lpd s)
    | MTimes (r, s) ->
        sup_seta (ceq_mregex, ccompare_mregex) (mTimesR (lpd r) s) (lpd s)
    | MStar r -> mTimesR (lpd r) (MStar r);;

let rec mTimesL
  r s = image (ceq_mregex, ccompare_mregex)
          (ceq_mregex, ccompare_mregex, set_impl_mregex)
          (fun a -> MTimes (r, a)) s;;

let rec rpd
  = function
    MWild ->
      insert (ceq_mregex, ccompare_mregex) MEps
        (set_empty (ceq_mregex, ccompare_mregex) (of_phantom set_impl_mregexa))
    | MEps ->
        set_empty (ceq_mregex, ccompare_mregex) (of_phantom set_impl_mregexa)
    | MTestPos phi ->
        set_empty (ceq_mregex, ccompare_mregex) (of_phantom set_impl_mregexa)
    | MTestNeg phi ->
        set_empty (ceq_mregex, ccompare_mregex) (of_phantom set_impl_mregexa)
    | MPlus (r, s) -> sup_seta (ceq_mregex, ccompare_mregex) (rpd r) (rpd s)
    | MTimes (r, s) ->
        sup_seta (ceq_mregex, ccompare_mregex) (mTimesL r (rpd s)) (rpd r)
    | MStar r -> mTimesL (MStar r) (rpd r);;

let rec remdups _A
  = function [] -> []
    | x :: xs ->
        (if membera _A xs x then remdups _A xs else x :: remdups _A xs);;

let rec lPDs_aux
  s = (let sa =
         sup_seta (ceq_mregex, ccompare_mregex) s
           (bind (ceq_mregex, ccompare_mregex)
             (ceq_mregex, ccompare_mregex, set_impl_mregex) s lpd)
         in
        (if less_eq_set (cenum_mregex, ceq_mregex, ccompare_mregex) sa s then s
          else lPDs_aux sa));;

let rec lPDs
  r = lPDs_aux
        (insert (ceq_mregex, ccompare_mregex) r
          (set_empty (ceq_mregex, ccompare_mregex)
            (of_phantom set_impl_mregexa)));;

let rec rPDs_aux
  s = (let sa =
         sup_seta (ceq_mregex, ccompare_mregex) s
           (bind (ceq_mregex, ccompare_mregex)
             (ceq_mregex, ccompare_mregex, set_impl_mregex) s rpd)
         in
        (if less_eq_set (cenum_mregex, ceq_mregex, ccompare_mregex) sa s then s
          else rPDs_aux sa));;

let rec rPDs
  r = rPDs_aux
        (insert (ceq_mregex, ccompare_mregex) r
          (set_empty (ceq_mregex, ccompare_mregex)
            (of_phantom set_impl_mregexa)));;

let rec impl_of (Alist x) = x;;

let rec lookup _A xa = map_of _A (impl_of xa);;

let rec ecard (_A1, _A2, _A3)
  a = (if finite (_A1.finite_UNIV_card_UNIV, _A2, _A3) a
        then Enat (card (_A1, _A2, _A3) a) else Infinity_enat);;

let rec rep_I (Abs_I x) = x;;

let rec left x = fst (rep_I x);;

let rec matcha _A
  x0 x1 = match x0, x1 with [], [] -> Some (fun _ -> None)
    | Const x :: ts, y :: ys -> (if eq _A x y then matcha _A ts ys else None)
    | Var x :: ts, y :: ys ->
        (match matcha _A ts ys with None -> None
          | Some f ->
            (match f x with None -> Some (fun_upd equal_nat f x (Some y))
              | Some z -> (if eq _A y z then Some f else None)))
    | Var vb :: va, [] -> None
    | v :: va, [] -> None
    | [], v :: va -> None;;

let rec less_eq_enat q x1 = match q, x1 with Infinity_enat, Enat n -> false
                       | q, Infinity_enat -> true
                       | Enat m, Enat n -> less_eq_nat m n;;

let rec empty_table (_A1, _A2, _A3) = bot_set (_A1, _A2, _A3);;

let rec unsafe_epsilon (_A1, _A2, _A3)
  guard phi_s x2 = match guard, phi_s, x2 with
    guard, phi_s, MWild ->
      empty_table
        ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)),
          set_impl_list)
    | guard, phi_s, MEps -> guard
    | guard, phi_s, MTestPos i -> join (_A1, _A2, _A3) guard true (nth phi_s i)
    | guard, phi_s, MTestNeg i -> join (_A1, _A2, _A3) guard false (nth phi_s i)
    | guard, phi_s, MPlus (r, s) ->
        sup_seta
          ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
          (unsafe_epsilon (_A1, _A2, _A3) guard phi_s r)
          (unsafe_epsilon (_A1, _A2, _A3) guard phi_s s)
    | guard, phi_s, MTimes (r, s) ->
        join (_A1, _A2, _A3) (unsafe_epsilon (_A1, _A2, _A3) guard phi_s r) true
          (unsafe_epsilon (_A1, _A2, _A3) guard phi_s s)
    | guard, phi_s, MStar r -> guard;;

let rec replicate
  n x = (if equal_nata n zero_nat then []
          else x :: replicate (minus_nat n one_nata) x);;

let rec unit_table (_A1, _A2)
  n = insert
        ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
        (replicate n None)
        (set_empty
          ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
          (of_phantom set_impl_lista));;

let rec safe_r_epsilon (_A1, _A2, _A3)
  n phi_s x2 = match n, phi_s, x2 with
    n, phi_s, MWild ->
      empty_table
        ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)),
          set_impl_list)
    | n, phi_s, MEps -> unit_table (_A1, _A2) n
    | n, phi_s, MTestPos i -> nth phi_s i
    | n, phi_s, MPlus (r, s) ->
        sup_seta
          ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
          (safe_r_epsilon (_A1, _A2, _A3) n phi_s r)
          (safe_r_epsilon (_A1, _A2, _A3) n phi_s s)
    | n, phi_s, MTimes (r, s) ->
        unsafe_epsilon (_A1, _A2, _A3)
          (safe_r_epsilon (_A1, _A2, _A3) n phi_s r) phi_s s
    | n, phi_s, MTestNeg v -> failwith "undefined"
    | n, phi_s, MStar v -> failwith "undefined";;

let rec lookupa (_A1, _A2) = function RBT_Mapping t -> lookupc _A1 t
                             | Assoc_List_Mapping al -> lookup _A2 al;;

let rec lookup_default (_B1, _B2)
  d m k = (match lookupa (_B1, _B2) m k with None -> d | Some v -> v);;

let rec lookupb (_A1, _A2) (_B1, _B2, _B3)
  = lookup_default (_A1, _A2) (empty_table (_B1, _B2, _B3));;

let rec r_delta (_A1, _A2, _A3)
  kappa x phi_s xa3 = match kappa, x, phi_s, xa3 with
    kappa, x, phi_s, MWild ->
      lookupb (ccompare_mregex, equal_mregex)
        ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)),
          set_impl_list)
        x (kappa MEps)
    | kappa, x, phi_s, MEps ->
        empty_table
          ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)),
            set_impl_list)
    | kappa, x, phi_s, MTestPos i ->
        empty_table
          ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)),
            set_impl_list)
    | kappa, x, phi_s, MTestNeg i ->
        empty_table
          ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)),
            set_impl_list)
    | kappa, x, phi_s, MPlus (r, s) ->
        sup_seta
          ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
          (r_delta (_A1, _A2, _A3) kappa x phi_s r)
          (r_delta (_A1, _A2, _A3) kappa x phi_s s)
    | kappa, x, phi_s, MTimes (r, s) ->
        sup_seta
          ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
          (r_delta (_A1, _A2, _A3) (fun t -> kappa (MTimes (r, t))) x phi_s s)
          (unsafe_epsilon (_A1, _A2, _A3)
            (r_delta (_A1, _A2, _A3) kappa x phi_s r) phi_s s)
    | kappa, x, phi_s, MStar r ->
        r_delta (_A1, _A2, _A3) (fun t -> kappa (MTimes (MStar r, t))) x phi_s
          r;;

let rec rbt_comp_bulkload
  c xs = foldr (fun (a, b) -> rbt_comp_insert c a b) xs Empty;;

let rec bulkload _A
  xa = Mapping_RBT (rbt_comp_bulkload (the (ccompare _A)) xa);;

let rec tabulatea _A (_B1, _B2)
  xs f =
    (match ccompare _A
      with None ->
        failwith "tabulate RBT_Mapping: ccompare = None"
          (fun _ -> tabulatea _A (_B1, _B2) xs f)
      | Some _ ->
        RBT_Mapping
          (bulkload _A
            (map_filter
              (fun k ->
                (let fk = f k in
                  (if is_empty
                        (card_UNIV_list, (ceq_list (ceq_option _B1)),
                          (cproper_interval_list (ccompare_option _B2)))
                        fk
                    then None else Some (k, fk))))
              xs)));;

let rec right x = snd (rep_I x);;

let rec update_matchP (_A1, _A2, _A3)
  n i mr mrs rels nt aux =
    (let auxa =
       (match
         maps (fun (t, rel) ->
                (if less_eq_enat (Enat (minus_nat nt t)) (right i)
                  then [(t, tabulatea ccompare_mregex (_A1, _A2) mrs
                              (fun mra ->
                                sup_seta
                                  ((ceq_list (ceq_option _A1)),
                                    (ccompare_list (ccompare_option _A2)))
                                  (r_delta (_A1, _A2, _A3) id rel rels mra)
                                  (if equal_nata t nt
                                    then safe_r_epsilon (_A1, _A2, _A3) n rels
   mra
                                    else set_empty
   ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
   (of_phantom set_impl_lista))))]
                  else []))
           aux
         with [] ->
           [(nt, tabulatea ccompare_mregex (_A1, _A2) mrs
                   (safe_r_epsilon (_A1, _A2, _A3) n rels))]
         | x :: auxa ->
           (if equal_nata (fst x) nt then x :: auxa
             else (nt, tabulatea ccompare_mregex (_A1, _A2) mrs
                         (safe_r_epsilon (_A1, _A2, _A3) n rels)) ::
                    x :: auxa))
       in
      (foldr (sup_seta
               ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2))))
         (maps (fun (t, rel) ->
                 (if less_eq_nat (left i) (minus_nat nt t)
                   then [lookupb (ccompare_mregex, equal_mregex)
                           ((ceq_list (ceq_option _A1)),
                             (ccompare_list (ccompare_option _A2)),
                             set_impl_list)
                           rel mr]
                   else []))
           auxa)
         (set_empty
           ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
           (of_phantom set_impl_lista)),
        auxa));;

let rec update_until (_A1, _A2, _A3)
  i pos rel1 rel2 nt aux =
    map (fun (t, (a1, a2)) ->
          (t, ((if pos then join (_A1, _A2, _A3) a1 true rel1
                 else sup_seta
                        ((ceq_list (ceq_option _A1)),
                          (ccompare_list (ccompare_option _A2)))
                        a1 rel1),
                (if less_eq_nat (left i) (minus_nat nt t) &&
                      less_eq_enat (Enat (minus_nat nt t)) (right i)
                  then sup_seta
                         ((ceq_list (ceq_option _A1)),
                           (ccompare_list (ccompare_option _A2)))
                         a2 (join (_A1, _A2, _A3) rel2 pos a1)
                  else a2))))
      aux @
      [(nt, (rel1,
              (if equal_nata (left i) zero_nat then rel2
                else empty_table
                       ((ceq_list (ceq_option _A1)),
                         (ccompare_list (ccompare_option _A2)),
                         set_impl_list))))];;

let zero_enat : enat = Enat zero_nat;;

let rec minus_enat x0 n = match x0, n with Enat a, Infinity_enat -> zero_enat
                     | Infinity_enat, n -> Infinity_enat
                     | Enat a, Enat b -> Enat (minus_nat a b);;

let rec update_since (_A1, _A2, _A3)
  i pos rel1 rel2 nt aux =
    (let auxa =
       (match map (fun (t, rel) -> (t, join (_A1, _A2, _A3) rel pos rel1)) aux
         with [] -> [(nt, rel2)]
         | x :: auxa ->
           (if equal_nata (fst x) nt
             then (fst x,
                    sup_seta
                      ((ceq_list (ceq_option _A1)),
                        (ccompare_list (ccompare_option _A2)))
                      (snd x) rel2) ::
                    auxa
             else (nt, rel2) :: x :: auxa))
       in
      (foldr (sup_seta
               ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2))))
         (maps (fun (t, rel) ->
                 (if less_eq_enat (minus_enat (Enat nt) (Enat t)) (right i)
                   then (if less_eq_nat (left i) (minus_nat nt t) then [rel]
                          else [])
                   else []))
           auxa)
         (set_empty
           ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
           (of_phantom set_impl_lista)),
        filtera (fun (t, _) -> less_eq_enat (Enat (minus_nat nt t)) (right i))
          auxa));;

let rec inf_cfi _A
  = Abs_comp_fun_idem (inf _A.semilattice_inf_lattice.inf_semilattice_inf);;

let rec inf_setb (_A1, _A2, _A3, _A4, _A5)
  a = (if finite
            ((finite_UNIV_set _A1),
              (ceq_set (_A2, _A3, _A4.ccompare_cproper_interval)),
              (ccompare_set (_A1, _A3, _A4, _A5)))
            a
        then set_fold_cfi
               ((ceq_set (_A2, _A3, _A4.ccompare_cproper_interval)),
                 (ccompare_set (_A1, _A3, _A4, _A5)))
               (inf_cfi (lattice_set (_A2, _A3, _A4.ccompare_cproper_interval)))
               (top_set (_A3, _A4.ccompare_cproper_interval, _A5)) a
        else failwith "Inf: infinite"
               (fun _ -> inf_setb (_A1, _A2, _A3, _A4, _A5) a));;

let rec subset (_A1, _A2, _A3, _A4) = subset_eq (_A2, _A3, _A4);;

let rec filterQueryNeg (_A1, _A2)
  v q = filter
          ((ceq_prod
             (ceq_set
               (cenum_nat, ceq_nat,
                 cproper_interval_nat.ccompare_cproper_interval))
             (ceq_set
               (cenum_list, (ceq_list (ceq_option _A1)),
                 (cproper_interval_list
                   (ccompare_option _A2)).ccompare_cproper_interval))),
            (ccompare_prod
              (ccompare_set
                (finite_UNIV_nat, ceq_nat, cproper_interval_nat, set_impl_nat))
              (ccompare_set
                (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                  (cproper_interval_list (ccompare_option _A2)),
                  set_impl_list))))
          (fun (a, _) ->
            subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat) a v)
          q;;

let rec restrict
  a v = map (fun i ->
              (if member (ceq_nat, ccompare_nat) i a then nth v i else None))
          (upt zero_nat (size_list v));;

let rec projectTable (_A1, _A2)
  v (s, t) =
    (inf_seta (ceq_nat, ccompare_nat) s v,
      image ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
        ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)),
          set_impl_list)
        (restrict v) t);;

let rec projectQuery (_A1, _A2)
  v s = image ((ceq_prod
                 (ceq_set
                   (cenum_nat, ceq_nat,
                     cproper_interval_nat.ccompare_cproper_interval))
                 (ceq_set
                   (cenum_list, (ceq_list (ceq_option _A1)),
                     (cproper_interval_list
                       (ccompare_option _A2)).ccompare_cproper_interval))),
                (ccompare_prod
                  (ccompare_set
                    (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                      set_impl_nat))
                  (ccompare_set
                    (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                      (cproper_interval_list (ccompare_option _A2)),
                      set_impl_list))))
          ((ceq_prod
             (ceq_set
               (cenum_nat, ceq_nat,
                 cproper_interval_nat.ccompare_cproper_interval))
             (ceq_set
               (cenum_list, (ceq_list (ceq_option _A1)),
                 (cproper_interval_list
                   (ccompare_option _A2)).ccompare_cproper_interval))),
            (ccompare_prod
              (ccompare_set
                (finite_UNIV_nat, ceq_nat, cproper_interval_nat, set_impl_nat))
              (ccompare_set
                (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                  (cproper_interval_list (ccompare_option _A2)),
                  set_impl_list))),
            (set_impl_prod set_impl_set set_impl_set))
          (projectTable (_A1, _A2) v) s;;

let rec filterQuery (_A1, _A2)
  v q = filter
          ((ceq_prod
             (ceq_set
               (cenum_nat, ceq_nat,
                 cproper_interval_nat.ccompare_cproper_interval))
             (ceq_set
               (cenum_list, (ceq_list (ceq_option _A1)),
                 (cproper_interval_list
                   (ccompare_option _A2)).ccompare_cproper_interval))),
            (ccompare_prod
              (ccompare_set
                (finite_UNIV_nat, ceq_nat, cproper_interval_nat, set_impl_nat))
              (ccompare_set
                (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                  (cproper_interval_list (ccompare_option _A2)),
                  set_impl_list))))
          (fun (s, _) ->
            not (is_empty (card_UNIV_nat, ceq_nat, cproper_interval_nat)
                  (inf_seta (ceq_nat, ccompare_nat) s v)))
          q;;

let rec minus_set (_A1, _A2) a b = inf_seta (_A1, _A2) a (uminus_set b);;

let rec isSameIntersection _A
  t1 s t2 =
    ball (ceq_nat, ccompare_nat) s
      (fun i -> equal_optiona _A (nth t1 i) (nth t2 i));;

let rec semiJoin (_A1, _A2, _A3)
  (s, tab) (st, tup) =
    (s, filter
          ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
          (isSameIntersection _A3 tup (inf_seta (ceq_nat, ccompare_nat) s st))
          tab);;

let rec newQuery (_A1, _A2, _A3)
  v q (st, t) =
    image ((ceq_prod
             (ceq_set
               (cenum_nat, ceq_nat,
                 cproper_interval_nat.ccompare_cproper_interval))
             (ceq_set
               (cenum_list, (ceq_list (ceq_option _A1)),
                 (cproper_interval_list
                   (ccompare_option _A2)).ccompare_cproper_interval))),
            (ccompare_prod
              (ccompare_set
                (finite_UNIV_nat, ceq_nat, cproper_interval_nat, set_impl_nat))
              (ccompare_set
                (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                  (cproper_interval_list (ccompare_option _A2)),
                  set_impl_list))))
      ((ceq_prod
         (ceq_set
           (cenum_nat, ceq_nat, cproper_interval_nat.ccompare_cproper_interval))
         (ceq_set
           (cenum_list, (ceq_list (ceq_option _A1)),
             (cproper_interval_list
               (ccompare_option _A2)).ccompare_cproper_interval))),
        (ccompare_prod
          (ccompare_set
            (finite_UNIV_nat, ceq_nat, cproper_interval_nat, set_impl_nat))
          (ccompare_set
            (finite_UNIV_list, (ceq_list (ceq_option _A1)),
              (cproper_interval_list (ccompare_option _A2)), set_impl_list))),
        (set_impl_prod set_impl_set set_impl_set))
      (fun tab ->
        projectTable (_A1, _A2) v (semiJoin (_A1, _A2, _A3) tab (st, t)))
      q;;

let rec merge_option = function (None, None) -> None
                       | (Some x, None) -> Some x
                       | (None, Some x) -> Some x
                       | (Some a, Some b) -> Some a;;

let rec merge t1 t2 = map merge_option (zip t1 t2);;

let rec insort_key _B
  f x xa2 = match f, x, xa2 with f, x, [] -> [x]
    | f, x, y :: ys ->
        (if less_eq _B.order_linorder.preorder_order.ord_preorder (f x) (f y)
          then x :: y :: ys else y :: insort_key _B f x ys);;

let rec sort_key _B f xs = foldr (insort_key _B f) xs [];;

let rec sorted_list_of_set (_A1, _A2, _A3, _A4)
  = function
    RBT_set rbt ->
      (match ccompare _A2
        with None ->
          failwith "sorted_list_of_set RBT_set: ccompare = None"
            (fun _ -> sorted_list_of_set (_A1, _A2, _A3, _A4) (RBT_set rbt))
        | Some _ -> sort_key _A4 (fun x -> x) (keysa _A2 rbt))
    | DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "sorted_list_of_set DList_set: ceq = None"
              (fun _ -> sorted_list_of_set (_A1, _A2, _A3, _A4) (DList_set dxs))
          | Some _ -> sort_key _A4 (fun x -> x) (list_of_dlist _A1 dxs))
    | Set_Monad xs -> sort_key _A4 (fun x -> x) (remdups _A3 xs);;

let rec arg_min_list _B
  f x1 = match f, x1 with f, [x] -> x
    | f, x :: y :: zs ->
        (let m = arg_min_list _B f (y :: zs) in
          (if less_eq _B.order_linorder.preorder_order.ord_preorder (f x) (f m)
            then x else m));;

let rec arg_max_list
  f l = (let m =
           maxa (ceq_nat, ccompare_nat, lattice_nat, linorder_nat)
             (set (ceq_nat, ccompare_nat, set_impl_nat) (map f l))
           in
          arg_min_list linorder_nat (fun x -> minus_nat m (f x)) l);;

let rec score (_A1, _A2)
  q i = (let relevant =
           image ((ceq_prod
                    (ceq_set
                      (cenum_nat, ceq_nat,
                        cproper_interval_nat.ccompare_cproper_interval))
                    (ceq_set
                      (cenum_list, (ceq_list (ceq_option _A1)),
                        (cproper_interval_list
                          (ccompare_option _A2)).ccompare_cproper_interval))),
                   (ccompare_prod
                     (ccompare_set
                       (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                         set_impl_nat))
                     (ccompare_set
                       (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                         (cproper_interval_list (ccompare_option _A2)),
                         set_impl_list))))
             (ceq_nat, ccompare_nat, set_impl_nat)
             (fun (_, a) ->
               card (card_UNIV_list, (ceq_list (ceq_option _A1)),
                      (ccompare_list (ccompare_option _A2)))
                 a)
             (filter
               ((ceq_prod
                  (ceq_set
                    (cenum_nat, ceq_nat,
                      cproper_interval_nat.ccompare_cproper_interval))
                  (ceq_set
                    (cenum_list, (ceq_list (ceq_option _A1)),
                      (cproper_interval_list
                        (ccompare_option _A2)).ccompare_cproper_interval))),
                 (ccompare_prod
                   (ccompare_set
                     (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                       set_impl_nat))
                   (ccompare_set
                     (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                       (cproper_interval_list (ccompare_option _A2)),
                       set_impl_list))))
               (fun (sign, _) -> member (ceq_nat, ccompare_nat) i sign) q)
           in
         let a =
           sorted_list_of_set (ceq_nat, ccompare_nat, equal_nat, linorder_nat)
             relevant
           in
          foldl plus_nat zero_nat a);;

let rec max_getIJ (_A1, _A2)
  q_pos q_neg v =
    (let l =
       sorted_list_of_set (ceq_nat, ccompare_nat, equal_nat, linorder_nat) v in
      (if is_empty
            ((card_UNIV_prod (card_UNIV_set card_UNIV_nat)
               (card_UNIV_set card_UNIV_list)),
              (ceq_prod
                (ceq_set
                  (cenum_nat, ceq_nat,
                    cproper_interval_nat.ccompare_cproper_interval))
                (ceq_set
                  (cenum_list, (ceq_list (ceq_option _A1)),
                    (cproper_interval_list
                      (ccompare_option _A2)).ccompare_cproper_interval))),
              (cproper_interval_prod
                (cproper_interval_set
                  (card_UNIV_nat, ceq_nat, cproper_interval_nat, set_impl_nat))
                (cproper_interval_set
                  (card_UNIV_list, (ceq_list (ceq_option _A1)),
                    (cproper_interval_list (ccompare_option _A2)),
                    set_impl_list))))
            q_neg
        then (let x = arg_max_list (score (_A1, _A2) q_pos) l in
               (insert (ceq_nat, ccompare_nat) x
                  (set_empty (ceq_nat, ccompare_nat)
                    (of_phantom set_impl_nata)),
                 minus_set (ceq_nat, ccompare_nat) v
                   (insert (ceq_nat, ccompare_nat) x
                     (set_empty (ceq_nat, ccompare_nat)
                       (of_phantom set_impl_nata)))))
        else (let x = arg_max_list (score (_A1, _A2) q_neg) l in
               (minus_set (ceq_nat, ccompare_nat) v
                  (insert (ceq_nat, ccompare_nat) x
                    (set_empty (ceq_nat, ccompare_nat)
                      (of_phantom set_impl_nata))),
                 insert (ceq_nat, ccompare_nat) x
                   (set_empty (ceq_nat, ccompare_nat)
                     (of_phantom set_impl_nata))))));;

let rec new_max_getIJ_genericJoin (_A1, _A2, _A3)
  v q_pos q_neg =
    (if less_eq_nat (card (card_UNIV_nat, ceq_nat, ccompare_nat) v) one_nata
      then minus_set
             ((ceq_list (ceq_option _A1)),
               (ccompare_list (ccompare_option _A2)))
             (inf_setb
               (finite_UNIV_list, cenum_list, (ceq_list (ceq_option _A1)),
                 (cproper_interval_list (ccompare_option _A2)), set_impl_list)
               (image
                 ((ceq_prod
                    (ceq_set
                      (cenum_nat, ceq_nat,
                        cproper_interval_nat.ccompare_cproper_interval))
                    (ceq_set
                      (cenum_list, (ceq_list (ceq_option _A1)),
                        (cproper_interval_list
                          (ccompare_option _A2)).ccompare_cproper_interval))),
                   (ccompare_prod
                     (ccompare_set
                       (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                         set_impl_nat))
                     (ccompare_set
                       (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                         (cproper_interval_list (ccompare_option _A2)),
                         set_impl_list))))
                 ((ceq_set
                    (cenum_list, (ceq_list (ceq_option _A1)),
                      (cproper_interval_list
                        (ccompare_option _A2)).ccompare_cproper_interval)),
                   (ccompare_set
                     (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                       (cproper_interval_list (ccompare_option _A2)),
                       set_impl_list)),
                   set_impl_set)
                 (fun (_, x) -> x) q_pos))
             (sup_setb
               (finite_UNIV_list, cenum_list, (ceq_list (ceq_option _A1)),
                 (cproper_interval_list (ccompare_option _A2)), set_impl_list)
               (image
                 ((ceq_prod
                    (ceq_set
                      (cenum_nat, ceq_nat,
                        cproper_interval_nat.ccompare_cproper_interval))
                    (ceq_set
                      (cenum_list, (ceq_list (ceq_option _A1)),
                        (cproper_interval_list
                          (ccompare_option _A2)).ccompare_cproper_interval))),
                   (ccompare_prod
                     (ccompare_set
                       (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                         set_impl_nat))
                     (ccompare_set
                       (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                         (cproper_interval_list (ccompare_option _A2)),
                         set_impl_list))))
                 ((ceq_set
                    (cenum_list, (ceq_list (ceq_option _A1)),
                      (cproper_interval_list
                        (ccompare_option _A2)).ccompare_cproper_interval)),
                   (ccompare_set
                     (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                       (cproper_interval_list (ccompare_option _A2)),
                       set_impl_list)),
                   set_impl_set)
                 (fun (_, x) -> x) q_neg))
      else (let (i, j) = max_getIJ (_A1, _A2) q_pos q_neg v in
            let q_I_pos =
              projectQuery (_A1, _A2) i (filterQuery (_A1, _A2) i q_pos) in
            let q_I_neg = filterQueryNeg (_A1, _A2) i q_neg in
            let r_I =
              new_max_getIJ_genericJoin (_A1, _A2, _A3) i q_I_pos q_I_neg in
            let q_J_neg =
              minus_set
                ((ceq_prod
                   (ceq_set
                     (cenum_nat, ceq_nat,
                       cproper_interval_nat.ccompare_cproper_interval))
                   (ceq_set
                     (cenum_list, (ceq_list (ceq_option _A1)),
                       (cproper_interval_list
                         (ccompare_option _A2)).ccompare_cproper_interval))),
                  (ccompare_prod
                    (ccompare_set
                      (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                        set_impl_nat))
                    (ccompare_set
                      (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                        (cproper_interval_list (ccompare_option _A2)),
                        set_impl_list))))
                q_neg q_I_neg
              in
            let q_J_pos = filterQuery (_A1, _A2) j q_pos in
            let x =
              image ((ceq_list (ceq_option _A1)),
                      (ccompare_list (ccompare_option _A2)))
                ((ceq_prod (ceq_list (ceq_option _A1))
                   (ceq_set
                     (cenum_list, (ceq_list (ceq_option _A1)),
                       (cproper_interval_list
                         (ccompare_option _A2)).ccompare_cproper_interval))),
                  (ccompare_prod (ccompare_list (ccompare_option _A2))
                    (ccompare_set
                      (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                        (cproper_interval_list (ccompare_option _A2)),
                        set_impl_list))),
                  (set_impl_prod set_impl_list set_impl_set))
                (fun t ->
                  (t, new_max_getIJ_genericJoin (_A1, _A2, _A3) j
                        (newQuery (_A1, _A2, _A3) j q_J_pos (i, t))
                        (newQuery (_A1, _A2, _A3) j q_J_neg (i, t))))
                r_I
              in
             sup_setb
               (finite_UNIV_list, cenum_list, (ceq_list (ceq_option _A1)),
                 (cproper_interval_list (ccompare_option _A2)), set_impl_list)
               (image
                 ((ceq_prod (ceq_list (ceq_option _A1))
                    (ceq_set
                      (cenum_list, (ceq_list (ceq_option _A1)),
                        (cproper_interval_list
                          (ccompare_option _A2)).ccompare_cproper_interval))),
                   (ccompare_prod (ccompare_list (ccompare_option _A2))
                     (ccompare_set
                       (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                         (cproper_interval_list (ccompare_option _A2)),
                         set_impl_list))))
                 ((ceq_set
                    (cenum_list, (ceq_list (ceq_option _A1)),
                      (cproper_interval_list
                        (ccompare_option _A2)).ccompare_cproper_interval)),
                   (ccompare_set
                     (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                       (cproper_interval_list (ccompare_option _A2)),
                       set_impl_list)),
                   set_impl_set)
                 (fun (t, a) ->
                   image ((ceq_list (ceq_option _A1)),
                           (ccompare_list (ccompare_option _A2)))
                     ((ceq_list (ceq_option _A1)),
                       (ccompare_list (ccompare_option _A2)), set_impl_list)
                     (fun xx -> merge xx t) a)
                 x)));;

let rec new_max_getIJ_wrapperGenericJoin (_A1, _A2, _A3)
  q_pos q_neg =
    (if bex ((ceq_prod
               (ceq_set
                 (cenum_nat, ceq_nat,
                   cproper_interval_nat.ccompare_cproper_interval))
               (ceq_set
                 (cenum_list, (ceq_list (ceq_option _A1)),
                   (cproper_interval_list
                     (ccompare_option _A2)).ccompare_cproper_interval))),
              (ccompare_prod
                (ccompare_set
                  (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                    set_impl_nat))
                (ccompare_set
                  (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                    (cproper_interval_list (ccompare_option _A2)),
                    set_impl_list))))
          q_pos
          (fun (_, a) ->
            is_empty
              (card_UNIV_list, (ceq_list (ceq_option _A1)),
                (cproper_interval_list (ccompare_option _A2)))
              a) ||
          bex ((ceq_prod
                 (ceq_set
                   (cenum_nat, ceq_nat,
                     cproper_interval_nat.ccompare_cproper_interval))
                 (ceq_set
                   (cenum_list, (ceq_list (ceq_option _A1)),
                     (cproper_interval_list
                       (ccompare_option _A2)).ccompare_cproper_interval))),
                (ccompare_prod
                  (ccompare_set
                    (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                      set_impl_nat))
                  (ccompare_set
                    (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                      (cproper_interval_list (ccompare_option _A2)),
                      set_impl_list))))
            q_neg
            (fun (a, x) ->
              is_empty (card_UNIV_nat, ceq_nat, cproper_interval_nat) a &&
                not (is_empty
                      (card_UNIV_list, (ceq_list (ceq_option _A1)),
                        (cproper_interval_list (ccompare_option _A2)))
                      x))
      then set_empty
             ((ceq_list (ceq_option _A1)),
               (ccompare_list (ccompare_option _A2)))
             (of_phantom set_impl_lista)
      else (let q =
              filter
                ((ceq_prod
                   (ceq_set
                     (cenum_nat, ceq_nat,
                       cproper_interval_nat.ccompare_cproper_interval))
                   (ceq_set
                     (cenum_list, (ceq_list (ceq_option _A1)),
                       (cproper_interval_list
                         (ccompare_option _A2)).ccompare_cproper_interval))),
                  (ccompare_prod
                    (ccompare_set
                      (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                        set_impl_nat))
                    (ccompare_set
                      (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                        (cproper_interval_list (ccompare_option _A2)),
                        set_impl_list))))
                (fun (a, _) ->
                  not (is_empty (card_UNIV_nat, ceq_nat, cproper_interval_nat)
                        a))
                q_pos
              in
             (if is_empty
                   ((card_UNIV_prod (card_UNIV_set card_UNIV_nat)
                      (card_UNIV_set card_UNIV_list)),
                     (ceq_prod
                       (ceq_set
                         (cenum_nat, ceq_nat,
                           cproper_interval_nat.ccompare_cproper_interval))
                       (ceq_set
                         (cenum_list, (ceq_list (ceq_option _A1)),
                           (cproper_interval_list
                             (ccompare_option
                               _A2)).ccompare_cproper_interval))),
                     (cproper_interval_prod
                       (cproper_interval_set
                         (card_UNIV_nat, ceq_nat, cproper_interval_nat,
                           set_impl_nat))
                       (cproper_interval_set
                         (card_UNIV_list, (ceq_list (ceq_option _A1)),
                           (cproper_interval_list (ccompare_option _A2)),
                           set_impl_list))))
                   q
               then minus_set
                      ((ceq_list (ceq_option _A1)),
                        (ccompare_list (ccompare_option _A2)))
                      (inf_setb
                        (finite_UNIV_list, cenum_list,
                          (ceq_list (ceq_option _A1)),
                          (cproper_interval_list (ccompare_option _A2)),
                          set_impl_list)
                        (image
                          ((ceq_prod
                             (ceq_set
                               (cenum_nat, ceq_nat,
                                 cproper_interval_nat.ccompare_cproper_interval))
                             (ceq_set
                               (cenum_list, (ceq_list (ceq_option _A1)),
                                 (cproper_interval_list
                                   (ccompare_option
                                     _A2)).ccompare_cproper_interval))),
                            (ccompare_prod
                              (ccompare_set
                                (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                                  set_impl_nat))
                              (ccompare_set
                                (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                                  (cproper_interval_list (ccompare_option _A2)),
                                  set_impl_list))))
                          ((ceq_set
                             (cenum_list, (ceq_list (ceq_option _A1)),
                               (cproper_interval_list
                                 (ccompare_option
                                   _A2)).ccompare_cproper_interval)),
                            (ccompare_set
                              (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                                (cproper_interval_list (ccompare_option _A2)),
                                set_impl_list)),
                            set_impl_set)
                          (fun (_, x) -> x) q_pos))
                      (sup_setb
                        (finite_UNIV_list, cenum_list,
                          (ceq_list (ceq_option _A1)),
                          (cproper_interval_list (ccompare_option _A2)),
                          set_impl_list)
                        (image
                          ((ceq_prod
                             (ceq_set
                               (cenum_nat, ceq_nat,
                                 cproper_interval_nat.ccompare_cproper_interval))
                             (ceq_set
                               (cenum_list, (ceq_list (ceq_option _A1)),
                                 (cproper_interval_list
                                   (ccompare_option
                                     _A2)).ccompare_cproper_interval))),
                            (ccompare_prod
                              (ccompare_set
                                (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                                  set_impl_nat))
                              (ccompare_set
                                (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                                  (cproper_interval_list (ccompare_option _A2)),
                                  set_impl_list))))
                          ((ceq_set
                             (cenum_list, (ceq_list (ceq_option _A1)),
                               (cproper_interval_list
                                 (ccompare_option
                                   _A2)).ccompare_cproper_interval)),
                            (ccompare_set
                              (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                                (cproper_interval_list (ccompare_option _A2)),
                                set_impl_list)),
                            set_impl_set)
                          (fun (_, x) -> x) q_neg))
               else (let v =
                       sup_setb
                         (finite_UNIV_nat, cenum_nat, ceq_nat,
                           cproper_interval_nat, set_impl_nat)
                         (image
                           ((ceq_prod
                              (ceq_set
                                (cenum_nat, ceq_nat,
                                  cproper_interval_nat.ccompare_cproper_interval))
                              (ceq_set
                                (cenum_list, (ceq_list (ceq_option _A1)),
                                  (cproper_interval_list
                                    (ccompare_option
                                      _A2)).ccompare_cproper_interval))),
                             (ccompare_prod
                               (ccompare_set
                                 (finite_UNIV_nat, ceq_nat,
                                   cproper_interval_nat, set_impl_nat))
                               (ccompare_set
                                 (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                                   (cproper_interval_list
                                     (ccompare_option _A2)),
                                   set_impl_list))))
                           ((ceq_set
                              (cenum_nat, ceq_nat,
                                cproper_interval_nat.ccompare_cproper_interval)),
                             (ccompare_set
                               (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                                 set_impl_nat)),
                             set_impl_set)
                           (fun (a, _) -> a) q)
                       in
                     let a =
                       filter
                         ((ceq_prod
                            (ceq_set
                              (cenum_nat, ceq_nat,
                                cproper_interval_nat.ccompare_cproper_interval))
                            (ceq_set
                              (cenum_list, (ceq_list (ceq_option _A1)),
                                (cproper_interval_list
                                  (ccompare_option
                                    _A2)).ccompare_cproper_interval))),
                           (ccompare_prod
                             (ccompare_set
                               (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                                 set_impl_nat))
                             (ccompare_set
                               (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                                 (cproper_interval_list (ccompare_option _A2)),
                                 set_impl_list))))
                         (fun (a, _) ->
                           subset
                             (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat) a
                             v &&
                             less_eq_nat one_nata
                               (card (card_UNIV_nat, ceq_nat, ccompare_nat) a))
                         q_neg
                       in
                      new_max_getIJ_genericJoin (_A1, _A2, _A3) v q a))));;

let rec mmulti_join (_A1, _A2, _A3)
  a_pos a_neg l =
    (let q =
       set ((ceq_prod
              (ceq_set
                (cenum_nat, ceq_nat,
                  cproper_interval_nat.ccompare_cproper_interval))
              (ceq_set
                (cenum_list, (ceq_list (ceq_option _A1)),
                  (cproper_interval_list
                    (ccompare_option _A2)).ccompare_cproper_interval))),
             (ccompare_prod
               (ccompare_set
                 (finite_UNIV_nat, ceq_nat, cproper_interval_nat, set_impl_nat))
               (ccompare_set
                 (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                   (cproper_interval_list (ccompare_option _A2)),
                   set_impl_list))),
             (set_impl_prod set_impl_set set_impl_set))
         (zip a_pos l)
       in
     let a =
       set ((ceq_prod
              (ceq_set
                (cenum_nat, ceq_nat,
                  cproper_interval_nat.ccompare_cproper_interval))
              (ceq_set
                (cenum_list, (ceq_list (ceq_option _A1)),
                  (cproper_interval_list
                    (ccompare_option _A2)).ccompare_cproper_interval))),
             (ccompare_prod
               (ccompare_set
                 (finite_UNIV_nat, ceq_nat, cproper_interval_nat, set_impl_nat))
               (ccompare_set
                 (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                   (cproper_interval_list (ccompare_option _A2)),
                   set_impl_list))),
             (set_impl_prod set_impl_set set_impl_set))
         (zip a_neg (drop (size_list a_pos) l))
       in
      new_max_getIJ_wrapperGenericJoin (_A1, _A2, _A3) q a);;

let rec mbufnt_take (_A1, _A2, _A3)
  f z buf ts =
    (if membera
          (equal_list
            (equal_set
              (cenum_list, (ceq_list (ceq_option _A1)),
                (ccompare_list (ccompare_option _A2)),
                (equal_list (equal_option _A3)))))
          buf [] ||
          null ts
      then (z, (buf, ts))
      else mbufnt_take (_A1, _A2, _A3) f (f (map hda buf) (hda ts) z)
             (map tla buf) (tla ts));;

let rec mbuf2t_take
  f z x2 ts = match f, z, x2, ts with
    f, z, (x :: xs, y :: ys), t :: ts -> mbuf2t_take f (f x y t z) (xs, ys) ts
    | f, z, ([], ys), ts -> (z, (([], ys), ts))
    | f, z, (xs, []), ts -> (z, ((xs, []), ts))
    | f, z, (xs, ys), [] -> (z, ((xs, ys), []));;

let rec mprev_next (_A1, _A2)
  i x1 ts = match i, x1, ts with i, [], ts -> ([], ([], ts))
    | i, v :: va, [] -> ([], (v :: va, []))
    | i, v :: va, [t] -> ([], (v :: va, [t]))
    | i, x :: xs, ta :: t :: ts ->
        (let a = mprev_next (_A1, _A2) i xs (t :: ts) in
         let (ys, aa) = a in
          ((if less_eq_nat (left i) (minus_nat t ta) &&
                 less_eq_enat (Enat (minus_nat t ta)) (right i)
             then x
             else empty_table
                    ((ceq_list (ceq_option _A1)),
                      (ccompare_list (ccompare_option _A2)), set_impl_list)) ::
             ys,
            aa));;

let rec mbufn_take (_A1, _A2, _A3)
  f z buf =
    (if null buf ||
          membera
            (equal_list
              (equal_set
                (cenum_list, (ceq_list (ceq_option _A1)),
                  (ccompare_list (ccompare_option _A2)),
                  (equal_list (equal_option _A3)))))
            buf []
      then (z, buf)
      else mbufn_take (_A1, _A2, _A3) f (f (map hda buf) z) (map tla buf));;

let rec mbuf2_take
  f x1 = match f, x1 with
    f, (x :: xs, y :: ys) ->
      (let a = mbuf2_take f (xs, ys) in
       let (zs, aa) = a in
        (f x y :: zs, aa))
    | f, ([], ys) -> ([], ([], ys))
    | f, (xs, []) -> ([], (xs, []));;

let rec plus_enat q qa = match q, qa with q, Infinity_enat -> Infinity_enat
                    | Infinity_enat, q -> Infinity_enat
                    | Enat m, Enat n -> Enat (plus_nat m n);;

let rec eval_until
  i nt x2 = match i, nt, x2 with i, nt, [] -> ([], [])
    | i, nt, (t, (a1, a2)) :: aux ->
        (if less_enat (plus_enat (Enat t) (right i)) (Enat nt)
          then (let a = eval_until i nt aux in
                let (xs, aa) = a in
                 (a2 :: xs, aa))
          else ([], (t, (a1, a2)) :: aux));;

let rec mbufn_add xsa xs = map (fun (a, b) -> a @ b) (zip xs xsa);;

let rec mbuf2_add xsa ysa (xs, ys) = (xs @ xsa, ys @ ysa);;

let rec map_split
  f x1 = match f, x1 with f, [] -> ([], [])
    | f, x :: xs -> (let (y, z) = f x in
                     let (ys, zs) = map_split f xs in
                      (y :: ys, z :: zs));;

let rec tabulate
  f x n =
    (if equal_nata n zero_nat then []
      else f x :: tabulate f (suc x) (minus_nat n one_nata));;

let rec singleton_table (_A1, _A2)
  n i x =
    insert ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
      (tabulate (fun j -> (if equal_nata i j then Some x else None)) zero_nat n)
      (set_empty
        ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
        (of_phantom set_impl_lista));;

let rec list_update
  x0 i y = match x0, i, y with [], i, y -> []
    | x :: xs, i, y ->
        (if equal_nata i zero_nat then y :: xs
          else x :: list_update xs (minus_nat i one_nata) y);;

let rec eval_agg (_A1, _A2, _A3, _A4)
  n g0 y omega b f rel =
    (if g0 && is_empty
                (card_UNIV_list, (ceq_list (ceq_option _A1)),
                  (cproper_interval_list (ccompare_option _A2)))
                rel
      then singleton_table (_A1, _A2) n y
             (omega
               (bot_set
                 ((ceq_prod _A1 ceq_enat), (ccompare_prod _A2 ccompare_enat),
                   (set_impl_prod _A4 set_impl_enat))))
      else image ((ceq_list (ceq_option _A1)),
                   (ccompare_list (ccompare_option _A2)))
             ((ceq_list (ceq_option _A1)),
               (ccompare_list (ccompare_option _A2)), set_impl_list)
             (fun k ->
               (let group =
                  filter
                    ((ceq_list (ceq_option _A1)),
                      (ccompare_list (ccompare_option _A2)))
                    (fun x -> equal_lista (equal_option _A3) (drop b x) k) rel
                  in
                let images =
                  image ((ceq_list (ceq_option _A1)),
                          (ccompare_list (ccompare_option _A2)))
                    (_A1, _A2, _A4) (comp f (map_filter id)) group
                  in
                let m =
                  image (_A1, _A2)
                    ((ceq_prod _A1 ceq_enat), (ccompare_prod _A2 ccompare_enat),
                      (set_impl_prod _A4 set_impl_enat))
                    (fun ya ->
                      (ya, ecard (card_UNIV_list, (ceq_list (ceq_option _A1)),
                                   (ccompare_list (ccompare_option _A2)))
                             (filter
                               ((ceq_list (ceq_option _A1)),
                                 (ccompare_list (ccompare_option _A2)))
                               (fun x -> eq _A3 (f (map_filter id x)) ya)
                               group)))
                    images
                  in
                 list_update k y (Some (omega m))))
             (image
               ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2)))
               ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2)), set_impl_list)
               (drop b) rel));;

let rec meval (_A1, _A2, _A3, _A4)
  n t db x3 = match n, t, db, x3 with
    n, t, db, MMatchP (i, mr, mrs, phi_s, buf, nts, aux) ->
      (let (xss, phi_sa) =
         map_split id (map (meval (_A1, _A2, _A3, _A4) n t db) phi_s) in
       let a =
         mbufnt_take (_A1, _A2, _A3)
           (fun rels ta (zs, auxa) ->
             (let a = update_matchP (_A1, _A2, _A3) n i mr mrs rels ta auxa in
              let (z, aa) = a in
               (zs @ [z], aa)))
           ([], aux) (mbufn_add xss buf) (nts @ [t])
         in
       let (aa, b) = a in
        (let (zs, auxa) = aa in
          (fun (bufa, ntsa) ->
            (zs, MMatchP (i, mr, mrs, phi_sa, bufa, ntsa, auxa))))
          b)
    | n, t, db, MUntil (pos, phi, i, psi, buf, nts, aux) ->
        (let (xs, phia) = meval (_A1, _A2, _A3, _A4) n t db phi in
         let (ys, psia) = meval (_A1, _A2, _A3, _A4) n t db psi in
         let (auxa, (bufa, ntsa)) =
           mbuf2t_take (update_until (_A1, _A2, _A3) i pos) aux
             (mbuf2_add xs ys buf) (nts @ [t])
           in
         let (zs, auxb) =
           eval_until i (match ntsa with [] -> t | nt :: _ -> nt) auxa in
          (zs, MUntil (pos, phia, i, psia, bufa, ntsa, auxb)))
    | n, t, db, MSince (pos, phi, i, psi, buf, nts, aux) ->
        (let (xs, phia) = meval (_A1, _A2, _A3, _A4) n t db phi in
         let (ys, psia) = meval (_A1, _A2, _A3, _A4) n t db psi in
         let a =
           mbuf2t_take
             (fun r1 r2 ta (zs, auxa) ->
               (let a = update_since (_A1, _A2, _A3) i pos r1 r2 ta auxa in
                let (z, aa) = a in
                 (zs @ [z], aa)))
             ([], aux) (mbuf2_add xs ys buf) (nts @ [t])
           in
         let (aa, b) = a in
          (let (zs, auxa) = aa in
            (fun (bufa, ntsa) ->
              (zs, MSince (pos, phia, i, psia, bufa, ntsa, auxa))))
            b)
    | n, t, db, MNext (i, phi, first, nts) ->
        (let (xs, phia) = meval (_A1, _A2, _A3, _A4) n t db phi in
         let (xsa, firsta) =
           (match (xs, first) with ([], b) -> ([], b)
             | (_ :: xsa, true) -> (xsa, false)
             | (x :: xsa, false) -> (x :: xsa, false))
           in
         let (zs, (_, ntsa)) = mprev_next (_A1, _A2) i xsa (nts @ [t]) in
          (zs, MNext (i, phia, firsta, ntsa)))
    | n, t, db, MPrev (i, phi, first, buf, nts) ->
        (let (xs, phia) = meval (_A1, _A2, _A3, _A4) n t db phi in
         let (zs, (bufa, ntsa)) = mprev_next (_A1, _A2) i (buf @ xs) (nts @ [t])
           in
          ((if first
             then empty_table
                    ((ceq_list (ceq_option _A1)),
                      (ccompare_list (ccompare_option _A2)), set_impl_list) ::
                    zs
             else zs),
            MPrev (i, phia, false, bufa, ntsa)))
    | n, t, db, MAgg (g0, y, omega, b, f, phi) ->
        (let (xs, phia) = meval (_A1, _A2, _A3, _A4) (plus_nat n b) t db phi in
          (map (eval_agg (_A1, _A2, _A3, _A4) n g0 y omega b f) xs,
            MAgg (g0, y, omega, b, f, phia)))
    | n, t, db, MExists phi ->
        (let (xs, phia) = meval (_A1, _A2, _A3, _A4) (suc n) t db phi in
          (map (image
                 ((ceq_list (ceq_option _A1)),
                   (ccompare_list (ccompare_option _A2)))
                 ((ceq_list (ceq_option _A1)),
                   (ccompare_list (ccompare_option _A2)), set_impl_list)
                 tla)
             xs,
            MExists phia))
    | n, t, db, MNeg phi ->
        (let (xs, phia) = meval (_A1, _A2, _A3, _A4) n t db phi in
          (map (fun r ->
                 (if is_empty
                       (card_UNIV_list, (ceq_list (ceq_option _A1)),
                         (cproper_interval_list (ccompare_option _A2)))
                       r
                   then unit_table (_A1, _A2) n
                   else empty_table
                          ((ceq_list (ceq_option _A1)),
                            (ccompare_list (ccompare_option _A2)),
                            set_impl_list)))
             xs,
            MNeg phia))
    | n, t, db, MOr (phi, psi, buf) ->
        (let (xs, phia) = meval (_A1, _A2, _A3, _A4) n t db phi in
         let (ys, psia) = meval (_A1, _A2, _A3, _A4) n t db psi in
         let (zs, bufa) =
           mbuf2_take
             (sup_seta
               ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2))))
             (mbuf2_add xs ys buf)
           in
          (zs, MOr (phia, psia, bufa)))
    | n, t, db, MAnds (a_pos, a_neg, l, buf) ->
        (let r = map (meval (_A1, _A2, _A3, _A4) n t db) l in
         let bufa = mbufn_add (map fst r) buf in
         let (zs, bufb) =
           mbufn_take (_A1, _A2, _A3)
             (fun xs zs -> zs @ [mmulti_join (_A1, _A2, _A3) a_pos a_neg xs]) []
             bufa
           in
          (zs, MAnds (a_pos, a_neg, map snd r, bufb)))
    | n, t, db, MAnd (phi, pos, psi, buf) ->
        (let (xs, phia) = meval (_A1, _A2, _A3, _A4) n t db phi in
         let (ys, psia) = meval (_A1, _A2, _A3, _A4) n t db psi in
         let (zs, bufa) =
           mbuf2_take (fun r1 -> join (_A1, _A2, _A3) r1 pos)
             (mbuf2_add xs ys buf)
           in
          (zs, MAnd (phia, pos, psia, bufa)))
    | n, t, db, MPred (e, ts) ->
        ([sup_setb
            (finite_UNIV_list, cenum_list, (ceq_list (ceq_option _A1)),
              (cproper_interval_list (ccompare_option _A2)), set_impl_list)
            (image
              ((ceq_prod (ceq_list ceq_char) (ceq_list _A1)),
                (ccompare_prod (ccompare_list ccompare_char)
                  (ccompare_list _A2)))
              ((ceq_set
                 (cenum_list, (ceq_list (ceq_option _A1)),
                   (cproper_interval_list
                     (ccompare_option _A2)).ccompare_cproper_interval)),
                (ccompare_set
                  (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                    (cproper_interval_list (ccompare_option _A2)),
                    set_impl_list)),
                set_impl_set)
              (fun (ea, x) ->
                (if equal_lista equal_char e ea
                  then set_option
                         ((ceq_list (ceq_option _A1)),
                           (ccompare_list (ccompare_option _A2)), set_impl_list)
                         (map_option (fun f -> tabulate f zero_nat n)
                           (matcha _A3 ts x))
                  else set_empty
                         ((ceq_list (ceq_option _A1)),
                           (ccompare_list (ccompare_option _A2)))
                         (of_phantom set_impl_lista)))
              db)],
          MPred (e, ts))
    | n, t, db, MRel rel -> ([rel], MRel rel);;

let rec is_Const = function Var x1 -> false
                   | Const x2 -> true;;

let rec equal_safety x0 x1 = match x0, x1 with Safe, Unsafe -> false
                       | Unsafe, Safe -> false
                       | Unsafe, Unsafe -> true
                       | Safe, Safe -> true;;

let rec eq_set (_A1, _A2, _A3, _A4) = set_eq (_A2, _A3, _A4);;

let rec remove_neg = function Neg phi -> phi
                     | Pred (v, va) -> Pred (v, va)
                     | Eq (v, va) -> Eq (v, va)
                     | Or (v, va) -> Or (v, va)
                     | Ands v -> Ands v
                     | Exists v -> Exists v
                     | Agg (v, va, vb, vc, vd) -> Agg (v, va, vb, vc, vd)
                     | Prev (v, va) -> Prev (v, va)
                     | Next (v, va) -> Next (v, va)
                     | Since (v, va, vb) -> Since (v, va, vb)
                     | Until (v, va, vb) -> Until (v, va, vb)
                     | MatchF (v, va) -> MatchF (v, va)
                     | MatchP (v, va) -> MatchP (v, va);;

let rec partition
  p x1 = match p, x1 with p, [] -> ([], [])
    | p, x :: xs ->
        (let (yes, no) = partition p xs in
          (if p x then (x :: yes, no) else (yes, x :: no)));;

let rec safe_formula (_A1, _A2)
  = function Eq (t1, t2) -> is_Const t1 || is_Const t2
    | Neg (Eq (Const x, Const y)) -> true
    | Neg (Eq (Var x, Var y)) -> equal_nata x y
    | Pred (e, ts) -> true
    | Neg (Or (Neg phi, psi)) ->
        safe_formula (_A1, _A2) phi &&
          (safe_formula (_A1, _A2) psi &&
             subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
               (fvi (_A1, _A2) zero_nat psi) (fvi (_A1, _A2) zero_nat phi) ||
            (match psi with Pred (_, _) -> false | Eq (_, _) -> false
              | Neg a -> safe_formula (_A1, _A2) a | Or (_, _) -> false
              | Ands _ -> false | Exists _ -> false
              | Agg (_, _, _, _, _) -> false | Prev (_, _) -> false
              | Next (_, _) -> false | Since (_, _, _) -> false
              | Until (_, _, _) -> false | MatchF (_, _) -> false
              | MatchP (_, _) -> false))
    | Neg (Pred (v, va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Pred (v, va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Pred (v, va))
    | Neg (Eq (Var vb, Const v)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Eq (Var vb, Const v)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Eq (Var vb, Const v))
    | Neg (Eq (Const va, Var vb)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Eq (Const va, Var vb)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Eq (Const va, Var vb))
    | Neg (Neg v) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Neg v))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Neg v)
    | Neg (Or (Pred (vb, vc), va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (Pred (vb, vc), va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Or (Pred (vb, vc), va))
    | Neg (Or (Eq (vb, vc), va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (Eq (vb, vc), va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Or (Eq (vb, vc), va))
    | Neg (Or (Or (vb, vc), va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (Or (vb, vc), va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Or (Or (vb, vc), va))
    | Neg (Or (Ands vb, va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (Ands vb, va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Or (Ands vb, va))
    | Neg (Or (Exists vb, va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (Exists vb, va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Or (Exists vb, va))
    | Neg (Or (Agg (vb, vc, vd, ve, vf), va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (Agg (vb, vc, vd, ve, vf), va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Or (Agg (vb, vc, vd, ve, vf), va))
    | Neg (Or (Prev (vb, vc), va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (Prev (vb, vc), va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Or (Prev (vb, vc), va))
    | Neg (Or (Next (vb, vc), va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (Next (vb, vc), va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Or (Next (vb, vc), va))
    | Neg (Or (Since (vb, vc, vd), va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (Since (vb, vc, vd), va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Or (Since (vb, vc, vd), va))
    | Neg (Or (Until (vb, vc, vd), va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (Until (vb, vc, vd), va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Or (Until (vb, vc, vd), va))
    | Neg (Or (MatchF (vb, vc), va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (MatchF (vb, vc), va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Or (MatchF (vb, vc), va))
    | Neg (Or (MatchP (vb, vc), va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (MatchP (vb, vc), va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Or (MatchP (vb, vc), va))
    | Neg (Ands v) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Ands v))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Ands v)
    | Neg (Exists v) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Exists v))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Exists v)
    | Neg (Agg (v, va, vb, vc, vd)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Agg (v, va, vb, vc, vd)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Agg (v, va, vb, vc, vd))
    | Neg (Prev (v, va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Prev (v, va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Prev (v, va))
    | Neg (Next (v, va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Next (v, va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Next (v, va))
    | Neg (Since (v, va, vb)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Since (v, va, vb)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Since (v, va, vb))
    | Neg (Until (v, va, vb)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Until (v, va, vb)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (Until (v, va, vb))
    | Neg (MatchF (v, va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (MatchF (v, va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (MatchF (v, va))
    | Neg (MatchP (v, va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (MatchP (v, va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          safe_formula (_A1, _A2) (MatchP (v, va))
    | Or (phi, psi) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat psi) (fvi (_A1, _A2) zero_nat phi) &&
          (safe_formula (_A1, _A2) phi && safe_formula (_A1, _A2) psi)
    | Ands l ->
        (let (pos, neg) = partition (safe_formula (_A1, _A2)) l in
          not (null pos) &&
            (list_all (safe_formula (_A1, _A2)) (map remove_neg neg) &&
              subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
                (sup_setb
                  (finite_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
                    set_impl_nat)
                  (set ((ceq_set
                          (cenum_nat, ceq_nat,
                            cproper_interval_nat.ccompare_cproper_interval)),
                         (ccompare_set
                           (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                             set_impl_nat)),
                         set_impl_set)
                    (map (fvi (_A1, _A2) zero_nat) neg)))
                (sup_setb
                  (finite_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
                    set_impl_nat)
                  (set ((ceq_set
                          (cenum_nat, ceq_nat,
                            cproper_interval_nat.ccompare_cproper_interval)),
                         (ccompare_set
                           (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                             set_impl_nat)),
                         set_impl_set)
                    (map (fvi (_A1, _A2) zero_nat) pos)))))
    | Exists phi -> safe_formula (_A1, _A2) phi
    | Agg (y, omega, b, f, phi) ->
        safe_formula (_A1, _A2) phi &&
          (not (member (ceq_nat, ccompare_nat) (plus_nat y b)
                 (fvi (_A1, _A2) zero_nat phi)) &&
            subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
              (set (ceq_nat, ccompare_nat, set_impl_nat) (upt zero_nat b))
              (fvi (_A1, _A2) zero_nat phi))
    | Prev (i, phi) -> safe_formula (_A1, _A2) phi
    | Next (i, phi) -> safe_formula (_A1, _A2) phi
    | Since (phi, i, psi) ->
        subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat phi) (fvi (_A1, _A2) zero_nat psi) &&
          ((safe_formula (_A1, _A2) phi ||
             (match phi with Pred (_, _) -> false | Eq (_, _) -> false
               | Neg a -> safe_formula (_A1, _A2) a | Or (_, _) -> false
               | Ands _ -> false | Exists _ -> false
               | Agg (_, _, _, _, _) -> false | Prev (_, _) -> false
               | Next (_, _) -> false | Since (_, _, _) -> false
               | Until (_, _, _) -> false | MatchF (_, _) -> false
               | MatchP (_, _) -> false)) &&
            safe_formula (_A1, _A2) psi)
    | Until (phi, i, psi) ->
        subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat phi) (fvi (_A1, _A2) zero_nat psi) &&
          ((safe_formula (_A1, _A2) phi ||
             (match phi with Pred (_, _) -> false | Eq (_, _) -> false
               | Neg a -> safe_formula (_A1, _A2) a | Or (_, _) -> false
               | Ands _ -> false | Exists _ -> false
               | Agg (_, _, _, _, _) -> false | Prev (_, _) -> false
               | Next (_, _) -> false | Since (_, _, _) -> false
               | Until (_, _, _) -> false | MatchF (_, _) -> false
               | MatchP (_, _) -> false)) &&
            safe_formula (_A1, _A2) psi)
    | MatchP (i, r) -> safe_regex (_A1, _A2) Past Safe r
    | MatchF (i, r) -> safe_regex (_A1, _A2) Future Safe r
and safe_regex (_A1, _A2)
  m uu x2 = match m, uu, x2 with m, uu, Wild -> true
    | m, g, Test phi ->
        safe_formula (_A1, _A2) phi ||
          equal_safety g Unsafe &&
            (match phi with Pred (_, _) -> false | Eq (_, _) -> false
              | Neg a -> safe_formula (_A1, _A2) a | Or (_, _) -> false
              | Ands _ -> false | Exists _ -> false
              | Agg (_, _, _, _, _) -> false | Prev (_, _) -> false
              | Next (_, _) -> false | Since (_, _, _) -> false
              | Until (_, _, _) -> false | MatchF (_, _) -> false
              | MatchP (_, _) -> false)
    | m, g, Plus (r, s) ->
        (equal_safety g Unsafe ||
          eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
            (fvi_regex (_A1, _A2) zero_nat r)
            (fvi_regex (_A1, _A2) zero_nat s)) &&
          (safe_regex (_A1, _A2) m g r && safe_regex (_A1, _A2) m g s)
    | Future, g, Times (r, s) ->
        (equal_safety g Unsafe ||
          subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
            (fvi_regex (_A1, _A2) zero_nat r)
            (fvi_regex (_A1, _A2) zero_nat s)) &&
          (safe_regex (_A1, _A2) Future g s &&
            safe_regex (_A1, _A2) Future Unsafe r)
    | Past, g, Times (r, s) ->
        (equal_safety g Unsafe ||
          subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
            (fvi_regex (_A1, _A2) zero_nat s)
            (fvi_regex (_A1, _A2) zero_nat r)) &&
          (safe_regex (_A1, _A2) Past g r &&
            safe_regex (_A1, _A2) Past Unsafe s)
    | m, g, Star r -> equal_safety g Unsafe && safe_regex (_A1, _A2) m g r;;

let rec to_mregex_exec (_A1, _A2)
  x0 xs = match x0, xs with Wild, xs -> (MWild, xs)
    | Test phi, xs ->
        (if safe_formula (_A1, _A2) phi
          then (MTestPos (size_list xs), xs @ [phi])
          else (match phi with Pred (_, _) -> (MEps, xs)
                 | Eq (_, _) -> (MEps, xs)
                 | Neg phia -> (MTestNeg (size_list xs), xs @ [phia])
                 | Or (_, _) -> (MEps, xs) | Ands _ -> (MEps, xs)
                 | Exists _ -> (MEps, xs) | Agg (_, _, _, _, _) -> (MEps, xs)
                 | Prev (_, _) -> (MEps, xs) | Next (_, _) -> (MEps, xs)
                 | Since (_, _, _) -> (MEps, xs) | Until (_, _, _) -> (MEps, xs)
                 | MatchF (_, _) -> (MEps, xs) | MatchP (_, _) -> (MEps, xs)))
    | Plus (r, s), xs ->
        (let (mr, ys) = to_mregex_exec (_A1, _A2) r xs in
         let a = to_mregex_exec (_A1, _A2) s ys in
         let (ms, aa) = a in
          (MPlus (mr, ms), aa))
    | Times (r, s), xs ->
        (let (mr, ys) = to_mregex_exec (_A1, _A2) r xs in
         let a = to_mregex_exec (_A1, _A2) s ys in
         let (ms, aa) = a in
          (MTimes (mr, ms), aa))
    | Star r, xs -> (let a = to_mregex_exec (_A1, _A2) r xs in
                     let (mr, aa) = a in
                      (MStar mr, aa));;

let rec to_mregex (_A1, _A2) r = to_mregex_exec (_A1, _A2) r [];;

let rec neq_rel (_A1, _A2, _A3)
  n x1 x2 = match n, x1, x2 with
    n, Const x, Const y ->
      (if eq _A3 x y
        then empty_table
               ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2)), set_impl_list)
        else unit_table (_A1, _A2) n)
    | n, Var x, Var y ->
        (if equal_nata x y
          then empty_table
                 ((ceq_list (ceq_option _A1)),
                   (ccompare_list (ccompare_option _A2)), set_impl_list)
          else failwith "undefined")
    | uu, Var v, Const va -> failwith "undefined"
    | uu, Const va, Var v -> failwith "undefined";;

let rec eq_rel (_A1, _A2, _A3)
  n x1 x2 = match n, x1, x2 with
    n, Const x, Const y ->
      (if eq _A3 x y then unit_table (_A1, _A2) n
        else empty_table
               ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2)), set_impl_list))
    | n, Var x, Const y -> singleton_table (_A1, _A2) n x y
    | n, Const x, Var y -> singleton_table (_A1, _A2) n y x
    | n, Var x, Var y -> failwith "undefined";;

let rec minit0 (_A1, _A2, _A3)
  n x1 = match n, x1 with
    n, Neg phi ->
      (match phi
        with Pred (list1, list2) ->
          MNeg (minit0 (_A1, _A2, _A3) n (Pred (list1, list2)))
        | Eq (t1, t2) -> MRel (neq_rel (_A1, _A2, _A3) n t1 t2)
        | Neg formula -> MNeg (minit0 (_A1, _A2, _A3) n (Neg formula))
        | Or (Pred (list1, list2), psi) ->
          MNeg (minit0 (_A1, _A2, _A3) n (Or (Pred (list1, list2), psi)))
        | Or (Eq (trm1, trm2), psi) ->
          MNeg (minit0 (_A1, _A2, _A3) n (Or (Eq (trm1, trm2), psi)))
        | Or (Neg phia, psi) ->
          (if safe_formula (_A2, _A3) psi &&
                subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
                  (fvi (_A2, _A3) zero_nat psi) (fvi (_A2, _A3) zero_nat phia)
            then MAnd (minit0 (_A1, _A2, _A3) n phia, false,
                        minit0 (_A1, _A2, _A3) n psi, ([], []))
            else (match psi
                   with Pred (list1, list2) ->
                     MNeg (minit0 (_A1, _A2, _A3) n
                            (Or (Neg phia, Pred (list1, list2))))
                   | Eq (trm1, trm2) ->
                     MNeg (minit0 (_A1, _A2, _A3) n
                            (Or (Neg phia, Eq (trm1, trm2))))
                   | Neg psia ->
                     MAnd (minit0 (_A1, _A2, _A3) n phia, true,
                            minit0 (_A1, _A2, _A3) n psia, ([], []))
                   | Or (formula1, formula2) ->
                     MNeg (minit0 (_A1, _A2, _A3) n
                            (Or (Neg phia, Or (formula1, formula2))))
                   | Ands lista ->
                     MNeg (minit0 (_A1, _A2, _A3) n (Or (Neg phia, Ands lista)))
                   | Exists formula ->
                     MNeg (minit0 (_A1, _A2, _A3) n
                            (Or (Neg phia, Exists formula)))
                   | Agg (nat1, fun1, nat2, fun2, formula) ->
                     MNeg (minit0 (_A1, _A2, _A3) n
                            (Or (Neg phia,
                                  Agg (nat1, fun1, nat2, fun2, formula))))
                   | Prev (i, formula) ->
                     MNeg (minit0 (_A1, _A2, _A3) n
                            (Or (Neg phia, Prev (i, formula))))
                   | Next (i, formula) ->
                     MNeg (minit0 (_A1, _A2, _A3) n
                            (Or (Neg phia, Next (i, formula))))
                   | Since (formula1, i, formula2) ->
                     MNeg (minit0 (_A1, _A2, _A3) n
                            (Or (Neg phia, Since (formula1, i, formula2))))
                   | Until (formula1, i, formula2) ->
                     MNeg (minit0 (_A1, _A2, _A3) n
                            (Or (Neg phia, Until (formula1, i, formula2))))
                   | MatchF (i, regex) ->
                     MNeg (minit0 (_A1, _A2, _A3) n
                            (Or (Neg phia, MatchF (i, regex))))
                   | MatchP (i, regex) ->
                     MNeg (minit0 (_A1, _A2, _A3) n
                            (Or (Neg phia, MatchP (i, regex))))))
        | Or (Or (formula1a, formula2b), psi) ->
          MNeg (minit0 (_A1, _A2, _A3) n (Or (Or (formula1a, formula2b), psi)))
        | Or (Ands lista, psi) ->
          MNeg (minit0 (_A1, _A2, _A3) n (Or (Ands lista, psi)))
        | Or (Exists formula, psi) ->
          MNeg (minit0 (_A1, _A2, _A3) n (Or (Exists formula, psi)))
        | Or (Agg (nat1, fun1, nat2, fun2, formula), psi) ->
          MNeg (minit0 (_A1, _A2, _A3) n
                 (Or (Agg (nat1, fun1, nat2, fun2, formula), psi)))
        | Or (Prev (i, formula), psi) ->
          MNeg (minit0 (_A1, _A2, _A3) n (Or (Prev (i, formula), psi)))
        | Or (Next (i, formula), psi) ->
          MNeg (minit0 (_A1, _A2, _A3) n (Or (Next (i, formula), psi)))
        | Or (Since (formula1a, i, formula2b), psi) ->
          MNeg (minit0 (_A1, _A2, _A3) n
                 (Or (Since (formula1a, i, formula2b), psi)))
        | Or (Until (formula1a, i, formula2b), psi) ->
          MNeg (minit0 (_A1, _A2, _A3) n
                 (Or (Until (formula1a, i, formula2b), psi)))
        | Or (MatchF (i, regex), psi) ->
          MNeg (minit0 (_A1, _A2, _A3) n (Or (MatchF (i, regex), psi)))
        | Or (MatchP (i, regex), psi) ->
          MNeg (minit0 (_A1, _A2, _A3) n (Or (MatchP (i, regex), psi)))
        | Ands lista -> MNeg (minit0 (_A1, _A2, _A3) n (Ands lista))
        | Exists formula -> MNeg (minit0 (_A1, _A2, _A3) n (Exists formula))
        | Agg (nat1, fun1, nat2, fun2, formula) ->
          MNeg (minit0 (_A1, _A2, _A3) n
                 (Agg (nat1, fun1, nat2, fun2, formula)))
        | Prev (i, formula) ->
          MNeg (minit0 (_A1, _A2, _A3) n (Prev (i, formula)))
        | Next (i, formula) ->
          MNeg (minit0 (_A1, _A2, _A3) n (Next (i, formula)))
        | Since (formula1, i, formula2) ->
          MNeg (minit0 (_A1, _A2, _A3) n (Since (formula1, i, formula2)))
        | Until (formula1, i, formula2) ->
          MNeg (minit0 (_A1, _A2, _A3) n (Until (formula1, i, formula2)))
        | MatchF (i, regex) ->
          MNeg (minit0 (_A1, _A2, _A3) n (MatchF (i, regex)))
        | MatchP (i, regex) ->
          MNeg (minit0 (_A1, _A2, _A3) n (MatchP (i, regex))))
    | n, Eq (t1, t2) -> MRel (eq_rel (_A1, _A2, _A3) n t1 t2)
    | n, Pred (e, ts) -> MPred (e, ts)
    | n, Or (phi, psi) ->
        MOr (minit0 (_A1, _A2, _A3) n phi, minit0 (_A1, _A2, _A3) n psi,
              ([], []))
    | n, Ands l ->
        (let (pos, neg) = partition (safe_formula (_A2, _A3)) l in
         let mpos = map (minit0 (_A1, _A2, _A3) n) pos in
         let mneg = map (minit0 (_A1, _A2, _A3) n) (map remove_neg neg) in
         let vpos = map (fvi (_A2, _A3) zero_nat) pos in
         let vneg = map (fvi (_A2, _A3) zero_nat) neg in
          MAnds (vpos, vneg, mpos @ mneg, replicate (size_list l) []))
    | n, Exists phi -> MExists (minit0 (_A1, _A2, _A3) (suc n) phi)
    | n, Agg (y, omega, b, f, phi) ->
        MAgg (subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
                (fvi (_A2, _A3) zero_nat phi)
                (set (ceq_nat, ccompare_nat, set_impl_nat) (upt zero_nat b)),
               y, omega, b, f, minit0 (_A1, _A2, _A3) (plus_nat n b) phi)
    | n, Prev (i, phi) -> MPrev (i, minit0 (_A1, _A2, _A3) n phi, true, [], [])
    | n, Next (i, phi) -> MNext (i, minit0 (_A1, _A2, _A3) n phi, true, [])
    | n, Since (phi, i, psi) ->
        (if safe_formula (_A2, _A3) phi
          then MSince
                 (true, minit0 (_A1, _A2, _A3) n phi, i,
                   minit0 (_A1, _A2, _A3) n psi, ([], []), [], [])
          else (let Neg phia = phi in
                 MSince
                   (false, minit0 (_A1, _A2, _A3) n phia, i,
                     minit0 (_A1, _A2, _A3) n psi, ([], []), [], [])))
    | n, Until (phi, i, psi) ->
        (if safe_formula (_A2, _A3) phi
          then MUntil
                 (true, minit0 (_A1, _A2, _A3) n phi, i,
                   minit0 (_A1, _A2, _A3) n psi, ([], []), [], [])
          else (let Neg phia = phi in
                 MUntil
                   (false, minit0 (_A1, _A2, _A3) n phia, i,
                     minit0 (_A1, _A2, _A3) n psi, ([], []), [], [])))
    | n, MatchP (i, r) ->
        (let (mr, phi_s) = to_mregex (_A2, _A3) r in
          MMatchP
            (i, mr,
              sorted_list_of_set
                (ceq_mregex, ccompare_mregex, equal_mregex, linorder_mregex)
                (rPDs mr),
              map (minit0 (_A1, _A2, _A3) n) phi_s,
              replicate (size_list phi_s) [], [], []))
    | n, MatchF (i, r) ->
        (let (mr, phi_s) = to_mregex (_A2, _A3) r in
          MMatchF
            (i, mr,
              sorted_list_of_set
                (ceq_mregex, ccompare_mregex, equal_mregex, linorder_mregex)
                (lPDs mr),
              map (minit0 (_A1, _A2, _A3) n) phi_s,
              replicate (size_list phi_s) [], [], []));;

let rec minit (_A1, _A2, _A3)
  phi = (let n = nfv (_A2, _A3) phi in
          Mstate_ext (zero_nat, minit0 (_A1, _A2, _A3) n phi, n, ()));;

let rec mstate_n (Mstate_ext (mstate_i, mstate_m, mstate_n, more)) = mstate_n;;

let rec mstate_m (Mstate_ext (mstate_i, mstate_m, mstate_n, more)) = mstate_m;;

let rec mstate_i (Mstate_ext (mstate_i, mstate_m, mstate_n, more)) = mstate_i;;

let rec enumerate
  n x1 = match n, x1 with n, x :: xs -> (n, x) :: enumerate (suc n) xs
    | n, [] -> [];;

let rec mstep (_A1, _A2, _A3, _A4)
  tdb st =
    (let (xs, m) =
       meval (_A1, _A2, _A3, _A4) (mstate_n st) (snd tdb) (fst tdb)
         (mstate_m st)
       in
      (sup_setb
         ((finite_UNIV_prod finite_UNIV_nat finite_UNIV_list),
           (cenum_prod cenum_nat cenum_list),
           (ceq_prod ceq_nat (ceq_list (ceq_option _A1))),
           (cproper_interval_prod cproper_interval_nat
             (cproper_interval_list (ccompare_option _A2))),
           (set_impl_prod set_impl_nat set_impl_list))
         (set ((ceq_set
                 ((cenum_prod cenum_nat cenum_list),
                   (ceq_prod ceq_nat (ceq_list (ceq_option _A1))),
                   (cproper_interval_prod cproper_interval_nat
                     (cproper_interval_list
                       (ccompare_option _A2))).ccompare_cproper_interval)),
                (ccompare_set
                  ((finite_UNIV_prod finite_UNIV_nat finite_UNIV_list),
                    (ceq_prod ceq_nat (ceq_list (ceq_option _A1))),
                    (cproper_interval_prod cproper_interval_nat
                      (cproper_interval_list (ccompare_option _A2))),
                    (set_impl_prod set_impl_nat set_impl_list))),
                set_impl_set)
           (map (fun (i, a) ->
                  image ((ceq_list (ceq_option _A1)),
                          (ccompare_list (ccompare_option _A2)))
                    ((ceq_prod ceq_nat (ceq_list (ceq_option _A1))),
                      (ccompare_prod ccompare_nat
                        (ccompare_list (ccompare_option _A2))),
                      (set_impl_prod set_impl_nat set_impl_list))
                    (fun aa -> (i, aa)) a)
             (enumerate (mstate_i st) xs))),
        Mstate_ext
          (plus_nat (mstate_i st) (size_list xs), m, mstate_n st, ())));;

let rec interval
  l r = Abs_I (if less_eq_enat (Enat l) r then (l, r)
                else rep_I (failwith "undefined"));;

let rec mmonitorable_exec (_A1, _A2)
  = function Eq (t1, t2) -> is_Const t1 || is_Const t2
    | Neg (Eq (Const x, Const y)) -> true
    | Neg (Eq (Var x, Var y)) -> equal_nata x y
    | Pred (e, ts) -> true
    | Neg (Or (Neg phi, psi)) ->
        mmonitorable_exec (_A1, _A2) phi &&
          (mmonitorable_exec (_A1, _A2) psi &&
             subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
               (fvi (_A1, _A2) zero_nat psi) (fvi (_A1, _A2) zero_nat phi) ||
            (match psi with Pred (_, _) -> false | Eq (_, _) -> false
              | Neg a -> mmonitorable_exec (_A1, _A2) a | Or (_, _) -> false
              | Ands _ -> false | Exists _ -> false
              | Agg (_, _, _, _, _) -> false | Prev (_, _) -> false
              | Next (_, _) -> false | Since (_, _, _) -> false
              | Until (_, _, _) -> false | MatchF (_, _) -> false
              | MatchP (_, _) -> false))
    | Or (phi, psi) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat psi) (fvi (_A1, _A2) zero_nat phi) &&
          (mmonitorable_exec (_A1, _A2) phi && mmonitorable_exec (_A1, _A2) psi)
    | Ands l ->
        (let (pos, neg) = partition (mmonitorable_exec (_A1, _A2)) l in
          not (null pos) &&
            (list_all (mmonitorable_exec (_A1, _A2)) (map remove_neg neg) &&
              subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
                (sup_setb
                  (finite_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
                    set_impl_nat)
                  (set ((ceq_set
                          (cenum_nat, ceq_nat,
                            cproper_interval_nat.ccompare_cproper_interval)),
                         (ccompare_set
                           (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                             set_impl_nat)),
                         set_impl_set)
                    (map (fvi (_A1, _A2) zero_nat) neg)))
                (sup_setb
                  (finite_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
                    set_impl_nat)
                  (set ((ceq_set
                          (cenum_nat, ceq_nat,
                            cproper_interval_nat.ccompare_cproper_interval)),
                         (ccompare_set
                           (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                             set_impl_nat)),
                         set_impl_set)
                    (map (fvi (_A1, _A2) zero_nat) pos)))))
    | Neg (Pred (v, va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Pred (v, va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Pred (v, va))
    | Neg (Eq (Var vb, Const v)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Eq (Var vb, Const v)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Eq (Var vb, Const v))
    | Neg (Eq (Const va, Var vb)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Eq (Const va, Var vb)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Eq (Const va, Var vb))
    | Neg (Neg v) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Neg v))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Neg v)
    | Neg (Or (Pred (vb, vc), va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (Pred (vb, vc), va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Or (Pred (vb, vc), va))
    | Neg (Or (Eq (vb, vc), va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (Eq (vb, vc), va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Or (Eq (vb, vc), va))
    | Neg (Or (Or (vb, vc), va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (Or (vb, vc), va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Or (Or (vb, vc), va))
    | Neg (Or (Ands vb, va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (Ands vb, va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Or (Ands vb, va))
    | Neg (Or (Exists vb, va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (Exists vb, va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Or (Exists vb, va))
    | Neg (Or (Agg (vb, vc, vd, ve, vf), va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (Agg (vb, vc, vd, ve, vf), va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Or (Agg (vb, vc, vd, ve, vf), va))
    | Neg (Or (Prev (vb, vc), va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (Prev (vb, vc), va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Or (Prev (vb, vc), va))
    | Neg (Or (Next (vb, vc), va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (Next (vb, vc), va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Or (Next (vb, vc), va))
    | Neg (Or (Since (vb, vc, vd), va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (Since (vb, vc, vd), va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Or (Since (vb, vc, vd), va))
    | Neg (Or (Until (vb, vc, vd), va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (Until (vb, vc, vd), va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Or (Until (vb, vc, vd), va))
    | Neg (Or (MatchF (vb, vc), va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (MatchF (vb, vc), va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Or (MatchF (vb, vc), va))
    | Neg (Or (MatchP (vb, vc), va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Or (MatchP (vb, vc), va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Or (MatchP (vb, vc), va))
    | Neg (Ands v) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Ands v))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Ands v)
    | Neg (Exists v) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Exists v))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Exists v)
    | Neg (Agg (v, va, vb, vc, vd)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Agg (v, va, vb, vc, vd)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Agg (v, va, vb, vc, vd))
    | Neg (Prev (v, va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Prev (v, va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Prev (v, va))
    | Neg (Next (v, va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Next (v, va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Next (v, va))
    | Neg (Since (v, va, vb)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Since (v, va, vb)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Since (v, va, vb))
    | Neg (Until (v, va, vb)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (Until (v, va, vb)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (Until (v, va, vb))
    | Neg (MatchF (v, va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (MatchF (v, va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (MatchF (v, va))
    | Neg (MatchP (v, va)) ->
        eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat (MatchP (v, va)))
          (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)) &&
          mmonitorable_exec (_A1, _A2) (MatchP (v, va))
    | Exists phi -> mmonitorable_exec (_A1, _A2) phi
    | Agg (y, omega, b, f, phi) ->
        mmonitorable_exec (_A1, _A2) phi &&
          (not (member (ceq_nat, ccompare_nat) (plus_nat y b)
                 (fvi (_A1, _A2) zero_nat phi)) &&
            subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
              (set (ceq_nat, ccompare_nat, set_impl_nat) (upt zero_nat b))
              (fvi (_A1, _A2) zero_nat phi))
    | Prev (i, phi) -> mmonitorable_exec (_A1, _A2) phi
    | Next (i, phi) ->
        mmonitorable_exec (_A1, _A2) phi &&
          not (equal_enat (right i) Infinity_enat)
    | Since (phi, i, psi) ->
        subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat phi) (fvi (_A1, _A2) zero_nat psi) &&
          ((mmonitorable_exec (_A1, _A2) phi ||
             (match phi with Pred (_, _) -> false | Eq (_, _) -> false
               | Neg a -> mmonitorable_exec (_A1, _A2) a | Or (_, _) -> false
               | Ands _ -> false | Exists _ -> false
               | Agg (_, _, _, _, _) -> false | Prev (_, _) -> false
               | Next (_, _) -> false | Since (_, _, _) -> false
               | Until (_, _, _) -> false | MatchF (_, _) -> false
               | MatchP (_, _) -> false)) &&
            mmonitorable_exec (_A1, _A2) psi)
    | Until (phi, i, psi) ->
        subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat phi) (fvi (_A1, _A2) zero_nat psi) &&
          (not (equal_enat (right i) Infinity_enat) &&
            ((mmonitorable_exec (_A1, _A2) phi ||
               (match phi with Pred (_, _) -> false | Eq (_, _) -> false
                 | Neg a -> mmonitorable_exec (_A1, _A2) a | Or (_, _) -> false
                 | Ands _ -> false | Exists _ -> false
                 | Agg (_, _, _, _, _) -> false | Prev (_, _) -> false
                 | Next (_, _) -> false | Since (_, _, _) -> false
                 | Until (_, _, _) -> false | MatchF (_, _) -> false
                 | MatchP (_, _) -> false)) &&
              mmonitorable_exec (_A1, _A2) psi))
    | MatchP (i, r) -> mmonitorable_regex_exec (_A1, _A2) Past Safe r
    | MatchF (i, r) ->
        mmonitorable_regex_exec (_A1, _A2) Future Safe r &&
          not (equal_enat (right i) Infinity_enat)
and mmonitorable_regex_exec (_A1, _A2)
  b g x2 = match b, g, x2 with b, g, Wild -> true
    | b, g, Test phi ->
        mmonitorable_exec (_A1, _A2) phi ||
          equal_safety g Unsafe &&
            (match phi with Pred (_, _) -> false | Eq (_, _) -> false
              | Neg a -> mmonitorable_exec (_A1, _A2) a | Or (_, _) -> false
              | Ands _ -> false | Exists _ -> false
              | Agg (_, _, _, _, _) -> false | Prev (_, _) -> false
              | Next (_, _) -> false | Since (_, _, _) -> false
              | Until (_, _, _) -> false | MatchF (_, _) -> false
              | MatchP (_, _) -> false)
    | b, g, Plus (r, s) ->
        (equal_safety g Unsafe ||
          eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
            (fvi_regex (_A1, _A2) zero_nat r)
            (fvi_regex (_A1, _A2) zero_nat s)) &&
          (mmonitorable_regex_exec (_A1, _A2) b g r &&
            mmonitorable_regex_exec (_A1, _A2) b g s)
    | Future, g, Times (r, s) ->
        (equal_safety g Unsafe ||
          subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
            (fvi_regex (_A1, _A2) zero_nat r)
            (fvi_regex (_A1, _A2) zero_nat s)) &&
          (mmonitorable_regex_exec (_A1, _A2) Future Unsafe r &&
            mmonitorable_regex_exec (_A1, _A2) Future g s)
    | Past, g, Times (r, s) ->
        (equal_safety g Unsafe ||
          subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
            (fvi_regex (_A1, _A2) zero_nat s)
            (fvi_regex (_A1, _A2) zero_nat r)) &&
          (mmonitorable_regex_exec (_A1, _A2) Past g r &&
            mmonitorable_regex_exec (_A1, _A2) Past Unsafe s)
    | b, g, Star r ->
        equal_safety g Unsafe && mmonitorable_regex_exec (_A1, _A2) b g r;;

let rec minit_safe (_A1, _A2, _A3)
  phi = (if mmonitorable_exec (_A2, _A3) phi then minit (_A1, _A2, _A3) phi
          else failwith "undefined");;

let rec mk_db (_A1, _A2)
  = set ((ceq_prod (ceq_list ceq_char) (ceq_list _A1)),
          (ccompare_prod (ccompare_list ccompare_char) (ccompare_list _A2)),
          (set_impl_prod set_impl_list set_impl_list));;

let rec get_or_list
  = function Or (phi, psi) -> get_or_list phi @ get_or_list psi
    | Pred (v, va) -> [Pred (v, va)]
    | Eq (v, va) -> [Eq (v, va)]
    | Neg v -> [Neg v]
    | Ands v -> [Ands v]
    | Exists v -> [Exists v]
    | Agg (v, va, vb, vc, vd) -> [Agg (v, va, vb, vc, vd)]
    | Prev (v, va) -> [Prev (v, va)]
    | Next (v, va) -> [Next (v, va)]
    | Since (v, va, vb) -> [Since (v, va, vb)]
    | Until (v, va, vb) -> [Until (v, va, vb)]
    | MatchF (v, va) -> [MatchF (v, va)]
    | MatchP (v, va) -> [MatchP (v, va)];;

let rec get_and_list (_A1, _A2)
  = function Ands l -> l
    | Neg phi ->
        (if safe_formula (_A1, _A2) (Neg phi) then [Neg phi]
          else map (fun a -> Neg a) (get_or_list phi))
    | Pred (v, va) -> [Pred (v, va)]
    | Eq (v, va) -> [Eq (v, va)]
    | Or (v, va) -> [Or (v, va)]
    | Exists v -> [Exists v]
    | Agg (v, va, vb, vc, vd) -> [Agg (v, va, vb, vc, vd)]
    | Prev (v, va) -> [Prev (v, va)]
    | Next (v, va) -> [Next (v, va)]
    | Since (v, va, vb) -> [Since (v, va, vb)]
    | Until (v, va, vb) -> [Until (v, va, vb)]
    | MatchF (v, va) -> [MatchF (v, va)]
    | MatchP (v, va) -> [MatchP (v, va)];;

let rec is_Neg = function Pred (x11, x12) -> false
                 | Eq (x21, x22) -> false
                 | Neg x3 -> true
                 | Or (x41, x42) -> false
                 | Ands x5 -> false
                 | Exists x6 -> false
                 | Agg (x71, x72, x73, x74, x75) -> false
                 | Prev (x81, x82) -> false
                 | Next (x91, x92) -> false
                 | Since (x101, x102, x103) -> false
                 | Until (x111, x112, x113) -> false
                 | MatchF (x121, x122) -> false
                 | MatchP (x131, x132) -> false;;

let rec un_Neg (Neg x3) = x3;;

let rec bit_cut_integer
  k = (if Z.equal k Z.zero then (Z.zero, false)
        else (let (r, s) =
                (fun k l -> if Z.equal Z.zero l then (Z.zero, l) else Z.div_rem
                  (Z.abs k) (Z.abs l))
                  k (Z.of_int 2)
                in
               ((if Z.lt Z.zero k then r else Z.sub (Z.neg r) s),
                 Z.equal s (Z.of_int 1))));;

let rec char_of_integer
  k = (let (q0, b0) = bit_cut_integer k in
       let (q1, b1) = bit_cut_integer q0 in
       let (q2, b2) = bit_cut_integer q1 in
       let (q3, b3) = bit_cut_integer q2 in
       let (q4, b4) = bit_cut_integer q3 in
       let (q5, b5) = bit_cut_integer q4 in
       let (q6, b6) = bit_cut_integer q5 in
       let a = bit_cut_integer q6 in
       let (_, aa) = a in
        Chara (b0, b1, b2, b3, b4, b5, b6, aa));;

let rec explode
  s = map char_of_integer
        (let s = s in let rec exp i l = if i < 0 then l else exp (i - 1) (let k = Char.code (String.get s i) in
      if k < 128 then Z.of_int k :: l else failwith "Non-ASCII character in literal") in exp (String.length s - 1) []);;

let rec convert_multiway (_A1, _A2)
  = function
    Neg phi ->
      (if eq_set (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
            (fvi (_A1, _A2) zero_nat phi)
            (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata))
        then Neg phi
        else (match phi with Pred (_, _) -> Neg phi | Eq (_, _) -> Neg phi
               | Neg _ -> Neg phi | Or (Pred (_, _), _) -> Neg phi
               | Or (Eq (_, _), _) -> Neg phi
               | Or (Neg alpha, beta) ->
                 (let a =
                    get_and_list (_A1, _A2) (convert_multiway (_A1, _A2) alpha)
                    in
                  let b =
                    (if is_Neg beta && safe_formula (_A1, _A2) (un_Neg beta)
                      then (let Neg betaa = beta in
                             get_and_list (_A1, _A2)
                               (convert_multiway (_A1, _A2) betaa))
                      else map (fun aa -> Neg aa)
                             (get_or_list (convert_multiway (_A1, _A2) beta)))
                    in
                   Ands (a @ b))
               | Or (Or (_, _), _) -> Neg phi | Or (Ands _, _) -> Neg phi
               | Or (Exists _, _) -> Neg phi
               | Or (Agg (_, _, _, _, _), _) -> Neg phi
               | Or (Prev (_, _), _) -> Neg phi | Or (Next (_, _), _) -> Neg phi
               | Or (Since (_, _, _), _) -> Neg phi
               | Or (Until (_, _, _), _) -> Neg phi
               | Or (MatchF (_, _), _) -> Neg phi
               | Or (MatchP (_, _), _) -> Neg phi | Ands _ -> Neg phi
               | Exists _ -> Neg phi | Agg (_, _, _, _, _) -> Neg phi
               | Prev (_, _) -> Neg phi | Next (_, _) -> Neg phi
               | Since (_, _, _) -> Neg phi | Until (_, _, _) -> Neg phi
               | MatchF (_, _) -> Neg phi | MatchP (_, _) -> Neg phi))
    | Or (phi, psi) ->
        Or (convert_multiway (_A1, _A2) phi, convert_multiway (_A1, _A2) psi)
    | Exists phi -> Exists (convert_multiway (_A1, _A2) phi)
    | Agg (y, omega, b, f, phi) ->
        Agg (y, omega, b, f, convert_multiway (_A1, _A2) phi)
    | Prev (r, phi) -> Prev (r, convert_multiway (_A1, _A2) phi)
    | Next (r, phi) -> Next (r, convert_multiway (_A1, _A2) phi)
    | Since (phi, r, psi) ->
        (if safe_formula (_A1, _A2) phi
          then Since (convert_multiway (_A1, _A2) phi, r,
                       convert_multiway (_A1, _A2) psi)
          else (let Neg phia = phi in
                 Since (Neg (convert_multiway (_A1, _A2) phia), r,
                         convert_multiway (_A1, _A2) psi)))
    | Until (phi, r, psi) ->
        (if safe_formula (_A1, _A2) phi
          then Until (convert_multiway (_A1, _A2) phi, r,
                       convert_multiway (_A1, _A2) psi)
          else (let Neg phia = phi in
                 Until (Neg (convert_multiway (_A1, _A2) phia), r,
                         convert_multiway (_A1, _A2) psi)))
    | MatchP (i, r) -> MatchP (i, convert_multiway_regex (_A1, _A2) r)
    | MatchF (i, r) -> MatchF (i, convert_multiway_regex (_A1, _A2) r)
    | Pred (v, va) -> Pred (v, va)
    | Eq (v, va) -> Eq (v, va)
    | Ands v -> Ands v
and convert_multiway_regex (_A1, _A2)
  = function Wild -> Wild
    | Test phi ->
        (if safe_formula (_A1, _A2) phi
          then Test (convert_multiway (_A1, _A2) phi)
          else (let Neg phia = phi in
                 Test (Neg (convert_multiway (_A1, _A2) phia))))
    | Plus (r, s) ->
        Plus (convert_multiway_regex (_A1, _A2) r,
               convert_multiway_regex (_A1, _A2) s)
    | Times (r, s) ->
        Times (convert_multiway_regex (_A1, _A2) r,
                convert_multiway_regex (_A1, _A2) s)
    | Star r -> Star (convert_multiway_regex (_A1, _A2) r);;

let rec rbt_verdict _A
  = keysa (ccompare_prod ccompare_nat (ccompare_list (ccompare_option _A)));;

let rec rbt_multiset _A = keysa (ccompare_prod _A ccompare_enat);;

end;; (*struct Monitor*)
