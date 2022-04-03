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

module FloatUtil : sig
  val iszero : float -> bool
  val isinfinite : float -> bool
  val isnan : float -> bool
  val copysign : float -> float -> float
  val compare : float -> float -> Z.t
end = struct
  let iszero x = (Stdlib.classify_float x = Stdlib.FP_zero);;
  let isinfinite x = (Stdlib.classify_float x = Stdlib.FP_infinite);;
  let isnan x = (Stdlib.classify_float x = Stdlib.FP_nan);;
  let copysign x y = if isnan y then Stdlib.nan else Stdlib.copysign x y;;
  let compare x y = Z.of_int (Stdlib.compare x y);;
end;;

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
  type ('a, 'b) phantom
  type set_impla
  type nat
  val integer_of_nat : nat -> Z.t
  type mapping_impla
  type 'a set_dlist
  type ('b, 'a) mapping_rbt
  type 'a set = Collect_set of ('a -> bool) | DList_set of 'a set_dlist |
    RBT_set of ('a, unit) mapping_rbt | Set_Monad of 'a list |
    Complement of 'a set
  val nat_of_integer : Z.t -> nat
  type event_data = EInt of Z.t | EFloat of float | EString of string
  type trm = Var of nat | Const of event_data | Plus of trm * trm |
    Minus of trm * trm | UMinus of trm | Mult of trm * trm | Div of trm * trm |
    Mod of trm * trm | F2i of trm | I2f of trm
  type enat = Enat of nat | Infinity_enat
  type rec_safety
  type agg_type = Agg_Cnt | Agg_Min | Agg_Max | Agg_Sum | Agg_Avg | Agg_Med
  type ty = TInt | TFloat | TString
  type i
  type 'a queue
  type ('a, 'b) mapping
  type int = Int_of_integer of Z.t
  type 'a regex = Skip of nat | Test of 'a | Plusa of 'a regex * 'a regex |
    Times of 'a regex * 'a regex | Star of 'a regex
  type safety
  type ('a, 'b) sum = Inl of 'a | Inr of 'b
  type tysym = TAny of nat | TNum of nat | TCst of ty
  type modality
  type 'a formula = Pred of string * trm list |
    Let of string * 'a formula * 'a formula |
    LetPast of string * 'a formula * 'a formula | Eq of trm * trm |
    Less of trm * trm | LessEq of trm * trm | Neg of 'a formula |
    Or of 'a formula * 'a formula | And of 'a formula * 'a formula |
    Ands of 'a formula list | Exists of 'a * 'a formula |
    Agg of nat * (agg_type * 'a) * 'a list * trm * 'a formula |
    Prev of i * 'a formula | Next of i * 'a formula |
    Since of 'a formula * i * 'a formula | Until of 'a formula * i * 'a formula
    | MatchF of i * 'a formula regex | MatchP of i * 'a formula regex |
    TP of trm | TS of trm
  type ('a, 'b) mformula
  type 'a wf_table
  type aggaux
  type ('a, 'b, 'c) mstate_ext
  val wild : 'a regex
  val integer_of_int : int -> Z.t
  val interval : nat -> enat -> i
  val type_check :
    (string * nat -> (tysym list) option) ->
      tysym formula -> (string, ty formula) sum
  val mstep :
    ((string * nat), (((event_data option) list) set list)) mapping * nat ->
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
        mstate_ext ->
        (nat * (nat * ((event_data option) list) set)) list *
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
  val empty_db : ((string * nat), (((event_data option) list) set list)) mapping
  val rbt_fold :
    ((event_data option) list -> 'a -> 'a) ->
      (((event_data option) list), unit) mapping_rbt -> 'a -> 'a
  val mmonitorable_exec : 'a formula -> bool
  val minit_safe :
    ty formula ->
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
  val convert_multiway : 'a formula -> 'a formula
  val insert_into_db :
    string * nat ->
      (event_data option) list ->
        ((string * nat), (((event_data option) list) set list)) mapping ->
          ((string * nat), (((event_data option) list) set list)) mapping
end = struct

let ceq_funa : (('a -> 'b) -> ('a -> 'b) -> bool) option = None;;

type 'a ceq = {ceq : ('a -> 'a -> bool) option};;
let ceq _A = _A.ceq;;

let ceq_fun = ({ceq = ceq_funa} : ('a -> 'b) ceq);;

type ('a, 'b) phantom = Phantom of 'b;;

type set_impla = Set_Choose | Set_Collect | Set_DList | Set_RBT | Set_Monada;;

let set_impl_funa : (('a -> 'b), set_impla) phantom = Phantom Set_Monada;;

type 'a set_impl = {set_impl : ('a, set_impla) phantom};;
let set_impl _A = _A.set_impl;;

let set_impl_fun = ({set_impl = set_impl_funa} : ('a -> 'b) set_impl);;

type ordera = Eqa | Lt | Gt;;

let ccompare_funa : (('a -> 'b) -> ('a -> 'b) -> ordera) option = None;;

type 'a ccompare = {ccompare : ('a -> 'a -> ordera) option};;
let ccompare _A = _A.ccompare;;

let ccompare_fun = ({ccompare = ccompare_funa} : ('a -> 'b) ccompare);;

type nat = Nat of Z.t;;

let rec integer_of_nat (Nat x) = x;;

let rec equal_nata m n = Z.equal (integer_of_nat m) (integer_of_nat n);;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_nat = ({equal = equal_nata} : nat equal);;

let rec times_nata m n = Nat (Z.mul (integer_of_nat m) (integer_of_nat n));;

type 'a times = {times : 'a -> 'a -> 'a};;
let times _A = _A.times;;

type 'a dvd = {times_dvd : 'a times};;

let times_nat = ({times = times_nata} : nat times);;

let dvd_nat = ({times_dvd = times_nat} : nat dvd);;

type num = One | Bit0 of num | Bit1 of num;;

let one_nata : nat = Nat (Z.of_int 1);;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_nat = ({one = one_nata} : nat one);;

let rec plus_nata m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

let plus_nat = ({plus = plus_nata} : nat plus);;

let zero_nata : nat = Nat Z.zero;;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

let zero_nat = ({zero = zero_nata} : nat zero);;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};;

type 'a numeral =
  {one_numeral : 'a one; semigroup_add_numeral : 'a semigroup_add};;

let semigroup_add_nat = ({plus_semigroup_add = plus_nat} : nat semigroup_add);;

let numeral_nat =
  ({one_numeral = one_nat; semigroup_add_numeral = semigroup_add_nat} :
    nat numeral);;

type 'a power = {one_power : 'a one; times_power : 'a times};;

let power_nat = ({one_power = one_nat; times_power = times_nat} : nat power);;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec max _A a b = (if less_eq _A a b then b else a);;

let ord_integer = ({less_eq = Z.leq; less = Z.lt} : Z.t ord);;

let rec minus_nata
  m n = Nat (max ord_integer Z.zero
              (Z.sub (integer_of_nat m) (integer_of_nat n)));;

type 'a minus = {minusa : 'a -> 'a -> 'a};;
let minusa _A = _A.minusa;;

let minus_nat = ({minusa = minus_nata} : nat minus);;

let rec min _A a b = (if less_eq _A a b then a else b);;

let rec less_eq_nat m n = Z.leq (integer_of_nat m) (integer_of_nat n);;

let rec less_nat m n = Z.lt (integer_of_nat m) (integer_of_nat n);;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

let rec inf_nata x = min ord_nat x;;

type 'a inf = {inf : 'a -> 'a -> 'a};;
let inf _A = _A.inf;;

let inf_nat = ({inf = inf_nata} : nat inf);;

let rec sup_nata x = max ord_nat x;;

type 'a sup = {sup : 'a -> 'a -> 'a};;
let sup _A = _A.sup;;

let sup_nat = ({sup = sup_nata} : nat sup);;

let rec apsnd f (x, y) = (x, f y);;

let rec divmod_integer
  k l = (if Z.equal k Z.zero then (Z.zero, Z.zero)
          else (if Z.lt Z.zero l
                 then (if Z.lt Z.zero k
                        then (fun k l -> if Z.equal Z.zero l then
                               (Z.zero, l) else Z.div_rem (Z.abs k) (Z.abs l))
                               k l
                        else (let (r, s) =
                                (fun k l -> if Z.equal Z.zero l then
                                  (Z.zero, l) else Z.div_rem (Z.abs k)
                                  (Z.abs l))
                                  k l
                                in
                               (if Z.equal s Z.zero then (Z.neg r, Z.zero)
                                 else (Z.sub (Z.neg r) (Z.of_int 1),
Z.sub l s))))
                 else (if Z.equal l Z.zero then (Z.zero, k)
                        else apsnd Z.neg
                               (if Z.lt k Z.zero
                                 then (fun k l -> if Z.equal Z.zero l then
(Z.zero, l) else Z.div_rem (Z.abs k) (Z.abs l))
k l
                                 else (let (r, s) =
 (fun k l -> if Z.equal Z.zero l then (Z.zero, l) else Z.div_rem (Z.abs k)
   (Z.abs l))
   k l
 in
(if Z.equal s Z.zero then (Z.neg r, Z.zero)
  else (Z.sub (Z.neg r) (Z.of_int 1), Z.sub (Z.neg l) s)))))));;

let rec fst (x1, x2) = x1;;

let rec divide_integer k l = fst (divmod_integer k l);;

let rec divide_nata
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

type 'a divide = {divide : 'a -> 'a -> 'a};;
let divide _A = _A.divide;;

let divide_nat = ({divide = divide_nata} : nat divide);;

let rec snd (x1, x2) = x2;;

let rec modulo_integer k l = snd (divmod_integer k l);;

let rec modulo_nata
  m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));;

type 'a modulo =
  {divide_modulo : 'a divide; dvd_modulo : 'a dvd; modulo : 'a -> 'a -> 'a};;
let modulo _A = _A.modulo;;

let modulo_nat =
  ({divide_modulo = divide_nat; dvd_modulo = dvd_nat; modulo = modulo_nata} :
    nat modulo);;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero};;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add;
    monoid_add_comm_monoid_add : 'a monoid_add};;

type 'a mult_zero = {times_mult_zero : 'a times; zero_mult_zero : 'a zero};;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add;
    semigroup_mult_semiring : 'a semigroup_mult};;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add;
    mult_zero_semiring_0 : 'a mult_zero; semiring_semiring_0 : 'a semiring};;

type 'a semiring_no_zero_divisors =
  {semiring_0_semiring_no_zero_divisors : 'a semiring_0};;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult;
    power_monoid_mult : 'a power};;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult;
    numeral_semiring_numeral : 'a numeral;
    semiring_semiring_numeral : 'a semiring};;

type 'a zero_neq_one =
  {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero};;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral;
    semiring_0_semiring_1 : 'a semiring_0;
    zero_neq_one_semiring_1 : 'a zero_neq_one};;

type 'a semiring_1_no_zero_divisors =
  {semiring_1_semiring_1_no_zero_divisors : 'a semiring_1;
    semiring_no_zero_divisors_semiring_1_no_zero_divisors :
      'a semiring_no_zero_divisors};;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add;
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add;
    minus_cancel_ab_semigroup_add : 'a minus};;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add;
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};;

type 'a semiring_0_cancel =
  {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add;
    semiring_0_semiring_0_cancel : 'a semiring_0};;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult;
    semiring_comm_semiring : 'a semiring};;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring;
    semiring_0_comm_semiring_0 : 'a semiring_0};;

type 'a comm_semiring_0_cancel =
  {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0;
    semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};;

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel;
    semiring_1_semiring_1_cancel : 'a semiring_1};;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult;
    monoid_mult_comm_monoid_mult : 'a monoid_mult;
    dvd_comm_monoid_mult : 'a dvd};;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult;
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0;
    semiring_1_comm_semiring_1 : 'a semiring_1};;

type 'a comm_semiring_1_cancel =
  {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel;
    comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1;
    semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel};;

type 'a semidom =
  {comm_semiring_1_cancel_semidom : 'a comm_semiring_1_cancel;
    semiring_1_no_zero_divisors_semidom : 'a semiring_1_no_zero_divisors};;

let ab_semigroup_add_nat =
  ({semigroup_add_ab_semigroup_add = semigroup_add_nat} :
    nat ab_semigroup_add);;

let monoid_add_nat =
  ({semigroup_add_monoid_add = semigroup_add_nat; zero_monoid_add = zero_nat} :
    nat monoid_add);;

let comm_monoid_add_nat =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_nat;
     monoid_add_comm_monoid_add = monoid_add_nat}
    : nat comm_monoid_add);;

let mult_zero_nat =
  ({times_mult_zero = times_nat; zero_mult_zero = zero_nat} : nat mult_zero);;

let semigroup_mult_nat =
  ({times_semigroup_mult = times_nat} : nat semigroup_mult);;

let semiring_nat =
  ({ab_semigroup_add_semiring = ab_semigroup_add_nat;
     semigroup_mult_semiring = semigroup_mult_nat}
    : nat semiring);;

let semiring_0_nat =
  ({comm_monoid_add_semiring_0 = comm_monoid_add_nat;
     mult_zero_semiring_0 = mult_zero_nat; semiring_semiring_0 = semiring_nat}
    : nat semiring_0);;

let semiring_no_zero_divisors_nat =
  ({semiring_0_semiring_no_zero_divisors = semiring_0_nat} :
    nat semiring_no_zero_divisors);;

let monoid_mult_nat =
  ({semigroup_mult_monoid_mult = semigroup_mult_nat;
     power_monoid_mult = power_nat}
    : nat monoid_mult);;

let semiring_numeral_nat =
  ({monoid_mult_semiring_numeral = monoid_mult_nat;
     numeral_semiring_numeral = numeral_nat;
     semiring_semiring_numeral = semiring_nat}
    : nat semiring_numeral);;

let zero_neq_one_nat =
  ({one_zero_neq_one = one_nat; zero_zero_neq_one = zero_nat} :
    nat zero_neq_one);;

let semiring_1_nat =
  ({semiring_numeral_semiring_1 = semiring_numeral_nat;
     semiring_0_semiring_1 = semiring_0_nat;
     zero_neq_one_semiring_1 = zero_neq_one_nat}
    : nat semiring_1);;

let semiring_1_no_zero_divisors_nat =
  ({semiring_1_semiring_1_no_zero_divisors = semiring_1_nat;
     semiring_no_zero_divisors_semiring_1_no_zero_divisors =
       semiring_no_zero_divisors_nat}
    : nat semiring_1_no_zero_divisors);;

let cancel_semigroup_add_nat =
  ({semigroup_add_cancel_semigroup_add = semigroup_add_nat} :
    nat cancel_semigroup_add);;

let cancel_ab_semigroup_add_nat =
  ({ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_nat;
     cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_nat;
     minus_cancel_ab_semigroup_add = minus_nat}
    : nat cancel_ab_semigroup_add);;

let cancel_comm_monoid_add_nat =
  ({cancel_ab_semigroup_add_cancel_comm_monoid_add =
      cancel_ab_semigroup_add_nat;
     comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_nat}
    : nat cancel_comm_monoid_add);;

let semiring_0_cancel_nat =
  ({cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_nat;
     semiring_0_semiring_0_cancel = semiring_0_nat}
    : nat semiring_0_cancel);;

let ab_semigroup_mult_nat =
  ({semigroup_mult_ab_semigroup_mult = semigroup_mult_nat} :
    nat ab_semigroup_mult);;

let comm_semiring_nat =
  ({ab_semigroup_mult_comm_semiring = ab_semigroup_mult_nat;
     semiring_comm_semiring = semiring_nat}
    : nat comm_semiring);;

let comm_semiring_0_nat =
  ({comm_semiring_comm_semiring_0 = comm_semiring_nat;
     semiring_0_comm_semiring_0 = semiring_0_nat}
    : nat comm_semiring_0);;

let comm_semiring_0_cancel_nat =
  ({comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_nat;
     semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_nat}
    : nat comm_semiring_0_cancel);;

let semiring_1_cancel_nat =
  ({semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_nat;
     semiring_1_semiring_1_cancel = semiring_1_nat}
    : nat semiring_1_cancel);;

let comm_monoid_mult_nat =
  ({ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_nat;
     monoid_mult_comm_monoid_mult = monoid_mult_nat;
     dvd_comm_monoid_mult = dvd_nat}
    : nat comm_monoid_mult);;

let comm_semiring_1_nat =
  ({comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_nat;
     comm_semiring_0_comm_semiring_1 = comm_semiring_0_nat;
     semiring_1_comm_semiring_1 = semiring_1_nat}
    : nat comm_semiring_1);;

let comm_semiring_1_cancel_nat =
  ({comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_nat;
     comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_nat;
     semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_nat}
    : nat comm_semiring_1_cancel);;

let semidom_nat =
  ({comm_semiring_1_cancel_semidom = comm_semiring_1_cancel_nat;
     semiring_1_no_zero_divisors_semidom = semiring_1_no_zero_divisors_nat}
    : nat semidom);;

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

let ceq_nat = ({ceq = ceq_nata} : nat ceq);;

let set_impl_nata : (nat, set_impla) phantom = Phantom Set_RBT;;

let set_impl_nat = ({set_impl = set_impl_nata} : nat set_impl);;

type 'a linorder = {order_linorder : 'a order};;

let linorder_nat = ({order_linorder = order_nat} : nat linorder);;

type 'a semiring_no_zero_divisors_cancel =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
     'a semiring_no_zero_divisors};;

type 'a semidom_divide =
  {divide_semidom_divide : 'a divide; semidom_semidom_divide : 'a semidom;
    semiring_no_zero_divisors_cancel_semidom_divide :
      'a semiring_no_zero_divisors_cancel};;

let semiring_no_zero_divisors_cancel_nat =
  ({semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
      semiring_no_zero_divisors_nat}
    : nat semiring_no_zero_divisors_cancel);;

let semidom_divide_nat =
  ({divide_semidom_divide = divide_nat; semidom_semidom_divide = semidom_nat;
     semiring_no_zero_divisors_cancel_semidom_divide =
       semiring_no_zero_divisors_cancel_nat}
    : nat semidom_divide);;

type 'a algebraic_semidom =
  {semidom_divide_algebraic_semidom : 'a semidom_divide};;

type 'a semiring_modulo =
  {comm_semiring_1_cancel_semiring_modulo : 'a comm_semiring_1_cancel;
    modulo_semiring_modulo : 'a modulo};;

type 'a semidom_modulo =
  {algebraic_semidom_semidom_modulo : 'a algebraic_semidom;
    semiring_modulo_semidom_modulo : 'a semiring_modulo};;

let algebraic_semidom_nat =
  ({semidom_divide_algebraic_semidom = semidom_divide_nat} :
    nat algebraic_semidom);;

let semiring_modulo_nat =
  ({comm_semiring_1_cancel_semiring_modulo = comm_semiring_1_cancel_nat;
     modulo_semiring_modulo = modulo_nat}
    : nat semiring_modulo);;

let semidom_modulo_nat =
  ({algebraic_semidom_semidom_modulo = algebraic_semidom_nat;
     semiring_modulo_semidom_modulo = semiring_modulo_nat}
    : nat semidom_modulo);;

let finite_UNIV_nata : (nat, bool) phantom = Phantom false;;

let card_UNIV_nata : (nat, nat) phantom = Phantom zero_nata;;

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

let rec eq _A a b = equal _A a b;;

let rec comparator_of (_A1, _A2)
  x y = (if less _A2.order_linorder.preorder_order.ord_preorder x y then Lt
          else (if eq _A1 x y then Eqa else Gt));;

let rec compare_nat x = comparator_of (equal_nat, linorder_nat) x;;

let ccompare_nata : (nat -> nat -> ordera) option = Some compare_nat;;

let ccompare_nat = ({ccompare = ccompare_nata} : nat ccompare);;

type mapping_impla = Mapping_Choose | Mapping_Assoc_List | Mapping_RBT |
  Mapping_Mapping;;

let mapping_impl_nata : (nat, mapping_impla) phantom = Phantom Mapping_RBT;;

type 'a mapping_impl = {mapping_impl : ('a, mapping_impla) phantom};;
let mapping_impl _A = _A.mapping_impl;;

let mapping_impl_nat = ({mapping_impl = mapping_impl_nata} : nat mapping_impl);;

let rec proper_interval_nat
  no x1 = match no, x1 with no, None -> true
    | None, Some x -> less_nat zero_nata x
    | Some x, Some y -> less_nat one_nata (minus_nata y x);;

let rec cproper_interval_nata x = proper_interval_nat x;;

type 'a cproper_interval =
  {ccompare_cproper_interval : 'a ccompare;
    cproper_interval : 'a option -> 'a option -> bool};;
let cproper_interval _A = _A.cproper_interval;;

let cproper_interval_nat =
  ({ccompare_cproper_interval = ccompare_nat;
     cproper_interval = cproper_interval_nata}
    : nat cproper_interval);;

type 'a set_dlist = Abs_dlist of 'a list;;

let rec list_of_dlist _A (Abs_dlist x) = x;;

let rec list_member
  equal x1 y = match equal, x1, y with
    equal, x :: xs, y -> equal x y || list_member equal xs y
    | equal, [], y -> false;;

type color = R | B;;

type ('a, 'b) rbt = Empty |
  Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt;;

type ('b, 'a) mapping_rbt = Mapping_RBTa of ('b, 'a) rbt;;

type 'a set = Collect_set of ('a -> bool) | DList_set of 'a set_dlist |
  RBT_set of ('a, unit) mapping_rbt | Set_Monad of 'a list |
  Complement of 'a set;;

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

let rec impl_ofa _B (Mapping_RBTa x) = x;;

let rec the (Some x2) = x2;;

let rec insertb _A
  xc xd xe =
    Mapping_RBTa (rbt_comp_insert (the (ccompare _A)) xc xd (impl_ofa _A xe));;

let rec rbt_baliR
  t1 ab bb x3 = match t1, ab, bb, x3 with
    t1, ab, bb, Branch (R, t2, aa, ba, Branch (R, t3, a, b, t4)) ->
      Branch (R, Branch (B, t1, ab, bb, t2), aa, ba, Branch (B, t3, a, b, t4))
    | t1, ab, bb, Branch (R, Branch (R, t2, aa, ba, t3), a, b, Empty) ->
        Branch
          (R, Branch (B, t1, ab, bb, t2), aa, ba, Branch (B, t3, a, b, Empty))
    | t1, ab, bb,
        Branch (R, Branch (R, t2, aa, ba, t3), a, b, Branch (B, va, vb, vc, vd))
        -> Branch
             (R, Branch (B, t1, ab, bb, t2), aa, ba,
               Branch (B, t3, a, b, Branch (B, va, vb, vc, vd)))
    | t1, a, b, Empty -> Branch (B, t1, a, b, Empty)
    | t1, a, b, Branch (B, va, vb, vc, vd) ->
        Branch (B, t1, a, b, Branch (B, va, vb, vc, vd))
    | t1, a, b, Branch (v, Empty, vb, vc, Empty) ->
        Branch (B, t1, a, b, Branch (v, Empty, vb, vc, Empty))
    | t1, a, b, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty) ->
        Branch
          (B, t1, a, b, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
    | t1, a, b, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)) ->
        Branch
          (B, t1, a, b, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
    | t1, a, b,
        Branch
          (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi))
        -> Branch
             (B, t1, a, b,
               Branch
                 (v, Branch (B, ve, vj, vk, vl), vb, vc,
                   Branch (B, vf, vg, vh, vi)));;

let rec equal_color x0 x1 = match x0, x1 with R, B -> false
                      | B, R -> false
                      | B, B -> true
                      | R, R -> true;;

let rec suc n = plus_nata n one_nata;;

let rec bheight
  = function Empty -> zero_nata
    | Branch (c, lt, k, v, rt) ->
        (if equal_color c B then suc (bheight lt) else bheight lt);;

let rec rbt_joinR
  l a b r =
    (if less_eq_nat (bheight l) (bheight r) then Branch (R, l, a, b, r)
      else (match l
             with Branch (R, la, ab, ba, ra) ->
               Branch (R, la, ab, ba, rbt_joinR ra a b r)
             | Branch (B, la, ab, ba, ra) ->
               rbt_baliR la ab ba (rbt_joinR ra a b r)));;

let rec rbt_baliL
  x0 a b t4 = match x0, a, b, t4 with
    Branch (R, Branch (R, t1, ab, bb, t2), aa, ba, t3), a, b, t4 ->
      Branch (R, Branch (B, t1, ab, bb, t2), aa, ba, Branch (B, t3, a, b, t4))
    | Branch (R, Empty, ab, bb, Branch (R, t2, aa, ba, t3)), a, b, t4 ->
        Branch
          (R, Branch (B, Empty, ab, bb, t2), aa, ba, Branch (B, t3, a, b, t4))
    | Branch
        (R, Branch (B, va, vb, vc, vd), ab, bb, Branch (R, t2, aa, ba, t3)),
        a, b, t4
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), ab, bb, t2), aa, ba,
               Branch (B, t3, a, b, t4))
    | Empty, a, b, t2 -> Branch (B, Empty, a, b, t2)
    | Branch (B, va, vb, vc, vd), a, b, t2 ->
        Branch (B, Branch (B, va, vb, vc, vd), a, b, t2)
    | Branch (v, Empty, vb, vc, Empty), a, b, t2 ->
        Branch (B, Branch (v, Empty, vb, vc, Empty), a, b, t2)
    | Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), a, b, t2 ->
        Branch
          (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), a, b, t2)
    | Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), a, b, t2 ->
        Branch
          (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), a, b, t2)
    | Branch
        (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        a, b, t2
        -> Branch
             (B, Branch
                   (v, Branch (B, vf, vg, vh, vi), vb, vc,
                     Branch (B, ve, vj, vk, vl)),
               a, b, t2);;

let rec rbt_joinL
  l a b r =
    (if less_eq_nat (bheight r) (bheight l) then Branch (R, l, a, b, r)
      else (match r
             with Branch (R, la, ab, ba, ra) ->
               Branch (R, rbt_joinL l a b la, ab, ba, ra)
             | Branch (B, la, ab, ba, ra) ->
               rbt_baliL (rbt_joinL l a b la) ab ba ra));;

let rec rbt_join
  l a b r =
    (let bhl = bheight l in
     let bhr = bheight r in
      (if less_nat bhr bhl then paint B (rbt_joinR l a b r)
        else (if less_nat bhl bhr then paint B (rbt_joinL l a b r)
               else Branch (B, l, a, b, r))));;

let rec rbt_split_comp
  c x1 k = match c, x1, k with c, Empty, k -> (Empty, (None, Empty))
    | c, Branch (uu, l, a, b, r), x ->
        (match c x a with Eqa -> (l, (Some b, r))
          | Lt ->
            (let (l1, (beta, l2)) = rbt_split_comp c l x in
              (l1, (beta, rbt_join l2 a b r)))
          | Gt ->
            (let (r1, (beta, r2)) = rbt_split_comp c r x in
              (rbt_join l a b r1, (beta, r2))));;

let rec nat_of_integer k = Nat (max ord_integer Z.zero k);;

let rec folda
  f xa1 x = match f, xa1, x with
    f, Branch (c, lt, k, v, rt), x -> folda f rt (f k v (folda f lt x))
    | f, Empty, x -> x;;

let rec rbt_comp_union_swap_rec
  c f gamma t1 t2 =
    (let bh1 = bheight t1 in
     let bh2 = bheight t2 in
     let (gammaa, (t2a, (bh2a, (t1a, _)))) =
       (if less_nat bh1 bh2 then (not gamma, (t1, (bh1, (t2, bh2))))
         else (gamma, (t2, (bh2, (t1, bh1)))))
       in
     let fa = (if gammaa then (fun k v va -> f k va v) else f) in
      (if less_nat bh2a (nat_of_integer (Z.of_int 4))
        then folda (rbt_comp_insert_with_key c fa) t2a t1a
        else (match t1a with Empty -> t2a
               | Branch (_, l1, a, b, r1) ->
                 (let (l2, (beta, r2)) = rbt_split_comp c t2a a in
                   rbt_join (rbt_comp_union_swap_rec c f gammaa l1 l2) a
                     (match beta with None -> b | Some ca -> fa a b ca)
                     (rbt_comp_union_swap_rec c f gammaa r1 r2)))));;

let rec rbt_comp_union_with_key
  c f t1 t2 = paint B (rbt_comp_union_swap_rec c f false t1 t2);;

let rec joina _A
  xc xd xe =
    Mapping_RBTa
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

let rec id x = (fun xa -> xa) x;;

let rec is_none = function Some x -> false
                  | None -> true;;

let rec filtera
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filtera p xs else filtera p xs);;

let rec inter_list _A
  xb xc =
    Mapping_RBTa
      (fold (fun k -> rbt_comp_insert (the (ccompare _A)) k ())
        (filtera
          (fun x ->
            not (is_none
                  (rbt_comp_lookup (the (ccompare _A)) (impl_ofa _A xb) x)))
          xc)
        Empty);;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (suc n) xs
                     | n, [] -> n;;

let rec size_lista x = gen_length zero_nata x;;

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
    (if equal_nata n zero_nata || equal_nata n one_nata then (Empty, kvs)
      else (let (na, r) = divmod_nat n (nat_of_integer (Z.of_int 2)) in
             (if equal_nata r zero_nata
               then (let (t1, (k, v) :: kvsa) = rbtreeify_g na kvs in
                      apfst (fun a -> Branch (B, t1, k, v, a))
                        (rbtreeify_g na kvsa))
               else (let (t1, (k, v) :: kvsa) = rbtreeify_f na kvs in
                      apfst (fun a -> Branch (B, t1, k, v, a))
                        (rbtreeify_g na kvsa)))))
and rbtreeify_f
  n kvs =
    (if equal_nata n zero_nata then (Empty, kvs)
      else (if equal_nata n one_nata
             then (let (k, v) :: kvsa = kvs in
                    (Branch (R, Empty, k, v, Empty), kvsa))
             else (let (na, r) = divmod_nat n (nat_of_integer (Z.of_int 2)) in
                    (if equal_nata r zero_nata
                      then (let (t1, (k, v) :: kvsa) = rbtreeify_f na kvs in
                             apfst (fun a -> Branch (B, t1, k, v, a))
                               (rbtreeify_g na kvsa))
                      else (let (t1, (k, v) :: kvsa) = rbtreeify_f na kvs in
                             apfst (fun a -> Branch (B, t1, k, v, a))
                               (rbtreeify_f na kvsa))))));;

let rec rbtreeify kvs = fst (rbtreeify_g (suc (size_lista kvs)) kvs);;

let rec gen_entries
  kvts x1 = match kvts, x1 with
    kvts, Branch (c, l, k, v, r) -> gen_entries (((k, v), r) :: kvts) l
    | (kv, t) :: kvts, Empty -> kv :: gen_entries kvts t
    | [], Empty -> [];;

let rec entries x = gen_entries [] x;;

let rec filtere _A
  xb xc = Mapping_RBTa (rbtreeify (filtera xb (entries (impl_ofa _A xc))));;

let rec map_filter
  f x1 = match f, x1 with f, [] -> []
    | f, x :: xs ->
        (match f x with None -> map_filter f xs
          | Some y -> y :: map_filter f xs);;

let rec map_filter_comp_inter
  c f t1 t2 =
    map_filter
      (fun (k, v) ->
        (match rbt_comp_lookup c t1 k with None -> None
          | Some va -> Some (k, f k va v)))
      (entries t2);;

let rec is_rbt_empty
  t = (match t with Empty -> true | Branch (_, _, _, _, _) -> false);;

let rec rbt_split_min
  = function Empty -> failwith "undefined"
    | Branch (uu, l, a, b, r) ->
        (if is_rbt_empty l then (a, (b, r))
          else (let (aa, (ba, la)) = rbt_split_min l in
                 (aa, (ba, rbt_join la a b r))));;

let rec rbt_join2
  l r = (if is_rbt_empty r then l
          else (let a = rbt_split_min r in
                let (aa, b) = a in
                let (ba, c) = b in
                 rbt_join l aa ba c));;

let rec rbt_comp_inter_swap_rec
  c f gamma t1 t2 =
    (let bh1 = bheight t1 in
     let bh2 = bheight t2 in
     let (gammaa, (t2a, (bh2a, (t1a, _)))) =
       (if less_nat bh1 bh2 then (not gamma, (t1, (bh1, (t2, bh2))))
         else (gamma, (t2, (bh2, (t1, bh1)))))
       in
     let fa = (if gammaa then (fun k v va -> f k va v) else f) in
      (if less_nat bh2a (nat_of_integer (Z.of_int 4))
        then rbtreeify (map_filter_comp_inter c fa t1a t2a)
        else (match t1a with Empty -> Empty
               | Branch (_, l1, a, b, r1) ->
                 (let (l2, (beta, r2)) = rbt_split_comp c t2a a in
                  let l = rbt_comp_inter_swap_rec c f gammaa l1 l2 in
                  let r = rbt_comp_inter_swap_rec c f gammaa r1 r2 in
                   (match beta with None -> rbt_join2 l r
                     | Some ba -> rbt_join l a (fa a b ba) r)))));;

let rec rbt_comp_inter_with_key
  c f t1 t2 = paint B (rbt_comp_inter_swap_rec c f false t1 t2);;

let rec meet _A
  xc xd xe =
    Mapping_RBTa
      (rbt_comp_inter_with_key (the (ccompare _A)) xc (impl_ofa _A xd)
        (impl_ofa _A xe));;

let rec filterd _A xb xc = Abs_dlist (filtera xb (list_of_dlist _A xc));;

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
          | Some eq -> DList_set (filterd _A1 (list_member eq xs) dxs1))
    | DList_set dxs1, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "inter DList_set DList_set: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) (DList_set dxs1) (DList_set dxs2))
          | Some _ -> DList_set (filterd _A1 (memberc _A1 dxs2) dxs1))
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
          | Some eq -> DList_set (filterd _A1 (list_member eq xs) dxs2))
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
              (filtere _A2 (comp (fun x -> member (_A1, _A2) x g) fst) rbt2))
    | RBT_set rbt1, g ->
        (match ccompare _A2
          with None ->
            failwith "inter RBT_set1: ccompare = None"
              (fun _ -> inf_seta (_A1, _A2) (RBT_set rbt1) g)
          | Some _ ->
            RBT_set
              (filtere _A2 (comp (fun x -> member (_A1, _A2) x g) fst) rbt1))
    | h, DList_set dxs2 ->
        (match ceq _A1
          with None ->
            failwith "inter DList_set2: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) h (DList_set dxs2))
          | Some _ ->
            DList_set (filterd _A1 (fun x -> member (_A1, _A2) x h) dxs2))
    | DList_set dxs1, h ->
        (match ceq _A1
          with None ->
            failwith "inter DList_set1: ceq = None"
              (fun _ -> inf_seta (_A1, _A2) (DList_set dxs1) h)
          | Some _ ->
            DList_set (filterd _A1 (fun x -> member (_A1, _A2) x h) dxs1))
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

let rec has_next g = fst (generator g);;

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

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let rec dlist_all _A x xc = list_all x (list_of_dlist _A xc);;

let rec rbt_init x = ([], x);;

let rec init _A xa = rbt_init (impl_ofa _A xa);;

let rec collect _A
  p = (match cEnum _A with None -> Collect_set p
        | Some (enum, _) -> Set_Monad (filtera p enum));;

let rec less_eq_set (_A1, _A2, _A3)
  x0 c = match x0, c with
    RBT_set rbt1, RBT_set rbt2 ->
      (match ccompare _A3
        with None ->
          failwith "subset RBT_set RBT_set: ccompare = None"
            (fun _ -> less_eq_set (_A1, _A2, _A3) (RBT_set rbt1) (RBT_set rbt2))
        | Some c ->
          (match ceq _A2
            with None ->
              sorted_list_subset_fusion (lt_of_comp c)
                (fun x y -> equal_order (c x y) Eqa) rbt_keys_generator
                rbt_keys_generator (init _A3 rbt1) (init _A3 rbt2)
            | Some eq ->
              sorted_list_subset_fusion (lt_of_comp c) eq rbt_keys_generator
                rbt_keys_generator (init _A3 rbt1) (init _A3 rbt2)))
    | Complement a1, Complement a2 -> less_eq_set (_A1, _A2, _A3) a2 a1
    | Collect_set p, Complement a ->
        less_eq_set (_A1, _A2, _A3) a (collect _A1 (fun x -> not (p x)))
    | Set_Monad xs, c -> list_all (fun x -> member (_A2, _A3) x c) xs
    | DList_set dxs, c ->
        (match ceq _A2
          with None ->
            failwith "subset DList_set1: ceq = None"
              (fun _ -> less_eq_set (_A1, _A2, _A3) (DList_set dxs) c)
          | Some _ -> dlist_all _A2 (fun x -> member (_A2, _A3) x c) dxs)
    | RBT_set rbt, b ->
        (match ccompare _A3
          with None ->
            failwith "subset RBT_set1: ccompare = None"
              (fun _ -> less_eq_set (_A1, _A2, _A3) (RBT_set rbt) b)
          | Some _ ->
            list_all_fusion rbt_keys_generator (fun x -> member (_A2, _A3) x b)
              (init _A3 rbt));;

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
  a n = (if equal_nata n zero_nata then one _A.one_power
          else times _A.times_power a (power _A a (minus_nata n one_nata)));;

let rec card_UNIV_seta _A
  = Phantom
      (let c = of_phantom (card_UNIVa _A) in
        (if equal_nata c zero_nata then zero_nata
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

let rec keysa x = gen_keys [] x;;

let rec keysb _A xa = keysa (impl_ofa _A xa);;

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
          | Some _ -> keysb _A2 rbt);;

let rec emptyc _A = Mapping_RBTa Empty;;

let rec emptyb _A = Abs_dlist [];;

let rec set_empty_choose (_A1, _A2)
  = (match ccompare _A2
      with None ->
        (match ceq _A1 with None -> Set_Monad []
          | Some _ -> DList_set (emptyb _A1))
      | Some _ -> RBT_set (emptyc _A2));;

let rec set_empty (_A1, _A2)
  = function Set_Choose -> set_empty_choose (_A1, _A2)
    | Set_Monada -> Set_Monad []
    | Set_RBT -> RBT_set (emptyc _A2)
    | Set_DList -> DList_set (emptyb _A1)
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

let rec finite (_A1, _A2, _A3)
  = function
    Collect_set p ->
      of_phantom (finite_UNIV _A1) ||
        failwith "finite Collect_set"
          (fun _ -> finite (_A1, _A2, _A3) (Collect_set p))
    | Set_Monad xs -> true
    | Complement a ->
        (if of_phantom (finite_UNIV _A1) then true
          else (if finite (_A1, _A2, _A3) a then false
                 else failwith "finite Complement: infinite set"
                        (fun _ -> finite (_A1, _A2, _A3) (Complement a))))
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
                 fold_fusion g (fun xa (n, _) -> (plus_nata n one_nata, xa)) sa
                   (one_nata, x))
          else (zero_nata, failwith "undefined"));;

let rec gen_length_fusion
  g n s =
    (if has_next g s then gen_length_fusion g (suc n) (snd (next g s)) else n);;

let rec length_fusion g = gen_length_fusion g zero_nata;;

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
                                 (plus_nata n one_nata) s1a s2
                        else (if less y x
                               then proper_interval ao (Some y) ||
                                      proper_interval_set_Compl_aux_fusion _A
less proper_interval g1 g2 (Some y) (plus_nata n one_nata) s1 s2a
                               else proper_interval ao (Some x) &&
                                      (let m =
 minus_nata (of_phantom (card_UNIV _A)) n in
not (equal_nata (minus_nata m (length_fusion g2 s2a))
      (nat_of_integer (Z.of_int 2))) ||
  not (equal_nata (minus_nata m (length_fusion g1 s1a))
        (nat_of_integer (Z.of_int 2)))))))
               else (let m = minus_nata (of_phantom (card_UNIV _A)) n in
                     let (len_x, xa) = length_last_fusion g1 s1 in
                      not (equal_nata m len_x) &&
                        (if equal_nata m (plus_nata len_x one_nata)
                          then not (proper_interval (Some xa) None)
                          else true))))
      else (if has_next g2 s2
             then (let (_, _) = next g2 s2 in
                   let m = minus_nata (of_phantom (card_UNIV _A)) n in
                   let (len_y, y) = length_last_fusion g2 s2 in
                    not (equal_nata m len_y) &&
                      (if equal_nata m (plus_nata len_y one_nata)
                        then not (proper_interval (Some y) None) else true))
             else less_nat (plus_nata n one_nata)
                    (of_phantom (card_UNIV _A))));;

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
      fold (fun xa (n, _) -> (plus_nata n one_nata, xa)) xs (one_nata, x)
    | [] -> (zero_nata, failwith "undefined");;

let rec proper_interval_set_Compl_aux _A
  less proper_interval ao n x4 x5 = match less, proper_interval, ao, n, x4, x5
    with
    less, proper_interval, ao, n, x :: xs, y :: ys ->
      (if less x y
        then proper_interval ao (Some x) ||
               proper_interval_set_Compl_aux _A less proper_interval (Some x)
                 (plus_nata n one_nata) xs (y :: ys)
        else (if less y x
               then proper_interval ao (Some y) ||
                      proper_interval_set_Compl_aux _A less proper_interval
                        (Some y) (plus_nata n one_nata) (x :: xs) ys
               else proper_interval ao (Some x) &&
                      (let m = minus_nata (of_phantom (card_UNIV _A)) n in
                        not (equal_nata (minus_nata m (size_lista ys))
                              (nat_of_integer (Z.of_int 2))) ||
                          not (equal_nata (minus_nata m (size_lista xs))
                                (nat_of_integer (Z.of_int 2))))))
    | less, proper_interval, ao, n, x :: xs, [] ->
        (let m = minus_nata (of_phantom (card_UNIV _A)) n in
         let (len_x, xa) = length_last (x :: xs) in
          not (equal_nata m len_x) &&
            (if equal_nata m (plus_nata len_x one_nata)
              then not (proper_interval (Some xa) None) else true))
    | less, proper_interval, ao, n, [], y :: ys ->
        (let m = minus_nata (of_phantom (card_UNIV _A)) n in
         let (len_y, ya) = length_last (y :: ys) in
          not (equal_nata m len_y) &&
            (if equal_nata m (plus_nata len_y one_nata)
              then not (proper_interval (Some ya) None) else true))
    | less, proper_interval, ao, n, [], [] ->
        less_nat (plus_nata n one_nata) (of_phantom (card_UNIV _A));;

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

let rec length _A xa = size_lista (list_of_dlist _A xa);;

let rec card (_A1, _A2, _A3)
  = function
    Complement a ->
      (let aa = card (_A1, _A2, _A3) a in
       let s = of_phantom (card_UNIVa _A1) in
        (if less_nat zero_nata s then minus_nata s aa
          else (if finite (_A1.finite_UNIV_card_UNIV, _A2, _A3) a then zero_nata
                 else failwith "card Complement: infinite"
                        (fun _ -> card (_A1, _A2, _A3) (Complement a)))))
    | Set_Monad xs ->
        (match ceq _A2
          with None ->
            failwith "card Set_Monad: ceq = None"
              (fun _ -> card (_A1, _A2, _A3) (Set_Monad xs))
          | Some eq -> size_lista (list_remdups eq xs))
    | RBT_set rbt ->
        (match ccompare _A3
          with None ->
            failwith "card RBT_set: ccompare = None"
              (fun _ -> card (_A1, _A2, _A3) (RBT_set rbt))
          | Some _ -> size_lista (keysb _A3 rbt))
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
    | a -> (let aa = of_phantom (card_UNIVa _A1) in
            let b = card (_A1, _A2, _A3.ccompare_cproper_interval) a in
             (if less_nat zero_nata aa then equal_nata aa b
               else (if less_nat zero_nata b then false
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
                None zero_nata (init _A3.ccompare_cproper_interval rbt1)
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
                (cproper_interval _A3) None zero_nata
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

let card_UNIV_lista : (('a list), nat) phantom = Phantom zero_nata;;

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

let mapping_impl_lista : (('a list), mapping_impla) phantom
  = Phantom Mapping_Choose;;

let mapping_impl_list =
  ({mapping_impl = mapping_impl_lista} : ('a list) mapping_impl);;

let rec cproper_interval_lista _A xso yso = failwith "undefined";;

let rec cproper_interval_list _A =
  ({ccompare_cproper_interval = (ccompare_list _A);
     cproper_interval = cproper_interval_lista _A}
    : ('a list) cproper_interval);;

let rec lcompare_double
  x y = (if FloatUtil.iszero x && FloatUtil.iszero y
          then FloatUtil.compare (FloatUtil.copysign 1.0 x)
                 (FloatUtil.copysign 1.0 y)
          else FloatUtil.compare x y);;

let rec equal_double x y = Z.equal (lcompare_double x y) Z.zero;;

type event_data = EInt of Z.t | EFloat of float | EString of string;;

let rec equal_event_dataa
  x0 x1 = match x0, x1 with EFloat x2, EString x3 -> false
    | EString x3, EFloat x2 -> false
    | EInt x1, EString x3 -> false
    | EString x3, EInt x1 -> false
    | EInt x1, EFloat x2 -> false
    | EFloat x2, EInt x1 -> false
    | EString x3, EString y3 -> Stdlib.(=) x3 y3
    | EFloat x2, EFloat y2 -> equal_double x2 y2
    | EInt x1, EInt y1 -> Z.equal x1 y1;;

type trm = Var of nat | Const of event_data | Plus of trm * trm |
  Minus of trm * trm | UMinus of trm | Mult of trm * trm | Div of trm * trm |
  Mod of trm * trm | F2i of trm | I2f of trm;;

let rec equal_trma
  x0 x1 = match x0, x1 with F2i x9, I2f x10 -> false
    | I2f x10, F2i x9 -> false
    | Mod (x81, x82), I2f x10 -> false
    | I2f x10, Mod (x81, x82) -> false
    | Mod (x81, x82), F2i x9 -> false
    | F2i x9, Mod (x81, x82) -> false
    | Div (x71, x72), I2f x10 -> false
    | I2f x10, Div (x71, x72) -> false
    | Div (x71, x72), F2i x9 -> false
    | F2i x9, Div (x71, x72) -> false
    | Div (x71, x72), Mod (x81, x82) -> false
    | Mod (x81, x82), Div (x71, x72) -> false
    | Mult (x61, x62), I2f x10 -> false
    | I2f x10, Mult (x61, x62) -> false
    | Mult (x61, x62), F2i x9 -> false
    | F2i x9, Mult (x61, x62) -> false
    | Mult (x61, x62), Mod (x81, x82) -> false
    | Mod (x81, x82), Mult (x61, x62) -> false
    | Mult (x61, x62), Div (x71, x72) -> false
    | Div (x71, x72), Mult (x61, x62) -> false
    | UMinus x5, I2f x10 -> false
    | I2f x10, UMinus x5 -> false
    | UMinus x5, F2i x9 -> false
    | F2i x9, UMinus x5 -> false
    | UMinus x5, Mod (x81, x82) -> false
    | Mod (x81, x82), UMinus x5 -> false
    | UMinus x5, Div (x71, x72) -> false
    | Div (x71, x72), UMinus x5 -> false
    | UMinus x5, Mult (x61, x62) -> false
    | Mult (x61, x62), UMinus x5 -> false
    | Minus (x41, x42), I2f x10 -> false
    | I2f x10, Minus (x41, x42) -> false
    | Minus (x41, x42), F2i x9 -> false
    | F2i x9, Minus (x41, x42) -> false
    | Minus (x41, x42), Mod (x81, x82) -> false
    | Mod (x81, x82), Minus (x41, x42) -> false
    | Minus (x41, x42), Div (x71, x72) -> false
    | Div (x71, x72), Minus (x41, x42) -> false
    | Minus (x41, x42), Mult (x61, x62) -> false
    | Mult (x61, x62), Minus (x41, x42) -> false
    | Minus (x41, x42), UMinus x5 -> false
    | UMinus x5, Minus (x41, x42) -> false
    | Plus (x31, x32), I2f x10 -> false
    | I2f x10, Plus (x31, x32) -> false
    | Plus (x31, x32), F2i x9 -> false
    | F2i x9, Plus (x31, x32) -> false
    | Plus (x31, x32), Mod (x81, x82) -> false
    | Mod (x81, x82), Plus (x31, x32) -> false
    | Plus (x31, x32), Div (x71, x72) -> false
    | Div (x71, x72), Plus (x31, x32) -> false
    | Plus (x31, x32), Mult (x61, x62) -> false
    | Mult (x61, x62), Plus (x31, x32) -> false
    | Plus (x31, x32), UMinus x5 -> false
    | UMinus x5, Plus (x31, x32) -> false
    | Plus (x31, x32), Minus (x41, x42) -> false
    | Minus (x41, x42), Plus (x31, x32) -> false
    | Const x2, I2f x10 -> false
    | I2f x10, Const x2 -> false
    | Const x2, F2i x9 -> false
    | F2i x9, Const x2 -> false
    | Const x2, Mod (x81, x82) -> false
    | Mod (x81, x82), Const x2 -> false
    | Const x2, Div (x71, x72) -> false
    | Div (x71, x72), Const x2 -> false
    | Const x2, Mult (x61, x62) -> false
    | Mult (x61, x62), Const x2 -> false
    | Const x2, UMinus x5 -> false
    | UMinus x5, Const x2 -> false
    | Const x2, Minus (x41, x42) -> false
    | Minus (x41, x42), Const x2 -> false
    | Const x2, Plus (x31, x32) -> false
    | Plus (x31, x32), Const x2 -> false
    | Var x1, I2f x10 -> false
    | I2f x10, Var x1 -> false
    | Var x1, F2i x9 -> false
    | F2i x9, Var x1 -> false
    | Var x1, Mod (x81, x82) -> false
    | Mod (x81, x82), Var x1 -> false
    | Var x1, Div (x71, x72) -> false
    | Div (x71, x72), Var x1 -> false
    | Var x1, Mult (x61, x62) -> false
    | Mult (x61, x62), Var x1 -> false
    | Var x1, UMinus x5 -> false
    | UMinus x5, Var x1 -> false
    | Var x1, Minus (x41, x42) -> false
    | Minus (x41, x42), Var x1 -> false
    | Var x1, Plus (x31, x32) -> false
    | Plus (x31, x32), Var x1 -> false
    | Var x1, Const x2 -> false
    | Const x2, Var x1 -> false
    | I2f x10, I2f y10 -> equal_trma x10 y10
    | F2i x9, F2i y9 -> equal_trma x9 y9
    | Mod (x81, x82), Mod (y81, y82) -> equal_trma x81 y81 && equal_trma x82 y82
    | Div (x71, x72), Div (y71, y72) -> equal_trma x71 y71 && equal_trma x72 y72
    | Mult (x61, x62), Mult (y61, y62) ->
        equal_trma x61 y61 && equal_trma x62 y62
    | UMinus x5, UMinus y5 -> equal_trma x5 y5
    | Minus (x41, x42), Minus (y41, y42) ->
        equal_trma x41 y41 && equal_trma x42 y42
    | Plus (x31, x32), Plus (y31, y32) ->
        equal_trma x31 y31 && equal_trma x32 y32
    | Const x2, Const y2 -> equal_event_dataa x2 y2
    | Var x1, Var y1 -> equal_nata x1 y1;;

let equal_trm = ({equal = equal_trma} : trm equal);;

let ceq_trma : (trm -> trm -> bool) option = Some equal_trma;;

let ceq_trm = ({ceq = ceq_trma} : trm ceq);;

let set_impl_trma : (trm, set_impla) phantom = Phantom Set_RBT;;

let set_impl_trm = ({set_impl = set_impl_trma} : trm set_impl);;

let rec comparator_double
  x y = (let c = lcompare_double x y in
          (if Z.equal c Z.zero then Eqa
            else (if Z.lt c Z.zero then Lt else Gt)));;

let preorder_integer = ({ord_preorder = ord_integer} : Z.t preorder);;

let order_integer = ({preorder_order = preorder_integer} : Z.t order);;

let linorder_integer = ({order_linorder = order_integer} : Z.t linorder);;

let equal_integer = ({equal = Z.equal} : Z.t equal);;

let ord_string8 = ({less_eq = Stdlib.(<=); less = Stdlib.(<)} : string ord);;

let preorder_string8 = ({ord_preorder = ord_string8} : string preorder);;

let order_string8 = ({preorder_order = preorder_string8} : string order);;

let linorder_string8 = ({order_linorder = order_string8} : string linorder);;

let equal_string8 = ({equal = Stdlib.(=)} : string equal);;

let rec comparator_event_data
  x0 x1 = match x0, x1 with
    EString x, EString yb ->
      comparator_of (equal_string8, linorder_string8) x yb
    | EString x, EFloat ya -> Gt
    | EString x, EInt y -> Gt
    | EFloat x, EString yb -> Lt
    | EFloat x, EFloat ya -> comparator_double x ya
    | EFloat x, EInt y -> Gt
    | EInt x, EString yb -> Lt
    | EInt x, EFloat ya -> Lt
    | EInt x, EInt y -> comparator_of (equal_integer, linorder_integer) x y;;

let rec comparator_trm
  x0 x1 = match x0, x1 with I2f x, I2f yn -> comparator_trm x yn
    | I2f x, F2i ym -> Gt
    | I2f x, Mod (yk, yl) -> Gt
    | I2f x, Div (yi, yj) -> Gt
    | I2f x, Mult (yg, yh) -> Gt
    | I2f x, UMinus yf -> Gt
    | I2f x, Minus (yd, ye) -> Gt
    | I2f x, Plus (yb, yc) -> Gt
    | I2f x, Const ya -> Gt
    | I2f x, Var y -> Gt
    | F2i x, I2f yn -> Lt
    | F2i x, F2i ym -> comparator_trm x ym
    | F2i x, Mod (yk, yl) -> Gt
    | F2i x, Div (yi, yj) -> Gt
    | F2i x, Mult (yg, yh) -> Gt
    | F2i x, UMinus yf -> Gt
    | F2i x, Minus (yd, ye) -> Gt
    | F2i x, Plus (yb, yc) -> Gt
    | F2i x, Const ya -> Gt
    | F2i x, Var y -> Gt
    | Mod (x, xa), I2f yn -> Lt
    | Mod (x, xa), F2i ym -> Lt
    | Mod (x, xa), Mod (yk, yl) ->
        (match comparator_trm x yk with Eqa -> comparator_trm xa yl | Lt -> Lt
          | Gt -> Gt)
    | Mod (x, xa), Div (yi, yj) -> Gt
    | Mod (x, xa), Mult (yg, yh) -> Gt
    | Mod (x, xa), UMinus yf -> Gt
    | Mod (x, xa), Minus (yd, ye) -> Gt
    | Mod (x, xa), Plus (yb, yc) -> Gt
    | Mod (x, xa), Const ya -> Gt
    | Mod (x, xa), Var y -> Gt
    | Div (x, xa), I2f yn -> Lt
    | Div (x, xa), F2i ym -> Lt
    | Div (x, xa), Mod (yk, yl) -> Lt
    | Div (x, xa), Div (yi, yj) ->
        (match comparator_trm x yi with Eqa -> comparator_trm xa yj | Lt -> Lt
          | Gt -> Gt)
    | Div (x, xa), Mult (yg, yh) -> Gt
    | Div (x, xa), UMinus yf -> Gt
    | Div (x, xa), Minus (yd, ye) -> Gt
    | Div (x, xa), Plus (yb, yc) -> Gt
    | Div (x, xa), Const ya -> Gt
    | Div (x, xa), Var y -> Gt
    | Mult (x, xa), I2f yn -> Lt
    | Mult (x, xa), F2i ym -> Lt
    | Mult (x, xa), Mod (yk, yl) -> Lt
    | Mult (x, xa), Div (yi, yj) -> Lt
    | Mult (x, xa), Mult (yg, yh) ->
        (match comparator_trm x yg with Eqa -> comparator_trm xa yh | Lt -> Lt
          | Gt -> Gt)
    | Mult (x, xa), UMinus yf -> Gt
    | Mult (x, xa), Minus (yd, ye) -> Gt
    | Mult (x, xa), Plus (yb, yc) -> Gt
    | Mult (x, xa), Const ya -> Gt
    | Mult (x, xa), Var y -> Gt
    | UMinus x, I2f yn -> Lt
    | UMinus x, F2i ym -> Lt
    | UMinus x, Mod (yk, yl) -> Lt
    | UMinus x, Div (yi, yj) -> Lt
    | UMinus x, Mult (yg, yh) -> Lt
    | UMinus x, UMinus yf -> comparator_trm x yf
    | UMinus x, Minus (yd, ye) -> Gt
    | UMinus x, Plus (yb, yc) -> Gt
    | UMinus x, Const ya -> Gt
    | UMinus x, Var y -> Gt
    | Minus (x, xa), I2f yn -> Lt
    | Minus (x, xa), F2i ym -> Lt
    | Minus (x, xa), Mod (yk, yl) -> Lt
    | Minus (x, xa), Div (yi, yj) -> Lt
    | Minus (x, xa), Mult (yg, yh) -> Lt
    | Minus (x, xa), UMinus yf -> Lt
    | Minus (x, xa), Minus (yd, ye) ->
        (match comparator_trm x yd with Eqa -> comparator_trm xa ye | Lt -> Lt
          | Gt -> Gt)
    | Minus (x, xa), Plus (yb, yc) -> Gt
    | Minus (x, xa), Const ya -> Gt
    | Minus (x, xa), Var y -> Gt
    | Plus (x, xa), I2f yn -> Lt
    | Plus (x, xa), F2i ym -> Lt
    | Plus (x, xa), Mod (yk, yl) -> Lt
    | Plus (x, xa), Div (yi, yj) -> Lt
    | Plus (x, xa), Mult (yg, yh) -> Lt
    | Plus (x, xa), UMinus yf -> Lt
    | Plus (x, xa), Minus (yd, ye) -> Lt
    | Plus (x, xa), Plus (yb, yc) ->
        (match comparator_trm x yb with Eqa -> comparator_trm xa yc | Lt -> Lt
          | Gt -> Gt)
    | Plus (x, xa), Const ya -> Gt
    | Plus (x, xa), Var y -> Gt
    | Const x, I2f yn -> Lt
    | Const x, F2i ym -> Lt
    | Const x, Mod (yk, yl) -> Lt
    | Const x, Div (yi, yj) -> Lt
    | Const x, Mult (yg, yh) -> Lt
    | Const x, UMinus yf -> Lt
    | Const x, Minus (yd, ye) -> Lt
    | Const x, Plus (yb, yc) -> Lt
    | Const x, Const ya -> comparator_event_data x ya
    | Const x, Var y -> Gt
    | Var x, I2f yn -> Lt
    | Var x, F2i ym -> Lt
    | Var x, Mod (yk, yl) -> Lt
    | Var x, Div (yi, yj) -> Lt
    | Var x, Mult (yg, yh) -> Lt
    | Var x, UMinus yf -> Lt
    | Var x, Minus (yd, ye) -> Lt
    | Var x, Plus (yb, yc) -> Lt
    | Var x, Const ya -> Lt
    | Var x, Var y -> comparator_of (equal_nat, linorder_nat) x y;;

let ccompare_trma : (trm -> trm -> ordera) option = Some comparator_trm;;

let ccompare_trm = ({ccompare = ccompare_trma} : trm ccompare);;

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

type mregex = MSkip of nat | MTestPos of nat | MTestNeg of nat |
  MPlus of mregex * mregex | MTimes of mregex * mregex | MStar of mregex;;

let rec equal_mregexa
  x0 x1 = match x0, x1 with MTimes (x51, x52), MStar x6 -> false
    | MStar x6, MTimes (x51, x52) -> false
    | MPlus (x41, x42), MStar x6 -> false
    | MStar x6, MPlus (x41, x42) -> false
    | MPlus (x41, x42), MTimes (x51, x52) -> false
    | MTimes (x51, x52), MPlus (x41, x42) -> false
    | MTestNeg x3, MStar x6 -> false
    | MStar x6, MTestNeg x3 -> false
    | MTestNeg x3, MTimes (x51, x52) -> false
    | MTimes (x51, x52), MTestNeg x3 -> false
    | MTestNeg x3, MPlus (x41, x42) -> false
    | MPlus (x41, x42), MTestNeg x3 -> false
    | MTestPos x2, MStar x6 -> false
    | MStar x6, MTestPos x2 -> false
    | MTestPos x2, MTimes (x51, x52) -> false
    | MTimes (x51, x52), MTestPos x2 -> false
    | MTestPos x2, MPlus (x41, x42) -> false
    | MPlus (x41, x42), MTestPos x2 -> false
    | MTestPos x2, MTestNeg x3 -> false
    | MTestNeg x3, MTestPos x2 -> false
    | MSkip x1, MStar x6 -> false
    | MStar x6, MSkip x1 -> false
    | MSkip x1, MTimes (x51, x52) -> false
    | MTimes (x51, x52), MSkip x1 -> false
    | MSkip x1, MPlus (x41, x42) -> false
    | MPlus (x41, x42), MSkip x1 -> false
    | MSkip x1, MTestNeg x3 -> false
    | MTestNeg x3, MSkip x1 -> false
    | MSkip x1, MTestPos x2 -> false
    | MTestPos x2, MSkip x1 -> false
    | MStar x6, MStar y6 -> equal_mregexa x6 y6
    | MTimes (x51, x52), MTimes (y51, y52) ->
        equal_mregexa x51 y51 && equal_mregexa x52 y52
    | MPlus (x41, x42), MPlus (y41, y42) ->
        equal_mregexa x41 y41 && equal_mregexa x42 y42
    | MTestNeg x3, MTestNeg y3 -> equal_nata x3 y3
    | MTestPos x2, MTestPos y2 -> equal_nata x2 y2
    | MSkip x1, MSkip y1 -> equal_nata x1 y1;;

let equal_mregex = ({equal = equal_mregexa} : mregex equal);;

let rec comparator_mregex
  x0 x1 = match x0, x1 with MStar x, MStar yg -> comparator_mregex x yg
    | MStar x, MTimes (ye, yf) -> Gt
    | MStar x, MPlus (yc, yd) -> Gt
    | MStar x, MTestNeg yb -> Gt
    | MStar x, MTestPos ya -> Gt
    | MStar x, MSkip y -> Gt
    | MTimes (x, xa), MStar yg -> Lt
    | MTimes (x, xa), MTimes (ye, yf) ->
        (match comparator_mregex x ye with Eqa -> comparator_mregex xa yf
          | Lt -> Lt | Gt -> Gt)
    | MTimes (x, xa), MPlus (yc, yd) -> Gt
    | MTimes (x, xa), MTestNeg yb -> Gt
    | MTimes (x, xa), MTestPos ya -> Gt
    | MTimes (x, xa), MSkip y -> Gt
    | MPlus (x, xa), MStar yg -> Lt
    | MPlus (x, xa), MTimes (ye, yf) -> Lt
    | MPlus (x, xa), MPlus (yc, yd) ->
        (match comparator_mregex x yc with Eqa -> comparator_mregex xa yd
          | Lt -> Lt | Gt -> Gt)
    | MPlus (x, xa), MTestNeg yb -> Gt
    | MPlus (x, xa), MTestPos ya -> Gt
    | MPlus (x, xa), MSkip y -> Gt
    | MTestNeg x, MStar yg -> Lt
    | MTestNeg x, MTimes (ye, yf) -> Lt
    | MTestNeg x, MPlus (yc, yd) -> Lt
    | MTestNeg x, MTestNeg yb -> comparator_of (equal_nat, linorder_nat) x yb
    | MTestNeg x, MTestPos ya -> Gt
    | MTestNeg x, MSkip y -> Gt
    | MTestPos x, MStar yg -> Lt
    | MTestPos x, MTimes (ye, yf) -> Lt
    | MTestPos x, MPlus (yc, yd) -> Lt
    | MTestPos x, MTestNeg yb -> Lt
    | MTestPos x, MTestPos ya -> comparator_of (equal_nat, linorder_nat) x ya
    | MTestPos x, MSkip y -> Gt
    | MSkip x, MStar yg -> Lt
    | MSkip x, MTimes (ye, yf) -> Lt
    | MSkip x, MPlus (yc, yd) -> Lt
    | MSkip x, MTestNeg yb -> Lt
    | MSkip x, MTestPos ya -> Lt
    | MSkip x, MSkip y -> comparator_of (equal_nat, linorder_nat) x y;;

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

let finite_UNIV_enata : (enat, bool) phantom = Phantom false;;

let finite_UNIV_enat = ({finite_UNIV = finite_UNIV_enata} : enat finite_UNIV);;

let rec less_enat x0 q = match x0, q with Infinity_enat, q -> false
                    | Enat m, Infinity_enat -> true
                    | Enat m, Enat n -> less_nat m n;;

let ccompare_enata : (enat -> enat -> ordera) option
  = Some (fun x y ->
           (if equal_enat x y then Eqa
             else (if less_enat x y then Lt else Gt)));;

let ccompare_enat = ({ccompare = ccompare_enata} : enat ccompare);;

let rec equal_proda _A _B (x1, x2) (y1, y2) = eq _A x1 y1 && eq _B x2 y2;;

let rec equal_prod _A _B = ({equal = equal_proda _A _B} : ('a * 'b) equal);;

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

let rec mapa f x1 = match f, x1 with f, [] -> []
               | f, x21 :: x22 -> f x21 :: mapa f x22;;

let rec product x0 uu = match x0, uu with [], uu -> []
                  | x :: xs, ys -> mapa (fun a -> (x, a)) ys @ product xs ys;;

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

let rec compare_string8 x = comparator_of (equal_string8, linorder_string8) x;;

let ccompare_string8a : (string -> string -> ordera) option
  = Some compare_string8;;

let ccompare_string8 = ({ccompare = ccompare_string8a} : string ccompare);;

let mapping_impl_string8a : (string, mapping_impla) phantom
  = Phantom Mapping_RBT;;

let mapping_impl_string8 =
  ({mapping_impl = mapping_impl_string8a} : string mapping_impl);;

type rec_safety = Unused | PastRec | NonFutuRec | AnyRec;;

let rec equal_rec_safety x0 x1 = match x0, x1 with NonFutuRec, AnyRec -> false
                           | AnyRec, NonFutuRec -> false
                           | PastRec, AnyRec -> false
                           | AnyRec, PastRec -> false
                           | PastRec, NonFutuRec -> false
                           | NonFutuRec, PastRec -> false
                           | Unused, AnyRec -> false
                           | AnyRec, Unused -> false
                           | Unused, NonFutuRec -> false
                           | NonFutuRec, Unused -> false
                           | Unused, PastRec -> false
                           | PastRec, Unused -> false
                           | AnyRec, AnyRec -> true
                           | NonFutuRec, NonFutuRec -> true
                           | PastRec, PastRec -> true
                           | Unused, Unused -> true;;

let ceq_rec_safetya : (rec_safety -> rec_safety -> bool) option
  = Some equal_rec_safety;;

let ceq_rec_safety = ({ceq = ceq_rec_safetya} : rec_safety ceq);;

let set_impl_rec_safetya : (rec_safety, set_impla) phantom = Phantom Set_DList;;

let set_impl_rec_safety =
  ({set_impl = set_impl_rec_safetya} : rec_safety set_impl);;

let rec comparator_rec_safety x0 x1 = match x0, x1 with AnyRec, AnyRec -> Eqa
                                | AnyRec, NonFutuRec -> Gt
                                | AnyRec, PastRec -> Gt
                                | AnyRec, Unused -> Gt
                                | NonFutuRec, AnyRec -> Lt
                                | NonFutuRec, NonFutuRec -> Eqa
                                | NonFutuRec, PastRec -> Gt
                                | NonFutuRec, Unused -> Gt
                                | PastRec, AnyRec -> Lt
                                | PastRec, NonFutuRec -> Lt
                                | PastRec, PastRec -> Eqa
                                | PastRec, Unused -> Gt
                                | Unused, AnyRec -> Lt
                                | Unused, NonFutuRec -> Lt
                                | Unused, PastRec -> Lt
                                | Unused, Unused -> Eqa;;

let ccompare_rec_safetya : (rec_safety -> rec_safety -> ordera) option
  = Some comparator_rec_safety;;

let ccompare_rec_safety =
  ({ccompare = ccompare_rec_safetya} : rec_safety ccompare);;

let equal_event_data = ({equal = equal_event_dataa} : event_data equal);;

let rec less_eq_event_data
  x0 x1 = match x0, x1 with EInt x, EInt y -> Z.leq x y
    | EFloat x, EFloat y -> Stdlib.(<=) x y
    | EString x, EString y -> Stdlib.(<=) x y
    | EFloat v, EInt va -> failwith "undefined"
    | EFloat v, EString va -> failwith "undefined"
    | EString v, EInt va -> failwith "undefined"
    | EString v, EFloat va -> failwith "undefined"
    | EInt va, EFloat v -> failwith "undefined"
    | EInt va, EString v -> failwith "undefined";;

let rec less_event_data
  x y = less_eq_event_data x y && not (less_eq_event_data y x);;

let ord_event_data =
  ({less_eq = less_eq_event_data; less = less_event_data} : event_data ord);;

let ceq_event_dataa : (event_data -> event_data -> bool) option
  = Some equal_event_dataa;;

let ceq_event_data = ({ceq = ceq_event_dataa} : event_data ceq);;

let set_impl_event_dataa : (event_data, set_impla) phantom = Phantom Set_RBT;;

let set_impl_event_data =
  ({set_impl = set_impl_event_dataa} : event_data set_impl);;

let finite_UNIV_event_dataa : (event_data, bool) phantom = Phantom false;;

let finite_UNIV_event_data =
  ({finite_UNIV = finite_UNIV_event_dataa} : event_data finite_UNIV);;

let ccompare_event_dataa : (event_data -> event_data -> ordera) option
  = Some comparator_event_data;;

let ccompare_event_data =
  ({ccompare = ccompare_event_dataa} : event_data ccompare);;

type agg_type = Agg_Cnt | Agg_Min | Agg_Max | Agg_Sum | Agg_Avg | Agg_Med;;

type ty = TInt | TFloat | TString;;

type 'a aggargs_ext =
  Aggargs_ext of
    nat set * nat * bool * nat * (agg_type * ty) * ty list * trm * 'a;;

type i = Abs_I of ((nat -> bool) * ((nat -> bool) * bool));;

type 'a args_ext =
  Args_ext of
    i * nat * nat set * nat set * bool * unit aggargs_ext option * 'a;;

type 'a queue = Abs_queue of ('a list * 'a list);;

type 'a mbuf_t = MBuf2_t of 'a queue;;

type mconstraint = MEq | MLess | MLessEq;;

type pred_mode = Copy | Simple | Match;;

type ('b, 'a) alist = Alist of ('b * 'a) list;;

type ('a, 'b) mapping = Assoc_List_Mapping of ('a, 'b) alist |
  RBT_Mapping of ('a, 'b) mapping_rbt | Mapping of ('a -> 'b option);;

type mtrm = MVar of nat | MConst of event_data;;

type ('a, 'b) meformula = MRel of ((event_data option) list) set |
  MPred of string * trm list * pred_mode |
  MLet of string * nat * ('a, 'b) meformula * ('a, 'b) meformula |
  MLetPast of
    string * nat * ('a, 'b) meformula * ('a, 'b) meformula * nat *
      ((event_data option) list) set option
  | MAnd of
      nat set * ('a, 'b) meformula * bool * nat set * ('a, 'b) meformula *
        (((event_data option) list) set mbuf_t *
          ((event_data option) list) set mbuf_t)
  | MAndAssign of ('a, 'b) meformula * (nat * trm) |
  MAndRel of ('a, 'b) meformula * (trm * (bool * (mconstraint * trm))) |
  MAnds of
    nat set list * nat set list * ('a, 'b) meformula list *
      ((event_data option) list) set mbuf_t list
  | MOr of
      ('a, 'b) meformula * ('a, 'b) meformula *
        (((event_data option) list) set mbuf_t *
          ((event_data option) list) set mbuf_t)
  | MNeg of ('a, 'b) meformula | MExists of ('a, 'b) meformula |
  MAgg of unit aggargs_ext * ('a, 'b) meformula |
  MPrev of
    i * ('a, 'b) meformula * bool * ((event_data option) list) set mbuf_t *
      nat mbuf_t
  | MNext of i * ('a, 'b) meformula * bool * nat mbuf_t |
  MSince of
    unit args_ext * ('a, 'b) meformula * ('a, 'b) meformula *
      (((event_data option) list) set mbuf_t *
        (((event_data option) list) set mbuf_t * (nat mbuf_t * bool))) *
      'a
  | MUntil of
      unit args_ext * ('a, 'b) meformula * ('a, 'b) meformula *
        (((event_data option) list) set mbuf_t *
          ((event_data option) list) set mbuf_t) *
        nat mbuf_t * nat * 'b
  | MMatchP of
      i * mregex * mregex list * ('a, 'b) meformula list *
        ((event_data option) list) set mbuf_t list * nat mbuf_t *
        (nat * (mregex, ((event_data option) list) set) mapping) list
  | MMatchF of
      i * mregex * mregex list * ('a, 'b) meformula list *
        ((event_data option) list) set mbuf_t list * nat mbuf_t * nat *
        (nat *
          (((event_data option) list) set list *
            ((event_data option) list) set)) list
  | MTP of mtrm * nat | MTS of mtrm;;

let rec size_list
  x xa1 = match x, xa1 with x, [] -> zero_nata
    | x, x21 :: x22 ->
        plus_nata (plus_nata (x x21) (size_list x x22)) (suc zero_nata);;

let rec size_meformulaa
  = function MRel x1 -> zero_nata
    | MPred (x21, x22, x23) -> zero_nata
    | MLet (x31, x32, x33, x34) ->
        plus_nata (plus_nata (size_meformulaa x33) (size_meformulaa x34))
          (suc zero_nata)
    | MLetPast (x41, x42, x43, x44, x45, x46) ->
        plus_nata (plus_nata (size_meformulaa x43) (size_meformulaa x44))
          (suc zero_nata)
    | MAnd (x51, x52, x53, x54, x55, x56) ->
        plus_nata (plus_nata (size_meformulaa x52) (size_meformulaa x55))
          (suc zero_nata)
    | MAndAssign (x61, x62) -> plus_nata (size_meformulaa x61) (suc zero_nata)
    | MAndRel (x71, x72) -> plus_nata (size_meformulaa x71) (suc zero_nata)
    | MAnds (x81, x82, x83, x84) ->
        plus_nata (size_list size_meformulaa x83) (suc zero_nata)
    | MOr (x91, x92, x93) ->
        plus_nata (plus_nata (size_meformulaa x91) (size_meformulaa x92))
          (suc zero_nata)
    | MNeg x10 -> plus_nata (size_meformulaa x10) (suc zero_nata)
    | MExists x11 -> plus_nata (size_meformulaa x11) (suc zero_nata)
    | MAgg (x121, x122) -> plus_nata (size_meformulaa x122) (suc zero_nata)
    | MPrev (x131, x132, x133, x134, x135) ->
        plus_nata (size_meformulaa x132) (suc zero_nata)
    | MNext (x141, x142, x143, x144) ->
        plus_nata (size_meformulaa x142) (suc zero_nata)
    | MSince (x151, x152, x153, x154, x155) ->
        plus_nata (plus_nata (size_meformulaa x152) (size_meformulaa x153))
          (suc zero_nata)
    | MUntil (x161, x162, x163, x164, x165, x166, x167) ->
        plus_nata (plus_nata (size_meformulaa x162) (size_meformulaa x163))
          (suc zero_nata)
    | MMatchP (x171, x172, x173, x174, x175, x176, x177) ->
        plus_nata (size_list size_meformulaa x174) (suc zero_nata)
    | MMatchF (x181, x182, x183, x184, x185, x186, x187, x188) ->
        plus_nata (size_list size_meformulaa x184) (suc zero_nata)
    | MTP (x191, x192) -> zero_nata
    | MTS x20 -> zero_nata;;

type 'a size = {size : 'a -> nat};;
let size _A = _A.size;;

let size_meformula = ({size = size_meformulaa} : ('a, 'b) meformula size);;

type int = Int_of_integer of Z.t;;

type 'a tree = Leaf | Node of 'a tree * 'a * 'a tree;;

type cmp_val = LT | EQ | GT;;

type 'a regex = Skip of nat | Test of 'a | Plusa of 'a regex * 'a regex |
  Times of 'a regex * 'a regex | Star of 'a regex;;

type safety = Strict | Lax;;

type ('a, 'b) sum = Inl of 'a | Inr of 'b;;

type tysym = TAny of nat | TNum of nat | TCst of ty;;

type modality = Past | Futu;;

type 'a formula = Pred of string * trm list |
  Let of string * 'a formula * 'a formula |
  LetPast of string * 'a formula * 'a formula | Eq of trm * trm |
  Less of trm * trm | LessEq of trm * trm | Neg of 'a formula |
  Or of 'a formula * 'a formula | And of 'a formula * 'a formula |
  Ands of 'a formula list | Exists of 'a * 'a formula |
  Agg of nat * (agg_type * 'a) * 'a list * trm * 'a formula |
  Prev of i * 'a formula | Next of i * 'a formula |
  Since of 'a formula * i * 'a formula | Until of 'a formula * i * 'a formula |
  MatchF of i * 'a formula regex | MatchP of i * 'a formula regex | TP of trm |
  TS of trm;;

type 'a wf_idx =
  Abs_wf_idx of
    (nat *
      (nat set *
        (nat set * ((('a option) list), (('a option) list) set) mapping)));;

type 'a wf_set = Abs_wf_set of (nat * (nat set * (('a option) list) set));;

type ('a, 'b) mformula = Rep_meformula of ('a, 'b) meformula;;

type 'a wf_table = Wf_table_of_wf_set of 'a wf_set |
  Wf_table_of_idx of 'a wf_idx;;

type typea = IntT | StringT;;

type 'a wf_wbt = Abs_wf_wbt of ('a * nat) tree;;

type 'a treelist = Collapse of 'a wf_wbt;;

type list_aux = LInt of Z.t treelist | LString of string treelist;;

type aggaux = CntAux of (((event_data option) list), nat) mapping |
  SumAux of (((event_data option) list), (nat * Z.t)) mapping |
  RankAux of ((((event_data option) list), list_aux) mapping * typea);;

type ('b, 'a) comp_fun_idem = Abs_comp_fun_idem of ('b -> 'a -> 'a);;

type 'a semilattice_set = Abs_semilattice_set of ('a -> 'a -> 'a);;

type ('a, 'b, 'c) mstate_ext =
  Mestate of nat * nat * ('a, 'b) mformula * nat * nat queue * 'c;;

type ('b, 'a) comp_fun_commute = Abs_comp_fun_commute of ('b -> 'a -> 'a);;

type 'a x_a_queue_x_a_option_prod_x_x_x_a_list_x_a_list_prod_x_a_option_prod =
  Abs_x_a_queue_x_a_option_prod_x_x_x_a_list_x_a_list_prod_x_a_option_prod of
    ('a option * ('a list * 'a list));;

let rec cmp (_A1, _A2)
  x y = (if less _A2.order_linorder.preorder_order.ord_preorder x y then LT
          else (if eq _A1 x y then EQ else GT));;

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
    (if equal_nata n zero_nata then x else nth xs (minus_nata n one_nata));;

let rec rev xs = fold (fun a b -> a :: b) xs [];;

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
        (if equal_nata n zero_nata then x :: xs
          else drop (minus_nata n one_nata) xs);;

let rec maps f x1 = match f, x1 with f, [] -> []
               | f, x :: xs -> f x @ maps f xs;;

let rec take
  n x1 = match n, x1 with n, [] -> []
    | n, x :: xs ->
        (if equal_nata n zero_nata then []
          else x :: take (minus_nata n one_nata) xs);;

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

let rec combinea
  xa0 x = match xa0, x with Empty, x -> x
    | Branch (v, va, vb, vc, vd), Empty -> Branch (v, va, vb, vc, vd)
    | Branch (R, a, k, x, b), Branch (R, c, s, y, d) ->
        (match combinea b c
          with Empty -> Branch (R, a, k, x, Branch (R, Empty, s, y, d))
          | Branch (R, b2, t, z, c2) ->
            Branch (R, Branch (R, a, k, x, b2), t, z, Branch (R, c2, s, y, d))
          | Branch (B, b2, t, z, c2) ->
            Branch (R, a, k, x, Branch (R, Branch (B, b2, t, z, c2), s, y, d)))
    | Branch (B, a, k, x, b), Branch (B, c, s, y, d) ->
        (match combinea b c
          with Empty -> balance_left a k x (Branch (B, Empty, s, y, d))
          | Branch (R, b2, t, z, c2) ->
            Branch (R, Branch (B, a, k, x, b2), t, z, Branch (B, c2, s, y, d))
          | Branch (B, b2, t, z, c2) ->
            balance_left a k x (Branch (B, Branch (B, b2, t, z, c2), s, y, d)))
    | Branch (B, va, vb, vc, vd), Branch (R, b, k, x, c) ->
        Branch (R, combinea (Branch (B, va, vb, vc, vd)) b, k, x, c)
    | Branch (R, a, k, x, b), Branch (B, va, vb, vc, vd) ->
        Branch (R, a, k, x, combinea b (Branch (B, va, vb, vc, vd)));;

let rec rbt_comp_del
  c x xa2 = match c, x, xa2 with c, x, Empty -> Empty
    | c, x, Branch (uu, a, y, s, b) ->
        (match c x y with Eqa -> combinea a b
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

let rec deleteb _A
  xb xc =
    Mapping_RBTa (rbt_comp_delete (the (ccompare _A)) xb (impl_ofa _A xc));;

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
          | Some _ -> RBT_set (deleteb _A2 x rbt))
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
    | f, Set_Monad xs -> Set_Monad (mapa f xs);;

let rec foldl f a x2 = match f, a, x2 with f, a, [] -> a
                | f, a, x :: xs -> foldl f (f a x) xs;;

let rec foldr f x1 = match f, x1 with f, [] -> id
                | f, x :: xs -> comp (f x) (foldr f xs);;

let rec map_of _A
  x0 k = match x0, k with
    (l, v) :: ps, k -> (if eq _A l k then Some v else map_of _A ps k)
    | [], k -> None;;

let rec funpow
  n f = (if equal_nata n zero_nata then id
          else comp f (funpow (minus_nata n one_nata) f));;

let wild : 'a regex = Skip one_nata;;

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

let rec map_option f x1 = match f, x1 with f, None -> None
                     | f, Some x2 -> Some (f x2);;

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
        then insert (ceq_nat, ccompare_nat) (minus_nata x b)
               (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata))
        else set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata))
    | b, Const uu ->
        set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)
    | b, Plus (x, y) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi_trm b x) (fvi_trm b y)
    | b, Minus (x, y) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi_trm b x) (fvi_trm b y)
    | b, UMinus x -> fvi_trm b x
    | b, Mult (x, y) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi_trm b x) (fvi_trm b y)
    | b, Div (x, y) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi_trm b x) (fvi_trm b y)
    | b, Mod (x, y) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi_trm b x) (fvi_trm b y)
    | b, F2i x -> fvi_trm b x
    | b, I2f x -> fvi_trm b x;;

let rec fv_regex (_B1, _B2, _B3)
  fv x1 = match fv, x1 with fv, Skip n -> bot_set (_B1, _B2, _B3)
    | fv, Test phi -> fv phi
    | fv, Plusa (r, s) ->
        sup_seta (_B1, _B2) (fv_regex (_B1, _B2, _B3) fv r)
          (fv_regex (_B1, _B2, _B3) fv s)
    | fv, Times (r, s) ->
        sup_seta (_B1, _B2) (fv_regex (_B1, _B2, _B3) fv r)
          (fv_regex (_B1, _B2, _B3) fv s)
    | fv, Star r -> fv_regex (_B1, _B2, _B3) fv r;;

let rec set_aux (_A1, _A2)
  = function Set_Monada -> (fun a -> Set_Monad a)
    | Set_Choose ->
        (match ccompare _A2
          with None ->
            (match ceq _A1 with None -> (fun a -> Set_Monad a)
              | Some _ ->
                foldl (fun s x -> insert (_A1, _A2) x s)
                  (DList_set (emptyb _A1)))
          | Some _ ->
            foldl (fun s x -> insert (_A1, _A2) x s) (RBT_set (emptyc _A2)))
    | impl ->
        foldl (fun s x -> insert (_A1, _A2) x s) (set_empty (_A1, _A2) impl);;

let rec set (_A1, _A2, _A3)
  xs = set_aux (_A1, _A2) (of_phantom (set_impl _A3)) xs;;

let rec fvi
  b x1 = match b, x1 with
    b, Pred (r, ts) ->
      sup_setb
        (finite_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
          set_impl_nat)
        (image (ceq_trm, ccompare_trm)
          ((ceq_set
             (cenum_nat, ceq_nat,
               cproper_interval_nat.ccompare_cproper_interval)),
            (ccompare_set
              (finite_UNIV_nat, ceq_nat, cproper_interval_nat, set_impl_nat)),
            set_impl_set)
          (fvi_trm b) (set (ceq_trm, ccompare_trm, set_impl_trm) ts))
    | b, Let (p, phi, psi) -> fvi b psi
    | b, LetPast (p, phi, psi) -> fvi b psi
    | b, Eq (t1, t2) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi_trm b t1) (fvi_trm b t2)
    | b, Less (t1, t2) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi_trm b t1) (fvi_trm b t2)
    | b, LessEq (t1, t2) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi_trm b t1) (fvi_trm b t2)
    | b, Neg phi -> fvi b phi
    | b, Or (phi, psi) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi b phi) (fvi b psi)
    | b, And (phi, psi) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi b phi) (fvi b psi)
    | b, Ands phi_s ->
        (let xs = mapa (fvi b) phi_s in
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
    | b, Exists (t, phi) -> fvi (suc b) phi
    | b, Agg (y, omega, tys, f, phi) ->
        sup_seta (ceq_nat, ccompare_nat)
          (sup_seta (ceq_nat, ccompare_nat)
            (fvi (plus_nata b (size_lista tys)) phi)
            (fvi_trm (plus_nata b (size_lista tys)) f))
          (if less_eq_nat b y
            then insert (ceq_nat, ccompare_nat) (minus_nata y b)
                   (set_empty (ceq_nat, ccompare_nat)
                     (of_phantom set_impl_nata))
            else set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata))
    | b, Prev (i, phi) -> fvi b phi
    | b, Next (i, phi) -> fvi b phi
    | b, Since (phi, i, psi) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi b phi) (fvi b psi)
    | b, Until (phi, i, psi) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi b phi) (fvi b psi)
    | b, MatchF (i, r) ->
        fv_regex (ceq_nat, ccompare_nat, set_impl_nat) (fvi b) r
    | b, MatchP (i, r) ->
        fv_regex (ceq_nat, ccompare_nat, set_impl_nat) (fvi b) r
    | b, TP t -> fvi_trm b t
    | b, TS t -> fvi_trm b t;;

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

let rec nfv
  phi = maxa (ceq_nat, ccompare_nat, lattice_nat, linorder_nat)
          (insert (ceq_nat, ccompare_nat) zero_nata
            (image (ceq_nat, ccompare_nat) (ceq_nat, ccompare_nat, set_impl_nat)
              suc (fvi zero_nata phi)));;

let rec fun_upd _A f a b = (fun x -> (if eq _A x a then b else f x));;

let rec membera _A x0 y = match x0, y with [], y -> false
                     | x :: xs, y -> eq _A x y || membera _A xs y;;

let rec mTimesR
  r s = image (ceq_mregex, ccompare_mregex)
          (ceq_mregex, ccompare_mregex, set_impl_mregex)
          (fun ra -> MTimes (ra, s)) r;;

let rec lpd
  = function
    MSkip n ->
      (if equal_nata n zero_nata
        then set_empty (ceq_mregex, ccompare_mregex)
               (of_phantom set_impl_mregexa)
        else insert (ceq_mregex, ccompare_mregex)
               (MSkip (minus_nata n one_nata))
               (set_empty (ceq_mregex, ccompare_mregex)
                 (of_phantom set_impl_mregexa)))
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
    MSkip n ->
      (if equal_nata n zero_nata
        then set_empty (ceq_mregex, ccompare_mregex)
               (of_phantom set_impl_mregexa)
        else insert (ceq_mregex, ccompare_mregex)
               (MSkip (minus_nata n one_nata))
               (set_empty (ceq_mregex, ccompare_mregex)
                 (of_phantom set_impl_mregexa)))
    | MTestPos phi ->
        set_empty (ceq_mregex, ccompare_mregex) (of_phantom set_impl_mregexa)
    | MTestNeg phi ->
        set_empty (ceq_mregex, ccompare_mregex) (of_phantom set_impl_mregexa)
    | MPlus (r, s) -> sup_seta (ceq_mregex, ccompare_mregex) (rpd r) (rpd s)
    | MTimes (r, s) ->
        sup_seta (ceq_mregex, ccompare_mregex) (mTimesL r (rpd s)) (rpd r)
    | MStar r -> mTimesL (MStar r) (rpd r);;

let rec update _A
  k v x2 = match k, v, x2 with k, v, [] -> [(k, v)]
    | k, v, p :: ps ->
        (if eq _A (fst p) k then (k, v) :: ps else p :: update _A k v ps);;

let empty : ('a, 'b) alist = Alist [];;

let rec remdups _A
  = function [] -> []
    | x :: xs ->
        (if membera _A xs x then remdups _A xs else x :: remdups _A xs);;

let rec map
  f x1 = match f, x1 with f, Empty -> Empty
    | f, Branch (c, lt, k, v, rt) -> Branch (c, map f lt, k, f k v, map f rt);;

let rec mapb _A xb xc = Mapping_RBTa (map xb (impl_ofa _A xc));;

let rec impl_of (Alist x) = x;;

let rec keysc (_A1, _A2, _A3) xa = set (_A1, _A2, _A3) (mapa fst (impl_of xa));;

let rec keys (_A1, _A2, _A3, _A4)
  = function RBT_Mapping t -> RBT_set (mapb _A3 (fun _ _ -> ()) t)
    | Assoc_List_Mapping al -> keysc (_A2, _A3, _A4) al
    | Mapping m -> collect _A1 (fun k -> not (is_none (m k)));;

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

let rec map_regex
  f x1 = match f, x1 with f, Skip x1 -> Skip x1
    | f, Test x2 -> Test (f x2)
    | f, Plusa (x31, x32) -> Plusa (map_regex f x31, map_regex f x32)
    | f, Times (x41, x42) -> Times (map_regex f x41, map_regex f x42)
    | f, Star x5 -> Star (map_regex f x5);;

let rec map_formula
  f x1 = match f, x1 with f, Pred (x11, x12) -> Pred (x11, x12)
    | f, Let (x21, x22, x23) -> Let (x21, map_formula f x22, map_formula f x23)
    | f, LetPast (x31, x32, x33) ->
        LetPast (x31, map_formula f x32, map_formula f x33)
    | f, Eq (x41, x42) -> Eq (x41, x42)
    | f, Less (x51, x52) -> Less (x51, x52)
    | f, LessEq (x61, x62) -> LessEq (x61, x62)
    | f, Neg x7 -> Neg (map_formula f x7)
    | f, Or (x81, x82) -> Or (map_formula f x81, map_formula f x82)
    | f, And (x91, x92) -> And (map_formula f x91, map_formula f x92)
    | f, Ands x10 -> Ands (mapa (map_formula f) x10)
    | f, Exists (x111, x112) -> Exists (f x111, map_formula f x112)
    | f, Agg (x121, x122, x123, x124, x125) ->
        Agg (x121, map_prod id f x122, mapa f x123, x124, map_formula f x125)
    | f, Prev (x131, x132) -> Prev (x131, map_formula f x132)
    | f, Next (x141, x142) -> Next (x141, map_formula f x142)
    | f, Since (x151, x152, x153) ->
        Since (map_formula f x151, x152, map_formula f x153)
    | f, Until (x161, x162, x163) ->
        Until (map_formula f x161, x162, map_formula f x163)
    | f, MatchF (x171, x172) -> MatchF (x171, map_regex (map_formula f) x172)
    | f, MatchP (x181, x182) -> MatchP (x181, map_regex (map_formula f) x182)
    | f, TP x19 -> TP x19
    | f, TS x20 -> TS x20;;

let rec binda m f = (match m with Inl a -> Inl a | Inr a -> f a);;

let rec map_sig f s = comp (map_option (mapa f)) s;;

let rec check_two_formulas
  check s e phi psi =
    binda (check s e phi)
      (fun f ->
        binda (check (map_sig f s) (comp f e) (map_formula f psi))
          (fun fa -> Inr (comp fa f)));;

let rec new_type_symbol
  t = (match t with TAny n -> TAny (suc n) | TNum n -> TNum (suc n)
        | TCst a -> TCst a);;

let rec equal_ty x0 x1 = match x0, x1 with TFloat, TString -> false
                   | TString, TFloat -> false
                   | TInt, TString -> false
                   | TString, TInt -> false
                   | TInt, TFloat -> false
                   | TFloat, TInt -> false
                   | TString, TString -> true
                   | TFloat, TFloat -> true
                   | TInt, TInt -> true;;

let rec equal_tysym x0 x1 = match x0, x1 with TNum x2, TCst x3 -> false
                      | TCst x3, TNum x2 -> false
                      | TAny x1, TCst x3 -> false
                      | TCst x3, TAny x1 -> false
                      | TAny x1, TNum x2 -> false
                      | TNum x2, TAny x1 -> false
                      | TCst x3, TCst y3 -> equal_ty x3 y3
                      | TNum x2, TNum y2 -> equal_nata x2 y2
                      | TAny x1, TAny y1 -> equal_nata x1 y1;;

let rec catch_error m f = (match m with Inl a -> f a | Inr a -> Inr a);;

let rec str_of_tysym = function TCst TInt -> "int"
                       | TCst TFloat -> "float"
                       | TCst TString -> "string"
                       | TNum uu -> "numeric"
                       | TAny uv -> "any";;

let rec update_env
  x e = (let (tnew, told) = x in
          (fun v -> (if equal_tysym v told then tnew else v)));;

let rec min_type
  x0 x1 = match x0, x1 with
    TNum a, TNum b ->
      Inr (if less_eq_nat a b then (TNum a, TNum b) else (TNum b, TNum a))
    | TAny a, TAny b ->
        Inr (if less_eq_nat a b then (TAny a, TAny b) else (TAny b, TAny a))
    | TNum v, TAny y -> Inr (TNum v, TAny y)
    | TCst v, TAny y -> Inr (TCst v, TAny y)
    | TAny y, TNum v -> Inr (TNum v, TAny y)
    | TAny y, TCst v -> Inr (TCst v, TAny y)
    | TCst TString, TNum uu -> Inl ""
    | TNum uv, TCst TString -> Inl ""
    | TCst TInt, TNum y -> Inr (TCst TInt, TNum y)
    | TCst TFloat, TNum y -> Inr (TCst TFloat, TNum y)
    | TNum y, TCst TInt -> Inr (TCst TInt, TNum y)
    | TNum y, TCst TFloat -> Inr (TCst TFloat, TNum y)
    | TCst x, TCst y ->
        (if equal_ty x y then Inr (TCst x, TCst y) else Inl "");;

let rec clash_propagate
  t1 t2 e =
    catch_error (binda (min_type t1 t2) (fun k -> Inr (update_env k e)))
      (fun _ ->
        Inl ((("clash of types " ^ str_of_tysym t1) ^ " and ") ^
              str_of_tysym t2));;

let rec check_binop
  check_trm e typ t1 t2 exp_typ =
    binda (clash_propagate exp_typ typ e)
      (fun f ->
        binda (check_trm (comp f e) (f typ) t1)
          (fun fa ->
            binda (check_trm (comp (comp fa f) e) (comp fa f typ) t2)
              (fun fb -> Inr (comp (comp fb fa) f))));;

let rec ty_of = function EInt uu -> TInt
                | EFloat uv -> TFloat
                | EString uw -> TString;;

let rec check_trm
  e typ x2 = match e, typ, x2 with e, typ, Var v -> clash_propagate (e v) typ e
    | e, typ, Const c -> clash_propagate (TCst (ty_of c)) typ e
    | e, typ, F2i t ->
        binda (clash_propagate typ (TCst TInt) e)
          (fun f ->
            binda (check_trm (comp f e) (TCst TFloat) t)
              (fun fa ->
                Inr (fun ta ->
                      (if equal_tysym ta typ then TCst TInt
                        else comp fa f ta))))
    | e, typ, I2f t ->
        binda (clash_propagate typ (TCst TFloat) e)
          (fun f ->
            binda (check_trm (comp f e) (TCst TInt) t)
              (fun fa ->
                Inr (fun ta ->
                      (if equal_tysym ta typ then TCst TFloat
                        else comp fa f ta))))
    | e, typ, UMinus t ->
        binda (clash_propagate (TNum zero_nata) (new_type_symbol typ)
                (comp new_type_symbol e))
          (fun f ->
            binda (check_trm (comp (comp f new_type_symbol) e)
                    (f (new_type_symbol typ)) t)
              (fun fa -> Inr (comp (comp fa f) new_type_symbol)))
    | e, typ, Plus (t1, t2) ->
        binda (check_binop check_trm (comp new_type_symbol e)
                (new_type_symbol typ) t1 t2 (TNum zero_nata))
          (fun f -> Inr (comp f new_type_symbol))
    | e, typ, Minus (t1, t2) ->
        binda (check_binop check_trm (comp new_type_symbol e)
                (new_type_symbol typ) t1 t2 (TNum zero_nata))
          (fun f -> Inr (comp f new_type_symbol))
    | e, typ, Mult (t1, t2) ->
        binda (check_binop check_trm (comp new_type_symbol e)
                (new_type_symbol typ) t1 t2 (TNum zero_nata))
          (fun f -> Inr (comp f new_type_symbol))
    | e, typ, Div (t1, t2) ->
        binda (check_binop check_trm (comp new_type_symbol e)
                (new_type_symbol typ) t1 t2 (TNum zero_nata))
          (fun f -> Inr (comp f new_type_symbol))
    | e, typ, Mod (t1, t2) -> check_binop check_trm e typ t1 t2 (TCst TInt);;

let rec check_comparison
  e t1 t2 =
    binda (check_trm (comp new_type_symbol e) (TAny zero_nata) t1)
      (fun f ->
        binda (check_trm (comp (comp f new_type_symbol) e) (f (TAny zero_nata))
                t2)
          (fun fa -> Inr (comp (comp fa f) new_type_symbol)));;

let rec agg_trm_tysym = function Agg_Sum -> TNum zero_nata
                        | Agg_Cnt -> TAny zero_nata
                        | Agg_Avg -> TNum zero_nata
                        | Agg_Med -> TNum zero_nata
                        | Agg_Min -> TAny zero_nata
                        | Agg_Max -> TAny zero_nata;;

let rec t_res_tysym x0 t = match x0, t with Agg_Sum, t -> t
                      | Agg_Cnt, uu -> TCst TInt
                      | Agg_Avg, uv -> TCst TFloat
                      | Agg_Med, uw -> TCst TFloat
                      | Agg_Min, t -> t
                      | Agg_Max, t -> t;;

let rec check_regex
  check s e x3 = match check, s, e, x3 with check, s, e, Skip l -> Inr id
    | check, s, e, Test phi -> check s e phi
    | check, sa, e, Plusa (r, s) ->
        binda (check_regex check sa e r)
          (fun f ->
            binda (check_regex check (map_sig f sa) (comp f e)
                    (map_regex (map_formula f) s))
              (fun fa -> Inr (comp fa f)))
    | check, sa, e, Times (r, s) ->
        binda (check_regex check sa e r)
          (fun f ->
            binda (check_regex check (map_sig f sa) (comp f e)
                    (map_regex (map_formula f) s))
              (fun fa -> Inr (comp fa f)))
    | check, s, e, Star r -> check_regex check s e r;;

let rec check_pred
  p e x2 x3 = match p, e, x2, x3 with
    p, e, trm :: trms, t :: ts ->
      binda (check_trm e t trm)
        (fun f ->
          binda (check_pred p (comp f e) trms (mapa f ts))
            (fun fa -> Inr (comp fa f)))
    | p, e, [], [] -> Inr id
    | p, e, [], v :: va -> Inl ("wrong arity for predicate " ^ id p)
    | p, e, v :: va, [] -> Inl ("wrong arity for predicate " ^ id p);;

let rec check_ands_f
  check s e =
    (fun phi f_op ->
      binda f_op
        (fun f ->
          binda (check (map_sig f s) (comp f e) (map_formula f phi))
            (fun fa -> Inr (comp fa f))));;

let rec check_ands
  check s e phi_s = foldr (check_ands_f check s e) phi_s (Inr id);;

let rec agg_tysenv
  e tys =
    (fun z ->
      (if less_nat z (size_lista tys) then nth tys z
        else e (minus_nata z (size_lista tys))));;

let rec tabulate
  f x n =
    (if equal_nata n zero_nata then []
      else f x :: tabulate f (suc x) (minus_nata n one_nata));;

let rec check
  s e x2 = match s, e, x2 with
    s, e, Pred (r, ts) ->
      (match s (r, size_lista ts)
        with None -> Inl (("unknown predicate " ^ id r) ^ " in input formula")
        | Some a -> check_pred r e ts a)
    | s, e, Let (p, phi, psi) ->
        (let f0 = funpow (nfv phi) new_type_symbol in
          binda (check (map_sig f0 s) (fun a -> TAny a) (map_formula f0 phi))
            (fun f1 ->
              binda (check
                      (map_sig f1
                        (fun_upd (equal_prod equal_string8 equal_nat)
                          (map_sig f0 s) (p, nfv phi)
                          (Some (mapa (fun a -> TAny a)
                                  (upt zero_nata (nfv phi))))))
                      (comp (comp f1 f0) e) (map_formula (comp f1 f0) psi))
                (fun f2 -> Inr (comp (comp f2 f1) f0))))
    | s, e, Eq (t1, t2) -> check_comparison e t1 t2
    | s, e, Less (t1, t2) -> check_comparison e t1 t2
    | s, e, LessEq (t1, t2) -> check_comparison e t1 t2
    | s, e, Neg phi -> check s e phi
    | s, e, Or (phi, psi) -> check_two_formulas check s e phi psi
    | s, e, And (phi, psi) -> check_two_formulas check s e phi psi
    | s, e, Ands phi_s -> check_ands check s e phi_s
    | s, e, Exists (t, phi) ->
        check s
          (fun n ->
            (if equal_nata n zero_nata then t else e (minus_nata n one_nata)))
          phi
    | s, e, Agg (y, (agg_type, d), tys, trm, phi) ->
        binda (check_trm (comp new_type_symbol (agg_tysenv e tys))
                (agg_trm_tysym agg_type) trm)
          (fun f ->
            binda (check (map_sig (comp f new_type_symbol) s)
                    (comp (comp f new_type_symbol) (agg_tysenv e tys))
                    (map_formula (comp f new_type_symbol) phi))
              (fun fa ->
                binda (check_trm (comp (comp (comp fa f) new_type_symbol) e)
                        (comp fa f
                          (t_res_tysym agg_type (agg_trm_tysym agg_type)))
                        (Var y))
                  (fun fb ->
                    binda (check_trm
                            (comp (comp (comp (comp fb fa) f) new_type_symbol)
                              e)
                            (comp (comp (comp fb fa) f) new_type_symbol d)
                            (Var y))
                      (fun fc ->
                        Inr (comp (comp (comp (comp fc fb) fa) f)
                              new_type_symbol)))))
    | s, e, Prev (i, phi) -> check s e phi
    | s, e, Next (i, phi) -> check s e phi
    | s, e, Since (phi, i, psi) -> check_two_formulas check s e phi psi
    | s, e, Until (phi, i, psi) -> check_two_formulas check s e phi psi
    | s, e, MatchF (i, r) -> check_regex check s e r
    | s, e, MatchP (i, r) -> check_regex check s e r
    | s, e, LetPast (p, phi, psi) ->
        (let f0 = funpow (nfv phi) new_type_symbol in
          binda (check
                  (fun_upd (equal_prod equal_string8 equal_nat) (map_sig f0 s)
                    (p, nfv phi)
                    (Some (tabulate (fun a -> TAny a) zero_nata (nfv phi))))
                  (fun a -> TAny a) (map_formula f0 phi))
            (fun f1 ->
              binda (check
                      (map_sig f1
                        (fun_upd (equal_prod equal_string8 equal_nat)
                          (map_sig f0 s) (p, nfv phi)
                          (Some (mapa (fun a -> TAny a)
                                  (upt zero_nata (nfv phi))))))
                      (comp (comp f1 f0) e) (map_formula (comp f1 f0) psi))
                (fun f2 -> Inr (comp (comp f2 f1) f0))))
    | s, e, TP t -> check_trm e (TCst TInt) t
    | s, e, TS t -> check_trm e (TCst TInt) t;;

let rec filterb xb xc = Alist (filtera xb (impl_of xc));;

let rec lookup _A xa = map_of _A (impl_of xa);;

let rec updatea _A xc xd xe = Alist (update _A xc xd (impl_of xe));;

let rec ecard (_A1, _A2, _A3)
  a = (if finite (_A1.finite_UNIV_card_UNIV, _A2, _A3) a
        then Enat (card (_A1, _A2, _A3) a) else Infinity_enat);;

let rec rep_I (Abs_I x) = x;;

let rec memL x = fst (rep_I x);;

let rec memR x = fst (snd (rep_I x));;

let rec mapping_empty_choose _A
  = (match ccompare _A with None -> Assoc_List_Mapping empty
      | Some _ -> RBT_Mapping (emptyc _A));;

let rec mapping_empty _A = function Mapping_RBT -> RBT_Mapping (emptyc _A)
                           | Mapping_Assoc_List -> Assoc_List_Mapping empty
                           | Mapping_Mapping -> Mapping (fun _ -> None)
                           | Mapping_Choose -> mapping_empty_choose _A;;

let rec emptya (_A1, _A2) = mapping_empty _A1 (of_phantom (mapping_impl _A2));;

let rec matcha
  uu uv = match uu, uv with [], [] -> Some (fun _ -> None)
    | Const x :: ts, Some y :: ys ->
        (if equal_event_dataa x y then matcha ts ys else None)
    | Var x :: ts, Some y :: ys ->
        (match matcha ts ys with None -> None
          | Some f ->
            (match f x with None -> Some (fun_upd equal_nat f x (Some y))
              | Some z -> (if equal_event_dataa y z then Some f else None)))
    | Var vb :: va, [] -> None
    | Var vb :: va, None :: vc -> None
    | Plus (vb, vc) :: va, uv -> None
    | Minus (vb, vc) :: va, uv -> None
    | UMinus vb :: va, uv -> None
    | Mult (vb, vc) :: va, uv -> None
    | Div (vb, vc) :: va, uv -> None
    | Mod (vb, vc) :: va, uv -> None
    | F2i vb :: va, uv -> None
    | I2f vb :: va, uv -> None
    | v :: va, [] -> None
    | v :: va, None :: vc -> None
    | [], v :: va -> None
    | uu, None :: va -> None;;

let rec inorder = function Leaf -> []
                  | Node (l, (a, uu), r) -> inorder l @ a :: inorder r;;

let rec partition
  p x1 = match p, x1 with p, [] -> ([], [])
    | p, x :: xs ->
        (let (yes, no) = partition p xs in
          (if p x then (x :: yes, no) else (yes, x :: no)));;

let rec replicate
  n x = (if equal_nata n zero_nata then []
          else x :: replicate (minus_nata n one_nata) x);;

let rec delete_aux _A
  k x1 = match k, x1 with k, [] -> []
    | ka, (k, v) :: xs ->
        (if eq _A ka k then xs else (k, v) :: delete_aux _A ka xs);;

let rec deletea _A xb xc = Alist (delete_aux _A xb (impl_of xc));;

let rec delete (_A1, _A2)
  k x1 = match k, x1 with
    k, RBT_Mapping t ->
      (match ccompare _A1
        with None ->
          failwith "delete RBT_Mapping: ccompare = None"
            (fun _ -> delete (_A1, _A2) k (RBT_Mapping t))
        | Some _ -> RBT_Mapping (deleteb _A1 k t))
    | k, Assoc_List_Mapping al -> Assoc_List_Mapping (deletea _A2 k al)
    | k, Mapping m -> Mapping (fun_upd _A2 m k None);;

let rec filterc _A
  p x1 = match p, x1 with
    p, RBT_Mapping t ->
      (match ccompare _A
        with None ->
          failwith "filter RBT_Mapping: ccompare = None"
            (fun _ -> filterc _A p (RBT_Mapping t))
        | Some _ -> RBT_Mapping (filtere _A (fun (a, b) -> p a b) t))
    | p, Assoc_List_Mapping al ->
        Assoc_List_Mapping (filterb (fun (a, b) -> p a b) al)
    | p, Mapping m ->
        Mapping
          (fun k ->
            (match m k with None -> None
              | Some v -> (if p k v then Some v else None)));;

let rec lookupa (_A1, _A2) = function RBT_Mapping t -> lookupc _A1 t
                             | Assoc_List_Mapping al -> lookup _A2 al;;

let rec updateb (_A1, _A2)
  k v x2 = match k, v, x2 with
    k, v, RBT_Mapping t ->
      (match ccompare _A1
        with None ->
          failwith "update RBT_Mapping: ccompare = None"
            (fun _ -> updateb (_A1, _A2) k v (RBT_Mapping t))
        | Some _ -> RBT_Mapping (insertb _A1 k v t))
    | k, v, Assoc_List_Mapping al -> Assoc_List_Mapping (updatea _A2 k v al)
    | k, v, Mapping m -> Mapping (fun_upd _A2 m k (Some v));;

let rec singleton_table (_A1, _A2)
  n i x =
    insert ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
      (tabulate (fun j -> (if equal_nata i j then Some x else None)) zero_nata
        n)
      (set_empty
        ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
        (of_phantom set_impl_lista));;

let rec empty_table (_A1, _A2, _A3) = bot_set (_A1, _A2, _A3);;

let rec unit_table (_A1, _A2)
  n = insert
        ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
        (replicate n None)
        (set_empty
          ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
          (of_phantom set_impl_lista));;

let rec eq_rel
  n uu uv = match n, uu, uv with
    n, Const x, Const y ->
      (if equal_event_dataa x y
        then unit_table (ceq_event_data, ccompare_event_data) n
        else empty_table
               ((ceq_list (ceq_option ceq_event_data)),
                 (ccompare_list (ccompare_option ccompare_event_data)),
                 set_impl_list))
    | n, Var x, Const y ->
        singleton_table (ceq_event_data, ccompare_event_data) n x y
    | n, Const x, Var y ->
        singleton_table (ceq_event_data, ccompare_event_data) n y x
    | n, Var v, Var va -> failwith "undefined"
    | n, Var v, Plus (va, vb) -> failwith "undefined"
    | n, Var v, Minus (va, vb) -> failwith "undefined"
    | n, Var v, UMinus va -> failwith "undefined"
    | n, Var v, Mult (va, vb) -> failwith "undefined"
    | n, Var v, Div (va, vb) -> failwith "undefined"
    | n, Var v, Mod (va, vb) -> failwith "undefined"
    | n, Var v, F2i va -> failwith "undefined"
    | n, Var v, I2f va -> failwith "undefined"
    | n, Plus (v, va), uv -> failwith "undefined"
    | n, Minus (v, va), uv -> failwith "undefined"
    | n, UMinus v, uv -> failwith "undefined"
    | n, Mult (v, va), uv -> failwith "undefined"
    | n, Div (v, va), uv -> failwith "undefined"
    | n, Mod (v, va), uv -> failwith "undefined"
    | n, F2i v, uv -> failwith "undefined"
    | n, I2f v, uv -> failwith "undefined"
    | n, uu, Plus (v, va) -> failwith "undefined"
    | n, uu, Minus (v, va) -> failwith "undefined"
    | n, uu, UMinus v -> failwith "undefined"
    | n, uu, Mult (v, va) -> failwith "undefined"
    | n, uu, Div (v, va) -> failwith "undefined"
    | n, uu, Mod (v, va) -> failwith "undefined"
    | n, uu, F2i v -> failwith "undefined"
    | n, uu, I2f v -> failwith "undefined";;

let rec lookup_default (_B1, _B2)
  d m k = (match lookupa (_B1, _B2) m k with None -> d | Some v -> v);;

let rec lookupb (_A1, _A2) (_B1, _B2, _B3)
  = lookup_default (_A1, _A2) (empty_table (_B1, _B2, _B3));;

let rec filter_comp_minus
  c t1 t2 =
    filtera (fun (k, _) -> is_none (rbt_comp_lookup c t2 k)) (entries t1);;

let rec small_rbt t = less_nat (bheight t) (nat_of_integer (Z.of_int 4));;

let rec comp_minus
  c t1 t2 =
    (if small_rbt t2 then folda (fun k _ -> rbt_comp_delete c k) t2 t1
      else (if small_rbt t1 then rbtreeify (filter_comp_minus c t1 t2)
             else (match t2 with Empty -> t1
                    | Branch (_, l2, a, _, r2) ->
                      (let (l1, (_, r1)) = rbt_split_comp c t1 a in
                        rbt_join2 (comp_minus c l1 l2)
                          (comp_minus c r1 r2)))));;

let rec rbt_comp_minus c t1 t2 = paint B (comp_minus c t1 t2);;

let rec minus _A
  xb xc =
    Mapping_RBTa
      (rbt_comp_minus (the (ccompare _A)) (impl_ofa _A xb) (impl_ofa _A xc));;

let rec restrict
  a v = mapa (fun i ->
               (if member (ceq_nat, ccompare_nat) i a then nth v i else None))
          (upt zero_nata (size_lista v));;

let rec equal_bool p pa = match p, pa with p, true -> p
                     | p, false -> not p
                     | true, p -> p
                     | false, p -> not p;;

let rec all_interval_nat
  p i j = less_eq_nat j i || p i && all_interval_nat p (suc i) j;;

let rec wf_tuple
  n v x =
    equal_nata (size_lista x) n &&
      all_interval_nat
        (fun i ->
          equal_bool (is_none (nth x i))
            (not (member (ceq_nat, ccompare_nat) i v)))
        zero_nata n;;

let rec add_to_rbt_comp (_B1, _B2, _B3)
  c = (fun (a, b) t ->
        (match rbt_comp_lookup c t a
          with None ->
            rbt_comp_insert c a (insert (_B1, _B2) b (bot_set (_B1, _B2, _B3)))
              t
          | Some x -> rbt_comp_insert c a (insert (_B1, _B2) b x) t));;

let rec cluster_rbt_comp (_B1, _B2, _B3)
  c f t =
    folda (fun b _ ta ->
            (match f b with None -> ta
              | Some a -> add_to_rbt_comp (_B1, _B2, _B3) c (a, b) ta))
      t Empty;;

let rec mapping_of_cluster (_B1, _B2, _B3) _A
  xb xc =
    Mapping_RBTa (cluster_rbt_comp (_B1, _B2, _B3) (the (ccompare _A)) xb xc);;

let rec cluster (_A1, _A2, _A3) _B
  f (RBT_set t) =
    (match ccompare _B
      with None ->
        failwith "cluster: ccompare = None"
          (fun _ -> cluster (_A1, _A2, _A3) _B f (RBT_set t))
      | Some _ ->
        (match ccompare _A2
          with None ->
            failwith "cluster: ccompare = None"
              (fun _ -> cluster (_A1, _A2, _A3) _B f (RBT_set t))
          | Some _ ->
            RBT_Mapping
              (mapping_of_cluster (_A1, _A2, _A3) _B f (impl_ofa _A2 t))));;

let rec combine _B
  f (RBT_Mapping t) (RBT_Mapping u) =
    (match ccompare _B
      with None ->
        failwith "combine RBT_Mapping: ccompare = None"
          (fun _ -> combine _B f (RBT_Mapping t) (RBT_Mapping u))
      | Some _ -> RBT_Mapping (joina _B (fun _ -> f) t u));;

let rec bounded x = snd (snd (rep_I x));;

let rec list_update
  x0 i y = match x0, i, y with [], i, y -> []
    | x :: xs, i, y ->
        (if equal_nata i zero_nata then y :: xs
          else x :: list_update xs (minus_nata i one_nata) y);;

let rec plus_event_data
  uu uv = match uu, uv with EInt x, EInt y -> EInt (Z.add x y)
    | EFloat x, EFloat y -> EFloat (Stdlib.(+.) x y)
    | EFloat v, EInt va -> failwith "undefined"
    | EFloat v, EString va -> failwith "undefined"
    | EString v, uv -> failwith "undefined"
    | EInt va, EFloat v -> failwith "undefined"
    | uu, EString v -> failwith "undefined";;

let rec double_of_event_data_agg = function EInt x -> Z.to_float x
                                   | EFloat x -> x
                                   | EString uu -> failwith "undefined";;

let rec integer_of_int (Int_of_integer k) = k;;

let rec aggreg_default_value
  op t =
    (match (op, t) with (Agg_Cnt, TInt) -> EInt Z.zero
      | (Agg_Cnt, TFloat) -> EFloat 0.0 | (Agg_Cnt, TString) -> EString ""
      | (Agg_Min, TInt) -> EInt Z.zero
      | (Agg_Min, TFloat) -> EFloat Stdlib.infinity
      | (Agg_Min, TString) -> EString "" | (Agg_Max, TInt) -> EInt Z.zero
      | (Agg_Max, TFloat) -> EFloat (Stdlib.(~-.) Stdlib.infinity)
      | (Agg_Max, TString) -> EString "" | (Agg_Sum, TInt) -> EInt Z.zero
      | (Agg_Sum, TFloat) -> EFloat 0.0 | (Agg_Sum, TString) -> EString ""
      | (Agg_Avg, TInt) -> EInt Z.zero | (Agg_Avg, TFloat) -> EFloat 0.0
      | (Agg_Avg, TString) -> EString "" | (Agg_Med, TInt) -> EInt Z.zero
      | (Agg_Med, TFloat) -> EFloat 0.0 | (Agg_Med, TString) -> EString "");;

let rec int_of_nat n = Int_of_integer (integer_of_nat n);;

let rec double_of_int (Int_of_integer x) = Z.to_float x;;

let rec the_enat (Enat n) = n;;

let rec flatten_multiset
  m = maps (fun (x, c) -> replicate (the_enat c) x)
        (csorted_list_of_set
          ((ceq_prod ceq_event_data ceq_enat),
            (ccompare_prod ccompare_event_data ccompare_enat))
          m);;

let rec finite_multiset_insert_fun
  (uu, k) v = (if equal_enat k Infinity_enat then false else true) && v;;

let finite_multiset_cfi : ((event_data * enat), bool) comp_fun_idem
  = Abs_comp_fun_idem finite_multiset_insert_fun;;

let rec finite_multiset
  m = (if finite
            ((finite_UNIV_prod finite_UNIV_event_data finite_UNIV_enat),
              (ceq_prod ceq_event_data ceq_enat),
              (ccompare_prod ccompare_event_data ccompare_enat))
            m
        then set_fold_cfi
               ((ceq_prod ceq_event_data ceq_enat),
                 (ccompare_prod ccompare_event_data ccompare_enat))
               finite_multiset_cfi true m
        else false);;

let rec dvd (_A1, _A2)
  a b = eq _A1
          (modulo _A2.semiring_modulo_semidom_modulo.modulo_semiring_modulo b a)
          (zero _A2.algebraic_semidom_semidom_modulo.semidom_divide_algebraic_semidom.semidom_semidom_divide.comm_semiring_1_cancel_semidom.comm_semiring_1_comm_semiring_1_cancel.semiring_1_comm_semiring_1.semiring_0_semiring_1.mult_zero_semiring_0.zero_mult_zero);;

let rec eval_agg_op
  x0 m = match x0, m with
    (Agg_Cnt, ty), m ->
      (let y0 = aggreg_default_value Agg_Cnt ty in
        (match (flatten_multiset m, finite_multiset m) with ([], true) -> y0
          | ([], false) -> y0
          | (a :: lista, true) ->
            EInt (integer_of_int (int_of_nat (size_lista (a :: lista))))
          | (_ :: _, false) -> y0))
    | (Agg_Min, ty), m ->
        (let y0 = aggreg_default_value Agg_Min ty in
          (match (flatten_multiset m, finite_multiset m) with ([], true) -> y0
            | ([], false) -> y0
            | (a :: lista, true) -> foldl (min ord_event_data) a lista
            | (_ :: _, false) -> y0))
    | (Agg_Max, ty), m ->
        (let y0 = aggreg_default_value Agg_Max ty in
          (match (flatten_multiset m, finite_multiset m) with ([], true) -> y0
            | ([], false) -> y0
            | (a :: lista, true) -> foldl (max ord_event_data) a lista
            | (_ :: _, false) -> y0))
    | (Agg_Sum, ty), m ->
        (let y0 = aggreg_default_value Agg_Sum ty in
          (match (flatten_multiset m, finite_multiset m) with ([], true) -> y0
            | ([], false) -> y0
            | (a :: lista, true) -> foldl plus_event_data a lista
            | (_ :: _, false) -> y0))
    | (Agg_Avg, ty), m ->
        (let y0 = aggreg_default_value Agg_Avg ty in
          (match (flatten_multiset m, finite_multiset m) with ([], true) -> y0
            | ([], false) -> y0
            | (a :: lista, true) ->
              EFloat
                (Stdlib.(/.)
                  (double_of_event_data_agg (foldl plus_event_data a lista))
                  (double_of_int (int_of_nat (size_lista (a :: lista)))))
            | (_ :: _, false) -> y0))
    | (Agg_Med, ty), m ->
        (let y0 = aggreg_default_value Agg_Med ty in
          (match (flatten_multiset m, finite_multiset m) with ([], true) -> y0
            | ([], false) -> y0
            | (a :: lista, true) ->
              EFloat
                (let u = size_lista (a :: lista) in
                 let ua = divide_nata u (nat_of_integer (Z.of_int 2)) in
                  (if dvd (equal_nat, semidom_modulo_nat)
                        (nat_of_integer (Z.of_int 2)) u
                    then Stdlib.(/.)
                           (Stdlib.(+.)
                             (double_of_event_data_agg
                               (nth (a :: lista) (minus_nata ua one_nata)))
                             (double_of_event_data_agg (nth (a :: lista) ua)))
                           (double_of_int (Int_of_integer (Z.of_int 2)))
                    else double_of_event_data_agg (nth (a :: lista) ua)))
            | (_ :: _, false) -> y0));;

let rec uminus_event_data = function EInt x -> EInt (Z.neg x)
                            | EFloat x -> EFloat (Stdlib.(~-.) x)
                            | EString v -> failwith "undefined";;

let rec mod_to_zero
  x y = (let z =
           snd ((fun k l -> if Z.equal Z.zero l then (Z.zero, l) else Z.div_rem
                  (Z.abs k) (Z.abs l))
                 x y)
           in
          (if Z.lt x Z.zero then Z.neg z else z));;

let rec modulo_event_data
  uu uv = match uu, uv with EInt x, EInt y -> EInt (mod_to_zero x y)
    | EFloat v, uv -> failwith "undefined"
    | EString v, uv -> failwith "undefined"
    | uu, EFloat v -> failwith "undefined"
    | uu, EString v -> failwith "undefined";;

let rec div_to_zero
  x y = (let z =
           fst ((fun k l -> if Z.equal Z.zero l then (Z.zero, l) else Z.div_rem
                  (Z.abs k) (Z.abs l))
                 x y)
           in
          (if not (equal_bool (Z.lt x Z.zero) (Z.lt y Z.zero)) then Z.neg z
            else z));;

let rec divide_event_data
  uu uv = match uu, uv with EInt x, EInt y -> EInt (div_to_zero x y)
    | EFloat x, EFloat y -> EFloat (Stdlib.(/.) x y)
    | EFloat v, EInt va -> failwith "undefined"
    | EFloat v, EString va -> failwith "undefined"
    | EString v, uv -> failwith "undefined"
    | EInt va, EFloat v -> failwith "undefined"
    | uu, EString v -> failwith "undefined";;

let rec times_event_data
  uu uv = match uu, uv with EInt x, EInt y -> EInt (Z.mul x y)
    | EFloat x, EFloat y -> EFloat (Stdlib.( *. ) x y)
    | EFloat v, EInt va -> failwith "undefined"
    | EFloat v, EString va -> failwith "undefined"
    | EString v, uv -> failwith "undefined"
    | EInt va, EFloat v -> failwith "undefined"
    | uu, EString v -> failwith "undefined";;

let rec minus_event_data
  uu uv = match uu, uv with EInt x, EInt y -> EInt (Z.sub x y)
    | EFloat x, EFloat y -> EFloat (Stdlib.(-.) x y)
    | EFloat v, EInt va -> failwith "undefined"
    | EFloat v, EString va -> failwith "undefined"
    | EString v, uv -> failwith "undefined"
    | EInt va, EFloat v -> failwith "undefined"
    | uu, EString v -> failwith "undefined";;

let rec integer_of_event_data = function EInt uu -> failwith "undefined"
                                | EFloat x -> Z.of_float x
                                | EString uv -> failwith "undefined";;

let rec double_of_event_data = function EInt x -> Z.to_float x
                               | EFloat uu -> failwith "undefined"
                               | EString uv -> failwith "undefined";;

let rec meval_trm
  x0 v = match x0, v with Var x, v -> the (nth v x)
    | Const x, v -> x
    | Plus (x, y), v -> plus_event_data (meval_trm x v) (meval_trm y v)
    | Minus (x, y), v -> minus_event_data (meval_trm x v) (meval_trm y v)
    | UMinus x, v -> uminus_event_data (meval_trm x v)
    | Mult (x, y), v -> times_event_data (meval_trm x v) (meval_trm y v)
    | Div (x, y), v -> divide_event_data (meval_trm x v) (meval_trm y v)
    | Mod (x, y), v -> modulo_event_data (meval_trm x v) (meval_trm y v)
    | F2i x, v -> EInt (integer_of_event_data (meval_trm x v))
    | I2f x, v -> EFloat (double_of_event_data (meval_trm x v));;

let rec add_to_rbt_compa (_B1, _B2, _B3)
  c = (fun (a, b) t ->
        (match rbt_comp_lookup c t a
          with None ->
            rbt_comp_insert c a (insert (_B1, _B2) b (bot_set (_B1, _B2, _B3)))
              t
          | Some x ->
            rbt_comp_insert c a
              (sup_seta (_B1, _B2) x
                (insert (_B1, _B2) b (bot_set (_B1, _B2, _B3))))
              t));;

let rec rbt_set_to_rbt_comp (_B1, _B2, _B3)
  c t = folda (fun ab _ -> add_to_rbt_compa (_B1, _B2, _B3) c ab) t Empty;;

let rec rbt_comp_bulkload
  c xs = foldr (fun (a, b) -> rbt_comp_insert c a b) xs Empty;;

let rec bulkload _A
  xa = Mapping_RBTa (rbt_comp_bulkload (the (ccompare _A)) xa);;

let rec mapping_to_set _A (_B1, _B2, _B3, _B4)
  t = bulkload (ccompare_prod _A (ccompare_set (_B1, _B2, _B3, _B4)))
        (mapa (fun x -> (x, ())) (entries t));;

let rec images _A (_B1, _B2, _B3, _B4)
  (RBT_set t) =
    (match ccompare _A
      with None ->
        failwith "images: ccompare = None"
          (fun _ -> images _A (_B1, _B2, _B3, _B4) (RBT_set t))
      | Some c ->
        (match ccompare _B3.ccompare_cproper_interval
          with None ->
            failwith "images: ccompare = None"
              (fun _ -> images _A (_B1, _B2, _B3, _B4) (RBT_set t))
          | Some _ ->
            RBT_set
              (mapping_to_set _A (_B1, _B2, _B3, _B4)
                (rbt_set_to_rbt_comp (_B2, _B3.ccompare_cproper_interval, _B4) c
                  (impl_ofa (ccompare_prod _A _B3.ccompare_cproper_interval)
                    t)))));;

let rec eval_agg
  n g0 y omega tys f rel =
    (if g0 && is_empty
                (card_UNIV_list, (ceq_list (ceq_option ceq_event_data)),
                  (cproper_interval_list (ccompare_option ccompare_event_data)))
                rel
      then singleton_table (ceq_event_data, ccompare_event_data) n y
             (eval_agg_op omega
               (set_empty
                 ((ceq_prod ceq_event_data ceq_enat),
                   (ccompare_prod ccompare_event_data ccompare_enat))
                 (of_phantom
                   (set_impl_proda set_impl_event_data set_impl_enat))))
      else image ((ceq_prod (ceq_list (ceq_option ceq_event_data))
                    (ceq_set
                      (cenum_list, (ceq_list (ceq_option ceq_event_data)),
                        (cproper_interval_list
                          (ccompare_option
                            ccompare_event_data)).ccompare_cproper_interval))),
                   (ccompare_prod
                     (ccompare_list (ccompare_option ccompare_event_data))
                     (ccompare_set
                       (finite_UNIV_list,
                         (ceq_list (ceq_option ceq_event_data)),
                         (cproper_interval_list
                           (ccompare_option ccompare_event_data)),
                         set_impl_list))))
             ((ceq_list (ceq_option ceq_event_data)),
               (ccompare_list (ccompare_option ccompare_event_data)),
               set_impl_list)
             (fun (k, group) ->
               (let m =
                  image ((ceq_prod ceq_event_data
                           (ceq_set
                             (cenum_list,
                               (ceq_list (ceq_option ceq_event_data)),
                               (cproper_interval_list
                                 (ccompare_option
                                   ccompare_event_data)).ccompare_cproper_interval))),
                          (ccompare_prod ccompare_event_data
                            (ccompare_set
                              (finite_UNIV_list,
                                (ceq_list (ceq_option ceq_event_data)),
                                (cproper_interval_list
                                  (ccompare_option ccompare_event_data)),
                                set_impl_list))))
                    ((ceq_prod ceq_event_data ceq_enat),
                      (ccompare_prod ccompare_event_data ccompare_enat),
                      (set_impl_prod set_impl_event_data set_impl_enat))
                    (fun (e, ts) ->
                      (e, ecard (card_UNIV_list,
                                  (ceq_list (ceq_option ceq_event_data)),
                                  (ccompare_list
                                    (ccompare_option ccompare_event_data)))
                            ts))
                    (images ccompare_event_data
                      (finite_UNIV_list, (ceq_list (ceq_option ceq_event_data)),
                        (cproper_interval_list
                          (ccompare_option ccompare_event_data)),
                        set_impl_list)
                      (image
                        ((ceq_list (ceq_option ceq_event_data)),
                          (ccompare_list (ccompare_option ccompare_event_data)))
                        ((ceq_prod ceq_event_data
                           (ceq_list (ceq_option ceq_event_data))),
                          (ccompare_prod ccompare_event_data
                            (ccompare_list
                              (ccompare_option ccompare_event_data))),
                          (set_impl_prod set_impl_event_data set_impl_list))
                        (fun t -> (meval_trm f t, t)) group))
                  in
                 list_update k y (Some (eval_agg_op omega m))))
             (images (ccompare_list (ccompare_option ccompare_event_data))
               (finite_UNIV_list, (ceq_list (ceq_option ceq_event_data)),
                 (cproper_interval_list (ccompare_option ccompare_event_data)),
                 set_impl_list)
               (image
                 ((ceq_list (ceq_option ceq_event_data)),
                   (ccompare_list (ccompare_option ccompare_event_data)))
                 ((ceq_prod (ceq_list (ceq_option ceq_event_data))
                    (ceq_list (ceq_option ceq_event_data))),
                   (ccompare_prod
                     (ccompare_list (ccompare_option ccompare_event_data))
                     (ccompare_list (ccompare_option ccompare_event_data))),
                   (set_impl_prod set_impl_list set_impl_list))
                 (fun t -> (drop (size_lista tys) t, t)) rel)));;

let rec rbt_product
  f rbt1 rbt2 =
    rbtreeify
      (rev (folda
             (fun a b ->
               folda (fun c d -> (fun e -> ((a, c), f a b c d) :: e)) rbt2)
             rbt1 []));;

let rec productd _A _B
  xc xd xe = Mapping_RBTa (rbt_product xc (impl_ofa _A xd) (impl_ofa _B xe));;

let rec producta _A _B
  rbt1 rbt2 = productd _A _B (fun _ _ _ _ -> ()) rbt1 rbt2;;

let rec atms (_A1, _A2, _A3)
  = function Skip x1 -> bot_set (_A1, _A2, _A3)
    | Test x2 -> insert (_A1, _A2) x2 (bot_set (_A1, _A2, _A3))
    | Plusa (x31, x32) ->
        sup_seta (_A1, _A2) (atms (_A1, _A2, _A3) x31)
          (atms (_A1, _A2, _A3) x32)
    | Times (x41, x42) ->
        sup_seta (_A1, _A2) (atms (_A1, _A2, _A3) x41)
          (atms (_A1, _A2, _A3) x42)
    | Star x5 -> atms (_A1, _A2, _A3) x5;;

let rec equal_safety x0 x1 = match x0, x1 with Strict, Lax -> false
                       | Lax, Strict -> false
                       | Lax, Lax -> true
                       | Strict, Strict -> true;;

let rec safe_regex (_B1, _B2, _B3, _B4, _B5)
  fv safe m uu x4 = match fv, safe, m, uu, x4 with
    fv, safe, m, uu, Skip n -> true
    | fv, safe, m, g, Test phi -> safe g phi
    | fv, safe, m, g, Plusa (r, s) ->
        (equal_safety g Lax ||
          set_eq (_B2, _B3, _B4.ccompare_cproper_interval)
            (fv_regex (_B3, _B4.ccompare_cproper_interval, _B5) fv r)
            (fv_regex (_B3, _B4.ccompare_cproper_interval, _B5) fv s)) &&
          (safe_regex (_B1, _B2, _B3, _B4, _B5) fv safe m g r &&
            safe_regex (_B1, _B2, _B3, _B4, _B5) fv safe m g s)
    | fv, safe, Futu, g, Times (r, s) ->
        (equal_safety g Lax ||
          less_eq_set (_B2, _B3, _B4.ccompare_cproper_interval)
            (fv_regex (_B3, _B4.ccompare_cproper_interval, _B5) fv r)
            (fv_regex (_B3, _B4.ccompare_cproper_interval, _B5) fv s)) &&
          (safe_regex (_B1, _B2, _B3, _B4, _B5) fv safe Futu g s &&
            safe_regex (_B1, _B2, _B3, _B4, _B5) fv safe Futu Lax r)
    | fv, safe, Past, g, Times (r, s) ->
        (equal_safety g Lax ||
          less_eq_set (_B2, _B3, _B4.ccompare_cproper_interval)
            (fv_regex (_B3, _B4.ccompare_cproper_interval, _B5) fv s)
            (fv_regex (_B3, _B4.ccompare_cproper_interval, _B5) fv r)) &&
          (safe_regex (_B1, _B2, _B3, _B4, _B5) fv safe Past g r &&
            safe_regex (_B1, _B2, _B3, _B4, _B5) fv safe Past Lax s)
    | fv, safe, m, g, Star r ->
        (equal_safety g Lax ||
          is_empty (_B1, _B3, _B4)
            (fv_regex (_B3, _B4.ccompare_cproper_interval, _B5) fv r)) &&
          safe_regex (_B1, _B2, _B3, _B4, _B5) fv safe m g r;;

let rec inf_cfi _A
  = Abs_comp_fun_idem (inf _A.semilattice_inf_lattice.inf_semilattice_inf);;

let rec sum_cfc _B
  xa = Abs_comp_fun_commute
         (comp (plus _B.monoid_add_comm_monoid_add.semigroup_add_monoid_add.plus_semigroup_add)
           xa);;

let rec productb _A _B
  dxs1 dxs2 =
    Abs_dlist
      (foldc _A (fun a -> foldc _B (fun c -> (fun b -> (a, c) :: b)) dxs2) dxs1
        []);;

let rec less_eq_enat q x1 = match q, x1 with Infinity_enat, Enat n -> false
                       | q, Infinity_enat -> true
                       | Enat m, Enat n -> less_eq_nat m n;;

let rec interval
  xb xc =
    Abs_I (if less_eq_enat (Enat xb) xc
            then (less_eq_nat xb,
                   ((fun i -> less_eq_enat (Enat i) xc),
                     not (equal_enat xc Infinity_enat)))
            else ((fun _ -> true), ((fun _ -> true), false)));;

let rec diff _A
  xb xc =
    Mapping_RBTa
      (rbt_comp_minus (the (ccompare _A)) (impl_ofa _A xb) (impl_ofa _A xc));;

let rec eval_mtrm
  n xa1 x = match n, xa1, x with
    n, MVar v, x -> singleton_table (ceq_event_data, ccompare_event_data) n v x
    | n, MConst c, x ->
        (if equal_event_dataa c x
          then unit_table (ceq_event_data, ccompare_event_data) n
          else empty_table
                 ((ceq_list (ceq_option ceq_event_data)),
                   (ccompare_list (ccompare_option ccompare_event_data)),
                   set_impl_list));;

let rec init_args i n l r pos agg = Args_ext (i, n, l, r, pos, agg, ());;

let rec epsilon_lax (_A1, _A2, _A3)
  guard phi_s x2 = match guard, phi_s, x2 with
    guard, phi_s, MSkip n ->
      (if equal_nata n zero_nata then guard
        else empty_table
               ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2)), set_impl_list))
    | guard, phi_s, MTestPos i -> join (_A1, _A2, _A3) guard true (nth phi_s i)
    | guard, phi_s, MTestNeg i -> join (_A1, _A2, _A3) guard false (nth phi_s i)
    | guard, phi_s, MPlus (r, s) ->
        sup_seta
          ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
          (epsilon_lax (_A1, _A2, _A3) guard phi_s r)
          (epsilon_lax (_A1, _A2, _A3) guard phi_s s)
    | guard, phi_s, MTimes (r, s) ->
        join (_A1, _A2, _A3) (epsilon_lax (_A1, _A2, _A3) guard phi_s r) true
          (epsilon_lax (_A1, _A2, _A3) guard phi_s s)
    | guard, phi_s, MStar r -> guard;;

let rec l_delta (_A1, _A2, _A3)
  kappa x phi_s xa3 = match kappa, x, phi_s, xa3 with
    kappa, x, phi_s, MSkip n ->
      (if equal_nata n zero_nata
        then empty_table
               ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2)), set_impl_list)
        else lookupb (ccompare_mregex, equal_mregex)
               ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2)), set_impl_list)
               x (kappa (MSkip (minus_nata n one_nata))))
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
          (l_delta (_A1, _A2, _A3) kappa x phi_s r)
          (l_delta (_A1, _A2, _A3) kappa x phi_s s)
    | kappa, x, phi_s, MTimes (r, s) ->
        sup_seta
          ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
          (l_delta (_A1, _A2, _A3) (fun t -> kappa (MTimes (t, s))) x phi_s r)
          (epsilon_lax (_A1, _A2, _A3) (l_delta (_A1, _A2, _A3) kappa x phi_s s)
            phi_s r)
    | kappa, x, phi_s, MStar r ->
        l_delta (_A1, _A2, _A3) (fun t -> kappa (MTimes (t, MStar r))) x phi_s
          r;;

let rec map_split
  f x1 = match f, x1 with f, [] -> ([], [])
    | f, x :: xs -> (let (y, z) = f x in
                     let (ys, zs) = map_split f xs in
                      (y :: ys, z :: zs));;

let rec r_delta (_A1, _A2, _A3)
  kappa x phi_s xa3 = match kappa, x, phi_s, xa3 with
    kappa, x, phi_s, MSkip n ->
      (if equal_nata n zero_nata
        then empty_table
               ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2)), set_impl_list)
        else lookupb (ccompare_mregex, equal_mregex)
               ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2)), set_impl_list)
               x (kappa (MSkip (minus_nata n one_nata))))
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
          (epsilon_lax (_A1, _A2, _A3) (r_delta (_A1, _A2, _A3) kappa x phi_s r)
            phi_s s)
    | kappa, x, phi_s, MStar r ->
        r_delta (_A1, _A2, _A3) (fun t -> kappa (MTimes (MStar r, t))) x phi_s
          r;;

let rec less_eq_rec_safety x0 uu = match x0, uu with Unused, uu -> true
                             | PastRec, PastRec -> true
                             | PastRec, NonFutuRec -> true
                             | PastRec, AnyRec -> true
                             | NonFutuRec, NonFutuRec -> true
                             | NonFutuRec, AnyRec -> true
                             | AnyRec, AnyRec -> true
                             | PastRec, Unused -> false
                             | NonFutuRec, Unused -> false
                             | NonFutuRec, PastRec -> false
                             | AnyRec, Unused -> false
                             | AnyRec, PastRec -> false
                             | AnyRec, NonFutuRec -> false;;

let rec safe_assignment
  x phi =
    (match phi with Pred (_, _) -> false | Let (_, _, _) -> false
      | LetPast (_, _, _) -> false
      | Eq (Var xa, Var y) ->
        equal_bool (not (member (ceq_nat, ccompare_nat) xa x))
          (member (ceq_nat, ccompare_nat) y x)
      | Eq (Var xa, Const event_data) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Const event_data)) x
      | Eq (Var xa, Plus (trm1, trm2)) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Plus (trm1, trm2))) x
      | Eq (Var xa, Minus (trm1, trm2)) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Minus (trm1, trm2))) x
      | Eq (Var xa, UMinus trm) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (UMinus trm)) x
      | Eq (Var xa, Mult (trm1, trm2)) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Mult (trm1, trm2))) x
      | Eq (Var xa, Div (trm1, trm2)) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Div (trm1, trm2))) x
      | Eq (Var xa, Mod (trm1, trm2)) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Mod (trm1, trm2))) x
      | Eq (Var xa, F2i trm) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (F2i trm)) x
      | Eq (Var xa, I2f trm) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (I2f trm)) x
      | Eq (Const event_data, Var xa) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Const event_data)) x
      | Eq (Const _, Const _) -> false | Eq (Const _, Plus (_, _)) -> false
      | Eq (Const _, Minus (_, _)) -> false | Eq (Const _, UMinus _) -> false
      | Eq (Const _, Mult (_, _)) -> false | Eq (Const _, Div (_, _)) -> false
      | Eq (Const _, Mod (_, _)) -> false | Eq (Const _, F2i _) -> false
      | Eq (Const _, I2f _) -> false
      | Eq (Plus (trm1, trm2), Var xa) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Plus (trm1, trm2))) x
      | Eq (Plus (_, _), Const _) -> false
      | Eq (Plus (_, _), Plus (_, _)) -> false
      | Eq (Plus (_, _), Minus (_, _)) -> false
      | Eq (Plus (_, _), UMinus _) -> false
      | Eq (Plus (_, _), Mult (_, _)) -> false
      | Eq (Plus (_, _), Div (_, _)) -> false
      | Eq (Plus (_, _), Mod (_, _)) -> false | Eq (Plus (_, _), F2i _) -> false
      | Eq (Plus (_, _), I2f _) -> false
      | Eq (Minus (trm1, trm2), Var xa) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Minus (trm1, trm2))) x
      | Eq (Minus (_, _), Const _) -> false
      | Eq (Minus (_, _), Plus (_, _)) -> false
      | Eq (Minus (_, _), Minus (_, _)) -> false
      | Eq (Minus (_, _), UMinus _) -> false
      | Eq (Minus (_, _), Mult (_, _)) -> false
      | Eq (Minus (_, _), Div (_, _)) -> false
      | Eq (Minus (_, _), Mod (_, _)) -> false
      | Eq (Minus (_, _), F2i _) -> false | Eq (Minus (_, _), I2f _) -> false
      | Eq (UMinus trm, Var xa) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (UMinus trm)) x
      | Eq (UMinus _, Const _) -> false | Eq (UMinus _, Plus (_, _)) -> false
      | Eq (UMinus _, Minus (_, _)) -> false | Eq (UMinus _, UMinus _) -> false
      | Eq (UMinus _, Mult (_, _)) -> false | Eq (UMinus _, Div (_, _)) -> false
      | Eq (UMinus _, Mod (_, _)) -> false | Eq (UMinus _, F2i _) -> false
      | Eq (UMinus _, I2f _) -> false
      | Eq (Mult (trm1, trm2), Var xa) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Mult (trm1, trm2))) x
      | Eq (Mult (_, _), Const _) -> false
      | Eq (Mult (_, _), Plus (_, _)) -> false
      | Eq (Mult (_, _), Minus (_, _)) -> false
      | Eq (Mult (_, _), UMinus _) -> false
      | Eq (Mult (_, _), Mult (_, _)) -> false
      | Eq (Mult (_, _), Div (_, _)) -> false
      | Eq (Mult (_, _), Mod (_, _)) -> false | Eq (Mult (_, _), F2i _) -> false
      | Eq (Mult (_, _), I2f _) -> false
      | Eq (Div (trm1, trm2), Var xa) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Div (trm1, trm2))) x
      | Eq (Div (_, _), Const _) -> false
      | Eq (Div (_, _), Plus (_, _)) -> false
      | Eq (Div (_, _), Minus (_, _)) -> false
      | Eq (Div (_, _), UMinus _) -> false
      | Eq (Div (_, _), Mult (_, _)) -> false
      | Eq (Div (_, _), Div (_, _)) -> false
      | Eq (Div (_, _), Mod (_, _)) -> false | Eq (Div (_, _), F2i _) -> false
      | Eq (Div (_, _), I2f _) -> false
      | Eq (Mod (trm1, trm2), Var xa) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (Mod (trm1, trm2))) x
      | Eq (Mod (_, _), Const _) -> false
      | Eq (Mod (_, _), Plus (_, _)) -> false
      | Eq (Mod (_, _), Minus (_, _)) -> false
      | Eq (Mod (_, _), UMinus _) -> false
      | Eq (Mod (_, _), Mult (_, _)) -> false
      | Eq (Mod (_, _), Div (_, _)) -> false
      | Eq (Mod (_, _), Mod (_, _)) -> false | Eq (Mod (_, _), F2i _) -> false
      | Eq (Mod (_, _), I2f _) -> false
      | Eq (F2i trm, Var xa) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (F2i trm)) x
      | Eq (F2i _, Const _) -> false | Eq (F2i _, Plus (_, _)) -> false
      | Eq (F2i _, Minus (_, _)) -> false | Eq (F2i _, UMinus _) -> false
      | Eq (F2i _, Mult (_, _)) -> false | Eq (F2i _, Div (_, _)) -> false
      | Eq (F2i _, Mod (_, _)) -> false | Eq (F2i _, F2i _) -> false
      | Eq (F2i _, I2f _) -> false
      | Eq (I2f trm, Var xa) ->
        not (member (ceq_nat, ccompare_nat) xa x) &&
          less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (fvi_trm zero_nata (I2f trm)) x
      | Eq (I2f _, Const _) -> false | Eq (I2f _, Plus (_, _)) -> false
      | Eq (I2f _, Minus (_, _)) -> false | Eq (I2f _, UMinus _) -> false
      | Eq (I2f _, Mult (_, _)) -> false | Eq (I2f _, Div (_, _)) -> false
      | Eq (I2f _, Mod (_, _)) -> false | Eq (I2f _, F2i _) -> false
      | Eq (I2f _, I2f _) -> false | Less (_, _) -> false
      | LessEq (_, _) -> false | Neg _ -> false | Or (_, _) -> false
      | And (_, _) -> false | Ands _ -> false | Exists (_, _) -> false
      | Agg (_, _, _, _, _) -> false | Prev (_, _) -> false
      | Next (_, _) -> false | Since (_, _, _) -> false
      | Until (_, _, _) -> false | MatchF (_, _) -> false
      | MatchP (_, _) -> false | TP _ -> false | TS _ -> false);;

let rec is_constraint = function Eq (t1, t2) -> true
                        | Less (t1, t2) -> true
                        | LessEq (t1, t2) -> true
                        | Neg (Eq (t1, t2)) -> true
                        | Neg (Less (t1, t2)) -> true
                        | Neg (LessEq (t1, t2)) -> true
                        | Pred (v, va) -> false
                        | Let (v, va, vb) -> false
                        | LetPast (v, va, vb) -> false
                        | Neg (Pred (va, vb)) -> false
                        | Neg (Let (va, vb, vc)) -> false
                        | Neg (LetPast (va, vb, vc)) -> false
                        | Neg (Neg va) -> false
                        | Neg (Or (va, vb)) -> false
                        | Neg (And (va, vb)) -> false
                        | Neg (Ands va) -> false
                        | Neg (Exists (va, vb)) -> false
                        | Neg (Agg (va, vb, vc, vd, ve)) -> false
                        | Neg (Prev (va, vb)) -> false
                        | Neg (Next (va, vb)) -> false
                        | Neg (Since (va, vb, vc)) -> false
                        | Neg (Until (va, vb, vc)) -> false
                        | Neg (MatchF (va, vb)) -> false
                        | Neg (MatchP (va, vb)) -> false
                        | Neg (TP va) -> false
                        | Neg (TS va) -> false
                        | Or (v, va) -> false
                        | And (v, va) -> false
                        | Ands v -> false
                        | Exists (v, va) -> false
                        | Agg (v, va, vb, vc, vd) -> false
                        | Prev (v, va) -> false
                        | Next (v, va) -> false
                        | Since (v, va, vb) -> false
                        | Until (v, va, vb) -> false
                        | MatchF (v, va) -> false
                        | MatchP (v, va) -> false
                        | TP v -> false
                        | TS v -> false;;

let rec is_Const = function Var x1 -> false
                   | Const x2 -> true
                   | Plus (x31, x32) -> false
                   | Minus (x41, x42) -> false
                   | UMinus x5 -> false
                   | Mult (x61, x62) -> false
                   | Div (x71, x72) -> false
                   | Mod (x81, x82) -> false
                   | F2i x9 -> false
                   | I2f x10 -> false;;

let rec times_rec_safety x0 uu = match x0, uu with Unused, uu -> Unused
                           | PastRec, Unused -> Unused
                           | NonFutuRec, Unused -> Unused
                           | AnyRec, Unused -> Unused
                           | AnyRec, PastRec -> AnyRec
                           | AnyRec, NonFutuRec -> AnyRec
                           | AnyRec, AnyRec -> AnyRec
                           | PastRec, AnyRec -> AnyRec
                           | NonFutuRec, AnyRec -> AnyRec
                           | PastRec, PastRec -> PastRec
                           | PastRec, NonFutuRec -> PastRec
                           | NonFutuRec, PastRec -> PastRec
                           | NonFutuRec, NonFutuRec -> NonFutuRec;;

let rec sup_rec_safety x0 uu = match x0, uu with AnyRec, uu -> AnyRec
                         | Unused, AnyRec -> AnyRec
                         | PastRec, AnyRec -> AnyRec
                         | NonFutuRec, AnyRec -> AnyRec
                         | NonFutuRec, Unused -> NonFutuRec
                         | NonFutuRec, PastRec -> NonFutuRec
                         | NonFutuRec, NonFutuRec -> NonFutuRec
                         | Unused, NonFutuRec -> NonFutuRec
                         | PastRec, NonFutuRec -> NonFutuRec
                         | PastRec, Unused -> PastRec
                         | PastRec, PastRec -> PastRec
                         | Unused, PastRec -> PastRec
                         | Unused, Unused -> Unused;;

let rec safe_letpast
  p x1 = match p, x1 with p, TS t -> Unused
    | p, TP t -> Unused
    | p, MatchF (i, r) ->
        times_rec_safety AnyRec
          (fold sup_rec_safety
            (csorted_list_of_set (ceq_rec_safety, ccompare_rec_safety)
              (atms (ceq_rec_safety, ccompare_rec_safety, set_impl_rec_safety)
                (map_regex (safe_letpast p) r)))
            Unused)
    | p, MatchP (i, r) ->
        fold sup_rec_safety
          (csorted_list_of_set (ceq_rec_safety, ccompare_rec_safety)
            (atms (ceq_rec_safety, ccompare_rec_safety, set_impl_rec_safety)
              (map_regex (safe_letpast p) r)))
          Unused
    | p, Until (phi, i, psi) ->
        times_rec_safety AnyRec
          (sup_rec_safety (safe_letpast p phi) (safe_letpast p psi))
    | p, Since (phi, i, psi) ->
        sup_rec_safety (safe_letpast p phi)
          (times_rec_safety (if memL i zero_nata then NonFutuRec else PastRec)
            (safe_letpast p psi))
    | p, Next (i, phi) -> times_rec_safety AnyRec (safe_letpast p phi)
    | p, Prev (i, phi) -> times_rec_safety PastRec (safe_letpast p phi)
    | p, Agg (y, omega, b, f, phi) -> safe_letpast p phi
    | p, Exists (ty, phi) -> safe_letpast p phi
    | p, Ands l -> fold (comp sup_rec_safety (safe_letpast p)) l Unused
    | p, And (phi, psi) ->
        sup_rec_safety (safe_letpast p phi) (safe_letpast p psi)
    | p, Or (phi, psi) ->
        sup_rec_safety (safe_letpast p phi) (safe_letpast p psi)
    | p, Neg phi -> safe_letpast p phi
    | p, LetPast (e, phi, psi) ->
        (if equal_proda equal_string8 equal_nat p (e, nfv phi) then Unused
          else sup_rec_safety
                 (times_rec_safety (safe_letpast (e, nfv phi) psi)
                   (safe_letpast p phi))
                 (safe_letpast p psi))
    | p, Let (e, phi, psi) ->
        sup_rec_safety
          (times_rec_safety (safe_letpast (e, nfv phi) psi)
            (safe_letpast p phi))
          (if equal_proda equal_string8 equal_nat p (e, nfv phi) then Unused
            else safe_letpast p psi)
    | p, Pred (e, ts) ->
        (if equal_proda equal_string8 equal_nat p (e, size_lista ts)
          then NonFutuRec else Unused)
    | p, LessEq (t1, t2) -> Unused
    | p, Less (t1, t2) -> Unused
    | p, Eq (t1, t2) -> Unused;;

let rec is_Var = function Var x1 -> true
                 | Const x2 -> false
                 | Plus (x31, x32) -> false
                 | Minus (x41, x42) -> false
                 | UMinus x5 -> false
                 | Mult (x61, x62) -> false
                 | Div (x71, x72) -> false
                 | Mod (x81, x82) -> false
                 | F2i x9 -> false
                 | I2f x10 -> false;;

let rec remove_neg = function Neg phi -> phi
                     | Pred (v, va) -> Pred (v, va)
                     | Let (v, va, vb) -> Let (v, va, vb)
                     | LetPast (v, va, vb) -> LetPast (v, va, vb)
                     | Eq (v, va) -> Eq (v, va)
                     | Less (v, va) -> Less (v, va)
                     | LessEq (v, va) -> LessEq (v, va)
                     | Or (v, va) -> Or (v, va)
                     | And (v, va) -> And (v, va)
                     | Ands v -> Ands v
                     | Exists (v, va) -> Exists (v, va)
                     | Agg (v, va, vb, vc, vd) -> Agg (v, va, vb, vc, vd)
                     | Prev (v, va) -> Prev (v, va)
                     | Next (v, va) -> Next (v, va)
                     | Since (v, va, vb) -> Since (v, va, vb)
                     | Until (v, va, vb) -> Until (v, va, vb)
                     | MatchF (v, va) -> MatchF (v, va)
                     | MatchP (v, va) -> MatchP (v, va)
                     | TP v -> TP v
                     | TS v -> TS v;;

let rec safe_formula
  = function
    Eq (t1, t2) ->
      is_Const t1 && (is_Const t2 || is_Var t2) || is_Var t1 && is_Const t2
    | Less (t1, t2) -> false
    | LessEq (t1, t2) -> false
    | Pred (e, ts) -> list_all (fun t -> is_Var t || is_Const t) ts
    | Let (p, phi, psi) ->
        less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
          (set (ceq_nat, ccompare_nat, set_impl_nat) (upt zero_nata (nfv phi)))
          (fvi zero_nata phi) &&
          (safe_formula phi && safe_formula psi)
    | LetPast (p, phi, psi) ->
        less_eq_rec_safety (safe_letpast (p, nfv phi) phi) PastRec &&
          (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
             (set (ceq_nat, ccompare_nat, set_impl_nat)
               (upt zero_nata (nfv phi)))
             (fvi zero_nata phi) &&
            (safe_formula phi && safe_formula psi))
    | Neg phi ->
        is_empty (card_UNIV_nat, ceq_nat, cproper_interval_nat)
          (fvi zero_nata phi) &&
          safe_formula phi
    | Or (phi, psi) ->
        set_eq (cenum_nat, ceq_nat, ccompare_nat) (fvi zero_nata psi)
          (fvi zero_nata phi) &&
          (safe_formula phi && safe_formula psi)
    | And (phi, psi) ->
        safe_formula phi &&
          (safe_assignment (fvi zero_nata phi) psi ||
            (safe_formula psi ||
              less_eq_set (cenum_nat, ceq_nat, ccompare_nat) (fvi zero_nata psi)
                (fvi zero_nata phi) &&
                (is_constraint psi ||
                  (match psi with Pred (_, _) -> false | Let (_, _, _) -> false
                    | LetPast (_, _, _) -> false | Eq (_, _) -> false
                    | Less (_, _) -> false | LessEq (_, _) -> false
                    | Neg a -> safe_formula a | Or (_, _) -> false
                    | And (_, _) -> false | Ands _ -> false
                    | Exists (_, _) -> false | Agg (_, _, _, _, _) -> false
                    | Prev (_, _) -> false | Next (_, _) -> false
                    | Since (_, _, _) -> false | Until (_, _, _) -> false
                    | MatchF (_, _) -> false | MatchP (_, _) -> false
                    | TP _ -> false | TS _ -> false))))
    | Ands l ->
        (let (pos, neg) = partition safe_formula l in
          not (null pos) &&
            (list_all safe_formula (mapa remove_neg neg) &&
              less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
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
                    (mapa (fvi zero_nata) neg)))
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
                    (mapa (fvi zero_nata) pos)))))
    | Exists (t, phi) ->
        safe_formula phi &&
          member (ceq_nat, ccompare_nat) zero_nata (fvi zero_nata phi)
    | Agg (y, omega, tys, f, phi) ->
        safe_formula phi &&
          (not (member (ceq_nat, ccompare_nat) (plus_nata y (size_lista tys))
                 (fvi zero_nata phi)) &&
            (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
               (set (ceq_nat, ccompare_nat, set_impl_nat)
                 (upt zero_nata (size_lista tys)))
               (fvi zero_nata phi) &&
              less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
                (fvi_trm zero_nata f) (fvi zero_nata phi)))
    | Prev (i, phi) -> safe_formula phi
    | Next (i, phi) -> safe_formula phi
    | Since (phi, i, psi) ->
        less_eq_set (cenum_nat, ceq_nat, ccompare_nat) (fvi zero_nata phi)
          (fvi zero_nata psi) &&
          ((safe_formula phi ||
             (match phi with Pred (_, _) -> false | Let (_, _, _) -> false
               | LetPast (_, _, _) -> false | Eq (_, _) -> false
               | Less (_, _) -> false | LessEq (_, _) -> false
               | Neg a -> safe_formula a | Or (_, _) -> false
               | And (_, _) -> false | Ands _ -> false | Exists (_, _) -> false
               | Agg (_, _, _, _, _) -> false | Prev (_, _) -> false
               | Next (_, _) -> false | Since (_, _, _) -> false
               | Until (_, _, _) -> false | MatchF (_, _) -> false
               | MatchP (_, _) -> false | TP _ -> false | TS _ -> false)) &&
            safe_formula psi)
    | Until (phi, i, psi) ->
        less_eq_set (cenum_nat, ceq_nat, ccompare_nat) (fvi zero_nata phi)
          (fvi zero_nata psi) &&
          ((safe_formula phi ||
             (match phi with Pred (_, _) -> false | Let (_, _, _) -> false
               | LetPast (_, _, _) -> false | Eq (_, _) -> false
               | Less (_, _) -> false | LessEq (_, _) -> false
               | Neg a -> safe_formula a | Or (_, _) -> false
               | And (_, _) -> false | Ands _ -> false | Exists (_, _) -> false
               | Agg (_, _, _, _, _) -> false | Prev (_, _) -> false
               | Next (_, _) -> false | Since (_, _, _) -> false
               | Until (_, _, _) -> false | MatchF (_, _) -> false
               | MatchP (_, _) -> false | TP _ -> false | TS _ -> false)) &&
            safe_formula psi)
    | MatchP (i, r) ->
        safe_regex
          (card_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
            set_impl_nat)
          (fvi zero_nata)
          (fun g phi ->
            safe_formula phi ||
              equal_safety g Lax &&
                (match phi with Pred (_, _) -> false | Let (_, _, _) -> false
                  | LetPast (_, _, _) -> false | Eq (_, _) -> false
                  | Less (_, _) -> false | LessEq (_, _) -> false
                  | Neg a -> safe_formula a | Or (_, _) -> false
                  | And (_, _) -> false | Ands _ -> false
                  | Exists (_, _) -> false | Agg (_, _, _, _, _) -> false
                  | Prev (_, _) -> false | Next (_, _) -> false
                  | Since (_, _, _) -> false | Until (_, _, _) -> false
                  | MatchF (_, _) -> false | MatchP (_, _) -> false
                  | TP _ -> false | TS _ -> false))
          Past Strict r
    | MatchF (i, r) ->
        safe_regex
          (card_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
            set_impl_nat)
          (fvi zero_nata)
          (fun g phi ->
            safe_formula phi ||
              equal_safety g Lax &&
                (match phi with Pred (_, _) -> false | Let (_, _, _) -> false
                  | LetPast (_, _, _) -> false | Eq (_, _) -> false
                  | Less (_, _) -> false | LessEq (_, _) -> false
                  | Neg a -> safe_formula a | Or (_, _) -> false
                  | And (_, _) -> false | Ands _ -> false
                  | Exists (_, _) -> false | Agg (_, _, _, _, _) -> false
                  | Prev (_, _) -> false | Next (_, _) -> false
                  | Since (_, _, _) -> false | Until (_, _, _) -> false
                  | MatchF (_, _) -> false | MatchP (_, _) -> false
                  | TP _ -> false | TS _ -> false))
          Futu Strict r
    | TP t -> is_Var t || is_Const t
    | TS t -> is_Var t || is_Const t;;

let rec to_mregex_exec
  x0 xs = match x0, xs with Skip n, xs -> (MSkip n, xs)
    | Test phi, xs ->
        (if safe_formula phi then (MTestPos (size_lista xs), xs @ [phi])
          else (match phi with Pred (_, _) -> (MSkip zero_nata, xs)
                 | Let (_, _, _) -> (MSkip zero_nata, xs)
                 | LetPast (_, _, _) -> (MSkip zero_nata, xs)
                 | Eq (_, _) -> (MSkip zero_nata, xs)
                 | Less (_, _) -> (MSkip zero_nata, xs)
                 | LessEq (_, _) -> (MSkip zero_nata, xs)
                 | Neg phia -> (MTestNeg (size_lista xs), xs @ [phia])
                 | Or (_, _) -> (MSkip zero_nata, xs)
                 | And (_, _) -> (MSkip zero_nata, xs)
                 | Ands _ -> (MSkip zero_nata, xs)
                 | Exists (_, _) -> (MSkip zero_nata, xs)
                 | Agg (_, _, _, _, _) -> (MSkip zero_nata, xs)
                 | Prev (_, _) -> (MSkip zero_nata, xs)
                 | Next (_, _) -> (MSkip zero_nata, xs)
                 | Since (_, _, _) -> (MSkip zero_nata, xs)
                 | Until (_, _, _) -> (MSkip zero_nata, xs)
                 | MatchF (_, _) -> (MSkip zero_nata, xs)
                 | MatchP (_, _) -> (MSkip zero_nata, xs)
                 | TP _ -> (MSkip zero_nata, xs)
                 | TS _ -> (MSkip zero_nata, xs)))
    | Plusa (r, s), xs ->
        (let (mr, ys) = to_mregex_exec r xs in
         let a = to_mregex_exec s ys in
         let (ms, aa) = a in
          (MPlus (mr, ms), aa))
    | Times (r, s), xs ->
        (let (mr, ys) = to_mregex_exec r xs in
         let a = to_mregex_exec s ys in
         let (ms, aa) = a in
          (MTimes (mr, ms), aa))
    | Star r, xs -> (let a = to_mregex_exec r xs in
                     let (mr, aa) = a in
                      (MStar mr, aa));;

let rec to_mregex r = to_mregex_exec r [];;

let rec rep_x_a_queue_x_a_option_prod_x_x_x_a_list_x_a_list_prod_x_a_option_prod
  (Abs_x_a_queue_x_a_option_prod_x_x_x_a_list_x_a_list_prod_x_a_option_prod x) =
    x;;

let rec sel12
  xa = Abs_queue
         (let (_, x2) =
            rep_x_a_queue_x_a_option_prod_x_x_x_a_list_x_a_list_prod_x_a_option_prod
              xa
            in
           x2);;

let rec sel11
  xa = (let (x1, _) =
          rep_x_a_queue_x_a_option_prod_x_x_x_a_list_x_a_list_prod_x_a_option_prod
            xa
          in
         x1);;

let rec rep_isom x = (sel11 x, sel12 x);;

let rec rep_queue (Abs_queue x) = x;;

let rec pop_t
  = function ([], []) -> (None, ([], []))
    | ([], [y]) -> (Some y, ([], []))
    | ([], y :: v :: va) -> (let z :: ys = rev (v :: va) in (Some z, (ys, [y])))
    | (x :: xs, ys) -> (Some x, (xs, ys));;

let rec pop_aux
  xa = Abs_x_a_queue_x_a_option_prod_x_x_x_a_list_x_a_list_prod_x_a_option_prod
         (pop_t (rep_queue xa));;

let rec pop x = rep_isom (pop_aux x);;

let rec check_wty_regex
  check_wty_formula x1 = match check_wty_formula, x1 with
    check_wty_formula, Skip l -> true
    | check_wty_formula, Test phi -> check_wty_formula phi
    | check_wty_formula, Plusa (r, s) ->
        check_wty_regex check_wty_formula r &&
          check_wty_regex check_wty_formula s
    | check_wty_formula, Times (r, s) ->
        check_wty_regex check_wty_formula r &&
          check_wty_regex check_wty_formula s
    | check_wty_formula, Star r -> check_wty_regex check_wty_formula r;;

let rec check_wty_formula
  = function Let (p, phi, psi) -> check_wty_formula phi && check_wty_formula psi
    | Neg phi -> check_wty_formula phi
    | Or (phi, psi) -> check_wty_formula phi && check_wty_formula psi
    | And (phi, psi) -> check_wty_formula phi && check_wty_formula psi
    | Ands phi_s -> foldl (fun a x -> a && check_wty_formula x) true phi_s
    | Exists (t, phi) -> check_wty_formula phi
    | Agg (y, (agg_type, d), tys, trm, phi) ->
        (match d with TAny _ -> false | TNum _ -> false
          | TCst _ -> check_wty_formula phi)
    | Prev (i, phi) -> check_wty_formula phi
    | Next (i, phi) -> check_wty_formula phi
    | Since (phi, i, psi) -> check_wty_formula phi && check_wty_formula psi
    | Until (phi, i, psi) -> check_wty_formula phi && check_wty_formula psi
    | MatchF (i, r) -> check_wty_regex check_wty_formula r
    | MatchP (i, r) -> check_wty_regex check_wty_formula r
    | LetPast (p, phi, psi) -> check_wty_formula phi && check_wty_formula psi
    | Pred (v, va) -> true
    | Eq (v, va) -> true
    | Less (v, va) -> true
    | LessEq (v, va) -> true
    | TP v -> true
    | TS v -> true;;

let rec convert_tysym = function TCst a -> a
                        | TAny v -> TFloat
                        | TNum v -> TFloat;;

let rec type_check
  s phi =
    binda (check s (fun a -> TAny a) phi)
      (fun f ->
        (if check_wty_formula (map_formula f phi)
          then Inr (map_formula (comp convert_tysym f) phi)
          else Inl "failed to infer ground type for aggregation result"));;

let rec mapping_join _B
  f (RBT_Mapping t) (RBT_Mapping u) =
    (match ccompare _B
      with None ->
        failwith "mapping_join RBT_Mapping: ccompare = None"
          (fun _ -> mapping_join _B f (RBT_Mapping t) (RBT_Mapping u))
      | Some _ -> RBT_Mapping (meet _B (fun _ -> f) t u));;

let rec proj_tuple x0 x1 = match x0, x1 with [], [] -> []
                     | true :: bs, a :: asa -> a :: proj_tuple bs asa
                     | false :: bs, a :: asa -> None :: proj_tuple bs asa
                     | b :: bs, [] -> []
                     | [], a :: asa -> [];;

let rec proj_tuple_in_join (_A1, _A2)
  pos bs asa t =
    (if pos
      then member
             ((ceq_list (ceq_option _A1)),
               (ccompare_list (ccompare_option _A2)))
             (proj_tuple bs asa) t
      else not (member
                 ((ceq_list (ceq_option _A1)),
                   (ccompare_list (ccompare_option _A2)))
                 (proj_tuple bs asa) t));;

let rec minus_set (_A1, _A2)
  a b = match a, b with
    RBT_set rbt1, RBT_set rbt2 ->
      (match ccompare _A2
        with None ->
          failwith "minus RBT_set RBT_set: ccompare = None"
            (fun _ -> minus_set (_A1, _A2) (RBT_set rbt1) (RBT_set rbt2))
        | Some _ -> RBT_set (minus _A2 rbt1 rbt2))
    | a, b -> inf_seta (_A1, _A2) a (uminus_set b);;

let rec join_mask
  n x = mapa (fun i -> member (ceq_nat, ccompare_nat) i x) (upt zero_nata n);;

let rec bin_join (_A1, _A2, _A3)
  n aa ta pos a t =
    (if is_empty
          (card_UNIV_list, (ceq_list (ceq_option _A1)),
            (cproper_interval_list (ccompare_option _A2)))
          ta
      then set_empty
             ((ceq_list (ceq_option _A1)),
               (ccompare_list (ccompare_option _A2)))
             (of_phantom set_impl_lista)
      else (if is_empty
                 (card_UNIV_list, (ceq_list (ceq_option _A1)),
                   (cproper_interval_list (ccompare_option _A2)))
                 t
             then (if pos
                    then set_empty
                           ((ceq_list (ceq_option _A1)),
                             (ccompare_list (ccompare_option _A2)))
                           (of_phantom set_impl_lista)
                    else ta)
             else (if is_empty (card_UNIV_nat, ceq_nat, cproper_interval_nat) a
                    then (if equal_bool pos
                               (member
                                 ((ceq_list (ceq_option _A1)),
                                   (ccompare_list (ccompare_option _A2)))
                                 (replicate n None) t)
                           then ta
                           else set_empty
                                  ((ceq_list (ceq_option _A1)),
                                    (ccompare_list (ccompare_option _A2)))
                                  (of_phantom set_impl_lista))
                    else (if set_eq (cenum_nat, ceq_nat, ccompare_nat) a aa
                           then (if pos
                                  then inf_seta
 ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2))) ta t
                                  else minus_set
 ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2))) ta t)
                           else (if less_eq_set
                                      (cenum_nat, ceq_nat, ccompare_nat) a aa
                                  then filter
 ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
 (fun asa -> proj_tuple_in_join (_A1, _A2) pos (join_mask n a) asa t) ta
                                  else (if less_eq_set
     (cenum_nat, ceq_nat, ccompare_nat) aa a &&
     pos
 then filter
        ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
        (fun asa -> proj_tuple_in_join (_A1, _A2) pos (join_mask n aa) asa ta) t
 else join (_A1, _A2, _A3) ta pos t))))));;

let rec idx_join _A (_B1, _B2, _B3)
  n aa ta a t =
    filterc _A
      (fun _ tb ->
        not (is_empty
              (card_UNIV_list, (ceq_list (ceq_option _B1)),
                (cproper_interval_list (ccompare_option _B2)))
              tb))
      (mapping_join _A (fun tb -> bin_join (_B1, _B2, _B3) n aa tb true a) ta
        t);;

let rec comp_fun_commute_apply (Abs_comp_fun_commute x) = x;;

let rec set_fold_cfc (_A1, _A2)
  f b x2 = match f, b, x2 with
    f, b, RBT_set rbt ->
      (match ccompare _A2
        with None ->
          failwith "set_fold_cfc RBT_set: ccompare = None"
            (fun _ -> set_fold_cfc (_A1, _A2) f b (RBT_set rbt))
        | Some _ -> foldb _A2 (comp_fun_commute_apply f) rbt b)
    | f, b, DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "set_fold_cfc DList_set: ceq = None"
              (fun _ -> set_fold_cfc (_A1, _A2) f b (DList_set dxs))
          | Some _ -> foldc _A1 (comp_fun_commute_apply f) dxs b)
    | f, b, Set_Monad xs ->
        (match ceq _A1
          with None ->
            failwith "set_fold_cfc Set_Monad: ceq = None"
              (fun _ -> set_fold_cfc (_A1, _A2) f b (Set_Monad xs))
          | Some eq -> fold (comp_fun_commute_apply f) (list_remdups eq xs) b)
    | f, b, Collect_set p ->
        failwith "set_fold_cfc not supported on Collect_set"
          (fun _ -> set_fold_cfc (_A1, _A2) f b (Collect_set p))
    | f, b, Complement a ->
        failwith "set_fold_cfc not supported on Complement"
          (fun _ -> set_fold_cfc (_A1, _A2) f b (Complement a));;

let rec sum (_A1, _A2, _A3) _B
  f a = (if finite (_A1, _A2, _A3) a
          then set_fold_cfc (_A2, _A3) (sum_cfc _B f)
                 (zero _B.monoid_add_comm_monoid_add.zero_monoid_add) a
          else zero _B.monoid_add_comm_monoid_add.zero_monoid_add);;

let rec score (_A1, _A2)
  q i = sum ((finite_UNIV_prod (finite_UNIV_set finite_UNIV_nat)
               (finite_UNIV_set finite_UNIV_list)),
              (ceq_prod
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
          comm_monoid_add_nat
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
            (fun (sign, _) -> member (ceq_nat, ccompare_nat) i sign) q);;

let rec map_valuesa
  xb xc = Alist (mapa (fun (x, y) -> (x, xb x y)) (impl_of xc));;

let rec map_values _A
  f x1 = match f, x1 with
    f, RBT_Mapping t ->
      (match ccompare _A
        with None ->
          failwith "map_values RBT_Mapping: ccompare = None"
            (fun _ -> map_values _A f (RBT_Mapping t))
        | Some _ -> RBT_Mapping (mapb _A f t))
    | f, Assoc_List_Mapping al -> Assoc_List_Mapping (map_valuesa f al)
    | f, Mapping m -> Mapping (fun k -> map_option (f k) (m k));;

let rec mrtabulate (_A1, _A2)
  xs f =
    (match ccompare_mregexa
      with None ->
        failwith "tabulate RBT_Mapping: ccompare = None"
          (fun _ -> mrtabulate (_A1, _A2) xs f)
      | Some _ ->
        RBT_Mapping
          (bulkload ccompare_mregex
            (map_filter
              (fun k ->
                (let fk = f k in
                  (if is_empty
                        (card_UNIV_list, (ceq_list (ceq_option _A1)),
                          (cproper_interval_list (ccompare_option _A2)))
                        fk
                    then None else Some (k, fk))))
              xs)));;

let rec aggargs_tys
  (Aggargs_ext
    (aggargs_cols, aggargs_n, aggargs_g0, aggargs_y, aggargs_omega, aggargs_tys,
      aggargs_f, more))
    = aggargs_tys;;

let rec rep_wf_wbt _A (Abs_wf_wbt x) = x;;

let rec size_wbt = function Leaf -> zero_nata
                   | Node (uu, (uv, n), uw) -> n;;

let rec balanced1
  t1 t2 =
    less_eq_nat
      (times_nata (nat_of_integer (Z.of_int 10))
        (plus_nata (size_wbt t2) one_nata))
      (times_nata (nat_of_integer (Z.of_int 25))
        (plus_nata (size_wbt t1) one_nata));;

let rec single
  t1 t2 =
    less_nat
      (times_nata (nat_of_integer (Z.of_int 10))
        (plus_nata (size_wbt t1) one_nata))
      (times_nata (nat_of_integer (Z.of_int 14))
        (plus_nata (size_wbt t2) one_nata));;

let rec n
  l a r =
    Node (l, (a, plus_nata (plus_nata (size_wbt l) (size_wbt r)) one_nata), r);;

let rec rot1R aa a ba b c = n aa a (n ba b c);;

let rec rot2 aa a (Node (b1, (b, uu), b2)) ca c = n (n aa a b1) b (n b2 ca c);;

let rec rotateR
  (Node (aa, (a, uu), ba)) b c =
    (if single ba aa then rot1R aa a ba b c else rot2 aa a ba b c);;

let rec balanceR l a r = (if balanced1 r l then n l a r else rotateR l a r);;

let rec rot1L aa a ba b c = n (n aa a ba) b c;;

let rec rotateL
  aa a (Node (ba, (b, uu), c)) =
    (if single ba c then rot1L aa a ba b c else rot2 aa a ba b c);;

let rec balanceL l a r = (if balanced1 l r then n l a r else rotateL l a r);;

let rec insertc (_A1, _A2)
  x xa1 = match x, xa1 with x, Leaf -> Node (Leaf, (x, one_nata), Leaf)
    | x, Node (l, (a, n), r) ->
        (match cmp (_A1, _A2) x a
          with LT -> balanceR (insertc (_A1, _A2) x l) a r
          | EQ -> balanceR (insertc (_A1, _A2) x l) a r
          | GT -> balanceL l a (insertc (_A1, _A2) x r));;

let rec tree_insert (_A1, _A2)
  xb xc = Abs_wf_wbt (insertc (_A1, _A2) xb (rep_wf_wbt _A2 xc));;

let rec insert_treelist (_A1, _A2)
  x (Collapse y) = Collapse (tree_insert (_A1, _A2) x y);;

let rec aggargs_f
  (Aggargs_ext
    (aggargs_cols, aggargs_n, aggargs_g0, aggargs_y, aggargs_omega, aggargs_tys,
      aggargs_f, more))
    = aggargs_f;;

let rec empty_tree _A = Abs_wf_wbt Leaf;;

let rec empty_treelist _A = Collapse (empty_tree _A);;

let rec insert_rank
  args typea t (v, m) =
    (if v then (let group = drop (size_lista (aggargs_tys args)) t in
                let term = meval_trm (aggargs_f args) t in
                let (new_v, new_list) =
                  (match
                    (lookupa
                       ((ccompare_list (ccompare_option ccompare_event_data)),
                         (equal_list (equal_option equal_event_data)))
                       m group,
                      (term, typea))
                    with (None, (EInt terma, IntT)) ->
                      (true,
                        LInt (insert_treelist (equal_integer, linorder_integer)
                               terma (empty_treelist linorder_integer)))
                    | (None, (EInt _, StringT)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (None, (EFloat _, _)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (None, (EString _, IntT)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (None, (EString terma, StringT)) ->
                      (true,
                        LString
                          (insert_treelist (equal_string8, linorder_string8)
                            terma (empty_treelist linorder_string8)))
                    | (Some (LInt ta), (EInt terma, IntT)) ->
                      (true,
                        LInt (insert_treelist (equal_integer, linorder_integer)
                               terma ta))
                    | (Some (LInt _), (EInt _, StringT)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (Some (LInt _), (EFloat _, _)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (Some (LInt _), (EString _, _)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (Some (LString _), (EInt _, _)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (Some (LString _), (EFloat _, _)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (Some (LString _), (EString _, IntT)) ->
                      (false, LInt (empty_treelist linorder_integer))
                    | (Some (LString ta), (EString terma, StringT)) ->
                      (true,
                        LString
                          (insert_treelist (equal_string8, linorder_string8)
                            terma ta)))
                  in
                 (new_v,
                   (if new_v
                     then updateb
                            ((ccompare_list
                               (ccompare_option ccompare_event_data)),
                              (equal_list (equal_option equal_event_data)))
                            group new_list m
                     else mapping_empty
                            (ccompare_list
                              (ccompare_option ccompare_event_data))
                            (of_phantom mapping_impl_lista))))
      else (v, m));;

let rec insert_rank_cfc xb xc = Abs_comp_fun_commute (insert_rank xb xc);;

let rec insert_sum
  args t (v, m) =
    (if v then (let group = drop (size_lista (aggargs_tys args)) t in
                let term = meval_trm (aggargs_f args) t in
                 (match
                   (lookupa
                      ((ccompare_list (ccompare_option ccompare_event_data)),
                        (equal_list (equal_option equal_event_data)))
                      m group,
                     term)
                   with (None, EInt i) ->
                     (true,
                       updateb
                         ((ccompare_list (ccompare_option ccompare_event_data)),
                           (equal_list (equal_option equal_event_data)))
                         group (one_nata, i) m)
                   | (None, EFloat _) ->
                     (false,
                       mapping_empty
                         (ccompare_list (ccompare_option ccompare_event_data))
                         (of_phantom mapping_impl_lista))
                   | (None, EString _) ->
                     (false,
                       mapping_empty
                         (ccompare_list (ccompare_option ccompare_event_data))
                         (of_phantom mapping_impl_lista))
                   | (Some (cnt, agg_sum), EInt i) ->
                     (true,
                       updateb
                         ((ccompare_list (ccompare_option ccompare_event_data)),
                           (equal_list (equal_option equal_event_data)))
                         group (plus_nata cnt one_nata, Z.add agg_sum i) m)
                   | (Some (_, _), EFloat _) ->
                     (false,
                       mapping_empty
                         (ccompare_list (ccompare_option ccompare_event_data))
                         (of_phantom mapping_impl_lista))
                   | (Some (_, _), EString _) ->
                     (false,
                       mapping_empty
                         (ccompare_list (ccompare_option ccompare_event_data))
                         (of_phantom mapping_impl_lista))))
      else (v, m));;

let rec insert_sum_cfc xa = Abs_comp_fun_commute (insert_sum xa);;

let rec insert_cnt
  args t (v, m) =
    (if v then (v, (let group = drop (size_lista (aggargs_tys args)) t in
                     (match
                       lookupa
                         ((ccompare_list (ccompare_option ccompare_event_data)),
                           (equal_list (equal_option equal_event_data)))
                         m group
                       with None ->
                         updateb
                           ((ccompare_list
                              (ccompare_option ccompare_event_data)),
                             (equal_list (equal_option equal_event_data)))
                           group one_nata m
                       | Some i ->
                         updateb
                           ((ccompare_list
                              (ccompare_option ccompare_event_data)),
                             (equal_list (equal_option equal_event_data)))
                           group (plus_nata i one_nata) m)))
      else (v, m));;

let rec insert_cnt_cfc xa = Abs_comp_fun_commute (insert_cnt xa);;

let rec insert_maggaux
  args data aux =
    (match aux
      with CntAux m ->
        (let (v, ma) =
           set_fold_cfc
             ((ceq_list (ceq_option ceq_event_data)),
               (ccompare_list (ccompare_option ccompare_event_data)))
             (insert_cnt_cfc args) (true, m) data
           in
          (v, CntAux ma))
      | SumAux m ->
        (let (v, ma) =
           set_fold_cfc
             ((ceq_list (ceq_option ceq_event_data)),
               (ccompare_list (ccompare_option ccompare_event_data)))
             (insert_sum_cfc args) (true, m) data
           in
          (v, SumAux ma))
      | RankAux (m, t) ->
        (let (v, ma) =
           set_fold_cfc
             ((ceq_list (ceq_option ceq_event_data)),
               (ccompare_list (ccompare_option ccompare_event_data)))
             (insert_rank_cfc args t) (true, m) data
           in
          (v, RankAux (ma, t))));;

let rec finitea (_A1, _A2, _A3) = finite (_A1, _A2, _A3);;

let rec insert_maggauxa
  args x xa2 = match args, x, xa2 with
    args, x, Some aux ->
      (let (v, auxa) = insert_maggaux args x aux in
        (if v && finitea
                   (finite_UNIV_list, (ceq_list (ceq_option ceq_event_data)),
                     (ccompare_list (ccompare_option ccompare_event_data)))
                   x
          then Some auxa else None))
    | args, x, None -> None;;

let rec get_map_result (_A1, _A2, _A3)
  m y f =
    image ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
      ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)),
        set_impl_list)
      (fun k ->
        (match
          lookupa
            ((ccompare_list (ccompare_option _A2)),
              (equal_list (equal_option _A3)))
            m k
          with None -> k | Some i -> list_update k y (Some (f i))))
      (keys (cenum_list, (ceq_list (ceq_option _A1)),
              (ccompare_list (ccompare_option _A2)), set_impl_list)
        m);;

let rec select
  x0 n = match x0, n with
    Node (l, (a, uu), r), n ->
      (let s = size_wbt l in
        (match cmp (equal_nat, linorder_nat) s n
          with LT -> select r (minus_nata (minus_nata n s) one_nata) | EQ -> a
          | GT -> select l n))
    | Leaf, n -> nth [] n;;

let rec tree_select _A xa = select (rep_wf_wbt _A xa);;

let rec get_treelist _A (Collapse y) n = tree_select _A y n;;

let rec get_edata_list
  x0 n = match x0, n with
    LString l, n -> EString (get_treelist linorder_string8 l n)
    | LInt l, n -> EInt (get_treelist linorder_integer l n);;

let rec tree_size _A xa = size_wbt (rep_wf_wbt _A xa);;

let rec length_treelist _A (Collapse y) = tree_size _A y;;

let rec get_length
  l = (match l with LInt a -> length_treelist linorder_integer a
        | LString a -> length_treelist linorder_string8 a);;

let rec result_maggaux
  (Aggargs_ext (cols, n, g0, y, omega, tys, f, ())) aux =
    (match aux
      with CntAux m ->
        (if g0 && is_empty
                    (card_UNIV_list, (ceq_list (ceq_option ceq_event_data)),
                      (cproper_interval_list
                        (ccompare_option ccompare_event_data)))
                    (keys (cenum_list, (ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list)
                      m)
          then singleton_table (ceq_event_data, ccompare_event_data) n y
                 (eval_agg_op omega
                   (set_empty
                     ((ceq_prod ceq_event_data ceq_enat),
                       (ccompare_prod ccompare_event_data ccompare_enat))
                     (of_phantom
                       (set_impl_proda set_impl_event_data set_impl_enat))))
          else get_map_result
                 (ceq_event_data, ccompare_event_data, equal_event_data) m y
                 (fun x -> EInt (integer_of_int (int_of_nat x))))
      | SumAux m ->
        (if g0 && is_empty
                    (card_UNIV_list, (ceq_list (ceq_option ceq_event_data)),
                      (cproper_interval_list
                        (ccompare_option ccompare_event_data)))
                    (keys (cenum_list, (ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list)
                      m)
          then singleton_table (ceq_event_data, ccompare_event_data) n y
                 (eval_agg_op omega
                   (set_empty
                     ((ceq_prod ceq_event_data ceq_enat),
                       (ccompare_prod ccompare_event_data ccompare_enat))
                     (of_phantom
                       (set_impl_proda set_impl_event_data set_impl_enat))))
          else (match fst omega
                 with Agg_Sum ->
                   get_map_result
                     (ceq_event_data, ccompare_event_data, equal_event_data) m y
                     (fun k -> EInt (snd k))
                 | Agg_Avg ->
                   get_map_result
                     (ceq_event_data, ccompare_event_data, equal_event_data) m y
                     (fun x ->
                       EFloat
                         (Stdlib.(/.)
                           (double_of_event_data
                             (EInt (snd (let (xa, a) = x in
  (int_of_nat xa, a)))))
                           (double_of_int
                             (fst (let (xa, a) = x in (int_of_nat xa, a))))))))
      | RankAux (m, _) ->
        (if g0 && is_empty
                    (card_UNIV_list, (ceq_list (ceq_option ceq_event_data)),
                      (cproper_interval_list
                        (ccompare_option ccompare_event_data)))
                    (keys (cenum_list, (ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list)
                      m)
          then singleton_table (ceq_event_data, ccompare_event_data) n y
                 (eval_agg_op omega
                   (set_empty
                     ((ceq_prod ceq_event_data ceq_enat),
                       (ccompare_prod ccompare_event_data ccompare_enat))
                     (of_phantom
                       (set_impl_proda set_impl_event_data set_impl_enat))))
          else (match fst omega
                 with Agg_Min ->
                   get_map_result
                     (ceq_event_data, ccompare_event_data, equal_event_data) m y
                     (fun k -> get_edata_list k zero_nata)
                 | Agg_Max ->
                   get_map_result
                     (ceq_event_data, ccompare_event_data, equal_event_data) m y
                     (fun k ->
                       get_edata_list k (minus_nata (get_length k) one_nata))
                 | Agg_Med ->
                   get_map_result
                     (ceq_event_data, ccompare_event_data, equal_event_data) m y
                     (fun k ->
                       (let u = get_length k in
                        let ua = divide_nata u (nat_of_integer (Z.of_int 2)) in
                        let a =
                          (if dvd (equal_nat, semidom_modulo_nat)
                                (nat_of_integer (Z.of_int 2)) u
                            then Stdlib.(/.)
                                   (Stdlib.(+.)
                                     (double_of_event_data_agg
                                       (get_edata_list k
 (minus_nata ua one_nata)))
                                     (double_of_event_data_agg
                                       (get_edata_list k ua)))
                                   (double_of_int (Int_of_integer (Z.of_int 2)))
                            else double_of_event_data_agg (get_edata_list k ua))
                          in
                         EFloat a)))));;

let rec result_maggauxa args x1 = match args, x1 with args, None -> None
                          | args, Some aux -> Some (result_maggaux args aux);;

let rec equal_tree _A
  x0 x1 = match x0, x1 with Leaf, Node (x21, x22, x23) -> false
    | Node (x21, x22, x23), Leaf -> false
    | Node (x21, x22, x23), Node (y21, y22, y23) ->
        equal_tree _A x21 y21 && (eq _A x22 y22 && equal_tree _A x23 y23)
    | Leaf, Leaf -> true;;

let rec equal_wf_wbt (_A1, _A2)
  xa xc =
    equal_tree (equal_prod _A1 equal_nat) (rep_wf_wbt _A2 xa)
      (rep_wf_wbt _A2 xc);;

let rec tree_inorder _A xa = inorder (rep_wf_wbt _A xa);;

let rec equal_treelist (_A1, _A2)
  (Collapse y1) (Collapse y2) =
    (if equal_wf_wbt (_A1, _A2) y2 (empty_tree _A2)
      then equal_wf_wbt (_A1, _A2) y1 (empty_tree _A2)
      else equal_lista _A1 (tree_inorder _A2 y1) (tree_inorder _A2 y2));;

let rec split_min _A
  (Node (l, (a, uu), r)) =
    (if equal_tree (equal_prod _A equal_nat) l Leaf then (a, r)
      else (let (x, la) = split_min _A l in (x, balanceL la a r)));;

let rec del_max _A
  (Node (l, (a, uu), r)) =
    (if equal_tree (equal_prod _A equal_nat) r Leaf then (a, l)
      else (let (x, ra) = del_max _A r in (x, balanceR l a ra)));;

let rec size_tree
  = function Leaf -> zero_nata
    | Node (x21, x22, x23) ->
        plus_nata (plus_nata (size_tree x21) (size_tree x23)) (suc zero_nata);;

let rec combineb _A
  x0 x1 = match x0, x1 with Leaf, Leaf -> Leaf
    | Leaf, Node (v, va, vb) -> Node (v, va, vb)
    | Node (v, va, vb), Leaf -> Node (v, va, vb)
    | Node (v, va, vb), Node (vc, vd, ve) ->
        (if less_nat (size_tree (Node (vc, vd, ve)))
              (size_tree (Node (v, va, vb)))
          then (let (lMax, l) = del_max _A (Node (v, va, vb)) in
                 balanceL l lMax (Node (vc, vd, ve)))
          else (let a = split_min _A (Node (vc, vd, ve)) in
                let (aa, b) = a in
                 balanceR (Node (v, va, vb)) aa b));;

let rec deletec (_A1, _A2)
  uu x1 = match uu, x1 with uu, Leaf -> Leaf
    | x, Node (l, (a, uv), r) ->
        (match cmp (_A1, _A2) x a
          with LT -> balanceL (deletec (_A1, _A2) x l) a r
          | EQ -> combineb _A1 l r
          | GT -> balanceR l a (deletec (_A1, _A2) x r));;

let rec tree_remove (_A1, _A2)
  xb xc = Abs_wf_wbt (deletec (_A1, _A2) xb (rep_wf_wbt _A2 xc));;

let rec remove_treelist (_A1, _A2)
  x (Collapse y) = Collapse (tree_remove (_A1, _A2) x y);;

let rec delete_rank
  args typea t (v, m) =
    (if v then (let group = drop (size_lista (aggargs_tys args)) t in
                let term = meval_trm (aggargs_f args) t in
                let a =
                  (match
                    (lookupa
                       ((ccompare_list (ccompare_option ccompare_event_data)),
                         (equal_list (equal_option equal_event_data)))
                       m group,
                      (term, typea))
                    with (None, (EInt _, IntT)) -> (true, m)
                    | (None, (EInt _, StringT)) ->
                      (false,
                        mapping_empty
                          (ccompare_list (ccompare_option ccompare_event_data))
                          (of_phantom mapping_impl_lista))
                    | (None, (EFloat _, _)) ->
                      (false,
                        mapping_empty
                          (ccompare_list (ccompare_option ccompare_event_data))
                          (of_phantom mapping_impl_lista))
                    | (None, (EString _, IntT)) ->
                      (false,
                        mapping_empty
                          (ccompare_list (ccompare_option ccompare_event_data))
                          (of_phantom mapping_impl_lista))
                    | (None, (EString _, StringT)) -> (true, m)
                    | (Some (LInt ta), (EInt terma, IntT)) ->
                      (true,
                        (let l =
                           remove_treelist (equal_integer, linorder_integer)
                             terma ta
                           in
                          (if equal_treelist (equal_integer, linorder_integer) l
                                (empty_treelist linorder_integer)
                            then delete
                                   ((ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                     (equal_list
                                       (equal_option equal_event_data)))
                                   group m
                            else updateb
                                   ((ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                     (equal_list
                                       (equal_option equal_event_data)))
                                   group (LInt l) m)))
                    | (Some (LInt _), (EInt _, StringT)) ->
                      (false,
                        mapping_empty
                          (ccompare_list (ccompare_option ccompare_event_data))
                          (of_phantom mapping_impl_lista))
                    | (Some (LInt _), (EFloat _, _)) ->
                      (false,
                        mapping_empty
                          (ccompare_list (ccompare_option ccompare_event_data))
                          (of_phantom mapping_impl_lista))
                    | (Some (LInt _), (EString _, _)) ->
                      (false,
                        mapping_empty
                          (ccompare_list (ccompare_option ccompare_event_data))
                          (of_phantom mapping_impl_lista))
                    | (Some (LString _), (EInt _, _)) ->
                      (false,
                        mapping_empty
                          (ccompare_list (ccompare_option ccompare_event_data))
                          (of_phantom mapping_impl_lista))
                    | (Some (LString _), (EFloat _, _)) ->
                      (false,
                        mapping_empty
                          (ccompare_list (ccompare_option ccompare_event_data))
                          (of_phantom mapping_impl_lista))
                    | (Some (LString _), (EString _, IntT)) ->
                      (false,
                        mapping_empty
                          (ccompare_list (ccompare_option ccompare_event_data))
                          (of_phantom mapping_impl_lista))
                    | (Some (LString ta), (EString terma, StringT)) ->
                      (true,
                        (let l =
                           remove_treelist (equal_string8, linorder_string8)
                             terma ta
                           in
                          (if equal_treelist (equal_string8, linorder_string8) l
                                (empty_treelist linorder_string8)
                            then delete
                                   ((ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                     (equal_list
                                       (equal_option equal_event_data)))
                                   group m
                            else updateb
                                   ((ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                     (equal_list
                                       (equal_option equal_event_data)))
                                   group (LString l) m))))
                  in
                let (aa, b) = a in
                 (aa, b))
      else (v, m));;

let rec delete_rank_cfc xb xc = Abs_comp_fun_commute (delete_rank xb xc);;

let rec delete_sum
  args t (v, m) =
    (if v then (let group = drop (size_lista (aggargs_tys args)) t in
                let term = meval_trm (aggargs_f args) t in
                 (match
                   (lookupa
                      ((ccompare_list (ccompare_option ccompare_event_data)),
                        (equal_list (equal_option equal_event_data)))
                      m group,
                     term)
                   with (None, _) ->
                     (false,
                       mapping_empty
                         (ccompare_list (ccompare_option ccompare_event_data))
                         (of_phantom mapping_impl_lista))
                   | (Some (cnt, agg_sum), EInt i) ->
                     (true,
                       (if equal_nata cnt one_nata
                         then delete
                                ((ccompare_list
                                   (ccompare_option ccompare_event_data)),
                                  (equal_list (equal_option equal_event_data)))
                                group m
                         else updateb
                                ((ccompare_list
                                   (ccompare_option ccompare_event_data)),
                                  (equal_list (equal_option equal_event_data)))
                                group (minus_nata cnt one_nata, Z.sub agg_sum i)
                                m))
                   | (Some (_, _), EFloat _) ->
                     (false,
                       mapping_empty
                         (ccompare_list (ccompare_option ccompare_event_data))
                         (of_phantom mapping_impl_lista))
                   | (Some (_, _), EString _) ->
                     (false,
                       mapping_empty
                         (ccompare_list (ccompare_option ccompare_event_data))
                         (of_phantom mapping_impl_lista))))
      else (v, m));;

let rec delete_sum_cfc xa = Abs_comp_fun_commute (delete_sum xa);;

let rec delete_cnt
  args t (v, m) =
    (if v then (v, (let group = drop (size_lista (aggargs_tys args)) t in
                     (match
                       lookupa
                         ((ccompare_list (ccompare_option ccompare_event_data)),
                           (equal_list (equal_option equal_event_data)))
                         m group
                       with None -> m
                       | Some i ->
                         (if equal_nata i one_nata
                           then delete
                                  ((ccompare_list
                                     (ccompare_option ccompare_event_data)),
                                    (equal_list
                                      (equal_option equal_event_data)))
                                  group m
                           else updateb
                                  ((ccompare_list
                                     (ccompare_option ccompare_event_data)),
                                    (equal_list
                                      (equal_option equal_event_data)))
                                  group (minus_nata i one_nata) m))))
      else (v, m));;

let rec delete_cnt_cfc xa = Abs_comp_fun_commute (delete_cnt xa);;

let rec delete_maggaux
  args data aux =
    (match aux
      with CntAux m ->
        (let (v, ma) =
           set_fold_cfc
             ((ceq_list (ceq_option ceq_event_data)),
               (ccompare_list (ccompare_option ccompare_event_data)))
             (delete_cnt_cfc args) (true, m) data
           in
          (v, CntAux ma))
      | SumAux m ->
        (let (v, ma) =
           set_fold_cfc
             ((ceq_list (ceq_option ceq_event_data)),
               (ccompare_list (ccompare_option ccompare_event_data)))
             (delete_sum_cfc args) (true, m) data
           in
          (v, SumAux ma))
      | RankAux (m, t) ->
        (let (v, ma) =
           set_fold_cfc
             ((ceq_list (ceq_option ceq_event_data)),
               (ccompare_list (ccompare_option ccompare_event_data)))
             (delete_rank_cfc args t) (true, m) data
           in
          (v, RankAux (ma, t))));;

let rec delete_maggauxa
  args x xa2 = match args, x, xa2 with args, x, None -> None
    | args, x, Some aux ->
        (match delete_maggaux args x aux with (true, auxa) -> Some auxa
          | (false, _) -> None);;

let rec aggargs_omega
  (Aggargs_ext
    (aggargs_cols, aggargs_n, aggargs_g0, aggargs_y, aggargs_omega, aggargs_tys,
      aggargs_f, more))
    = aggargs_omega;;

let rec init_maggaux
  args =
    (let aggtype = fst (aggargs_omega args) in
     let y0 = snd (aggargs_omega args) in
      (match (aggtype, y0)
        with (Agg_Cnt, _) ->
          (true,
            CntAux
              (mapping_empty
                (ccompare_list (ccompare_option ccompare_event_data))
                (of_phantom mapping_impl_lista)))
        | (Agg_Min, TInt) ->
          (true,
            RankAux
              (mapping_empty
                 (ccompare_list (ccompare_option ccompare_event_data))
                 (of_phantom mapping_impl_lista),
                IntT))
        | (Agg_Min, TFloat) ->
          (false,
            CntAux
              (mapping_empty
                (ccompare_list (ccompare_option ccompare_event_data))
                (of_phantom mapping_impl_lista)))
        | (Agg_Min, TString) ->
          (true,
            RankAux
              (mapping_empty
                 (ccompare_list (ccompare_option ccompare_event_data))
                 (of_phantom mapping_impl_lista),
                StringT))
        | (Agg_Max, TInt) ->
          (true,
            RankAux
              (mapping_empty
                 (ccompare_list (ccompare_option ccompare_event_data))
                 (of_phantom mapping_impl_lista),
                IntT))
        | (Agg_Max, TFloat) ->
          (false,
            CntAux
              (mapping_empty
                (ccompare_list (ccompare_option ccompare_event_data))
                (of_phantom mapping_impl_lista)))
        | (Agg_Max, TString) ->
          (true,
            RankAux
              (mapping_empty
                 (ccompare_list (ccompare_option ccompare_event_data))
                 (of_phantom mapping_impl_lista),
                StringT))
        | (Agg_Sum, TInt) ->
          (true,
            SumAux
              (mapping_empty
                (ccompare_list (ccompare_option ccompare_event_data))
                (of_phantom mapping_impl_lista)))
        | (Agg_Sum, TFloat) ->
          (false,
            CntAux
              (mapping_empty
                (ccompare_list (ccompare_option ccompare_event_data))
                (of_phantom mapping_impl_lista)))
        | (Agg_Sum, TString) ->
          (false,
            CntAux
              (mapping_empty
                (ccompare_list (ccompare_option ccompare_event_data))
                (of_phantom mapping_impl_lista)))
        | (Agg_Avg, TInt) ->
          (true,
            SumAux
              (mapping_empty
                (ccompare_list (ccompare_option ccompare_event_data))
                (of_phantom mapping_impl_lista)))
        | (Agg_Avg, TFloat) ->
          (false,
            CntAux
              (mapping_empty
                (ccompare_list (ccompare_option ccompare_event_data))
                (of_phantom mapping_impl_lista)))
        | (Agg_Avg, TString) ->
          (false,
            CntAux
              (mapping_empty
                (ccompare_list (ccompare_option ccompare_event_data))
                (of_phantom mapping_impl_lista)))
        | (Agg_Med, TInt) ->
          (false,
            CntAux
              (mapping_empty
                (ccompare_list (ccompare_option ccompare_event_data))
                (of_phantom mapping_impl_lista)))
        | (Agg_Med, TFloat) ->
          (true,
            RankAux
              (mapping_empty
                 (ccompare_list (ccompare_option ccompare_event_data))
                 (of_phantom mapping_impl_lista),
                IntT))
        | (Agg_Med, TString) ->
          (false,
            CntAux
              (mapping_empty
                (ccompare_list (ccompare_option ccompare_event_data))
                (of_phantom mapping_impl_lista)))));;

let rec init_maggauxa
  args =
    (match init_maggaux args with (true, aux) -> Some aux
      | (false, _) -> None);;

let rec tl_queue_t = function ([], []) -> ([], [])
                     | ([], [l]) -> ([], [])
                     | ([], l :: v :: va) -> (tla (rev (v :: va)), [l])
                     | (a :: asa, fs) -> (asa, fs);;

let rec tl_queue xa = Abs_queue (tl_queue_t (rep_queue xa));;

let rec safe_hd_t
  = function ([], []) -> (None, ([], []))
    | ([], [l]) -> (Some l, ([], [l]))
    | ([], l :: v :: va) ->
        (let fs = rev (v :: va) in (Some (hda fs), (fs, [l])))
    | (f :: fs, l :: ls) -> (Some f, (f :: fs, l :: ls))
    | (f :: fs, []) -> failwith "undefined";;

let rec safe_hd_aux
  xa = Abs_x_a_queue_x_a_option_prod_x_x_x_a_list_x_a_list_prod_x_a_option_prod
         (safe_hd_t (rep_queue xa));;

let rec safe_hd x = rep_isom (safe_hd_aux x);;

let rec takedropWhile_queue
  f q = (match safe_hd q with (None, qa) -> (qa, [])
          | (Some a, qa) ->
            (if f a
              then (let (qb, asa) = takedropWhile_queue f (tl_queue qa) in
                     (qb, a :: asa))
              else (qa, [])));;

let rec mapping_delete_set_cfi (_A1, _A2)
  = Abs_comp_fun_idem (delete (_A1, _A2));;

let rec mapping_delete_set (_A1, _A2, _A3, _A4)
  m a = (if finite (_A1, _A2, _A3) a
          then set_fold_cfi (_A2, _A3) (mapping_delete_set_cfi (_A3, _A4)) m a
          else failwith "mapping_delete_set: infinite"
                 (fun _ -> mapping_delete_set (_A1, _A2, _A3, _A4) m a));;

let rec ts_tp_lt
  i ts tp tstp =
    (match tstp with Inl tsa -> memL i (minus_nata tsa ts)
      | Inr a -> less_eq_nat tp a);;

let rec max_tstp
  x0 x1 = match x0, x1 with Inl tsa, Inl ts -> Inl (max ord_nat tsa ts)
    | Inr tpa, Inr tp -> Inr (max ord_nat tpa tp)
    | Inl ts, Inr v -> Inl ts
    | Inr v, Inl ts -> Inl ts;;

let rec args_agg
  (Args_ext (args_ivl, args_n, args_L, args_R, args_pos, args_agg, more)) =
    args_agg;;

let rec aggargs_g0
  (Aggargs_ext
    (aggargs_cols, aggargs_n, aggargs_g0, aggargs_y, aggargs_omega, aggargs_tys,
      aggargs_f, more))
    = aggargs_g0;;

let rec aggargs_y
  (Aggargs_ext
    (aggargs_cols, aggargs_n, aggargs_g0, aggargs_y, aggargs_omega, aggargs_tys,
      aggargs_f, more))
    = aggargs_y;;

let rec aggargs_n
  (Aggargs_ext
    (aggargs_cols, aggargs_n, aggargs_g0, aggargs_y, aggargs_omega, aggargs_tys,
      aggargs_f, more))
    = aggargs_n;;

let rec eval_aggargs
  args =
    eval_agg (aggargs_n args) (aggargs_g0 args) (aggargs_y args)
      (aggargs_omega args) (aggargs_tys args) (aggargs_f args);;

let rec eval_args_agg
  args x =
    (match args_agg args with None -> x
      | Some aggargs -> eval_aggargs aggargs x);;

let rec args_ivl
  (Args_ext (args_ivl, args_n, args_L, args_R, args_pos, args_agg, more)) =
    args_ivl;;

let rec eval_step_mmuaux
  args (tp, (tss, (tables,
                    (len, (maskL,
                            (maskR,
                              (result,
                                (a1_map, (a2_map, (tstp_map, donea))))))))))
    = (let (Some _, tssa) = safe_hd tss in
       let Some m = lookupa (ccompare_nat, equal_nat) a2_map (minus_nata tp len)
         in
       let i = args_ivl args in
       let t = eval_args_agg args result in
       let tssb = tl_queue tssa in
       let (ts, tssc) =
         (match safe_hd tssb with (None, tssc) -> (zero_nata, tssc)
           | (Some ts, tssc) -> (ts, tssc))
         in
       let (tablesa, taken) =
         takedropWhile_queue
           (fun (_, tstp) ->
             not (ts_tp_lt i ts (plus_nata (minus_nata tp len) one_nata) tstp))
           tables
         in
       let to_del_approx =
         sup_setb
           (finite_UNIV_list, cenum_list,
             (ceq_list (ceq_option ceq_event_data)),
             (cproper_interval_list (ccompare_option ccompare_event_data)),
             set_impl_list)
           (set ((ceq_set
                   (cenum_list, (ceq_list (ceq_option ceq_event_data)),
                     (cproper_interval_list
                       (ccompare_option
                         ccompare_event_data)).ccompare_cproper_interval)),
                  (ccompare_set
                    (finite_UNIV_list, (ceq_list (ceq_option ceq_event_data)),
                      (cproper_interval_list
                        (ccompare_option ccompare_event_data)),
                      set_impl_list)),
                  set_impl_set)
             (mapa fst taken))
         in
       let to_del =
         filter
           ((ceq_list (ceq_option ceq_event_data)),
             (ccompare_list (ccompare_option ccompare_event_data)))
           (fun x ->
             (match
               lookupa
                 ((ccompare_list (ccompare_option ccompare_event_data)),
                   (equal_list (equal_option equal_event_data)))
                 m x
               with None -> false
               | Some tstp ->
                 not (ts_tp_lt i ts (plus_nata (minus_nata tp len) one_nata)
                       tstp)))
           to_del_approx
         in
       let ma =
         mapping_delete_set
           (finite_UNIV_list, (ceq_list (ceq_option ceq_event_data)),
             (ccompare_list (ccompare_option ccompare_event_data)),
             (equal_list (equal_option equal_event_data)))
           m to_del
         in
       let resulta =
         (if equal_nata len one_nata
           then set_empty
                  ((ceq_list (ceq_option ceq_event_data)),
                    (ccompare_list (ccompare_option ccompare_event_data)))
                  (of_phantom set_impl_lista)
           else sup_seta
                  ((ceq_list (ceq_option ceq_event_data)),
                    (ccompare_list (ccompare_option ccompare_event_data)))
                  (minus_set
                    ((ceq_list (ceq_option ceq_event_data)),
                      (ccompare_list (ccompare_option ccompare_event_data)))
                    result to_del)
                  (let Some a =
                     lookupa (ccompare_nat, equal_nat) a2_map
                       (plus_nata (minus_nata tp len) one_nata)
                     in
                    keys (cenum_list, (ceq_list (ceq_option ceq_event_data)),
                           (ccompare_list
                             (ccompare_option ccompare_event_data)),
                           set_impl_list)
                      a))
         in
       let a2_mapa =
         (if equal_nata len one_nata
           then updateb (ccompare_nat, equal_nat) tp
                  (mapping_empty
                    (ccompare_list (ccompare_option ccompare_event_data))
                    (of_phantom mapping_impl_lista))
                  a2_map
           else updateb (ccompare_nat, equal_nat)
                  (plus_nata (minus_nata tp len) one_nata)
                  (let Some a =
                     lookupa (ccompare_nat, equal_nat) a2_map
                       (plus_nata (minus_nata tp len) one_nata)
                     in
                    combine
                      (ccompare_list (ccompare_option ccompare_event_data))
                      max_tstp ma a)
                  a2_map)
         in
       let a2_mapb =
         delete (ccompare_nat, equal_nat) (minus_nata tp len) a2_mapa in
       let tstp_mapa =
         delete (ccompare_nat, equal_nat) (minus_nata tp len) tstp_map in
        (tp, (tssc,
               (tablesa,
                 (minus_nata len one_nata,
                   (maskL,
                     (maskR,
                       (resulta,
                         (a1_map, (a2_mapb, (tstp_mapa, t :: donea)))))))))));;

let rec eval_step_mmauaux
  args ((tp, (tss, (tables,
                     (len, (maskL,
                             (maskR,
                               (result,
                                 (a1_map, (a2_map, (tstp_map, donea)))))))))),
         aggaux)
    = (let (Some _, tssa) = safe_hd tss in
        (match args_agg args
          with None ->
            (eval_step_mmuaux args
               (tp, (tss, (tables,
                            (len, (maskL,
                                    (maskR,
                                      (result,
(a1_map, (a2_map, (tstp_map, donea)))))))))),
              aggaux)
          | Some aggargs ->
            (let Some m =
               lookupa (ccompare_nat, equal_nat) a2_map (minus_nata tp len) in
             let i = args_ivl args in
             let tssb = tl_queue tssa in
             let (ts, tssc) =
               (match safe_hd tssb with (None, tssc) -> (zero_nata, tssc)
                 | (Some ts, tssc) -> (ts, tssc))
               in
             let (tablesa, taken) =
               takedropWhile_queue
                 (fun (_, tstp) ->
                   not (ts_tp_lt i ts (plus_nata (minus_nata tp len) one_nata)
                         tstp))
                 tables
               in
             let to_del_approx =
               sup_setb
                 (finite_UNIV_list, cenum_list,
                   (ceq_list (ceq_option ceq_event_data)),
                   (cproper_interval_list
                     (ccompare_option ccompare_event_data)),
                   set_impl_list)
                 (set ((ceq_set
                         (cenum_list, (ceq_list (ceq_option ceq_event_data)),
                           (cproper_interval_list
                             (ccompare_option
                               ccompare_event_data)).ccompare_cproper_interval)),
                        (ccompare_set
                          (finite_UNIV_list,
                            (ceq_list (ceq_option ceq_event_data)),
                            (cproper_interval_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list)),
                        set_impl_set)
                   (mapa fst taken))
               in
             let to_del =
               filter
                 ((ceq_list (ceq_option ceq_event_data)),
                   (ccompare_list (ccompare_option ccompare_event_data)))
                 (fun x ->
                   (match
                     lookupa
                       ((ccompare_list (ccompare_option ccompare_event_data)),
                         (equal_list (equal_option equal_event_data)))
                       m x
                     with None -> false
                     | Some tstp ->
                       not (ts_tp_lt i ts
                             (plus_nata (minus_nata tp len) one_nata) tstp)))
                 to_del_approx
               in
             let ma =
               mapping_delete_set
                 (finite_UNIV_list, (ceq_list (ceq_option ceq_event_data)),
                   (ccompare_list (ccompare_option ccompare_event_data)),
                   (equal_list (equal_option equal_event_data)))
                 m to_del
               in
             let resulta =
               (if equal_nata len one_nata
                 then set_empty
                        ((ceq_list (ceq_option ceq_event_data)),
                          (ccompare_list (ccompare_option ccompare_event_data)))
                        (of_phantom set_impl_lista)
                 else sup_seta
                        ((ceq_list (ceq_option ceq_event_data)),
                          (ccompare_list (ccompare_option ccompare_event_data)))
                        (minus_set
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)))
                          result to_del)
                        (let Some a =
                           lookupa (ccompare_nat, equal_nat) a2_map
                             (plus_nata (minus_nata tp len) one_nata)
                           in
                          keys (cenum_list,
                                 (ceq_list (ceq_option ceq_event_data)),
                                 (ccompare_list
                                   (ccompare_option ccompare_event_data)),
                                 set_impl_list)
                            a))
               in
             let to_ins =
               (let Some mb =
                  lookupa (ccompare_nat, equal_nat) a2_map
                    (plus_nata (minus_nata tp len) one_nata)
                  in
                 mb)
               in
             let a2_mapa =
               (if equal_nata len one_nata
                 then updateb (ccompare_nat, equal_nat) tp
                        (mapping_empty
                          (ccompare_list (ccompare_option ccompare_event_data))
                          (of_phantom mapping_impl_lista))
                        a2_map
                 else updateb (ccompare_nat, equal_nat)
                        (plus_nata (minus_nata tp len) one_nata)
                        (combine
                          (ccompare_list (ccompare_option ccompare_event_data))
                          max_tstp ma to_ins)
                        a2_map)
               in
             let a2_mapb =
               delete (ccompare_nat, equal_nat) (minus_nata tp len) a2_mapa in
             let tstp_mapa =
               delete (ccompare_nat, equal_nat) (minus_nata tp len) tstp_map in
             let agg_result = result_maggauxa aggargs aggaux in
             let t =
               (match agg_result
                 with None ->
                   eval_args_agg args
                     (keys (cenum_list, (ceq_list (ceq_option ceq_event_data)),
                             (ccompare_list
                               (ccompare_option ccompare_event_data)),
                             set_impl_list)
                       m)
                 | Some k -> k)
               in
             let to_insa =
               filterc (ccompare_list (ccompare_option ccompare_event_data))
                 (fun k _ ->
                   is_none
                     (lookupa
                       ((ccompare_list (ccompare_option ccompare_event_data)),
                         (equal_list (equal_option equal_event_data)))
                       ma k))
                 to_ins
               in
             let a =
               (if equal_nata len one_nata then init_maggauxa aggargs
                 else insert_maggauxa aggargs
                        (keys (cenum_list,
                                (ceq_list (ceq_option ceq_event_data)),
                                (ccompare_list
                                  (ccompare_option ccompare_event_data)),
                                set_impl_list)
                          to_insa)
                        (delete_maggauxa aggargs to_del aggaux))
               in
              ((tp, (tssc,
                      (tablesa,
                        (minus_nata len one_nata,
                          (maskL,
                            (maskR,
                              (resulta,
                                (a1_map,
                                  (a2_mapb, (tstp_mapa, t :: donea)))))))))),
                a))));;

let rec prepend_queue_t a x1 = match a, x1 with a, ([], []) -> ([], [a])
                          | a, (fs, l :: ls) -> (a :: fs, l :: ls)
                          | a, (f :: fs, []) -> failwith "undefined";;

let rec prepend_queue xb xc = Abs_queue (prepend_queue_t xb (rep_queue xc));;

let empty_queue : 'a queue = Abs_queue ([], []);;

let rec takeWhile_queue
  f q = (match safe_hd q with (None, qa) -> (qa, qa)
          | (Some a, qa) ->
            (if f a
              then (let (qaa, _) = takeWhile_queue f (tl_queue qa) in
                     (prepend_queue a qaa, qa))
              else (empty_queue, qa)));;

let rec linearize xa = (let (fs, ls) = rep_queue xa in fs @ rev ls);;

let rec shift_mmauaux
  args nt
    ((tp, (tss, (tables,
                  (len, (maskL,
                          (maskR,
                            (result,
                              (a1_map, (a2_map, (tstp_map, donea)))))))))),
      auxs)
    = (let (tss_queue, tssa) =
         takeWhile_queue (fun t -> not (memR (args_ivl args) (minus_nata nt t)))
           tss
         in
        foldl (fun aux _ -> eval_step_mmauaux args aux)
          ((tp, (tssa,
                  (tables,
                    (len, (maskL,
                            (maskR,
                              (result,
                                (a1_map, (a2_map, (tstp_map, donea)))))))))),
            auxs)
          (linearize tss_queue));;

let rec upd_nested_step (_B1, _B2) (_C1, _C2, _C3)
  d f x m =
    (let (k, ka) = x in
      (match lookupa (_B1, _B2) m k
        with None ->
          updateb (_B1, _B2) k (updateb (_C1, _C2) ka d (emptya (_C1, _C3))) m
        | Some ma ->
          (match lookupa (_C1, _C2) ma ka
            with None -> updateb (_B1, _B2) k (updateb (_C1, _C2) ka d ma) m
            | Some v ->
              updateb (_B1, _B2) k (updateb (_C1, _C2) ka (f v) ma) m)));;

let rec upd_nested_max_tstp_cfi (_A1, _A2) (_B1, _B2, _B3)
  xa = Abs_comp_fun_idem
         (upd_nested_step (_A1, _A2) (_B1, _B2, _B3) xa (max_tstp xa));;

let rec upd_nested_max_tstp (_A1, _A2, _A3, _A4) (_B1, _B2, _B3, _B4, _B5)
  m d x =
    (if finite
          ((finite_UNIV_prod _A1 _B1), (ceq_prod _A2 _B2),
            (ccompare_prod _A3 _B3))
          x
      then set_fold_cfi ((ceq_prod _A2 _B2), (ccompare_prod _A3 _B3))
             (upd_nested_max_tstp_cfi (_A3, _A4) (_B3, _B4, _B5) d) m x
      else failwith "upd_nested_max_tstp: infinite"
             (fun _ ->
               upd_nested_max_tstp (_A1, _A2, _A3, _A4)
                 (_B1, _B2, _B3, _B4, _B5) m d x));;

let rec shift_mmuaux
  args nt
    (tp, (tss, (len, (maskL,
                       (maskR,
                         (result, (a1_map, (a2_map, (donea, done_length)))))))))
    = (let (tss_queue, tssa) =
         takeWhile_queue (fun t -> not (memR (args_ivl args) (minus_nata nt t)))
           tss
         in
        foldl (fun aux _ -> eval_step_mmuaux args aux)
          (tp, (tssa,
                 (len, (maskL,
                         (maskR,
                           (result,
                             (a1_map, (a2_map, (donea, done_length)))))))))
          (linearize tss_queue));;

let rec append_queue
  xb xc = Abs_queue (let (fs, ls) = rep_queue xc in (fs, xb :: ls));;

let rec upd_cfi (_A1, _A2)
  xa = Abs_comp_fun_idem (fun a -> updateb (_A1, _A2) a (xa a));;

let rec upd_set (_A1, _A2, _A3, _A4)
  m f a =
    (if finite (_A1, _A2, _A3) a
      then set_fold_cfi (_A2, _A3) (upd_cfi (_A3, _A4) f) m a
      else failwith "upd_set: infinite"
             (fun _ -> upd_set (_A1, _A2, _A3, _A4) m f a));;

let rec args_pos
  (Args_ext (args_ivl, args_n, args_L, args_R, args_pos, args_agg, more)) =
    args_pos;;

let rec productc (_A1, _A2, _A3) (_B1, _B2, _B3)
  a2 b2 = match a2, b2 with
    RBT_set rbt1, RBT_set rbt2 ->
      (match ccompare _A2
        with None ->
          failwith "product RBT_set RBT_set: ccompare1 = None"
            (fun _ ->
              productc (_A1, _A2, _A3) (_B1, _B2, _B3) (RBT_set rbt1)
                (RBT_set rbt2))
        | Some _ ->
          (match ccompare _B2
            with None ->
              failwith "product RBT_set RBT_set: ccompare2 = None"
                (fun _ ->
                  productc (_A1, _A2, _A3) (_B1, _B2, _B3) (RBT_set rbt1)
                    (RBT_set rbt2))
            | Some _ -> RBT_set (producta _A2 _B2 rbt1 rbt2)))
    | a2, RBT_set rbt2 ->
        (match ccompare _B2
          with None ->
            failwith "product RBT_set: ccompare2 = None"
              (fun _ ->
                productc (_A1, _A2, _A3) (_B1, _B2, _B3) a2 (RBT_set rbt2))
          | Some _ ->
            foldb _B2
              (fun y ->
                sup_seta ((ceq_prod _A1 _B1), (ccompare_prod _A2 _B2))
                  (image (_A1, _A2)
                    ((ceq_prod _A1 _B1), (ccompare_prod _A2 _B2),
                      (set_impl_prod _A3 _B3))
                    (fun x -> (x, y)) a2))
              rbt2
              (bot_set
                ((ceq_prod _A1 _B1), (ccompare_prod _A2 _B2),
                  (set_impl_prod _A3 _B3))))
    | RBT_set rbt1, b2 ->
        (match ccompare _A2
          with None ->
            failwith "product RBT_set: ccompare1 = None"
              (fun _ ->
                productc (_A1, _A2, _A3) (_B1, _B2, _B3) (RBT_set rbt1) b2)
          | Some _ ->
            foldb _A2
              (fun x ->
                sup_seta ((ceq_prod _A1 _B1), (ccompare_prod _A2 _B2))
                  (image (_B1, _B2)
                    ((ceq_prod _A1 _B1), (ccompare_prod _A2 _B2),
                      (set_impl_prod _A3 _B3))
                    (fun a -> (x, a)) b2))
              rbt1
              (bot_set
                ((ceq_prod _A1 _B1), (ccompare_prod _A2 _B2),
                  (set_impl_prod _A3 _B3))))
    | DList_set dxs, DList_set dys ->
        (match ceq _A1
          with None ->
            failwith "product DList_set DList_set: ceq1 = None"
              (fun _ ->
                productc (_A1, _A2, _A3) (_B1, _B2, _B3) (DList_set dxs)
                  (DList_set dys))
          | Some _ ->
            (match ceq _B1
              with None ->
                failwith "product DList_set DList_set: ceq2 = None"
                  (fun _ ->
                    productc (_A1, _A2, _A3) (_B1, _B2, _B3) (DList_set dxs)
                      (DList_set dys))
              | Some _ -> DList_set (productb _A1 _B1 dxs dys)))
    | a1, DList_set dys ->
        (match ceq _B1
          with None ->
            failwith "product DList_set2: ceq = None"
              (fun _ ->
                productc (_A1, _A2, _A3) (_B1, _B2, _B3) a1 (DList_set dys))
          | Some _ ->
            foldc _B1
              (fun y ->
                sup_seta ((ceq_prod _A1 _B1), (ccompare_prod _A2 _B2))
                  (image (_A1, _A2)
                    ((ceq_prod _A1 _B1), (ccompare_prod _A2 _B2),
                      (set_impl_prod _A3 _B3))
                    (fun x -> (x, y)) a1))
              dys (bot_set
                    ((ceq_prod _A1 _B1), (ccompare_prod _A2 _B2),
                      (set_impl_prod _A3 _B3))))
    | DList_set dxs, b1 ->
        (match ceq _A1
          with None ->
            failwith "product DList_set1: ceq = None"
              (fun _ ->
                productc (_A1, _A2, _A3) (_B1, _B2, _B3) (DList_set dxs) b1)
          | Some _ ->
            foldc _A1
              (fun x ->
                sup_seta ((ceq_prod _A1 _B1), (ccompare_prod _A2 _B2))
                  (image (_B1, _B2)
                    ((ceq_prod _A1 _B1), (ccompare_prod _A2 _B2),
                      (set_impl_prod _A3 _B3))
                    (fun a -> (x, a)) b1))
              dxs (bot_set
                    ((ceq_prod _A1 _B1), (ccompare_prod _A2 _B2),
                      (set_impl_prod _A3 _B3))))
    | Set_Monad xs, Set_Monad ys ->
        Set_Monad
          (fold (fun x -> fold (fun y -> (fun a -> (x, y) :: a)) ys) xs [])
    | a, b ->
        Collect_set
          (fun (x, y) -> member (_A1, _A2) x a && member (_B1, _B2) y b);;

let rec add_new_mmuaux
  args rel1 rel2 nt aux =
    (let (tp, (tss, (tables,
                      (len, (maskL,
                              (maskR,
                                (result,
                                  (a1_map, (a2_map, (tstp_map, donea))))))))))
       = shift_mmuaux args nt aux in
     let i = args_ivl args in
     let pos = args_pos args in
     let new_tstp = (if memL i zero_nata then Inr tp else Inl nt) in
     let tstp_mapa = updateb (ccompare_nat, equal_nat) tp nt tstp_map in
     let tmp =
       sup_seta
         ((ceq_prod ceq_nat (ceq_list (ceq_option ceq_event_data))),
           (ccompare_prod ccompare_nat
             (ccompare_list (ccompare_option ccompare_event_data))))
         (sup_setb
           ((finite_UNIV_prod finite_UNIV_nat finite_UNIV_list),
             (cenum_prod cenum_nat cenum_list),
             (ceq_prod ceq_nat (ceq_list (ceq_option ceq_event_data))),
             (cproper_interval_prod cproper_interval_nat
               (cproper_interval_list (ccompare_option ccompare_event_data))),
             (set_impl_prod set_impl_nat set_impl_list))
           (image
             ((ceq_list (ceq_option ceq_event_data)),
               (ccompare_list (ccompare_option ccompare_event_data)))
             ((ceq_set
                ((cenum_prod cenum_nat cenum_list),
                  (ceq_prod ceq_nat (ceq_list (ceq_option ceq_event_data))),
                  (cproper_interval_prod cproper_interval_nat
                    (cproper_interval_list
                      (ccompare_option
                        ccompare_event_data))).ccompare_cproper_interval)),
               (ccompare_set
                 ((finite_UNIV_prod finite_UNIV_nat finite_UNIV_list),
                   (ceq_prod ceq_nat (ceq_list (ceq_option ceq_event_data))),
                   (cproper_interval_prod cproper_interval_nat
                     (cproper_interval_list
                       (ccompare_option ccompare_event_data))),
                   (set_impl_prod set_impl_nat set_impl_list))),
               set_impl_set)
             (fun asa ->
               (match
                 lookupa
                   ((ccompare_list (ccompare_option ccompare_event_data)),
                     (equal_list (equal_option equal_event_data)))
                   a1_map (proj_tuple maskL asa)
                 with None ->
                   (if not pos
                     then insert
                            ((ceq_prod ceq_nat
                               (ceq_list (ceq_option ceq_event_data))),
                              (ccompare_prod ccompare_nat
                                (ccompare_list
                                  (ccompare_option ccompare_event_data))))
                            (minus_nata tp len, asa)
                            (set_empty
                              ((ceq_prod ceq_nat
                                 (ceq_list (ceq_option ceq_event_data))),
                                (ccompare_prod ccompare_nat
                                  (ccompare_list
                                    (ccompare_option ccompare_event_data))))
                              (of_phantom
                                (set_impl_proda set_impl_nat set_impl_list)))
                     else set_empty
                            ((ceq_prod ceq_nat
                               (ceq_list (ceq_option ceq_event_data))),
                              (ccompare_prod ccompare_nat
                                (ccompare_list
                                  (ccompare_option ccompare_event_data))))
                            (of_phantom
                              (set_impl_proda set_impl_nat set_impl_list)))
                 | Some tpa ->
                   (if pos
                     then insert
                            ((ceq_prod ceq_nat
                               (ceq_list (ceq_option ceq_event_data))),
                              (ccompare_prod ccompare_nat
                                (ccompare_list
                                  (ccompare_option ccompare_event_data))))
                            (max ord_nat (minus_nata tp len) tpa, asa)
                            (set_empty
                              ((ceq_prod ceq_nat
                                 (ceq_list (ceq_option ceq_event_data))),
                                (ccompare_prod ccompare_nat
                                  (ccompare_list
                                    (ccompare_option ccompare_event_data))))
                              (of_phantom
                                (set_impl_proda set_impl_nat set_impl_list)))
                     else insert
                            ((ceq_prod ceq_nat
                               (ceq_list (ceq_option ceq_event_data))),
                              (ccompare_prod ccompare_nat
                                (ccompare_list
                                  (ccompare_option ccompare_event_data))))
                            (max ord_nat (minus_nata tp len)
                               (plus_nata tpa one_nata),
                              asa)
                            (set_empty
                              ((ceq_prod ceq_nat
                                 (ceq_list (ceq_option ceq_event_data))),
                                (ccompare_prod ccompare_nat
                                  (ccompare_list
                                    (ccompare_option ccompare_event_data))))
                              (of_phantom
                                (set_impl_proda set_impl_nat set_impl_list))))))
             rel2))
         (if memL i zero_nata
           then productc (ceq_nat, ccompare_nat, set_impl_nat)
                  ((ceq_list (ceq_option ceq_event_data)),
                    (ccompare_list (ccompare_option ccompare_event_data)),
                    set_impl_list)
                  (insert (ceq_nat, ccompare_nat) tp
                    (set_empty (ceq_nat, ccompare_nat)
                      (of_phantom set_impl_nata)))
                  rel2
           else set_empty
                  ((ceq_prod ceq_nat (ceq_list (ceq_option ceq_event_data))),
                    (ccompare_prod ccompare_nat
                      (ccompare_list (ccompare_option ccompare_event_data))))
                  (of_phantom (set_impl_proda set_impl_nat set_impl_list)))
       in
     let tmpa =
       filter
         ((ceq_prod ceq_nat (ceq_list (ceq_option ceq_event_data))),
           (ccompare_prod ccompare_nat
             (ccompare_list (ccompare_option ccompare_event_data))))
         (fun (tpa, _) ->
           (let Some ts = lookupa (ccompare_nat, equal_nat) tstp_mapa tpa in
             memL i (minus_nata nt ts)))
         tmp
       in
     let table =
       image ((ceq_prod ceq_nat (ceq_list (ceq_option ceq_event_data))),
               (ccompare_prod ccompare_nat
                 (ccompare_list (ccompare_option ccompare_event_data))))
         ((ceq_list (ceq_option ceq_event_data)),
           (ccompare_list (ccompare_option ccompare_event_data)), set_impl_list)
         snd tmpa
       in
     let tablesa =
       append_queue (table, (if memL i zero_nata then Inr tp else Inl nt))
         tables
       in
     let a2_mapa =
       updateb (ccompare_nat, equal_nat) (plus_nata tp one_nata)
         (mapping_empty (ccompare_list (ccompare_option ccompare_event_data))
           (of_phantom mapping_impl_lista))
         (upd_nested_max_tstp
           (finite_UNIV_nat, ceq_nat, ccompare_nat, equal_nat)
           (finite_UNIV_list, (ceq_list (ceq_option ceq_event_data)),
             (ccompare_list (ccompare_option ccompare_event_data)),
             (equal_list (equal_option equal_event_data)), mapping_impl_list)
           a2_map new_tstp tmpa)
       in
     let a1_mapa =
       (if pos
         then filterc (ccompare_list (ccompare_option ccompare_event_data))
                (fun asa _ ->
                  member
                    ((ceq_list (ceq_option ceq_event_data)),
                      (ccompare_list (ccompare_option ccompare_event_data)))
                    asa rel1)
                (upd_set
                  (finite_UNIV_list, (ceq_list (ceq_option ceq_event_data)),
                    (ccompare_list (ccompare_option ccompare_event_data)),
                    (equal_list (equal_option equal_event_data)))
                  a1_map (fun _ -> tp)
                  (filter
                    ((ceq_list (ceq_option ceq_event_data)),
                      (ccompare_list (ccompare_option ccompare_event_data)))
                    (fun k ->
                      is_none
                        (lookupa
                          ((ccompare_list
                             (ccompare_option ccompare_event_data)),
                            (equal_list (equal_option equal_event_data)))
                          a1_map k))
                    rel1))
         else upd_set
                (finite_UNIV_list, (ceq_list (ceq_option ceq_event_data)),
                  (ccompare_list (ccompare_option ccompare_event_data)),
                  (equal_list (equal_option equal_event_data)))
                a1_map (fun _ -> tp) rel1)
       in
     let tssa = append_queue nt tss in
      (plus_nata tp one_nata,
        (tssa,
          (tablesa,
            (plus_nata len one_nata,
              (maskL,
                (maskR,
                  (sup_seta
                     ((ceq_list (ceq_option ceq_event_data)),
                       (ccompare_list (ccompare_option ccompare_event_data)))
                     result
                     (image
                       ((ceq_prod ceq_nat
                          (ceq_list (ceq_option ceq_event_data))),
                         (ccompare_prod ccompare_nat
                           (ccompare_list
                             (ccompare_option ccompare_event_data))))
                       ((ceq_list (ceq_option ceq_event_data)),
                         (ccompare_list (ccompare_option ccompare_event_data)),
                         set_impl_list)
                       snd (filter
                             ((ceq_prod ceq_nat
                                (ceq_list (ceq_option ceq_event_data))),
                               (ccompare_prod ccompare_nat
                                 (ccompare_list
                                   (ccompare_option ccompare_event_data))))
                             (fun (t, _) -> equal_nata t (minus_nata tp len))
                             tmpa)),
                    (a1_mapa, (a2_mapa, (tstp_mapa, donea)))))))))));;

let rec to_add_set_fun _A (_B1, _B2, _B3)
  a m elem s =
    (if eq _A a (fst elem) && is_none (lookupa (_B2, _B3) m (snd elem))
      then insert (_B1, _B2) (snd elem) s else s);;

let rec to_add_set_cfi _A (_B1, _B2, _B3)
  xb xc = Abs_comp_fun_idem (to_add_set_fun _A (_B1, _B2, _B3) xb xc);;

let rec to_add_set (_A1, _A2, _A3, _A4) (_B1, _B2, _B3, _B4, _B5)
  a m tmp =
    (if finite
          ((finite_UNIV_prod _A1 _B1), (ceq_prod _A2 _B2),
            (ccompare_prod _A3 _B3))
          tmp
      then set_fold_cfi ((ceq_prod _A2 _B2), (ccompare_prod _A3 _B3))
             (to_add_set_cfi _A4 (_B2, _B3, _B4) a m) (bot_set (_B2, _B3, _B5))
             tmp
      else failwith "to_add_set: infinite set"
             (fun _ ->
               to_add_set (_A1, _A2, _A3, _A4) (_B1, _B2, _B3, _B4, _B5) a m
                 tmp));;

let rec add_new_mmauaux
  args rel1 rel2 nt (mmuaux, aggaux) =
    (match args_agg args
      with None ->
        (let (tp, (tss, (tables,
                          (len, (maskL,
                                  (maskR,
                                    (result,
                                      (a1_map,
(a2_map, (tstp_map, donea))))))))))
           = add_new_mmuaux args rel1 rel2 nt mmuaux in
          ((tp, (tss, (tables,
                        (len, (maskL,
                                (maskR,
                                  (result,
                                    (a1_map,
                                      (a2_map, (tstp_map, donea)))))))))),
            aggaux))
      | Some aggargs ->
        (let a = shift_mmauaux args nt (mmuaux, aggaux) in
         let (aa, b) = a in
          (let (tp, (tss, (tables,
                            (len, (maskL,
                                    (maskR,
                                      (result,
(a1_map, (a2_map, (tstp_map, donea))))))))))
             = aa in
            (fun aggauxa ->
              (let i = args_ivl args in
               let pos = args_pos args in
               let new_tstp = (if memL i zero_nata then Inr tp else Inl nt) in
               let tstp_mapa = updateb (ccompare_nat, equal_nat) tp nt tstp_map
                 in
               let m =
                 (let Some m =
                    lookupa (ccompare_nat, equal_nat) a2_map (minus_nata tp len)
                    in
                   m)
                 in
               let tmp =
                 sup_seta
                   ((ceq_prod ceq_nat (ceq_list (ceq_option ceq_event_data))),
                     (ccompare_prod ccompare_nat
                       (ccompare_list (ccompare_option ccompare_event_data))))
                   (sup_setb
                     ((finite_UNIV_prod finite_UNIV_nat finite_UNIV_list),
                       (cenum_prod cenum_nat cenum_list),
                       (ceq_prod ceq_nat
                         (ceq_list (ceq_option ceq_event_data))),
                       (cproper_interval_prod cproper_interval_nat
                         (cproper_interval_list
                           (ccompare_option ccompare_event_data))),
                       (set_impl_prod set_impl_nat set_impl_list))
                     (image
                       ((ceq_list (ceq_option ceq_event_data)),
                         (ccompare_list (ccompare_option ccompare_event_data)))
                       ((ceq_set
                          ((cenum_prod cenum_nat cenum_list),
                            (ceq_prod ceq_nat
                              (ceq_list (ceq_option ceq_event_data))),
                            (cproper_interval_prod cproper_interval_nat
                              (cproper_interval_list
                                (ccompare_option
                                  ccompare_event_data))).ccompare_cproper_interval)),
                         (ccompare_set
                           ((finite_UNIV_prod finite_UNIV_nat finite_UNIV_list),
                             (ceq_prod ceq_nat
                               (ceq_list (ceq_option ceq_event_data))),
                             (cproper_interval_prod cproper_interval_nat
                               (cproper_interval_list
                                 (ccompare_option ccompare_event_data))),
                             (set_impl_prod set_impl_nat set_impl_list))),
                         set_impl_set)
                       (fun asa ->
                         (match
                           lookupa
                             ((ccompare_list
                                (ccompare_option ccompare_event_data)),
                               (equal_list (equal_option equal_event_data)))
                             a1_map (proj_tuple maskL asa)
                           with None ->
                             (if not pos
                               then insert
                                      ((ceq_prod ceq_nat
 (ceq_list (ceq_option ceq_event_data))),
(ccompare_prod ccompare_nat
  (ccompare_list (ccompare_option ccompare_event_data))))
                                      (minus_nata tp len, asa)
                                      (set_empty
((ceq_prod ceq_nat (ceq_list (ceq_option ceq_event_data))),
  (ccompare_prod ccompare_nat
    (ccompare_list (ccompare_option ccompare_event_data))))
(of_phantom (set_impl_proda set_impl_nat set_impl_list)))
                               else set_empty
                                      ((ceq_prod ceq_nat
 (ceq_list (ceq_option ceq_event_data))),
(ccompare_prod ccompare_nat
  (ccompare_list (ccompare_option ccompare_event_data))))
                                      (of_phantom
(set_impl_proda set_impl_nat set_impl_list)))
                           | Some tpa ->
                             (if pos
                               then insert
                                      ((ceq_prod ceq_nat
 (ceq_list (ceq_option ceq_event_data))),
(ccompare_prod ccompare_nat
  (ccompare_list (ccompare_option ccompare_event_data))))
                                      (max ord_nat (minus_nata tp len) tpa, asa)
                                      (set_empty
((ceq_prod ceq_nat (ceq_list (ceq_option ceq_event_data))),
  (ccompare_prod ccompare_nat
    (ccompare_list (ccompare_option ccompare_event_data))))
(of_phantom (set_impl_proda set_impl_nat set_impl_list)))
                               else insert
                                      ((ceq_prod ceq_nat
 (ceq_list (ceq_option ceq_event_data))),
(ccompare_prod ccompare_nat
  (ccompare_list (ccompare_option ccompare_event_data))))
                                      (max ord_nat (minus_nata tp len)
 (plus_nata tpa one_nata),
asa)
                                      (set_empty
((ceq_prod ceq_nat (ceq_list (ceq_option ceq_event_data))),
  (ccompare_prod ccompare_nat
    (ccompare_list (ccompare_option ccompare_event_data))))
(of_phantom (set_impl_proda set_impl_nat set_impl_list))))))
                       rel2))
                   (if memL i zero_nata
                     then productc (ceq_nat, ccompare_nat, set_impl_nat)
                            ((ceq_list (ceq_option ceq_event_data)),
                              (ccompare_list
                                (ccompare_option ccompare_event_data)),
                              set_impl_list)
                            (insert (ceq_nat, ccompare_nat) tp
                              (set_empty (ceq_nat, ccompare_nat)
                                (of_phantom set_impl_nata)))
                            rel2
                     else set_empty
                            ((ceq_prod ceq_nat
                               (ceq_list (ceq_option ceq_event_data))),
                              (ccompare_prod ccompare_nat
                                (ccompare_list
                                  (ccompare_option ccompare_event_data))))
                            (of_phantom
                              (set_impl_proda set_impl_nat set_impl_list)))
                 in
               let tmpa =
                 filter
                   ((ceq_prod ceq_nat (ceq_list (ceq_option ceq_event_data))),
                     (ccompare_prod ccompare_nat
                       (ccompare_list (ccompare_option ccompare_event_data))))
                   (fun (tpa, _) ->
                     (let Some ts =
                        lookupa (ccompare_nat, equal_nat) tstp_mapa tpa in
                       memL i (minus_nata nt ts)))
                   tmp
                 in
               let table =
                 image ((ceq_prod ceq_nat
                          (ceq_list (ceq_option ceq_event_data))),
                         (ccompare_prod ccompare_nat
                           (ccompare_list
                             (ccompare_option ccompare_event_data))))
                   ((ceq_list (ceq_option ceq_event_data)),
                     (ccompare_list (ccompare_option ccompare_event_data)),
                     set_impl_list)
                   snd tmpa
                 in
               let tablesa =
                 append_queue
                   (table, (if memL i zero_nata then Inr tp else Inl nt)) tables
                 in
               let a2_mapa =
                 updateb (ccompare_nat, equal_nat) (plus_nata tp one_nata)
                   (mapping_empty
                     (ccompare_list (ccompare_option ccompare_event_data))
                     (of_phantom mapping_impl_lista))
                   (upd_nested_max_tstp
                     (finite_UNIV_nat, ceq_nat, ccompare_nat, equal_nat)
                     (finite_UNIV_list, (ceq_list (ceq_option ceq_event_data)),
                       (ccompare_list (ccompare_option ccompare_event_data)),
                       (equal_list (equal_option equal_event_data)),
                       mapping_impl_list)
                     a2_map new_tstp tmpa)
                 in
               let a1_mapa =
                 (if pos
                   then filterc
                          (ccompare_list (ccompare_option ccompare_event_data))
                          (fun asa _ ->
                            member
                              ((ceq_list (ceq_option ceq_event_data)),
                                (ccompare_list
                                  (ccompare_option ccompare_event_data)))
                              asa rel1)
                          (upd_set
                            (finite_UNIV_list,
                              (ceq_list (ceq_option ceq_event_data)),
                              (ccompare_list
                                (ccompare_option ccompare_event_data)),
                              (equal_list (equal_option equal_event_data)))
                            a1_map (fun _ -> tp)
                            (filter
                              ((ceq_list (ceq_option ceq_event_data)),
                                (ccompare_list
                                  (ccompare_option ccompare_event_data)))
                              (fun k ->
                                is_none
                                  (lookupa
                                    ((ccompare_list
                                       (ccompare_option ccompare_event_data)),
                                      (equal_list
(equal_option equal_event_data)))
                                    a1_map k))
                              rel1))
                   else upd_set
                          (finite_UNIV_list,
                            (ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            (equal_list (equal_option equal_event_data)))
                          a1_map (fun _ -> tp) rel1)
                 in
               let to_add =
                 to_add_set (finite_UNIV_nat, ceq_nat, ccompare_nat, equal_nat)
                   (finite_UNIV_list, (ceq_list (ceq_option ceq_event_data)),
                     (ccompare_list (ccompare_option ccompare_event_data)),
                     (equal_list (equal_option equal_event_data)),
                     set_impl_list)
                   (minus_nata tp len) m tmpa
                 in
               let aggauxb = insert_maggauxa aggargs to_add aggauxa in
               let tssa = append_queue nt tss in
                ((plus_nata tp one_nata,
                   (tssa,
                     (tablesa,
                       (plus_nata len one_nata,
                         (maskL,
                           (maskR,
                             (sup_seta
                                ((ceq_list (ceq_option ceq_event_data)),
                                  (ccompare_list
                                    (ccompare_option ccompare_event_data)))
                                result
                                (image
                                  ((ceq_prod ceq_nat
                                     (ceq_list (ceq_option ceq_event_data))),
                                    (ccompare_prod ccompare_nat
                                      (ccompare_list
(ccompare_option ccompare_event_data))))
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list)
                                  snd (filter
((ceq_prod ceq_nat (ceq_list (ceq_option ceq_event_data))),
  (ccompare_prod ccompare_nat
    (ccompare_list (ccompare_option ccompare_event_data))))
(fun (t, _) -> equal_nata t (minus_nata tp len)) tmpa)),
                               (a1_mapa, (a2_mapa, (tstp_mapa, donea)))))))))),
                  aggauxb))))
            b));;

let rec eval_mmauaux
  args nt aux =
    (let a = shift_mmauaux args nt aux in
     let (aa, b) = a in
      (let (tp, (tss, (tables,
                        (len, (maskL,
                                (maskR,
                                  (result,
                                    (a1_map, (a2_map, (tstp_map, donea))))))))))
         = aa in
        (fun auxs ->
          (rev donea,
            ((tp, (tss, (tables,
                          (len, (maskL,
                                  (maskR,
                                    (result,
                                      (a1_map, (a2_map, (tstp_map, [])))))))))),
              auxs))))
        b);;

let rec rep_mbuf_t (MBuf2_t x) = linearize x;;

let rec mbuf_t_append (MBuf2_t xs) ys = MBuf2_t (fold append_queue ys xs);;

let mbuf_t_empty : 'a mbuf_t = MBuf2_t empty_queue;;

let rec letpast_meeval0 (_B1, _B2) _D
  eval j i ys xs p ts db phi =
    (let (ysa, phia) = eval ts (updateb (_B1, _B2) p xs db) phi in
      (if not (equal_nata (size _D phia) (size _D phi))
        then (mbuf_t_empty, (zero_nata, (None, phi)))
        else (match ysa
               with [] ->
                 (mbuf_t_append ys ysa,
                   (plus_nata i (size_lista xs), (None, phia)))
               | y :: _ ->
                 (if less_eq_nat j (suc (plus_nata i (size_lista xs)))
                   then (mbuf_t_append ys ysa,
                          (plus_nata i (size_lista xs), (Some y, phia)))
                   else letpast_meeval0 (_B1, _B2) _D eval j
                          (plus_nata i (size_lista xs)) (mbuf_t_append ys ysa)
                          ysa p [] (map_values _B1 (fun _ _ -> []) db)
                          phia))));;

let rec find_sub_in (_A1, _A2, _A3)
  x xa1 b = match x, xa1, b with x, [], b -> None
    | xa, x :: xs, b ->
        (if less_eq_set (_A1, _A2, _A3) x xa ||
              b && less_eq_set (_A1, _A2, _A3) xa x
          then Some ([], (x, xs))
          else (match find_sub_in (_A1, _A2, _A3) xa xs b with None -> None
                 | Some (ys, (z, zs)) -> Some (x :: ys, (z, zs))));;

let rec find_sub_False (_A1, _A2, _A3)
  x0 ns = match x0, ns with [], ns -> None
    | x :: xs, ns ->
        (match find_sub_in (_A1, _A2, _A3) x ns false
          with None ->
            (match find_sub_False (_A1, _A2, _A3) xs ns with None -> None
              | Some ((rs, (w, ws)), (ys, (z, zs))) ->
                Some ((x :: rs, (w, ws)), (ys, (z, zs))))
          | Some (ys, (z, zs)) -> Some (([], (x, xs)), (ys, (z, zs))));;

let rec proj_list_3
  xs (ys, (z, zs)) =
    (take (size_lista ys) xs,
      (nth xs (size_lista ys),
        take (size_lista zs) (drop (plus_nata (size_lista ys) one_nata) xs)));;

let rec dominate_False
  a_pos l_pos a_neg l_neg =
    (match find_sub_False (cenum_nat, ceq_nat, ccompare_nat) a_pos a_neg
      with None -> None
      | Some (pos_split, neg_split) ->
        Some ((pos_split, neg_split),
               (proj_list_3 l_pos pos_split, proj_list_3 l_neg neg_split)));;

let rec find_sub_True (_A1, _A2, _A3)
  = function [] -> None
    | x :: xs ->
        (match find_sub_in (_A1, _A2, _A3) x xs true
          with None ->
            (match find_sub_True (_A1, _A2, _A3) xs with None -> None
              | Some (ys, (w, (ws, (z, zs)))) ->
                Some (x :: ys, (w, (ws, (z, zs)))))
          | Some (ys, (z, zs)) -> Some ([], (x, (ys, (z, zs)))));;

let rec proj_list_5
  xs (ys, (w, (ws, (z, zs)))) =
    (take (size_lista ys) xs,
      (nth xs (size_lista ys),
        (take (size_lista ws) (drop (plus_nata (size_lista ys) one_nata) xs),
          (nth xs
             (plus_nata (plus_nata (size_lista ys) one_nata) (size_lista ws)),
            drop (plus_nata
                   (plus_nata (plus_nata (size_lista ys) one_nata)
                     (size_lista ws))
                   one_nata)
              xs))));;

let rec dominate_True
  a_pos l_pos =
    (match find_sub_True (cenum_nat, ceq_nat, ccompare_nat) a_pos
      with None -> None | Some split -> Some (split, proj_list_5 l_pos split));;

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

let rec proj _A (_B1, _B2, _B3)
  (RBT_set t) =
    (match ccompare _A
      with None ->
        failwith "proj: ccompare = None"
          (fun _ -> proj _A (_B1, _B2, _B3) (RBT_set t))
      | Some c ->
        (match ccompare _B2
          with None ->
            failwith "proj: ccompare = None"
              (fun _ -> proj _A (_B1, _B2, _B3) (RBT_set t))
          | Some _ ->
            (let m =
               rbt_set_to_rbt_comp (_B1, _B2, _B3) c
                 (impl_ofa (ccompare_prod _A _B2) t)
               in
              (fun a ->
                (match rbt_comp_lookup c m a
                  with None -> bot_set (_B1, _B2, _B3) | Some x -> x)))));;

let rec squery_of_query (_A1, _A2)
  i j q =
    (i, (j, image ((ceq_prod
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
                 ceq_fun),
                (ccompare_prod
                  (ccompare_set
                    (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                      set_impl_nat))
                  ccompare_fun),
                (set_impl_prod set_impl_set set_impl_fun))
              (fun (v, t) ->
                (v, proj (ccompare_list (ccompare_option _A2))
                      ((ceq_list (ceq_option _A1)),
                        (ccompare_list (ccompare_option _A2)), set_impl_list)
                      (image
                        ((ceq_list (ceq_option _A1)),
                          (ccompare_list (ccompare_option _A2)))
                        ((ceq_prod (ceq_list (ceq_option _A1))
                           (ceq_list (ceq_option _A1))),
                          (ccompare_prod (ccompare_list (ccompare_option _A2))
                            (ccompare_list (ccompare_option _A2))),
                          (set_impl_prod set_impl_list set_impl_list))
                        (fun ta ->
                          (restrict (inf_seta (ceq_nat, ccompare_nat) v i) ta,
                            restrict j ta))
                        t)))
              q));;

let rec query_of_squery (_A1, _A2)
  (i, (j, sq)) t =
    image ((ceq_prod
             (ceq_set
               (cenum_nat, ceq_nat,
                 cproper_interval_nat.ccompare_cproper_interval))
             ceq_fun),
            (ccompare_prod
              (ccompare_set
                (finite_UNIV_nat, ceq_nat, cproper_interval_nat, set_impl_nat))
              ccompare_fun))
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
      (fun (v, f) ->
        (inf_seta (ceq_nat, ccompare_nat) v j,
          f (restrict (inf_seta (ceq_nat, ccompare_nat) v i) t)))
      sq;;

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
          (fun (a, _) -> less_eq_set (cenum_nat, ceq_nat, ccompare_nat) a v) q;;

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

let rec remove_Union_cfi (_B1, _B2)
  xa = Abs_comp_fun_idem (fun x a -> minus_set (_B1, _B2) a (xa x));;

let rec remove_Union (_A1, _A2, _A3, _A4, _A5) (_B1, _B2, _B3)
  a x b =
    (if finite (_B1, _B2, _B3) x
      then set_fold_cfi (_B2, _B3)
             (remove_Union_cfi (_A3, _A4.ccompare_cproper_interval) b) a x
      else minus_set (_A3, _A4.ccompare_cproper_interval) a
             (sup_setb (_A1, _A2, _A3, _A4, _A5)
               (image (_B2, _B3)
                 ((ceq_set (_A2, _A3, _A4.ccompare_cproper_interval)),
                   (ccompare_set (_A1, _A3, _A4, _A5)), set_impl_set)
                 b x)));;

let rec merge_option = function (None, None) -> None
                       | (Some x, None) -> Some x
                       | (None, Some x) -> Some x
                       | (Some a, Some b) -> Some a;;

let rec merge t1 t2 = mapa merge_option (zip t1 t2);;

let rec part _B
  f pivot x2 = match f, pivot, x2 with
    f, pivot, x :: xs ->
      (let (lts, (eqs, gts)) = part _B f pivot xs in
       let xa = f x in
        (if less _B.order_linorder.preorder_order.ord_preorder xa pivot
          then (x :: lts, (eqs, gts))
          else (if less _B.order_linorder.preorder_order.ord_preorder pivot xa
                 then (lts, (eqs, x :: gts)) else (lts, (x :: eqs, gts)))))
    | f, pivot, [] -> ([], ([], []));;

let rec sort_key _B
  f xs =
    (match xs with [] -> [] | [_] -> xs
      | [x; y] ->
        (if less_eq _B.order_linorder.preorder_order.ord_preorder (f x) (f y)
          then xs else [y; x])
      | _ :: _ :: _ :: _ ->
        (let (lts, (eqs, gts)) =
           part _B f
             (f (nth xs
                  (divide_nata (size_lista xs) (nat_of_integer (Z.of_int 2)))))
             xs
           in
          sort_key _B f lts @ eqs @ sort_key _B f gts));;

let rec sorted_list_of_set (_A1, _A2, _A3, _A4)
  = function
    RBT_set rbt ->
      (match ccompare _A2
        with None ->
          failwith "sorted_list_of_set RBT_set: ccompare = None"
            (fun _ -> sorted_list_of_set (_A1, _A2, _A3, _A4) (RBT_set rbt))
        | Some _ -> sort_key _A4 (fun x -> x) (keysb _A2 rbt))
    | DList_set dxs ->
        (match ceq _A1
          with None ->
            failwith "sorted_list_of_set DList_set: ceq = None"
              (fun _ -> sorted_list_of_set (_A1, _A2, _A3, _A4) (DList_set dxs))
          | Some _ -> sort_key _A4 (fun x -> x) (list_of_dlist _A1 dxs))
    | Set_Monad xs -> sort_key _A4 (fun x -> x) (remdups _A3 xs);;

let rec arg_max_list _B
  f x1 = match f, x1 with f, [x] -> x
    | f, x :: y :: zs ->
        (let m = arg_max_list _B f (y :: zs) in
          (if less_eq _B.order_linorder.preorder_order.ord_preorder (f m) (f x)
            then x else m));;

let rec max_getIJ (_A1, _A2)
  q_pos q_neg v =
    (let x =
       arg_max_list linorder_nat (score (_A1, _A2) q_pos)
         (sorted_list_of_set (ceq_nat, ccompare_nat, equal_nat, linorder_nat) v)
       in
      (insert (ceq_nat, ccompare_nat) x
         (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)),
        minus_set (ceq_nat, ccompare_nat) v
          (insert (ceq_nat, ccompare_nat) x
            (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata)))));;

let rec new_max_getIJ_genericJoin (_A1, _A2)
  v q_pos q_neg =
    (if less_eq_nat (card (card_UNIV_nat, ceq_nat, ccompare_nat) v) one_nata
      then remove_Union
             (finite_UNIV_list, cenum_list, (ceq_list (ceq_option _A1)),
               (cproper_interval_list (ccompare_option _A2)), set_impl_list)
             ((finite_UNIV_prod (finite_UNIV_set finite_UNIV_nat)
                (finite_UNIV_set finite_UNIV_list)),
               (ceq_prod
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
             q_neg (fun (_, x) -> x)
      else (let (i, j) = max_getIJ (_A1, _A2) q_pos q_neg v in
            let q_I_pos =
              projectQuery (_A1, _A2) i (filterQuery (_A1, _A2) i q_pos) in
            let q_I_neg = filterQueryNeg (_A1, _A2) i q_neg in
            let r_I = new_max_getIJ_genericJoin (_A1, _A2) i q_I_pos q_I_neg in
             (if is_empty
                   (card_UNIV_list, (ceq_list (ceq_option _A1)),
                     (cproper_interval_list (ccompare_option _A2)))
                   r_I
               then set_empty
                      ((ceq_list (ceq_option _A1)),
                        (ccompare_list (ccompare_option _A2)))
                      (of_phantom set_impl_lista)
               else (let q_J_neg =
                       minus_set
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
                         q_neg q_I_neg
                       in
                     let q_J_pos = filterQuery (_A1, _A2) j q_pos in
                     let sQ_J_pos =
                       squery_of_query (_A1, _A2) i j
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
                                   set_impl_list))),
                             (set_impl_prod set_impl_set set_impl_set))
                           (fun (va, t) ->
                             (let vaa = inf_seta (ceq_nat, ccompare_nat) va i in
                              let r =
                                image ((ceq_list (ceq_option _A1)),
(ccompare_list (ccompare_option _A2)))
                                  ((ceq_list (ceq_option _A1)),
                                    (ccompare_list (ccompare_option _A2)),
                                    set_impl_list)
                                  (restrict vaa) r_I
                                in
                               (va, filter
                                      ((ceq_list (ceq_option _A1)),
(ccompare_list (ccompare_option _A2)))
                                      (fun ta ->
member ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
  (restrict vaa ta) r)
                                      t)))
                           q_J_pos)
                       in
                     let sQ_J_neg =
                       squery_of_query (_A1, _A2) i j
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
                                   set_impl_list))),
                             (set_impl_prod set_impl_set set_impl_set))
                           (fun (va, t) ->
                             (let vaa = inf_seta (ceq_nat, ccompare_nat) va i in
                              let r =
                                image ((ceq_list (ceq_option _A1)),
(ccompare_list (ccompare_option _A2)))
                                  ((ceq_list (ceq_option _A1)),
                                    (ccompare_list (ccompare_option _A2)),
                                    set_impl_list)
                                  (restrict vaa) r_I
                                in
                               (va, filter
                                      ((ceq_list (ceq_option _A1)),
(ccompare_list (ccompare_option _A2)))
                                      (fun ta ->
member ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
  (restrict vaa ta) r)
                                      t)))
                           q_J_neg)
                       in
                     let x =
                       image ((ceq_list (ceq_option _A1)),
                               (ccompare_list (ccompare_option _A2)))
                         ((ceq_prod (ceq_list (ceq_option _A1))
                            (ceq_set
                              (cenum_list, (ceq_list (ceq_option _A1)),
                                (cproper_interval_list
                                  (ccompare_option
                                    _A2)).ccompare_cproper_interval))),
                           (ccompare_prod (ccompare_list (ccompare_option _A2))
                             (ccompare_set
                               (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                                 (cproper_interval_list (ccompare_option _A2)),
                                 set_impl_list))),
                           (set_impl_prod set_impl_list set_impl_set))
                         (fun t ->
                           (t, new_max_getIJ_genericJoin (_A1, _A2) j
                                 (query_of_squery (_A1, _A2) sQ_J_pos t)
                                 (query_of_squery (_A1, _A2) sQ_J_neg t)))
                         r_I
                       in
                      sup_setb
                        (finite_UNIV_list, cenum_list,
                          (ceq_list (ceq_option _A1)),
                          (cproper_interval_list (ccompare_option _A2)),
                          set_impl_list)
                        (image
                          ((ceq_prod (ceq_list (ceq_option _A1))
                             (ceq_set
                               (cenum_list, (ceq_list (ceq_option _A1)),
                                 (cproper_interval_list
                                   (ccompare_option
                                     _A2)).ccompare_cproper_interval))),
                            (ccompare_prod (ccompare_list (ccompare_option _A2))
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
                          (fun (t, a) ->
                            image ((ceq_list (ceq_option _A1)),
                                    (ccompare_list (ccompare_option _A2)))
                              ((ceq_list (ceq_option _A1)),
                                (ccompare_list (ccompare_option _A2)),
                                set_impl_list)
                              (fun xx -> merge xx t) a)
                          x)))));;

let rec new_max_getIJ_wrapperGenericJoin (_A1, _A2)
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
               then remove_Union
                      (finite_UNIV_list, cenum_list,
                        (ceq_list (ceq_option _A1)),
                        (cproper_interval_list (ccompare_option _A2)),
                        set_impl_list)
                      ((finite_UNIV_prod (finite_UNIV_set finite_UNIV_nat)
                         (finite_UNIV_set finite_UNIV_list)),
                        (ceq_prod
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
                      q_neg (fun (_, x) -> x)
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
                           less_eq_set (cenum_nat, ceq_nat, ccompare_nat) a v &&
                             less_eq_nat one_nata
                               (card (card_UNIV_nat, ceq_nat, ccompare_nat) a))
                         q_neg
                       in
                      new_max_getIJ_genericJoin (_A1, _A2) v q a))));;

let rec mmulti_joina (_A1, _A2)
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
         (zip a_neg (drop (size_lista a_pos) l))
       in
      new_max_getIJ_wrapperGenericJoin (_A1, _A2) q a);;

let rec mmulti_join (_A1, _A2, _A3)
  n a_pos a_neg l =
    (if not (equal_nata (plus_nata (size_lista a_pos) (size_lista a_neg))
              (size_lista l))
      then set_empty
             ((ceq_list (ceq_option _A1)),
               (ccompare_list (ccompare_option _A2)))
             (of_phantom set_impl_lista)
      else (let l_pos = take (size_lista a_pos) l in
            let l_neg = drop (size_lista a_pos) l in
             (match dominate_True a_pos l_pos
               with None ->
                 (match dominate_False a_pos l_pos a_neg l_neg
                   with None -> mmulti_joina (_A1, _A2) a_pos a_neg l
                   | Some (((a_zs, (a_x, a_xs)), (a_ws, (a_y, a_ys))),
                            ((zs, (x, xs)), (ws, (y, ys))))
                     -> mmulti_join (_A1, _A2, _A3) n (a_zs @ a_x :: a_xs)
                          (a_ws @ a_ys)
                          ((zs @ bin_join (_A1, _A2, _A3) n a_x x false a_y y ::
                                   xs) @
                            ws @ ys))
               | Some ((a_zs, (a_x, (a_xs, (a_y, a_ys)))),
                        (zs, (x, (xs, (y, ys)))))
                 -> mmulti_join (_A1, _A2, _A3) n
                      (a_zs @
                        sup_seta (ceq_nat, ccompare_nat) a_x a_y :: a_xs @ a_ys)
                      a_neg
                      ((zs @ bin_join (_A1, _A2, _A3) n a_x x true a_y y ::
                               xs @ ys) @
                        l_neg))));;

let rec idx_create (_A1, _A2)
  t x = cluster
          ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)),
            set_impl_list)
          (ccompare_list (ccompare_option _A2))
          (comp (fun a -> Some a) (restrict x)) t;;

let rec wf_idx_of_set (_A1, _A2)
  xc xd xe xf =
    Abs_wf_idx
      (let a = xd in
       let i = inf_seta (ceq_nat, ccompare_nat) xe a in
        (xc, (a, (i, idx_create (_A1, _A2)
                       (filter
                         ((ceq_list (ceq_option _A1)),
                           (ccompare_list (ccompare_option _A2)))
                         (wf_tuple xc a) xf)
                       i))));;

let rec args_n
  (Args_ext (args_ivl, args_n, args_L, args_R, args_pos, args_agg, more)) =
    args_n;;

let rec args_R
  (Args_ext (args_ivl, args_n, args_L, args_R, args_pos, args_agg, more)) =
    args_R;;

let rec args_L
  (Args_ext (args_ivl, args_n, args_L, args_R, args_pos, args_agg, more)) =
    args_L;;

let rec wf_table_of_set_args (_A1, _A2)
  args x =
    Wf_table_of_idx
      (wf_idx_of_set (_A1, _A2) (args_n args) (args_R args) (args_L args) x);;

let rec minus_keys (_A1, _A2, _A3)
  x m = filter (_A1, _A2)
          (fun xa ->
            (match lookupa (_A2, _A3) m xa with None -> true | Some _ -> false))
          x;;

let rec rep_wf_set (Abs_wf_set x) = x;;

let rec wf_idx_of_wf_set (_A1, _A2)
  xb xc =
    Abs_wf_idx
      (let (n, a) = rep_wf_set xc in
       let (aa, t) = a in
       let i = inf_seta (ceq_nat, ccompare_nat) xb aa in
        (n, (aa, (i, idx_create (_A1, _A2) t i))));;

let rec wf_set_union (_A1, _A2)
  xb xc =
    Abs_wf_set
      ((let (n, a) = rep_wf_set xb in
        let (aa, t) = a in
         (fun (na, (aaa, ta)) ->
           (if equal_nata n na &&
                 set_eq (cenum_nat, ceq_nat, ccompare_nat) aa aaa
             then (n, (aa, sup_seta
                             ((ceq_list (ceq_option _A1)),
                               (ccompare_list (ccompare_option _A2)))
                             t ta))
             else (n, (aa, t)))))
        (rep_wf_set xc));;

let rec rep_wf_idx (Abs_wf_idx x) = x;;

let rec entriesa _A xa = entries (impl_ofa _A xa);;

let rec set_of_idx (_A1, _A2, _A3) (_B1, _B2, _B3, _B4, _B5)
  (RBT_Mapping t) =
    (match ccompare _A2
      with None ->
        failwith "set_of_idx RBT_Mapping: ccompare = None"
          (fun _ ->
            set_of_idx (_A1, _A2, _A3) (_B1, _B2, _B3, _B4, _B5)
              (RBT_Mapping t))
      | Some _ ->
        sup_setb (_B1, _B2, _B3, _B4, _B5)
          (image
            ((ceq_prod _A1 (ceq_set (_B2, _B3, _B4.ccompare_cproper_interval))),
              (ccompare_prod _A2 (ccompare_set (_B1, _B3, _B4, _B5))))
            ((ceq_set (_B2, _B3, _B4.ccompare_cproper_interval)),
              (ccompare_set (_B1, _B3, _B4, _B5)), set_impl_set)
            snd (set ((ceq_prod _A1
                        (ceq_set (_B2, _B3, _B4.ccompare_cproper_interval))),
                       (ccompare_prod _A2 (ccompare_set (_B1, _B3, _B4, _B5))),
                       (set_impl_prod _A3 set_impl_set))
                  (entriesa _A2 t))));;

let rec idx_reindex (_A1, _A2)
  ia i t =
    (if set_eq (cenum_nat, ceq_nat, ccompare_nat) i ia then t
      else idx_create (_A1, _A2)
             (set_of_idx
               ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2)), set_impl_list)
               (finite_UNIV_list, cenum_list, (ceq_list (ceq_option _A1)),
                 (cproper_interval_list (ccompare_option _A2)), set_impl_list)
               t)
             ia);;

let rec idx_union _A (_B1, _B2) = combine _A (sup_seta (_B1, _B2));;

let rec wf_idx_union (_A1, _A2)
  xb xc =
    Abs_wf_idx
      ((let (n, a) = rep_wf_idx xb in
        let (aa, (i, t)) = a in
         (fun (na, (aaa, (ia, ta))) ->
           (if equal_nata n na &&
                 set_eq (cenum_nat, ceq_nat, ccompare_nat) aa aaa
             then (let ib = inf_seta (ceq_nat, ccompare_nat) i ia in
                   let ic = idx_reindex (_A1, _A2) ib i t in
                   let iaa = idx_reindex (_A1, _A2) ib ia ta in
                    (n, (aa, (ib, idx_union
                                    (ccompare_list (ccompare_option _A2))
                                    ((ceq_list (ceq_option _A1)),
                                      (ccompare_list (ccompare_option _A2)))
                                    ic iaa))))
             else (n, (aa, (i, t))))))
        (rep_wf_idx xc));;

let rec wf_idx_cols x = (let (_, (_, (i, _))) = rep_wf_idx x in i);;

let rec wf_table_union (_A1, _A2)
  x0 x1 = match x0, x1 with
    Wf_table_of_wf_set t, Wf_table_of_idx i ->
      Wf_table_of_idx
        (wf_idx_union (_A1, _A2) (wf_idx_of_wf_set (_A1, _A2) (wf_idx_cols i) t)
          i)
    | Wf_table_of_wf_set ta, Wf_table_of_wf_set t ->
        Wf_table_of_wf_set (wf_set_union (_A1, _A2) ta t)
    | Wf_table_of_idx i, Wf_table_of_wf_set t ->
        Wf_table_of_idx
          (wf_idx_union (_A1, _A2) i
            (wf_idx_of_wf_set (_A1, _A2) (wf_idx_cols i) t))
    | Wf_table_of_idx ia, Wf_table_of_idx i ->
        Wf_table_of_idx (wf_idx_union (_A1, _A2) ia i);;

let rec add_new_table_mmsaux (_A1, _A2, _A3)
  args x
    (t, (gc, (maskL,
               (maskR,
                 (data_prev,
                   (data_in,
                     (table_in,
                       (wf_table_in,
                         (tuple_in, (wf_table_since, tuple_since))))))))))
    = (let xa =
         minus_keys
           ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)),
             (equal_list (equal_option _A3)))
           x tuple_since
         in
       let wf_table_sincea =
         wf_table_union (_A1, _A2) wf_table_since
           (wf_table_of_set_args (_A1, _A2) args xa)
         in
       let tuple_sincea =
         upd_set
           (finite_UNIV_list, (ceq_list (ceq_option _A1)),
             (ccompare_list (ccompare_option _A2)),
             (equal_list (equal_option _A3)))
           tuple_since (fun _ -> t) xa
         in
        (if memL (args_ivl args) zero_nata
          then (t, (gc, (maskL,
                          (maskR,
                            (data_prev,
                              (append_queue (t, x) data_in,
                                (sup_seta
                                   ((ceq_list (ceq_option _A1)),
                                     (ccompare_list (ccompare_option _A2)))
                                   table_in x,
                                  (wf_table_union (_A1, _A2) wf_table_in
                                     (wf_table_of_set_args (_A1, _A2) args x),
                                    (upd_set
                                       (finite_UNIV_list,
 (ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)),
 (equal_list (equal_option _A3)))
                                       tuple_in (fun _ -> t) x,
                                      (wf_table_sincea, tuple_sincea))))))))))
          else (t, (gc, (maskL,
                          (maskR,
                            (append_queue (t, x) data_prev,
                              (data_in,
                                (table_in,
                                  (wf_table_in,
                                    (tuple_in,
                                      (wf_table_sincea,
tuple_sincea))))))))))));;

let rec add_new_table_mmasaux
  args x
    ((nt, (gc, (maskL,
                 (maskR,
                   (data_prev,
                     (data_in,
                       (table_in,
                         (wf_table_in,
                           (tuple_in, (wf_table_since, tuple_since)))))))))),
      aggaux)
    = (let msaux =
         add_new_table_mmsaux
           (ceq_event_data, ccompare_event_data, equal_event_data) args x
           (nt, (gc, (maskL,
                       (maskR,
                         (data_prev,
                           (data_in,
                             (table_in,
                               (wf_table_in,
                                 (tuple_in,
                                   (wf_table_since, tuple_since))))))))))
         in
        (match args_agg args with None -> (msaux, aggaux)
          | Some aggargs ->
            (msaux,
              (if memL (args_ivl args) zero_nata
                then insert_maggauxa aggargs
                       (filter
                         ((ceq_list (ceq_option ceq_event_data)),
                           (ccompare_list
                             (ccompare_option ccompare_event_data)))
                         (fun k ->
                           is_none
                             (lookupa
                               ((ccompare_list
                                  (ccompare_option ccompare_event_data)),
                                 (equal_list (equal_option equal_event_data)))
                               tuple_in k))
                         x)
                       aggaux
                else aggaux))));;

let rec upd_set_keys (_C1, _C2, _C3, _C4)
  z (t, x) (m, y) =
    (upd_set (_C1, _C2, _C3, _C4) m (fun _ -> t) (z x t),
      sup_seta (_C2, _C3) y (z x t));;

let rec valid_tuple (_A1, _A2)
  tuple_since =
    (fun (t, asa) ->
      (match
        lookupa
          ((ccompare_list (ccompare_option _A1)),
            (equal_list (equal_option _A2)))
          tuple_since asa
        with None -> false | Some ta -> less_eq_nat ta t));;

let rec add_new_ts_mmsaux (_A1, _A2, _A3)
  args nt
    (t, (gc, (maskL,
               (maskR,
                 (data_prev,
                   (data_in,
                     (table_in,
                       (wf_table_in,
                         (tuple_in, (wf_table_since, tuple_since))))))))))
    = (let i = args_ivl args in
       let (data_preva, move) =
         takedropWhile_queue (fun (ta, _) -> memL i (minus_nata nt ta))
           data_prev
         in
       let data_ina = fold (fun (ta, x) -> append_queue (ta, x)) move data_in in
       let (tuple_ina, add) =
         fold (upd_set_keys
                (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                  (ccompare_list (ccompare_option _A2)),
                  (equal_list (equal_option _A3)))
                (fun x ta ->
                  filter
                    ((ceq_list (ceq_option _A1)),
                      (ccompare_list (ccompare_option _A2)))
                    (fun asa -> valid_tuple (_A2, _A3) tuple_since (ta, asa))
                    x))
           move
           (tuple_in,
             set_empty
               ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2)))
               (of_phantom set_impl_lista))
         in
        (nt, (gc, (maskL,
                    (maskR,
                      (data_preva,
                        (data_ina,
                          (sup_seta
                             ((ceq_list (ceq_option _A1)),
                               (ccompare_list (ccompare_option _A2)))
                             table_in add,
                            (wf_table_union (_A1, _A2) wf_table_in
                               (wf_table_of_set_args (_A1, _A2) args add),
                              (tuple_ina,
                                (wf_table_since, tuple_since)))))))))));;

let rec add_new_ts_mmasauxa
  args nt
    ((t, (gc, (maskL,
                (maskR,
                  (data_prev,
                    (data_in,
                      (table_in,
                        (wf_table_in,
                          (tuple_in, (wf_table_since, tuple_since)))))))))),
      aggaux)
    = (match args_agg args
        with None ->
          (add_new_ts_mmsaux
             (ceq_event_data, ccompare_event_data, equal_event_data) args nt
             (t, (gc, (maskL,
                        (maskR,
                          (data_prev,
                            (data_in,
                              (table_in,
                                (wf_table_in,
                                  (tuple_in,
                                    (wf_table_since, tuple_since)))))))))),
            aggaux)
        | Some aggargs ->
          (let i = args_ivl args in
           let (data_preva, move) =
             takedropWhile_queue (fun (ta, _) -> memL i (minus_nata nt ta))
               data_prev
             in
           let data_ina =
             fold (fun (ta, x) -> append_queue (ta, x)) move data_in in
           let (tuple_ina, add) =
             fold (upd_set_keys
                    (finite_UNIV_list, (ceq_list (ceq_option ceq_event_data)),
                      (ccompare_list (ccompare_option ccompare_event_data)),
                      (equal_list (equal_option equal_event_data)))
                    (fun x ta ->
                      filter
                        ((ceq_list (ceq_option ceq_event_data)),
                          (ccompare_list (ccompare_option ccompare_event_data)))
                        (fun asa ->
                          valid_tuple (ccompare_event_data, equal_event_data)
                            tuple_since (ta, asa))
                        x))
               move
               (tuple_in,
                 set_empty
                   ((ceq_list (ceq_option ceq_event_data)),
                     (ccompare_list (ccompare_option ccompare_event_data)))
                   (of_phantom set_impl_lista))
             in
            ((nt, (gc, (maskL,
                         (maskR,
                           (data_preva,
                             (data_ina,
                               (sup_seta
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)))
                                  table_in add,
                                 (wf_table_union
                                    (ceq_event_data, ccompare_event_data)
                                    wf_table_in
                                    (wf_table_of_set_args
                                      (ceq_event_data, ccompare_event_data) args
                                      add),
                                   (tuple_ina,
                                     (wf_table_since, tuple_since)))))))))),
              insert_maggauxa aggargs
                (filter
                  ((ceq_list (ceq_option ceq_event_data)),
                    (ccompare_list (ccompare_option ccompare_event_data)))
                  (fun k ->
                    is_none
                      (lookupa
                        ((ccompare_list (ccompare_option ccompare_event_data)),
                          (equal_list (equal_option equal_event_data)))
                        tuple_in k))
                  add)
                aggaux)));;

let rec dropWhile_queue
  f q = (match safe_hd q with (None, qa) -> qa
          | (Some a, qa) ->
            (if f a then dropWhile_queue f (tl_queue qa) else qa));;

let rec wf_set_antijoin (_A1, _A2, _A3)
  xb xc =
    Abs_wf_set
      ((let (n, a) = rep_wf_set xb in
        let (aa, t) = a in
         (fun (na, (aaa, ta)) ->
           (if equal_nata n na &&
                 less_eq_set (cenum_nat, ceq_nat, ccompare_nat) aaa aa
             then (n, (sup_seta (ceq_nat, ccompare_nat) aa aaa,
                        bin_join (_A1, _A2, _A3) n aa t false aaa ta))
             else (n, (aa, t)))))
        (rep_wf_set xc));;

let rec mapping_antijoin _A
  (RBT_Mapping t) (RBT_Mapping u) =
    (match ccompare _A
      with None ->
        failwith "mapping_antijoin RBT_Mapping: ccompare = None"
          (fun _ -> mapping_antijoin _A (RBT_Mapping t) (RBT_Mapping u))
      | Some _ -> RBT_Mapping (diff _A t u));;

let rec idx_antijoin _A (_B1, _B2, _B3)
  n aa ta a t =
    combine _A
      (sup_seta
        ((ceq_list (ceq_option _B1)), (ccompare_list (ccompare_option _B2))))
      (mapping_antijoin _A ta t)
      (filterc _A
        (fun _ tb ->
          not (is_empty
                (card_UNIV_list, (ceq_list (ceq_option _B1)),
                  (cproper_interval_list (ccompare_option _B2)))
                tb))
        (mapping_join _A (fun tb -> bin_join (_B1, _B2, _B3) n aa tb false a) ta
          t));;

let rec wf_idx_antijoin (_A1, _A2, _A3)
  xb xc =
    Abs_wf_idx
      ((let (n, a) = rep_wf_idx xb in
        let (aa, (i, t)) = a in
         (fun (na, (aaa, (ia, ta))) ->
           (if equal_nata n na &&
                 less_eq_set (cenum_nat, ceq_nat, ccompare_nat) aaa aa
             then (let ib = inf_seta (ceq_nat, ccompare_nat) i ia in
                    (if set_eq (cenum_nat, ceq_nat, ccompare_nat) ib aaa
                      then (let ic = idx_reindex (_A1, _A2) ib i t in
                             (n, (aa, (ib,
mapping_antijoin (ccompare_list (ccompare_option _A2)) ic ta))))
                      else (let ic = idx_reindex (_A1, _A2) ib i t in
                            let iaa = idx_reindex (_A1, _A2) ib ia ta in
                             (n, (aa, (ib,
idx_antijoin (ccompare_list (ccompare_option _A2)) (_A1, _A2, _A3) n aa ic aaa
  iaa))))))
             else (n, (aa, (i, t))))))
        (rep_wf_idx xc));;

let rec wf_table_antijoin (_A1, _A2, _A3)
  x0 x1 = match x0, x1 with
    Wf_table_of_wf_set t, Wf_table_of_idx i ->
      Wf_table_of_idx
        (wf_idx_antijoin (_A1, _A2, _A3)
          (wf_idx_of_wf_set (_A1, _A2) (wf_idx_cols i) t) i)
    | Wf_table_of_wf_set ta, Wf_table_of_wf_set t ->
        Wf_table_of_wf_set (wf_set_antijoin (_A1, _A2, _A3) ta t)
    | Wf_table_of_idx i, Wf_table_of_wf_set t ->
        Wf_table_of_idx
          (wf_idx_antijoin (_A1, _A2, _A3) i
            (wf_idx_of_wf_set (_A1, _A2) (wf_idx_cols i) t))
    | Wf_table_of_idx ia, Wf_table_of_idx i ->
        Wf_table_of_idx (wf_idx_antijoin (_A1, _A2, _A3) ia i);;

let rec filter_cfi _B (_A1, _A2, _A3, _A4)
  xa = Abs_comp_fun_idem
         (fun a (m, y) ->
           (match lookupa (_A2, _A3) m a with None -> (m, y)
             | Some u ->
               (if eq _B xa u
                 then (delete (_A2, _A3) a m,
                        sup_seta (_A1, _A2) y
                          (insert (_A1, _A2) a (bot_set (_A1, _A2, _A4))))
                 else (m, y))));;

let rec filter_set _A (_B1, _B2, _B3, _B4, _B5)
  (t, a) (m, y) =
    (if finite (_B1, _B2, _B3) a
      then set_fold_cfi (_B2, _B3) (filter_cfi _A (_B2, _B3, _B4, _B5) t) (m, y)
             a
      else failwith "upd_set: infinite"
             (fun _ -> filter_set _A (_B1, _B2, _B3, _B4, _B5) (t, a) (m, y)));;

let rec shift_end (_A1, _A2, _A3)
  args nt
    (t, (gc, (maskL,
               (maskR,
                 (data_prev,
                   (data_in,
                     (table_in,
                       (wf_table_in,
                         (tuple_in, (wf_table_since, tuple_since))))))))))
    = (let i = args_ivl args in
       let data_preva =
         dropWhile_queue (fun (ta, _) -> not (memR i (minus_nata nt ta)))
           data_prev
         in
       let (data_ina, discard) =
         takedropWhile_queue (fun (ta, _) -> not (memR i (minus_nata nt ta)))
           data_in
         in
       let (tuple_ina, del) =
         fold (filter_set equal_nat
                (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                  (ccompare_list (ccompare_option _A2)),
                  (equal_list (equal_option _A3)), set_impl_list))
           discard
           (tuple_in,
             set_empty
               ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2)))
               (of_phantom set_impl_lista))
         in
        (t, (gc, (maskL,
                   (maskR,
                     (data_preva,
                       (data_ina,
                         (minus_set
                            ((ceq_list (ceq_option _A1)),
                              (ccompare_list (ccompare_option _A2)))
                            table_in del,
                           (wf_table_antijoin (_A1, _A2, _A3) wf_table_in
                              (wf_table_of_set_args (_A1, _A2) args del),
                             (tuple_ina,
                               (wf_table_since, tuple_since)))))))))));;

let rec shift_end_mmasaux
  args nt
    ((t, (gc, (maskL,
                (maskR,
                  (data_prev,
                    (data_in,
                      (table_in,
                        (wf_table_in,
                          (tuple_in, (wf_table_since, tuple_since)))))))))),
      aggaux)
    = (match args_agg args
        with None ->
          (shift_end (ceq_event_data, ccompare_event_data, equal_event_data)
             args nt
             (t, (gc, (maskL,
                        (maskR,
                          (data_prev,
                            (data_in,
                              (table_in,
                                (wf_table_in,
                                  (tuple_in,
                                    (wf_table_since, tuple_since)))))))))),
            aggaux)
        | Some aggargs ->
          (let i = args_ivl args in
           let data_preva =
             dropWhile_queue (fun (ta, _) -> not (memR i (minus_nata nt ta)))
               data_prev
             in
           let (data_ina, discard) =
             takedropWhile_queue
               (fun (ta, _) -> not (memR i (minus_nata nt ta))) data_in
             in
           let (tuple_ina, del) =
             fold (filter_set equal_nat
                    (finite_UNIV_list, (ceq_list (ceq_option ceq_event_data)),
                      (ccompare_list (ccompare_option ccompare_event_data)),
                      (equal_list (equal_option equal_event_data)),
                      set_impl_list))
               discard
               (tuple_in,
                 set_empty
                   ((ceq_list (ceq_option ceq_event_data)),
                     (ccompare_list (ccompare_option ccompare_event_data)))
                   (of_phantom set_impl_lista))
             in
            ((t, (gc, (maskL,
                        (maskR,
                          (data_preva,
                            (data_ina,
                              (minus_set
                                 ((ceq_list (ceq_option ceq_event_data)),
                                   (ccompare_list
                                     (ccompare_option ccompare_event_data)))
                                 table_in del,
                                (wf_table_antijoin
                                   (ceq_event_data, ccompare_event_data,
                                     equal_event_data)
                                   wf_table_in
                                   (wf_table_of_set_args
                                     (ceq_event_data, ccompare_event_data) args
                                     del),
                                  (tuple_ina,
                                    (wf_table_since, tuple_since)))))))))),
              delete_maggauxa aggargs del aggaux)));;

let rec add_new_ts_mmasaux
  args nt aux = add_new_ts_mmasauxa args nt (shift_end_mmasaux args nt aux);;

let rec wf_set_join (_A1, _A2, _A3)
  xb xc =
    Abs_wf_set
      ((let (n, a) = rep_wf_set xb in
        let (aa, t) = a in
         (fun (na, (aaa, ta)) ->
           (if equal_nata n na
             then (n, (sup_seta (ceq_nat, ccompare_nat) aa aaa,
                        bin_join (_A1, _A2, _A3) n aa t true aaa ta))
             else (n, (aa, t)))))
        (rep_wf_set xc));;

let rec wf_idx_join (_A1, _A2, _A3)
  xb xc =
    Abs_wf_idx
      ((let (n, a) = rep_wf_idx xb in
        let (aa, (i, t)) = a in
         (fun (na, (aaa, (ia, ta))) ->
           (if equal_nata n na
             then (let ib = inf_seta (ceq_nat, ccompare_nat) i ia in
                   let ic = idx_reindex (_A1, _A2) ib i t in
                   let iaa = idx_reindex (_A1, _A2) ib ia ta in
                    (n, (sup_seta (ceq_nat, ccompare_nat) aa aaa,
                          (ib, idx_join (ccompare_list (ccompare_option _A2))
                                 (_A1, _A2, _A3) n aa ic aaa iaa))))
             else (n, (aa, (i, t))))))
        (rep_wf_idx xc));;

let rec wf_table_join (_A1, _A2, _A3)
  x0 x1 = match x0, x1 with
    Wf_table_of_wf_set t, Wf_table_of_idx i ->
      Wf_table_of_idx
        (wf_idx_join (_A1, _A2, _A3)
          (wf_idx_of_wf_set (_A1, _A2) (wf_idx_cols i) t) i)
    | Wf_table_of_wf_set ta, Wf_table_of_wf_set t ->
        Wf_table_of_wf_set (wf_set_join (_A1, _A2, _A3) ta t)
    | Wf_table_of_idx i, Wf_table_of_wf_set t ->
        Wf_table_of_idx
          (wf_idx_join (_A1, _A2, _A3) i
            (wf_idx_of_wf_set (_A1, _A2) (wf_idx_cols i) t))
    | Wf_table_of_idx ia, Wf_table_of_idx i ->
        Wf_table_of_idx (wf_idx_join (_A1, _A2, _A3) ia i);;

let rec wf_set_set x = (let (_, (_, t)) = rep_wf_set x in t);;

let rec wf_idx_set (_A1, _A2)
  x = (let (_, a) = rep_wf_idx x in
       let (_, aa) = a in
       let (_, ab) = aa in
        set_of_idx
          ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)),
            set_impl_list)
          (finite_UNIV_list, cenum_list, (ceq_list (ceq_option _A1)),
            (cproper_interval_list (ccompare_option _A2)), set_impl_list)
          ab);;

let rec wf_table_set (_A1, _A2)
  = function Wf_table_of_wf_set t -> wf_set_set t
    | Wf_table_of_idx t -> wf_idx_set (_A1, _A2) t;;

let rec join_mmsaux (_A1, _A2, _A3)
  args x
    (t, (gc, (maskL,
               (maskR,
                 (data_prev,
                   (data_in,
                     (table_in,
                       (wf_table_in,
                         (tuple_in, (wf_table_since, tuple_since))))))))))
    = (let pos = args_pos args in
        (if list_all not maskL
          then (let nones = replicate (size_lista maskL) None in
                let take_all =
                  equal_bool pos
                    (member
                      ((ceq_list (ceq_option _A1)),
                        (ccompare_list (ccompare_option _A2)))
                      nones x)
                  in
                let table_ina =
                  (if take_all then table_in
                    else set_empty
                           ((ceq_list (ceq_option _A1)),
                             (ccompare_list (ccompare_option _A2)))
                           (of_phantom set_impl_lista))
                  in
                let wf_table_ina =
                  (if take_all then wf_table_in
                    else wf_table_of_set_args (_A1, _A2) args
                           (set_empty
                             ((ceq_list (ceq_option _A1)),
                               (ccompare_list (ccompare_option _A2)))
                             (of_phantom set_impl_lista)))
                  in
                let tuple_ina =
                  (if take_all then tuple_in
                    else mapping_empty (ccompare_list (ccompare_option _A2))
                           (of_phantom mapping_impl_lista))
                  in
                let wf_table_sincea =
                  (if take_all then wf_table_since
                    else wf_table_of_set_args (_A1, _A2) args
                           (set_empty
                             ((ceq_list (ceq_option _A1)),
                               (ccompare_list (ccompare_option _A2)))
                             (of_phantom set_impl_lista)))
                  in
                let tuple_sincea =
                  (if take_all then tuple_since
                    else mapping_empty (ccompare_list (ccompare_option _A2))
                           (of_phantom mapping_impl_lista))
                  in
                 (t, (gc, (maskL,
                            (maskR,
                              (data_prev,
                                (data_in,
                                  (table_ina,
                                    (wf_table_ina,
                                      (tuple_ina,
(wf_table_sincea, tuple_sincea)))))))))))
          else (let wf_X =
                  Wf_table_of_idx
                    (wf_idx_of_set (_A1, _A2) (args_n args) (args_L args)
                      (args_L args) x)
                  in
                let wf_in_del =
                  (if pos then wf_table_antijoin (_A1, _A2, _A3)
                    else wf_table_join (_A1, _A2, _A3))
                    wf_table_in
                    wf_X
                  in
                let in_del = wf_table_set (_A1, _A2) wf_in_del in
                let tuple_ina =
                  mapping_delete_set
                    (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                      (ccompare_list (ccompare_option _A2)),
                      (equal_list (equal_option _A3)))
                    tuple_in in_del
                  in
                let table_ina =
                  minus_set
                    ((ceq_list (ceq_option _A1)),
                      (ccompare_list (ccompare_option _A2)))
                    table_in in_del
                  in
                let wf_table_ina =
                  wf_table_antijoin (_A1, _A2, _A3) wf_table_in wf_in_del in
                let wf_since_del =
                  (if pos then wf_table_antijoin (_A1, _A2, _A3)
                    else wf_table_join (_A1, _A2, _A3))
                    wf_table_since
                    wf_X
                  in
                let since_del = wf_table_set (_A1, _A2) wf_since_del in
                let tuple_sincea =
                  mapping_delete_set
                    (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                      (ccompare_list (ccompare_option _A2)),
                      (equal_list (equal_option _A3)))
                    tuple_since since_del
                  in
                let wf_table_sincea =
                  wf_table_antijoin (_A1, _A2, _A3) wf_table_since wf_since_del
                  in
                 (t, (gc, (maskL,
                            (maskR,
                              (data_prev,
                                (data_in,
                                  (table_ina,
                                    (wf_table_ina,
                                      (tuple_ina,
(wf_table_sincea, tuple_sincea)))))))))))));;

let rec join_mmasaux
  args x
    ((t, (gc, (maskL,
                (maskR,
                  (data_prev,
                    (data_in,
                      (table_in,
                        (wf_table_in,
                          (tuple_in, (wf_table_since, tuple_since)))))))))),
      aggaux)
    = (match args_agg args
        with None ->
          (join_mmsaux (ceq_event_data, ccompare_event_data, equal_event_data)
             args x
             (t, (gc, (maskL,
                        (maskR,
                          (data_prev,
                            (data_in,
                              (table_in,
                                (wf_table_in,
                                  (tuple_in,
                                    (wf_table_since, tuple_since)))))))))),
            aggaux)
        | Some aggargs ->
          (let pos = args_pos args in
            (if list_all not maskL
              then (let nones = replicate (size_lista maskL) None in
                    let take_all =
                      equal_bool pos
                        (member
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)))
                          nones x)
                      in
                    let table_ina =
                      (if take_all then table_in
                        else set_empty
                               ((ceq_list (ceq_option ceq_event_data)),
                                 (ccompare_list
                                   (ccompare_option ccompare_event_data)))
                               (of_phantom set_impl_lista))
                      in
                    let wf_table_ina =
                      (if take_all then wf_table_in
                        else wf_table_of_set_args
                               (ceq_event_data, ccompare_event_data) args
                               (set_empty
                                 ((ceq_list (ceq_option ceq_event_data)),
                                   (ccompare_list
                                     (ccompare_option ccompare_event_data)))
                                 (of_phantom set_impl_lista)))
                      in
                    let tuple_ina =
                      (if take_all then tuple_in
                        else mapping_empty
                               (ccompare_list
                                 (ccompare_option ccompare_event_data))
                               (of_phantom mapping_impl_lista))
                      in
                    let aggauxa =
                      (if take_all then aggaux else init_maggauxa aggargs) in
                    let wf_table_sincea =
                      (if take_all then wf_table_since
                        else wf_table_of_set_args
                               (ceq_event_data, ccompare_event_data) args
                               (set_empty
                                 ((ceq_list (ceq_option ceq_event_data)),
                                   (ccompare_list
                                     (ccompare_option ccompare_event_data)))
                                 (of_phantom set_impl_lista)))
                      in
                    let tuple_sincea =
                      (if take_all then tuple_since
                        else mapping_empty
                               (ccompare_list
                                 (ccompare_option ccompare_event_data))
                               (of_phantom mapping_impl_lista))
                      in
                     ((t, (gc, (maskL,
                                 (maskR,
                                   (data_prev,
                                     (data_in,
                                       (table_ina,
 (wf_table_ina, (tuple_ina, (wf_table_sincea, tuple_sincea)))))))))),
                       aggauxa))
              else (let wf_X =
                      Wf_table_of_idx
                        (wf_idx_of_set (ceq_event_data, ccompare_event_data)
                          (args_n args) (args_L args) (args_L args) x)
                      in
                    let wf_in_del =
                      (if pos
                        then wf_table_antijoin
                               (ceq_event_data, ccompare_event_data,
                                 equal_event_data)
                        else wf_table_join
                               (ceq_event_data, ccompare_event_data,
                                 equal_event_data))
                        wf_table_in
                        wf_X
                      in
                    let in_del =
                      wf_table_set (ceq_event_data, ccompare_event_data)
                        wf_in_del
                      in
                    let tuple_ina =
                      mapping_delete_set
                        (finite_UNIV_list,
                          (ceq_list (ceq_option ceq_event_data)),
                          (ccompare_list (ccompare_option ccompare_event_data)),
                          (equal_list (equal_option equal_event_data)))
                        tuple_in in_del
                      in
                    let table_ina =
                      minus_set
                        ((ceq_list (ceq_option ceq_event_data)),
                          (ccompare_list (ccompare_option ccompare_event_data)))
                        table_in in_del
                      in
                    let wf_table_ina =
                      wf_table_antijoin
                        (ceq_event_data, ccompare_event_data, equal_event_data)
                        wf_table_in wf_in_del
                      in
                    let wf_since_del =
                      (if pos
                        then wf_table_antijoin
                               (ceq_event_data, ccompare_event_data,
                                 equal_event_data)
                        else wf_table_join
                               (ceq_event_data, ccompare_event_data,
                                 equal_event_data))
                        wf_table_since
                        wf_X
                      in
                    let since_del =
                      wf_table_set (ceq_event_data, ccompare_event_data)
                        wf_since_del
                      in
                    let tuple_sincea =
                      mapping_delete_set
                        (finite_UNIV_list,
                          (ceq_list (ceq_option ceq_event_data)),
                          (ccompare_list (ccompare_option ccompare_event_data)),
                          (equal_list (equal_option equal_event_data)))
                        tuple_since since_del
                      in
                    let wf_table_sincea =
                      wf_table_antijoin
                        (ceq_event_data, ccompare_event_data, equal_event_data)
                        wf_table_since wf_since_del
                      in
                     ((t, (gc, (maskL,
                                 (maskR,
                                   (data_prev,
                                     (data_in,
                                       (table_ina,
 (wf_table_ina, (tuple_ina, (wf_table_sincea, tuple_sincea)))))))))),
                       delete_maggauxa aggargs in_del aggaux)))));;

let rec gc_mmsaux (_A1, _A2)
  args (nt, (gc, (maskL,
                   (maskR,
                     (data_prev,
                       (data_in,
                         (table_in,
                           (wf_table_in,
                             (tuple_in, (wf_table_since, tuple_since))))))))))
    = (let all_tuples =
         sup_setb
           (finite_UNIV_list, cenum_list, (ceq_list (ceq_option _A1)),
             (cproper_interval_list (ccompare_option _A2)), set_impl_list)
           (image
             ((ceq_prod ceq_nat
                (ceq_set
                  (cenum_list, (ceq_list (ceq_option _A1)),
                    (cproper_interval_list
                      (ccompare_option _A2)).ccompare_cproper_interval))),
               (ccompare_prod ccompare_nat
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
             snd (sup_seta
                   ((ceq_prod ceq_nat
                      (ceq_set
                        (cenum_list, (ceq_list (ceq_option _A1)),
                          (cproper_interval_list
                            (ccompare_option _A2)).ccompare_cproper_interval))),
                     (ccompare_prod ccompare_nat
                       (ccompare_set
                         (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                           (cproper_interval_list (ccompare_option _A2)),
                           set_impl_list))))
                   (set ((ceq_prod ceq_nat
                           (ceq_set
                             (cenum_list, (ceq_list (ceq_option _A1)),
                               (cproper_interval_list
                                 (ccompare_option
                                   _A2)).ccompare_cproper_interval))),
                          (ccompare_prod ccompare_nat
                            (ccompare_set
                              (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                                (cproper_interval_list (ccompare_option _A2)),
                                set_impl_list))),
                          (set_impl_prod set_impl_nat set_impl_set))
                     (linearize data_prev))
                   (set ((ceq_prod ceq_nat
                           (ceq_set
                             (cenum_list, (ceq_list (ceq_option _A1)),
                               (cproper_interval_list
                                 (ccompare_option
                                   _A2)).ccompare_cproper_interval))),
                          (ccompare_prod ccompare_nat
                            (ccompare_set
                              (finite_UNIV_list, (ceq_list (ceq_option _A1)),
                                (cproper_interval_list (ccompare_option _A2)),
                                set_impl_list))),
                          (set_impl_prod set_impl_nat set_impl_set))
                     (linearize data_in))))
         in
       let tuple_sincea =
         filterc (ccompare_list (ccompare_option _A2))
           (fun asa _ ->
             member
               ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2)))
               asa all_tuples)
           tuple_since
         in
        (nt, (nt, (maskL,
                    (maskR,
                      (data_prev,
                        (data_in,
                          (table_in,
                            (wf_table_in,
                              (tuple_in,
                                (wf_table_of_set_args (_A1, _A2) args
                                   (keys (cenum_list,
   (ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)),
   set_impl_list)
                                     tuple_sincea),
                                  tuple_sincea)))))))))));;

let rec gc_join_mmasaux
  args x
    ((t, (gc, (maskL,
                (maskR,
                  (data_prev,
                    (data_in,
                      (table_in,
                        (wf_table_in,
                          (tuple_in, (wf_table_since, tuple_since)))))))))),
      aux)
    = (if not (memR (args_ivl args) (minus_nata t gc))
        then join_mmasaux args x
               (gc_mmsaux (ceq_event_data, ccompare_event_data) args
                  (t, (gc, (maskL,
                             (maskR,
                               (data_prev,
                                 (data_in,
                                   (table_in,
                                     (wf_table_in,
                                       (tuple_in,
 (wf_table_since, tuple_since)))))))))),
                 aux)
        else join_mmasaux args x
               ((t, (gc, (maskL,
                           (maskR,
                             (data_prev,
                               (data_in,
                                 (table_in,
                                   (wf_table_in,
                                     (tuple_in,
                                       (wf_table_since, tuple_since)))))))))),
                 aux));;

let rec result_mmasaux
  args ((nt, (gc, (maskL,
                    (maskR,
                      (data_prev,
                        (data_in,
                          (table_in,
                            (wf_table_in,
                              (tuple_in, (wf_table_since, tuple_since)))))))))),
         aggaux)
    = (match (args_agg args, aggaux) with (None, _) -> table_in
        | (Some aggargs, None) -> eval_aggargs aggargs table_in
        | (Some aggargs, Some a) -> result_maggaux aggargs a);;

let rec mbuf_t_cases
  (MBuf2_t xs) =
    (match safe_hd xs with (None, xsa) -> (None, MBuf2_t xsa)
      | (Some x, xsa) -> (Some x, MBuf2_t (tl_queue xsa)));;

let rec mbuf_t_Cons x (MBuf2_t xs) = MBuf2_t (prepend_queue x xs);;

let rec meeval_since
  args rs (xs, (ys, (ts, skew))) aux =
    (match mbuf_t_cases ys
      with (None, _) ->
        (match mbuf_t_cases xs
          with (None, _) ->
            (rev rs, ((mbuf_t_empty, (mbuf_t_empty, (ts, skew))), aux))
          | (Some x, xsa) ->
            (match mbuf_t_cases ts
              with (None, _) ->
                (rev rs,
                  ((mbuf_t_Cons x xsa, (mbuf_t_empty, (mbuf_t_empty, skew))),
                    aux))
              | (Some t, tsa) ->
                (if skew || memL (args_ivl args) zero_nata
                  then (rev rs,
                         ((mbuf_t_Cons x xsa,
                            (mbuf_t_empty, (mbuf_t_Cons t tsa, skew))),
                           aux))
                  else (let auxa =
                          gc_join_mmasaux args x (add_new_ts_mmasaux args t aux)
                          in
                         (rev (result_mmasaux args auxa :: rs),
                           ((xsa, (mbuf_t_empty, (tsa, true))), auxa))))))
      | (Some y, ysa) ->
        (if skew
          then meeval_since args rs (xs, (ysa, (ts, false)))
                 (add_new_table_mmasaux args y aux)
          else (match mbuf_t_cases xs
                 with (None, _) ->
                   (rev rs,
                     ((mbuf_t_empty, (mbuf_t_Cons y ysa, (ts, skew))), aux))
                 | (Some x, xsa) ->
                   (match mbuf_t_cases ts
                     with (None, tsa) ->
                       (rev rs,
                         ((mbuf_t_Cons x xsa, (mbuf_t_Cons y ysa, (tsa, skew))),
                           aux))
                     | (Some t, tsa) ->
                       (let auxa =
                          add_new_table_mmasaux args y
                            (gc_join_mmasaux args x
                              (add_new_ts_mmasaux args t aux))
                          in
                         meeval_since args (result_mmasaux args auxa :: rs)
                           (xsa, (ysa, (tsa, false))) auxa)))));;

let rec is_emptyb
  xa = (match rep_queue xa with ([], []) -> true | ([], _ :: _) -> false
         | (_ :: _, _) -> false);;

let rec mbuf_t_is_empty (MBuf2_t xs) = is_emptyb xs;;

let rec mebufnt_take
  f z buf t0 ts =
    (match mbuf_t_cases ts with (None, _) -> (z, (buf, (t0, ts)))
      | (Some t, tsa) ->
        (if list_ex mbuf_t_is_empty buf then (z, (buf, (t, mbuf_t_Cons t tsa)))
          else mebufnt_take f
                 (f (mapa (comp (comp the fst) mbuf_t_cases) buf) t z)
                 (mapa (comp snd mbuf_t_cases) buf) t tsa));;

let rec mebuf2t_take
  f z (xs, ys) t0 ts =
    (match mbuf_t_cases ts with (None, tsa) -> (z, ((xs, ys), (t0, tsa)))
      | (Some t, tsa) ->
        (match mbuf_t_cases xs
          with (None, xsa) -> (z, ((xsa, ys), (t, mbuf_t_Cons t tsa)))
          | (Some x, xsa) ->
            (match mbuf_t_cases ys
              with (None, ysa) ->
                (z, ((mbuf_t_Cons x xsa, ysa), (t, mbuf_t_Cons t tsa)))
              | (Some y, ysa) ->
                mebuf2t_take f (f x y t z) (xsa, ysa) t tsa)));;

let rec meprev_next
  i xs ts =
    (match mbuf_t_cases xs with (None, _) -> ([], (mbuf_t_empty, ts))
      | (Some x, xsa) ->
        (match mbuf_t_cases ts
          with (None, _) -> ([], (mbuf_t_Cons x xsa, mbuf_t_empty))
          | (Some t, tsa) ->
            (match mbuf_t_cases tsa
              with (None, _) ->
                ([], (mbuf_t_Cons x xsa, mbuf_t_Cons t mbuf_t_empty))
              | (Some ta, tsb) ->
                (let a = meprev_next i xsa (mbuf_t_Cons ta tsb) in
                 let (ys, aa) = a in
                  ((if memL i (minus_nata ta t) && memR i (minus_nata ta t)
                     then x
                     else empty_table
                            ((ceq_list (ceq_option ceq_event_data)),
                              (ccompare_list
                                (ccompare_option ccompare_event_data)),
                              set_impl_list)) ::
                     ys,
                    aa)))));;

let rec mebufn_take
  f z buf =
    (if null buf || list_ex mbuf_t_is_empty buf then (z, buf)
      else mebufn_take f (f (mapa (comp (comp the fst) mbuf_t_cases) buf) z)
             (mapa (comp snd mbuf_t_cases) buf));;

let rec mebuf2_take
  f (xs, ys) =
    (match mbuf_t_cases xs with (None, xsa) -> ([], (xsa, ys))
      | (Some x, xsa) ->
        (match mbuf_t_cases ys
          with (None, ysa) -> ([], (mbuf_t_Cons x xsa, ysa))
          | (Some y, ysa) ->
            (let a = mebuf2_take f (xsa, ysa) in
             let (zs, aa) = a in
              (f x y :: zs, aa))));;

let rec mebuf2S_add
  xsa ysa tsa (xs, (ys, (ts, skew))) =
    (mbuf_t_append xs xsa,
      (mbuf_t_append ys ysa, (mbuf_t_append ts tsa, skew)));;

let rec mebufn_add
  xsa xs = mapa (fun (a, b) -> mbuf_t_append a b) (zip xs xsa);;

let rec mebuf2_add
  xsa ysa (xs, ys) = (mbuf_t_append xs xsa, mbuf_t_append ys ysa);;

let rec eval_constraint0
  xa0 x y = match xa0, x, y with MEq, x, y -> equal_event_dataa x y
    | MLess, x, y -> less_event_data x y
    | MLessEq, x, y -> less_eq_event_data x y;;

let rec eval_constraint
  (t1, (p, (c, t2))) x =
    equal_bool (eval_constraint0 c (meval_trm t1 x) (meval_trm t2 x)) p;;

let rec eval_assignment (x, t) y = list_update y x (Some (meval_trm t y));;

let rec list_of_option = function None -> []
                         | Some x -> [x];;

let rec r_epsilon_strict (_A1, _A2, _A3)
  n phi_s x2 = match n, phi_s, x2 with
    n, phi_s, MSkip m ->
      (if equal_nata m zero_nata then unit_table (_A1, _A2) n
        else empty_table
               ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2)), set_impl_list))
    | n, phi_s, MTestPos i -> nth phi_s i
    | n, phi_s, MTestNeg i ->
        (if is_empty
              (card_UNIV_list, (ceq_list (ceq_option _A1)),
                (cproper_interval_list (ccompare_option _A2)))
              (nth phi_s i)
          then unit_table (_A1, _A2) n
          else empty_table
                 ((ceq_list (ceq_option _A1)),
                   (ccompare_list (ccompare_option _A2)), set_impl_list))
    | n, phi_s, MPlus (r, s) ->
        sup_seta
          ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
          (r_epsilon_strict (_A1, _A2, _A3) n phi_s r)
          (r_epsilon_strict (_A1, _A2, _A3) n phi_s s)
    | n, phi_s, MTimes (r, s) ->
        epsilon_lax (_A1, _A2, _A3) (r_epsilon_strict (_A1, _A2, _A3) n phi_s r)
          phi_s s
    | n, phi_s, MStar r -> unit_table (_A1, _A2) n;;

let rec update_matchP
  n i mr mrs rels nt aux =
    (let auxa =
       (match
         maps (fun (t, rel) ->
                (if memR i (minus_nata nt t)
                  then [(t, mrtabulate (ceq_event_data, ccompare_event_data) mrs
                              (fun mra ->
                                sup_seta
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)))
                                  (r_delta
                                    (ceq_event_data, ccompare_event_data,
                                      equal_event_data)
                                    id rel rels mra)
                                  (if equal_nata t nt
                                    then r_epsilon_strict
   (ceq_event_data, ccompare_event_data, equal_event_data) n rels mra
                                    else set_empty
   ((ceq_list (ceq_option ceq_event_data)),
     (ccompare_list (ccompare_option ccompare_event_data)))
   (of_phantom set_impl_lista))))]
                  else []))
           aux
         with [] ->
           [(nt, mrtabulate (ceq_event_data, ccompare_event_data) mrs
                   (r_epsilon_strict
                     (ceq_event_data, ccompare_event_data, equal_event_data) n
                     rels))]
         | x :: auxa ->
           (if equal_nata (fst x) nt then x :: auxa
             else (nt, mrtabulate (ceq_event_data, ccompare_event_data) mrs
                         (r_epsilon_strict
                           (ceq_event_data, ccompare_event_data,
                             equal_event_data)
                           n rels)) ::
                    x :: auxa))
       in
      (foldr (sup_seta
               ((ceq_list (ceq_option ceq_event_data)),
                 (ccompare_list (ccompare_option ccompare_event_data))))
         (maps (fun (t, rel) ->
                 (if memL i (minus_nata nt t)
                   then [lookupb (ccompare_mregex, equal_mregex)
                           ((ceq_list (ceq_option ceq_event_data)),
                             (ccompare_list
                               (ccompare_option ccompare_event_data)),
                             set_impl_list)
                           rel mr]
                   else []))
           auxa)
         (set_empty
           ((ceq_list (ceq_option ceq_event_data)),
             (ccompare_list (ccompare_option ccompare_event_data)))
           (of_phantom set_impl_lista)),
        auxa));;

let rec update_matchF_step (_A1, _A2, _A3)
  i mr mrs nt =
    (fun (t, (rels, rel)) (aux, x) ->
      (let y = mrtabulate (_A1, _A2) mrs (l_delta (_A1, _A2, _A3) id x rels) in
        ((t, (rels,
               (if memL i (minus_nata nt t) && memR i (minus_nata nt t)
                 then sup_seta
                        ((ceq_list (ceq_option _A1)),
                          (ccompare_list (ccompare_option _A2)))
                        rel (lookupb (ccompare_mregex, equal_mregex)
                              ((ceq_list (ceq_option _A1)),
                                (ccompare_list (ccompare_option _A2)),
                                set_impl_list)
                              y mr)
                 else rel))) ::
           aux,
          y)));;

let rec l_epsilon_strict (_A1, _A2, _A3)
  n phi_s x2 = match n, phi_s, x2 with
    n, phi_s, MSkip m ->
      (if equal_nata m zero_nata then unit_table (_A1, _A2) n
        else empty_table
               ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2)), set_impl_list))
    | n, phi_s, MTestPos i -> nth phi_s i
    | n, phi_s, MTestNeg i ->
        (if is_empty
              (card_UNIV_list, (ceq_list (ceq_option _A1)),
                (cproper_interval_list (ccompare_option _A2)))
              (nth phi_s i)
          then unit_table (_A1, _A2) n
          else empty_table
                 ((ceq_list (ceq_option _A1)),
                   (ccompare_list (ccompare_option _A2)), set_impl_list))
    | n, phi_s, MPlus (r, s) ->
        sup_seta
          ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
          (l_epsilon_strict (_A1, _A2, _A3) n phi_s r)
          (l_epsilon_strict (_A1, _A2, _A3) n phi_s s)
    | n, phi_s, MTimes (r, s) ->
        epsilon_lax (_A1, _A2, _A3) (l_epsilon_strict (_A1, _A2, _A3) n phi_s s)
          phi_s r
    | n, phi_s, MStar r -> unit_table (_A1, _A2) n;;

let rec update_matchF_base (_A1, _A2, _A3)
  n i mr mrs rels nt =
    (let x = mrtabulate (_A1, _A2) mrs (l_epsilon_strict (_A1, _A2, _A3) n rels)
       in
      ([(nt, (rels,
               (if memL i zero_nata
                 then lookupb (ccompare_mregex, equal_mregex)
                        ((ceq_list (ceq_option _A1)),
                          (ccompare_list (ccompare_option _A2)), set_impl_list)
                        x mr
                 else empty_table
                        ((ceq_list (ceq_option _A1)),
                          (ccompare_list (ccompare_option _A2)),
                          set_impl_list))))],
        x));;

let rec update_matchF
  n i mr mrs rels nt aux =
    fst (foldr
          (update_matchF_step
            (ceq_event_data, ccompare_event_data, equal_event_data) i mr mrs nt)
          aux (update_matchF_base
                (ceq_event_data, ccompare_event_data, equal_event_data) n i mr
                mrs rels nt));;

let rec simple_match
  n m x2 ux = match n, m, x2, ux with
    n, m, [], [] -> replicate (minus_nata n m) None
    | n, m, Var x :: ts, y :: ys ->
        (if less_nat m x
          then None :: simple_match n (suc m) (Var x :: ts) (y :: ys)
          else y :: simple_match n (suc m) ts ys)
    | uu, uv, Const vb :: va, ux -> []
    | uu, uv, Plus (vb, vc) :: va, ux -> []
    | uu, uv, Minus (vb, vc) :: va, ux -> []
    | uu, uv, UMinus vb :: va, ux -> []
    | uu, uv, Mult (vb, vc) :: va, ux -> []
    | uu, uv, Div (vb, vc) :: va, ux -> []
    | uu, uv, Mod (vb, vc) :: va, ux -> []
    | uu, uv, F2i vb :: va, ux -> []
    | uu, uv, I2f vb :: va, ux -> []
    | uu, uv, v :: va, [] -> []
    | uu, uv, [], v :: va -> [];;

let rec eval_matchF
  i mr nt x3 = match i, mr, nt, x3 with i, mr, nt, [] -> ([], [])
    | i, mr, nt, (t, (rels, rel)) :: aux ->
        (if not (memR i (minus_nata nt t))
          then (let a = eval_matchF i mr nt aux in
                let (xs, aa) = a in
                 (rel :: xs, aa))
          else ([], (t, (rels, rel)) :: aux));;

let rec meeval
  j n ts db x4 = match j, n, ts, db, x4 with
    j, n, ts, db, MTS mt ->
      (mapa (fun x -> eval_mtrm n mt (EInt (integer_of_nat x))) ts, MTS mt)
    | j, n, ts, db, MTP (mt, i) ->
        (mapa (fun x -> eval_mtrm n mt (EInt (integer_of_nat x))) (upt i j),
          MTP (mt, j))
    | j, n, ts, db, MMatchF (i, mr, mrs, phi_s, buf, nts, t, auxa) ->
        (let (xss, phi_sa) = map_split id (mapa (meeval j n ts db) phi_s) in
         let (aux, (bufa, (nt, ntsa))) =
           mebufnt_take (update_matchF n i mr mrs) auxa (mebufn_add xss buf) t
             (mbuf_t_append nts ts)
           in
         let (zs, auxb) = eval_matchF i mr nt aux in
          (zs, MMatchF (i, mr, mrs, phi_sa, bufa, ntsa, nt, auxb)))
    | j, n, ts, db, MMatchP (i, mr, mrs, phi_s, buf, nts, aux) ->
        (let (xss, phi_sa) = map_split id (mapa (meeval j n ts db) phi_s) in
         let a =
           mebufnt_take
             (fun rels t (zs, auxa) ->
               (let a = update_matchP n i mr mrs rels t auxa in
                let (z, aa) = a in
                 (mbuf_t_append zs [z], aa)))
             (mbuf_t_empty, aux) (mebufn_add xss buf) zero_nata
             (mbuf_t_append nts ts)
           in
         let (aa, b) = a in
          (let (zs, auxa) = aa in
            (fun (bufa, (_, ntsa)) ->
              (rep_mbuf_t zs, MMatchP (i, mr, mrs, phi_sa, bufa, ntsa, auxa))))
            b)
    | j, n, ts, db, MUntil (args, phi, psi, bufc, nts, t, auxc) ->
        (let (xs, phia) = meeval j (args_n args) ts db phi in
         let (ys, psia) = meeval j (args_n args) ts db psi in
         let (aux, (buf, (nt, ntsa))) =
           mebuf2t_take (add_new_mmauaux args) auxc (mebuf2_add xs ys bufc) t
             (mbuf_t_append nts ts)
           in
         let (zs, auxa) = eval_mmauaux args nt aux in
          (zs, MUntil (args, phia, psia, buf, ntsa, nt, auxa)))
    | j, n, ts, db, MSince (args, phi, psi, bufb, auxb) ->
        (let (xs, phia) = meeval j (args_n args) ts db phi in
         let (ys, psia) = meeval j (args_n args) ts db psi in
         let (zs, (buf, aux)) =
           meeval_since args [] (mebuf2S_add xs ys ts bufb) auxb in
          (zs, MSince (args, phia, psia, buf, aux)))
    | j, n, ts, db, MNext (i, phi, first, nts) ->
        (let (xs, phia) = meeval j n ts db phi in
         let (xsa, firsta) =
           (match (xs, first) with ([], b) -> ([], b)
             | (_ :: xsa, true) -> (xsa, false)
             | (x :: xsa, false) -> (x :: xsa, false))
           in
         let (zs, (_, ntsa)) =
           meprev_next i (mbuf_t_append mbuf_t_empty xsa) (mbuf_t_append nts ts)
           in
          (zs, MNext (i, phia, firsta, ntsa)))
    | j, n, ts, db, MPrev (i, phi, first, bufd, nts) ->
        (let (xs, phia) = meeval j n ts db phi in
          (if first && null ts
            then ([], MPrev (i, phia, true, mbuf_t_append bufd xs,
                              mbuf_t_append nts ts))
            else (let (zs, (buf, ntsa)) =
                    meprev_next i (mbuf_t_append bufd xs) (mbuf_t_append nts ts)
                    in
                   ((if first
                      then empty_table
                             ((ceq_list (ceq_option ceq_event_data)),
                               (ccompare_list
                                 (ccompare_option ccompare_event_data)),
                               set_impl_list) ::
                             zs
                      else zs),
                     MPrev (i, phia, false, buf, ntsa)))))
    | j, n, ts, db, MAgg (argsa, phi) ->
        (let (xs, phia) =
           meeval j (plus_nata (size_lista (aggargs_tys argsa)) n) ts db phi in
          (mapa (eval_aggargs argsa) xs, MAgg (argsa, phia)))
    | j, n, ts, db, MExists phi ->
        (let (xs, phia) = meeval j (suc n) ts db phi in
          (mapa (image
                  ((ceq_list (ceq_option ceq_event_data)),
                    (ccompare_list (ccompare_option ccompare_event_data)))
                  ((ceq_list (ceq_option ceq_event_data)),
                    (ccompare_list (ccompare_option ccompare_event_data)),
                    set_impl_list)
                  tla)
             xs,
            MExists phia))
    | j, n, ts, db, MNeg phi ->
        (let (xs, phia) = meeval j n ts db phi in
          (mapa (fun r ->
                  (if is_empty
                        (card_UNIV_list, (ceq_list (ceq_option ceq_event_data)),
                          (cproper_interval_list
                            (ccompare_option ccompare_event_data)))
                        r
                    then unit_table (ceq_event_data, ccompare_event_data) n
                    else empty_table
                           ((ceq_list (ceq_option ceq_event_data)),
                             (ccompare_list
                               (ccompare_option ccompare_event_data)),
                             set_impl_list)))
             xs,
            MNeg phia))
    | j, n, ts, db, MOr (phi, psi, bufc) ->
        (let (xs, phia) = meeval j n ts db phi in
         let (ys, psia) = meeval j n ts db psi in
         let (zs, buf) =
           mebuf2_take
             (sup_seta
               ((ceq_list (ceq_option ceq_event_data)),
                 (ccompare_list (ccompare_option ccompare_event_data))))
             (mebuf2_add xs ys bufc)
           in
          (zs, MOr (phia, psia, buf)))
    | j, n, ts, db, MAnds (a_pos, a_neg, l, buf) ->
        (let r = mapa (meeval j n ts db) l in
         let bufa = mebufn_add (mapa fst r) buf in
         let (zs, bufb) =
           mebufn_take
             (fun xs zs ->
               mbuf_t_append zs
                 [mmulti_join
                    (ceq_event_data, ccompare_event_data, equal_event_data) n
                    a_pos a_neg xs])
             mbuf_t_empty bufa
           in
          (rep_mbuf_t zs, MAnds (a_pos, a_neg, mapa snd r, bufb)))
    | j, n, ts, db, MAndRel (phi, confa) ->
        (let (xs, phia) = meeval j n ts db phi in
          (mapa (filter
                  ((ceq_list (ceq_option ceq_event_data)),
                    (ccompare_list (ccompare_option ccompare_event_data)))
                  (eval_constraint confa))
             xs,
            MAndRel (phia, confa)))
    | j, n, ts, db, MAndAssign (phi, conf) ->
        (let (xs, phia) = meeval j n ts db phi in
          (mapa (image
                  ((ceq_list (ceq_option ceq_event_data)),
                    (ccompare_list (ccompare_option ccompare_event_data)))
                  ((ceq_list (ceq_option ceq_event_data)),
                    (ccompare_list (ccompare_option ccompare_event_data)),
                    set_impl_list)
                  (eval_assignment conf))
             xs,
            MAndAssign (phia, conf)))
    | j, n, ts, db, MAnd (a_phi, phi, pos, a_psi, psi, bufc) ->
        (let (xs, phia) = meeval j n ts db phi in
         let (ys, psia) = meeval j n ts db psi in
         let (zs, buf) =
           mebuf2_take
             (fun r1 ->
               bin_join (ceq_event_data, ccompare_event_data, equal_event_data)
                 n a_phi r1 pos a_psi)
             (mebuf2_add xs ys bufc)
           in
          (zs, MAnd (a_phi, phia, pos, a_psi, psia, buf)))
    | j, n, ts, db, MLetPast (p, m, phi, psi, i, bufa) ->
        (let (xs, (ia, (buf, phia))) =
           letpast_meeval0
             ((ccompare_prod ccompare_string8 ccompare_nat),
               (equal_prod equal_string8 equal_nat))
             size_meformula (meeval j m) j i mbuf_t_empty (list_of_option bufa)
             (p, m) ts db phi
           in
         let (ys, psia) =
           meeval j n ts
             (updateb
               ((ccompare_prod ccompare_string8 ccompare_nat),
                 (equal_prod equal_string8 equal_nat))
               (p, m) (rep_mbuf_t xs) db)
             psi
           in
          (ys, MLetPast (p, m, phia, psia, ia, buf)))
    | j, n, ts, db, MLet (p, m, phi, psi) ->
        (let (xs, phia) = meeval j m ts db phi in
         let (ys, psia) =
           meeval j n ts
             (updateb
               ((ccompare_prod ccompare_string8 ccompare_nat),
                 (equal_prod equal_string8 equal_nat))
               (p, m) xs db)
             psi
           in
          (ys, MLet (p, m, phia, psia)))
    | lookahead, n, ts, db, MPred (e, tms, mode) ->
        ((match
           lookupa
             ((ccompare_prod ccompare_string8 ccompare_nat),
               (equal_prod equal_string8 equal_nat))
             db (e, size_lista tms)
           with None ->
             replicate (size_lista ts)
               (set_empty
                 ((ceq_list (ceq_option ceq_event_data)),
                   (ccompare_list (ccompare_option ccompare_event_data)))
                 (of_phantom set_impl_lista))
           | Some xs ->
             (match mode with Copy -> xs
               | Simple ->
                 mapa (image
                        ((ceq_list (ceq_option ceq_event_data)),
                          (ccompare_list (ccompare_option ccompare_event_data)))
                        ((ceq_list (ceq_option ceq_event_data)),
                          (ccompare_list (ccompare_option ccompare_event_data)),
                          set_impl_list)
                        (simple_match n zero_nata tms))
                   xs
               | Match ->
                 mapa (fun x ->
                        sup_setb
                          (finite_UNIV_list, cenum_list,
                            (ceq_list (ceq_option ceq_event_data)),
                            (cproper_interval_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list)
                          (image
                            ((ceq_list (ceq_option ceq_event_data)),
                              (ccompare_list
                                (ccompare_option ccompare_event_data)))
                            ((ceq_set
                               (cenum_list,
                                 (ceq_list (ceq_option ceq_event_data)),
                                 (cproper_interval_list
                                   (ccompare_option
                                     ccompare_event_data)).ccompare_cproper_interval)),
                              (ccompare_set
                                (finite_UNIV_list,
                                  (ceq_list (ceq_option ceq_event_data)),
                                  (cproper_interval_list
                                    (ccompare_option ccompare_event_data)),
                                  set_impl_list)),
                              set_impl_set)
                            (fun v ->
                              set_option
                                ((ceq_list (ceq_option ceq_event_data)),
                                  (ccompare_list
                                    (ccompare_option ccompare_event_data)),
                                  set_impl_list)
                                (map_option (fun f -> tabulate f zero_nata n)
                                  (matcha tms v)))
                            x))
                   xs)),
          MPred (e, tms, mode))
    | j, n, ts, db, MRel rel -> (replicate (size_lista ts) rel, MRel rel);;

let rec meval
  j n ts db (Rep_meformula phi) =
    (let (zs, phia) = meeval j n ts db phi in (zs, Rep_meformula phia));;

let rec init_mmuaux
  args =
    (zero_nata,
      (empty_queue,
        (empty_queue,
          (zero_nata,
            (join_mask (args_n args) (args_L args),
              (join_mask (args_n args) (args_R args),
                (set_empty
                   ((ceq_list (ceq_option ceq_event_data)),
                     (ccompare_list (ccompare_option ccompare_event_data)))
                   (of_phantom set_impl_lista),
                  (mapping_empty
                     (ccompare_list (ccompare_option ccompare_event_data))
                     (of_phantom mapping_impl_lista),
                    (updateb (ccompare_nat, equal_nat) zero_nata
                       (mapping_empty
                         (ccompare_list (ccompare_option ccompare_event_data))
                         (of_phantom mapping_impl_lista))
                       (mapping_empty ccompare_nat
                         (of_phantom mapping_impl_nata)),
                      (mapping_empty ccompare_nat
                         (of_phantom mapping_impl_nata),
                        []))))))))));;

let rec init_mmauaux
  args =
    (init_mmuaux args,
      (match args_agg args with None -> None | Some a -> init_maggauxa a));;

let rec init_mmsaux (_A1, _A2)
  args =
    (zero_nata,
      (zero_nata,
        (join_mask (args_n args) (args_L args),
          (join_mask (args_n args) (args_R args),
            (empty_queue,
              (empty_queue,
                (set_empty
                   ((ceq_list (ceq_option _A1)),
                     (ccompare_list (ccompare_option _A2)))
                   (of_phantom set_impl_lista),
                  (Wf_table_of_idx
                     (wf_idx_of_set (_A1, _A2) (args_n args) (args_R args)
                       (args_L args)
                       (set_empty
                         ((ceq_list (ceq_option _A1)),
                           (ccompare_list (ccompare_option _A2)))
                         (of_phantom set_impl_lista))),
                    (mapping_empty (ccompare_list (ccompare_option _A2))
                       (of_phantom mapping_impl_lista),
                      (wf_table_of_set_args (_A1, _A2) args
                         (set_empty
                           ((ceq_list (ceq_option _A1)),
                             (ccompare_list (ccompare_option _A2)))
                           (of_phantom set_impl_lista)),
                        mapping_empty (ccompare_list (ccompare_option _A2))
                          (of_phantom mapping_impl_lista)))))))))));;

let rec init_mmasaux
  args =
    (match args_agg args
      with None ->
        (init_mmsaux (ceq_event_data, ccompare_event_data) args, None)
      | Some aggargs ->
        (init_mmsaux (ceq_event_data, ccompare_event_data) args,
          init_maggauxa aggargs));;

let rec split_constraint
  = function Eq (t1, t2) -> (t1, (true, (MEq, t2)))
    | Less (t1, t2) -> (t1, (true, (MLess, t2)))
    | LessEq (t1, t2) -> (t1, (true, (MLessEq, t2)))
    | Neg (Eq (t1, t2)) -> (t1, (false, (MEq, t2)))
    | Neg (Less (t1, t2)) -> (t1, (false, (MLess, t2)))
    | Neg (LessEq (t1, t2)) -> (t1, (false, (MLessEq, t2)))
    | Pred (v, va) -> failwith "undefined"
    | Let (v, va, vb) -> failwith "undefined"
    | LetPast (v, va, vb) -> failwith "undefined"
    | Neg (Pred (va, vb)) -> failwith "undefined"
    | Neg (Let (va, vb, vc)) -> failwith "undefined"
    | Neg (LetPast (va, vb, vc)) -> failwith "undefined"
    | Neg (Neg va) -> failwith "undefined"
    | Neg (Or (va, vb)) -> failwith "undefined"
    | Neg (And (va, vb)) -> failwith "undefined"
    | Neg (Ands va) -> failwith "undefined"
    | Neg (Exists (va, vb)) -> failwith "undefined"
    | Neg (Agg (va, vb, vc, vd, ve)) -> failwith "undefined"
    | Neg (Prev (va, vb)) -> failwith "undefined"
    | Neg (Next (va, vb)) -> failwith "undefined"
    | Neg (Since (va, vb, vc)) -> failwith "undefined"
    | Neg (Until (va, vb, vc)) -> failwith "undefined"
    | Neg (MatchF (va, vb)) -> failwith "undefined"
    | Neg (MatchP (va, vb)) -> failwith "undefined"
    | Neg (TP va) -> failwith "undefined"
    | Neg (TS va) -> failwith "undefined"
    | Or (v, va) -> failwith "undefined"
    | And (v, va) -> failwith "undefined"
    | Ands v -> failwith "undefined"
    | Exists (v, va) -> failwith "undefined"
    | Agg (v, va, vb, vc, vd) -> failwith "undefined"
    | Prev (v, va) -> failwith "undefined"
    | Next (v, va) -> failwith "undefined"
    | Since (v, va, vb) -> failwith "undefined"
    | Until (v, va, vb) -> failwith "undefined"
    | MatchF (v, va) -> failwith "undefined"
    | MatchP (v, va) -> failwith "undefined"
    | TP v -> failwith "undefined"
    | TS v -> failwith "undefined";;

let rec split_assignment
  x xa1 = match x, xa1 with
    x, Eq (t1, t2) ->
      (let (xa, xaa) = (t1, t2) in
        (match xa
          with Var xab ->
            (match xaa
              with Var y ->
                (if member (ceq_nat, ccompare_nat) xab x then (y, t1)
                  else (xab, t2))
              | Const _ -> (xab, t2) | Plus (_, _) -> (xab, t2)
              | Minus (_, _) -> (xab, t2) | UMinus _ -> (xab, t2)
              | Mult (_, _) -> (xab, t2) | Div (_, _) -> (xab, t2)
              | Mod (_, _) -> (xab, t2) | F2i _ -> (xab, t2)
              | I2f _ -> (xab, t2))
          | Const _ -> (let Var y = xaa in (y, t1))
          | Plus (_, _) -> (let Var y = xaa in (y, t1))
          | Minus (_, _) -> (let Var y = xaa in (y, t1))
          | UMinus _ -> (let Var y = xaa in (y, t1))
          | Mult (_, _) -> (let Var y = xaa in (y, t1))
          | Div (_, _) -> (let Var y = xaa in (y, t1))
          | Mod (_, _) -> (let Var y = xaa in (y, t1))
          | F2i _ -> (let Var y = xaa in (y, t1))
          | I2f _ -> (let Var y = xaa in (y, t1))))
    | uu, Pred (v, va) -> failwith "undefined"
    | uu, Let (v, va, vb) -> failwith "undefined"
    | uu, LetPast (v, va, vb) -> failwith "undefined"
    | uu, Less (v, va) -> failwith "undefined"
    | uu, LessEq (v, va) -> failwith "undefined"
    | uu, Neg v -> failwith "undefined"
    | uu, Or (v, va) -> failwith "undefined"
    | uu, And (v, va) -> failwith "undefined"
    | uu, Ands v -> failwith "undefined"
    | uu, Exists (v, va) -> failwith "undefined"
    | uu, Agg (v, va, vb, vc, vd) -> failwith "undefined"
    | uu, Prev (v, va) -> failwith "undefined"
    | uu, Next (v, va) -> failwith "undefined"
    | uu, Since (v, va, vb) -> failwith "undefined"
    | uu, Until (v, va, vb) -> failwith "undefined"
    | uu, MatchF (v, va) -> failwith "undefined"
    | uu, MatchP (v, va) -> failwith "undefined"
    | uu, TP v -> failwith "undefined"
    | uu, TS v -> failwith "undefined";;

let rec is_simple_pattern
  x0 uu = match x0, uu with [], uu -> true
    | Var y :: ts, x -> less_eq_nat x y && is_simple_pattern ts (suc y)
    | Const vb :: va, uw -> false
    | Plus (vb, vc) :: va, uw -> false
    | Minus (vb, vc) :: va, uw -> false
    | UMinus vb :: va, uw -> false
    | Mult (vb, vc) :: va, uw -> false
    | Div (vb, vc) :: va, uw -> false
    | Mod (vb, vc) :: va, uw -> false
    | F2i vb :: va, uw -> false
    | I2f vb :: va, uw -> false;;

let rec is_copy_pattern
  n ts = equal_lista equal_trm ts (mapa (fun a -> Var a) (upt zero_nata n));;

let rec pred_mode_of
  n ts =
    (if is_copy_pattern n ts then Copy
      else (if is_simple_pattern ts zero_nata then Simple else Match));;

let rec init_aggargs
  cols n g0 y omega tys f = Aggargs_ext (cols, n, g0, y, omega, tys, f, ());;

let rec mtrm_of_trm = function Var x -> MVar x
                      | Const x -> MConst x
                      | Plus (v, va) -> failwith "undefined"
                      | Minus (v, va) -> failwith "undefined"
                      | UMinus v -> failwith "undefined"
                      | Mult (v, va) -> failwith "undefined"
                      | Div (v, va) -> failwith "undefined"
                      | Mod (v, va) -> failwith "undefined"
                      | F2i v -> failwith "undefined"
                      | I2f v -> failwith "undefined";;

let rec meinit0
  n x1 = match n, x1 with
    n, Neg phi ->
      (if is_empty (card_UNIV_nat, ceq_nat, cproper_interval_nat)
            (fvi zero_nata phi)
        then MNeg (meinit0 n phi)
        else MRel (empty_table
                    ((ceq_list (ceq_option ceq_event_data)),
                      (ccompare_list (ccompare_option ccompare_event_data)),
                      set_impl_list)))
    | n, Eq (t1, t2) -> MRel (eq_rel n t1 t2)
    | n, Pred (e, ts) -> MPred (e, ts, pred_mode_of n ts)
    | n, Let (p, phi, psi) ->
        MLet (p, nfv phi, meinit0 (nfv phi) phi, meinit0 n psi)
    | n, LetPast (p, phi, psi) ->
        MLetPast
          (p, nfv phi, meinit0 (nfv phi) phi, meinit0 n psi, zero_nata, None)
    | n, Or (phi, psi) ->
        MOr (meinit0 n phi, meinit0 n psi, (mbuf_t_empty, mbuf_t_empty))
    | n, And (phi, psi) ->
        (if safe_assignment (fvi zero_nata phi) psi
          then MAndAssign
                 (meinit0 n phi, split_assignment (fvi zero_nata phi) psi)
          else (if safe_formula psi
                 then MAnd (fvi zero_nata phi, meinit0 n phi, true,
                             fvi zero_nata psi, meinit0 n psi,
                             (mbuf_t_empty, mbuf_t_empty))
                 else (if is_constraint psi
                        then MAndRel (meinit0 n phi, split_constraint psi)
                        else (match psi
                               with Pred (_, _) ->
                                 MRel (empty_table
((ceq_list (ceq_option ceq_event_data)),
  (ccompare_list (ccompare_option ccompare_event_data)), set_impl_list))
                               | Let (_, _, _) ->
                                 MRel (empty_table
((ceq_list (ceq_option ceq_event_data)),
  (ccompare_list (ccompare_option ccompare_event_data)), set_impl_list))
                               | LetPast (_, _, _) ->
                                 MRel (empty_table
((ceq_list (ceq_option ceq_event_data)),
  (ccompare_list (ccompare_option ccompare_event_data)), set_impl_list))
                               | Eq (_, _) ->
                                 MRel (empty_table
((ceq_list (ceq_option ceq_event_data)),
  (ccompare_list (ccompare_option ccompare_event_data)), set_impl_list))
                               | Less (_, _) ->
                                 MRel (empty_table
((ceq_list (ceq_option ceq_event_data)),
  (ccompare_list (ccompare_option ccompare_event_data)), set_impl_list))
                               | LessEq (_, _) ->
                                 MRel (empty_table
((ceq_list (ceq_option ceq_event_data)),
  (ccompare_list (ccompare_option ccompare_event_data)), set_impl_list))
                               | Neg psia ->
                                 MAnd (fvi zero_nata phi, meinit0 n phi, false,
fvi zero_nata psia, meinit0 n psia, (mbuf_t_empty, mbuf_t_empty))
                               | Or (_, _) ->
                                 MRel (empty_table
((ceq_list (ceq_option ceq_event_data)),
  (ccompare_list (ccompare_option ccompare_event_data)), set_impl_list))
                               | And (_, _) ->
                                 MRel (empty_table
((ceq_list (ceq_option ceq_event_data)),
  (ccompare_list (ccompare_option ccompare_event_data)), set_impl_list))
                               | Ands _ ->
                                 MRel (empty_table
((ceq_list (ceq_option ceq_event_data)),
  (ccompare_list (ccompare_option ccompare_event_data)), set_impl_list))
                               | Exists (_, _) ->
                                 MRel (empty_table
((ceq_list (ceq_option ceq_event_data)),
  (ccompare_list (ccompare_option ccompare_event_data)), set_impl_list))
                               | Agg (_, _, _, _, _) ->
                                 MRel (empty_table
((ceq_list (ceq_option ceq_event_data)),
  (ccompare_list (ccompare_option ccompare_event_data)), set_impl_list))
                               | Prev (_, _) ->
                                 MRel (empty_table
((ceq_list (ceq_option ceq_event_data)),
  (ccompare_list (ccompare_option ccompare_event_data)), set_impl_list))
                               | Next (_, _) ->
                                 MRel (empty_table
((ceq_list (ceq_option ceq_event_data)),
  (ccompare_list (ccompare_option ccompare_event_data)), set_impl_list))
                               | Since (_, _, _) ->
                                 MRel (empty_table
((ceq_list (ceq_option ceq_event_data)),
  (ccompare_list (ccompare_option ccompare_event_data)), set_impl_list))
                               | Until (_, _, _) ->
                                 MRel (empty_table
((ceq_list (ceq_option ceq_event_data)),
  (ccompare_list (ccompare_option ccompare_event_data)), set_impl_list))
                               | MatchF (_, _) ->
                                 MRel (empty_table
((ceq_list (ceq_option ceq_event_data)),
  (ccompare_list (ccompare_option ccompare_event_data)), set_impl_list))
                               | MatchP (_, _) ->
                                 MRel (empty_table
((ceq_list (ceq_option ceq_event_data)),
  (ccompare_list (ccompare_option ccompare_event_data)), set_impl_list))
                               | TP _ ->
                                 MRel (empty_table
((ceq_list (ceq_option ceq_event_data)),
  (ccompare_list (ccompare_option ccompare_event_data)), set_impl_list))
                               | TS _ ->
                                 MRel (empty_table
((ceq_list (ceq_option ceq_event_data)),
  (ccompare_list (ccompare_option ccompare_event_data)), set_impl_list))))))
    | n, Ands l ->
        (let (pos, neg) = partition safe_formula l in
         let mpos = mapa (meinit0 n) pos in
         let mneg = mapa (meinit0 n) (mapa remove_neg neg) in
         let vpos = mapa (fvi zero_nata) pos in
         let vneg = mapa (fvi zero_nata) neg in
          MAnds (vpos, vneg, mpos @ mneg,
                  replicate (size_lista l) mbuf_t_empty))
    | n, Exists (t, phi) -> MExists (meinit0 (suc n) phi)
    | n, Agg (y, omega, tys, f, phi) ->
        (let default =
           MAgg (init_aggargs (fvi zero_nata phi) n
                   (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
                     (fvi zero_nata phi)
                     (set (ceq_nat, ccompare_nat, set_impl_nat)
                       (upt zero_nata (size_lista tys))))
                   y omega tys f,
                  meinit0 (plus_nata (size_lista tys) n) phi)
           in
          (match phi with Pred (_, _) -> default | Let (_, _, _) -> default
            | LetPast (_, _, _) -> default | Eq (_, _) -> default
            | Less (_, _) -> default | LessEq (_, _) -> default
            | Neg _ -> default | Or (_, _) -> default | And (_, _) -> default
            | Ands _ -> default | Exists (_, _) -> default
            | Agg (_, _, _, _, _) -> default | Prev (_, _) -> default
            | Next (_, _) -> default
            | Since (phia, i, psi) ->
              (let agg =
                 Some (init_aggargs (fvi zero_nata phi) n
                        (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
                          (fvi zero_nata phi)
                          (set (ceq_nat, ccompare_nat, set_impl_nat)
                            (upt zero_nata (size_lista tys))))
                        y omega tys f)
                 in
               let args =
                 (fun k ->
                   init_args i (plus_nata (size_lista tys) n)
                     (fvi zero_nata phia) (fvi zero_nata psi) k agg)
                 in
                (if safe_formula phia
                  then MSince
                         (args true,
                           meinit0 (plus_nata (size_lista tys) n) phia,
                           meinit0 (plus_nata (size_lista tys) n) psi,
                           (mbuf_t_empty,
                             (mbuf_t_empty, (mbuf_t_empty, false))),
                           init_mmasaux (args true))
                  else (match phia
                         with Pred (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Let (_, _, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | LetPast (_, _, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Eq (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Less (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | LessEq (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Neg phib ->
                           MSince
                             (args false,
                               meinit0 (plus_nata (size_lista tys) n) phib,
                               meinit0 (plus_nata (size_lista tys) n) psi,
                               (mbuf_t_empty,
                                 (mbuf_t_empty, (mbuf_t_empty, false))),
                               init_mmasaux (args false))
                         | Or (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | And (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Ands _ ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Exists (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Agg (_, _, _, _, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Prev (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Next (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Since (_, _, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Until (_, _, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | MatchF (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | MatchP (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | TP _ ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | TS _ ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list)))))
            | Until (phia, i, psi) ->
              (let agg =
                 Some (init_aggargs (fvi zero_nata phi) n
                        (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
                          (fvi zero_nata phi)
                          (set (ceq_nat, ccompare_nat, set_impl_nat)
                            (upt zero_nata (size_lista tys))))
                        y omega tys f)
                 in
               let args =
                 (fun k ->
                   init_args i (plus_nata (size_lista tys) n)
                     (fvi zero_nata phia) (fvi zero_nata psi) k agg)
                 in
                (if safe_formula phia
                  then MUntil
                         (args true,
                           meinit0 (plus_nata (size_lista tys) n) phia,
                           meinit0 (plus_nata (size_lista tys) n) psi,
                           (mbuf_t_empty, mbuf_t_empty), mbuf_t_empty,
                           zero_nata, init_mmauaux (args true))
                  else (match phia
                         with Pred (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Let (_, _, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | LetPast (_, _, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Eq (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Less (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | LessEq (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Neg phib ->
                           MUntil
                             (args false,
                               meinit0 (plus_nata (size_lista tys) n) phib,
                               meinit0 (plus_nata (size_lista tys) n) psi,
                               (mbuf_t_empty, mbuf_t_empty), mbuf_t_empty,
                               zero_nata, init_mmauaux (args false))
                         | Or (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | And (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Ands _ ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Exists (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Agg (_, _, _, _, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Prev (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Next (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Since (_, _, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | Until (_, _, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | MatchF (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | MatchP (_, _) ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | TP _ ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list))
                         | TS _ ->
                           MRel (empty_table
                                  ((ceq_list (ceq_option ceq_event_data)),
                                    (ccompare_list
                                      (ccompare_option ccompare_event_data)),
                                    set_impl_list)))))
            | MatchF (_, _) -> default | MatchP (_, _) -> default
            | TP _ -> default | TS _ -> default))
    | n, Prev (i, phi) ->
        MPrev (i, meinit0 n phi, true, mbuf_t_empty, mbuf_t_empty)
    | n, Next (i, phi) -> MNext (i, meinit0 n phi, true, mbuf_t_empty)
    | n, Since (phi, i, psi) ->
        (if safe_formula phi
          then MSince
                 (init_args i n (fvi zero_nata phi) (fvi zero_nata psi) true
                    None,
                   meinit0 n phi, meinit0 n psi,
                   (mbuf_t_empty, (mbuf_t_empty, (mbuf_t_empty, false))),
                   init_mmasaux
                     (init_args i n (fvi zero_nata phi) (fvi zero_nata psi) true
                       None))
          else (match phi
                 with Pred (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Let (_, _, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | LetPast (_, _, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Eq (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Less (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | LessEq (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Neg phia ->
                   MSince
                     (init_args i n (fvi zero_nata phi) (fvi zero_nata psi)
                        false None,
                       meinit0 n phia, meinit0 n psi,
                       (mbuf_t_empty, (mbuf_t_empty, (mbuf_t_empty, false))),
                       init_mmasaux
                         (init_args i n (fvi zero_nata phi) (fvi zero_nata psi)
                           false None))
                 | Or (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | And (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Ands _ ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Exists (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Agg (_, _, _, _, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Prev (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Next (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Since (_, _, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Until (_, _, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | MatchF (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | MatchP (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | TP _ ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | TS _ ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))))
    | n, Until (phi, i, psi) ->
        (if safe_formula phi
          then MUntil
                 (init_args i n (fvi zero_nata phi) (fvi zero_nata psi) true
                    None,
                   meinit0 n phi, meinit0 n psi, (mbuf_t_empty, mbuf_t_empty),
                   mbuf_t_empty, zero_nata,
                   init_mmauaux
                     (init_args i n (fvi zero_nata phi) (fvi zero_nata psi) true
                       None))
          else (match phi
                 with Pred (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Let (_, _, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | LetPast (_, _, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Eq (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Less (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | LessEq (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Neg phia ->
                   MUntil
                     (init_args i n (fvi zero_nata phi) (fvi zero_nata psi)
                        false None,
                       meinit0 n phia, meinit0 n psi,
                       (mbuf_t_empty, mbuf_t_empty), mbuf_t_empty, zero_nata,
                       init_mmauaux
                         (init_args i n (fvi zero_nata phi) (fvi zero_nata psi)
                           false None))
                 | Or (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | And (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Ands _ ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Exists (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Agg (_, _, _, _, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Prev (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Next (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Since (_, _, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | Until (_, _, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | MatchF (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | MatchP (_, _) ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | TP _ ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))
                 | TS _ ->
                   MRel (empty_table
                          ((ceq_list (ceq_option ceq_event_data)),
                            (ccompare_list
                              (ccompare_option ccompare_event_data)),
                            set_impl_list))))
    | n, MatchP (i, r) ->
        (let (mr, phi_s) = to_mregex r in
          MMatchP
            (i, mr,
              sorted_list_of_set
                (ceq_mregex, ccompare_mregex, equal_mregex, linorder_mregex)
                (rPDs mr),
              mapa (meinit0 n) phi_s, replicate (size_lista phi_s) mbuf_t_empty,
              mbuf_t_empty, []))
    | n, MatchF (i, r) ->
        (let (mr, phi_s) = to_mregex r in
          MMatchF
            (i, mr,
              sorted_list_of_set
                (ceq_mregex, ccompare_mregex, equal_mregex, linorder_mregex)
                (lPDs mr),
              mapa (meinit0 n) phi_s, replicate (size_lista phi_s) mbuf_t_empty,
              mbuf_t_empty, zero_nata, []))
    | n, TP t -> MTP (mtrm_of_trm t, zero_nata)
    | n, TS t -> MTS (mtrm_of_trm t)
    | n, Less (v, va) ->
        MRel (empty_table
               ((ceq_list (ceq_option ceq_event_data)),
                 (ccompare_list (ccompare_option ccompare_event_data)),
                 set_impl_list))
    | n, LessEq (v, va) ->
        MRel (empty_table
               ((ceq_list (ceq_option ceq_event_data)),
                 (ccompare_list (ccompare_option ccompare_event_data)),
                 set_impl_list));;

let rec minit0 n phi = Rep_meformula (meinit0 n phi);;

let rec minit
  phi = (let n = nfv phi in
          Mestate (zero_nata, zero_nata, minit0 n phi, n, empty_queue, ()));;

let rec annotate_verdicts
  i tq x2 acc = match i, tq, x2, acc with i, tq, [], acc -> (i, (tq, rev acc))
    | i, tq, v :: vs, acc ->
        (match pop tq
          with (None, tqa) ->
            (plus_nata (plus_nata i one_nata) (size_lista vs),
              (funpow (plus_nata one_nata (size_lista vs)) tl_queue tqa,
                rev acc))
          | (Some t, tqa) ->
            annotate_verdicts (plus_nata i one_nata) tqa vs
              ((i, (t, v)) :: acc));;

let rec mstep
  (db, t) (Mestate (i, j, m, n, tq, zeta)) =
    (let (vs, ma) = meval (plus_nata j one_nata) n [t] db m in
     let (ia, (ts, vsa)) = annotate_verdicts i (append_queue t tq) vs [] in
      (vsa, Mestate (ia, plus_nata j one_nata, ma, n, ts, zeta)));;

let rec get_and_list = function Ands l -> (if null l then [Ands l] else l)
                       | Pred (v, va) -> [Pred (v, va)]
                       | Let (v, va, vb) -> [Let (v, va, vb)]
                       | LetPast (v, va, vb) -> [LetPast (v, va, vb)]
                       | Eq (v, va) -> [Eq (v, va)]
                       | Less (v, va) -> [Less (v, va)]
                       | LessEq (v, va) -> [LessEq (v, va)]
                       | Neg v -> [Neg v]
                       | Or (v, va) -> [Or (v, va)]
                       | And (v, va) -> [And (v, va)]
                       | Exists (v, va) -> [Exists (v, va)]
                       | Agg (v, va, vb, vc, vd) -> [Agg (v, va, vb, vc, vd)]
                       | Prev (v, va) -> [Prev (v, va)]
                       | Next (v, va) -> [Next (v, va)]
                       | Since (v, va, vb) -> [Since (v, va, vb)]
                       | Until (v, va, vb) -> [Until (v, va, vb)]
                       | MatchF (v, va) -> [MatchF (v, va)]
                       | MatchP (v, va) -> [MatchP (v, va)]
                       | TP v -> [TP v]
                       | TS v -> [TS v];;

let rec is_simple_eq
  t1 t2 =
    is_Const t1 && (is_Const t2 || is_Var t2) || is_Var t1 && is_Const t2;;

let rec mapping_impl_choose2
  x y = match x, y with Mapping_RBT, Mapping_RBT -> Mapping_RBT
    | Mapping_Assoc_List, Mapping_Assoc_List -> Mapping_Assoc_List
    | Mapping_Mapping, Mapping_Mapping -> Mapping_Mapping
    | x, y -> Mapping_Choose;;

let rec mapping_impl_prod _A _B
  = Phantom
      (mapping_impl_choose2 (of_phantom (mapping_impl _A))
        (of_phantom (mapping_impl _B)));;

let empty_db : ((string * nat), (((event_data option) list) set list)) mapping
  = mapping_empty (ccompare_prod ccompare_string8 ccompare_nat)
      (of_phantom (mapping_impl_prod mapping_impl_string8 mapping_impl_nat));;

let rec rbt_fold
  x = foldb (ccompare_list (ccompare_option ccompare_event_data)) x;;

let rec mmonitorable_exec
  = function Eq (t1, t2) -> is_simple_eq t1 t2
    | Pred (e, ts) -> list_all (fun t -> is_Var t || is_Const t) ts
    | Let (p, phi, psi) ->
        less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
          (set (ceq_nat, ccompare_nat, set_impl_nat) (upt zero_nata (nfv phi)))
          (fvi zero_nata phi) &&
          (mmonitorable_exec phi && mmonitorable_exec psi)
    | LetPast (p, phi, psi) ->
        less_eq_rec_safety (safe_letpast (p, nfv phi) phi) PastRec &&
          (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
             (set (ceq_nat, ccompare_nat, set_impl_nat)
               (upt zero_nata (nfv phi)))
             (fvi zero_nata phi) &&
            (mmonitorable_exec phi && mmonitorable_exec psi))
    | Neg phi ->
        is_empty (card_UNIV_nat, ceq_nat, cproper_interval_nat)
          (fvi zero_nata phi) &&
          mmonitorable_exec phi
    | Or (phi, psi) ->
        set_eq (cenum_nat, ceq_nat, ccompare_nat) (fvi zero_nata phi)
          (fvi zero_nata psi) &&
          (mmonitorable_exec phi && mmonitorable_exec psi)
    | And (phi, psi) ->
        mmonitorable_exec phi &&
          (safe_assignment (fvi zero_nata phi) psi ||
            (mmonitorable_exec psi ||
              less_eq_set (cenum_nat, ceq_nat, ccompare_nat) (fvi zero_nata psi)
                (fvi zero_nata phi) &&
                (is_constraint psi ||
                  (match psi with Pred (_, _) -> false | Let (_, _, _) -> false
                    | LetPast (_, _, _) -> false | Eq (_, _) -> false
                    | Less (_, _) -> false | LessEq (_, _) -> false
                    | Neg a -> mmonitorable_exec a | Or (_, _) -> false
                    | And (_, _) -> false | Ands _ -> false
                    | Exists (_, _) -> false | Agg (_, _, _, _, _) -> false
                    | Prev (_, _) -> false | Next (_, _) -> false
                    | Since (_, _, _) -> false | Until (_, _, _) -> false
                    | MatchF (_, _) -> false | MatchP (_, _) -> false
                    | TP _ -> false | TS _ -> false))))
    | Ands l ->
        (let (pos, neg) = partition mmonitorable_exec l in
          not (null pos) &&
            (list_all mmonitorable_exec (mapa remove_neg neg) &&
              less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
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
                    (mapa (fvi zero_nata) neg)))
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
                    (mapa (fvi zero_nata) pos)))))
    | Exists (t, phi) ->
        member (ceq_nat, ccompare_nat) zero_nata (fvi zero_nata phi) &&
          mmonitorable_exec phi
    | Agg (y, omega, tys, f, phi) ->
        mmonitorable_exec phi &&
          (not (member (ceq_nat, ccompare_nat) (plus_nata y (size_lista tys))
                 (fvi zero_nata phi)) &&
            (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
               (set (ceq_nat, ccompare_nat, set_impl_nat)
                 (upt zero_nata (size_lista tys)))
               (fvi zero_nata phi) &&
              less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
                (fvi_trm zero_nata f) (fvi zero_nata phi)))
    | Prev (i, phi) -> mmonitorable_exec phi
    | Next (i, phi) -> mmonitorable_exec phi
    | Since (phi, i, psi) ->
        less_eq_set (cenum_nat, ceq_nat, ccompare_nat) (fvi zero_nata phi)
          (fvi zero_nata psi) &&
          ((mmonitorable_exec phi ||
             (match phi with Pred (_, _) -> false | Let (_, _, _) -> false
               | LetPast (_, _, _) -> false | Eq (_, _) -> false
               | Less (_, _) -> false | LessEq (_, _) -> false
               | Neg a -> mmonitorable_exec a | Or (_, _) -> false
               | And (_, _) -> false | Ands _ -> false | Exists (_, _) -> false
               | Agg (_, _, _, _, _) -> false | Prev (_, _) -> false
               | Next (_, _) -> false | Since (_, _, _) -> false
               | Until (_, _, _) -> false | MatchF (_, _) -> false
               | MatchP (_, _) -> false | TP _ -> false | TS _ -> false)) &&
            mmonitorable_exec psi)
    | Until (phi, i, psi) ->
        less_eq_set (cenum_nat, ceq_nat, ccompare_nat) (fvi zero_nata phi)
          (fvi zero_nata psi) &&
          (bounded i &&
            ((mmonitorable_exec phi ||
               (match phi with Pred (_, _) -> false | Let (_, _, _) -> false
                 | LetPast (_, _, _) -> false | Eq (_, _) -> false
                 | Less (_, _) -> false | LessEq (_, _) -> false
                 | Neg a -> mmonitorable_exec a | Or (_, _) -> false
                 | And (_, _) -> false | Ands _ -> false
                 | Exists (_, _) -> false | Agg (_, _, _, _, _) -> false
                 | Prev (_, _) -> false | Next (_, _) -> false
                 | Since (_, _, _) -> false | Until (_, _, _) -> false
                 | MatchF (_, _) -> false | MatchP (_, _) -> false
                 | TP _ -> false | TS _ -> false)) &&
              mmonitorable_exec psi))
    | MatchP (i, r) ->
        safe_regex
          (card_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
            set_impl_nat)
          (fvi zero_nata)
          (fun g phi ->
            mmonitorable_exec phi ||
              equal_safety g Lax &&
                (match phi with Pred (_, _) -> false | Let (_, _, _) -> false
                  | LetPast (_, _, _) -> false | Eq (_, _) -> false
                  | Less (_, _) -> false | LessEq (_, _) -> false
                  | Neg a -> mmonitorable_exec a | Or (_, _) -> false
                  | And (_, _) -> false | Ands _ -> false
                  | Exists (_, _) -> false | Agg (_, _, _, _, _) -> false
                  | Prev (_, _) -> false | Next (_, _) -> false
                  | Since (_, _, _) -> false | Until (_, _, _) -> false
                  | MatchF (_, _) -> false | MatchP (_, _) -> false
                  | TP _ -> false | TS _ -> false))
          Past Strict r
    | MatchF (i, r) ->
        safe_regex
          (card_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
            set_impl_nat)
          (fvi zero_nata)
          (fun g phi ->
            mmonitorable_exec phi ||
              equal_safety g Lax &&
                (match phi with Pred (_, _) -> false | Let (_, _, _) -> false
                  | LetPast (_, _, _) -> false | Eq (_, _) -> false
                  | Less (_, _) -> false | LessEq (_, _) -> false
                  | Neg a -> mmonitorable_exec a | Or (_, _) -> false
                  | And (_, _) -> false | Ands _ -> false
                  | Exists (_, _) -> false | Agg (_, _, _, _, _) -> false
                  | Prev (_, _) -> false | Next (_, _) -> false
                  | Since (_, _, _) -> false | Until (_, _, _) -> false
                  | MatchF (_, _) -> false | MatchP (_, _) -> false
                  | TP _ -> false | TS _ -> false))
          Futu Strict r &&
          bounded i
    | TP t -> is_Var t || is_Const t
    | TS t -> is_Var t || is_Const t
    | Less (v, va) -> false
    | LessEq (v, va) -> false;;

let rec minit_safe
  phi = (if mmonitorable_exec phi then minit phi else failwith "undefined");;

let rec convert_multiway
  = function Pred (p, ts) -> Pred (p, ts)
    | Eq (t, u) -> Eq (t, u)
    | Less (t, u) -> Less (t, u)
    | LessEq (t, u) -> LessEq (t, u)
    | Let (p, phi, psi) -> Let (p, convert_multiway phi, convert_multiway psi)
    | LetPast (p, phi, psi) ->
        LetPast (p, convert_multiway phi, convert_multiway psi)
    | Neg phi -> Neg (convert_multiway phi)
    | Or (phi, psi) -> Or (convert_multiway phi, convert_multiway psi)
    | And (phi, psi) ->
        (if safe_assignment (fvi zero_nata phi) psi
          then And (convert_multiway phi, psi)
          else (if safe_formula psi
                 then Ands (get_and_list (convert_multiway phi) @
                             get_and_list (convert_multiway psi))
                 else (if is_constraint psi then And (convert_multiway phi, psi)
                        else Ands (convert_multiway psi ::
                                    get_and_list (convert_multiway phi)))))
    | Ands phi_s -> Ands (mapa convert_multiway phi_s)
    | Exists (t, phi) -> Exists (t, convert_multiway phi)
    | Agg (y, omega, b, f, phi) -> Agg (y, omega, b, f, convert_multiway phi)
    | Prev (i, phi) -> Prev (i, convert_multiway phi)
    | Next (i, phi) -> Next (i, convert_multiway phi)
    | Since (phi, i, psi) ->
        Since (convert_multiway phi, i, convert_multiway psi)
    | Until (phi, i, psi) ->
        Until (convert_multiway phi, i, convert_multiway psi)
    | MatchP (i, r) -> MatchP (i, map_regex convert_multiway r)
    | MatchF (i, r) -> MatchF (i, map_regex convert_multiway r)
    | TP t -> TP t
    | TS t -> TS t;;

let rec mapping_rbt_insertwk _A
  xc xd xe xf =
    Mapping_RBTa
      (rbt_comp_insert_with_key (the (ccompare _A)) xc xd xe (impl_ofa _A xf));;

let rec update_mapping_with _A
  f k v (RBT_Mapping t) =
    (match ccompare _A
      with None ->
        failwith "update_mapping_with RBT_Mapping: ccompare = None"
          (fun _ -> update_mapping_with _A f k v (RBT_Mapping t))
      | Some _ -> RBT_Mapping (mapping_rbt_insertwk _A f k v t));;

let rec insert_into_db
  p xs db =
    update_mapping_with (ccompare_prod ccompare_string8 ccompare_nat)
      (fun _ tbl _ ->
        mapa (insert
               ((ceq_list (ceq_option ceq_event_data)),
                 (ccompare_list (ccompare_option ccompare_event_data)))
               xs)
          tbl)
      p [insert
           ((ceq_list (ceq_option ceq_event_data)),
             (ccompare_list (ccompare_option ccompare_event_data)))
           xs (set_empty
                ((ceq_list (ceq_option ceq_event_data)),
                  (ccompare_list (ccompare_option ccompare_event_data)))
                (of_phantom set_impl_lista))]
      db;;

end;; (*struct Monitor*)
