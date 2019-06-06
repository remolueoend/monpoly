module Monpoly : sig
  type nat
  val integer_of_nat : nat -> Big_int.big_int
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
  type 'a set_dlist
  type ('b, 'a) mapping_rbt
  type 'a set = Collect_set of ('a -> bool) | DList_set of 'a set_dlist |
    RBT_set of ('a, unit) mapping_rbt | Set_Monad of 'a list |
    Complement of 'a set
  val nat_of_integer : Big_int.big_int -> nat
  type 'a trm = Var of nat | Const of 'a
  type char
  type enat = Enat of nat | Infinity_enat
  type i
  type 'a formula = Pred of char list * 'a trm list | Eq of 'a trm * 'a trm |
    Neg of 'a formula | Or of 'a formula * 'a formula | Exists of 'a formula |
    Prev of i * 'a formula | Next of i * 'a formula |
    Since of 'a formula * i * 'a formula | Until of 'a formula * i * 'a formula
  type 'a mformula
  type ('a, 'b) mstate_ext
  val set : 'a ceq * 'a ccompare * 'a set_impl -> 'a list -> 'a set
  val mstep :
    'a ceq * 'a ccompare * 'a equal ->
      (char list * 'a list) set * nat ->
        ('a, unit) mstate_ext ->
          (nat * ('a option) list) set * ('a, unit) mstate_ext
  val interval : nat * enat -> i
  val minit_safe :
    'a ceq * 'a ccompare * 'a equal -> 'a formula -> ('a, unit) mstate_ext
  val db_code :
    'a ceq * 'a ccompare ->
      (char list * 'a list) list -> (char list * 'a list) set
  val explode : string -> char list
  val verdict_code :
    'a ccompare ->
      ((nat * ('a option) list), unit) mapping_rbt ->
        (nat * ('a option) list) list
end = struct

type nat = Nat of Big_int.big_int;;

let rec integer_of_nat (Nat x) = x;;

let rec equal_nata
  m n = Big_int.eq_big_int (integer_of_nat m) (integer_of_nat n);;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_nat = ({equal = equal_nata} : nat equal);;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec min _A a b = (if less_eq _A a b then a else b);;

let rec less_eq_nat
  m n = Big_int.le_big_int (integer_of_nat m) (integer_of_nat n);;

let rec less_nat
  m n = Big_int.lt_big_int (integer_of_nat m) (integer_of_nat n);;

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

let zero_nat : nat = Nat Big_int.zero_big_int;;

let card_UNIV_nata : (nat, nat) phantom = Phantom zero_nat;;

type 'a finite_UNIV = {finite_UNIV : ('a, bool) phantom};;
let finite_UNIV _A = _A.finite_UNIV;;

type 'a card_UNIV =
  {finite_UNIV_card_UNIV : 'a finite_UNIV; card_UNIV : ('a, nat) phantom};;
let card_UNIV _A = _A.card_UNIV;;

let finite_UNIV_nat = ({finite_UNIV = finite_UNIV_nata} : nat finite_UNIV);;

let card_UNIV_nat =
  ({finite_UNIV_card_UNIV = finite_UNIV_nat; card_UNIV = card_UNIV_nata} :
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

let ord_integer =
  ({less_eq = Big_int.le_big_int; less = Big_int.lt_big_int} :
    Big_int.big_int ord);;

let rec minus_nat
  m n = Nat (max ord_integer Big_int.zero_big_int
              (Big_int.sub_big_int (integer_of_nat m) (integer_of_nat n)));;

type num = One | Bit0 of num | Bit1 of num;;

let one_nat : nat = Nat (Big_int.big_int_of_int 1);;

let rec proper_interval_nat
  no x1 = match no, x1 with no, None -> true
    | None, Some x -> less_nat zero_nat x
    | Some x, Some y -> less_nat one_nat (minus_nat y x);;

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

type ('b, 'a) mapping_rbt = Mapping_RBT of ('b, 'a) rbt;;

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

let rec impl_of _B (Mapping_RBT x) = x;;

let rec the (Some x2) = x2;;

let rec insertb _A
  xc xd xe =
    Mapping_RBT (rbt_comp_insert (the (ccompare _A)) xc xd (impl_of _A xe));;

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

let rec plus_nat
  m n = Nat (Big_int.add_big_int (integer_of_nat m) (integer_of_nat n));;

let rec suc n = plus_nat n one_nat;;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (suc n) xs
                     | n, [] -> n;;

let rec size_list x = gen_length zero_nat x;;

let rec fst (x1, x2) = x1;;

let rec nat_of_integer k = Nat (max ord_integer Big_int.zero_big_int k);;

let rec apfst f (x, y) = (f x, y);;

let rec sgn_integer
  k = (if Big_int.eq_big_int k Big_int.zero_big_int then Big_int.zero_big_int
        else (if Big_int.lt_big_int k Big_int.zero_big_int
               then (Big_int.minus_big_int (Big_int.big_int_of_int 1))
               else (Big_int.big_int_of_int 1)));;

let rec apsnd f (x, y) = (x, f y);;

let rec comp f g = (fun x -> f (g x));;

let rec divmod_integer
  k l = (if Big_int.eq_big_int k Big_int.zero_big_int
          then (Big_int.zero_big_int, Big_int.zero_big_int)
          else (if Big_int.eq_big_int l Big_int.zero_big_int
                 then (Big_int.zero_big_int, k)
                 else comp (comp apsnd Big_int.mult_big_int) sgn_integer l
                        (if Big_int.eq_big_int (sgn_integer k) (sgn_integer l)
                          then Big_int.quomod_big_int (Big_int.abs_big_int k)
                                 (Big_int.abs_big_int l)
                          else (let (r, s) =
                                  Big_int.quomod_big_int (Big_int.abs_big_int k)
                                    (Big_int.abs_big_int l)
                                  in
                                 (if Big_int.eq_big_int s Big_int.zero_big_int
                                   then (Big_int.minus_big_int r,
  Big_int.zero_big_int)
                                   else (Big_int.sub_big_int
   (Big_int.minus_big_int r) (Big_int.big_int_of_int 1),
  Big_int.sub_big_int (Big_int.abs_big_int l) s))))));;

let rec snd (x1, x2) = x2;;

let rec modulo_integer k l = snd (divmod_integer k l);;

let rec modulo_nat
  m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));;

let rec divide_integer k l = fst (divmod_integer k l);;

let rec divide_nat
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

let rec divmod_nat m n = (divide_nat m n, modulo_nat m n);;

let rec rbtreeify_g
  n kvs =
    (if equal_nata n zero_nat || equal_nata n one_nat then (Empty, kvs)
      else (let (na, r) =
              divmod_nat n (nat_of_integer (Big_int.big_int_of_int 2)) in
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
      else (if equal_nata n one_nat
             then (let (k, v) :: kvsa = kvs in
                    (Branch (R, Empty, k, v, Empty), kvsa))
             else (let (na, r) =
                     divmod_nat n (nat_of_integer (Big_int.big_int_of_int 2)) in
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
      (rbt_comp_union_with_key (the (ccompare _A)) xc (impl_of _A xd)
        (impl_of _A xe));;

let rec list_insert
  equal x xs = (if list_member equal xs x then xs else x :: xs);;

let rec inserta _A
  xb xc = Abs_dlist (list_insert (the (ceq _A)) xb (list_of_dlist _A xc));;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec foldc _A x xc = fold x (list_of_dlist _A xc);;

let rec union _A = foldc _A (inserta _A);;

let rec memberb _A xa = list_member (the (ceq _A)) (list_of_dlist _A xa);;

let rec equal_option _A x0 x1 = match x0, x1 with None, Some x2 -> false
                          | Some x2, None -> false
                          | Some x2, Some y2 -> eq _A x2 y2
                          | None, None -> true;;

let rec rbt_comp_lookup
  c x1 k = match c, x1, k with c, Empty, k -> None
    | c, Branch (uu, l, x, y, r), k ->
        (match c k x with Eqa -> Some y | Lt -> rbt_comp_lookup c l k
          | Gt -> rbt_comp_lookup c r k);;

let rec lookup _A xa = rbt_comp_lookup (the (ccompare _A)) (impl_of _A xa);;

let rec equal_unita u v = true;;

let equal_unit = ({equal = equal_unita} : unit equal);;

let rec membera _A t x = equal_option equal_unit (lookup _A t x) (Some ());;

let rec member (_A1, _A2)
  x xa1 = match x, xa1 with
    x, Set_Monad xs ->
      (match ceq _A1
        with None ->
          failwith "member Set_Monad: ceq = None"
            (fun _ -> member (_A1, _A2) x (Set_Monad xs))
        | Some eq -> list_member eq xs x)
    | xa, Complement x -> not (member (_A1, _A2) xa x)
    | x, RBT_set rbt -> membera _A2 rbt x
    | x, DList_set dxs -> memberb _A1 dxs x
    | x, Collect_set a -> a x;;

let rec id x = (fun xa -> xa) x;;

let rec is_none = function Some x -> false
                  | None -> true;;

let rec filtera
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filtera p xs else filtera p xs);;

let rec inter_list _A
  xb xc =
    Mapping_RBT
      (fold (fun k -> rbt_comp_insert (the (ccompare _A)) k ())
        (filtera
          (fun x ->
            not (is_none
                  (rbt_comp_lookup (the (ccompare _A)) (impl_of _A xb) x)))
          xc)
        Empty);;

let rec filterc _A
  xb xc = Mapping_RBT (rbtreeify (filtera xb (entries (impl_of _A xc))));;

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
      (rbt_comp_inter_with_key (the (ccompare _A)) xc (impl_of _A xd)
        (impl_of _A xe));;

let rec filterb _A xb xc = Abs_dlist (filtera xb (list_of_dlist _A xc));;

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
          | Some _ -> DList_set (filterb _A1 (memberb _A1 dxs2) dxs1))
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

let rec init _A xa = rbt_init (impl_of _A xa);;

let rec collect _A
  p = (match cEnum _A with None -> Collect_set p
        | Some (enum, _) -> Set_Monad (filtera p enum));;

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

let rec finite_UNIV_set _A =
  ({finite_UNIV = finite_UNIV_seta _A} : 'a set finite_UNIV);;

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

let rec keysa _A xa = keys (impl_of _A xa);;

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

let cEnum_list :
  (('a list) list *
    ((('a list -> bool) -> bool) * (('a list -> bool) -> bool))) option
  = None;;

let cenum_list = ({cEnum = cEnum_list} : ('a list) cenum);;

let finite_UNIV_lista : (('a list), bool) phantom = Phantom false;;

let finite_UNIV_list =
  ({finite_UNIV = finite_UNIV_lista} : ('a list) finite_UNIV);;

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

type 'a one = {one : 'a};;
let one _A = _A.one;;

type 'a zero_neq_one =
  {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero};;

let rec of_bool _A = function true -> one _A.one_zero_neq_one
                     | false -> zero _A.zero_zero_neq_one;;

let one_integera : Big_int.big_int = (Big_int.big_int_of_int 1);;

let zero_integer = ({zero = Big_int.zero_big_int} : Big_int.big_int zero);;

let one_integer = ({one = one_integera} : Big_int.big_int one);;

let zero_neq_one_integer =
  ({one_zero_neq_one = one_integer; zero_zero_neq_one = zero_integer} :
    Big_int.big_int zero_neq_one);;

let rec integer_of_char
  (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
    Big_int.add_big_int
      (Big_int.mult_big_int
        (Big_int.add_big_int
          (Big_int.mult_big_int
            (Big_int.add_big_int
              (Big_int.mult_big_int
                (Big_int.add_big_int
                  (Big_int.mult_big_int
                    (Big_int.add_big_int
                      (Big_int.mult_big_int
                        (Big_int.add_big_int
                          (Big_int.mult_big_int
                            (Big_int.add_big_int
                              (Big_int.mult_big_int
                                (of_bool zero_neq_one_integer b7)
                                (Big_int.big_int_of_int 2))
                              (of_bool zero_neq_one_integer b6))
                            (Big_int.big_int_of_int 2))
                          (of_bool zero_neq_one_integer b5))
                        (Big_int.big_int_of_int 2))
                      (of_bool zero_neq_one_integer b4))
                    (Big_int.big_int_of_int 2))
                  (of_bool zero_neq_one_integer b3))
                (Big_int.big_int_of_int 2))
              (of_bool zero_neq_one_integer b2))
            (Big_int.big_int_of_int 2))
          (of_bool zero_neq_one_integer b1))
        (Big_int.big_int_of_int 2))
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

let rec equality_option
  eq_a x1 x2 = match eq_a, x1, x2 with eq_a, Some x, Some y -> eq_a x y
    | eq_a, Some x, None -> false
    | eq_a, None, Some y -> false
    | eq_a, None, None -> true;;

let rec ceq_optiona _A
  = (match ceq _A with None -> None
      | Some eq_a -> Some (equality_option eq_a));;

let rec ceq_option _A = ({ceq = ceq_optiona _A} : ('a option) ceq);;

let rec set_impl_optiona _A = Phantom (of_phantom (set_impl _A));;

let rec set_impl_option _A =
  ({set_impl = set_impl_optiona _A} : ('a option) set_impl);;

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

let rec finite_UNIV_proda _A _B
  = Phantom (of_phantom (finite_UNIV _A) && of_phantom (finite_UNIV _B));;

let rec finite_UNIV_prod _A _B =
  ({finite_UNIV = finite_UNIV_proda _A _B} : ('a * 'b) finite_UNIV);;

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

type enat = Enat of nat | Infinity_enat;;

type i = Abs_I of (nat * enat);;

type 'a formula = Pred of char list * 'a trm list | Eq of 'a trm * 'a trm |
  Neg of 'a formula | Or of 'a formula * 'a formula | Exists of 'a formula |
  Prev of i * 'a formula | Next of i * 'a formula |
  Since of 'a formula * i * 'a formula | Until of 'a formula * i * 'a formula;;

type 'a mformula = MRel of (('a option) list) set |
  MPred of char list * 'a trm list |
  MAnd of
    'a mformula * bool * 'a mformula *
      ((('a option) list) set list * (('a option) list) set list)
  | MOr of
      'a mformula * 'a mformula *
        ((('a option) list) set list * (('a option) list) set list)
  | MExists of 'a mformula |
  MPrev of i * 'a mformula * bool * (('a option) list) set list * nat list |
  MNext of i * 'a mformula * bool * nat list |
  MSince of
    bool * 'a mformula * i * 'a mformula *
      ((('a option) list) set list * (('a option) list) set list) * nat list *
      (nat * (('a option) list) set) list
  | MUntil of
      bool * 'a mformula * i * 'a mformula *
        ((('a option) list) set list * (('a option) list) set list) * nat list *
        (nat * ((('a option) list) set * (('a option) list) set)) list;;

type ('b, 'a) comp_fun_idem = Abs_comp_fun_idem of ('b -> 'a -> 'a);;

type 'a semilattice_set = Abs_semilattice_set of ('a -> 'a -> 'a);;

type ('a, 'b) mstate_ext = Mstate_ext of nat * 'a mformula * nat * 'b;;

let rec rev xs = fold (fun a b -> a :: b) xs [];;

let rec maps f x1 = match f, x1 with f, [] -> []
               | f, x :: xs -> f x @ maps f xs;;

let rec comp_fun_idem_apply (Abs_comp_fun_idem x) = x;;

let rec foldb _A x xc = folda (fun a _ -> x a) (impl_of _A xc);;

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
  xb xc = Mapping_RBT (rbt_comp_delete (the (ccompare _A)) xb (impl_of _A xc));;

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

let rec fvi_trm
  b x1 = match b, x1 with
    b, Var x ->
      (if less_eq_nat b x
        then insert (ceq_nat, ccompare_nat) (minus_nat x b)
               (set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata))
        else set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata))
    | b, Const uu ->
        set_empty (ceq_nat, ccompare_nat) (of_phantom set_impl_nata);;

let rec foldl f a x2 = match f, a, x2 with f, a, [] -> a
                | f, a, x :: xs -> foldl f (f a x) xs;;

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
    | b, Exists phi -> fvi (_A1, _A2) (suc b) phi
    | b, Prev (i, phi) -> fvi (_A1, _A2) b phi
    | b, Next (i, phi) -> fvi (_A1, _A2) b phi
    | b, Since (phi, i, psi) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi (_A1, _A2) b phi)
          (fvi (_A1, _A2) b psi)
    | b, Until (phi, i, psi) ->
        sup_seta (ceq_nat, ccompare_nat) (fvi (_A1, _A2) b phi)
          (fvi (_A1, _A2) b psi);;

let rec semilattice_set_apply (Abs_semilattice_set x) = x;;

let rec is_empty _A
  xa = (match impl_of _A xa with Empty -> true
         | Branch (_, _, _, _, _) -> false);;

let rec rBT_Impl_fold1
  f x1 = match f, x1 with
    f, Branch (ca, Branch (c, l, ka, va, ra), k, v, r) ->
      folda (fun kb _ -> f kb) r
        (f k (rBT_Impl_fold1 f (Branch (c, l, ka, va, ra))))
    | f, Branch (c, Empty, k, v, r) -> folda (fun ka _ -> f ka) r k
    | f, Empty -> failwith "undefined";;

let rec fold1 _A x xc = rBT_Impl_fold1 x (impl_of _A xc);;

let rec nulla _A xa = null (list_of_dlist _A xa);;

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
          (if is_empty _A2 rbt
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

let rec foldr f x1 = match f, x1 with f, [] -> id
                | f, x :: xs -> comp (f x) (foldr f xs);;

let rec filter (_A1, _A2) p a = inf_seta (_A1, _A2) a (Collect_set p);;

let rec minus_set (_A1, _A2) a b = inf_seta (_A1, _A2) a (uminus_set b);;

let rec productb _A _B
  dxs1 dxs2 =
    Abs_dlist
      (foldc _A (fun a -> foldc _B (fun c -> (fun b -> (a, c) :: b)) dxs2) dxs1
        []);;

let rec rbt_product
  f rbt1 rbt2 =
    rbtreeify
      (rev (folda
             (fun a b ->
               folda (fun c d -> (fun e -> ((a, c), f a b c d) :: e)) rbt2)
             rbt1 []));;

let rec productd _A _B
  xc xd xe = Mapping_RBT (rbt_product xc (impl_of _A xd) (impl_of _B xe));;

let rec producta _A _B
  rbt1 rbt2 = productd _A _B (fun _ _ _ _ -> ()) rbt1 rbt2;;

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

let rec these (_A1, _A2, _A3)
  a = image ((ceq_option _A1), (ccompare_option _A2)) (_A1, _A2, _A3) the
        (filter ((ceq_option _A1), (ccompare_option _A2))
          (fun x -> not (is_none x)) a);;

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
  a pos b =
    (if pos
      then these ((ceq_list (ceq_option _A1)),
                   (ccompare_list (ccompare_option _A2)), set_impl_list)
             (image
               ((ceq_prod (ceq_list (ceq_option _A1))
                  (ceq_list (ceq_option _A1))),
                 (ccompare_prod (ccompare_list (ccompare_option _A2))
                   (ccompare_list (ccompare_option _A2))))
               ((ceq_option (ceq_list (ceq_option _A1))),
                 (ccompare_option (ccompare_list (ccompare_option _A2))),
                 (set_impl_option set_impl_list))
               (join1 _A3)
               (productc
                 ((ceq_list (ceq_option _A1)),
                   (ccompare_list (ccompare_option _A2)), set_impl_list)
                 ((ceq_list (ceq_option _A1)),
                   (ccompare_list (ccompare_option _A2)), set_impl_list)
                 a b))
      else minus_set
             ((ceq_list (ceq_option _A1)),
               (ccompare_list (ccompare_option _A2)))
             a (these
                 ((ceq_list (ceq_option _A1)),
                   (ccompare_list (ccompare_option _A2)), set_impl_list)
                 (image
                   ((ceq_prod (ceq_list (ceq_option _A1))
                      (ceq_list (ceq_option _A1))),
                     (ccompare_prod (ccompare_list (ccompare_option _A2))
                       (ccompare_list (ccompare_option _A2))))
                   ((ceq_option (ceq_list (ceq_option _A1))),
                     (ccompare_option (ccompare_list (ccompare_option _A2))),
                     (set_impl_option set_impl_list))
                   (join1 _A3)
                   (productc
                     ((ceq_list (ceq_option _A1)),
                       (ccompare_list (ccompare_option _A2)), set_impl_list)
                     ((ceq_list (ceq_option _A1)),
                       (ccompare_list (ccompare_option _A2)), set_impl_list)
                     a b))));;

let rec fun_upd _A f a b = (fun x -> (if eq _A x a then b else f x));;

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

let rec equal_list _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_list _A x22 y22
    | [], [] -> true;;

let rec less_eq_enat q x1 = match q, x1 with Infinity_enat, Enat n -> false
                       | q, Infinity_enat -> true
                       | Enat m, Enat n -> less_eq_nat m n;;

let rec empty_table (_A1, _A2, _A3) = bot_set (_A1, _A2, _A3);;

let rec right x = snd (rep_I x);;

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
       (match
         maps (fun (t, rel) ->
                (if less_eq_enat (minus_enat (Enat nt) (Enat t)) (right i)
                  then [(t, join (_A1, _A2, _A3) rel pos rel1)] else []))
           aux
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
                 (if less_eq_nat (left i) (minus_nat nt t) then [rel] else []))
           auxa)
         (set_empty
           ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
           (of_phantom set_impl_lista)),
        auxa));;

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

let rec less_enat x0 q = match x0, q with Infinity_enat, q -> false
                    | Enat m, Infinity_enat -> true
                    | Enat m, Enat n -> less_nat m n;;

let rec eval_until
  i nt x2 = match i, nt, x2 with i, nt, [] -> ([], [])
    | i, nt, (t, (a1, a2)) :: aux ->
        (if less_enat (plus_enat (Enat t) (right i)) (Enat nt)
          then (let a = eval_until i nt aux in
                let (xs, aa) = a in
                 (a2 :: xs, aa))
          else ([], (t, (a1, a2)) :: aux));;

let rec mbuf2_add xsa ysa (xs, ys) = (xs @ xsa, ys @ ysa);;

let rec tabulate
  f x n =
    (if equal_nata n zero_nat then []
      else f x :: tabulate f (suc x) (minus_nat n one_nat));;

let rec meval (_A1, _A2, _A3)
  n t db x3 = match n, t, db, x3 with
    n, t, db, MUntil (pos, phi, i, psi, buf, nts, aux) ->
      (let (xs, phia) = meval (_A1, _A2, _A3) n t db phi in
       let (ys, psia) = meval (_A1, _A2, _A3) n t db psi in
       let (auxa, (bufa, ntsa)) =
         mbuf2t_take (update_until (_A1, _A2, _A3) i pos) aux
           (mbuf2_add xs ys buf) (nts @ [t])
         in
       let (zs, auxb) =
         eval_until i (match ntsa with [] -> t | nt :: _ -> nt) auxa in
        (zs, MUntil (pos, phia, i, psia, bufa, ntsa, auxb)))
    | n, t, db, MSince (pos, phi, i, psi, buf, nts, aux) ->
        (let (xs, phia) = meval (_A1, _A2, _A3) n t db phi in
         let (ys, psia) = meval (_A1, _A2, _A3) n t db psi in
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
        (let (xs, phia) = meval (_A1, _A2, _A3) n t db phi in
         let (xsa, firsta) =
           (match (xs, first) with ([], b) -> ([], b)
             | (_ :: xsa, true) -> (xsa, false)
             | (x :: xsa, false) -> (x :: xsa, false))
           in
         let (zs, (_, ntsa)) = mprev_next (_A1, _A2) i xsa (nts @ [t]) in
          (zs, MNext (i, phia, firsta, ntsa)))
    | n, t, db, MPrev (i, phi, first, buf, nts) ->
        (let (xs, phia) = meval (_A1, _A2, _A3) n t db phi in
         let (zs, (bufa, ntsa)) = mprev_next (_A1, _A2) i (buf @ xs) (nts @ [t])
           in
          ((if first
             then empty_table
                    ((ceq_list (ceq_option _A1)),
                      (ccompare_list (ccompare_option _A2)), set_impl_list) ::
                    zs
             else zs),
            MPrev (i, phia, false, bufa, ntsa)))
    | n, t, db, MExists phi ->
        (let (xs, phia) = meval (_A1, _A2, _A3) (suc n) t db phi in
          (map (image
                 ((ceq_list (ceq_option _A1)),
                   (ccompare_list (ccompare_option _A2)))
                 ((ceq_list (ceq_option _A1)),
                   (ccompare_list (ccompare_option _A2)), set_impl_list)
                 tla)
             xs,
            MExists phia))
    | n, t, db, MOr (phi, psi, buf) ->
        (let (xs, phia) = meval (_A1, _A2, _A3) n t db phi in
         let (ys, psia) = meval (_A1, _A2, _A3) n t db psi in
         let (zs, bufa) =
           mbuf2_take
             (sup_seta
               ((ceq_list (ceq_option _A1)),
                 (ccompare_list (ccompare_option _A2))))
             (mbuf2_add xs ys buf)
           in
          (zs, MOr (phia, psia, bufa)))
    | n, t, db, MAnd (phi, pos, psi, buf) ->
        (let (xs, phia) = meval (_A1, _A2, _A3) n t db phi in
         let (ys, psia) = meval (_A1, _A2, _A3) n t db psi in
         let (zs, bufa) =
           mbuf2_take (fun r1 -> join (_A1, _A2, _A3) r1 pos)
             (mbuf2_add xs ys buf)
           in
          (zs, MAnd (phia, pos, psia, bufa)))
    | n, t, db, MPred (e, ts) ->
        ([these ((ceq_list (ceq_option _A1)),
                  (ccompare_list (ccompare_option _A2)), set_impl_list)
            (image ((ceq_list _A1), (ccompare_list _A2))
              ((ceq_option (ceq_list (ceq_option _A1))),
                (ccompare_option (ccompare_list (ccompare_option _A2))),
                (set_impl_option set_impl_list))
              (comp (map_option (fun f -> tabulate f zero_nat n))
                (matcha _A3 ts))
              (sup_setb
                (finite_UNIV_list, cenum_list, (ceq_list _A1),
                  (cproper_interval_list _A2), set_impl_list)
                (image
                  ((ceq_prod (ceq_list ceq_char) (ceq_list _A1)),
                    (ccompare_prod (ccompare_list ccompare_char)
                      (ccompare_list _A2)))
                  ((ceq_set
                     (cenum_list, (ceq_list _A1),
                       (cproper_interval_list _A2).ccompare_cproper_interval)),
                    (ccompare_set
                      (finite_UNIV_list, (ceq_list _A1),
                        (cproper_interval_list _A2), set_impl_list)),
                    set_impl_set)
                  (fun (ea, x) ->
                    (if equal_list equal_char e ea
                      then insert ((ceq_list _A1), (ccompare_list _A2)) x
                             (set_empty ((ceq_list _A1), (ccompare_list _A2))
                               (of_phantom set_impl_lista))
                      else set_empty ((ceq_list _A1), (ccompare_list _A2))
                             (of_phantom set_impl_lista)))
                  db)))],
          MPred (e, ts))
    | n, t, db, MRel rel -> ([rel], MRel rel);;

let rec subset (_A1, _A2, _A3, _A4) = subset_eq (_A2, _A3, _A4);;

let rec is_Const = function Var x1 -> false
                   | Const x2 -> true;;

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
              | Exists _ -> false | Prev (_, _) -> false | Next (_, _) -> false
              | Since (_, _, _) -> false | Until (_, _, _) -> false))
    | Or (phi, psi) ->
        set_eq (cenum_nat, ceq_nat, ccompare_nat) (fvi (_A1, _A2) zero_nat psi)
          (fvi (_A1, _A2) zero_nat phi) &&
          (safe_formula (_A1, _A2) phi && safe_formula (_A1, _A2) psi)
    | Exists phi -> safe_formula (_A1, _A2) phi
    | Prev (i, phi) -> safe_formula (_A1, _A2) phi
    | Next (i, phi) -> safe_formula (_A1, _A2) phi
    | Since (phi, i, psi) ->
        subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat phi) (fvi (_A1, _A2) zero_nat psi) &&
          ((safe_formula (_A1, _A2) phi ||
             (match phi with Pred (_, _) -> false | Eq (_, _) -> false
               | Neg a -> safe_formula (_A1, _A2) a | Or (_, _) -> false
               | Exists _ -> false | Prev (_, _) -> false | Next (_, _) -> false
               | Since (_, _, _) -> false | Until (_, _, _) -> false)) &&
            safe_formula (_A1, _A2) psi)
    | Until (phi, i, psi) ->
        subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat phi) (fvi (_A1, _A2) zero_nat psi) &&
          ((safe_formula (_A1, _A2) phi ||
             (match phi with Pred (_, _) -> false | Eq (_, _) -> false
               | Neg a -> safe_formula (_A1, _A2) a | Or (_, _) -> false
               | Exists _ -> false | Prev (_, _) -> false | Next (_, _) -> false
               | Since (_, _, _) -> false | Until (_, _, _) -> false)) &&
            safe_formula (_A1, _A2) psi)
    | Neg (Pred (va, vb)) -> false
    | Neg (Eq (Var vc, Const v)) -> false
    | Neg (Eq (Const v, Var vc)) -> false
    | Neg (Neg va) -> false
    | Neg (Or (Pred (v, vc), vb)) -> false
    | Neg (Or (Eq (v, vc), vb)) -> false
    | Neg (Or (Or (v, vc), vb)) -> false
    | Neg (Or (Exists v, vb)) -> false
    | Neg (Or (Prev (v, vc), vb)) -> false
    | Neg (Or (Next (v, vc), vb)) -> false
    | Neg (Or (Since (v, vc, vd), vb)) -> false
    | Neg (Or (Until (v, vc, vd), vb)) -> false
    | Neg (Exists va) -> false
    | Neg (Prev (va, vb)) -> false
    | Neg (Next (va, vb)) -> false
    | Neg (Since (va, vb, vc)) -> false
    | Neg (Until (va, vb, vc)) -> false;;

let rec replicate
  n x = (if equal_nata n zero_nat then []
          else x :: replicate (minus_nat n one_nat) x);;

let rec unit_table (_A1, _A2)
  n = insert
        ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
        (replicate n None)
        (set_empty
          ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
          (of_phantom set_impl_lista));;

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

let rec singleton_table (_A1, _A2)
  n i x =
    insert ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
      (tabulate (fun j -> (if equal_nata i j then Some x else None)) zero_nat n)
      (set_empty
        ((ceq_list (ceq_option _A1)), (ccompare_list (ccompare_option _A2)))
        (of_phantom set_impl_lista));;

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
      (match phi with Eq (t1, t2) -> MRel (neq_rel (_A1, _A2, _A3) n t1 t2)
        | Or (Neg phia, psi) ->
          (if safe_formula (_A2, _A3) psi &&
                subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
                  (fvi (_A2, _A3) zero_nat psi) (fvi (_A2, _A3) zero_nat phia)
            then MAnd (minit0 (_A1, _A2, _A3) n phia, false,
                        minit0 (_A1, _A2, _A3) n psi, ([], []))
            else (let Neg psia = psi in
                   MAnd (minit0 (_A1, _A2, _A3) n phia, true,
                          minit0 (_A1, _A2, _A3) n psia, ([], [])))))
    | n, Eq (t1, t2) -> MRel (eq_rel (_A1, _A2, _A3) n t1 t2)
    | n, Pred (e, ts) -> MPred (e, ts)
    | n, Or (phi, psi) ->
        MOr (minit0 (_A1, _A2, _A3) n phi, minit0 (_A1, _A2, _A3) n psi,
              ([], []))
    | n, Exists phi -> MExists (minit0 (_A1, _A2, _A3) (suc n) phi)
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
                     minit0 (_A1, _A2, _A3) n psi, ([], []), [], [])));;

let rec minit (_A1, _A2, _A3)
  phi = (let n = nfv (_A2, _A3) phi in
          Mstate_ext (zero_nat, minit0 (_A1, _A2, _A3) n phi, n, ()));;

let rec mstate_n (Mstate_ext (mstate_i, mstate_m, mstate_n, more)) = mstate_n;;

let rec mstate_m (Mstate_ext (mstate_i, mstate_m, mstate_n, more)) = mstate_m;;

let rec mstate_i (Mstate_ext (mstate_i, mstate_m, mstate_n, more)) = mstate_i;;

let rec enumerate
  n x1 = match n, x1 with n, x :: xs -> (n, x) :: enumerate (suc n) xs
    | n, [] -> [];;

let rec mstep (_A1, _A2, _A3)
  tdb st =
    (let (xs, m) =
       meval (_A1, _A2, _A3) (mstate_n st) (snd tdb) (fst tdb) (mstate_m st) in
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
  i = Abs_I (if less_eq_enat (Enat (fst i)) (snd i) then i
              else rep_I (failwith "undefined"));;

let rec equal_enat x0 x1 = match x0, x1 with Enat nat, Infinity_enat -> false
                     | Infinity_enat, Enat nat -> false
                     | Enat nata, Enat nat -> equal_nata nata nat
                     | Infinity_enat, Infinity_enat -> true;;

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
              | Exists _ -> false | Prev (_, _) -> false | Next (_, _) -> false
              | Since (_, _, _) -> false | Until (_, _, _) -> false))
    | Or (phi, psi) ->
        set_eq (cenum_nat, ceq_nat, ccompare_nat) (fvi (_A1, _A2) zero_nat psi)
          (fvi (_A1, _A2) zero_nat phi) &&
          (mmonitorable_exec (_A1, _A2) phi && mmonitorable_exec (_A1, _A2) psi)
    | Exists phi -> mmonitorable_exec (_A1, _A2) phi
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
               | Exists _ -> false | Prev (_, _) -> false | Next (_, _) -> false
               | Since (_, _, _) -> false | Until (_, _, _) -> false)) &&
            mmonitorable_exec (_A1, _A2) psi)
    | Until (phi, i, psi) ->
        subset (card_UNIV_nat, cenum_nat, ceq_nat, ccompare_nat)
          (fvi (_A1, _A2) zero_nat phi) (fvi (_A1, _A2) zero_nat psi) &&
          (not (equal_enat (right i) Infinity_enat) &&
            ((mmonitorable_exec (_A1, _A2) phi ||
               (match phi with Pred (_, _) -> false | Eq (_, _) -> false
                 | Neg a -> mmonitorable_exec (_A1, _A2) a | Or (_, _) -> false
                 | Exists _ -> false | Prev (_, _) -> false
                 | Next (_, _) -> false | Since (_, _, _) -> false
                 | Until (_, _, _) -> false)) &&
              mmonitorable_exec (_A1, _A2) psi))
    | Neg (Pred (va, vb)) -> false
    | Neg (Eq (Var vc, Const v)) -> false
    | Neg (Eq (Const v, Var vc)) -> false
    | Neg (Neg va) -> false
    | Neg (Or (Pred (v, vc), vb)) -> false
    | Neg (Or (Eq (v, vc), vb)) -> false
    | Neg (Or (Or (v, vc), vb)) -> false
    | Neg (Or (Exists v, vb)) -> false
    | Neg (Or (Prev (v, vc), vb)) -> false
    | Neg (Or (Next (v, vc), vb)) -> false
    | Neg (Or (Since (v, vc, vd), vb)) -> false
    | Neg (Or (Until (v, vc, vd), vb)) -> false
    | Neg (Exists va) -> false
    | Neg (Prev (va, vb)) -> false
    | Neg (Next (va, vb)) -> false
    | Neg (Since (va, vb, vc)) -> false
    | Neg (Until (va, vb, vc)) -> false;;

let rec minit_safe (_A1, _A2, _A3)
  phi = (if mmonitorable_exec (_A2, _A3) phi then minit (_A1, _A2, _A3) phi
          else failwith "undefined");;

let rec db_code (_A1, _A2)
  = set ((ceq_prod (ceq_list ceq_char) (ceq_list _A1)),
          (ccompare_prod (ccompare_list ccompare_char) (ccompare_list _A2)),
          (set_impl_prod set_impl_list set_impl_list));;

let rec bit_cut_integer
  k = (if Big_int.eq_big_int k Big_int.zero_big_int
        then (Big_int.zero_big_int, false)
        else (let (r, s) =
                Big_int.quomod_big_int (Big_int.abs_big_int k)
                  (Big_int.abs_big_int (Big_int.big_int_of_int 2))
                in
               ((if Big_int.lt_big_int Big_int.zero_big_int k then r
                  else Big_int.sub_big_int (Big_int.minus_big_int r) s),
                 Big_int.eq_big_int s (Big_int.big_int_of_int 1))));;

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
        (let s = s in let rec exp i l = if i < 0 then l else exp (i - 1) (let k = Char.code (Bytes.get s i) in
      if k < 128 then Big_int.big_int_of_int k :: l else failwith "Non-ASCII character in literal") in exp (Bytes.length s - 1) []);;

let rec verdict_code _A
  = keysa (ccompare_prod ccompare_nat (ccompare_list (ccompare_option _A)));;

end;; (*struct Monpoly*)
