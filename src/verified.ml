module Monpoly : sig
  type nat
  val integer_of_nat : nat -> Big_int.big_int
  type 'a equal = {equal : 'a -> 'a -> bool}
  val equal : 'a equal -> 'a -> 'a -> bool
  type 'a set = Set of 'a list | Coset of 'a list
  type char
  type enat = Enat of nat | Infinity_enat
  type 'a trm = Var of nat | Const of 'a
  type i
  type 'a formula = Pred of char list * 'a trm list | Eq of 'a trm * 'a trm |
    Neg of 'a formula | Disj of 'a formula * 'a formula | Exists of 'a formula |
    Prev of i * 'a formula | Next of i * 'a formula |
    Since of 'a formula * i * 'a formula | Until of 'a formula * i * 'a formula
  type 'a mformula
  type ('a, 'b) mstate_ext
  val interval : nat * enat -> i
  val mstep :
    'a equal ->
      (char list * 'a list) set * nat ->
        ('a, unit) mstate_ext ->
          (nat * ('a option) list) set * ('a, unit) mstate_ext
  val minit_safe : 'a equal -> 'a formula -> ('a, unit) mstate_ext
  val explode : string -> char list
  val nat_of_integer : Big_int.big_int -> nat
end = struct

type nat = Nat of Big_int.big_int;;

let rec integer_of_nat (Nat x) = x;;

let rec equal_nata
  m n = Big_int.eq_big_int (integer_of_nat m) (integer_of_nat n);;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_nat = ({equal = equal_nata} : nat equal);;

let rec less_eq_nat
  m n = Big_int.le_big_int (integer_of_nat m) (integer_of_nat n);;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec less_nat
  m n = Big_int.lt_big_int (integer_of_nat m) (integer_of_nat n);;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

let preorder_nat = ({ord_preorder = ord_nat} : nat preorder);;

let order_nat = ({preorder_order = preorder_nat} : nat order);;

type 'a linorder = {order_linorder : 'a order};;

let linorder_nat = ({order_linorder = order_nat} : nat linorder);;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

type 'a set = Set of 'a list | Coset of 'a list;;

let rec eq _A a b = equal _A a b;;

let rec membera _A x0 y = match x0, y with [], y -> false
                     | x :: xs, y -> eq _A x y || membera _A xs y;;

let rec member _A
  x xa1 = match x, xa1 with x, Coset xs -> not (membera _A xs x)
    | x, Set xs -> membera _A xs x;;

let rec less_eq_set _A
  a b = match a, b with Coset [], Set [] -> false
    | a, Coset ys -> list_all (fun y -> not (member _A y a)) ys
    | Set xs, b -> list_all (fun x -> member _A x b) xs;;

let rec equal_seta _A a b = less_eq_set _A a b && less_eq_set _A b a;;

let rec equal_set _A = ({equal = equal_seta _A} : 'a set equal);;

let rec equal_lista _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_lista _A x22 y22
    | [], [] -> true;;

let rec equal_list _A = ({equal = equal_lista _A} : ('a list) equal);;

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

let rec equal_optiona _A x0 x1 = match x0, x1 with None, Some x2 -> false
                           | Some x2, None -> false
                           | Some x2, Some y2 -> eq _A x2 y2
                           | None, None -> true;;

let rec equal_option _A = ({equal = equal_optiona _A} : ('a option) equal);;

type enat = Enat of nat | Infinity_enat;;

let rec less_eq_enat q x1 = match q, x1 with Infinity_enat, Enat n -> false
                       | q, Infinity_enat -> true
                       | Enat m, Enat n -> less_eq_nat m n;;

let rec less_enat x0 q = match x0, q with Infinity_enat, q -> false
                    | Enat m, Infinity_enat -> true
                    | Enat m, Enat n -> less_nat m n;;

let ord_enat = ({less_eq = less_eq_enat; less = less_enat} : enat ord);;

let rec equal_proda _A _B (x1, x2) (y1, y2) = eq _A x1 y1 && eq _B x2 y2;;

let rec equal_prod _A _B = ({equal = equal_proda _A _B} : ('a * 'b) equal);;

let ord_integer =
  ({less_eq = Big_int.le_big_int; less = Big_int.lt_big_int} :
    Big_int.big_int ord);;

type num = One | Bit0 of num | Bit1 of num;;

type 'a trm = Var of nat | Const of 'a;;

type i = Abs_I of (nat * enat);;

type 'a formula = Pred of char list * 'a trm list | Eq of 'a trm * 'a trm |
  Neg of 'a formula | Disj of 'a formula * 'a formula | Exists of 'a formula |
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

type ('a, 'b) mstate_ext = Mstate_ext of nat * 'a mformula * nat * 'b;;

let rec id x = (fun xa -> xa) x;;

let rec plus_nat
  m n = Nat (Big_int.add_big_int (integer_of_nat m) (integer_of_nat n));;

let one_nat : nat = Nat (Big_int.big_int_of_int 1);;

let rec suc n = plus_nat n one_nat;;

let rec comp f g = (fun x -> f (g x));;

let rec filtera
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filtera p xs else filtera p xs);;

let rec removeAll _A
  x xa1 = match x, xa1 with x, [] -> []
    | x, y :: xs ->
        (if eq _A x y then removeAll _A x xs else y :: removeAll _A x xs);;

let rec inserta _A x xs = (if membera _A xs x then xs else x :: xs);;

let rec insert _A
  x xa1 = match x, xa1 with x, Coset xs -> Coset (removeAll _A x xs)
    | x, Set xs -> Set (inserta _A x xs);;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec sup_set _A
  x0 a = match x0, a with
    Coset xs, a -> Coset (filtera (fun x -> not (member _A x a)) xs)
    | Set xs, a -> fold (insert _A) xs a;;

let bot_set : 'a set = Set [];;

let rec sup_seta _A (Set xs) = fold (sup_set _A) xs bot_set;;

let rec max _A a b = (if less_eq _A a b then b else a);;

let rec minus_nat
  m n = Nat (max ord_integer Big_int.zero_big_int
              (Big_int.sub_big_int (integer_of_nat m) (integer_of_nat n)));;

let rec fv_trm
  b x1 = match b, x1 with
    b, Var x ->
      (if less_eq_nat b x then insert equal_nat (minus_nat x b) bot_set
        else bot_set)
    | b, Const uu -> bot_set;;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec remdups _A
  = function [] -> []
    | x :: xs ->
        (if membera _A xs x then remdups _A xs else x :: remdups _A xs);;

let rec image _B f (Set xs) = Set (remdups _B (map f xs));;

let rec fv
  b x1 = match b, x1 with
    b, Pred (r, ts) ->
      sup_seta equal_nat (image (equal_set equal_nat) (fv_trm b) (Set ts))
    | b, Eq (t1, t2) -> sup_set equal_nat (fv_trm b t1) (fv_trm b t2)
    | b, Neg phi -> fv b phi
    | b, Disj (phi, psi) -> sup_set equal_nat (fv b phi) (fv b psi)
    | b, Exists phi -> fv (suc b) phi
    | b, Prev (i, phi) -> fv b phi
    | b, Next (i, phi) -> fv b phi
    | b, Since (phi, i, psi) -> sup_set equal_nat (fv b phi) (fv b psi)
    | b, Until (phi, i, psi) -> sup_set equal_nat (fv b phi) (fv b psi);;

let rec maps f x1 = match f, x1 with f, [] -> []
               | f, x :: xs -> f x @ maps f xs;;

let rec maxa _A
  (Set (x :: xs)) =
    fold (max _A.order_linorder.preorder_order.ord_preorder) xs x;;

let zero_nat : nat = Nat Big_int.zero_big_int;;

let rec nfv
  phi = maxa linorder_nat
          (insert equal_nat zero_nat (image equal_nat suc (fv zero_nat phi)));;

let rec foldr f x1 = match f, x1 with f, [] -> id
                | f, x :: xs -> comp (f x) (foldr f xs);;

let rec filter p (Set xs) = Set (filtera p xs);;

let rec remove _A
  x xa1 = match x, xa1 with x, Coset xs -> Coset (inserta _A x xs)
    | x, Set xs -> Set (removeAll _A x xs);;

let rec minus_set _A
  a x1 = match a, x1 with
    a, Coset xs -> Set (filtera (fun x -> member _A x a) xs)
    | a, Set xs -> fold (remove _A) xs a;;

let rec product
  (Set xs) (Set ys) = Set (maps (fun x -> map (fun a -> (x, a)) ys) xs);;

let rec the (Some x2) = x2;;

let rec is_none = function Some x -> false
                  | None -> true;;

let rec these _A a = image _A the (filter (fun x -> not (is_none x)) a);;

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

let rec join _A
  a pos b =
    (if pos
      then these (equal_list (equal_option _A))
             (image (equal_option (equal_list (equal_option _A))) (join1 _A)
               (product a b))
      else minus_set (equal_list (equal_option _A)) a
             (these (equal_list (equal_option _A))
               (image (equal_option (equal_list (equal_option _A))) (join1 _A)
                 (product a b))));;

let rec fun_upd _A f a b = (fun x -> (if eq _A x a then b else f x));;

let rec tl = function [] -> []
             | x21 :: x22 -> x22;;

let rec rep_I (Abs_I x) = x;;

let rec fst (x1, x2) = x1;;

let rec left x = fst (rep_I x);;

let rec snd (x1, x2) = x2;;

let rec right x = snd (rep_I x);;

let rec enumerate
  n x1 = match n, x1 with n, x :: xs -> (n, x) :: enumerate (suc n) xs
    | n, [] -> [];;

let rec replicate
  n x = (if equal_nata n zero_nat then []
          else x :: replicate (minus_nat n one_nat) x);;

let rec tabulate
  f x n =
    (if equal_nata n zero_nat then []
      else f x :: tabulate f (suc x) (minus_nat n one_nat));;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (suc n) xs
                     | n, [] -> n;;

let rec unit_table _A
  n = insert (equal_list (equal_option _A)) (replicate n None) bot_set;;

let rec interval
  i = Abs_I (if less_eq_enat (Enat (fst i)) (snd i) then i
              else rep_I (failwith "undefined"));;

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

let empty_table : 'a set = bot_set;;

let rec update_until _A
  i pos rel1 rel2 nt aux =
    map (fun (t, (a1, a2)) ->
          (t, ((if pos then join _A a1 true rel1
                 else sup_set (equal_list (equal_option _A)) a1 rel1),
                (if less_eq_nat (left i) (minus_nat nt t) &&
                      less_eq_enat (Enat (minus_nat nt t)) (right i)
                  then sup_set (equal_list (equal_option _A)) a2
                         (join _A rel2 pos a1)
                  else a2))))
      aux @
      [(nt, (rel1,
              (if equal_nata (left i) zero_nat then rel2 else empty_table)))];;

let zero_enat : enat = Enat zero_nat;;

let rec minus_enat x0 n = match x0, n with Enat a, Infinity_enat -> zero_enat
                     | Infinity_enat, n -> Infinity_enat
                     | Enat a, Enat b -> Enat (minus_nat a b);;

let rec update_since _A
  i pos rel1 rel2 nt aux =
    (let auxa =
       (match
         maps (fun (t, rel) ->
                (if less_eq_enat (minus_enat (Enat nt) (Enat t)) (right i)
                  then [(t, join _A rel pos rel1)] else []))
           aux
         with [] -> [(nt, rel2)]
         | x :: auxa ->
           (if equal_nata (fst x) nt
             then (fst x,
                    sup_set (equal_list (equal_option _A)) (snd x) rel2) ::
                    auxa
             else (nt, rel2) :: x :: auxa))
       in
      (foldr (sup_set (equal_list (equal_option _A)))
         (maps (fun (t, rel) ->
                 (if less_eq_nat (left i) (minus_nat nt t) then [rel] else []))
           auxa)
         bot_set,
        auxa));;

let rec mbuf2t_take
  f z x2 ts = match f, z, x2, ts with
    f, z, (x :: xs, y :: ys), t :: ts -> mbuf2t_take f (f x y t z) (xs, ys) ts
    | f, z, ([], ys), ts -> (z, (([], ys), ts))
    | f, z, (xs, []), ts -> (z, ((xs, []), ts))
    | f, z, (xs, ys), [] -> (z, ((xs, ys), []));;

let rec mprev_next
  i x1 ts = match i, x1, ts with i, [], ts -> ([], ([], ts))
    | i, v :: va, [] -> ([], (v :: va, []))
    | i, v :: va, [t] -> ([], (v :: va, [t]))
    | i, x :: xs, ta :: t :: ts ->
        (let a = mprev_next i xs (t :: ts) in
         let (ys, aa) = a in
          ((if less_eq_nat (left i) (minus_nat t ta) &&
                 less_eq_enat (Enat (minus_nat t ta)) (right i)
             then x else empty_table) ::
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

let rec eval_until
  i nt x2 = match i, nt, x2 with i, nt, [] -> ([], [])
    | i, nt, (t, (a1, a2)) :: aux ->
        (if less_enat (plus_enat (Enat t) (right i)) (Enat nt)
          then (let a = eval_until i nt aux in
                let (xs, aa) = a in
                 (a2 :: xs, aa))
          else ([], (t, (a1, a2)) :: aux));;

let rec mbuf2_add xsa ysa (xs, ys) = (xs @ xsa, ys @ ysa);;

let rec meval _A
  n t db x3 = match n, t, db, x3 with
    n, t, db, MUntil (pos, phi, i, psi, buf, nts, aux) ->
      (let (xs, phia) = meval _A n t db phi in
       let (ys, psia) = meval _A n t db psi in
       let (auxa, (bufa, ntsa)) =
         mbuf2t_take (update_until _A i pos) aux (mbuf2_add xs ys buf)
           (nts @ [t])
         in
       let (zs, auxb) =
         eval_until i (match ntsa with [] -> t | nt :: _ -> nt) auxa in
        (zs, MUntil (pos, phia, i, psia, bufa, ntsa, auxb)))
    | n, t, db, MSince (pos, phi, i, psi, buf, nts, aux) ->
        (let (xs, phia) = meval _A n t db phi in
         let (ys, psia) = meval _A n t db psi in
         let a =
           mbuf2t_take
             (fun r1 r2 ta (zs, auxa) ->
               (let a = update_since _A i pos r1 r2 ta auxa in
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
        (let (xs, phia) = meval _A n t db phi in
         let (xsa, firsta) =
           (match (xs, first) with ([], b) -> ([], b)
             | (_ :: xsa, true) -> (xsa, false)
             | (x :: xsa, false) -> (x :: xsa, false))
           in
         let (zs, (_, ntsa)) = mprev_next i xsa (nts @ [t]) in
          (zs, MNext (i, phia, firsta, ntsa)))
    | n, t, db, MPrev (i, phi, first, buf, nts) ->
        (let (xs, phia) = meval _A n t db phi in
         let (zs, (bufa, ntsa)) = mprev_next i (buf @ xs) (nts @ [t]) in
          ((if first then empty_table :: zs else zs),
            MPrev (i, phia, false, bufa, ntsa)))
    | n, t, db, MExists phi ->
        (let (xs, phia) = meval _A (suc n) t db phi in
          (map (image (equal_list (equal_option _A)) tl) xs, MExists phia))
    | n, t, db, MOr (phi, psi, buf) ->
        (let (xs, phia) = meval _A n t db phi in
         let (ys, psia) = meval _A n t db psi in
         let (zs, bufa) =
           mbuf2_take (sup_set (equal_list (equal_option _A)))
             (mbuf2_add xs ys buf)
           in
          (zs, MOr (phia, psia, bufa)))
    | n, t, db, MAnd (phi, pos, psi, buf) ->
        (let (xs, phia) = meval _A n t db phi in
         let (ys, psia) = meval _A n t db psi in
         let (zs, bufa) =
           mbuf2_take (fun r1 -> join _A r1 pos) (mbuf2_add xs ys buf) in
          (zs, MAnd (phia, pos, psia, bufa)))
    | n, t, db, MPred (e, ts) ->
        ([these (equal_list (equal_option _A))
            (image (equal_option (equal_list (equal_option _A)))
              (comp (map_option (fun f -> tabulate f zero_nat n))
                (matcha _A ts))
              (sup_seta (equal_list _A)
                (image (equal_set (equal_list _A))
                  (fun (ea, x) ->
                    (if equal_lista equal_char e ea
                      then insert (equal_list _A) x bot_set else bot_set))
                  db)))],
          MPred (e, ts))
    | n, t, db, MRel rel -> ([rel], MRel rel);;

let rec neq_rel _A
  n x1 x2 = match n, x1, x2 with
    n, Const x, Const y -> (if eq _A x y then empty_table else unit_table _A n)
    | n, Var x, Var y ->
        (if equal_nata x y then empty_table else failwith "undefined")
    | uu, Var v, Const va -> failwith "undefined"
    | uu, Const va, Var v -> failwith "undefined";;

let rec singleton_table _A
  n i x =
    insert (equal_list (equal_option _A))
      (tabulate (fun j -> (if equal_nata i j then Some x else None)) zero_nat n)
      bot_set;;

let rec eq_rel _A
  n x1 x2 = match n, x1, x2 with
    n, Const x, Const y -> (if eq _A x y then unit_table _A n else empty_table)
    | n, Var x, Const y -> singleton_table _A n x y
    | n, Const x, Var y -> singleton_table _A n y x
    | n, Var x, Var y -> failwith "undefined";;

let rec minit0 _A
  n x1 = match n, x1 with
    n, Neg phi ->
      (match phi with Eq (t1, t2) -> MRel (neq_rel _A n t1 t2)
        | Disj (Neg phia, psi) ->
          (match psi
            with Pred (list1, list2) ->
              MAnd (minit0 _A n phia, false, minit0 _A n (Pred (list1, list2)),
                     ([], []))
            | Eq (trm1, trm2) ->
              MAnd (minit0 _A n phia, false, minit0 _A n (Eq (trm1, trm2)),
                     ([], []))
            | Neg psia ->
              MAnd (minit0 _A n phia, true, minit0 _A n psia, ([], []))
            | Disj (formula1, formula2) ->
              MAnd (minit0 _A n phia, false,
                     minit0 _A n (Disj (formula1, formula2)), ([], []))
            | Exists formula ->
              MAnd (minit0 _A n phia, false, minit0 _A n (Exists formula),
                     ([], []))
            | Prev (i, formula) ->
              MAnd (minit0 _A n phia, false, minit0 _A n (Prev (i, formula)),
                     ([], []))
            | Next (i, formula) ->
              MAnd (minit0 _A n phia, false, minit0 _A n (Next (i, formula)),
                     ([], []))
            | Since (formula1, i, formula2) ->
              MAnd (minit0 _A n phia, false,
                     minit0 _A n (Since (formula1, i, formula2)), ([], []))
            | Until (formula1, i, formula2) ->
              MAnd (minit0 _A n phia, false,
                     minit0 _A n (Until (formula1, i, formula2)), ([], []))))
    | n, Eq (t1, t2) -> MRel (eq_rel _A n t1 t2)
    | n, Pred (e, ts) -> MPred (e, ts)
    | n, Disj (phi, psi) -> MOr (minit0 _A n phi, minit0 _A n psi, ([], []))
    | n, Exists phi -> MExists (minit0 _A (suc n) phi)
    | n, Prev (i, phi) -> MPrev (i, minit0 _A n phi, true, [], [])
    | n, Next (i, phi) -> MNext (i, minit0 _A n phi, true, [])
    | n, Since (phi, i, psi) ->
        (match phi
          with Pred (_, _) ->
            MSince (true, minit0 _A n phi, i, minit0 _A n psi, ([], []), [], [])
          | Eq (_, _) ->
            MSince (true, minit0 _A n phi, i, minit0 _A n psi, ([], []), [], [])
          | Neg phia ->
            MSince
              (false, minit0 _A n phia, i, minit0 _A n psi, ([], []), [], [])
          | Disj (_, _) ->
            MSince (true, minit0 _A n phi, i, minit0 _A n psi, ([], []), [], [])
          | Exists _ ->
            MSince (true, minit0 _A n phi, i, minit0 _A n psi, ([], []), [], [])
          | Prev (_, _) ->
            MSince (true, minit0 _A n phi, i, minit0 _A n psi, ([], []), [], [])
          | Next (_, _) ->
            MSince (true, minit0 _A n phi, i, minit0 _A n psi, ([], []), [], [])
          | Since (_, _, _) ->
            MSince (true, minit0 _A n phi, i, minit0 _A n psi, ([], []), [], [])
          | Until (_, _, _) ->
            MSince
              (true, minit0 _A n phi, i, minit0 _A n psi, ([], []), [], []))
    | n, Until (phi, i, psi) ->
        (match phi
          with Pred (_, _) ->
            MUntil (true, minit0 _A n phi, i, minit0 _A n psi, ([], []), [], [])
          | Eq (_, _) ->
            MUntil (true, minit0 _A n phi, i, minit0 _A n psi, ([], []), [], [])
          | Neg phia ->
            MUntil
              (false, minit0 _A n phia, i, minit0 _A n psi, ([], []), [], [])
          | Disj (_, _) ->
            MUntil (true, minit0 _A n phi, i, minit0 _A n psi, ([], []), [], [])
          | Exists _ ->
            MUntil (true, minit0 _A n phi, i, minit0 _A n psi, ([], []), [], [])
          | Prev (_, _) ->
            MUntil (true, minit0 _A n phi, i, minit0 _A n psi, ([], []), [], [])
          | Next (_, _) ->
            MUntil (true, minit0 _A n phi, i, minit0 _A n psi, ([], []), [], [])
          | Since (_, _, _) ->
            MUntil (true, minit0 _A n phi, i, minit0 _A n psi, ([], []), [], [])
          | Until (_, _, _) ->
            MUntil
              (true, minit0 _A n phi, i, minit0 _A n psi, ([], []), [], []));;

let rec minit _A
  phi = (let n = nfv phi in Mstate_ext (zero_nat, minit0 _A n phi, n, ()));;

let rec size_list x = gen_length zero_nat x;;

let rec mstate_n (Mstate_ext (mstate_i, mstate_m, mstate_n, more)) = mstate_n;;

let rec mstate_m (Mstate_ext (mstate_i, mstate_m, mstate_n, more)) = mstate_m;;

let rec mstate_i (Mstate_ext (mstate_i, mstate_m, mstate_n, more)) = mstate_i;;

let rec mstep _A
  tdb st =
    (let (xs, m) = meval _A (mstate_n st) (snd tdb) (fst tdb) (mstate_m st) in
      (sup_seta (equal_prod equal_nat (equal_list (equal_option _A)))
         (Set (map (fun (i, a) ->
                     image (equal_prod equal_nat (equal_list (equal_option _A)))
                       (fun aa -> (i, aa)) a)
                (enumerate (mstate_i st) xs))),
        Mstate_ext
          (plus_nat (mstate_i st) (size_list xs), m, mstate_n st, ())));;

let one_enat : enat = Enat one_nat;;

let rec future_reach
  = function Pred (uu, uv) -> zero_enat
    | Eq (uw, ux) -> zero_enat
    | Neg phi -> future_reach phi
    | Disj (phi, psi) -> max ord_enat (future_reach phi) (future_reach psi)
    | Exists phi -> future_reach phi
    | Prev (i, phi) -> minus_enat (future_reach phi) (Enat (left i))
    | Next (i, phi) ->
        plus_enat (plus_enat (future_reach phi) (right i)) one_enat
    | Since (phi, i, psi) ->
        max ord_enat (future_reach phi)
          (minus_enat (future_reach psi) (Enat (left i)))
    | Until (phi, i, psi) ->
        plus_enat
          (plus_enat (max ord_enat (future_reach phi) (future_reach psi))
            (right i))
          one_enat;;

let rec is_Const = function Var x1 -> false
                   | Const x2 -> true;;

let rec equal_enat x0 x1 = match x0, x1 with Enat nat, Infinity_enat -> false
                     | Infinity_enat, Enat nat -> false
                     | Enat nata, Enat nat -> equal_nata nata nat
                     | Infinity_enat, Infinity_enat -> true;;

let rec monitorable_formula_exec
  = function Eq (t1, t2) -> is_Const t1 || is_Const t2
    | Neg (Eq (Const x, Const y)) -> true
    | Neg (Eq (Var x, Var y)) -> equal_nata x y
    | Pred (e, ts) -> true
    | Neg (Disj (Neg phi, Neg psi)) ->
        monitorable_formula_exec phi && monitorable_formula_exec psi
    | Neg (Disj (Neg phi, Pred (v, va))) ->
        less_eq_set equal_nat (fv zero_nat (Pred (v, va))) (fv zero_nat phi) &&
          (monitorable_formula_exec phi &&
            monitorable_formula_exec (Pred (v, va)))
    | Neg (Disj (Neg phi, Eq (v, va))) ->
        less_eq_set equal_nat (fv zero_nat (Eq (v, va))) (fv zero_nat phi) &&
          (monitorable_formula_exec phi &&
            monitorable_formula_exec (Eq (v, va)))
    | Neg (Disj (Neg phi, Disj (v, va))) ->
        less_eq_set equal_nat (fv zero_nat (Disj (v, va))) (fv zero_nat phi) &&
          (monitorable_formula_exec phi &&
            monitorable_formula_exec (Disj (v, va)))
    | Neg (Disj (Neg phi, Exists v)) ->
        less_eq_set equal_nat (fv zero_nat (Exists v)) (fv zero_nat phi) &&
          (monitorable_formula_exec phi && monitorable_formula_exec (Exists v))
    | Neg (Disj (Neg phi, Prev (v, va))) ->
        less_eq_set equal_nat (fv zero_nat (Prev (v, va))) (fv zero_nat phi) &&
          (monitorable_formula_exec phi &&
            monitorable_formula_exec (Prev (v, va)))
    | Neg (Disj (Neg phi, Next (v, va))) ->
        less_eq_set equal_nat (fv zero_nat (Next (v, va))) (fv zero_nat phi) &&
          (monitorable_formula_exec phi &&
            monitorable_formula_exec (Next (v, va)))
    | Neg (Disj (Neg phi, Since (v, va, vb))) ->
        less_eq_set equal_nat (fv zero_nat (Since (v, va, vb)))
          (fv zero_nat phi) &&
          (monitorable_formula_exec phi &&
            monitorable_formula_exec (Since (v, va, vb)))
    | Neg (Disj (Neg phi, Until (v, va, vb))) ->
        less_eq_set equal_nat (fv zero_nat (Until (v, va, vb)))
          (fv zero_nat phi) &&
          (monitorable_formula_exec phi &&
            monitorable_formula_exec (Until (v, va, vb)))
    | Disj (phi, psi) ->
        equal_seta equal_nat (fv zero_nat psi) (fv zero_nat phi) &&
          (monitorable_formula_exec phi && monitorable_formula_exec psi)
    | Exists phi -> monitorable_formula_exec phi
    | Prev (i, phi) -> monitorable_formula_exec phi
    | Next (i, phi) -> monitorable_formula_exec phi
    | Since (Neg phi, i, psi) ->
        less_eq_set equal_nat (fv zero_nat phi) (fv zero_nat psi) &&
          (monitorable_formula_exec phi && monitorable_formula_exec psi)
    | Since (Pred (v, va), i, psi) ->
        less_eq_set equal_nat (fv zero_nat (Pred (v, va))) (fv zero_nat psi) &&
          (monitorable_formula_exec (Pred (v, va)) &&
            monitorable_formula_exec psi)
    | Since (Eq (v, va), i, psi) ->
        less_eq_set equal_nat (fv zero_nat (Eq (v, va))) (fv zero_nat psi) &&
          (monitorable_formula_exec (Eq (v, va)) &&
            monitorable_formula_exec psi)
    | Since (Disj (v, va), i, psi) ->
        less_eq_set equal_nat (fv zero_nat (Disj (v, va))) (fv zero_nat psi) &&
          (monitorable_formula_exec (Disj (v, va)) &&
            monitorable_formula_exec psi)
    | Since (Exists v, i, psi) ->
        less_eq_set equal_nat (fv zero_nat (Exists v)) (fv zero_nat psi) &&
          (monitorable_formula_exec (Exists v) && monitorable_formula_exec psi)
    | Since (Prev (v, va), i, psi) ->
        less_eq_set equal_nat (fv zero_nat (Prev (v, va))) (fv zero_nat psi) &&
          (monitorable_formula_exec (Prev (v, va)) &&
            monitorable_formula_exec psi)
    | Since (Next (v, va), i, psi) ->
        less_eq_set equal_nat (fv zero_nat (Next (v, va))) (fv zero_nat psi) &&
          (monitorable_formula_exec (Next (v, va)) &&
            monitorable_formula_exec psi)
    | Since (Since (v, va, vb), i, psi) ->
        less_eq_set equal_nat (fv zero_nat (Since (v, va, vb)))
          (fv zero_nat psi) &&
          (monitorable_formula_exec (Since (v, va, vb)) &&
            monitorable_formula_exec psi)
    | Since (Until (v, va, vb), i, psi) ->
        less_eq_set equal_nat (fv zero_nat (Until (v, va, vb)))
          (fv zero_nat psi) &&
          (monitorable_formula_exec (Until (v, va, vb)) &&
            monitorable_formula_exec psi)
    | Until (Neg phi, i, psi) ->
        less_eq_set equal_nat (fv zero_nat phi) (fv zero_nat psi) &&
          (monitorable_formula_exec phi && monitorable_formula_exec psi)
    | Until (Pred (v, va), i, psi) ->
        less_eq_set equal_nat (fv zero_nat (Pred (v, va))) (fv zero_nat psi) &&
          (monitorable_formula_exec (Pred (v, va)) &&
            monitorable_formula_exec psi)
    | Until (Eq (v, va), i, psi) ->
        less_eq_set equal_nat (fv zero_nat (Eq (v, va))) (fv zero_nat psi) &&
          (monitorable_formula_exec (Eq (v, va)) &&
            monitorable_formula_exec psi)
    | Until (Disj (v, va), i, psi) ->
        less_eq_set equal_nat (fv zero_nat (Disj (v, va))) (fv zero_nat psi) &&
          (monitorable_formula_exec (Disj (v, va)) &&
            monitorable_formula_exec psi)
    | Until (Exists v, i, psi) ->
        less_eq_set equal_nat (fv zero_nat (Exists v)) (fv zero_nat psi) &&
          (monitorable_formula_exec (Exists v) && monitorable_formula_exec psi)
    | Until (Prev (v, va), i, psi) ->
        less_eq_set equal_nat (fv zero_nat (Prev (v, va))) (fv zero_nat psi) &&
          (monitorable_formula_exec (Prev (v, va)) &&
            monitorable_formula_exec psi)
    | Until (Next (v, va), i, psi) ->
        less_eq_set equal_nat (fv zero_nat (Next (v, va))) (fv zero_nat psi) &&
          (monitorable_formula_exec (Next (v, va)) &&
            monitorable_formula_exec psi)
    | Until (Since (v, va, vb), i, psi) ->
        less_eq_set equal_nat (fv zero_nat (Since (v, va, vb)))
          (fv zero_nat psi) &&
          (monitorable_formula_exec (Since (v, va, vb)) &&
            monitorable_formula_exec psi)
    | Until (Until (v, va, vb), i, psi) ->
        less_eq_set equal_nat (fv zero_nat (Until (v, va, vb)))
          (fv zero_nat psi) &&
          (monitorable_formula_exec (Until (v, va, vb)) &&
            monitorable_formula_exec psi)
    | Neg (Pred (va, vb)) -> false
    | Neg (Eq (Var vc, Const v)) -> false
    | Neg (Eq (Const v, Var vc)) -> false
    | Neg (Neg va) -> false
    | Neg (Disj (Pred (v, vc), vb)) -> false
    | Neg (Disj (Eq (v, vc), vb)) -> false
    | Neg (Disj (Disj (v, vc), vb)) -> false
    | Neg (Disj (Exists v, vb)) -> false
    | Neg (Disj (Prev (v, vc), vb)) -> false
    | Neg (Disj (Next (v, vc), vb)) -> false
    | Neg (Disj (Since (v, vc, vd), vb)) -> false
    | Neg (Disj (Until (v, vc, vd), vb)) -> false
    | Neg (Exists va) -> false
    | Neg (Prev (va, vb)) -> false
    | Neg (Next (va, vb)) -> false
    | Neg (Since (va, vb, vc)) -> false
    | Neg (Until (va, vb, vc)) -> false;;

let rec monitorable_formula phi = monitorable_formula_exec phi;;

let rec mmonitorable
  phi = monitorable_formula phi &&
          not (equal_enat (future_reach phi) Infinity_enat);;

let rec minit_safe _A
  phi = (if mmonitorable phi then minit _A phi else failwith "undefined");;

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

let rec nat_of_integer k = Nat (max ord_integer Big_int.zero_big_int k);;

end;; (*struct Monpoly*)
