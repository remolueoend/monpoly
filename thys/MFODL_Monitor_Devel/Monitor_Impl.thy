(*<*)
theory Monitor_Impl
  imports Monitor
    Optimized_Agg_Temporal
    Optimized_Agg
    Optimized_MTL
    "HOL-Library.Code_Target_Nat"
    Containers.Containers
    "Generic_Join_Devel.Proj_Code"
begin
(*>*)

declare Let_def[simp del]

section \<open>Data refinement\<close>

typedef 'a mbuf_t = "UNIV :: 'a list set" ..

setup_lifting type_definition_mbuf_t

instantiation mbuf_t :: (type) size
begin

lift_definition size_mbuf_t :: "'a mbuf_t \<Rightarrow> nat" is "length" .

instance ..

end

lift_definition mbuf_t_empty :: "'a mbuf_t" is "[]" .

lift_definition mbuf_t_is_empty :: "'a mbuf_t \<Rightarrow> bool" is "\<lambda>xs. xs = []" .

lift_definition mbuf_t_Cons :: "'a \<Rightarrow> 'a mbuf_t \<Rightarrow> 'a mbuf_t" is Cons .

no_notation SCons (infixr "##" 65)
notation mbuf_t_Cons (infixr "##" 65)

lift_definition mbuf_t_append :: "'a mbuf_t \<Rightarrow> 'a list \<Rightarrow> 'a mbuf_t" is append .

notation mbuf_t_append (infixr "@@" 65)

lift_definition mbuf_t_cases :: "'a mbuf_t \<Rightarrow> 'a option \<times> 'a mbuf_t" is
  "\<lambda>xs. case xs of [] \<Rightarrow> (None, xs) | y # ys \<Rightarrow> (Some y, ys)" .

lemma Rep_mbuf_t_cases[simp]:
  "mbuf_t_cases xs = (None, xs') \<Longrightarrow> Rep_mbuf_t xs = []"
  "mbuf_t_cases xs = (None, xs') \<Longrightarrow> Rep_mbuf_t xs' = []"
  "mbuf_t_cases xs = (Some x, xs') \<Longrightarrow> Rep_mbuf_t xs = x # Rep_mbuf_t xs'"
  subgoal by transfer (auto split: option.splits list.splits)
  subgoal by transfer (auto split: option.splits list.splits)
  subgoal by transfer (auto split: option.splits list.splits)
  done

lemma mbuf_t_cases_size[termination_simp]: "(Some x, xs') = mbuf_t_cases xs \<Longrightarrow> size xs' < size xs"
  by transfer (auto split: list.splits)

lift_definition MBuf2_t :: "'a queue \<Rightarrow> 'a mbuf_t" is "linearize" .

code_datatype MBuf2_t

declare MBuf2_t.rep_eq[code]

lemma mbuf_t_empty_code[code]: "mbuf_t_empty = MBuf2_t empty_queue"
  by transfer' (auto simp: empty_queue_rep)

lemma mbuf_t_is_empty_code[code]: "mbuf_t_is_empty (MBuf2_t xs) = is_empty xs"
  by transfer' (auto simp: is_empty_alt)

lemma mbuf_t_Cons_code[code]: "mbuf_t_Cons x (MBuf2_t xs) = MBuf2_t (prepend_queue x xs)"
  by transfer' (auto simp: prepend_queue_rep)

lemma mbuf_t_append_code[code]: "mbuf_t_append (MBuf2_t xs) ys = MBuf2_t (fold append_queue ys xs)"
  apply transfer'
  subgoal for xs ys
  proof (induction ys arbitrary: xs)
    case (Cons y ys)
    show ?case
      using Cons[of "append_queue y xs"]
      by (auto simp: append_queue_rep)
  qed simp
  done

lemma mbuf_t_cases_code[code]: "mbuf_t_cases (MBuf2_t xs) = (case safe_hd xs of (None, xs') \<Rightarrow> (None, MBuf2_t xs')
  | (Some x, xs') \<Rightarrow> (Some x, MBuf2_t (tl_queue xs')))"
  by transfer' (auto simp: tl_queue_rep split: list.splits prod.splits option.splits dest: safe_hd_rep)

type_synonym 'a mebuf2 = "'a table mbuf_t \<times> 'a table mbuf_t"
type_synonym 'a mebufn = "'a table mbuf_t list"
type_synonym 'a mebuf2S = "'a table mbuf_t \<times> 'a table mbuf_t \<times> ts mbuf_t \<times> bool"

datatype (dead 'msaux, dead 'muaux) meformula =
  MRel "event_data table"
  | MPred Formula.name "Formula.trm list" pred_mode
  | MLet Formula.name nat "('msaux, 'muaux) meformula" "('msaux, 'muaux) meformula"
  | MLetPast Formula.name nat "('msaux, 'muaux) meformula" "('msaux, 'muaux) meformula" nat "event_data table option"
  | MAnd "nat set" "('msaux, 'muaux) meformula" bool "nat set" "('msaux, 'muaux) meformula" "event_data mebuf2"
  | MAndAssign "('msaux, 'muaux) meformula" "nat \<times> Formula.trm"
  | MAndRel "('msaux, 'muaux) meformula" "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm"
  | MAnds "nat set list" "nat set list" "('msaux, 'muaux) meformula list" "event_data mebufn"
  | MOr "('msaux, 'muaux) meformula" "('msaux, 'muaux) meformula" "event_data mebuf2"
  | MNeg "('msaux, 'muaux) meformula"
  | MExists "('msaux, 'muaux) meformula"
  | MAgg aggargs "('msaux, 'muaux) meformula"
  | MPrev \<I> "('msaux, 'muaux) meformula" bool "event_data table mbuf_t" "ts mbuf_t"
  | MNext \<I> "('msaux, 'muaux) meformula" bool "ts mbuf_t"
  | MSince args "('msaux, 'muaux) meformula" "('msaux, 'muaux) meformula" "event_data mebuf2S" "'msaux"
  | MUntil args "('msaux, 'muaux) meformula" "('msaux, 'muaux) meformula" "event_data mebuf2" "ts mbuf_t" ts "'muaux"
  | MMatchP \<I> "mregex" "mregex list" "('msaux, 'muaux) meformula list" "event_data mebufn" "ts mbuf_t" "event_data mr\<delta>aux"
  | MMatchF \<I> "mregex" "mregex list" "('msaux, 'muaux) meformula list" "event_data mebufn" "ts mbuf_t" ts "event_data ml\<delta>aux"
  | MTP mtrm nat
  | MTS mtrm

fun Rep_meformula :: "('msaux, 'muaux) meformula \<Rightarrow> ('msaux, 'muaux) mformula" where
  "Rep_meformula (MRel rel) = mformula.MRel rel"
| "Rep_meformula (MPred e tms mode) = mformula.MPred e tms mode"
| "Rep_meformula (MLet p m \<phi> \<psi>) = mformula.MLet p m (Rep_meformula \<phi>) (Rep_meformula \<psi>)"
| "Rep_meformula (MLetPast p m \<phi> \<psi> i buf) = mformula.MLetPast p m (Rep_meformula \<phi>) (Rep_meformula \<psi>) i buf"
| "Rep_meformula (MAnd A_\<phi> \<phi> pos A_\<psi> \<psi> buf) = mformula.MAnd A_\<phi> (Rep_meformula \<phi>) pos A_\<psi> (Rep_meformula \<psi>) (map_prod Rep_mbuf_t Rep_mbuf_t buf)"
| "Rep_meformula (MAndAssign \<phi> conf) = mformula.MAndAssign (Rep_meformula \<phi>) conf"
| "Rep_meformula (MAndRel \<phi> conf) = mformula.MAndRel (Rep_meformula \<phi>) conf"
| "Rep_meformula (MAnds A_pos A_neg L buf) = mformula.MAnds A_pos A_neg (map Rep_meformula L) (map Rep_mbuf_t buf)"
| "Rep_meformula (MOr \<phi> \<psi> buf) = mformula.MOr (Rep_meformula \<phi>) (Rep_meformula \<psi>) (map_prod Rep_mbuf_t Rep_mbuf_t buf)"
| "Rep_meformula (MNeg \<phi>) = mformula.MNeg (Rep_meformula \<phi>)"
| "Rep_meformula (MExists \<phi>) = mformula.MExists (Rep_meformula \<phi>)"
| "Rep_meformula (MAgg args \<phi>) = mformula.MAgg args (Rep_meformula \<phi>)"
| "Rep_meformula (MPrev I \<phi> first buf nts) = mformula.MPrev I (Rep_meformula \<phi>) first (Rep_mbuf_t buf) (Rep_mbuf_t nts)"
| "Rep_meformula (MNext I \<phi> first nts) = mformula.MNext I (Rep_meformula \<phi>) first (Rep_mbuf_t nts)"
| "Rep_meformula (MSince args \<phi> \<psi> buf aux) = mformula.MSince args (Rep_meformula \<phi>) (Rep_meformula \<psi>)
    (case buf of (a, b, c, d) \<Rightarrow> (Rep_mbuf_t a, Rep_mbuf_t b, Rep_mbuf_t c, d)) aux"
| "Rep_meformula (MUntil args \<phi> \<psi> buf nts t aux) = mformula.MUntil args (Rep_meformula \<phi>) (Rep_meformula \<psi>)
    (map_prod Rep_mbuf_t Rep_mbuf_t buf) (Rep_mbuf_t nts) t aux"
| "Rep_meformula (MMatchP I mr mrs \<phi>s buf nts aux) = mformula.MMatchP I mr mrs (map Rep_meformula \<phi>s)
    (map Rep_mbuf_t buf) (Rep_mbuf_t nts) aux"
| "Rep_meformula (MMatchF I mr mrs \<phi>s buf nts t aux) = mformula.MMatchF I mr mrs (map Rep_meformula \<phi>s)
    (map Rep_mbuf_t buf) (Rep_mbuf_t nts) t aux"
| "Rep_meformula (MTP mt i) = mformula.MTP mt i"
| "Rep_meformula (MTS mt) = mformula.MTS mt"

lemma size_list_cong: "xs = ys \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> f x = g x) \<Longrightarrow> size_list f xs = size_list g ys"
  by (induct xs arbitrary: ys) auto

lemma size_Rep_meformula[simp]: "size (Rep_meformula \<psi>) = size \<psi>"
  by (induction \<psi> rule: Rep_meformula.induct) (auto simp: comp_def cong: size_list_cong)

code_datatype Rep_meformula

abbreviation (input) "init_mebuf2S \<equiv> (mbuf_t_empty, mbuf_t_empty, mbuf_t_empty, False)"

function (in maux) (sequential) meinit0 :: "nat \<Rightarrow> ty Formula.formula \<Rightarrow> ('msaux, 'muaux) meformula" where
  "meinit0 n (Formula.Neg \<phi>) = (if fv \<phi> = {} then MNeg (meinit0 n \<phi>) else MRel empty_table)"
| "meinit0 n (Formula.Eq t1 t2) = MRel (eq_rel n t1 t2)"
| "meinit0 n (Formula.Pred e ts) = MPred e ts (pred_mode_of n ts)"
| "meinit0 n (Formula.Let p \<phi> \<psi>) = MLet p (Formula.nfv \<phi>) (meinit0 (Formula.nfv \<phi>) \<phi>) (meinit0 n \<psi>)"
| "meinit0 n (Formula.LetPast p \<phi> \<psi>) = MLetPast p (Formula.nfv \<phi>) (meinit0 (Formula.nfv \<phi>) \<phi>) (meinit0 n \<psi>) 0 None"
| "meinit0 n (Formula.Or \<phi> \<psi>) = MOr (meinit0 n \<phi>) (meinit0 n \<psi>) (mbuf_t_empty, mbuf_t_empty)"
| "meinit0 n (Formula.And \<phi> \<psi>) = (if safe_assignment (fv \<phi>) \<psi> then
      MAndAssign (meinit0 n \<phi>) (split_assignment (fv \<phi>) \<psi>)
    else if safe_formula \<psi> then
      MAnd (fv \<phi>) (meinit0 n \<phi>) True (fv \<psi>) (meinit0 n \<psi>) (mbuf_t_empty, mbuf_t_empty)
    else if is_constraint \<psi> then
      MAndRel (meinit0 n \<phi>) (split_constraint \<psi>)
    else (case \<psi> of Formula.Neg \<psi> \<Rightarrow>
      MAnd (fv \<phi>) (meinit0 n \<phi>) False (fv \<psi>) (meinit0 n \<psi>) (mbuf_t_empty, mbuf_t_empty)
      | _ \<Rightarrow> MRel empty_table))"
| "meinit0 n (Formula.Ands l) = (let (pos, neg) = partition safe_formula l in
    let mpos = map (meinit0 n) pos in
    let mneg = map (meinit0 n) (map remove_neg neg) in
    let vpos = map fv pos in
    let vneg = map fv neg in
    MAnds vpos vneg (mpos @ mneg) (replicate (length l) mbuf_t_empty))"
| "meinit0 n (Formula.Exists t \<phi>) = MExists (meinit0 (Suc n) \<phi>)"
| "meinit0 n (Formula.Agg y \<omega> tys f \<phi>) = 
    (let default = MAgg (init_aggargs (fv \<phi>) n (fv \<phi> \<subseteq> {0..<length tys}) y \<omega> tys f) (meinit0 ((length tys) + n) \<phi>) in
    (case \<phi> of Formula.Since \<phi>' I \<psi>' \<Rightarrow>
        let agg = Some (init_aggargs (fv \<phi>) n (fv \<phi> \<subseteq> {0..<length tys}) y \<omega> tys f) in
        (let args = (\<lambda>k. (init_args I ((length tys) + n) (Formula.fv \<phi>') (Formula.fv \<psi>') k agg)) in
            if safe_formula \<phi>'
            then MSince (args True) (meinit0 ((length tys) + n) \<phi>') (meinit0 ((length tys) + n) \<psi>') init_mebuf2S (init_msaux (args True))
            else (case \<phi>' of
              Formula.Neg \<phi>'' \<Rightarrow> MSince (args False) (meinit0 ((length tys) + n) \<phi>'') (meinit0 ((length tys) + n) \<psi>') init_mebuf2S (init_msaux (args False))
              | _ \<Rightarrow> MRel empty_table))
     | Formula.Until \<phi>' I \<psi>' \<Rightarrow>
        let agg = Some (init_aggargs (fv \<phi>) n (fv \<phi> \<subseteq> {0..<length tys}) y \<omega> tys f) in
        (let args = (\<lambda>k. (init_args I ((length tys) + n) (Formula.fv \<phi>') (Formula.fv \<psi>') k agg)) in
            if safe_formula \<phi>'
            then MUntil (args True) (meinit0 ((length tys) + n) \<phi>') (meinit0 ((length tys) + n) \<psi>') (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty 0 (init_muaux (args True))
             else (case \<phi>' of
              Formula.Neg \<phi>'' \<Rightarrow> MUntil (args False) (meinit0 ((length tys) + n) \<phi>'') (meinit0 ((length tys) + n) \<psi>') (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty 0 (init_muaux (args False))
              | _ \<Rightarrow> MRel empty_table))
     | _ \<Rightarrow> default))"
| "meinit0 n (Formula.Prev I \<phi>) = MPrev I (meinit0 n \<phi>) True mbuf_t_empty mbuf_t_empty"
| "meinit0 n (Formula.Next I \<phi>) = MNext I (meinit0 n \<phi>) True mbuf_t_empty"
| "meinit0 n (Formula.Since \<phi> I \<psi>) = 
    (if safe_formula \<phi>
    then MSince (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True None) (meinit0 n \<phi>) (meinit0 n \<psi>) init_mebuf2S (init_msaux (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True None))
    else (case \<phi> of
      Formula.Neg \<phi>' \<Rightarrow> MSince (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) False None) (meinit0 n \<phi>') (meinit0 n \<psi>) init_mebuf2S (init_msaux (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) False None))
    | _ \<Rightarrow> MRel empty_table))"
| "meinit0 n (Formula.Until \<phi> I \<psi>) = 
    (if safe_formula \<phi>
    then MUntil (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True None) (meinit0 n \<phi>) (meinit0 n \<psi>) (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty 0 (init_muaux (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True None))
    else (case \<phi> of
      Formula.Neg \<phi>' \<Rightarrow> MUntil (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) False None) (meinit0 n \<phi>') (meinit0 n \<psi>) (mbuf_t_empty, mbuf_t_empty) mbuf_t_empty 0 (init_muaux (init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) False None))
    | _ \<Rightarrow> MRel empty_table))"
| "meinit0 n (Formula.MatchP I r) =
    (let (mr, \<phi>s) = to_mregex r
    in MMatchP I mr (sorted_list_of_set (RPDs mr)) (map (meinit0 n) \<phi>s) (replicate (length \<phi>s) mbuf_t_empty) mbuf_t_empty [])"
| "meinit0 n (Formula.MatchF I r) =
    (let (mr, \<phi>s) = to_mregex r
    in MMatchF I mr (sorted_list_of_set (LPDs mr)) (map (meinit0 n) \<phi>s) (replicate (length \<phi>s) mbuf_t_empty) mbuf_t_empty 0 [])"
| "meinit0 n (Formula.TP t) = MTP (mtrm_of_trm t) 0"
| "meinit0 n (Formula.TS t) = MTS (mtrm_of_trm t)"
| "meinit0 n _ = MRel empty_table"
  by pat_completeness auto 
termination (in maux)
  by (relation "measure (\<lambda>(_, \<phi>). size \<phi>)") (auto simp: less_Suc_eq_le size_list_estimation' size_remove_neg
      dest!: to_mregex_ok[OF sym] atms_size) 

lemma (in maux) minit0_code[code]: "minit0 n \<phi> = Rep_meformula (meinit0 n \<phi>)"
  by (induction n \<phi> rule: meinit0.induct) (auto simp: init_since_def init_until_def
      mbuf_t_empty.rep_eq Let_def split: formula.splits prod.splits)

definition mestate :: "nat \<Rightarrow> nat \<Rightarrow> ('a, 'b) mformula \<Rightarrow> nat \<Rightarrow> ts queue \<Rightarrow> 'c \<Rightarrow> ('a, 'b, 'c) mstate_ext" where
  "mestate i j m n t \<zeta> =
    \<lparr>mstate_i = i, mstate_j = j, mstate_m = m, mstate_n = n, mstate_t = linearize t, \<dots> = \<zeta>\<rparr>"

code_datatype mestate

lemma (in maux) minit_code[code]: "minit \<phi> = (let n = Formula.nfv \<phi> in mestate 0 0 (minit0 n \<phi>) n empty_queue ())"
  by (auto simp: minit_def Let_def mestate_def empty_queue_rep)

fun meprev_next :: "\<I> \<Rightarrow> event_data table mbuf_t \<Rightarrow> ts mbuf_t \<Rightarrow> event_data table list \<times> event_data table mbuf_t \<times> ts mbuf_t" where
  "meprev_next I xs ts = (case mbuf_t_cases xs of (None, xs') \<Rightarrow> ([], mbuf_t_empty, ts)
  | (Some x, xs') \<Rightarrow> (case mbuf_t_cases ts of (None, ts') \<Rightarrow> ([], x ## xs', mbuf_t_empty)
  | (Some t, ts') \<Rightarrow> (case mbuf_t_cases ts' of (None, ts'') \<Rightarrow> ([], x ## xs', t ## mbuf_t_empty)
  | (Some t', ts'') \<Rightarrow> (let (ys, zs) = meprev_next I xs' (t' ## ts'')
    in ((if mem I ((t' - t)) then x else empty_table) # ys, zs)))))"

lemma meprev_next: "meprev_next I xs ts = (zs, xs', ts') \<Longrightarrow> mprev_next I (Rep_mbuf_t xs) (Rep_mbuf_t ts) =
  (zs, Rep_mbuf_t xs', Rep_mbuf_t ts')"
proof (induction I xs ts arbitrary: zs xs' ts' rule: meprev_next.induct)
  case (1 I xs ts)
  obtain xo xs'' where xs_def: "mbuf_t_cases xs = (xo, xs'')"
    by fastforce
  obtain to ts'' where ts_def: "mbuf_t_cases ts = (to, ts'')"
    by fastforce
  obtain to' ts''' where ts''_def: "mbuf_t_cases ts'' = (to', ts''')"
    by fastforce
  show ?case
    using 1
    by (cases xo; cases to; cases to')
       (auto simp: xs_def ts_def ts''_def mbuf_t_empty.rep_eq mbuf_t_Cons.rep_eq split: prod.splits)
qed

fun mebuf2_add :: "event_data table list \<Rightarrow> event_data table list \<Rightarrow> event_data mebuf2 \<Rightarrow> event_data mebuf2" where
  "mebuf2_add xs' ys' (xs, ys) = (xs @@ xs', ys @@ ys')"

lemma mbuf2_add: "mbuf2_add xs ys (map_prod Rep_mbuf_t Rep_mbuf_t buf) = map_prod Rep_mbuf_t Rep_mbuf_t (mebuf2_add xs ys buf)"
  by (cases buf) (auto simp: mbuf_t_append.rep_eq)

fun mebuf2S_add :: "event_data table list \<Rightarrow> event_data table list \<Rightarrow> ts list \<Rightarrow> event_data mebuf2S \<Rightarrow> event_data mebuf2S" where
  "mebuf2S_add xs' ys' ts' (xs, ys, ts, skew) = (xs @@ xs', ys @@ ys', ts @@ ts', skew)"

fun mebuf2_take :: "(event_data table \<Rightarrow> event_data table \<Rightarrow> 'b) \<Rightarrow> event_data mebuf2 \<Rightarrow> 'b list \<times> event_data mebuf2" where
  "mebuf2_take f (xs, ys) = (case mbuf_t_cases xs of (None, xs') \<Rightarrow> ([], (xs', ys)) | (Some x, xs') \<Rightarrow>
    (case mbuf_t_cases ys of (None, ys') \<Rightarrow> ([], (x ## xs', ys')) | (Some y, ys') \<Rightarrow>
    let (zs, buf) = mebuf2_take f (xs', ys') in (f x y # zs, buf)))"

lemma mebuf2_take_aux: "mebuf2_take f (xs, ys) = (zs, (xs', ys')) \<Longrightarrow>
  mbuf2_take f (Rep_mbuf_t xs, Rep_mbuf_t ys) = (zs, (Rep_mbuf_t xs', Rep_mbuf_t ys'))"
proof (induction f "(xs, ys)" arbitrary: xs ys zs xs' ys' rule: mebuf2_take.induct)
  case (1 f xs ys)
  obtain x xs'' where xs_def: "mbuf_t_cases xs = (x, xs'')"
    by fastforce
  obtain y ys'' where ys_def: "mbuf_t_cases ys = (y, ys'')"
    by fastforce
  show ?case
    using 1 xs_def ys_def
    by (cases x; cases y) (auto simp: mbuf_t_Cons.rep_eq split: prod.splits)
qed

lemma mebuf2_take: "mebuf2_take f buf = (zs, buf') \<Longrightarrow>
  mbuf2_take f (map_prod Rep_mbuf_t Rep_mbuf_t buf) = (zs, (map_prod Rep_mbuf_t Rep_mbuf_t buf'))"
  using mebuf2_take_aux
  by (cases buf; cases buf') fastforce

fun mebuf2t_take :: "(event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow>
    event_data mebuf2 \<Rightarrow> ts \<Rightarrow> ts mbuf_t \<Rightarrow> 'b \<times> event_data mebuf2 \<times> ts \<times> ts mbuf_t" where
  "mebuf2t_take f z (xs, ys) t0 ts =
    (case mbuf_t_cases ts of (None, ts') \<Rightarrow> (z, (xs, ys), t0, ts') | (Some t, ts') \<Rightarrow>
    (case mbuf_t_cases xs of (None, xs') \<Rightarrow> (z, (xs', ys), t, t ## ts') | (Some x, xs') \<Rightarrow>
    (case mbuf_t_cases ys of (None, ys') \<Rightarrow> (z, (x ## xs', ys'), t, t ## ts') | (Some y, ys') \<Rightarrow>
    mebuf2t_take f (f x y t z) (xs', ys') t ts')))"

lemma mebuf2t_take_aux: "mebuf2t_take f z (xs, ys) t ts = (zs, (xs', ys'), nt, ts') \<Longrightarrow>
  mbuf2t_take f z (Rep_mbuf_t xs, Rep_mbuf_t ys) t (Rep_mbuf_t ts) = (zs, (Rep_mbuf_t xs', Rep_mbuf_t ys'), nt, Rep_mbuf_t ts')"
proof (induction f z "(xs, ys)" t ts arbitrary: xs ys rule: mebuf2t_take.induct)
  case (1 f z xs ys t ts)
  obtain x xs'' where xs_def: "mbuf_t_cases xs = (x, xs'')"
    by fastforce
  obtain y ys'' where ys_def: "mbuf_t_cases ys = (y, ys'')"
    by fastforce
  obtain t ts'' where ts_def: "mbuf_t_cases ts = (t, ts'')"
    by fastforce
  show ?case
    using 1 xs_def ys_def ts_def
    by (cases x; cases y; cases t) (auto simp: mbuf_t_Cons.rep_eq split: prod.splits list.splits)
qed

lemma mebuf2t_take: "mebuf2t_take f z buf t ts = (zs, buf', nt, nts) \<Longrightarrow>
  mbuf2t_take f z (map_prod Rep_mbuf_t Rep_mbuf_t buf) t (Rep_mbuf_t ts) = (zs, (map_prod Rep_mbuf_t Rep_mbuf_t buf'), nt, Rep_mbuf_t nts)"
  using mebuf2t_take_aux
  by (cases buf; cases buf') fastforce

context maux begin
context fixes args :: args begin

fun eeval_since :: "event_data table list \<Rightarrow> event_data mebuf2S \<Rightarrow> 'msaux \<Rightarrow>
  event_data table list \<times> event_data mebuf2S \<times> 'msaux" where
  "eeval_since rs (xs, ys, ts, skew) aux =
    (case mbuf_t_cases ys of (None, ys') \<Rightarrow>
      (case mbuf_t_cases xs of (Some x, xs') \<Rightarrow>
        (case mbuf_t_cases ts of (Some t, ts') \<Rightarrow>
    (if skew \<or> memL (args_ivl args) 0
    then (rev rs, (x ## xs', mbuf_t_empty, t ## ts', skew), aux)
    else (let aux' = join_msaux args x (add_new_ts_msaux args t aux)
      in (rev (result_msaux args aux' # rs), (xs', mbuf_t_empty, ts', True), aux')))
        | (None, ts') \<Rightarrow> (rev rs, (x ## xs', mbuf_t_empty, mbuf_t_empty, skew), aux))
      | (None, xs') \<Rightarrow> (rev rs, (mbuf_t_empty, mbuf_t_empty, ts, skew), aux))
    | (Some y, ys') \<Rightarrow>
      if skew then eeval_since rs (xs, ys', ts, False) (add_new_table_msaux args y aux) else
      (case mbuf_t_cases xs of (Some x, xs') \<Rightarrow>
        (case mbuf_t_cases ts of (Some t, ts') \<Rightarrow>
    (let aux' = add_new_table_msaux args y (join_msaux args x (add_new_ts_msaux args t aux))
    in eeval_since (result_msaux args aux' # rs) (xs', ys', ts', False) aux')
        | (None, ts') \<Rightarrow> (rev rs, (x ## xs', y ## ys', ts', skew), aux))
      | (None, xs') \<Rightarrow> (rev rs, (mbuf_t_empty, y ## ys', ts, skew), aux)))"

lemma eeval_since: "eeval_since rs (xs, ys, ts, skew) aux = (res, (xs', ys', ts', skew'), aux') \<Longrightarrow>
  eval_since args rs (Rep_mbuf_t xs, Rep_mbuf_t ys, Rep_mbuf_t ts, skew) aux = (res, (Rep_mbuf_t xs', Rep_mbuf_t ys', Rep_mbuf_t ts', skew'), aux')"
proof (induction rs "(xs, ys, ts, skew)" aux arbitrary: xs ys ts skew res xs' ys' ts' skew' aux' rule: eeval_since.induct)
  case (1 rs xs ys ts skew aux)
  obtain x xs'' where xs_def: "mbuf_t_cases xs = (x, xs'')"
    by fastforce
  obtain y ys'' where ys_def: "mbuf_t_cases ys = (y, ys'')"
    by fastforce
  obtain t ts'' where ts_def: "mbuf_t_cases ts = (t, ts'')"
    by fastforce
  show ?case
    using 1 xs_def ys_def ts_def
    by (cases x; cases y; cases t) (auto simp: mbuf_t_empty.rep_eq mbuf_t_Cons.rep_eq Let_def split: if_splits)
qed

end (* fixes args *)
end (* maux *)

fun mebufn_add :: "event_data table list list \<Rightarrow> event_data mebufn \<Rightarrow> event_data mebufn" where
  "mebufn_add xs' xs = List.map2 (@@) xs xs'"

lemma mbufn_add: "mbufn_add xss (map Rep_mbuf_t buf) = map Rep_mbuf_t (mebufn_add xss buf)"
  by (auto simp: comp_def zip_map1 mbuf_t_append.rep_eq)

lemma size_snd_mbuf_t_cases: "\<not> mbuf_t_is_empty a \<Longrightarrow> size (snd (mbuf_t_cases a)) < size a"
  by transfer (auto split: list.splits)

lemma size_list_snd_mbuf_t_cases: assumes "buf \<noteq> []" "\<And>x. x \<in> set buf \<Longrightarrow> \<not> mbuf_t_is_empty x"
  shows "size_list (\<lambda>x. size (snd (mbuf_t_cases x))) buf < size_list size buf"
  using assms
proof (induction buf)
  case IH: (Cons a buf)
  show ?case
  proof (cases buf)
    case Nil
    show ?thesis
      using IH(3) size_snd_mbuf_t_cases
      by (auto simp: Nil)
  next
    case (Cons a' buf')
    have "size_list (\<lambda>x. size (snd (mbuf_t_cases x))) buf < size_list size buf"
      using IH(1,3)
      by (auto simp: Cons)
    then show ?thesis
      using IH(3) size_snd_mbuf_t_cases
      by force
  qed
qed auto

function mebufn_take :: "(event_data table list \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> event_data mebufn \<Rightarrow> 'b \<times> event_data mebufn" where
  "mebufn_take f z buf = (if buf = [] \<or> (\<exists>x \<in> set buf. mbuf_t_is_empty x) then (z, buf)
    else mebufn_take f (f (map (the \<circ> fst \<circ> mbuf_t_cases) buf) z) (map (snd \<circ> mbuf_t_cases) buf))"
  by pat_completeness auto
termination
  using size_list_snd_mbuf_t_cases
  by (relation "measure (\<lambda>(_, _, buf). size_list size buf)") (auto simp: comp_def Suc_le_eq size_list_length_diff1)

lemma mbuf_t_is_empty_in_set: "[] \<in> set (map Rep_mbuf_t buf) \<longleftrightarrow> (\<exists>x \<in> set buf. mbuf_t_is_empty x)"
  by transfer auto

lemma hd_Rep_mbuf_t:
  assumes "\<And>x. x \<in> set buf \<Longrightarrow> \<not> mbuf_t_is_empty x"
  shows "map (hd \<circ> Rep_mbuf_t) buf = map (the \<circ> fst \<circ> mbuf_t_cases) buf"
  using assms
  by transfer (auto split: list.splits)

lemma tl_Rep_mbuf_t:
  assumes "\<And>x. x \<in> set buf \<Longrightarrow> \<not> mbuf_t_is_empty x"
  shows "map (tl \<circ> Rep_mbuf_t) buf = map Rep_mbuf_t (map (snd \<circ> mbuf_t_cases) buf)"
  using assms
  by transfer (auto split: list.splits)

lemma mebufn_take: "mebufn_take f z buf = (z', buf') \<Longrightarrow>
  mbufn_take f z (map Rep_mbuf_t buf) = (z', map Rep_mbuf_t buf')"
proof (induction f z buf arbitrary: z' buf' rule: mebufn_take.induct)
  case (1 f z buf)
  show ?case
    using 1(1,2)
    unfolding mebufn_take.simps[of _ _ buf] mbufn_take.simps[of _ _ "map Rep_mbuf_t buf"] mbuf_t_is_empty_in_set map_is_Nil_conv
    by (auto simp del: mbufn_take.simps mebufn_take.simps simp: hd_Rep_mbuf_t tl_Rep_mbuf_t split: if_splits)
qed

lemma mbufn_take_app: "mbufn_take (\<lambda>xs zs. zs @@ [f xs]) zs buf = (buf', zs') \<Longrightarrow>
  mbufn_take (\<lambda>xs zs. zs @ [f xs]) (Rep_mbuf_t zs) buf = (buf'', zs'') \<Longrightarrow>
  buf'' = Rep_mbuf_t buf' \<and> zs'' = zs'"
proof (induction "\<lambda>xs zs. zs @@ [f xs]" zs buf rule: mbufn_take.induct)
  case (1 z buf)
  then show ?case
    by (auto simp: mbufn_take.simps[where ?buf="buf"] mbuf_t_append.rep_eq simp del: mbufn_take.simps split: if_splits)
qed

fun mebufnt_take :: "(event_data table list \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>
    'b \<Rightarrow> event_data mebufn \<Rightarrow> ts \<Rightarrow> ts mbuf_t \<Rightarrow> 'b \<times> event_data mebufn \<times> ts \<times> ts mbuf_t" where
  "mebufnt_take f z buf t0 ts =
    (case mbuf_t_cases ts of (None, ts') \<Rightarrow> (z, buf, t0, ts) | (Some t, ts') \<Rightarrow>
    (if (\<exists>x \<in> set buf. mbuf_t_is_empty x) then (z, buf, t, t ## ts')
    else mebufnt_take f (f (map (the \<circ> fst \<circ> mbuf_t_cases) buf) t z) (map (snd \<circ> mbuf_t_cases) buf) t ts'))"

lemma mebufnt_take: "mebufnt_take f z buf t nts = (z', buf', nt, nts') \<Longrightarrow>
  mbufnt_take f z (map Rep_mbuf_t buf) t (Rep_mbuf_t nts) = (z', map Rep_mbuf_t buf', nt, Rep_mbuf_t nts')"
proof (induction f z buf t nts arbitrary: z' buf' nts' rule: mebufnt_take.induct)
  case (1 f z buf t ts)
  obtain to ts'' where ts_def: "mbuf_t_cases ts = (to, ts'')"
    by fastforce
  show ?case
    using 1(1,2) ts_def
    unfolding mebufnt_take.simps[of _ _ buf] mbufnt_take.simps[of _ _ "map Rep_mbuf_t buf"] mbuf_t_is_empty_in_set map_is_Nil_conv
    by (cases to) (auto simp del: mbufnt_take.simps mebufnt_take.simps simp: hd_Rep_mbuf_t tl_Rep_mbuf_t mbuf_t_Cons.rep_eq split: if_splits)
qed

lemma mbufnt_take_app: "mbufnt_take (\<lambda>xs t (zs, aux). case f xs t aux of (z, aux) \<Rightarrow> (zs @@ [z], aux)) (zs, aux) buf t0 ts = ((zs', aux'), buf', nt', ts') \<Longrightarrow>
  mbufnt_take (\<lambda>xs t (zs, aux). case f xs t aux of (z, aux) \<Rightarrow> (zs @ [z], aux)) (Rep_mbuf_t zs, aux) buf t0 ts = ((zs'', aux''), buf'', nt'', ts'') \<Longrightarrow>
  zs'' = Rep_mbuf_t zs' \<and> aux'' = aux' \<and> buf'' = buf' \<and> nt'' = nt' \<and> ts'' = ts'"
proof (induction "\<lambda>xs t (zs, aux). case f xs t aux of (z, aux) \<Rightarrow> (zs @@ [z], aux)" "(zs, aux)" buf t0 ts arbitrary: zs aux rule: mbufnt_take.induct)
  case (1 buf t0 ts)
  then show ?case
    by (auto simp: mbufnt_take.simps[where ?ts=ts] mbuf_t_append.rep_eq simp del: mbufnt_take.simps split: if_splits prod.splits)
qed

function letpast_meeval0 where
  "letpast_meeval0 eval j i ys xs p ts db \<phi> =
     (let (ys', \<phi>') = eval ts (Mapping.update p xs db) \<phi>
     in if size \<phi>' \<noteq> size \<phi> then (mbuf_t_empty, 0, None, \<phi>)
     else (case ys' of
       [] \<Rightarrow> (ys @@ ys', i + length xs, None, \<phi>')
     | y # _ \<Rightarrow> (if Suc (i + length xs) \<ge> j then (ys @@ ys', i + length xs, Some y, \<phi>')
         else letpast_meeval0 eval j (i + length xs) (ys @@ ys') ys' p [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>')))"
  by auto
termination
  by (relation "measure (\<lambda>(_, j, i, _, xs, _). j - (i + length xs))")
    (auto simp: not_le min_def diff_less_mono2)

declare letpast_meeval0.simps[simp del]

lemma letpast_meeval0: "letpast_meeval0 eval j i ys xs p ts db \<phi> = (ys', i', buf', \<phi>') \<Longrightarrow>
  letpast_meval0 eval j i (Rep_mbuf_t ys) xs p ts db \<phi> = (Rep_mbuf_t ys', i', buf', \<phi>')"
proof (induction eval j i ys xs p ts db \<phi> rule: letpast_meeval0.induct)
  case (1 eval j i ys xs p ts db \<phi>)
  then show ?case
    by (auto simp: letpast_meeval0.simps[where \<phi>=\<phi>] letpast_meval0.simps[where \<phi>=\<phi>]
        mbuf_t_empty.rep_eq mbuf_t_append.rep_eq split: prod.splits list.splits)
qed

lemma letpast_meeval0_cong[fundef_cong]:
  assumes "(\<And>ts db \<psi>. size \<psi> = size \<phi> \<Longrightarrow>  eval ts db \<psi> = eval' ts db \<psi>)"
  shows "letpast_meeval0 eval j i ys xs p ts db \<phi> = letpast_meeval0 eval' j i ys xs p ts db \<phi>"
  using assms
  apply (induct eval j i ys xs p ts db \<phi> arbitrary: eval' rule: letpast_meeval0.induct)
  subgoal premises IH for eval j i ys xs p ts db \<phi> eval'
    apply (subst (1 2) letpast_meeval0.simps)
    apply (auto split: prod.splits list.splits simp: Let_def IH)
    done
  done

lemma size_letpast_meeval: "(\<And>ts db \<psi>. size \<psi> = size \<phi> \<Longrightarrow> size (snd (eval ts db \<psi>)) = size \<psi>) \<Longrightarrow>
  size (snd (snd (snd (letpast_meeval0 eval j i ys xs p ts db \<phi>)))) = size \<phi>"
  apply (induct eval j i ys xs p ts db \<phi> rule: letpast_meeval0.induct)
  apply (subst letpast_meeval0.simps)
  apply (auto split: prod.splits list.splits simp: Let_def dest: sndI)
  done

lemma letpast_meval0_cong_f:
  assumes "(\<And>ts db \<psi>. size \<psi> = size \<phi> \<Longrightarrow>  eval ts db (f \<psi>) = (case eval' ts db \<psi> of (zs, \<psi>') \<Rightarrow> (zs, f \<psi>')))"
    "\<And>\<psi>. size (f \<psi>) = size \<psi>"
    "letpast_meval0 eval j i ys xs p ts db (f \<phi>) = (ys', i', buf', \<phi>')"
    "letpast_meval0 eval' j i ys xs p ts db \<phi> = (ys'', i'', buf'', \<phi>'')"
  shows "ys' = ys'' \<and> i' = i'' \<and> buf' = buf'' \<and> \<phi>' = f \<phi>''"
  using assms
  apply (induct eval' j i ys xs p ts db \<phi> rule: letpast_meval0.induct)
  subgoal premises IH for eval j i ys xs p ts db \<phi>
    using IH
    by (auto simp: letpast_meval0.simps[where ?\<phi>=\<phi>] letpast_meval0.simps[where ?\<phi>="f \<phi>"]
        split: prod.splits list.splits if_splits simp: Let_def)
  done

context maux
begin

context
  fixes j :: nat
begin

function (sequential) meeval :: "nat \<Rightarrow> ts list \<Rightarrow> database \<Rightarrow> ('msaux, 'muaux) meformula \<Rightarrow>
  event_data table list \<times> ('msaux, 'muaux) meformula" where
  "meeval n ts db (MRel rel) = (replicate (length ts) rel, MRel rel)"
| "meeval n ts db (MPred e tms mode) =
    ((case Mapping.lookup db (e, length tms) of
        None \<Rightarrow> replicate (length ts) {}
      | Some xs \<Rightarrow> (case mode of
          Copy \<Rightarrow> xs
        | Simple \<Rightarrow> map (\<lambda>X. simple_match n 0 tms ` X) xs
        | Match \<Rightarrow> map (\<lambda>X. (\<lambda>f. Table.tabulate f 0 n) ` Option.these (match tms ` X)) xs)),
    MPred e tms mode)"
| "meeval n ts db (MLet p m \<phi> \<psi>) =
    (let (xs, \<phi>) = meeval m ts db \<phi>;
      (ys, \<psi>) = meeval n ts (Mapping.update (p, m) xs db) \<psi>
    in (ys, MLet p m \<phi> \<psi>))"
| "meeval n ts db (MLetPast p m \<phi> \<psi> i buf) =
    (let (xs, i, buf, \<phi>) = letpast_meeval0 (meeval m) j i mbuf_t_empty (list_of_option buf) (p, m) ts db \<phi>;
         (ys, \<psi>) = meeval n ts (Mapping.update (p, m) (Rep_mbuf_t xs) db) \<psi>
    in (ys, MLetPast p m \<phi> \<psi> i buf))"
| "meeval n ts db (MAnd A_\<phi> \<phi> pos A_\<psi> \<psi> buf) =
    (let (xs, \<phi>) = meeval n ts db \<phi>; (ys, \<psi>) = meeval n ts db \<psi>;
      (zs, buf) = mebuf2_take (\<lambda>r1 r2. bin_join n A_\<phi> r1 pos A_\<psi> r2) (mebuf2_add xs ys buf)
    in (zs, MAnd A_\<phi> \<phi> pos A_\<psi> \<psi> buf))"
| "meeval n ts db (MAndAssign \<phi> conf) =
    (let (xs, \<phi>) = meeval n ts db \<phi> in (map (\<lambda>r. eval_assignment conf ` r) xs, MAndAssign \<phi> conf))"
| "meeval n ts db (MAndRel \<phi> conf) =
    (let (xs, \<phi>) = meeval n ts db \<phi> in (map (Set.filter (eval_constraint conf)) xs, MAndRel \<phi> conf))"
| "meeval n ts db (MAnds A_pos A_neg L buf) =
    (let R = map (meeval n ts db) L in
    let buf = mebufn_add (map fst R) buf in
    let (zs, buf) = mebufn_take (\<lambda>xs zs. zs @@ [mmulti_join n A_pos A_neg xs]) mbuf_t_empty buf in
    (Rep_mbuf_t zs, MAnds A_pos A_neg (map snd R) buf))"
| "meeval n ts db (MOr \<phi> \<psi> buf) =
    (let (xs, \<phi>) = meeval n ts db \<phi>; (ys, \<psi>) = meeval n ts db \<psi>;
      (zs, buf) = mebuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mebuf2_add xs ys buf)
    in (zs, MOr \<phi> \<psi> buf))"
| "meeval n ts db (MNeg \<phi>) =
    (let (xs, \<phi>) = meeval n ts db \<phi> in (map (\<lambda>r. (if r = empty_table then unit_table n else empty_table)) xs, MNeg \<phi>))"
| "meeval n ts db (MExists \<phi>) =
    (let (xs, \<phi>) = meeval (Suc n) ts db \<phi> in (map (\<lambda>r. tl ` r) xs, MExists \<phi>))"
| "meeval n ts db (MAgg args \<phi>) =
    (let (xs, \<phi>) = meeval (length (aggargs_tys args) + n) ts db \<phi> in (map (eval_aggargs args) xs, MAgg args \<phi>))"
| "meeval n ts db (MPrev I \<phi> first buf nts) =
    (let (xs, \<phi>) = meeval n ts db \<phi>
    in if first \<and> ts = [] then ([], MPrev I \<phi> True (buf @@ xs) (nts @@ ts))
    else let (zs, buf, nts) = meprev_next I (buf @@ xs) (nts @@ ts)
      in (if first then empty_table # zs else zs, MPrev I \<phi> False buf nts))"
| "meeval n ts db (MNext I \<phi> first nts) =
    (let (xs, \<phi>) = meeval n ts db \<phi>;
      (xs, first) = (case (xs, first) of (_ # xs, True) \<Rightarrow> (xs, False) | a \<Rightarrow> a);
      (zs, _, nts) = meprev_next I (mbuf_t_empty @@ xs) (nts @@ ts)
    in (zs, MNext I \<phi> first nts))"
| "meeval n ts db (MSince args \<phi> \<psi> buf aux) =
    (let (xs, \<phi>) = meeval (args_n args) ts db \<phi>; (ys, \<psi>) = meeval (args_n args) ts db \<psi>;
      (zs, buf, aux) = eeval_since args [] (mebuf2S_add xs ys ts buf) aux
    in (zs, MSince args \<phi> \<psi> buf aux))"
| "meeval n ts db (MUntil args \<phi> \<psi> buf nts t aux) =
    (let (xs, \<phi>) = meeval (args_n args) ts db \<phi>; (ys, \<psi>) = meeval (args_n args) ts db \<psi>;
      (aux, buf, nt, nts') = mebuf2t_take (add_new_muaux args) aux (mebuf2_add xs ys buf) t (nts @@ ts);
      (zs, aux) = eval_muaux args nt aux
    in (zs, MUntil args \<phi> \<psi> buf nts' nt aux))"
| "meeval n ts db (MMatchP I mr mrs \<phi>s buf nts aux) =
    (let (xss, \<phi>s) = map_split id (map (meeval n ts db) \<phi>s);
      ((zs, aux), buf, _, nts) = mebufnt_take (\<lambda>rels t (zs, aux).
        let (z, aux) = update_matchP n I mr mrs rels t aux
        in (zs @@ [z], aux)) (mbuf_t_empty, aux) (mebufn_add xss buf) 0 (nts @@ ts)
    in (Rep_mbuf_t zs, MMatchP I mr mrs \<phi>s buf nts aux))"
| "meeval n ts db (MMatchF I mr mrs \<phi>s buf nts t aux) =
    (let (xss, \<phi>s) = map_split id (map (meeval n ts db) \<phi>s);
      (aux, buf, nt, nts') = mebufnt_take (update_matchF n I mr mrs) aux (mebufn_add xss buf) t (nts @@ ts);
      (zs, aux) = eval_matchF I mr nt aux
    in (zs, MMatchF I mr mrs \<phi>s buf nts' nt aux))"
| "meeval n ts db (MTP mt i) = (map (\<lambda>x. eval_mtrm n mt (EInt (integer_of_nat x))) [i..<j], MTP mt j)"
| "meeval n ts db (MTS mt) = (map (\<lambda>x. eval_mtrm n mt (EInt (integer_of_nat x))) ts, MTS mt)"
  by pat_completeness auto

lemma psize_snd_meeval: "meeval_dom (n, t, db, \<phi>) \<Longrightarrow> size (snd (meeval n t db \<phi>)) = size \<phi>"
  apply (induct rule: meeval.pinduct)
  apply (auto simp only: prod.inject meeval.psimps Let_def snd_conv meformula.size map_split_map id_o map_split_eq_Pair_iff size_list_map o_apply cong: size_list_cong split: prod.splits)
    apply (metis snd_conv size_letpast_meeval)
    apply simp
  done

lemma total_meeval: "All meeval_dom"
  by (relation "measure (\<lambda>(_, _, _, \<phi>). size \<phi>)") (auto simp: termination_simp psize_snd_meeval)

termination meeval
  by (rule total_meeval)

lemma meval_code[code]: "meval j n ts db (Rep_meformula \<phi>) = (let (zs, \<phi>') = meeval n ts db \<phi> in (zs, Rep_meformula \<phi>'))"
proof (induction n ts db \<phi> rule: meeval.induct)
  case (4 n ts db p m \<phi> \<psi> i buf)
  have IH: "size \<psi> = size \<phi> \<Longrightarrow> meval j m ts db (Monitor_Impl.Rep_meformula \<psi>) =
    (case meeval m ts db \<psi> of (zs, \<psi>') \<Rightarrow> (zs, Monitor_Impl.Rep_meformula \<psi>'))" for ts db \<psi>
    using 4 by auto
  show ?case
    using 4(1) 4(2)[OF refl _ refl refl]
    by (cases "letpast_meeval0 (meeval m) j i mbuf_t_empty (list_of_option buf) (p, m) ts db \<phi>")
       (auto simp: letpast_meval_def mbuf_t_empty.rep_eq split: prod.splits
        dest!: letpast_meval0_cong_f[where ?eval="meval j m" and ?eval'="meeval m" and \<phi>=\<phi>, OF IH size_Rep_meformula, simplified] letpast_meeval0)
next
  case (8 n ts db A_pos A_neg L buf)
  have "map fst (map (meeval n ts db) L) = map fst (map (meval j n ts db) (map Monitor_Impl.Rep_meformula L))"
    "map snd (map (meval j n ts db) (map Monitor_Impl.Rep_meformula L)) = map Monitor_Impl.Rep_meformula (map snd (map (meeval n ts db) L))"
    by (auto dest: 8 split: prod.splits)
  then show ?case
    using 8
    by (auto simp only: Let_def meval.simps meeval.simps mbufn_add Rep_meformula.simps mbuf_t_empty.rep_eq
        split: prod.splits dest!: mebufn_take mbufn_take_app)
next
  case (17 n ts db I mr mrs \<phi>s buf nts aux)
  have IH: "zs = zs' \<and> \<phi>s' = map Rep_meformula \<phi>s''" if
    "map_split id (map (meval j n ts db) (map Rep_meformula \<phi>s)) = (zs, \<phi>s')"
    "map_split id (map (meeval n ts db) \<phi>s) = (zs', \<phi>s'')" for zs zs' \<phi>s' \<phi>s''
    using 17 that
    by (induction \<phi>s arbitrary: zs zs' \<phi>s' \<phi>s'') (auto simp: comp_def split: prod.splits)
  show ?case
    using 17
    by (auto simp only: meval.simps meeval.simps Rep_meformula.simps Let_def mbufn_add mbuf_t_empty.rep_eq mbuf_t_append.rep_eq
        split: prod.splits dest!: mebufnt_take IH dest: mbufnt_take_app)
next
  case (18 n ts db I mr mrs \<phi>s buf nts t aux)
  have IH: "zs = zs' \<and> \<phi>s' = map Rep_meformula \<phi>s''" if
    "map_split id (map (meval j n ts db) (map Rep_meformula \<phi>s)) = (zs, \<phi>s')"
    "map_split id (map (meeval n ts db) \<phi>s) = (zs', \<phi>s'')" for zs zs' \<phi>s' \<phi>s''
    using 18 that
    by (induction \<phi>s arbitrary: zs zs' \<phi>s' \<phi>s'') (auto simp: comp_def split: prod.splits)
  show ?case
    using 18
    by (auto simp only: meval.simps meeval.simps Rep_meformula.simps Let_def mbufn_add mbuf_t_append.rep_eq
        split: prod.splits dest!: mebufnt_take IH)
qed (auto simp: mbuf2_add mbuf_t_empty.rep_eq mbuf_t_append.rep_eq
    simp del: mprev_next.simps meprev_next.simps eval_since.simps eeval_since.simps
    split: prod.splits dest!: mebuf2_take mebuf2t_take meprev_next eeval_since)

end


fun annotate_verdicts :: "nat \<Rightarrow> ts queue \<Rightarrow> event_data table list \<Rightarrow>
  (nat \<times> ts \<times> event_data table) list \<Rightarrow> nat \<times> ts queue \<times> (nat \<times> ts \<times> event_data table) list" where
  "annotate_verdicts i tq [] acc = (i, tq, rev acc)"
| "annotate_verdicts i tq (v # vs) acc = (case pop tq of
      (None, tq') \<Rightarrow> (i + 1 + length vs, (tl_queue^^(1 + length vs)) tq', rev acc)  \<comment> \<open>unreachable due to invariant\<close>
    | (Some t, tq') \<Rightarrow> annotate_verdicts (i + 1) tq' vs ((i, t, v) # acc))"

lemma linearize_funpow_tl_queue: "linearize ((tl_queue^^n) q) = drop n (linearize q)"
  by (induction n) (auto simp add: tl_queue_rep drop_Suc tl_drop)

lemma annotate_verdicts_alt: "annotate_verdicts i tq xs acc = (i', tq', xs') \<Longrightarrow>
  i' = i + length xs \<and> linearize tq' = drop (length xs) (linearize tq) \<and>
    xs' = rev acc @ List.enumerate i (zip (linearize tq) xs)"
  by (induction i tq xs acc rule: annotate_verdicts.induct)
    (auto simp add: linearize_funpow_tl_queue tl_queue_rep drop_Suc neq_Nil_conv
      simp del: funpow.simps split: prod.splits option.splits dest!: pop_rep)

lemma mstep_code[code]: "mstep (db, t) (mestate i j m n tq \<zeta>) =
  (case meval (j + 1) n [t] db m of
    (vs, m') \<Rightarrow> (case annotate_verdicts i (append_queue t tq) vs [] of
      (i', ts', vs') \<Rightarrow> (vs', mestate i' (j + 1) m' n ts' \<zeta>)))"
  unfolding mstep_def mestate_def
  by (auto simp add: append_queue_rep split: prod.split dest!: annotate_verdicts_alt)

end

section \<open>Instantiation of the generic algorithm and code setup\<close>

(*
  The following snippet (context \<dots> end) is taken from HOL-Library.Code_Cardinality.
  We do not include the entire theory because the remaining code setup is superseded
  by Containers.
*)
context
begin

qualified definition card_UNIV' :: "'a card_UNIV"
where [code del]: "card_UNIV' = Phantom('a) CARD('a)"

lemma CARD_code [code_unfold]:
  "CARD('a) = of_phantom (card_UNIV' :: 'a card_UNIV)"
by(simp add: card_UNIV'_def)

lemma card_UNIV'_code [code]:
  "card_UNIV' = card_UNIV"
by(simp add: card_UNIV card_UNIV'_def)

end

instantiation enat :: set_impl begin
definition set_impl_enat :: "(enat, set_impl) phantom" where
  "set_impl_enat = phantom set_RBT"

instance ..
end

derive ccompare Formula.trm
derive (eq) ceq Formula.trm
derive (rbt) set_impl Formula.trm
derive (eq) ceq Monitor.mregex
derive ccompare Monitor.mregex
derive (rbt) set_impl Monitor.mregex
derive (rbt) mapping_impl Monitor.mregex
derive (no) cenum Monitor.mregex
derive (rbt) set_impl string8
derive (rbt) mapping_impl string8
derive (rbt) set_impl event_data
derive (rbt) mapping_impl event_data

type_synonym 'a vmsaux = "nat \<times> (nat \<times> 'a table) list"

definition valid_vmsaux :: "args \<Rightarrow> nat \<Rightarrow> event_data vmsaux \<Rightarrow>
  (nat \<times> event_data table) list \<Rightarrow> bool" where
  "valid_vmsaux = (\<lambda>_ cur (t, aux) auxlist. t = cur \<and> aux = auxlist)"

definition init_vmsaux :: "args \<Rightarrow> event_data vmsaux" where
  "init_vmsaux = (\<lambda>_. (0, []))"

definition add_new_ts_vmsaux :: "args \<Rightarrow> nat \<Rightarrow> event_data vmsaux \<Rightarrow> event_data vmsaux" where
  "add_new_ts_vmsaux = (\<lambda>args nt (t, auxlist). (nt, filter (\<lambda>(t, rel).
    memR (args_ivl args) (nt - t)) auxlist))"

definition join_vmsaux :: "args \<Rightarrow> event_data table \<Rightarrow> event_data vmsaux \<Rightarrow> event_data vmsaux" where
  "join_vmsaux = (\<lambda>args rel1 (t, auxlist). (t, map (\<lambda>(t, rel).
    (t, join rel (args_pos args) rel1)) auxlist))"

definition add_new_table_vmsaux :: "args \<Rightarrow> event_data table \<Rightarrow> event_data vmsaux \<Rightarrow>
  event_data vmsaux" where
  "add_new_table_vmsaux = (\<lambda>args rel2 (cur, auxlist). (cur, (case auxlist of
    [] => [(cur, rel2)]
  | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> rel2) # ts else (cur, rel2) # auxlist)))"

definition result_vmsaux :: "args \<Rightarrow> event_data vmsaux \<Rightarrow> event_data table" where
  "result_vmsaux = (\<lambda>args (cur, auxlist). eval_args_agg args
    (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {}))"

type_synonym 'a vmuaux = "nat \<times> (nat \<times> 'a table \<times> 'a table) list"

definition valid_vmuaux :: "args \<Rightarrow> nat \<Rightarrow> event_data vmuaux \<Rightarrow>
  (nat \<times> event_data table \<times> event_data table) list \<Rightarrow> bool" where
  "valid_vmuaux = (\<lambda>_ cur (t, aux) auxlist. t = cur \<and> aux = auxlist)"

definition init_vmuaux :: "args \<Rightarrow> event_data vmuaux" where
  "init_vmuaux = (\<lambda>_. (0, []))"

definition add_new_vmuaux ::  "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> nat \<Rightarrow>
  event_data vmuaux \<Rightarrow> event_data vmuaux" where
  "add_new_vmuaux = (\<lambda>args rel1 rel2 nt (t, auxlist). (nt, update_until args rel1 rel2 nt auxlist))"

definition length_vmuaux :: "args \<Rightarrow> event_data vmuaux \<Rightarrow> nat" where
  "length_vmuaux = (\<lambda>_ (_, auxlist). length auxlist)"

definition eval_vmuaux :: "args \<Rightarrow> nat \<Rightarrow> event_data vmuaux \<Rightarrow>
  event_data table list \<times> event_data vmuaux" where
  "eval_vmuaux = (\<lambda>args nt (t, auxlist).
    (let (res, auxlist') = eval_until (args_ivl args) nt auxlist in (map (eval_args_agg args)res, (t, auxlist'))))"

global_interpretation verimon_maux: maux valid_vmsaux init_vmsaux add_new_ts_vmsaux join_vmsaux
  add_new_table_vmsaux result_vmsaux valid_vmuaux init_vmuaux add_new_vmuaux length_vmuaux
  eval_vmuaux
  defines vminit0 = "maux.minit0 (init_vmsaux :: _ \<Rightarrow> event_data vmsaux) (init_vmuaux :: _ \<Rightarrow> event_data vmuaux) :: _ \<Rightarrow> ty Formula.formula \<Rightarrow> _"
  and vmeinit0 = "maux.meinit0 (init_vmsaux :: _ \<Rightarrow> event_data vmsaux) (init_vmuaux :: _ \<Rightarrow> event_data vmuaux) :: _ \<Rightarrow> ty Formula.formula \<Rightarrow> _"
  and vminit = "maux.minit (init_vmsaux :: _ \<Rightarrow> event_data vmsaux) (init_vmuaux :: _ \<Rightarrow> event_data vmuaux) :: ty Formula.formula \<Rightarrow> _"
  and vminit_safe = "maux.minit_safe (init_vmsaux :: _ \<Rightarrow> event_data vmsaux) (init_vmuaux :: _ \<Rightarrow> event_data vmuaux) :: ty Formula.formula \<Rightarrow> _"
  and vmeval_since = "maux.eval_since add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> event_data table)"
  and vmeeval_since = "maux.eeval_since add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> event_data table)"
  and vmeval = "maux.meval add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _)"
  and vmeeval = "maux.meeval add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _)"
  and letpast_vmeval = "maux.letpast_meval add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _)"
  and vmstep = "maux.mstep add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _)"
  and vmsteps0_stateless = "maux.msteps0_stateless add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _)"
  and vmsteps_stateless = "maux.msteps_stateless add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _)"
  and vmonitor = "maux.monitor init_vmsaux add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) init_vmuaux add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _)"
  unfolding valid_vmsaux_def init_vmsaux_def add_new_ts_vmsaux_def join_vmsaux_def
    add_new_table_vmsaux_def result_vmsaux_def valid_vmuaux_def init_vmuaux_def add_new_vmuaux_def
    length_vmuaux_def eval_vmuaux_def
  by unfold_locales auto

global_interpretation default_maux: maux valid_mmasaux "init_mmasaux :: _ \<Rightarrow> mmasaux" add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux result_mmasaux
  valid_mmauaux "init_mmauaux :: _ \<Rightarrow> mmauaux" add_new_mmauaux length_mmauaux eval_mmauaux'
  defines minit0 = "maux.minit0 (init_mmasaux :: _ \<Rightarrow> mmasaux) (init_mmauaux :: _ \<Rightarrow> mmauaux) :: _ \<Rightarrow> ty Formula.formula \<Rightarrow> _"
  and meinit0 = "maux.meinit0 (init_mmasaux :: _ \<Rightarrow> mmasaux) (init_mmauaux :: _ \<Rightarrow> mmauaux) :: _ \<Rightarrow> ty Formula.formula \<Rightarrow> _"
  and minit = "maux.minit (init_mmasaux :: _ \<Rightarrow> mmasaux) (init_mmauaux :: _ \<Rightarrow> mmauaux) :: ty Formula.formula \<Rightarrow> _"
  and minit_safe = "maux.minit_safe (init_mmasaux :: _ \<Rightarrow> mmasaux) (init_mmauaux :: _ \<Rightarrow> mmauaux) :: ty Formula.formula \<Rightarrow> _"
  and meval_since = "maux.eval_since add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> event_data table)"
  and meeval_since = "maux.eeval_since add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> event_data table)"
  and meval = "maux.meval add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> _) add_new_mmauaux (eval_mmauaux' :: _ \<Rightarrow> _ \<Rightarrow> mmauaux \<Rightarrow> _)"
  and meeval = "maux.meeval add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> _) add_new_mmauaux (eval_mmauaux' :: _ \<Rightarrow> _ \<Rightarrow> mmauaux \<Rightarrow> _)"
  and letpast_meval = "maux.letpast_meval add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> _) add_new_mmauaux (eval_mmauaux' :: _ \<Rightarrow> _ \<Rightarrow> mmauaux \<Rightarrow> _)"
  and mstep = "maux.mstep add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> _) add_new_mmauaux (eval_mmauaux' :: _ \<Rightarrow> _ \<Rightarrow> mmauaux \<Rightarrow> _)"
  and msteps0_stateless = "maux.msteps0_stateless add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> _) add_new_mmauaux (eval_mmauaux' :: _ \<Rightarrow> _ \<Rightarrow> mmauaux \<Rightarrow> _)"
  and msteps_stateless = "maux.msteps_stateless add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> _) add_new_mmauaux (eval_mmauaux' :: _ \<Rightarrow> _ \<Rightarrow> mmauaux \<Rightarrow> _)"
  and monitor = "maux.monitor init_mmasaux add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux (result_mmasaux :: _ \<Rightarrow> mmasaux \<Rightarrow> _) init_mmauaux add_new_mmauaux (eval_mmauaux' :: _ \<Rightarrow> _ \<Rightarrow> mmauaux \<Rightarrow> _)"
  by unfold_locales

lemma image_these: "f ` Option.these X = Option.these (map_option f ` X)"
  by (force simp: in_these_eq Bex_def image_iff map_option_case split: option.splits)

definition "meval_pred_impl n ts db e tms mode =
  (case Mapping.lookup db (e, length tms) of
      None \<Rightarrow> replicate (length ts) {}
    | Some Xs \<Rightarrow> (case mode of
        Copy \<Rightarrow> Xs
      | Simple \<Rightarrow> map (\<lambda>X. simple_match n 0 tms ` X) Xs
      | Match \<Rightarrow> map (\<lambda>X. \<Union>v \<in> X. (set_option (map_option (\<lambda>f. Table.tabulate f 0 n) (match tms v)))) Xs))"
declare meval_pred_impl_def[code_unfold]

lemma meval_pred_impl_eq: "meval_pred_impl n ts db e tms mode =
  (case Mapping.lookup db (e, length tms) of
      None \<Rightarrow> replicate (length ts) {}
    | Some xs \<Rightarrow> (case mode of
        Copy \<Rightarrow> xs
      | Simple \<Rightarrow> map (\<lambda>X. simple_match n 0 tms ` X) xs
      | Match \<Rightarrow> map (\<lambda>X. (\<lambda>f. Table.tabulate f 0 n) ` Option.these (match tms ` X)) xs))"
  unfolding meval_pred_impl_def
  by (force simp: Option.these_def image_iff intro!: option.case_cong pred_mode.case_cong)

lemma meeval_MPred: "meeval lookahead n ts db (meformula.MPred e tms mode) =
  (meval_pred_impl n ts db e tms mode, meformula.MPred e tms mode)"
  by (simp add: meval_pred_impl_eq)

lemma vmeeval_MPred: "vmeeval lookahead n ts db (meformula.MPred e tms mode) =
  (meval_pred_impl n ts db e tms mode, meformula.MPred e tms mode)"
  by (simp add: meval_pred_impl_eq)

declare [[code drop: meeval vmeeval]]
lemmas meeval_code[code] = default_maux.meeval.simps(1) meeval_MPred default_maux.meeval.simps(3-)
lemmas vmeeval_code[code] = verimon_maux.meeval.simps(1) vmeeval_MPred verimon_maux.meeval.simps(3-)

lemma saturate_commute:
  assumes "\<And>s. r \<in> g s" "\<And>s. g (Set.insert r s) = g s" "\<And>s. r \<in> s \<Longrightarrow> h s = g s"
  and terminates: "mono g" "\<And>X. X \<subseteq> C \<Longrightarrow> g X \<subseteq> C" "finite C"
shows "saturate g {} = saturate h {r}"
proof (cases "g {} = {r}")
  case True
  with assms have "g {r} = {r}" "h {r} = {r}" by auto
  with True show ?thesis
    by (subst (1 2) saturate_code; subst saturate_code) (simp add: Let_def)
next
  case False
  then show ?thesis
    unfolding saturate_def while_def
    using while_option_finite_subset_Some[OF terminates] assms(1-3)
    by (subst while_option_commute_invariant[of "\<lambda>S. S = {} \<or> r \<in> S" "\<lambda>S. g S \<noteq> S" g "\<lambda>S. h S \<noteq> S" "Set.insert r" h "{}", symmetric])
      (auto 4 4 dest: while_option_stop[of "\<lambda>S. g S \<noteq> S" g "{}"])
qed

definition "RPDs_aux = saturate (\<lambda>S. S \<union> \<Union> (RPD ` S))"

lemma RPDs_aux_code[code]:
  "RPDs_aux S = (let S' = S \<union> Set.bind S RPD in if S' \<subseteq> S then S else RPDs_aux S')"
  unfolding RPDs_aux_def bind_UNION
  by (subst saturate_code) auto

declare RPDs_code[code del]
lemma RPDs_code[code]: "RPDs r = RPDs_aux {r}"
  unfolding RPDs_aux_def RPDs_code
  by (rule saturate_commute[where C="RPDs r"])
     (auto 0 3 simp: mono_def subset_singleton_iff RPDs_refl RPDs_trans finite_RPDs)

definition "LPDs_aux = saturate (\<lambda>S. S \<union> \<Union> (LPD ` S))"

lemma LPDs_aux_code[code]:
  "LPDs_aux S = (let S' = S \<union> Set.bind S LPD in if S' \<subseteq> S then S else LPDs_aux S')"
  unfolding LPDs_aux_def bind_UNION
  by (subst saturate_code) auto

declare LPDs_code[code del]
lemma LPDs_code[code]: "LPDs r = LPDs_aux {r}"
  unfolding LPDs_aux_def LPDs_code
  by (rule saturate_commute[where C="LPDs r"])
     (auto 0 3 simp: mono_def subset_singleton_iff LPDs_refl LPDs_trans finite_LPDs)

lemma is_empty_table_unfold [code_unfold]:
  "X = empty_table \<longleftrightarrow> Set.is_empty X"
  "empty_table = X \<longleftrightarrow> Set.is_empty X"
  "set_eq X empty_table \<longleftrightarrow> Set.is_empty X"
  "set_eq empty_table X \<longleftrightarrow> Set.is_empty X"
  "X = (set_empty impl) \<longleftrightarrow> Set.is_empty X"
  "(set_empty impl) = X \<longleftrightarrow> Set.is_empty X"
  "set_eq X (set_empty impl) \<longleftrightarrow> Set.is_empty X"
  "set_eq (set_empty impl) X \<longleftrightarrow> Set.is_empty X"
  unfolding set_eq_def set_empty_def empty_table_def Set.is_empty_def by auto

lemma tabulate_rbt_code[code]: "Monitor.mrtabulate (xs :: mregex list) f =
  (case ID CCOMPARE(mregex) of None \<Rightarrow> Code.abort (STR ''tabulate RBT_Mapping: ccompare = None'') (\<lambda>_. Monitor.mrtabulate (xs :: mregex list) f)
  | _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.bulkload (List.map_filter (\<lambda>k. let fk = f k in if fk = empty_table then None else Some (k, fk)) xs)))"
  unfolding mrtabulate.abs_eq RBT_Mapping_def
  by (auto split: option.splits)

lemma upd_set_empty[simp]: "upd_set m f {} = m"
  by transfer auto

lemma upd_set_insert[simp]: "upd_set m f (Set.insert x A) = Mapping.update x (f x) (upd_set m f A)"
  by (rule mapping_eqI) (auto simp: Mapping_lookup_upd_set Mapping.lookup_update')

lemma upd_set_fold:
  assumes "finite A"
  shows "upd_set m f A = Finite_Set.fold (\<lambda>a. Mapping.update a (f a)) m A"
proof -
  interpret comp_fun_idem "\<lambda>a. Mapping.update a (f a)"
    by unfold_locales (transfer; auto simp: fun_eq_iff)+
  from assms show ?thesis
    by (induct A arbitrary: m rule: finite.induct) auto
qed

lift_definition upd_cfi :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, ('a, 'b) mapping) comp_fun_idem"
  is "\<lambda>f a m. Mapping.update a (f a) m"
  by unfold_locales (transfer; auto simp: fun_eq_iff)+

lemma upd_set_code[code]:
  "upd_set m f A = (if finite A then set_fold_cfi (upd_cfi f) m A else Code.abort (STR ''upd_set: infinite'') (\<lambda>_. upd_set m f A))"
  by (transfer fixing: m) (auto simp: upd_set_fold)

lemma lexordp_eq_code[code]: "lexordp_eq xs ys \<longleftrightarrow> (case xs of [] \<Rightarrow> True
  | x # xs \<Rightarrow> (case ys of [] \<Rightarrow> False
    | y # ys \<Rightarrow> if x < y then True else if x > y then False else lexordp_eq xs ys))"
  by (subst lexordp_eq.simps) (auto split: list.split)

lemma upd_set'_empty[simp]: "upd_set' m d f {} = m"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup)

lemma upd_set'_insert: "d = f d \<Longrightarrow> (\<And>x. f (f x) = f x) \<Longrightarrow> upd_set' m d f (Set.insert x A) =
  (let m' = (upd_set' m d f A) in case Mapping.lookup m' x of None \<Rightarrow> Mapping.update x d m'
  | Some v \<Rightarrow> Mapping.update x (f v) m')"
  by (rule mapping_eqI) (auto simp: upd_set'_lookup Mapping.lookup_update' split: option.splits)

lemma upd_set'_aux1: "upd_set' Mapping.empty d f {b. b = k \<or> (a, b) \<in> A} =
  Mapping.update k d (upd_set' Mapping.empty d f {b. (a, b) \<in> A})"
  by (rule mapping_eqI) (auto simp add: Let_def upd_set'_lookup Mapping.lookup_update'
      split: option.splits)

lemma upd_set'_aux2: "Mapping.lookup m k = None \<Longrightarrow> upd_set' m d f {b. b = k \<or> (a, b) \<in> A} =
  Mapping.update k d (upd_set' m d f {b. (a, b) \<in> A})"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup Mapping.lookup_update' split: option.splits)

lemma upd_set'_aux3: "Mapping.lookup m k = Some v \<Longrightarrow> upd_set' m d f {b. b = k \<or> (a, b) \<in> A} =
  Mapping.update k (f v) (upd_set' m d f {b. (a, b) \<in> A})"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup Mapping.lookup_update' split: option.splits)

lemma upd_set'_aux4: "k \<notin> fst ` A \<Longrightarrow> upd_set' Mapping.empty d f {b. (k, b) \<in> A} = Mapping.empty"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup Mapping.lookup_update' Domain.DomainI fst_eq_Domain
      split: option.splits)

lemma filter_set_empty[simp]: "filter_set (t, {}) (m, Y) = (m, Y)"
  unfolding filter_set.simps
  by transfer (auto simp: Let_def fun_eq_iff split: option.splits)

lemma filter_set_insert[simp]: "filter_set (t, Set.insert x A) (m, Y) = (let (m', Y') = filter_set (t, A) (m, Y) in
  case Mapping.lookup m' x of Some u \<Rightarrow> if t = u then (Mapping.delete x m', Y' \<union> {x}) else (m', Y') | _ \<Rightarrow> (m', Y'))"
  unfolding filter_set.simps
  by transfer (auto simp: fun_eq_iff Let_def split: option.splits)

lemma filter_set_fold:
  assumes "finite A"
  shows "filter_set (t, A) (m, Y) = Finite_Set.fold (\<lambda>a (m, Y).
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then (Mapping.delete a m, Y \<union> {a}) else (m, Y) | _ \<Rightarrow> (m, Y)) (m, Y) A"
proof -
  interpret comp_fun_idem "\<lambda>a (m, Y).
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then (Mapping.delete a m, Y \<union> {a}) else (m, Y) | _ \<Rightarrow> (m, Y)"
    by unfold_locales
      (transfer; auto simp: fun_eq_iff split: option.splits)+
  from assms show ?thesis
    by (induct A arbitrary: m rule: finite.induct) (auto simp: Let_def)
qed

lift_definition filter_cfi :: "'b \<Rightarrow> ('a, ('a, 'b) mapping \<times> 'a set) comp_fun_idem"
  is "\<lambda>t a (m, Y).
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then (Mapping.delete a m, Y \<union> {a}) else (m, Y) | _ \<Rightarrow> (m, Y)"
  by unfold_locales (transfer; auto simp: fun_eq_iff split: option.splits)+

lemma filter_set_code[code]:
  "filter_set (t, A) (m, Y) = (if finite A then set_fold_cfi (filter_cfi t) (m, Y) A else Code.abort (STR ''upd_set: infinite'') (\<lambda>_. filter_set (t, A) (m, Y)))"
  by (transfer fixing: m) (auto simp: filter_set_fold)

lemma mapping_delete_set_empty: "mapping_delete_set m {} = m"
  unfolding mapping_delete_set_def
  by (auto simp: Mapping_lookup_filter_Some intro!: mapping_eqI)

lemma mapping_delete_set_insert: "mapping_delete_set m (Set.insert a X) = Mapping.delete a (mapping_delete_set m X)"
proof(rule mapping_eqI)
  fix x
  show "Mapping.lookup (mapping_delete_set m (Set.insert a X)) x =
        Mapping.lookup (Mapping.delete a (mapping_delete_set m X)) x"
    unfolding Optimized_MTL.Mapping_lookup_delete mapping_delete_set_def
    by (auto simp add: Mapping_lookup_filter_None)
       (metis (mono_tags, lifting) Mapping_lookup_filter_None Mapping_lookup_filter_Some)
qed

lemma mapping_delete_fold:
  assumes "finite A"
  shows "mapping_delete_set m A = Finite_Set.fold Mapping.delete m A"
proof -
  interpret comp_fun_idem "Mapping.delete" by(unfold_locales; transfer; simp add: fun_eq_iff)
  from assms show ?thesis
  proof (induction A arbitrary: m)
    case empty
    then show ?case using mapping_delete_set_empty by auto
  next
    case (insert a A)
    then show ?case using mapping_delete_set_insert[of m a A] fold_insert[OF insert(1-2), of m] by(simp)
  qed
qed

lift_definition mapping_delete_set_cfi :: "('a, ('a, 'b) mapping) comp_fun_idem" is
  Mapping.delete by(unfold_locales; transfer; simp add:fun_eq_iff)

lemma mapping_delete_set_code[code]:
  "mapping_delete_set m A = (if finite A then set_fold_cfi mapping_delete_set_cfi m A else Code.abort (STR ''mapping_delete_set: infinite'') (\<lambda>_. mapping_delete_set m A))"
  using mapping_delete_fold[of A m] by (simp add: mapping_delete_set_cfi.rep_eq set_fold_cfi.rep_eq)

(*
definition set_minus :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "set_minus X Y = X - Y"

lift_definition remove_cfi :: "('a, 'a set) comp_fun_idem"
  is "\<lambda>b a. a - {b}"
  by unfold_locales auto

lemma set_minus_finite:
  assumes fin: "finite Y"
  shows "set_minus X Y = Finite_Set.fold (\<lambda>a X. X - {a}) X Y"
proof -
  interpret comp_fun_idem "\<lambda>a X. X - {a}"
    by unfold_locales auto
  from assms show ?thesis
    by (induction Y arbitrary: X rule: finite.induct) (auto simp add: set_minus_def)
qed

lemma set_minus_code[code]: "set_minus X Y =
  (if finite Y \<and> card Y < card X then set_fold_cfi remove_cfi X Y else X - Y)"
  by transfer (use set_minus_finite in \<open>auto simp add: set_minus_def\<close>)

declare [[code drop: bin_join]]
declare bin_join.simps[folded set_minus_def, code]
*)

definition remove_Union where
  "remove_Union A X B = A - (\<Union>x \<in> X. B x)"

lemma remove_Union_finite:
  assumes "finite X"
  shows "remove_Union A X B = Finite_Set.fold (\<lambda>x A. A - B x) A X"
proof -
  interpret comp_fun_idem "\<lambda>x A. A - B x"
    by unfold_locales auto
  from assms show ?thesis
    by (induct X arbitrary: A rule: finite_induct) (auto simp: remove_Union_def)
qed

lift_definition remove_Union_cfi :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a, 'b set) comp_fun_idem" is "\<lambda>B x A. A - B x"
  by unfold_locales auto

lemma remove_Union_code[code]: "remove_Union A X B =
  (if finite X then set_fold_cfi (remove_Union_cfi B) A X else A - (\<Union>x \<in> X. B x))"
  by (transfer fixing: A X B) (use remove_Union_finite[of X A B] in \<open>auto simp add: remove_Union_def\<close>)

lemma tabulate_remdups: "Mapping.tabulate xs f = Mapping.tabulate (remdups xs) f"
  by (transfer fixing: xs f) (auto simp: map_of_map_restrict)

declare [[code drop: New_max_getIJ_genericJoin New_max_getIJ_wrapperGenericJoin]]
declare New_max.genericJoin_code[folded remove_Union_def, code]
declare New_max.wrapperGenericJoin.simps[folded remove_Union_def, code]

lemma group_images: "(\<lambda>k. let group = Set.filter (\<lambda>x. f x = k) rel in g k group) ` f ` rel =
    (\<lambda>(k, group). g k group) ` images ((\<lambda>t. (f t, t)) ` rel)"
proof (rule set_eqI, rule iffI)
  fix x
  assume "x \<in> (\<lambda>k. Let (Set.filter (\<lambda>x. f x = k) rel) (g k)) ` f ` rel"
  then obtain t where t_def: "t \<in> rel" "x = g (f t) {x \<in> rel. f x = f t}"
    by (auto simp: Set.filter_def)
  have "(f t, {b. (f t, b) \<in> (\<lambda>t. (f t, t)) ` rel}) \<in>
    (\<lambda>a. (a, {b. (a, b) \<in> (\<lambda>t. (f t, t)) ` rel})) ` fst ` (\<lambda>t. (f t, t)) ` rel"
    using t_def(1)
    by force
  moreover have "{b. (f t, b) \<in> (\<lambda>t. (f t, t)) ` rel} = {x \<in> rel. f x = f t}"
    by (auto simp add: image_def)
  ultimately show "x \<in> (\<lambda>(k, group). g k group) ` images ((\<lambda>t. (f t, t)) ` rel)"
    unfolding t_def(2) images_def
    by auto
next
  fix x
  assume "x \<in> (\<lambda>(k, group). g k group) ` images ((\<lambda>t. (f t, t)) ` rel)"
  then obtain t where t_def: "t \<in> rel" "x = g (f t) {b. (f t, b) \<in> (\<lambda>t. (f t, t)) ` rel}"
    by (auto simp: images_def)
  have "{b. (f t, b) \<in> (\<lambda>t. (f t, t)) ` rel} = {x \<in> rel. f x = f t}"
    by (auto simp add: image_def)
  then show "x \<in> (\<lambda>k. Let (Set.filter (\<lambda>x. f x = k) rel) (g k)) ` f ` rel"
    using t_def(1)
    by (auto simp: t_def(2) Set.filter_def)
qed

lemma eval_agg_code[code]: "eval_agg n g0 y \<omega> tys f rel = (if g0 \<and> rel = empty_table
  then singleton_table n y (eval_agg_op \<omega> {})
  else (\<lambda>(k, group). let M = (\<lambda>(e, ts). (e, ecard ts)) ` images ((\<lambda>t. (meval_trm f t, t)) ` group) in
    k[y:=Some (eval_agg_op \<omega> M)]) ` images ((\<lambda>t. (drop (length tys) t, t)) ` rel))"
proof -
  have "(\<lambda>k. let group = Set.filter (\<lambda>x. drop (length tys) x = k) rel;
      M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group in
      k[y:=Some (eval_agg_op \<omega> M)]) ` (drop (length tys)) ` rel =
    (\<lambda>(k, group). let M = (\<lambda>(e, ts). (e, ecard ts)) ` images ((\<lambda>t. (meval_trm f t, t)) ` group) in
      k[y:=Some (eval_agg_op \<omega> M)]) ` images ((\<lambda>t. (drop (length tys) t, t)) ` rel)"
    unfolding Let_def group_images[of "drop (length tys)" rel
      "(\<lambda>k g. k[y := Some (eval_agg_op \<omega> ((\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) g))) ` meval_trm f ` g))])", unfolded Let_def]
    unfolding group_images[of "meval_trm f" _ "(\<lambda>y g. (y, ecard g))", unfolded Let_def]
    by simp
  then show ?thesis
    by (auto simp: eval_agg_def)
qed


declare regex.pred_inject[code]

declare regex.pred_set[THEN fun_cong, symmetric, code_unfold]

lemma Bex_pred_regex[code_unfold]: "Bex (regex.atms x) P \<longleftrightarrow> \<not> regex.pred_regex (Not o P) x"
  by (induct x) auto


derive (eq) ceq rec_safety
derive ccompare rec_safety
derive (dlist) set_impl rec_safety

declare [[code drop: safe_letpast]]
lemma safe_letpast_code[code]:
  "safe_letpast p (Formula.Eq t1 t2) = Unused"
  "safe_letpast p (Formula.Less t1 t2) = Unused"
  "safe_letpast p (Formula.LessEq t1 t2) = Unused"
  "safe_letpast p (Formula.Pred e ts) = (if p = (e, length ts) then NonFutuRec else Unused)"
  "safe_letpast p (Formula.Let e \<phi> \<psi>) =
      (safe_letpast (e, Formula.nfv \<phi>) \<psi> * safe_letpast p \<phi>) \<squnion>
      (if p = (e, Formula.nfv \<phi>) then Unused else safe_letpast p \<psi>)"
  "safe_letpast p (Formula.LetPast e \<phi> \<psi>) =
      (if p = (e, Formula.nfv \<phi>) then Unused else
        (safe_letpast (e, Formula.nfv \<phi>) \<psi> * safe_letpast p \<phi>) \<squnion> safe_letpast p \<psi>)"
  "safe_letpast p (Formula.Neg \<phi>) = safe_letpast p \<phi>"
  "safe_letpast p (Formula.Or \<phi> \<psi>) = (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
  "safe_letpast p (Formula.And \<phi> \<psi>) = (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
  "safe_letpast p (Formula.Ands l) = \<Squnion> set (map (safe_letpast p) l)"
  "safe_letpast p (Formula.Exists ty \<phi>) = safe_letpast p \<phi>"
  "safe_letpast p (Formula.Agg y \<omega> b' f \<phi>) = safe_letpast p \<phi>"
  "safe_letpast p (Formula.Prev I \<phi>) = PastRec * safe_letpast p \<phi>"
  "safe_letpast p (Formula.Next I \<phi>) = AnyRec * safe_letpast p \<phi>"
  "safe_letpast p (Formula.Since \<phi> I \<psi>) = safe_letpast p \<phi> \<squnion>
    (if memL I 0 then NonFutuRec else PastRec) * safe_letpast p \<psi>"
  "safe_letpast p (Formula.Until \<phi> I \<psi>) = AnyRec * (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
  "safe_letpast p (Formula.MatchP I r) = \<Squnion> Regex.atms (Regex.map_regex (safe_letpast p) r)"
  "safe_letpast p (Formula.MatchF I r) =  AnyRec * \<Squnion> Regex.atms (Regex.map_regex (safe_letpast p) r)"
  "safe_letpast p (Formula.TP t) = Unused"
  "safe_letpast p (Formula.TS t) = Unused"
  by (auto simp add: regex.set_map)

lemma Sup_rec_safety_set[code_unfold]:
  "\<Squnion> (set l :: rec_safety set) = fold (\<squnion>) l Unused"
  by (simp add: Sup_rec_safety_def comp_fun_idem_on.fold_set_fold[OF comp_fun_idem_on_sup])

lemma Sup_rec_safety_atms[code_unfold]:
  "\<Squnion> (Regex.atms r :: rec_safety set) = fold (\<squnion>) (csorted_list_of_set (Regex.atms r)) Unused"
  by (simp add: Sup_rec_safety_def csorted_list_of_set_def ccompare_rec_safety_def ID_def
      linorder.set_sorted_list_of_set[OF comparator.linorder] comparator_rec_safety
      flip: comp_fun_idem_on.fold_set_fold[OF comp_fun_idem_on_sup])

lift_definition delete_cnt_cfc::"aggargs \<Rightarrow> (event_data tuple, (bool \<times> nat agg_map)) comp_fun_commute" is
  "\<lambda>args. delete_cnt args" using delete_cnt_comm by unfold_locales auto

lemma [code_unfold]: "Finite_Set.fold (delete_cnt args) (v, m) data = set_fold_cfc (delete_cnt_cfc args) (v, m) data"
  by(transfer) auto

lift_definition delete_sum_cfc::"aggargs \<Rightarrow> (event_data tuple, (bool \<times> ((nat \<times> integer) agg_map))) comp_fun_commute" is
  "\<lambda>args. delete_sum args" using delete_sum_comm by unfold_locales auto

lemma [code_unfold]: "Finite_Set.fold (delete_sum args) (v, m) data = set_fold_cfc (delete_sum_cfc args) (v, m) data"
  by(transfer) auto

lift_definition delete_rank_cfc::"aggargs \<Rightarrow> type \<Rightarrow> (event_data tuple, bool \<times> list_aux agg_map) comp_fun_commute" is
  "\<lambda>args. delete_rank args" using delete_rank_comm by unfold_locales auto

lemma [code_unfold]: "Finite_Set.fold (delete_rank args type) (v, m) data = set_fold_cfc (delete_rank_cfc args type) (v, m) data"
  by(transfer) auto

lift_definition insert_cnt_cfc::"aggargs \<Rightarrow> (event_data tuple, (bool \<times> nat agg_map)) comp_fun_commute" is
  "\<lambda>args. insert_cnt args" using insert_cnt_comm by unfold_locales auto

lemma [code_unfold]: "Finite_Set.fold (insert_cnt args) (v, m) data = set_fold_cfc (insert_cnt_cfc args) (v, m) data"
  by(transfer) auto

lift_definition insert_sum_cfc::"aggargs \<Rightarrow> (event_data tuple, (bool \<times> ((nat \<times> integer) agg_map))) comp_fun_commute" is
  "\<lambda>args. insert_sum args" using insert_sum_comm by unfold_locales auto

lemma [code_unfold]: "Finite_Set.fold (insert_sum args) (v, m) data = set_fold_cfc (insert_sum_cfc args) (v, m) data"
  by(transfer) auto

lift_definition insert_rank_cfc::"aggargs \<Rightarrow> type \<Rightarrow> (event_data tuple, bool \<times> list_aux agg_map) comp_fun_commute" is
  "\<lambda>args. insert_rank args" using insert_rank_comm by unfold_locales auto

lemma [code_unfold]: "Finite_Set.fold (insert_rank args type) (v, m) data = set_fold_cfc (insert_rank_cfc args type) (v, m) data"
  by(transfer) auto

definition finite' :: "'a set \<Rightarrow> bool" where
  "finite' = finite"

declare insert_maggaux'.simps [code del]
declare insert_maggaux'.simps [folded finite'_def, code]

lemma [code_unfold]: "X - Mapping.keys tuple_in = Set.filter (\<lambda>k. Mapping.lookup tuple_in k = None) X"
  by(transfer) auto

instantiation treelist :: (equal) equal begin
lift_definition equal_treelist :: "'a treelist \<Rightarrow> 'a treelist \<Rightarrow> bool" is "(=)" .
instance by (standard; transfer; auto)
end

instantiation wf_wbt :: (linorder) equal begin
lift_definition equal_wf_wbt :: "'a wf_wbt \<Rightarrow> 'a wf_wbt \<Rightarrow> bool" is "(=)" .
instance by(standard; transfer; auto)
end

lemma eq_treelist_code[code]: "equal_class.equal (Collapse y1) (Collapse y2) = (if y2 = empty_tree then (y1 = empty_tree) else (tree_inorder y1 = tree_inorder y2))"
  apply(transfer) using Tree2.inorder.elims by auto

definition to_add_set where
  "to_add_set a m tmp = {b. (a, b) \<in> tmp \<and> Mapping.lookup m b = None}"

definition to_add_set_fun :: "'b \<Rightarrow> ('a, 'c) mapping \<Rightarrow> 'b \<times> 'a \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "to_add_set_fun a m elem s = (if a = fst elem \<and> Mapping.lookup m (snd elem) = None then Set.insert (snd elem) s else s)"

lemma to_add_set_empty: "to_add_set a m {} = {}"
  unfolding to_add_set_def by auto

lemma to_add_set_insert: "to_add_set a m (Set.insert x X) = to_add_set_fun a m x (to_add_set a m X) "
  unfolding to_add_set_def to_add_set_fun_def
  by transfer auto

lemma to_add_set_fold:
  assumes "finite tmp"
  shows "to_add_set a m tmp = Finite_Set.fold (to_add_set_fun a m) {} tmp"
proof -
  interpret comp_fun_idem "to_add_set_fun a m"
    by(unfold_locales) (auto simp:to_add_set_fun_def comp_def split:if_splits)
  from assms show ?thesis
  proof (induction tmp)
    case empty
    then show ?case using to_add_set_empty[of a m] by simp
  next
    case (insert a A)
    show ?case unfolding fold_insert[OF insert(1-2)] insert(3)[symmetric] unfolding to_add_set_def to_add_set_fun_def
      by transfer auto
   qed 
 qed

lift_definition to_add_set_cfi :: "'b \<Rightarrow> ('a, 'c) mapping \<Rightarrow> (('b \<times> 'a), 'a set) comp_fun_idem" is 
  "\<lambda>a m. to_add_set_fun a m" by(unfold_locales) (auto simp:to_add_set_fun_def comp_def split:if_splits)

lemma [code]: "to_add_set a m tmp = (if finite tmp then set_fold_cfi (to_add_set_cfi a m) {} tmp else Code.abort (STR ''to_add_set: infinite set'') (\<lambda>_. to_add_set a m tmp))"
  using to_add_set_fold[of tmp a m] by transfer auto

lemma upd_nested_empty[simp]: "upd_nested m d f {} = m"
  by (rule mapping_eqI) (auto simp add: upd_nested_lookup split: option.splits)

definition upd_nested_step :: "'c \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> ('a, ('b, 'c) mapping) mapping \<Rightarrow>
  ('a, ('b, 'c) mapping) mapping" where
  "upd_nested_step d f x m = (case x of (k, k') \<Rightarrow>
    (case Mapping.lookup m k of Some m' \<Rightarrow>
      (case Mapping.lookup m' k' of Some v \<Rightarrow> Mapping.update k (Mapping.update k' (f v) m') m
      | None \<Rightarrow> Mapping.update k (Mapping.update k' d m') m)
    | None \<Rightarrow> Mapping.update k (Mapping.update k' d Mapping.empty) m))"

lemma upd_nested_insert:
  "d = f d \<Longrightarrow> (\<And>x. f (f x) = f x) \<Longrightarrow> upd_nested m d f (Set.insert x A) =
  upd_nested_step d f x (upd_nested m d f A)"
  unfolding upd_nested_step_def
  using upd_set'_aux1[of d f _ _ A] upd_set'_aux2[of _ _ d f _ A] upd_set'_aux3[of _ _ _ d f _ A]
    upd_set'_aux4[of _ A d f]
  by (auto simp add: Let_def upd_nested_lookup upd_set'_lookup Mapping.lookup_update'
      split: option.splits prod.splits if_splits intro!: mapping_eqI)

definition upd_nested_max_tstp where
  "upd_nested_max_tstp m d X = upd_nested m d (max_tstp d) X"

lemma upd_nested_max_tstp_fold:
  assumes "finite X"
  shows "upd_nested_max_tstp m d X = Finite_Set.fold (upd_nested_step d (max_tstp d)) m X"
proof -
  interpret comp_fun_idem "upd_nested_step d (max_tstp d)"
    by (unfold_locales; rule ext)
      (auto simp add: comp_def upd_nested_step_def Mapping.lookup_update'
       update_update max_tstp_d_d max_tstp_idem' split: option.splits)
  note upd_nested_insert' = upd_nested_insert[of d "max_tstp d",
    OF max_tstp_d_d[symmetric] max_tstp_idem']
  show ?thesis
    using assms
    by (induct X arbitrary: m rule: finite.induct)
       (auto simp add: upd_nested_max_tstp_def upd_nested_insert')
qed

lift_definition upd_nested_max_tstp_cfi ::
  "ts + tp \<Rightarrow> ('a \<times> 'b, ('a, ('b, ts + tp) mapping) mapping) comp_fun_idem"
  is "\<lambda>d. upd_nested_step d (max_tstp d)"
  by (unfold_locales; rule ext)
    (auto simp add: comp_def upd_nested_step_def Mapping.lookup_update'
      update_update max_tstp_d_d max_tstp_idem' split: option.splits)

lemma upd_nested_max_tstp_code[code]:
  "upd_nested_max_tstp m d X = (if finite X then set_fold_cfi (upd_nested_max_tstp_cfi d) m X
    else Code.abort (STR ''upd_nested_max_tstp: infinite'') (\<lambda>_. upd_nested_max_tstp m d X))"
  by transfer (auto simp add: upd_nested_max_tstp_fold)


lemma [code]: 
  "add_new_mmuaux args rel1 rel2 nt aux =
    (let (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done) =
    shift_mmuaux args nt aux;
    I = args_ivl args; pos = args_pos args;
    new_tstp = (if memL I 0 then Inr tp else Inl nt);
    tstp_map = Mapping.update tp nt tstp_map;
    tmp = \<Union>((\<lambda>as. case Mapping.lookup a1_map (proj_tuple maskL as) of None \<Rightarrow>
      (if \<not>pos then {(tp - len, as)} else {})
      | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
      else {(max (tp - len) (tp' + 1), as)}) ` rel2) \<union> (if memL I 0 then {tp} \<times> rel2 else {});
    tmp = Set.filter (\<lambda>(tp, as). case Mapping.lookup tstp_map tp of Some ts \<Rightarrow> memL I (nt - ts)) tmp;
    table = snd ` tmp;
    tables = append_queue (table, if memL I 0 then Inr tp else Inl nt) tables;
    a2_map = Mapping.update (tp + 1) Mapping.empty
      (upd_nested_max_tstp a2_map new_tstp tmp);
    a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
      (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
    tss = append_queue nt tss in
    (tp + 1, tss, tables, len + 1, maskL, maskR, result \<union> snd ` (Set.filter (\<lambda>(t, x). t = tp - len) tmp), a1_map, a2_map, tstp_map, done))" 
  by(auto simp: upd_nested_max_tstp_def split:option.splits prod.splits)

lemma [code]:
  "add_new_mmauaux args rel1 rel2 nt (mmuaux, aggaux) =
    (case args_agg args of 
     None \<Rightarrow> let (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done) = add_new_mmuaux args rel1 rel2 nt mmuaux in
  ((tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done), aggaux) |
     Some aggargs \<Rightarrow>
    (let ((tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done), aggaux) = shift_mmauaux args nt (mmuaux, aggaux);
    I = args_ivl args; pos = args_pos args;
    new_tstp = (if memL I 0 then Inr tp else Inl nt);
    tstp_map = Mapping.update tp nt tstp_map;
    m = case Mapping.lookup a2_map (tp - len) of Some m \<Rightarrow> m;
    tmp = \<Union>((\<lambda>as. case Mapping.lookup a1_map (proj_tuple maskL as) of None \<Rightarrow>
      (if \<not>pos then {(tp - len, as)} else {})
      | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
      else {(max (tp - len) (tp' + 1), as)}) ` rel2) \<union> (if memL I 0 then {tp} \<times> rel2 else {});
    tmp = Set.filter (\<lambda>(tp, as). case Mapping.lookup tstp_map tp of Some ts \<Rightarrow> memL I (nt - ts)) tmp;
    table = snd ` tmp;
    tables = append_queue (table, if memL I 0 then Inr tp else Inl nt) tables;
    a2_map' = Mapping.update (tp + 1) Mapping.empty
      (upd_nested_max_tstp a2_map new_tstp tmp);
    a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
      (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
    to_add = to_add_set (tp - len) m tmp;
    aggaux = insert_maggaux' aggargs to_add aggaux;
    tss = append_queue nt tss in
    ((tp + 1, tss, tables, len + 1, maskL, maskR, result \<union> snd ` (Set.filter (\<lambda>(t, x). t = tp - len) tmp), a1_map, a2_map', tstp_map, done), aggaux)))"
  by(auto simp del: add_new_mmuaux.simps simp add: to_add_set_def  upd_nested_max_tstp_def split:option.splits prod.splits)


lift_definition update_mapping_with :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>f k v m. case m k of None \<Rightarrow> m(k \<mapsto> v) | Some v' \<Rightarrow> m(k \<mapsto> f k v' v)" .

lemma update_mapping_with_alt: "update_mapping_with f k v m =
  (case Mapping.lookup m k of
      None \<Rightarrow> Mapping.update k v m
    | Some v' \<Rightarrow> Mapping.update k (f k v' v) m)"
  by transfer simp

lift_definition mapping_rbt_insertwk :: "('a::ccompare \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow> ('a, 'b) mapping_rbt" is
  "rbt_comp_insert_with_key ccomp"
  by (auto 0 3 intro: linorder.rbt_insertwk_is_rbt ID_ccompare simp: rbt_comp_insert_with_key[OF ID_ccompare'])

declare [[code drop: update_mapping_with]]

lemma update_mapping_with_code[code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt" shows
  "update_mapping_with f k v (RBT_Mapping t) =
  (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''update_mapping_with RBT_Mapping: ccompare = None'') (\<lambda>_. update_mapping_with f k v (RBT_Mapping t))
  | Some _ \<Rightarrow> RBT_Mapping (mapping_rbt_insertwk f k v t))"
  by (clarsimp split: option.split, transfer fixing: f k v)
    (auto simp add: rbt_comp_lookup[OF ID_ccompare'] rbt_comp_insert_with_key[OF ID_ccompare']
      linorder.rbt_lookup_rbt_insertwk[OF ID_ccompare] ord.is_rbt_rbt_sorted
      split: option.split)

definition empty_db :: database where "empty_db = Mapping.empty"

definition insert_into_db :: "string8 \<times> nat \<Rightarrow> event_data tuple \<Rightarrow> database \<Rightarrow> database" where
  "insert_into_db p xs db = update_mapping_with (\<lambda>_ tbl _. map (Set.insert xs) tbl) p [{xs}] db"

definition rbt_fold :: "_ \<Rightarrow> event_data tuple set_rbt \<Rightarrow> _ \<Rightarrow> _" where
  "rbt_fold = RBT_Set2.fold"

fun finite_multiset_insert_fun :: "event_data \<times> enat \<Rightarrow> bool \<Rightarrow> bool" where
  "finite_multiset_insert_fun (_, k) v = ((if k = infinity then False else True) \<and> v)"

lemma finite_mset_insert_idem: 
  "comp_fun_idem finite_multiset_insert_fun"
proof -
   have *: "(finite_multiset_insert_fun (a, b) \<circ> finite_multiset_insert_fun (c, d)) e =
       (finite_multiset_insert_fun (c, d) \<circ> finite_multiset_insert_fun (a, b)) e" for a b c d e by auto
  then have aux1: "(finite_multiset_insert_fun (a, b) \<circ> finite_multiset_insert_fun (c, d)) =
       (finite_multiset_insert_fun (c, d) \<circ> finite_multiset_insert_fun (a, b))" for a b c d 
    using *[of a b c d] by presburger
  have *: "(finite_multiset_insert_fun (a, b) \<circ> finite_multiset_insert_fun (a, b)) c =
       (finite_multiset_insert_fun (a, b) c)" for a b c by auto
  then have aux2: "finite_multiset_insert_fun (a, b) \<circ> finite_multiset_insert_fun (a, b) =
       finite_multiset_insert_fun (a, b)" for a b using *[of a b] by presburger
  show ?thesis
    using aux1 aux2 by unfold_locales auto
qed

lemma finite_multiset_eq:
  assumes "finite M"
  shows "finite_multiset M = 
         Finite_Set.fold finite_multiset_insert_fun True M"
proof -
  interpret comp_fun_idem finite_multiset_insert_fun
    using finite_mset_insert_idem by auto
  from assms show ?thesis
  proof (induction M)
    case empty
    then show ?case by(auto simp:finite_multiset_def)
  next
    case (insert a A)
    have fin: "finite ((\<lambda>(x, y). case_enat (\<lambda>nat. True) False y) ` A)"
      using insert(1) by auto
    obtain s e where a_def: "a = (s, e)" by force
    then show ?case unfolding fold_insert[OF insert(1-2)] unfolding a_def
      using insert(3) by(cases e) (auto simp:finite_multiset_def)
  qed 
qed

lift_definition finite_multiset_cfi :: "(event_data \<times> enat, bool) comp_fun_idem" is 
  "finite_multiset_insert_fun"
  using finite_mset_insert_idem .

lemma finite_multiset_code[code]:
  "finite_multiset M = (if finite M then set_fold_cfi finite_multiset_cfi True M else False)"
  using finite_multiset_def finite_multiset_eq by transfer auto

(*<*)
end
(*>*)
