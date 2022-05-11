(*<*)
theory Table
  imports Main
begin
(*>*)

section \<open>Finite tables\<close>

type_synonym 'a tuple = "'a option list"
type_synonym 'a table = "'a tuple set"


subsection \<open> Well-formed tuples and tables \<close>

definition wf_tuple :: "nat \<Rightarrow> nat set \<Rightarrow> 'a tuple \<Rightarrow> bool" where
  "wf_tuple n V x \<longleftrightarrow> length x = n \<and> (\<forall>i<n. x!i = None \<longleftrightarrow> i \<notin> V)"

lemma wf_tuple_length: "wf_tuple n V x \<Longrightarrow> length x = n"
  unfolding wf_tuple_def by simp

lemma wf_tuple_Nil[simp]: "wf_tuple n A [] = (n = 0)"
  unfolding wf_tuple_def by auto

lemma Suc_pred': "Suc (x - Suc 0) = (case x of 0 \<Rightarrow> Suc 0 | _ \<Rightarrow> x)"
  by (auto split: nat.splits)

lemma wf_tuple_Cons[simp]:
  "wf_tuple n A (x # xs) \<longleftrightarrow> ((if x = None then 0 \<notin> A else 0 \<in> A) \<and>
   (\<exists>m. n = Suc m \<and> wf_tuple m ((\<lambda>x. x - 1) ` (A - {0})) xs))"
  unfolding wf_tuple_def
  by (auto 0 3 simp: nth_Cons image_iff Ball_def gr0_conv_Suc Suc_pred' split: nat.splits)

lemma wf_tuple_Suc: "wf_tuple (Suc m) A a \<longleftrightarrow> a \<noteq> [] \<and>
   wf_tuple m ((\<lambda>x. x - 1) ` (A - {0})) (tl a) \<and> (0 \<in> A \<longleftrightarrow> hd a \<noteq> None)"
  by (cases a) (auto simp: nth_Cons image_iff split: nat.splits)

lemma wf_tuple_cong:
  assumes "wf_tuple n A v" "wf_tuple n A w" "\<forall>x \<in> A. map the v ! x = map the w ! x"
  shows "v = w"
proof -
  from assms(1,2) have "length v = length w" unfolding wf_tuple_def by simp
  from this assms show "v = w"
  proof (induct v w arbitrary: n A rule: list_induct2)
    case (Cons x xs y ys)
    let ?n = "n - 1" and ?A = "(\<lambda>x. x - 1) ` (A - {0})"
    have *: "map the xs ! z = map the ys ! z" if "z \<in> ?A" for z
      using that Cons(5)[THEN bspec, of "Suc z"]
      by (cases z) (auto simp: le_Suc_eq split: if_splits)
    from Cons(1,3-5) show ?case
      by (auto intro!: Cons(2)[of ?n ?A] * split: if_splits)
  qed simp
qed

lemma eq_replicate_None_iff:
  "v = replicate n None \<longleftrightarrow> length v = n \<and> (\<forall>i<n. v ! i = None)"
  by (metis length_replicate nth_equalityI nth_replicate)

lemma wf_tuple_empty_iff:
  "wf_tuple n {} v \<longleftrightarrow> v = replicate n None"
  unfolding eq_replicate_None_iff by (simp add: wf_tuple_def)

lemma wf_tuple_replicate_None_iff: 
  "wf_tuple n X (replicate n None) \<longleftrightarrow> X \<subseteq> {m. n \<le> m}"
  unfolding wf_tuple_def 
  using leI by (auto simp add: subset_eq)

lemma wf_tuple_nemptyD:
  "X \<noteq> {} \<Longrightarrow> X \<subseteq> {m. m < n} \<Longrightarrow> wf_tuple n X v \<Longrightarrow> v \<noteq> replicate n None"
  by (subst wf_tuple_empty_iff[symmetric]) 
    (auto simp: wf_tuple_def subset_eq)

definition table :: "nat \<Rightarrow> nat set \<Rightarrow> 'a table \<Rightarrow> bool" where
  "table n V X \<longleftrightarrow> (\<forall>x\<in>X. wf_tuple n V x)"

lemma table_Un[simp]: "table n V X \<Longrightarrow> table n V Y \<Longrightarrow> table n V (X \<union> Y)"
  unfolding table_def by auto

lemma table_InterI: "\<R> \<noteq> {} \<Longrightarrow> \<forall>R\<in>\<R>. table n X R \<Longrightarrow> table n X (\<Inter> \<R>)"
  unfolding table_def by auto

lemma table_project: "table (Suc n) A X \<Longrightarrow> table n ((\<lambda>x. x - Suc 0) ` (A - {0})) (tl ` X)"
  unfolding table_def
  by (auto simp: wf_tuple_Suc)


subsection \<open> Tuple restriction \<close>

definition restrict where
  "restrict A v = map (\<lambda>i. if i \<in> A then v ! i else None) [0 ..< length v]"

lemma restrict_Nil[simp]: "restrict A [] = []"
  unfolding restrict_def by auto

lemma restrict_Cons[simp]: "restrict A (x # xs) =
  (if 0 \<in> A then x # restrict ((\<lambda>x. x - 1) ` (A - {0})) xs else None # restrict ((\<lambda>x. x - 1) ` A) xs)"
  unfolding restrict_def
  by (auto simp: map_upt_Suc image_iff Suc_pred' Ball_def simp del: upt_Suc split: nat.splits)

lemma restrict_empty_eq: "length v = n \<Longrightarrow> restrict {} v = replicate n None"
  by (induct v arbitrary: n)
    (simp_all add: restrict_def map_replicate_trivial)

lemma restrict_update: "y \<notin> A \<Longrightarrow> y < length x \<Longrightarrow> restrict A (x[y:=z]) = restrict A x"
  unfolding restrict_def by (auto simp add: nth_list_update)

lemma restrict_idle: "wf_tuple n A v \<Longrightarrow> restrict A v = v"
  by (induct v arbitrary: n A) (auto split: if_splits)

lemma length_restrict[simp]: "length (restrict A v) = length v"
  unfolding restrict_def by auto

lemma map_the_restrict:
  "i \<in> A \<Longrightarrow> map the (restrict A v) ! i = map the v ! i"
  by (induct v arbitrary: A i) (auto simp: nth_Cons' gr0_conv_Suc split: option.splits)

lemma restrict_restrict: "restrict A (restrict B z) = restrict (A\<inter>B) z"
  by(simp add: restrict_def)

lemma nth_restrict': "i < length z \<Longrightarrow> (restrict A z)!i = (if i \<in> A then z!i else None)"
  by(simp add: restrict_def)

lemma wf_tuple_restrict: "wf_tuple n B v \<Longrightarrow> A \<inter> B = C \<Longrightarrow> wf_tuple n C (restrict A v)"
  unfolding restrict_def wf_tuple_def by auto

lemma wf_tuple_restrict_simple: "wf_tuple n B v \<Longrightarrow> A \<subseteq> B \<Longrightarrow> wf_tuple n A (restrict A v)"
  unfolding restrict_def wf_tuple_def by auto

lemma nth_restrict: "i \<in> A \<Longrightarrow> i < length v \<Longrightarrow> restrict A v ! i = v ! i"
  unfolding restrict_def by auto

lemma restrict_eq_Nil[simp]: "restrict A v = [] \<longleftrightarrow> v = []"
  unfolding restrict_def by auto


subsection \<open> Empty and unit tables \<close>

definition "empty_table = {}"

lemma in_empty_table[simp]: "\<not> x \<in> empty_table"
  unfolding empty_table_def by simp

lemma empty_table[simp]: "table n V empty_table"
  unfolding table_def empty_table_def by simp

lemma table_empty[simp]: "table n X {}"
  by (simp add: table_def)

definition "unit_table n = {replicate n None}"

lemma unit_table_wf_tuple[simp]: "V = {} \<Longrightarrow> x \<in> unit_table n \<Longrightarrow> wf_tuple n V x"
  unfolding unit_table_def wf_tuple_def by simp

lemma unit_table[simp]: "V = {} \<Longrightarrow> table n V (unit_table n)"
  unfolding table_def by simp

lemma in_unit_table: "v \<in> unit_table n \<longleftrightarrow> wf_tuple n {} v"
  unfolding unit_table_def wf_tuple_def by (auto intro!: nth_equalityI)

lemma empty_neq_unit_table [simp]: "empty_table \<noteq> unit_table n"
  by (simp add: empty_table_def unit_table_def)

lemma union_empty_table_eq [simp]: 
  "empty_table \<union> R = R"
  "R \<union> empty_table = R"
  by (simp_all add: empty_table_def)

lemma table_empty_vars_iff: 
  "table n {} R \<longleftrightarrow> R = empty_table \<or> R = unit_table n"
  unfolding table_def wf_tuple_empty_iff unit_table_def 
  by force

lemmas table_empty_varsD = iffD1[OF table_empty_vars_iff, rule_format]

lemma table_unit_table_iff: "table n X (unit_table n) \<longleftrightarrow> X \<subseteq> {m. m \<ge> n}"
  unfolding table_def unit_table_def 
  using leI by (auto simp: subset_eq wf_tuple_def)

lemmas table_unitD = iffD1[OF table_unit_table_iff]

lemma table_unitD2: "table n X (unit_table n) \<Longrightarrow> X \<subseteq> {m. m < n} \<Longrightarrow> X = {}"
  unfolding table_def 
  by (auto simp: unit_table_def wf_tuple_def subset_eq)


subsection \<open> Singleton table \<close>

primrec tabulate :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "tabulate f x 0 = []"
| "tabulate f x (Suc n) = f x # tabulate f (Suc x) n"

lemma tabulate_alt: "tabulate f x n = map f [x ..< x + n]"
  by (induct n arbitrary: x) (auto simp: not_le Suc_le_eq upt_rec)

lemma length_tabulate[simp]: "length (tabulate f x n) = n"
  by (induction n arbitrary: x) simp_all

lemma map_tabulate[simp]: "map f (tabulate g x n) = tabulate (\<lambda>x. f (g x)) x n"
  by (induction n arbitrary: x) simp_all

lemma nth_tabulate[simp]: "k < n \<Longrightarrow> tabulate f x n ! k = f (x + k)"
proof (induction n arbitrary: x k)
  case (Suc n)
  then show ?case by (cases k) simp_all
qed simp

definition "singleton_table n i x = {tabulate (\<lambda>j. if i = j then Some x else None) 0 n}"

lemma singleton_table_wf_tuple[simp]: "V = {i} \<Longrightarrow> x \<in> singleton_table n i z \<Longrightarrow> wf_tuple n V x"
  unfolding singleton_table_def wf_tuple_def by simp

lemma singleton_table[simp]: "V = {i} \<Longrightarrow> table n V (singleton_table n i z)"
  unfolding table_def by simp


subsection \<open> Join \<close>

subsubsection \<open> Joining tuples \<close>

fun join1 :: "'a tuple \<times> 'a tuple \<Rightarrow> 'a tuple option" where
  "join1 ([], []) = Some []"
| "join1 (None # xs, None # ys) = map_option (Cons None) (join1 (xs, ys))"
| "join1 (Some x # xs, None # ys) = map_option (Cons (Some x)) (join1 (xs, ys))"
| "join1 (None # xs, Some y # ys) = map_option (Cons (Some y)) (join1 (xs, ys))"
| "join1 (Some x # xs, Some y # ys) = (if x = y
    then map_option (Cons (Some x)) (join1 (xs, ys))
    else None)"
| "join1 _ = None"

lemma join1_Some_iff: "(\<exists>v. join1 (x, y) = Some v) \<longleftrightarrow> (length x = length y 
  \<and> (\<forall>i<length x. (x ! i = None \<or> y ! i = None) \<or> (\<exists>a. x ! i = Some a \<and> y ! i = Some a)))"
  apply (induct "(x, y)" arbitrary: x y rule: join1.induct)
  using less_Suc_eq_0_disj by auto

lemma join1_Some_wf_tuple_eqD:
  assumes "join1 (v1, v2) = Some v" 
    and "wf_tuple n X v1" 
    and "wf_tuple n X v2"
  shows "v1 = v2" 
    and "v = v1" 
    and "v = v2"
  using assms 
  by (induct "(v1, v2)" arbitrary: v1 v2 v n X rule: join1.induct; 
      force split: if_splits)+

lemma join1_eq_lengths: "join1 (x, y) = Some z \<Longrightarrow> length x = length y"
  by (induct "(x, y)" arbitrary: z x y rule: join1.induct) (auto split: if_splits)

lemma join1_replicate_None_iff_nth: "join1 (v1, v2) = Some (replicate n None) 
  \<longleftrightarrow> (length v1 = length v2 \<and> length v1 = n \<and>  (\<forall>i<length v1. (v1 ! i = None \<and> v2 ! i = None)))"
proof (induct "(v1, v2)" arbitrary: v1 v2 n rule: join1.induct)
  case (2 xs ys)
  then show ?case
    apply (intro iffI conjI; clarsimp)
    using join1_eq_lengths apply blast
    apply (metis length_Cons length_replicate list.inject replicate_Suc)
    apply (metis eq_replicate_None_iff length_Cons list.inject replicate_Suc)
    by auto
next
  case (3 x xs ys)
  then show ?case 
    apply (intro iffI conjI; clarsimp)
    using join1_Some_iff apply blast
    apply (metis length_Cons length_replicate list.inject replicate_Suc)
    apply (metis eq_replicate_None_iff length_Cons list.inject replicate_Suc)
    by force
next
  case (4 xs y ys)
  then show ?case 
    apply (intro iffI conjI; clarsimp)
    using join1_Some_iff apply blast
    apply (metis length_Cons length_replicate list.inject replicate_Suc)
    apply (metis eq_replicate_None_iff length_Cons list.inject replicate_Suc)
    by force
next
  case (5 x xs y ys)
  then show ?case 
    apply (intro iffI conjI; clarsimp split: if_splits)
    using join1_Some_iff apply blast
    apply (metis length_Cons length_replicate list.inject replicate_Suc)
    apply (metis eq_replicate_None_iff length_Cons list.inject replicate_Suc)
    by force
qed simp_all

lemma join1_replicate_None_iff: "join1 (v1, v2) = Some (replicate n None) 
  \<longleftrightarrow> v1 = replicate n None \<and> v2 = replicate n None"
  using eq_replicate_None_iff
  by (auto simp: join1_replicate_None_iff_nth)

lemma join1_self: "join1 (x, x) = Some x"
  by (induct "(x, x)" arbitrary: x rule: join1.induct) auto

lemma self_join1: "join1 (xs, ys) \<noteq> Some xs \<Longrightarrow> join1 (zs, ys) \<noteq> Some xs"
  by (induct "(zs, ys)" arbitrary: zs ys xs rule: join1.induct; auto; auto)

lemma join1_commute: "join1 (x, y) = join1 (y, x)"
  by (induct "(x, y)" arbitrary: x y rule: join1.induct) auto

lemma join1_wf_tuple:
  "join1 (v1, v2) = Some v \<Longrightarrow> wf_tuple n A v1 \<Longrightarrow> wf_tuple n B v2 \<Longrightarrow> wf_tuple n (A \<union> B) v"
  by (induct "(v1, v2)" arbitrary: n v v1 v2 A B rule: join1.induct)
    (auto simp: image_Un Un_Diff split: if_splits)

lemma wf_tuple_join1I: "wf_tuple n X v1 \<Longrightarrow> wf_tuple n Y v2 \<Longrightarrow> Z = X \<union> Y 
  \<Longrightarrow> join1 (v1, v2) = Some v \<Longrightarrow> wf_tuple n Z v"
  using join1_wf_tuple by blast

lemma join1_replicate_None:
  assumes "length x = n"
  defines "y \<equiv> replicate n None"
  shows "join1 (x, y) = Some x"
    and "join1 (y, x) = Some x"
  using assms
  by (induct "(x,y)" arbitrary: n x y 
      rule: join1.induct; clarsimp)+

lemma join1_Some_sub_tuples1:
  "join1 (x, y) = Some z \<Longrightarrow> wf_tuple n X x \<Longrightarrow> wf_tuple n Y y \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> x = z"
  apply (induct "(x, y)" arbitrary: x y z n X Y rule: join1.induct; clarsimp split: if_splits)
proof (goal_cases NoneNone SomeNone NoneSome SomeSome)
  case nn: (NoneNone xs ys X Y w m)
  show ?case 
    apply(rule nn(1)[OF refl nn(6,7)])
    using nn(2,3,4) leI zero_less_iff_neq_zero 
    by (fastforce simp: subset_eq)+
next
  case sn: (SomeNone xs ys X Y w m)
  show ?case
    apply (rule sn(1)[OF refl sn(6,7)])
    using sn(2,3,4,5) 
    by (auto simp: subset_eq image_iff)
next
  case ns: (NoneSome xs ys X Y w m)
  thus ?case 
    by auto
next
  case ss: (SomeSome x xs X Y w m)
  show ?case 
    apply(rule ss(2)[OF refl ss(5,6)])
    using ss(1,2,4,5)
    by (auto simp: subset_eq image_iff)
qed

lemma join1_Some_sub_tuples2:
  "join1 (x, y) = Some z \<Longrightarrow> wf_tuple n X x \<Longrightarrow> wf_tuple n Y y \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> y = restrict Y z"
  apply (induct "(x, y)" arbitrary: x y z n X Y rule: join1.induct; clarsimp split: if_splits)
proof (goal_cases NoneNone SomeNone NoneSome SomeSome)
  case nn: (NoneNone xs ys X Y w m)
  show ?case 
    apply(rule nn(1)[OF refl nn(6,7)])
    using nn(2,3,4) leI zero_less_iff_neq_zero 
    by (fastforce simp: subset_eq)+
next
  case sn: (SomeNone xs ys X Y w m)
  show ?case
    apply (rule sn(1)[OF refl sn(6,7)])
    using sn(2,3,4,5) 
    by (auto simp: subset_eq image_iff)
next
  case ns: (NoneSome xs ys X Y w m)
  show ?case 
    apply (rule ns(1)[OF refl ns(6,7)])
    using ns(2,3,4,5) 
    by (auto simp: subset_eq image_iff)
next
  case ss: (SomeSome x xs X Y w m)
  show ?case 
    apply(rule ss(2)[OF refl ss(5,6)])
    using ss(1,2,4,5)
    by (auto simp: subset_eq image_iff)
qed


subsubsection \<open> Joining tables \<close>

definition join :: "'a table \<Rightarrow> bool \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "join A pos B = (if pos then Option.these (join1 ` (A \<times> B))
    else A - Option.these (join1 ` (A \<times> B)))"

lemma join_True_code[code]: "join A True B = (\<Union>a \<in> A. \<Union>b \<in> B. set_option (join1 (a, b)))"
  unfolding join_def by (force simp: Option.these_def image_iff)

lemma join_False_alt: "join X False Y = X - join X True Y"
  unfolding join_def by auto

lemma join_False_code[code]: "join A False B = {a \<in> A. \<forall>b \<in> B. join1 (a, b) \<noteq> Some a}"
  unfolding join_False_alt join_True_code
  by (auto simp: Option.these_def image_iff dest: self_join1)

lemma join_commute: "join R1 True R2 = join R2 True R1"
  unfolding join_def 
  using join1_commute
  by (auto simp: image_def Option.these_def)
    fastforce+

lemma join_wf_tuple: "x \<in> join X b Y \<Longrightarrow> \<forall>v \<in> X. wf_tuple n A v \<Longrightarrow> \<forall>v \<in> Y. wf_tuple n B v 
  \<Longrightarrow> (\<not> b \<Longrightarrow> B \<subseteq> A) \<Longrightarrow> A \<union> B = C \<Longrightarrow> wf_tuple n C x"
  unfolding join_def
  by (fastforce simp: Option.these_def image_iff sup_absorb1 dest: join1_wf_tuple split: if_splits)

lemma join_table: "table n A X \<Longrightarrow> table n B Y \<Longrightarrow> (\<not> b \<Longrightarrow> B \<subseteq> A) \<Longrightarrow> A \<union> B = C \<Longrightarrow>
  table n C (join X b Y)"
  unfolding table_def by (auto elim!: join_wf_tuple)

lemma join1_Some_restrict:
  fixes x y :: "'a tuple"
  assumes "wf_tuple n A x" "wf_tuple n B y"
  shows "join1 (x, y) = Some z \<longleftrightarrow> wf_tuple n (A \<union> B) z \<and> restrict A z = x \<and> restrict B z = y"
  using assms
proof (induct "(x, y)" arbitrary: n x y z A B rule: join1.induct)
  case (2 xs ys)
  then show ?case
    by (cases z) (auto 4 0 simp: image_Un Un_Diff)+
next
  case (3 x xs ys)
  then show ?case
    by (cases z) (auto 4 0 simp: image_Un Un_Diff)+
next
  case (4 xs y ys)
  then show ?case
    by (cases z) (auto 4 0 simp: image_Un Un_Diff)+
next
  case (5 x xs y ys)
  then show ?case
    by (cases z) (auto 4 0 simp: image_Un Un_Diff)+
qed auto

lemma join_restrict:
  fixes X Y :: "'a tuple set"
  assumes "\<And>v. v \<in> X \<Longrightarrow> wf_tuple n A v" "\<And>v. v \<in> Y \<Longrightarrow> wf_tuple n B v" "\<not> b \<Longrightarrow> B \<subseteq> A"
  shows "v \<in> join X b Y \<longleftrightarrow>
    wf_tuple n (A \<union> B) v \<and> restrict A v \<in> X \<and> (if b then restrict B v \<in> Y else restrict B v \<notin> Y)"
  by (auto 4 4 simp: join_def Option.these_def image_iff assms wf_tuple_restrict sup_absorb1 restrict_idle
    restrict_idle[OF assms(1)] elim: assms
    dest: join1_Some_restrict[OF assms(1,2), THEN iffD1, rotated -1]
    dest!: spec[of _ "Some v"]
    intro!: exI[of _ "Some v"] join1_Some_restrict[THEN iffD2, symmetric] bexI[rotated])

lemma in_joinI: "table n A X \<Longrightarrow> table n B Y \<Longrightarrow> (\<not>b \<Longrightarrow> B \<subseteq> A) \<Longrightarrow> wf_tuple n (A \<union> B) v \<Longrightarrow>
  restrict A v \<in> X \<Longrightarrow> (b \<Longrightarrow> restrict B v \<in> Y) \<Longrightarrow> (\<not>b \<Longrightarrow> restrict B v \<notin> Y) \<Longrightarrow> v \<in> join X b Y"
  unfolding table_def
  by (subst join_restrict) (auto)

lemma in_joinE: "v \<in> join X b Y \<Longrightarrow> table n A X \<Longrightarrow> table n B Y \<Longrightarrow> (\<not> b \<Longrightarrow> B \<subseteq> A) \<Longrightarrow>
  (wf_tuple n (A \<union> B) v \<Longrightarrow> restrict A v \<in> X \<Longrightarrow> if b then restrict B v \<in> Y else restrict B v \<notin> Y \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding table_def
  by (subst (asm) join_restrict) (auto)

lemma join_restrict_table:
  assumes "table n A X" "table n B Y" "\<not> b \<Longrightarrow> B \<subseteq> A"
  shows "v \<in> join X b Y \<longleftrightarrow>
    wf_tuple n (A \<union> B) v \<and> restrict A v \<in> X \<and> (if b then restrict B v \<in> Y else restrict B v \<notin> Y)"
  using assms unfolding table_def
  by (simp add: join_restrict)

lemma join_restrict_annotated:
  fixes X Y :: "'a tuple set"
  assumes "\<not> b =simp=> B \<subseteq> A"
  shows "join {v. wf_tuple n A v \<and> P v} b {v. wf_tuple n B v \<and> Q v} =
    {v. wf_tuple n (A \<union> B) v \<and> P (restrict A v) \<and> (if b then Q (restrict B v) else \<not> Q (restrict B v))}"
  using assms
  by (intro set_eqI, subst join_restrict) (auto simp: wf_tuple_restrict_simple simp_implies_def)

lemma join_unit_table:
  "table n X R \<Longrightarrow> join R True (unit_table n) = R"
  "table n X R \<Longrightarrow> join (unit_table n) True R  = R"
  by (auto simp: join_def image_def unit_table_def table_def 
      wf_tuple_def join1_replicate_None Option.these_def)

lemma join_unit_unit [simp]: "join (unit_table n) True (unit_table n) = unit_table n"
  by (rule join_unit_table[OF unit_table[OF refl]])

lemma join_unitD: "table n X R1 \<Longrightarrow> table n Y R2 \<Longrightarrow> join R1 True R2 = unit_table n 
  \<Longrightarrow> R1 = unit_table n \<and> R2 = unit_table n"
  by (clarsimp simp: unit_table_def join_def Option.these_def image_def set_eq_iff)
    (metis (no_types, opaque_lifting) join1_replicate_None join1_replicate_None_iff 
      option.sel table_def wf_tuple_def)

lemma join_empty_table:
  "join R True empty_table = empty_table"
  "join empty_table True R = empty_table"
  by (auto simp: join_def Option.these_def)

lemma join_sub_tables_eq:
  "table n X R\<^sub>1 \<Longrightarrow> table n Y R\<^sub>2 \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> join R\<^sub>1 True R\<^sub>2 = {v \<in> R\<^sub>1. (restrict Y v) \<in> R\<^sub>2 }"
  using join1_Some_sub_tuples1 join1_Some_sub_tuples2
  unfolding table_def join_def 
  by (auto simp: Option.these_def image_iff)
    (smt (z3) Un_absorb2 join1_Some_restrict option.sel restrict_idle)+

lemma join_eq_interI: 
  "table n X R1 \<Longrightarrow> table n X R2 \<Longrightarrow> join R1 True R2 = R1 \<inter> R2"
  apply (intro set_eqI iffI; clarsimp simp: join_def image_def Option.these_def table_def)
  using join1_Some_wf_tuple_eqD(2,3) apply blast
  using join1_self by (metis option.sel)

lemma foldr_join_tables_eq_InterI:
  "\<forall>R\<in>set Rs. table n X R \<Longrightarrow> foldr (\<lambda>r1 r2. join r1 True r2) Rs (unit_table n) = 
  (if Rs = [] then unit_table n else (\<Inter> (set Rs)))"
  apply (induct Rs arbitrary: n X; clarsimp simp: join_unit_table(1))
  using table_InterI[of "set _"] join_eq_interI
  by (metis set_empty2)

lemma join_Un_distrib:
  "join R True (\<Union>i\<in>\<I>. \<R> i) = (\<Union>i\<in>\<I>. join R True (\<R> i))"
  "join (\<Union>i\<in>\<I>. \<R> i) True R = (\<Union>i\<in>\<I>. join (\<R> i) True R)"
  unfolding Union_eq 
  by (auto; smt (verit, best) UN_E UN_I join_True_code mem_Collect_eq)+


subsection \<open> Union of tables \<close>

lemma table_union_must_subset:
  "R\<^sub>1 \<noteq> {} \<Longrightarrow> \<forall>x\<in>X\<union>Y. x < n \<Longrightarrow> table n X R\<^sub>1 \<Longrightarrow> table n (X \<union> Y) (R\<^sub>1 \<union> R\<^sub>2) \<Longrightarrow> Y \<subseteq> X"
  "R\<^sub>2 \<noteq> {} \<Longrightarrow> \<forall>x\<in>X\<union>Y. x < n \<Longrightarrow> table n Y R\<^sub>2 \<Longrightarrow> table n (X \<union> Y) (R\<^sub>1 \<union> R\<^sub>2) \<Longrightarrow> X \<subseteq> Y"
  by (clarsimp simp: table_def) (clarsimp simp: table_def wf_tuple_def, blast)+

lemma union_unit_iff: "R1 \<union> R2 = unit_table n 
  \<longleftrightarrow> (R1 = unit_table n \<and> R2 = {}) \<or> (R1 = {} \<and> R2 = unit_table n) \<or> (R1 = unit_table n \<and> R2 = unit_table n)"
  apply (clarsimp simp: unit_table_def, intro iffI)
  by (metis singleton_Un_iff) auto

lemma union_unitD: 
  assumes "R1 \<union> R2 = unit_table n"
  shows "R1 = unit_table n \<or> R2 = unit_table n"
    and "R1 = {} \<longrightarrow> R2 = unit_table n"
    and "R2 = {} \<longrightarrow> R1 = unit_table n"
  using assms unfolding union_unit_iff
  by blast+

corollary 
  "R\<^sub>1 \<noteq> {} \<Longrightarrow> R\<^sub>2 \<noteq> {} \<Longrightarrow> \<forall>x\<in>X\<union>Y. x < n \<Longrightarrow> table n X R\<^sub>1 \<Longrightarrow> table n Y R\<^sub>2 
  \<Longrightarrow> X = Y \<longleftrightarrow> table n (X \<union> Y) (R\<^sub>1 \<union> R\<^sub>2)"
  apply (rule iffI)
  apply (auto simp: table_def wf_tuple_def)[1]
  using table_union_must_subset(1,2)[of _ X Y n _] by auto blast


subsection \<open> Correctness predicate \<close>

definition qtable :: "nat \<Rightarrow> nat set \<Rightarrow> ('a tuple \<Rightarrow> bool) \<Rightarrow> ('a tuple \<Rightarrow> bool) \<Rightarrow>
  'a table \<Rightarrow> bool" where
  "qtable n A P Q X \<longleftrightarrow> table n A X \<and> (\<forall>x. (x \<in> X \<and> P x \<longrightarrow> Q x) \<and> (wf_tuple n A x \<and> P x \<and> Q x \<longrightarrow> x \<in> X))"

lemma qtable_iff: "qtable n X P Q R \<longleftrightarrow> 
  (table n X R \<and> (\<forall>v. P v \<longrightarrow> v \<in> R \<longleftrightarrow> (Q v \<and> wf_tuple n X v)))"
  by (auto simp: qtable_def table_def)

lemma qtable_cong: "qtable n A P Q X \<Longrightarrow> A = B \<Longrightarrow> (\<And>v. P v \<Longrightarrow> Q v \<longleftrightarrow> Q' v) 
  \<Longrightarrow> qtable n B P Q' X"
  by (auto simp: qtable_def)

lemma qtable_cong_strong: "A = B \<Longrightarrow> (\<And>v. wf_tuple n A v \<Longrightarrow> P v \<Longrightarrow> Q v \<longleftrightarrow> Q' v) 
  \<Longrightarrow> qtable n A P Q = qtable n B P Q'"
  apply (auto simp: qtable_def fun_eq_iff)
  using table_def by blast+

abbreviation wf_table where
  "wf_table n A Q X \<equiv> qtable n A (\<lambda>_. True) Q X"

lemma wf_table_iff: "wf_table n A Q X \<longleftrightarrow> (\<forall>x. x \<in> X \<longleftrightarrow> (Q x \<and> wf_tuple n A x))"
  unfolding qtable_def table_def by auto

lemma table_wf_table: "table n A X = wf_table n A (\<lambda>v. v \<in> X) X"
  unfolding table_def wf_table_iff by auto

lemma qtableI: "table n A X \<Longrightarrow>
  (\<And>x. x \<in> X \<Longrightarrow> wf_tuple n A x \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow>
  (\<And>x. wf_tuple n A x \<Longrightarrow> P x \<Longrightarrow> Q x \<Longrightarrow> x \<in> X) \<Longrightarrow>
  qtable n A P Q X"
  unfolding qtable_def table_def by auto

lemma in_qtableI: "qtable n A P Q X \<Longrightarrow> wf_tuple n A x \<Longrightarrow> P x \<Longrightarrow> Q x \<Longrightarrow> x \<in> X"
  unfolding qtable_def by blast

lemma in_qtableE: "qtable n A P Q X \<Longrightarrow> x \<in> X \<Longrightarrow> P x \<Longrightarrow> (wf_tuple n A x \<Longrightarrow> Q x \<Longrightarrow> R) \<Longrightarrow> R"
  unfolding qtable_def table_def by blast

lemma qtableD:
  assumes "qtable n X P Q R"
  shows "table n X R"
    and "P v \<Longrightarrow> v \<in> R \<Longrightarrow> Q v"
    and "P v \<Longrightarrow> v \<in> R \<Longrightarrow> wf_tuple n X v"
    and "P v \<Longrightarrow> Q v \<Longrightarrow> wf_tuple n X v \<Longrightarrow> v \<in> R"
  using assms unfolding qtable_iff by auto

lemma qtable_empty_vars_iff: 
  "qtable n {} P Q R \<longleftrightarrow> (R = empty_table \<or> R = unit_table n) 
    \<and> (\<forall>v. P v \<longrightarrow> (v \<in> R) = (Q v \<and> v = replicate n None))"
  unfolding qtable_iff table_empty_vars_iff wf_tuple_empty_iff by simp

lemma qtable_empty_varsI:
  "(\<And>v. P v \<Longrightarrow> Q v \<Longrightarrow> v \<noteq> replicate n None) \<Longrightarrow> qtable n {} P Q empty_table"
  "(\<And>v. P v \<Longrightarrow> (v = replicate n None) = Q v) \<Longrightarrow> qtable n {} P Q (unit_table n)"
  unfolding qtable_iff table_empty_vars_iff wf_tuple_empty_iff 
  by (auto simp: unit_table_def)

lemmas qtable_empty_varsD = 
  iffD1[OF qtable_empty_vars_iff, THEN conjunct1, rule_format]
  iffD1[OF qtable_empty_vars_iff, THEN conjunct2, rule_format]

lemma nullary_qtable_cases: "qtable n {} P Q X \<Longrightarrow> (X = empty_table \<or> X = unit_table n)"
  by (simp add: qtable_empty_vars_iff)

lemma qtable_empty_unit_table:
  "qtable n {} R P empty_table \<Longrightarrow> qtable n {} R (\<lambda>v. \<not> P v) (unit_table n)"
  by (auto simp: qtable_iff wf_tuple_empty_iff unit_table_def table_empty_vars_iff)

lemma qtable_unit_empty_table:
  "qtable n {} R P (unit_table n) \<Longrightarrow> qtable n {} R (\<lambda>v. \<not> P v) empty_table"
  by (auto simp: qtable_iff wf_tuple_empty_iff unit_table_def table_empty_vars_iff)

lemma qtable_nonempty_empty_table:
  "qtable n {} R P X \<Longrightarrow> x \<in> X \<Longrightarrow> qtable n {} R (\<lambda>v. \<not> P v) empty_table"
  by (frule nullary_qtable_cases) (auto dest: qtable_unit_empty_table)


subsubsection \<open> Empty and unit table \<close>

lemma qtable_empty: "(\<And>x. wf_tuple n A x \<Longrightarrow> P x \<Longrightarrow> Q x \<Longrightarrow> False) \<Longrightarrow> qtable n A P Q empty_table"
  unfolding qtable_def table_def empty_table_def by auto

lemma qtable_empty_iff: "qtable n A P Q empty_table = (\<forall>x. wf_tuple n A x \<longrightarrow> P x \<longrightarrow> Q x \<longrightarrow> False)"
  unfolding qtable_def table_def empty_table_def by auto

lemma qtable_unit_iff: "qtable n X P Q (unit_table n) 
  \<longleftrightarrow> (X \<subseteq> {m. n \<le> m} \<and> (P (replicate n None) \<longrightarrow> Q (replicate n None)))"
  unfolding qtable_iff table_unit_table_iff 
  by (auto simp: unit_table_def leD subset_eq wf_tuple_def)
    (meson eq_replicate_None_iff leD)+

lemma qtable_unitI: "(P (replicate n None) \<Longrightarrow> Q (replicate n None)) 
  \<Longrightarrow> X = {} \<Longrightarrow> qtable n X P Q (unit_table n)"
  by (subst qtable_unit_iff; clarsimp)

lemma qtable_unit_table: "(\<And>x. wf_tuple n {} x \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> qtable n {} P Q (unit_table n)"
  unfolding qtable_def table_def in_unit_table by auto


subsubsection \<open> Union \<close>

lemma qtable_union: "qtable n A P Q1 X \<Longrightarrow> qtable n A P Q2 Y \<Longrightarrow>
  (\<And>x. wf_tuple n A x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> Q1 x \<or> Q2 x) \<Longrightarrow> qtable n A P Q (X \<union> Y)"
  unfolding qtable_def table_def by blast

lemma qtable_union_emptyI: 
  "qtable n X P Q R \<Longrightarrow> qtable n X P Q (R \<union> empty_table)"
  "qtable n X P Q R \<Longrightarrow> qtable n X P Q (empty_table \<union> R)"
  unfolding qtable_iff by auto

lemma qtable_Union: "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> qtable n A P (Qi i) (Xi i)) \<Longrightarrow>
  (\<And>x. wf_tuple n A x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> (\<exists>i \<in> I. Qi i x)) \<Longrightarrow> qtable n A P Q (\<Union>i \<in> I. Xi i)"
proof (induct I arbitrary: Q rule: finite_induct)
  case (insert i F)
  then show ?case
    by (auto intro!: qtable_union[where ?Q1.0 = "Qi i" and ?Q2.0 = "\<lambda>x. \<exists>i\<in>F. Qi i x"])
qed (auto intro!: qtable_empty[unfolded empty_table_def])


subsubsection \<open> Join \<close>

lemma qtable_inter: "qtable n X P Q1 R1 \<Longrightarrow> qtable n X P Q2 R2 
  \<Longrightarrow> (\<And>x. wf_tuple n X x \<Longrightarrow> P x \<Longrightarrow> Q x = (Q1 x \<and> Q2 x)) 
  \<Longrightarrow> qtable n X P Q (R1 \<inter> R2)"
  unfolding qtable_def table_def by blast

lemma qtable_join: 
  assumes "qtable n A P Q1 X" "qtable n B P Q2 Y" "\<not> b \<Longrightarrow> B \<subseteq> A" "C = A \<union> B"
  "\<And>x. wf_tuple n C x \<Longrightarrow> P x \<Longrightarrow> P (restrict A x) \<and> P (restrict B x)"
  "\<And>x. b \<Longrightarrow> wf_tuple n C x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> Q1 (restrict A x) \<and> Q2 (restrict B x)"
  "\<And>x. \<not> b \<Longrightarrow> wf_tuple n C x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> Q1 (restrict A x) \<and> \<not> Q2 (restrict B x)"
  shows "qtable n C P Q (join X b Y)"
proof (rule qtableI)
  from assms(1-4) show "table n C (join X b Y)" 
    unfolding qtable_def by (auto simp: join_table)
next
  fix x assume "x \<in> join X b Y" "wf_tuple n C x" "P x"
  with assms(1-3) assms(5-7)[of x] show "Q x" unfolding qtable_def
    by (auto 0 2 simp: wf_tuple_restrict_simple elim!: in_joinE split: if_splits)
next
  fix x assume "wf_tuple n C x" "P x" "Q x"
  with assms(1-4) assms(5-7)[of x] show "x \<in> join X b Y" unfolding qtable_def
    by (auto dest: wf_tuple_restrict_simple intro!: in_joinI[of n A X B Y])
qed

lemma qtable_join_fixed: 
  assumes "qtable n A P Q1 X" "qtable n B P Q2 Y" "\<not> b \<Longrightarrow> B \<subseteq> A" "C = A \<union> B"
  "\<And>x. wf_tuple n C x \<Longrightarrow> P x \<Longrightarrow> P (restrict A x) \<and> P (restrict B x)"
  shows "qtable n C P (\<lambda>x. Q1 (restrict A x) \<and> (if b then Q2 (restrict B x) else \<not> Q2 (restrict B x))) (join X b Y)"
  by (rule qtable_join[OF assms]) auto

lemma qtable_assign:
  assumes "qtable n A P Q X"
    "y < n" "insert y A = A'" "y \<notin> A"
    "\<And>x'. wf_tuple n A' x' \<Longrightarrow> P x' \<Longrightarrow> P (restrict A x')"
    "\<And>x. wf_tuple n A x \<Longrightarrow> P x \<Longrightarrow> Q x \<Longrightarrow> Q' (x[y:=Some (f x)])"
    "\<And>x'. wf_tuple n A' x' \<Longrightarrow> P x' \<Longrightarrow> Q' x' 
  \<Longrightarrow> Q (restrict A x') \<and> x' ! y = Some (f (restrict A x'))"
  shows "qtable n A' P Q' ((\<lambda>x. x[y:=Some (f x)]) ` X)" (is "qtable _ _ _ _ ?Y")
proof (rule qtableI)
  from assms(1) have "table n A X" unfolding qtable_def by simp
  then show "table n A' ?Y"
    unfolding table_def wf_tuple_def using assms(2,3)
    by (auto simp: nth_list_update)
next
  fix x'
  assume "x' \<in> ?Y" "wf_tuple n A' x'" "P x'"
  then obtain x where "x \<in> X" and x'_eq: "x' = x[y:=Some (f x)]" by blast
  then have "wf_tuple n A x"
    using assms(1) unfolding qtable_def table_def by blast
  then have "y < length x" using assms(2) by (simp add: wf_tuple_def)
  with \<open>wf_tuple n A x\<close> have "restrict A x' = x"
    unfolding x'_eq by (simp add: restrict_update[OF assms(4)] restrict_idle)
  with \<open>wf_tuple n A' x'\<close> \<open>P x'\<close> have "P x"
    using assms(5) by blast
  with \<open>wf_tuple n A x\<close> \<open>x \<in> X\<close> have "Q x"
    using assms(1) by (elim in_qtableE)
  with \<open>wf_tuple n A x\<close> \<open>P x\<close> show "Q' x'"
    unfolding x'_eq by (rule assms(6))
next
  fix x'
  assume "wf_tuple n A' x'" "P x'" "Q' x'"
  then have "wf_tuple n A (restrict A x')"
    using assms(3) by (auto intro!: wf_tuple_restrict_simple)
  moreover have "P (restrict A x')"
    using \<open>wf_tuple n A' x'\<close> \<open>P x'\<close> by (rule assms(5))
  moreover have "Q (restrict A x')" and y: "x' ! y = Some (f (restrict A x'))"
    using \<open>wf_tuple n A' x'\<close> \<open>P x'\<close> \<open>Q' x'\<close> by (auto dest!: assms(7))
  ultimately have "restrict A x' \<in> X" by (intro in_qtableI[OF assms(1)])
  moreover have "x' = (restrict A x')[y:=Some (f (restrict A x'))]"
    using y assms(2,3) \<open>wf_tuple n A (restrict A x')\<close> \<open>wf_tuple n A' x'\<close>
    by (auto simp: list_eq_iff_nth_eq wf_tuple_def nth_list_update nth_restrict)
  ultimately show "x' \<in> ?Y" by simp
qed

lemma qtable_filter:
  assumes "qtable n A P Q X"
    "\<And>x. wf_tuple n A x \<Longrightarrow> P x \<Longrightarrow> Q x \<and> R x \<longleftrightarrow> Q' x"
  shows "qtable n A P Q' (Set.filter R X)" (is "qtable _ _ _ _ ?Y")
proof (rule qtableI)
  from assms(1) have "table n A X"
    unfolding qtable_def by simp
  then show "table n A ?Y"
    unfolding table_def wf_tuple_def by simp
next
  fix x
  assume "x \<in> ?Y" "wf_tuple n A x" "P x"
  with assms show "Q' x" by (auto elim!: in_qtableE)
next
  fix x
  assume "wf_tuple n A x" "P x" "Q' x"
  with assms show "x \<in> Set.filter R X" by (auto intro!: in_qtableI)
qed


subsubsection \<open> Projection \<close>

definition mem_restr :: "'a list set \<Rightarrow> 'a tuple \<Rightarrow> bool" where
  "mem_restr A x \<longleftrightarrow> (\<exists>y\<in>A. list_all2 (\<lambda>a b. a \<noteq> None \<longrightarrow> a = Some b) x y)"

lemma mem_restrI: "y \<in> A \<Longrightarrow> length y = n \<Longrightarrow> wf_tuple n V x \<Longrightarrow> \<forall>i\<in>V. x ! i = Some (y ! i) \<Longrightarrow> mem_restr A x"
  unfolding mem_restr_def wf_tuple_def by (force simp add: list_all2_conv_all_nth)

lemma mem_restrE: "mem_restr A x \<Longrightarrow> wf_tuple n V x \<Longrightarrow> \<forall>i\<in>V. i < n \<Longrightarrow>
  (\<And>y. y \<in> A \<Longrightarrow> \<forall>i\<in>V. x ! i = Some (y ! i) \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding mem_restr_def wf_tuple_def by (fastforce simp add: list_all2_conv_all_nth)

lemma mem_restr_IntD: "mem_restr (A \<inter> B) v \<Longrightarrow> mem_restr A v \<and> mem_restr B v"
  unfolding mem_restr_def by auto

lemma mem_restr_Un_iff: "mem_restr (A \<union> B) x \<longleftrightarrow> mem_restr A x \<or> mem_restr B x"
  unfolding mem_restr_def by blast

lemma mem_restr_UNIV [simp]: "mem_restr UNIV x"
  unfolding mem_restr_def
  by (auto simp add: list.rel_map intro!: exI[of _ "map the x"] list.rel_refl)

lemma restrict_mem_restr[simp]: "mem_restr A x \<Longrightarrow> mem_restr A (restrict V x)"
  unfolding mem_restr_def restrict_def
  by (auto simp: list_all2_conv_all_nth elim!: bexI[rotated])

definition lift_envs :: "'a list set \<Rightarrow> 'a list set" where
  "lift_envs R = (\<lambda>(a,b). a # b) ` (UNIV \<times> R)"

lemma lift_envs_mem_restr[simp]: "mem_restr A x \<Longrightarrow> mem_restr (lift_envs A) (a # x)"
  by (auto simp: mem_restr_def lift_envs_def)

lemma qtable_project:
  assumes "qtable (Suc n) A (mem_restr (lift_envs R)) P X"
  shows "qtable n ((\<lambda>x. x - Suc 0) ` (A - {0})) (mem_restr R)
      (\<lambda>v. \<exists>x. P ((if 0 \<in> A then Some x else None) # v)) (tl ` X)"
      (is "qtable n ?A (mem_restr R) ?P ?X")
proof ((rule qtableI; (elim exE)?), goal_cases table left right)
  case table
  with assms show ?case
    unfolding qtable_def by (simp add: table_project) 
next
  case (left v)
  from assms have "[] \<notin> X"
    unfolding qtable_def table_def by fastforce
  with left(1) obtain x where "x # v \<in> X"
    by (metis (no_types, opaque_lifting) image_iff hd_Cons_tl)
  with assms show ?case
    by (rule in_qtableE) (auto simp: left(3) split: if_splits)
next
  case (right v x)
  with assms have "(if 0 \<in> A then Some x else None) # v \<in> X"
    by (elim in_qtableI) auto
  then show ?case
    by (auto simp: image_iff elim: bexI[rotated])
qed

(*<*)
end
(*>*)
