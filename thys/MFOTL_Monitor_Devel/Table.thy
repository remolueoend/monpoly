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

lemma restrict_restrict: "restrict A (restrict B v) = restrict (A \<inter> B) v"
  by (simp add: restrict_def)

lemma sub_restrict_restrict: "A \<subseteq> B \<Longrightarrow> restrict A (restrict B v) = restrict A v"
  by (simp add: restrict_restrict Int_absorb2)

lemma restrict_update: "y \<notin> A \<Longrightarrow> y < length x \<Longrightarrow> restrict A (x[y:=z]) = restrict A x"
  unfolding restrict_def by (auto simp add: nth_list_update)

lemma restrict_idle: "wf_tuple n A v \<Longrightarrow> restrict A v = v"
  by (induct v arbitrary: n A) (auto split: if_splits)

lemma length_restrict[simp]: "length (restrict A v) = length v"
  unfolding restrict_def by auto

lemma map_the_restrict:
  "i \<in> A \<Longrightarrow> map the (restrict A v) ! i = map the v ! i"
  by (induct v arbitrary: A i) (auto simp: nth_Cons' gr0_conv_Suc split: option.splits)

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

lemma join1_Cons_None [simp]: 
  "join1 (None # as, b # bs) = map_option ((#) b) (join1 (as, bs))"
  "join1 (a # as, None # bs) = map_option ((#) a) (join1 (as, bs))"
  apply (induct "(None # as, b # bs)" rule: join1.induct; clarsimp)
  by (induct "(a # as, None # bs)" rule: join1.induct; clarsimp)

lemma join1_Cons_SomeD1: 
  "join1 (a # as, b # bs) = Some (z # zs) \<Longrightarrow> join1 (as, bs) = Some zs"
  by (induct "(a # as, b # bs)" arbitrary: a b as bs z zs rule: join1.induct)
    (simp_all split: if_splits)

lemma join1_Cons_SomeD2: 
  "join1 (a # as, b # bs) = Some (z # zs) \<Longrightarrow> (a = z \<and> b = None) \<or> (a = None \<and> b = z) \<or> (a = b \<and> b = z)"
  by (induct "(a # as, b # bs)" arbitrary: a b as bs z zs rule: join1.induct)
    (simp_all split: if_splits)

lemma join1_Cons_Some_exI: "join1 (a # as, bs) = Some zs 
  \<Longrightarrow> \<exists>b bs' z zs'. bs = b # bs' \<and> zs = z # zs' \<and> join1 (as, bs') = Some zs'"
proof-
  assume hyp: "join1 (a # as, bs) = Some zs"
  then obtain b bs' where bs_eq: "bs = b # bs'"
    by (metis join1.simps(7) list.exhaust option.discI)
  moreover obtain z zs' where zs_eq: "zs = z # zs'"
    using hyp by (metis join1.simps(8) join1_commute 
        neq_Nil_conv option.distinct(1) self_join1) 
  ultimately have "join1 (as, bs') = Some (zs')"
    using join1_Cons_SomeD1 hyp by auto
  thus ?thesis
    using bs_eq zs_eq by blast
qed


lemma join1_assoc1: "Some jabc = join1 (a, jbc) \<Longrightarrow> join1 (b, c) = Some jbc 
  \<Longrightarrow> \<exists>y. join1 (a, b) = Some y"
proof ((induct "(a,b)" arbitrary: a b c jbc jabc rule: join1.induct), 
    goal_cases NilNil Nones SNone NSome SSome Nil1 Nil2 Nil3 Nil4)
  case (Nones as bs c jbc jabc)
  then show ?case
    by (metis join1.simps(2) join1_Cons_Some_exI 
        list.inject option.simps(9))
next
  case (SNone a as bs c jbc jabc)
  then show ?case
    by (metis (no_types, lifting) join1.simps(3) join1_Cons_Some_exI 
        list.inject option.simps(9)) 
next
  case (NSome as b bs c jbc jabc)
  then show ?case
    by (metis (no_types, lifting) join1.simps(4) join1_Cons_Some_exI 
        list.inject option.simps(9))
next
  case (SSome a as b bs c jbc jabc)
  obtain bc bcs abc abcs c' cs 
    where jbc_eq: "jbc = bc # bcs" 
    and jabc_eq: "jabc = abc # abcs"
    and c_eq: "c = c' # cs"
    and eq1: "join1 (as, bcs) = Some abcs"
    and eq2: "join1 (bs, cs) = Some bcs"
    using join1_Cons_Some_exI[OF SSome(3)] 
      join1_Cons_Some_exI[OF SSome(2)[symmetric]]
    by auto
  note join1_Cons_SomeD2[OF SSome(3)[unfolded c_eq jbc_eq], simplified]
    join1_Cons_SomeD2[OF SSome(2)[symmetric, unfolded jabc_eq jbc_eq], simplified]
  hence "a = b"
    by blast
  thus ?case 
    using SSome(1)[OF _ eq1[symmetric] eq2]
    by auto
next
  case (Nil1 a as c jbc jabc)
  then show ?case
    using join1_eq_lengths by force
next
  case (Nil2 a as c jbc jabc)
  then show ?case 
    using join1_eq_lengths by force
qed (auto dest: join1_Cons_Some_exI)

lemma join1_assoc2: "Some jabc = join1 (a, jbc) \<Longrightarrow> join1 (b, c) = Some jbc 
  \<Longrightarrow> join1 (a, jbc) = join1 (the (join1 (a, b)), c)"
proof ((induct "(a,b)" arbitrary: a b c jbc jabc rule: join1.induct), 
    goal_cases NilNil Nones SNone NSome SSome Nil1 Nil2 Nil3 Nil4)
  case (NilNil c jbc jabc)
  then show ?case
    by clarsimp (metis join1_commute self_join1)
next
  case (Nones as bs c jbc jabc)
  then obtain abc abcs bc bcs c' cs
    where jbc_eq: "jbc = bc # bcs" 
    and jabc_eq: "jabc = abc # abcs"
    and c_eq: "c = c' # cs"
    and eq1: "join1 (as, bcs) = Some abcs"
    and eq2: "join1 (bs, cs) = Some bcs"
    using join1_Cons_Some_exI[OF Nones(3)] 
      join1_Cons_Some_exI[OF Nones(2)[symmetric]]
    by auto 
  hence "c' = bc"
    using Nones(3) by simp
  then show ?case
    using Nones(1)[OF eq1[symmetric] eq2] Nones(2,3)
    apply (clarsimp simp: c_eq jbc_eq)
    by (metis (no_types, lifting) eq1 join1_Cons_None(1) join1_assoc1 
        option.discI option.map_sel)
next
  case (SNone a as bs c jbc jabc)
  then obtain abc abcs bc bcs c' cs
    where jbc_eq: "jbc = bc # bcs"
    and jabc_eq: "jabc = abc # abcs"
    and c_eq: "c = c' # cs"
    and eq1: "join1 (as, bcs) = Some abcs"
    and eq2: "join1 (bs, cs) = Some bcs"
    using join1_Cons_Some_exI[OF SNone(3)] 
      join1_Cons_Some_exI[OF SNone(2)[symmetric]]
    by auto 
  hence "c' = bc" "abc = Some a"
    using SNone(2,3) 
    by simp_all (metis join1_Cons_SomeD2 not_None_eq)
  then show ?case
    using SNone(1)[OF eq1[symmetric] eq2] SNone(2,3)
    apply (clarsimp simp: c_eq jbc_eq)
    by (smt (z3) join1.simps(1,3,5,6) join1_Cons_SomeD2 
        join1_Cons_Some_exI join1_assoc1 list.inject option.distinct(1)  
        option.exhaust_sel option.inject option.map_disc_iff)
next
  case (NSome as b bs c jbc jabc)
  then obtain abc abcs bc bcs c' cs
    where jbc_eq: "jbc = bc # bcs"
    and jabc_eq: "jabc = abc # abcs"
    and c_eq: "c = c' # cs"
    and eq1: "join1 (as, bcs) = Some abcs"
    and eq2: "join1 (bs, cs) = Some bcs"
    using join1_Cons_Some_exI[OF NSome(3)] 
      join1_Cons_Some_exI[OF NSome(2)[symmetric]]
    by auto 
  note join1_Cons_SomeD2[OF NSome(3)[unfolded c_eq jbc_eq], simplified]
    join1_Cons_SomeD2[OF NSome(2)[symmetric, unfolded jabc_eq jbc_eq], simplified]
  hence "abc = bc" and "bc = Some b" 
    and "c' = None \<or> c' = Some b"
    by blast+
  then show ?case
    using NSome(1)[OF eq1[symmetric] eq2] NSome(2,3)
    unfolding c_eq jbc_eq
    apply (elim disjE; clarsimp simp: c_eq jbc_eq)
    by (metis (no_types, lifting) eq1 join1_Cons_None(2) join1_assoc1 option.distinct(1) option.map_sel)
      (metis eq1 join1.simps(5) join1_assoc1 option.map_sel option.simps(3))
next
  case (SSome a as b bs c jbc jabc)
    then obtain abc abcs bc bcs c' cs
    where jbc_eq: "jbc = bc # bcs"
    and jabc_eq: "jabc = abc # abcs"
    and c_eq: "c = c' # cs"
    and eq1: "join1 (as, bcs) = Some abcs"
    and eq2: "join1 (bs, cs) = Some bcs"
    using join1_Cons_Some_exI[OF SSome(3)] 
      join1_Cons_Some_exI[OF SSome(2)[symmetric]]
    by auto 
  note join1_Cons_SomeD2[OF SSome(3)[unfolded c_eq jbc_eq], simplified]
    join1_Cons_SomeD2[OF SSome(2)[symmetric, unfolded jabc_eq jbc_eq], simplified]
  hence "a = b" and "abc = bc" 
    and "bc = Some b" and "c' = None \<or> c' = Some b"
    by blast+
  then show ?case
    using SSome(1)[OF _ eq1[symmetric] eq2] SSome(2,3)
    unfolding c_eq jbc_eq
    apply (elim disjE; clarsimp simp: c_eq jbc_eq)
    by (metis (no_types, lifting) eq1 join1_Cons_None(2) join1_assoc1 option.distinct(1) option.map_sel)
      (metis eq1 join1.simps(5) join1_assoc1 option.map_sel option.simps(3))
qed (auto dest: join1_assoc1)

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

definition join :: "'a table \<Rightarrow> bool \<Rightarrow> 'a table \<Rightarrow> 'a table" 
  where "join A pos B = (if pos then Option.these (join1 ` (A \<times> B))
    else A - Option.these (join1 ` (A \<times> B)))"

abbreviation nat_join :: "'a option list set \<Rightarrow> 'a option list set 
  \<Rightarrow> 'a option list set" (infixl "\<bowtie>" 70)
  where "R1 \<bowtie> R2 \<equiv> join R1 True R2"

lemma join_True_code[code]: "A \<bowtie> B = (\<Union>a \<in> A. \<Union>b \<in> B. set_option (join1 (a, b)))"
  unfolding join_def by (force simp: Option.these_def image_iff)

lemma join_False_alt: "join X False Y = X - X \<bowtie> Y"
  unfolding join_def by auto

lemma join_False_code[code]: "join A False B = {a \<in> A. \<forall>b \<in> B. join1 (a, b) \<noteq> Some a}"
  unfolding join_False_alt join_True_code
  by (auto simp: Option.these_def image_iff dest: self_join1)

lemma join_commute: "R1 \<bowtie> R2 = R2 \<bowtie> R1"
  unfolding join_def 
  using join1_commute
  by (auto simp: image_def Option.these_def)
    fastforce+

lemma join_assoc: "R1 \<bowtie> (R2 \<bowtie> R3) = R1 \<bowtie> R2 \<bowtie> R3"
  unfolding join_def 
  apply (clarsimp simp: Option.these_def)
  apply (intro set_eqI iffI; clarsimp simp: image_iff)
   apply (rename_tac a jabc b c jbc)
   apply (rule_tac x="Some jabc" in exI, clarsimp)
  apply (intro conjI)
    apply (rule_tac x="join1 (a,b)" in exI; intro conjI; clarsimp?)
     apply (rule_tac x=a in bexI; clarsimp?)
      apply (rule_tac x=b in bexI; clarsimp)
  using join1_assoc1 apply force
    apply (rule_tac x=c in bexI; clarsimp?)
  using join1_assoc2 apply force
   apply metis
   apply (rename_tac jabc a b c jab)
   apply (rule_tac x="Some jabc" in exI, clarsimp)
  apply (intro conjI)
   apply (rule_tac x=a in bexI; clarsimp?)
    apply (rule_tac x="join1 (b,c)" in exI; intro conjI; clarsimp?)
     apply (rule_tac x=b in bexI; clarsimp?)
     apply (rule_tac x=c in bexI; clarsimp?)
    apply (metis join1_assoc1 join1_commute)
  apply (smt (verit, best) join1_assoc2 join1_commute)
  using join1_assoc1 by force

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
  "table n X R \<Longrightarrow> R \<bowtie> unit_table n = R"
  "table n X R \<Longrightarrow> unit_table n \<bowtie> R = R"
  by (auto simp: join_def image_def unit_table_def table_def 
      wf_tuple_def join1_replicate_None Option.these_def)

lemma join_unit_unit [simp]: "join (unit_table n) True (unit_table n) = unit_table n"
  by (rule join_unit_table[OF unit_table[OF refl]])

lemma join_unitD: "table n X R1 \<Longrightarrow> table n Y R2 \<Longrightarrow> join R1 True R2 = unit_table n 
  \<Longrightarrow> R1 = unit_table n \<and> R2 = unit_table n"
  by (clarsimp simp: unit_table_def join_def Option.these_def image_def set_eq_iff)
    (metis (no_types, opaque_lifting) join1_replicate_None join1_replicate_None_iff 
      option.sel table_def wf_tuple_def)

lemma join_empty [simp]:
  "R \<bowtie> {} = {}"
  "{} \<bowtie> R = {}"
  by (auto simp: join_def Option.these_def)

lemma join_empty_table:
  "R \<bowtie> empty_table = empty_table"
  "empty_table \<bowtie> R = empty_table"
  by (auto simp: empty_table_def)

lemma join_sub_tables_eq:
  "table n X R\<^sub>1 \<Longrightarrow> table n Y R\<^sub>2 \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> R\<^sub>1 \<bowtie> R\<^sub>2 = {v \<in> R\<^sub>1. (restrict Y v) \<in> R\<^sub>2 }"
  using join1_Some_sub_tuples1 join1_Some_sub_tuples2
  unfolding table_def join_def 
  by (auto simp: Option.these_def image_iff)
    (smt (z3) Un_absorb2 join1_Some_restrict option.sel restrict_idle)+

lemma join_eq_interI: 
  "table n X R1 \<Longrightarrow> table n X R2 \<Longrightarrow> R1 \<bowtie> R2 = R1 \<inter> R2"
  apply (intro set_eqI iffI; clarsimp simp: join_def image_def Option.these_def table_def)
  using join1_Some_wf_tuple_eqD(2,3) apply blast
  using join1_self by (metis option.sel)

lemma foldr_join_tables_eq_InterI:
  "\<forall>R\<in>set Rs. table n X R \<Longrightarrow> foldr (\<bowtie>) Rs (unit_table n) = 
  (if Rs = [] then unit_table n else (\<Inter> (set Rs)))"
  apply (induct Rs arbitrary: n X; clarsimp simp: join_unit_table(1))
  using table_InterI[of "set _"] join_eq_interI
  by (metis set_empty2)

lemma join_union_distrib: 
  "R1 \<bowtie> (R2 \<union> R3) = R1 \<bowtie> R2 \<union> R1 \<bowtie> R3"
  "(R1 \<union> R2) \<bowtie> R3 = R1 \<bowtie> R3 \<union> R2 \<bowtie> R3"
  by (auto simp: join_True_code)

lemma join_Un_distrib:
  "R \<bowtie> (\<Union>i\<in>\<I>. \<R> i) = (\<Union>i\<in>\<I>. R \<bowtie> (\<R> i))"
  "(\<Union>i\<in>\<I>. \<R> i) \<bowtie> R = (\<Union>i\<in>\<I>. (\<R> i) \<bowtie> R)"
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


subsection \<open> N-ary join \<close>

term sum
term comm_monoid_set.F
term Finite_Set.fold

interpretation join_comp_fun: comp_fun_commute_on "UNIV" "(\<bowtie>)"
  apply standard
  apply (rule ext; clarsimp)
  apply (subst join_assoc)
  apply (subst join_assoc)
  apply (subst join_commute)
  by simp

interpretation join_ab_semigroup: ab_semigroup_mult "(\<bowtie>)"
  by (standard, clarsimp simp: join_assoc, clarsimp simp: join_commute)

interpretation join_monoid: comm_monoid_set "(\<bowtie>)" "unit_table n"
  apply (standard)
  oops

lemma join_idemp[simp]: "table n X R \<Longrightarrow> R \<bowtie> R = R"
  apply (intro set_eqI iffI; clarsimp simp: join_def Option.these_def image_iff table_def)
  using join1_Some_wf_tuple_eqD(2)
  by blast (metis join1_self option.sel)

definition nary_join :: "nat \<Rightarrow> 'a option list set set \<Rightarrow> 'a option list set"
  where eq_fold: "nary_join n \<R> = Finite_Set.fold (\<bowtie>) (unit_table n) \<R>"

lemma infinite_nary_join [simp]: "\<not> finite \<R> \<Longrightarrow> nary_join n \<R> = unit_table n"
  by (simp add: eq_fold)

lemma nary_join_empty [simp]: "nary_join n {} = unit_table n"
  by (simp add: eq_fold)

lemma nary_join_insert [simp]: 
  "finite \<R> \<Longrightarrow> R \<notin> \<R> \<Longrightarrow> nary_join n (insert R \<R>) = R \<bowtie> nary_join n \<R>"
  "finite \<R> \<Longrightarrow> R \<in> \<R> \<Longrightarrow> nary_join n (insert R \<R>) = nary_join n \<R>"
  by (simp add: eq_fold)
    (induct \<R> arbitrary: R rule: infinite_finite_induct, simp_all add: insert_absorb)

lemma nary_join_set: "nary_join n (set (R # Rs)) 
  = (if R \<in> set Rs then nary_join n (set Rs) else R \<bowtie> nary_join n (set Rs))"
  by (simp split: if_splits)

lemma nary_join_with_empty: "finite \<R> \<Longrightarrow> {} \<in> \<R> \<Longrightarrow> nary_join n \<R> = {}"
  by (induct \<R> rule: infinite_finite_induct) auto

lemma join_nary_join_elem: "\<forall>R\<in>\<R>. table n (X R) R \<Longrightarrow> finite \<R> \<Longrightarrow> R \<in> \<R> 
  \<Longrightarrow> R \<bowtie> nary_join n \<R> = nary_join n \<R>"
proof (induct \<R> arbitrary: R rule: infinite_finite_induct)
  case (insert C \<C>)
  hence "C \<bowtie> (C \<bowtie> nary_join n \<C>) = C \<bowtie> nary_join n \<C>"
    by (simp add: join_assoc)
      (subst join_idemp, auto)
  hence "R = C \<Longrightarrow> ?case"
    using insert by simp
  moreover have "R \<in> \<C> \<Longrightarrow> ?case"
    using insert.hyps insert.prems
    by (clarsimp, subst join_assoc, subst join_commute)
      (clarsimp simp: join_assoc[symmetric])
  ultimately show ?case 
    using insert.prems by blast
qed simp_all

lemma nary_join_insert_table: 
  "\<forall>R\<in>\<R>. \<exists>X. table n X R \<Longrightarrow> finite \<R> \<Longrightarrow> nary_join n (insert R \<R>) = R \<bowtie> nary_join n \<R>"
  apply (induct \<R> arbitrary: R rule: infinite_finite_induct)
  by (simp, simp) (metis insert_absorb join_nary_join_elem nary_join_insert(1))

lemma nary_join_remove:
  assumes "finite \<R>" and "R \<in> \<R>"
  shows "nary_join n \<R> = R \<bowtie> nary_join n (\<R> - {R})"
proof -
  from \<open>R \<in> \<R>\<close> obtain \<R>' where R_eq: "\<R> = insert R \<R>'" and "R \<notin> \<R>'"
    by (auto dest: mk_disjoint_insert)
  moreover from \<open>finite \<R>\<close> R_eq have "finite \<R>'" by simp
  ultimately show ?thesis by simp
qed

lemma nary_join_insert_remove: 
  "finite \<R> \<Longrightarrow> nary_join n (insert R \<R>) = R \<bowtie> nary_join n (\<R> - {R})"
  by (cases "R \<in> \<R>") (simp_all add: nary_join_remove insert_absorb)

lemma nary_join_insert_if: "finite \<R> 
  \<Longrightarrow> nary_join n (insert R \<R>) = (if R \<in> \<R> then nary_join n \<R> else R \<bowtie> nary_join n \<R>)"
  by (cases "R \<in> \<R>") (simp_all add: insert_absorb)

lemma nary_join_neutral: "\<forall>R\<in>\<R>. R = unit_table n \<Longrightarrow> nary_join n \<R> = unit_table n"
  by (induct \<R> rule: infinite_finite_induct) simp_all

lemma table_nary_joinI: "finite \<R> \<Longrightarrow> \<forall>R\<in>\<R>. table n (X R) R 
  \<Longrightarrow> table n (\<Union>R\<in>\<R>. X R) (nary_join n \<R>)"
  by (induct \<R> rule: infinite_finite_induct) (simp_all, metis join_table)

lemma nary_join_union_inter:
  assumes "finite \<C>" and "finite \<D>"
  shows "nary_join n (\<C> \<union> \<D>) \<bowtie> nary_join n (\<C> \<inter> \<D>) = nary_join n \<C> \<bowtie> nary_join n \<D>"
  using assms
proof (induct \<C>)
  case empty
  then show ?case 
    by (simp add: join_commute)
next
  case (insert x \<C>)
  then show ?case
    by (auto simp: insert_absorb Int_insert_left; 
        simp add: join_ab_semigroup.mult.left_commute join_ab_semigroup.mult_assoc)
qed

corollary nary_join_union_inter_neutral:
  assumes "finite \<C>" and "finite \<D>" 
    and "\<forall>R\<in>\<C>\<inter>\<D>. R = unit_table n"
    and "\<forall>R\<in>\<C>\<union>\<D>. table n (X R) R"
  shows "nary_join n (\<C> \<union> \<D>) = nary_join n \<C> \<bowtie> nary_join n \<D>"
  using nary_join_union_inter[OF assms(1,2)] 
    nary_join_neutral[OF assms(3)]
    table_nary_joinI[OF _ assms(4)]
  by (metis assms(1,2) finite_Un join_unit_table(1))

corollary nary_join_union_disjoint:
  assumes "finite \<C>" and "finite \<D>"     
    and "\<forall>R\<in>\<C>\<union>\<D>. table n (X R) R"
    and "\<C> \<inter> \<D> = {}"
  shows "nary_join n (\<C> \<union> \<D>) = nary_join n \<C> \<bowtie> nary_join n \<D>"
  using assms by (simp add: nary_join_union_inter_neutral)

lemma nary_join_union_diff:
  assumes "finite \<C>" and "finite \<D>" and "\<forall>R\<in>\<C>\<union>\<D>. table n (X R) R"
  shows "nary_join n (\<C> \<union> \<D>) = nary_join n (\<C> - \<D>) \<bowtie> nary_join n (\<D> - \<C>) \<bowtie> nary_join n (\<C> \<inter> \<D>)"
proof -
  have "\<C> \<union> \<D> = (\<C> - \<D>) \<union> (\<D> - \<C>) \<union> \<C> \<inter> \<D>"
    by auto
  with assms show ?thesis
    apply simp
    by (subst nary_join_union_disjoint, simp_all; (subst nary_join_union_disjoint)?) auto
qed

lemma nary_join_subset_diff:
  assumes "\<D> \<subseteq> \<C>" and "finite \<C>" and "\<forall>R\<in>\<C>. table n (X R) R"
  shows "nary_join n \<C> = nary_join n (\<C> - \<D>) \<bowtie> nary_join n \<D>"
proof -
  from assms have "finite (\<C> - \<D>)" 
    by auto
  moreover have "finite \<D>"
    using assms(1,2) by (rule finite_subset)
  moreover from assms have "(\<C> - \<D>) \<inter> \<D> = {}"
    using assms by auto
  ultimately have "nary_join n (\<C> - \<D> \<union> \<D>) = nary_join n(\<C> - \<D>) \<bowtie> nary_join n \<D>" 
    using assms
    by (subst nary_join_union_disjoint) auto
  moreover from assms have "\<C> \<union> \<D> = \<C>" 
    by auto
  ultimately show ?thesis 
    by simp
qed

lemma nary_join_inter_diff:
  assumes "finite \<C>" and "\<forall>R\<in>\<C>. table n (X R) R"
  shows "nary_join n \<C> = nary_join n (\<C> \<inter> \<D>) \<bowtie> nary_join n (\<C> - \<D>)"
  using assms
  by (subst nary_join_subset_diff[where \<D>="\<C> - \<D>" and X=X])
    (auto simp:  Diff_Diff_Int assms)

lemma nary_join_setdiff_irrelevant:
  assumes "finite \<C>" and "\<forall>R\<in>\<C>. table n (X R) R"
  shows "nary_join n (\<C> - {unit_table n}) = nary_join n \<C>"
  using assms 
  apply (induct \<C>) 
  by (simp_all add: insert_Diff_if)
    (metis boolean_algebra.conj_zero_right empty_table_def finite.emptyI 
      join_commute nary_join_empty nary_join_union_disjoint union_empty_table_eq(2))

lemma nary_join_not_neutral_contains_not_neutral:
  assumes "nary_join n \<C> \<noteq> unit_table n"
  obtains R where "R \<in> \<C>" and "R \<noteq> unit_table n"
proof -
  from assms have "\<exists>R\<in>\<C>. R \<noteq> unit_table n"
  proof (induct \<C> rule: infinite_finite_induct)
    case infinite
    then show ?case by simp
  next
    case empty
    then show ?case by simp
  next
    case (insert R \<C>)
    then show ?case by fastforce
  qed
  with that show thesis by blast
qed

lemma UNION_disjoint:
  assumes "finite I" and "\<forall>i\<in>I. finite (\<C> i)"
    and "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> \<C> i \<inter> \<C> j = {}"
    and "\<forall>R\<in>(\<Union>i\<in>I. \<C> i). table n (X R) R"
  shows "nary_join n (\<Union>(\<C> ` I)) = nary_join n ((\<lambda>x. nary_join n (\<C> x)) ` I)"
  using assms
proof (induction rule: finite_induct)
  case (insert i I)
  hence "\<forall>j\<in>I. j \<noteq> i"
    by blast
  hence obs1: "\<C> i \<inter> \<Union>(\<C> ` I) = {}"
    using insert.prems by blast
  have obs2: "finite (\<Union> (\<C> ` I))"
    using insert by auto
  have obs3: "\<forall>R\<in>\<C> i \<union> \<Union> (\<C> ` I). table n (X R) R"
    using insert by auto
  hence obs4: "\<forall>R\<in>(\<lambda>x. nary_join n (\<C> x)) ` I. \<exists>X. table n X R"
    apply (clarsimp, rename_tac j)
    apply (rule_tac x="\<Union>R\<in>(\<C> j). X R" in exI)
    using insert by (auto intro!: table_nary_joinI)
  thus ?case
    apply (simp, subst nary_join_union_disjoint[OF insert(4)[rule_format] obs2 obs3 obs1]; clarsimp)
    apply(subst nary_join_insert_table)
    using insert by force+
qed auto

lemma foldr_join_tables_eq_nary_join[simp]: "\<forall>R\<in>set Rs. \<exists>X. table n X R 
  \<Longrightarrow> foldr (\<lambda>r1 r2. join r1 True r2) Rs (unit_table n) = (nary_join n (set Rs))"
  by (induct Rs arbitrary: n) (auto simp: nary_join_insert_table)

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

lemma qtable_unique_vars:
  "R \<noteq> {} \<Longrightarrow> X \<subseteq> {m. m < n} \<Longrightarrow> Y \<subseteq> {m. m < n} \<Longrightarrow> table n X R \<Longrightarrow> table n Y R \<Longrightarrow> X = Y"
  by (auto simp: table_def wf_tuple_def subset_eq)

lemma qtable_unique_pred:
  "qtable n X P Q1 R \<Longrightarrow> qtable n X P Q2 R \<Longrightarrow> (\<forall>v. P v \<longrightarrow> wf_tuple n X v \<longrightarrow> Q1 v = Q2 v)"
  by (auto simp: qtable_iff fun_eq_iff)

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
  by (simp add: qtable_empty_vars_iff) (* replace everywhere with qtable_empty_varsD(1) *)

lemma qtable_empty_unit_table:
  "qtable n {} R P empty_table \<Longrightarrow> qtable n {} R (\<lambda>v. \<not> P v) (unit_table n)"
  by (auto simp: qtable_iff wf_tuple_empty_iff unit_table_def table_empty_vars_iff)

lemma qtable_unit_empty_table:
  "qtable n {} R P (unit_table n) \<Longrightarrow> qtable n {} R (\<lambda>v. \<not> P v) empty_table"
  by (auto simp: qtable_iff wf_tuple_empty_iff unit_table_def table_empty_vars_iff)

lemma qtable_nonempty_empty_table:
  "qtable n {} R P X \<Longrightarrow> x \<in> X \<Longrightarrow> qtable n {} R (\<lambda>v. \<not> P v) empty_table"
  by (frule qtable_empty_varsD(1)) (auto dest: qtable_unit_empty_table)


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

lemma qtable_union_iff: "qtable n Z P Q1 R1 \<Longrightarrow> qtable n Z P Q2 R2
  \<Longrightarrow> qtable n Z P Q (R1 \<union> R2)
  \<longleftrightarrow> (\<forall>v. P v \<longrightarrow> wf_tuple n Z v \<longrightarrow> Q v = (Q1 v \<or> Q2 v))"
  by (auto simp: qtable_iff)

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

lemma qtable_Inter_list:
  "Rs \<noteq> [] \<Longrightarrow> (\<And>i. i < length Rs \<Longrightarrow> qtable n X P (Qi i) (Rs ! i)) 
  \<Longrightarrow> (\<And>x. wf_tuple n X x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> (\<forall>i<length Rs. Qi i x)) 
  \<Longrightarrow> qtable n X P Q (\<Inter> (set Rs))"
proof (induct Rs arbitrary: n X Q Qi)
  case (Cons R Rs)
  hence "Rs = [] \<Longrightarrow> ?case"
    by clarsimp (metis qtable_cong_strong)
  moreover have "Rs \<noteq> [] \<Longrightarrow> ?case"
    apply (simp, rule_tac qtable_inter[OF Cons.prems(2)[of 0, simplified]])
     apply (rule Cons.hyps[of n X "\<lambda>i. Qi (Suc i)"]; clarsimp?)
    using Cons.prems(2,3) by (force, auto simp: less_Suc_eq_0_disj)
  ultimately show ?case
    by blast
qed simp

lemma qtable_Inter:
  assumes "finite I" "I \<noteq> {}" 
    and "(\<And>i. i \<in> I \<Longrightarrow> qtable n X P (Qi i) (Ri i))"
    and "(\<And>x. wf_tuple n X x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> (\<forall>i \<in> I. Qi i x))"
  shows "qtable n X P Q (\<Inter>i \<in> I. Ri i)"
proof-
  obtain m::nat and f 
    where I_eq: "I = f ` {i. i < m}" 
      and "m > 0"
    using \<open>finite I\<close> \<open>I \<noteq> {}\<close>
    by (metis Collect_empty_eq finite_imp_nat_seg_image_inj_on 
        gr0I image_is_empty less_nat_zero_code)
  then obtain "Rs" 
    where Rs_def: "\<And>i. i < length Rs \<Longrightarrow> Rs ! i = Ri (f i)"
    and len_Rs: "length Rs = m"
    by (atomize_elim, rule_tac x="map (Ri \<circ> f) [0..<m]" in exI, force)
  hence to_set: "set Rs = Ri ` I"
    by (clarsimp simp: I_eq, safe) 
      (metis image_eqI in_set_conv_nth mem_Collect_eq,
        metis in_set_conv_nth)
  hence "Rs \<noteq> []"
    using I_eq \<open>I \<noteq> {}\<close> by force
  moreover have "\<And>i. i < length Rs \<Longrightarrow> qtable n X P ((Qi \<circ> f) i) (Rs ! i)"
    and "\<And>x. wf_tuple n X x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> (\<forall>i<length Rs. (Qi \<circ> f) i x)"
    using assms(3,4) Rs_def len_Rs
    by (simp add: I_eq)+
  ultimately have "qtable n X P Q (\<Inter> (set Rs))"
    using qtable_Inter_list[of Rs n X P "Qi \<circ> f"] by force
  thus "qtable n X P Q (\<Inter>i \<in> I. Ri i)"
    unfolding to_set .
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

lemma mem_restr_join1l: "mem_restr U z \<Longrightarrow> join1 (x, y) = Some z \<Longrightarrow> mem_restr U x"
  apply (induct "(x, y)" arbitrary: x y z U rule: join1.induct)
  by (auto simp: list_all2_Cons1 mem_restr_def split: if_splits) blast+

lemma mem_restr_join1r: "mem_restr U z \<Longrightarrow> join1 (x, y) = Some z \<Longrightarrow> mem_restr U y"
  apply (induct "(x, y)" arbitrary: x y z U rule: join1.induct)
  by (auto simp: list_all2_Cons1 mem_restr_def split: if_splits) blast+

lemma qtable_mem_restr_UNIV: "qtable n X (mem_restr UNIV) Q R = wf_table n X Q R"
  unfolding qtable_def by auto

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


subsubsection \<open> N-ary join \<close>

lemma qtable_nary_join_list:
  "(\<And>i. i < length Rs \<Longrightarrow> qtable n (X i) P (Qi i) (Rs ! i)) 
  \<Longrightarrow> (\<And>i. i < length Rs \<Longrightarrow> X i \<subseteq> {m. m < n})
  \<Longrightarrow> (\<And>X Y v i. P v \<Longrightarrow> wf_tuple n Y v \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> P (restrict X v))
  \<Longrightarrow> (\<And>v. P v \<Longrightarrow> wf_tuple n (\<Union>i<length Rs. X i) v 
    \<Longrightarrow> Q v \<longleftrightarrow> (\<forall>i<length Rs. Qi i (restrict (X i) v))) 
  \<Longrightarrow> qtable n (\<Union>i<length Rs. X i) P Q (nary_join n (set Rs))"
proof (induct Rs arbitrary: n X Q Qi)
  case Nil
  then show ?case
    apply (clarsimp simp: qtable_unit_iff)
    using wf_tuple_empty_iff by blast
next
  case (Cons R Rs)
  let ?U = "\<Union> (X ` {..<Suc (length Rs)})"
  have "\<Union> (X ` {..<Suc 0}) = X 0"
    by auto
  hence "Rs = [] \<Longrightarrow> ?case"
    using Cons.prems(1,4)
      join_unit_table(1)[OF qtableD(1)[of n "X 0" P "Qi 0" R]]
    by clarsimp (smt (verit, best) qtable_cong_strong restrict_idle)
  moreover have "{} \<in> set (R # Rs) \<Longrightarrow> ?case"
  proof-
    assume hyp: "{} \<in> set (R # Rs)"
    then obtain i 
      where i_le: "i < length (R # Rs)" 
        and "(R # Rs) ! i = {}"
        and "qtable n (X i) P (Qi i) {}"
      unfolding in_set_conv_nth[of "{}" "R # Rs"]
      using Cons.prems(1) by force
    hence "\<forall>v. P v \<longrightarrow> wf_tuple n (X i) v \<longrightarrow> \<not> Qi i v"
      unfolding qtable_iff by auto
    moreover have "\<forall>v. P v \<longrightarrow> wf_tuple n ?U v \<longrightarrow> P (restrict (X i) v)"
      using i_le Cons.prems(3)[of _ ?U "X i"] 
      by auto
    moreover have "\<forall>v. P v \<longrightarrow> wf_tuple n ?U v \<longrightarrow> wf_tuple n (X i) (restrict (X i) v)"
      using i_le wf_tuple_restrict_simple[of n ?U _ "X i"] 
      by auto
    moreover have nary_simp: "nary_join n (set (R # Rs)) = {}"
      using hyp
      by (subst nary_join_with_empty) 
        simp_all
    ultimately show ?thesis
      apply (clarsimp simp: qtable_iff)
      apply (erule_tac x="restrict (X i) v" in allE)
      using Cons.prems(4) i_le by auto
  qed
  moreover have "Rs \<noteq> [] \<Longrightarrow> {} \<notin> set (R # Rs) \<Longrightarrow> ?case"
  proof-
    assume "Rs \<noteq> []" 
      and no_empty: "{} \<notin> set (R # Rs)"
    hence qtableR: "qtable n (X 0) P (Qi 0) R"
      and qtables: "\<And>i. i < length Rs \<Longrightarrow> qtable n (X (Suc i)) P (Qi (Suc i)) (Rs ! i)" 
      and wf_vars: "\<And>i. i < length Rs \<Longrightarrow> (X \<circ> Suc) i \<subseteq> {m. m < n}"
      and empty_case: "\<And>i. i < length Rs \<Longrightarrow> Rs ! i = {} \<Longrightarrow> length Rs \<noteq> 1 
        \<Longrightarrow> (X \<circ> Suc) i \<in> {(X \<circ> Suc) j |j. j \<noteq> i \<and> j < length Rs}"
      using Cons.prems(1,2) \<open>Rs \<noteq> []\<close> 
      by (fastforce, fastforce, fastforce, metis list.set_intros(2) nth_mem)
    then show ?thesis
    proof(cases "R \<in> set Rs")
      case True
      then obtain i where i_def: "Rs ! i = R" 
        and i_le: "i < length Rs"
        by (meson in_set_conv_nth)
      hence "table n (X 0) R" "table n (X (Suc i)) R"
        using qtableD(1)[OF qtableR]
          qtableD(1)[OF Cons.prems(1)[of "Suc i"]]
        by auto
      hence eq_vars: "X 0 = X (Suc i)"
        using no_empty Cons.prems(2)[of 0]
          Cons.prems(2)[of "Suc i"] \<open>i < length Rs\<close>
        by (auto simp: table_def wf_tuple_def subset_eq)
      hence rw_vars: "?U = \<Union> ((X \<circ> Suc) ` {..<length Rs})" (is "_ = ?U'")
        apply (rule_tac f=\<Union> in arg_cong)
        using i_le less_Suc_eq_0_disj by auto
      show ?thesis
        using True
        apply simp
        unfolding rw_vars
        apply (rule Cons.hyps[of n "X \<circ> Suc" "Qi \<circ> Suc"])
        using qtables apply force
        using wf_vars apply force
        using Cons.prems(3) apply force
        subgoal for v
          using Cons.prems(4)[simplified, unfolded rw_vars, of v]
          apply clarsimp
          apply (intro conjI impI allI iffI)
           apply force
          subgoal for j
            apply (cases "j=0"; clarsimp)
             apply (erule_tac x=i in allE)
            using i_le apply clarsimp
            using qtable_unique_pred[OF qtables[OF i_le, unfolded i_def] qtableR[unfolded eq_vars]]
              wf_tuple_restrict_simple[of n ?U' v "X 0", simplified]
              Cons.prems(3)[of v ?U' "X 0", simplified]
            apply (metis SUP_upper eq_vars lessThan_iff)
            using less_Suc_eq_0_disj by auto
          done
        done
    next
      case False
      then show ?thesis
        using \<open>Rs \<noteq> []\<close>
        apply simp
        apply (rule qtable_join[OF qtableR, where b=True, simplified])
           apply (rule Cons.hyps[of n "X \<circ> Suc" "Qi \<circ> Suc"])
        using qtables apply force
        using wf_vars apply force
        using Cons.prems(3) apply force
        apply force
           prefer 2 subgoal for v
          using Cons.prems(3)[of v ?U "\<Union>((X \<circ> Suc) ` {..<length Rs})"]
            Cons.prems(3)[of v "\<Union> (X ` _)" "X 0"] by force
         subgoal
          apply (intro set_eqI iffI; clarsimp)
          using less_Suc_eq_0_disj by force blast
        subgoal for v
          using Cons.prems(4)[of v, simplified] apply clarsimp
          apply (intro conjI impI allI iffI; clarsimp)
           apply (subst sub_restrict_restrict)
          apply force
           apply force
          subgoal for j
            apply (cases "j=length Rs", clarsimp)
            apply (erule_tac x="j-1" in allE)
            apply clarsimp
            apply (subst (asm) sub_restrict_restrict)
              apply auto[1]
            apply (metis Suc_pred length_greater_0_conv lessI lessThan_iff)
            apply (metis length_0_conv lessI lessThan_iff less_Suc_eq_0_disj)
            apply fastforce
            apply (erule_tac x="j-1" in allE)
            apply clarsimp
            apply (subst (asm) sub_restrict_restrict)
             apply (clarsimp simp: subset_eq)
            apply (metis lessThan_iff less_Suc_eq less_imp_diff_less)
            by (metis Suc_pred gr0I less_SucE less_imp_diff_less)
          done
        done
    qed
  qed
  ultimately show ?case
    by blast
qed

no_notation nat_join (infixl "\<bowtie>" 70)

(*<*)
end
(*>*)
