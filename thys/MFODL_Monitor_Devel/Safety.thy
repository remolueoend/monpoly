(*<*)
theory Safety
  imports Formula
begin
(*>*)


section \<open> Safety \<close>


subsection \<open> Preliminaries \<close>

\<comment> \<open> Finiteness \<close>

lemma finite_Union_image_Collect: 
  "finite A \<Longrightarrow> (\<And>X. X \<in> A \<Longrightarrow> finite (f X)) \<Longrightarrow> finite (\<Union>{f X|X. X \<in> A})"
  by (rule finite_Union, auto)

lemma finite_image_Collect: "finite A \<Longrightarrow> finite {f k |k. k \<in> A}"
  apply (subst Collect_mem_eq[where A=A, symmetric])
  by (rule finite_image_set) simp

lemma finite_bounded_\<I>: "bounded I \<Longrightarrow> finite {i |i. memL I i \<and> memR I i}"
  by (transfer, clarsimp simp: upclosed_def downclosed_def)
    (metis (lifting) infinite_nat_iff_unbounded_le mem_Collect_eq)

lemma finite_bounded_\<I>2: "bounded I \<Longrightarrow> finite {f i |i. memL I (f i) \<and> memR I (f i)}"
  apply (transfer, clarsimp simp: upclosed_def downclosed_def)
  by (smt (verit, best) infinite_nat_iff_unbounded_le mem_Collect_eq)

lemma finite_vimage_set: "finite {x. P x} \<Longrightarrow> inj f \<Longrightarrow> finite {x. P (f x)}"
  using finite_vimageI
  unfolding vimage_def by force

thm finite_vimage_set[OF finite_bounded_\<I>, of _ "\<lambda>k. \<tau> \<sigma> k - \<tau> \<sigma> \<iota>", unfolded inj_on_def, simplified]

lemma finite_vimage_\<tau>_nat: "finite {k. \<tau> \<sigma> k - c = n}"
proof (transfer, clarsimp)
  fix \<sigma> :: "('a \<times> nat) stream" 
    and c :: nat 
    and n :: nat
  assume h1: "ssorted (smap snd \<sigma>)"
    and h2: "sincreasing (smap snd \<sigma>)"
  have "\<exists>k. n < snd (\<sigma> !! k) - c"
    using h2 sincreasing_grD less_diff_conv 
    by (metis smap_alt)
  moreover have "\<forall>i j. i \<le> j \<longrightarrow> snd (\<sigma> !! i) \<le> snd (\<sigma> !! j)"
    using iffD1[OF ssorted_iff_mono h1] smap_alt by auto
  ultimately show "finite {k. snd (\<sigma> !! k) - c = n}"
    unfolding finite_nat_set_iff_bounded_le
    by (smt (verit, del_insts) add_less_cancel_left diff_le_mono linorder_le_cases 
        mem_Collect_eq nat_arith.rule0 order_less_le_trans zero_order(3))
qed

lemma finite_vimage_\<I>_Until:
  assumes "bounded I"
  shows "finite {k. mem I (\<tau> \<sigma> k - \<tau> \<sigma> \<iota>)}"
proof-
  let ?A = "{{k. \<tau> \<sigma> k - \<tau> \<sigma> \<iota> = n}|n. mem I n}"
  have "?A = (\<lambda>n. {k. \<tau> \<sigma> k - \<tau> \<sigma> \<iota> = n}) ` {i |i. mem I i}"
    by auto
  hence "finite ?A"
    using finite_bounded_\<I>[OF assms] 
    by simp
  moreover have "{k. mem I (\<tau> \<sigma> k - \<tau> \<sigma> \<iota>)} = \<Union>?A"
    by auto
  ultimately show ?thesis
    using finite_Union[of ?A] 
      finite_vimage_\<tau>_nat[of \<sigma> \<open>\<tau> \<sigma> \<iota>\<close>]
    by auto
qed

\<comment> \<open> Pairwise union \<close>

lemma set_eqI2: "(\<And>x. x\<in>A \<Longrightarrow> x\<in>B) \<Longrightarrow> (\<And>x. x\<in>B \<Longrightarrow> x\<in>A) \<Longrightarrow> A = B"
  by auto

lemma eq_singleton_iff: "A = {a} \<longleftrightarrow> a \<in> A \<and> (\<forall>x. x \<in> A \<longrightarrow> x = a)"
  by auto

lemma sub_pair_unfold: "A \<subseteq> {{}, X} \<longleftrightarrow> A = {} \<or> A = {{}} \<or> A = {X} \<or> A = {{},X}"
  by blast

definition pairw_union :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> 'a set set" (infixl "\<uplus>" 70)
  where "A \<uplus> B = (\<lambda>(X, Y). X \<union> Y) ` (A \<times> B)"

lemma pairw_union_eq:
  "A \<uplus> B = {a \<union> b|a b. a \<in> A \<and> b \<in> B}"
  by (auto simp: pairw_union_def)

lemma in_pairw_union_iff: "x \<in> A \<uplus> B \<longleftrightarrow> (\<exists>a b. a \<in> A \<and> b \<in> B \<and> x = a \<union> b)"
  unfolding pairw_union_eq by blast

lemma union_in_pairw_union: "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> a \<union> b \<in> A \<uplus> B"
  by (auto simp: pairw_union_eq)

lemma empty_in_pairw_unionI: "{} \<in> A \<Longrightarrow> {} \<in> B \<Longrightarrow> {} \<in> A \<uplus> B"
  using union_in_pairw_union[where a="{}"] by auto

lemma empty_notin_pairw_unionI:
  "{} \<in> A \<Longrightarrow> {} \<notin> B \<Longrightarrow> {} \<notin> A \<uplus> B" 
  "{} \<notin> A \<Longrightarrow> {} \<in> B \<Longrightarrow> {} \<notin> A \<uplus> B"
  unfolding pairw_union_eq by auto

lemma subset_pairw_unionI:
  "{} \<in> A \<Longrightarrow> B \<subseteq> A \<uplus> B"
  "{} \<in> B \<Longrightarrow> A \<subseteq> A \<uplus> B"
  unfolding pairw_union_eq by auto

lemma pairw_union_empty[simp]:
  "A \<uplus> {} = {}"
  "{} \<uplus> B = {}"
  by (simp_all add: pairw_union_def)

lemma pairw_union_unit[simp]:
  "A \<uplus> {{}} = A"
  "{{}} \<uplus> B = B"
  by (auto simp: pairw_union_def)

lemma pairw_union_UNIV[simp]:
  "A \<noteq> {} \<Longrightarrow> A \<uplus> {UNIV} = {UNIV}"
  "B \<noteq> {} \<Longrightarrow> {UNIV} \<uplus> B = {UNIV}"
  by (auto simp: pairw_union_eq)

lemma pairw_union_commutes: "A \<uplus> B = B \<uplus> A"
  by (auto simp: pairw_union_def)

lemma pairw_union_assoc: "(A \<uplus> B) \<uplus> C = A \<uplus> (B \<uplus> C)"
  apply(rule set_eqI2; clarsimp simp: pairw_union_eq)
  by (rename_tac c a b, rule_tac x=a in exI, rule_tac x="b \<union> c" in exI, blast)
    (rename_tac a b c, rule_tac x="a \<union> b" in exI, rule_tac x=c in exI, blast)

lemma pairw_union_absorbL_iff: 
  "A \<uplus> B = A \<longleftrightarrow> (\<forall>x\<in>A.\<exists>a\<in>A.\<exists>b\<in>B. x = a \<union> b) \<and> (\<forall>a\<in>A. \<forall>b\<in>B. a \<union> b \<in> A)"
  apply (intro iffI set_eqI2)
  by (auto simp: pairw_union_eq)
    (smt (verit, best) CollectD pairw_union_eq)+

lemma pairw_union_absorbR_iff:
  "A \<uplus> B = B \<longleftrightarrow> (\<forall>x\<in>B.\<exists>a\<in>A.\<exists>b\<in>B. x = a \<union> b) \<and> (\<forall>a\<in>A. \<forall>b\<in>B. a \<union> b \<in> B)"
  by (subst pairw_union_commutes, subst pairw_union_absorbL_iff)
    (metis (no_types, lifting) sup.commute)

lemma pairw_union_absorbI:
  "B \<noteq> {} \<Longrightarrow> \<forall>X\<in>A. \<forall>Y\<in>B. Y \<subseteq> X \<Longrightarrow> A \<uplus> B = A"
  "A \<noteq> {} \<Longrightarrow> \<forall>X\<in>A. \<forall>Y\<in>B. X \<subseteq> Y \<Longrightarrow> A \<uplus> B = B"
  unfolding pairw_union_absorbL_iff pairw_union_absorbR_iff
  by (auto simp: sup_absorb1 sup_absorb2)

lemma pairw_union_eq_singletonI:
  "A \<noteq> {} \<Longrightarrow> \<forall>X\<in>A. X \<subseteq> Y \<Longrightarrow> B = {Y} \<Longrightarrow> A \<uplus> B = {Y}"
  "B \<noteq> {} \<Longrightarrow> \<forall>X\<in>B. X \<subseteq> Y \<Longrightarrow> A = {Y} \<Longrightarrow> A \<uplus> B = {Y}"
  by (metis singleton_iff pairw_union_absorbI(2))
    (metis singleton_iff pairw_union_absorbI(1))

interpretation pairw_semiring1: comm_semiring_1 "(\<uplus>)" "{{}}" "(\<union>)" "{}"
  by (unfold_locales, rule pairw_union_assoc) (auto simp: pairw_union_eq)

interpretation pairw_no_zero_div: semiring_no_zero_divisors "(\<union>)" "{}" "(\<uplus>)"
  by unfold_locales (auto simp: pairw_union_eq)

lemma Union_pairw_union_bdd_above: "\<Union> \<A> \<subseteq> C \<Longrightarrow> \<Union> \<B> \<subseteq> C \<Longrightarrow> \<Union> (\<A> \<uplus> \<B>) \<subseteq> C"
  by (auto simp: pairw_union_eq)

lemma Union_pairw_union_bdd_below: "A \<subseteq> \<Union>\<A> \<Longrightarrow> \<B> \<noteq> {} \<Longrightarrow> A \<subseteq> \<Union> (\<B> \<uplus> \<A>) "
  by (auto simp: pairw_union_eq)

lemma (in mult_zero) foldl_times_zero [simp]: 
  "foldl (*) 0 xs = 0"
  "0 \<in> set xs \<Longrightarrow> foldl (*) x xs = 0"
  by (induction xs arbitrary: x, auto)

lemma (in mult_zero) foldr_times_zero [simp]: 
  "foldr (*) xs 0 = 0"
  "0 \<in> set xs \<Longrightarrow> foldr (*) xs x = 0"
  by (induction xs arbitrary: x, auto)

lemma (in semiring_no_zero_divisors) non_zero_foldl_times: 
  "\<forall>y \<in> set xs. f y \<noteq> 0 \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> foldl (*) x (map f xs) \<noteq> 0"
  by (induct xs arbitrary: x, simp_all)

lemma (in semiring_no_zero_divisors) foldl_times_non_zeroD: 
  "foldl (*) x (map f xs) \<noteq> 0 \<Longrightarrow> (\<forall>y \<in> set xs. f y \<noteq> 0) \<and> x \<noteq> 0"
  by (induct xs arbitrary: x, simp)
    (metis image_eqI list.set_map foldl_times_zero(1,2))

lemma (in semiring_no_zero_divisors) foldl_times_non_zero_eq[simp]: 
  "foldl (*) x (map f xs) \<noteq> 0 \<longleftrightarrow> (\<forall>y \<in> set xs. f y \<noteq> 0) \<and> x \<noteq> 0"
  by (rule iffI, rule foldl_times_non_zeroD, assumption)
    (rule non_zero_foldl_times, auto)

lemma (in monoid_mult) foldr_times_one_all_one[simp]:
  "\<forall>x\<in>set xs. x = 1 \<Longrightarrow> foldr (*) xs 1 = 1"
  by (induct xs, simp_all)

lemma (in monoid_mult) foldl_times_one [simp]:
  "xs \<noteq> [] \<Longrightarrow> foldl (*) 1 (x # xs) = foldl (*) x xs"
  "\<forall>x\<in>set xs. x = 1 \<Longrightarrow> foldl (*) 1 xs = 1"
  by (induct xs arbitrary: x, simp_all)

lemma (in monoid_mult) foldl_times_one_expand: 
  "foldl (*) x xs = x * (foldl (*) 1 xs)"
  by (induct xs arbitrary: x, simp)
    (metis foldl_Cons local.mult_1_left mult_assoc)

lemma (in comm_monoid_mult) foldr_times_one [simp]:
  "xs \<noteq> [] \<Longrightarrow> foldr (*) (x # xs) 1 = foldr (*) xs x"
  using local.mult.left_commute 
  by (induct xs arbitrary: x) (simp_all, fastforce)

lemma "(\<lambda>(A, B, C). (A \<union> B) \<union> C) ` (X \<times> Y \<times> Z) = (X \<uplus> Y) \<uplus> Z"
  by (auto simp: pairw_union_eq)

lemma in_foldl_pairwD:
  "X \<in> foldl (\<uplus>) A As \<Longrightarrow> (\<forall>Z\<in>set As. Z \<noteq> {})"
  by (erule contrapos_pp, simp)

lemma pairw_union_eq_one_iff[simp]: 
  "A \<uplus> B = {{}} \<longleftrightarrow> A = {{}} \<and> B = {{}}"
proof(rule iffI)
  assume h1: "A \<uplus> B = {{}}"
  hence "\<forall>x\<in>A \<uplus> B. x = {}"
    unfolding pairw_union_eq by auto
  hence "\<forall>a\<in>A. \<forall>b\<in>B. a \<union> b = {}" 
    unfolding pairw_union_eq by auto
  hence "(\<forall>a\<in>A. a = {}) \<and> (\<forall>b\<in>B. b = {})" 
    using h1 Un_empty by (metis all_not_in_conv insert_not_empty 
        pairw_no_zero_div.mult_eq_0_iff) 
  thus "A = {{}} \<and> B = {{}}"
    by (metis h1 insertI1 is_singletonI' is_singleton_the_elem 
        pairw_union_empty(1) pairw_union_empty(2))
next
  show "A = {{}} \<and> B = {{}} \<Longrightarrow> A \<uplus> B = {{}}"
    unfolding pairw_union_eq by auto
qed

lemma foldl_pairw_eq_one_iff[simp]: 
  "foldl (\<uplus>) x xs = {{}} \<longleftrightarrow> (x={{}} \<and> (\<forall>x\<in>(set xs). x = {{}}))"
  by (induct xs arbitrary: x, simp_all)

lemma foldl_pairw_one_eq:
  defines "choice As f \<equiv> (\<forall>n < length As. f n \<in> As ! n)"
  shows "foldl (\<uplus>) {{}} As = {\<Union> (f ` ({0..<length As}))|f. choice As f}" (is "_ = ?rhs As")
proof(induct As, simp add: assms)
  case (Cons A As)
  have "foldl (\<uplus>) {{}} (A # As) = A \<uplus> ?rhs As"
    using Cons pairw_semiring1.foldl_times_one_expand
    by (metis foldl_Cons pairw_union_unit(2))
  also have "... = ?rhs (A # As)"
  proof(rule set_eqI2)
    fix X assume "X \<in> A \<uplus> ?rhs As"
    then obtain a and f where "a \<in> A" and f_def: "choice As f"
      and X_def: "X = a \<union> \<Union> (f ` {0..<length As})"
      by (auto simp: pairw_union_eq)
    let "?g" = "(override_on f (f \<circ> (\<lambda>x. x - 1)) ({1..<Suc (length As)}))(0:=a)"
    have "X = \<Union> (?g ` {0..<length (A # As)})"
      using X_def by auto (metis (no_types, lifting) Ex_less_Suc Int_iff 
          atLeast0LessThan diff_Suc_Suc diff_zero lessThan_iff less_trans_Suc 
          mem_Collect_eq zero_less_Suc)
    moreover have "choice (A # As) ?g"
      using f_def unfolding assms using \<open>a \<in> A\<close> by auto
    ultimately show "X \<in> ?rhs (A # As)"
      by blast
  next
    fix X assume "X \<in> ?rhs (A # As)"
    then obtain g where g_def: "choice (A # As) g" 
      and X_def: "X = \<Union> (g ` {0..<length (A # As)})" (is "X = ?img g (A#As)")
      by blast
    define f where f_def: "f = override_on g (g \<circ> Suc) ({0..< (length As)})"
    have "\<Union> (g ` {1..<Suc (length As)}) = ?img f As"
      apply(rule set_eqI2; clarsimp)
      unfolding f_def by clarsimp (metis atLeastLessThan_iff
          less_Suc_eq_0_disj not_less, force)
    moreover have "choice As f"
      using g_def unfolding f_def assms by auto
    moreover have "X = g 0 \<union> (?img f As)"
      unfolding X_def f_def apply (rule set_eqI; clarsimp)
      using less_Suc_eq_0_disj by force+
    moreover have "g 0 \<in> A" and "?img f As \<in> {?img f As|f. choice As f}"
      using X_def g_def unfolding assms apply clarsimp
      using \<open>choice As f\<close> unfolding assms by auto
    ultimately show "X \<in> A \<uplus> ?rhs As"
      unfolding pairw_union_eq by auto
  qed
  finally show "foldl (\<uplus>) {{}} (A # As) = ?rhs (A # As)"
    by simp
qed

lemma in_foldl_pairw_single_emptyD: "X \<in> foldl (\<uplus>) {{}} As \<Longrightarrow> \<exists>A\<subseteq>\<Union>(set As). X = \<Union>A"
  unfolding foldl_pairw_one_eq apply (clarsimp simp: subset_eq)
  by (rule_tac x="f ` {0..<length As}" in exI, rule conjI; clarsimp) auto

lemma imgage_in_foldl_pairw_union: "\<forall>x\<in>set xs. f x \<in> g x \<Longrightarrow> \<Union>(f ` set xs) \<in> (foldl (\<uplus>) {{}} (map g xs))"
  by (induct xs, simp_all)
    (subst pairw_semiring1.foldl_times_one_expand, simp add: union_in_pairw_union)


subsection \<open> Sets of safe free variables \<close>

unbundle MFODL_notation \<comment> \<open> enable notation \<close>

fun is_constraint :: "'t Formula.formula \<Rightarrow> bool" 
  where "is_constraint (t1 =\<^sub>F t2) = True"
  | "is_constraint (t1 <\<^sub>F t2) = True"
  | "is_constraint (t1 \<le>\<^sub>F t2) = True"
  | "is_constraint (\<not>\<^sub>F (t1 =\<^sub>F t2)) = True"
  | "is_constraint (\<not>\<^sub>F (t1 <\<^sub>F t2)) = True"
  | "is_constraint (\<not>\<^sub>F (t1 \<le>\<^sub>F t2)) = True"
  | "is_constraint _ = False"

lemma is_constraint_Neg_iff: "is_constraint (\<not>\<^sub>F \<alpha>) \<longleftrightarrow> 
  (\<exists>t1 t2. \<alpha> = t1 =\<^sub>F t2 \<or> \<alpha> = t1 <\<^sub>F t2 \<or> \<alpha> = t1 \<le>\<^sub>F t2)"
  by (cases \<alpha>, simp_all)

lemma is_constraint_iff: "is_constraint \<alpha> \<longleftrightarrow> (\<exists>t1 t2. \<alpha> = t1 =\<^sub>F t2 \<or> \<alpha> = t1 <\<^sub>F t2 
  \<or> \<alpha> = t1 \<le>\<^sub>F t2 \<or> \<alpha> = \<not>\<^sub>F (t1 =\<^sub>F t2) \<or> \<alpha> = \<not>\<^sub>F (t1 <\<^sub>F t2) \<or> \<alpha> = \<not>\<^sub>F (t1 \<le>\<^sub>F t2))"
  by (cases \<alpha>, simp_all add: is_constraint_Neg_iff)

definition safe_assignment :: "nat set \<Rightarrow> 'a Formula.formula \<Rightarrow> bool" where
  "safe_assignment X \<alpha> = (case \<alpha> of
       \<^bold>v x =\<^sub>F \<^bold>v y \<Rightarrow> (x \<notin> X \<longleftrightarrow> y \<in> X)
     | \<^bold>v x =\<^sub>F t \<Rightarrow> (x \<notin> X \<and> fv_trm t \<subseteq> X)
     | t =\<^sub>F \<^bold>v x \<Rightarrow> (x \<notin> X \<and> fv_trm t \<subseteq> X)
     | _ \<Rightarrow> False)"

lemma safe_assignment_Eq_iff: "safe_assignment X (t1 =\<^sub>F t2) 
  \<longleftrightarrow> (\<exists>x y. t1 = \<^bold>v x \<and> t2 = \<^bold>v y \<and> (x \<notin> X \<longleftrightarrow> y \<in> X)) 
    \<or> (\<exists>x. t1 = \<^bold>v x \<and> (x \<notin> X \<and> FV\<^sub>t t2 \<subseteq> X)) 
    \<or> (\<exists>x. t2 = \<^bold>v x \<and> (x \<notin> X \<and> FV\<^sub>t t1 \<subseteq> X))"
  by (cases t1; cases t2, auto simp: safe_assignment_def)

lemmas safe_assignment_EqD = iffD1[OF safe_assignment_Eq_iff]
   and safe_assignment_EqI = iffD2[OF safe_assignment_Eq_iff]

lemma safe_assignment_iff: "safe_assignment X \<beta> 
  \<longleftrightarrow> (\<exists>x y. \<beta> = (\<^bold>v x =\<^sub>F \<^bold>v y) \<and> (x \<notin> X \<longleftrightarrow> y \<in> X)) 
    \<or> (\<exists>x t. \<beta> = (\<^bold>v x =\<^sub>F t) \<and> (x \<notin> X \<and> FV\<^sub>t t \<subseteq> X)) 
    \<or> (\<exists>x t. \<beta> = (t =\<^sub>F \<^bold>v x) \<and> (x \<notin> X \<and> FV\<^sub>t t \<subseteq> X))"
  by (cases \<beta>; simp add: safe_assignment_Eq_iff) 
    (simp_all add: safe_assignment_def)

lemma safe_assignment_iff2: 
  "safe_assignment X \<beta> \<longleftrightarrow> (\<exists>x t. (x \<notin> X \<and> FV\<^sub>t t \<subseteq> X) \<and> (\<beta> = (\<^bold>v x =\<^sub>F t) \<or> \<beta> = (t =\<^sub>F \<^bold>v x)))
  \<or> (\<exists>x y. (x \<notin> X \<longleftrightarrow> y \<in> X) \<and> \<beta> = (\<^bold>v x =\<^sub>F \<^bold>v y))"
  unfolding safe_assignment_iff
  by (intro conjI impI allI iffI; (clarsimp, blast))

lemmas safe_assignmentD = iffD1[OF safe_assignment_iff]
   and safe_assignmentI = iffD2[OF safe_assignment_iff]

lemma safe_assignment_Neg_iff[simp]: "safe_assignment X (\<not>\<^sub>F \<beta>) \<longleftrightarrow> False"
  unfolding safe_assignment_iff by auto


subsection \<open> Safe formula predicate \<close>

context begin

fun safe_letpast :: "Formula.name \<times> nat \<Rightarrow> 't Formula.formula \<Rightarrow> rec_safety" 
  where "safe_letpast p (t1 =\<^sub>F t2) = Unused"
  | "safe_letpast p (t1 <\<^sub>F t2) = Unused"
  | "safe_letpast p (t1 \<le>\<^sub>F t2) = Unused"
  | "safe_letpast p (e \<dagger> ts) = (if p = (e, length ts) then NonFutuRec else Unused)"
  | "safe_letpast p (Formula.Let e \<phi> \<psi>) =
        (safe_letpast (e, Formula.nfv \<phi>) \<psi> * safe_letpast p \<phi>) \<squnion>
        (if p = (e, Formula.nfv \<phi>) then Unused else safe_letpast p \<psi>)"
  | "safe_letpast p (Formula.LetPast e \<phi> \<psi>) =
        (if p = (e, Formula.nfv \<phi>) then Unused else
          (safe_letpast (e, Formula.nfv \<phi>) \<psi> * safe_letpast p \<phi>) \<squnion> safe_letpast p \<psi>)"
  | "safe_letpast p (\<not>\<^sub>F \<phi>) = safe_letpast p \<phi>"
  | "safe_letpast p (\<phi> \<or>\<^sub>F \<psi>) = (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
  | "safe_letpast p (\<phi> \<and>\<^sub>F \<psi>) = (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
  | "safe_letpast p (\<And>\<^sub>F l) = \<Squnion>(safe_letpast p ` set l)"
  | "safe_letpast p (\<exists>\<^sub>F:t. \<phi>) = safe_letpast p \<phi>"
  | "safe_letpast p (Formula.Agg y \<omega> tys f \<phi>) = safe_letpast p \<phi>"
  | "safe_letpast p (\<^bold>Y I \<phi>) = PastRec * safe_letpast p \<phi>"
  | "safe_letpast p (\<^bold>X I \<phi>) = AnyRec * safe_letpast p \<phi>"
  | "safe_letpast p (\<phi> \<^bold>S I \<psi>) = safe_letpast p \<phi> \<squnion>
        ((if memL I 0 then NonFutuRec else PastRec) * safe_letpast p \<psi>)"
  | "safe_letpast p (\<phi> \<^bold>U I \<psi>) = AnyRec * (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
  | "safe_letpast p (Formula.MatchP I r) = \<Squnion>(safe_letpast p ` Regex.atms r)"
  | "safe_letpast p (Formula.MatchF I r) =  AnyRec * \<Squnion>(safe_letpast p ` Regex.atms r)"
  | "safe_letpast p (Formula.TP t) = Unused"
  | "safe_letpast p (Formula.TS t) = Unused"

fun remove_neg :: "'t Formula.formula \<Rightarrow> 't Formula.formula" 
  where "remove_neg (\<not>\<^sub>F \<phi>) = \<phi>"
  | "remove_neg \<phi> = \<phi>"

lemma fvi_remove_neg[simp]: "Formula.fvi b (remove_neg \<phi>) = Formula.fvi b \<phi>"
  by (cases \<phi>) simp_all

lemma size_remove_neg[termination_simp]: "size (remove_neg \<phi>) \<le> size \<phi>"
  by (cases \<phi>) simp_all

lemma partition_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x\<in>set xs \<Longrightarrow> f x = g x) \<Longrightarrow> partition f xs = partition g ys"
  by (induction xs arbitrary: ys) auto


fun safe_formula :: "'t Formula.formula \<Rightarrow> bool" where
  "safe_formula (t1 =\<^sub>F t2) = (Formula.is_Const t1 \<and> (Formula.is_Const t2 \<or> Formula.is_Var t2) \<or> Formula.is_Var t1 \<and> Formula.is_Const t2)"
| "safe_formula (t1 <\<^sub>F t2) = False"
| "safe_formula (t1 \<le>\<^sub>F t2) = False"
| "safe_formula (e \<dagger> ts) = (\<forall>t\<in>set ts. Formula.is_Var t \<or> Formula.is_Const t)"
| "safe_formula (Formula.Let p \<phi> \<psi>) = ({0..<Formula.nfv \<phi>} \<subseteq> fv \<phi> \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
| "safe_formula (Formula.LetPast p \<phi> \<psi>) = (safe_letpast (p, Formula.nfv \<phi>) \<phi> \<le> PastRec \<and> {0..<Formula.nfv \<phi>} \<subseteq> fv \<phi> \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
| "safe_formula (\<not>\<^sub>F \<phi>) = (fv \<phi> = {} \<and> safe_formula \<phi>)"
| "safe_formula (\<phi> \<or>\<^sub>F \<psi>) = (fv \<psi> = fv \<phi> \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
| "safe_formula (\<phi> \<and>\<^sub>F \<psi>) = (safe_formula \<phi> \<and>
    (safe_assignment (fv \<phi>) \<psi> \<or> safe_formula \<psi> \<or>
      fv \<psi> \<subseteq> fv \<phi> \<and> (is_constraint \<psi> \<or> (case \<psi> of \<not>\<^sub>F \<psi>' \<Rightarrow> safe_formula \<psi>' | _ \<Rightarrow> False))))"
| "safe_formula (\<And>\<^sub>F l) = (let (pos, neg) = partition safe_formula l in pos \<noteq> [] \<and>
    list_all safe_formula (map remove_neg neg) \<and> \<Union>(set (map fv neg)) \<subseteq> \<Union>(set (map fv pos)))"
| "safe_formula (\<exists>\<^sub>F:t. \<phi>) = (safe_formula \<phi> \<and> 0 \<in> fv \<phi>)"
| "safe_formula (Formula.Agg y \<omega> tys f \<phi>) = (safe_formula \<phi> \<and> y + length tys \<notin> fv \<phi> \<and> {0..<length tys} \<subseteq> fv \<phi> \<and> fv_trm f \<subseteq> fv \<phi>)"
| "safe_formula (\<^bold>Y I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (\<^bold>X I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (\<phi> \<^bold>S I \<psi>) = (fv \<phi> \<subseteq> fv \<psi> \<and>
    (safe_formula \<phi> \<or> (case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)) \<and> safe_formula \<psi>)"
| "safe_formula (\<phi> \<^bold>U I \<psi>) = (fv \<phi> \<subseteq> fv \<psi> \<and>
    (safe_formula \<phi> \<or> (case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)) \<and> safe_formula \<psi>)"
| "safe_formula (Formula.MatchP I r) = Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
     (g = Lax \<and> (case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))) Past Strict r"
| "safe_formula (Formula.MatchF I r) = Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
     (g = Lax \<and> (case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))) Futu Strict r"
| "safe_formula (Formula.TP t) = (Formula.is_Var t \<or> Formula.is_Const t)"
| "safe_formula (Formula.TS t) = (Formula.is_Var t \<or> Formula.is_Const t)"

abbreviation "safe_regex \<equiv> Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
  (g = Lax \<and> (case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)))"

lemma safe_regex_safe_formula:
  "safe_regex m g r \<Longrightarrow> \<phi> \<in> Regex.atms r \<Longrightarrow> safe_formula \<phi> \<or>
  (\<exists>\<psi>. \<phi> = \<not>\<^sub>F \<psi> \<and> safe_formula \<psi>)"
  by (cases g) (auto dest!: safe_regex_safe[rotated] split: Formula.formula.splits[where formula=\<phi>])

lemma safe_abbrevs[simp]: "safe_formula Formula.TT" "safe_formula Formula.FF"
  unfolding Formula.TT_def Formula.FF_def by auto

definition safe_neg :: "'t Formula.formula \<Rightarrow> bool" where
  "safe_neg \<phi> \<longleftrightarrow> safe_formula (remove_neg \<phi>)"

definition atms :: "'t Formula.formula Regex.regex \<Rightarrow> 't Formula.formula set" where
  "atms r = (\<Union>\<phi> \<in> Regex.atms r.
     if safe_formula \<phi> then {\<phi>} else case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {})"

lemma atms_simps[simp]:
  "atms (Regex.Skip n) = {}"
  "atms (Regex.Test \<phi>) = (if safe_formula \<phi> then {\<phi>} else case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {})"
  "atms (Regex.Plus r s) = atms r \<union> atms s"
  "atms (Regex.Times r s) = atms r \<union> atms s"
  "atms (Regex.Star r) = atms r"
  unfolding atms_def by auto

lemma finite_atms[simp]: "finite (atms r)"
  by (induct r) (auto split: Formula.formula.splits)

lemma disjE_Not2: "P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (\<not>P \<Longrightarrow> Q \<Longrightarrow> R) \<Longrightarrow> R"
  by blast

lemma safe_formula_induct[consumes 1, case_names Eq_Const Eq_Var1 Eq_Var2 Pred Let LetPast
    And_assign And_safe And_constraint And_Not Ands Neg Or Exists Agg
    Prev Next Since Not_Since Until Not_Until MatchP MatchF TP TS]:
  assumes "safe_formula \<phi>"
    and Eq_Const: "\<And>c d. P (\<^bold>c c =\<^sub>F \<^bold>c d)"
    and Eq_Var1: "\<And>c x. P (\<^bold>c c =\<^sub>F \<^bold>v x)"
    and Eq_Var2: "\<And>c x. P (\<^bold>v x =\<^sub>F (\<^bold>c c))"
    and Pred: "\<And>e ts. \<forall>t\<in>set ts. Formula.is_Var t \<or> Formula.is_Const t \<Longrightarrow> P (e \<dagger> ts)"
    and Let: "\<And>p \<phi> \<psi>. {0..<Formula.nfv \<phi>} \<subseteq> fv \<phi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Formula.Let p \<phi> \<psi>)"
    and LetPast: "\<And>p \<phi> \<psi>. safe_letpast (p, Formula.nfv \<phi>) \<phi> \<le> PastRec \<Longrightarrow> {0..<Formula.nfv \<phi>} \<subseteq> fv \<phi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Formula.LetPast p \<phi> \<psi>)"
    and And_assign: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (\<phi> \<and>\<^sub>F \<psi>)"
    and And_safe: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow>
      P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (\<phi> \<and>\<^sub>F \<psi>)"
    and And_constraint: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> \<not> safe_formula \<psi> \<Longrightarrow>
      fv \<psi> \<subseteq> fv \<phi> \<Longrightarrow> is_constraint \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (\<phi> \<and>\<^sub>F \<psi>)"
    and And_Not: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) (\<not>\<^sub>F \<psi>) \<Longrightarrow> \<not> safe_formula (\<not>\<^sub>F \<psi>) \<Longrightarrow>
      fv (\<not>\<^sub>F \<psi>) \<subseteq> fv \<phi> \<Longrightarrow> \<not> is_constraint (\<not>\<^sub>F \<psi>) \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (\<phi> \<and>\<^sub>F (\<not>\<^sub>F \<psi>))"
    and Ands: "\<And>l pos neg. (pos, neg) = partition safe_formula l \<Longrightarrow> pos \<noteq> [] \<Longrightarrow>
      list_all safe_formula pos \<Longrightarrow> list_all safe_formula (map remove_neg neg) \<Longrightarrow>
      (\<Union>\<phi>\<in>set neg. fv \<phi>) \<subseteq> (\<Union>\<phi>\<in>set pos. fv \<phi>) \<Longrightarrow>
      list_all P pos \<Longrightarrow> list_all P (map remove_neg neg) \<Longrightarrow> P (\<And>\<^sub>F l)"
    and Neg: "\<And>\<phi>. fv \<phi> = {} \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (\<not>\<^sub>F \<phi>)"
    and Or: "\<And>\<phi> \<psi>. fv \<psi> = fv \<phi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (\<phi> \<or>\<^sub>F \<psi>)"
    and Exists: "\<And>t \<phi>. safe_formula \<phi> \<Longrightarrow> 0 \<in> fv \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (\<exists>\<^sub>F:t. \<phi>)" (* any t?*)
    and Agg: "\<And>y \<omega> tys f \<phi>. y + length tys \<notin> fv \<phi> \<Longrightarrow> {0..<length tys} \<subseteq> fv \<phi> \<Longrightarrow> fv_trm f \<subseteq> fv \<phi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow>
      (\<And>\<phi>'. size \<phi>' \<le> size \<phi> \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> P \<phi>') \<Longrightarrow> P (Formula.Agg y \<omega> tys f \<phi>)"
    and Prev: "\<And>I \<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (\<^bold>Y I \<phi>)"
    and Next: "\<And>I \<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (\<^bold>X I \<phi>)"
    and Since: "\<And>\<phi> I \<psi>. fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (\<phi> \<^bold>S I \<psi>)"
    and Not_Since: "\<And>\<phi> I \<psi>. fv (\<not>\<^sub>F \<phi>) \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow>
      \<not> safe_formula (\<not>\<^sub>F \<phi>) \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P ((\<not>\<^sub>F \<phi>) \<^bold>S I \<psi> )"
    and Until: "\<And>\<phi> I \<psi>. fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (\<phi> \<^bold>U I \<psi>)"
    and Not_Until: "\<And>\<phi> I \<psi>. fv (\<not>\<^sub>F \<phi>) \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow>
      \<not> safe_formula (\<not>\<^sub>F \<phi>) \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P ((\<not>\<^sub>F \<phi>) \<^bold>U I \<psi>)"
    and MatchP: "\<And>I r. safe_regex Past Strict r \<Longrightarrow> \<forall>\<phi> \<in> atms r. P \<phi> \<Longrightarrow> P (Formula.MatchP I r)"
    and MatchF: "\<And>I r. safe_regex Futu Strict r \<Longrightarrow> \<forall>\<phi> \<in> atms r. P \<phi> \<Longrightarrow> P (Formula.MatchF I r)"
    and TP: "\<And>t. Formula.is_Var t \<or> Formula.is_Const t \<Longrightarrow> P (Formula.TP t)"
    and TS: "\<And>t. Formula.is_Var t \<or> Formula.is_Const t \<Longrightarrow> P (Formula.TS t)"
  shows "P \<phi>"
using assms(1) proof (induction "size \<phi>" arbitrary: \<phi> rule: nat_less_induct)
  case 1
  then have IH: "size \<psi> < size \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<psi>" "safe_formula \<phi>" for \<psi>
    by auto
  then show ?case
  proof (cases \<phi> rule: safe_formula.cases)
    case (1 t1 t2)
    then show ?thesis 
      using Eq_Const Eq_Var1 Eq_Var2 IH 
      by (auto simp: trm.is_Const_def trm.is_Var_def)
  next
    case (9 \<phi>' \<psi>')
    from IH(2)[unfolded 9] consider
      (a) "safe_assignment (fv \<phi>') \<psi>'"
      | (b) "\<not> safe_assignment (fv \<phi>') \<psi>'" "safe_formula \<psi>'"
      | (c) "fv \<psi>' \<subseteq> fv \<phi>'" "\<not> safe_assignment (fv \<phi>') \<psi>'" "\<not> safe_formula \<psi>'" "is_constraint \<psi>'"
      | (d) \<psi>'' where "fv \<psi>' \<subseteq> fv \<phi>'" "\<not> safe_assignment (fv \<phi>') \<psi>'" "\<not> safe_formula \<psi>'" "\<not> is_constraint \<psi>'"
        "\<psi>' = \<not>\<^sub>F \<psi>''" "safe_formula \<psi>''"
      by (cases \<psi>') auto
    then show ?thesis proof cases
      case a
      then show ?thesis using IH by (auto simp: 9 intro: And_assign)
    next
      case b
      then show ?thesis using IH by (auto simp: 9 intro: And_safe)
    next
      case c
      then show ?thesis using IH by (auto simp: 9 intro: And_constraint)
    next
      case d
      then show ?thesis using IH by (auto simp: 9 intro!: And_Not)
    qed
  next
    case (10 l)
    obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
    have "pos \<noteq> []" using IH(2) posneg by (simp add: 10)
    moreover have "list_all safe_formula pos" using posneg by (simp add: list.pred_set)
    moreover have safe_remove_neg: "list_all safe_formula (map remove_neg neg)"
      using IH(2) posneg by (auto simp: 10)
    moreover have "list_all P pos"
      using posneg IH(1)
      by (auto simp add: 10 list_all_iff le_imp_less_Suc size_list_estimation')
    moreover have "list_all P (map remove_neg neg)"
      using IH(1) posneg safe_remove_neg
      by (auto simp add: 10 list_all_iff le_imp_less_Suc size_list_estimation' size_remove_neg)
    ultimately show ?thesis using IH Ands posneg by (simp add: 10)
  next
    case (15 \<phi>' I \<psi>')
    with IH show ?thesis
    proof (cases \<phi>')
      case (Ands l)
      then show ?thesis using IH Since
        by (auto simp: 15)
    qed (auto 0 3 simp: 15 elim!: disjE_Not2 intro: Since Not_Since) (*SLOW*)
  next
    case (16 \<phi>' I \<psi>')
    with IH show ?thesis
    proof (cases \<phi>')
      case (Ands l)
      then show ?thesis using IH Until by (auto simp: 16)
    qed (auto 0 3 simp: 16 elim!: disjE_Not2 intro: Until Not_Until) (*SLOW*)
  next
    case (17 I r)
    have case_Neg: "\<phi> \<in> (case x of \<not>\<^sub>F \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {}) \<Longrightarrow> x = \<not>\<^sub>F \<phi>" for \<phi> :: "'t Formula.formula" and x
      by (auto split: Formula.formula.splits)
    {
      fix \<psi>
      assume atms: "\<psi> \<in> atms r"
      then have "safe_formula \<psi>"
        using safe_regex_safe_formula IH(2)
        by (fastforce simp: 17 atms_def)
      moreover have "size \<psi> \<le> regex.size_regex size r"
        using atms
        by (auto simp: atms_def size_regex_estimation' dest!: case_Neg)
      ultimately have "P \<psi>"
        using IH(1)
        by (auto simp: 17)
    }
    then show ?thesis
      using IH(2)
      by (auto simp: 17 intro!: MatchP)
  next
    case (18 I r)
    have case_Neg: "\<phi> \<in> (case x of \<not>\<^sub>F \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {}) \<Longrightarrow> x = \<not>\<^sub>F \<phi>" for \<phi> :: "'t Formula.formula" and x
      by (auto split: Formula.formula.splits)
    {
      fix \<psi>
      assume atms: "\<psi> \<in> atms r"
      then have "safe_formula \<psi>"
        using safe_regex_safe_formula IH(2)
        by (fastforce simp: 18 atms_def)
      moreover have "size \<psi> \<le> regex.size_regex size r"
        using atms
        by (auto simp: atms_def size_regex_estimation' dest!: case_Neg)
      ultimately have "P \<psi>"
        using IH(1)
        by (auto simp: 18)
    }
    then show ?thesis
      using IH(2)
      by (auto simp: 18 intro!: MatchF)
  qed (auto simp: assms)
qed

lemma safe_formula_NegD:
  "safe_formula (\<not>\<^sub>F \<phi>) \<Longrightarrow> fv \<phi> = {}"
  by (induct "\<not>\<^sub>F \<phi>" rule: safe_formula_induct) auto


subsection \<open>Future reach\<close>

qualified fun future_bounded :: "'t Formula.formula \<Rightarrow> bool" where
  "future_bounded (Formula.Pred _ _) = True"
| "future_bounded (Formula.Let p \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Formula.LetPast p \<phi> \<psi>) = (safe_letpast (p, Formula.nfv \<phi>) \<phi> \<le> PastRec \<and> future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Formula.Eq _ _) = True"
| "future_bounded (Formula.Less _ _) = True"
| "future_bounded (Formula.LessEq _ _) = True"
| "future_bounded (\<not>\<^sub>F \<phi>) = future_bounded \<phi>"
| "future_bounded (\<phi> \<or>\<^sub>F \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (\<phi> \<and>\<^sub>F \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (\<And>\<^sub>F l) = list_all future_bounded l"
| "future_bounded (\<exists>\<^sub>F:t. \<phi>) = future_bounded \<phi>"
| "future_bounded (Formula.Agg y \<omega> tys f \<phi>) = future_bounded \<phi>"
| "future_bounded (\<^bold>Y I \<phi>) = future_bounded \<phi>"
| "future_bounded (\<^bold>X I \<phi>) = future_bounded \<phi>"
| "future_bounded (\<phi> \<^bold>S I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (\<phi> \<^bold>U I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi> \<and> bounded I)"
| "future_bounded (Formula.MatchP I r) = Regex.pred_regex future_bounded r"
| "future_bounded (Formula.MatchF I r) = (Regex.pred_regex future_bounded r \<and> bounded I)"
| "future_bounded (Formula.TP _) = True"
| "future_bounded (Formula.TS _) = True"


subsection \<open>Translation to n-ary conjunction\<close>

fun get_and_list :: "'t Formula.formula \<Rightarrow> 't Formula.formula list" where
  "get_and_list (\<And>\<^sub>F l) = (if l = [] then [\<And>\<^sub>F l] else l)"
| "get_and_list \<phi> = [\<phi>]"

lemma fv_get_and: "(\<Union>x\<in>(set (get_and_list \<phi>)). Formula.fvi b x) = Formula.fvi b \<phi>"
  by (induction \<phi> rule: get_and_list.induct) simp_all

lemma safe_remove_negI: "safe_formula \<phi> \<Longrightarrow> safe_formula (remove_neg \<phi>)"
  by (cases \<phi>) auto

lemma safe_get_and: "safe_formula \<phi> \<Longrightarrow> list_all safe_neg (get_and_list \<phi>)"
  by (induction \<phi> rule: get_and_list.induct) (auto simp: safe_neg_def list_all_iff intro: safe_remove_negI)

lemma sat_get_and: "Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> list_all (Formula.sat \<sigma> V v i) (get_and_list \<phi>)"
  by (induction \<phi> rule: get_and_list.induct) (simp_all add: list_all_iff)

lemma safe_letpast_get_and: "\<Squnion>(safe_letpast p ` set (get_and_list \<phi>)) = safe_letpast p \<phi>"
  by (induction \<phi> rule: get_and_list.induct) (simp_all flip: bot_rec_safety_def)

lemma not_contains_pred_get_and: "\<And>x.\<not>contains_pred p \<phi> \<Longrightarrow> x \<in> set (get_and_list \<phi>) \<Longrightarrow> \<not> contains_pred p x"
  by (induction \<phi> rule: get_and_list.induct) (auto split: if_splits)

primrec convert_multiway :: "'t Formula.formula \<Rightarrow> 't Formula.formula" where
  "convert_multiway (Formula.Pred p ts) = (Formula.Pred p ts)"
| "convert_multiway (Formula.Eq t u) = (Formula.Eq t u)"
| "convert_multiway (Formula.Less t u) = (Formula.Less t u)"
| "convert_multiway (Formula.LessEq t u) = (Formula.LessEq t u)"
| "convert_multiway (Formula.Let p \<phi> \<psi>) = Formula.Let p (convert_multiway \<phi>) (convert_multiway \<psi>)"
| "convert_multiway (Formula.LetPast p \<phi> \<psi>) = Formula.LetPast p (convert_multiway \<phi>) (convert_multiway \<psi>)"
| "convert_multiway (\<not>\<^sub>F \<phi>) = \<not>\<^sub>F (convert_multiway \<phi>)"
| "convert_multiway (\<phi> \<or>\<^sub>F \<psi>) = (convert_multiway \<phi>) \<or>\<^sub>F (convert_multiway \<psi>)"
| "convert_multiway (\<phi> \<and>\<^sub>F \<psi>) = (if safe_assignment (fv \<phi>) \<psi> then
      (convert_multiway \<phi>) \<and>\<^sub>F \<psi>
    else if safe_formula \<psi> then
      \<And>\<^sub>F (get_and_list (convert_multiway \<phi>) @ get_and_list (convert_multiway \<psi>))
    else if is_constraint \<psi> then
      (convert_multiway \<phi>) \<and>\<^sub>F \<psi>
    else \<And>\<^sub>F (convert_multiway \<psi> # get_and_list (convert_multiway \<phi>)))"
| "convert_multiway (\<And>\<^sub>F \<phi>s) = \<And>\<^sub>F (map convert_multiway \<phi>s)"
| "convert_multiway (\<exists>\<^sub>F:t. \<phi>) = \<exists>\<^sub>F:t. (convert_multiway \<phi>)"
| "convert_multiway (Formula.Agg y \<omega> b f \<phi>) = Formula.Agg y \<omega> b f (convert_multiway \<phi>)"
| "convert_multiway (\<^bold>Y I \<phi>) = \<^bold>Y I (convert_multiway \<phi>)"
| "convert_multiway (\<^bold>X I \<phi>) = \<^bold>X I (convert_multiway \<phi>)"
| "convert_multiway (\<phi> \<^bold>S I \<psi>) = (convert_multiway \<phi>) \<^bold>S I (convert_multiway \<psi>)"
| "convert_multiway (\<phi> \<^bold>U I \<psi>) = (convert_multiway \<phi>) \<^bold>U I (convert_multiway \<psi>)"
| "convert_multiway (Formula.MatchP I r) = Formula.MatchP I (Regex.map_regex convert_multiway r)"
| "convert_multiway (Formula.MatchF I r) = Formula.MatchF I (Regex.map_regex convert_multiway r)"
| "convert_multiway (Formula.TP t) = Formula.TP t"
| "convert_multiway (Formula.TS t) = Formula.TS t"

abbreviation "convert_multiway_regex \<equiv> Regex.map_regex convert_multiway"

lemma fv_safe_get_and:
  "safe_formula \<phi> \<Longrightarrow> fv \<phi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list \<phi>))). fv x)"
proof (induction \<phi> rule: get_and_list.induct)
  case (1 l)
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  have sub: "(\<Union>x\<in>set neg. fv x) \<subseteq> (\<Union>x\<in>set pos. fv x)" using "1.prems" posneg by simp
  then have "fv (\<And>\<^sub>F l) \<subseteq> (\<Union>x\<in>set pos. fv x)"
  proof -
    have "fv (\<And>\<^sub>F l) = (\<Union>x\<in>set pos. fv x) \<union> (\<Union>x\<in>set neg. fv x)" using posneg by auto
    then show ?thesis using sub by simp
  qed
  then show ?case using posneg by auto
qed auto

lemma ex_safe_get_and:
  "safe_formula \<phi> \<Longrightarrow> list_ex safe_formula (get_and_list \<phi>)"
proof (induction \<phi> rule: get_and_list.induct)
  case (1 l)
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  then have "pos \<noteq> []" using "1.prems" by simp
  then obtain x where "x \<in> set pos" by fastforce
  then show ?case using posneg using Bex_set_list_ex by fastforce
qed simp_all

lemma case_NegE: "(case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> P \<phi>' | _ \<Rightarrow> False) \<Longrightarrow> (\<And>\<phi>'. \<phi> = \<not>\<^sub>F \<phi>' \<Longrightarrow> P \<phi>' \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (cases \<phi>) simp_all

lemma convert_multiway_remove_neg: "safe_formula (remove_neg \<phi>) \<Longrightarrow> convert_multiway (remove_neg \<phi>) = remove_neg (convert_multiway \<phi>)"
  by (cases \<phi>) (auto elim: case_NegE)

lemma fv_convert_multiway: "Formula.fvi b (convert_multiway \<phi>) = Formula.fvi b \<phi>"
  by (induction \<phi> arbitrary: b)
    (auto simp add: fv_get_and Un_commute fv_regex_alt regex.set_map)

lemma nfv_convert_multiway: "Formula.nfv (convert_multiway \<phi>) = Formula.nfv \<phi>"
  unfolding Formula.nfv_def by (auto simp: fv_convert_multiway)

lemma get_and_nonempty[simp]: "get_and_list \<phi> \<noteq> []"
  by (induction \<phi>) auto

lemma future_bounded_get_and:
  "list_all future_bounded (get_and_list \<phi>) = future_bounded \<phi>"
  by (induction \<phi>) simp_all

lemma contains_pred_convert_multiway: "\<not> (contains_pred p \<phi>) \<Longrightarrow> \<not>(contains_pred p (convert_multiway \<phi>))"
proof (induction p \<phi> rule: contains_pred.induct)
  case(9 p \<phi> \<psi>)
  then show ?case by (auto simp: not_contains_pred_get_and)
next
  case(17 p I r)
  then show ?case by (auto simp add: regex.set_map)
next
  case(18 p I r)
  then show ?case by (auto simp add: regex.set_map)
qed(auto simp: nfv_convert_multiway)

lemma safe_letpast_convert_multiway: "safe_letpast p (convert_multiway \<phi>) = safe_letpast p \<phi>"
proof (induction p \<phi> rule: safe_letpast.induct)
  case (5 p e \<phi> \<psi>)
  then show?case by (auto simp add: contains_pred_convert_multiway nfv_convert_multiway)
next
  case (6 p e \<phi> \<psi>)
  then show?case by (auto simp add: contains_pred_convert_multiway nfv_convert_multiway)
next
  case(9 p \<phi> \<psi>)
  then show ?case
    by (simp add: image_Un Sup_rec_safety_union safe_letpast_get_and sup_commute)
next
  case(17 p I r)
  then show ?case
    by (simp add: regex.set_map image_image cong: image_cong)
next
  case(18 p I r)
  then show ?case
    by (simp add: regex.set_map image_image cong: image_cong)
qed (auto simp add: image_image)

lemma safe_convert_multiway: "safe_formula \<phi> \<Longrightarrow> safe_formula (convert_multiway \<phi>)"
proof (induction \<phi> rule: safe_formula_induct)
  case (LetPast p \<phi> \<psi>)
  then show ?case
    by (auto simp: safe_letpast_convert_multiway nfv_convert_multiway fv_convert_multiway)
next
  case (And_safe \<phi> \<psi>)
  let ?a = "\<phi> \<and>\<^sub>F \<psi>"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = \<And>\<^sub>F (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    using And_safe by simp
  show ?case proof -
    let ?l = "get_and_list ?c\<phi> @ get_and_list ?c\<psi>"
    obtain pos neg where posneg: "(pos, neg) = partition safe_formula ?l" by simp
    then have "list_all safe_formula pos" by (auto simp: list_all_iff)
    have lsafe_neg: "list_all safe_neg ?l"
      using And_safe \<open>safe_formula \<phi>\<close> \<open>safe_formula \<psi>\<close>
      by (simp add: safe_get_and)
    then have "list_all safe_formula (map remove_neg neg)"
    proof -
      have "\<And>x. x \<in> set neg \<Longrightarrow> safe_formula (remove_neg x)"
      proof -
        fix x assume "x \<in> set neg"
        then have "\<not> safe_formula x" using posneg by auto
        moreover have "safe_neg x" using lsafe_neg \<open>x \<in> set neg\<close>
          unfolding safe_neg_def list_all_iff partition_set[OF posneg[symmetric], symmetric]
          by simp
        ultimately show "safe_formula (remove_neg x)" using safe_neg_def by blast
      qed
      then show ?thesis by (auto simp: list_all_iff)
    qed

    have pos_filter: "pos = filter safe_formula (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
      using posneg by simp
    have "(\<Union>x\<in>set neg. fv x) \<subseteq> (\<Union>x\<in>set pos. fv x)"
    proof -
      have 1: "fv ?c\<phi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list ?c\<phi>))). fv x)" (is "_ \<subseteq> ?fv\<phi>")
        using And_safe \<open>safe_formula \<phi>\<close> by (blast intro!: fv_safe_get_and)
      have 2: "fv ?c\<psi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list ?c\<psi>))). fv x)" (is "_ \<subseteq> ?fv\<psi>")
        using And_safe \<open>safe_formula \<psi>\<close> by (blast intro!: fv_safe_get_and)
      have "(\<Union>x\<in>set neg. fv x) \<subseteq> fv ?c\<phi> \<union> fv ?c\<psi>" proof -
        have "\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` (set pos \<union> set neg))"
          by simp
        also have "... \<subseteq> fv (convert_multiway \<phi>) \<union> fv (convert_multiway \<psi>)"
          unfolding partition_set[OF posneg[symmetric], simplified]
          by (simp add: fv_get_and)
        finally show ?thesis .
      qed
      then have "(\<Union>x\<in>set neg. fv x) \<subseteq> ?fv\<phi> \<union> ?fv\<psi>" using 1 2 by blast
      then show ?thesis unfolding pos_filter by simp
    qed
    have "pos \<noteq> []"
    proof -
      obtain x where "x \<in> set (get_and_list ?c\<phi>)" "safe_formula x"
        using And_safe \<open>safe_formula \<phi>\<close> ex_safe_get_and by (auto simp: list_ex_iff)
      then show ?thesis
        unfolding pos_filter by (auto simp: filter_empty_conv)
    qed
    then show ?thesis unfolding b_def
      using \<open>\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` set pos)\<close> \<open>list_all safe_formula (map remove_neg neg)\<close>
        \<open>list_all safe_formula pos\<close> posneg
      by simp
  qed
next
  case (And_Not \<phi> \<psi>)
  let ?a = "\<phi> \<and>\<^sub>F (\<not>\<^sub>F \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = \<And>\<^sub>F (\<not>\<^sub>F ?c\<psi> # get_and_list ?c\<phi>)"
    using And_Not by simp
  show ?case proof -
    let ?l = "\<not>\<^sub>F ?c\<psi> # get_and_list ?c\<phi>"
    note \<open>safe_formula ?c\<phi>\<close>
    then have "list_all safe_neg (get_and_list ?c\<phi>)" by (simp add: safe_get_and)
    moreover have "safe_neg (\<not>\<^sub>F ?c\<psi>)"
      using \<open>safe_formula ?c\<psi>\<close> by (simp add: safe_neg_def)
    then have lsafe_neg: "list_all safe_neg ?l" using calculation by simp
    obtain pos neg where posneg: "(pos, neg) = partition safe_formula ?l" by simp
    then have "list_all safe_formula pos" by (auto simp: list_all_iff)
    then have "list_all safe_formula (map remove_neg neg)"
    proof -
      have "\<And>x. x \<in> (set neg) \<Longrightarrow> safe_formula (remove_neg x)"
      proof -
        fix x assume "x \<in> set neg"
        then have "\<not> safe_formula x" using posneg by (auto simp del: filter.simps)
        moreover have "safe_neg x" using lsafe_neg \<open>x \<in> set neg\<close>
          unfolding safe_neg_def list_all_iff partition_set[OF posneg[symmetric], symmetric]
          by simp
        ultimately show "safe_formula (remove_neg x)" using safe_neg_def by blast
      qed
      then show ?thesis using Ball_set_list_all by force
    qed

    have pos_filter: "pos = filter safe_formula ?l"
      using posneg by simp
    have neg_filter: "neg = filter (Not \<circ> safe_formula) ?l"
      using posneg by simp
    have "(\<Union>x\<in>(set neg). fv x) \<subseteq> (\<Union>x\<in>(set pos). fv x)"
    proof -
      have fv_neg: "(\<Union>x\<in>(set neg). fv x) \<subseteq> (\<Union>x\<in>(set ?l). fv x)" using posneg by auto
      have "(\<Union>x\<in>(set ?l). fv x) \<subseteq> fv ?c\<phi> \<union> fv ?c\<psi>"
        using \<open>safe_formula \<phi>\<close> \<open>safe_formula \<psi>\<close>
        by (simp add: fv_get_and fv_convert_multiway)
      also have "fv ?c\<phi> \<union> fv ?c\<psi> \<subseteq> fv ?c\<phi>"
        using \<open>fv (\<not>\<^sub>F \<psi>) \<subseteq> fv \<phi>\<close>
        by (simp add: fv_convert_multiway)
      finally have "(\<Union>x\<in>(set neg). fv x) \<subseteq> fv ?c\<phi>"
        using fv_neg unfolding neg_filter by blast
      then show ?thesis
        unfolding pos_filter
        using fv_safe_get_and[OF And_Not.IH(1)]
        by auto
    qed
    have "pos \<noteq> []"
    proof -
      obtain x where "x \<in> set (get_and_list ?c\<phi>)" "safe_formula x"
        using And_Not.IH \<open>safe_formula \<phi>\<close> ex_safe_get_and by (auto simp: list_ex_iff)
      then show ?thesis
        unfolding pos_filter by (auto simp: filter_empty_conv)
    qed
    then show ?thesis unfolding b_def
      using \<open>\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` set pos)\<close> \<open>list_all safe_formula (map remove_neg neg)\<close>
        \<open>list_all safe_formula pos\<close> posneg
      by simp
  qed
next
  case (Ands l)
  then show ?case
    using convert_multiway_remove_neg fv_convert_multiway
    apply (auto simp: list.pred_set filter_map filter_empty_conv subset_eq)
     apply (smt (verit, del_insts) convert_multiway_remove_neg)(*metis fvi_remove_neg*)
  by (smt (verit, del_insts) convert_multiway_remove_neg fv_convert_multiway fvi_remove_neg)
next
  case (Neg \<phi>)
  have "safe_formula (\<not>\<^sub>F \<phi>') \<longleftrightarrow> safe_formula \<phi>'" if "fv \<phi>' = {}" for \<phi>' :: "'t Formula.formula"
    using that by (cases "\<not>\<^sub>F \<phi>'" rule: safe_formula.cases) simp_all
  with Neg show ?case 
    by (simp add: \<open>\<And>\<phi>'. fv \<phi>' = {} \<Longrightarrow> safe_formula (\<not>\<^sub>F \<phi>') = safe_formula \<phi>'\<close> fv_convert_multiway)(*simp add: fv_convert_multiway*)
next
  case (MatchP I r)
  then show ?case
    by (auto 0 3 simp: atms_def fv_convert_multiway intro!: safe_regex_map_regex
      elim!: disjE_Not2 case_NegE
      dest: safe_regex_safe_formula split: if_splits)
next
  case (MatchF I r)
  then show ?case
    by (auto 0 3 simp: atms_def fv_convert_multiway intro!: safe_regex_map_regex
      elim!: disjE_Not2 case_NegE
      dest: safe_regex_safe_formula split: if_splits)
qed (auto simp add: fv_convert_multiway nfv_convert_multiway)

lemma future_bounded_remove_neg: "future_bounded (remove_neg \<phi>) = future_bounded \<phi>"
  by (cases \<phi>) auto

lemma future_bounded_convert_multiway: "safe_formula \<phi> \<Longrightarrow> future_bounded (convert_multiway \<phi>) = future_bounded \<phi>"
proof (induction \<phi> rule: safe_formula_induct)
  case (LetPast p \<phi> \<psi>)
  then show ?case by (auto simp: safe_letpast_convert_multiway nfv_convert_multiway)
next
  case (And_safe \<phi> \<psi>)
  let ?a = "\<phi> \<and>\<^sub>F \<psi>"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = \<And>\<^sub>F (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    using And_safe by simp
  have "future_bounded ?a = (future_bounded ?c\<phi> \<and> future_bounded ?c\<psi>)"
    using And_safe by simp
  moreover have "future_bounded ?c\<phi> = list_all future_bounded (get_and_list ?c\<phi>)"
    using \<open>safe_formula \<phi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "future_bounded ?c\<psi> = list_all future_bounded (get_and_list ?c\<psi>)"
    using \<open>safe_formula \<psi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "future_bounded ?b = list_all future_bounded (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    unfolding b_def by simp
  ultimately show ?case by simp
next
  case (And_Not \<phi> \<psi>)
  let ?a = "\<phi> \<and>\<^sub>F (\<not>\<^sub>F \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = \<And>\<^sub>F (\<not>\<^sub>F ?c\<psi> # get_and_list ?c\<phi>)"
    using And_Not by simp
  have "future_bounded ?a = (future_bounded ?c\<phi> \<and> future_bounded ?c\<psi>)"
    using And_Not by simp
  moreover have "future_bounded ?c\<phi> = list_all future_bounded (get_and_list ?c\<phi>)"
    using \<open>safe_formula \<phi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "future_bounded ?b = list_all future_bounded (\<not>\<^sub>F ?c\<psi> # get_and_list ?c\<phi>)"
    unfolding b_def by (simp add: list.pred_map o_def)
  ultimately show ?case by auto
next
  case (MatchP I r)
  then show ?case
    by (fastforce simp: atms_def regex.pred_set regex.set_map ball_Un
        elim: safe_regex_safe_formula[THEN disjE_Not2])
next
  case (MatchF I r)
  then show ?case
    by (fastforce simp: atms_def regex.pred_set regex.set_map ball_Un
        elim: safe_regex_safe_formula[THEN disjE_Not2])
qed (auto simp: list.pred_set convert_multiway_remove_neg future_bounded_remove_neg)

lemma sat_convert_multiway: "safe_formula \<phi> \<Longrightarrow> Formula.sat \<sigma> V v i (convert_multiway \<phi>) \<longleftrightarrow> Formula.sat \<sigma> V v i \<phi>"
proof (induction \<phi> arbitrary: V v i rule: safe_formula_induct)
  case (And_safe \<phi> \<psi>)
  let ?a = "\<phi> \<and>\<^sub>F \<psi>"
  let ?b = "convert_multiway ?a"
  let ?la = "get_and_list (convert_multiway \<phi>)"
  let ?lb = "get_and_list (convert_multiway \<psi>)"
  let ?sat = "Formula.sat \<sigma> V v i"
  have b_def: "?b = \<And>\<^sub>F (?la @ ?lb)" using And_safe by simp
  have "list_all ?sat ?la \<longleftrightarrow> ?sat \<phi>" using And_safe sat_get_and by blast
  moreover have "list_all ?sat ?lb \<longleftrightarrow> ?sat \<psi>" using And_safe sat_get_and by blast
  ultimately show ?case using And_safe by (auto simp: list.pred_set)
next
  case (And_Not \<phi> \<psi>)
  let ?a = "\<phi> \<and>\<^sub>F (\<not>\<^sub>F \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?la = "get_and_list (convert_multiway \<phi>)"
  let ?lb = "convert_multiway \<psi>"
  let ?sat = "Formula.sat \<sigma> V v i"
  have b_def: "?b = \<And>\<^sub>F (\<not>\<^sub>F ?lb # ?la)" using And_Not by simp
  have "list_all ?sat ?la \<longleftrightarrow> ?sat \<phi>" using And_Not sat_get_and by blast
  then show ?case using And_Not by (auto simp: list.pred_set)
next
  case (Agg y \<omega> tys f \<phi>)
  then show ?case
    by (simp add: Formula.nfv_def fv_convert_multiway cong: conj_cong)
next
  case (MatchP I r)
  then have "Regex.match (Formula.sat \<sigma> V v) (convert_multiway_regex r) = Regex.match (Formula.sat \<sigma> V v) r"
    unfolding match_map_regex
    by (intro Regex.match_fv_cong)
      (auto 0 5 simp: atms_def elim!: disjE_Not2 dest!: safe_regex_safe_formula)
  then show ?case
    by auto
next
  case (MatchF I r)
  then have "Regex.match (Formula.sat \<sigma> V v) (convert_multiway_regex r) = Regex.match (Formula.sat \<sigma> V v) r"
    unfolding match_map_regex
    by (intro Regex.match_fv_cong)
      (auto 0 5 simp: atms_def elim!: disjE_Not2 dest!: safe_regex_safe_formula)
  then show ?case
    by auto
next
  case (Let p \<phi> \<psi>)
  then show ?case
    by (auto simp add: nfv_convert_multiway fun_upd_def)
next
  case (LetPast p \<phi> \<psi>)
  then show ?case
    by (auto simp add: nfv_convert_multiway fun_upd_def)
next
  case (Ands l)
  have sat_remove_neg: "(Formula.sat \<sigma> V v i (remove_neg \<phi>) \<longleftrightarrow> Formula.sat \<sigma> V v i (remove_neg \<psi>)) \<longleftrightarrow>
        (Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> Formula.sat \<sigma> V v i \<psi>)" if "Formula.is_Neg \<phi> \<longleftrightarrow> Formula.is_Neg \<psi>" for V v i \<phi> \<psi>
    using that by (cases \<phi>; cases \<psi>) (auto simp add: Formula.is_Neg_def)
  have is_Neg_cm: "Formula.is_Neg (convert_multiway \<phi>) \<longleftrightarrow> Formula.is_Neg \<phi>" for \<phi> :: "'t Formula.formula"
    by (cases \<phi>) auto
  from Ands show ?case
    by (fastforce simp: list.pred_set convert_multiway_remove_neg sat_remove_neg[OF is_Neg_cm])
qed (auto cong: nat.case_cong)

(*
subsection \<open> Finite @{term safe_formula} \<close>

lemma inj_eval: " \<forall>t\<in>set ts. Formula.is_Var t \<or> Formula.is_Const t \<Longrightarrow>
    inj_on (\<lambda>v. map (Formula.eval_trm (map the v)) ts) {v. wf_tuple n (\<Union> (fv_trm ` set ts)) v}"
  apply(intro inj_onI)
      apply(rule nth_equalityI)
       apply(auto simp add: wf_tuple_def)[]
      subgoal for x y i
        apply(cases "i \<in> (\<Union> (fv_trm ` set ts))")
         apply(subgoal_tac "\<^bold>v i \<in> set ts")
          apply(simp)
        apply(rotate_tac)
          apply(drule(1) bspec)
          apply(simp add: wf_tuple_def)
          apply (meson option.expand)
         apply(auto simp add: Formula.is_Var_def Formula.is_Const_def)[]
          apply(simp add: wf_tuple_def)
        by metis
      done

lemma inj_eval2: " \<forall>t\<in>set ts. Formula.is_Var t \<or> Formula.is_Const t \<Longrightarrow>
    inj_on (\<lambda>v. (e, map (Formula.eval_trm (map the v)) ts)) {v. wf_tuple n (\<Union> (fv_trm ` set ts)) v}"
  apply(intro inj_onI)
      apply(rule nth_equalityI)
       apply(auto simp add: wf_tuple_def)[]
      subgoal for x y i
        apply(cases "i \<in> (\<Union> (fv_trm ` set ts))")
         apply(subgoal_tac "\<^bold>v i \<in> set ts")
          apply(simp)
        apply(rotate_tac)
          apply(drule(1) bspec)
          apply(simp add: wf_tuple_def)
          apply (meson option.expand)
         apply(auto simp add: Formula.is_Var_def Formula.is_Const_def)[]
          apply(simp add: wf_tuple_def)
        by metis
      done

lemma finite_listset: "(\<And>A. A \<in> set xs \<Longrightarrow> finite A) \<Longrightarrow> finite (listset xs)"
  by (induct xs) (simp_all add: set_Cons_def finite_image_set2)

fun joinN :: "'a tuple list \<Rightarrow> 'a tuple option" where
"joinN [] = Some []"
|"joinN (a#b#cs) =  (case (join1 (a, b)) of None \<Rightarrow> None| Some x \<Rightarrow> joinN (x#cs))"
|"joinN (a#[]) = Some a"

lemma in_listset_conv_list_all2: "xs \<in> listset ys \<longleftrightarrow> list_all2 (\<in>) xs ys"
  by (induct ys arbitrary: xs) (auto simp: set_Cons_def list_all2_Cons2)

lemma joinN_Some_restrict:
  fixes as :: "'a tuple list"
  fixes bs :: "nat set list"
  assumes "list_all2 (wf_tuple n) bs as"
  assumes "as\<noteq>[]"
  shows "joinN (as) = Some z \<longleftrightarrow> wf_tuple n (\<Union> (set bs)) z \<and> list_all2 (\<lambda>b a. restrict b z = a) bs as"
  using assms
proof (induct "as" arbitrary: n bs z rule: joinN.induct)
  case 1
  then show ?case
    by(auto)
next
  case (2 a b cs)
  then show ?case
    apply(simp)
    apply(cases "join1 (a, b)")
     apply(simp_all)
     apply(auto simp add: list_all2_Cons2)[]
    subgoal for A B Cs
      using join1_Some_restrict[of n A a B b "(restrict (A\<union>B) z)"] apply(auto simp add: restrict_restrict intro: wf_tuple_restrict_simple)
      done
    subgoal for c
      apply(erule thin_rl)
      apply(clarsimp simp add: list_all2_Cons2)[]
      subgoal for A B Cs
      using join1_Some_restrict[of n A a B b c] 2(1)[of c n "(A\<union>B)#Cs" z] apply(auto simp add: Un_assoc restrict_restrict intro: wf_tuple_restrict_simple)
      apply(subgoal_tac "restrict (A\<union>B) z = restrict (A\<union>B) c")
       apply(simp add: restrict_idle)
      apply(simp add: list_eq_iff_nth_eq nth_restrict')
      apply(simp split: if_splits)
      by (metis nth_restrict)
    done
    done
next
  case (3 a)
  then show ?case
    apply(auto)
      apply(simp add: wf_tuple_def)
      apply (smt (verit, best) in_set_simps(2) list_all2_Cons2 list_all2_Nil2)
      apply(simp add: wf_tuple_def)
     apply (smt (z3) "3.prems" list_all2_Cons2 list_all2_Nil2 restrict_idle)
    apply(simp add: wf_tuple_def)
    apply(auto)
    by (smt (z3) in_set_simps(2) list.inject list_all2_Cons2 list_all2_Nil2 nth_equalityI nth_restrict)
qed

lemma finite_letpast:
  assumes fv: "{0..<Formula.nfv \<phi>} \<subseteq> fv \<phi>"
  assumes V: "\<forall>pn\<in>dom V. \<forall>i. finite {v. length v = snd pn \<and> the (V pn) v i}"
  assumes IH: "\<And>V i.
    \<forall>pn\<in>dom V. \<forall>i. finite {v. length v = snd pn \<and> the (V pn) v i} \<Longrightarrow>
    finite {v. wf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
  shows "finite {v. length v = Formula.nfv \<phi> \<and>
    letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) u k \<phi>) v i}"
proof (induction i rule: less_induct)
  case (less i)
  note fun_upd_apply[simp del]
  show ?case
    apply (rule finite_surj[where f="map the"])
     apply (rule IH[where i=i and V="(V((p, Formula.nfv \<phi>) \<mapsto>
          \<lambda>w j. j < i \<and> letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) u k \<phi>) w j))"])
     apply (intro ballI)
     apply clarsimp
    subgoal for p' n k
      apply (cases "(p', n) = (p, Formula.nfv \<phi>)")
       apply (clarsimp simp add: fun_upd_apply)
       apply (cases "k < i")
        apply simp
        apply (rule less[of k])
        apply simp
       apply clarsimp
      apply (subst fun_upd_apply)
      apply (simp only: if_False)
      apply (rule V[rule_format, of "(p', n)", simplified])
      by auto
    apply (intro subsetI)
    subgoal for v
      apply (rule image_eqI[where x="map Some v"])
       apply simp
      apply (subst (asm) letpast_sat.simps)
      using fv by (auto simp: wf_tuple_def)
    done
qed

lemma safe_regex_Past_finite: "safe_regex Past Strict r \<Longrightarrow>
  (\<And>i \<phi>. \<phi> \<in> atms r \<Longrightarrow> finite {v. wf_tuple n (fv \<phi>) v \<and> test v i \<phi>}) \<Longrightarrow>
  finite {v. wf_tuple n (fv_regex r) v \<and> (\<exists>j\<le>i. Regex.match (test v) r j i)}"
  apply (induct Past Strict r arbitrary: i rule: safe_regex.induct)
      apply (auto simp flip: in_unit_table simp add: unit_table_def
        conj_disj_distribL ex_disj_distrib relcompp_apply Un_absorb2)
  subgoal for r s i
  apply (rule finite_subset[rotated])
     apply (rule finite_UN_I[where B="\<lambda>i. {v. wf_tuple n (fv_regex r) v \<and> (\<exists>j\<le>i. Regex.match (test v) r j i)}"])
      apply (rule finite_atLeastAtMost[of 0 i])
     apply assumption
    apply (auto simp: Bex_def)
    apply (meson match_le)
    done
  done

lemma safe_regex_Future_finite: "safe_regex Futu Strict r \<Longrightarrow>
  (\<And>i \<phi>. \<phi> \<in> atms r \<Longrightarrow> finite {v. wf_tuple n (fv \<phi>) v \<and> test v i \<phi>}) \<Longrightarrow>
  finite {v. wf_tuple n (fv_regex r) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) r i j)}"
  apply (induct Futu Strict r arbitrary: i rule: safe_regex.induct)
      apply (auto simp flip: in_unit_table simp add: unit_table_def Bex_def
        conj_disj_distribL ex_disj_distrib relcompp_apply Un_absorb1 intro: rev_finite_subset)
  subgoal for r s i
  apply (rule finite_subset[rotated])
     apply (rule finite_UN_I[where B="\<lambda>i. {v. wf_tuple n (fv_regex s) v \<and> (\<exists>j\<ge>i. j \<le> thr \<and> Regex.match (test v) s i j)}"])
      apply (rule finite_atLeastAtMost[of i thr])
     apply assumption
    apply (auto simp: Bex_def)
    apply (meson match_le order_trans)
    done
  done

lemma Collect_singleton_tuple_eq_image: "i < n \<Longrightarrow> {v. wf_tuple n {i} v \<and> P (map the v ! i)} =
  (\<lambda>x. (replicate n None)[i := Some x]) ` Collect P"
  unfolding wf_tuple_def
  by (auto simp add: list_eq_iff_nth_eq nth_list_update intro: rev_image_eqI)
  
lemma safe_formula_finite: "safe_formula \<phi> \<Longrightarrow> future_bounded \<phi> \<Longrightarrow> n\<ge> (Formula.nfv \<phi>) \<Longrightarrow> \<forall> i. finite (\<Gamma> \<sigma> i) \<Longrightarrow>
  \<forall>pn\<in>dom V. \<forall>i. finite {v. length v = snd pn \<and> the (V pn) v i} \<Longrightarrow>
  finite {v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
proof(induct \<phi> arbitrary: i n V rule: safe_formula_induct)
  case (Eq_Const c d)
  then show ?case
    by(simp flip: in_unit_table add: unit_table_def)
next
  case (Eq_Var1 c x)
  then have "finite (singleton_table n x c)"
    unfolding singleton_table_def by(simp)
  then show ?case using Eq_Var1
    apply(elim finite_subset[rotated])
    apply(auto intro: nth_equalityI simp add: singleton_table_def wf_tuple_def tabulate_alt Formula.nfv_def Suc_le_eq)
    done
next
  case (Eq_Var2 c x)
  then have "finite (singleton_table n x c)"
    unfolding singleton_table_def by(simp)
  then show ?case
    apply(simp)
    apply(elim finite_subset[rotated])
    apply(auto intro: nth_equalityI simp add: singleton_table_def wf_tuple_def tabulate_alt Formula.nfv_def Suc_le_eq)
    done
next
case (Pred e ts)
  then show ?case
    apply(simp)
    apply(cases "V (e, length ts)")
     apply(simp)
    subgoal
      apply(rule finite_vimage_IntI[of "\<Gamma> \<sigma> i" "\<lambda> v. (e, map (Formula.eval_trm (map the v)) ts)" "{v. wf_tuple n (\<Union> (fv_trm ` set ts)) v}", THEN finite_subset[rotated]])
        apply simp
       apply(auto simp add: inj_eval2)
      done
    apply(simp)
    subgoal for a
      apply(rule finite_vimage_IntI[of "{v. length v = length ts \<and> a v i}" "\<lambda> v. map (Formula.eval_trm (map the v)) ts" "{v. wf_tuple n (\<Union> (fv_trm ` set ts)) v}", THEN finite_subset[rotated]])
        apply (drule (1) bspec[OF _ domI])
        apply(auto simp add: inj_eval)
      done
    done
next
  case (Let p \<phi> \<psi>)
  then have IH: " finite {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) i \<psi>}"
    apply(simp)
    done
  then have IH2: "\<forall>i.  finite (map the ` {v. wf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>})" using Let
    by(auto)
  then have "\<forall> i. {v. length v = Formula.nfv \<phi> \<and> Formula.sat \<sigma> V v i \<phi>} = map the ` {v. wf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    using Let
    apply(simp)
    by(auto simp add: wf_tuple_def intro!: image_eqI[where x="map Some _"])
   then have " finite {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j \<phi>)) (map the v) i \<psi>}"
     using Let IH2
    by(auto)
  then show ?case using Let
    apply(elim finite_subset[rotated])
    by(auto)
next
  case (LetPast p \<phi> \<psi>)
  show ?case
    unfolding sat.simps fvi.simps Let_def
    apply (rule LetPast.hyps(6))
    using LetPast apply auto[3]
    apply (intro ballI allI)
    subgoal for pn i
      apply (cases "pn = (p, Formula.nfv \<phi>)")
       apply (simp add: dom_def)
       apply (rule finite_letpast)
      using LetPast apply auto[2]
      apply (rule LetPast.hyps(5))
      using LetPast by auto
    done
next
  case (And_assign \<phi> \<psi>)
  then have IH: " finite {v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    apply(simp)
    done
  consider x y where "\<psi> = \<^bold>v x =\<^sub>F (\<^bold>v y)" and  "(x \<notin> fv \<phi> \<longleftrightarrow> y \<in> fv \<phi>)"
    |x t where "\<psi> = \<^bold>v x =\<^sub>F t" and "\<not> Formula.is_Var t" and "(x \<notin> fv \<phi> \<and> fv_trm t \<subseteq> fv \<phi>)"
    |x t where "\<psi> = t =\<^sub>F (\<^bold>v x)" and "\<not> Formula.is_Var t" and "(x \<notin> fv \<phi> \<and> fv_trm t \<subseteq> fv \<phi>)"
    using And_assign(2)
    by(simp add: safe_assignment_def Formula.is_Var_def split: Formula.formula.splits trm.splits)
      then show ?case proof cases
        case 1
        then show ?thesis
          apply(simp)
          apply(cases "(x \<notin> fv \<phi>)")
           apply(simp add: insert_commute insert_absorb)
          thm finite_surj[OF IH, of _ "\<lambda> v. v [x:=v!y]"]
           apply(rule finite_surj[OF IH, of _ "\<lambda> v. v [x:=v!y]"])
           apply(auto)[]
          subgoal for v
            apply(rule rev_image_eqI[of "v [x:=None]"])
             apply(auto)
              apply(simp add: wf_tuple_def)
              apply (metis nth_list_update nth_list_update_neq)
            apply (smt (verit, best) map_update nth_list_update_neq sat_fv_cong)
            apply(rule sym)
            apply(subst list_update_same_conv)
            using And_assign(5) apply(simp add: wf_tuple_def Formula.nfv_def)
            apply(simp add: wf_tuple_def)
            apply(subst nth_list_update_neq)
             apply blast
            using And_assign(5) apply(simp add: wf_tuple_def Formula.nfv_def)
            by (metis Suc_le_lessD option.expand nth_map)
          apply(simp add: insert_absorb)
           apply(rule finite_surj[OF IH, of _ "\<lambda> v. v [y:=v!x]"])
           apply(auto)[]
          subgoal for v
            apply(rule rev_image_eqI[of "v [y:=None]"])
             apply(auto)
              apply(simp add: wf_tuple_def)
              apply (metis nth_list_update nth_list_update_neq)
            apply (smt (verit, best) map_update nth_list_update_neq sat_fv_cong)
            apply(rule sym)
            apply(subst list_update_same_conv)
            using And_assign(5) apply(simp add: wf_tuple_def Formula.nfv_def)
            apply(simp add: wf_tuple_def)
            apply(subst nth_list_update_neq)
             apply blast
            using And_assign(5) apply(simp add: wf_tuple_def Formula.nfv_def)
            by (metis Suc_le_eq nth_map option.expand)
          done
      next
        case 2
        then show ?thesis
          apply(simp add: Un_absorb2)
          apply(rule finite_surj[OF IH, of _ "\<lambda> v. v [x:=Some (Formula.eval_trm (map the v) t)]"])
          apply(auto)[]
          subgoal for v
            apply(rule rev_image_eqI[of "v [x:=None]"])
             apply(auto)
              apply(simp add: wf_tuple_def)
              apply (metis nth_list_update_eq nth_list_update_neq)
             apply (smt (verit, best) map_update nth_list_update_neq sat_fv_cong)
            apply(rule sym)
            apply(subst list_update_same_conv)
            using And_assign(5) apply(simp_all add: wf_tuple_def Formula.nfv_def)
            apply(subst eval_trm_fv_cong[of _ _ "map the v"] )
             apply (metis in_mono map_update nth_list_update_neq)
            by (metis Suc_le_eq option.collapse)
          done
      next
        case 3
        then show ?thesis
          apply(simp add: Un_absorb2)
          apply(rule finite_surj[OF IH, of _ "\<lambda> v. v [x:=Some (Formula.eval_trm (map the v) t)]"])
          apply(auto)[]
          subgoal for v
            apply(rule rev_image_eqI[of "v [x:=None]"])
             apply(auto)
              apply(simp add: wf_tuple_def)
              apply (metis nth_list_update_eq nth_list_update_neq)
             apply (smt (verit, best) map_update nth_list_update_neq sat_fv_cong)
            apply(rule sym)
            apply(subst list_update_same_conv)
            using And_assign(5) apply(simp_all add: wf_tuple_def Formula.nfv_def)
            apply(subst eval_trm_fv_cong[of _ _ "map the v"] )
             apply (metis in_mono map_update nth_list_update_neq)
            by (metis Suc_le_eq option.collapse)
          done
      qed
next
  case (And_safe \<phi> \<psi>)
  let ?A = "\<lambda>\<phi>. {v | v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
  let ?p = "\<lambda>v. (restrict (fv \<phi>) v, restrict (fv \<psi>) v)"
  let ?test = "(?A \<phi> \<times> ?A \<psi>)"
  have "finite (?A \<phi>)" and "finite (?A \<psi>)" using And_safe by auto
  then have "finite (?A \<phi> \<times> ?A \<psi>)" ..
  then have "finite (Option.these (join1 ` (?A \<phi> \<times> ?A \<psi>)))"
    by (auto simp: Option.these_def)
  moreover have "{v. wf_tuple n (fv \<phi> \<union> fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi> \<and> Formula.sat \<sigma> V (map the v) i \<psi>}
      \<subseteq> Option.these (join1 ` (?A \<phi> \<times> ?A \<psi>))" (is "?B \<subseteq> ?B'")
  proof
    fix v
    assume "v \<in> ?B"
    then have "(restrict (fv \<phi>) v, restrict (fv \<psi>) v) \<in> ?A \<phi> \<times> ?A \<psi>"
      by (auto simp: wf_tuple_restrict_simple sat_the_restrict)
    moreover have "join1 (restrict (fv \<phi>) v, restrict (fv \<psi>) v) = Some v"
      using \<open>v \<in> ?B\<close>
      apply (subst join1_Some_restrict)
      by(auto simp: wf_tuple_restrict_simple)
    ultimately show "v \<in> ?B'"
      apply(simp)
      by (force simp: Option.these_def)
  qed
  ultimately show ?case
    by (auto elim!: finite_subset)
next
  case (And_constraint \<phi> \<psi>)
  then have "finite {v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by(simp)
  then show ?case using And_constraint
    apply(elim finite_subset[rotated])
    apply(auto)
    by (metis sup.order_iff)
next
  case (And_Not \<phi> \<psi>)
  then have "finite {v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by(simp)
  then show ?case using And_Not
    apply(elim finite_subset[rotated])
    by(auto simp add: Un_absorb2)
next
  case (Ands l pos neg)
  let ?A = "\<lambda>\<phi>. {v | v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
  let ?p = "\<lambda>v. (map (\<lambda> \<phi>.(restrict (fv \<phi>) v)) pos)"
  let ?A_list = "listset (map (\<lambda> \<phi>. ?A \<phi>) pos)"
  have "finite (?A_list)" using Ands
    apply(intro finite_listset)
    by(auto simp add:list_all_def)
  then have "finite (Option.these (joinN ` (?A_list)))"
    by(auto simp: Option.these_def)
  moreover have "{v. wf_tuple n (\<Union> (fv ` set l)) v \<and> (\<forall>x\<in>set l. Formula.sat \<sigma> V (map the v) i x)}
      \<subseteq> (Option.these (joinN ` (?A_list)))" (is "?B \<subseteq> ?B'")
  proof
    fix v
    assume "v \<in> ?B"
    then have "?p v \<in> ?A_list"
      using Ands(1)
      by (auto simp: sat_the_restrict in_listset_conv_list_all2 list.rel_map intro!: list.rel_refl_strong wf_tuple_restrict_simple)
    moreover have "joinN (?p v) = Some v"
      using \<open>v \<in> ?B\<close> using Ands(1, 5) Ands.hyps(2)
      thm joinN_Some_restrict[of n "map fv pos" "map (\<lambda>\<phi>. restrict (fv \<phi>) v) pos" v]
      apply(subst joinN_Some_restrict[of n "map fv pos" "map (\<lambda>\<phi>. restrict (fv \<phi>) v) pos" v])
       apply(auto simp: wf_tuple_restrict_simple list.rel_map intro!: list.rel_refl_strong wf_tuple_restrict_simple)
      apply(subgoal_tac "\<Union> (fv ` {x \<in> set l. safe_formula x}) = \<Union> (fv ` set l)")
      by(auto)
    ultimately show "v \<in> ?B'"
      apply(simp)
      by (force simp: Option.these_def)
  qed
   ultimately show ?case
    by (auto elim!: finite_subset)
next
  case (Neg \<phi>)
  then show ?case
   by(simp flip: in_unit_table add: unit_table_def)
next
  case (Or \<phi> \<psi>)
  then have "finite {v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by(simp)
  moreover from Or have "finite {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) i \<psi>}"
    by(simp)
  ultimately have "finite ({v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>} \<union> {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) i \<psi>})"
    by(simp)
  then show ?case using Or
    apply(elim finite_subset[rotated])
    by(auto)
next
  case (Exists t \<phi>)
 then have "finite (Formula.fvi (Suc 0) \<phi>)"
   by(simp)
  moreover from Exists have IH: "finite {v. wf_tuple (Suc n) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by(simp add: Formula.nfv_def fvi_Suc_bound Suc_le_eq)
  ultimately show ?case using Exists
    apply(simp)
    apply(rule finite_surj[OF IH, of _ "tl"])
    apply(auto)
    subgoal for v z
      apply(rule image_eqI[of _ _ "(if 0 \<in> fv \<phi> then Some z else None)#v"])
       apply(auto simp add: wf_tuple_def)
      apply (metis fvi_Suc length_nth_simps(3) length_nth_simps(4) less_Suc_eq_0_disj option.discI)
      apply (metis fvi_Suc length_nth_simps(4) less_Suc_eq_0_disj)
      done
    done
next
  case (Agg y \<omega> tys f \<phi>)
  define b where [simp]: "b= length tys"
  from Agg have IH: "finite {v. wf_tuple (n+b) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by(auto 0 4 simp add: Suc_le_eq ball_Un Formula.nfv_def intro!: Agg(5)[where ?n="n+(length tys)"] dest!: fvi_plus_bound[where b=0 and c=b, simplified])
  then have IH_alt: "finite (drop b`{v. wf_tuple (n+b) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>})"
    by(auto)
  have drop_b: "finite (drop b`{v. wf_tuple (n+b) (fv \<phi>) v \<and> fv \<phi> = {0..<b}})"
    apply(rule finite_subset[of _ "{replicate n None}"])
     apply(auto simp add: wf_tuple_def list_eq_iff_nth_eq[where ?ys="replicate n None"])
    done
  have final_subset: "finite (drop b`{v. wf_tuple (n+b) (fv \<phi>) v \<and> (Formula.sat \<sigma> V (map the v) i \<phi> \<or> fv \<phi> = {0..<b})})"
    using drop_b IH_alt
    apply(auto)
    by (smt (z3) Collect_cong b_def drop_b)
  have sat_eq: "Formula.sat \<sigma> V (zs @ map the (x[y := None])) i \<phi> = Formula.sat \<sigma> V (zs @ map the (x)) i \<phi>" if "length zs = b" and "y<length x" for x zs
    using Agg(1, 7) that
    apply -
    apply(rule sat_fv_cong)
    apply(simp add: nth_append)
    apply(auto simp add: Formula.nfv_def Suc_le_eq)
    by (metis add.commute add_diff_inverse_nat map_update nth_list_update_neq)
  have eval_trm_eq: "Formula.eval_trm (zs @ map the (x[y := None])) f = Formula.eval_trm (zs @ map the (x)) f" if "length zs = b" and "y<length x" for x zs
using Agg(1, 7) that
    apply -
    apply(rule eval_trm_fv_cong)
    apply(simp add: nth_append)
  apply(auto simp add: Formula.nfv_def Suc_le_eq)
  by (metis Agg.hyps(3) add.commute add_diff_inverse_nat map_update nth_list_update_neq subset_iff)
  then show ?case using Agg IH
    apply(simp)
    apply(rule finite_surj[ of "{v. wf_tuple n (Formula.fvi b \<phi> \<union> Formula.fvi_trm b f) v \<and>
         ((\<forall>a x. length x = b \<longrightarrow> Formula.sat \<sigma> V (x @ map the v) i \<phi> \<longrightarrow> Formula.eval_trm (x @ map the v) f \<noteq> a) \<longrightarrow>
          fv \<phi> = {0..<b})}" _ "\<lambda> v. v [y:= (Some (eval_agg_op \<omega>
         {(x, ecard
               {zs.
                length zs = b \<and>
                Formula.sat \<sigma> V (zs @ map the v) i \<phi> \<and> Formula.eval_trm (zs @ map the v) f = x}) |
          x. \<exists>xa. Formula.sat \<sigma> V (xa @ map the v) i \<phi> \<and>
                  length xa = b \<and> Formula.eval_trm (xa @ map the v) f = x}))]"])
     defer
     apply(intro subsetI)
     apply(clarify)
    subgoal for x
      apply(frule wf_tuple_length)
    apply(rule image_eqI[where x="x[y:=None]"])
       apply(rule sym)
      apply(simp add: ac_simps sat_eq eval_trm_eq Formula.nfv_def Suc_le_eq cong: conj_cong Collect_cong)
     apply(subst list_update_same_conv)
      apply(simp add: Formula.nfv_def Suc_le_eq wf_tuple_def)
       apply(simp add: Formula.nfv_def Suc_le_eq wf_tuple_def)
       apply (metis option.exhaust_sel)
      apply(auto)
      apply(auto simp add: sat_eq eval_trm_eq wf_tuple_def nth_list_update Formula.nfv_def Suc_le_eq  fvi_trm_iff_fv_trm[where b="length _"] fvi_iff_fv[where b="length _"])
      done
    apply(rule finite_subset[of _ "(drop b`{v. wf_tuple (n+b) (fv \<phi>) v \<and> (Formula.sat \<sigma> V (map the v) i \<phi> \<or> fv \<phi> = {0..<b})})"])
     apply(intro subsetI)
    apply(clarify)
    subgoal for x
      apply(erule impCE)
       apply(simp)
       apply(elim exE conjE)
      subgoal for zs
        apply(rule image_eqI[where x="map2 (\<lambda> i z. if i \<in> fv \<phi> then Some z else None) [0..<b] zs @ x"])
         apply(simp)
        apply(intro conjI[rotated] CollectI)
        apply(subgoal_tac "Formula.sat \<sigma> V (map the (map2 (\<lambda>x y. if x \<in> fv \<phi> then Some y else None) [0..<b] zs @ x)) i \<phi>")
        apply(simp)
         apply(erule sat_fv_cong[THEN iffD1, rotated])
         apply(simp add: Formula.nfv_def nth_append)
         apply(auto simp add: wf_tuple_def nth_append Formula.nfv_def)
           apply (metis add_diff_inverse_nat fvi_iff_fv le_add1 le_add_diff_inverse2)
        apply (metis bot_nat_0.not_eq_extremum diff_is_0_eq fvi_iff_fv le_add_diff_inverse2 zero_less_diff)
        subgoal for i
          apply(subgoal_tac "i\<in>fv_trm f")
           apply(auto)[]
          by (metis bot_nat_0.not_eq_extremum diff_is_0_eq fvi_trm_iff_fv_trm le_add_diff_inverse2 zero_less_diff)
        done
      apply(subgoal_tac "wf_tuple n {} x")
      subgoal
        apply(subgoal_tac "x \<in> drop b ` {v. wf_tuple (n + b) (fv \<phi>) v \<and> fv \<phi> = {0..<b}}")
          apply blast
        apply(subgoal_tac "x\<in>{v. wf_tuple n {} v}")
        subgoal
          apply(subgoal_tac "{v. wf_tuple n {} v} \<subseteq> drop b ` {v. wf_tuple (n + b) (fv \<phi>) v}")
           apply(auto )[]
          by (auto simp: in_unit_table[symmetric] unit_table_def image_iff nth_append
    intro!: exI[of _ "replicate b (Some undefined) @ replicate n None"] wf_tuple_def[THEN iffD2])
        apply(auto)
        done
      apply(auto simp add: wf_tuple_def fvi_iff_fv[of _ "length tys"] fvi_trm_iff_fv_trm[of _ "length tys"])
      done
      using final_subset apply(auto)
      done
next
  case (Prev I \<phi>)
  then have "finite
            {v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) (i-1) \<phi>}"
    apply(simp)
    done
  then show ?case
    apply(simp)
    apply(cases "i")
     apply(simp)
    apply(simp)
    apply(elim finite_subset[rotated])
    by(auto)
next
  case (Next I \<phi>)
  then have "finite
     {v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) (Suc i) \<phi>}"
    apply(simp)
    done
  then show ?case using Next
    apply(elim finite_subset[rotated])
    by(auto)
next
  case (Since \<phi> I \<psi>)
  then have "\<forall> j. finite {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>}"
    by(simp)
  then have "finite (\<Union> j\<le>i. {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>})"
    by(auto)
  then show ?case using Since
    apply(elim finite_subset[rotated])
    by(auto simp add: Un_absorb1)
next
  case (Not_Since \<phi> I \<psi>)
  then have "\<forall> j. finite {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>}"
    by(simp)
  then have "finite (\<Union> j\<le>i. {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>})"
    by(auto)
  then show ?case using Not_Since
    apply(elim finite_subset[rotated])
    by(auto simp add: Un_absorb1)
next
  case (Until \<phi> I \<psi>)
  then obtain m j where m: "\<not> memR I m" and "m = (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    apply(auto)
    apply(atomize_elim)
    apply(simp add: bounded_memR)
    by (metis (no_types, opaque_lifting) add_diff_cancel_right' diff_le_mono ex_le_\<tau> memR_antimono)
  moreover from Until have "\<forall> j. finite {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>}"
    by(simp)
  moreover from Until have "finite (\<Union> j'\<le>j. {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j' \<psi>})"
    by(auto)
  ultimately show ?case using Until
    apply(elim finite_subset[rotated])
    apply(simp add: Un_absorb1)
    apply(auto)
    subgoal for v j2
      apply(cases "(\<tau> \<sigma> j2 - \<tau> \<sigma> i)\<le>m")
      subgoal
        apply(auto)
        apply(subgoal_tac "j2\<le>j")
         apply blast
        by (metis \<tau>_mono diff_le_mono le_antisym nat_le_linear)
      subgoal
        apply(subgoal_tac "\<not> memR I (\<tau> \<sigma> j2 - \<tau> \<sigma> i)")
         apply blast
        apply(auto)
        by (meson memR_antimono nat_le_linear)
      done
    done
next
  case (Not_Until \<phi> I \<psi>)
  then obtain m j where m: "\<not> memR I m" and "m = (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    apply(auto)
    apply(atomize_elim)
    apply(simp add: bounded_memR)
    by (metis (no_types, opaque_lifting) add_diff_cancel_right' diff_le_mono ex_le_\<tau> memR_antimono)
  moreover from Not_Until have "\<forall> j. finite {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>}"
    by(simp)
  moreover from Not_Until have "finite (\<Union> j'\<le>j. {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j' \<psi>})"
    by(auto)
  ultimately show ?case using Not_Until
    apply(elim finite_subset[rotated])
    apply(simp add: Un_absorb1)
    apply(auto)
    subgoal for v j2
      apply(cases "(\<tau> \<sigma> j2 - \<tau> \<sigma> i)\<le>m")
      subgoal
        apply(auto)
        apply(subgoal_tac "j2\<le>j")
         apply blast
        by (metis \<tau>_mono diff_le_mono le_antisym nat_le_linear)
      subgoal
        apply(subgoal_tac "\<not> memR I (\<tau> \<sigma> j2 - \<tau> \<sigma> i)")
         apply blast
        apply(auto)
        by (meson memR_antimono nat_le_linear)
      done
    done
next
  case (MatchP I r)
  from MatchP(1,3-) have IH: "finite {v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) k \<phi>}"
    if "\<phi> \<in> atms r" for k \<phi> using that
    apply (intro MatchP(2)[rule_format, OF that])
       apply (auto simp: regex.pred_set atms_def Regex.nfv_regex_def fv_regex_alt Formula.nfv_def)
     apply (auto split: Formula.formula.splits)
    done
  from MatchP(3-) show ?case
    by (intro finite_subset[OF _ safe_regex_Past_finite[OF MatchP(1) IH, of i]]) auto
next
  case (MatchF I r)
  then obtain m j where m: "\<not> memR I m" "m = (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    apply(auto)
    apply(atomize_elim)
    apply(simp add: bounded_memR)
    by (metis (no_types, opaque_lifting) add_diff_cancel_right' diff_le_mono ex_le_\<tau> memR_antimono)
  from MatchF(1,3-) have IH: "finite {v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) k \<phi>}"
    if "\<phi> \<in> atms r" for k \<phi> using that
    apply (intro MatchF(2)[rule_format, OF that])
       apply (auto simp: regex.pred_set atms_def Regex.nfv_regex_def fv_regex_alt Formula.nfv_def)
     apply (auto split: Formula.formula.splits)
    done
  from MatchF(3-) m show ?case
    apply (intro finite_subset[OF _ safe_regex_Future_finite[OF MatchF(1) IH, of i j]])
     apply clarsimp
     apply (erule bexI[where A = "{i .. j}"])
     apply auto
    apply (meson \<tau>_mono diff_le_mono le_cases memR_antimono)
    done
next
  case (TP t)
  then show ?case
    unfolding Formula.is_Var_def Formula.is_Const_def Formula.nfv_def 
    by (auto simp add: wf_tuple_empty_iff Collect_singleton_tuple_eq_image[where P="\<lambda>x. x = _"])
next
  case (TS t)
  then show ?case
    unfolding Formula.is_Var_def Formula.is_Const_def Formula.nfv_def
    by (auto simp add: wf_tuple_empty_iff Collect_singleton_tuple_eq_image[where P="\<lambda>x. x = _"])
qed

*)

subsection \<open>Slicing traces\<close>

qualified fun matches ::
  "Formula.env \<Rightarrow> 't Formula.formula \<Rightarrow> Formula.name \<times> event_data list \<Rightarrow> bool" where
  "matches v (Formula.Pred r ts) e = (fst e = r \<and> map (Formula.eval_trm v) ts = snd e)"
| "matches v (Formula.Let p \<phi> \<psi>) e =
    ((\<exists>v'. matches v' \<phi> e \<and> matches v \<psi> (p, v')) \<or>
    (fst e \<noteq> p \<or> length (snd e) \<noteq> Formula.nfv \<phi>) \<and> matches v \<psi> e)"
| "matches v (Formula.LetPast p \<phi> \<psi>) e =
    ((fst e \<noteq> p \<or> length (snd e) \<noteq> Formula.nfv \<phi>) \<and>
      (\<exists>e'. (\<lambda>e' e. matches (snd e') \<phi> e \<and> fst e' = p)\<^sup>*\<^sup>* e' e \<and> matches v \<psi> e'))"
| "matches v (Formula.Eq _ _) e = False"
| "matches v (Formula.Less _ _) e = False"
| "matches v (Formula.LessEq _ _) e = False"
| "matches v (\<not>\<^sub>F \<phi>) e = matches v \<phi> e"
| "matches v (\<phi> \<or>\<^sub>F \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (\<phi> \<and>\<^sub>F \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (\<And>\<^sub>F l) e = (\<exists>\<phi>\<in>set l. matches v \<phi> e)"
| "matches v (\<exists>\<^sub>F:t. \<phi>) e = (\<exists>z. matches (z # v) \<phi> e)"
| "matches v (Formula.Agg y \<omega> tys f \<phi>) e = (\<exists>zs. length zs = length tys \<and> matches (zs @ v) \<phi> e)"
| "matches v (\<^bold>Y I \<phi>) e = matches v \<phi> e"
| "matches v (\<^bold>X I \<phi>) e = matches v \<phi> e"
| "matches v (\<phi> \<^bold>S I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (\<phi> \<^bold>U I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Formula.MatchP I r) e = (\<exists>\<phi> \<in> Regex.atms r. matches v \<phi> e)"
| "matches v (Formula.MatchF I r) e = (\<exists>\<phi> \<in> Regex.atms r. matches v \<phi> e)"
| "matches v (Formula.TP _) e = False"
| "matches v (Formula.TS _) e = False"

lemma matches_cong:
  "\<forall>x\<in>fv \<phi>. v!x = v'!x \<Longrightarrow> matches v \<phi> e = matches v' \<phi> e"
proof (induct \<phi> arbitrary: v v' e)
  case (Pred n ts)
  show ?case
    by (simp cong: map_cong eval_trm_fv_cong[OF Pred(1)[simplified, THEN bspec]])
next
  case (Let p \<phi> \<psi>)
  then show ?case
    by (cases e) (auto 11 0)
next
  case (LetPast p \<phi> \<psi>)
  then show ?case
    by (cases e) (auto 11 0)
next
  case (Ands l)
  have "\<And>\<phi>. \<phi> \<in> (set l) \<Longrightarrow> matches v \<phi> e = matches v' \<phi> e"
  proof -
    fix \<phi> assume "\<phi> \<in> (set l)"
    then have "fv \<phi> \<subseteq> fv (\<And>\<^sub>F l)" using fv_subset_Ands by blast
    then have "\<forall>x\<in>fv \<phi>. v!x = v'!x" using Ands.prems by blast
    then show "matches v \<phi> e = matches v' \<phi> e" using Ands.hyps \<open>\<phi> \<in> set l\<close> by blast
  qed
  then show ?case by simp
next
  case (Exists \<phi>)
  then show ?case unfolding matches.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
next
  case (Agg y \<omega> tys f \<phi>)
  let ?b = "length tys"
  have "matches (zs @ v) \<phi> e = matches (zs @ v') \<phi> e" if "length zs = ?b" for zs
    using that Agg.prems by (simp add: Agg.hyps[where v="zs @ v" and v'="zs @ v'"]
        nth_append fvi_iff_fv(1)[where b= ?b])
  then show ?case by auto
qed (auto 9 0 simp add: nth_Cons' fv_regex_alt)

abbreviation relevant_events where "relevant_events \<phi> S \<equiv> {e. S \<inter> {v. matches v \<phi> e} \<noteq> {}}"

lemma sat_slice_strong:
  assumes "v \<in> S" "dom V = dom V'"
    "\<And>p n v i. (p, n) \<in> dom V \<Longrightarrow> (p, v) \<in> relevant_events \<phi> S \<Longrightarrow> n = length v \<Longrightarrow>
      the (V (p, n)) v i = the (V' (p, n)) v i"
  shows "relevant_events \<phi> S - {e. (fst e, length (snd e)) \<in> dom V} \<subseteq> E \<Longrightarrow>
    Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>"
  using assms
proof (induction \<phi> arbitrary: V V' v S i)
  case (Pred r ts)
  let ?rn = "(r, length ts)"
  show ?case proof (cases "V ?rn")
    case None
    then have "V' ?rn = None" using \<open>dom V = dom V'\<close> by auto
    with None Pred(1,2) show ?thesis by (auto simp: domIff dest!: subsetD)
  next
    case (Some a)
    moreover obtain a' where "V' ?rn = Some a'" using Some \<open>dom V = dom V'\<close> by auto
    moreover have "the (V ?rn) (map (Formula.eval_trm v) ts) i = the (V' ?rn) (map (Formula.eval_trm v) ts) i"
      using Some Pred(2,4) by force
    ultimately show ?thesis by simp
  qed
next
  case (Let p \<phi> \<psi>)
  from Let.prems show ?case unfolding sat.simps
  proof (intro Let(2)[of S], goal_cases relevant v dom V)
    case (V p' n v' i)
    then show ?case
    proof (cases "(p', n) = (p, Formula.nfv \<phi>)")
      case True
      with V show ?thesis
        unfolding fun_upd_apply eqTrueI[OF True] if_True option.sel mem_Collect_eq
      proof (intro conj_cong refl Let(1)[where
        S="{v'. (p, v') \<in> relevant_events \<psi> S}" and V=V],
        goal_cases relevant' v' dom' V')
        case relevant'
        then show ?case
          by (elim subset_trans[rotated]) (auto simp: set_eq_iff)
      next
        case v'
        with True show ?case by simp
      next
        case (V' p' v' i)
        then show ?case
          by (intro V(4)) (auto simp: set_eq_iff)
      qed auto
    next
      case False
      from V(3,5,6,7) show ?thesis
        unfolding fun_upd_apply eq_False[THEN iffD2, OF False] if_False
        using False by (intro V(4)) (auto simp add: dom_def)
    qed
  qed (auto simp: dom_def)
next
  case (LetPast p \<phi> \<psi>)
  show ?case unfolding sat.simps Let_def
  proof (intro LetPast.IH(2)[of "S"], goal_cases relevant v dom V)
    case (V p' n v' i')
    show ?case
    proof (cases "(p', n) = (p, Formula.nfv \<phi>)")
      case True
      let ?pn = "(p, Formula.nfv \<phi>)"
      let ?R = "(\<lambda>e' e. matches (snd e') \<phi> e \<and> fst e' = p)\<^sup>*\<^sup>*"
      have inter_matches_imp_R: "{w. ?R (p, v') (p, w)} \<inter> {w. matches w \<phi> (p'', u)} \<noteq> {} \<Longrightarrow>
        ?R (p, v') (p'', u)" for p'' u
        by (auto intro: rtranclp.rtrancl_into_rtrancl)

      have "letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>) w j =
          letpast_sat (\<lambda>X u k. Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) (V'(?pn \<mapsto> X)) u k \<phi>) w j"
        if "?R (p, v') (p, w)" "j \<le> i'" for w j
        using that
      proof (induct "\<lambda>X u k. Formula.sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>" w j rule: letpast_sat.induct)
        case (1 w j)
        show ?case
        proof (subst (1 2) letpast_sat.simps,
            rule LetPast.IH(1)[where S="{w. ?R (p, v') (p, w)}"],
            goal_cases relevant R dom eq)
          case relevant
          have "relevant_events \<phi> {w. ?R (p, v') (p, w)} - {e. (fst e, length (snd e)) \<in> insert ?pn (dom V)}
          \<subseteq> relevant_events (Formula.LetPast p \<phi> \<psi>) S - {e. (fst e, length (snd e)) \<in> dom V}"
            using V(2) True
            by (fastforce dest!: inter_matches_imp_R)
          also have "insert ?pn (dom V) = dom (V(?pn \<mapsto> \<lambda>w j'. j' < j \<and> letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>) w j'))"
            by simp
          finally show ?case
            using LetPast.prems(1) by (rule subset_trans)
        next
          case R
          with 1 show ?case by simp
        next
          case dom
          then show ?case
            using LetPast.prems(3) by (auto simp add: dom_def)
        next
          case (eq p'' n' w' j')
          show ?case proof (cases "(p'', n') = ?pn")
            case True
            moreover have "letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>) w' j' =
            letpast_sat (\<lambda>X u k. Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) (V'(?pn \<mapsto> X)) u k \<phi>) w' j'"
              if "j' < j"
              using that eq "1" True
              by (auto split: if_splits dest!: inter_matches_imp_R)
            ultimately show ?thesis
              by (simp cong: conj_cong)
          next
            case False
            then show ?thesis
              using eq V(2) LetPast.prems(4)[of p'' n' w' j'] True
              by (fastforce simp add: dom_def dest!: inter_matches_imp_R)
          qed
        qed
      qed
      then show ?thesis
        by (auto simp add: True)
    next
      case False
      then show ?thesis
        using V LetPast.prems(4)[of p' n v' i']
        by (fastforce simp: dom_def)
    qed
  qed (use LetPast.prems in \<open>auto simp: dom_def\<close>)
next
  case (Or \<phi> \<psi>)
  show ?case using Or.IH[of S V v V'] Or.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (And \<phi> \<psi>)
  show ?case using And.IH[of S V v V'] And.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (Ands l)
  obtain "relevant_events (\<And>\<^sub>F l) S - {e. (fst e, length (snd e)) \<in> dom V} \<subseteq> E" "v \<in> S"
    using Ands.prems(1) Ands.prems(2) by blast
  then have "{e. S \<inter> {v. matches v (\<And>\<^sub>F l) e} \<noteq> {}} - {e. (fst e, length (snd e)) \<in> dom V} \<subseteq> E" by simp
  have "\<And>\<phi>. \<phi> \<in> set l \<Longrightarrow> Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>"
  proof -
    fix \<phi> assume "\<phi> \<in> set l"
    have "relevant_events \<phi> S = {e. S \<inter> {v. matches v \<phi> e} \<noteq> {}}" by simp
    have "{e. S \<inter> {v. matches v \<phi> e} \<noteq> {}} \<subseteq> {e. S \<inter> {v. matches v (\<And>\<^sub>F l) e} \<noteq> {}}" (is "?A \<subseteq> ?B")
    proof (rule subsetI)
      fix e assume "e \<in> ?A"
      then have "S \<inter> {v. matches v \<phi> e} \<noteq> {}" by blast
      moreover have "S \<inter> {v. matches v (\<And>\<^sub>F l) e} \<noteq> {}"
      proof -
        obtain v where "v \<in> S" "matches v \<phi> e" using calculation by blast
        then show ?thesis using \<open>\<phi> \<in> set l\<close> by auto
      qed
      then show "e \<in> ?B" by blast
    qed
    then have "relevant_events \<phi> S - {e. (fst e, length (snd e)) \<in> dom V} \<subseteq> E"
      using Ands.prems(1) by auto
    then show "Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>"
      using Ands.prems(2,3) \<open>\<phi> \<in> set l\<close>
      by (intro Ands.IH[of \<phi> S V v V' i] Ands.prems(4)) auto
  qed
  show ?case using \<open>\<And>\<phi>. \<phi> \<in> set l \<Longrightarrow> Formula.sat \<sigma> V v i \<phi> = Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>\<close> sat_Ands by blast
next
  case (Exists t \<phi>)
  have "Formula.sat \<sigma> V (z # v) i \<phi> = Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' (z # v) i \<phi>" for z
    using Exists.prems(1-3) by (intro Exists.IH[where S="{z # v | v. v \<in> S}"] Exists.prems(4)) auto
  then show ?case by simp
next
  case (Agg y \<omega> tys f \<phi>)
  have "Formula.sat \<sigma> V (zs @ v) i \<phi> = Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' (zs @ v) i \<phi>" if "length zs = length tys" for zs
    using that Agg.prems(1-3) by (intro Agg.IH[where S="{zs @ v | v. v \<in> S}"] Agg.prems(4)) auto
  then show ?case by (simp cong: conj_cong)
next
  case (Prev I \<phi>)
  then show ?case by (auto cong: nat.case_cong)
next
  case (Next I \<phi>)
  then show ?case by simp
next
  case (Since \<phi> I \<psi>)
  show ?case using Since.IH[of S V] Since.prems
   by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (Until \<phi> I \<psi>)
  show ?case using Until.IH[of S V] Until.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (MatchP I r)
  from MatchP.prems(1-3) have "Regex.match (Formula.sat \<sigma> V v) r = Regex.match (Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v) r"
    by (intro Regex.match_fv_cong MatchP(1)[of _ S V v] MatchP.prems(4)) auto
  then show ?case
    by auto
next
  case (MatchF I r)
  from MatchF.prems(1-3) have "Regex.match (Formula.sat \<sigma> V v) r = Regex.match (Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v) r"
    by (intro Regex.match_fv_cong MatchF(1)[of _ S V v] MatchF.prems(4)) auto
  then show ?case
    by auto
qed simp_all

end (*context*)


interpretation Formula_slicer: abstract_slicer "relevant_events \<phi>" for \<phi> .

lemma sat_slice_iff:
  assumes "v \<in> S"
  shows "Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> Formula.sat (Formula_slicer.slice Formula_slicer \<phi> S \<sigma>) V v i \<phi>" (*added Formula_slicer*)
  by (rule sat_slice_strong[OF assms]) auto

lemma Neg_splits:
  "P (case \<phi> of Formula.formula.Neg \<psi> \<Rightarrow> f \<psi> | \<phi> \<Rightarrow> g \<phi>) =
   ((\<forall>\<psi>. \<phi> = Formula.formula.Neg \<psi> \<longrightarrow> P (f \<psi>)) \<and> ((\<not> Formula.is_Neg \<phi>) \<longrightarrow> P (g \<phi>)))"
  "P (case \<phi> of Formula.formula.Neg \<psi> \<Rightarrow> f \<psi> | _ \<Rightarrow> g \<phi>) =
   (\<not> ((\<exists>\<psi>. \<phi> = Formula.formula.Neg \<psi> \<and> \<not> P (f \<psi>)) \<or> ((\<not> Formula.is_Neg \<phi>) \<and> \<not> P (g \<phi>))))"
  by (cases \<phi>; auto simp: Formula.is_Neg_def)+

unbundle MFODL_no_notation \<comment> \<open> disable notation \<close>


(*<*)
end
(*>*)