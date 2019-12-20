(*<*)
theory Formula
  imports Interval
    Trace Regex
    "MFOTL_Monitor.Table"
begin
(*>*)

section \<open>Metric First-order Temporal Logic\<close>

context begin

subsection \<open>Formulas and Satisfiability\<close>

qualified type_synonym name = string
qualified type_synonym 'a event = "(name \<times> 'a list)"
qualified type_synonym 'a database = "'a event set"
qualified type_synonym 'a prefix = "(name \<times> 'a list) prefix"
qualified type_synonym 'a trace = "(name \<times> 'a list) trace"

qualified type_synonym 'a env = "'a list"

subsubsection \<open>Syntax\<close>

qualified datatype 'a trm = Var nat | is_Const: Const 'a

qualified primrec fvi_trm :: "nat \<Rightarrow> 'a trm \<Rightarrow> nat set" where
  "fvi_trm b (Var x) = (if b \<le> x then {x - b} else {})"
| "fvi_trm b (Const _) = {}"

abbreviation "fv_trm \<equiv> fvi_trm 0"

qualified primrec eval_trm :: "'a env \<Rightarrow> 'a trm \<Rightarrow> 'a" where
  "eval_trm v (Var x) = v ! x"
| "eval_trm v (Const x) = x"

lemma eval_trm_fv_cong: "\<forall>x\<in>fv_trm t. v ! x = v' ! x \<Longrightarrow> eval_trm v t = eval_trm v' t"
  by (cases t) simp_all

qualified datatype (discs_sels) 'a formula = Pred name "'a trm list" | Eq "'a trm" "'a trm"
  | Neg "'a formula" | Or "'a formula" "'a formula" | Ands "'a formula list" | Exists "'a formula"
  | Agg nat "('a \<times> enat) set \<Rightarrow> 'a" nat "'a env \<Rightarrow> 'a" "'a formula"
  | Prev \<I> "'a formula" | Next \<I> "'a formula"
  | Since "'a formula" \<I> "'a formula" | Until "'a formula" \<I> "'a formula"
  | MatchF \<I> "'a formula Regex.regex" | MatchP \<I> "'a formula Regex.regex"

qualified definition "FF = Exists (Neg (Eq (Var 0) (Var 0)))"
qualified definition "TT \<equiv> Neg FF"

qualified fun fvi :: "nat \<Rightarrow> 'a formula \<Rightarrow> nat set" where
  "fvi b (Pred r ts) = (\<Union>t\<in>set ts. fvi_trm b t)"
| "fvi b (Eq t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (Neg \<phi>) = fvi b \<phi>"
| "fvi b (Or \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Ands \<phi>s) = (let xs = map (fvi b) \<phi>s in \<Union>x\<in>set xs. x)"
| "fvi b (Exists \<phi>) = fvi (Suc b) \<phi>"
| "fvi b (Agg y \<omega> b' f \<phi>) = fvi (b + b') \<phi> \<union> (if b \<le> y then {y - b} else {})"
| "fvi b (Prev I \<phi>) = fvi b \<phi>"
| "fvi b (Next I \<phi>) = fvi b \<phi>"
| "fvi b (Since \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Until \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (MatchF I r) = Regex.fv_regex (fvi b) r"
| "fvi b (MatchP I r) = Regex.fv_regex (fvi b) r"

abbreviation "fv \<equiv> fvi 0"
abbreviation "fv_regex \<equiv> Regex.fv_regex fv"

lemma fv_abbrevs[simp]: "fv TT = {}" "fv FF = {}"
  unfolding TT_def FF_def by auto

lemma fv_subset_Ands: "\<phi> \<in> set \<phi>s \<Longrightarrow> fv \<phi> \<subseteq> fv (Ands \<phi>s)"
  by auto

lemma finite_fvi_trm[simp]: "finite (fvi_trm b t)"
  by (cases t) simp_all

lemma finite_fvi[simp]:
  fixes \<phi> :: "'a formula"
  shows "finite (fvi b \<phi>)"
  by (induction \<phi> arbitrary: b) simp_all

lemma fvi_trm_plus: "x \<in> fvi_trm (b + c) t \<longleftrightarrow> x + c \<in> fvi_trm b t"
  by (cases t) auto

lemma fvi_plus:
  fixes \<phi> :: "'a formula"
  shows "x \<in> fvi (b + c) \<phi> \<longleftrightarrow> x + c \<in> fvi b \<phi>"
proof (induction \<phi> arbitrary: b rule: formula.induct)
  case (Exists \<phi>)
  then show ?case by force
next
  case (Agg y \<omega> b' f \<phi>)
  have *: "b + c + b' = b + b' + c" by simp
  from Agg show ?case by (force simp: *)
qed (auto simp add: fvi_trm_plus fv_regex_commute[where g = "\<lambda>x. x + c"])

lemma fvi_Suc:
  "x \<in> fvi (Suc b) \<phi> \<longleftrightarrow> Suc x \<in> fvi b \<phi>"
  using fvi_plus[where c=1] by simp

lemma fvi_plus_bound:
  assumes "\<forall>i\<in>fvi (b + c) \<phi>. i < n"
  shows "\<forall>i\<in>fvi b \<phi>. i < c + n"
proof
  fix i
  assume "i \<in> fvi b \<phi>"
  show "i < c + n"
  proof (cases "i < c")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain i' where "i = i' + c"
      using nat_le_iff_add by (auto simp: not_less)
    with assms \<open>i \<in> fvi b \<phi>\<close> show ?thesis by (simp add: fvi_plus)
  qed
qed

lemma fvi_Suc_bound:
  assumes "\<forall>i\<in>fvi (Suc b) \<phi>. i < n"
  shows "\<forall>i\<in>fvi b \<phi>. i < Suc n"
  using assms fvi_plus_bound[where c=1] by simp

lemma fvi_iff_fv:
  "x \<in> fvi b \<phi> \<longleftrightarrow> x + b \<in> fv \<phi>"
  using fvi_plus[where b=0 and c=b] by simp_all

qualified definition nfv :: "'a formula \<Rightarrow> nat" where
  "nfv \<phi> = Max (insert 0 (Suc ` fv \<phi>))"

qualified abbreviation nfv_regex where
  "nfv_regex \<equiv> Regex.nfv_regex fv"

qualified definition envs :: "'a formula \<Rightarrow> 'a env set" where
  "envs \<phi> = {v. length v = nfv \<phi>}"

lemma nfv_simps[simp]:
  "nfv (Neg \<phi>) = nfv \<phi>"
  "nfv (Or \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Prev I \<phi>) = nfv \<phi>"
  "nfv (Next I \<phi>) = nfv \<phi>"
  "nfv (Since \<phi> I \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Until \<phi> I \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (MatchP I r) = Regex.nfv_regex fv r"
  "nfv (MatchF I r) = Regex.nfv_regex fv r"
  "nfv_regex (Regex.Skip n) = 0"
  "nfv_regex (Regex.Test \<phi>) = Max (insert 0 (Suc ` fv \<phi>))"
  "nfv_regex (Regex.Plus r s) = max (nfv_regex r) (nfv_regex s)"
  "nfv_regex (Regex.Times r s) = max (nfv_regex r) (nfv_regex s)"
  "nfv_regex (Regex.Star r) = nfv_regex r"
  unfolding nfv_def Regex.nfv_regex_def by (simp_all add: image_Un Max_Un[symmetric])

lemma nfv_Ands[simp]: "nfv (Ands l) = Max (insert 0 (nfv ` set l))"
proof (induction l)
  case Nil
  then show ?case unfolding nfv_def by simp
next
  case (Cons a l)
  have "fv (Ands (a # l)) = fv a \<union> fv (Ands l)" by simp
  then have "nfv (Ands (a # l)) = max (nfv a) (nfv (Ands l))"
    unfolding nfv_def
    by (auto simp: image_Un Max.union[symmetric])
  with Cons.IH show ?case
    by (cases l) auto
qed

lemma fvi_less_nfv: "\<forall>i\<in>fv \<phi>. i < nfv \<phi>"
  unfolding nfv_def
  by (auto simp add: Max_gr_iff intro: max.strict_coboundedI2)

lemma fvi_less_nfv_regex: "\<forall>i\<in>fv_regex \<phi>. i < nfv_regex \<phi>"
  unfolding Regex.nfv_regex_def
  by (auto simp add: Max_gr_iff intro: max.strict_coboundedI2)

subsubsection \<open>Future Reach\<close>

qualified fun future_reach :: "'a formula \<Rightarrow> enat" where
  "future_reach (Pred _ _) = 0"
| "future_reach (Eq _ _) = 0"
| "future_reach (Neg \<phi>) = future_reach \<phi>"
| "future_reach (Or \<phi> \<psi>) = max (future_reach \<phi>) (future_reach \<psi>)"
| "future_reach (Ands l) = foldl max 0 (map future_reach l)"
| "future_reach (Exists \<phi>) = future_reach \<phi>"
| "future_reach (Agg y \<omega> b f \<phi>) = future_reach \<phi>"
| "future_reach (Prev I \<phi>) = future_reach \<phi> - left I"
| "future_reach (Next I \<phi>) = future_reach \<phi> + right I + 1"
| "future_reach (Since \<phi> I \<psi>) = max (future_reach \<phi>) (future_reach \<psi> - left I)"
| "future_reach (Until \<phi> I \<psi>) = max (future_reach \<phi>) (future_reach \<psi>) + right I + 1"
| "future_reach (MatchP I r) = Regex.max_regex future_reach r - left I"
| "future_reach (MatchF I r) = Regex.max_regex future_reach r + right I + 1"

lemma foldl_Max:
  assumes "l \<noteq> []"
  shows "foldl max n l = max n (Max (set l))"
  using assms
proof (induction l arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  show ?case
  proof (cases "l = []")
    case False
    then have "foldl max (max n a) l = max (max n a) (Max (set l))"
      using Cons.IH by simp
    also have "... = max n (max a (Max (set l)))" by (simp add: max.assoc)
    moreover have "max a (Max (set l)) = Max (set [a] \<union> set l)"
      using \<open>l \<noteq> []\<close> by simp
    ultimately show ?thesis by simp
  qed simp
qed

lemma foldl_max_infinity:
  "foldl max \<infinity> (l::enat list) = \<infinity>"
  by (induction l) auto

lemma foldl_max_infinity_iff: "r \<noteq> \<infinity> \<Longrightarrow> foldl max r (l::enat list) = \<infinity> \<longleftrightarrow> \<infinity> \<in> set l"
proof (induct l arbitrary: r)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case by (cases a) (auto simp: foldl_max_infinity)
qed

lemma future_reach_Ands_bounded: "future_reach (Ands l) \<noteq> \<infinity> \<longleftrightarrow> (\<forall>\<phi>\<in>set l. future_reach \<phi> \<noteq> \<infinity>)"
  by (force simp: foldl_max_infinity_iff)

subsubsection \<open>Semantics\<close>

definition "ecard A = (if finite A then card A else \<infinity>)"

qualified definition fv_env :: "'a formula \<Rightarrow> 'a env \<Rightarrow> 'a env" where
  "fv_env \<phi> v = [v ! x. x \<leftarrow> [0..<nfv \<phi>], x \<in> fv \<phi>]"

lemma fv_env_fv_cong: "\<forall>x\<in>fv \<phi>. v ! x = v' ! x \<Longrightarrow> fv_env \<phi> v = fv_env \<phi> v'"
  unfolding fv_env_def by (auto intro!: arg_cong[where f=concat] cong: map_cong)

qualified fun sat :: "'a trace \<Rightarrow> 'a env \<Rightarrow> nat \<Rightarrow> 'a formula \<Rightarrow> bool" where
  "sat \<sigma> v i (Pred r ts) = ((r, map (eval_trm v) ts) \<in> \<Gamma> \<sigma> i)"
| "sat \<sigma> v i (Eq t1 t2) = (eval_trm v t1 = eval_trm v t2)"
| "sat \<sigma> v i (Neg \<phi>) = (\<not> sat \<sigma> v i \<phi>)"
| "sat \<sigma> v i (Or \<phi> \<psi>) = (sat \<sigma> v i \<phi> \<or> sat \<sigma> v i \<psi>)"
| "sat \<sigma> v i (Ands l) = list_all id (map (sat \<sigma> v i) l)"
| "sat \<sigma> v i (Exists \<phi>) = (\<exists>z. sat \<sigma> (z # v) i \<phi>)"
| "sat \<sigma> v i (Agg y \<omega> b f \<phi>) =
    (let M = {(x, ecard Zs) | x Zs. Zs = {zs. length zs = b \<and> sat \<sigma> (zs @ v) i \<phi> \<and> f (fv_env \<phi> (zs @ v)) = x} \<and> Zs \<noteq> {}}
    in (M = {} \<longrightarrow> fv \<phi> \<subseteq> {..<b}) \<and> v ! y = \<omega> M)"
| "sat \<sigma> v i (Prev I \<phi>) = (case i of 0 \<Rightarrow> False | Suc j \<Rightarrow> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> sat \<sigma> v j \<phi>)"
| "sat \<sigma> v i (Next I \<phi>) = (mem (\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i) I \<and> sat \<sigma> v (Suc i) \<phi>)"
| "sat \<sigma> v i (Since \<phi> I \<psi>) = (\<exists>j\<le>i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> sat \<sigma> v j \<psi> \<and> (\<forall>k \<in> {j <.. i}. sat \<sigma> v k \<phi>))"
| "sat \<sigma> v i (Until \<phi> I \<psi>) = (\<exists>j\<ge>i. mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> sat \<sigma> v j \<psi> \<and> (\<forall>k \<in> {i ..< j}. sat \<sigma> v k \<phi>))"
| "sat \<sigma> v i (MatchP I r) = (\<exists>j\<le>i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> Regex.match (sat \<sigma> v) r j i)"
| "sat \<sigma> v i (MatchF I r) = (\<exists>j\<ge>i. mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> Regex.match (sat \<sigma> v) r i j)"

lemma sat_abbrevs[simp]:
  "sat \<sigma> v i TT" "\<not> sat \<sigma> v i FF"
  unfolding TT_def FF_def by auto

lemma sat_Ands: "sat \<sigma> v i (Ands l) \<longleftrightarrow> (\<forall>\<phi>\<in>set l. sat \<sigma> v i \<phi>)"
  by (simp add: list_all_iff)

lemma sat_Until_rec: "sat \<sigma> v i (Until \<phi> I \<psi>) \<longleftrightarrow>
  mem 0 I \<and> sat \<sigma> v i \<psi> \<or>
  (\<Delta> \<sigma> (i + 1) \<le> right I \<and> sat \<sigma> v i \<phi> \<and> sat \<sigma> v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>))"
  (is "?L \<longleftrightarrow> ?R")
proof (rule iffI; (elim disjE conjE)?)
  assume ?L
  then obtain j where j: "i \<le> j" "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I" "sat \<sigma> v j \<psi>" "\<forall>k \<in> {i ..< j}. sat \<sigma> v k \<phi>"
    by auto
  then show ?R
  proof (cases "i = j")
    case False
    with j(1,2) have "\<Delta> \<sigma> (i + 1) \<le> right I"
      by (auto elim: order_trans[rotated] simp: diff_le_mono)
    moreover from False j(1,4) have "sat \<sigma> v i \<phi>" by auto
    moreover from False j have "sat \<sigma> v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>)"
      by (cases "right I") (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j])
    ultimately show ?thesis by blast
  qed simp
next
  assume \<Delta>: "\<Delta> \<sigma> (i + 1) \<le> right I" and now: "sat \<sigma> v i \<phi>" and
   "next": "sat \<sigma> v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>)"
  from "next" obtain j where j: "i + 1 \<le> j" "mem (\<tau> \<sigma> j - \<tau> \<sigma> (i + 1)) ((subtract (\<Delta> \<sigma> (i + 1)) I))"
      "sat \<sigma> v j \<psi>" "\<forall>k \<in> {i + 1 ..< j}. sat \<sigma> v k \<phi>"
    by auto
  from \<Delta> j(1,2) have "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I"
    by (cases "right I") (auto simp: le_diff_conv2)
  with now j(1,3,4) show ?L by (auto simp: le_eq_less_or_eq[of i] intro!: exI[of _ j])
qed auto

lemma sat_Since_rec: "sat \<sigma> v i (Since \<phi> I \<psi>) \<longleftrightarrow>
  mem 0 I \<and> sat \<sigma> v i \<psi> \<or>
  (i > 0 \<and> \<Delta> \<sigma> i \<le> right I \<and> sat \<sigma> v i \<phi> \<and> sat \<sigma> v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>))"
  (is "?L \<longleftrightarrow> ?R")
proof (rule iffI; (elim disjE conjE)?)
  assume ?L
  then obtain j where j: "j \<le> i" "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I" "sat \<sigma> v j \<psi>" "\<forall>k \<in> {j <.. i}. sat \<sigma> v k \<phi>"
    by auto
  then show ?R
  proof (cases "i = j")
    case False
    with j(1) obtain k where [simp]: "i = k + 1"
      by (cases i) auto
    with j(1,2) False have "\<Delta> \<sigma> i \<le> right I"
      by (auto elim: order_trans[rotated] simp: diff_le_mono2 le_Suc_eq)
    moreover from False j(1,4) have "sat \<sigma> v i \<phi>" by auto
    moreover from False j have "sat \<sigma> v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>)"
      by (cases "right I") (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j])
    ultimately show ?thesis by auto
  qed simp
next
  assume i: "0 < i" and \<Delta>: "\<Delta> \<sigma> i \<le> right I" and now: "sat \<sigma> v i \<phi>" and
   "prev": "sat \<sigma> v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>)"
  from "prev" obtain j where j: "j \<le> i - 1" "mem (\<tau> \<sigma> (i - 1) - \<tau> \<sigma> j) ((subtract (\<Delta> \<sigma> i) I))"
      "sat \<sigma> v j \<psi>" "\<forall>k \<in> {j <.. i - 1}. sat \<sigma> v k \<phi>"
    by auto
  from \<Delta> i j(1,2) have "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I"
    by (cases "right I") (auto simp: le_diff_conv2)
  with now i j(1,3,4) show ?L by (auto simp: le_Suc_eq gr0_conv_Suc intro!: exI[of _ j])
qed auto

lemma sat_MatchF_rec: "sat \<sigma> v i (MatchF I r) \<longleftrightarrow> mem 0 I \<and> Regex.eps (sat \<sigma> v) i r \<or>
  \<Delta> \<sigma> (i + 1) \<le> right I \<and> (\<exists>s \<in> Regex.lpd (sat \<sigma> v) i r. sat \<sigma> v (i + 1) (MatchF (subtract (\<Delta> \<sigma> (i + 1)) I) s))"
  (is "?L \<longleftrightarrow> ?R1 \<or> ?R2")
proof (rule iffI; (elim disjE conjE bexE)?)
  assume ?L
  then obtain j where j: "j \<ge> i" "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I" and "Regex.match (sat \<sigma> v) r i j" by auto
  then show "?R1 \<or> ?R2"
  proof (cases "i < j")
    case True
    with \<open>Regex.match (sat \<sigma> v) r i j\<close> lpd_match[of i j "sat \<sigma> v" r]
    obtain s where "s \<in> Regex.lpd (sat \<sigma> v) i r" "Regex.match (sat \<sigma> v) s (i + 1) j" by auto
    with True j have ?R2
      by (cases "right I")
        (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j] elim: le_trans[rotated])
    then show ?thesis by blast
  qed (auto simp: eps_match)
next
  assume "enat (\<Delta> \<sigma> (i + 1)) \<le> right I"
  moreover
  fix s
  assume [simp]: "s \<in> Regex.lpd (sat \<sigma> v) i r" and "sat \<sigma> v (i + 1) (MatchF (subtract (\<Delta> \<sigma> (i + 1)) I) s)"
  then obtain j where "j > i" "Regex.match (sat \<sigma> v) s (i + 1) j"
    "mem (\<tau> \<sigma> j - \<tau> \<sigma> (Suc i)) (subtract (\<Delta> \<sigma> (i + 1)) I)" by (auto simp: Suc_le_eq)
  ultimately show ?L
    by (cases "right I")
      (auto simp: le_diff_conv lpd_match intro!: exI[of _ j] bexI[of _ s])
qed (auto simp: eps_match intro!: exI[of _ i])

lemma sat_MatchP_rec: "sat \<sigma> v i (MatchP I r) \<longleftrightarrow> mem 0 I \<and> Regex.eps (sat \<sigma> v) i r \<or>
  i > 0 \<and> \<Delta> \<sigma> i \<le> right I \<and> (\<exists>s \<in> Regex.rpd (sat \<sigma> v) i r. sat \<sigma> v (i - 1) (MatchP (subtract (\<Delta> \<sigma> i) I) s))"
  (is "?L \<longleftrightarrow> ?R1 \<or> ?R2")
proof (rule iffI; (elim disjE conjE bexE)?)
  assume ?L
  then obtain j where j: "j \<le> i" "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I" and "Regex.match (sat \<sigma> v) r j i" by auto
  then show "?R1 \<or> ?R2"
  proof (cases "j < i")
    case True
    with \<open>Regex.match (sat \<sigma> v) r j i\<close> rpd_match[of j i "sat \<sigma> v" r]
    obtain s where "s \<in> Regex.rpd (sat \<sigma> v) i r" "Regex.match (sat \<sigma> v) s j (i - 1)" by auto
    with True j have ?R2
      by (cases "right I")
        (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j] elim: le_trans)
    then show ?thesis by blast
  qed (auto simp: eps_match)
next
  assume "enat (\<Delta> \<sigma> i) \<le> right I"
  moreover
  fix s
  assume [simp]: "s \<in> Regex.rpd (sat \<sigma> v) i r" and "sat \<sigma> v (i - 1) (MatchP (subtract (\<Delta> \<sigma> i) I) s)" "i > 0"
  then obtain j where "j < i" "Regex.match (sat \<sigma> v) s j (i - 1)"
    "mem (\<tau> \<sigma> (i - 1) - \<tau> \<sigma> j) (subtract (\<Delta> \<sigma> i) I)" by (auto simp: gr0_conv_Suc less_Suc_eq_le)
  ultimately show ?L
    by (cases "right I")
      (auto simp: le_diff_conv rpd_match intro!: exI[of _ j] bexI[of _ s])
qed (auto simp: eps_match intro!: exI[of _ i])

lemma sat_Since_0: "sat \<sigma> v 0 (Since \<phi> I \<psi>) \<longleftrightarrow> mem 0 I \<and> sat \<sigma> v 0 \<psi>"
  by auto

lemma sat_MatchP_0: "sat \<sigma> v 0 (MatchP I r) \<longleftrightarrow> mem 0 I \<and> Regex.eps (sat \<sigma> v) 0 r"
  by (auto simp: eps_match)

lemma sat_Since_point: "sat \<sigma> v i (Since \<phi> I \<psi>) \<Longrightarrow>
    (\<And>j. j \<le> i \<Longrightarrow> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<Longrightarrow> sat \<sigma> v i (Since \<phi> (point (\<tau> \<sigma> i - \<tau> \<sigma> j)) \<psi>) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto intro: diff_le_self)

lemma sat_MatchP_point: "sat \<sigma> v i (MatchP I r) \<Longrightarrow>
    (\<And>j. j \<le> i \<Longrightarrow> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<Longrightarrow> sat \<sigma> v i (MatchP (point (\<tau> \<sigma> i - \<tau> \<sigma> j)) r) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto intro: diff_le_self)

lemma sat_Since_pointD: "sat \<sigma> v i (Since \<phi> (point t) \<psi>) \<Longrightarrow> mem t I \<Longrightarrow> sat \<sigma> v i (Since \<phi> I \<psi>)"
  by auto

lemma sat_MatchP_pointD: "sat \<sigma> v i (MatchP (point t) r) \<Longrightarrow> mem t I \<Longrightarrow> sat \<sigma> v i (MatchP I r)"
  by auto

lemma sat_fv_cong: "\<forall>x\<in>fv \<phi>. v!x = v'!x \<Longrightarrow> sat \<sigma> v i \<phi> = sat \<sigma> v' i \<phi>"
proof (induct \<phi> arbitrary: v v' i rule: formula.induct)
  case (Pred n ts)
  show ?case by (simp cong: map_cong eval_trm_fv_cong[OF Pred[simplified, THEN bspec]])
next
  case (Eq x1 x2)
  then show ?case  unfolding fvi.simps sat.simps by (metis UnCI eval_trm_fv_cong)
next
  case (Ands l)
  have "\<And>\<phi>. \<phi> \<in> set l \<Longrightarrow> sat \<sigma> v i \<phi> = sat \<sigma> v' i \<phi>"
  proof -
    fix \<phi> assume "\<phi> \<in> set l"
    then have "fv \<phi> \<subseteq> fv (Ands l)" using fv_subset_Ands by blast
    then have "\<forall>x\<in>fv \<phi>. v!x = v'!x" using Ands.prems by blast
    then show "sat \<sigma> v i \<phi> = sat \<sigma> v' i \<phi>" using Ands.hyps \<open>\<phi> \<in> set l\<close> by blast
  qed
  then show ?case using sat_Ands by blast
next
  case (Exists \<phi>)
  then show ?case unfolding sat.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
next
  case (Agg y \<omega> b f \<phi>)
  have "v ! y = v' ! y"
    using Agg.prems by simp
  moreover have "sat \<sigma> (zs @ v) i \<phi> = sat \<sigma> (zs @ v') i \<phi>" if "length zs = b" for zs
    using that Agg.prems by (simp add: Agg.hyps[where v="zs @ v" and v'="zs @ v'"]
        nth_append fvi_iff_fv(1)[where b=b])
  moreover have "f (fv_env \<phi> (zs @ v)) = f (fv_env \<phi> (zs @ v'))" if "length zs = b" for zs
    using that Agg.prems by (simp add: fv_env_fv_cong[where v="zs @ v" and v'="zs @ v'"]
        nth_append fvi_iff_fv(1)[where b=b])
  ultimately show ?case
    by (simp cong: conj_cong)
next
  case (MatchF I r)
  then have "Regex.match (sat \<sigma> v) r = Regex.match (sat \<sigma> v') r"
    by (intro match_fv_cong) (auto simp: fv_regex_alt)
  then show ?case
    by auto
next
  case (MatchP I r)
  then have "Regex.match (sat \<sigma> v) r = Regex.match (sat \<sigma> v') r"
    by (intro match_fv_cong) (auto simp: fv_regex_alt)
  then show ?case
    by auto
qed (auto 8 0 split: nat.splits intro!: iff_exI)

lemma match_fv_cong:
  "\<forall>x\<in>fv_regex r. v!x = v'!x \<Longrightarrow> Regex.match (sat \<sigma> v) r = Regex.match (sat \<sigma> v') r"
  by (rule match_fv_cong, rule sat_fv_cong) (auto simp: fv_regex_alt)

lemma eps_fv_cong:
  "\<forall>x\<in>fv_regex r. v!x = v'!x \<Longrightarrow> Regex.eps (sat \<sigma> v) i r = Regex.eps (sat \<sigma> v') i r"
  unfolding eps_match by (erule match_fv_cong[THEN fun_cong, THEN fun_cong])

subsubsection \<open>Defined Connectives\<close>

qualified definition "And \<phi> \<psi> = Neg (Or (Neg \<phi>) (Neg \<psi>))"

lemma fvi_And: "fvi b (And \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
  unfolding And_def by simp

lemma nfv_And[simp]: "nfv (And \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  unfolding nfv_def by (simp add: fvi_And image_Un Max_Un[symmetric])

lemma future_reach_And: "future_reach (And \<phi> \<psi>) = max (future_reach \<phi>) (future_reach \<psi>)"
  unfolding And_def by simp

lemma sat_And: "sat \<sigma> v i (And \<phi> \<psi>) = (sat \<sigma> v i \<phi> \<and> sat \<sigma> v i \<psi>)"
  unfolding And_def by simp

qualified definition "And_Not \<phi> \<psi> = Neg (Or (Neg \<phi>) \<psi>)"

lemma fvi_And_Not: "fvi b (And_Not \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
  unfolding And_Not_def by simp

lemma nfv_And_Not[simp]: "nfv (And_Not \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  unfolding nfv_def by (simp add: fvi_And_Not image_Un Max_Un[symmetric])

lemma future_reach_And_Not: "future_reach (And_Not \<phi> \<psi>) = max (future_reach \<phi>) (future_reach \<psi>)"
  unfolding And_Not_def by simp

lemma sat_And_Not: "sat \<sigma> v i (And_Not \<phi> \<psi>) = (sat \<sigma> v i \<phi> \<and> \<not> sat \<sigma> v i \<psi>)"
  unfolding And_Not_def by simp


subsection \<open>Safe Formulas\<close>

fun remove_neg :: "'a formula \<Rightarrow> 'a formula" where
  "remove_neg (Neg \<phi>) = \<phi>"
| "remove_neg \<phi> = \<phi>"

lemma fvi_remove_neg[simp]: "fvi b (remove_neg \<phi>) = fvi b \<phi>"
  by (cases \<phi>) simp_all

lemma partition_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x\<in>set xs \<Longrightarrow> f x = g x) \<Longrightarrow> partition f xs = partition g ys"
  by (induction xs arbitrary: ys) auto

lemma size_remove_neg[termination_simp]: "size (remove_neg \<phi>) \<le> size \<phi>"
  by (cases \<phi>) simp_all

fun safe_formula :: "'a formula \<Rightarrow> bool" where
  "safe_formula (Eq t1 t2) = (is_Const t1 \<or> is_Const t2)"
| "safe_formula (Neg (Eq (Const x) (Const y))) = True"
| "safe_formula (Neg (Eq (Var x) (Var y))) = (x = y)"
| "safe_formula (Pred e ts) = True"
| "safe_formula (Neg (Or (Neg \<phi>) \<psi>)) = (safe_formula \<phi> \<and>
    (safe_formula \<psi> \<and> fv \<psi> \<subseteq> fv \<phi> \<or> (case \<psi> of Neg \<psi>' \<Rightarrow> safe_formula \<psi>' | _ \<Rightarrow> False)))"
| "safe_formula (Neg \<phi>) = (fv \<phi> = {} \<and> safe_formula \<phi>)"
| "safe_formula (Or \<phi> \<psi>) = (fv \<psi> = fv \<phi> \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
| "safe_formula (Ands l) = (let (pos, neg) = partition safe_formula l in pos \<noteq> [] \<and>
    list_all safe_formula (map remove_neg neg) \<and> \<Union>(set (map fv neg)) \<subseteq> \<Union>(set (map fv pos)))"
| "safe_formula (Exists \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Agg y \<omega> b f \<phi>) = (safe_formula \<phi> \<and> y + b \<notin> fv \<phi> \<and> {..<b} \<subseteq> fv \<phi>)"
| "safe_formula (Prev I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Next I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Since \<phi> I \<psi>) = (fv \<phi> \<subseteq> fv \<psi> \<and>
    (safe_formula \<phi> \<or> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)) \<and> safe_formula \<psi>)"
| "safe_formula (Until \<phi> I \<psi>) = (fv \<phi> \<subseteq> fv \<psi> \<and>
    (safe_formula \<phi> \<or> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)) \<and> safe_formula \<psi>)"
| "safe_formula (MatchP I r) = Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
     (g = Unsafe \<and> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))) Past Safe r"
| "safe_formula (MatchF I r) = Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
     (g = Unsafe \<and> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))) Future Safe r"

abbreviation "safe_regex \<equiv> Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
  (g = Unsafe \<and> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)))"

lemma safe_regex_safe_formula:
  "safe_regex m g r \<Longrightarrow> \<phi> \<in> Regex.atms r \<Longrightarrow> safe_formula \<phi> \<or>
  (\<exists>\<psi>. \<phi> = Neg \<psi> \<and> safe_formula \<psi>)"
  by (cases g) (auto dest!: safe_regex_safe[rotated] split: formula.splits[where formula=\<phi>])

lemma safe_abbrevs[simp]: "safe_formula TT" "safe_formula FF"
  unfolding TT_def FF_def by auto

definition safe_neg :: "'a formula \<Rightarrow> bool" where
  "safe_neg \<phi> \<longleftrightarrow> (\<not> safe_formula \<phi> \<longrightarrow> safe_formula (remove_neg \<phi>))"

definition atms :: "'a formula Regex.regex \<Rightarrow> 'a formula set" where
  "atms r = (\<Union>\<phi> \<in> Regex.atms r.
     if safe_formula \<phi> then {\<phi>} else case \<phi> of Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {})"

lemma atms_simps[simp]:
  "atms (Regex.Skip n) = {}"
  "atms (Regex.Test \<phi>) = (if safe_formula \<phi> then {\<phi>} else case \<phi> of Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {})"
  "atms (Regex.Plus r s) = atms r \<union> atms s"
  "atms (Regex.Times r s) = atms r \<union> atms s"
  "atms (Regex.Star r) = atms r"
  unfolding atms_def by auto

lemma finite_atms[simp]: "finite (atms r)"
  by (induct r) (auto split: formula.splits)

lemma disjE_Not2: "P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (\<not>P \<Longrightarrow> Q \<Longrightarrow> R) \<Longrightarrow> R"
  by blast

lemma safe_formula_induct[consumes 1]:
  assumes "safe_formula \<phi>"
    and "\<And>t1 t2. is_Const t1 \<Longrightarrow> P (Eq t1 t2)"
    and "\<And>t1 t2. is_Const t2 \<Longrightarrow> P (Eq t1 t2)"
    and "\<And>x y. P (Neg (Eq (Const x) (Const y)))"
    and "\<And>x y. x = y \<Longrightarrow> P (Neg (Eq (Var x) (Var y)))"
    and "\<And>e ts. P (Pred e ts)"
    and "\<And>\<phi> \<psi>. \<not> (safe_formula (Neg \<psi>) \<and> fv \<psi> \<subseteq> fv \<phi>) \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And \<phi> \<psi>)"
    and "\<And>\<phi> \<psi>. safe_formula \<psi> \<Longrightarrow> fv \<psi> \<subseteq> fv \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And_Not \<phi> \<psi>)"
    and "\<And>l neg pos. (pos, neg) = partition safe_formula l \<Longrightarrow> pos \<noteq> [] \<Longrightarrow>
      list_all safe_formula (map remove_neg neg) \<Longrightarrow>
      (\<Union>\<phi>\<in>set neg. fv \<phi>) \<subseteq> (\<Union>\<phi>\<in>set pos. fv \<phi>) \<Longrightarrow>
      list_all P pos \<Longrightarrow> list_all P (map remove_neg neg) \<Longrightarrow> P (Ands l)"
    and "\<And>\<phi>. \<lbrakk>\<forall>t1 t2. \<phi> \<noteq> Eq t1 t2; \<forall>\<psi>\<^sub>1 \<psi>\<^sub>2. \<not> (\<phi> = Or (Neg \<psi>\<^sub>1) \<psi>\<^sub>2 \<and> safe_formula \<psi>\<^sub>2 \<and> fv \<psi>\<^sub>2 \<subseteq> fv \<psi>\<^sub>1);
              \<forall>\<psi>\<^sub>1 \<psi>\<^sub>2 \<psi>\<^sub>2'. \<not> (\<phi> = Or (Neg \<psi>\<^sub>1) \<psi>\<^sub>2 \<and> \<not>(safe_formula \<psi>\<^sub>2 \<and> fv \<psi>\<^sub>2 \<subseteq> fv \<psi>\<^sub>1) \<and> \<psi>\<^sub>2 = Neg \<psi>\<^sub>2') \<rbrakk> \<Longrightarrow>
              fv \<phi> = {} \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Neg \<phi>)"
    and "\<And>\<phi> \<psi>. fv \<psi> = fv \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Or \<phi> \<psi>)"
    and "\<And>\<phi>. P \<phi> \<Longrightarrow> P (Exists \<phi>)"
    and "\<And>y \<omega> b f \<phi>. y + b \<notin> fv \<phi> \<Longrightarrow> {..<b} \<subseteq> fv \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Agg y \<omega> b f \<phi>)"
    and "\<And>I \<phi>. P \<phi> \<Longrightarrow> P (Prev I \<phi>)"
    and "\<And>I \<phi>. P \<phi> \<Longrightarrow> P (Next I \<phi>)"
    and "\<And>\<phi> I \<psi>. fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Since \<phi> I \<psi>)"
    and "\<And>\<phi> I \<psi>. fv (Neg \<phi>) \<subseteq> fv \<psi> \<Longrightarrow>
      \<not> safe_formula (Neg \<phi>) \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Since (Neg \<phi>) I \<psi> )"
    and "\<And>\<phi> I \<psi>. fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Until \<phi> I \<psi>)"
    and "\<And>\<phi> I \<psi>. fv (Neg \<phi>) \<subseteq> fv \<psi> \<Longrightarrow>
      \<not> safe_formula (Neg \<phi>) \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Until (Neg \<phi>) I \<psi>)"
    and "\<And>I r. safe_regex Past Safe r \<Longrightarrow> \<forall>\<phi> \<in> atms r. P \<phi> \<Longrightarrow> P (MatchP I r)"
    and "\<And>I r. safe_regex Future Safe r \<Longrightarrow> \<forall>\<phi> \<in> atms r. P \<phi> \<Longrightarrow> P (MatchF I r)"
  shows "P \<phi>"
using assms(1) proof (induction \<phi> rule: safe_formula.induct)
  case (5 \<phi> \<psi>)
  then show ?case
    by (cases \<psi>)
      (auto 0 3 elim!: disjE_Not2 intro: assms[unfolded And_def And_Not_def])
next
  case (8 l)
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  have "pos \<noteq> []" using "8.prems" posneg by simp
  moreover have safe_remove_neg: "list_all safe_formula (map remove_neg neg)" using "8.prems" posneg by auto
  moreover have "list_all P pos"
    using posneg "8.IH"(1) by (simp add: list_all_iff)
  moreover have "list_all P (map remove_neg neg)"
    using "8.IH"(2)[OF posneg] safe_remove_neg by (simp add: list_all_iff)
  ultimately show ?case using "8.IH"(1) "8.prems" assms(9) posneg by simp
next
  case (13 \<phi> I \<psi>)
  then show ?case
  proof (cases \<phi>)
    case (Ands l)
    then show ?thesis using "13.IH"(1) "13.IH"(3) "13.prems" assms(16) by auto
  qed (auto 0 3 elim!: disjE_Not2 intro: assms)
next
  case (14 \<phi> I \<psi>)
  then show ?case
  proof (cases \<phi>)
    case (Ands l)
    then show ?thesis using "14.IH"(1) "14.IH"(3) "14.prems" assms(18) by auto
  qed (auto 0 3 elim!: disjE_Not2 intro: assms)
next
  case (15 I r)
  then show ?case
    by (intro assms(20)) (auto simp: atms_def dest: safe_regex_safe_formula split: if_splits)
next
  case (16 I r)
  then show ?case
    by (intro assms(21)) (auto simp: atms_def dest: safe_regex_safe_formula split: if_splits)
qed (auto simp: assms)


subsection \<open>Slicing Traces\<close>

qualified fun matches :: "'a env \<Rightarrow> 'a formula \<Rightarrow> name \<times> 'a list \<Rightarrow> bool" where
  "matches v (Pred r ts) e = (r = fst e \<and> map (eval_trm v) ts = snd e)"
| "matches v (Eq _ _) e = False"
| "matches v (Neg \<phi>) e = matches v \<phi> e"
| "matches v (Or \<phi> \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Ands l) e = list_ex id (map (\<lambda>\<phi>. matches v \<phi> e) l)"
| "matches v (Exists \<phi>) e = (\<exists>z. matches (z # v) \<phi> e)"
| "matches v (Agg y \<omega> b f \<phi>) e = (\<exists>zs. length zs = b \<and> matches (zs @ v) \<phi> e)"
| "matches v (Prev I \<phi>) e = matches v \<phi> e"
| "matches v (Next I \<phi>) e = matches v \<phi> e"
| "matches v (Since \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Until \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (MatchP I r) e = (\<exists>\<phi> \<in> Regex.atms r. matches v \<phi> e)"
| "matches v (MatchF I r) e = (\<exists>\<phi> \<in> Regex.atms r. matches v \<phi> e)"

lemma matches_Ands: "matches v (Ands l) e \<longleftrightarrow> (\<exists>\<phi>\<in>set l. matches v \<phi> e)"
  by (simp add: list_ex_iff)

lemma matches_cong:
  "\<forall>x\<in>fv \<phi>. v!x = v'!x \<Longrightarrow> matches v \<phi> e = matches v' \<phi> e"
proof (induct \<phi> arbitrary: v v')
  case (Pred n ts)
  show ?case by (simp cong: map_cong eval_trm_fv_cong[OF Pred[simplified, THEN bspec]])
next
  case (Ands l)
  have "\<And>\<phi>. \<phi> \<in> (set l) \<Longrightarrow> matches v \<phi> e = matches v' \<phi> e"
  proof -
    fix \<phi> assume "\<phi> \<in> (set l)"
    then have "fv \<phi> \<subseteq> fv (Ands l)" using fv_subset_Ands by blast
    then have "\<forall>x\<in>fv \<phi>. v!x = v'!x" using Ands.prems by blast
    then show "matches v \<phi> e = matches v' \<phi> e" using Ands.hyps \<open>\<phi> \<in> set l\<close> by blast
  qed
  then show ?case using matches_Ands by blast
next
  case (Exists \<phi>)
  then show ?case unfolding matches.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
next
  case (Agg y \<omega> b f \<phi>)
  have "matches (zs @ v) \<phi> e = matches (zs @ v') \<phi> e" if "length zs = b" for zs
    using that Agg.prems by (simp add: Agg.hyps[where v="zs @ v" and v'="zs @ v'"]
        nth_append fvi_iff_fv(1)[where b=b])
  then show ?case by auto
qed (auto 8 0 simp add: nth_Cons' fv_regex_alt)

abbreviation relevant_events where
  "relevant_events \<phi> S \<equiv> {e. S \<inter> {v. matches v \<phi> e} \<noteq> {}}"

qualified definition slice :: "'a formula \<Rightarrow> 'a env set \<Rightarrow> 'a trace \<Rightarrow> 'a trace" where
  "slice \<phi> S \<sigma> = map_\<Gamma> (\<lambda>D. D \<inter> relevant_events \<phi> S) \<sigma>"

lemma \<tau>_slice[simp]: "\<tau> (slice \<phi> S \<sigma>) = \<tau> \<sigma>"
  unfolding slice_def by (simp add: fun_eq_iff)

lemma sat_slice_strong:
  assumes "v \<in> S"
  shows "relevant_events \<phi> S \<subseteq> E \<Longrightarrow> sat \<sigma> v i \<phi> \<longleftrightarrow> sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) v i \<phi>"
  using assms
proof (induction \<phi> arbitrary: v S i)
  case (Pred r ts)
  then show ?case by (auto simp: subset_eq)
next
  case (Eq t1 t2)
  show ?case
    unfolding sat.simps
    by simp
next
  case (Neg \<phi>)
  then show ?case by simp
next
  case (Or \<phi> \<psi>)
  show ?case using Or.IH[of S] Or.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (Ands l)
  obtain "relevant_events (Ands l) S \<subseteq> E" "v \<in> S" using Ands.prems(1) Ands.prems(2) by blast
  then have "{e. S \<inter> {v. matches v (Ands l) e} \<noteq> {}} \<subseteq> E" by simp
  have "\<And>\<phi>. \<phi> \<in> set l \<Longrightarrow> sat \<sigma> v i \<phi> \<longleftrightarrow> sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) v i \<phi>"
  proof -
    fix \<phi> assume "\<phi> \<in> set l"
    have "relevant_events \<phi> S = {e. S \<inter> {v. matches v \<phi> e} \<noteq> {}}" by simp
    have "{e. S \<inter> {v. matches v \<phi> e} \<noteq> {}} \<subseteq> {e. S \<inter> {v. matches v (Ands l) e} \<noteq> {}}" (is "?A \<subseteq> ?B")
    proof (rule subsetI)
      fix e assume "e \<in> ?A"
      then have "S \<inter> {v. matches v \<phi> e} \<noteq> {}" by blast
      moreover have "S \<inter> {v. matches v (Ands l) e} \<noteq> {}"
      proof -
        obtain v where "v \<in> S" "matches v \<phi> e" using calculation by blast
        then show ?thesis using \<open>\<phi> \<in> set l\<close> by (auto simp add: matches_Ands list_ex_iff)
      qed
      then show "e \<in> ?B" by blast
    qed
    then have "relevant_events \<phi> S \<subseteq> E" using Ands.prems(1) by auto
    then show "sat \<sigma> v i \<phi> \<longleftrightarrow> sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) v i \<phi>" using Ands.IH[of \<phi> S v i]
      using Ands.prems(2) \<open>\<phi> \<in> set l\<close> by blast
  qed
  show ?case using \<open>\<And>\<phi>. \<phi> \<in> set l \<Longrightarrow> sat \<sigma> v i \<phi> = sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) v i \<phi>\<close> sat_Ands by blast
next
  case (Exists \<phi>)
  have "sat \<sigma> (z # v) i \<phi> = sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) (z # v) i \<phi>" for z
    using Exists.prems by (auto intro!: Exists.IH[of "{z # v | v. v \<in> S}"])
  then show ?case by simp
next
  case (Agg y \<omega> b f \<phi>)
  have "sat \<sigma> (zs @ v) i \<phi> = sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) (zs @ v) i \<phi>" if "length zs = b" for zs
    using that Agg.prems by (auto intro!: Agg.IH[where S="{zs @ v | v. v \<in> S}"])
  then show ?case by (simp cong: conj_cong)
next
  case (Prev I \<phi>)
  then show ?case by (auto cong: nat.case_cong)
next
  case (Next I \<phi>)
  then show ?case by simp
next
  case (Since \<phi> I \<psi>)
  show ?case using Since.IH[of S] Since.prems
   by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (Until \<phi> I \<psi>)
  show ?case using Until.IH[of S] Until.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (MatchP I r)
  from MatchP(2,3) have "Regex.match (sat \<sigma> v) r = Regex.match (sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) v) r"
    by (intro Regex.match_fv_cong) (auto dest!: MatchP(1)[of _ S v, rotated 2])
  then show ?case
    by auto
next
  case (MatchF I r)
  from MatchF(2,3) have "Regex.match (sat \<sigma> v) r = Regex.match (sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) v) r"
    by (intro Regex.match_fv_cong) (auto dest!: MatchF(1)[of _ S v, rotated 2])
  then show ?case
    by auto
qed

lemma sat_slice_iff:
  assumes "v \<in> S"
  shows "sat \<sigma> v i \<phi> \<longleftrightarrow> sat (slice \<phi> S \<sigma>) v i \<phi>"
  unfolding slice_def
  by (rule sat_slice_strong[OF assms subset_refl])

qualified lift_definition pslice :: "'a formula \<Rightarrow> 'a env set \<Rightarrow> 'a prefix \<Rightarrow> 'a prefix" is
  "\<lambda>\<phi> S \<pi>. map (\<lambda>(D, t). (D \<inter> relevant_events \<phi> S, t)) \<pi>"
  by (auto simp: o_def split_beta)

lemma prefix_of_pslice_slice: "prefix_of \<pi> \<sigma> \<Longrightarrow> prefix_of (pslice \<phi> R \<pi>) (slice \<phi> R \<sigma>)"
  unfolding slice_def
  by transfer simp

lemma plen_pslice[simp]: "plen (pslice \<phi> R \<pi>) = plen \<pi>"
  by transfer simp

lemma pslice_pnil[simp]: "pslice \<phi> R pnil = pnil"
  by transfer simp

lemma last_ts_pslice[simp]: "last_ts (pslice \<phi> R \<pi>) = last_ts \<pi>"
  by transfer (simp add: last_map case_prod_beta split: list.split)

lemma prefix_of_replace_prefix:
  "prefix_of (pslice \<phi> R \<pi>) \<sigma> \<Longrightarrow> prefix_of \<pi> (replace_prefix \<pi> \<sigma>)"
proof (transfer; safe; goal_cases)
  case (1 \<phi> R \<pi> \<sigma>)
  then show ?case
    by (subst (asm) (2) stake_sdrop[symmetric, of _ "length \<pi>"])
      (auto 0 3 simp: ssorted_shift split_beta o_def stake_shift sdrop_smap[symmetric]
        ssorted_sdrop not_le pslice_def simp del: sdrop_smap)
qed

lemma slice_replace_prefix:
  "prefix_of (pslice \<phi> R \<pi>) \<sigma> \<Longrightarrow> slice \<phi> R (replace_prefix \<pi> \<sigma>) = slice \<phi> R \<sigma>"
unfolding slice_def proof (transfer; safe; goal_cases)
  case (1 \<phi> R \<pi> \<sigma>)
  then show ?case
    by (subst (asm) (2) stake_sdrop[symmetric, of \<sigma> "length \<pi>"],
        subst (3) stake_sdrop[symmetric, of \<sigma> "length \<pi>"])
      (auto simp: ssorted_shift split_beta o_def stake_shift sdrop_smap[symmetric] ssorted_sdrop
        not_le pslice_def simp del: sdrop_smap cong: map_cong)
qed

lemma prefix_of_psliceD:
  assumes "prefix_of (pslice \<phi> R \<pi>) \<sigma>"
  shows "\<exists>\<sigma>'. prefix_of \<pi> \<sigma>' \<and> prefix_of (pslice \<phi> R \<pi>) (slice \<phi> R \<sigma>')"
proof -
  from assms(1) obtain \<sigma>' where 1: "prefix_of \<pi> \<sigma>'"
    using ex_prefix_of by blast
  then have "prefix_of (pslice \<phi> R \<pi>) (slice \<phi> R \<sigma>')"
    unfolding slice_def
    by transfer simp
  with 1 show ?thesis by blast
qed

lemma prefix_of_sliceD:
  assumes "prefix_of \<pi>' (slice \<phi> R \<sigma>)"
  shows "\<exists>\<pi>''. \<pi>' = pslice \<phi> R \<pi>'' \<and> prefix_of \<pi>'' \<sigma>"
  using assms unfolding slice_def
  by transfer (auto intro!: exI[of _ "stake (length _) _"] elim: sym dest: sorted_stake)


subsection \<open>Translation to n-ary Conjunction\<close>

fun get_or_list :: "'a formula \<Rightarrow> 'a formula list" where
  "get_or_list (Or \<phi> \<psi>) = (get_or_list \<phi>) @ (get_or_list \<psi>)"
| "get_or_list \<phi> = [\<phi>]"

lemma fv_get_or:
  "(\<Union>x\<in>set (get_or_list \<phi>). fvi b x) = fvi b \<phi>"
  by (induction \<phi> rule: get_or_list.induct) simp_all

lemma safe_get_or:
  "safe_formula \<phi> \<Longrightarrow> list_all safe_formula (get_or_list \<phi>)"
  by (induction \<phi> rule: get_or_list.induct) simp_all

lemma sat_get_or:
  "sat \<sigma> v i \<phi> \<longleftrightarrow> list_ex (sat \<sigma> v i) (get_or_list \<phi>)"
  by (induction \<phi> rule: get_or_list.induct) simp_all

fun get_and_list :: "'a formula \<Rightarrow> 'a formula list" where
  "get_and_list (Ands l) = l"
| "get_and_list (Neg \<phi>) = (if safe_formula (Neg \<phi>) then [Neg \<phi>] else map Neg (get_or_list \<phi>))"
| "get_and_list \<phi> = [\<phi>]"

lemma fv_get_and:
  "(\<Union>x\<in>(set (get_and_list \<phi>)). fvi b x) = fvi b \<phi>"
proof (induction \<phi> rule: get_and_list.induct)
  case (2 \<phi>)
  show ?case by (simp add: fv_get_or[where \<phi>=\<phi>])
qed simp_all

lemma safe_get_and:
  "safe_formula \<phi> \<Longrightarrow> list_all safe_neg (get_and_list \<phi>)"
  by (induction \<phi> rule: get_and_list.induct) (simp_all add: safe_neg_def list_all_iff)

lemma sat_get_and:
  "sat \<sigma> v i \<phi> \<longleftrightarrow> list_all (sat \<sigma> v i) (get_and_list \<phi>)"
proof (induction \<phi> rule: get_and_list.induct)
  case (2 \<phi>)
  show ?case by (simp add: list_all_iff sat_get_or[where \<phi>=\<phi>] list_ex_iff)
qed (simp_all add: list_all_iff)

fun convert_multiway :: "'a formula \<Rightarrow> 'a formula"
  where
  "convert_multiway (Neg \<phi>) = (if fv \<phi> = {}
    then Neg \<phi>
    else (case \<phi> of
      Or (Neg \<alpha>) \<beta> \<Rightarrow>
        let a = get_and_list (convert_multiway \<alpha>);
            b = (if is_Neg \<beta> \<and> safe_formula (un_Neg \<beta>)
              then (case \<beta> of Neg \<beta>' \<Rightarrow> get_and_list (convert_multiway \<beta>'))
              else map Neg (get_or_list (convert_multiway \<beta>)))
        in Ands (a @ b)
    | _ \<Rightarrow> Neg \<phi>))"
| "convert_multiway (Or \<phi> \<psi>) = Or (convert_multiway \<phi>) (convert_multiway \<psi>)"
| "convert_multiway (Exists \<phi>) = Exists (convert_multiway \<phi>)"
| "convert_multiway (Agg y \<omega> b f \<phi>) = Agg y \<omega> b f (convert_multiway \<phi>)"
| "convert_multiway (Prev r \<phi> ) = Prev r (convert_multiway \<phi>)"
| "convert_multiway (Next r \<phi>) = Next r (convert_multiway \<phi>)"
| "convert_multiway (Since \<phi> r \<psi>) = (if safe_formula \<phi> then
       Since (convert_multiway \<phi>) r (convert_multiway \<psi>)
  else (case \<phi> of Neg \<phi>' \<Rightarrow> Since (Neg (convert_multiway \<phi>')) r (convert_multiway \<psi>) | _ \<Rightarrow> undefined))"
| "convert_multiway (Until \<phi> r \<psi>) = (if safe_formula \<phi> then
       Until (convert_multiway \<phi>) r (convert_multiway \<psi>)
  else (case \<phi> of Neg \<phi>' \<Rightarrow> Until (Neg (convert_multiway \<phi>')) r (convert_multiway \<psi>) | _ \<Rightarrow> undefined))"
| "convert_multiway (MatchP I r) = MatchP I (Regex.map_regex (\<lambda>\<phi>. if safe_formula \<phi>
    then convert_multiway \<phi>
    else (case \<phi> of Neg \<phi>' \<Rightarrow> Neg (convert_multiway \<phi>'))) r)"
| "convert_multiway (MatchF I r) = MatchF I (Regex.map_regex (\<lambda>\<phi>. if safe_formula \<phi>
    then convert_multiway \<phi>
    else (case \<phi> of Neg \<phi>' \<Rightarrow> Neg (convert_multiway \<phi>'))) r)"
| "convert_multiway \<phi> = \<phi>"

abbreviation "convert_multiway_regex \<equiv> Regex.map_regex (\<lambda>\<phi>. if safe_formula \<phi>
    then convert_multiway \<phi>
    else (case \<phi> of Neg \<phi>' \<Rightarrow> Neg (convert_multiway \<phi>')))"

lemma fv_safe_get_and:
  "safe_formula \<phi> \<Longrightarrow> fv \<phi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list \<phi>))). fv x)"
proof (induction \<phi> rule: get_and_list.induct)
  case (1 l)
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  have "get_and_list (Ands l) = l" by simp
  have sub: "(\<Union>x\<in>set neg. fv x) \<subseteq> (\<Union>x\<in>set pos. fv x)" using "1.prems" posneg by simp
  then have "fv (Ands l) \<subseteq> (\<Union>x\<in>set pos. fv x)"
  proof -
    have "fv (Ands l) = (\<Union>x\<in>set pos. fv x) \<union> (\<Union>x\<in>set neg. fv x)" using posneg by auto
    then show ?thesis using sub by simp
  qed
  then show ?case using posneg by auto
qed auto

lemma ex_safe_get_and:
  "safe_formula \<phi> \<Longrightarrow> list_ex safe_formula (get_and_list \<phi>)"
proof (induction \<phi> rule: get_and_list.induct)
  case (1 l)
  have "get_and_list (Ands l) = l" by simp
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  then have "pos \<noteq> []" using "1.prems" by simp
  then obtain x where "x \<in> set pos" by fastforce
  then show ?case using posneg using Bex_set_list_ex by fastforce
qed simp_all

lemma fv_convert_multiway: "safe_formula \<phi> \<Longrightarrow> fvi b (convert_multiway \<phi>) = fvi b \<phi>"
proof (induction \<phi> arbitrary: b rule: safe_formula.induct)
  case (5 \<phi> \<psi>)
  show ?case proof (cases "is_Neg \<psi> \<and> safe_formula (un_Neg \<psi>)")
    case True
    then obtain \<psi>' where "\<psi> = Neg \<psi>'" by (auto simp: is_Neg_def)
    with True have "safe_formula \<psi>'" by simp
    with 5 show ?thesis
      by (simp add: \<open>\<psi> = Neg \<psi>'\<close> fv_get_and)
  next
    case False
    with "5.prems" have "safe_formula \<psi>" by (simp split: formula.splits)
    with False 5 show ?thesis
      by (auto simp: fv_get_and fv_get_or)
  qed
next
  case (13 \<phi> I \<psi>)
  show ?case proof (cases "safe_formula \<phi>")
    case True
    with 13 show ?thesis by simp
  next
    case False
    with "13.prems" obtain \<phi>' where "\<phi> = Neg \<phi>'" by (simp split: formula.splits)
    with False 13 show ?thesis by simp
  qed
next
  case (14 \<phi> I \<psi>)
  show ?case proof (cases "safe_formula \<phi>")
    case True
    with 14 show ?thesis by simp
  next
    case False
    with "14.prems" obtain \<phi>' where "\<phi> = Neg \<phi>'" by (simp split: formula.splits)
    with False 14 show ?thesis by simp
  qed
next
  case (15 I r)
  then show ?case
    unfolding convert_multiway.simps fvi.simps fv_regex_alt regex.set_map image_image
    by (intro arg_cong[where f=Union, OF image_cong[OF refl]])
      (auto dest!: safe_regex_safe_formula)
next
  case (16 I r)
  then show ?case 
    unfolding convert_multiway.simps fvi.simps fv_regex_alt regex.set_map image_image
    by (intro arg_cong[where f=Union, OF image_cong[OF refl]])
      (auto dest!: safe_regex_safe_formula)
qed auto

lemma get_or_nonempty:
  assumes "safe_formula \<phi>"
  shows "get_or_list \<phi> \<noteq> []"
  using assms by (induction \<phi>) auto

lemma get_and_nonempty:
  assumes "safe_formula \<phi>"
  shows "get_and_list \<phi> \<noteq> []"
  using assms by (induction \<phi>) (auto intro: Suc_leI)

lemma future_reach_get_or:
  "safe_formula \<phi> \<Longrightarrow> Max (future_reach ` (set (get_or_list \<phi>))) = future_reach \<phi>"
proof (induction \<phi>)
  case (Or \<phi> \<psi>)
  then show ?case by (simp add: image_Un Max_Un get_or_nonempty)
qed auto

lemma future_reach_get_and:
  "safe_formula \<phi> \<Longrightarrow> Max (future_reach ` (set (get_and_list \<phi>))) = future_reach \<phi>"
proof (induction \<phi>)
  case (Ands l)
  then have "l \<noteq> []" by auto
  with Ands show ?case by (simp add: foldl_Max)
qed auto

lemma
  fixes \<phi> :: "'a formula"
  shows safe_convert_multiway: "safe_formula \<phi> \<Longrightarrow> safe_formula (convert_multiway \<phi>)"
proof (induction \<phi> rule: safe_formula.induct)
  case (5 \<phi> \<psi>)
  then have "safe_formula \<phi>" by simp
  show ?case proof (cases "fv \<phi> = {} \<and> fv \<psi> = {}")
    case True
    with 5 show ?thesis by simp
  next
    case not_closed: False
    show ?thesis proof (cases "is_Neg \<psi> \<and> safe_formula (un_Neg \<psi>)")
      case True
      then obtain \<psi>' where "\<psi> = Neg \<psi>'" by (auto simp: is_Neg_def)
      with True have "safe_formula \<psi>'" by simp
      let ?a = "And \<phi> \<psi>'"
      let ?b = "convert_multiway ?a"
      let ?c\<phi> = "convert_multiway \<phi>"
      let ?c\<psi> = "convert_multiway \<psi>'"
      have b_def: "?b = Ands (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
        using not_closed True by (simp add: And_def \<open>\<psi> = Neg \<psi>'\<close>)
      have "safe_formula ?b"
      proof -
        let ?l = "get_and_list ?c\<phi> @ get_and_list ?c\<psi>"
        obtain pos neg where posneg: "(pos, neg) = partition safe_formula ?l" by simp
        then have "list_all safe_formula pos" by (auto simp: list_all_iff)
        have lsafe_neg: "list_all safe_neg ?l"
          using "5.IH" \<open>safe_formula \<phi>\<close> \<open>safe_formula \<psi>'\<close> \<open>\<psi> = Neg \<psi>'\<close>
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
            using "5.IH" \<open>safe_formula \<phi>\<close> by (blast intro!: fv_safe_get_and)
          have 2: "fv ?c\<psi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list ?c\<psi>))). fv x)" (is "_ \<subseteq> ?fv\<psi>")
            using "5.IH" \<open>safe_formula \<psi>'\<close> \<open>\<psi> = Neg \<psi>'\<close> by (blast intro!: fv_safe_get_and)
          have "(\<Union>x\<in>set neg. fv x) \<subseteq> fv ?c\<phi> \<union> fv ?c\<psi>" proof -
            have "\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` (set pos \<union> set neg))"
              by simp
            also have "... \<subseteq> fv (convert_multiway \<phi>) \<union> fv (convert_multiway \<psi>')"
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
            using "5.IH" \<open>safe_formula \<phi>\<close> ex_safe_get_and by (auto simp: list_ex_iff)
          then show ?thesis
            unfolding pos_filter by (auto simp: filter_empty_conv)
        qed
        then show ?thesis unfolding b_def
          using \<open>\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` set pos)\<close> \<open>list_all safe_formula (map remove_neg neg)\<close>
            \<open>list_all safe_formula pos\<close> posneg
          by simp
      qed
      then show ?thesis unfolding And_def \<open>\<psi> = Neg \<psi>'\<close> .

    next
      case False
      with "5.prems" have "safe_formula \<psi>" "fv \<psi> \<subseteq> fv \<phi>" by (simp_all split: formula.splits)
      let ?a = "And_Not \<phi> \<psi>"
      let ?b = "convert_multiway ?a"
      let ?c\<phi> = "convert_multiway \<phi>"
      let ?c\<psi> = "convert_multiway \<psi>"
      have b_def: "?b = Ands (get_and_list ?c\<phi> @ map Neg (get_or_list ?c\<psi>))"
        using not_closed False by (auto simp: And_Not_def)
      have fvi_psi:"\<And>b. (\<Union>x\<in>(set (map Neg (get_or_list ?c\<psi>))). fvi b x) = fvi b \<psi>"
      proof -
        fix b
        have "(\<Union>x\<in>(set (get_or_list ?c\<psi>)). fvi b (Neg x)) = fvi b ?c\<psi>" using fv_get_or by auto
        then have "(\<Union>x\<in>(set (map Neg (get_or_list ?c\<psi>))). fvi b x) = fvi b ?c\<psi>" by auto
        then show "(\<Union>x\<in>(set (map Neg (get_or_list ?c\<psi>))). fvi b x) = fvi b \<psi>"
          by (simp add: fv_convert_multiway[OF \<open>safe_formula \<psi>\<close>])
      qed
      have "safe_formula ?b"
      proof -
        let ?l = "(get_and_list ?c\<phi>) @ (map Neg (get_or_list ?c\<psi>))"
        have "safe_formula ?c\<phi>" "safe_formula ?c\<psi>"
          using "5.IH" \<open>safe_formula \<phi>\<close> \<open>safe_formula \<psi>\<close> by blast+
        then have "list_all safe_neg (get_and_list ?c\<phi>)" by (simp add: safe_get_and)
        moreover have "list_all safe_formula (get_or_list ?c\<psi>)"
          by (simp add: \<open>safe_formula (convert_multiway \<psi>)\<close> safe_get_or)
        then have "list_all safe_neg (map Neg (get_or_list ?c\<psi>))" using safe_neg_def
          by (simp add: safe_neg_def list_all_length)
        then have lsafe_neg: "list_all safe_neg ?l" using calculation list_all_append by blast
        obtain pos neg where posneg: "(pos, neg) = partition safe_formula ?l" by simp
        then have "list_all safe_formula pos" by (auto simp: list_all_iff)
        then have "list_all safe_formula (map remove_neg neg)"
        proof -
          have "\<And>x. x \<in> (set neg) \<Longrightarrow> safe_formula (remove_neg x)"
          proof -
            fix x assume "x \<in> set neg"
            then have "\<not> safe_formula x" using posneg by auto
            moreover have "safe_neg x" using lsafe_neg \<open>x \<in> set neg\<close>
              unfolding safe_neg_def list_all_iff partition_set[OF posneg[symmetric], symmetric]
              by simp
            ultimately show "safe_formula (remove_neg x)" using safe_neg_def by blast
          qed
          then show ?thesis using Ball_set_list_all by force
        qed

        have pos_filter: "pos = filter safe_formula (get_and_list ?c\<phi> @ map Neg (get_or_list ?c\<psi>))"
          using posneg by simp
        have neg_filter: "neg = filter (Not \<circ> safe_formula) (get_and_list ?c\<phi> @ map Neg (get_or_list ?c\<psi>))"
          using posneg by simp
        have "(\<Union>x\<in>(set neg). fv x) \<subseteq> (\<Union>x\<in>(set pos). fv x)"
        proof -
          have fv_neg: "(\<Union>x\<in>(set neg). fv x) \<subseteq> (\<Union>x\<in>(set ?l). fv x)" using posneg by auto
          have "(\<Union>x\<in>(set ?l). fv x) \<subseteq> fv ?c\<phi> \<union> fv ?c\<psi>"
            using fvi_psi \<open>safe_formula \<phi>\<close> \<open>safe_formula \<psi>\<close>
            by (simp add: fv_get_and fv_convert_multiway)
          also have "fv ?c\<phi> \<union> fv ?c\<psi> \<subseteq> fv ?c\<phi>"
            using \<open>safe_formula \<phi>\<close> \<open>safe_formula \<psi>\<close> \<open>fv \<psi> \<subseteq> fv \<phi>\<close>
            by (simp add: fv_convert_multiway[symmetric])
          finally have "(\<Union>x\<in>(set neg). fv x) \<subseteq> fv ?c\<phi>"
            using fv_neg unfolding neg_filter by blast
          then show ?thesis
            unfolding pos_filter
            using fv_safe_get_and[OF "5.IH"(1), OF \<open>safe_formula \<phi>\<close>]
            by auto
        qed
        have "pos \<noteq> []"
        proof -
          obtain x where "x \<in> set (get_and_list ?c\<phi>)" "safe_formula x"
            using "5.IH" \<open>safe_formula \<phi>\<close> ex_safe_get_and by (auto simp: list_ex_iff)
          then show ?thesis
            unfolding pos_filter by (auto simp: filter_empty_conv)
        qed
        then show ?thesis unfolding b_def
          using \<open>\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` set pos)\<close> \<open>list_all safe_formula (map remove_neg neg)\<close>
            \<open>list_all safe_formula pos\<close> posneg
          by simp
      qed
      then show ?thesis unfolding And_Not_def .
    qed
  qed
next
  case (13 \<phi> I \<psi>)
  show ?case proof (cases "safe_formula \<phi>")
    case True
    with 13 show ?thesis by (simp add: fv_convert_multiway)
  next
    case False
    with "13.prems" obtain \<phi>' where "\<phi> = Neg \<phi>'" by (simp split: formula.splits)
    with False 13 show ?thesis by (simp add: fv_convert_multiway)
  qed
next
  case (14 \<phi> I \<psi>)
  show ?case proof (cases "safe_formula \<phi>")
    case True
    with 14 show ?thesis by (simp add: fv_convert_multiway)
  next
    case False
    with "14.prems" obtain \<phi>' where "\<phi> = Neg \<phi>'" by (simp split: formula.splits)
    with False 14 show ?thesis by (simp add: fv_convert_multiway)
  qed
next
  case (15 I r)
  then show ?case
    by (auto 0 3 simp: fv_convert_multiway intro!: safe_regex_map_regex
      dest: safe_regex_safe_formula split: if_splits)
next
  case (16 I r)
  then show ?case
    by (auto 0 3 simp: fv_convert_multiway intro!: safe_regex_map_regex
      dest: safe_regex_safe_formula split: if_splits)
qed (auto simp: fv_convert_multiway)

lemma
  fixes \<phi> :: "'a formula"
  shows future_reach_convert_multiway: "safe_formula \<phi> \<Longrightarrow> future_reach (convert_multiway \<phi>) = future_reach \<phi>"
proof (induction \<phi> rule: safe_formula.induct)
  case (5 \<phi> \<psi>)
  then have "safe_formula \<phi>" by simp
  show ?case proof (cases "fv \<phi> = {} \<and> fv \<psi> = {}")
    case True
    with 5 show ?thesis by simp
  next
    case not_closed: False
    show ?thesis proof (cases "is_Neg \<psi> \<and> safe_formula (un_Neg \<psi>)")
      case True
      then obtain \<psi>' where "\<psi> = Neg \<psi>'" by (auto simp: is_Neg_def)
      with True have "safe_formula \<psi>'" by simp
      let ?a = "And \<phi> \<psi>'"
      let ?b = "convert_multiway ?a"
      let ?c\<phi> = "convert_multiway \<phi>"
      let ?c\<psi> = "convert_multiway \<psi>'"
      have b_def: "?b = Ands (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
        using not_closed True by (simp add: And_def \<open>\<psi> = Neg \<psi>'\<close>)
      moreover have "future_reach ?c\<phi> = future_reach \<phi>" using "5.IH"(1)[OF \<open>safe_formula \<phi>\<close>] .
      moreover have "future_reach ?c\<psi> = future_reach \<psi>'" using "5.IH"(3)[OF \<open>\<psi> = Neg \<psi>'\<close> \<open>safe_formula \<psi>'\<close>] .
      ultimately have "future_reach ?a = max (future_reach ?c\<phi>) (future_reach ?c\<psi>)"
        by (simp add: future_reach_And)
      moreover have "future_reach ?c\<phi> = Max (future_reach ` (set (get_and_list ?c\<phi>)))"
        using \<open>safe_formula \<phi>\<close> by (simp add: future_reach_get_and safe_convert_multiway)
      moreover have "future_reach ?c\<psi> = Max (future_reach ` (set (get_and_list ?c\<psi>)))"
        using \<open>safe_formula \<psi>'\<close> by (simp add: future_reach_get_and safe_convert_multiway)
      moreover have "future_reach ?b = Max (future_reach ` (set ((get_and_list ?c\<phi>) @ (get_and_list ?c\<psi>))))"
        unfolding b_def using safe_convert_multiway[OF \<open>safe_formula \<phi>\<close>]
        by (simp add: foldl_Max image_Un get_and_nonempty del: foldl_append)
      moreover have "... = Max ((future_reach ` (set (get_and_list ?c\<phi>))) \<union> (future_reach ` (set (get_and_list ?c\<psi>))))"
        by (simp add: image_Un)
      moreover have "... = max (Max (future_reach ` (set (get_and_list ?c\<phi>)))) (Max (future_reach ` (set (get_and_list ?c\<psi>))))"
      proof -
        have "get_and_list ?c\<phi> \<noteq> []"
          using get_and_nonempty safe_convert_multiway \<open>safe_formula \<phi>\<close> by blast
        moreover have "get_and_list ?c\<psi> \<noteq> []"
          using get_and_nonempty safe_convert_multiway \<open>safe_formula \<psi>'\<close> by blast
        ultimately show ?thesis by (simp add: Max_Un)
      qed
      ultimately show ?thesis unfolding And_def \<open>\<psi> = Neg \<psi>'\<close> by simp

    next
      case False
      with "5.prems" have "safe_formula \<psi>" "fv \<psi> \<subseteq> fv \<phi>" by (simp_all split: formula.splits)
      let ?a = "And_Not \<phi> \<psi>"
      let ?b = "convert_multiway ?a"
      let ?c\<phi> = "convert_multiway \<phi>"
      let ?c\<psi> = "convert_multiway \<psi>"
      have b_def: "?b = Ands (get_and_list ?c\<phi> @ map Neg (get_or_list ?c\<psi>))"
        using not_closed False by (auto simp: And_Not_def)

      moreover have "future_reach ?c\<phi> = future_reach \<phi>" using "5.IH"(1)[OF \<open>safe_formula \<phi>\<close>] .
      moreover have "future_reach ?c\<psi> = future_reach \<psi>" using "5.IH"(2)[OF \<open>safe_formula \<psi>\<close>] .
      ultimately have "future_reach ?a = max (future_reach ?c\<phi>) (future_reach ?c\<psi>)"
        by (simp add: future_reach_And_Not)
      moreover have "future_reach ?c\<phi> = Max (future_reach ` (set (get_and_list ?c\<phi>)))"
        using \<open>safe_formula \<phi>\<close> by (simp add: future_reach_get_and safe_convert_multiway)
      moreover have "future_reach ?c\<psi> = Max (future_reach ` (set (get_or_list ?c\<psi>)))"
        using \<open>safe_formula \<psi>\<close> by (simp add: future_reach_get_or safe_convert_multiway)
      moreover have "future_reach ?b = Max (future_reach ` (set ((get_and_list ?c\<phi>) @ (map Neg (get_or_list ?c\<psi>)))))"
        unfolding b_def using safe_convert_multiway[OF \<open>safe_formula \<phi>\<close>]
        by (simp add: foldl_Max image_Un get_and_nonempty get_or_nonempty image_image del: foldl_append)
      moreover have "... = Max ((future_reach ` (set (get_and_list ?c\<phi>))) \<union> (future_reach ` (set (map Neg (get_or_list ?c\<psi>)))))"
        by (simp add: image_Un)
      moreover have "... = max (Max (future_reach ` (set (get_and_list ?c\<phi>)))) (Max (future_reach ` (set (get_or_list ?c\<psi>))))"
      proof -
        have "get_and_list ?c\<phi> \<noteq> []"
          using get_and_nonempty safe_convert_multiway \<open>safe_formula \<phi>\<close> by blast
        moreover have "get_or_list ?c\<psi> \<noteq> []"
          using get_or_nonempty safe_convert_multiway \<open>safe_formula \<psi>\<close> by blast
        ultimately show ?thesis  by (simp add: Max_Un image_image)
      qed
      ultimately show ?thesis unfolding And_Not_def by simp
    qed
  qed
next
  case (13 \<phi> I \<psi>)
  show ?case proof (cases "safe_formula \<phi>")
    case True
    with 13 show ?thesis by simp
  next
    case False
    with "13.prems" obtain \<phi>' where "\<phi> = Neg \<phi>'" by (simp split: formula.splits)
    with False 13 show ?thesis by simp
  qed
next
  case (14 \<phi> I \<psi>)
  show ?case proof (cases "safe_formula \<phi>")
    case True
    with 14 show ?thesis by simp
  next
    case False
    with "14.prems" obtain \<phi>' where "\<phi> = Neg \<phi>'" by (simp split: formula.splits)
    with False 14 show ?thesis by simp
  qed
next
  case (15 I r)
  then show ?case
    by (auto 0 3 intro!: max_regex_cong arg_cong2[where f="(-)"] dest: safe_regex_safe_formula)
next
  case (16 I r)
  then show ?case
    by (auto 0 3 intro!: max_regex_cong arg_cong2[where f="(+)"] dest: safe_regex_safe_formula)
qed auto

lemma
  fixes \<phi> :: "'a formula"
  shows sat_convert_multiway: "safe_formula \<phi> \<Longrightarrow> sat \<sigma> v i (convert_multiway \<phi>) \<longleftrightarrow> sat \<sigma> v i \<phi>"
proof (induction \<phi> arbitrary: v i rule: safe_formula.induct)
  case (5 \<phi> \<psi>)
  then have "safe_formula \<phi>" by simp
  show ?case proof (cases "fv \<phi> = {} \<and> fv \<psi> = {}")
    case True
    with 5 show ?thesis by simp
  next
    case not_closed: False
    let ?a = "Neg (Or (Neg \<phi>) \<psi>)"
    let ?b = "convert_multiway ?a"
    let ?la = "get_and_list (convert_multiway \<phi>)"
    let ?sat = "sat \<sigma> v i"
    show ?thesis proof (cases "is_Neg \<psi> \<and> safe_formula (un_Neg \<psi>)")
      case True
      then obtain \<psi>' where "\<psi> = Neg \<psi>'" by (auto simp: is_Neg_def)
      with True have "safe_formula \<psi>'" by simp
      let ?lb = "get_and_list (convert_multiway \<psi>')"
      have b_def: "?b = Ands (?la @ ?lb)" using not_closed True \<open>\<psi> = Neg \<psi>'\<close> by simp
      moreover have "?sat (convert_multiway \<phi>) \<longleftrightarrow> ?sat \<phi>"
        using "5.IH"(1)[OF \<open>safe_formula \<phi>\<close>] .
      then have "list_all ?sat ?la \<longleftrightarrow> ?sat \<phi>" using sat_get_and by blast
      moreover have "?sat (convert_multiway \<psi>') \<longleftrightarrow> ?sat \<psi>'"
        using "5.IH"(3)[OF \<open>\<psi> = Neg \<psi>'\<close> \<open>safe_formula \<psi>'\<close>] .
      then have "list_all ?sat ?lb \<longleftrightarrow> ?sat \<psi>'" using sat_get_and by blast
      ultimately show ?thesis
        unfolding \<open>\<psi> = Neg \<psi>'\<close> by (auto simp: list_all_iff)
    next
      case False
      with "5.prems" have "safe_formula \<psi>" "fv \<psi> \<subseteq> fv \<phi>" by (simp_all split: formula.splits)
      let ?lb = "map Neg (get_or_list (convert_multiway \<psi>))"
      have b_def: "?b = Ands (?la @ ?lb)" using not_closed False by auto
      moreover have "?sat (convert_multiway \<phi>) \<longleftrightarrow> ?sat \<phi>"
        using "5.IH"(1)[OF \<open>safe_formula \<phi>\<close>] .
      then have "list_all ?sat ?la \<longleftrightarrow> ?sat \<phi>" using sat_get_and by blast
      moreover have "list_all ?sat ?lb \<longleftrightarrow> list_all (\<lambda>\<psi>. \<not> ?sat \<psi>) (get_or_list (convert_multiway \<psi>))"
        by (simp add: list_all_length)
      moreover have "?sat \<psi> \<longleftrightarrow> ?sat (convert_multiway \<psi>)"
        using "5.IH"(2)[OF \<open>safe_formula \<psi>\<close>] ..
      moreover have "?sat (convert_multiway \<psi>) \<longleftrightarrow> list_ex ?sat (get_or_list (convert_multiway \<psi>))"
        by (simp add: sat_get_or)
      moreover have "list_all (\<lambda>\<psi>. \<not> ?sat \<psi>) (get_or_list (convert_multiway \<psi>)) \<longleftrightarrow> \<not> (list_ex ?sat (get_or_list (convert_multiway \<psi>)))"
        by (simp add: list_all_iff list_ex_iff)
      ultimately show ?thesis by (auto simp: list_all_iff)
    qed
  qed
next
  case (10 y \<omega> b f \<phi>)
  then show ?case
    by (simp add: fv_env_def nfv_def fv_convert_multiway cong: conj_cong)
next
  case (13 \<phi> I \<psi>)
  show ?case proof (cases "safe_formula \<phi>")
    case True
    with 13 show ?thesis by simp
  next
    case False
    with "13.prems" obtain \<phi>' where "\<phi> = Neg \<phi>'" by (simp split: formula.splits)
    with False 13 show ?thesis by simp
  qed
next
  case (14 \<phi> I \<psi>)
  show ?case proof (cases "safe_formula \<phi>")
    case True
    with 14 show ?thesis by simp
  next
    case False
    with "14.prems" obtain \<phi>' where "\<phi> = Neg \<phi>'" by (simp split: formula.splits)
    with False 14 show ?thesis by simp
  qed
next
  case (15 I r)
  then have "Regex.match (sat \<sigma> v) (convert_multiway_regex r) = Regex.match (sat \<sigma> v) r"
    unfolding match_map_regex
    by (intro Regex.match_fv_cong) (auto dest!: safe_regex_safe_formula)
  then show ?case
    by auto
next
  case (16 I r)
  then have "Regex.match (sat \<sigma> v) (convert_multiway_regex r) = Regex.match (sat \<sigma> v) r"
    unfolding match_map_regex
    by (intro Regex.match_fv_cong) (auto dest!: safe_regex_safe_formula)
  then show ?case
    by auto
qed (auto cong: nat.case_cong)

end (*context*)

lemma Neg_splits:
  "P (case \<phi> of formula.Neg \<psi> \<Rightarrow> f \<psi> | \<phi> \<Rightarrow> g \<phi>) =
   ((\<forall>\<psi>. \<phi> = formula.Neg \<psi> \<longrightarrow> P (f \<psi>)) \<and> ((\<not> Formula.is_Neg \<phi>) \<longrightarrow> P (g \<phi>)))"
  "P (case \<phi> of formula.Neg \<psi> \<Rightarrow> f \<psi> | _ \<Rightarrow> g \<phi>) =
   (\<not> ((\<exists>\<psi>. \<phi> = formula.Neg \<psi> \<and> \<not> P (f \<psi>)) \<or> ((\<not> Formula.is_Neg \<phi>) \<and> \<not> P (g \<phi>))))"
  by (cases \<phi>; auto simp: Formula.is_Neg_def)+

(*<*)
end
(*>*)
