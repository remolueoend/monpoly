(*<*)
theory Slicing
  imports Abstract_Monitor MFOTL
begin
(*>*)

section \<open>Section 4.2\<close>

subsection \<open>Definition 1\<close>

text \<open>Corresponds to locale @{locale monitor} defined in theory @{theory "Draft.Abstract_Monitor"}.\<close>

subsection \<open>Definition 2\<close>

locale slicer = monitor +
  fixes submonitor :: "'k :: finite \<Rightarrow> 'a prefix \<Rightarrow> (nat \<times> 'b option list) set"
  and   splitter :: "'a prefix \<Rightarrow> 'k \<Rightarrow> 'a prefix"
  and   joiner :: "('k \<Rightarrow> (nat \<times> 'b option list) set) \<Rightarrow> (nat \<times> 'b option list) set"
assumes mono_splitter: "\<pi> \<le> \<pi>' \<Longrightarrow> splitter \<pi> k \<le> splitter \<pi>' k"
  and   correct_slicer: "joiner (\<lambda>k. submonitor k (splitter \<pi> k)) = M \<pi>"
begin

lemmas sound_slicer = equalityD1[OF correct_slicer]
lemmas complete_slicer = equalityD2[OF correct_slicer]

end

locale self_slicer = slicer where M = M and submonitor = "\<lambda>_. M" for M

subsection \<open>Definition 3\<close>

locale event_separable_splitter =
  fixes event_splitter :: "'a MFOTL.formula \<Rightarrow> 'a MFOTL.event \<Rightarrow> 'k :: finite set"
begin

lift_definition splitter :: "'a MFOTL.formula \<Rightarrow> 'a MFOTL.prefix \<Rightarrow> 'k \<Rightarrow> 'a MFOTL.prefix" is
  "\<lambda>\<phi> \<pi> k. map (\<lambda>(D, t). ({e \<in> D. k \<in> event_splitter \<phi> e}, t)) \<pi>"
  by (auto simp: o_def split_beta)

subsection \<open>Lemma 1\<close>

lemma mono_splitter: "\<pi> \<le> \<pi>' \<Longrightarrow> splitter \<phi> \<pi> k \<le> splitter \<phi> \<pi>' k"
  by transfer auto

end

section \<open>Section 4.3\<close>

abbreviation (input) "ok \<phi> v \<equiv> wf_tuple (MFOTL.nfv \<phi>) (MFOTL.fv \<phi>) v"

locale splitting_strategy =
  fixes strategy :: "'a MFOTL.formula \<Rightarrow> 'a option list \<Rightarrow> 'k :: finite set"
  assumes strategy_nonempty: "monitorable \<phi> \<Longrightarrow> wf_tuple (MFOTL.nfv \<phi>) (MFOTL.fv \<phi>) v \<Longrightarrow> strategy \<phi> v \<noteq> {}"
begin

abbreviation slice_set where
  "slice_set \<phi> k \<equiv> {v. \<exists>v'. map the v' = v \<and> ok \<phi> v' \<and> k \<in> strategy \<phi> v'}"

end

subsection \<open>Definition 4\<close>

locale joint_data_slicer = monitor "MFOTL.nfv \<phi>" "MFOTL.fv \<phi>" "M \<phi>" + splitting_strategy strategy
  for monitorable ::and strategy :: "'a MFOTL.formula \<Rightarrow> _"
begin

definition event_splitter where
  "event_splitter \<phi> e = (\<Union>(strategy \<phi> ` {v. ok \<phi> v \<and> MFOTL.matches (map the v) \<phi> e}))"

sublocale event_separable_splitter where event_splitter = event_splitter .

definition joiner where
  "joiner \<phi> = (\<lambda>s. \<Union>k. s k \<inter> (UNIV :: nat set) \<times> {v. k \<in> strategy \<phi> v})"

lemma splitter_pslice: "splitter \<phi> \<pi> k = MFOTL.pslice \<phi> (slice_set \<phi> k) \<pi>"
  by transfer (auto simp: event_splitter_def)

subsection \<open>Lemma 2\<close>

text \<open>Corresponds to the following theorem @{thm[source] sat_slice_strong} proved in theory
   @{theory "MFOTL_Monitor.Abstract_Monitor"}:

   @{thm sat_slice_strong[no_vars]}\<close>

subsection \<open>Theorem 1\<close>

sublocale joint_monitor: monitor monitorable "\<lambda>\<phi> \<pi>. joiner \<phi> (\<lambda>k. M \<phi> (splitter \<phi> \<pi> k))"
proof (standard, goal_cases mono sound complete)
  case (mono \<phi> \<pi> \<pi>')
  show ?case
    using mono_monitor[OF _ mono_splitter, OF mono]
    by (auto simp: joiner_def)
next
  case (sound \<phi> i v \<pi>)
  then obtain k where in_M: "(i, v) \<in> M \<phi> (splitter \<phi> \<pi> k)"  and k: "k \<in> strategy \<phi> v"
    unfolding joiner_def by (auto split: if_splits)
  have len: "i < plen (splitter \<phi> \<pi> k)" and wf: "wf_tuple (MFOTL.nfv \<phi>) (MFOTL.fv \<phi>) v" and
    sat: "\<And>\<sigma>. prefix_of (splitter \<phi> \<pi> k) \<sigma> \<Longrightarrow> MFOTL.sat \<sigma> (map the v) i \<phi>"
    using sound_monitor[OF sound(1) in_M] by auto
  from len have "i < plen \<pi>"
    by transfer auto
  moreover have "MFOTL.sat \<sigma> (map the v) i \<phi>" if "prefix_of \<pi> \<sigma>" for \<sigma>
    using that wf k
    by (intro iffD2[OF sat_slice_iff[of "map the v" "slice_set \<phi> k" \<sigma> i \<phi>]])
      (auto simp: wf_tuple_def fvi_less_nfv splitter_pslice intro!: exI[of _ v] prefix_of_pslice_slice sat)
  ultimately show ?case using wf by blast
next
  case (complete \<phi> \<pi> \<sigma> i v)
  with strategy_nonempty obtain k where k: "k \<in> strategy \<phi> v" by blast
  have "MFOTL.sat \<sigma>' (map the v) i \<phi>" if "prefix_of (MFOTL.pslice \<phi> (slice_set \<phi> k) \<pi>) \<sigma>'" for \<sigma>'
  proof -
    have "MFOTL.sat \<sigma>' (map the v) i \<phi> = MFOTL.sat (MFOTL.slice \<phi> (slice_set \<phi> k) \<sigma>') (map the v) i \<phi>"
      using complete(4) k by (auto intro!: sat_slice_iff)
    also have "\<dots> = MFOTL.sat (MFOTL.slice \<phi> (slice_set \<phi> k) (replace_prefix \<pi> \<sigma>')) (map the v) i \<phi>"
      using that complete k by (subst slice_replace_prefix[symmetric]; simp)
    also have "\<dots> = MFOTL.sat (replace_prefix \<pi> \<sigma>') (map the v) i \<phi>"
      using complete(4) k by (auto intro!: sat_slice_iff[symmetric])
    also have "\<dots>"
      by (rule complete(5)[rule_format], rule prefix_of_replace_prefix[OF that])
    finally show ?thesis .
  qed
  with complete(1-4) obtain \<pi>' where \<pi>':
    "prefix_of \<pi>' (MFOTL.slice \<phi> (slice_set \<phi> k) \<sigma>)"" (i, v) \<in> M \<phi> \<pi>'"
    by (atomize_elim, intro complete_monitor[where \<pi>="MFOTL.pslice \<phi> (slice_set \<phi> k) \<pi>"])
      (auto simp: splitter_pslice intro!: prefix_of_pslice_slice)
  from \<pi>'(1) obtain \<pi>'' where "\<pi>' = MFOTL.pslice \<phi> (slice_set \<phi> k) \<pi>''" "prefix_of \<pi>'' \<sigma>"
    by (atomize_elim, rule prefix_of_sliceD)
  with \<pi>' k show ?case
    by (intro exI[of _ \<pi>'']) (auto simp: joiner_def splitter_pslice intro!: exI[of _ k])
qed

subsection \<open>Corollary 1\<close>

sublocale joint_slicer: slicer
  monitorable "\<lambda>\<phi> \<pi>. joiner \<phi> (\<lambda>k. M \<phi> (splitter \<phi> \<pi> k))" "\<lambda>\<phi> _. M \<phi>" splitter joiner
  by standard (auto simp: mono_splitter)

end

subsection \<open>Definition 5\<close>

text \<open>Corresponds to locale @{locale slicable_monitor} defined in theory @{theory "MFOTL_Monitor.Abstract_Monitor"}.\<close>

locale slicable_joint_data_slicer = slicable_monitor + joint_data_slicer
begin

lemma monitor_split: "ok \<phi> v \<Longrightarrow> k \<in> strategy \<phi> v \<Longrightarrow> (i, v) \<in> M \<phi> (splitter \<phi> \<pi> k) \<longleftrightarrow> (i, v) \<in> M \<phi> \<pi>"
  unfolding splitter_pslice
  by (rule monitor_slice)
    (auto simp: wf_tuple_def fvi_less_nfv intro!: mem_restrI[rotated 2, where y="map the v"])

subsection \<open>Theorem 2\<close>

sublocale self_slicer monitorable M splitter joiner
proof (standard, erule mono_splitter, safe, goal_cases sound complete)
  case (sound \<phi> \<pi> i v)
  have "ok \<phi> v" using joint_monitor.sound_monitor[OF sound] by auto
  from sound(2) obtain k where "(i, v) \<in> M \<phi> (splitter \<phi> \<pi> k)" "k \<in> strategy \<phi> v"
    unfolding joiner_def by blast
  with \<open>ok \<phi> v\<close> show ?case by (simp add: monitor_split)
next
  case (complete \<phi> \<pi> i v)
  have "ok \<phi> v" using sound_monitor[OF complete] by auto
  with complete strategy_nonempty obtain k where k: "k \<in> strategy \<phi> v" by blast
  then have "(i, v) \<in> M \<phi> (splitter \<phi> \<pi> k)" using complete \<open>ok \<phi> v\<close> by (simp add: monitor_split)
  with k show ?case unfolding joiner_def by blast
qed

end

section \<open>Towards Theorem 3\<close>

(*TODO(JS): Clean up*)
fun names :: "'a MFOTL.formula \<Rightarrow> MFOTL.name set" where
  "names (MFOTL.Pred e _) = {e}"
| "names (MFOTL.Eq _ _) = {}"
| "names (MFOTL.Neg \<psi>) = names \<psi>"
| "names (MFOTL.Or \<alpha> \<beta>) = names \<alpha> \<union> names \<beta>"
| "names (MFOTL.Exists \<psi>) = names \<psi>"
| "names (MFOTL.Prev I \<psi>) = names \<psi>"
| "names (MFOTL.Next I \<psi>) = names \<psi>"
| "names (MFOTL.Since \<alpha> I \<beta>) = names \<alpha> \<union> names \<beta>"
| "names (MFOTL.Until \<alpha> I \<beta>) = names \<alpha> \<union> names \<beta>"

fun gen_unique :: "'a MFOTL.formula \<Rightarrow> bool" where
  "gen_unique (MFOTL.Pred _ _) = True"
| "gen_unique (MFOTL.Eq (MFOTL.Var _) (MFOTL.Const _)) = False"
| "gen_unique (MFOTL.Eq (MFOTL.Const _) (MFOTL.Var _)) = False"
| "gen_unique (MFOTL.Eq _ _) = True"
| "gen_unique (MFOTL.Neg \<psi>) = gen_unique \<psi>"
| "gen_unique (MFOTL.Or \<alpha> \<beta>) = (gen_unique \<alpha> \<and> gen_unique \<beta> \<and> names \<alpha> \<inter> names \<beta> = {})"
| "gen_unique (MFOTL.Exists \<psi>) = gen_unique \<psi>"
| "gen_unique (MFOTL.Prev I \<psi>) = gen_unique \<psi>"
| "gen_unique (MFOTL.Next I \<psi>) = gen_unique \<psi>"
| "gen_unique (MFOTL.Since \<alpha> I \<beta>) = (gen_unique \<alpha> \<and> gen_unique \<beta> \<and> names \<alpha> \<inter> names \<beta> = {})"
| "gen_unique (MFOTL.Until \<alpha> I \<beta>) = (gen_unique \<alpha> \<and> gen_unique \<beta> \<and> names \<alpha> \<inter> names \<beta> = {})"

lemma sat_inter_names_cong: "(\<And>e. e \<in> names \<phi> \<Longrightarrow> {xs. (e, xs) \<in> E} = {xs. (e, xs) \<in> F}) \<Longrightarrow>
  MFOTL.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) v i \<phi> \<longleftrightarrow> MFOTL.sat (map_\<Gamma> (\<lambda>D. D \<inter> F) \<sigma>) v i \<phi>"
  by (induction \<phi> arbitrary: v i) (auto split: nat.splits)

lemma matches_in_names: "MFOTL.matches v \<phi> x \<Longrightarrow> fst x \<in> names \<phi>"
  by (induction \<phi> arbitrary: v) (auto)

lemma unique_names_matches_absorb: "fst x \<in> names \<alpha> \<Longrightarrow> names \<alpha> \<inter> names \<beta> = {} \<Longrightarrow>
    MFOTL.matches v \<alpha> x \<or> MFOTL.matches v \<beta> x \<longleftrightarrow> MFOTL.matches v \<alpha> x"
  "fst x \<in> names \<beta> \<Longrightarrow> names \<alpha> \<inter> names \<beta> = {} \<Longrightarrow>
    MFOTL.matches v \<alpha> x \<or> MFOTL.matches v \<beta> x \<longleftrightarrow> MFOTL.matches v \<beta> x"
  by (auto dest: matches_in_names)

definition mergeable_envs where
  "mergeable_envs n S \<longleftrightarrow> (\<forall>v1\<in>S. \<forall>v2\<in>S. (\<forall>A B f.
    (\<forall>x\<in>A. x < n \<and> v1 ! x = f x) \<and> (\<forall>x\<in>B. x < n \<and> v2 ! x = f x) \<longrightarrow>
    (\<exists>v\<in>S. \<forall>x\<in>A \<union> B. v ! x = f x)))"

lemma mergeable_envsI:
  assumes "\<And>v1 v2 v. v1 \<in> S \<Longrightarrow> v2 \<in> S \<Longrightarrow> length v = n \<Longrightarrow> \<forall>x < n. v ! x = v1 ! x \<or> v ! x = v2 ! x \<Longrightarrow> v \<in> S"
  shows "mergeable_envs n S"
  unfolding mergeable_envs_def
proof (safe, goal_cases mergeable)
  case [simp]: (mergeable v1 v2 A B f)
  let ?v = "tabulate (\<lambda>x. if x \<in> A \<union> B then f x else v1 ! x) 0 n"
  from assms[of v1 v2 ?v, simplified] show ?case
    by (auto intro!: bexI[of _ ?v])
qed

lemma in_listset_nth: "x \<in> listset As \<Longrightarrow> i < length As \<Longrightarrow> x ! i \<in> As ! i"
  by (induction As arbitrary: x i) (auto simp: set_Cons_def nth_Cons split: nat.split)

lemma all_nth_in_listset: "length x = length As \<Longrightarrow> (\<And>i. i < length As \<Longrightarrow> x ! i \<in> As ! i) \<Longrightarrow> x \<in> listset As"
  by (induction x As rule: list_induct2) (fastforce simp: set_Cons_def nth_Cons)+

lemma mergeable_envs_listset: "mergeable_envs (length As) (listset As)"
  by (rule mergeable_envsI) (auto intro!: all_nth_in_listset elim!: in_listset_nth)

lemma mergeable_envs_Ex: "mergeable_envs n S \<Longrightarrow> MFOTL.nfv \<alpha> \<le> n \<Longrightarrow> MFOTL.nfv \<beta> \<le> n \<Longrightarrow>
  (\<exists>v'\<in>S. \<forall>x\<in>fv \<alpha>. v' ! x = v ! x) \<Longrightarrow> (\<exists>v'\<in>S. \<forall>x\<in>fv \<beta>. v' ! x = v ! x) \<Longrightarrow>
  (\<exists>v'\<in>S. \<forall>x\<in>fv \<alpha> \<union> fv \<beta>. v' ! x = v ! x)"
proof (clarify, goal_cases mergeable)
  case (mergeable v1 v2)
  then show ?case
    by (auto intro: order.strict_trans2[OF fvi_less_nfv[rule_format]]
      elim!: mergeable_envs_def[THEN iffD1, rule_format, of _ _ v1 v2])
qed

lemma in_set_ConsE: "xs \<in> set_Cons A As \<Longrightarrow> (\<And>y ys. xs = y # ys \<Longrightarrow> y \<in> A \<Longrightarrow> ys \<in> As \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding set_Cons_def by blast

lemma mergeable_envs_set_Cons: "mergeable_envs n S \<Longrightarrow> mergeable_envs (Suc n) (set_Cons UNIV S)"
  unfolding mergeable_envs_def
proof (clarify, elim in_set_ConsE, goal_cases mergeable)
  case (mergeable v1 v2 A B f y1 ys1 y2 ys2)
  let ?A = "(\<lambda>x. x - 1) ` (A - {0})"
  let ?B = "(\<lambda>x. x - 1) ` (B - {0})"
  from mergeable(4-9) have "\<exists>v \<in> S. \<forall>x\<in>?A \<union> ?B. v ! x = f (Suc x)"
    by (auto dest!: mergeable(2,3)[rule_format] intro!: mergeable(1)[rule_format, of ys1 ys2])
  then obtain v where "v \<in> S" "\<forall>x\<in>?A \<union> ?B. v ! x = f (Suc x)" by blast
  then show ?case
    by (intro bexI[of _ "f 0 # v"]) (auto simp: nth_Cons' set_Cons_def)
qed

lemma slice_Exists: "MFOTL.slice (MFOTL.Exists \<phi>) S \<sigma> = MFOTL.slice \<phi> (set_Cons UNIV S) \<sigma>"
  unfolding MFOTL.slice_def by (auto simp: set_Cons_def intro: map_\<Gamma>_cong)

lemma image_Suc_fvi: "Suc ` MFOTL.fvi (Suc b) \<phi> = MFOTL.fvi b \<phi> - {0}"
  by (auto simp: image_def Bex_def MFOTL.fvi_Suc dest: gr0_implies_Suc)

lemma nfv_Exists: "MFOTL.nfv (MFOTL.Exists \<phi>) = MFOTL.nfv \<phi> - 1"
  unfolding MFOTL.nfv_def
  by (cases "fv \<phi> = {}") (auto simp add: image_Suc_fvi mono_Max_commute[symmetric] mono_def)

lemma set_Cons_empty_iff[simp]: "set_Cons A Xs = {} \<longleftrightarrow> A = {} \<or> Xs = {}"
  unfolding set_Cons_def by auto

lemma unique_sat_slice_mem: "safe_formula \<phi> \<Longrightarrow> gen_unique \<phi> \<Longrightarrow> S \<noteq> {} \<Longrightarrow>
  mergeable_envs n S \<Longrightarrow> MFOTL.nfv \<phi> \<le> n \<Longrightarrow>
  MFOTL.sat (MFOTL.slice \<phi> S \<sigma>) v i \<phi> \<Longrightarrow> \<exists>v'\<in>S. \<forall>x\<in>fv \<phi>. v' ! x = v ! x"
proof (induction arbitrary: v i S n rule: safe_formula_induct)
  case (1 t1 t2)
  then show ?case by (cases "t2") (auto simp: MFOTL.is_Const_def)
next
  case (2 t1 t2)
  then show ?case by (cases "t1") (auto simp: MFOTL.is_Const_def)
next
  case (3 x y)
  then show ?case by auto
next
  case (4 x y)
  then show ?case by simp
next
  case (5 e ts)
  then obtain v' where "v' \<in> S" and eq: "\<forall>t\<in>set ts. MFOTL.eval_trm v' t = MFOTL.eval_trm v t"
    by (auto simp: MFOTL.slice_def)
  have "\<forall>t\<in>set ts. \<forall>x\<in>fv_trm t. v' ! x = v ! x" proof
    fix t assume "t \<in> set ts"
    with eq have "MFOTL.eval_trm v' t = MFOTL.eval_trm v t" ..
    then show "\<forall>x\<in>fv_trm t. v' ! x = v ! x" by (cases t) (simp_all)
  qed
  with \<open>v' \<in> S\<close> show ?case by auto
next
  case (6 \<phi> \<psi>)
  from \<open>gen_unique (MFOTL.And \<phi> \<psi>)\<close>
  have *:
    "MFOTL.sat (MFOTL.slice (MFOTL.And \<phi> \<psi>) S \<sigma>) v i \<phi> = MFOTL.sat (MFOTL.slice \<phi> S \<sigma>) v i \<phi>"
    "MFOTL.sat (MFOTL.slice (MFOTL.And \<phi> \<psi>) S \<sigma>) v i \<psi> = MFOTL.sat (MFOTL.slice \<psi> S \<sigma>) v i \<psi>"
    unfolding MFOTL.slice_def MFOTL.And_def
    by (fastforce simp: unique_names_matches_absorb intro!: sat_inter_names_cong)+
  from 6(1,4-) 6(2,3)[where S=S] show ?case
    unfolding MFOTL.And_def
    by (auto simp: *[unfolded MFOTL.And_def] intro!: mergeable_envs_Ex)
next
  case (7 \<phi> \<psi>)
  from \<open>gen_unique (MFOTL.And_Not \<phi> \<psi>)\<close>
  have *:
    "MFOTL.sat (MFOTL.slice (MFOTL.And_Not \<phi> \<psi>) S \<sigma>) v i \<phi> = MFOTL.sat (MFOTL.slice \<phi> S \<sigma>) v i \<phi>"
    unfolding MFOTL.slice_def MFOTL.And_Not_def
    by (fastforce simp: unique_names_matches_absorb intro!: sat_inter_names_cong)
  from 7(1,2,5-) 7(3)[where S=S] have "\<exists>v'\<in>S. \<forall>x\<in>fv \<phi>. v' ! x = v ! x"
    unfolding MFOTL.And_Not_def
    by (auto simp: *[unfolded MFOTL.And_Not_def])
  with \<open>fv \<psi> \<subseteq> fv \<phi>\<close> show ?case by (auto simp: MFOTL.fvi_And_Not)
next
  case (8 \<phi> \<psi>)
  from \<open>gen_unique (MFOTL.Or \<phi> \<psi>)\<close>
  have *:
    "MFOTL.sat (MFOTL.slice (MFOTL.Or \<phi> \<psi>) S \<sigma>) v i \<phi> = MFOTL.sat (MFOTL.slice \<phi> S \<sigma>) v i \<phi>"
    "MFOTL.sat (MFOTL.slice (MFOTL.Or \<phi> \<psi>) S \<sigma>) v i \<psi> = MFOTL.sat (MFOTL.slice \<psi> S \<sigma>) v i \<psi>"
    unfolding MFOTL.slice_def
    by (fastforce simp: unique_names_matches_absorb intro!: sat_inter_names_cong)+
  from 8(1,4-) 8(2,3)[where S=S] have "\<exists>v'\<in>S. \<forall>x\<in>fv \<phi>. v' ! x = v ! x"
    by (auto simp: * \<open>fv \<psi> = fv \<phi>\<close>)
  then show ?case by (auto simp: \<open>fv \<psi> = fv \<phi>\<close>)
next
  case (9 \<phi>)
  then obtain z where sat_\<phi>: "MFOTL.sat (MFOTL.slice (MFOTL.Exists \<phi>) S \<sigma>) (z # v) i \<phi>"
    by auto
  from "9.prems" sat_\<phi> have "\<exists>v'\<in>set_Cons UNIV S. \<forall>x\<in>fv \<phi>. v' ! x = (z # v) ! x"
    by (intro "9.IH") (auto simp: nfv_Exists slice_Exists intro!: mergeable_envs_set_Cons)
  then show ?case
    by (auto simp: set_Cons_def fvi_Suc Ball_def nth_Cons split: nat.splits)
next
  case (10 I \<phi>)
  then obtain j where "MFOTL.sat (MFOTL.slice \<phi> S \<sigma>) v j \<phi>"
    by (auto simp: MFOTL.slice_def split: nat.splits)
  with 10 show ?case by simp
next
  case (11 I \<phi>)
  then obtain j where "MFOTL.sat (MFOTL.slice \<phi> S \<sigma>) v j \<phi>"
    by (auto simp: MFOTL.slice_def split: nat.splits)
  with 11 show ?case by simp
next
  case (12 \<phi> I \<psi>)
  from \<open>gen_unique (MFOTL.Since \<phi> I \<psi>)\<close>
  have *:
    "MFOTL.sat (MFOTL.slice (MFOTL.Since \<phi> I \<psi>) S \<sigma>) v j \<psi> = MFOTL.sat (MFOTL.slice \<psi> S \<sigma>) v j \<psi>" for j
    unfolding MFOTL.slice_def
    by (fastforce simp: unique_names_matches_absorb intro!: sat_inter_names_cong)
  from 12 obtain j where "MFOTL.sat (MFOTL.slice (MFOTL.Since \<phi> I \<psi>) S \<sigma>) v j \<psi>"
    by auto
  with 12 have "\<exists>v'\<in>S. \<forall>x\<in>fv \<psi>. v' ! x = v ! x" by (auto simp: *)
  with \<open>fv \<phi> \<subseteq> fv \<psi>\<close> show ?case by auto
next
  case (13 \<phi> I \<psi>)
  from \<open>gen_unique (MFOTL.Since (MFOTL.Neg \<phi>) I \<psi>)\<close>
  have *:
    "MFOTL.sat (MFOTL.slice (MFOTL.Since (MFOTL.Neg \<phi>) I \<psi>) S \<sigma>) v j \<psi> = MFOTL.sat (MFOTL.slice \<psi> S \<sigma>) v j \<psi>" for j
    unfolding MFOTL.slice_def
    by (fastforce simp: unique_names_matches_absorb intro!: sat_inter_names_cong)
  from 13 obtain j where "MFOTL.sat (MFOTL.slice (MFOTL.Since (MFOTL.Neg \<phi>) I \<psi>) S \<sigma>) v j \<psi>"
    by auto
  with 13 have "\<exists>v'\<in>S. \<forall>x\<in>fv \<psi>. v' ! x = v ! x" by (auto simp: *)
  with \<open>fv (MFOTL.Neg \<phi>) \<subseteq> fv \<psi>\<close> show ?case by auto
next
  case (14 \<phi> I \<psi>)
  from \<open>gen_unique (MFOTL.Until \<phi> I \<psi>)\<close>
  have *:
    "MFOTL.sat (MFOTL.slice (MFOTL.Until \<phi> I \<psi>) S \<sigma>) v j \<psi> = MFOTL.sat (MFOTL.slice \<psi> S \<sigma>) v j \<psi>" for j
    unfolding MFOTL.slice_def
    by (fastforce simp: unique_names_matches_absorb intro!: sat_inter_names_cong)
  from 14 obtain j where "MFOTL.sat (MFOTL.slice (MFOTL.Until \<phi> I \<psi>) S \<sigma>) v j \<psi>"
    by auto
  with 14 have "\<exists>v'\<in>S. \<forall>x\<in>fv \<psi>. v' ! x = v ! x" by (auto simp: *)
  with \<open>fv \<phi> \<subseteq> fv \<psi>\<close> show ?case by auto
next
  case (15 \<phi> I \<psi>)
  from \<open>gen_unique (MFOTL.Until (MFOTL.Neg \<phi>) I \<psi>)\<close>
  have *:
    "MFOTL.sat (MFOTL.slice (MFOTL.Until (MFOTL.Neg \<phi>) I \<psi>) S \<sigma>) v j \<psi> = MFOTL.sat (MFOTL.slice \<psi> S \<sigma>) v j \<psi>" for j
    unfolding MFOTL.slice_def
    by (fastforce simp: unique_names_matches_absorb intro!: sat_inter_names_cong)
  from 15 obtain j where "MFOTL.sat (MFOTL.slice (MFOTL.Until (MFOTL.Neg \<phi>) I \<psi>) S \<sigma>) v j \<psi>"
    by auto
  with 15 have "\<exists>v'\<in>S. \<forall>x\<in>fv \<psi>. v' ! x = v ! x" by (auto simp: *)
  with \<open>fv (MFOTL.Neg \<phi>) \<subseteq> fv \<psi>\<close> show ?case by auto
qed

lemma unique_sat_slice:
  assumes formula: "safe_formula \<phi>" "gen_unique \<phi>"
      and restr: "S \<noteq> {}" "mergeable_envs (MFOTL.nfv \<phi>) S"
      and sat_slice: "MFOTL.sat (MFOTL.slice \<phi> S \<sigma>) v i \<phi>"
    shows "MFOTL.sat \<sigma> v i \<phi>"
proof -
  obtain v' where "v' \<in> S" and fv_eq: "\<forall>x\<in>fv \<phi>. v' ! x = v ! x"
    using unique_sat_slice_mem[OF formula restr order_refl sat_slice] ..
  with sat_slice have "MFOTL.sat (MFOTL.slice \<phi> S \<sigma>) v' i \<phi>"
    by (auto iff: sat_fvi_cong)
  then have "MFOTL.sat \<sigma> v' i \<phi>"
    unfolding sat_slice_iff[OF \<open>v' \<in> S\<close>, symmetric] .
  with fv_eq show ?thesis by (auto iff: sat_fvi_cong)
qed

subsection \<open>Lemma 3\<close>

lemma (in splitting_strategy) unique_sat_strategy:
  "safe_formula \<phi> \<Longrightarrow> gen_unique \<phi> \<Longrightarrow> slice_set \<phi> k \<noteq> {} \<Longrightarrow>
  mergeable_envs (MFOTL.nfv \<phi>) (slice_set \<phi> k) \<Longrightarrow>
  MFOTL.sat (MFOTL.slice \<phi> (slice_set \<phi> k) \<sigma>) (map the v) i \<phi> \<Longrightarrow>
  ok \<phi> v \<Longrightarrow> k \<in> strategy \<phi> v"
  by (drule (3) unique_sat_slice_mem) (auto dest: wf_tuple_cong)

locale skip_inter = joint_data_slicer +
  assumes nonempty: "slice_set \<phi> k \<noteq> {}"
  and mergeable: "mergeable_envs (MFOTL.nfv \<phi>) (slice_set \<phi> k)"
begin

subsection \<open>Definition of J'\<close>

definition "skip_joiner = (\<lambda>s. \<Union>k. s k)"

subsection \<open>Theorem 3\<close>

lemma skip_joiner:
  assumes "monitorable \<phi>" "safe_formula \<phi>" "gen_unique \<phi>"
  shows "joiner \<phi> (\<lambda>k. M \<phi> (splitter \<phi> \<pi> k)) = skip_joiner (\<lambda>k. M \<phi> (splitter \<phi> \<pi> k))"
  (is "?L = ?R")
proof safe
  fix i v
  assume "(i, v) \<in> ?R"
  then obtain k where in_M: "(i, v) \<in> M \<phi> (splitter \<phi> \<pi> k)"
  unfolding skip_joiner_def by blast
  from ex_prefix_of obtain \<sigma> where "prefix_of \<pi> \<sigma>" by blast
  with sound_monitor[OF assms(1) in_M] have
    "MFOTL.sat (MFOTL.slice \<phi> (slice_set \<phi> k) \<sigma>) (map the v) i \<phi>" "ok \<phi> v"
    by (auto simp: splitter_pslice intro!: prefix_of_pslice_slice)
  note unique_sat_strategy[OF assms(2,3) nonempty mergeable this]
  with in_M show "(i, v) \<in> ?L" unfolding joiner_def by blast
qed (auto simp: joiner_def skip_joiner_def)

sublocale skip_joint_monitor: monitor monitorable
  "\<lambda>\<phi> \<pi>. (if safe_formula \<phi> \<and> gen_unique \<phi> then skip_joiner else joiner \<phi>) (\<lambda>k. M \<phi> (splitter \<phi> \<pi> k))"
  using joint_monitor.mono_monitor joint_monitor.sound_monitor joint_monitor.complete_monitor
  by unfold_locales (auto simp: skip_joiner[symmetric] split: if_splits)

end

(*<*)
end
(*>*)