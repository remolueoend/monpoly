(*<*)
theory Formula
  imports Interval Trace Table "HOL-Library.Lattice_Syntax"
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
  | Neg "'a formula" | Or "'a formula" "'a formula" | Exists "'a formula"
  | Prev \<I> "'a formula" | Next \<I> "'a formula"
  | Since "'a formula" \<I> "'a formula" | Until "'a formula" \<I> "'a formula"
  | MatchF \<I> "'a regex" | MatchP \<I> "'a regex"
and 'a regex = Wild | Test "'a formula"
| Plus "'a regex" "'a regex" | Times "'a regex" "'a regex"  | Star "'a regex"

qualified primrec fvi :: "nat \<Rightarrow> 'a formula \<Rightarrow> nat set" and fvi_regex where
  "fvi b (Pred r ts) = (\<Union>t\<in>set ts. fvi_trm b t)"
| "fvi b (Eq t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (Neg \<phi>) = fvi b \<phi>"
| "fvi b (Or \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Exists \<phi>) = fvi (Suc b) \<phi>"
| "fvi b (Prev I \<phi>) = fvi b \<phi>"
| "fvi b (Next I \<phi>) = fvi b \<phi>"
| "fvi b (Since \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Until \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (MatchF I r) = fvi_regex b r"
| "fvi b (MatchP I r) = fvi_regex b r"
| "fvi_regex b Wild = {}"
| "fvi_regex b (Test \<phi>) = fvi b \<phi>"
| "fvi_regex b (Plus r s) = fvi_regex b r \<union> fvi_regex b s"
| "fvi_regex b (Times r s) = fvi_regex b r \<union> fvi_regex b s"
| "fvi_regex b (Star r) = fvi_regex b r"

abbreviation "fv \<equiv> fvi 0"
abbreviation "fv_regex \<equiv> fvi_regex 0"

lemma finite_fvi_trm[simp]: "finite (fvi_trm b t)"
  by (cases t) simp_all

lemma finite_fvi[simp]:
  fixes \<phi> :: "'a formula" and r :: "'a regex"
  shows "finite (fvi b \<phi>)" "finite (fvi_regex b r)"
  by (induction \<phi> and r arbitrary: b and b rule: formula.induct regex.induct) simp_all

lemma fvi_trm_Suc: "x \<in> fvi_trm (Suc b) t \<longleftrightarrow> Suc x \<in> fvi_trm b t"
  by (cases t) auto

lemma fvi_Suc:
  fixes \<phi> :: "'a formula" and r :: "'a regex"
  shows "x \<in> fvi (Suc b) \<phi> \<longleftrightarrow> Suc x \<in> fvi b \<phi>" "x \<in> fvi_regex (Suc b) r \<longleftrightarrow> Suc x \<in> fvi_regex b r"
  by (induction \<phi> and r arbitrary: b and b rule: formula.induct regex.induct) (simp_all add: fvi_trm_Suc)

lemma fvi_Suc_bound:
  assumes "\<forall>i\<in>fvi (Suc b) \<phi>. i < n"
  shows "\<forall>i\<in>fvi b \<phi>. i < Suc n"
proof
  fix i
  assume "i \<in> fvi b \<phi>"
  with assms show "i < Suc n" by (cases i) (simp_all add: fvi_Suc)
qed

lemma fvi_regex_Suc_bound:
  assumes "\<forall>i\<in>fvi_regex (Suc b) \<phi>. i < n"
  shows "\<forall>i\<in>fvi_regex b \<phi>. i < Suc n"
proof
  fix i
  assume "i \<in> fvi_regex b \<phi>"
  with assms show "i < Suc n" by (cases i) (simp_all add: fvi_Suc)
qed

qualified definition nfv :: "'a formula \<Rightarrow> nat" where
  "nfv \<phi> = Max (insert 0 (Suc ` fv \<phi>))"

qualified definition nfv_regex :: "'a regex \<Rightarrow> nat" where
  "nfv_regex r = Max (insert 0 (Suc ` fv_regex r))"

qualified definition envs :: "'a formula \<Rightarrow> 'a env set" where
  "envs \<phi> = {v. length v = nfv \<phi>}"

lemma nfv_simps[simp]:
  "nfv (Neg \<phi>) = nfv \<phi>"
  "nfv (Or \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Prev I \<phi>) = nfv \<phi>"
  "nfv (Next I \<phi>) = nfv \<phi>"
  "nfv (Since \<phi> I \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Until \<phi> I \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (MatchP I r) = nfv_regex r"
  "nfv (MatchF I r) = nfv_regex r"
  "nfv_regex Wild = 0"
  "nfv_regex (Test \<phi>) = nfv \<phi>"
  "nfv_regex (Plus r s) = max (nfv_regex r) (nfv_regex s)"
  "nfv_regex (Times r s) = max (nfv_regex r) (nfv_regex s)"
  "nfv_regex (Star r) = nfv_regex r"
  unfolding nfv_def nfv_regex_def by (simp_all add: image_Un Max_Un[symmetric])

lemma fvi_less_nfv: "\<forall>i\<in>fv \<phi>. i < nfv \<phi>"
  unfolding nfv_def
  by (auto simp add: Max_gr_iff intro: max.strict_coboundedI2)

lemma fvi_less_nfv_regex: "\<forall>i\<in>fv_regex \<phi>. i < nfv_regex \<phi>"
  unfolding nfv_regex_def
  by (auto simp add: Max_gr_iff intro: max.strict_coboundedI2)


qualified primrec future_reach :: "'a formula \<Rightarrow> enat" and future_reach_regex :: "'a regex \<Rightarrow> enat" where
  "future_reach (Pred _ _) = 0"
| "future_reach (Eq _ _) = 0"
| "future_reach (Neg \<phi>) = future_reach \<phi>"
| "future_reach (Or \<phi> \<psi>) = max (future_reach \<phi>) (future_reach \<psi>)"
| "future_reach (Exists \<phi>) = future_reach \<phi>"
| "future_reach (Prev I \<phi>) = future_reach \<phi> - left I"
| "future_reach (Next I \<phi>) = future_reach \<phi> + right I + 1"
| "future_reach (Since \<phi> I \<psi>) = max (future_reach \<phi>) (future_reach \<psi> - left I)"
| "future_reach (Until \<phi> I \<psi>) = max (future_reach \<phi>) (future_reach \<psi>) + right I + 1"
| "future_reach (MatchP I r) = future_reach_regex r - left I"
| "future_reach (MatchF I r) = future_reach_regex r + right I + 1"
| "future_reach_regex Wild = 1"
| "future_reach_regex (Test \<phi>) = future_reach \<phi>"
| "future_reach_regex (Plus r s) = max (future_reach_regex r) (future_reach_regex s)"
| "future_reach_regex (Times r s) = max (future_reach_regex r) (future_reach_regex s)"
| "future_reach_regex (Star r) = future_reach_regex r"


qualified primrec sat :: "'a trace \<Rightarrow> 'a env \<Rightarrow> nat \<Rightarrow> 'a formula \<Rightarrow> bool"
              and match :: "'a trace \<Rightarrow> 'a env \<Rightarrow> 'a regex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"where
  "sat \<sigma> v i (Pred r ts) = ((r, map (eval_trm v) ts) \<in> \<Gamma> \<sigma> i)"
| "sat \<sigma> v i (Eq t1 t2) = (eval_trm v t1 = eval_trm v t2)"
| "sat \<sigma> v i (Neg \<phi>) = (\<not> sat \<sigma> v i \<phi>)"
| "sat \<sigma> v i (Or \<phi> \<psi>) = (sat \<sigma> v i \<phi> \<or> sat \<sigma> v i \<psi>)"
| "sat \<sigma> v i (Exists \<phi>) = (\<exists>z. sat \<sigma> (z # v) i \<phi>)"
| "sat \<sigma> v i (Prev I \<phi>) = (case i of 0 \<Rightarrow> False | Suc j \<Rightarrow> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> sat \<sigma> v j \<phi>)"
| "sat \<sigma> v i (Next I \<phi>) = (mem (\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i) I \<and> sat \<sigma> v (Suc i) \<phi>)"
| "sat \<sigma> v i (Since \<phi> I \<psi>) = (\<exists>j\<le>i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> sat \<sigma> v j \<psi> \<and> (\<forall>k \<in> {j <.. i}. sat \<sigma> v k \<phi>))"
| "sat \<sigma> v i (Until \<phi> I \<psi>) = (\<exists>j\<ge>i. mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> sat \<sigma> v j \<psi> \<and> (\<forall>k \<in> {i ..< j}. sat \<sigma> v k \<phi>))"
| "sat \<sigma> v i (MatchP I r) = (\<exists>j\<le>i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> match \<sigma> v r j i)"
| "sat \<sigma> v i (MatchF I r) = (\<exists>j\<ge>i. mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> match \<sigma> v r i j)"
| "match \<sigma> v Wild = (\<lambda>i j. j = i + 1)"
| "match \<sigma> v (Test \<phi>) = (\<lambda>i j. i = j \<and> sat \<sigma> v i \<phi>)"
| "match \<sigma> v (Plus r s) = match \<sigma> v r \<squnion> match \<sigma> v s"
| "match \<sigma> v (Times r s) = match \<sigma> v r OO match \<sigma> v s"
| "match \<sigma> v (Star r) = (match \<sigma> v r)\<^sup>*\<^sup>*"

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

lemmas regex_induct[case_names Wild Test Plus Times Star, induct type: regex] =
  regex.induct[of "\<lambda>_. True", simplified]

qualified primrec eps where 
  "eps \<sigma> v i Wild = False"
| "eps \<sigma> v i (Test \<phi>) = sat \<sigma> v i \<phi>"
| "eps \<sigma> v i (Plus r s) = (eps \<sigma> v i r \<or> eps \<sigma> v i s)"
| "eps \<sigma> v i (Times r s) = (eps \<sigma> v i r \<and> eps \<sigma> v i s)"
| "eps \<sigma> v i (Star r) = True"

qualified definition "TimesL r S = Times r ` S"
qualified definition "TimesR R s = (\<lambda>r. Times r s) ` R"
qualified definition "FF = Exists (Neg (Eq (Var 0) (Var 0)))"
qualified definition "TT \<equiv> Neg FF"

lemma sat_abbrevs[simp]:
  "sat \<sigma> v i TT" "\<not> sat \<sigma> v i FF"
  unfolding TT_def FF_def by auto

lemma fv_abbrevs[simp]: "fv TT = {}" "fv FF = {}"
  unfolding TT_def FF_def by auto

qualified primrec lpd where 
  "lpd \<sigma> v i Wild = {Test TT}"
| "lpd \<sigma> v i (Test \<phi>) = {}"
| "lpd \<sigma> v i (Plus r s) = (lpd \<sigma> v i r \<union> lpd \<sigma> v i s)"
| "lpd \<sigma> v i (Times r s) = TimesR (lpd \<sigma> v i r) s \<union> (if eps \<sigma> v i r then (lpd \<sigma> v i s) else {})"
| "lpd \<sigma> v i (Star r) = TimesR (lpd \<sigma> v i r) (Star r)"

qualified primrec lpd\<kappa> where 
  "lpd\<kappa> \<kappa> \<sigma> v i Wild = {\<kappa> (Test TT)}"
| "lpd\<kappa> \<kappa> \<sigma> v i (Test \<phi>) = {}"
| "lpd\<kappa> \<kappa> \<sigma> v i (Plus r s) = lpd\<kappa> \<kappa> \<sigma> v i r \<union> lpd\<kappa> \<kappa> \<sigma> v i s"
| "lpd\<kappa> \<kappa> \<sigma> v i (Times r s) = lpd\<kappa> (\<lambda>t. \<kappa> (Times t s)) \<sigma> v i r \<union> (if eps \<sigma> v i r then lpd\<kappa> \<kappa> \<sigma> v i s else {})"
| "lpd\<kappa> \<kappa> \<sigma> v i (Star r) = lpd\<kappa> (\<lambda>t. \<kappa> (Times t (Star r))) \<sigma> v i r"

qualified primrec rpd where 
  "rpd \<sigma> v i Wild = {Test TT}"
| "rpd \<sigma> v i (Test \<phi>) = {}"
| "rpd \<sigma> v i (Plus r s) = (rpd \<sigma> v i r \<union> rpd \<sigma> v i s)"
| "rpd \<sigma> v i (Times r s) = TimesL r (rpd \<sigma> v i s) \<union> (if eps \<sigma> v i s then rpd \<sigma> v i r else {})"
| "rpd \<sigma> v i (Star r) = TimesL (Star r) (rpd \<sigma> v i r)"

qualified primrec rpd\<kappa> where 
  "rpd\<kappa> \<kappa> \<sigma> v i Wild = {\<kappa> (Test TT)}"
| "rpd\<kappa> \<kappa> \<sigma> v i (Test \<phi>) = {}"
| "rpd\<kappa> \<kappa> \<sigma> v i (Plus r s) = rpd\<kappa> \<kappa> \<sigma> v i r \<union> rpd\<kappa> \<kappa> \<sigma> v i s"
| "rpd\<kappa> \<kappa> \<sigma> v i (Times r s) = rpd\<kappa> (\<lambda>t. \<kappa> (Times r t)) \<sigma> v i s \<union> (if eps \<sigma> v i s then rpd\<kappa> \<kappa> \<sigma> v i r else {})"
| "rpd\<kappa> \<kappa> \<sigma> v i (Star r) = rpd\<kappa> (\<lambda>t. \<kappa> (Times (Star r) t)) \<sigma> v i r"

lemma lpd\<kappa>_lpd: "lpd\<kappa> \<kappa> \<sigma> v i r = \<kappa> ` lpd \<sigma> v i r"
  by (induct r arbitrary: \<kappa>) (auto simp: TimesR_def)

lemma rpd\<kappa>_rpd: "rpd\<kappa> \<kappa> \<sigma> v i r = \<kappa> ` rpd \<sigma> v i r"
  by (induct r arbitrary: \<kappa>) (auto simp: TimesL_def)

lemma match_le: "match \<sigma> v r i j \<Longrightarrow> i \<le> j"
proof (induction r arbitrary: i j v)
  case (Times r s)
  then show ?case using order.trans by fastforce
next
  case (Star r)
  from Star.prems show ?case
    unfolding match.simps by (induct i j rule: rtranclp.induct) (force dest: Star.IH)+
qed auto

lemma eps_match: "eps \<sigma> v i r \<longleftrightarrow> match \<sigma> v r i i"
  by (induction r) (auto dest: antisym[OF match_le match_le])

lemma lpd_match: "i < j \<Longrightarrow> match \<sigma> v r i j \<longleftrightarrow> (\<Squnion>s \<in> lpd \<sigma> v i r. match \<sigma> v s) (i + 1) j"
proof (induction r arbitrary: i j)
  case (Times r s)
  have "match \<sigma> v (Times r s) i j \<longleftrightarrow> (\<exists>k. match \<sigma> v r i k \<and> match \<sigma> v s k j)"
    by auto
  also have "\<dots> \<longleftrightarrow> match \<sigma> v r i i \<and> match \<sigma> v s i j \<or>
    (\<exists>k>i. match \<sigma> v r i k \<and> match \<sigma> v s k j)"
    using match_le[of \<sigma> v r i] nat_less_le by auto
  also have "\<dots> \<longleftrightarrow> match \<sigma> v r i i \<and> (\<Squnion>t \<in> lpd \<sigma> v i s. match \<sigma> v t) (i + 1) j \<or>
    (\<exists>k>i. (\<Squnion>t \<in> lpd \<sigma> v i r. match \<sigma> v t) (i + 1) k \<and> match \<sigma> v s k j)"
    using Times.IH(1) Times.IH(2)[OF Times.prems] by metis
  also have "\<dots> \<longleftrightarrow> match \<sigma> v r i i \<and> (\<Squnion>t \<in> lpd \<sigma> v i s. match \<sigma> v t) (i + 1) j \<or>
    (\<exists>k. (\<Squnion>t \<in> lpd \<sigma> v i r. match \<sigma> v t) (i + 1) k \<and> match \<sigma> v s k j)"
    using Times.prems by (intro disj_cong[OF refl] iff_exI) (auto dest: match_le)
  also have "\<dots> \<longleftrightarrow> SUPREMUM (lpd \<sigma> v i (Times r s)) (match \<sigma> v) (i + 1) j"
    by (force simp: TimesL_def TimesR_def eps_match)
  finally show ?case .
next
  case (Star r)
  have "\<exists>s\<in>lpd \<sigma> v i r. (match \<sigma> v s OO (match \<sigma> v r)\<^sup>*\<^sup>*) (i + 1) j" if "(match \<sigma> v r)\<^sup>*\<^sup>* i j"
    using that Star.prems match_le[of \<sigma> v _ "i + 1"]
  proof (induct rule: converse_rtranclp_induct)
    case (step i k)
    then show ?case 
      by (cases "i < k") (auto simp: not_less Star.IH dest: match_le)
  qed simp
  with Star.prems show ?case using match_le[of \<sigma> v _  "i + 1"]
    by (auto simp: TimesL_def TimesR_def Suc_le_eq Star.IH[of i]
      elim!: converse_rtranclp_into_rtranclp[rotated])
qed auto

lemma rpd_match: "i < j \<Longrightarrow> match \<sigma> v r i j \<longleftrightarrow> (\<Squnion>s \<in> rpd \<sigma> v j r. match \<sigma> v s) i (j - 1)"
proof (induction r arbitrary: i j)
  case (Times r s)
  have "match \<sigma> v (Times r s) i j \<longleftrightarrow> (\<exists>k. match \<sigma> v r i k \<and> match \<sigma> v s k j)"
    by auto
  also have "\<dots> \<longleftrightarrow> match \<sigma> v r i j \<and> match \<sigma> v s j j \<or>
    (\<exists>k<j. match \<sigma> v r i k \<and> match \<sigma> v s k j)"
    using match_le[of \<sigma> v s _ j] nat_less_le by auto
  also have "\<dots> \<longleftrightarrow> (\<Squnion>t \<in> rpd \<sigma> v j r. match \<sigma> v t) i (j - 1) \<and> match \<sigma> v s j j  \<or>
    (\<exists>k<j. match \<sigma> v r i k \<and> (\<Squnion>t \<in> rpd \<sigma> v j s. match \<sigma> v t) k (j - 1))"
    using Times.IH(1)[OF Times.prems] Times.IH(2) by metis
  also have "\<dots> \<longleftrightarrow> (\<Squnion>t \<in> rpd \<sigma> v j r. match \<sigma> v t) i (j - 1) \<and> match \<sigma> v s j j  \<or>
    (\<exists>k. match \<sigma> v r i k \<and> (\<Squnion>t \<in> rpd \<sigma> v j s. match \<sigma> v t) k (j - 1))"
    using Times.prems by (intro disj_cong[OF refl] iff_exI) (auto dest: match_le)
  also have "\<dots> \<longleftrightarrow> SUPREMUM (rpd \<sigma> v j (Times r s)) (match \<sigma> v) i (j - 1)"
    by (force simp: TimesL_def TimesR_def eps_match)
  finally show ?case .
next
  case (Star r)
  have "\<exists>s\<in>rpd \<sigma> v j r. ((match \<sigma> v r)\<^sup>*\<^sup>* OO match \<sigma> v s) i (j - 1)" if "(match \<sigma> v r)\<^sup>*\<^sup>* i j"
    using that Star.prems match_le[of \<sigma> v _ _ "j - 1"]
  proof (induct rule: rtranclp_induct)
    case (step k j)
    then show ?case
      by (cases "k < j") (auto simp: not_less Star.IH dest: match_le)
  qed simp
  with Star.prems show ?case
    by (auto 0 3 simp: TimesL_def TimesR_def intro: Star.IH[of _ j, THEN iffD2]
      elim!: rtranclp.rtrancl_into_rtrancl dest: match_le[of \<sigma> v _ _ "j - 1", unfolded One_nat_def])
qed auto

lemma lpd_fv_regex: "s \<in> lpd \<sigma> v i r \<Longrightarrow> fv_regex s \<subseteq> fv_regex r"
  by (induct r arbitrary: s) (force simp: TimesR_def TimesL_def split: if_splits)+

lemma rpd_fv_regex: "s \<in> rpd \<sigma> v i r \<Longrightarrow> fv_regex s \<subseteq> fv_regex r"
  by (induct r arbitrary: s) (force simp: TimesR_def TimesL_def split: if_splits)+

lemma sat_MatchF_rec: "sat \<sigma> v i (MatchF I r) \<longleftrightarrow> mem 0 I \<and> eps \<sigma> v i r \<or>
  \<Delta> \<sigma> (i + 1) \<le> right I \<and> (\<exists>s \<in> lpd \<sigma> v i r. sat \<sigma> v (i + 1) (MatchF (subtract (\<Delta> \<sigma> (i + 1)) I) s))"
  (is "?L \<longleftrightarrow> ?R1 \<or> ?R2")
proof (rule iffI; (elim disjE conjE bexE)?)
  assume ?L
  then obtain j where j: "j \<ge> i" "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I" and"match \<sigma> v r i j" by auto
  then show "?R1 \<or> ?R2"
  proof (cases "i < j")
    case True
    with \<open>match \<sigma> v r i j\<close> lpd_match[of i j \<sigma> v r]
    obtain s where "s \<in> lpd \<sigma> v i r" "match \<sigma> v s (i + 1) j" by auto
    with True j have ?R2
      by (cases "right I")
        (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j] elim: le_trans[rotated])
    then show ?thesis by blast
  qed (auto simp: eps_match)
next
  assume "enat (\<Delta> \<sigma> (i + 1)) \<le> right I"
  moreover
  fix s
  assume [simp]: "s \<in> lpd \<sigma> v i r" and "sat \<sigma> v (i + 1) (MatchF (subtract (\<Delta> \<sigma> (i + 1)) I) s)"
  then obtain j where "j > i" "match \<sigma> v s (i + 1) j"
    "mem (\<tau> \<sigma> j - \<tau> \<sigma> (Suc i)) (subtract (\<Delta> \<sigma> (i + 1)) I)" by (auto simp: Suc_le_eq)
  ultimately show ?L
    by (cases "right I")
      (auto simp: le_diff_conv lpd_match intro!: exI[of _ j] bexI[of _ s])
qed (auto simp: eps_match intro!: exI[of _ i])

lemma sat_MatchP_rec: "sat \<sigma> v i (MatchP I r) \<longleftrightarrow> mem 0 I \<and> eps \<sigma> v i r \<or>
  i > 0 \<and> \<Delta> \<sigma> i \<le> right I \<and> (\<exists>s \<in> rpd \<sigma> v i r. sat \<sigma> v (i - 1) (MatchP (subtract (\<Delta> \<sigma> i) I) s))"
  (is "?L \<longleftrightarrow> ?R1 \<or> ?R2")
proof (rule iffI; (elim disjE conjE bexE)?)
  assume ?L
  then obtain j where j: "j \<le> i" "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I" and "match \<sigma> v r j i" by auto
  then show "?R1 \<or> ?R2"
  proof (cases "j < i")
    case True
    with \<open>match \<sigma> v r j i\<close> rpd_match[of j i \<sigma> v r]
    obtain s where "s \<in> rpd \<sigma> v i r" "match \<sigma> v s j (i - 1)" by auto
    with True j have ?R2
      by (cases "right I")
        (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j] elim: le_trans)
    then show ?thesis by blast
  qed (auto simp: eps_match)
next
  assume "enat (\<Delta> \<sigma> i) \<le> right I"
  moreover
  fix s
  assume [simp]: "s \<in> rpd \<sigma> v i r" and "sat \<sigma> v (i - 1) (MatchP (subtract (\<Delta> \<sigma> i) I) s)" "i > 0"
  then obtain j where "j < i" "match \<sigma> v s j (i - 1)"
    "mem (\<tau> \<sigma> (i - 1) - \<tau> \<sigma> j) (subtract (\<Delta> \<sigma> i) I)" by (auto simp: gr0_conv_Suc less_Suc_eq_le)
  ultimately show ?L
    by (cases "right I")
      (auto simp: le_diff_conv rpd_match intro!: exI[of _ j] bexI[of _ s])
qed (auto simp: eps_match intro!: exI[of _ i])

lemma sat_Since_0: "sat \<sigma> v 0 (Since \<phi> I \<psi>) \<longleftrightarrow> mem 0 I \<and> sat \<sigma> v 0 \<psi>"
  by auto

lemma sat_MatchP_0: "sat \<sigma> v 0 (MatchP I r) \<longleftrightarrow> mem 0 I \<and> eps \<sigma> v 0 r"
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
  and match_fv_cong: "\<forall>x\<in>fv_regex r. v!x = v'!x \<Longrightarrow> match \<sigma> v r = match \<sigma> v' r"
proof (induct \<phi> and r arbitrary: v v' i and v v' rule: formula.induct regex.induct)
  case (Pred n ts)
  show ?case by (simp cong: map_cong eval_trm_fv_cong[OF Pred[simplified, THEN bspec]])
next
  case (Eq x1 x2)
  then show ?case  unfolding fvi.simps sat.simps by (metis UnCI eval_trm_fv_cong)
next
  case (Exists \<phi>)
  then show ?case unfolding sat.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
next
  case (Star r)
  then show ?case by (auto intro!: arg_cong[of _ _ rtranclp])
qed (auto 8 0 simp add: nth_Cons' fun_eq_iff relcompp_apply split: nat.splits intro!: iff_exI)

lemma eps_fv_cong:
  "\<forall>x\<in>fv_regex r. v!x = v'!x \<Longrightarrow> eps \<sigma> v i r = eps \<sigma> v' i r"
  unfolding eps_match by (erule match_fv_cong[THEN fun_cong, THEN fun_cong])

subsection \<open>Defined Connectives\<close>

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

datatype modality = Past | Future
datatype safety = Safe | Unsafe

fun safe_formula :: "'a formula \<Rightarrow> bool"
and safe_regex :: "modality \<Rightarrow> safety \<Rightarrow> 'a regex \<Rightarrow> bool" where
  "safe_formula (Eq t1 t2) = (is_Const t1 \<or> is_Const t2)"
| "safe_formula (Neg (Eq (Const x) (Const y))) = True"
| "safe_formula (Neg (Eq (Var x) (Var y))) = (x = y)"
| "safe_formula (Pred e ts) = True"
| "safe_formula (Neg (Or (Neg \<phi>) \<psi>)) = (safe_formula \<phi> \<and>
    (safe_formula \<psi> \<and> fv \<psi> \<subseteq> fv \<phi> \<or> (case \<psi> of Neg \<psi>' \<Rightarrow> safe_formula \<psi>' | _ \<Rightarrow> False)))"
| "safe_formula (Neg \<phi>) = (fv \<phi> = {} \<and> safe_formula \<phi>)"
| "safe_formula (Or \<phi> \<psi>) = (fv \<psi> = fv \<phi> \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
| "safe_formula (Exists \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Prev I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Next I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Since \<phi> I \<psi>) = (fv \<phi> \<subseteq> fv \<psi> \<and>
    (safe_formula \<phi> \<or> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)) \<and> safe_formula \<psi>)"
| "safe_formula (Until \<phi> I \<psi>) = (fv \<phi> \<subseteq> fv \<psi> \<and>
    (safe_formula \<phi> \<or> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)) \<and> safe_formula \<psi>)"
| "safe_formula (MatchP I r) = (safe_regex Past Safe r)"
| "safe_formula (MatchF I r) = (safe_regex Future Safe r)"
| "safe_regex m _ Wild = True"
| "safe_regex m g (Test \<phi>) = (safe_formula \<phi> \<or>
     (g = Unsafe \<and> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)))"
| "safe_regex m g (Plus r s) = ((g = Unsafe \<or> fv_regex r = fv_regex s) \<and> safe_regex m g r \<and> safe_regex m g s)"
| "safe_regex Future g (Times r s) =
    ((g = Unsafe \<or> fv_regex r \<subseteq> fv_regex s) \<and> safe_regex Future g s \<and> safe_regex Future Unsafe r)"
| "safe_regex Past g (Times r s) =
    ((g = Unsafe \<or> fv_regex s \<subseteq> fv_regex r) \<and> safe_regex Past g r \<and> safe_regex Past Unsafe s)"
| "safe_regex m g (Star r) = (g = Unsafe \<and> safe_regex m g r)"

lemma safe_abbrevs[simp]: "safe_formula TT" "safe_formula FF"
  unfolding TT_def FF_def by auto

lemma safe_cosafe: "safe_regex m Safe r \<Longrightarrow> safe_regex m Unsafe r"
  by (induct r; cases m) auto

lemma safe_lpd_fv_regex_le: "safe_regex Future Safe r \<Longrightarrow> s \<in> lpd \<sigma> v i r \<Longrightarrow> fv_regex r \<subseteq> fv_regex s"
  by (induct r) (auto simp: TimesR_def split: if_splits)

lemma safe_lpd_fv_regex: "safe_regex Future Safe r \<Longrightarrow> s \<in> lpd \<sigma> v i r \<Longrightarrow> fv_regex s = fv_regex r"
  by (simp add: eq_iff lpd_fv_regex safe_lpd_fv_regex_le)

lemma cosafe_lpd: "safe_regex Future Unsafe r \<Longrightarrow> s \<in> lpd \<sigma> v i r \<Longrightarrow> safe_regex Future Unsafe s"
proof (induct r arbitrary: s)
  case (Plus r1 r2)
  from Plus(3,4) show ?case 
    by (auto elim: Plus(1,2))
next
  case (Times r1 r2)
  from Times(3,4) show ?case 
    by (auto simp: TimesR_def elim: Times(1,2) split: if_splits)
qed (auto simp: TimesR_def)

lemma safe_lpd: "safe_regex Future Safe r \<Longrightarrow> s \<in> lpd \<sigma> v i r \<Longrightarrow> safe_regex Future Safe s"
proof (induct r arbitrary: s)
  case (Plus r1 r2)
  from Plus(3,4) show ?case 
    by (auto elim: Plus(1,2))
next
  case (Times r1 r2)
  from Times(3,4) show ?case
    by (force simp: TimesR_def elim: Times(1,2) cosafe_lpd dest: lpd_fv_regex split: if_splits)
qed auto

lemma safe_rpd_fv_regex_le: "safe_regex Past Safe r \<Longrightarrow> s \<in> rpd \<sigma> v i r \<Longrightarrow> fv_regex r \<subseteq> fv_regex s"
  by (induct r) (auto simp: TimesL_def split: if_splits)

lemma safe_rpd_fv_regex: "safe_regex Past Safe r \<Longrightarrow> s \<in> rpd \<sigma> v i r \<Longrightarrow> fv_regex s = fv_regex r"
  by (simp add: eq_iff rpd_fv_regex safe_rpd_fv_regex_le)

lemma cosafe_rpd: "safe_regex Past Unsafe r \<Longrightarrow> s \<in> rpd \<sigma> v i r \<Longrightarrow> safe_regex Past Unsafe s"
proof (induct r arbitrary: s)
  case (Plus r1 r2)
  from Plus(3,4) show ?case 
    by (auto elim: Plus(1,2))
next
  case (Times r1 r2)
  from Times(3,4) show ?case 
    by (auto simp: TimesL_def elim: Times(1,2) split: if_splits)
qed (auto simp: TimesL_def)

lemma safe_rpd: "safe_regex Past Safe r \<Longrightarrow> s \<in> rpd \<sigma> v i r \<Longrightarrow> safe_regex Past Safe s"
proof (induct r arbitrary: s)
  case (Plus r1 r2)
  from Plus(3,4) show ?case 
    by (auto elim: Plus(1,2))
next
  case (Times r1 r2)
  from Times(3,4) show ?case
    by (force simp: TimesL_def elim: Times(1,2) cosafe_rpd dest: rpd_fv_regex split: if_splits)
qed auto

lemma disjE_Not2: "P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (\<not>P \<Longrightarrow> Q \<Longrightarrow> R) \<Longrightarrow> R"
  by blast

primrec atms :: "'a regex \<Rightarrow> 'a formula set" where
  "atms (Test \<phi>) = (if safe_formula \<phi> then {\<phi>} else case \<phi> of Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {})"
| "atms Wild = {}"
| "atms (Plus r s) = atms r \<union> atms s"
| "atms (Times r s) = atms r \<union> atms s"
| "atms (Star r) = atms r"

lemma finite_atms[simp]: "finite (atms r)"
  by (induct r) (auto split: formula.splits)

lemma safe_formula_regex_induct[consumes 2]:
  assumes "safe_formula \<phi>" "safe_regex b g r"
    and "\<And>t1 t2. is_Const t1 \<Longrightarrow> P (Eq t1 t2)"
    and "\<And>t1 t2. is_Const t2 \<Longrightarrow> P (Eq t1 t2)"
    and "\<And>x y. P (Neg (Eq (Const x) (Const y)))"
    and "\<And>x y. x = y \<Longrightarrow> P (Neg (Eq (Var x) (Var y)))"
    and "\<And>e ts. P (Pred e ts)"
    and "\<And>\<phi> \<psi>. \<not> (safe_formula (Neg \<psi>) \<and> fv \<psi> \<subseteq> fv \<phi>) \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And \<phi> \<psi>)"
    and "\<And>\<phi> \<psi>. safe_formula \<psi> \<Longrightarrow> fv \<psi> \<subseteq> fv \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And_Not \<phi> \<psi>)"
    and "\<And>\<phi>. \<lbrakk>\<forall>t1 t2. \<phi> \<noteq> Eq t1 t2; \<forall>\<psi>\<^sub>1 \<psi>\<^sub>2. \<not> (\<phi> = Or (Neg \<psi>\<^sub>1) \<psi>\<^sub>2 \<and> safe_formula \<psi>\<^sub>2 \<and> fv \<psi>\<^sub>2 \<subseteq> fv \<psi>\<^sub>1);
              \<forall>\<psi>\<^sub>1 \<psi>\<^sub>2 \<psi>\<^sub>2'. \<not> (\<phi> = Or (Neg \<psi>\<^sub>1) \<psi>\<^sub>2 \<and> \<not>(safe_formula \<psi>\<^sub>2 \<and> fv \<psi>\<^sub>2 \<subseteq> fv \<psi>\<^sub>1) \<and> \<psi>\<^sub>2 = Neg \<psi>\<^sub>2') \<rbrakk> \<Longrightarrow>
              fv \<phi> = {} \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Neg \<phi>)"
    and "\<And>\<phi> \<psi>. fv \<psi> = fv \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Or \<phi> \<psi>)"
    and "\<And>\<phi>. P \<phi> \<Longrightarrow> P (Exists \<phi>)"
    and "\<And>I \<phi>. P \<phi> \<Longrightarrow> P (Prev I \<phi>)"
    and "\<And>I \<phi>. P \<phi> \<Longrightarrow> P (Next I \<phi>)"
    and "\<And>\<phi> I \<psi>. fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Since \<phi> I \<psi>)"
    and "\<And>\<phi> I \<psi>. fv (Neg \<phi>) \<subseteq> fv \<psi> \<Longrightarrow>
      \<not> safe_formula (Neg \<phi>) \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Since (Neg \<phi>) I \<psi> )"
    and "\<And>\<phi> I \<psi>. fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Until \<phi> I \<psi>)"
    and "\<And>\<phi> I \<psi>. fv (Neg \<phi>) \<subseteq> fv \<psi> \<Longrightarrow>
      \<not> safe_formula (Neg \<phi>) \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Until (Neg \<phi>) I \<psi>)"
    and "\<And>I r. safe_regex Past Safe r \<Longrightarrow> Q Past Safe r \<Longrightarrow> P (MatchP I r)"
    and "\<And>I r. safe_regex Future Safe r \<Longrightarrow> Q Future Safe r \<Longrightarrow> P (MatchF I r)"
    and "\<And>b g. Q b g Wild"
    and "\<And>b g \<phi>. if safe_formula \<phi> then P \<phi> else g = Unsafe \<and> (\<exists>\<psi>. \<phi> = Neg \<psi> \<and> safe_formula \<psi> \<and> P \<psi>) \<Longrightarrow> Q b g (Test \<phi>)"
    and "\<And>b g r s. g = Unsafe \<or> fv_regex r = fv_regex s \<Longrightarrow> safe_regex b g r \<Longrightarrow> Q b g r \<Longrightarrow>
      safe_regex b g s \<Longrightarrow> Q b g s \<Longrightarrow> Q b g (Plus r s)"
    and "\<And>b g r s. g = Unsafe \<or> (case b of Future \<Rightarrow> fv_regex r \<subseteq> fv_regex s | Past \<Rightarrow> fv_regex s \<subseteq> fv_regex r) \<Longrightarrow>
      safe_regex b (case b of Future \<Rightarrow> Unsafe | Past \<Rightarrow> g) r \<Longrightarrow> Q b (case b of Future \<Rightarrow> Unsafe | Past \<Rightarrow> g) r \<Longrightarrow>
      safe_regex b (case b of Future \<Rightarrow> g | Past \<Rightarrow> Unsafe) s \<Longrightarrow> Q b (case b of Future \<Rightarrow> g | Past \<Rightarrow> Unsafe) s \<Longrightarrow>
      Q b g (Times r s)"
    and "\<And>b g r s. g = Unsafe \<Longrightarrow> safe_regex b g r \<Longrightarrow> Q b g r \<Longrightarrow> Q b g (Star r)"
  shows "P \<phi>" and "Q b g r"
  using assms(1,2)
  using [[goals_limit=50]]
proof (induction \<phi> and b g r rule: safe_formula_safe_regex.induct)
  case (5 \<phi> \<psi>)
  then show ?case
    by (cases \<psi>)
      (auto 0 3 elim!: disjE_Not2 intro: assms[unfolded And_def And_Not_def])
next
  case (11 \<phi> I \<psi>)
  then show ?case
    by (cases \<phi>) (auto 0 3 elim!: disjE_Not2 intro: assms)
next
  case (12 \<phi> I \<psi>)
  then show ?case
    by (cases \<phi>) (auto 0 3 elim!: disjE_Not2 intro: assms)
next
  case (16 b g \<phi>)
  then show ?case
    by (auto split: if_splits formula.splits simp: assms)
qed (auto intro: assms)

lemma safe_formula_induct[consumes 1]:
  assumes "safe_formula \<phi>"
    and "\<And>t1 t2. is_Const t1 \<Longrightarrow> P (Eq t1 t2)"
    and "\<And>t1 t2. is_Const t2 \<Longrightarrow> P (Eq t1 t2)"
    and "\<And>x y. P (Neg (Eq (Const x) (Const y)))"
    and "\<And>x y. x = y \<Longrightarrow> P (Neg (Eq (Var x) (Var y)))"
    and "\<And>e ts. P (Pred e ts)"
    and "\<And>\<phi> \<psi>. \<not> (safe_formula (Neg \<psi>) \<and> fv \<psi> \<subseteq> fv \<phi>) \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And \<phi> \<psi>)"
    and "\<And>\<phi> \<psi>. safe_formula \<psi> \<Longrightarrow> fv \<psi> \<subseteq> fv \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And_Not \<phi> \<psi>)"
    and "\<And>\<phi>. \<lbrakk>\<forall>t1 t2. \<phi> \<noteq> Eq t1 t2; \<forall>\<psi>\<^sub>1 \<psi>\<^sub>2. \<not> (\<phi> = Or (Neg \<psi>\<^sub>1) \<psi>\<^sub>2 \<and> safe_formula \<psi>\<^sub>2 \<and> fv \<psi>\<^sub>2 \<subseteq> fv \<psi>\<^sub>1);
              \<forall>\<psi>\<^sub>1 \<psi>\<^sub>2 \<psi>\<^sub>2'. \<not> (\<phi> = Or (Neg \<psi>\<^sub>1) \<psi>\<^sub>2 \<and> \<not>(safe_formula \<psi>\<^sub>2 \<and> fv \<psi>\<^sub>2 \<subseteq> fv \<psi>\<^sub>1) \<and> \<psi>\<^sub>2 = Neg \<psi>\<^sub>2') \<rbrakk> \<Longrightarrow>
              fv \<phi> = {} \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Neg \<phi>)"
    and "\<And>\<phi> \<psi>. fv \<psi> = fv \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Or \<phi> \<psi>)"
    and "\<And>\<phi>. P \<phi> \<Longrightarrow> P (Exists \<phi>)"
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
  by (rule safe_formula_regex_induct[where r = Wild and Q = "\<lambda>b g r. safe_regex b g r \<and> (\<forall>\<phi> \<in> atms r. P \<phi>)"])
    (auto simp: assms split: if_splits modality.splits)

lemma safe_regex_induct[consumes 1, case_names Wild Test Plus Times Star]:
  assumes "safe_regex b g r"
    and "\<And>b g. Q b g Wild"
    and "\<And>b g \<phi>. safe_formula \<phi> \<or> g = Unsafe \<and> (\<exists>\<psi>. \<phi> = Neg \<psi> \<and> safe_formula \<psi>) \<Longrightarrow> Q b g (Test \<phi>)"
    and "\<And>b g r s. g = Unsafe \<or> fv_regex r = fv_regex s \<Longrightarrow> safe_regex b g r \<Longrightarrow> Q b g r \<Longrightarrow>
      safe_regex b g s \<Longrightarrow> Q b g s \<Longrightarrow> Q b g (Plus r s)"
    and "\<And>b g r s. g = Unsafe \<or> (case b of Future \<Rightarrow> fv_regex r \<subseteq> fv_regex s | Past \<Rightarrow> fv_regex s \<subseteq> fv_regex r) \<Longrightarrow>
      safe_regex b (case b of Future \<Rightarrow> Unsafe | Past \<Rightarrow> g) r \<Longrightarrow> Q b (case b of Future \<Rightarrow> Unsafe | Past \<Rightarrow> g) r \<Longrightarrow>
      safe_regex b (case b of Future \<Rightarrow> g | Past \<Rightarrow> Unsafe) s \<Longrightarrow> Q b (case b of Future \<Rightarrow> g | Past \<Rightarrow> Unsafe) s \<Longrightarrow> Q b g (Times r s)"
    and "\<And>b g r. g = Unsafe \<Longrightarrow> safe_regex b g r \<Longrightarrow> Q b g r \<Longrightarrow> Q b g (Star r)"
  shows "Q b g r"
proof (rule safe_formula_regex_induct[where \<phi> = TT and P = safe_formula])
  fix \<phi> :: "'a formula"
  assume "\<forall>t1 t2. \<phi> \<noteq> Eq t1 t2"
    "\<forall>\<psi>\<^sub>1 \<psi>\<^sub>2. \<not> (\<phi> = Or (Neg \<psi>\<^sub>1) \<psi>\<^sub>2 \<and> safe_formula \<psi>\<^sub>2 \<and> fv \<psi>\<^sub>2 \<subseteq> fv \<psi>\<^sub>1)"
    "\<forall>\<psi>\<^sub>1 \<psi>\<^sub>2 \<psi>\<^sub>2'. \<not> (\<phi> = Or (Neg \<psi>\<^sub>1) \<psi>\<^sub>2 \<and> \<not> (safe_formula \<psi>\<^sub>2 \<and> fv \<psi>\<^sub>2 \<subseteq> fv \<psi>\<^sub>1) \<and> \<psi>\<^sub>2 = Neg \<psi>\<^sub>2')"
    "fv \<phi> = {}" "safe_formula \<phi>"
  then show "safe_formula (Neg \<phi>)"
  proof (induct \<phi>)
    case (Or \<phi>1 \<phi>2)
    then show ?case
      by (cases \<phi>1) auto
  qed auto
qed (auto simp: And_def And_Not_def intro!: assms)


subsection \<open>Slicing Traces\<close>

qualified primrec matches :: "'a env \<Rightarrow> 'a formula \<Rightarrow> name \<times> 'a list \<Rightarrow> bool"
  and matches_regex :: "'a env \<Rightarrow> 'a regex \<Rightarrow> name \<times> 'a list \<Rightarrow> bool" where
  "matches v (Pred r ts) e = (r = fst e \<and> map (eval_trm v) ts = snd e)"
| "matches v (Eq _ _) e = False"
| "matches v (Neg \<phi>) e = matches v \<phi> e"
| "matches v (Or \<phi> \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Exists \<phi>) e = (\<exists>z. matches (z # v) \<phi> e)"
| "matches v (Prev I \<phi>) e = matches v \<phi> e"
| "matches v (Next I \<phi>) e = matches v \<phi> e"
| "matches v (Since \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Until \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (MatchP I r) e = matches_regex v r e"
| "matches v (MatchF I r) e = matches_regex v r e"
| "matches_regex v Wild e = False"
| "matches_regex v (Test \<phi>) e = matches v \<phi> e"
| "matches_regex v (Plus r s) e = (matches_regex v r e \<or> matches_regex v s e)"
| "matches_regex v (Times r s) e = (matches_regex v r e \<or> matches_regex v s e)"
| "matches_regex v (Star r) e = matches_regex v r e"

lemma matches_cong:
  "\<forall>x\<in>fv \<phi>. v!x = v'!x \<Longrightarrow> matches v \<phi> e = matches v' \<phi> e"
  "\<forall>x\<in>fv_regex r. v!x = v'!x \<Longrightarrow> matches_regex v r e = matches_regex v' r e"
proof (induct \<phi> and r arbitrary: v v' and v v')
  case (Pred n ts)
  show ?case by (simp cong: map_cong eval_trm_fv_cong[OF Pred[simplified, THEN bspec]])
next
  case (Exists \<phi>)
  then show ?case unfolding matches.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
qed (auto 5 0 simp add: nth_Cons')

abbreviation relevant_events where
  "relevant_events \<phi> S \<equiv> {e. S \<inter> {v. matches v \<phi> e} \<noteq> {}}"

abbreviation relevant_events_regex where
  "relevant_events_regex r S \<equiv> {e. S \<inter> {v. matches_regex v r e} \<noteq> {}}"

qualified definition slice :: "'a formula \<Rightarrow> 'a env set \<Rightarrow> 'a trace \<Rightarrow> 'a trace" where
  "slice \<phi> S \<sigma> = map_\<Gamma> (\<lambda>D. D \<inter> relevant_events \<phi> S) \<sigma>"

lemma \<tau>_slice[simp]: "\<tau> (slice \<phi> S \<sigma>) = \<tau> \<sigma>"
  unfolding slice_def by (simp add: fun_eq_iff)

lemma sat_slice_strong:
  assumes "v \<in> S"
  shows "relevant_events \<phi> S \<subseteq> E \<Longrightarrow> sat \<sigma> v i \<phi> \<longleftrightarrow> sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) v i \<phi>"
    and "relevant_events_regex r S \<subseteq> E \<Longrightarrow> match \<sigma> v r = match (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) v r"
  using assms
proof (induction \<phi> and r arbitrary: v S i and v S i)
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
  case (Exists \<phi>)
  have "sat \<sigma> (z # v) i \<phi> = sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) (z # v) i \<phi>" for z
    thm Exists.IH[of "{z # v | v. v \<in> S}"]
    using Exists.prems by (auto intro!: Exists.IH[of "{z # v | v. v \<in> S}"])
  then show ?case by simp
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
  case (Plus r s)
  then have "relevant_events_regex r S \<subseteq> E" "relevant_events_regex s S \<subseteq> E"
    by auto
  with Plus show ?case
    by auto
next
  case (Times r s)
  then have "relevant_events_regex r S \<subseteq> E" "relevant_events_regex s S \<subseteq> E"
    by auto
  with Times show ?case
    by auto
qed auto

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

end (*context*)

(*<*)
end
(*>*)