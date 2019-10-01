(*<*)
theory Monitor
  imports Abstract_Monitor Table
    "HOL-Library.While_Combinator"
    "HOL-Library.Mapping"
    "Deriving.Derive"
begin
(*>*)

section \<open>Concrete Monitor\<close>

subsection \<open>Monitorable Formulas\<close>

definition "mmonitorable \<phi> \<longleftrightarrow> safe_formula \<phi> \<and> MFOTL.future_reach \<phi> \<noteq> \<infinity>"
definition "mmonitorable_regex b g r \<longleftrightarrow> safe_regex b g r \<and> MFOTL.future_reach_regex r \<noteq> \<infinity>"

fun mmonitorable_exec :: "'a MFOTL.formula \<Rightarrow> bool"
and mmonitorable_regex_exec :: "modality \<Rightarrow> safety \<Rightarrow> 'a MFOTL.regex \<Rightarrow> bool" where
  "mmonitorable_exec (MFOTL.Eq t1 t2) = (MFOTL.is_Const t1 \<or> MFOTL.is_Const t2)"
| "mmonitorable_exec (MFOTL.Neg (MFOTL.Eq (MFOTL.Const x) (MFOTL.Const y))) = True"
| "mmonitorable_exec (MFOTL.Neg (MFOTL.Eq (MFOTL.Var x) (MFOTL.Var y))) = (x = y)"
| "mmonitorable_exec (MFOTL.Pred e ts) = True"
| "mmonitorable_exec (MFOTL.Neg (MFOTL.Or (MFOTL.Neg \<phi>) \<psi>)) = (mmonitorable_exec \<phi> \<and>
    (mmonitorable_exec \<psi> \<and> MFOTL.fv \<psi> \<subseteq> MFOTL.fv \<phi> \<or> (case \<psi> of MFOTL.Neg \<psi>' \<Rightarrow> mmonitorable_exec \<psi>' | _ \<Rightarrow> False)))"
| "mmonitorable_exec (MFOTL.Or \<phi> \<psi>) = (MFOTL.fv \<psi> = MFOTL.fv \<phi> \<and> mmonitorable_exec \<phi> \<and> mmonitorable_exec \<psi>)"
| "mmonitorable_exec (MFOTL.Neg \<phi>) = (MFOTL.fv \<phi> = {} \<and> mmonitorable_exec \<phi>)"
| "mmonitorable_exec (MFOTL.Exists \<phi>) = (mmonitorable_exec \<phi>)"
| "mmonitorable_exec (MFOTL.Prev I \<phi>) = (mmonitorable_exec \<phi>)"
| "mmonitorable_exec (MFOTL.Next I \<phi>) = (mmonitorable_exec \<phi> \<and> right I \<noteq> \<infinity>)"
| "mmonitorable_exec (MFOTL.Since \<phi> I \<psi>) = (MFOTL.fv \<phi> \<subseteq> MFOTL.fv \<psi> \<and>
    (mmonitorable_exec \<phi> \<or> (case \<phi> of MFOTL.Neg \<phi>' \<Rightarrow> mmonitorable_exec \<phi>' | _ \<Rightarrow> False)) \<and> mmonitorable_exec \<psi>)"
| "mmonitorable_exec (MFOTL.Until \<phi> I \<psi>) = (MFOTL.fv \<phi> \<subseteq> MFOTL.fv \<psi> \<and> right I \<noteq> \<infinity> \<and>
    (mmonitorable_exec \<phi> \<or> (case \<phi> of MFOTL.Neg \<phi>' \<Rightarrow> mmonitorable_exec \<phi>' | _ \<Rightarrow> False)) \<and> mmonitorable_exec \<psi>)"
| "mmonitorable_exec (MFOTL.MatchP I r) = mmonitorable_regex_exec Past Safe r"
| "mmonitorable_exec (MFOTL.MatchF I r) = (mmonitorable_regex_exec Future Safe r \<and> right I \<noteq> \<infinity>)"
| "mmonitorable_regex_exec b g MFOTL.Wild = True"
| "mmonitorable_regex_exec b g (MFOTL.Test \<phi>) = (mmonitorable_exec \<phi> \<or> (g = Unsafe \<and> (case \<phi> of MFOTL.Neg \<phi>' \<Rightarrow> mmonitorable_exec \<phi>' | _ \<Rightarrow> False)))"
| "mmonitorable_regex_exec b g (MFOTL.Plus r s) = ((g = Unsafe \<or> fv_regex r = fv_regex s) \<and> mmonitorable_regex_exec b g r \<and> mmonitorable_regex_exec b g s)"
| "mmonitorable_regex_exec Future g (MFOTL.Times r s) = ((g = Unsafe \<or> fv_regex r \<subseteq> fv_regex s) \<and> mmonitorable_regex_exec Future Unsafe r \<and> mmonitorable_regex_exec Future g s)"
| "mmonitorable_regex_exec Past g (MFOTL.Times r s) = ((g = Unsafe \<or> fv_regex s \<subseteq> fv_regex r) \<and> mmonitorable_regex_exec Past g r \<and> mmonitorable_regex_exec Past Unsafe s)"
| "mmonitorable_regex_exec b g (MFOTL.Star r) = (g = Unsafe \<and> mmonitorable_regex_exec b g r)"

lemma plus_eq_enat_iff: "a + b = enat i \<longleftrightarrow> (\<exists>j k. a = enat j \<and> b = enat k \<and> j + k = i)"
  by (cases a; cases b) auto

lemma minus_eq_enat_iff: "a - enat k = enat i \<longleftrightarrow> (\<exists>j. a = enat j \<and> j - k = i)"
  by (cases a) auto

lemma le_enat_iff: "a \<le> enat i \<longleftrightarrow> (\<exists>j. a = enat j \<and> j \<le> i)"
  by (cases a) auto

lemma less_enat_iff: "a < enat i \<longleftrightarrow> (\<exists>j. a = enat j \<and> j < i)"
  by (cases a) auto

lemma safe_formula_mmonitorable_exec:
  fixes \<phi> :: "'a MFOTL.formula" and r :: "'a MFOTL.regex"
  shows "safe_formula \<phi> \<Longrightarrow> MFOTL.future_reach \<phi> \<noteq> \<infinity> \<Longrightarrow> mmonitorable_exec \<phi>"
  and "safe_regex b g r \<Longrightarrow> MFOTL.future_reach_regex r \<noteq> \<infinity> \<Longrightarrow> mmonitorable_regex_exec b g r"
proof (induct \<phi> and b g r rule: safe_formula_safe_regex.induct)
  case (5 \<phi> \<psi>)
  then show ?case
    unfolding safe_formula.simps future_reach.simps mmonitorable_exec.simps
    by (fastforce split: formula.splits)
next
  case (7 \<phi> \<psi>)
  then show ?case 
    unfolding safe_formula.simps future_reach.simps mmonitorable_exec.simps
    by (fastforce split: formula.splits)
next
  case (11 \<phi> I \<psi>)
  then show ?case 
    unfolding safe_formula.simps future_reach.simps mmonitorable_exec.simps
    by (fastforce split: formula.splits)
next
  case (12 \<phi> I \<psi>)
  then show ?case
    unfolding safe_formula.simps future_reach.simps mmonitorable_exec.simps
    by (fastforce simp: plus_eq_enat_iff split: formula.splits)
next
  case (16 b g \<phi>)
  then show ?case
    by (cases \<phi>) auto
qed (auto simp add: plus_eq_enat_iff minus_eq_enat_iff max_def
  le_enat_iff less_enat_iff not_le split: if_splits)

lemma mmonitorable_exec_mmonitorable:
  fixes \<phi> :: "'a MFOTL.formula" and r :: "'a MFOTL.regex"
  shows "mmonitorable_exec \<phi> \<Longrightarrow> mmonitorable \<phi>"
  and "mmonitorable_regex_exec b g r \<Longrightarrow> mmonitorable_regex b g r"
proof (induct \<phi> and b g r rule: mmonitorable_exec_mmonitorable_regex_exec.induct)
  case (5 \<phi> \<psi>)
  then show ?case
    unfolding mmonitorable_def mmonitorable_exec.simps safe_formula.simps
    by (fastforce split: formula.splits)
next
  case (11 \<phi> I \<psi>)
  then show ?case
    unfolding mmonitorable_def mmonitorable_exec.simps safe_formula.simps
    by (fastforce split: formula.splits)
next
  case (12 \<phi> I \<psi>)
  then show ?case
    unfolding mmonitorable_def mmonitorable_exec.simps safe_formula.simps
    by (fastforce simp: one_enat_def split: formula.splits)
next
  case (16 b g \<phi>)
  then show ?case
    by (cases \<phi>) (auto simp: mmonitorable_regex_def mmonitorable_def)
qed (auto simp add: mmonitorable_def mmonitorable_regex_def one_enat_def)

lemma monitorable_formula_code[code]: "mmonitorable \<phi> = mmonitorable_exec \<phi>"
  using mmonitorable_exec_mmonitorable safe_formula_mmonitorable_exec mmonitorable_def
  by blast

subsection \<open>Handling Regular Expressions\<close>

datatype mregex =
  MWild
| MEps
| MTestPos nat
| MTestNeg nat
| MPlus mregex mregex
| MTimes mregex mregex
| MStar mregex

primrec ok where
  "ok _ MWild = True"
| "ok _ MEps = True"
| "ok m (MTestPos n) = (n < m)"
| "ok m (MTestNeg n) = (n < m)"
| "ok m (MPlus r s) = (ok m r \<and> ok m s)"
| "ok m (MTimes r s) = (ok m r \<and> ok m s)"
| "ok m (MStar r) = ok m r"

primrec from_mregex where
  "from_mregex MWild _ = MFOTL.Wild"
| "from_mregex MEps _ = MFOTL.Test MFOTL.TT"
| "from_mregex (MTestPos n) \<phi>s = MFOTL.Test (\<phi>s ! n)"
| "from_mregex (MTestNeg n) \<phi>s = (if safe_formula (MFOTL.Neg (\<phi>s ! n)) then
       MFOTL.Times (MFOTL.Star (MFOTL.Test MFOTL.FF))
         (MFOTL.Times (MFOTL.Test (MFOTL.Neg (\<phi>s ! n))) (MFOTL.Star (MFOTL.Test MFOTL.FF))) \<comment> \<open>hack to produce a sound but unsafe formula\<close>
     else MFOTL.Test (MFOTL.Neg (\<phi>s ! n)))"
| "from_mregex (MPlus r s) \<phi>s = MFOTL.Plus (from_mregex r \<phi>s) (from_mregex s \<phi>s)"
| "from_mregex (MTimes r s) \<phi>s = MFOTL.Times (from_mregex r \<phi>s) (from_mregex s \<phi>s)"
| "from_mregex (MStar r) \<phi>s = MFOTL.Star (from_mregex r \<phi>s)"

primrec to_mregex_exec where
  "to_mregex_exec MFOTL.Wild xs = (MWild, xs)"
| "to_mregex_exec (MFOTL.Test \<phi>) xs = (if safe_formula \<phi> then (MTestPos (length xs), xs @ [\<phi>])
     else case \<phi> of MFOTL.Neg \<phi>' \<Rightarrow> (MTestNeg (length xs), xs @ [\<phi>']) | _ \<Rightarrow> (MEps, xs))"
| "to_mregex_exec (MFOTL.Plus r s) xs = 
     (let (mr, ys) = to_mregex_exec r xs; (ms, zs) = to_mregex_exec s ys
     in (MPlus mr ms, zs))"
| "to_mregex_exec (MFOTL.Times r s) xs = 
     (let (mr, ys) = to_mregex_exec r xs; (ms, zs) = to_mregex_exec s ys
     in (MTimes mr ms, zs))"
| "to_mregex_exec (MFOTL.Star r) xs = 
     (let (mr, ys) = to_mregex_exec r xs in (MStar mr, ys))"

primrec shift where
  "shift MWild k = MWild"
| "shift MEps k = MEps"
| "shift (MTestPos i) k = MTestPos (i + k)"
| "shift (MTestNeg i) k = MTestNeg (i + k)"
| "shift (MPlus r s) k = MPlus (shift r k) (shift s k)"
| "shift (MTimes r s) k = MTimes (shift r k) (shift s k)"
| "shift (MStar r) k = MStar (shift r k)"

primrec to_mregex where
  "to_mregex MFOTL.Wild = (MWild, [])"
| "to_mregex (MFOTL.Test \<phi>) = (if safe_formula \<phi> then (MTestPos 0, [\<phi>])
     else case \<phi> of MFOTL.Neg \<phi>' \<Rightarrow> (MTestNeg 0, [\<phi>']) | _ \<Rightarrow> (MEps, []))"
| "to_mregex (MFOTL.Plus r s) =
     (let (mr, ys) = to_mregex r; (ms, zs) = to_mregex s
     in (MPlus mr (shift ms (length ys)), ys @ zs))"
| "to_mregex (MFOTL.Times r s) =
     (let (mr, ys) = to_mregex r; (ms, zs) = to_mregex s
     in (MTimes mr (shift ms (length ys)), ys @ zs))"
| "to_mregex (MFOTL.Star r) = 
     (let (mr, ys) = to_mregex r in (MStar mr, ys))"

lemma shift_0: "shift r 0 = r"
  by (induct r) auto

lemma shift_shift: "shift (shift r k) j = shift r (k + j)"
  by (induct r) auto

lemma to_mregex_to_mregex_exec: 
  "case to_mregex r of (mr, \<phi>s) \<Rightarrow> to_mregex_exec r xs = (shift mr (length xs), xs @ \<phi>s)"
  by (induct r arbitrary: xs)
    (auto simp: shift_shift ac_simps split: formula.splits prod.splits)

lemma to_mregex_to_mregex_exec_Nil[code]: "to_mregex r = to_mregex_exec r []"
  using to_mregex_to_mregex_exec[where xs="[]" and r = r] by (auto simp: shift_0)

lemma ok_mono: "ok m mr \<Longrightarrow> m \<le> n \<Longrightarrow> ok n mr"
  by (induct mr) auto

lemma from_mregex_cong: "ok m mr \<Longrightarrow> (\<forall>i < m. xs ! i = ys ! i) \<Longrightarrow> from_mregex mr xs = from_mregex mr ys"
  by (induct mr) auto

lemma to_mregex_exec_ok: 
  "to_mregex_exec r xs = (mr, ys) \<Longrightarrow> \<exists>zs. ys = xs @ zs \<and> set zs = atms r \<and> ok (length ys) mr"
  by (induct r arbitrary: xs mr ys)
    (fastforce split: if_splits prod.splits formula.splits elim: ok_mono)+

lemma ok_shift: "ok (i + m) (Monitor.shift r i) \<longleftrightarrow> ok m r"
  by (induct r) auto

lemma to_mregex_ok: "to_mregex r = (mr, ys) \<Longrightarrow> set ys = atms r \<and> ok (length ys) mr"
  by (induct r arbitrary: mr ys)
    (fastforce simp: ok_shift elim: ok_mono split: if_splits prod.splits formula.splits)+

lemma from_mregex_shift: "from_mregex (shift r (length xs)) (xs @ ys) = from_mregex r ys"
  by (induct r) (auto simp: nth_append)

lemma from_mregex_to_mregex: "safe_regex m g r \<Longrightarrow> case_prod from_mregex (to_mregex r) = r"
  by (induct r rule: safe_regex_induct)
    (auto dest: to_mregex_ok intro!: from_mregex_cong simp: nth_append from_mregex_shift
      split: prod.splits modality.splits)

lemma from_mregex_eq: "safe_regex m g r \<Longrightarrow> to_mregex r = (mr, \<phi>s) \<Longrightarrow> from_mregex mr \<phi>s = r"
  using from_mregex_to_mregex[of m g r] by auto

lemma from_mregex_to_mregex_exec: "safe_regex m g r \<Longrightarrow> case_prod from_mregex (to_mregex_exec r xs) = r"
proof (induct r arbitrary: xs rule: safe_regex_induct)
  case (Plus b g r s)
  from Plus(1,2,4) Plus(3)[of xs] Plus(5)[of "snd (to_mregex_exec r xs)"] show ?case
    by (auto split: prod.splits simp: nth_append dest: to_mregex_exec_ok
      intro!: from_mregex_cong[where m = "length (snd (to_mregex_exec r xs))"])
next
  case (Times b g r s)
  from Times(1,2,4) Times(3)[of xs] Times(5)[of "snd (to_mregex_exec r xs)"] show ?case
    by (auto split: prod.splits simp: nth_append dest: to_mregex_exec_ok
      intro!: from_mregex_cong[where m = "length (snd (to_mregex_exec r xs))"])
next
  case (Star b g r)
  from Star(1,2) Star(3)[of xs] show ?case
    by (auto split: prod.splits)
qed (auto split: prod.splits)
  

derive linorder mregex

section \<open>LPD\<close>

definition saturate where
  "saturate f = while (\<lambda>S. f S \<noteq> S) f"

lemma saturate_code[code]:
  "saturate f S = (let S' = f S in if S' = S then S else saturate f S')"
  unfolding saturate_def Let_def
  by (subst while_unfold) auto

definition "MTimesL r S = MTimes r ` S"
definition "MTimesR R s = (\<lambda>r. MTimes r s) ` R"

primrec LPD where 
  "LPD MWild = {MEps}"
| "LPD MEps = {}"
| "LPD (MTestPos \<phi>) = {}"
| "LPD (MTestNeg \<phi>) = {}"
| "LPD (MPlus r s) = (LPD r \<union> LPD s)"
| "LPD (MTimes r s) = MTimesR (LPD r) s \<union> LPD s"
| "LPD (MStar r) = MTimesR (LPD r) (MStar r)"

primrec LPDi where
  "LPDi 0 r = {r}"
| "LPDi (Suc i) r = (\<Union>s \<in> LPD r. LPDi i s)"

lemma LPDi_Suc_alt: "LPDi (Suc i) r = (\<Union>s \<in> LPDi i r. LPD s)"
  by (induct i arbitrary: r) fastforce+

definition "LPDs r = (\<Union>i. LPDi i r)"

lemma LPDs_refl: "r \<in> LPDs r"
  by (auto simp: LPDs_def intro: exI[of _ 0])
lemma LPDs_trans: "r \<in> LPD s \<Longrightarrow> s \<in> LPDs t \<Longrightarrow> r \<in> LPDs t"
  by (force simp: LPDs_def LPDi_Suc_alt simp del: LPDi.simps intro: exI[of _ "Suc _"])

lemma LPDi_Test:
  "LPDi i (MEps) \<subseteq> {MEps}"
  "LPDi i (MTestPos \<phi>) \<subseteq> {MTestPos \<phi>}"
  "LPDi i (MTestNeg \<phi>) \<subseteq> {MTestNeg \<phi>}"
  by (induct i) auto

lemma LPDs_Test:
  "LPDs (MEps) \<subseteq> {MEps}"
  "LPDs (MTestPos \<phi>) \<subseteq> {MTestPos \<phi>}"
  "LPDs (MTestNeg \<phi>) \<subseteq> {MTestNeg \<phi>}"
  unfolding LPDs_def using LPDi_Test by blast+

lemma LPDi_Wild: "LPDi i (MWild) \<subseteq> {MWild, MEps}"
  by (induct i) (auto dest: set_mp[OF LPDi_Test(1)])

lemma LPDs_Wild: "LPDs (MWild) \<subseteq> {MWild, MEps}"
  unfolding LPDs_def using LPDi_Wild by auto

lemma LPDi_Plus: "LPDi i (MPlus r s) \<subseteq> {MPlus r s} \<union> LPDi i r \<union> LPDi i s"
  by (induct i arbitrary: r s) auto

lemma LPDs_Plus: "LPDs (MPlus r s) \<subseteq> {MPlus r s} \<union> LPDs r \<union> LPDs s"
  unfolding LPDs_def using LPDi_Plus[of _ r s] by auto

lemma LPDi_Times: 
  "LPDi i (MTimes r s) \<subseteq> {MTimes r s} \<union> MTimesR (\<Union>j \<le> i. LPDi j r) s \<union> (\<Union>j \<le> i. LPDi j s)"
proof (induct i arbitrary: r s)
  case (Suc i)
  show ?case 
    by (fastforce simp: MTimesR_def dest: bspec[of _ _ "Suc _"] dest!: set_mp[OF Suc])
qed simp

lemma LPDs_Times: "LPDs (MTimes r s) \<subseteq> {MTimes r s} \<union> MTimesR (LPDs r) s \<union> LPDs s"
  unfolding LPDs_def using LPDi_Times[of _ r s] by (force simp: MTimesR_def)

lemma LPDi_Star: "j \<le> i \<Longrightarrow> LPDi j (MStar r) \<subseteq> {MStar r} \<union> MTimesR (\<Union>j \<le> i. LPDi j r) (MStar r)"
proof (induct i arbitrary: j r)
  case (Suc i)
  from Suc(2) show ?case 
    by (auto 0 5 simp: MTimesR_def image_iff le_Suc_eq
       dest: bspec[of _ _ "Suc 0"] bspec[of _ _ "Suc _"] set_mp[OF Suc(1)] dest!: set_mp[OF LPDi_Times])
qed simp

lemma LPDs_Star: "LPDs (MStar r) \<subseteq> {MStar r} \<union> MTimesR (LPDs r) (MStar r)"
  unfolding LPDs_def using LPDi_Star[OF order_refl, of _ r] by (force simp: MTimesR_def)

lemma finite_LPDs: "finite (LPDs r)"
proof (induct r)
  case MWild
  then show ?case by (intro finite_subset[OF LPDs_Wild]) simp
next
  case (MEps)
  then show ?case by (intro finite_subset[OF LPDs_Test(1)]) simp
next
  case (MTestPos \<phi>)
  then show ?case by (intro finite_subset[OF LPDs_Test(2)]) simp
next
  case (MTestNeg \<phi>)
  then show ?case by (intro finite_subset[OF LPDs_Test(3)]) simp
next
  case (MPlus r s)
  then show ?case by (intro finite_subset[OF LPDs_Plus]) simp
next
  case (MTimes r s)
  then show ?case by (intro finite_subset[OF LPDs_Times]) (simp add: MTimesR_def)
next
  case (MStar r)
  then show ?case by (intro finite_subset[OF LPDs_Star]) (simp add: MTimesR_def)
qed

context begin

private abbreviation (input) "addLPD r \<equiv> \<lambda>S. insert r S \<union> UNION (insert r S) LPD"

private lemma mono_addLPD: "mono (addLPD r)"
  unfolding mono_def by auto

private lemma LPDs_aux1: "lfp (addLPD r) \<subseteq> LPDs r"
  by (rule lfp_induct[OF mono_addLPD], auto intro: LPDs_refl LPDs_trans)

private lemma LPDs_aux2: "LPDi i r \<subseteq> lfp (addLPD r)"
proof (induct i)
  case 0
  then show ?case
    by (subst lfp_unfold[OF mono_addLPD]) auto
next
  case (Suc i)
  then show ?case
    by (subst lfp_unfold[OF mono_addLPD]) (auto simp: LPDi_Suc_alt simp del: LPDi.simps)
qed

lemma LPDs_alt: "LPDs r = lfp (addLPD r)"
  using LPDs_aux1 LPDs_aux2 by (force simp: LPDs_def)

lemma LPDs_code[code]:
  "LPDs r = saturate (addLPD r) {}"
  unfolding LPDs_alt saturate_def
  by (rule lfp_while[OF mono_addLPD _ finite_LPDs, of r]) (auto simp: LPDs_refl LPDs_trans)

end

section \<open>RPD\<close>

primrec RPD where 
  "RPD MWild = {MEps}"
| "RPD MEps = {}"
| "RPD (MTestPos \<phi>) = {}"
| "RPD (MTestNeg \<phi>) = {}"
| "RPD (MPlus r s) = (RPD r \<union> RPD s)"
| "RPD (MTimes r s) = MTimesL r (RPD s) \<union> RPD r"
| "RPD (MStar r) = MTimesL (MStar r) (RPD r)"

primrec RPDi where
  "RPDi 0 r = {r}"
| "RPDi (Suc i) r = (\<Union>s \<in> RPD r. RPDi i s)"

lemma RPDi_Suc_alt: "RPDi (Suc i) r = (\<Union>s \<in> RPDi i r. RPD s)"
  by (induct i arbitrary: r) fastforce+

definition "RPDs r = (\<Union>i. RPDi i r)"

lemma RPDs_refl: "r \<in> RPDs r"
  by (auto simp: RPDs_def intro: exI[of _ 0])
lemma RPDs_trans: "r \<in> RPD s \<Longrightarrow> s \<in> RPDs t \<Longrightarrow> r \<in> RPDs t"
  by (force simp: RPDs_def RPDi_Suc_alt simp del: RPDi.simps intro: exI[of _ "Suc _"])

lemma RPDi_Test:
  "RPDi i (MEps) \<subseteq> {MEps}"
  "RPDi i (MTestPos \<phi>) \<subseteq> {MTestPos \<phi>}"
  "RPDi i (MTestNeg \<phi>) \<subseteq> {MTestNeg \<phi>}"
  by (induct i) auto

lemma RPDs_Test:
  "RPDs (MEps) \<subseteq> {MEps}"
  "RPDs (MTestPos \<phi>) \<subseteq> {MTestPos \<phi>}"
  "RPDs (MTestNeg \<phi>) \<subseteq> {MTestNeg \<phi>}"
  unfolding RPDs_def using RPDi_Test by blast+

lemma MEps_RPDs_Wild: "MEps \<in> RPDs MWild"
  unfolding RPDs_def by (auto intro: exI[of _ 1])

lemma RPDi_Wild: "RPDi i (MWild) \<subseteq> {MWild, MEps}"
  by (induct i) (auto dest: set_mp[OF RPDi_Test(1)])

lemma RPDs_Wild: "RPDs (MWild) \<subseteq> {MWild, MEps}"
  unfolding RPDs_def using RPDi_Wild by auto

lemma RPDs_base_eq:
  "RPDs MWild = {MWild, MEps}"
  "RPDs MEps = {MEps}"
  "RPDs (MTestPos \<phi>) = {MTestPos \<phi>}"
  "RPDs (MTestNeg \<phi>) = {MTestNeg \<phi>}"
  using RPDs_Wild MEps_RPDs_Wild RPDs_refl RPDs_Test(1) RPDs_Test(2,3)[of \<phi>] by auto

lemma RPDi_Plus: "RPDi i (MPlus r s) \<subseteq> {MPlus r s} \<union> RPDi i r \<union> RPDi i s"
  by (induct i arbitrary: r s) auto

lemma RPDi_Suc_RPD_Plus:
  "RPDi (Suc i) r \<subseteq> RPDs (MPlus r s)"
  "RPDi (Suc i) s \<subseteq> RPDs (MPlus r s)"
  unfolding RPDs_def by (force intro!: exI[of _ "Suc i"])+

lemma RPDs_Plus: "RPDs (MPlus r s) \<subseteq> {MPlus r s} \<union> RPDs r \<union> RPDs s"
  unfolding RPDs_def using RPDi_Plus[of _ r s] by auto

lemma RPDi_Times: 
  "RPDi i (MTimes r s) \<subseteq> {MTimes r s} \<union> MTimesL r (\<Union>j \<le> i. RPDi j s) \<union> (\<Union>j \<le> i. RPDi j r)"
proof (induct i arbitrary: r s)
  case (Suc i)
  show ?case 
    by (fastforce simp: MTimesL_def dest: bspec[of _ _ "Suc _"] dest!: set_mp[OF Suc])
qed simp

lemma RPDs_Times: "RPDs (MTimes r s) \<subseteq> {MTimes r s} \<union> MTimesL r (RPDs s) \<union> RPDs r"
  unfolding RPDs_def using RPDi_Times[of _ r s] by (force simp: MTimesL_def)

lemma RPDi_Star: "j \<le> i \<Longrightarrow> RPDi j (MStar r) \<subseteq> {MStar r} \<union> MTimesL (MStar r) (\<Union>j \<le> i. RPDi j r)"
proof (induct i arbitrary: j r)
  case (Suc i)
  from Suc(2) show ?case 
    by (auto 0 5 simp: MTimesL_def image_iff le_Suc_eq
       dest: bspec[of _ _ "Suc 0"] bspec[of _ _ "Suc _"] set_mp[OF Suc(1)] dest!: set_mp[OF RPDi_Times])
qed simp

lemma RPDs_Star: "RPDs (MStar r) \<subseteq> {MStar r} \<union> MTimesL (MStar r) (RPDs r)"
  unfolding RPDs_def using RPDi_Star[OF order_refl, of _ r] by (force simp: MTimesL_def)

lemma finite_RPDs: "finite (RPDs r)"
proof (induct r)
  case MWild
  then show ?case by (intro finite_subset[OF RPDs_Wild]) simp
next
  case (MEps)
  then show ?case by (intro finite_subset[OF RPDs_Test(1)]) simp
next
  case (MTestPos \<phi>)
  then show ?case by (intro finite_subset[OF RPDs_Test(2)]) simp
next
  case (MTestNeg \<phi>)
  then show ?case by (intro finite_subset[OF RPDs_Test(3)]) simp
next
  case (MPlus r s)
  then show ?case by (intro finite_subset[OF RPDs_Plus]) simp
next
  case (MTimes r s)
  then show ?case by (intro finite_subset[OF RPDs_Times]) (simp add: MTimesL_def)
next
  case (MStar r)
  then show ?case by (intro finite_subset[OF RPDs_Star]) (simp add: MTimesL_def)
qed

context begin

private abbreviation (input) "addRPD r \<equiv> \<lambda>S. insert r S \<union> UNION (insert r S) RPD"

private lemma mono_addRPD: "mono (addRPD r)"
  unfolding mono_def by auto

private lemma RPDs_aux1: "lfp (addRPD r) \<subseteq> RPDs r"
  by (rule lfp_induct[OF mono_addRPD], auto intro: RPDs_refl RPDs_trans)

private lemma RPDs_aux2: "RPDi i r \<subseteq> lfp (addRPD r)"
proof (induct i)
  case 0
  then show ?case
    by (subst lfp_unfold[OF mono_addRPD]) auto
next
  case (Suc i)
  then show ?case
    by (subst lfp_unfold[OF mono_addRPD]) (auto simp: RPDi_Suc_alt simp del: RPDi.simps)
qed

lemma RPDs_alt: "RPDs r = lfp (addRPD r)"
  using RPDs_aux1 RPDs_aux2 by (force simp: RPDs_def)

lemma RPDs_code[code]:
  "RPDs r = saturate (addRPD r) {}"
  unfolding RPDs_alt saturate_def
  by (rule lfp_while[OF mono_addRPD _ finite_RPDs, of r]) (auto simp: RPDs_refl RPDs_trans)

end

subsection \<open>The Executable Monitor\<close>

type_synonym ts = nat

type_synonym 'a mbuf2 = "'a table list \<times> 'a table list"
type_synonym 'a mbufn = "'a table list list"
type_synonym 'a msaux = "(ts \<times> 'a table) list"
type_synonym 'a muaux = "(ts \<times> 'a table \<times> 'a table) list"
type_synonym 'a mr\<delta>aux = "(ts \<times> (mregex, 'a table) mapping) list"
type_synonym 'a ml\<delta>aux = "(ts \<times> 'a table list \<times> 'a table) list"

datatype 'a mformula =
    MRel "'a table"
  | MPred MFOTL.name "'a MFOTL.trm list"
  | MAnd "'a mformula" bool "'a mformula" "'a mbuf2"
  | MOr "'a mformula" "'a mformula" "'a mbuf2"
  | MNeg "'a mformula"
  | MExists "'a mformula"
  | MPrev \<I> "'a mformula" bool "'a table list" "ts list"
  | MNext \<I> "'a mformula" bool "ts list"
  | MSince bool "'a mformula" \<I> "'a mformula" "'a mbuf2" "ts list" "'a msaux"
  | MUntil bool "'a mformula" \<I> "'a mformula" "'a mbuf2" "ts list" "'a muaux"
  | MMatchP \<I> "mregex" "mregex list" "'a mformula list" "'a mbufn" "ts list" "'a mr\<delta>aux"
  | MMatchF \<I> "mregex" "mregex list" "'a mformula list" "'a mbufn" "ts list" "'a ml\<delta>aux"

record 'a mstate =
  mstate_i :: nat
  mstate_m :: "'a mformula"
  mstate_n :: nat

fun eq_rel :: "nat \<Rightarrow> 'a MFOTL.trm \<Rightarrow> 'a MFOTL.trm \<Rightarrow> 'a table" where
  "eq_rel n (MFOTL.Const x) (MFOTL.Const y) = (if x = y then unit_table n else empty_table)"
| "eq_rel n (MFOTL.Var x) (MFOTL.Const y) = singleton_table n x y"
| "eq_rel n (MFOTL.Const x) (MFOTL.Var y) = singleton_table n y x"
| "eq_rel n (MFOTL.Var x) (MFOTL.Var y) = undefined"

fun neq_rel :: "nat \<Rightarrow> 'a MFOTL.trm \<Rightarrow> 'a MFOTL.trm \<Rightarrow> 'a table" where
  "neq_rel n (MFOTL.Const x) (MFOTL.Const y) = (if x = y then empty_table else unit_table n)"
| "neq_rel n (MFOTL.Var x) (MFOTL.Var y) = (if x = y then empty_table else undefined)"
| "neq_rel _ _ _ = undefined"

lemma atms_size: "x \<in> atms r \<Longrightarrow> size x < size r"
  by (induct r) (auto split: if_splits formula.splits)

function (sequential) minit0 :: "nat \<Rightarrow> 'a MFOTL.formula \<Rightarrow> 'a mformula" where
  "minit0 n (MFOTL.Neg \<phi>) = (case \<phi> of
    MFOTL.Eq t1 t2 \<Rightarrow> MRel (neq_rel n t1 t2)
  | MFOTL.Or (MFOTL.Neg \<phi>) \<psi> \<Rightarrow> (if safe_formula \<psi> \<and> MFOTL.fv \<psi> \<subseteq> MFOTL.fv \<phi>
      then MAnd (minit0 n \<phi>) False (minit0 n \<psi>) ([], [])
      else (case \<psi> of MFOTL.Neg \<psi> \<Rightarrow> MAnd (minit0 n \<phi>) True (minit0 n \<psi>) ([], []) | \<psi> \<Rightarrow> MNeg (minit0 n (MFOTL.Or (MFOTL.Neg \<phi>) \<psi>))))
  | \<phi> \<Rightarrow> MNeg (minit0 n \<phi>))"
| "minit0 n (MFOTL.Eq t1 t2) = MRel (eq_rel n t1 t2)"
| "minit0 n (MFOTL.Pred e ts) = MPred e ts"
| "minit0 n (MFOTL.Or \<phi> \<psi>) = MOr (minit0 n \<phi>) (minit0 n \<psi>) ([], [])"
| "minit0 n (MFOTL.Exists \<phi>) = MExists (minit0 (Suc n) \<phi>)"
| "minit0 n (MFOTL.Prev I \<phi>) = MPrev I (minit0 n \<phi>) True [] []"
| "minit0 n (MFOTL.Next I \<phi>) = MNext I (minit0 n \<phi>) True []"
| "minit0 n (MFOTL.Since \<phi> I \<psi>) = (if safe_formula \<phi>
    then MSince True (minit0 n \<phi>) I (minit0 n \<psi>) ([], []) [] []
    else (case \<phi> of
      MFOTL.Neg \<phi> \<Rightarrow> MSince False (minit0 n \<phi>) I (minit0 n \<psi>) ([], []) [] []
    | _ \<Rightarrow> undefined))"
| "minit0 n (MFOTL.Until \<phi> I \<psi>) = (if safe_formula \<phi>
    then MUntil True (minit0 n \<phi>) I (minit0 n \<psi>) ([], []) [] []
    else (case \<phi> of
      MFOTL.Neg \<phi> \<Rightarrow> MUntil False (minit0 n \<phi>) I (minit0 n \<psi>) ([], []) [] []
    | _ \<Rightarrow> undefined))"
| "minit0 n (MFOTL.MatchP I r) =
    (let (mr, \<phi>s) = to_mregex r
    in MMatchP I mr (sorted_list_of_set (RPDs mr)) (map (minit0 n) \<phi>s) (replicate (length \<phi>s) []) [] [])"
| "minit0 n (MFOTL.MatchF I r) = 
    (let (mr, \<phi>s) = to_mregex r
    in MMatchF I mr (sorted_list_of_set (LPDs mr)) (map (minit0 n) \<phi>s) (replicate (length \<phi>s) []) [] [])"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(_, \<phi>). size \<phi>)")
    (auto dest!: to_mregex_ok[OF sym] atms_size)

definition minit :: "'a MFOTL.formula \<Rightarrow> 'a mstate" where
  "minit \<phi> = (let n = MFOTL.nfv \<phi> in \<lparr>mstate_i = 0, mstate_m = minit0 n \<phi>, mstate_n = n\<rparr>)"

fun mprev_next :: "\<I> \<Rightarrow> 'a table list \<Rightarrow> ts list \<Rightarrow> 'a table list \<times> 'a table list \<times> ts list" where
  "mprev_next I [] ts = ([], [], ts)"
| "mprev_next I xs [] = ([], xs, [])"
| "mprev_next I xs [t] = ([], xs, [t])"
| "mprev_next I (x # xs) (t # t' # ts) = (let (ys, zs) = mprev_next I xs (t' # ts)
    in ((if mem (t' - t) I then x else empty_table) # ys, zs))"

fun mbuf2_add :: "'a table list \<Rightarrow> 'a table list \<Rightarrow> 'a mbuf2 \<Rightarrow> 'a mbuf2" where
 "mbuf2_add xs' ys' (xs, ys) = (xs @ xs', ys @ ys')"

fun mbuf2_take :: "('a table \<Rightarrow> 'a table \<Rightarrow> 'b) \<Rightarrow> 'a mbuf2 \<Rightarrow> 'b list \<times> 'a mbuf2" where
  "mbuf2_take f (x # xs, y # ys) = (let (zs, buf) = mbuf2_take f (xs, ys) in (f x y # zs, buf))"
| "mbuf2_take f (xs, ys) = ([], (xs, ys))"

fun mbuf2t_take :: "('a table \<Rightarrow> 'a table \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow>
  'a mbuf2 \<Rightarrow> ts list \<Rightarrow> 'b \<times> 'a mbuf2 \<times> ts list" where
  "mbuf2t_take f z (x # xs, y # ys) (t # ts) = mbuf2t_take f (f x y t z) (xs, ys) ts"
| "mbuf2t_take f z (xs, ys) ts = (z, (xs, ys), ts)"

lemma size_list_length_diff1: "[] \<notin> set xs \<Longrightarrow> size_list (\<lambda>xs. length xs - Suc 0) xs \<le> size_list length xs"
proof (induct xs)
  case (Cons x xs)
  then show ?case
    by (cases xs) auto
qed simp

fun mbufn_add :: "'a table list list \<Rightarrow> 'a mbufn \<Rightarrow> 'a mbufn" where
 "mbufn_add xs' xs = List.map2 (@) xs xs'"

fun mbufnt_take :: "('a table list \<Rightarrow> ts \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>
    'b \<Rightarrow> 'a mbufn \<Rightarrow> ts list \<Rightarrow> 'b \<times> 'a mbufn \<times> ts list" where
  "mbufnt_take f z buf ts =
    (if [] \<in> set buf \<or> ts = [] then (z, buf, ts) 
    else mbufnt_take f (f (map hd buf) (hd ts) z) (map tl buf) (tl ts))"

fun match :: "'a MFOTL.trm list \<Rightarrow> 'a list \<Rightarrow> (nat \<rightharpoonup> 'a) option" where
  "match [] [] = Some Map.empty"
| "match (MFOTL.Const x # ts) (y # ys) = (if x = y then match ts ys else None)"
| "match (MFOTL.Var x # ts) (y # ys) = (case match ts ys of
      None \<Rightarrow> None
    | Some f \<Rightarrow> (case f x of
        None \<Rightarrow> Some (f(x \<mapsto> y))
      | Some z \<Rightarrow> if y = z then Some f else None))"
| "match _ _ = None"

definition update_since :: "\<I> \<Rightarrow> bool \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> ts \<Rightarrow>
  'a msaux \<Rightarrow> 'a table \<times> 'a msaux" where
  "update_since I pos rel1 rel2 nt aux =
    (let aux = (case [(t, join rel pos rel1). (t, rel) \<leftarrow> aux] of
        [] \<Rightarrow> [(nt, rel2)]
      | x # aux' \<Rightarrow> (if fst x = nt then (fst x, snd x \<union> rel2) # aux' else (nt, rel2) # x # aux'))
    in (foldr (\<union>) [rel. (t, rel) \<leftarrow> aux, nt - t \<le> right I, left I \<le> nt - t] {}, filter (\<lambda>(t, _). enat (nt - t) \<le> right I) aux))"

abbreviation "lookup \<equiv> Mapping.lookup_default empty_table"

fun unsafe_\<epsilon> where
  "unsafe_\<epsilon> guard \<phi>s MWild = empty_table"
| "unsafe_\<epsilon> guard \<phi>s MEps = guard"
| "unsafe_\<epsilon> guard \<phi>s (MTestPos i) = join guard True (\<phi>s ! i)"
| "unsafe_\<epsilon> guard \<phi>s (MTestNeg i) = join guard False (\<phi>s ! i)"
| "unsafe_\<epsilon> guard \<phi>s (MPlus r s) = unsafe_\<epsilon> guard \<phi>s r \<union> unsafe_\<epsilon> guard \<phi>s s"
| "unsafe_\<epsilon> guard \<phi>s (MTimes r s) = join (unsafe_\<epsilon> guard \<phi>s r) True (unsafe_\<epsilon> guard \<phi>s s)"
| "unsafe_\<epsilon> guard \<phi>s (MStar r) = guard"

fun safe_r\<epsilon> where
  "safe_r\<epsilon> n \<phi>s MWild = empty_table"
| "safe_r\<epsilon> n \<phi>s MEps = unit_table n"
| "safe_r\<epsilon> n \<phi>s (MTestPos i) = \<phi>s ! i"
| "safe_r\<epsilon> n \<phi>s (MPlus r s) = safe_r\<epsilon> n \<phi>s r \<union> safe_r\<epsilon> n \<phi>s s"
| "safe_r\<epsilon> n \<phi>s (MTimes r s) = unsafe_\<epsilon> (safe_r\<epsilon> n \<phi>s r) \<phi>s s"
| "safe_r\<epsilon> n \<phi>s _ = undefined"

fun safe_l\<epsilon> where
  "safe_l\<epsilon> n \<phi>s MWild = empty_table"
| "safe_l\<epsilon> n \<phi>s MEps = unit_table n"
| "safe_l\<epsilon> n \<phi>s (MTestPos i) = \<phi>s ! i"
| "safe_l\<epsilon> n \<phi>s (MPlus r s) = safe_l\<epsilon> n \<phi>s r \<union> safe_l\<epsilon> n \<phi>s s"
| "safe_l\<epsilon> n \<phi>s (MTimes r s) = unsafe_\<epsilon> (safe_l\<epsilon> n \<phi>s s) \<phi>s r"
| "safe_l\<epsilon> n \<phi>s _ = undefined"

fun r\<delta> :: "(mregex \<Rightarrow> mregex) \<Rightarrow> (mregex, 'a table) mapping \<Rightarrow> 'a table list \<Rightarrow> mregex \<Rightarrow> 'a table"  where
  "r\<delta> \<kappa> X \<phi>s MWild = lookup X (\<kappa> MEps)"
| "r\<delta> \<kappa> X \<phi>s MEps = empty_table"
| "r\<delta> \<kappa> X \<phi>s (MTestPos i) = empty_table"
| "r\<delta> \<kappa> X \<phi>s (MTestNeg i) = empty_table"
| "r\<delta> \<kappa> X \<phi>s (MPlus r s) = r\<delta> \<kappa> X \<phi>s r \<union> r\<delta> \<kappa> X \<phi>s s"
| "r\<delta> \<kappa> X \<phi>s (MTimes r s) = r\<delta> (\<lambda>t. \<kappa> (MTimes r t)) X \<phi>s s \<union> unsafe_\<epsilon> (r\<delta> \<kappa> X \<phi>s r) \<phi>s s"
| "r\<delta> \<kappa> X \<phi>s (MStar r) = r\<delta> (\<lambda>t. \<kappa> (MTimes (MStar r) t)) X \<phi>s r"

fun l\<delta> :: "(mregex \<Rightarrow> mregex) \<Rightarrow> (mregex, 'a table) mapping \<Rightarrow> 'a table list \<Rightarrow> mregex \<Rightarrow> 'a table" where
  "l\<delta> \<kappa> X \<phi>s MWild = lookup X (\<kappa> MEps)"
| "l\<delta> \<kappa> X \<phi>s MEps = empty_table"
| "l\<delta> \<kappa> X \<phi>s (MTestPos i) = empty_table"
| "l\<delta> \<kappa> X \<phi>s (MTestNeg i) = empty_table"
| "l\<delta> \<kappa> X \<phi>s (MPlus r s) = l\<delta> \<kappa> X \<phi>s r \<union> l\<delta> \<kappa> X \<phi>s s"
| "l\<delta> \<kappa> X \<phi>s (MTimes r s) = l\<delta> (\<lambda>t. \<kappa> (MTimes t s)) X \<phi>s r \<union> unsafe_\<epsilon> (l\<delta> \<kappa> X \<phi>s s) \<phi>s r"
| "l\<delta> \<kappa> X \<phi>s (MStar r) = l\<delta> (\<lambda>t. \<kappa> (MTimes t (MStar r))) X \<phi>s r"

definition update_matchP :: "nat \<Rightarrow> \<I> \<Rightarrow> mregex \<Rightarrow> mregex list \<Rightarrow> 'a table list \<Rightarrow> ts \<Rightarrow>
  'a mr\<delta>aux \<Rightarrow> 'a table \<times> 'a mr\<delta>aux" where
  "update_matchP n I mr mrs rels nt aux =
    (let aux = (case [(t, Mapping.tabulate mrs (\<lambda>mr. 
        r\<delta> id rel rels mr \<union> (if t = nt then safe_r\<epsilon> n rels mr else {}))). 
      (t, rel) \<leftarrow> aux, enat (nt - t) \<le> right I]
      of [] \<Rightarrow> [(nt, Mapping.tabulate mrs (safe_r\<epsilon> n rels))]
      | x # aux' \<Rightarrow> (if fst x = nt then x # aux'
                     else (nt, Mapping.tabulate mrs (safe_r\<epsilon> n rels)) # x # aux'))
    in (foldr (\<union>) [lookup rel mr. (t, rel) \<leftarrow> aux, left I \<le> nt - t] {}, aux))"

definition update_until :: "\<I> \<Rightarrow> bool \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> ts \<Rightarrow> 'a muaux \<Rightarrow> 'a muaux" where
  "update_until I pos rel1 rel2 nt aux =
    (map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if mem (nt - t) I then a2 \<union> join rel2 pos a1 else a2)) aux) @
    [(nt, rel1, if left I = 0 then rel2 else empty_table)]"

fun eval_until :: "\<I> \<Rightarrow> ts \<Rightarrow> 'a muaux \<Rightarrow> 'a table list \<times> 'a muaux" where
  "eval_until I nt [] = ([], [])"
| "eval_until I nt ((t, a1, a2) # aux) = (if t + right I < nt then
    (let (xs, aux) = eval_until I nt aux in (a2 # xs, aux)) else ([], (t, a1, a2) # aux))"

definition update_matchF_base where
  "update_matchF_base n I mr mrs rels nt =
     (let X = Mapping.tabulate mrs (safe_l\<epsilon> n rels)
     in ([(nt, rels, if left I = 0 then lookup X mr else empty_table)], X))"

definition update_matchF_step where
  "update_matchF_step I mr mrs nt = (\<lambda>(t, rels', rel) (aux', X).
     (let Y = Mapping.tabulate mrs (l\<delta> id X rels')
     in ((t, rels', if mem (nt - t) I then rel \<union> lookup Y mr else rel) # aux', Y)))"

definition update_matchF :: "nat \<Rightarrow> \<I> \<Rightarrow> mregex \<Rightarrow> mregex list \<Rightarrow> 'a table list \<Rightarrow> ts \<Rightarrow> 'a ml\<delta>aux \<Rightarrow> 'a ml\<delta>aux" where
  "update_matchF n I mr mrs rels nt aux =
     fst (foldr (update_matchF_step I mr mrs nt) aux (update_matchF_base n I mr mrs rels nt))"

fun eval_matchF :: "\<I> \<Rightarrow> mregex \<Rightarrow> ts \<Rightarrow> 'a ml\<delta>aux \<Rightarrow> 'a table list \<times> 'a ml\<delta>aux" where
  "eval_matchF I mr nt [] = ([], [])"
| "eval_matchF I mr nt ((t, rels, rel) # aux) = (if t + right I < nt then
    (let (xs, aux) = eval_matchF I mr nt aux in (rel # xs, aux)) else ([], (t, rels, rel) # aux))"

primrec map_split where
  "map_split f [] = ([], [])"
| "map_split f (x # xs) =
    (let (y, z) = f x; (ys, zs) = map_split f xs
    in (y # ys, z # zs))"

primrec meval :: "nat \<Rightarrow> ts \<Rightarrow> 'a MFOTL.database \<Rightarrow> 'a mformula \<Rightarrow> 'a table list \<times> 'a mformula" where
  "meval n t db (MRel rel) = ([rel], MRel rel)"
| "meval n t db (MPred e ts) = ([(\<lambda>f. tabulate f 0 n) ` Option.these
    (match ts ` (\<Union>(e', x)\<in>db. if e = e' then {x} else {}))], MPred e ts)"
| "meval n t db (MAnd \<phi> pos \<psi> buf) =
    (let (xs, \<phi>) = meval n t db \<phi>; (ys, \<psi>) = meval n t db \<psi>;
      (zs, buf) = mbuf2_take (\<lambda>r1 r2. join r1 pos r2) (mbuf2_add xs ys buf)
    in (zs, MAnd \<phi> pos \<psi> buf))"
| "meval n t db (MOr \<phi> \<psi> buf) =
    (let (xs, \<phi>) = meval n t db \<phi>; (ys, \<psi>) = meval n t db \<psi>;
      (zs, buf) = mbuf2_take (\<lambda>r1 r2. r1 \<union> r2) (mbuf2_add xs ys buf)
    in (zs, MOr \<phi> \<psi> buf))"
| "meval n t db (MNeg \<phi>) =
    (let (xs, \<phi>) = meval n t db \<phi> in (map (\<lambda>r. (if r = empty_table then unit_table n else empty_table)) xs, MNeg \<phi>))"
| "meval n t db (MExists \<phi>) =
    (let (xs, \<phi>) = meval (Suc n) t db \<phi> in (map (\<lambda>r. tl ` r) xs, MExists \<phi>))"
| "meval n t db (MPrev I \<phi> first buf nts) =
    (let (xs, \<phi>) = meval n t db \<phi>;
      (zs, buf, nts) = mprev_next I (buf @ xs) (nts @ [t])
    in (if first then empty_table # zs else zs, MPrev I \<phi> False buf nts))"
| "meval n t db (MNext I \<phi> first nts) =
    (let (xs, \<phi>) = meval n t db \<phi>;
      (xs, first) = (case (xs, first) of (_ # xs, True) \<Rightarrow> (xs, False) | a \<Rightarrow> a);
      (zs, _, nts) = mprev_next I xs (nts @ [t])
    in (zs, MNext I \<phi> first nts))"
| "meval n t db (MSince pos \<phi> I \<psi> buf nts aux) =
    (let (xs, \<phi>) = meval n t db \<phi>; (ys, \<psi>) = meval n t db \<psi>;
      ((zs, aux), buf, nts) = mbuf2t_take (\<lambda>r1 r2 t (zs, aux).
        let (z, aux) = update_since I pos r1 r2 t aux
        in (zs @ [z], aux)) ([], aux) (mbuf2_add xs ys buf) (nts @ [t])
    in (zs, MSince pos \<phi> I \<psi> buf nts aux))"
| "meval n t db (MUntil pos \<phi> I \<psi> buf nts aux) =
    (let (xs, \<phi>) = meval n t db \<phi>; (ys, \<psi>) = meval n t db \<psi>;
      (aux, buf, nts) = mbuf2t_take (update_until I pos) aux (mbuf2_add xs ys buf) (nts @ [t]);
      (zs, aux) = eval_until I (case nts of [] \<Rightarrow> t | nt # _ \<Rightarrow> nt) aux
    in (zs, MUntil pos \<phi> I \<psi> buf nts aux))"
| "meval n t db (MMatchP I mr mrs \<phi>s buf nts aux) =
    (let (xss, \<phi>s) = map_split id (map (meval n t db) \<phi>s);
      ((zs, aux), buf, nts) = mbufnt_take (\<lambda>rels t (zs, aux).
        let (z, aux) = update_matchP n I mr mrs rels t aux
        in (zs @ [z], aux)) ([], aux) (mbufn_add xss buf) (nts @ [t])
    in (zs, MMatchP I mr mrs \<phi>s buf nts aux))"
| "meval n t db (MMatchF I mr mrs \<phi>s buf nts aux) =
    (let (xss, \<phi>s) = map_split id (map (meval n t db) \<phi>s);
      (aux, buf, nts) = mbufnt_take (update_matchF n I mr mrs) aux (mbufn_add xss buf) (nts @ [t]);
      (zs, aux) = eval_matchF I mr (case nts of [] \<Rightarrow> t | nt # _ \<Rightarrow> nt) aux 
    in (zs, MMatchF I mr mrs \<phi>s buf nts aux))"

definition mstep :: "'a MFOTL.database \<times> ts \<Rightarrow> 'a mstate \<Rightarrow> (nat \<times> 'a tuple) set \<times> 'a mstate" where
  "mstep tdb st =
     (let (xs, m) = meval (mstate_n st) (snd tdb) (fst tdb) (mstate_m st)
     in (\<Union> (set (map (\<lambda>(i, X). (\<lambda>v. (i, v)) ` X) (List.enumerate (mstate_i st) xs))),
      \<lparr>mstate_i = mstate_i st + length xs, mstate_m = m, mstate_n = mstate_n st\<rparr>))"

lemma mstep_alt: "mstep tdb st =
     (let (xs, m) = meval (mstate_n st) (snd tdb) (fst tdb) (mstate_m st)
     in (\<Union>(i, X) \<in> set (List.enumerate (mstate_i st) xs). \<Union>v \<in> X. {(i,v)},
      \<lparr>mstate_i = mstate_i st + length xs, mstate_m = m, mstate_n = mstate_n st\<rparr>))"
  unfolding mstep_def
  by (auto split: prod.split)


subsection \<open>Verdict Delay\<close>

lemmas formula_atms_induct = formula.induct[where ?P1.0 = P and 
  ?P2.0 = "\<lambda>r. \<forall>\<phi> \<in> atms r. P \<phi>" for P,
  case_names Pred Eq Neg Or Exists Prev Next Since Until MatchF MatchP Wild Test Plus Times Star]

lemma atms_size_estimation[termination_simp]: "x \<in> atms r \<Longrightarrow> size x < Suc (size r)"
  by (induct r) (auto split: if_splits formula.splits)

fun progress :: "'a MFOTL.trace \<Rightarrow> 'a MFOTL.formula \<Rightarrow> nat \<Rightarrow> nat"
and progress_regex :: "'a MFOTL.trace \<Rightarrow> 'a MFOTL.regex \<Rightarrow> nat \<Rightarrow> nat" where
  "progress \<sigma> (MFOTL.Pred e ts) j = j"
| "progress \<sigma> (MFOTL.Eq t1 t2) j = j"
| "progress \<sigma> (MFOTL.Neg \<phi>) j = progress \<sigma> \<phi> j"
| "progress \<sigma> (MFOTL.Or \<phi> \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
| "progress \<sigma> (MFOTL.Exists \<phi>) j = progress \<sigma> \<phi> j"
| "progress \<sigma> (MFOTL.Prev I \<phi>) j = (if j = 0 then 0 else min (Suc (progress \<sigma> \<phi> j)) j)"
| "progress \<sigma> (MFOTL.Next I \<phi>) j = progress \<sigma> \<phi> j - 1"
| "progress \<sigma> (MFOTL.Since \<phi> I \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
| "progress \<sigma> (MFOTL.Until \<phi> I \<psi>) j =
    Inf {i. \<forall>k. k < j \<and> k \<le> min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j) \<longrightarrow> \<tau> \<sigma> i + right I \<ge> \<tau> \<sigma> k}"
| "progress \<sigma> (MFOTL.MatchP I r) j = progress_regex \<sigma> r j"
| "progress \<sigma> (MFOTL.MatchF I r) j =
    Inf {i. \<forall>k. k < j \<and> k \<le> progress_regex \<sigma> r j \<longrightarrow> \<tau> \<sigma> i + right I \<ge> \<tau> \<sigma> k}"
| "progress_regex \<sigma> MFOTL.Wild j = j"
| "progress_regex \<sigma> (MFOTL.Test \<phi>) j = progress \<sigma> \<phi> j"
| "progress_regex \<sigma> (MFOTL.Plus r s) j = min (progress_regex \<sigma> r j) (progress_regex \<sigma> s j)"
| "progress_regex \<sigma> (MFOTL.Times r s) j = min (progress_regex \<sigma> r j) (progress_regex \<sigma> s j)"
| "progress_regex \<sigma> (MFOTL.Star r) j = progress_regex \<sigma> r j"

lemma progress_And[simp]: "progress \<sigma> (MFOTL.And \<phi> \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
  unfolding MFOTL.And_def by simp

lemma progress_And_Not[simp]: "progress \<sigma> (MFOTL.And_Not \<phi> \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
  unfolding MFOTL.And_Not_def by simp

lemma
  progress_mono: "j \<le> j' \<Longrightarrow> progress \<sigma> \<phi> j \<le> progress \<sigma> \<phi> j'" and
  progress_regex_mono: "j \<le> j' \<Longrightarrow> progress_regex \<sigma> r j \<le> progress_regex \<sigma> r j'"
proof (induction \<phi> and r)
  case (Until \<phi> I \<psi>)
  then show ?case
    by (cases "right I")
      (auto dest: trans_le_add1[OF \<tau>_mono] intro!: cInf_superset_mono)
next
  case (MatchF I r)
  then show ?case
    by (cases "right I")
      (auto dest: trans_le_add1[OF \<tau>_mono] intro!: cInf_superset_mono)
qed auto

lemma progress_le: "progress \<sigma> \<phi> j \<le> j" and progress_regex_le: "progress_regex \<sigma> r j \<le> j"
proof (induction \<phi> and r)
  case (Until \<phi> I \<psi>)
  then show ?case
    by (cases "right I")
      (auto intro: trans_le_add1[OF \<tau>_mono] intro!: cInf_lower)
next
  case (MatchF I r)
  then show ?case
    by (cases "right I")
      (auto intro: trans_le_add1[OF \<tau>_mono] intro!: cInf_lower)
qed auto

lemma progress_0[simp]: "progress \<sigma> \<phi> 0 = 0"
  using progress_le by auto

lemma progress_regex_0[simp]: "progress_regex \<sigma> r 0 = 0"
  using progress_regex_le by auto

lemma
  progress_ge: "MFOTL.future_reach \<phi> \<noteq> \<infinity> \<Longrightarrow> \<exists>j. i \<le> progress \<sigma> \<phi> j" and
  progress_regex_ge: "MFOTL.future_reach_regex r \<noteq> \<infinity> \<Longrightarrow> \<exists>j. i \<le> progress_regex \<sigma> r j"
proof (induction \<phi> and r arbitrary: i and i)
  case (Pred e ts)
  then show ?case by auto
next
  case (Eq t1 t2)
  then show ?case by auto
next
  case (Neg \<phi>)
  then show ?case by simp
next
  case (Or \<phi>1 \<phi>2)
  from Or.prems have "MFOTL.future_reach \<phi>1 \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach \<phi>1") (auto)
  moreover from Or.prems have "MFOTL.future_reach \<phi>2 \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach \<phi>2") (auto)
  ultimately obtain j1 j2 where "i \<le> progress \<sigma> \<phi>1 j1" and "i \<le> progress \<sigma> \<phi>2 j2"
    using Or.IH[of i] by blast
  then have "i \<le> progress \<sigma> (MFOTL.Or \<phi>1 \<phi>2) (max j1 j2)"
    by (cases "j1 \<le> j2") (auto elim!: order.trans[OF _ progress_mono])
  then show ?case by blast
next
  case (Exists \<phi>)
  then show ?case by simp
next
  case (Prev I \<phi>)
  from Prev.prems have "MFOTL.future_reach \<phi> \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach \<phi>") (auto)
  then obtain j where "i \<le> progress \<sigma> \<phi> j"
    using Prev.IH[of i] by blast
  then show ?case by (auto intro!: exI[of _ j] elim!: order.trans[OF _ progress_le])
next
  case (Next I \<phi>)
  from Next.prems have "MFOTL.future_reach \<phi> \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach \<phi>") (auto)
  then obtain j where "Suc i \<le> progress \<sigma> \<phi> j"
    using Next.IH[of "Suc i"] by blast
  then show ?case by (auto intro!: exI[of _ j])
next
  case (Since \<phi>1 I \<phi>2)
  from Since.prems have "MFOTL.future_reach \<phi>1 \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach \<phi>1") (auto)
  moreover from Since.prems have "MFOTL.future_reach \<phi>2 \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach \<phi>2") (auto)
  ultimately obtain j1 j2 where "i \<le> progress \<sigma> \<phi>1 j1" and "i \<le> progress \<sigma> \<phi>2 j2"
    using Since.IH[of i] by blast
  then have "i \<le> progress \<sigma> (MFOTL.Since \<phi>1 I \<phi>2) (max j1 j2)"
    by (cases "j1 \<le> j2") (auto elim!: order.trans[OF _ progress_mono])
  then show ?case by blast
next
  case (Until \<phi>1 I \<phi>2)
  from Until.prems obtain b where [simp]: "right I = enat b"
    by (cases "right I") (auto)
  obtain i' where "i < i'" and "\<tau> \<sigma> i + b + 1 \<le> \<tau> \<sigma> i'"
    using ex_le_\<tau>[where x="\<tau> \<sigma> i + b + 1"] by (auto simp add: less_eq_Suc_le)
  then have 1: "\<tau> \<sigma> i + b < \<tau> \<sigma> i'" by simp
  from Until.prems have "MFOTL.future_reach \<phi>1 \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach \<phi>1") (auto)
  moreover from Until.prems have "MFOTL.future_reach \<phi>2 \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach \<phi>2") (auto)
  ultimately obtain j1 j2 where "Suc i' \<le> progress \<sigma> \<phi>1 j1" and "Suc i' \<le> progress \<sigma> \<phi>2 j2"
    using Until.IH[of "Suc i'"] by blast
  then have "i \<le> progress \<sigma> (MFOTL.Until \<phi>1 I \<phi>2) (max j1 j2)"
    unfolding progress.simps
  proof (intro cInf_greatest, goal_cases nonempty greatest)
    case nonempty
    then show ?case
      by (auto simp: trans_le_add1[OF \<tau>_mono] intro!: exI[of _ "max j1 j2"])
  next
    case (greatest x)
    with \<open>i < i'\<close> 1 show ?case
      by (cases "j1 \<le> j2")
        (auto dest!: spec[of _ i'] simp: max_absorb1 max_absorb2 less_eq_Suc_le
          elim: order.trans[OF _ progress_le] order.trans[OF _ progress_mono, rotated]
          dest!: not_le_imp_less[THEN less_imp_le] intro!: less_\<tau>D[THEN less_imp_le, of \<sigma> i x])
  qed
  then show ?case by blast
next
  case (MatchP I r)
  then show ?case
    by (cases "MFOTL.future_reach_regex r") auto
next
  case (MatchF I r)
  from MatchF.prems obtain b where "right I = enat b"
    by (auto simp: plus_eq_enat_iff)
  moreover
  obtain i' where "i < i'" and "\<tau> \<sigma> i + b + 1 \<le> \<tau> \<sigma> i'"
    using ex_le_\<tau>[where x="\<tau> \<sigma> i + b + 1"] by (auto simp add: less_eq_Suc_le)
  then have 1: "\<tau> \<sigma> i + b < \<tau> \<sigma> i'" by simp
  moreover
  from MatchF.prems have "MFOTL.future_reach_regex r \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach_regex r") auto
  with MatchF obtain j where "Suc i' \<le> progress_regex \<sigma> r j"
    by auto
  moreover have "i \<le> x" if "\<tau> \<sigma> i' \<le> b + \<tau> \<sigma> x" "b + \<tau> \<sigma> i < \<tau> \<sigma> i'" for x
    using less_\<tau>D[of \<sigma> i] that less_le_trans by fastforce
  ultimately show ?case using \<open>i < i'\<close> progress_regex_le[of \<sigma> r j] \<tau>_mono[of _ j \<sigma>] less_\<tau>D[of \<sigma> i] 
    by (auto 0 3 intro!: exI[of _ "j"] cInf_greatest simp: ac_simps Suc_le_eq trans_le_add2
      dest: spec[of _ "i'"] spec[of _ j])
next
  case (Plus r s)
  from Plus.prems have "MFOTL.future_reach_regex r \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach_regex r") (auto)
  moreover from Plus.prems have "MFOTL.future_reach_regex s \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach_regex s") (auto)
  ultimately obtain j1 j2 where "i \<le> progress_regex \<sigma> r j1" and "i \<le> progress_regex \<sigma> s j2"
    using Plus.IH[of i] by blast
  then have "i \<le> progress_regex \<sigma> (MFOTL.Plus r s) (max j1 j2)"
    by (cases "j1 \<le> j2") (auto elim!: order.trans[OF _ progress_regex_mono])
  then show ?case by blast
next
  case (Times r s)
  from Times.prems have "MFOTL.future_reach_regex r \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach_regex r") (auto)
  moreover from Times.prems have "MFOTL.future_reach_regex s \<noteq> \<infinity>"
    by (cases "MFOTL.future_reach_regex s") (auto)
  ultimately obtain j1 j2 where "i \<le> progress_regex \<sigma> r j1" and "i \<le> progress_regex \<sigma> s j2"
    using Times.IH[of i] by blast
  then have "i \<le> progress_regex \<sigma> (MFOTL.Times r s) (max j1 j2)"
    by (cases "j1 \<le> j2") (auto elim!: order.trans[OF _ progress_regex_mono])
  then show ?case by blast
qed auto

lemma cInf_restrict_nat:
  fixes x :: nat
  assumes "x \<in> A"
  shows "Inf A = Inf {y \<in> A. y \<le> x}"
  using assms by (auto intro!: antisym intro: cInf_greatest cInf_lower Inf_nat_def1)

lemma
  assumes "\<forall>i<j. \<tau> \<sigma> i = \<tau> \<sigma>' i"
  shows progress_time_conv: "progress \<sigma> \<phi> j = progress \<sigma>' \<phi> j" and
    progress_regex_time_conv: "progress_regex \<sigma> r j = progress_regex \<sigma>' r j"
proof (induction \<phi> and r)
  case (Until \<phi>1 I \<phi>2)
  have *: "i \<le> j - 1 \<longleftrightarrow> i < j" if "j \<noteq> 0" for i
    using that by auto
  with Until show ?case
  proof (cases "right I")
    case (enat b)
    then show ?thesis
    proof (cases "j")
      case (Suc n)
      with enat * Until show ?thesis
        using assms \<tau>_mono[THEN trans_le_add1]
        by (auto 6 0
          intro!: box_equals[OF arg_cong[where f=Inf]
            cInf_restrict_nat[symmetric, where x=n] cInf_restrict_nat[symmetric, where x=n]])
    qed simp
  qed simp
next
  case (MatchF I r)
  have *: "i \<le> j - 1 \<longleftrightarrow> i < j" if "j \<noteq> 0" for i
    using that by auto
  with MatchF show ?case using assms \<tau>_mono[THEN trans_le_add1]
    by (cases "right I"; cases j)
      ((auto 6 0 intro!: box_equals[OF arg_cong[where f=Inf]
      cInf_restrict_nat[symmetric, where x="j-1"] cInf_restrict_nat[symmetric, where x="j-1"]]) [])+
qed auto

lemma Inf_UNIV_nat: "(Inf UNIV :: nat) = 0"
  by (simp add: cInf_eq_minimum)

lemma progress_prefix_conv:
  assumes "prefix_of \<pi> \<sigma>" and "prefix_of \<pi> \<sigma>'"
  shows "progress \<sigma> \<phi> (plen \<pi>) = progress \<sigma>' \<phi> (plen \<pi>)"
  using assms by (auto intro: progress_time_conv \<tau>_prefix_conv)

lemma progress_regex_prefix_conv:
  assumes "prefix_of \<pi> \<sigma>" and "prefix_of \<pi> \<sigma>'"
  shows "progress_regex \<sigma> r (plen \<pi>) = progress_regex \<sigma>' r (plen \<pi>)"
  using assms by (auto intro: progress_regex_time_conv \<tau>_prefix_conv)

lemma bounded_rtranclp_mono:
  fixes n :: "'a :: linorder"
  assumes "\<And>i j. R i j \<Longrightarrow> j < n \<Longrightarrow> S i j" "\<And>i j. R i j \<Longrightarrow> i \<le> j"
  shows "rtranclp R i j \<Longrightarrow> j < n \<Longrightarrow> rtranclp S i j"
proof (induct rule: rtranclp_induct)
  case (step y z)
  then show ?case
    using assms(1,2)[of y z]
    by (auto elim!: rtrancl_into_rtrancl[to_pred, rotated])
qed auto

lemma
  assumes "prefix_of \<pi> \<sigma>" and "prefix_of \<pi> \<sigma>'"
  shows sat_prefix_conv: "i < progress \<sigma> \<phi> (plen \<pi>) \<Longrightarrow> MFOTL.sat \<sigma> v i \<phi> \<longleftrightarrow> MFOTL.sat \<sigma>' v i \<phi>"
    and match_prefix_conv: "j < progress_regex \<sigma> r (plen \<pi>) \<Longrightarrow> MFOTL.match \<sigma> v r i j \<longleftrightarrow> MFOTL.match \<sigma>' v r i j"
proof (induction \<phi> and r arbitrary: v i and v i j)
  case (Pred e ts)
  with \<Gamma>_prefix_conv[OF assms(1,2)] show ?case by simp
next
  case (Eq t1 t2)
  show ?case by simp
next
  case (Neg \<phi>)
  then show ?case by simp
next
  case (Or \<phi>1 \<phi>2)
  then show ?case by simp
next
  case (Exists \<phi>)
  then show ?case by simp
next
  case (Prev I \<phi>)
  with \<tau>_prefix_conv[OF assms(1,2)] show ?case
    by (cases i) (auto split: if_splits)
next
  case (Next I \<phi>)
  then have "Suc i < plen \<pi>"
    by (auto intro: order.strict_trans2[OF _ progress_le[of \<sigma> \<phi>]])
  with Next \<tau>_prefix_conv[OF assms(1,2)] show ?case by simp
next
  case (Since \<phi>1 I \<phi>2)
  then have "i < plen \<pi>"
    by (auto elim!: order.strict_trans2[OF _ progress_le])
  with Since \<tau>_prefix_conv[OF assms(1,2)] show ?case by auto
next
  case (Until \<phi>1 I \<phi>2)
  from Until.prems obtain b where [simp]: "right I = enat b"
    by (cases "right I") (auto simp add: Inf_UNIV_nat)
  from Until.prems obtain j where "\<tau> \<sigma> i + b + 1 \<le> \<tau> \<sigma> j"
    "j \<le> progress \<sigma> \<phi>1 (plen \<pi>)" "j \<le> progress \<sigma> \<phi>2 (plen \<pi>)"
    by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
      dest!: le_cInf_iff[THEN iffD1, rotated -1])
  then have 1: "k < progress \<sigma> \<phi>1 (plen \<pi>)" and 2: "k < progress \<sigma> \<phi>2 (plen \<pi>)"
    if "\<tau> \<sigma> k \<le> \<tau> \<sigma> i + b" for k
    using that by (fastforce elim!: order.strict_trans2[rotated] intro: less_\<tau>D[of \<sigma>])+
  have 3: "k < plen \<pi>" if "\<tau> \<sigma> k \<le> \<tau> \<sigma> i + b" for k
    using 1[OF that] by (simp add: less_eq_Suc_le order.trans[OF _ progress_le])

  from Until.prems have "i < progress \<sigma>' (MFOTL.Until \<phi>1 I \<phi>2) (plen \<pi>)"
    unfolding progress_prefix_conv[OF assms(1,2)] .
  then obtain j where "\<tau> \<sigma>' i + b + 1 \<le> \<tau> \<sigma>' j"
    "j \<le> progress \<sigma>' \<phi>1 (plen \<pi>)" "j \<le> progress \<sigma>' \<phi>2 (plen \<pi>)"
    by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
      dest!: le_cInf_iff[THEN iffD1, rotated -1])
  then have 11: "k < progress \<sigma> \<phi>1 (plen \<pi>)" and 21: "k < progress \<sigma> \<phi>2 (plen \<pi>)"
    if "\<tau> \<sigma>' k \<le> \<tau> \<sigma>' i + b" for k
    unfolding progress_prefix_conv[OF assms(1,2)]
    using that by (fastforce elim!: order.strict_trans2[rotated] intro: less_\<tau>D[of \<sigma>'])+
  have 31: "k < plen \<pi>" if "\<tau> \<sigma>' k \<le> \<tau> \<sigma>' i + b" for k
    using 11[OF that] by (simp add: less_eq_Suc_le order.trans[OF _ progress_le])

  show ?case unfolding sat.simps
  proof ((intro ex_cong iffI; elim conjE), goal_cases LR RL)
    case (LR j)
    with Until.IH(1)[OF 1] Until.IH(2)[OF 2] \<tau>_prefix_conv[OF assms(1,2) 3] show ?case
      by (auto 0 4 simp: le_diff_conv add.commute dest: less_imp_le order.trans[OF \<tau>_mono, rotated])
  next
    case (RL j)
    with Until.IH(1)[OF 11] Until.IH(2)[OF 21] \<tau>_prefix_conv[OF assms(1,2) 31] show ?case
      by (auto 0 4 simp: le_diff_conv add.commute dest: less_imp_le order.trans[OF \<tau>_mono, rotated])
  qed
next
  case (MatchP I r)
  then have "i < plen \<pi>"
    by (auto elim!: order.strict_trans2[OF _ progress_regex_le])
  with MatchP \<tau>_prefix_conv[OF assms(1,2)] show ?case by auto
next
  case (MatchF I r)
  from MatchF.prems obtain b where [simp]: "right I = enat b"
    by (cases "right I") (auto simp add: Inf_UNIV_nat)
  from MatchF.prems obtain j where "\<tau> \<sigma> i + b + 1 \<le> \<tau> \<sigma> j" "j \<le> progress_regex \<sigma> r (plen \<pi>)"
    by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le dest!: le_cInf_iff[THEN iffD1, rotated -1])
  then have 1: "k < progress_regex \<sigma> r (plen \<pi>)" if "\<tau> \<sigma> k \<le> \<tau> \<sigma> i + b" for k
    using that by (fastforce elim!: order.strict_trans2[rotated] intro: less_\<tau>D[of \<sigma>])
  have 2: "k < plen \<pi>" if "\<tau> \<sigma> k \<le> \<tau> \<sigma> i + b" for k
    using 1[OF that] by (simp add: less_eq_Suc_le order.trans[OF _ progress_regex_le])

  from MatchF.prems have "i < progress \<sigma>' (MFOTL.MatchF I r) (plen \<pi>)"
    unfolding progress_prefix_conv[OF assms(1,2)] .
  then obtain j where "\<tau> \<sigma>' i + b + 1 \<le> \<tau> \<sigma>' j" "j \<le> progress_regex \<sigma>' r (plen \<pi>)"
    by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le dest!: le_cInf_iff[THEN iffD1, rotated -1])
  then have 11: "k < progress_regex \<sigma> r (plen \<pi>)" if "\<tau> \<sigma>' k \<le> \<tau> \<sigma>' i + b" for k
    unfolding progress_regex_prefix_conv[OF assms(1,2)]
    using that by (fastforce elim!: order.strict_trans2[rotated] intro: less_\<tau>D[of \<sigma>'])+
  have 21: "k < plen \<pi>" if "\<tau> \<sigma>' k \<le> \<tau> \<sigma>' i + b" for k
    using 11[OF that] by (simp add: less_eq_Suc_le order.trans[OF _ progress_regex_le])

  show ?case unfolding sat.simps
  proof ((intro ex_cong iffI; elim conjE), goal_cases LR RL)
    case (LR j)
    with MatchF.IH(1)[OF 1] \<tau>_prefix_conv[OF assms(1,2) 2] show ?case
      by (auto 0 4 simp: le_diff_conv add.commute dest: less_imp_le order.trans[OF \<tau>_mono, rotated])
  next
    case (RL j)
    with MatchF.IH(1)[OF 11] \<tau>_prefix_conv[OF assms(1,2) 21] show ?case
      by (auto 0 4 simp: le_diff_conv add.commute dest: less_imp_le order.trans[OF \<tau>_mono, rotated])
  qed
next
  case (Times r s)
  then show ?case
    by (auto 0 3 intro!: relcomppI[rotated] dest: match_le[of \<sigma>' v s _ j])
next
  case (Star r)
  then show ?case
    by (auto elim!: bounded_rtranclp_mono[rotated 2] match_le)
qed auto

interpretation verimon: monitor_timed_progress "\<lambda>\<phi>. MFOTL.future_reach \<phi> \<noteq> \<infinity>" progress
  by (unfold_locales, (fact progress_mono progress_le progress_time_conv sat_prefix_conv |
        simp add: mmonitorable_def progress_ge)+)

abbreviation "mverdicts \<equiv> verimon.verdicts"


subsection \<open>Correctness\<close>

subsubsection \<open>Invariants\<close>

definition wf_mbuf2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a table \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 'a table \<Rightarrow> bool) \<Rightarrow>
  'a mbuf2 \<Rightarrow> bool" where
  "wf_mbuf2 i ja jb P Q buf \<longleftrightarrow> i \<le> ja \<and> i \<le> jb \<and> (case buf of (xs, ys) \<Rightarrow>
    list_all2 P [i..<ja] xs \<and> list_all2 Q [i..<jb] ys)"

inductive list_all3 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> bool" for P :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool)" where
  "list_all3 P [] [] []"
| "P a1 a2 a3 \<Longrightarrow> list_all3 P q1 q2 q3 \<Longrightarrow> list_all3 P (a1 # q1) (a2 # q2) (a3 # q3)"

lemma list_all3_list_all2D: "list_all3 P xs ys zs \<Longrightarrow>
  (length xs = length ys \<and> list_all2 (case_prod P) (zip xs ys) zs)"
  by (induct xs ys zs rule: list_all3.induct) auto

lemma list_all2_list_all3I: "length xs = length ys \<Longrightarrow> list_all2 (case_prod P) (zip xs ys) zs \<Longrightarrow>
  list_all3 P xs ys zs"
  by (induct xs ys arbitrary: zs rule: list_induct2)
    (auto simp: list_all2_Cons1 intro: list_all3.intros)

lemma list_all3_list_all2_eq: "list_all3 P xs ys zs \<longleftrightarrow>
  (length xs = length ys \<and> list_all2 (case_prod P) (zip xs ys) zs)"
  using list_all2_list_all3I list_all3_list_all2D by blast

lemma list_all3_mapD: "list_all3 P (map f xs) (map g ys) (map h zs) \<Longrightarrow>
  list_all3 (\<lambda>x y z. P (f x) (g y) (h z)) xs ys zs"
  by (induct "map f xs" "map g ys" "map h zs" arbitrary: xs ys zs rule: list_all3.induct)
    (auto intro: list_all3.intros)

lemma list_all3_mapI: "list_all3 (\<lambda>x y z. P (f x) (g y) (h z)) xs ys zs \<Longrightarrow>
  list_all3 P (map f xs) (map g ys) (map h zs)"
  by (induct xs ys zs rule: list_all3.induct)
    (auto intro: list_all3.intros)

lemma list_all3_map_iff: "list_all3 P (map f xs) (map g ys) (map h zs) \<longleftrightarrow>
  list_all3 (\<lambda>x y z. P (f x) (g y) (h z)) xs ys zs"
  using list_all3_mapD list_all3_mapI by blast

lemmas list_all3_map =
  list_all3_map_iff[where g=id and h=id, unfolded list.map_id id_apply]
  list_all3_map_iff[where f=id and h=id, unfolded list.map_id id_apply]
  list_all3_map_iff[where f=id and g=id, unfolded list.map_id id_apply]

lemma list_all3_conv_all_nth:
  "list_all3 P xs ys zs =
  (length xs = length ys \<and> length ys = length zs \<and> (\<forall>i < length xs. P (xs!i) (ys!i) (zs!i)))"
  by (auto simp add: list_all3_list_all2_eq list_all2_conv_all_nth)

lemma list_all3_refl [intro?]:
  "(\<And>x. x \<in> set xs \<Longrightarrow> P x x x) \<Longrightarrow> list_all3 P xs xs xs"
  by (simp add: list_all3_conv_all_nth)

definition wf_mbufn :: "nat \<Rightarrow> nat list \<Rightarrow> (nat \<Rightarrow> 'a table \<Rightarrow> bool) list \<Rightarrow> 'a mbufn \<Rightarrow> bool" where
  "wf_mbufn i js Ps buf \<longleftrightarrow> list_all3 (\<lambda>P j xs. i \<le> j \<and> list_all2 P [i..<j] xs) Ps js buf"

definition wf_mbuf2' :: "'a MFOTL.trace \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list set \<Rightarrow>
  'a MFOTL.formula \<Rightarrow> 'a MFOTL.formula \<Rightarrow> 'a mbuf2 \<Rightarrow> bool" where
  "wf_mbuf2' \<sigma> j n R \<phi> \<psi> buf \<longleftrightarrow> wf_mbuf2 (min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j))
    (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)
    (\<lambda>i. qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>))
    (\<lambda>i. qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<psi>)) buf"

definition wf_mbufn' :: "'a MFOTL.trace \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list set \<Rightarrow>
  'a MFOTL.regex \<Rightarrow> 'a mbufn \<Rightarrow> bool" where
  "wf_mbufn' \<sigma> j n R r buf \<longleftrightarrow> (case to_mregex r of (mr, \<phi>s) \<Rightarrow>
    wf_mbufn (progress_regex \<sigma> r j) (map (\<lambda>\<phi>. progress \<sigma> \<phi> j) \<phi>s)
    (map (\<lambda>\<phi> i. qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>)) \<phi>s)
    buf) "

lemma wf_mbuf2'_UNIV_alt: "wf_mbuf2' \<sigma> j n UNIV \<phi> \<psi> buf \<longleftrightarrow> (case buf of (xs, ys) \<Rightarrow>
  list_all2 (\<lambda>i. wf_table n (MFOTL.fv \<phi>) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>))
    [min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j) ..< (progress \<sigma> \<phi> j)] xs \<and>
  list_all2 (\<lambda>i. wf_table n (MFOTL.fv \<psi>) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<psi>))
    [min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j) ..< (progress \<sigma> \<psi> j)] ys)"
  unfolding wf_mbuf2'_def wf_mbuf2_def
  by (simp add: mem_restr_UNIV[THEN eqTrueI, abs_def] split: prod.split)

definition wf_ts :: "'a MFOTL.trace \<Rightarrow> nat \<Rightarrow> 'a MFOTL.formula \<Rightarrow> 'a MFOTL.formula \<Rightarrow> ts list \<Rightarrow> bool" where
  "wf_ts \<sigma> j \<phi> \<psi> ts \<longleftrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)..<j] ts"

definition wf_ts_regex :: "'a MFOTL.trace \<Rightarrow> nat \<Rightarrow> 'a MFOTL.regex \<Rightarrow> ts list \<Rightarrow> bool" where
  "wf_ts_regex \<sigma> j r ts \<longleftrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress_regex \<sigma> r j..<j] ts"

abbreviation "Sincep pos \<phi> I \<psi> \<equiv> MFOTL.Since (if pos then \<phi> else MFOTL.Neg \<phi>) I \<psi>"

definition wf_since_aux :: "'a MFOTL.trace \<Rightarrow> nat \<Rightarrow> 'a list set \<Rightarrow> bool \<Rightarrow>
    'a MFOTL.formula \<Rightarrow> \<I> \<Rightarrow> 'a MFOTL.formula \<Rightarrow> 'a msaux \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_since_aux \<sigma> n R pos \<phi> I \<psi> aux ne \<longleftrightarrow> sorted_wrt (\<lambda>x y. fst x > fst y) aux \<and>
    (\<forall>t X. (t, X) \<in> set aux \<longrightarrow> ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> \<tau> \<sigma> (ne-1) - t \<le> right I \<and> (\<exists>i. \<tau> \<sigma> i = t) \<and>
      qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) (ne-1) (Sincep pos \<phi> (point (\<tau> \<sigma> (ne-1) - t)) \<psi>)) X) \<and>
    (\<forall>t. ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> \<tau> \<sigma> (ne-1) - t \<le> right I \<and> (\<exists>i. \<tau> \<sigma> i = t) \<longrightarrow>
      (\<exists>X. (t, X) \<in> set aux))"

definition wf_matchP_aux :: "'a MFOTL.trace \<Rightarrow> nat \<Rightarrow> 'a list set \<Rightarrow>
    \<I> \<Rightarrow> 'a MFOTL.regex \<Rightarrow> 'a mr\<delta>aux \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_matchP_aux \<sigma> n R I r aux ne \<longleftrightarrow> sorted_wrt (\<lambda>x y. fst x > fst y) aux \<and>
    (\<forall>t X. (t, X) \<in> set aux \<longrightarrow> ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> \<tau> \<sigma> (ne-1) - t \<le> right I \<and> (\<exists>i. \<tau> \<sigma> i = t) \<and>
      (case to_mregex r of (mr, \<phi>s) \<Rightarrow>
      (\<forall>ms \<in> RPDs mr. qtable n (MFOTL.fv_regex r) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) (ne-1)
         (MFOTL.MatchP (point (\<tau> \<sigma> (ne-1) - t)) (from_mregex ms \<phi>s)))
         (Mapping.lookup_default empty_table X ms)))) \<and>
    (\<forall>t. ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> \<tau> \<sigma> (ne-1) - t \<le> right I \<and> (\<exists>i. \<tau> \<sigma> i = t) \<longrightarrow>
      (\<exists>X. (t, X) \<in> set aux))"

lemma qtable_mem_restr_UNIV: "qtable n A (mem_restr UNIV) Q X = wf_table n A Q X"
  unfolding qtable_def by auto

lemma wf_since_aux_UNIV_alt:
  "wf_since_aux \<sigma> n UNIV pos \<phi> I \<psi> aux ne \<longleftrightarrow> sorted_wrt (\<lambda>x y. fst x > fst y) aux \<and>
    (\<forall>t X. (t, X) \<in> set aux \<longrightarrow> ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> \<tau> \<sigma> (ne-1) - t \<le> right I \<and> (\<exists>i. \<tau> \<sigma> i = t) \<and>
      wf_table n (MFOTL.fv \<psi>)
          (\<lambda>v. MFOTL.sat \<sigma> (map the v) (ne-1) (Sincep pos \<phi> (point (\<tau> \<sigma> (ne-1) - t)) \<psi>)) X) \<and>
    (\<forall>t. ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> \<tau> \<sigma> (ne-1) - t \<le> right I \<and> (\<exists>i. \<tau> \<sigma> i = t) \<longrightarrow>
      (\<exists>X. (t, X) \<in> set aux))"
  unfolding wf_since_aux_def qtable_mem_restr_UNIV ..

definition wf_until_aux :: "'a MFOTL.trace \<Rightarrow> nat \<Rightarrow> 'a list set \<Rightarrow> bool \<Rightarrow>
    'a MFOTL.formula \<Rightarrow> \<I> \<Rightarrow> 'a MFOTL.formula \<Rightarrow> 'a muaux \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_until_aux \<sigma> n R pos \<phi> I \<psi> aux ne \<longleftrightarrow> list_all2 (\<lambda>x i. case x of (t, r1, r2) \<Rightarrow> t = \<tau> \<sigma> i \<and>
      qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. if pos then (\<forall>k\<in>{i..<ne+length aux}. MFOTL.sat \<sigma> (map the v) k \<phi>)
          else (\<exists>k\<in>{i..<ne+length aux}. MFOTL.sat \<sigma> (map the v) k \<phi>)) r1 \<and>
      qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. (\<exists>j. i \<le> j \<and> j < ne + length aux \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and>
          MFOTL.sat \<sigma> (map the v) j \<psi> \<and>
          (\<forall>k\<in>{i..<j}. if pos then MFOTL.sat \<sigma> (map the v) k \<phi> else \<not> MFOTL.sat \<sigma> (map the v) k \<phi>))) r2)
    aux [ne..<ne+length aux]"

lemma wf_until_aux_UNIV_alt:
  "wf_until_aux \<sigma> n UNIV pos \<phi> I \<psi> aux ne \<longleftrightarrow> list_all2 (\<lambda>x i. case x of (t, r1, r2) \<Rightarrow> t = \<tau> \<sigma> i \<and>
      wf_table n (MFOTL.fv \<phi>) (\<lambda>v. if pos
          then (\<forall>k\<in>{i..<ne+length aux}. MFOTL.sat \<sigma> (map the v) k \<phi>)
          else (\<exists>k\<in>{i..<ne+length aux}. MFOTL.sat \<sigma> (map the v) k \<phi>)) r1 \<and>
      wf_table n (MFOTL.fv \<psi>) (\<lambda>v. \<exists>j. i \<le> j \<and> j < ne + length aux \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and>
          MFOTL.sat \<sigma> (map the v) j \<psi> \<and>
          (\<forall>k\<in>{i..<j}. if pos then MFOTL.sat \<sigma> (map the v) k \<phi> else \<not> MFOTL.sat \<sigma> (map the v) k \<phi>)) r2)
    aux [ne..<ne+length aux]"
  unfolding wf_until_aux_def qtable_mem_restr_UNIV ..

definition wf_matchF_aux :: "'a MFOTL.trace \<Rightarrow> nat \<Rightarrow> 'a list set \<Rightarrow>
    \<I> \<Rightarrow> 'a MFOTL.regex \<Rightarrow> 'a ml\<delta>aux \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_matchF_aux \<sigma> n R I r aux ne k \<longleftrightarrow> (case to_mregex r of (mr, \<phi>s) \<Rightarrow> 
      list_all2 (\<lambda>x i. case x of (t, rels, rel) \<Rightarrow> t = \<tau> \<sigma> i \<and>
        list_all2 (\<lambda>\<phi>. qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v.
          MFOTL.sat \<sigma> (map the v) i \<phi>)) \<phi>s rels \<and>
        qtable n (MFOTL.fv_regex r) (mem_restr R) (\<lambda>v. (\<exists>j. i \<le> j \<and> j < ne + length aux + k \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and>
          MFOTL.match \<sigma> (map the v) r i j)) rel)
    aux [ne..<ne+length aux])"

definition wf_matchF_invar where
  "wf_matchF_invar \<sigma> n R I r st i =
     (case st of (aux, Y) \<Rightarrow> aux \<noteq> [] \<and> wf_matchF_aux \<sigma> n R I r aux i 0 \<and>
     (case to_mregex r of (mr, \<phi>s) \<Rightarrow> \<forall>ms \<in> LPDs mr.
       qtable n (MFOTL.fv_regex r) (mem_restr R) (\<lambda>v.
         MFOTL.match \<sigma> (map the v) (from_mregex ms \<phi>s) i (i + length aux - 1)) (lookup Y ms)))"

inductive wf_mformula :: "'a MFOTL.trace \<Rightarrow> nat \<Rightarrow>
  nat \<Rightarrow> 'a list set \<Rightarrow> 'a mformula \<Rightarrow> 'a MFOTL.formula \<Rightarrow> bool"
  for \<sigma> j where
  Eq: "MFOTL.is_Const t1 \<or> MFOTL.is_Const t2 \<Longrightarrow>
    \<forall>x\<in>MFOTL.fv_trm t1. x < n \<Longrightarrow> \<forall>x\<in>MFOTL.fv_trm t2. x < n \<Longrightarrow>
    wf_mformula \<sigma> j n R (MRel (eq_rel n t1 t2)) (MFOTL.Eq t1 t2)"
| neq_Const: "\<phi> = MRel (neq_rel n (MFOTL.Const x) (MFOTL.Const y)) \<Longrightarrow>
    wf_mformula \<sigma> j n R \<phi> (MFOTL.Neg (MFOTL.Eq (MFOTL.Const x) (MFOTL.Const y)))"
| neq_Var: "x < n \<Longrightarrow>
    wf_mformula \<sigma> j n R (MRel empty_table) (MFOTL.Neg (MFOTL.Eq (MFOTL.Var x) (MFOTL.Var x)))"
| Pred: "\<forall>x\<in>MFOTL.fv (MFOTL.Pred e ts). x < n \<Longrightarrow>
    wf_mformula \<sigma> j n R (MPred e ts) (MFOTL.Pred e ts)"
| And: "wf_mformula \<sigma> j n R \<phi> \<phi>' \<Longrightarrow> wf_mformula \<sigma> j n R \<psi> \<psi>' \<Longrightarrow>
    if pos then \<chi> = MFOTL.And \<phi>' \<psi>' \<and> \<not> (safe_formula (MFOTL.Neg \<psi>') \<and> MFOTL.fv \<psi>' \<subseteq> MFOTL.fv \<phi>')
      else \<chi> = MFOTL.And_Not \<phi>' \<psi>' \<and> safe_formula \<psi>' \<and> MFOTL.fv \<psi>' \<subseteq> MFOTL.fv \<phi>' \<Longrightarrow>
    wf_mbuf2' \<sigma> j n R \<phi>' \<psi>' buf \<Longrightarrow>
    wf_mformula \<sigma> j n R (MAnd \<phi> pos \<psi> buf) \<chi>"
| Or: "wf_mformula \<sigma> j n R \<phi> \<phi>' \<Longrightarrow> wf_mformula \<sigma> j n R \<psi> \<psi>' \<Longrightarrow>
    MFOTL.fv \<phi>' = MFOTL.fv \<psi>' \<Longrightarrow>
    wf_mbuf2' \<sigma> j n R \<phi>' \<psi>' buf \<Longrightarrow>
    wf_mformula \<sigma> j n R (MOr \<phi> \<psi> buf) (MFOTL.Or \<phi>' \<psi>')"
| Neg: "wf_mformula \<sigma> j n R \<phi> \<phi>' \<Longrightarrow> MFOTL.fv \<phi>' = {} \<Longrightarrow>
    wf_mformula \<sigma> j n R (MNeg \<phi>) (MFOTL.Neg \<phi>')"
| Exists: "wf_mformula \<sigma> j (Suc n) (lift_envs R) \<phi> \<phi>' \<Longrightarrow>
    wf_mformula \<sigma> j n R (MExists \<phi>) (MFOTL.Exists \<phi>')"
| Prev: "wf_mformula \<sigma> j n R \<phi> \<phi>' \<Longrightarrow>
    first \<longleftrightarrow> j = 0 \<Longrightarrow>
    list_all2 (\<lambda>i. qtable n (MFOTL.fv \<phi>') (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>'))
      [min (progress \<sigma> \<phi>' j) (j-1)..<progress \<sigma> \<phi>' j] buf \<Longrightarrow>
    list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> \<phi>' j) (j-1)..<j] nts \<Longrightarrow>
    wf_mformula \<sigma> j n R (MPrev I \<phi> first buf nts) (MFOTL.Prev I \<phi>')"
| Next: "wf_mformula \<sigma> j n R \<phi> \<phi>' \<Longrightarrow>
    first \<longleftrightarrow> progress \<sigma> \<phi>' j = 0 \<Longrightarrow>
    list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress \<sigma> \<phi>' j - 1..<j] nts \<Longrightarrow>
    wf_mformula \<sigma> j n R (MNext I \<phi> first nts) (MFOTL.Next I \<phi>')"
| Since: "wf_mformula \<sigma> j n R \<phi> \<phi>' \<Longrightarrow> wf_mformula \<sigma> j n R \<psi> \<psi>' \<Longrightarrow>
    if pos then \<phi>'' = \<phi>' else \<phi>'' = MFOTL.Neg \<phi>' \<Longrightarrow>
    safe_formula \<phi>'' = pos \<Longrightarrow>
    MFOTL.fv \<phi>' \<subseteq> MFOTL.fv \<psi>' \<Longrightarrow>
    wf_mbuf2' \<sigma> j n R \<phi>' \<psi>' buf \<Longrightarrow>
    wf_ts \<sigma> j \<phi>' \<psi>' nts \<Longrightarrow>
    wf_since_aux \<sigma> n R pos \<phi>' I \<psi>' aux (progress \<sigma> (MFOTL.Since \<phi>'' I \<psi>') j) \<Longrightarrow>
    wf_mformula \<sigma> j n R (MSince pos \<phi> I \<psi> buf nts aux) (MFOTL.Since \<phi>'' I \<psi>')"
| Until: "wf_mformula \<sigma> j n R \<phi> \<phi>' \<Longrightarrow> wf_mformula \<sigma> j n R \<psi> \<psi>' \<Longrightarrow>
    if pos then \<phi>'' = \<phi>' else \<phi>'' = MFOTL.Neg \<phi>' \<Longrightarrow>
    safe_formula \<phi>'' = pos \<Longrightarrow>
    MFOTL.fv \<phi>' \<subseteq> MFOTL.fv \<psi>' \<Longrightarrow>
    wf_mbuf2' \<sigma> j n R \<phi>' \<psi>' buf \<Longrightarrow>
    wf_ts \<sigma> j \<phi>' \<psi>' nts \<Longrightarrow>
    wf_until_aux \<sigma> n R pos \<phi>' I \<psi>' aux (progress \<sigma> (MFOTL.Until \<phi>'' I \<psi>') j) \<Longrightarrow>
    progress \<sigma> (MFOTL.Until \<phi>'' I \<psi>') j + length aux = min (progress \<sigma> \<phi>' j) (progress \<sigma> \<psi>' j) \<Longrightarrow>
    wf_mformula \<sigma> j n R (MUntil pos \<phi> I \<psi> buf nts aux) (MFOTL.Until \<phi>'' I \<psi>')"
| MatchP: "(case to_mregex r of (mr', \<phi>s') \<Rightarrow>
      list_all2 (wf_mformula \<sigma> j n R) \<phi>s \<phi>s' \<and> mr = mr') \<Longrightarrow>
    mrs = sorted_list_of_set (RPDs mr) \<Longrightarrow>
    safe_regex Past Safe r \<Longrightarrow>
    wf_mbufn' \<sigma> j n R r buf \<Longrightarrow>
    wf_ts_regex \<sigma> j r nts \<Longrightarrow>
    wf_matchP_aux \<sigma> n R I r aux (progress \<sigma> (MFOTL.MatchP I r) j) \<Longrightarrow>
    wf_mformula \<sigma> j n R (MMatchP I mr mrs \<phi>s buf nts aux) (MFOTL.MatchP I r)"
| MatchF: "(case to_mregex r of (mr', \<phi>s') \<Rightarrow>
      list_all2 (wf_mformula \<sigma> j n R) \<phi>s \<phi>s' \<and> mr = mr') \<Longrightarrow>
    mrs = sorted_list_of_set (LPDs mr) \<Longrightarrow>
    safe_regex Future Safe r \<Longrightarrow>
    wf_mbufn' \<sigma> j n R r buf \<Longrightarrow>
    wf_ts_regex \<sigma> j r nts \<Longrightarrow>
    wf_matchF_aux \<sigma> n R I r aux (progress \<sigma> (MFOTL.MatchF I r) j) 0 \<Longrightarrow>
    progress \<sigma> (MFOTL.MatchF I r) j + length aux = progress_regex \<sigma> r j \<Longrightarrow>
    wf_mformula \<sigma> j n R (MMatchF I mr mrs \<phi>s buf nts aux) (MFOTL.MatchF I r)"

definition wf_mstate :: "'a MFOTL.formula \<Rightarrow> 'a MFOTL.prefix \<Rightarrow> 'a list set \<Rightarrow> 'a mstate \<Rightarrow> bool" where
  "wf_mstate \<phi> \<pi> R st \<longleftrightarrow> mstate_n st = MFOTL.nfv \<phi> \<and> (\<forall>\<sigma>. prefix_of \<pi> \<sigma> \<longrightarrow>
    mstate_i st = progress \<sigma> \<phi> (plen \<pi>) \<and>
    wf_mformula \<sigma> (plen \<pi>) (mstate_n st) R (mstate_m st) \<phi>)"


subsubsection \<open>Initialisation\<close>

lemma minit0_And: "\<not> (safe_formula (MFOTL.Neg \<psi>) \<and> MFOTL.fv \<psi> \<subseteq> MFOTL.fv \<phi>) \<Longrightarrow>
     minit0 n (MFOTL.And \<phi> \<psi>) = MAnd (minit0 n \<phi>) True (minit0 n \<psi>) ([], [])"
  unfolding MFOTL.And_def by simp

lemma minit0_And_Not: "safe_formula \<psi> \<and> MFOTL.fv \<psi> \<subseteq> MFOTL.fv \<phi> \<Longrightarrow>
  minit0 n (MFOTL.And_Not \<phi> \<psi>) = (MAnd (minit0 n \<phi>) False (minit0 n \<psi>) ([], []))"
  unfolding MFOTL.And_Not_def MFOTL.is_Neg_def by (simp split: formula.split)

lemma wf_mbuf2'_0: "wf_mbuf2' \<sigma> 0 n R \<phi> \<psi> ([], [])"
  unfolding wf_mbuf2'_def wf_mbuf2_def by simp

lemma wf_mbufn'_0: "to_mregex r = (mr, \<phi>s) \<Longrightarrow> wf_mbufn' \<sigma> 0 n R r (replicate (length \<phi>s) [])"
  unfolding wf_mbufn'_def wf_mbufn_def map_replicate_const[symmetric]
  by (auto simp: list_all3_map intro: list_all3_refl)

lemma wf_ts_0: "wf_ts \<sigma> 0 \<phi> \<psi> []"
  unfolding wf_ts_def by simp

lemma wf_ts_regex_0: "wf_ts_regex \<sigma> 0 r []"
  unfolding wf_ts_regex_def by simp

lemma wf_since_aux_Nil: "wf_since_aux \<sigma> n R pos \<phi>' I \<psi>' [] 0"
  unfolding wf_since_aux_def by simp

lemma wf_until_aux_Nil: "wf_until_aux \<sigma> n R pos \<phi>' I \<psi>' [] 0"
  unfolding wf_until_aux_def by simp

lemma wf_matchP_aux_Nil: "wf_matchP_aux \<sigma> n R I r [] 0"
  unfolding wf_matchP_aux_def by simp

lemma wf_matchF_aux_Nil: "wf_matchF_aux \<sigma> n R I r [] 0 k"
  unfolding wf_matchF_aux_def by simp

lemma minit0_Neg_Eq: "minit0 n (MFOTL.Neg (formula.Eq t1 t2)) = MRel (neq_rel n t1 t2)"
  by simp

lemma minit0_Neg_Or1: "safe_formula \<psi> \<and> MFOTL.fv \<psi> \<subseteq> MFOTL.fv \<phi> \<Longrightarrow> minit0 n (MFOTL.Neg (MFOTL.Or (MFOTL.Neg \<phi>) \<psi>)) = MAnd (minit0 n \<phi>) False (minit0 n \<psi>) ([], [])"
  by simp

lemma minit0_Neg_Or2: "\<not> (safe_formula \<psi> \<and> MFOTL.fv \<psi> \<subseteq> MFOTL.fv \<phi>) \<Longrightarrow> \<psi> = MFOTL.Neg \<psi>' \<Longrightarrow> minit0 n (MFOTL.Neg (MFOTL.Or (MFOTL.Neg \<phi>) \<psi>)) = MAnd (minit0 n \<phi>) True (minit0 n \<psi>') ([], [])"
  by simp

lemma minit0_Neg_other: "\<lbrakk>\<forall>t1 t2. \<phi> \<noteq> MFOTL.Eq t1 t2;
  \<forall>\<psi>\<^sub>1 \<psi>\<^sub>2. \<not> (\<phi> = MFOTL.Or (MFOTL.Neg \<psi>\<^sub>1) \<psi>\<^sub>2 \<and> safe_formula \<psi>\<^sub>2 \<and> fv \<psi>\<^sub>2 \<subseteq> fv \<psi>\<^sub>1);
  \<forall>\<psi>\<^sub>1 \<psi>\<^sub>2 \<psi>\<^sub>2'. \<not> (\<phi> = MFOTL.Or (MFOTL.Neg \<psi>\<^sub>1) \<psi>\<^sub>2 \<and> \<not>(safe_formula \<psi>\<^sub>2 \<and> MFOTL.fv \<psi>\<^sub>2 \<subseteq> MFOTL.fv \<psi>\<^sub>1) \<and> \<psi>\<^sub>2 = MFOTL.Neg \<psi>\<^sub>2') \<rbrakk>
  \<Longrightarrow> minit0 n (MFOTL.Neg \<phi>) = MNeg (minit0 n \<phi>)"
  by (subst minit0.simps, (split formula.split)+) auto

lemma fv_regex_alt: "safe_regex m g r \<Longrightarrow> MFOTL.fv_regex r = (\<Union>\<phi> \<in> atms r. MFOTL.fv \<phi>)"
  by (induct m g r rule: safe_regex_induct) auto

lemmas to_mregex_atms =
  to_mregex_ok[THEN conjunct1, THEN equalityD1, THEN set_mp, rotated]

lemma wf_minit0: "safe_formula \<phi> \<Longrightarrow> \<forall>x\<in>MFOTL.fv \<phi>. x < n \<Longrightarrow>
  wf_mformula \<sigma> 0 n R (minit0 n \<phi>) \<phi>"
  by (induction arbitrary: n R rule: safe_formula_induct)
    (auto simp del: minit0.simps(1)
      simp add: minit0_Neg_Eq minit0_Neg_other minit0_And fvi_And minit0_And_Not fvi_And_Not
        list.rel_map fv_regex_alt wf_mformula.intros(14)
      intro!: wf_mformula.intros(1-14) wf_mbuf2'_0 wf_mbufn'_0 wf_ts_0 wf_ts_regex_0
        wf_since_aux_Nil wf_until_aux_Nil wf_matchP_aux_Nil wf_matchF_aux_Nil list.rel_refl_strong
      dest: fvi_Suc_bound dest!: to_mregex_atms split: prod.splits)

lemma wf_mstate_minit: "safe_formula \<phi> \<Longrightarrow> wf_mstate \<phi> pnil R (minit \<phi>)"
  unfolding wf_mstate_def minit_def Let_def
  by (auto intro!: wf_minit0 fvi_less_nfv)


subsubsection \<open>Evaluation\<close>

lemma match_wf_tuple: "Some f = match ts xs \<Longrightarrow> wf_tuple n (\<Union>t\<in>set ts. MFOTL.fv_trm t) (tabulate f 0 n)"
  by (induction ts xs arbitrary: f rule: match.induct)
    (fastforce simp: wf_tuple_def split: if_splits option.splits)+

lemma match_fvi_trm_None: "Some f = match ts xs \<Longrightarrow> \<forall>t\<in>set ts. x \<notin> MFOTL.fv_trm t \<Longrightarrow> f x = None"
  by (induction ts xs arbitrary: f rule: match.induct) (auto split: if_splits option.splits)

lemma match_fvi_trm_Some: "Some f = match ts xs \<Longrightarrow> t \<in> set ts \<Longrightarrow> x \<in> MFOTL.fv_trm t \<Longrightarrow> f x \<noteq> None"
  by (induction ts xs arbitrary: f rule: match.induct) (auto split: if_splits option.splits)

lemma match_eval_trm: "\<forall>t\<in>set ts. \<forall>i\<in>MFOTL.fv_trm t. i < n \<Longrightarrow> Some f = match ts xs \<Longrightarrow>
    map (MFOTL.eval_trm (tabulate (\<lambda>i. the (f i)) 0 n)) ts = xs"
proof (induction ts xs arbitrary: f rule: match.induct)
  case (3 x ts y ys)
  from 3(1)[symmetric] 3(2,3) show ?case
    by (auto 0 3 dest: match_fvi_trm_Some sym split: option.splits if_splits intro!: eval_trm_fv_cong)
qed (auto split: if_splits)

lemma wf_tuple_tabulate_Some: "wf_tuple n A (tabulate f 0 n) \<Longrightarrow> x \<in> A \<Longrightarrow> x < n \<Longrightarrow> \<exists>y. f x = Some y"
  unfolding wf_tuple_def by auto

lemma ex_match: "wf_tuple n (\<Union>t\<in>set ts. MFOTL.fv_trm t) v \<Longrightarrow> \<forall>t\<in>set ts. \<forall>x\<in>MFOTL.fv_trm t. x < n \<Longrightarrow>
    \<exists>f. match ts (map (MFOTL.eval_trm (map the v)) ts) = Some f \<and> v = tabulate f 0 n"
proof (induction ts "map (MFOTL.eval_trm (map the v)) ts" arbitrary: v rule: match.induct)
  case (3 x ts y ys)
  then show ?case
  proof (cases "x \<in> (\<Union>t\<in>set ts. MFOTL.fv_trm t)")
    case True
    with 3 show ?thesis
      by (auto simp: insert_absorb dest!: wf_tuple_tabulate_Some meta_spec[of _ v])
  next
    case False
    with 3(3,4) have
      *: "map (MFOTL.eval_trm (map the v)) ts = map (MFOTL.eval_trm (map the (v[x := None]))) ts"
      by (auto simp: wf_tuple_def nth_list_update intro!: eval_trm_fv_cong)
    from False 3(2-4) obtain f where
      "match ts (map (MFOTL.eval_trm (map the v)) ts) = Some f" "v[x := None] = tabulate f 0 n"
      unfolding *
      by (atomize_elim, intro 3(1)[of "v[x := None]"])
        (auto simp: wf_tuple_def nth_list_update intro!: eval_trm_fv_cong)
    moreover from False this have "f x = None" "length v = n"
      by (auto dest: match_fvi_trm_None[OF sym] arg_cong[of _ _ length])
    ultimately show ?thesis using 3(3)
      by (auto simp: list_eq_iff_nth_eq wf_tuple_def)
  qed
qed (auto simp: wf_tuple_def intro: nth_equalityI)

lemma eq_rel_eval_trm: "v \<in> eq_rel n t1 t2 \<Longrightarrow> MFOTL.is_Const t1 \<or> MFOTL.is_Const t2 \<Longrightarrow>
  \<forall>x\<in>MFOTL.fv_trm t1 \<union> MFOTL.fv_trm t2. x < n \<Longrightarrow>
  MFOTL.eval_trm (map the v) t1 = MFOTL.eval_trm (map the v) t2"
  by (cases t1; cases t2) (simp_all add: singleton_table_def split: if_splits)

lemma in_eq_rel: "wf_tuple n (MFOTL.fv_trm t1 \<union> MFOTL.fv_trm t2) v \<Longrightarrow>
  MFOTL.is_Const t1 \<or> MFOTL.is_Const t2 \<Longrightarrow>
  MFOTL.eval_trm (map the v) t1 = MFOTL.eval_trm (map the v) t2 \<Longrightarrow>
  v \<in> eq_rel n t1 t2"
  by (cases t1; cases t2)
    (auto simp: singleton_table_def wf_tuple_def unit_table_def intro!: nth_equalityI split: if_splits)

lemma table_eq_rel: "MFOTL.is_Const t1 \<or> MFOTL.is_Const t2 \<Longrightarrow>
  table n (MFOTL.fv_trm t1 \<union> MFOTL.fv_trm t2) (eq_rel n t1 t2)"
  by (cases t1; cases t2; simp)

lemma wf_tuple_Suc_fviD: "wf_tuple (Suc n) (MFOTL.fvi b \<phi>) v \<Longrightarrow> wf_tuple n (MFOTL.fvi (Suc b) \<phi>) (tl v)"
  unfolding wf_tuple_def by (simp add: fvi_Suc nth_tl)

lemma table_fvi_tl: "table (Suc n) (MFOTL.fvi b \<phi>) X \<Longrightarrow> table n (MFOTL.fvi (Suc b) \<phi>) (tl ` X)"
  unfolding table_def by (auto intro: wf_tuple_Suc_fviD)

lemma wf_tuple_Suc_fvi_SomeI: "0 \<in> MFOTL.fvi b \<phi> \<Longrightarrow> wf_tuple n (MFOTL.fvi (Suc b) \<phi>) v \<Longrightarrow>
  wf_tuple (Suc n) (MFOTL.fvi b \<phi>) (Some x # v)"
  unfolding wf_tuple_def
  by (auto simp: fvi_Suc less_Suc_eq_0_disj)

lemma wf_tuple_Suc_fvi_NoneI: "0 \<notin> MFOTL.fvi b \<phi> \<Longrightarrow> wf_tuple n (MFOTL.fvi (Suc b) \<phi>) v \<Longrightarrow>
  wf_tuple (Suc n) (MFOTL.fvi b \<phi>) (None # v)"
  unfolding wf_tuple_def
  by (auto simp: fvi_Suc less_Suc_eq_0_disj)

lemma qtable_project_fv: "qtable (Suc n) (fv \<phi>) (mem_restr (lift_envs R)) P X \<Longrightarrow>
    qtable n (MFOTL.fvi (Suc 0) \<phi>) (mem_restr R)
      (\<lambda>v. \<exists>x. P ((if 0 \<in> fv \<phi> then Some x else None) # v)) (tl ` X)"
  using neq0_conv by (fastforce simp: image_iff Bex_def fvi_Suc elim!: qtable_cong dest!: qtable_project)

lemma mprev: "mprev_next I xs ts = (ys, xs', ts') \<Longrightarrow>
  list_all2 P [i..<j'] xs \<Longrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [i..<j] ts \<Longrightarrow> i \<le> j' \<Longrightarrow> i < j \<Longrightarrow>
  list_all2 (\<lambda>i X. if mem (\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i) I then P i X else X = empty_table)
    [i..<min j' (j-1)] ys \<and>
  list_all2 P [min j' (j-1)..<j'] xs' \<and>
  list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min j' (j-1)..<j] ts'"
proof (induction I xs ts arbitrary: i ys xs' ts' rule: mprev_next.induct)
  case (1 I ts)
  then have "min j' (j-1) = i" by auto
  with 1 show ?case by auto
next
  case (3 I v v' t)
  then have "min j' (j-1) = i" by (auto simp: list_all2_Cons2 upt_eq_Cons_conv)
  with 3 show ?case by auto
next
  case (4 I x xs t t' ts)
  from 4(1)[of "tl ys" xs' ts' "Suc i"] 4(2-6) show ?case
    by (auto simp add: list_all2_Cons2 upt_eq_Cons_conv Suc_less_eq2
      elim!: list.rel_mono_strong split: prod.splits if_splits)
qed simp

lemma mnext: "mprev_next I xs ts = (ys, xs', ts') \<Longrightarrow>
  list_all2 P [Suc i..<j'] xs \<Longrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [i..<j] ts \<Longrightarrow> Suc i \<le> j' \<Longrightarrow> i < j \<Longrightarrow>
  list_all2 (\<lambda>i X. if mem (\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i) I then P (Suc i) X else X = empty_table)
    [i..<min (j'-1) (j-1)] ys \<and>
  list_all2 P [Suc (min (j'-1) (j-1))..<j'] xs' \<and>
  list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (j'-1) (j-1)..<j] ts'"
proof (induction I xs ts arbitrary: i ys xs' ts' rule: mprev_next.induct)
  case (1 I ts)
  then have "min (j' - 1) (j-1) = i" by auto
  with 1 show ?case by auto
next
  case (3 I v v' t)
  then have "min (j' - 1) (j-1) = i" by (auto simp: list_all2_Cons2 upt_eq_Cons_conv)
  with 3 show ?case by auto
next
  case (4 I x xs t t' ts)
  from 4(1)[of "tl ys" xs' ts' "Suc i"] 4(2-6) show ?case
    by (auto simp add: list_all2_Cons2 upt_eq_Cons_conv Suc_less_eq2
      elim!: list.rel_mono_strong split: prod.splits if_splits) (* slow 10 sec *)
qed simp

lemma in_foldr_UnI: "x \<in> A \<Longrightarrow> A \<in> set xs \<Longrightarrow> x \<in> foldr (\<union>) xs {}"
  by (induction xs) auto

lemma in_foldr_UnE: "x \<in> foldr (\<union>) xs {} \<Longrightarrow> (\<And>A. A \<in> set xs \<Longrightarrow> x \<in> A \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction xs) auto

lemma sat_the_restrict: "fv \<phi> \<subseteq> A \<Longrightarrow> MFOTL.sat \<sigma> (map the (restrict A v)) i \<phi> = MFOTL.sat \<sigma> (map the v) i \<phi>"
  by (rule sat_fv_cong) (auto intro!: map_the_restrict)

lemma eps_the_restrict: "fv_regex r \<subseteq> A \<Longrightarrow> MFOTL.eps \<sigma> (map the (restrict A v)) i r = MFOTL.eps \<sigma> (map the v) i r"
  by (rule eps_fv_cong) (auto intro!: map_the_restrict)

lemma sorted_wrt_filter[simp]: "sorted_wrt R xs \<Longrightarrow> sorted_wrt R (filter P xs)"
  by (induct xs) auto

lemma concat_map_filter[simp]:
  "concat (map f (filter P xs)) = concat (map (\<lambda>x. if P x then f x else []) xs)"
  by (induct xs) auto

lemma update_since:
  assumes pre: "wf_since_aux \<sigma> n R pos \<phi> I \<psi> aux ne"
    and qtable1: "qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) ne \<phi>) rel1"
    and qtable2: "qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) ne \<psi>) rel2"
    and result_eq: "(rel, aux') = update_since I pos rel1 rel2 (\<tau> \<sigma> ne) aux"
    and fvi_subset: "MFOTL.fv \<phi> \<subseteq> MFOTL.fv \<psi>"
  shows "wf_since_aux \<sigma> n R pos \<phi> I \<psi> aux' (Suc ne)"
    and "qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) ne (Sincep pos \<phi> I \<psi>)) rel"
proof -
  let ?wf_tuple = "\<lambda>v. wf_tuple n (MFOTL.fv \<psi>) v"
  note sat.simps[simp del]

  define aux0 where "aux0 = [(t, join rel pos rel1). (t, rel) \<leftarrow> aux]"
  have sorted_aux0: "sorted_wrt (\<lambda>x y. fst x > fst y) aux0"
    using pre[unfolded wf_since_aux_def, THEN conjunct1]
    unfolding aux0_def
    by (induction aux) (auto simp add: sorted_wrt_append)
  have in_aux0_1: "(t, X) \<in> set aux0 \<Longrightarrow> ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> \<tau> \<sigma> (ne - 1) - t \<le> right I \<and>
      (\<exists>i. \<tau> \<sigma> i = t) \<and>
      qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. (MFOTL.sat \<sigma> (map the v) (ne-1) (Sincep pos \<phi> (point (\<tau> \<sigma> (ne-1) - t)) \<psi>) \<and>
        (if pos then MFOTL.sat \<sigma> (map the v) ne \<phi> else \<not> MFOTL.sat \<sigma> (map the v) ne \<phi>))) X" for t X
    unfolding aux0_def using fvi_subset
    by (auto 0 1 elim!: qtable_join[OF _ qtable1] simp: sat_the_restrict
      dest!: assms(1)[unfolded wf_since_aux_def, THEN conjunct2, THEN conjunct1, rule_format])
  then have in_aux0_le_\<tau>: "(t, X) \<in> set aux0 \<Longrightarrow> t \<le> \<tau> \<sigma> ne" for t X
    by (meson \<tau>_mono diff_le_self le_trans)
  have in_aux0_2: "ne \<noteq> 0 \<Longrightarrow> t \<le> \<tau> \<sigma> (ne-1) \<Longrightarrow> \<tau> \<sigma> (ne - 1) - t \<le> right I \<Longrightarrow> \<exists>i. \<tau> \<sigma> i = t \<Longrightarrow>
    \<exists>X. (t, X) \<in> set aux0" for t
  proof -
    fix t
    assume "ne \<noteq> 0" "t \<le> \<tau> \<sigma> (ne-1)" "\<tau> \<sigma> (ne - 1) - t \<le> right I" "\<exists>i. \<tau> \<sigma> i = t"
    then obtain X where "(t, X) \<in> set aux"
      by (atomize_elim, intro assms(1)[unfolded wf_since_aux_def, THEN conjunct2, THEN conjunct2, rule_format])
        (auto simp: gr0_conv_Suc elim!: order_trans[rotated] intro!: diff_le_mono \<tau>_mono)
    with \<open>\<tau> \<sigma> (ne - 1) - t \<le> right I\<close> have "(t, join X pos rel1) \<in> set aux0" 
      unfolding aux0_def by (auto elim!: bexI[rotated] intro!: exI[of _ X])
    then show "\<exists>X. (t, X) \<in> set aux0"
      by blast
  qed
  have aux0_Nil: "aux0 = [] \<Longrightarrow> ne = 0 \<or> ne \<noteq> 0 \<and> (\<forall>t. t \<le> \<tau> \<sigma> (ne-1) \<and> \<tau> \<sigma> (ne - 1) - t \<le> right I \<longrightarrow>
        (\<nexists>i. \<tau> \<sigma> i = t))"
    using in_aux0_2 by (cases "ne = 0") (auto)

  have aux'_eq: "aux' = filter (\<lambda>(t, _). enat (\<tau> \<sigma> ne - t) \<le> right I) (case aux0 of
      [] \<Rightarrow> [(\<tau> \<sigma> ne, rel2)]
    | x # aux' \<Rightarrow> (if fst x = \<tau> \<sigma> ne then (fst x, snd x \<union> rel2) # aux' else (\<tau> \<sigma> ne, rel2) # x # aux'))"
    using result_eq unfolding aux0_def update_since_def Let_def by simp
  have sorted_aux': "sorted_wrt (\<lambda>x y. fst x > fst y) aux'"
    unfolding aux'_eq
    using sorted_aux0 in_aux0_le_\<tau> by (cases aux0) fastforce+
  have in_aux'_1: "t \<le> \<tau> \<sigma> ne \<and> \<tau> \<sigma> ne - t \<le> right I \<and> (\<exists>i. \<tau> \<sigma> i = t) \<and>
      qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) ne (Sincep pos \<phi> (point (\<tau> \<sigma> ne - t)) \<psi>)) X"
    if aux': "(t, X) \<in> set aux'" for t X
  proof (cases aux0)
    case Nil
    with aux' show ?thesis 
      unfolding aux'_eq using qtable2 aux0_Nil
      by (auto simp: zero_enat_def[symmetric] sat_Since_rec[where i=ne]
        dest: spec[of _ "\<tau> \<sigma> (ne-1)"] elim!: qtable_cong[OF _ refl])
  next
    case (Cons a as)
    show ?thesis
    proof (cases "t = \<tau> \<sigma> ne")
      case t: True
      show ?thesis
      proof (cases "fst a = \<tau> \<sigma> ne")
        case True
        with aux' Cons t have "X = snd a \<union> rel2"
          unfolding aux'_eq using sorted_aux0 by (auto split: if_splits)
        moreover from in_aux0_1[of "fst a" "snd a"] Cons have "ne \<noteq> 0"
          "fst a \<le> \<tau> \<sigma> (ne - 1)" "\<tau> \<sigma> ne - fst a \<le> right I" "\<exists>i. \<tau> \<sigma> i = fst a"
          "qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) (ne - 1)
            (Sincep pos \<phi> (point (\<tau> \<sigma> (ne - 1) - fst a)) \<psi>) \<and> (if pos then MFOTL.sat \<sigma> (map the v) ne \<phi>
              else \<not> MFOTL.sat \<sigma> (map the v) ne \<phi>)) (snd a)"
          by (auto simp: True[symmetric] zero_enat_def[symmetric])
        ultimately show ?thesis using qtable2 t True
          by (auto simp: sat_Since_rec[where i=ne] sat.simps(3) elim!: qtable_union)
      next
        case False
        with aux' Cons t have "X = rel2"
          unfolding aux'_eq using sorted_aux0 in_aux0_le_\<tau>[of "fst a" "snd a"] by (auto split: if_splits)
        with aux' Cons t False show ?thesis
          unfolding aux'_eq using qtable2 in_aux0_2[of "\<tau> \<sigma> (ne-1)"] in_aux0_le_\<tau>[of "fst a" "snd a"] sorted_aux0
          by (auto simp: sat_Since_rec[where i=ne] sat.simps(3) zero_enat_def[symmetric] enat_0_iff not_le
            elim!: qtable_cong[OF _ refl] dest!: le_\<tau>_less meta_mp)
    qed
    next
      case False
      with aux' Cons have "(t, X) \<in> set aux0"
        unfolding aux'_eq by (auto split: if_splits)
      then have "ne \<noteq> 0" "t \<le> \<tau> \<sigma> (ne - 1)" "\<tau> \<sigma> (ne - 1) - t \<le> right I" "\<exists>i. \<tau> \<sigma> i = t"
        "qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) (ne - 1) (Sincep pos \<phi> (point (\<tau> \<sigma> (ne - 1) - t)) \<psi>) \<and>
           (if pos then MFOTL.sat \<sigma> (map the v) ne \<phi> else \<not> MFOTL.sat \<sigma> (map the v) ne \<phi>)) X"
        using in_aux0_1 by blast+
      with False aux' Cons show ?thesis
        unfolding aux'_eq using qtable2
        by (fastforce simp: sat_Since_rec[where i=ne] sat.simps(3)
          diff_diff_right[where i="\<tau> \<sigma> ne" and j="\<tau> \<sigma> _ + \<tau> \<sigma> ne" and k="\<tau> \<sigma> (ne - 1)",
            OF trans_le_add2, simplified] elim!: qtable_cong[OF _ refl] order_trans dest: le_\<tau>_less)
    qed
  qed

  have in_aux'_2: "\<exists>X. (t, X) \<in> set aux'" if "t \<le> \<tau> \<sigma> ne" "\<tau> \<sigma> ne - t \<le> right I" "\<exists>i. \<tau> \<sigma> i = t" for t
  proof (cases "t = \<tau> \<sigma> ne")
    case True
    then show ?thesis
    proof (cases aux0)
      case Nil
      with True show ?thesis unfolding aux'_eq by (simp add: zero_enat_def[symmetric])
    next
      case (Cons a as)
      with True show ?thesis unfolding aux'_eq
        by (cases "fst a = \<tau> \<sigma> ne") (auto simp: zero_enat_def[symmetric])
    qed
  next
    case False
    with that have "ne \<noteq> 0"
      using le_\<tau>_less neq0_conv by blast
    moreover from False that have  "t \<le> \<tau> \<sigma> (ne-1)"
      by (metis One_nat_def Suc_leI Suc_pred \<tau>_mono diff_is_0_eq' order.antisym neq0_conv not_le)
    ultimately obtain X where "(t, X) \<in> set aux0" using \<open>\<tau> \<sigma> ne - t \<le> right I\<close> \<open>\<exists>i. \<tau> \<sigma> i = t\<close>
      using \<tau>_mono[of "ne - 1" "ne" \<sigma>] by (atomize_elim, cases "right I") (auto intro!: in_aux0_2 simp del: \<tau>_mono)      
    then show ?thesis unfolding aux'_eq using False \<open>\<tau> \<sigma> ne - t \<le> right I\<close>
      by (auto intro: exI[of _ X] split: list.split)
  qed

  show "wf_since_aux \<sigma> n R pos \<phi> I \<psi> aux' (Suc ne)"
    unfolding wf_since_aux_def
    by (auto dest: in_aux'_1 intro: sorted_aux' in_aux'_2)

  have rel_eq: "rel = foldr (\<union>) [rel. (t, rel) \<leftarrow> aux', left I \<le> \<tau> \<sigma> ne - t] {}"
    unfolding aux'_eq aux0_def
    using result_eq by (auto simp add: update_since_def Let_def
     intro!: arg_cong[where f = "\<lambda>x. foldr (\<union>) (concat x) {}"])
  have rel_alt: "rel = (\<Union>(t, rel) \<in> set aux'. if left I \<le> \<tau> \<sigma> ne - t then rel else empty_table)"
    unfolding rel_eq
    by (auto elim!: in_foldr_UnE bexI[rotated] intro!: in_foldr_UnI)
  show "qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) ne (Sincep pos \<phi> I \<psi>)) rel"
    unfolding rel_alt
  proof (rule qtable_Union[where Qi="\<lambda>(t, X) v.
    left I \<le> \<tau> \<sigma> ne - t \<and> MFOTL.sat \<sigma> (map the v) ne (Sincep pos \<phi> (point (\<tau> \<sigma> ne - t)) \<psi>)"],
    goal_cases finite qtable equiv)
    case (equiv v)
    show ?case
    proof (rule iffI, erule sat_Since_point, goal_cases left right)
      case (left j)
      then show ?case using in_aux'_2[of "\<tau> \<sigma> j", OF _ _ exI, OF _ _ refl] by auto
    next
      case right
      then show ?case by (auto elim!: sat_Since_pointD dest: in_aux'_1)
    qed
  qed (auto dest!: in_aux'_1 intro!: qtable_empty)
qed

lemma fv_regex_from_mregex: 
  "ok (length \<phi>s) mr \<Longrightarrow> fv_regex (from_mregex mr \<phi>s) \<subseteq> (\<Union>\<phi> \<in> set \<phi>s. fv \<phi>)"
  by (induct mr) (auto simp: Bex_def in_set_conv_nth)+

lemma qtable_unsafe_\<epsilon>:
  assumes "ok (length \<phi>s) mr"
  and "list_all2 (\<lambda>\<phi> rel. qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>) rel) \<phi>s rels"
  and "fv_regex (from_mregex mr \<phi>s) \<subseteq> A" and "qtable n A (mem_restr R) Q guard"
  shows "qtable n A (mem_restr R)
   (\<lambda>v. MFOTL.eps \<sigma> (map the v) i (from_mregex mr \<phi>s) \<and> Q v) (unsafe_\<epsilon> guard rels mr)"
  using assms
proof (induct mr)
  case (MPlus mr1 mr2)
  from MPlus(3-6) show ?case
    by (auto intro!: qtable_union[OF MPlus(1,2)])
next
  case (MTimes mr1 mr2)
  then have "fv_regex (from_mregex mr1 \<phi>s) \<subseteq> A" "fv_regex (from_mregex mr2 \<phi>s) \<subseteq> A"
    using fv_regex_from_mregex[of \<phi>s mr1] fv_regex_from_mregex[of \<phi>s mr2] by (auto simp: subset_eq)
  with MTimes(3-6) show ?case 
    by (auto simp: eps_the_restrict restrict_idle intro!: qtable_join[OF MTimes(1,2)])
qed (auto split: prod.splits if_splits simp: qtable_empty_iff list_all2_conv_all_nth
  in_set_conv_nth restrict_idle sat_the_restrict
  intro: in_qtableI qtableI elim!: qtable_join[where A=A and C=A])

lemma qtable_safe_r\<epsilon>:
  assumes "safe_regex Past Safe (from_mregex mr \<phi>s)" "ok (length \<phi>s) mr" "A = fv_regex (from_mregex mr \<phi>s)"
  and "list_all2 (\<lambda>\<phi> rel. qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>) rel) \<phi>s rels"
  shows "qtable n A (mem_restr R) (\<lambda>v. MFOTL.eps \<sigma> (map the v) i (from_mregex mr \<phi>s)) (safe_r\<epsilon> n rels mr)"
  using assms
proof (hypsubst, induct Past Safe "from_mregex mr \<phi>s" arbitrary: mr rule: safe_regex_induct)
case Wild
  then show ?case
    by (cases mr) (auto simp: qtable_empty_iff split: if_splits)
next
  case (Test \<phi>)
  then show ?case
    by (cases mr) (auto simp: qtable_unit_table list_all2_conv_all_nth split: if_splits)
next
  case (Plus r s)
  then show ?case
    by (cases mr) (fastforce intro: qtable_union split: if_splits)+
next
  case (Times r s)
  then show ?case
    by (cases mr) (auto intro: qtable_cong[OF qtable_unsafe_\<epsilon>] split: if_splits)+
next
  case (Star r)
  then show ?case 
    by (cases mr) auto
qed

lemma qtable_safe_l\<epsilon>:
  assumes "safe_regex Future Safe (from_mregex mr \<phi>s)" "ok (length \<phi>s) mr" "A = fv_regex (from_mregex mr \<phi>s)"
  and "list_all2 (\<lambda>\<phi> rel. qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>) rel) \<phi>s rels"
  shows "qtable n A (mem_restr R) (\<lambda>v. MFOTL.eps \<sigma> (map the v) i (from_mregex mr \<phi>s)) (safe_l\<epsilon> n rels mr)"
  using assms
proof (hypsubst, induct Future Safe "from_mregex mr \<phi>s" arbitrary: mr rule: safe_regex_induct)
case Wild
  then show ?case
    by (cases mr) (auto simp: qtable_empty_iff split: if_splits)
next
  case (Test \<phi>)
  then show ?case
    by (cases mr) (auto simp: qtable_unit_table list_all2_conv_all_nth split: if_splits)
next
  case (Plus r s)
  then show ?case
    by (cases mr) (fastforce intro: qtable_union split: if_splits)+
next
  case (Times r s)
  then show ?case
    by (cases mr) (auto intro: qtable_cong[OF qtable_unsafe_\<epsilon>] split: if_splits)+
next
  case (Star r)
  then show ?case 
    by (cases mr) auto
qed

lemma rtranclp_False: "(\<lambda>i j. False)\<^sup>*\<^sup>* = (=)"
proof -
  have "(\<lambda>i j. False)\<^sup>*\<^sup>* i j \<Longrightarrow> i = j" for i j :: 'a
    by (induct i j rule: rtranclp.induct) auto
  then show ?thesis
    by (auto intro: exI[of _ 0])
qed

inductive ok_rctxt for \<phi>s where
  "ok_rctxt \<phi>s id id"
| "ok_rctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> ok_rctxt \<phi>s (\<lambda>t. \<kappa> (MTimes mr t)) (\<lambda>t. \<kappa>' (MFOTL.Times (from_mregex mr \<phi>s) t))"

lemma ok_rctxt_swap: "ok_rctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> from_mregex (\<kappa> mr) \<phi>s = \<kappa>' (from_mregex mr \<phi>s)"
  by (induct \<kappa> \<kappa>' arbitrary: mr rule: ok_rctxt.induct) auto

lemma ok_rctxt_cong: "ok_rctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> MFOTL.match \<sigma> v r = MFOTL.match \<sigma> v s \<Longrightarrow>
  MFOTL.match \<sigma> v (\<kappa>' r) i j = MFOTL.match \<sigma> v (\<kappa>' s) i j"
  by (induct \<kappa> \<kappa>' arbitrary: r s rule: ok_rctxt.induct) simp_all

lemma qtable_r\<delta>\<kappa>:
  assumes "ok (length \<phi>s) mr" "fv_regex (from_mregex mr \<phi>s) \<subseteq> A"
  and "list_all2 (\<lambda>\<phi> rel. qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) j \<phi>) rel) \<phi>s rels"
  and "ok_rctxt \<phi>s \<kappa> \<kappa>'"
  and "\<forall>ms \<in> \<kappa> ` RPD mr. qtable n A (mem_restr R) (\<lambda>v. Q (map the v) (from_mregex ms \<phi>s)) (lookup rel ms)"
  shows "qtable n A (mem_restr R)
  (\<lambda>v. \<exists>s \<in> MFOTL.rpd\<kappa> \<kappa>' \<sigma> (map the v) j (from_mregex mr \<phi>s). Q (map the v) s)
  (r\<delta> \<kappa> rel rels mr)"
  using assms
proof (induct mr arbitrary: \<kappa> \<kappa>')
  case MWild
  then show ?case
    by (auto simp: rtranclp_False ok_rctxt_swap elim!: qtable_cong[OF _ _ ok_rctxt_cong[of _ \<kappa> \<kappa>']])
next
  case (MPlus mr1 mr2)
  from MPlus(3-7) show ?case
    by (auto intro!: qtable_union[OF MPlus(1,2)])
next
  case (MTimes mr1 mr2)
  from MTimes(3-7) show ?case 
    by (auto intro!: qtable_union[OF MTimes(2) qtable_unsafe_\<epsilon>[OF _ _ _ MTimes(1)]]
      elim!: ok_rctxt.intros(2) simp: MTimesL_def Ball_def)
next
  case (MStar mr)
  from MStar(2-6) show ?case 
    by (auto intro!: qtable_cong[OF MStar(1)] intro: ok_rctxt.intros simp: MTimesL_def Ball_def)
qed (auto simp: qtable_empty_iff)

lemmas qtable_r\<delta> = qtable_r\<delta>\<kappa>[OF _ _ _ ok_rctxt.intros(1), unfolded rpd\<kappa>_rpd image_id id_apply]

inductive ok_lctxt for \<phi>s where
  "ok_lctxt \<phi>s id id"
| "ok_lctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> ok_lctxt \<phi>s (\<lambda>t. \<kappa> (MTimes t mr)) (\<lambda>t. \<kappa>' (MFOTL.Times t (from_mregex mr \<phi>s)))"

lemma ok_lctxt_swap: "ok_lctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> from_mregex (\<kappa> mr) \<phi>s = \<kappa>' (from_mregex mr \<phi>s)"
  by (induct \<kappa> \<kappa>' arbitrary: mr rule: ok_lctxt.induct) auto

lemma ok_lctxt_cong: "ok_lctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> MFOTL.match \<sigma> v r = MFOTL.match \<sigma> v s \<Longrightarrow>
  MFOTL.match \<sigma> v (\<kappa>' r) i j = MFOTL.match \<sigma> v (\<kappa>' s) i j"
  by (induct \<kappa> \<kappa>' arbitrary: r s rule: ok_lctxt.induct) simp_all

lemma qtable_l\<delta>\<kappa>:
  assumes "ok (length \<phi>s) mr" "fv_regex (from_mregex mr \<phi>s) \<subseteq> A"
  and "list_all2 (\<lambda>\<phi> rel. qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) j \<phi>) rel) \<phi>s rels"
  and "ok_lctxt \<phi>s \<kappa> \<kappa>'"
  and "\<forall>ms \<in> \<kappa> ` LPD mr. qtable n A (mem_restr R) (\<lambda>v. Q (map the v) (from_mregex ms \<phi>s)) (lookup rel ms)"
  shows "qtable n A (mem_restr R)
  (\<lambda>v. \<exists>s \<in> MFOTL.lpd\<kappa> \<kappa>' \<sigma> (map the v) j (from_mregex mr \<phi>s). Q (map the v) s)
  (l\<delta> \<kappa> rel rels mr)"
  using assms
proof (induct mr arbitrary: \<kappa> \<kappa>')
  case MWild
  then show ?case
    by (auto simp: rtranclp_False ok_lctxt_swap elim!: qtable_cong[OF _ _ ok_rctxt_cong[of _ \<kappa> \<kappa>']])
next
  case (MPlus mr1 mr2)
  from MPlus(3-7) show ?case
    by (auto intro!: qtable_union[OF MPlus(1,2)])
next
  case (MTimes mr1 mr2)
  from MTimes(3-7) show ?case
    by (auto intro!: qtable_union[OF MTimes(1) qtable_unsafe_\<epsilon>[OF _ _ _ MTimes(2)]]
      elim!: ok_lctxt.intros(2) simp: MTimesR_def Ball_def)
next
  case (MStar mr)
  from MStar(2-6) show ?case 
    by (auto intro!: qtable_cong[OF MStar(1)] intro: ok_lctxt.intros simp: MTimesR_def Ball_def)
qed (auto simp: qtable_empty_iff)

lemmas qtable_l\<delta> = qtable_l\<delta>\<kappa>[OF _ _ _ ok_lctxt.intros(1), unfolded lpd\<kappa>_lpd image_id id_apply]

lemma RPD_fv_regex_le: 
  "ms \<in> RPD mr \<Longrightarrow> fv_regex (from_mregex ms \<phi>s) \<subseteq> fv_regex (from_mregex mr \<phi>s)"
  by (induct mr arbitrary: ms) (force simp: MTimesL_def)+

lemma RPD_safe: "safe_regex Past g (from_mregex mr \<phi>s) \<Longrightarrow> 
  ms \<in> RPD mr \<Longrightarrow> safe_regex Past g (from_mregex ms \<phi>s)"
proof (induct Past g "from_mregex mr \<phi>s" arbitrary: mr ms rule: safe_regex_induct)
  case Wild
  then show ?case
    by (cases mr) auto
next
  case (Test g \<phi>)
  then show ?case 
    by (cases mr) auto
next
  case (Plus g r s)
  then show ?case
    by (cases mr) auto
next
  case (Times g r s)
  then show ?case
    by (cases mr; cases g)
      (auto 0 4 simp: MTimesL_def dest: RPD_fv_regex_le split: modality.splits)
next
  case (Star g r)
  then show ?case
    by (cases mr) (auto simp: MTimesL_def)
qed

lemma RPDi_safe: "safe_regex Past g (from_mregex mr \<phi>s) \<Longrightarrow> 
  ms \<in> RPDi n mr ==> safe_regex Past g (from_mregex ms \<phi>s)"
  by (induct n arbitrary: ms mr) (auto dest: RPD_safe)

lemma RPDs_safe: "safe_regex Past g (from_mregex mr \<phi>s) \<Longrightarrow> 
  ms \<in> RPDs mr ==> safe_regex Past g (from_mregex ms \<phi>s)"
  unfolding RPDs_def by (auto dest: RPDi_safe)

lemma RPD_safe_fv_regex: "safe_regex Past Safe (from_mregex mr \<phi>s) \<Longrightarrow> 
  ms \<in> RPD mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
proof (induct Past Safe "from_mregex mr \<phi>s" arbitrary: mr rule: safe_regex_induct)
  case Wild
  then show ?case
    by (cases mr) auto
next
  case (Test \<phi>)
  then show ?case 
    by (cases mr) auto
next
  case (Plus r s)
  then show ?case
    by (cases mr) auto
next
  case (Times r s)
  then show ?case
    by (cases mr) (auto 0 3 simp: MTimesL_def dest: RPD_fv_regex_le split: modality.splits)
qed auto

lemma RPDi_safe_fv_regex: "safe_regex Past Safe (from_mregex mr \<phi>s) \<Longrightarrow> 
  ms \<in> RPDi n mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
  by (induct n arbitrary: ms mr) (auto 5 0 dest: RPD_safe_fv_regex RPD_safe)

lemma RPDs_safe_fv_regex: "safe_regex Past Safe (from_mregex mr \<phi>s) \<Longrightarrow> 
  ms \<in> RPDs mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
  unfolding RPDs_def by (auto dest: RPDi_safe_fv_regex)

lemma RPD_ok: "ok m mr \<Longrightarrow> ms \<in> RPD mr \<Longrightarrow> ok m ms"
proof (induct mr arbitrary: ms)
  case (MPlus mr1 mr2)
  from MPlus(3,4) show ?case
    by (auto elim: MPlus(1,2))
next
  case (MTimes mr1 mr2)
  from MTimes(3,4) show ?case
    by (auto elim: MTimes(1,2) simp: MTimesL_def)
next
  case (MStar mr)
  from MStar(2,3) show ?case
    by (auto elim: MStar(1) simp: MTimesL_def)
qed auto

lemma RPDi_ok: "ok m mr \<Longrightarrow> ms \<in> RPDi n mr \<Longrightarrow> ok m ms"
  by (induct n arbitrary: ms mr) (auto intro: RPD_ok)

lemma RPDs_ok: "ok m mr \<Longrightarrow> ms \<in> RPDs mr \<Longrightarrow> ok m ms"
  unfolding RPDs_def by (auto intro: RPDi_ok)

lemma LPD_fv_regex_le: 
  "ms \<in> LPD mr \<Longrightarrow> fv_regex (from_mregex ms \<phi>s) \<subseteq> fv_regex (from_mregex mr \<phi>s)"
  by (induct mr arbitrary: ms) (force simp: MTimesR_def)+

lemma LPD_safe: "safe_regex Future g (from_mregex mr \<phi>s) \<Longrightarrow> 
  ms \<in> LPD mr ==> safe_regex Future g (from_mregex ms \<phi>s)"
proof (induct Future g "from_mregex mr \<phi>s" arbitrary: mr ms rule: safe_regex_induct)
  case Wild
  then show ?case
    by (cases mr) auto
next
  case (Test g \<phi>)
  then show ?case 
    by (cases mr) auto
next
  case (Plus g r s)
  then show ?case
    by (cases mr) auto
next
  case (Times g r s)
  then show ?case
    by (cases mr; cases g)
      (auto 0 4 simp: MTimesR_def dest: LPD_fv_regex_le split: modality.splits)
next
  case (Star g r)
  then show ?case
    by (cases mr) (auto simp: MTimesR_def)
qed

lemma LPDi_safe: "safe_regex Future g (from_mregex mr \<phi>s) \<Longrightarrow> 
  ms \<in> LPDi n mr ==> safe_regex Future g (from_mregex ms \<phi>s)"
  by (induct n arbitrary: ms mr) (auto dest: LPD_safe)

lemma LPDs_safe: "safe_regex Future g (from_mregex mr \<phi>s) \<Longrightarrow> 
  ms \<in> LPDs mr ==> safe_regex Future g (from_mregex ms \<phi>s)"
  unfolding LPDs_def by (auto dest: LPDi_safe)

lemma LPD_safe_fv_regex: "safe_regex Future Safe (from_mregex mr \<phi>s) \<Longrightarrow> 
  ms \<in> LPD mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
proof (induct Future Safe "from_mregex mr \<phi>s" arbitrary: mr rule: safe_regex_induct)
  case Wild
  then show ?case
    by (cases mr) auto
next
  case (Test \<phi>)
  then show ?case 
    by (cases mr) auto
next
  case (Plus r s)
  then show ?case
    by (cases mr) auto
next
  case (Times r s)
  then show ?case
    by (cases mr) (auto 0 3 simp: MTimesR_def dest: LPD_fv_regex_le split: modality.splits)
qed auto

lemma LPDi_safe_fv_regex: "safe_regex Future Safe (from_mregex mr \<phi>s) \<Longrightarrow> 
  ms \<in> LPDi n mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
  by (induct n arbitrary: ms mr) (auto 5 0 dest: LPD_safe_fv_regex LPD_safe)

lemma LPDs_safe_fv_regex: "safe_regex Future Safe (from_mregex mr \<phi>s) \<Longrightarrow> 
  ms \<in> LPDs mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
  unfolding LPDs_def by (auto dest: LPDi_safe_fv_regex)

lemma LPD_ok: "ok m mr \<Longrightarrow> ms \<in> LPD mr \<Longrightarrow> ok m ms"
proof (induct mr arbitrary: ms)
  case (MPlus mr1 mr2)
  from MPlus(3,4) show ?case
    by (auto elim: MPlus(1,2))
next
  case (MTimes mr1 mr2)
  from MTimes(3,4) show ?case
    by (auto elim: MTimes(1,2) simp: MTimesR_def)
next
  case (MStar mr)
  from MStar(2,3) show ?case
    by (auto elim: MStar(1) simp: MTimesR_def)
qed auto

lemma LPDi_ok: "ok m mr \<Longrightarrow> ms \<in> LPDi n mr \<Longrightarrow> ok m ms"
  by (induct n arbitrary: ms mr) (auto intro: LPD_ok)

lemma LPDs_ok: "ok m mr \<Longrightarrow> ms \<in> LPDs mr \<Longrightarrow> ok m ms"
  unfolding LPDs_def by (auto intro: LPDi_ok)

lemma update_matchP:
  assumes pre: "wf_matchP_aux \<sigma> n R I r aux ne"
    and safe: "safe_regex Past Safe r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and mrs: "mrs = sorted_list_of_set (RPDs mr)"
    and qtables: "list_all2 (\<lambda>\<phi> rel. qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) ne \<phi>) rel) \<phi>s rels"
    and result_eq: "(rel, aux') = update_matchP n I mr mrs rels (\<tau> \<sigma> ne) aux"
  shows "wf_matchP_aux \<sigma> n R I r aux' (Suc ne)"
    and "qtable n (MFOTL.fv_regex r) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) ne (MFOTL.MatchP I r)) rel"
proof -
  let ?wf_tuple = "\<lambda>v. wf_tuple n (MFOTL.fv_regex r) v"
  let ?update = "\<lambda>rel t. Mapping.tabulate mrs (\<lambda>mr. 
    r\<delta> id rel rels mr \<union> (if t = \<tau> \<sigma> ne then safe_r\<epsilon> n rels mr else {}))"
  note sat.simps[simp del]

  define aux0 where "aux0 = [(t, ?update rel t). (t, rel) \<leftarrow> aux, enat (\<tau> \<sigma> ne - t) \<le> right I]"
  have sorted_aux0: "sorted_wrt (\<lambda>x y. fst x > fst y) aux0"
    using pre[unfolded wf_matchP_aux_def, THEN conjunct1]
    unfolding aux0_def
    by (induction aux) (auto simp add: sorted_wrt_append)
  { fix ms
    assume "ms \<in> RPDs mr"
    then have "fv_regex (from_mregex ms \<phi>s) = fv_regex r"
      "safe_regex Past Safe (from_mregex ms \<phi>s)" "ok (length \<phi>s) ms" "RPD ms \<subseteq> RPDs mr"
      using safe RPDs_safe RPDs_safe_fv_regex mr from_mregex_to_mregex RPDs_ok to_mregex_ok RPDs_trans
      by fastforce+
  } note * = this
  have in_aux0_1: "(t, X) \<in> set aux0 \<Longrightarrow> ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> ne \<and> \<tau> \<sigma> ne - t \<le> right I \<and>
      (\<exists>i. \<tau> \<sigma> i = t) \<and>
      (\<forall>ms\<in>RPDs mr. qtable n (fv_regex r) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) ne
         (MFOTL.MatchP (point (\<tau> \<sigma> ne - t)) (from_mregex ms \<phi>s))) (lookup X ms))" for t X
    unfolding aux0_def using safe mr mrs
    apply (subst lookup_default_def)
    apply (auto simp: lookup_tabulate map_of_map_restrict restrict_map_def
        finite_RPDs
        dest!: assms(1)[unfolded wf_matchP_aux_def, THEN conjunct2, THEN conjunct1, rule_format]
        split: option.splits if_splits)
      apply (metis (no_types, hide_lams) Suc_leD \<tau>_mono diff_Suc_Suc dual_order.trans gr0_conv_Suc minus_nat.diff_0 order_refl)
     apply (rule qtable_union[OF qtable_r\<delta>[where \<phi>s=\<phi>s]])
           apply (simp add: * )
          apply (simp add: * )
         apply (rule qtables)
        apply (rule ballI)
        apply (drule bspec)
         apply (erule set_mp[rotated]) back
         apply (simp add: * )
        apply assumption
      apply (rule qtable_safe_r\<epsilon>)
         apply (rule * )
         apply assumption
        apply (simp add: * )
       apply (simp add: * )
      apply (rule qtables)
     apply (subst sat_MatchP_rec)
     apply (auto) []
    apply (rule qtable_cong[OF qtable_r\<delta>])
          apply (erule * )
         apply (rule equalityD1)
         apply (erule * )
        apply (rule qtables)
       apply (rule ballI)
       apply (drule bspec)
        apply (erule set_mp[rotated]) back
        apply (erule * )
       apply assumption
     apply simp
    apply (subst (2) sat_MatchP_rec)
    apply simp
    apply safe
         apply simp
        apply simp
       apply auto []
       apply (drule bspec, assumption) back
       apply (metis (no_types, lifting) Nat.diff_diff_right \<tau>_mono add.commute add_diff_cancel_left diff_le_self less_le_trans not_add_less2 not_le)

      apply auto []
      apply (drule bspec, assumption) back
      apply (metis (no_types, lifting) Nat.diff_diff_right \<tau>_mono add.commute add_diff_cancel_left diff_le_self le_add2 order_trans)
     apply (metis (no_types, lifting) Suc_pred \<tau>_mono diff_le_self le_\<tau>_less le_antisym not_less_eq)
    apply (erule bexI[rotated])
    apply (metis (no_types, lifting) Nat.diff_diff_right \<tau>_mono add.commute add_diff_cancel_left diff_le_self le_add2 order_trans)
    done
  then have in_aux0_le_\<tau>: "(t, X) \<in> set aux0 \<Longrightarrow> t \<le> \<tau> \<sigma> ne" for t X
    by (meson \<tau>_mono diff_le_self le_trans)
  have in_aux0_2: "ne \<noteq> 0 \<Longrightarrow> t \<le> \<tau> \<sigma> (ne-1) \<Longrightarrow> \<tau> \<sigma> ne - t \<le> right I \<Longrightarrow> \<exists>i. \<tau> \<sigma> i = t \<Longrightarrow>
    \<exists>X. (t, X) \<in> set aux0" for t
  proof -
    fix t
    assume "ne \<noteq> 0" "t \<le> \<tau> \<sigma> (ne-1)" "\<tau> \<sigma> ne - t \<le> right I" "\<exists>i. \<tau> \<sigma> i = t"
    then obtain X where "(t, X) \<in> set aux"
      by (atomize_elim, intro assms(1)[unfolded wf_matchP_aux_def, THEN conjunct2, THEN conjunct2, rule_format])
        (auto simp: gr0_conv_Suc elim!: order_trans[rotated] intro!: diff_le_mono \<tau>_mono)
    with \<open>\<tau> \<sigma> ne - t \<le> right I\<close> have "(t, ?update X t) \<in> set aux0" 
      unfolding aux0_def by (auto simp: id_def elim!: bexI[rotated] intro!: exI[of _ X])
    then show "\<exists>X. (t, X) \<in> set aux0"
      by blast
  qed
  have aux0_Nil: "aux0 = [] \<Longrightarrow> ne = 0 \<or> ne \<noteq> 0 \<and> (\<forall>t. t \<le> \<tau> \<sigma> (ne-1) \<and> \<tau> \<sigma> ne - t \<le> right I \<longrightarrow>
        (\<nexists>i. \<tau> \<sigma> i = t))"
    using in_aux0_2 by (cases "ne = 0") (auto)

  have aux'_eq: "aux' = (case aux0 of
      [] \<Rightarrow> [(\<tau> \<sigma> ne, Mapping.tabulate mrs (safe_r\<epsilon> n rels))]
    | x # aux' \<Rightarrow> (if fst x = \<tau> \<sigma> ne then x # aux'
       else (\<tau> \<sigma> ne, Mapping.tabulate mrs (safe_r\<epsilon> n rels)) # x # aux'))"
    using result_eq unfolding aux0_def update_matchP_def Let_def by simp
  have sorted_aux': "sorted_wrt (\<lambda>x y. fst x > fst y) aux'"
    unfolding aux'_eq
    using sorted_aux0 in_aux0_le_\<tau> by (cases aux0) (fastforce)+

  have in_aux'_1: "t \<le> \<tau> \<sigma> ne \<and> \<tau> \<sigma> ne - t \<le> right I \<and> (\<exists>i. \<tau> \<sigma> i = t) \<and>
     (\<forall>ms\<in>RPDs mr. qtable n (MFOTL.fv_regex r) (mem_restr R) (\<lambda>v.
        MFOTL.sat \<sigma> (map the v) ne (MFOTL.MatchP (point (\<tau> \<sigma> ne - t)) (from_mregex ms \<phi>s))) (lookup X ms))"
    if aux': "(t, X) \<in> set aux'" for t X
  proof (cases aux0)
    case Nil
    with aux' show ?thesis 
      unfolding aux'_eq using safe mrs qtables aux0_Nil *
      by (auto simp: zero_enat_def[symmetric] sat_MatchP_rec[where i=ne]
          lookup_default_def lookup_tabulate finite_RPDs split: option.splits
          intro!: qtable_cong[OF qtable_safe_r\<epsilon>]
          dest: spec[of _ "\<tau> \<sigma> (ne-1)"])
  next
    case (Cons a as)
    show ?thesis
    proof (cases "t = \<tau> \<sigma> ne")
      case t: True
      show ?thesis
      proof (cases "fst a = \<tau> \<sigma> ne")
        case True
        with aux' Cons t have "X = snd a"
          unfolding aux'_eq using sorted_aux0 by auto
        moreover from in_aux0_1[of "fst a" "snd a"] Cons have "ne \<noteq> 0"
          "fst a \<le> \<tau> \<sigma> ne" "\<tau> \<sigma> ne - fst a \<le> right I" "\<exists>i. \<tau> \<sigma> i = fst a"
          "\<forall>ms \<in> RPDs mr. qtable n (fv_regex r) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) ne
            (MFOTL.MatchP (point (\<tau> \<sigma> ne - fst a)) (from_mregex ms \<phi>s))) (lookup (snd a) ms)"
          by auto
        ultimately show ?thesis using t True
          by auto
      next
        case False
        with aux' Cons t have "X = Mapping.tabulate mrs (safe_r\<epsilon> n rels)"
          unfolding aux'_eq using sorted_aux0 in_aux0_le_\<tau>[of "fst a" "snd a"] by auto
        with aux' Cons t False show ?thesis
          unfolding aux'_eq using safe mrs qtables * in_aux0_2[of "\<tau> \<sigma> (ne-1)"] in_aux0_le_\<tau>[of "fst a" "snd a"] sorted_aux0
          by (auto simp: sat_MatchP_rec[where i=ne] sat.simps(3) zero_enat_def[symmetric] enat_0_iff not_le
              lookup_default_def lookup_tabulate finite_RPDs split: option.splits
              intro!: qtable_cong[OF qtable_safe_r\<epsilon>] dest!: le_\<tau>_less meta_mp)
      qed
    next
      case False
      with aux' Cons have "(t, X) \<in> set aux0"
        unfolding aux'_eq by (auto split: if_splits)
      then have "ne \<noteq> 0" "t \<le> \<tau> \<sigma> ne" "\<tau> \<sigma> ne - t \<le> right I" "\<exists>i. \<tau> \<sigma> i = t"
        "\<forall>ms \<in> RPDs mr. qtable n (fv_regex r) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) ne
          (MFOTL.MatchP (point (\<tau> \<sigma> ne - t)) (from_mregex ms \<phi>s))) (lookup X ms)"
        using in_aux0_1 by blast+
      with False aux' Cons show ?thesis
        unfolding aux'_eq by auto
    qed
  qed

  have in_aux'_2: "\<exists>X. (t, X) \<in> set aux'" if "t \<le> \<tau> \<sigma> ne" "\<tau> \<sigma> ne - t \<le> right I" "\<exists>i. \<tau> \<sigma> i = t" for t
  proof (cases "t = \<tau> \<sigma> ne")
    case True
    then show ?thesis
    proof (cases aux0)
      case Nil
      with True show ?thesis unfolding aux'_eq by simp
    next
      case (Cons a as)
      with True show ?thesis unfolding aux'_eq using eq_fst_iff[of t a]
        by (cases "fst a = \<tau> \<sigma> ne") auto
    qed
  next
    case False
    with that have "ne \<noteq> 0"
      using le_\<tau>_less neq0_conv by blast
    moreover from False that have  "t \<le> \<tau> \<sigma> (ne-1)"
      by (metis One_nat_def Suc_leI Suc_pred \<tau>_mono diff_is_0_eq' order.antisym neq0_conv not_le)
    ultimately obtain X where "(t, X) \<in> set aux0" using \<open>\<tau> \<sigma> ne - t \<le> right I\<close> \<open>\<exists>i. \<tau> \<sigma> i = t\<close>
      by atomize_elim (auto intro!: in_aux0_2)
    then show ?thesis unfolding aux'_eq using False
      by (auto intro: exI[of _ X] split: list.split)
  qed

  show "wf_matchP_aux \<sigma> n R I r aux' (Suc ne)"
    unfolding wf_matchP_aux_def using mr
    by (auto dest: in_aux'_1 intro: sorted_aux' in_aux'_2)

  have rel_eq: "rel = foldr (\<union>) [lookup rel mr. (t, rel) \<leftarrow> aux', left I \<le> \<tau> \<sigma> ne - t] {}"
    unfolding aux'_eq aux0_def
    using result_eq by (simp add: update_matchP_def Let_def)
  have rel_alt: "rel = (\<Union>(t, rel) \<in> set aux'. if left I \<le> \<tau> \<sigma> ne - t then lookup rel mr else empty_table)"
    unfolding rel_eq
    by (auto elim!: in_foldr_UnE bexI[rotated] intro!: in_foldr_UnI)
  show "qtable n (fv_regex r) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) ne (MFOTL.MatchP I r)) rel"
    unfolding rel_alt
  proof (rule qtable_Union[where Qi="\<lambda>(t, X) v.
    left I \<le> \<tau> \<sigma> ne - t \<and> MFOTL.sat \<sigma> (map the v) ne (MFOTL.MatchP (point (\<tau> \<sigma> ne - t)) r)"],
    goal_cases finite qtable equiv)
    case (equiv v)
    show ?case
    proof (rule iffI, erule sat_MatchP_point, goal_cases left right)
      case (left j)
      then show ?case using in_aux'_2[of "\<tau> \<sigma> j", OF _ _ exI, OF _ _ refl] by auto
    next
      case right
      then show ?case by (auto elim!: sat_MatchP_pointD dest: in_aux'_1)
    qed
  qed (auto dest!: in_aux'_1 intro!: qtable_empty dest!: bspec[OF _ RPDs_refl]
    simp: from_mregex_eq[OF safe mr])
qed

lemma length_update_until: "length (update_until pos I rel1 rel2 nt aux) = Suc (length aux)"
  unfolding update_until_def by simp

lemma wf_update_until:
  assumes pre: "wf_until_aux \<sigma> n R pos \<phi> I \<psi> aux ne"
    and qtable1: "qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) (ne + length aux) \<phi>) rel1"
    and qtable2: "qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) (ne + length aux) \<psi>) rel2"
    and fvi_subset: "MFOTL.fv \<phi> \<subseteq> MFOTL.fv \<psi>"
  shows "wf_until_aux \<sigma> n R pos \<phi> I \<psi> (update_until I pos rel1 rel2 (\<tau> \<sigma> (ne + length aux)) aux) ne"
  unfolding wf_until_aux_def length_update_until
  unfolding update_until_def list.rel_map add_Suc_right upt.simps eqTrueI[OF le_add1] if_True
proof (rule list_all2_appendI, unfold list.rel_map, goal_cases old new)
  case old
  show ?case
  proof (rule list.rel_mono_strong[OF assms(1)[unfolded wf_until_aux_def]]; safe, goal_cases mono1 mono2)
    case (mono1 i X Y v)
    then show ?case
      by (fastforce simp: sat_the_restrict less_Suc_eq
        elim!: qtable_join[OF _ qtable1] qtable_union[OF _ qtable1])
  next
    case (mono2 i X Y v)
    then show ?case using fvi_subset
      by (auto 0 3 simp: sat_the_restrict less_Suc_eq split: if_splits
        elim!: qtable_union[OF _ qtable_join_fixed[OF qtable2]]
        elim: qtable_cong[OF _ refl] intro: exI[of _ "ne + length aux"]) (* slow 8 sec*)
  qed
next
  case new
  then show ?case 
    by (auto intro!: qtable_empty qtable1 qtable2[THEN qtable_cong] exI[of _ "ne + length aux"]
      simp: less_Suc_eq zero_enat_def[symmetric])
qed

lemma length_update_matchF_base:
  "length (fst (update_matchF_base I mr mrs nt entry st)) = Suc 0"
  by (auto simp: Let_def update_matchF_base_def)

lemma length_update_matchF_step:
  "length (fst (update_matchF_step I mr mrs nt entry st)) = Suc (length (fst st))"
  by (auto simp: Let_def update_matchF_step_def split: prod.splits)

lemma length_foldr_update_matchF_step:
  "length (fst (foldr (update_matchF_step I mr mrs nt) aux base)) = length aux + length (fst base)"
  by (induct aux arbitrary: base) (auto simp: Let_def length_update_matchF_step)

lemma length_update_matchF: "length (update_matchF n I mr mrs rels nt aux) = Suc (length aux)"
  unfolding update_matchF_def update_matchF_base_def length_foldr_update_matchF_step
  by (auto simp: Let_def)

lemma wf_update_matchF_base_invar:
  assumes safe: "safe_regex Future Safe r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and mrs: "mrs = sorted_list_of_set (LPDs mr)"
    and qtables: "list_all2 (\<lambda>\<phi> rel. qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) j \<phi>) rel) \<phi>s rels"
  shows "wf_matchF_invar \<sigma> n R I r (update_matchF_base n I mr mrs rels (\<tau> \<sigma> j)) j"
proof -
  have from_mregex: "from_mregex mr \<phi>s = r"
    using safe mr using from_mregex_eq by blast
  { fix ms
    assume "ms \<in> LPDs mr"
    then have "fv_regex (from_mregex ms \<phi>s) = fv_regex r"
      "safe_regex Future Safe (from_mregex ms \<phi>s)" "ok (length \<phi>s) ms" "LPD ms \<subseteq> LPDs mr"
      using safe LPDs_safe LPDs_safe_fv_regex mr from_mregex_to_mregex LPDs_ok to_mregex_ok LPDs_trans
      by fastforce+
  } note * = this
  show ?thesis
  unfolding wf_matchF_invar_def wf_matchF_aux_def update_matchF_base_def mr prod.case Let_def mrs
  using safe
  by (auto simp: * from_mregex qtables qtable_empty_iff zero_enat_def[symmetric]
    lookup_tabulate lookup_default_def finite_LPDs eps_match less_Suc_eq LPDs_refl
    intro!: qtable_cong[OF qtable_safe_l\<epsilon>[where \<phi>s=\<phi>s]] intro: qtables exI[of _ j]
    split: option.splits)
qed

lemma Un_empty_table[simp]: "rel \<union> empty_table = rel" "empty_table \<union> rel = rel"
  unfolding empty_table_def by auto

lemma wf_matchF_invar_step:
  assumes wf: "wf_matchF_invar \<sigma> n R I r st (Suc i)"
    and safe: "safe_regex Future Safe r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and mrs: "mrs = sorted_list_of_set (LPDs mr)"
    and qtables: "list_all2 (\<lambda>\<phi> rel. qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>) rel) \<phi>s rels"
    and rel: "qtable n (MFOTL.fv_regex r) (mem_restr R) (\<lambda>v. (\<exists>j. i \<le> j \<and> j < i + length (fst st) \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and>
          MFOTL.match \<sigma> (map the v) r i j)) rel"
    and entry: "entry = (\<tau> \<sigma> i, rels, rel)"
    and nt: "nt = \<tau> \<sigma> (i + length (fst st))"
  shows "wf_matchF_invar \<sigma> n R I r (update_matchF_step I mr mrs nt entry st) i"
proof -
  have from_mregex: "from_mregex mr \<phi>s = r"
    using safe mr using from_mregex_eq by blast
  { fix ms
    assume "ms \<in> LPDs mr"
    then have "fv_regex (from_mregex ms \<phi>s) = fv_regex r"
      "safe_regex Future Safe (from_mregex ms \<phi>s)" "ok (length \<phi>s) ms" "LPD ms \<subseteq> LPDs mr"
      using safe LPDs_safe LPDs_safe_fv_regex mr from_mregex_to_mregex LPDs_ok to_mregex_ok LPDs_trans
      by fastforce+
  } note * = this
  show ?thesis
    using wf mr mrs entry nt
    apply (cases st)
    apply hypsubst
    unfolding wf_matchF_invar_def update_matchF_step_def Let_def mr prod.case
    apply safe
     apply (subst lookup_default_def)
     apply (auto simp: Let_def wf_matchF_aux_def mr * LPDs_refl
        list_all2_Cons1 append_eq_Cons_conv upt_eq_Cons_conv Suc_le_eq qtables
        lookup_tabulate finite_LPDs id_def
        split: if_splits prod.splits) []
       apply (rule qtable_union[OF rel qtable_l\<delta>[where \<phi>s=\<phi>s]])
           apply (simp_all add: * LPDs_refl)
         apply (rule qtables)
        apply (rule ballI)
        apply (erule bspec)
    using LPDs_trans LPDs_refl apply blast
       apply safe
    subgoal for aux X v j
      apply (auto simp add: less_Suc_eq from_mregex)
      apply (subst (asm) (3) lpd_match)
       apply auto
      done
    subgoal for aux X v j
      apply (auto simp add: from_mregex)
      done
    subgoal for aux X v r
      apply (auto simp add: from_mregex intro!: exI[of _ "i + length aux"])
      apply (subst lpd_match)
       apply auto
      done
      apply (rule qtable_cong[OF rel]; auto simp: less_Suc_eq)
     apply (rule qtable_cong[OF rel]; auto simp: less_Suc_eq)
    apply (subst lookup_default_def)
    apply (auto simp: Let_def wf_matchF_aux_def mr * LPDs_refl
        list_all2_Cons1 append_eq_Cons_conv upt_eq_Cons_conv Suc_le_eq qtables
        lookup_tabulate finite_LPDs id_def
        split: if_splits prod.splits) []
    apply (rule qtable_cong[OF qtable_l\<delta>[where \<phi>s=\<phi>s]])
         apply (simp_all add: *)
      apply (rule qtables)
     apply (rule ballI)
     apply (erule bspec)
    using LPDs_trans LPDs_refl apply blast
    apply (subst (2) lpd_match)
     apply auto
    done
qed

lemma wf_update_matchF_invar:
  assumes pre: "wf_matchF_aux \<sigma> n R I r aux ne (length (fst st) - 1)"
    and wf: "wf_matchF_invar \<sigma> n R I r st (ne + length aux)"
    and safe: "safe_regex Future Safe r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and mrs: "mrs = sorted_list_of_set (LPDs mr)"
    and j: "j = ne + length aux + length (fst st) - 1"
    shows "wf_matchF_invar \<sigma> n R I r (foldr (update_matchF_step I mr mrs (\<tau> \<sigma> j)) aux st) ne"
  using pre wf unfolding j
proof (induct aux arbitrary: ne)
  case (Cons entry aux)
  from Cons(1)[of "Suc ne"] Cons(2,3) show ?case
    unfolding foldr.simps o_apply
    by (intro wf_matchF_invar_step[where rels = "fst (snd entry)" and rel = "snd (snd entry)"])
      (auto simp: safe mr mrs wf_matchF_aux_def wf_matchF_invar_def list_all2_Cons1 append_eq_Cons_conv
        Suc_le_eq upt_eq_Cons_conv length_foldr_update_matchF_step add.assoc split: if_splits)
qed simp


lemma wf_update_matchF:
  assumes pre: "wf_matchF_aux \<sigma> n R I r aux ne 0"
    and safe: "safe_regex Future Safe r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and mrs: "mrs = sorted_list_of_set (LPDs mr)"
    and nt: "nt = \<tau> \<sigma> (ne + length aux)"
    and qtables: "list_all2 (\<lambda>\<phi> rel. qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) (ne + length aux) \<phi>) rel) \<phi>s rels"
  shows "wf_matchF_aux \<sigma> n R I r (update_matchF n I mr mrs rels nt aux) ne 0"
  unfolding update_matchF_def using wf_update_matchF_base_invar[OF safe mr mrs qtables, of I]
  unfolding nt
  by (intro wf_update_matchF_invar[OF _ _ safe mr mrs, unfolded wf_matchF_invar_def split_beta, THEN conjunct2, THEN conjunct1])
    (auto simp: length_update_matchF_base wf_matchF_invar_def update_matchF_base_def Let_def pre)

lemma wf_until_aux_Cons: "wf_until_aux \<sigma> n R pos \<phi> I \<psi> (a # aux) ne \<Longrightarrow>
  wf_until_aux \<sigma> n R pos \<phi> I \<psi> aux (Suc ne)"
  unfolding wf_until_aux_def
  by (simp add: upt_conv_Cons del: upt_Suc cong: if_cong)

lemma wf_matchF_aux_Cons: "wf_matchF_aux \<sigma> n R I r (entry # aux) ne i \<Longrightarrow>
  wf_matchF_aux \<sigma> n R I r aux (Suc ne) i"
  unfolding wf_matchF_aux_def
  by (simp add: upt_conv_Cons del: upt_Suc cong: if_cong split: prod.splits)

lemma wf_until_aux_Cons1: "wf_until_aux \<sigma> n R pos \<phi> I \<psi> ((t, a1, a2) # aux) ne \<Longrightarrow> t = \<tau> \<sigma> ne"
  unfolding wf_until_aux_def
  by (simp add: upt_conv_Cons del: upt_Suc)

lemma wf_matchF_aux_Cons1: "wf_matchF_aux \<sigma> n R I r ((t, rels, rel) # aux) ne i \<Longrightarrow> t = \<tau> \<sigma> ne"
  unfolding wf_matchF_aux_def
  by (simp add: upt_conv_Cons del: upt_Suc split: prod.splits)

lemma wf_until_aux_Cons3: "wf_until_aux \<sigma> n R pos \<phi> I \<psi> ((t, a1, a2) # aux) ne \<Longrightarrow>
  qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. (\<exists>j. ne \<le> j \<and> j < Suc (ne + length aux) \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> ne) I \<and>
    MFOTL.sat \<sigma> (map the v) j \<psi> \<and> (\<forall>k\<in>{ne..<j}. if pos then MFOTL.sat \<sigma> (map the v) k \<phi> else \<not> MFOTL.sat \<sigma> (map the v) k \<phi>))) a2"
  unfolding wf_until_aux_def
  by (simp add: upt_conv_Cons del: upt_Suc)

lemma wf_matchF_aux_Cons3: "wf_matchF_aux \<sigma> n R I r ((t, rels, rel) # aux) ne i \<Longrightarrow>
  qtable n (MFOTL.fv_regex r) (mem_restr R) (\<lambda>v. (\<exists>j. ne \<le> j \<and> j < Suc (ne + length aux + i) \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> ne) I \<and>
    MFOTL.match \<sigma> (map the v) r ne j)) rel"
  unfolding wf_matchF_aux_def
  by (simp add: upt_conv_Cons del: upt_Suc split: prod.splits)

lemma upt_append: "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> [a..<b] @ [b..<c] = [a..<c]"
  by (metis le_Suc_ex upt_add_eq_append)

lemma wf_mbuf2_add:
  assumes "wf_mbuf2 i ja jb P Q buf"
    and "list_all2 P [ja..<ja'] xs"
    and "list_all2 Q [jb..<jb'] ys"
    and "ja \<le> ja'" "jb \<le> jb'"
  shows "wf_mbuf2 i ja' jb' P Q (mbuf2_add xs ys buf)"
  using assms unfolding wf_mbuf2_def
  by (auto 0 3 simp: list_all2_append2 upt_append dest: list_all2_lengthD
    intro: exI[where x="[i..<ja]"] exI[where x="[ja..<ja']"]
           exI[where x="[i..<jb]"] exI[where x="[jb..<jb']"] split: prod.splits)

lemma wf_mbufn_add:
  assumes "wf_mbufn i js Ps buf"
    and "list_all3 list_all2 Ps (List.map2 (\<lambda>j j'. [j..<j']) js js') xss"
    and "list_all2 (\<le>) js js'"
  shows "wf_mbufn i js' Ps (mbufn_add xss buf)"
  unfolding wf_mbufn_def list_all3_conv_all_nth
proof safe
  show "length Ps = length js'" "length js' = length (mbufn_add xss buf)"
    using assms unfolding wf_mbufn_def list_all3_conv_all_nth list_all2_conv_all_nth by auto
next
  fix k assume k: "k < length Ps"
  then show "i \<le> js' ! k"
    using assms unfolding wf_mbufn_def list_all3_conv_all_nth list_all2_conv_all_nth
    by (auto 0 4 dest: spec[of _ i])
  from k have " [i..<js' ! k] =  [i..<js ! k] @ [js ! k ..<js' ! k]" and
    "length [i..<js ! k] = length (buf ! k)"
    using assms(1,3) unfolding wf_mbufn_def list_all3_conv_all_nth list_all2_conv_all_nth
    by (auto simp: upt_append)
  with k show "list_all2 (Ps ! k) [i..<js' ! k] (mbufn_add xss buf ! k)"
    using assms[unfolded wf_mbufn_def list_all3_conv_all_nth]
    by (auto simp add: list_all2_append)
qed

lemma mbuf2_take_eqD:
  assumes "mbuf2_take f buf = (xs, buf')"
    and "wf_mbuf2 i ja jb P Q buf"
  shows "wf_mbuf2 (min ja jb) ja jb P Q buf'"
    and "list_all2 (\<lambda>i z. \<exists>x y. P i x \<and> Q i y \<and> z = f x y) [i..<min ja jb] xs"
  using assms unfolding wf_mbuf2_def
  by (induction f buf arbitrary: i xs buf' rule: mbuf2_take.induct)
    (fastforce simp add: list_all2_Cons2 upt_eq_Cons_conv min_absorb1 min_absorb2 split: prod.splits)+

lemma list_all3_Nil[simp]:
  "list_all3 P xs ys [] \<longleftrightarrow> xs = [] \<and> ys = []"
  "list_all3 P xs [] zs \<longleftrightarrow> xs = [] \<and> zs = []"
  "list_all3 P [] ys zs \<longleftrightarrow> ys = [] \<and> zs = []"
  unfolding list_all3_conv_all_nth by auto

lemma list_all3_Cons:
  "list_all3 P xs ys (z # zs) \<longleftrightarrow> (\<exists>x xs' y ys'. xs = x # xs' \<and> ys = y # ys' \<and> P x y z \<and> list_all3 P xs' ys' zs)"
  "list_all3 P xs (y # ys) zs \<longleftrightarrow> (\<exists>x xs' z zs'. xs = x # xs' \<and> zs = z # zs' \<and> P x y z \<and> list_all3 P xs' ys zs')"
  "list_all3 P (x # xs) ys zs \<longleftrightarrow> (\<exists>y ys' z zs'. ys = y # ys' \<and> zs = z # zs' \<and> P x y z \<and> list_all3 P xs ys' zs')"
  unfolding list_all3_conv_all_nth
  by (auto simp: length_Suc_conv Suc_length_conv nth_Cons split: nat.splits)

lemma list_all3_mono_strong: "list_all3 P xs ys zs \<Longrightarrow>
  (\<And>x y z. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> z \<in> set zs \<Longrightarrow> P x y z \<Longrightarrow> Q x y z) \<Longrightarrow>
  list_all3 Q xs ys zs"
  by (induct xs ys zs rule: list_all3.induct) (auto intro: list_all3.intros)

abbreviation Mini where
  "Mini i js \<equiv> (if js = [] then i else Min (set js))"

lemma wf_mbufn_in_set_Mini:
  assumes "wf_mbufn i js Ps buf"
  shows "[] \<in> set buf \<Longrightarrow> Mini i js = i"
  unfolding in_set_conv_nth
proof (elim exE conjE)
  fix k
  have "i \<le> j" if "j \<in> set js" for j
    using that assms unfolding wf_mbufn_def list_all3_conv_all_nth in_set_conv_nth by auto
  moreover assume "k < length buf" "buf ! k = []"
  ultimately show ?thesis using assms
    unfolding wf_mbufn_def list_all3_conv_all_nth
    by (auto 0 4 dest!: spec[of _ k] intro: Min_eqI simp: in_set_conv_nth)
qed

lemma wf_mbufn_notin_set:
  assumes "wf_mbufn i js Ps buf"
  shows "[] \<notin> set buf \<Longrightarrow> j \<in> set js \<Longrightarrow> i < j"
  using assms unfolding wf_mbufn_def list_all3_conv_all_nth
  by (cases "i \<in> set js") (auto intro: le_neq_implies_less simp: in_set_conv_nth)

lemma wf_mbufn_map_tl:
  "wf_mbufn i js Ps buf \<Longrightarrow> [] \<notin> set buf \<Longrightarrow> wf_mbufn (Suc i) js Ps (map tl buf)"
  by (auto simp: wf_mbufn_def list_all3_map Suc_le_eq
    dest: rel_funD[OF tl_transfer]  elim!: list_all3_mono_strong le_neq_implies_less)

lemma list_all3_list_all2I: "list_all3 (\<lambda>x y z. Q x z) xs ys zs \<Longrightarrow> list_all2 Q xs zs"
  by (induct xs ys zs rule: list_all3.induct) auto

lemma mbuf2t_take_eqD:
  assumes "mbuf2t_take f z buf nts = (z', buf', nts')"
    and "wf_mbuf2 i ja jb P Q buf"
    and "list_all2 R [i..<j] nts"
    and "ja \<le> j" "jb \<le> j"
  shows "wf_mbuf2 (min ja jb) ja jb P Q buf'"
    and "list_all2 R [min ja jb..<j] nts'"
  using assms unfolding wf_mbuf2_def
  by (induction f z buf nts arbitrary: i z' buf' nts' rule: mbuf2t_take.induct)
    (auto simp add: list_all2_Cons2 upt_eq_Cons_conv less_eq_Suc_le min_absorb1 min_absorb2
      split: prod.split)

lemma mbufnt_take_eqD:
  assumes "mbufnt_take f z buf nts = (z', buf', nts')"
    and "wf_mbufn i js Ps buf"
    and "list_all2 R [i..<j] nts"
    and "\<And>k. k \<in> set js \<Longrightarrow> k \<le> j"
    and "k = Mini (i + length nts) js"
  shows "wf_mbufn k js Ps buf'"
    and "list_all2 R [k..<j] nts'"
  using assms(1-4) unfolding assms(5)
proof (induction f z buf nts arbitrary: i z' buf' nts' rule: mbufnt_take.induct)
  case IH: (1 f z buf nts)
  note mbufnt_take.simps[simp del]
  case 1
  then have *: "list_all2 R [Suc i..<j] (tl nts)"
    by (auto simp: list.rel_sel[of R "[i..<j]" nts, simplified])
  from 1 show ?case
    using wf_mbufn_in_set_Mini[OF 1(2)]
    by (subst (asm) mbufnt_take.simps)
      (force simp: wf_mbufn_def split: if_splits prod.splits elim!: list_all3_mono_strong
      dest!: IH(1)[rotated, OF _ wf_mbufn_map_tl[OF 1(2)] *])
  case 2
  then have *: "list_all2 R [Suc i..<j] (tl nts)"
    by (auto simp: list.rel_sel[of R "[i..<j]" nts, simplified])
  have [simp]: "Suc (i + (length nts - Suc 0)) = i + length nts" if "nts \<noteq> []"
    using that by (fastforce simp flip: length_greater_0_conv)
  with 2 show ?case
    using wf_mbufn_in_set_Mini[OF 2(2)] wf_mbufn_notin_set[OF 2(2)]
    by (subst (asm) mbufnt_take.simps) (force simp: wf_mbufn_def
        dest!: IH(2)[rotated, OF _ wf_mbufn_map_tl[OF 2(2)] *]
        split: if_splits prod.splits)
qed

lemma mbuf2t_take_induct[consumes 5, case_names base step]:
  assumes "mbuf2t_take f z buf nts = (z', buf', nts')"
    and "wf_mbuf2 i ja jb P Q buf"
    and "list_all2 R [i..<j] nts"
    and "ja \<le> j" "jb \<le> j"
    and "U i z"
    and "\<And>k x y t z. i \<le> k \<Longrightarrow> Suc k \<le> ja \<Longrightarrow> Suc k \<le> jb \<Longrightarrow>
      P k x \<Longrightarrow> Q k y \<Longrightarrow> R k t \<Longrightarrow> U k z \<Longrightarrow> U (Suc k) (f x y t z)"
  shows "U (min ja jb) z'"
  using assms unfolding wf_mbuf2_def
  by (induction f z buf nts arbitrary: i z' buf' nts' rule: mbuf2t_take.induct)
    (auto simp add: list_all2_Cons2 upt_eq_Cons_conv less_eq_Suc_le min_absorb1 min_absorb2
       elim!: arg_cong2[of _ _ _ _ U, OF _ refl, THEN iffD1, rotated] split: prod.split)

lemma list_all2_hdD:
  assumes "list_all2 P [i..<j] xs" "xs \<noteq> []"
  shows "P i (hd xs)" "i < j"
  using assms unfolding list_all2_conv_all_nth
  by (auto simp: hd_conv_nth intro: zero_less_diff[THEN iffD1] dest!: spec[of _ 0])

lemma mbufnt_take_induct[consumes 5, case_names base step]:
  assumes "mbufnt_take f z buf nts = (z', buf', nts')"
    and "wf_mbufn i js Ps buf"
    and "list_all2 R [i..<j] nts"
    and "\<And>k. k \<in> set js \<Longrightarrow> k \<le> j"
    and "U i z"
    and "\<And>k xs t z. i \<le> k \<Longrightarrow> Suc k \<le> Mini j js \<Longrightarrow>
      list_all2 (\<lambda>P x. P k x) Ps xs \<Longrightarrow> R k t \<Longrightarrow> U k z \<Longrightarrow> U (Suc k) (f xs t z)"
  shows "U (Mini (i + length nts) js) z'"
  using assms
proof (induction f z buf nts arbitrary: i z' buf' nts' rule: mbufnt_take.induct)
  case (1 f z buf nts)
  then have *: "list_all2 R [Suc i..<j] (tl nts)"
    by (auto simp: list.rel_sel[of R "[i..<j]" nts, simplified])
  note mbufnt_take.simps[simp del]
  from 1(2-6) have "i = Min (set js)" if "js \<noteq> []" "nts = []"
    using that unfolding wf_mbufn_def using wf_mbufn_in_set_Mini[OF 1(3)]
    by (fastforce simp: list_all3_Cons neq_Nil_conv)
  with 1(2-7) list_all2_hdD[OF 1(4)] show ?case
    unfolding wf_mbufn_def using wf_mbufn_in_set_Mini[OF 1(3)] wf_mbufn_notin_set[OF 1(3)]
    by (subst (asm) mbufnt_take.simps)
      (auto simp add: list.rel_map Suc_le_eq
        elim!: arg_cong2[of _ _ _ _ U, OF _ refl, THEN iffD1, rotated]
          list_all3_mono_strong[THEN list_all3_list_all2I[of _ _ js]] list_all2_hdD
        dest!: 1(1)[rotated, OF _ wf_mbufn_map_tl[OF 1(3)] * _ 1(7)] split: prod.split if_splits)
qed

lemma mbuf2_take_add':
  assumes eq: "mbuf2_take f (mbuf2_add xs ys buf) = (zs, buf')"
    and pre: "wf_mbuf2' \<sigma> j n R \<phi> \<psi> buf"
    and xs: "list_all2 (\<lambda>i. qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>))
      [progress \<sigma> \<phi> j..<progress \<sigma> \<phi> j'] xs"
    and ys: "list_all2 (\<lambda>i. qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<psi>))
      [progress \<sigma> \<psi> j..<progress \<sigma> \<psi> j'] ys"
    and "j \<le> j'"
  shows "wf_mbuf2' \<sigma> j' n R \<phi> \<psi> buf'"
    and "list_all2 (\<lambda>i Z. \<exists>X Y.
      qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>) X \<and>
      qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<psi>) Y \<and>
      Z = f X Y)
      [min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)..<min (progress \<sigma> \<phi> j') (progress \<sigma> \<psi> j')] zs"
  using pre unfolding wf_mbuf2'_def
  by (force intro!: mbuf2_take_eqD[OF eq] wf_mbuf2_add[OF _ xs ys] progress_mono[OF \<open>j \<le> j'\<close>])+

lemma mbuf2t_take_add':
  assumes eq: "mbuf2t_take f z (mbuf2_add xs ys buf) nts = (z', buf', nts')"
    and pre_buf: "wf_mbuf2' \<sigma> j n R \<phi> \<psi> buf"
    and pre_nts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)..<j'] nts"
    and xs: "list_all2 (\<lambda>i. qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>))
      [progress \<sigma> \<phi> j..<progress \<sigma> \<phi> j'] xs"
    and ys: "list_all2 (\<lambda>i. qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<psi>))
      [progress \<sigma> \<psi> j..<progress \<sigma> \<psi> j'] ys"
    and "j \<le> j'"
  shows "wf_mbuf2' \<sigma> j' n R \<phi> \<psi> buf'"
    and "wf_ts \<sigma> j' \<phi> \<psi> nts'"
  using pre_buf pre_nts unfolding wf_mbuf2'_def wf_ts_def
  by (blast intro!: mbuf2t_take_eqD[OF eq] wf_mbuf2_add[OF _ xs ys] progress_mono[OF \<open>j \<le> j'\<close>]
      progress_le)+

lemma ok_0_progress: "ok 0 mr \<Longrightarrow> progress_regex \<sigma> (from_mregex mr []) j = j"
  by (induct mr) (auto simp: MFOTL.TT_def MFOTL.FF_def)

lemma atms_empty_progress: "safe_regex m g r \<Longrightarrow> atms r = {} \<Longrightarrow> progress_regex \<sigma> r j = j"
  by (induct r rule: safe_regex_induct) (auto split: if_splits)

lemma to_mregex_empty_progress: "safe_regex m g r \<Longrightarrow> to_mregex r = (mr, []) \<Longrightarrow>
  progress_regex \<sigma> r j = j"
  using from_mregex_eq ok_0_progress to_mregex_ok by fastforce

lemma atms_nonempty_progress:
  "safe_regex m g r \<Longrightarrow> atms r \<noteq> {} \<Longrightarrow> progress_regex \<sigma> r j = (MIN \<phi>\<in>atms r. progress \<sigma> \<phi> j)"
proof (induct r rule: safe_regex_induct)
  case (Plus m g r1 r2)
  then show ?case
    using progress_regex_le[of \<sigma> r1 j] progress_regex_le[of \<sigma> r2 j]
    by (cases "atms r1 = {} \<or> atms r2 = {}")
      (auto simp: Min_Un image_Un atms_empty_progress min_absorb1 min_absorb2 elim!: meta_mp)
next
  case (Times m g r1 r2)
  then show ?case 
    using progress_regex_le[of \<sigma> r1 j] progress_regex_le[of \<sigma> r2 j]
    by (cases "atms r1 = {} \<or> atms r2 = {}")
      (auto simp: Min_Un image_Un atms_empty_progress min_absorb1 min_absorb2 elim!: meta_mp)
qed (auto split: if_splits prod.splits formula.splits)

lemma to_mregex_nonempty_progress: "safe_regex m g r \<Longrightarrow> to_mregex r = (mr, \<phi>s) \<Longrightarrow> \<phi>s \<noteq> [] \<Longrightarrow>
   progress_regex \<sigma> r j = (MIN \<phi>\<in>set \<phi>s. progress \<sigma> \<phi> j)"
  using atms_nonempty_progress to_mregex_ok by fastforce

lemma to_mregex_progress: "safe_regex m g r \<Longrightarrow> to_mregex r = (mr, \<phi>s) \<Longrightarrow>
   progress_regex \<sigma> r j = (if \<phi>s = [] then j else (MIN \<phi>\<in>set \<phi>s. progress \<sigma> \<phi> j))"
  using to_mregex_nonempty_progress to_mregex_empty_progress by auto

lemma mbufnt_take_add':
  assumes eq: "mbufnt_take f z (mbufn_add xss buf) nts = (z', buf', nts')"
    and safe: "safe_regex m g r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and pre_buf: "wf_mbufn' \<sigma> j n R r buf"
    and pre_nts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress_regex \<sigma> r j..<j'] nts"
    and xss: "list_all3 list_all2
     (map (\<lambda>\<phi> i. qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>)) \<phi>s)
     (map2 upt (map (\<lambda>\<phi>. progress \<sigma> \<phi> j) \<phi>s) (map (\<lambda>\<phi>. progress \<sigma> \<phi> j') \<phi>s)) xss"
    and "j \<le> j'"
  shows "wf_mbufn' \<sigma> j' n R r buf'"
    and "wf_ts_regex \<sigma> j' r nts'"
  using pre_buf pre_nts mr safe xss \<open>j \<le> j'\<close> unfolding wf_mbufn'_def wf_ts_regex_def
  by (auto 0 3 simp: list.rel_map to_mregex_empty_progress to_mregex_nonempty_progress
    intro: progress_mono[OF \<open>j \<le> j'\<close>] list.rel_refl_strong progress_le
    dest: list_all2_lengthD elim!: mbufnt_take_eqD[OF eq wf_mbufn_add])

lemma mbuf2t_take_add_induct'[consumes 6, case_names base step]:
  assumes eq: "mbuf2t_take f z (mbuf2_add xs ys buf) nts = (z', buf', nts')"
    and pre_buf: "wf_mbuf2' \<sigma> j n R \<phi> \<psi> buf"
    and pre_nts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)..<j'] nts"
    and xs: "list_all2 (\<lambda>i. qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>))
      [progress \<sigma> \<phi> j..<progress \<sigma> \<phi> j'] xs"
    and ys: "list_all2 (\<lambda>i. qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<psi>))
      [progress \<sigma> \<psi> j..<progress \<sigma> \<psi> j'] ys"
    and "j \<le> j'"
    and base: "U (min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)) z"
    and step: "\<And>k X Y z. min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j) \<le> k \<Longrightarrow>
      Suc k \<le> progress \<sigma> \<phi> j' \<Longrightarrow> Suc k \<le> progress \<sigma> \<psi> j' \<Longrightarrow>
      qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) k \<phi>) X \<Longrightarrow>
      qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) k \<psi>) Y \<Longrightarrow>
      U k z \<Longrightarrow> U (Suc k) (f X Y (\<tau> \<sigma> k) z)"
  shows "U (min (progress \<sigma> \<phi> j') (progress \<sigma> \<psi> j')) z'"
  using pre_buf pre_nts unfolding wf_mbuf2'_def
  by (blast intro!: mbuf2t_take_induct[OF eq] wf_mbuf2_add[OF _ xs ys] progress_mono[OF \<open>j \<le> j'\<close>]
      progress_le base step)

lemma mbufnt_take_add_induct'[consumes 6, case_names base step]:
  assumes eq: "mbufnt_take f z (mbufn_add xss buf) nts = (z', buf', nts')"
    and safe: "safe_regex m g r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and pre_buf: "wf_mbufn' \<sigma> j n R r buf"
    and pre_nts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress_regex \<sigma> r j..<j'] nts"
    and xss: "list_all3 list_all2
     (map (\<lambda>\<phi> i. qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>)) \<phi>s)
     (map2 upt (map (\<lambda>\<phi>. progress \<sigma> \<phi> j) \<phi>s) (map (\<lambda>\<phi>. progress \<sigma> \<phi> j') \<phi>s)) xss"
    and "j \<le> j'"
    and base: "U (progress_regex \<sigma> r j) z"
    and step: "\<And>k Xs z. progress_regex \<sigma> r j \<le> k \<Longrightarrow> Suc k \<le> progress_regex \<sigma> r j' \<Longrightarrow>
      list_all2 (\<lambda>\<phi>. qtable n (MFOTL.fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) k \<phi>)) \<phi>s Xs \<Longrightarrow>
      U k z \<Longrightarrow> U (Suc k) (f Xs (\<tau> \<sigma> k) z)"
  shows "U (progress_regex \<sigma> r j') z'"
  using pre_buf pre_nts \<open>j \<le> j'\<close> to_mregex_progress[OF safe mr, of \<sigma> j'] to_mregex_empty_progress[OF safe, of mr \<sigma> j] base
  unfolding wf_mbufn'_def mr prod.case
  by (fastforce dest!: mbufnt_take_induct[OF eq wf_mbufn_add[OF _ xss] pre_nts, of U]
    simp: list.rel_map le_imp_diff_is_add ac_simps
    intro: progress_mono[OF \<open>j \<le> j'\<close>] list.rel_refl_strong progress_le
    intro!: base step  dest: list_all2_lengthD split: if_splits)

lemma progress_Until_le: "progress \<sigma> (MFOTL.Until \<phi> I \<psi>) j \<le> min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
  by (cases "right I") (auto simp: trans_le_add1 intro!: cInf_lower)

lemma progress_MatchF_le: "progress \<sigma> (MFOTL.MatchF I r) j \<le> progress_regex \<sigma> r j"
  by (cases "right I") (auto simp: trans_le_add1 intro!: cInf_lower)

lemma list_all2_upt_Cons: "P a x \<Longrightarrow> list_all2 P [Suc a..<b] xs \<Longrightarrow> Suc a \<le> b \<Longrightarrow>
  list_all2 P [a..<b] (x # xs)"
  by (simp add: list_all2_Cons2 upt_eq_Cons_conv)

lemma list_all2_upt_append: "list_all2 P [a..<b] xs \<Longrightarrow> list_all2 P [b..<c] ys \<Longrightarrow>
  a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> list_all2 P [a..<c] (xs @ ys)"
  by (induction xs arbitrary: a) (auto simp add: list_all2_Cons2 upt_eq_Cons_conv)

lemma list_all3_list_all2_conv: "list_all3 R xs xs ys = list_all2 (\<lambda>x. R x x) xs ys"
  by (auto simp: list_all3_conv_all_nth list_all2_conv_all_nth)

lemma map_split_map: "map_split f (map g xs) = map_split (f o g) xs"
  by (induct xs) auto

lemma map_split_alt: "map_split f xs = (map (fst o f) xs, map (snd o f) xs)"
  by (induct xs) (auto split: prod.splits)

lemma meval:
  assumes "wf_mformula \<sigma> j n R \<phi> \<phi>'"
  shows "case meval n (\<tau> \<sigma> j) (\<Gamma> \<sigma> j) \<phi> of (xs, \<phi>\<^sub>n) \<Rightarrow> wf_mformula \<sigma> (Suc j) n R \<phi>\<^sub>n \<phi>' \<and>
    list_all2 (\<lambda>i. qtable n (MFOTL.fv \<phi>') (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>'))
    [progress \<sigma> \<phi>' j..<progress \<sigma> \<phi>' (Suc j)] xs"
using assms proof (induction \<phi> arbitrary: n R \<phi>')
  case (MRel rel)
  then show ?case
    by (cases pred: wf_mformula)
      (auto simp add: ball_Un intro: wf_mformula.intros qtableI table_eq_rel eq_rel_eval_trm
        in_eq_rel qtable_empty qtable_unit_table)
next
  case (MPred e ts)
  then show ?case
    by (cases pred: wf_mformula)
      (auto 0 4 simp: table_def in_these_eq match_wf_tuple match_eval_trm image_iff dest: ex_match
        split: if_splits intro!: wf_mformula.intros qtableI elim!: bexI[rotated])
next
  case (MAnd \<phi> pos \<psi> buf)
  from MAnd.prems show ?case
    by (cases pred: wf_mformula)
      (auto simp: fvi_And sat_And fvi_And_Not sat_And_Not sat_the_restrict
       dest!: MAnd.IH split: if_splits prod.splits intro!: wf_mformula.And qtable_join
       dest: mbuf2_take_add' elim!: list.rel_mono_strong)
next
  case (MOr \<phi> \<psi> buf)
  from MOr.prems show ?case
    by (cases pred: wf_mformula)
      (auto dest!: MOr.IH split: if_splits prod.splits intro!: wf_mformula.Or qtable_union
       dest: mbuf2_take_add' elim!: list.rel_mono_strong)
next
  case (MNeg \<phi>)
  have *: "qtable n {} (mem_restr R) (\<lambda>v. P v) X \<Longrightarrow> 
    \<not> qtable n {} (mem_restr R) (\<lambda>v. \<not> P v) empty_table \<Longrightarrow> x \<in> X \<Longrightarrow> False" for P x X
    using qtable_empty_implies_empty_or_unit qtable_unit_empty_table by fastforce
  from MNeg.prems show ?case
    by (cases pred: wf_mformula)
      (auto 0 4 intro!: wf_mformula.Neg dest!: MNeg.IH
       simp add: list.rel_map
       dest: qtable_empty_implies_empty_or_unit qtable_unit_empty_table intro!: qtable_empty_unit_table
       elim!: list.rel_mono_strong elim: *)
next
  case (MExists \<phi>)
  from MExists.prems show ?case
    by (cases pred: wf_mformula)
      (force simp: list.rel_map fvi_Suc sat_fv_cong nth_Cons'
        intro!: wf_mformula.Exists dest!: MExists.IH qtable_project_fv 
        elim!: list.rel_mono_strong table_fvi_tl qtable_cong sat_fv_cong[THEN iffD1, rotated -1]
        split: if_splits)+
next
  case (MPrev I \<phi> first buf nts)
  from MPrev.prems show ?case
  proof (cases pred: wf_mformula)
    case (Prev \<psi>)
    let ?xs = "fst (meval n (\<tau> \<sigma> j) (\<Gamma> \<sigma> j) \<phi>)"
    let ?\<phi> = "snd (meval n (\<tau> \<sigma> j) (\<Gamma> \<sigma> j) \<phi>)"
    let ?ls = "fst (mprev_next I (buf @ ?xs) (nts @ [\<tau> \<sigma> j]))"
    let ?rs = "fst (snd (mprev_next I (buf @ ?xs) (nts @ [\<tau> \<sigma> j])))"
    let ?ts = "snd (snd (mprev_next I (buf @ ?xs) (nts @ [\<tau> \<sigma> j])))"
    let ?P = "\<lambda>i X. qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<psi>) X"
    let ?min = "min (progress \<sigma> \<psi> (Suc j)) (Suc j - 1)"
    from Prev MPrev.IH[of n R \<psi>] have IH: "wf_mformula \<sigma> (Suc j) n R ?\<phi> \<psi>" and
      "list_all2 ?P [progress \<sigma> \<psi> j..<progress \<sigma> \<psi> (Suc j)] ?xs" by auto
    with Prev(4,5) have "list_all2 (\<lambda>i X. if mem (\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i) I then ?P i X else X = empty_table)
        [min (progress \<sigma> \<psi> j) (j - 1)..<?min] ?ls \<and>
       list_all2 ?P [?min..<progress \<sigma> \<psi> (Suc j)] ?rs \<and>
       list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [?min..<Suc j] ?ts"
      by (intro mprev)
        (auto simp: progress_mono progress_le simp del: 
          intro!: list_all2_upt_append list_all2_appendI order.trans[OF min.cobounded1])
    moreover have "min (Suc (progress \<sigma> \<psi> j)) j = Suc (min (progress \<sigma> \<psi> j) (j-1))" if "j > 0"
      using that by auto
    ultimately show ?thesis using progress_mono[of j "Suc j" \<sigma> \<psi>] Prev(1,3) IH 
      by (auto simp: map_Suc_upt[symmetric] upt_Suc[of 0] list.rel_map qtable_empty_iff
        simp del: upt_Suc elim!: wf_mformula.Prev list.rel_mono_strong
        split: prod.split if_split_asm)
  qed simp
next
  case (MNext I \<phi> first nts)
  from MNext.prems show ?case
  proof (cases pred: wf_mformula)
    case (Next \<psi>)

    have min[simp]:
      "min (progress \<sigma> \<psi> j - Suc 0) (j - Suc 0) = progress \<sigma> \<psi> j - Suc 0"
      "min (progress \<sigma> \<psi> (Suc j) - Suc 0) j = progress \<sigma> \<psi> (Suc j) - Suc 0" for j
      using progress_le[of \<sigma> \<psi> j] progress_le[of \<sigma> \<psi> "Suc j"] by auto

    let ?xs = "fst (meval n (\<tau> \<sigma> j) (\<Gamma> \<sigma> j) \<phi>)"
    let ?ys = "case (?xs, first) of (_ # xs, True) \<Rightarrow> xs | _ \<Rightarrow> ?xs"
    let ?\<phi> = "snd (meval n (\<tau> \<sigma> j) (\<Gamma> \<sigma> j) \<phi>)"
    let ?ls = "fst (mprev_next I ?ys (nts @ [\<tau> \<sigma> j]))"
    let ?rs = "fst (snd (mprev_next I ?ys (nts @ [\<tau> \<sigma> j])))"
    let ?ts = "snd (snd (mprev_next I ?ys (nts @ [\<tau> \<sigma> j])))"
    let ?P = "\<lambda>i X. qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<psi>) X"
    let ?min = "min (progress \<sigma> \<psi> (Suc j) - 1) (Suc j - 1)"
    from Next MNext.IH[of n R \<psi>] have IH: "wf_mformula \<sigma> (Suc j) n R ?\<phi> \<psi>"
      "list_all2 ?P [progress \<sigma> \<psi> j..<progress \<sigma> \<psi> (Suc j)] ?xs" by auto
    with Next have "list_all2 (\<lambda>i X. if mem (\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i) I then ?P (Suc i) X else X = empty_table)
        [progress \<sigma> \<psi> j - 1..<?min] ?ls \<and>
       list_all2 ?P [Suc ?min..<progress \<sigma> \<psi> (Suc j)] ?rs \<and>
       list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [?min..<Suc j] ?ts" if "progress \<sigma> \<psi> j < progress \<sigma> \<psi> (Suc j)"
      using progress_le[of \<sigma> \<psi> j] that
      by (intro mnext)
        (auto simp: progress_mono list_all2_Cons2 upt_eq_Cons_conv
          intro!: list_all2_upt_append list_all2_appendI split: list.splits)
    then show ?thesis using progress_mono[of j "Suc j" \<sigma> \<psi>] progress_le[of \<sigma> \<psi> "Suc j"] Next IH
      by (cases "progress \<sigma> \<psi> (Suc j) > progress \<sigma> \<psi> j")
        (auto 0 3 simp: qtable_empty_iff le_Suc_eq le_diff_conv
         elim!: wf_mformula.Next list.rel_mono_strong list_all2_appendI
         split: prod.split list.splits if_split_asm)  (* slow 5 sec*)
  qed simp
next
  case (MSince pos \<phi> I \<psi> buf nts aux)
  note sat.simps[simp del]
  from MSince.prems obtain \<phi>'' \<phi>''' \<psi>'' where Since_eq: "\<phi>' = MFOTL.Since \<phi>''' I \<psi>''"
    and pos: "if pos then \<phi>''' = \<phi>'' else \<phi>''' = MFOTL.Neg \<phi>''"
    and pos_eq: "safe_formula \<phi>''' = pos"
    and \<phi>: "wf_mformula \<sigma> j n R \<phi> \<phi>''"
    and \<psi>: "wf_mformula \<sigma> j n R \<psi> \<psi>''"
    and fvi_subset: "MFOTL.fv \<phi>'' \<subseteq> MFOTL.fv \<psi>''"
    and buf: "wf_mbuf2' \<sigma> j n R \<phi>'' \<psi>'' buf"
    and nts: "wf_ts \<sigma> j \<phi>'' \<psi>'' nts"
    and aux: "wf_since_aux \<sigma> n R pos \<phi>'' I \<psi>'' aux (progress \<sigma> (MFOTL.Since \<phi>''' I \<psi>'') j)"
    by (cases pred: wf_mformula) (auto)
  have \<phi>''': "MFOTL.fv \<phi>''' = MFOTL.fv \<phi>''" "progress \<sigma> \<phi>''' j = progress \<sigma> \<phi>'' j" for j
    using pos by (simp_all split: if_splits)
  have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i)
    [min (progress \<sigma> \<phi>'' j) (progress \<sigma> \<psi>'' j)..<Suc j] (nts @ [\<tau> \<sigma> j])"
    using nts unfolding wf_ts_def
    by (auto simp add: progress_le[THEN min.coboundedI1] intro: list_all2_appendI)
  have update: "wf_since_aux \<sigma> n R pos \<phi>'' I \<psi>'' (snd (zs, aux')) (progress \<sigma> (MFOTL.Since \<phi>''' I \<psi>'') (Suc j)) \<and>
    list_all2 (\<lambda>i. qtable n (MFOTL.fv \<phi>''' \<union> MFOTL.fv \<psi>'') (mem_restr R)
      (\<lambda>v. MFOTL.sat \<sigma> (map the v) i (MFOTL.Since \<phi>''' I \<psi>'')))
      [progress \<sigma> (MFOTL.Since \<phi>''' I \<psi>'') j..<progress \<sigma> (MFOTL.Since \<phi>''' I \<psi>'') (Suc j)] (fst (zs, aux'))"
    if eval_\<phi>: "fst (meval n (\<tau> \<sigma> j) (\<Gamma> \<sigma> j) \<phi>) = xs"
      and eval_\<psi>: "fst (meval n (\<tau> \<sigma> j) (\<Gamma> \<sigma> j) \<psi>) = ys"
      and eq: "mbuf2t_take (\<lambda>r1 r2 t (zs, aux).
        case update_since I pos r1 r2 t aux of (z, x) \<Rightarrow> (zs @ [z], x))
        ([], aux) (mbuf2_add xs ys buf) (nts @ [\<tau> \<sigma> j]) = ((zs, aux'), buf', nts')"
    for xs ys zs aux' buf' nts'
    unfolding progress.simps \<phi>'''
  proof (rule mbuf2t_take_add_induct'[where j'="Suc j" and z'="(zs, aux')", OF eq buf nts_snoc],
      goal_cases xs ys _ base step)
    case xs
    then show ?case 
      using MSince.IH(1)[OF \<phi>] eval_\<phi> by auto
  next
    case ys
    then show ?case 
      using MSince.IH(2)[OF \<psi>] eval_\<psi> by auto
  next
    case base
    then show ?case
     using aux by (simp add: \<phi>''')
  next
    case (step k X Y z)
    then show ?case
      using fvi_subset pos
      by (auto simp: Un_absorb1 elim!: update_since(1) list_all2_appendI dest!: update_since(2)
        split: prod.split if_splits)
  qed simp
  with MSince.IH(1)[OF \<phi>] MSince.IH(2)[OF \<psi>] show ?case
    by (auto 0 3 simp: Since_eq split: prod.split
      intro: wf_mformula.Since[OF _  _ pos pos_eq fvi_subset]
      elim: mbuf2t_take_add'(1)[OF _ buf nts_snoc] mbuf2t_take_add'(2)[OF _ buf nts_snoc])
next
  case (MUntil pos \<phi> I \<psi> buf nts aux)
  note sat.simps[simp del] progress.simps[simp del]
  from MUntil.prems obtain \<phi>'' \<phi>''' \<psi>'' where Until_eq: "\<phi>' = MFOTL.Until \<phi>''' I \<psi>''"
    and pos: "if pos then \<phi>''' = \<phi>'' else \<phi>''' = MFOTL.Neg \<phi>''"
    and pos_eq: "safe_formula \<phi>''' = pos"
    and \<phi>: "wf_mformula \<sigma> j n R \<phi> \<phi>''"
    and \<psi>: "wf_mformula \<sigma> j n R \<psi> \<psi>''"
    and fvi_subset: "MFOTL.fv \<phi>'' \<subseteq> MFOTL.fv \<psi>''"
    and buf: "wf_mbuf2' \<sigma> j n R \<phi>'' \<psi>'' buf"
    and nts: "wf_ts \<sigma> j \<phi>'' \<psi>'' nts"
    and aux: "wf_until_aux \<sigma> n R pos \<phi>'' I \<psi>'' aux (progress \<sigma> (MFOTL.Until \<phi>''' I \<psi>'') j)"
    and length_aux: "progress \<sigma> (MFOTL.Until \<phi>''' I \<psi>'') j + length aux =
      min (progress \<sigma> \<phi>'' j) (progress \<sigma> \<psi>'' j)"
    by (cases pred: wf_mformula) (auto)
  have \<phi>''': "progress \<sigma> \<phi>''' j = progress \<sigma> \<phi>'' j" for j
    using pos by (simp_all add: progress.simps split: if_splits)
  have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i)
    [min (progress \<sigma> \<phi>'' j) (progress \<sigma> \<psi>'' j)..<Suc j] (nts @ [\<tau> \<sigma> j])"
    using nts unfolding wf_ts_def
    by (auto simp add: progress_le[THEN min.coboundedI1] intro: list_all2_appendI)
  {
    fix xs ys zs aux' aux'' buf' nts'
    assume eval_\<phi>: "fst (meval n (\<tau> \<sigma> j) (\<Gamma> \<sigma> j) \<phi>) = xs"
      and eval_\<psi>: "fst (meval n (\<tau> \<sigma> j) (\<Gamma> \<sigma> j) \<psi>) = ys"
      and eq1: "mbuf2t_take (update_until I pos) aux (mbuf2_add xs ys buf) (nts @ [\<tau> \<sigma> j]) =
        (aux', buf', nts')"
      and eq2: "eval_until I (case nts' of [] \<Rightarrow> \<tau> \<sigma> j | nt # _ \<Rightarrow> nt) aux' = (zs, aux'')"
    have update1: "wf_until_aux \<sigma> n R pos \<phi>'' I \<psi>'' aux' (progress \<sigma> (MFOTL.Until \<phi>''' I \<psi>'') j) \<and>
      progress \<sigma> (MFOTL.Until \<phi>''' I \<psi>'') j + length aux' =
        min (progress \<sigma> \<phi>''' (Suc j)) (progress \<sigma> \<psi>'' (Suc j))"
      using MUntil.IH(1)[OF \<phi>] eval_\<phi> MUntil.IH(2)[OF \<psi>]
        eval_\<psi> nts_snoc nts_snoc length_aux aux fvi_subset
      unfolding \<phi>'''
      by (elim mbuf2t_take_add_induct'[where j'="Suc j", OF eq1 buf])
        (auto simp: length_update_until elim: wf_update_until)
    have nts': "wf_ts \<sigma> (Suc j) \<phi>'' \<psi>'' nts'"
      using MUntil.IH(1)[OF \<phi>] eval_\<phi> MUntil.IH(2)[OF \<psi>] eval_\<psi> nts_snoc
      unfolding wf_ts_def
      by (intro mbuf2t_take_eqD(2)[OF eq1]) (auto simp: progress_mono progress_le
        intro: wf_mbuf2_add buf[unfolded wf_mbuf2'_def])
    have "i \<le> progress \<sigma> (MFOTL.Until \<phi>''' I \<psi>'') (Suc j) \<Longrightarrow>
      wf_until_aux \<sigma> n R pos \<phi>'' I \<psi>'' aux' i \<Longrightarrow>
      i + length aux' = min (progress \<sigma> \<phi>''' (Suc j)) (progress \<sigma> \<psi>'' (Suc j)) \<Longrightarrow>
      wf_until_aux \<sigma> n R pos \<phi>'' I \<psi>'' aux'' (progress \<sigma> (MFOTL.Until \<phi>''' I \<psi>'') (Suc j)) \<and>
        i + length zs = progress \<sigma> (MFOTL.Until \<phi>''' I \<psi>'') (Suc j) \<and>
        i + length zs + length aux'' = min (progress \<sigma> \<phi>''' (Suc j)) (progress \<sigma> \<psi>'' (Suc j)) \<and>
        list_all2 (\<lambda>i. qtable n (MFOTL.fv \<psi>'') (mem_restr R)
          (\<lambda>v. MFOTL.sat \<sigma> (map the v) i (MFOTL.Until (if pos then \<phi>'' else MFOTL.Neg \<phi>'') I \<psi>'')))
          [i..<i + length zs] zs" for i
      using eq2
    proof (induction aux' arbitrary: zs aux'' i)
      case Nil
      then show ?case by (auto dest!: antisym[OF progress_Until_le])
    next
      case (Cons a aux')
      obtain t a1 a2 where "a = (t, a1, a2)" by (cases a)
      from Cons.prems(2) have aux': "wf_until_aux \<sigma> n R pos \<phi>'' I \<psi>'' aux' (Suc i)"
        by (rule wf_until_aux_Cons)
      from Cons.prems(2) have 1: "t = \<tau> \<sigma> i"
        unfolding \<open>a = (t, a1, a2)\<close> by (rule wf_until_aux_Cons1)
      from Cons.prems(2) have 3: "qtable n (MFOTL.fv \<psi>'') (mem_restr R) (\<lambda>v.
        (\<exists>j\<ge>i. j < Suc (i + length aux') \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> MFOTL.sat \<sigma> (map the v) j \<psi>'' \<and>
        (\<forall>k\<in>{i..<j}. if pos then MFOTL.sat \<sigma> (map the v) k \<phi>'' else \<not> MFOTL.sat \<sigma> (map the v) k \<phi>''))) a2"
        unfolding \<open>a = (t, a1, a2)\<close> by (rule wf_until_aux_Cons3)
      from Cons.prems(3) have Suc_i_aux': "Suc i + length aux' =
          min (progress \<sigma> \<phi>''' (Suc j)) (progress \<sigma> \<psi>'' (Suc j))"
        by simp
      have "i \<ge> progress \<sigma> (MFOTL.Until \<phi>''' I \<psi>'') (Suc j)"
        if "enat (case nts' of [] \<Rightarrow> \<tau> \<sigma> j | nt # x \<Rightarrow> nt) \<le> enat t + right I"
        using that nts' unfolding wf_ts_def progress.simps
        by (auto simp add: 1 list_all2_Cons2 upt_eq_Cons_conv \<phi>'''
          intro!: cInf_lower \<tau>_mono elim!: order.trans[rotated] simp del: upt_Suc split: if_splits list.splits)
      moreover
      have "Suc i \<le> progress \<sigma> (MFOTL.Until \<phi>''' I \<psi>'') (Suc j)"
        if "enat t + right I < enat (case nts' of [] \<Rightarrow> \<tau> \<sigma> j | nt # x \<Rightarrow> nt)"
      proof -
        from that obtain m where m: "right I = enat m" by (cases "right I") auto
        have \<tau>_min:  "\<tau> \<sigma> (min j k) = min (\<tau> \<sigma> j) (\<tau> \<sigma> k)" for k
          by (simp add: min_of_mono monoI)
        have le_progress_iff[simp]: "i \<le> progress \<sigma> \<phi> i \<longleftrightarrow> progress \<sigma> \<phi> i = i" for \<phi> i
          using progress_le[of \<sigma> \<phi> i] by auto
        have min_Suc[simp]: "min j (Suc j) = j" by auto
        let ?X = "{i. \<forall>k. k < Suc j \<and> k \<le>min (progress \<sigma> \<phi>''' (Suc j)) (progress \<sigma> \<psi>'' (Suc j)) \<longrightarrow> enat (\<tau> \<sigma> k) \<le> enat (\<tau> \<sigma> i) + right I}"
        let ?min = "min j (min (progress \<sigma> \<phi>'' (Suc j)) (progress \<sigma> \<psi>'' (Suc j)))"
        have "\<tau> \<sigma> ?min \<le> \<tau> \<sigma> j"
          by (rule \<tau>_mono) auto
        from m have "?X \<noteq> {}"
          by (auto dest!: \<tau>_mono[of _ "progress \<sigma> \<phi>'' (Suc j)" \<sigma>]
           simp: not_le not_less \<phi>''' intro!: exI[of _ "progress \<sigma> \<phi>'' (Suc j)"])
        from m show ?thesis
          using that nts' unfolding wf_ts_def progress.simps
          by (intro cInf_greatest[OF \<open>?X \<noteq> {}\<close>])
            (auto simp: 1 \<phi>''' not_le not_less list_all2_Cons2 upt_eq_Cons_conv less_Suc_eq
              simp del: upt_Suc split: list.splits if_splits
              dest!: spec[of _ "?min"] less_le_trans[of "\<tau> \<sigma> i + m" "\<tau> \<sigma> _" "\<tau> \<sigma> _ + m"] less_\<tau>D)
      qed
      moreover have *: "k < progress \<sigma> \<psi> (Suc j)" if
        "enat (\<tau> \<sigma> i) + right I < enat (case nts' of [] \<Rightarrow> \<tau> \<sigma> j | nt # x \<Rightarrow> nt)"
        "enat (\<tau> \<sigma> k - \<tau> \<sigma> i) \<le> right I" "\<psi> = \<psi>'' \<or> \<psi> = \<phi>''" for k \<psi>
      proof -
        from that(1,2) obtain m where "right I = enat m"
           "\<tau> \<sigma> i + m < (case nts' of [] \<Rightarrow> \<tau> \<sigma> j | nt # x \<Rightarrow> nt)" "\<tau> \<sigma> k - \<tau> \<sigma> i \<le> m"
          by (cases "right I") auto
        with that(3) nts' progress_le[of \<sigma> \<psi>'' "Suc j"] progress_le[of \<sigma> \<phi>'' "Suc j"]
        show ?thesis
          unfolding wf_ts_def le_diff_conv
          by (auto simp: not_le list_all2_Cons2 upt_eq_Cons_conv less_Suc_eq add.commute
            simp del: upt_Suc split: list.splits if_splits dest!: le_less_trans[of "\<tau> \<sigma> k"] less_\<tau>D)
      qed
      ultimately show ?case using Cons.prems Suc_i_aux'[simplified]
        unfolding \<open>a = (t, a1, a2)\<close>
        by (auto simp: \<phi>''' 1 sat.simps upt_conv_Cons dest!:  Cons.IH[OF _ aux' Suc_i_aux']
          simp del: upt_Suc split: if_splits prod.splits intro!: iff_exI qtable_cong[OF 3 refl])
    qed
    note this[OF progress_mono[OF le_SucI, OF order.refl] conjunct1[OF update1] conjunct2[OF update1]]
  }
  note update = this
  from MUntil.IH(1)[OF \<phi>] MUntil.IH(2)[OF \<psi>] pos pos_eq fvi_subset show ?case
    by (auto 0 4 simp: Until_eq \<phi>''' progress.simps(3) split: prod.split if_splits
      dest!: update[OF refl refl, rotated]
      intro!: wf_mformula.Until
      elim!: list.rel_mono_strong qtable_cong
      elim: mbuf2t_take_add'(1)[OF _ buf nts_snoc] mbuf2t_take_add'(2)[OF _ buf nts_snoc])
next
  case (MMatchP I mr mrs \<phi>s buf nts aux)
  note sat.simps[simp del] mbufnt_take.simps[simp del] mbufn_add.simps[simp del]
  from MMatchP.prems obtain r \<psi>s where eq: "\<phi>' = MFOTL.MatchP I r"
    and safe: "safe_regex Past Safe r"
    and mr: "to_mregex r = (mr, \<psi>s)"
    and mrs: "mrs = sorted_list_of_set (RPDs mr)"
    and \<psi>s: "list_all2 (wf_mformula \<sigma> j n R) \<phi>s \<psi>s"
    and buf: "wf_mbufn' \<sigma> j n R r buf"
    and nts: "wf_ts_regex \<sigma> j r nts"
    and aux: "wf_matchP_aux \<sigma> n R I r aux (progress \<sigma> (MFOTL.MatchP I r) j)"
    by (cases pred: wf_mformula) (auto)
  have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress_regex \<sigma> r j..<Suc j] (nts @ [\<tau> \<sigma> j])"
    using nts unfolding wf_ts_regex_def
    by (auto simp add: progress_regex_le intro: list_all2_appendI)
  have update: "wf_matchP_aux \<sigma> n R I r (snd (zs, aux')) (progress \<sigma> (MFOTL.MatchP I r) (Suc j)) \<and>
    list_all2 (\<lambda>i. qtable n (MFOTL.fv_regex r) (mem_restr R)
      (\<lambda>v. MFOTL.sat \<sigma> (map the v) i (MFOTL.MatchP I r)))
      [progress \<sigma> (MFOTL.MatchP I r) j..<progress \<sigma> (MFOTL.MatchP I r) (Suc j)] (fst (zs, aux'))"
    if eval: "map (fst o meval n (\<tau> \<sigma> j) (\<Gamma> \<sigma> j)) \<phi>s = xss"
      and eq: "mbufnt_take (\<lambda>rels t (zs, aux).
        case update_matchP n I mr mrs rels t aux of (z, x) \<Rightarrow> (zs @ [z], x))
        ([], aux) (mbufn_add xss buf) (nts @ [\<tau> \<sigma> j]) = ((zs, aux'), buf', nts')"
    for xss zs aux' buf' nts'
    unfolding progress.simps
  proof (rule mbufnt_take_add_induct'[where j'="Suc j" and z'="(zs, aux')", OF eq safe mr buf nts_snoc],
      goal_cases xss _ base step)
    case xss
    then show ?case 
      using eval \<psi>s
      by (auto simp: list_all3_map map2_map_map list_all3_list_all2_conv list.rel_map
         list.rel_flip[symmetric, of _ \<psi>s \<phi>s] dest!: MMatchP.IH(1)
         elim!: list.rel_mono_strong split: prod.splits)
  next
    case base
    then show ?case
     using aux by auto
  next
    case (step k Xs z)
    then show ?case
      by (auto simp: Un_absorb1 mrs safe mr elim!: update_matchP(1) list_all2_appendI
        dest!: update_matchP(2) split: prod.split)
  qed simp
  then show ?case using \<psi>s
    by (auto simp: eq mr mrs safe map_split_alt list.rel_flip[symmetric, of _ \<psi>s \<phi>s]
      list_all3_map map2_map_map list_all3_list_all2_conv list.rel_map intro!: wf_mformula.intros
      elim!: list.rel_mono_strong mbufnt_take_add'(1)[OF _ safe mr buf nts_snoc]
                                  mbufnt_take_add'(2)[OF _ safe mr buf nts_snoc]
      dest!: MMatchP.IH split: prod.splits)
next
  case (MMatchF I mr mrs \<phi>s buf nts aux)
  note sat.simps[simp del] mbufnt_take.simps[simp del] mbufn_add.simps[simp del] progress.simps[simp del]
  from MMatchF.prems obtain r \<psi>s where eq: "\<phi>' = MFOTL.MatchF I r"
    and safe: "safe_regex Future Safe r"
    and mr: "to_mregex r = (mr, \<psi>s)"
    and mrs: "mrs = sorted_list_of_set (LPDs mr)"
    and \<psi>s: "list_all2 (wf_mformula \<sigma> j n R) \<phi>s \<psi>s"
    and buf: "wf_mbufn' \<sigma> j n R r buf"
    and nts: "wf_ts_regex \<sigma> j r nts"
    and aux: "wf_matchF_aux \<sigma> n R I r aux (progress \<sigma> (MFOTL.MatchF I r) j) 0"
    and length_aux: "progress \<sigma> (MFOTL.MatchF I r) j + length aux = progress_regex \<sigma> r j"
    by (cases pred: wf_mformula) (auto)
  have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i)
    [progress_regex \<sigma> r j..<Suc j] (nts @ [\<tau> \<sigma> j])"
    using nts unfolding wf_ts_regex_def
    by (auto simp add: progress_regex_le intro: list_all2_appendI)
  {
    fix xss zs aux' aux'' buf' nts'
    assume eval: "map (fst o meval n (\<tau> \<sigma> j) (\<Gamma> \<sigma> j)) \<phi>s = xss"
      and eq1: "mbufnt_take (update_matchF n I mr mrs) aux (mbufn_add xss buf) (nts @ [\<tau> \<sigma> j]) =
        (aux', buf', nts')"
      and eq2: "eval_matchF I mr (case nts' of [] \<Rightarrow> \<tau> \<sigma> j | nt # _ \<Rightarrow> nt) aux' = (zs, aux'')"
    have update1: "wf_matchF_aux \<sigma> n R I r aux' (progress \<sigma> (MFOTL.MatchF I r) j) 0 \<and>
      progress \<sigma> (MFOTL.MatchF I r) j + length aux' = progress_regex \<sigma> r (Suc j)"
      using eval nts_snoc nts_snoc length_aux aux \<psi>s
      by (elim mbufnt_take_add_induct'[where j'="Suc j", OF eq1 safe mr buf])
        (auto simp: length_update_matchF
         list_all3_map map2_map_map list_all3_list_all2_conv list.rel_map list.rel_flip[symmetric, of _ \<psi>s \<phi>s]
         dest!:  MMatchF.IH elim: wf_update_matchF[OF _ safe mr mrs] elim!: list.rel_mono_strong)
    have nts': "wf_ts_regex \<sigma> (Suc j) r nts'"
      using eval eval nts_snoc \<psi>s
      unfolding wf_ts_regex_def
      by (intro mbufnt_take_eqD(2)[OF eq1 wf_mbufn_add[where js'="map (\<lambda>\<phi>. progress \<sigma> \<phi> (Suc j)) \<psi>s", 
        OF buf[unfolded wf_mbufn'_def mr prod.case]]])
        (auto simp: progress_mono progress_regex_le progress_le to_mregex_progress[OF safe mr]
         list_all3_map map2_map_map list_all3_list_all2_conv list.rel_map list.rel_flip[symmetric, of _ \<psi>s \<phi>s]
         list_all2_Cons1 elim!: list.rel_mono_strong intro!: list.rel_refl_strong dest!: MMatchF.IH)
    have "i \<le> progress \<sigma> (MFOTL.MatchF I r) (Suc j) \<Longrightarrow>
      wf_matchF_aux \<sigma> n R I r aux' i 0 \<Longrightarrow>
      i + length aux' = progress_regex \<sigma> r (Suc j) \<Longrightarrow>
      wf_matchF_aux \<sigma> n R I r aux'' (progress \<sigma> (MFOTL.MatchF I r) (Suc j)) 0 \<and>
        i + length zs = progress \<sigma> (MFOTL.MatchF I r) (Suc j) \<and>
        i + length zs + length aux'' = progress_regex \<sigma> r (Suc j) \<and>
        list_all2 (\<lambda>i. qtable n (MFOTL.fv_regex r) (mem_restr R)
          (\<lambda>v. MFOTL.sat \<sigma> (map the v) i (MFOTL.MatchF I r)))
          [i..<i + length zs] zs" for i
      using eq2
    proof (induction aux' arbitrary: zs aux'' i)
      case Nil
      then show ?case by (auto dest!: antisym[OF progress_MatchF_le])
    next
      case (Cons a aux')
      obtain t rels rel where "a = (t, rels, rel)" by (cases a)
      from Cons.prems(2) have aux': "wf_matchF_aux \<sigma> n R I r aux' (Suc i) 0"
        by (rule wf_matchF_aux_Cons)
      from Cons.prems(2) have 1: "t = \<tau> \<sigma> i"
        unfolding \<open>a = (t, rels, rel)\<close> by (rule wf_matchF_aux_Cons1)
      from Cons.prems(2) have 3: "qtable n (MFOTL.fv_regex r) (mem_restr R) (\<lambda>v.
        (\<exists>j\<ge>i. j < Suc (i + length aux') \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> MFOTL.match \<sigma> (map the v) r i j)) rel"
        unfolding \<open>a = (t, rels, rel)\<close> using wf_matchF_aux_Cons3 by force
      from Cons.prems(3) have Suc_i_aux': "Suc i + length aux' = progress_regex \<sigma> r (Suc j)"
        by simp
      have "i \<ge> progress \<sigma> (MFOTL.MatchF I r) (Suc j)"
        if "enat (case nts' of [] \<Rightarrow> \<tau> \<sigma> j | nt # x \<Rightarrow> nt) \<le> enat t + right I"
        using that nts' unfolding wf_ts_regex_def progress.simps
        by (auto simp add: 1 list_all2_Cons2 upt_eq_Cons_conv
          intro!: cInf_lower \<tau>_mono elim!: order.trans[rotated] simp del: upt_Suc split: if_splits list.splits)
      moreover
      have "Suc i \<le> progress \<sigma> (MFOTL.MatchF I r) (Suc j)"
        if "enat t + right I < enat (case nts' of [] \<Rightarrow> \<tau> \<sigma> j | nt # x \<Rightarrow> nt)"
      proof -
        from that obtain m where m: "right I = enat m" by (cases "right I") auto
        have \<tau>_min:  "\<tau> \<sigma> (min j k) = min (\<tau> \<sigma> j) (\<tau> \<sigma> k)" for k
          by (simp add: min_of_mono monoI)
        have le_progress_iff[simp]: "i \<le> progress \<sigma> \<phi> i \<longleftrightarrow> progress \<sigma> \<phi> i = i" for \<phi> i
          using progress_le[of \<sigma> \<phi> i] by auto
        have min_Suc[simp]: "min j (Suc j) = j" by auto
        let ?X = "{i. \<forall>k. k < Suc j \<and> k \<le> progress_regex \<sigma> r (Suc j) \<longrightarrow> enat (\<tau> \<sigma> k) \<le> enat (\<tau> \<sigma> i) + right I}"
        let ?min = "min j (progress_regex \<sigma> r (Suc j))"
        have "\<tau> \<sigma> ?min \<le> \<tau> \<sigma> j"
          by (rule \<tau>_mono) auto
        from m have "?X \<noteq> {}"
          by (auto dest!: less_\<tau>D add_lessD1 simp: not_le not_less)
        from m show ?thesis
          using that nts' progress_regex_le[of \<sigma> r "Suc j"] unfolding wf_ts_regex_def progress.simps
          by (intro cInf_greatest[OF \<open>?X \<noteq> {}\<close>])
            (auto simp: 1 not_le not_less list_all2_Cons2 upt_eq_Cons_conv less_Suc_eq
              simp del: upt_Suc split: list.splits if_splits
              dest!: spec[of _ "?min"] less_le_trans[of "\<tau> \<sigma> i + m" "\<tau> \<sigma> _" "\<tau> \<sigma> _ + m"] less_\<tau>D)
      qed
      moreover have *: "k < progress_regex \<sigma> r (Suc j)" if
        "enat (\<tau> \<sigma> i) + right I < enat (case nts' of [] \<Rightarrow> \<tau> \<sigma> j | nt # x \<Rightarrow> nt)"
        "enat (\<tau> \<sigma> k - \<tau> \<sigma> i) \<le> right I" for k
      proof -
        from that(1,2) obtain m where "right I = enat m"
           "\<tau> \<sigma> i + m < (case nts' of [] \<Rightarrow> \<tau> \<sigma> j | nt # x \<Rightarrow> nt)" "\<tau> \<sigma> k - \<tau> \<sigma> i \<le> m"
          by (cases "right I") auto
        with nts' progress_regex_le[of \<sigma> r "Suc j"]
        show ?thesis
          unfolding wf_ts_regex_def le_diff_conv
          by (auto simp: not_le list_all2_Cons2 upt_eq_Cons_conv less_Suc_eq add.commute
            simp del: upt_Suc split: list.splits if_splits dest!: le_less_trans[of "\<tau> \<sigma> k"] less_\<tau>D)
      qed
      ultimately show ?case using Cons.prems Suc_i_aux'[simplified]
        unfolding \<open>a = (t, rels, rel)\<close>
        by (auto simp: 1 sat.simps upt_conv_Cons dest!:  Cons.IH[OF _ aux' Suc_i_aux']
          simp del: upt_Suc split: if_splits prod.splits intro!: iff_exI qtable_cong[OF 3 refl])
        
    qed
    note this[OF progress_mono[OF le_SucI, OF order.refl] conjunct1[OF update1] conjunct2[OF update1]]
  }
  note update = this[OF refl, rotated]
  show ?case using \<psi>s
    by (auto simp: eq mr mrs safe map_split_alt list.rel_flip[symmetric, of _ \<psi>s \<phi>s]
      list_all3_map map2_map_map list_all3_list_all2_conv list.rel_map intro!: wf_mformula.intros
      elim!: list.rel_mono_strong mbufnt_take_add'(1)[OF _ safe mr buf nts_snoc]
                                  mbufnt_take_add'(2)[OF _ safe mr buf nts_snoc]
      dest!: MMatchF.IH update split: prod.splits)
qed


subsubsection \<open>Monitor Step\<close>

lemma wf_mstate_mstep: "wf_mstate \<phi> \<pi> R st \<Longrightarrow> last_ts \<pi> \<le> snd tdb \<Longrightarrow>
  wf_mstate \<phi> (psnoc \<pi> tdb) R (snd (mstep tdb st))"
  unfolding wf_mstate_def mstep_def Let_def
  by (fastforce simp add: progress_mono le_imp_diff_is_add split: prod.splits
      elim!: prefix_of_psnocE dest: meval list_all2_lengthD)

lemma mstep_output_iff:
  assumes "wf_mstate \<phi> \<pi> R st" "last_ts \<pi> \<le> snd tdb" "prefix_of (psnoc \<pi> tdb) \<sigma>" "mem_restr R v" 
  shows "(i, v) \<in> fst (mstep tdb st) \<longleftrightarrow>
    progress \<sigma> \<phi> (plen \<pi>) \<le> i \<and> i < progress \<sigma> \<phi> (Suc (plen \<pi>)) \<and>
    wf_tuple (MFOTL.nfv \<phi>) (MFOTL.fv \<phi>) v \<and> MFOTL.sat \<sigma> (map the v) i \<phi>"
proof -
  from prefix_of_psnocE[OF assms(3,2)] have "prefix_of \<pi> \<sigma>" 
    "\<Gamma> \<sigma> (plen \<pi>) = fst tdb" "\<tau> \<sigma> (plen \<pi>) = snd tdb" by auto
  moreover from assms(1) \<open>prefix_of \<pi> \<sigma>\<close> have "mstate_n st = MFOTL.nfv \<phi>"
    "mstate_i st = progress \<sigma> \<phi> (plen \<pi>)" "wf_mformula \<sigma> (plen \<pi>) (mstate_n st) R (mstate_m st) \<phi>"
    unfolding wf_mstate_def by blast+
  moreover from meval[OF \<open>wf_mformula \<sigma> (plen \<pi>) (mstate_n st) R (mstate_m st) \<phi>\<close>] obtain Vs st' where
    "meval (mstate_n st) (\<tau> \<sigma> (plen \<pi>)) (\<Gamma> \<sigma> (plen \<pi>)) (mstate_m st) = (Vs, st')"
    "wf_mformula \<sigma> (Suc (plen \<pi>)) (mstate_n st) R st' \<phi>"
    "list_all2 (\<lambda>i. qtable (mstate_n st) (fv \<phi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>))
      [progress \<sigma> \<phi> (plen \<pi>)..<progress \<sigma> \<phi> (Suc (plen \<pi>))] Vs" by blast
  moreover from this assms(4) have "qtable (mstate_n st) (fv \<phi>) (mem_restr R)
    (\<lambda>v. MFOTL.sat \<sigma> (map the v) i \<phi>) (Vs ! (i - progress \<sigma> \<phi> (plen \<pi>)))"
      if "progress \<sigma> \<phi> (plen \<pi>) \<le> i" "i < progress \<sigma> \<phi> (Suc (plen \<pi>))"
    using that by (auto simp: list_all2_conv_all_nth
      dest!: spec[of _ "(i - progress \<sigma> \<phi> (plen \<pi>))"])
  ultimately show ?thesis
    using assms(4) unfolding mstep_def Let_def
    by (auto simp: in_set_enumerate_eq list_all2_conv_all_nth progress_mono le_imp_diff_is_add
      elim!: in_qtableE in_qtableI intro!: bexI[of _ "(i, Vs ! (i - progress \<sigma> \<phi> (plen \<pi>)))"])
qed


subsubsection \<open>Monitor Function\<close>

definition minit_safe where
  "minit_safe \<phi> = (if mmonitorable_exec \<phi> then minit \<phi> else undefined)"

lemma minit_safe_minit: "mmonitorable \<phi> \<Longrightarrow> minit_safe \<phi> = minit \<phi>"
  unfolding minit_safe_def monitorable_formula_code by simp

lemma mstep_mverdicts:
  assumes wf: "wf_mstate \<phi> \<pi> R st"
    and le[simp]: "last_ts \<pi> \<le> snd tdb"
    and restrict: "mem_restr R v"
  shows "(i, v) \<in> fst (mstep tdb st) \<longleftrightarrow> (i, v) \<in> mverdicts \<phi> (psnoc \<pi> tdb) - mverdicts \<phi> \<pi>"
proof -
  obtain \<sigma> where p2: "prefix_of (psnoc \<pi> tdb) \<sigma>"
    using ex_prefix_of by blast
  with le have p1: "prefix_of \<pi> \<sigma>" by (blast elim!: prefix_of_psnocE)
  show ?thesis
    unfolding verimon.verdicts_def
    by (auto 0 3 simp: p2 progress_prefix_conv[OF _ p1] sat_prefix_conv[OF _ p1] not_less
      dest:  mstep_output_iff[OF wf le p2 restrict, THEN iffD1] spec[of _ \<sigma>]
             mstep_output_iff[OF wf le _ restrict, THEN iffD1] verimon.progress_sat_cong[OF p1]
      intro: mstep_output_iff[OF wf le p2 restrict, THEN iffD2] p1)
qed

primrec msteps0 where
  "msteps0 [] st = ({}, st)"
| "msteps0 (tdb # \<pi>) st =
    (let (V', st') = mstep tdb st; (V'', st'') = msteps0 \<pi> st' in (V' \<union> V'', st''))"

primrec msteps0_stateless where
  "msteps0_stateless [] st = {}"
| "msteps0_stateless (tdb # \<pi>) st = (let (V', st') = mstep tdb st in V' \<union> msteps0_stateless \<pi> st')"

lemma msteps0_msteps0_stateless: "fst (msteps0 w st) = msteps0_stateless w st"
  by (induct w arbitrary: st) (auto simp: split_beta)

lift_definition msteps :: "'a MFOTL.prefix \<Rightarrow> 'a mstate \<Rightarrow> (nat \<times> 'a option list) set \<times> 'a mstate"
  is msteps0 .

lift_definition msteps_stateless :: "'a MFOTL.prefix \<Rightarrow> 'a mstate \<Rightarrow> (nat \<times> 'a option list) set"
  is msteps0_stateless .

lemma msteps_msteps_stateless: "fst (msteps w st) = msteps_stateless w st"
  by transfer (rule msteps0_msteps0_stateless)

lemma msteps0_snoc: "msteps0 (\<pi> @ [tdb]) st =
   (let (V', st') = msteps0 \<pi> st; (V'', st'') = mstep tdb st' in (V' \<union> V'', st''))"
  by (induct \<pi> arbitrary: st) (auto split: prod.splits)

lemma msteps_psnoc: "last_ts \<pi> \<le> snd tdb \<Longrightarrow> msteps (psnoc \<pi> tdb) st =
   (let (V', st') = msteps \<pi> st; (V'', st'') = mstep tdb st' in (V' \<union> V'', st''))"
  by transfer (auto simp: msteps0_snoc split: list.splits prod.splits if_splits)

definition monitor where
  "monitor \<phi> \<pi> = msteps_stateless \<pi> (minit_safe \<phi>)"

lemma Suc_length_conv_snoc: "(Suc n = length xs) = (\<exists>y ys. xs = ys @ [y] \<and> length ys = n)"
  by (cases xs rule: rev_cases) auto

lemma wf_mstate_msteps: "wf_mstate \<phi> \<pi> R st \<Longrightarrow> mem_restr R v \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow>
  X = msteps (pdrop (plen \<pi>) \<pi>') st \<Longrightarrow> wf_mstate \<phi> \<pi>' R (snd X) \<and>
  ((i, v) \<in> fst X) = ((i, v) \<in> mverdicts \<phi> \<pi>' - mverdicts \<phi> \<pi>)"
proof (induct "plen \<pi>' - plen \<pi>" arbitrary: X st \<pi> \<pi>')
  case 0
  from 0(1,4,5) have "\<pi> = \<pi>'"  "X = ({}, st)"
    by (transfer; auto)+
  with 0(2) show ?case by simp
next
  case (Suc x)
  from Suc(2,5) obtain \<pi>'' tdb where "x = plen \<pi>'' - plen \<pi>"  "\<pi> \<le> \<pi>''"
    "\<pi>' = psnoc \<pi>'' tdb" "pdrop (plen \<pi>) (psnoc \<pi>'' tdb) = psnoc (pdrop (plen \<pi>) \<pi>'') tdb"
    "last_ts (pdrop (plen \<pi>) \<pi>'') \<le> snd tdb" "last_ts \<pi>'' \<le> snd tdb"
    "\<pi>'' \<le> psnoc \<pi>'' tdb"
  proof (atomize_elim, transfer, elim exE, goal_cases prefix)
    case (prefix _ _ \<pi>' _ \<pi>_tdb)
    then show ?case
    proof (cases \<pi>_tdb rule: rev_cases)
      case (snoc \<pi> tdb)
      with prefix show ?thesis
        by (intro bexI[of _ "\<pi>' @ \<pi>"] exI[of _ tdb])
          (force simp: sorted_append append_eq_Cons_conv split: list.splits if_splits)+
    qed simp
  qed
  with Suc(1)[OF this(1) Suc.prems(1,2) this(2) refl] Suc.prems show ?case
    unfolding msteps_msteps_stateless[symmetric]
    by (auto simp: msteps_psnoc split_beta mstep_mverdicts
      dest: verimon.verdicts_mono[THEN set_mp, rotated] intro!: wf_mstate_mstep)
qed

lemma wf_mstate_msteps_stateless:
  assumes "wf_mstate \<phi> \<pi> R st" "mem_restr R v" "\<pi> \<le> \<pi>'"
  shows "(i, v) \<in> msteps_stateless (pdrop (plen \<pi>) \<pi>') st \<longleftrightarrow> (i, v) \<in> mverdicts \<phi> \<pi>' - mverdicts \<phi> \<pi>"
  using wf_mstate_msteps[OF assms refl] unfolding msteps_msteps_stateless by simp

lemma wf_mstate_msteps_stateless_UNIV: "wf_mstate \<phi> \<pi> UNIV st \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow>
  msteps_stateless (pdrop (plen \<pi>) \<pi>') st = mverdicts \<phi> \<pi>' - mverdicts \<phi> \<pi>"
  by (auto dest: wf_mstate_msteps_stateless[OF _ mem_restr_UNIV])

lemma mverdicts_Nil: "mverdicts \<phi> pnil = {}"
  unfolding verimon.verdicts_def
  by (auto intro: ex_prefix_of)

lemma wf_mstate_minit_safe: "mmonitorable \<phi> \<Longrightarrow> wf_mstate \<phi> pnil R (minit_safe \<phi>)"
  using wf_mstate_minit minit_safe_minit mmonitorable_def by metis

lemma monitor_mverdicts: "mmonitorable \<phi> \<Longrightarrow> monitor \<phi> \<pi> = mverdicts \<phi> \<pi>"
  unfolding monitor_def
  by (subst wf_mstate_msteps_stateless_UNIV[OF wf_mstate_minit_safe, simplified])
    (auto simp: mmonitorable_def mverdicts_Nil)

subsection \<open>Collected Correctness Results\<close>

text \<open>We summarize the main results proved above.
\begin{enumerate}
\item The term @{term mverdicts} describes semantically the monitor's expected behaviour:
\begin{itemize}
\item @{thm[source] verimon.mono_monitor}: @{thm verimon.mono_monitor[no_vars]}
\item @{thm[source] verimon.sound_monitor}: @{thm verimon.sound_monitor[no_vars]}
\item @{thm[source] verimon.complete_monitor}: @{thm verimon.complete_monitor[no_vars]}
\item @{thm[source] verimon.monitor_slice}: @{thm verimon.monitor_slice[no_vars]}
\end{itemize}
\item The executable monitor's online interface @{term minit_safe} and @{term mstep}
  preserves the invariant @{term wf_mstate} and produces the the verdicts according
  to @{term mverdicts}:
\begin{itemize}
\item @{thm[source] wf_mstate_minit_safe}: @{thm wf_mstate_minit_safe[no_vars]}
\item @{thm[source] wf_mstate_mstep}: @{thm wf_mstate_mstep[no_vars]}
\item @{thm[source] mstep_mverdicts}: @{thm mstep_mverdicts[no_vars]}
\end{itemize}
\item The executable monitor's offline interface @{term monitor} implements @{term mverdicts}:
\begin{itemize}
\item @{thm[source] monitor_mverdicts}: @{thm monitor_mverdicts[no_vars]}
\end{itemize}
\end{enumerate}
\<close>

(*<*)
end
(*>*)
