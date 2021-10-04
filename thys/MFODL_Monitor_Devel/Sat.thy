theory Sat
  imports Monitor
begin

lemma smap2_const[simp]: "smap2 (\<lambda>_. f) s t = smap f t"
  by (coinduction arbitrary: s t) auto

lift_definition map_\<Gamma>i :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a trace \<Rightarrow> 'b trace" is
  "\<lambda>f s. smap2 (\<lambda>i (x, tau). (f i x, tau)) nats s"
  by (auto simp: stream.map_comp prod.case_eq_if cong: stream.map_cong)

lemma \<tau>_map_\<Gamma>i[simp]: "\<tau> (map_\<Gamma>i f \<sigma>) = \<tau> \<sigma>"
  by transfer (auto split: prod.splits)

lemma \<Gamma>_map_\<Gamma>i: "\<Gamma> (map_\<Gamma>i f \<sigma>) i = f i (\<Gamma> \<sigma> i)"
  by transfer (auto split: prod.splits)

lemma map_\<Gamma>i_id[simp]: "map_\<Gamma>i (\<lambda>i x. x) \<sigma> = \<sigma>"
  by transfer (auto simp: stream.map_id)

lemma map_\<Gamma>i_comp[simp]: "map_\<Gamma>i f (map_\<Gamma>i g \<sigma>) = map_\<Gamma>i (\<lambda>i. f i o g i) \<sigma>"
  by transfer (auto simp: stream_eq_iff split: prod.splits)

lemma map_\<Gamma>_map_\<Gamma>i[simp]: "map_\<Gamma> f (map_\<Gamma>i g \<sigma>) = map_\<Gamma>i (\<lambda>i. f o g i) \<sigma>"
  by transfer (auto simp: stream_eq_iff split: prod.splits)

lemma map_\<Gamma>i_map_\<Gamma>[simp]: "map_\<Gamma>i f (map_\<Gamma> g \<sigma>) = map_\<Gamma>i (\<lambda>i. f i o g) \<sigma>"
  by transfer (auto simp: stream_eq_iff split: prod.splits)

lemma map_\<Gamma>i_map_\<Gamma>i_cong: "(\<And>i. f i (\<Gamma> \<sigma> i) = g i (\<Gamma> \<sigma> i))\<Longrightarrow> map_\<Gamma>i f \<sigma> = map_\<Gamma>i g \<sigma>"
  by transfer (auto simp: stream_eq_iff split_beta)

lemma map_\<Gamma>i_map_\<Gamma>_cong: "(\<And>i. f i (\<Gamma> \<sigma> i) = g (\<Gamma> \<sigma> i))\<Longrightarrow> map_\<Gamma>i f \<sigma> = map_\<Gamma> g \<sigma>"
  by transfer (auto simp: stream_eq_iff split_beta)

abbreviation update_\<Gamma> where "update_\<Gamma> \<sigma> pn f \<equiv> map_\<Gamma>i (\<lambda>j db. db(pn := f j)) \<sigma>"

nonterminal upd\<Gamma>binds and upd\<Gamma>bind

syntax
  "_upd\<Gamma>bind" :: "'a \<Rightarrow> 'a \<Rightarrow> upd\<Gamma>bind"             ("(2_ \<Rrightarrow>/ _)")
  ""         :: "upd\<Gamma>bind \<Rightarrow> upd\<Gamma>binds"             ("_")
  "_upd\<Gamma>binds":: "upd\<Gamma>bind \<Rightarrow> upd\<Gamma>binds \<Rightarrow> upd\<Gamma>binds" ("_,/ _")
  "_Upd\<Gamma>ate"  :: "'a \<Rightarrow> upd\<Gamma>binds \<Rightarrow> 'a"            ("_/'((_)')" [1000, 0] 900)

translations
  "_Upd\<Gamma>ate f (_updbinds b bs)" \<rightleftharpoons> "_Upd\<Gamma>ate (_Upd\<Gamma>ate f b) bs"
  "f(x\<Rrightarrow>y)" \<rightleftharpoons> "CONST update_\<Gamma> f x y"

context begin

subsection \<open>Syntax and semantics\<close>

qualified type_synonym database = "Formula.name \<times> nat \<Rightarrow> Formula.env set"
qualified type_synonym prefix = "database prefix"
qualified type_synonym trace = "database trace"

fun letpast_sat where
  "letpast_sat sat (i::nat) = sat (\<lambda>j. if j < i then letpast_sat sat j else {}) i"
declare letpast_sat.simps[simp del]

lemma subst_letpast_sat:
  "(\<And>X v j. j \<le> i \<Longrightarrow> f X j = g X j) \<Longrightarrow> letpast_sat f i = letpast_sat g i"
  by (induct f i rule: letpast_sat.induct) (subst (1 2) letpast_sat.simps, auto cong: if_cong)

lemma letpast_sat_alt:
  "letpast_sat sat i = {v. Formula.letpast_sat (\<lambda>X v i. v \<in> sat (\<lambda>j. {w. X w j}) i) v i}"
  apply (induct sat i rule: letpast_sat.induct)
  subgoal for sat i
  apply (subst letpast_sat.simps)
    apply (subst Formula.letpast_sat.simps)
    apply (rule set_eqI)
    apply (unfold mem_Collect_eq)
    apply (rule arg_cong[of _ _ "\<lambda>X. x \<in> sat X i" for x])
    apply (auto simp: fun_eq_iff)
    done
  done

fun sat :: "trace \<Rightarrow> Formula.env \<Rightarrow> nat \<Rightarrow> Formula.formula \<Rightarrow> bool" where
  "sat \<sigma> v i (Formula.Pred r ts) = (map (Formula.eval_trm v) ts \<in> \<Gamma> \<sigma> i (r, length ts))"
| "sat \<sigma> v i (Formula.Let p \<phi> \<psi>) =
    (let pn = (p, Formula.nfv \<phi>) in
    sat (\<sigma>(pn \<Rrightarrow> \<lambda>j. {w. sat \<sigma> w j \<phi>})) v i \<psi>)"
| "sat \<sigma> v i (Formula.LetPast p \<phi> \<psi>) =
    (let pn = (p, Formula.nfv \<phi>) in
    sat (\<sigma>(pn \<Rrightarrow> letpast_sat (\<lambda>X k. {u. sat (\<sigma>(pn \<Rrightarrow> X)) u k \<phi>}))) v i \<psi>)"
| "sat \<sigma> v i (Formula.Eq t1 t2) = (Formula.eval_trm v t1 = Formula.eval_trm v t2)"
| "sat \<sigma> v i (Formula.Less t1 t2) = (Formula.eval_trm v t1 < Formula.eval_trm v t2)"
| "sat \<sigma> v i (Formula.LessEq t1 t2) = (Formula.eval_trm v t1 \<le> Formula.eval_trm v t2)"
| "sat \<sigma> v i (Formula.Neg \<phi>) = (\<not> sat \<sigma> v i \<phi>)"
| "sat \<sigma> v i (Formula.Or \<phi> \<psi>) = (sat \<sigma> v i \<phi> \<or> sat \<sigma> v i \<psi>)"
| "sat \<sigma> v i (Formula.And \<phi> \<psi>) = (sat \<sigma> v i \<phi> \<and> sat \<sigma> v i \<psi>)"
| "sat \<sigma> v i (Formula.Ands l) = (\<forall>\<phi> \<in> set l. sat \<sigma> v i \<phi>)"
| "sat \<sigma> v i (Formula.Exists \<phi>) = (\<exists>z. sat \<sigma> (z # v) i \<phi>)"
| "sat \<sigma> v i (Formula.Agg y \<omega> b f \<phi>) =
    (let M = {(x, ecard Zs) | x Zs. Zs = {zs. length zs = b \<and> sat \<sigma> (zs @ v) i \<phi> \<and> Formula.eval_trm (zs @ v) f = x} \<and> Zs \<noteq> {}}
    in (M = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<b}) \<and> v ! y = eval_agg_op \<omega> M)"
| "sat \<sigma> v i (Formula.Prev I \<phi>) = (case i of 0 \<Rightarrow> False | Suc j \<Rightarrow> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> v j \<phi>)"
| "sat \<sigma> v i (Formula.Next I \<phi>) = (mem I ((\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i)) \<and> sat \<sigma> v (Suc i) \<phi>)"
| "sat \<sigma> v i (Formula.Since \<phi> I \<psi>) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> v j \<psi> \<and> (\<forall>k \<in> {j <.. i}. sat \<sigma> v k \<phi>))"
| "sat \<sigma> v i (Formula.Until \<phi> I \<psi>) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat \<sigma> v j \<psi> \<and> (\<forall>k \<in> {i ..< j}. sat \<sigma> v k \<phi>))"
| "sat \<sigma> v i (Formula.MatchP I r) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Regex.match (sat \<sigma> v) r j i)"
| "sat \<sigma> v i (Formula.MatchF I r) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Regex.match (sat \<sigma> v) r i j)"

end

definition "convert \<sigma> V = map_\<Gamma>i (\<lambda>i db pn. case V pn of None \<Rightarrow> {w. (fst pn, w) \<in> db \<and> length w = snd pn} | Some X \<Rightarrow> {w. X w i}) \<sigma>"

abbreviation to_db where "to_db db \<equiv> {(a, v). v \<in> db (a, length v)}"
definition "unconvert \<sigma> = map_\<Gamma> to_db \<sigma>"
definition "punconvert \<pi> = pmap_\<Gamma> to_db \<pi>"

lemma prefix_of_unconvert: "prefix_of \<pi> \<sigma> \<Longrightarrow> prefix_of (punconvert \<pi>) (unconvert \<sigma>)"
  unfolding unconvert_def punconvert_def by transfer auto

lemma plen_punconvert[simp]: "plen (punconvert \<pi>) = plen \<pi>"
  unfolding punconvert_def by transfer auto

abbreviation fix_length where "fix_length X \<equiv> (\<lambda>(a, n). X (a, n) \<inter> {w. length w = n})"

lemma unconvert_convert: "unconvert (convert \<sigma> Map.empty) = \<sigma>"
  unfolding convert_def unconvert_def by (auto simp: o_def)

lemma convert_unconvert: "convert (unconvert \<sigma>) Map.empty = map_\<Gamma> fix_length \<sigma>"
  unfolding convert_def unconvert_def by (auto intro!: map_\<Gamma>i_map_\<Gamma>_cong)

lemma \<tau>_convert[simp]: "\<tau> (convert \<sigma> V) = \<tau> \<sigma>"
  unfolding convert_def by simp

lemma \<tau>_unconvert[simp]: "\<tau> (unconvert \<sigma>) = \<tau> \<sigma>"
  unfolding unconvert_def by auto

lemma map_\<Gamma>_update_\<Gamma>: "(map_\<Gamma> f \<sigma>)(pn \<Rrightarrow> X) = map_\<Gamma>i (\<lambda>i x. (f x)(pn := X i)) \<sigma>"
  by (auto simp: o_def)

lemma convert_update_\<Gamma>: "(convert \<sigma> V)(pn \<Rrightarrow> X) = convert \<sigma> (V(pn \<mapsto> \<lambda>v i. v \<in> X i))"
  unfolding convert_def
  by (auto simp: fun_eq_iff intro!: arg_cong[of _ _ "\<lambda>f. map_\<Gamma>i f \<sigma>"])

lemma sat_convert: "Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> sat (convert \<sigma> V) v i \<phi>"
proof (induct \<phi> arbitrary: V v i)
  case (Pred e ts)
  then show ?case
    by (auto simp: convert_def \<Gamma>_map_\<Gamma>i split: option.splits)
next
  case (Let p \<phi> \<psi>)
  then show ?case
    by (simp del: fun_upd_apply add: convert_update_\<Gamma>)
next
  case (LetPast p \<phi> \<psi>)
  then show ?case
    by (simp del: fun_upd_apply add: Let_def convert_update_\<Gamma> letpast_sat_alt)
qed (auto split: nat.splits cong: match_cong)

lemma sat_fix_length: "sat (map_\<Gamma> fix_length \<sigma>) v i \<phi> = sat \<sigma> v i \<phi>"
proof (induct \<phi> arbitrary: \<sigma> v i)
  case (Pred e ts)
  then show ?case
    by (auto split: option.splits)
next
  case (Let p \<phi> \<psi>)
  show ?case
    unfolding sat.simps Let_def Let(1)
    by (subst (1 2) Let(2)[symmetric])
      (auto simp add: fun_eq_iff intro!: map_\<Gamma>i_map_\<Gamma>i_cong arg_cong[of _ _ "\<lambda>X. sat X v i \<psi>"])
next
  case (LetPast p \<phi> \<psi>)
  show ?case
    unfolding sat.simps Let_def
    apply (subst (1 2) LetPast(2)[symmetric])
    apply (rule arg_cong[of _ _ "\<lambda>X. sat X v i \<psi>"])
    apply (simp add: o_def)
    apply (rule map_\<Gamma>i_map_\<Gamma>i_cong)
    apply (rule ext)
    apply (simp only: split_beta)
    apply (rule set_eqI)
    apply (simp only: Int_iff conj_commute)
    apply (rule conj_cong[OF refl])
    apply (unfold if_split_mem2)
    apply (rule conj_cong)
     apply (rule imp_cong[OF refl])
     apply (rule arg_cong2[where f="(\<in>)", OF refl])
     apply (rule subst_letpast_sat)
     apply (rule Collect_cong)
     apply (subst (1 2) LetPast(1)[symmetric])
     apply (rule arg_cong[where f="\<lambda>X. sat X _ _ \<phi>"])
     apply (auto simp: fun_eq_iff intro!: map_\<Gamma>i_map_\<Gamma>i_cong) []
    apply auto
    done
qed (auto split: nat.splits cong: match_cong)

lemma sat_unconvert: "sat \<sigma> v i \<phi> \<longleftrightarrow> Formula.sat (unconvert \<sigma>) Map.empty v i \<phi>"
  unfolding sat_convert convert_unconvert sat_fix_length ..

subsection \<open>Collected correctness results\<close>

definition pprogress :: "Formula.formula \<Rightarrow> Sat.prefix \<Rightarrow> nat" where
  "pprogress \<phi> \<pi> = (THE n. \<forall>\<sigma>. prefix_of \<pi> \<sigma> \<longrightarrow> progress (unconvert \<sigma>) Map.empty \<phi> (plen \<pi>) = n)"

lemma pprogress_eq: "prefix_of \<pi> \<sigma> \<Longrightarrow> pprogress \<phi> \<pi> = progress (unconvert \<sigma>) Map.empty \<phi> (plen \<pi>)"
  unfolding pprogress_def plen_punconvert[symmetric]
  using progress_prefix_conv prefix_of_unconvert by blast

sublocale future_bounded_mfodl \<subseteq> Sat: timed_progress "Formula.nfv \<phi>" "Formula.fv \<phi>"
  "\<lambda>\<sigma> v i. sat \<sigma> v i \<phi>" "pprogress \<phi>"
proof (unfold_locales, goal_cases)
  case (1 x)
  then show ?case by (simp add: fvi_less_nfv)
next
  case (2 v v' \<sigma> i)
  then show ?case
    unfolding sat_unconvert by (simp cong: sat_fv_cong[rule_format])
next
  case (3 \<pi> \<pi>')
  moreover obtain \<sigma> where "prefix_of \<pi>' \<sigma>"
    using ex_prefix_of ..
  moreover have "prefix_of \<pi> \<sigma>"
    using prefix_of_antimono[OF \<open>\<pi> \<le> \<pi>'\<close> \<open>prefix_of \<pi>' \<sigma>\<close>] .
  ultimately show ?case
    by (simp add: pprogress_eq plen_mono Monitor.progress_mono)
next
  case (4 \<sigma> x)
  obtain j where "x \<le> progress (unconvert \<sigma>) Map.empty \<phi> j"
    using future_bounded progress_ge by blast
  then have "x \<le> pprogress \<phi> (take_prefix j \<sigma>)"
    by (simp add: pprogress_eq[of _ \<sigma>])
  then show ?case by force
next
  case (5 \<pi> \<sigma> \<sigma>' i v)
  then have "i < progress (unconvert \<sigma>) Map.empty \<phi> (plen \<pi>)"
    by (simp add: pprogress_eq)
  with 5 show ?case
    unfolding sat_unconvert
    by (intro sat_prefix_conv) (auto elim!: prefix_of_unconvert)
next
  case (6 \<pi> \<pi>')
  then have "plen \<pi> = plen \<pi>'"
    by transfer (simp add: list_eq_iff_nth_eq)
  moreover obtain \<sigma> \<sigma>' where "prefix_of \<pi> \<sigma>" "prefix_of \<pi>' \<sigma>'"
    using ex_prefix_of by blast+
  moreover have "\<forall>i < plen \<pi>. \<tau> \<sigma> i = \<tau> \<sigma>' i"
    using 6 calculation
    by transfer (simp add: list_eq_iff_nth_eq)
  ultimately show ?case
    by (simp add: pprogress_eq Monitor.progress_time_conv[where j="plen (punconvert _)", simplified])
qed

context verimon
begin

lemma pprogress_punconvert: "Sat.pprogress \<phi> \<pi> = Monitor.pprogress \<phi> (punconvert \<pi>)"
  by (metis Monitor.pprogress_eq Sat.pprogress_eq ex_prefix_of plen_punconvert prefix_of_unconvert)

lemma M_alt: "Sat.M \<pi> = M (punconvert \<pi>)"
  unfolding Sat.M_def M_def
  unfolding pprogress_punconvert sat_unconvert
  apply (auto simp: prefix_of_unconvert)
  using ex_prefix_of prefix_of_unconvert progress_sat_cong apply blast
  done

lemma last_ts_punconvert[simp]: "last_ts (punconvert \<pi>) = last_ts \<pi>"
  unfolding punconvert_def by transfer (auto simp: last_map split: list.splits prod.splits)

lemma punconvert_pnil[simp]: "punconvert pnil = pnil"
  unfolding punconvert_def
  by transfer auto

lemma punconvert_psnoc[simp]: "punconvert (psnoc \<pi> tdb) = psnoc (punconvert \<pi>) (apfst to_db tdb)"
  unfolding punconvert_def
  by transfer (auto simp: last_map split: list.splits prod.splits)

abbreviation invar where "invar \<equiv> \<lambda>\<phi> \<pi>. wf_mstate \<phi> (punconvert \<pi>)"
abbreviation monitor_step where "monitor_step \<equiv> \<lambda>db t. mstep (apfst mk_db (to_db db, t))"

text \<open>Main Results\<close>

lemmas monitor_specification =
  Sat.mono_monitor
  Sat.sound_monitor
  Sat.complete_monitor

theorem invar_minit_safe:
  "mmonitorable \<phi> \<Longrightarrow> invar \<phi> pnil R (minit_safe \<phi>)"
  by (auto elim: wf_mstate_minit_safe)

theorem invar_mstep:
  assumes "invar \<phi>' \<pi> R st" "last_ts \<pi> \<le> t"
  shows "invar \<phi>' (psnoc \<pi> (db, t)) R (snd (monitor_step db t st))"
  using wf_mstate_mstep[OF assms(1), of "(to_db db, t)", simplified, OF assms(2)]
  by auto

theorem mstep_mverdicts:
  assumes "invar \<phi> \<pi> R st" "last_ts \<pi> \<le> t" "mem_restr R v"
  shows "((i, v) \<in> flatten_verdicts (fst (monitor_step db t st))) =
         ((i, v) \<in> Sat.M (psnoc \<pi> (db, t)) - Sat.M \<pi>)"
  using mstep_mverdicts[OF assms(1), of "(to_db db, t)" v i, simplified, OF assms(2,3)]
  by (auto simp: M_alt)

end