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

fun preds :: "Formula.formula \<Rightarrow> (Formula.name \<times> nat) set" where
   "preds (Formula.Eq t1 t2) = {}"
|  "preds (Formula.Less t1 t2) = {}"
|  "preds (Formula.LessEq t1 t2) = {}"
|  "preds (Formula.Pred e ts) = {(e, length ts)}"
|  "preds (Formula.Let e \<phi> \<psi>) = (preds \<phi> \<union> preds \<psi>)"
     \<comment> \<open>(let en = (e, Formula.nfv \<phi>); p\<psi> = preds \<psi> in (p\<psi> - {en} \<union> (if en \<in> p\<psi> then preds \<phi> else {})))\<close>
|  "preds (Formula.LetPast e \<phi> \<psi>) = (preds \<phi> \<union> preds \<psi>)"
     \<comment> \<open>(let en = (e, Formula.nfv \<phi>); p\<psi> = preds \<psi> in (p\<psi> \<union> (if en \<in> p\<psi> then preds \<phi> else {})) - {en})\<close>
|  "preds (Formula.Neg \<phi>) = preds \<phi>"
|  "preds (Formula.Or \<phi> \<psi>) = (preds \<phi> \<union> preds \<psi>)"
|  "preds (Formula.And \<phi> \<psi>) = (preds \<phi> \<union> preds \<psi>)"
|  "preds (Formula.Ands l) = (\<Union>\<phi>\<in>set l. preds \<phi>)"
|  "preds (Formula.Exists \<phi>) = preds \<phi>"
|  "preds (Formula.Agg y \<omega> b' f \<phi>) = preds \<phi>"
|  "preds (Formula.Prev I \<phi>) = preds \<phi>"
|  "preds (Formula.Next I \<phi>) = preds \<phi>"
|  "preds (Formula.Since \<phi> I \<psi>) = (preds \<phi> \<union> preds \<psi>)"
|  "preds (Formula.Until \<phi> I \<psi>) = (preds \<phi> \<union> preds \<psi>)"
|  "preds (Formula.MatchP I r) = (\<Union>\<phi>\<in>Regex.atms r. preds \<phi>)"
|  "preds (Formula.MatchF I r) =  (\<Union>\<phi>\<in>Regex.atms r. preds \<phi>)"

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

abbreviation to_db where "to_db A db \<equiv> \<Union>(p,n) \<in> A. Pair p ` {v \<in> db (p, n). length v = n}"
definition "unconvert A \<sigma> = map_\<Gamma> (to_db A) \<sigma>"
definition "punconvert A \<pi> = pmap_\<Gamma> (to_db A) \<pi>"

lemma prefix_of_unconvert: "prefix_of \<pi> \<sigma> \<Longrightarrow> prefix_of (punconvert A \<pi>) (unconvert A \<sigma>)"
  unfolding unconvert_def punconvert_def by transfer auto

lemma plen_punconvert[simp]: "plen (punconvert A \<pi>) = plen \<pi>"
  unfolding punconvert_def by transfer auto

abbreviation fix_length where "fix_length A X \<equiv> (\<lambda>(a, n). if (a, n) \<in> A then X (a, n) \<inter> {w. length w = n} else {})"

lemma unconvert_convert: "unconvert UNIV (convert \<sigma> Map.empty) = \<sigma>"
  unfolding convert_def unconvert_def by (force simp: o_def intro!: trans[OF map_\<Gamma>i_map_\<Gamma>_cong[of _ _ id]])

lemma convert_unconvert: "convert (unconvert A \<sigma>) Map.empty = map_\<Gamma> (fix_length A) \<sigma>"
  unfolding convert_def unconvert_def by (force intro!: map_\<Gamma>i_map_\<Gamma>_cong simp: fun_eq_iff)

lemma \<tau>_convert[simp]: "\<tau> (convert \<sigma> V) = \<tau> \<sigma>"
  unfolding convert_def by simp

lemma \<tau>_unconvert[simp]: "\<tau> (unconvert A \<sigma>) = \<tau> \<sigma>"
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

lemma sat_fix_length: "preds \<phi> \<subseteq> A \<Longrightarrow> sat (map_\<Gamma> (fix_length A) \<sigma>) v i \<phi> = sat \<sigma> v i \<phi>"
proof (induct \<phi> arbitrary: \<sigma> v i)
  case (Pred e ts)
  then show ?case
    by (auto split: option.splits)
next
  case (Let p \<phi> \<psi>)

  show ?case
    unfolding sat.simps Let_def using Let(1,3)
    by (subst (1 2) Let(2)[symmetric])
      (auto simp add: Let_def intro!: map_\<Gamma>i_map_\<Gamma>i_cong arg_cong[of _ _ "\<lambda>X. sat X v i \<psi>"] split: if_splits)
next
  case (LetPast p \<phi> \<psi>)
  show ?case
    unfolding sat.simps Let_def using LetPast(3)
    apply (subst (1 2) LetPast(2)[symmetric])
     apply simp
    apply (rule arg_cong[of _ _ "\<lambda>X. sat X v i \<psi>"])
    apply (simp add: o_def)
    apply (rule map_\<Gamma>i_map_\<Gamma>i_cong)
    apply (rule ext)
    apply (simp only: split_beta)
    apply (rule if_cong[OF refl _ refl])
    apply (rule set_eqI)
    apply (simp only: Int_iff conj_commute fun_upd_def)
    apply (rule conj_cong[OF refl])
    apply (unfold if_split_mem2)
    apply (rule conj_cong)
     apply (rule imp_cong[OF refl])
     apply (rule arg_cong2[where f="(\<in>)", OF refl])
     apply (rule subst_letpast_sat)
     apply (rule Collect_cong)
     apply (subst (1 2) LetPast(1)[symmetric])
      apply simp
     apply (rule arg_cong[where f="\<lambda>X. sat X _ _ \<phi>"])
     apply (auto simp: fun_eq_iff intro!: map_\<Gamma>i_map_\<Gamma>i_cong) []
    apply auto
    done
qed (auto simp: subset_eq split: nat.splits cong: match_cong)

lemma sat_unconvert: "sat \<sigma> v i \<phi> \<longleftrightarrow> Formula.sat (unconvert (preds \<phi>) \<sigma>) Map.empty v i \<phi>"
  unfolding sat_convert convert_unconvert sat_fix_length[OF subset_refl] ..

subsection \<open>Collected correctness results\<close>

definition pprogress :: "Formula.formula \<Rightarrow> Sat.prefix \<Rightarrow> nat" where
  "pprogress \<phi> \<pi> = (THE n. \<forall>\<sigma>. prefix_of \<pi> \<sigma> \<longrightarrow> progress (unconvert (preds \<phi>) \<sigma>) Map.empty \<phi> (plen \<pi>) = n)"

lemma pprogress_eq: "prefix_of \<pi> \<sigma> \<Longrightarrow> pprogress \<phi> \<pi> = progress (unconvert (preds \<phi>) \<sigma>) Map.empty \<phi> (plen \<pi>)"
  unfolding pprogress_def plen_punconvert[where A="preds \<phi>", symmetric]
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
  obtain j where "x \<le> progress (unconvert (preds \<phi>) \<sigma>) Map.empty \<phi> j"
    using future_bounded progress_ge by blast
  then have "x \<le> pprogress \<phi> (take_prefix j \<sigma>)"
    by (simp add: pprogress_eq[of _ \<sigma>])
  then show ?case by force
next
  case (5 \<pi> \<sigma> \<sigma>' i v)
  then have "i < progress (unconvert (preds \<phi>) \<sigma>) Map.empty \<phi> (plen \<pi>)"
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
    by (simp add: pprogress_eq Monitor.progress_time_conv[where j="plen (punconvert (preds \<phi>) _)", simplified])
qed

context verimon
begin

lemma pprogress_punconvert: "Sat.pprogress \<phi> \<pi> = Monitor.pprogress \<phi> (punconvert (preds \<phi>) \<pi>)"
  by (metis Monitor.pprogress_eq Sat.pprogress_eq ex_prefix_of plen_punconvert prefix_of_unconvert)

lemma M_alt: "Sat.M \<pi> = M (punconvert (preds \<phi>) \<pi>)"
  unfolding Sat.M_def M_def
  unfolding pprogress_punconvert sat_unconvert
  apply (auto simp: prefix_of_unconvert)
  using ex_prefix_of prefix_of_unconvert progress_sat_cong apply blast
  done

lemma last_ts_punconvert[simp]: "last_ts (punconvert A \<pi>) = last_ts \<pi>"
  unfolding punconvert_def by transfer (auto simp: last_map split: list.splits prod.splits)

lemma punconvert_pnil[simp]: "punconvert A pnil = pnil"
  unfolding punconvert_def
  by transfer auto

lemma punconvert_psnoc[simp]: "punconvert A (psnoc \<pi> tdb) = psnoc (punconvert A \<pi>) (apfst (to_db A) tdb)"
  unfolding punconvert_def
  by transfer (auto simp: last_map split: list.splits prod.splits)

definition monitor_invar where "monitor_invar \<equiv> \<lambda>\<phi> \<pi> R (st, P). wf_mstate \<phi> (punconvert P \<pi>) R st \<and> P = preds \<phi>"
definition monitor_init where "monitor_init \<equiv> \<lambda>\<phi>. (minit_safe \<phi>, preds \<phi>)"
definition monitor_step where "monitor_step \<equiv> \<lambda>db t (st, P). apsnd (\<lambda>st. (st, P)) (mstep (apfst mk_db (to_db P db, t)) st)"

text \<open>Main Results\<close>

lemmas monitor_specification =
  Sat.mono_monitor
  Sat.sound_monitor
  Sat.complete_monitor

theorem invar_minit_safe:
  "mmonitorable \<phi> \<Longrightarrow> monitor_invar \<phi> pnil R (monitor_init \<phi>)"
  by (auto elim: wf_mstate_minit_safe simp: monitor_invar_def monitor_init_def)

theorem invar_mstep:
  assumes "monitor_invar \<phi> \<pi> R st" "last_ts \<pi> \<le> t"
  shows "monitor_invar \<phi> (psnoc \<pi> (db, t)) R (snd (monitor_step db t st))"
  using assms wf_mstate_mstep[of \<phi> "punconvert (snd st) \<pi>" R "fst st" "(to_db (snd st) db, t)"]
  by (auto simp: monitor_invar_def monitor_step_def)

theorem mstep_mverdicts:
  assumes "monitor_invar \<phi> \<pi> R st" "last_ts \<pi> \<le> t" "mem_restr R v"
  shows "((i, v) \<in> flatten_verdicts (fst (monitor_step db t st))) =
         ((i, v) \<in> Sat.M (psnoc \<pi> (db, t)) - Sat.M \<pi>)"
  using assms mstep_mverdicts[of "punconvert (snd st) \<pi>" R "fst st" "(to_db (snd st) db, t)"]
  by (auto simp: M_alt monitor_invar_def monitor_step_def)

end

end