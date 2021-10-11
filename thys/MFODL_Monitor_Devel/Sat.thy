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

fun sat :: "trace \<Rightarrow> Formula.env \<Rightarrow> nat \<Rightarrow> Formula.formula \<Rightarrow> bool" where
  "sat \<sigma> v i (Formula.Pred r ts) = (map (Formula.eval_trm v) ts \<in> \<Gamma> \<sigma> i (r, length ts))"
| "sat \<sigma> v i (Formula.Let p \<phi> \<psi>) =
    (let pn = (p, Formula.nfv \<phi>) in
    sat (\<sigma>(pn \<Rrightarrow> \<lambda>j. {w. sat \<sigma> w j \<phi> \<and> length w = snd pn})) v i \<psi>)"
| "sat \<sigma> v i (Formula.LetPast p \<phi> \<psi>) =
    (let pn = (p, Formula.nfv \<phi>) in
    sat (\<sigma>(pn \<Rrightarrow> letpast_sat (\<lambda>X k. {u. sat (\<sigma>(pn \<Rrightarrow> X)) u k \<phi> \<and> length u = snd pn}))) v i \<psi>)"
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

definition "convert \<sigma> V = map_\<Gamma>i (\<lambda>i db pn. case V pn of None \<Rightarrow> {w. (fst pn, w) \<in> db \<and> length w = snd pn}
  | Some X \<Rightarrow> {w. X w i \<and> length w = snd pn}) \<sigma>"

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

definition "unconvertV X \<sigma> p = (if p \<in> X then Some (\<lambda>v i. v \<in> \<Gamma> \<sigma> i p \<and> length v = snd p) else None)"

lemma unconvertV_empty[simp]: "unconvertV {} \<sigma> = Map.empty"
  unfolding unconvertV_def by auto

lemma convert_unconvert: "convert (unconvert A \<sigma>) (unconvertV X \<sigma>) = map_\<Gamma> (fix_length (A \<union> X)) \<sigma>"
  unfolding convert_def unconvert_def unconvertV_def
  by (force intro!: map_\<Gamma>i_map_\<Gamma>_cong simp: fun_eq_iff)

lemma \<tau>_convert[simp]: "\<tau> (convert \<sigma> V) = \<tau> \<sigma>"
  unfolding convert_def by simp

lemma \<tau>_unconvert[simp]: "\<tau> (unconvert A \<sigma>) = \<tau> \<sigma>"
  unfolding unconvert_def by auto

lemma map_\<Gamma>_update_\<Gamma>: "(map_\<Gamma> f \<sigma>)(pn \<Rrightarrow> X) = map_\<Gamma>i (\<lambda>i x. (f x)(pn := X i)) \<sigma>"
  by (auto simp: o_def)

lemma convert_fun_upd: "convert \<sigma> (V(pn \<mapsto> X)) = (convert \<sigma> V)(pn \<Rrightarrow> \<lambda>j. {w. X w j \<and> length w = snd pn})"
  unfolding convert_def
  by (auto simp: fun_eq_iff intro!: arg_cong[of _ _ "\<lambda>f. map_\<Gamma>i f \<sigma>"])

lemma letpast_sat_alt:
  "letpast_sat (\<lambda>X j. {w. sat ((convert \<sigma> V)(pn \<Rrightarrow> X)) w j \<phi> \<and> length w = snd pn}) i
  = {v. Formula.letpast_sat (\<lambda>X w j. sat (convert \<sigma> (V(pn \<mapsto> X))) w j \<phi>) v i \<and> length v = snd pn}"
  apply (induction i rule: less_induct)
  apply (subst Sat.letpast_sat.simps)
  apply (subst Formula.letpast_sat.simps)
  apply (intro Collect_cong conj_cong[OF _ refl])
  apply (subst ext[where f="\<lambda>j db. db(pn := if j < _ then _ j else {})"])
   apply (rule ext)
   apply (rule arg_cong[where f="fun_upd _ pn"])
   apply (rule if_cong[OF refl _ refl])
   apply assumption
  apply (subst (2) convert_fun_upd)
  apply (rule arg_cong[where f="\<lambda>g. sat (_(pn \<Rrightarrow> g)) _ _ _"])
  by (simp add: fun_eq_iff)

lemma sat_convert: "Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> sat (convert \<sigma> V) v i \<phi>"
proof (induct \<phi> arbitrary: V v i)
  case (Pred e ts)
  then show ?case
    by (auto simp: convert_def \<Gamma>_map_\<Gamma>i split: option.splits)
next
  case (Let p \<phi> \<psi>)
  then show ?case
    by (simp del: fun_upd_apply add: convert_fun_upd)
next
  case (LetPast p \<phi> \<psi>)
  then show ?case
    by (simp del: fun_upd_apply add: Let_def convert_fun_upd letpast_sat_alt)
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
     apply (rule conj_cong[OF refl])
     apply (rule arg_cong[where f="\<lambda>X. sat X _ _ \<phi>"])
     apply (auto simp: fun_eq_iff intro!: map_\<Gamma>i_map_\<Gamma>i_cong) []
    apply auto
    done
qed (auto simp: subset_eq split: nat.splits cong: match_cong)

lemma sat_unconvert:
  "preds \<phi> \<subseteq> X \<union> A \<Longrightarrow> sat \<sigma> v i \<phi> \<longleftrightarrow> Formula.sat (unconvert X \<sigma>) (unconvertV A \<sigma>) v i \<phi>"
  unfolding sat_convert convert_unconvert by (rule sat_fix_length[symmetric]) simp

lemmas sat_unconvert' = sat_unconvert[where A="{}" and X="preds \<phi>" and \<phi>=\<phi> for \<phi>, simplified]

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
    unfolding sat_unconvert' by (auto intro!: sat_fv_cong)
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
    unfolding sat_unconvert' unconvertV_empty
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
  unfolding pprogress_punconvert sat_unconvert'
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

context maux begin

definition wf_envs where "wf_envs \<sigma> j \<delta> P P' db =
  (Mapping.keys db \<supseteq> dom P \<union> (\<Union>k \<in> {j ..< j + \<delta>}. {(p, n). \<exists>x. x \<in> \<Gamma> \<sigma> k (p, n) \<and> n = length x}) \<and>
   rel_mapping (\<le>) P P' \<and>
   pred_mapping (\<lambda>i. i \<le> j) P \<and>
   pred_mapping (\<lambda>i. i \<le> j + \<delta>) P' \<and>
   (\<forall>pn \<in> Mapping.keys db. the (Mapping.lookup db pn) = map (\<lambda>k. map Some ` {ts. ts \<in> \<Gamma> \<sigma> k pn \<and> length ts = snd pn})
     (if pn \<in> dom P then [the (P pn)..<the (P' pn)] else [j ..< j + \<delta>])))"

definition invar_mformula where
  "invar_mformula \<sigma> j P n R \<phi> \<phi>' =
     wf_mformula (unconvert UNIV \<sigma>) j P (unconvertV (dom P) \<sigma>) n R \<phi> \<phi>'"

lemma progress_unconvert: "progress (unconvert A \<sigma>) P \<phi> j = progress \<sigma> P \<phi> j"
  by (simp add: progress_time_conv)

lemma dom_unconvertV[simp]: "dom (unconvertV X \<sigma>) = X"
  by (auto simp: unconvertV_def split: if_splits)

lemma in_\<Gamma>_unconvert[simp]:
  "(p, v) \<in> \<Gamma> (unconvert X \<sigma>) k \<longleftrightarrow> v \<in> \<Gamma> \<sigma> k (p, length v) \<and> (p, length v) \<in> X"
  by (auto simp: unconvert_def)

lemma meval:
  assumes "invar_mformula \<sigma> j P n R \<phi> \<phi>'" "wf_envs \<sigma> j \<delta> P P' db"
  shows "case meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi> of (xs, \<phi>\<^sub>n) \<Rightarrow> invar_mformula \<sigma> (j + \<delta>) P' n R \<phi>\<^sub>n \<phi>' \<and>
    list_all2 (\<lambda>i. qtable n (Formula.fv \<phi>') (mem_restr R) (\<lambda>v. Sat.sat \<sigma> (map the v) i \<phi>'))
    [progress \<sigma> P \<phi>' j..<progress \<sigma> P' \<phi>' (j + \<delta>)] xs"
proof -
  from assms have *: "dom P' = dom P"
    unfolding wf_envs_def by (simp add: rel_mapping_alt)
  from assms(1) have "wf_mformula (unconvert UNIV \<sigma>) j P (unconvertV (dom P) \<sigma>) n R \<phi> \<phi>'"
    unfolding invar_mformula_def by simp
  moreover
  from assms(2) have "Monitor.wf_envs (unconvert UNIV \<sigma>) j \<delta> P P' (unconvertV (dom P) \<sigma>) db"
    unfolding wf_envs_def Monitor.wf_envs_def
    apply clarsimp
    apply safe
    apply blast
    apply force
    apply force
    apply (drule bspec)
     apply (erule set_mp)
    apply blast
    apply (auto simp: list.rel_eq[symmetric] list.rel_map domIff unconvertV_def
        elim!: list.rel_flip[THEN iffD1, OF list.rel_mono_strong])
    done
  ultimately show ?thesis
    unfolding invar_mformula_def *
      sat_unconvert[where A = "dom P" and X = UNIV, simplified]
    by (subst (1 2) progress_unconvert[symmetric, where A = UNIV])
      (rule meval[of "(unconvert UNIV \<sigma>)", unfolded \<tau>_unconvert])
qed

lemma progress_convert_cong:
  "convert \<sigma> V = convert \<sigma>' V' \<Longrightarrow> progress \<sigma> P \<phi> j = progress \<sigma>' P \<phi> j"
  by (auto simp add: progress_time_conv dest!: arg_cong[where f=\<tau>])

lemma sat_convert_cong:
  "convert \<sigma> V = convert \<sigma>' V' \<Longrightarrow> Formula.sat \<sigma> V v i \<phi> = Formula.sat \<sigma>' V' v i \<phi>"
  by (simp add: sat_convert)

lemma wf_mformula_convert_cong_aux:
  "wf_mformula \<sigma> j P V m R \<phi> \<phi>' \<Longrightarrow> convert \<sigma> V = convert \<sigma>' V' \<Longrightarrow> wf_mformula \<sigma>' j P V' m R \<phi> \<phi>'"
proof (induction arbitrary: V' rule: wf_mformula.induct)
  case (Let P V m \<phi> \<phi>' p n R \<psi> \<psi>' b)
  show ?case
    apply (rule wf_mformula.Let)
        apply (rule Let.IH(1); fact)
       apply (rule Let.IH(2)[unfolded progress_convert_cong[OF Let.prems]])
       apply (simp add: convert_fun_upd Let.prems del: fun_upd_apply cong: sat_convert_cong)
    by fact+
next
  case (LetPast P p m i V \<phi>' \<phi> n R \<psi> \<psi>' buf b)
  show ?case
    apply (rule wf_mformula.LetPast)
          apply (rule LetPast.IH(1))
    subgoal 1
      apply (simp add: convert_fun_upd LetPast.prems del: fun_upd_apply)
      apply (rule arg_cong[where f="\<lambda>g. map_\<Gamma>i (\<lambda>i db. db(_ := g i)) _"])
      apply (intro ext Collect_cong)
      apply (rule arg_cong[where f="\<lambda>g. Formula.letpast_sat g _ _ \<and> _"])
      apply (simp add: fun_eq_iff LetPast.prems sat_convert_cong[of \<sigma> _ \<sigma>'] convert_fun_upd del: fun_upd_apply)
      done
         apply (simp only: letpast_progress_def)
         apply (rule LetPast.IH(2)[unfolded letpast_progress_def progress_convert_cong[OF LetPast.prems]])
         apply (rule 1)
    subgoal
      apply (insert LetPast.hyps(3))
      apply (simp only: letpast_progress_def progress_convert_cong[OF LetPast.prems])
      apply (erule option.case_cong[OF refl refl, THEN iffD1, rotated])
      apply (rule arg_cong[of "\<lambda>a b c. Formula.sat \<sigma> (_ (Some a)) b c _" "\<lambda>a b c. Formula.sat \<sigma>' (_ (Some a)) b c _"])
      apply (simp add: fun_eq_iff LetPast.prems sat_convert_cong[of \<sigma> _ \<sigma>'] convert_fun_upd del: fun_upd_apply)
      done
    by fact+
next
  case (And P V n R \<phi> \<phi>' \<psi> \<psi>' pos \<chi> buf)
  then show ?case
    by (auto simp add: wf_mbuf2'_def progress_convert_cong[of \<sigma> V \<sigma>' V'] cong: sat_convert_cong
        intro!: wf_mformula.intros)
next
  case (Ands P V n R l l_pos l_neg l' buf A_pos A_neg)
  have 1: "progress \<sigma> = progress \<sigma>'"
    "Formula.sat \<sigma> V = Formula.sat \<sigma>' V'"
    by (simp_all add: fun_eq_iff progress_convert_cong[of \<sigma> V \<sigma>' V'] Ands.prems
        sat_convert_cong[of \<sigma> _ \<sigma>'] convert_fun_upd del: fun_upd_apply)
  show ?case
    apply (rule wf_mformula.Ands[where l_pos=l_pos and l_neg=l_neg])
           apply (rule list.rel_mono_strong[OF Ands.IH])
           apply (simp add: Ands.prems)
    using Ands.hyps(1) apply (simp add: wf_mbufn_def 1)
    by fact+
next
  case (Or P V n R \<phi> \<phi>' \<psi> \<psi>' buf)
  then show ?case
    by (auto simp add: wf_mbuf2'_def progress_convert_cong[of \<sigma> V \<sigma>' V'] cong: sat_convert_cong
        intro!: wf_mformula.intros)
next
  case (Prev P V n R \<phi> \<phi>' first buf nts I)
  then show ?case
    by (auto simp add: progress_convert_cong[of \<sigma> V \<sigma>' V'] cong: sat_convert_cong
        intro!: wf_mformula.intros elim!: list.rel_mono_strong dest!: arg_cong[where f=\<tau>])
next
  case (Next P V n R \<phi> \<phi>' first nts I)
  then show ?case
    by (auto simp add: progress_convert_cong[of \<sigma> V \<sigma>' V'] cong: sat_convert_cong
        intro!: wf_mformula.intros elim!: list.rel_mono_strong dest!: arg_cong[where f=\<tau>])
next
  case (Since P V n R \<phi> \<phi>' \<psi> \<psi>' args \<phi>'' I buf aux)
  moreover obtain buf\<phi> buf\<psi> ts skew where "buf = (buf\<phi>, buf\<psi>, ts, skew)"
    by (cases buf)
  moreover have "Formula.sat \<sigma> V v i \<phi>' = Formula.sat \<sigma>' V' v i \<phi>'"
    "Formula.sat \<sigma> V v i \<psi>' = Formula.sat \<sigma>' V' v i \<psi>'" for v i
    by (simp_all add: fun_eq_iff Since.prems sat_convert_cong[of \<sigma> _ \<sigma>'] convert_fun_upd del: fun_upd_apply)
  moreover have "\<tau> \<sigma> = \<tau> \<sigma>'"
    by (metis Since.prems \<tau>_convert)
  ultimately show ?case
    apply (intro wf_mformula.Since)
              apply (simp_all add: wf_since_aux_def sat_since_point_def
        progress_convert_cong[of \<sigma> V \<sigma>' V'] split del: if_split cong: if_cong) (* SLOW 20s *)
    by force
next
  case (Until P V n R \<phi> \<phi>' \<psi> \<psi>' args \<phi>'' I buf nts t aux)
  moreover have "Formula.sat \<sigma> V v i \<phi>' = Formula.sat \<sigma>' V' v i \<phi>'"
    "Formula.sat \<sigma> V v i \<psi>' = Formula.sat \<sigma>' V' v i \<psi>'" for v i
    by (simp_all add: fun_eq_iff Until.prems sat_convert_cong[of \<sigma> _ \<sigma>'] convert_fun_upd del: fun_upd_apply)
  moreover have "\<tau> \<sigma> = \<tau> \<sigma>'"
    by (metis Until.prems \<tau>_convert)
  ultimately show ?case
    apply (intro wf_mformula.Until)
    by (simp_all add: wf_mbuf2'_def wf_until_aux_def wf_until_auxlist_def wf_ts_def
        progress_convert_cong[of \<sigma> V \<sigma>' V'] split del: if_split cong: if_cong) (* SLOW 30s *)
next
  case (MatchP r P V n R \<phi>s mr mrs buf nts I aux)
  then show ?case sorry
next
  case (MatchF r P V n R \<phi>s mr mrs buf nts t I aux)
  then show ?case sorry
qed (auto intro!: wf_mformula.intros)

lemma convert_unconvert_shadow: "convert (unconvert UNIV \<sigma>) ((unconvertV A \<sigma>)(pn \<mapsto> R))
  = convert (unconvert UNIV (\<sigma>(pn \<Rrightarrow> \<lambda>j. {w. R w j}))) (unconvertV (insert pn A) (\<sigma>(pn \<Rrightarrow> \<lambda>j. {w. R w j})))"
  unfolding convert_def unconvert_def unconvertV_def
  apply simp
  apply (rule arg_cong[where f="\<lambda>g. map_\<Gamma>i g \<sigma>"])
  by (auto simp add: fun_eq_iff \<Gamma>_map_\<Gamma>i split: option.split)

lemma invar_mformula_Let:
  "invar_mformula \<sigma> j P m UNIV \<phi> \<phi>' \<Longrightarrow>
   invar_mformula (\<sigma>((p, m) \<Rrightarrow> \<lambda>j. {w. Sat.sat \<sigma> w j \<phi>'})) j (P((p, m) \<mapsto> Monitor.progress \<sigma> P \<phi>' j)) n
   R \<psi> \<psi>' \<Longrightarrow> {0..<m} \<subseteq> fv \<phi>' \<Longrightarrow> b \<le> m \<Longrightarrow> m = Formula.nfv \<phi>' \<Longrightarrow>
   invar_mformula \<sigma> j P n R (MLet p m \<phi> \<psi>) (formula.Let p \<phi>' \<psi>')"
  unfolding invar_mformula_def
  apply (rule wf_mformula.Let; assumption?)
  apply (simp add: progress_unconvert)
  apply (erule wf_mformula_convert_cong_aux)
  by (simp add: convert_unconvert_shadow flip: sat_unconvert)

end

end