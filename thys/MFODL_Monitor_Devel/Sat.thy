theory Sat
  imports Formula
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

lemma map_\<Gamma>i_comp: "map_\<Gamma>i f (map_\<Gamma>i g \<sigma>) = map_\<Gamma>i (\<lambda>i. f i o g i) \<sigma>"
  by transfer (auto simp: stream_eq_iff split: prod.splits)

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

lemma \<tau>_convert[simp]: "\<tau> (convert \<sigma> V) = \<tau> \<sigma>"
  unfolding convert_def by simp

lemma convert_update_\<Gamma>: "(convert \<sigma> V)(pn \<Rrightarrow> X) = convert \<sigma> (V(pn \<mapsto> \<lambda>v i. v \<in> X i))"
  unfolding convert_def
  by (auto simp: map_\<Gamma>i_comp fun_eq_iff intro!: arg_cong[of _ _ "\<lambda>f. map_\<Gamma>i f \<sigma>"])

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
  case (LetPast x1 \<phi>1 \<phi>2)
  then show ?case
    by (simp del: fun_upd_apply add: Let_def convert_update_\<Gamma> letpast_sat_alt)
qed (auto split: nat.splits cong: match_cong)

end