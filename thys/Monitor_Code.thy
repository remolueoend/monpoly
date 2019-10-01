(*<*)
theory Monitor_Code
  imports Monitor
  "HOL-Library.Code_Target_Nat"
  "HOL.String"
  Containers.Containers
begin
(*>*)

derive ccompare MFOTL.trm
derive (eq) ceq MFOTL.trm
derive (rbt) set_impl MFOTL.trm
derive (eq) ceq Monitor.mregex
derive ccompare Monitor.mregex
derive (rbt) set_impl Monitor.mregex
derive (no) cenum Monitor.mregex

lemma image_these: "f ` Option.these X = Option.these (map_option f ` X)"
  by (force simp: in_these_eq Bex_def image_iff map_option_case split: option.splits)

lemma meval_MPred: "meval n t db (MPred e ts) = ([Option.these
  ((map_option (\<lambda>f. tabulate f 0 n) o match ts) ` (\<Union>(e', x)\<in>db. if e = e' then {x} else {}))], MPred e ts)"
  unfolding meval.simps image_these image_image o_def ..

lemma meval_MPred': "meval n t db (MPred e ts) = ([Option.these
  (\<Union>(e', x)\<in>db. if e = e' then {map_option (\<lambda>f. tabulate f 0 n) (match ts x)} else {})], MPred e ts)"
  unfolding meval_MPred image_UN split_beta if_distrib[of "image _"] image_insert image_empty o_apply
  ..

lemma these_UNION: "Option.these (UNION A B) = UNION A (Option.these o B)"
  by (auto simp: Option.these_def)

lemma meval_MPred'': "meval n t db (MPred e ts) = ([
  (\<Union>(e', x)\<in>db. if e = e' then set_option (map_option (\<lambda>f. tabulate f 0 n) (match ts x)) else {})], MPred e ts)"
  unfolding meval_MPred' these_UNION o_def prod.case_distrib[of Option.these]
  by (auto simp: Option.these_def map_option_case image_iff split: if_splits option.splits)

lemmas meval_code[code] = meval.simps(1) meval_MPred'' meval.simps(3-9)

definition db_code :: "(char list \<times> 'a list) list \<Rightarrow> (char list \<times> 'a list) set" where
  "db_code = set"

definition verdict_code :: "_ \<Rightarrow> (nat \<times> 'a :: ccompare option list) list" where
  "verdict_code = RBT_Set2.keys"

lemma saturate_commute:
  assumes "\<And>s. r \<in> g s" "\<And>s. g (insert r s) = g s" "\<And>s. r \<in> s \<Longrightarrow> h s = g s"
  and terminates: "mono g" "\<And>X. X \<subseteq> C \<Longrightarrow> g X \<subseteq> C" "finite C"
shows "saturate g {} = saturate h {r}"
proof (cases "g {} = {r}")
  case True
  with assms have "g {r} = {r}" "h {r} = {r}" by auto
  with True show ?thesis
    by (subst (1 2) saturate_code; subst saturate_code) (simp add: Let_def)
next
  case False
  then show ?thesis 
    unfolding saturate_def while_def
    using while_option_finite_subset_Some[OF terminates] assms(1-3)
    by (subst while_option_commute_invariant[of "\<lambda>S. S = {} \<or> r \<in> S" "\<lambda>S. g S \<noteq> S" g "\<lambda>S. h S \<noteq> S" "insert r" h "{}", symmetric])
      (auto 4 4 dest: while_option_stop[of "\<lambda>S. g S \<noteq> S" g "{}"])
qed

definition "RPDs_aux = saturate (\<lambda>S. S \<union> \<Union> (RPD ` S))"

lemma RPDs_aux_code[code]:
  "RPDs_aux S = (let S' = S \<union> Set.bind S RPD in if S' \<subseteq> S then S else RPDs_aux S')"
  unfolding RPDs_aux_def bind_UNION
  by (subst saturate_code) auto

declare RPDs_code[code del]
lemma RPDs_code[code]: "RPDs r = RPDs_aux {r}"
  unfolding RPDs_aux_def RPDs_code
  by (rule saturate_commute[where C="RPDs r"])
     (auto simp: mono_def subset_singleton_iff RPDs_refl RPDs_trans finite_RPDs)

definition "LPDs_aux = saturate (\<lambda>S. S \<union> \<Union> (LPD ` S))"

lemma LPDs_aux_code[code]:
  "LPDs_aux S = (let S' = S \<union> Set.bind S LPD in if S' \<subseteq> S then S else LPDs_aux S')"
  unfolding LPDs_aux_def bind_UNION
  by (subst saturate_code) auto

declare LPDs_code[code del]
lemma LPDs_code[code]: "LPDs r = LPDs_aux {r}"
  unfolding LPDs_aux_def LPDs_code
  by (rule saturate_commute[where C="LPDs r"])
     (auto simp: mono_def subset_singleton_iff LPDs_refl LPDs_trans finite_LPDs)

export_code HOL.equal Collection_Eq.ceq Collection_Order.ccompare Eq Lt Gt set_RBT set_impl phantom
  nat_of_integer integer_of_nat enat literal.explode db_code set interval RBT_set verdict_code
  MFOTL.Var MFOTL.Const
  MFOTL.Pred MFOTL.Eq MFOTL.Neg MFOTL.Or MFOTL.Exists
  MFOTL.Prev MFOTL.Next MFOTL.Since MFOTL.Until MFOTL.MatchP MFOTL.MatchF
  checking OCaml?

export_code HOL.equal Collection_Eq.ceq Collection_Order.ccompare Eq Lt Gt set_RBT set_impl phantom
  nat_of_integer integer_of_nat enat literal.explode db_code set interval RBT_set verdict_code
  MFOTL.Var MFOTL.Const
  MFOTL.Pred MFOTL.Eq MFOTL.Neg MFOTL.Or MFOTL.Exists
  MFOTL.Prev MFOTL.Next MFOTL.Since MFOTL.Until MFOTL.MatchP MFOTL.MatchF
  MFOTL.Wild MFOTL.Test MFOTL.Plus MFOTL.Times MFOTL.Star
  safe_formula
  minit_safe mstep in OCaml module_name Monitor file_prefix "verified"

(*<*)
end
(*>*)
