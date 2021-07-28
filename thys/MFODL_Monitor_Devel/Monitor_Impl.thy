(*<*)
theory Monitor_Impl
  imports Monitor
    Optimized_MTL
    "HOL-Library.Code_Target_Nat"
    Containers.Containers
    "Generic_Join_Devel.Proj_Code"
begin
(*>*)

section \<open>Instantiation of the generic algorithm and code setup\<close>

(*
  The following snippet (context \<dots> end) is taken from HOL-Library.Code_Cardinality.
  We do not include the entire theory because the remaining code setup is superseded
  by Containers.
*)
context
begin

qualified definition card_UNIV' :: "'a card_UNIV"
where [code del]: "card_UNIV' = Phantom('a) CARD('a)"

lemma CARD_code [code_unfold]:
  "CARD('a) = of_phantom (card_UNIV' :: 'a card_UNIV)"
by(simp add: card_UNIV'_def)

lemma card_UNIV'_code [code]:
  "card_UNIV' = card_UNIV"
by(simp add: card_UNIV card_UNIV'_def)

end

instantiation enat :: set_impl begin
definition set_impl_enat :: "(enat, set_impl) phantom" where
  "set_impl_enat = phantom set_RBT"

instance ..
end

derive ccompare Formula.trm
derive (eq) ceq Formula.trm
derive (rbt) set_impl Formula.trm
derive (eq) ceq Monitor.mregex
derive ccompare Monitor.mregex
derive (rbt) set_impl Monitor.mregex
derive (rbt) mapping_impl Monitor.mregex
derive (no) cenum Monitor.mregex
derive (rbt) set_impl string8
derive (rbt) mapping_impl string8
derive (rbt) set_impl event_data
derive (rbt) mapping_impl event_data

type_synonym 'a vmsaux = "nat \<times> (nat \<times> 'a table) list"

definition valid_vmsaux :: "args \<Rightarrow> nat \<Rightarrow> event_data vmsaux \<Rightarrow>
  (nat \<times> event_data table) list \<Rightarrow> bool" where
  "valid_vmsaux = (\<lambda>_ cur (t, aux) auxlist. t = cur \<and> aux = auxlist)"

definition init_vmsaux :: "args \<Rightarrow> event_data vmsaux" where
  "init_vmsaux = (\<lambda>_. (0, []))"

definition add_new_ts_vmsaux :: "args \<Rightarrow> nat \<Rightarrow> event_data vmsaux \<Rightarrow> event_data vmsaux" where
  "add_new_ts_vmsaux = (\<lambda>args nt (t, auxlist). (nt, filter (\<lambda>(t, rel).
    memR (args_ivl args) (nt - t)) auxlist))"

definition join_vmsaux :: "args \<Rightarrow> event_data table \<Rightarrow> event_data vmsaux \<Rightarrow> event_data vmsaux" where
  "join_vmsaux = (\<lambda>args rel1 (t, auxlist). (t, map (\<lambda>(t, rel).
    (t, join rel (args_pos args) rel1)) auxlist))"

definition add_new_table_vmsaux :: "args \<Rightarrow> event_data table \<Rightarrow> event_data vmsaux \<Rightarrow>
  event_data vmsaux" where
  "add_new_table_vmsaux = (\<lambda>args rel2 (cur, auxlist). (cur, (case auxlist of
    [] => [(cur, rel2)]
  | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> rel2) # ts else (cur, rel2) # auxlist)))"

definition result_vmsaux :: "args \<Rightarrow> event_data vmsaux \<Rightarrow> event_data table" where
  "result_vmsaux = (\<lambda>args (cur, auxlist).
    foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {})"

type_synonym 'a vmuaux = "nat \<times> (nat \<times> 'a table \<times> 'a table) list"

definition valid_vmuaux :: "args \<Rightarrow> nat \<Rightarrow> event_data vmuaux \<Rightarrow>
  (nat \<times> event_data table \<times> event_data table) list \<Rightarrow> bool" where
  "valid_vmuaux = (\<lambda>_ cur (t, aux) auxlist. t = cur \<and> aux = auxlist)"

definition init_vmuaux :: "args \<Rightarrow> event_data vmuaux" where
  "init_vmuaux = (\<lambda>_. (0, []))"

definition add_new_vmuaux ::  "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> nat \<Rightarrow>
  event_data vmuaux \<Rightarrow> event_data vmuaux" where
  "add_new_vmuaux = (\<lambda>args rel1 rel2 nt (t, auxlist). (nt, update_until args rel1 rel2 nt auxlist))"

definition length_vmuaux :: "args \<Rightarrow> event_data vmuaux \<Rightarrow> nat" where
  "length_vmuaux = (\<lambda>_ (_, auxlist). length auxlist)"

definition eval_vmuaux :: "args \<Rightarrow> nat \<Rightarrow> event_data vmuaux \<Rightarrow>
  event_data table list \<times> event_data vmuaux" where
  "eval_vmuaux = (\<lambda>args nt (t, auxlist).
    (let (res, auxlist') = eval_until (args_ivl args) nt auxlist in (res, (t, auxlist'))))"

global_interpretation verimon_maux: maux valid_vmsaux init_vmsaux add_new_ts_vmsaux join_vmsaux
  add_new_table_vmsaux result_vmsaux valid_vmuaux init_vmuaux add_new_vmuaux length_vmuaux
  eval_vmuaux
  defines vminit0 = "maux.minit0 (init_vmsaux :: _ \<Rightarrow> event_data vmsaux) (init_vmuaux :: _ \<Rightarrow> event_data vmuaux) :: _ \<Rightarrow> Formula.formula \<Rightarrow> _"
  and vminit = "maux.minit (init_vmsaux :: _ \<Rightarrow> event_data vmsaux) (init_vmuaux :: _ \<Rightarrow> event_data vmuaux) :: Formula.formula \<Rightarrow> _"
  and vminit_safe = "maux.minit_safe (init_vmsaux :: _ \<Rightarrow> event_data vmsaux) (init_vmuaux :: _ \<Rightarrow> event_data vmuaux) :: Formula.formula \<Rightarrow> _"
  and vmeval_since = "maux.eval_since add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> event_data table)"
  and vmeval = "maux.meval add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _)"
  and letpast_vmeval = "maux.letpast_meval add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _)"
  and vmstep = "maux.mstep add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _)"
  and vmsteps0_stateless = "maux.msteps0_stateless add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _)"
  and vmsteps_stateless = "maux.msteps_stateless add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _)"
  and vmonitor = "maux.monitor init_vmsaux add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) init_vmuaux add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _)"
  unfolding valid_vmsaux_def init_vmsaux_def add_new_ts_vmsaux_def join_vmsaux_def
    add_new_table_vmsaux_def result_vmsaux_def valid_vmuaux_def init_vmuaux_def add_new_vmuaux_def
    length_vmuaux_def eval_vmuaux_def
  by unfold_locales auto

global_interpretation default_maux: maux valid_mmsaux "init_mmsaux :: _ \<Rightarrow> event_data mmsaux" add_new_ts_mmsaux gc_join_mmsaux add_new_table_mmsaux result_mmsaux
  valid_mmuaux "init_mmuaux :: _ \<Rightarrow> event_data mmuaux" add_new_mmuaux length_mmuaux eval_mmuaux'
  defines minit0 = "maux.minit0 (init_mmsaux :: _ \<Rightarrow> event_data mmsaux) (init_mmuaux :: _ \<Rightarrow> event_data mmuaux) :: _ \<Rightarrow> Formula.formula \<Rightarrow> _"
  and minit = "maux.minit (init_mmsaux :: _ \<Rightarrow> event_data mmsaux) (init_mmuaux :: _ \<Rightarrow> event_data mmuaux) :: Formula.formula \<Rightarrow> _"
  and minit_safe = "maux.minit_safe (init_mmsaux :: _ \<Rightarrow> event_data mmsaux) (init_mmuaux :: _ \<Rightarrow> event_data mmuaux) :: Formula.formula \<Rightarrow> _"
  and meval_since = "maux.eval_since add_new_ts_mmsaux gc_join_mmsaux add_new_table_mmsaux (result_mmsaux :: _ \<Rightarrow> event_data mmsaux \<Rightarrow> event_data table)"
  and meval = "maux.meval add_new_ts_mmsaux gc_join_mmsaux add_new_table_mmsaux (result_mmsaux :: _ \<Rightarrow> event_data mmsaux \<Rightarrow> _) add_new_mmuaux (eval_mmuaux' :: _ \<Rightarrow> _ \<Rightarrow> event_data mmuaux \<Rightarrow> _)"
  and letpast_meval = "maux.letpast_meval add_new_ts_mmsaux gc_join_mmsaux add_new_table_mmsaux (result_mmsaux :: _ \<Rightarrow> event_data mmsaux \<Rightarrow> _) add_new_mmuaux (eval_mmuaux' :: _ \<Rightarrow> _ \<Rightarrow> event_data mmuaux \<Rightarrow> _)"
  and mstep = "maux.mstep add_new_ts_mmsaux gc_join_mmsaux add_new_table_mmsaux (result_mmsaux :: _ \<Rightarrow> event_data mmsaux \<Rightarrow> _) add_new_mmuaux (eval_mmuaux' :: _ \<Rightarrow> _ \<Rightarrow> event_data mmuaux \<Rightarrow> _)"
  and msteps0_stateless = "maux.msteps0_stateless add_new_ts_mmsaux gc_join_mmsaux add_new_table_mmsaux (result_mmsaux :: _ \<Rightarrow> event_data mmsaux \<Rightarrow> _) add_new_mmuaux (eval_mmuaux' :: _ \<Rightarrow> _ \<Rightarrow> event_data mmuaux \<Rightarrow> _)"
  and msteps_stateless = "maux.msteps_stateless add_new_ts_mmsaux gc_join_mmsaux add_new_table_mmsaux (result_mmsaux :: _ \<Rightarrow> event_data mmsaux \<Rightarrow> _) add_new_mmuaux (eval_mmuaux' :: _ \<Rightarrow> _ \<Rightarrow> event_data mmuaux \<Rightarrow> _)"
  and monitor = "maux.monitor init_mmsaux add_new_ts_mmsaux gc_join_mmsaux add_new_table_mmsaux (result_mmsaux :: _ \<Rightarrow> event_data mmsaux \<Rightarrow> _) init_mmuaux add_new_mmuaux (eval_mmuaux' :: _ \<Rightarrow> _ \<Rightarrow> event_data mmuaux \<Rightarrow> _)"
  by unfold_locales

lemma image_these: "f ` Option.these X = Option.these (map_option f ` X)"
  by (force simp: in_these_eq Bex_def image_iff map_option_case split: option.splits)

definition "meval_pred_impl n ts db e tms mode =
  (case Mapping.lookup db (e, length tms) of
      None \<Rightarrow> replicate (length ts) {}
    | Some Xs \<Rightarrow> (case mode of
        Copy \<Rightarrow> Xs
      | Simple \<Rightarrow> map (\<lambda>X. simple_match n 0 tms ` X) Xs
      | Match \<Rightarrow> map (\<lambda>X. \<Union>v \<in> X. (set_option (map_option (\<lambda>f. Table.tabulate f 0 n) (match tms v)))) Xs))"
declare meval_pred_impl_def[code_unfold]

lemma meval_pred_impl_eq: "meval_pred_impl n ts db e tms mode =
  (case Mapping.lookup db (e, length tms) of
      None \<Rightarrow> replicate (length ts) {}
    | Some xs \<Rightarrow> (case mode of
        Copy \<Rightarrow> xs
      | Simple \<Rightarrow> map (\<lambda>X. simple_match n 0 tms ` X) xs
      | Match \<Rightarrow> map (\<lambda>X. (\<lambda>f. Table.tabulate f 0 n) ` Option.these (match tms ` X)) xs))"
  unfolding meval_pred_impl_def
  by (force simp: Option.these_def image_iff intro!: option.case_cong pred_mode.case_cong)

lemma meval_MPred: "meval lookahead n ts db (MPred e tms mode) =
  (meval_pred_impl n ts db e tms mode, MPred e tms mode)"
  by (simp add: meval_pred_impl_eq)

lemma vmeval_MPred: "vmeval lookahead n ts db (MPred e tms mode) =
  (meval_pred_impl n ts db e tms mode, MPred e tms mode)"
  by (simp add: meval_pred_impl_eq)

declare [[code drop: meval vmeval]]
lemmas meval_code[code] = default_maux.meval_simps(1) meval_MPred default_maux.meval_simps(3-)
lemmas vmeval_code[code] = verimon_maux.meval_simps(1) vmeval_MPred verimon_maux.meval_simps(3-)

definition mk_db :: "((Formula.name \<times> nat) \<times> event_data option list set) list \<Rightarrow> database" where
  "mk_db m = Mapping.of_alist (map (\<lambda>(p, X). (p, [X])) m)"

definition rbt_fold :: "_ \<Rightarrow> event_data tuple set_rbt \<Rightarrow> _ \<Rightarrow> _" where
  "rbt_fold = RBT_Set2.fold"

definition rbt_empty :: "event_data option list set_rbt" where
  "rbt_empty = RBT_Set2.empty"

definition rbt_insert :: "_ \<Rightarrow> _ \<Rightarrow> event_data option list set_rbt" where
  "rbt_insert = RBT_Set2.insert"

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
     (auto 0 3 simp: mono_def subset_singleton_iff RPDs_refl RPDs_trans finite_RPDs)

definition "LPDs_aux = saturate (\<lambda>S. S \<union> \<Union> (LPD ` S))"

lemma LPDs_aux_code[code]:
  "LPDs_aux S = (let S' = S \<union> Set.bind S LPD in if S' \<subseteq> S then S else LPDs_aux S')"
  unfolding LPDs_aux_def bind_UNION
  by (subst saturate_code) auto

declare LPDs_code[code del]
lemma LPDs_code[code]: "LPDs r = LPDs_aux {r}"
  unfolding LPDs_aux_def LPDs_code
  by (rule saturate_commute[where C="LPDs r"])
     (auto 0 3 simp: mono_def subset_singleton_iff LPDs_refl LPDs_trans finite_LPDs)

lemma is_empty_table_unfold [code_unfold]:
  "X = empty_table \<longleftrightarrow> Set.is_empty X"
  "empty_table = X \<longleftrightarrow> Set.is_empty X"
  "set_eq X empty_table \<longleftrightarrow> Set.is_empty X"
  "set_eq empty_table X \<longleftrightarrow> Set.is_empty X"
  "X = (set_empty impl) \<longleftrightarrow> Set.is_empty X"
  "(set_empty impl) = X \<longleftrightarrow> Set.is_empty X"
  "set_eq X (set_empty impl) \<longleftrightarrow> Set.is_empty X"
  "set_eq (set_empty impl) X \<longleftrightarrow> Set.is_empty X"
  unfolding set_eq_def set_empty_def empty_table_def Set.is_empty_def by auto

lemma tabulate_rbt_code[code]: "Monitor.mrtabulate (xs :: mregex list) f =
  (case ID CCOMPARE(mregex) of None \<Rightarrow> Code.abort (STR ''tabulate RBT_Mapping: ccompare = None'') (\<lambda>_. Monitor.mrtabulate (xs :: mregex list) f)
  | _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.bulkload (List.map_filter (\<lambda>k. let fk = f k in if fk = empty_table then None else Some (k, fk)) xs)))"
  unfolding mrtabulate.abs_eq RBT_Mapping_def
  by (auto split: option.splits)

lemma combine_Mapping[code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt" shows
  "Mapping.combine f (RBT_Mapping t) (RBT_Mapping u) = 
  (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''combine RBT_Mapping: ccompare = None'') (\<lambda>_. Mapping.combine f (RBT_Mapping t) (RBT_Mapping u))
                     | Some _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.join (\<lambda>_. f) t u))"
  by (auto simp add: Mapping.combine.abs_eq Mapping_inject lookup_join split: option.split)

lemma upd_set_empty[simp]: "upd_set m f {} = m"
  by transfer auto

lemma upd_set_insert[simp]: "upd_set m f (insert x A) = Mapping.update x (f x) (upd_set m f A)"
  by (rule mapping_eqI) (auto simp: Mapping_lookup_upd_set Mapping.lookup_update')

lemma upd_set_fold:
  assumes "finite A"
  shows "upd_set m f A = Finite_Set.fold (\<lambda>a. Mapping.update a (f a)) m A"
proof -
  interpret comp_fun_idem "\<lambda>a. Mapping.update a (f a)"
    by unfold_locales (transfer; auto simp: fun_eq_iff)+
  from assms show ?thesis
    by (induct A arbitrary: m rule: finite.induct) auto
qed

lift_definition upd_cfi :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, ('a, 'b) mapping) comp_fun_idem"
  is "\<lambda>f a m. Mapping.update a (f a) m"
  by unfold_locales (transfer; auto simp: fun_eq_iff)+

lemma upd_set_code[code]:
  "upd_set m f A = (if finite A then set_fold_cfi (upd_cfi f) m A else Code.abort (STR ''upd_set: infinite'') (\<lambda>_. upd_set m f A))"
  by (transfer fixing: m) (auto simp: upd_set_fold)

lemma lexordp_eq_code[code]: "lexordp_eq xs ys \<longleftrightarrow> (case xs of [] \<Rightarrow> True
  | x # xs \<Rightarrow> (case ys of [] \<Rightarrow> False
    | y # ys \<Rightarrow> if x < y then True else if x > y then False else lexordp_eq xs ys))"
  by (subst lexordp_eq.simps) (auto split: list.split)

lemma upd_set'_empty[simp]: "upd_set' m d f {} = m"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup)

lemma upd_set'_insert: "d = f d \<Longrightarrow> (\<And>x. f (f x) = f x) \<Longrightarrow> upd_set' m d f (insert x A) =
  (let m' = (upd_set' m d f A) in case Mapping.lookup m' x of None \<Rightarrow> Mapping.update x d m'
  | Some v \<Rightarrow> Mapping.update x (f v) m')"
  by (rule mapping_eqI) (auto simp: upd_set'_lookup Mapping.lookup_update' split: option.splits)

lemma upd_set'_aux1: "upd_set' Mapping.empty d f {b. b = k \<or> (a, b) \<in> A} =
  Mapping.update k d (upd_set' Mapping.empty d f {b. (a, b) \<in> A})"
  by (rule mapping_eqI) (auto simp add: Let_def upd_set'_lookup Mapping.lookup_update'
      Mapping.lookup_empty split: option.splits)

lemma upd_set'_aux2: "Mapping.lookup m k = None \<Longrightarrow> upd_set' m d f {b. b = k \<or> (a, b) \<in> A} =
  Mapping.update k d (upd_set' m d f {b. (a, b) \<in> A})"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup Mapping.lookup_update' split: option.splits)

lemma upd_set'_aux3: "Mapping.lookup m k = Some v \<Longrightarrow> upd_set' m d f {b. b = k \<or> (a, b) \<in> A} =
  Mapping.update k (f v) (upd_set' m d f {b. (a, b) \<in> A})"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup Mapping.lookup_update' split: option.splits)

lemma upd_set'_aux4: "k \<notin> fst ` A \<Longrightarrow> upd_set' Mapping.empty d f {b. (k, b) \<in> A} = Mapping.empty"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup Mapping.lookup_update' Domain.DomainI fst_eq_Domain
      split: option.splits)

lemma upd_nested_empty[simp]: "upd_nested m d f {} = m"
  by (rule mapping_eqI) (auto simp add: upd_nested_lookup split: option.splits)

definition upd_nested_step :: "'c \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> ('a, ('b, 'c) mapping) mapping \<Rightarrow>
  ('a, ('b, 'c) mapping) mapping" where
  "upd_nested_step d f x m = (case x of (k, k') \<Rightarrow>
    (case Mapping.lookup m k of Some m' \<Rightarrow>
      (case Mapping.lookup m' k' of Some v \<Rightarrow> Mapping.update k (Mapping.update k' (f v) m') m
      | None \<Rightarrow> Mapping.update k (Mapping.update k' d m') m)
    | None \<Rightarrow> Mapping.update k (Mapping.update k' d Mapping.empty) m))"

lemma upd_nested_insert:
  "d = f d \<Longrightarrow> (\<And>x. f (f x) = f x) \<Longrightarrow> upd_nested m d f (insert x A) =
  upd_nested_step d f x (upd_nested m d f A)"
  unfolding upd_nested_step_def
  using upd_set'_aux1[of d f _ _ A] upd_set'_aux2[of _ _ d f _ A] upd_set'_aux3[of _ _ _ d f _ A]
    upd_set'_aux4[of _ A d f]
  by (auto simp add: Let_def upd_nested_lookup upd_set'_lookup Mapping.lookup_update'
      Mapping.lookup_empty split: option.splits prod.splits if_splits intro!: mapping_eqI)

lemma upd_nested_max_tstp_fold:
  assumes "finite X"
  shows "upd_nested_max_tstp m d X = Finite_Set.fold (upd_nested_step d (max_tstp d)) m X"
proof -
  interpret comp_fun_idem "upd_nested_step d (max_tstp d)"
    by (unfold_locales; rule ext)
      (auto simp add: comp_def upd_nested_step_def Mapping.lookup_update' Mapping.lookup_empty
       update_update max_tstp_d_d max_tstp_idem' split: option.splits)
  note upd_nested_insert' = upd_nested_insert[of d "max_tstp d",
    OF max_tstp_d_d[symmetric] max_tstp_idem']
  show ?thesis
    using assms
    by (induct X arbitrary: m rule: finite.induct)
       (auto simp add: upd_nested_max_tstp_def upd_nested_insert')
qed

lift_definition upd_nested_max_tstp_cfi ::
  "ts + tp \<Rightarrow> ('a \<times> 'b, ('a, ('b, ts + tp) mapping) mapping) comp_fun_idem"
  is "\<lambda>d. upd_nested_step d (max_tstp d)"
  by (unfold_locales; rule ext)
    (auto simp add: comp_def upd_nested_step_def Mapping.lookup_update' Mapping.lookup_empty
      update_update max_tstp_d_d max_tstp_idem' split: option.splits)

lemma upd_nested_max_tstp_code[code]:
  "upd_nested_max_tstp m d X = (if finite X then set_fold_cfi (upd_nested_max_tstp_cfi d) m X
    else Code.abort (STR ''upd_nested_max_tstp: infinite'') (\<lambda>_. upd_nested_max_tstp m d X))"
  by transfer (auto simp add: upd_nested_max_tstp_fold)

lemma filter_set_empty[simp]: "filter_set (t, {}) (m, Y) = (m, Y)"
  unfolding filter_set.simps
  by transfer (auto simp: Let_def fun_eq_iff split: option.splits)

lemma filter_set_insert[simp]: "filter_set (t, insert x A) (m, Y) = (let (m', Y') = filter_set (t, A) (m, Y) in
  case Mapping.lookup m' x of Some u \<Rightarrow> if t = u then (Mapping.delete x m', Y' \<union> {x}) else (m', Y') | _ \<Rightarrow> (m', Y'))"
  unfolding filter_set.simps
  by transfer (auto simp: fun_eq_iff Let_def Map_To_Mapping.map_apply_def split: option.splits)

lemma filter_set_fold:
  assumes "finite A"
  shows "filter_set (t, A) (m, Y) = Finite_Set.fold (\<lambda>a (m, Y).
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then (Mapping.delete a m, Y \<union> {a}) else (m, Y) | _ \<Rightarrow> (m, Y)) (m, Y) A"
proof -
  interpret comp_fun_idem "\<lambda>a (m, Y).
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then (Mapping.delete a m, Y \<union> {a}) else (m, Y) | _ \<Rightarrow> (m, Y)"
    by unfold_locales
      (transfer; auto simp: fun_eq_iff Map_To_Mapping.map_apply_def split: option.splits)+
  from assms show ?thesis
    by (induct A arbitrary: m rule: finite.induct) (auto simp: Let_def)
qed

lift_definition filter_cfi :: "'b \<Rightarrow> ('a, ('a, 'b) mapping \<times> 'a set) comp_fun_idem"
  is "\<lambda>t a (m, Y).
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then (Mapping.delete a m, Y \<union> {a}) else (m, Y) | _ \<Rightarrow> (m, Y)"
  by unfold_locales (transfer; auto simp: fun_eq_iff Map_To_Mapping.map_apply_def split: option.splits)+

lemma filter_set_code[code]:
  "filter_set (t, A) (m, Y) = (if finite A then set_fold_cfi (filter_cfi t) (m, Y) A else Code.abort (STR ''upd_set: infinite'') (\<lambda>_. filter_set (t, A) (m, Y)))"
  by (transfer fixing: m) (auto simp: filter_set_fold)

lemma filter_join_False_empty: "filter_join False {} m = m"
  unfolding filter_join_def
  by transfer (auto split: option.splits)

lemma filter_join_False_insert: "filter_join False (insert a A) m =
  filter_join False A (Mapping.delete a m)"
proof -
  {
    fix x
    have "Mapping.lookup (filter_join False (insert a A) m) x =
      Mapping.lookup (filter_join False A (Mapping.delete a m)) x"
      by (auto simp add: filter_join_def Mapping.lookup_filter Mapping_lookup_delete
          split: option.splits)
  }
  then show ?thesis
    by (simp add: mapping_eqI)
qed

lemma filter_join_False:
  assumes "finite A"
  shows "filter_join False A m = Finite_Set.fold Mapping.delete m A"
proof -
  interpret comp_fun_idem "Mapping.delete"
    by (unfold_locales; transfer) (fastforce simp add: comp_def)+
  from assms show ?thesis
    by (induction A arbitrary: m rule: finite.induct)
       (auto simp add: filter_join_False_empty filter_join_False_insert fold_fun_left_comm)
qed

lift_definition filter_not_in_cfi :: "('a, ('a, 'b) mapping) comp_fun_idem" is "Mapping.delete"
  by (unfold_locales; transfer) (fastforce simp add: comp_def)+

lemma filter_join_code[code]:
  "filter_join pos A m =
    (if \<not>pos \<and> finite A then set_fold_cfi filter_not_in_cfi m A
    else Mapping.filter (join_filter_cond pos A) m)"
  unfolding filter_join_def
  by (transfer fixing: m) (use filter_join_False in \<open>auto simp add: filter_join_def\<close>)

lemma mapping_delete_set_empty: "mapping_delete_set m {} = m"
  unfolding mapping_delete_set_def by (simp add: Mapping.lookup.rep_eq rep_inverse)

lemma mapping_delete_set_insert: "mapping_delete_set m (Set.insert a X) = Mapping.delete a (mapping_delete_set m X)"
proof(rule mapping_eqI)
  fix x
  show "Mapping.lookup (mapping_delete_set m (Set.insert a X)) x =
        Mapping.lookup (Mapping.delete a (mapping_delete_set m X)) x"
    unfolding Optimized_MTL.Mapping_lookup_delete mapping_delete_set_def
    by(auto simp: Mapping.lookup.rep_eq Mapping_inverse)
qed

lemma mapping_delete_fold:
  assumes "finite A"
  shows "mapping_delete_set m A = Finite_Set.fold Mapping.delete m A"
proof -
  interpret comp_fun_idem "Mapping.delete" by(unfold_locales; transfer; simp add: fun_eq_iff) 
  from assms show ?thesis
  proof (induction A arbitrary: m)
    case empty
    then show ?case using mapping_delete_set_empty by auto
  next
    case (insert a A)
    then show ?case using mapping_delete_set_insert[of m a A] fold_insert[OF insert(1-2), of m] by(simp)
  qed 
qed

lift_definition mapping_delete_set_cfi :: "('a, ('a, 'b) mapping) comp_fun_idem" is 
  Mapping.delete by(unfold_locales; transfer; simp add:fun_eq_iff)

lemma mapping_delete_set_code[code]:
  "mapping_delete_set m A = (if finite A then set_fold_cfi mapping_delete_set_cfi m A else Code.abort (STR ''mapping_delete_set: infinite'') (\<lambda>_. mapping_delete_set m A))"
  using mapping_delete_fold[of A m] by (simp add: mapping_delete_set_cfi.rep_eq set_fold_cfi.rep_eq)

(*
definition set_minus :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "set_minus X Y = X - Y"

lift_definition remove_cfi :: "('a, 'a set) comp_fun_idem"
  is "\<lambda>b a. a - {b}"
  by unfold_locales auto

lemma set_minus_finite:
  assumes fin: "finite Y"
  shows "set_minus X Y = Finite_Set.fold (\<lambda>a X. X - {a}) X Y"
proof -
  interpret comp_fun_idem "\<lambda>a X. X - {a}"
    by unfold_locales auto
  from assms show ?thesis
    by (induction Y arbitrary: X rule: finite.induct) (auto simp add: set_minus_def)
qed

lemma set_minus_code[code]: "set_minus X Y =
  (if finite Y \<and> card Y < card X then set_fold_cfi remove_cfi X Y else X - Y)"
  by transfer (use set_minus_finite in \<open>auto simp add: set_minus_def\<close>)

declare [[code drop: bin_join]]
declare bin_join.simps[folded set_minus_def, code]
*)

definition remove_Union where
  "remove_Union A X B = A - (\<Union>x \<in> X. B x)"

lemma remove_Union_finite: 
  assumes "finite X"
  shows "remove_Union A X B = Finite_Set.fold (\<lambda>x A. A - B x) A X"
proof -
  interpret comp_fun_idem "\<lambda>x A. A - B x"
    by unfold_locales auto
  from assms show ?thesis
    by (induct X arbitrary: A rule: finite_induct) (auto simp: remove_Union_def)
qed

lift_definition remove_Union_cfi :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a, 'b set) comp_fun_idem" is "\<lambda>B x A. A - B x"
  by unfold_locales auto

lemma remove_Union_code[code]: "remove_Union A X B =
  (if finite X then set_fold_cfi (remove_Union_cfi B) A X else A - (\<Union>x \<in> X. B x))"
  by (transfer fixing: A X B) (use remove_Union_finite[of X A B] in \<open>auto simp add: remove_Union_def\<close>)

lemma tabulate_remdups: "Mapping.tabulate xs f = Mapping.tabulate (remdups xs) f"
  by (transfer fixing: xs f) (auto simp: map_of_map_restrict)

declare [[code drop: New_max_getIJ_genericJoin New_max_getIJ_wrapperGenericJoin]]
declare New_max.genericJoin_code[folded remove_Union_def, code]
declare New_max.wrapperGenericJoin.simps[folded remove_Union_def, code]

declare regex.pred_inject[code]

declare regex.pred_set[THEN fun_cong, symmetric, code_unfold]

lemma Bex_pred_regex[code_unfold]: "Bex (regex.atms x) P \<longleftrightarrow> \<not> regex.pred_regex (Not o P) x"
  by (induct x) auto


derive (eq) ceq rec_safety
derive ccompare rec_safety
derive (dlist) set_impl rec_safety

declare [[code drop: safe_letpast]]
lemma safe_letpast_code[code]:
  "safe_letpast p (Formula.Eq t1 t2) = Unused"
  "safe_letpast p (Formula.Less t1 t2) = Unused"        
  "safe_letpast p (Formula.LessEq t1 t2) = Unused"
  "safe_letpast p (Formula.Pred e ts) = (if p = (e, length ts) then NonFutuRec else Unused)"
  "safe_letpast p (Formula.Let e \<phi> \<psi>) =
      (safe_letpast (e, Formula.nfv \<phi>) \<psi> * safe_letpast p \<phi>) \<squnion>
      (if p = (e, Formula.nfv \<phi>) then Unused else safe_letpast p \<psi>)"
  "safe_letpast p (Formula.LetPast e \<phi> \<psi>) =
      (if p = (e, Formula.nfv \<phi>) then Unused else
        (safe_letpast (e, Formula.nfv \<phi>) \<psi> * safe_letpast p \<phi>) \<squnion> safe_letpast p \<psi>)"
  "safe_letpast p (Formula.Neg \<phi>) = safe_letpast p \<phi>"
  "safe_letpast p (Formula.Or \<phi> \<psi>) = (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
  "safe_letpast p (Formula.And \<phi> \<psi>) = (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
  "safe_letpast p (Formula.Ands l) = \<Squnion> set (map (safe_letpast p) l)"
  "safe_letpast p (Formula.Exists \<phi>) = safe_letpast p \<phi>"
  "safe_letpast p (Formula.Agg y \<omega> b' f \<phi>) = safe_letpast p \<phi>"
  "safe_letpast p (Formula.Prev I \<phi>) = PastRec * safe_letpast p \<phi>"
  "safe_letpast p (Formula.Next I \<phi>) = AnyRec * safe_letpast p \<phi>"
  "safe_letpast p (Formula.Since \<phi> I \<psi>) = safe_letpast p \<phi> \<squnion>
    (if memL I 0 then NonFutuRec else PastRec) * safe_letpast p \<psi>"
  "safe_letpast p (Formula.Until \<phi> I \<psi>) = AnyRec * (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
  "safe_letpast p (Formula.MatchP I r) = \<Squnion> Regex.atms (Regex.map_regex (safe_letpast p) r)"
  "safe_letpast p (Formula.MatchF I r) =  AnyRec * \<Squnion> Regex.atms (Regex.map_regex (safe_letpast p) r)"
  by (auto simp add: regex.set_map)

lemma Sup_rec_safety_set[code_unfold]:
  "\<Squnion> (set l :: rec_safety set) = fold (\<squnion>) l Unused"
  by (simp add: Sup_rec_safety_def comp_fun_idem_on.fold_set_fold[OF comp_fun_idem_on_sup])

lemma Sup_rec_safety_atms[code_unfold]:
  "\<Squnion> (Regex.atms r :: rec_safety set) = fold (\<squnion>) (csorted_list_of_set (Regex.atms r)) Unused"
  by (simp add: Sup_rec_safety_def csorted_list_of_set_def ccompare_rec_safety_def ID_def
      linorder.set_sorted_list_of_set[OF comparator.linorder] comparator_rec_safety
      flip: comp_fun_idem_on.fold_set_fold[OF comp_fun_idem_on_sup])

lift_definition MBuf2_t :: "'a queue \<Rightarrow> 'a mbuf_t" is "linearize" .

code_datatype MBuf2_t

lemma mbuf_t_empty_code[code]: "mbuf_t_empty = MBuf2_t empty_queue"
  by transfer' (auto simp: empty_queue_rep)

lemma mbuf_t_Cons_code[code]: "mbuf_t_Cons x (MBuf2_t xs) = MBuf2_t (prepend_queue x xs)"
  by transfer' (auto simp: prepend_queue_rep)

lemma mbuf_t_append_code[code]: "mbuf_t_append (MBuf2_t xs) ys = MBuf2_t (fold append_queue ys xs)"
  apply transfer'
  subgoal for xs ys
  proof (induction ys arbitrary: xs)
    case (Cons y ys)
    show ?case
      using Cons[of "append_queue y xs"]
      by (auto simp: append_queue_rep)
  qed simp
  done

lemma mbuf_t_cases_code[code]: "mbuf_t_cases (MBuf2_t xs) = (case safe_hd xs of (None, xs') \<Rightarrow> (None, MBuf2_t xs')
  | (Some x, xs') \<Rightarrow> (Some x, MBuf2_t (tl_queue xs')))"
  by transfer' (auto simp: tl_queue_rep[unfolded is_empty_alt, OF list.discI] split: list.splits prod.splits option.splits dest: safe_hd_rep)

(*<*)
end
(*>*)
