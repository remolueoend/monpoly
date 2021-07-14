(*<*)
theory Monitor_Impl
  imports Monitor
    Optimized_Agg_Temporal
    Optimized_Agg
    Optimized_MTL
    "HOL-Library.Code_Target_Nat"
    Containers.Containers
    "Generic_Join_Devel.Proj_Code"
begin
(*>*)

section \<open>Instantiation of the generic algorithm and code setup\<close>

lemma [code_unfold del, symmetric, code_post del]: "card \<equiv> Cardinality.card'" by simp
declare [[code drop: card]] Set_Impl.card_code[code]

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
  "result_vmsaux = (\<lambda>args (cur, auxlist). eval_args_agg args
    (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {}))"

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
    (let (res, auxlist') = eval_until (args_ivl args) nt auxlist in (map (eval_args_agg args) res, (t, auxlist'))))"

global_interpretation verimon_maux: maux valid_vmsaux init_vmsaux add_new_ts_vmsaux join_vmsaux
  add_new_table_vmsaux result_vmsaux valid_vmuaux init_vmuaux add_new_vmuaux length_vmuaux
  eval_vmuaux
  defines vminit0 = "maux.minit0 (init_vmsaux :: _ \<Rightarrow> event_data vmsaux) (init_vmuaux :: _ \<Rightarrow> event_data vmuaux) :: _ \<Rightarrow> Formula.formula \<Rightarrow> _"
  and vminit = "maux.minit (init_vmsaux :: _ \<Rightarrow> event_data vmsaux) (init_vmuaux :: _ \<Rightarrow> event_data vmuaux) :: Formula.formula \<Rightarrow> _"
  and vminit_since = "verimon_maux.init_since"
  and vminit_until = "verimon_maux.init_until"
  and vminit_safe = "maux.minit_safe (init_vmsaux :: _ \<Rightarrow> event_data vmsaux) (init_vmuaux :: _ \<Rightarrow> event_data vmuaux) :: Formula.formula \<Rightarrow> _"
  and vmupdate_since = "maux.update_since add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> event_data table)"
  and vmeval = "maux.meval add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _)"
  and vmstep = "maux.mstep add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _)"
  and vmsteps0_stateless = "maux.msteps0_stateless add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _)"
  and vmsteps_stateless = "maux.msteps_stateless add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _)"
  and vmonitor = "maux.monitor init_vmsaux add_new_ts_vmsaux join_vmsaux add_new_table_vmsaux (result_vmsaux :: _ \<Rightarrow> event_data vmsaux \<Rightarrow> _) init_vmuaux add_new_vmuaux (eval_vmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data vmuaux \<Rightarrow> _)"
  unfolding valid_vmsaux_def init_vmsaux_def add_new_ts_vmsaux_def join_vmsaux_def
    add_new_table_vmsaux_def result_vmsaux_def valid_vmuaux_def init_vmuaux_def add_new_vmuaux_def
    length_vmuaux_def eval_vmuaux_def
  by unfold_locales auto

global_interpretation default_maux: maux valid_mmasaux "init_mmasaux :: _ \<Rightarrow> mmasaux" add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux result_mmasaux
  valid_mmauaux "init_mmauaux :: _ \<Rightarrow> mmauaux" add_new_mmauaux length_mmauaux eval_mmauaux'
  defines minit0 = "maux.minit0 (init_mmasaux :: _ \<Rightarrow> mmasaux) (init_mmauaux :: _ \<Rightarrow> mmauaux) :: _ \<Rightarrow> Formula.formula \<Rightarrow> _"
  and minit = "maux.minit (init_mmasaux :: _ \<Rightarrow> mmasaux) (init_mmauaux :: _ \<Rightarrow> mmauaux) :: Formula.formula \<Rightarrow> _"
  and minit_since = "default_maux.init_since"
  and minit_until = "default_maux.init_until"
  and minit_safe = "maux.minit_safe (init_mmasaux :: _ \<Rightarrow> mmasaux) (init_mmauaux :: _ \<Rightarrow> mmauaux) :: Formula.formula \<Rightarrow> _"
  and mupdate_since = "maux.update_since add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux result_mmasaux"
  and meval = "maux.meval add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux result_mmasaux add_new_mmauaux eval_mmauaux'"
  and mstep = "maux.mstep add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux result_mmasaux add_new_mmauaux eval_mmauaux'"
  and msteps0_stateless = "maux.msteps0_stateless add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux result_mmasaux add_new_mmauaux eval_mmauaux'"
  and msteps_stateless = "maux.msteps_stateless add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux result_mmasaux add_new_mmauaux eval_mmauaux'"
  and monitor = "maux.monitor init_mmasaux add_new_ts_mmasaux gc_join_mmasaux add_new_table_mmasaux result_mmasaux init_mmauaux add_new_mmauaux eval_mmauaux'"
  by unfold_locales

lemma image_these: "f ` Option.these X = Option.these (map_option f ` X)"
  by (force simp: in_these_eq Bex_def image_iff map_option_case split: option.splits)

thm default_maux.meval.simps(2)

lemma meval_MPred: "meval n ts db (MPred e tms) =
  (case Mapping.lookup db e of None \<Rightarrow> replicate (length ts) {} | Some Xs \<Rightarrow> map (\<lambda>X. \<Union>v \<in> X.
  (set_option (map_option (\<lambda>f. Table.tabulate f 0 n) (match tms v)))) Xs, MPred e tms)"
  by (force split: option.splits simp: Option.these_def image_iff)

lemmas meval_code[code] = default_maux.meval.simps(1) meval_MPred default_maux.meval.simps(3-)

definition mk_db :: "(Formula.name \<times> event_data list set) list \<Rightarrow> _" where
  "mk_db t = Monitor.mk_db (\<Union>n \<in> set (map fst t). (\<lambda>v. (n, v)) ` the (map_of t n))"

definition rbt_fold :: "_ \<Rightarrow> event_data tuple set_rbt \<Rightarrow> _ \<Rightarrow> _" where
  "rbt_fold = RBT_Set2.fold"

definition rbt_empty :: "event_data list set_rbt" where
  "rbt_empty = RBT_Set2.empty"

definition rbt_insert :: "_ \<Rightarrow> _ \<Rightarrow> event_data list set_rbt" where
  "rbt_insert = RBT_Set2.insert"

lemma saturate_commute:
  assumes "\<And>s. r \<in> g s" "\<And>s. g (Set.insert r s) = g s" "\<And>s. r \<in> s \<Longrightarrow> h s = g s"
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
    by (subst while_option_commute_invariant[of "\<lambda>S. S = {} \<or> r \<in> S" "\<lambda>S. g S \<noteq> S" g "\<lambda>S. h S \<noteq> S" "Set.insert r" h "{}", symmetric])
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
  "Cardinality.eq_set X empty_table \<longleftrightarrow> Set.is_empty X"
  "Cardinality.eq_set empty_table X \<longleftrightarrow> Set.is_empty X"
  "set_eq X empty_table \<longleftrightarrow> Set.is_empty X"
  "set_eq empty_table X \<longleftrightarrow> Set.is_empty X"
  "X = (set_empty impl) \<longleftrightarrow> Set.is_empty X"
  "(set_empty impl) = X \<longleftrightarrow> Set.is_empty X"
  "Cardinality.eq_set X (set_empty impl) \<longleftrightarrow> Set.is_empty X"
  "Cardinality.eq_set (set_empty impl) X \<longleftrightarrow> Set.is_empty X"
  "set_eq X (set_empty impl) \<longleftrightarrow> Set.is_empty X"
  "set_eq (set_empty impl) X \<longleftrightarrow> Set.is_empty X"
  unfolding set_eq_def set_empty_def empty_table_def Set.is_empty_def Cardinality.eq_set_def by auto

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

lemma upd_set_insert[simp]: "upd_set m f (Set.insert x A) = Mapping.update x (f x) (upd_set m f A)"
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

definition "filter_set m X t = Mapping.filter (filter_cond X m t) m"

declare [[code drop: shift_end]]
declare shift_end.simps[folded filter_set_def, code]

lemma upd_set'_empty[simp]: "upd_set' m d f {} = m"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup)

lemma upd_set'_insert: "d = f d \<Longrightarrow> (\<And>x. f (f x) = f x) \<Longrightarrow> upd_set' m d f (Set.insert x A) =
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
  "d = f d \<Longrightarrow> (\<And>x. f (f x) = f x) \<Longrightarrow> upd_nested m d f (Set.insert x A) =
  upd_nested_step d f x (upd_nested m d f A)"
  unfolding upd_nested_step_def
  using upd_set'_aux1[of d f _ _ A] upd_set'_aux2[of _ _ d f _ A] upd_set'_aux3[of _ _ _ d f _ A]
    upd_set'_aux4[of _ A d f]
  by (auto simp add: Let_def upd_nested_lookup upd_set'_lookup Mapping.lookup_update'
      Mapping.lookup_empty split: option.splits prod.splits if_splits intro!: mapping_eqI)

definition upd_nested_max_tstp where
  "upd_nested_max_tstp m d X = upd_nested m d (max_tstp d) X"

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

lemma filter_set_empty[simp]: "filter_set m {} t = m"
  unfolding filter_set_def
  by transfer (auto simp: fun_eq_iff split: option.splits)

lemma filter_set_insert[simp]: "filter_set m (Set.insert x A) t = (let m' = filter_set m A t in
  case Mapping.lookup m' x of Some u \<Rightarrow> if t = u then Mapping.delete x m' else m' | _ \<Rightarrow> m')"
  unfolding filter_set_def
  by transfer (auto simp: fun_eq_iff Let_def Map_To_Mapping.map_apply_def split: option.splits)

lemma filter_set_fold:
  assumes "finite A"
  shows "filter_set m A t = Finite_Set.fold (\<lambda>a m.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Mapping.delete a m else m | _ \<Rightarrow> m) m A"
proof -
  interpret comp_fun_idem "\<lambda>a m.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Mapping.delete a m else m | _ \<Rightarrow> m"
    by unfold_locales
      (transfer; auto simp: fun_eq_iff Map_To_Mapping.map_apply_def split: option.splits)+
  from assms show ?thesis
    by (induct A arbitrary: m rule: finite.induct) (auto simp: Let_def)
qed

lift_definition filter_cfi :: "'b \<Rightarrow> ('a, ('a, 'b) mapping) comp_fun_idem"
  is "\<lambda>t a m.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Mapping.delete a m else m | _ \<Rightarrow> m"
  by unfold_locales
    (transfer; auto simp: fun_eq_iff Map_To_Mapping.map_apply_def split: option.splits)+

lemma filter_set_code[code]:
  "filter_set m A t = (if finite A then set_fold_cfi (filter_cfi t) m A else Code.abort (STR ''upd_set: infinite'') (\<lambda>_. filter_set m A t))"
  by (transfer fixing: m) (auto simp: filter_set_fold)

lemma filter_Mapping[code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt" shows
  "Mapping.filter P (RBT_Mapping t) = 
  (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''filter RBT_Mapping: ccompare = None'') (\<lambda>_. Mapping.filter P (RBT_Mapping t))
                     | Some _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.filter (case_prod P) t))"
  by (auto simp add: Mapping.filter.abs_eq Mapping_inject split: option.split)

definition "filter_join pos X m = Mapping.filter (join_filter_cond pos X) m"

declare [[code drop: join_mmsaux]]
declare join_mmsaux.simps[folded filter_join_def, code]

lemma filter_join_False_empty: "filter_join False {} m = m"
  unfolding filter_join_def
  by transfer (auto split: option.splits)

lemma filter_join_False_insert: "filter_join False (Set.insert a A) m =
  filter_join False A (Mapping.delete a m)"
proof -
  {
    fix x
    have "Mapping.lookup (filter_join False (Set.insert a A) m) x =
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
    (if \<not>pos \<and> finite A \<and> card A < Mapping.size m then set_fold_cfi filter_not_in_cfi m A
    else Mapping.filter (join_filter_cond pos A) m)"
  unfolding filter_join_def
  by (transfer fixing: m) (use filter_join_False in \<open>auto simp add: filter_join_def\<close>)

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

lift_definition clearjunk :: "(string8 \<times> event_data list set) list \<Rightarrow> (string8, event_data list set list) alist" is
  "\<lambda>t. List.map_filter (\<lambda>(p, X). if X = {} then None else Some (p, [X])) (AList.clearjunk t)"
  unfolding map_filter_def o_def list.map_comp
  by (subst map_cong[OF refl, of _ _ fst]) (auto simp: map_filter_def distinct_map_fst_filter split: if_splits)

lemma map_filter_snd_map_filter: "List.map_filter (\<lambda>(a, b). if P b then None else Some (f a b)) xs =
    map (\<lambda>(a, b). f a b) (filter (\<lambda>x. \<not> P (snd x)) xs)"
  by (simp add: map_filter_def prod.case_eq_if)

lemma mk_db_code_alist:
  "mk_db t = Assoc_List_Mapping (clearjunk t)"
  unfolding mk_db_def Assoc_List_Mapping_def
  by (transfer' fixing: t)
    (auto simp: map_filter_snd_map_filter fun_eq_iff map_of_map image_iff map_of_clearjunk
      map_of_filter_apply dest: weak_map_of_SomeI intro!: bexI[rotated, OF map_of_SomeD]
      split: if_splits option.splits)

lemma mk_db_code[code]:
  "mk_db t = Mapping.of_alist (List.map_filter (\<lambda>(p, X). if X = {} then None else Some (p, [X])) (AList.clearjunk t))"
  unfolding mk_db_def
  by (transfer' fixing: t) (auto simp: map_filter_snd_map_filter fun_eq_iff map_of_map image_iff
      map_of_clearjunk map_of_filter_apply dest: weak_map_of_SomeI intro!: bexI[rotated, OF map_of_SomeD]
      split: if_splits option.splits)

declare [[code drop: New_max_getIJ_genericJoin New_max_getIJ_wrapperGenericJoin]]
declare New_max.genericJoin_code[folded remove_Union_def, code]
declare New_max.wrapperGenericJoin.simps[folded remove_Union_def, code]

lift_definition delete_cnt_cfc::"aggargs \<Rightarrow> (event_data tuple, (bool \<times> nat agg_map)) comp_fun_commute" is
  "\<lambda>args. delete_cnt args" using delete_cnt_comm by unfold_locales auto

lemma [code_unfold]: "Finite_Set.fold (delete_cnt args) (v, m) data = set_fold_cfc (delete_cnt_cfc args) (v, m) data"
  by(transfer) auto

lift_definition delete_sum_cfc::"aggargs \<Rightarrow> (event_data tuple, (bool \<times> ((nat \<times> integer) agg_map))) comp_fun_commute" is
  "\<lambda>args. delete_sum args" using delete_sum_comm by unfold_locales auto

lemma [code_unfold]: "Finite_Set.fold (delete_sum args) (v, m) data = set_fold_cfc (delete_sum_cfc args) (v, m) data"
  by(transfer) auto

lift_definition delete_rank_cfc::"aggargs \<Rightarrow> type \<Rightarrow> (event_data tuple, bool \<times> list_aux agg_map) comp_fun_commute" is
  "\<lambda>args. delete_rank args" using delete_rank_comm by unfold_locales auto

lemma [code_unfold]: "Finite_Set.fold (delete_rank args type) (v, m) data = set_fold_cfc (delete_rank_cfc args type) (v, m) data"
  by(transfer) auto

lift_definition insert_cnt_cfc::"aggargs \<Rightarrow> (event_data tuple, (bool \<times> nat agg_map)) comp_fun_commute" is
  "\<lambda>args. insert_cnt args" using insert_cnt_comm by unfold_locales auto

lemma [code_unfold]: "Finite_Set.fold (insert_cnt args) (v, m) data = set_fold_cfc (insert_cnt_cfc args) (v, m) data"
  by(transfer) auto

lift_definition insert_sum_cfc::"aggargs \<Rightarrow> (event_data tuple, (bool \<times> ((nat \<times> integer) agg_map))) comp_fun_commute" is
  "\<lambda>args. insert_sum args" using insert_sum_comm by unfold_locales auto

lemma [code_unfold]: "Finite_Set.fold (insert_sum args) (v, m) data = set_fold_cfc (insert_sum_cfc args) (v, m) data"
  by(transfer) auto

lift_definition insert_rank_cfc::"aggargs \<Rightarrow> type \<Rightarrow> (event_data tuple, bool \<times> list_aux agg_map) comp_fun_commute" is
  "\<lambda>args. insert_rank args" using insert_rank_comm by unfold_locales auto

lemma [code_unfold]: "Finite_Set.fold (insert_rank args type) (v, m) data = set_fold_cfc (insert_rank_cfc args type) (v, m) data"
  by(transfer) auto

definition finite' :: "'a set \<Rightarrow> bool" where
  "finite' = finite"

declare insert_maggaux'.simps [code del]
declare insert_maggaux'.simps [folded finite'_def, code]


lemma [code_unfold]: "X - Mapping.keys tuple_in = Set.filter (\<lambda>k. Mapping.lookup tuple_in k = None) X"
  by(transfer) (auto simp: Map_To_Mapping.map_apply_def) 

definition "filter_join' pos X m = (Mapping.filter (join_filter_cond pos X) m, Mapping.keys m - Mapping.keys (Mapping.filter (join_filter_cond pos X) m))"

declare [[code drop: join_mmasaux]]
declare join_mmasaux.simps[folded filter_join'_def filter_join_def, code]

lemma filter_join'_False_empty: "filter_join' False {} m = (m, {})"
  unfolding filter_join'_def
  by transfer (auto split: option.splits)

lemma filter_join'_False_insert: 
  "filter_join' False (Set.insert a A) m = (case filter_join' False A m of
   (m', X) \<Rightarrow> (Mapping.delete a m', case Mapping.lookup m' a of Some _ \<Rightarrow> Set.insert a X |
                                    _ \<Rightarrow> X))"
  unfolding filter_join'_def
  by(transfer) (auto simp: Map_To_Mapping.map_apply_def split: option.splits if_splits)

fun filter_join'_fold_fun where
  "filter_join'_fold_fun x (m, X) = (Mapping.delete x m, case Mapping.lookup m x of Some _ \<Rightarrow> Set.insert x X |
                                                                                      None \<Rightarrow> X)"

lemma filter_join'_False:
  assumes "finite A"
  shows "filter_join' False A m = 
         Finite_Set.fold filter_join'_fold_fun (m, {}) A"
proof -
  interpret comp_fun_idem "filter_join'_fold_fun"
    by(unfold_locales; simp add:fun_eq_iff; transfer) (auto simp: Map_To_Mapping.map_apply_def split:option.splits if_splits)
  from assms show ?thesis
  proof (induction A arbitrary: m)
    case empty
    then show ?case using filter_join'_False_empty by auto
  next
    case (insert a A)
    then show ?case using filter_join'_False_insert[of a A m]
      by(simp only:fold_insert[OF insert(1-2)] split:option.splits prod.splits; simp)
   qed 
qed

lift_definition filter_not_in_cfi' :: "('a, ('a, 'b) mapping \<times> 'a set) comp_fun_idem" is 
  "filter_join'_fold_fun"
  by(unfold_locales; simp add:fun_eq_iff; transfer) (auto simp: Map_To_Mapping.map_apply_def split:option.splits if_splits)

lemma filter_join'_code[code]:
  "filter_join' pos A m =
    (if \<not>pos \<and> finite A \<and> card A < Mapping.size m then set_fold_cfi filter_not_in_cfi' (m, {}) A
    else (Mapping.filter (join_filter_cond pos A) m, Mapping.keys m - Mapping.keys (Mapping.filter (join_filter_cond pos A) m)))"
  unfolding filter_join'_def
  by (transfer fixing: m) (use filter_join'_False in \<open>auto simp add: filter_join'_def\<close>)

definition "filter_set' m X t = (Mapping.filter (filter_cond X m t) m, Mapping.keys m - Mapping.keys (Mapping.filter (filter_cond X m t) m))"

declare [[code drop: shift_end_mmasaux]]
declare shift_end_mmasaux.simps[folded filter_set'_def, code]

lemma filter_set'_empty: "filter_set' m {} t = (m, {})"
  unfolding filter_set'_def
  by transfer (auto simp: fun_eq_iff split: option.splits)

lemma filter_set'_insert: "filter_set' m (Set.insert x A) t = (let (m', X) = filter_set' m A t in
  case Mapping.lookup m' x of Some u \<Rightarrow> if t = u then (Mapping.delete x m', Set.insert x X) else (m', X) | _ \<Rightarrow> (m', X))"
  unfolding filter_set'_def
  by transfer (auto simp: Map_To_Mapping.map_apply_def split: option.splits if_splits)

fun filter_set'_fold_fun where
  "filter_set'_fold_fun t a (m, X) = (case Mapping.lookup m a of 
                                    Some u \<Rightarrow> if t = u then (Mapping.delete a m, Set.insert a X) else (m, X) | 
                                    _ \<Rightarrow> (m, X))"

lemma filter_set'_fold:
  assumes "finite A"
  shows "filter_set' m A t = Finite_Set.fold (filter_set'_fold_fun t) (m, {}) A"
proof -
  interpret comp_fun_idem "filter_set'_fold_fun t"
    by(unfold_locales; simp add:fun_eq_iff split:option.splits; transfer) (auto simp: Map_To_Mapping.map_apply_def)
  from assms show ?thesis
  proof (induction A arbitrary: m)
    case empty
    then show ?case using filter_set'_empty by auto
  next
    case (insert a A)
    then show ?case using filter_set'_insert[of m a A t]
      by(simp only:fold_insert[OF insert(1-2)] Let_def split:option.splits prod.splits; simp)
   qed 
qed

lift_definition filter'_cfi :: "'b \<Rightarrow> ('a, ('a, 'b) mapping \<times> 'a set) comp_fun_idem" is 
  "\<lambda>t. filter_set'_fold_fun t"
  by(unfold_locales; simp add:fun_eq_iff split:option.splits; transfer) (auto simp: Map_To_Mapping.map_apply_def split:option.splits if_splits)

lemma filter_set'_code[code]:
  "filter_set' m A t = (if finite A then set_fold_cfi (filter'_cfi t) (m, {}) A else Code.abort (STR ''upd_set: infinite'') (\<lambda>_. filter_set' m A t))"
  by (transfer fixing: m) (auto simp: filter_set'_fold)

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

instantiation treelist :: (equal) equal begin
lift_definition equal_treelist :: "'a treelist \<Rightarrow> 'a treelist \<Rightarrow> bool" is "(=)" .
instance by (standard; transfer; auto)
end

instantiation wf_wbt :: (linorder) equal begin
lift_definition equal_wf_wbt :: "'a wf_wbt \<Rightarrow> 'a wf_wbt \<Rightarrow> bool" is "(=)" .
instance by(standard; transfer; auto)
end

lemma eq_treelist_code[code]: "equal_class.equal (Collapse y1) (Collapse y2) = (if y2 = empty_tree then (y1 = empty_tree) else (tree_inorder y1 = tree_inorder y2))"
  apply(transfer) using Tree2.inorder.elims by auto

definition to_add_set where
  "to_add_set a m tmp = {b. (a, b) \<in> tmp \<and> Mapping.lookup m b = None}"

definition to_add_set_fun :: "'b \<Rightarrow> ('a, 'c) mapping \<Rightarrow> 'b \<times> 'a \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "to_add_set_fun a m elem s = (if a = fst elem \<and> Mapping.lookup m (snd elem) = None then Set.insert (snd elem) s else s)"

lemma to_add_set_empty: "to_add_set a m {} = {}"
  unfolding to_add_set_def by auto

lemma to_add_set_insert: "to_add_set a m (Set.insert x X) = to_add_set_fun a m x (to_add_set a m X) "
  unfolding to_add_set_def to_add_set_fun_def
  by transfer (auto simp: Map_To_Mapping.map_apply_def)

lemma to_add_set_fold:
  assumes "finite tmp"
  shows "to_add_set a m tmp = Finite_Set.fold (to_add_set_fun a m) {} tmp"
proof -
  interpret comp_fun_idem "to_add_set_fun a m"
    by(unfold_locales) (auto simp:to_add_set_fun_def comp_def split:if_splits)
  from assms show ?thesis
  proof (induction tmp)
    case empty
    then show ?case using to_add_set_empty[of a m] by simp
  next
    case (insert a A)
    show ?case unfolding fold_insert[OF insert(1-2)] insert(3)[symmetric] unfolding to_add_set_def to_add_set_fun_def
      by transfer auto
   qed 
 qed

lift_definition to_add_set_cfi :: "'b \<Rightarrow> ('a, 'c) mapping \<Rightarrow> (('b \<times> 'a), 'a set) comp_fun_idem" is 
  "\<lambda>a m. to_add_set_fun a m" by(unfold_locales) (auto simp:to_add_set_fun_def comp_def split:if_splits)

lemma [code]: "to_add_set a m tmp = (if finite tmp then set_fold_cfi (to_add_set_cfi a m) {} tmp else Code.abort (STR ''to_add_set: infinite set'') (\<lambda>_. to_add_set a m tmp))"
  using to_add_set_fold[of tmp a m] by transfer auto

lemma [code]: 
  "add_new_mmuaux args rel1 rel2 nt aux =
    (let (tp, tss, tables, len, maskL, maskR, a1_map, a2_map, tstp_map, done, done_length) =
    shift_mmuaux args nt aux;
    I = args_ivl args; pos = args_pos args;
    new_tstp = (if memL I 0 then Inr tp else Inl nt);
    tstp_map = Mapping.update tp nt tstp_map;
    tmp = \<Union>((\<lambda>as. case Mapping.lookup a1_map (proj_tuple maskL as) of None \<Rightarrow>
      (if \<not>pos then {(tp - len, as)} else {})
      | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
      else {(max (tp - len) (tp' + 1), as)}) ` rel2) \<union> (if memL I 0 then {tp} \<times> rel2 else {});
    tmp = Set.filter (\<lambda>(tp, as). case Mapping.lookup tstp_map tp of Some ts \<Rightarrow> memL I (nt - ts)) tmp;
    table = snd ` tmp;
    tables = append_queue (table, if memL I 0 then Inr tp else Inl nt) tables;
    a2_map = Mapping.update (tp + 1) Mapping.empty
      (upd_nested_max_tstp a2_map new_tstp tmp);
    a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
      (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
    tss = append_queue nt tss in
    (tp + 1, tss, tables, len + 1, maskL, maskR, a1_map, a2_map, tstp_map, done, done_length))" 
  by(auto simp: upd_nested_max_tstp_def split:option.splits prod.splits)

lemma [code]:
  "add_new_mmauaux args rel1 rel2 nt (mmuaux, aggaux) =
    (case args_agg args of 
     None \<Rightarrow> let (tp, tss, tables, len, maskL, maskR, a1_map, a2_map, tstp_map, done, done_length) = add_new_mmuaux args rel1 rel2 nt mmuaux in
  ((tp, tss, tables, len, maskL, maskR, a1_map, a2_map, tstp_map, done, done_length), aggaux) |
     Some aggargs \<Rightarrow>
    (let ((tp, tss, tables, len, maskL, maskR, a1_map, a2_map, tstp_map, done, done_length), aggaux) = shift_mmauaux args nt (mmuaux, aggaux);
    I = args_ivl args; pos = args_pos args;
    new_tstp = (if memL I 0 then Inr tp else Inl nt);
    tstp_map = Mapping.update tp nt tstp_map;
    m = case Mapping.lookup a2_map (tp - len) of Some m \<Rightarrow> m;
    tmp = \<Union>((\<lambda>as. case Mapping.lookup a1_map (proj_tuple maskL as) of None \<Rightarrow>
      (if \<not>pos then {(tp - len, as)} else {})
      | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
      else {(max (tp - len) (tp' + 1), as)}) ` rel2) \<union> (if memL I 0 then {tp} \<times> rel2 else {});
    tmp = Set.filter (\<lambda>(tp, as). case Mapping.lookup tstp_map tp of Some ts \<Rightarrow> memL I (nt - ts)) tmp;
    table = snd ` tmp;
    tables = append_queue (table, if memL I 0 then Inr tp else Inl nt) tables;
    a2_map' = Mapping.update (tp + 1) Mapping.empty
      (upd_nested_max_tstp a2_map new_tstp tmp);
    a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
      (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
    to_add = to_add_set (tp - len) m tmp;
    aggaux = insert_maggaux' aggargs to_add aggaux;
    tss = append_queue nt tss in
    ((tp + 1, tss, tables, len + 1, maskL, maskR, a1_map, a2_map', tstp_map, done, done_length), aggaux)))"
  by(auto simp del: add_new_mmuaux.simps simp add: to_add_set_def  upd_nested_max_tstp_def split:option.splits prod.splits)

(*<*)
end
(*>*)
