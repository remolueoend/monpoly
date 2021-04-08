theory Optimized_Agg
  imports Monitor
begin

type_synonym 'a agg_map = "(event_data tuple, 'a) mapping"

datatype aggaux' = CntAux nat

datatype aggaux = CntAux "nat agg_map" | SumAux "(nat \<times> event_data) agg_map" | MinAux "event_data table"
  | MaxAux "event_data table" | MedAux "event_data table"

definition group_multiset where
  "group_multiset k b f X = (let group = Set.filter (\<lambda>x. drop b x = k) X in
                      (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group)"

definition valid_aggmap :: "(event_data list \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> Formula.trm \<Rightarrow> (event_data option list, 'a) mapping \<Rightarrow> event_data option list set \<Rightarrow> bool" where
  "valid_aggmap g b f m X \<longleftrightarrow> (\<forall>k. k \<in> (drop b) ` X \<longleftrightarrow> k \<in> Mapping.keys m) \<and>
                    (\<forall>k. k \<in> Mapping.keys m \<longrightarrow> Mapping.lookup m k = 
                    (let M = group_multiset k b f X
                    in Some (g (flatten_multiset M))))"

fun valid_maggaux :: "aggargs \<Rightarrow> aggaux \<Rightarrow> event_data table \<Rightarrow> bool" where
  "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> aux X = 
  (finite X \<and>
  (let aggtype = fst \<omega> in case aux of 
      CntAux m \<Rightarrow>
        (aggtype = Formula.Agg_Cnt) \<and> 
        (valid_aggmap (\<lambda>k. length k) b f m X)
    | SumAux m \<Rightarrow> (aggtype = Formula.Agg_Sum \<or> aggtype = Formula.Agg_Avg) \<and> 
                  (let y0 = (if aggtype = Formula.Agg_Sum then snd \<omega> else EInt 0) in
                  (valid_aggmap (\<lambda>k. (length k, foldl plus y0 k)) b f m X))
    | MinAux t \<Rightarrow> (aggtype = Formula.Agg_Min) \<and> t = X
    | MaxAux t \<Rightarrow> (aggtype = Formula.Agg_Max) \<and> t = X
    | MedAux t \<Rightarrow> (aggtype = Formula.Agg_Med) \<and> t = X))"

fun init_maggaux :: "aggargs \<Rightarrow> aggaux" where
  "init_maggaux args =
  (let aggtype = fst (aggargs_\<omega> args) in case aggtype of
      Formula.Agg_Cnt \<Rightarrow> CntAux Mapping.empty
    | Formula.Agg_Sum \<Rightarrow> SumAux Mapping.empty
    | Formula.Agg_Min \<Rightarrow> MinAux {}
    | Formula.Agg_Max \<Rightarrow> MaxAux {}
    | Formula.Agg_Avg \<Rightarrow> SumAux Mapping.empty
    | Formula.Agg_Med \<Rightarrow> MedAux {})"

fun insert_cnt :: "aggargs \<Rightarrow> nat agg_map \<Rightarrow> event_data tuple \<Rightarrow> nat agg_map" where
  "insert_cnt args m t = (let group = drop (aggargs_b args) t 
                       in case (Mapping.lookup m group) of
                        Some i \<Rightarrow> Mapping.update group (i + 1) m
                      | None \<Rightarrow> Mapping.update group 1 m)"

fun insert_sum :: "aggargs \<Rightarrow> event_data \<Rightarrow> (nat \<times> event_data) agg_map \<Rightarrow> event_data tuple \<Rightarrow> (nat \<times> event_data) agg_map" where
  "insert_sum args y0 m t = (let group = drop (aggargs_b args) t;
                                         term = meval_trm (aggargs_f args) t
                                     in case (Mapping.lookup m group) of
                        Some (cnt, agg_sum) \<Rightarrow> Mapping.update group (cnt + 1, agg_sum + term) m
                      | None \<Rightarrow> Mapping.update group (1, y0 + term) m)"

fun insert_maggaux :: "aggargs \<Rightarrow> event_data table \<Rightarrow> aggaux \<Rightarrow> aggaux" where
  "insert_maggaux args data aux = (case aux of
    CntAux m \<Rightarrow> CntAux (foldl (insert_cnt args) m (csorted_list_of_set data))
  | SumAux m \<Rightarrow> let y0 = snd (aggargs_\<omega> args) in SumAux (foldl (insert_sum args y0) m (csorted_list_of_set data))
  | MinAux t \<Rightarrow> MinAux (t \<union> data)
  | MaxAux t \<Rightarrow> MaxAux (t \<union> data)
  | MedAux t \<Rightarrow> MedAux (t \<union> data))"

fun delete_cnt :: "nat \<Rightarrow> nat agg_map \<Rightarrow> event_data tuple \<Rightarrow> nat agg_map" where
  "delete_cnt b m t = (let group = drop b t
                       in case (Mapping.lookup m group) of
                         Some i \<Rightarrow> (if i = 1 then Mapping.delete group m 
                                    else Mapping.update group (i - 1) m)
                       | None \<Rightarrow> m)"

fun delete_sum :: "aggargs \<Rightarrow> (nat \<times> event_data) agg_map \<Rightarrow> event_data tuple \<Rightarrow> (nat \<times> event_data) agg_map" where
  "delete_sum args m t = (let group = drop (aggargs_b args) t;
                              term = meval_trm (aggargs_f args) t
                          in case (Mapping.lookup m group) of
                            Some (cnt, agg_sum) \<Rightarrow> (if cnt = 1 then Mapping.delete group m
                                                    else Mapping.update group (cnt - 1, agg_sum - term) m)
                          | None \<Rightarrow> m)"

fun delete_maggaux :: "aggargs \<Rightarrow> event_data table \<Rightarrow> aggaux \<Rightarrow> aggaux" where
  "delete_maggaux args data aux = (case aux of
    CntAux m \<Rightarrow> CntAux (foldl (delete_cnt (aggargs_b args)) m (csorted_list_of_set data))
  | SumAux m \<Rightarrow> SumAux (foldl (delete_sum args) m (csorted_list_of_set data))
  | MinAux t \<Rightarrow> MinAux (t - data)
  | MaxAux t \<Rightarrow> MaxAux (t - data)
  | MedAux t \<Rightarrow> MedAux (t - data))"

fun result_maggaux :: "aggargs \<Rightarrow> aggaux \<Rightarrow> event_data table" where
  "result_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> aux = (case aux of
    CntAux m \<Rightarrow> (if g0 \<and> Mapping.keys m = {} 
                then singleton_table n y (eval_agg_op \<omega> {})
                else (\<lambda>k. (case Mapping.lookup m k of
                             Some i \<Rightarrow> k[y:=Some (EInt (integer_of_int i))]
                           | None \<Rightarrow> k))` Mapping.keys m)
  | SumAux m \<Rightarrow> (if g0 \<and> Mapping.keys m = {}
                      then singleton_table n y (eval_agg_op \<omega> {})
                      else if fst \<omega> = Formula.Agg_Sum
                      then (\<lambda>k. (case Mapping.lookup m k of 
                                   Some (_, agg_sum) \<Rightarrow> k[y:=Some agg_sum]
                                 | None \<Rightarrow> k)) ` Mapping.keys m
                      else (\<lambda>k. (case Mapping.lookup m k of
                                   Some (cnt, agg_sum) \<Rightarrow> k[y:=Some (EFloat ((double_of_event_data agg_sum) / (double_of_int cnt)))] 
                                 | None \<Rightarrow> k)) ` Mapping.keys m)
  | MinAux t \<Rightarrow> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> t
  | MaxAux t \<Rightarrow> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> t
  | MedAux t \<Rightarrow> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> t)"

lemma valid_init_maggaux_unfolded: "safe_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> \<Longrightarrow> valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (init_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr>) {}"
  by (cases "fst \<omega>") (auto simp add:valid_aggmap_def)

lemma valid_init_maggaux: "safe_aggargs args \<Longrightarrow> valid_maggaux args (init_maggaux args) {}"
  using valid_init_maggaux_unfolded by (cases args) fast

primrec iter_f :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
  where
    "iter_f f 0 t y0 = y0"
  | "iter_f f (Suc n) t y0 = f t (iter_f f n t y0)"

lemma iter_f_comm: 
  assumes commute_f: "comp_fun_commute f"
  shows "iter_f f n1 t1 (iter_f f n2 t2 y0) = iter_f f n2 t2 (iter_f f n1 t1 y0)"
proof(induction n1)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case sorry
qed


lemma fold_flatten_multiset: 
  assumes finite_m: "finite M"
  assumes commute_f: "comp_fun_commute f"
  shows "fold f (flatten_multiset M) y0  = Finite_Set.fold (\<lambda> (t, m) y. iter_f f (the_enat m) t y) y0 M"
proof -
  interpret comp_fun_commute "\<lambda> (t, m) y. iter_f f (the_enat m) t y"
    using iter_f_comm[of f] commute_f
    by unfold_locales auto
  obtain c where c_def: "ID ccompare = Some (c :: (event_data \<times> enat) comparator)" 
    by (simp add: ID_def ccompare_prod_def ccompare_event_data_def ccompare_enat_def split:if_splits option.splits)
  note c = ID_ccompare'[OF c_def] 
  note c_class = comparator.linorder[OF c]
  show ?thesis
    using finite_m
  proof(induction M)
    case empty
    then show ?case
      using linorder.sorted_list_of_set_empty[OF c_class]
      by (auto simp add:flatten_multiset_def csorted_list_of_set_def c_def)
  next
    case (insert x F)
    obtain t m where "x = (t, m)"
      by (cases x) auto
    then show ?case
      using insert(1-2) insert(3)[symmetric] linorder.sorted_list_of_set_insert[OF c_class]
      apply(simp add:flatten_multiset_def csorted_list_of_set_def c_def) sorry
  qed
qed

lemma length_fold: "length xs = fold (\<lambda> _ n. n + 1) xs 0"
  by (induction xs) (auto simp:fold_commute_apply)

lemma iter_f_len: "iter_f (\<lambda> _. Suc) m t y = y + m"
  by (induction m) auto

lemma length_flatten_multiset: 
  assumes "finite M"
  shows "length (flatten_multiset M) = Finite_Set.fold (\<lambda> (t, m) y. y + (the_enat m)) 0 M"
  using length_fold[of "flatten_multiset M"] by (simp add: fold_flatten_multiset assms comp_fun_commute.intro iter_f_len)

lemma valid_insert_cnt_unfolded: 
  assumes valid_before: "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (CntAux m) X" 
  and correct_type: "type_restr \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> {elem}"
  and disjoint: "elem \<notin> X"
shows "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> 
        (CntAux (insert_cnt \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> m elem)) (X \<union> {elem})"
proof - 
  define updated_map where "updated_map = insert_cnt \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> m elem"
  define updated_data where "updated_data = X \<union> {elem}"
  interpret comp_fun_commute "\<lambda>(t, m) y. y + the_enat m" 
    by(unfold_locales) auto
  have valid_finite: "finite updated_data" using valid_before by (auto simp:updated_data_def)
  have valid_key_invariant: "\<And>k. k \<in> (drop b) ` updated_data \<longleftrightarrow> k \<in> Mapping.keys updated_map"
  proof (rule iffI)
    fix k
    assume assm: "k \<in> (drop b) ` updated_data"
    show "k \<in>  Mapping.keys updated_map"
      using valid_before assm
      unfolding updated_map_def updated_data_def
      by (cases "k \<in> (drop b) ` X") (auto simp: valid_aggmap_def Let_def split:option.splits)
  next
    fix k
    assume assm: "k \<in> Mapping.keys updated_map"
    show "k \<in> (drop b) ` updated_data"
      using valid_before assm
      unfolding updated_map_def updated_data_def
      by (cases "k \<in> Mapping.keys m") (auto simp: valid_aggmap_def Let_def split:option.splits)
  qed
  have valid_value_invariant: "\<And>k. k \<in> Mapping.keys updated_map \<longrightarrow> Mapping.lookup updated_map k = 
          (let group = Set.filter (\<lambda>x. drop b x = k) updated_data;
           M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group
          in Some (length (flatten_multiset M)))"
  proof rule
    fix k
    define group where "group = Set.filter (\<lambda>x. drop b x = k) updated_data"
    define M where "M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group"
    define old_group where "old_group = Set.filter (\<lambda>x. drop b x = k) X"
    define old_M where "old_M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) old_group))) ` meval_trm f ` old_group"
    assume assm: "k \<in> Mapping.keys updated_map"
    show "Mapping.lookup updated_map k = 
          (let group = Set.filter (\<lambda>x. drop b x = k) updated_data;
           M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group
          in Some (length (flatten_multiset M)))"
    proof (cases "k \<in> Mapping.keys m")
      case False
      then have map_val: "Mapping.lookup updated_map k = Some 1" 
        using assm by (auto simp: updated_map_def keys_is_none_rep Let_def lookup_update' split:option.splits)
      have "drop b elem = k" 
        using assm False 
        by(auto simp: updated_map_def Let_def split:option.splits)
      then have group_single_elem: "group = {elem}" 
        using False valid_before image_iff
        by(fastforce simp: group_def updated_data_def valid_aggmap_def)
      then have "M = insert (meval_trm f elem, enat 1) {}"
        using group_single_elem unfolding M_def Set.filter_def ecard_def by (auto cong: conj_cong)
      then have "length(flatten_multiset M) = 1" 
        using length_flatten_multiset[of M] Finite_Set.comp_fun_commute.fold_insert by(auto)
      then show ?thesis using map_val by (simp add: M_def local.group_def)
    next
      case True
      then show ?thesis sorry
        
    qed
  qed
  show ?thesis using valid_value_invariant valid_key_invariant valid_finite valid_before
    by (auto simp add:updated_data_def valid_aggmap_def updated_map_def group_multiset_def Let_def)
qed

lemma valid_aggmap_empty_data: "valid_aggmap g b f m X \<Longrightarrow> X = {} \<longleftrightarrow> Mapping.keys m = {}"
  by (auto simp:valid_aggmap_def)

lemma flatten_multiset_not_empty: 
  assumes valid_map: "valid_aggmap g b f m X"
  and finite: "finite X"
  and in_map: "k \<in> Mapping.keys m"
  shows "flatten_multiset (group_multiset k b f X) \<noteq> []"
proof -
  define M where "M = group_multiset k b f X"
  obtain c where c_def: "ID ccompare = Some (c :: (event_data \<times> enat) comparator)" 
    by (simp add: ID_def ccompare_prod_def ccompare_event_data_def ccompare_enat_def split:if_splits option.splits)
  note c = ID_ccompare'[OF c_def] 
  note c_class = comparator.linorder[OF c]
  define M_list where "M_list = linorder.sorted_list_of_set (le_of_comp c) M"
  obtain elem where elem_prop: "elem \<in> X \<and> drop b elem = k" using in_map valid_map imageE[of k "drop b" X] by (auto simp: valid_aggmap_def)
  then obtain m where m_prop: "(meval_trm f elem, m) \<in> M" 
    by (auto simp: group_multiset_def Let_def valid_aggmap_def M_def) fastforce
  define group where "group = Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) (Set.filter (\<lambda>x. drop b x = k) X)"
  then have "elem \<in> group" using elem_prop by (auto simp: group_def)
  moreover have finite_g: "finite group" using finite by (auto simp: group_def)
  ultimately have "ecard group \<noteq> 0" by (auto simp:ecard_def zero_enat_def)
  then have m_pos: "m > 0 \<and> m \<noteq> \<infinity>" 
    using elem_prop m_prop finite_g  by (auto simp: M_def group_multiset_def Let_def group_def ecard_def)
  then have "the_enat m > 0"
    apply(auto simp: the_enat_def)
    using enat_0_iff(1) by blast
  then obtain n where n_def: "the_enat m = Suc n" using gr0_implies_Suc by auto
  have finite_m: "finite M" using finite by (auto simp: M_def group_multiset_def Let_def)
  then have "(meval_trm f elem, m) \<in> set (linorder.sorted_list_of_set (le_of_comp c) M)"
    using m_prop linorder.set_sorted_list_of_set[OF c_class] by auto
  then show ?thesis 
    using finite_m n_def by (simp add:flatten_multiset_def csorted_list_of_set_def c_def M_def) force
qed
  
lemma valid_result_maggaux_unfolded: "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> aux X
                                  \<Longrightarrow> result_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> aux
                                    = eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> X"
proof(induction aux)
  case(SumAux m)
  then show ?case
  proof (cases "g0 \<and> X = {}")
    case True
    then show ?thesis unfolding eval_aggargs_def eval_agg_def using SumAux
      by (auto simp add: valid_aggmap_def)
  next
    case False
    then have assm_map: "\<not>(g0 \<and> Mapping.keys m = {})" using valid_aggmap_empty_data[of _ b f m X] SumAux by force
    have assm_reg: "\<not>(g0 \<and> X = {})" using False by auto
    show ?thesis
    proof (cases "fst \<omega> = Formula.Agg_Sum")
      case True
      show ?thesis
      proof (rule set_eqI, rule iffI)
      fix result
      assume "result \<in> result_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (SumAux m)"
      then obtain k where k_assm: "k \<in> Mapping.keys m \<and> result = (case Mapping.lookup m k of 
                                                      Some (_, agg_sum) \<Rightarrow> k[y:=Some agg_sum]
                                                    | None \<Rightarrow> k)" using assm_map True by auto
      define group where "group = Set.filter (\<lambda>x. drop b x = k) X"
      define M where "M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group"
      have "Mapping.lookup m k = Some (length (flatten_multiset M), foldl plus (snd \<omega>) (flatten_multiset M))" 
        using SumAux k_assm True by (simp add: M_def group_def Let_def lookup_default_def valid_aggmap_def group_multiset_def)
      then have "result = k[y:= Some (eval_agg_op \<omega> M)]" 
        using k_assm True by auto (metis eval_agg_op.simps(4) prod.collapse)
      then show "result \<in> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> X"
        using k_assm SumAux by (auto simp add: M_def group_def Let_def eval_agg_def eval_aggargs_def valid_aggmap_def)
    next
      fix result
      assume "result \<in> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> X"
      then obtain k where k_assm: "(k \<in> (drop b) ` X \<and> result = (let group = Set.filter (\<lambda>x. drop b x = k) X;
                                                                   M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group
                                                                 in k[y:=Some (eval_agg_op \<omega> M)]))" 
        unfolding eval_aggargs_def eval_agg_def empty_table_def using False by auto
      define group where "group = Set.filter (\<lambda>x. drop b x = k) X"
      define M where "M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group"
      have key_in_map: "k \<in> Mapping.keys m"
        using SumAux by (auto simp add:valid_aggmap_def) (metis k_assm)
      then have "Mapping.lookup m k = Some (length (flatten_multiset M), foldl plus (snd \<omega>) (flatten_multiset M))"
        using SumAux True by (simp add: M_def group_def Let_def lookup_default_def valid_aggmap_def group_multiset_def)
      then have "result = (case Mapping.lookup m k of 
                            Some (_, agg_sum) \<Rightarrow> k[y:=Some agg_sum]
                          | None \<Rightarrow> k)"
        using True k_assm unfolding M_def group_def by auto (metis (no_types, lifting) eval_agg_op.simps(4) prod.exhaust_sel)
      then show  "result \<in> result_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (SumAux m)"
        using key_in_map True by auto
    qed
    next
      case False
      then have agg_type: "fst \<omega> = Formula.Agg_Avg" using SumAux by auto
      obtain aux where aux_def: "\<omega> = (Formula.Agg_Avg, aux)" using agg_type 
        by (simp add: prod_eq_iff)
      show ?thesis 
      proof (rule set_eqI, rule iffI)
      fix result
      assume "result \<in> result_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (SumAux m)"
      then obtain k where k_assm: "k \<in> Mapping.keys m \<and> result = (case Mapping.lookup m k of 
                                                      Some (cnt, agg_sum) \<Rightarrow> k[y:=Some (EFloat ((double_of_event_data agg_sum) / (double_of_int cnt)))]
                                                    | None \<Rightarrow> k)" using assm_map agg_type by auto
      define group where "group = Set.filter (\<lambda>x. drop b x = k) X"
      define M where "M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group"
      have not_empty: "flatten_multiset M \<noteq> []" 
        using flatten_multiset_not_empty[of _ b f m X k] SumAux k_assm False 
        by (auto simp: Let_def M_def group_multiset_def group_def)
      have "Mapping.lookup m k = Some (length (flatten_multiset M), foldl plus (EInt 0) (flatten_multiset M))" 
        using SumAux k_assm agg_type by (simp add: M_def group_def Let_def lookup_default_def valid_aggmap_def group_multiset_def)
      then have "result = k[y:= Some (eval_agg_op \<omega> M)]" 
        using k_assm agg_type not_empty SumAux aux_def
        by(auto simp add:valid_aggmap_def Let_def M_def group_def group_multiset_def split:list.splits)
      then show "result \<in> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> X"
        using k_assm SumAux by (auto simp add: M_def group_def Let_def eval_agg_def eval_aggargs_def valid_aggmap_def)
    next
      fix result
      assume "result \<in> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> X"
      then obtain k where k_assm: "(k \<in> (drop b) ` X \<and> result = (let group = Set.filter (\<lambda>x. drop b x = k) X;
                                                                   M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group
                                                                 in k[y:=Some (eval_agg_op \<omega> M)]))" 
        unfolding eval_aggargs_def eval_agg_def empty_table_def using assm_reg by auto
      define group where "group = Set.filter (\<lambda>x. drop b x = k) X"
      define M where "M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group"
      have "k \<in> Mapping.keys m" using k_assm SumAux 
      by (metis (no_types, lifting) aggaux.simps(27) valid_aggmap_def valid_maggaux.simps)
      then have not_empty: "flatten_multiset M \<noteq> []" 
        using flatten_multiset_not_empty[of _ b f m X k] SumAux k_assm False 
        unfolding group_multiset_def Let_def M_def group_def by fastforce
      have key_in_map: "k \<in> Mapping.keys m"
        using SumAux by (auto simp add:valid_aggmap_def) (metis k_assm)
      then have "Mapping.lookup m k = Some (length (flatten_multiset M), foldl plus (EInt 0) (flatten_multiset M))"
        using SumAux False by (simp add: M_def group_def Let_def lookup_default_def valid_aggmap_def group_multiset_def)
      then have "result = (case Mapping.lookup m k of 
                             Some (cnt, agg_sum) \<Rightarrow> k[y:=Some (EFloat ((double_of_event_data agg_sum) / (double_of_int cnt)))]
                          | None \<Rightarrow> k)"
        using False k_assm not_empty aux_def unfolding M_def group_def 
        by(auto simp: Let_def split:list.splits)
      then show  "result \<in> result_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (SumAux m)"
        using key_in_map False by auto
    qed
  qed
qed
next 
  case(MinAux x)
  then show ?case by auto
next
  case(MaxAux x)
  then show ?case by auto
next  
  case(MedAux x)
  then show ?case by auto
next
  case(CntAux m)
  have agg_type: "fst \<omega> = Formula.Agg_Cnt" using CntAux by auto
  then show ?case
  proof (cases "g0 \<and> X = {}")
    case(True)
    then show ?thesis 
      unfolding eval_aggargs_def eval_agg_def
      using CntAux by (auto simp add: valid_aggmap_def)
  next
    case(False)
    then have assm_map: "\<not>(g0 \<and> Mapping.keys m = {})" using CntAux by (auto simp add: valid_aggmap_def)
    show ?thesis
    proof (rule set_eqI, rule iffI)
      fix result
      assume "result \<in> result_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (CntAux m)"
      then have "\<exists>k. k \<in> Mapping.keys m \<and> result = (case Mapping.lookup m k of
                                                      Some i \<Rightarrow> k[y:=Some (EInt (integer_of_int i))]
                                                    | None \<Rightarrow> k)" 
        using assm_map by auto
      then obtain k where k_assm: "k \<in> Mapping.keys m \<and> result = (case Mapping.lookup m k of
                                                      Some i \<Rightarrow> k[y:=Some (EInt (integer_of_int i))]
                                                    | None \<Rightarrow> k)" by blast
      define group where "group = Set.filter (\<lambda>x. drop b x = k) X"
      define M where "M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group"
      have "Mapping.lookup m k = Some (length (flatten_multiset M))" 
        using CntAux k_assm 
        by (simp add: M_def group_def Let_def lookup_default_def valid_aggmap_def group_multiset_def)
      then have "result = k[y:= Some (eval_agg_op \<omega> M)]" 
        using k_assm agg_type 
        by (metis eval_agg_op.simps(1) option.simps(5) prod.collapse)
      then show "result \<in> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> X"
        using k_assm CntAux
        by (auto simp add: M_def group_def Let_def eval_agg_def eval_aggargs_def valid_aggmap_def)
    next
      fix result
      assume "result \<in> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> X"
      then have "\<exists>k. (k \<in> (drop b) ` X \<and> result = (let group = Set.filter (\<lambda>x. drop b x = k) X;
                                                     M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group
                                                   in k[y:=Some (eval_agg_op \<omega> M)]))" 
        unfolding eval_aggargs_def eval_agg_def empty_table_def
        using False by auto
      then obtain k where k_assm: "(k \<in> (drop b) ` X \<and> result = (let group = Set.filter (\<lambda>x. drop b x = k) X;
                                                                   M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group
                                                                 in k[y:=Some (eval_agg_op \<omega> M)]))" by blast
      define group where "group = Set.filter (\<lambda>x. drop b x = k) X"
      define M where "M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group"
      have key_in_map: "k \<in> Mapping.keys m"
        using CntAux k_assm by (auto simp add:valid_aggmap_def)
      then have "Mapping.lookup m k = Some (length (flatten_multiset M))"
        using CntAux 
        by (simp add: M_def group_def Let_def lookup_default_def valid_aggmap_def group_multiset_def)
      then have "result = (case Mapping.lookup m k of
                             Some i \<Rightarrow> k[y:=Some (EInt (integer_of_int i))]
                           | None \<Rightarrow> k)"
        using agg_type k_assm
        unfolding M_def group_def
        by (metis (no_types, lifting) eval_agg_op.simps(1) option.simps(5) prod.collapse)
      then show  "result \<in> result_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (CntAux m)"
        using key_in_map by auto
    qed
  qed
qed

lemma valid_result_maggaux: "valid_maggaux args aux X \<Longrightarrow> result_maggaux args aux = eval_aggargs args X"
  using valid_result_maggaux_unfolded by (cases args) fast

end
