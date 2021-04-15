theory Optimized_Agg
  imports Monitor
begin

type_synonym 'a agg_map = "(event_data tuple, 'a) mapping"

datatype aggaux' = CntAux nat

datatype aggaux = CntAux "nat agg_map" | SumAux "(nat \<times> event_data) agg_map" | MinAux "event_data table"
  | MaxAux "event_data table" | MedAux "event_data table"

definition group where [simp]:
  "group k b X = Set.filter (\<lambda>x. drop b x = k) X"

definition group_multiset where [simp]:
  "group_multiset k b f X = (let group = group k b X in
                      (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group)"


definition valid_aggmap :: "(event_data list \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> Formula.trm \<Rightarrow> (event_data option list, 'a) mapping \<Rightarrow> event_data option list set \<Rightarrow> bool" where [simp]:
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

fun insert_cnt :: "aggargs \<Rightarrow>  event_data tuple \<Rightarrow> nat agg_map \<Rightarrow> nat agg_map" where
  "insert_cnt args t m = (let group = drop (aggargs_b args) t 
                       in case (Mapping.lookup m group) of
                        Some i \<Rightarrow> Mapping.update group (i + 1) m
                      | None \<Rightarrow> Mapping.update group 1 m)"

fun insert_sum :: "aggargs \<Rightarrow> event_data tuple \<Rightarrow> (nat \<times> event_data) agg_map \<Rightarrow> (nat \<times> event_data) agg_map" where
  "insert_sum args t m = (let group = drop (aggargs_b args) t;
                              aggtype = fst (aggargs_\<omega> args);
                              y0 = (if aggtype = Formula.Agg_Sum then snd (aggargs_\<omega> args) else EInt 0);
                                         term = meval_trm (aggargs_f args) t
                                     in case (Mapping.lookup m group) of
                        Some (cnt, agg_sum) \<Rightarrow> Mapping.update group (cnt + 1, agg_sum + term) m
                      | None \<Rightarrow> Mapping.update group (1, y0 + term) m)"

fun insert_maggaux :: "aggargs \<Rightarrow> event_data table \<Rightarrow> aggaux \<Rightarrow> aggaux" where
  "insert_maggaux args data aux = (case aux of
    CntAux m \<Rightarrow> CntAux (Finite_Set.fold (insert_cnt args) m data)
  | SumAux m \<Rightarrow> SumAux (Finite_Set.fold (insert_sum args) m data)
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

lemma unique_term_multiset: "(t, y1) \<in> group_multiset k b f X \<Longrightarrow> y2 \<noteq> y1 \<Longrightarrow> (t, y2) \<notin> group_multiset k b f X"
proof rule
  assume term_in: "(t, y1) \<in> group_multiset k b f X" and not_eq: "y2 \<noteq> y1" and term_in_2: "(t, y2) \<in> group_multiset k b f X"
  define group where [simp]: "group = Set.filter (\<lambda>x. drop b x = k) X"
  have "y2 = ecard (Set.filter (\<lambda>x. meval_trm f x = t) group)" using term_in_2 by(auto simp: Let_def)
  moreover have "y1 = ecard (Set.filter (\<lambda>x. meval_trm f x = t) group)" using term_in by(auto simp: Let_def)
  ultimately show False using not_eq by auto
qed

lemma valid_init_maggaux_unfolded: "safe_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> \<Longrightarrow> valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (init_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr>) {}"
  by (cases "fst \<omega>") auto

lemma valid_init_maggaux: "safe_aggargs args \<Longrightarrow> valid_maggaux args (init_maggaux args) {}"
  using valid_init_maggaux_unfolded by (cases args) fast

lemma insert_cnt_comm: "(insert_cnt args x \<circ> insert_cnt args y) m  = (insert_cnt args y \<circ> insert_cnt args x) m"
  by (auto split:option.splits simp add: Let_def update_update(2) lookup_update') 

lemma cmp_comm: 
  assumes commute_f: "comp_fun_commute f"
  shows "(f t1 ^^ n1 \<circ> f t2 ^^ n2) y0 = (f t2 ^^ n2 \<circ> f t1 ^^ n1) y0" 
proof(induction n1)
case 0
  then show ?case by auto
next
  case (Suc n)
  have aux1: "f t1 ((f t1 ^^ n) y0) = (f t1 ^^ n) (f t1 y0)" by (induction n) auto
  moreover have "f t1 ((f t2 ^^ n2) ((f t1 ^^ n) y0)) = (f t2 ^^ n2) ((f t1 ^^ n) (f t1 y0))" 
    using aux1 commute_f comp_fun_commute.fun_left_comm[of f t1 t2] by(induction n2) auto
  ultimately show ?case using Suc by auto
qed

lemma fold_flatten_multiset: 
  assumes finite_m: "finite M"
  assumes commute_f: "comp_fun_commute f"
  shows "fold f (flatten_multiset M) y0  = Finite_Set.fold (\<lambda> (t, m) y. ((f t) ^^ (the_enat m)) y) y0 M"
proof -
  interpret comp_fun_commute "\<lambda> (t, m) y. ((f t) ^^ (the_enat m)) y"
    using cmp_comm[of f] commute_f
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
    obtain t m where x_def: "x = (t, m)"
      by (cases x) auto
    define xs where "xs = (linorder.sorted_list_of_set (le_of_comp c) F)"
    have "fold f (concat (map (\<lambda>(x, c). replicate (the_enat c) x) (linorder.insort_key (le_of_comp c) (\<lambda>x. x) (t, m) xs))) y0
       = (f t ^^ the_enat m) (fold f (concat (map (\<lambda>(x, c). replicate (the_enat c) x) xs)) y0)" 
    proof(induction xs arbitrary: y0)
      case Nil
      then show ?case using linorder.insort_key.simps[OF c_class, of "(\<lambda>x. x)"] by (auto simp:xs_def)
    next
      case (Cons a as)
      then show ?case 
        using linorder.insort_key.simps[OF c_class, of "(\<lambda>x. x)"] cmp_comm[of f "the_enat m1"] 
        by (auto simp:xs_def commute_f comp_fun_commute.comp_fun_commute fn_comm_power' fold_commute_apply)
    qed
    then show ?case
      using x_def insert linorder.sorted_list_of_set_insert[OF c_class]
      by (simp add:flatten_multiset_def csorted_list_of_set_def c_def xs_def)
  qed
qed

lemma length_fold: "length xs = fold (\<lambda> _ n. n + 1) xs 0"
  by (induction xs) (auto simp:fold_commute_apply)

lemma length_flatten_multiset: 
  assumes "finite M"
  shows "length (flatten_multiset M) = Finite_Set.fold (\<lambda> (t, m) y. y + (the_enat m)) 0 M"
  using length_fold[of "flatten_multiset M"] fold_flatten_multiset[of M "(\<lambda>_ n. n + 1)" 0]
  by (simp add: fold_flatten_multiset assms comp_fun_commute.intro) (meson add.commute)

lemma other_evals_unchanged:
  assumes elem_group: "drop b elem = k"
  and diff_group: "x \<noteq> meval_trm f elem"
  shows "(x, y) \<in> group_multiset k b f (insert elem X) \<longleftrightarrow> (x, y) \<in> group_multiset k b f X"
proof
  define old_group where [simp]: "old_group = group k b X"
  define new_group where [simp]: "new_group = group k b (X \<union> {elem})"
  have aux1: "\<And>x. x \<noteq> meval_trm f elem \<Longrightarrow> Set.filter (\<lambda>xa. meval_trm f xa = x) new_group = Set.filter (\<lambda>xa. meval_trm f xa = x) old_group" by auto
  assume assm: "(x, y) \<in> group_multiset k b f (insert elem X)"
  then have x_old_eval: "x \<in> meval_trm f ` old_group" using diff_group by(auto simp: Let_def)
  have "y = ecard (Set.filter (\<lambda>xa. meval_trm f xa = x) new_group)" using assm by(auto simp: Let_def)
  then have "y =  ecard (Set.filter (\<lambda>xa. meval_trm f xa = x) old_group)" using aux1 diff_group by auto
  then show "(x, y) \<in>  group_multiset k b f X" using x_old_eval by (auto simp: Let_def)
next
  define old_group where [simp]: "old_group = group k b X"
  define new_group where [simp]: "new_group = group k b (X \<union> {elem})"
  have aux1: "\<And>x. x \<noteq> meval_trm f elem \<Longrightarrow> Set.filter (\<lambda>xa. meval_trm f xa = x) new_group = Set.filter (\<lambda>xa. meval_trm f xa = x) old_group" by auto
  assume assm: "(x, y) \<in>  group_multiset k b f X"
  then have x_old_eval: "x \<in> meval_trm f ` old_group" by(auto simp: Let_def)
  have "y = ecard (Set.filter (\<lambda>xa. meval_trm f xa = x) old_group)" using assm by(auto simp: Let_def)
  then have "y =  ecard (Set.filter (\<lambda>xa. meval_trm f xa = x) new_group)" using aux1 diff_group by auto
  then show "(x, y) \<in> group_multiset k b f (insert elem X)" using x_old_eval by (auto simp: Let_def)
qed

lemma multiset_new_term_insert:
  assumes elem_group: "drop b elem = k"
  and new_term_eval: "Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) (group k b X) = {}"
  shows "group_multiset k b f (insert elem X) = insert (meval_trm f elem, 1) (group_multiset k b f X)"
proof -
  define updated_data where [simp]: "updated_data = X \<union> {elem}"
  define old_group where [simp]: "old_group = group k b X"
  define new_group where [simp]: "new_group = group k b updated_data"
  define old_evals where "old_evals = meval_trm f ` old_group"
  have aux: "Set.filter (\<lambda>x. drop b x = k) (insert elem X) = insert elem old_group" using elem_group by auto
  have aux1: "\<And>x. x \<noteq> meval_trm f elem \<Longrightarrow> Set.filter (\<lambda>xa. meval_trm f xa = x) new_group = Set.filter (\<lambda>xa. meval_trm f xa = x) old_group" by auto
  have aux2: "meval_trm f elem \<notin> old_evals" using new_term_eval by (auto simp: old_evals_def)
  moreover have "Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) new_group = {elem}" using new_term_eval elem_group by auto
  moreover have "ecard {elem} = 1" using enat_1 by (auto simp:ecard_def)
  moreover have "(\<lambda>x. (x, ecard (Set.filter (\<lambda>xa. meval_trm f xa = x) new_group))) ` old_evals = 
                 (\<lambda>x. (x, ecard (Set.filter (\<lambda>xa. meval_trm f xa = x) old_group))) ` old_evals"
    using other_evals_unchanged by (metis (mono_tags, lifting) aux1 aux2 image_cong)
  ultimately show "group_multiset k b f (insert elem X) = insert (meval_trm f elem, 1) (group_multiset k b f X)" using aux
    by(simp add:Let_def old_evals_def)
qed

lemma multiset_old_term_insert:
  assumes elem_group: "drop b elem = k"
  and old_term_eval: "Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) (group k b X) \<noteq> {}"
  and old_val: "(meval_trm f elem, y) \<in> group_multiset k b f X" 
  and disjoint: "elem \<notin> X"
  and finite: "finite X"
  shows "group_multiset k b f (insert elem X) = 
         insert (meval_trm f elem, y + 1) ((group_multiset k b f X) - {(meval_trm f elem, y)})"
proof (rule set_eqI, rule iffI)
  fix x
  assume x_in_M: "x \<in> group_multiset k b f (insert elem X)"
  then obtain t v where x_def: "x = (t, v)" by fastforce
  define updated_data where [simp]: "updated_data = X \<union> {elem}"
  define old_group where [simp]: "old_group = group k b X"
  define new_group where [simp]: "new_group = group k b updated_data"
  define old_evals where "old_evals = meval_trm f ` old_group"
  have group_ins: "new_group = insert elem old_group" using elem_group by auto
  have y_card: "y = ecard (Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) old_group)" using old_val by (auto simp: Let_def)
  moreover have "Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) (insert elem (Set.filter (\<lambda>x. drop b x = k) X)) =
                 insert elem  (Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) (Set.filter (\<lambda>x. drop b x = k) X))" by auto
  moreover have "elem \<notin> Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) (Set.filter (\<lambda>x. drop b x = k) X)" by (meson Set.member_filter disjoint)
  ultimately have correct_card: "y + 1 = ecard (Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) new_group)" 
    using eSuc_enat plus_1_eSuc(2) group_ins by(auto simp: ecard_def) 
  then have aux1: "(meval_trm f elem, y + 1) \<in> group_multiset k b f (insert elem X)" using group_ins by (auto simp:Let_def)
  have aux2: "(meval_trm f elem, y) \<notin> group_multiset k b f (insert elem X)" 
    using unique_term_multiset[of "meval_trm f elem" "y + 1" k b f updated_data y] aux1 y_card
    by(simp add:Let_def) (meson ecard_def finite_filter finite valid_maggaux.simps)
  show "x \<in> insert (meval_trm f elem, y + 1) ((group_multiset k b f X) - {(meval_trm f elem, y)})"
  proof (cases "t = meval_trm f elem")
    case True
    then have "v = y + 1" using x_in_M x_def aux1 using unique_term_multiset by blast
    then show ?thesis using x_def x_in_M True by auto
  next
    case False
    then show ?thesis using other_evals_unchanged 
      by (metis Pair_inject Set.member_remove elem_group insertI2 x_def x_in_M)
  qed
next
  fix x
  assume x_in_oldM: "x \<in> insert (meval_trm f elem, y + 1) ((group_multiset k b f X) - {(meval_trm f elem, y)})"
  then obtain t v where x_def: "x = (t, v)" by force
  define updated_data where [simp]: "updated_data = X \<union> {elem}"
  define old_group where [simp]: "old_group = group k b X"
  define new_group where [simp]: "new_group = group k b updated_data"
  define old_evals where "old_evals = meval_trm f ` old_group"
  have group_ins: "new_group = insert elem old_group" using elem_group by auto
  have y_card: "y = ecard (Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) old_group)" using old_val by (auto simp: Let_def)
  moreover have "Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) (insert elem (Set.filter (\<lambda>x. drop b x = k) X)) =
                 insert elem  (Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) (Set.filter (\<lambda>x. drop b x = k) X))" by auto
  moreover have "elem \<notin> Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) (Set.filter (\<lambda>x. drop b x = k) X)" by (meson Set.member_filter disjoint)
  ultimately have correct_card: "y + 1 = ecard (Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) new_group)" 
    using eSuc_enat plus_1_eSuc(2) group_ins by(auto simp: ecard_def) 
  then have aux1: "(meval_trm f elem, y + 1) \<in> group_multiset k b f (insert elem X)" using group_ins by (auto simp:Let_def)
  show "x \<in> group_multiset k b f (insert elem X)" 
  proof (cases "t = meval_trm f elem")
    case True
    then have "v = y + 1" using x_in_oldM x_def by (metis DiffE insertE old.prod.inject old_val singleton_iff unique_term_multiset)
    then show ?thesis using True aux1 x_def by blast
  next
    case False
    then show ?thesis by (metis DiffD1 elem_group insertE old.prod.inject other_evals_unchanged x_def x_in_oldM)
  qed
qed  

lemma valid_insert_cnt_unfolded: 
  assumes valid_before: "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (CntAux m) X" 
  and disjoint: "elem \<notin> X"
shows "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> 
        (CntAux (insert_cnt \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> elem m)) (X \<union> {elem})"
proof - 
  define updated_map where [simp]: "updated_map = insert_cnt \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> elem m"
  define updated_data where [simp]: "updated_data = X \<union> {elem}"
  interpret comp_fun_commute "\<lambda>(t, m) y. y + the_enat m" 
    by(unfold_locales) auto
  have valid_finite: "finite updated_data" using valid_before by auto
  have valid_key_invariant: "\<And>k. k \<in> (drop b) ` updated_data \<longleftrightarrow> k \<in> Mapping.keys updated_map"
  proof (rule iffI)
    fix k
    assume assm: "k \<in> (drop b) ` updated_data"
    show "k \<in>  Mapping.keys updated_map"
      using valid_before assm
      by (cases "k \<in> (drop b) ` X") (auto simp: Let_def split:option.splits)
  next
    fix k
    assume assm: "k \<in> Mapping.keys updated_map"
    show "k \<in> (drop b) ` updated_data"
      using valid_before assm
      by (cases "k \<in> Mapping.keys m") (auto simp: Let_def split:option.splits)
  qed
  have valid_value_invariant: "\<And>k. k \<in> Mapping.keys updated_map \<longrightarrow> Mapping.lookup updated_map k = 
          (let group = Set.filter (\<lambda>x. drop b x = k) updated_data;
           M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group
          in Some (length (flatten_multiset M)))"
  proof rule
    fix k
    define group where [simp]: "group = Set.filter (\<lambda>x. drop b x = k) updated_data"
    define M where [simp]: "M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group"
    define old_group where [simp]: "old_group = Set.filter (\<lambda>x. drop b x = k) X"
    define old_M where [simp]: "old_M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) old_group))) ` meval_trm f ` old_group"
    define old_evals where "old_evals = meval_trm f ` old_group"
    assume assm: "k \<in> Mapping.keys updated_map"
    show "Mapping.lookup updated_map k = 
          (let group = Set.filter (\<lambda>x. drop b x = k) updated_data;
           M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group
          in Some (length (flatten_multiset M)))"
    proof (cases "k \<in> Mapping.keys m")
      case False
      then have map_val: "Mapping.lookup updated_map k = Some 1" 
        using assm by (auto simp: keys_is_none_rep Let_def lookup_update' split:option.splits)
      have "drop b elem = k" 
        using assm False 
        by(auto simp: Let_def split:option.splits)
      then have group_single_elem: "group = {elem}" 
        using False valid_before image_iff
        by fastforce
      then have "M = insert (meval_trm f elem, enat 1) {}"
        using group_single_elem unfolding M_def Set.filter_def ecard_def by (auto cong: conj_cong)
      then have "length(flatten_multiset M) = 1" 
        using length_flatten_multiset[of M] Finite_Set.comp_fun_commute.fold_insert by(auto)
      then show ?thesis using map_val by simp
    next
      case True
      then have in_map: "k \<in> Mapping.keys m" by auto
      show ?thesis
      proof(cases "drop b elem = k")
        case True
        then have elem_group: "drop b elem = k" by auto
        then have newgroup_def: "group = insert elem old_group" by auto
        have both_finite: "finite old_M \<and> finite M" using valid_before by auto
        have "length(flatten_multiset(M)) = length(flatten_multiset(old_M)) + 1"
        proof(cases "Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) old_group = {}")
          case True
          then have "M = insert (meval_trm f elem, 1) old_M" using multiset_new_term_insert elem_group by(simp add: Let_def)
          moreover have "(meval_trm f elem, 1) \<notin> old_M" using True by auto
          ultimately show ?thesis using both_finite by (auto simp:length_flatten_multiset one_enat_def)
        next
          case False
          then obtain y where y_def: "(meval_trm f elem, y) \<in> old_M" 
            by (smt (z3) Collect_empty_eq Set.filter_def image_eqI old_M_def)
          then obtain i where i_def: "y = enat i" 
            by (smt (z3) Pair_inject ecard_def finite_filter image_iff old_M_def old_group_def valid_before valid_maggaux.simps)
          have finite_remove: "finite (old_M - {(meval_trm f elem, y)})" using both_finite finite_Diff  by (auto simp: Set.remove_def)
          have finite_insert: "finite (insert (meval_trm f elem, y) old_M)" using both_finite by blast
          have M_insert_remove_def: "M = insert (meval_trm f elem, y + 1) (old_M - {(meval_trm f elem, y)})" 
            using multiset_old_term_insert[of b elem k f X y] elem_group False y_def valid_before disjoint
            by(simp only: M_def old_M_def group_def old_group_def updated_data_def group_multiset_def Let_def Optimized_Agg.group_def) auto          
          then have aux: "length(flatten_multiset(insert (meval_trm f elem, y) old_M)) = length(flatten_multiset(old_M - {(meval_trm f elem, y)})) + i" 
            using both_finite finite_insert finite_remove 
            Finite_Set.comp_fun_commute.fold_insert_remove[of "\<lambda>(t, m) y. y + the_enat m" old_M 0 "(meval_trm f elem, y)"]
            by (simp only: length_flatten_multiset) (metis comp_fun_commute_axioms i_def old.prod.case the_enat.simps)
          have "(meval_trm f elem, y + 1) \<notin> old_M - {(meval_trm f elem, y)}" using y_def by auto
          then show ?thesis using both_finite finite_remove M_insert_remove_def i_def Finite_Set.comp_fun_commute.fold_insert[of "\<lambda>(t, m) y. y + the_enat m" "old_M - {(meval_trm f elem, y)}" "(meval_trm f elem, y + 1)" 0]
            by (metis (mono_tags, lifting) aux case_prod_conv comp_fun_commute_axioms group_cancel.add1 insert_absorb length_flatten_multiset one_enat_def plus_enat_simps(1) the_enat.simps y_def)
        qed
        moreover obtain len where len_def: "Mapping.lookup m k = Some len \<and> len = length(flatten_multiset(old_M))" 
          using valid_before in_map by auto metis
        then have "Mapping.lookup updated_map k = Some (len + 1)" by (simp add: elem_group lookup_update)
        ultimately show ?thesis by (simp add: len_def)
      next
        case False
        then have same_group: "group = old_group" by auto
        then have "M = old_M" by auto
        then have "Mapping.lookup updated_map k = Mapping.lookup m k" 
          using False by (auto split:option.splits simp:Let_def lookup_update')
        then show ?thesis using valid_before same_group in_map 
          by (auto simp: Let_def)
      qed
    qed
  qed
  show ?thesis using valid_value_invariant valid_key_invariant valid_finite valid_before
    by (auto simp add: Let_def)
qed

lemma valid_insert_maggaux_unfolded: 
  "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> aux X \<Longrightarrow>
  finite Y \<Longrightarrow>
  X \<inter> Y = {} \<Longrightarrow>
  valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> 
  (insert_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> Y aux) (X \<union> Y)" 
proof(induction aux)
  case (CntAux m)
  have disjoint: "X \<inter> Y = {}" using CntAux by auto
  have finite_y: "finite Y" using CntAux by auto
  then show ?case using disjoint
  proof(induction Y)
    case empty
    then show ?case using CntAux by auto
  next
    case (insert x F)
    define args where "args = \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr>"
    interpret comp_fun_commute "insert_cnt args"
      using insert_cnt_comm by unfold_locales auto
    obtain intermediate_map where intermediate_map_def: "CntAux intermediate_map = insert_maggaux args F (CntAux m)" by auto
    have valid_a: "valid_maggaux args (CntAux (insert_cnt args x intermediate_map)) (X \<union> F \<union> {x})" 
      using insert valid_insert_cnt_unfolded disjoint Un_iff args_def intermediate_map_def by (metis disjoint_insert(1))
    then have "Finite_Set.fold (insert_cnt args) m (insert x F) = insert_cnt args x (Finite_Set.fold (insert_cnt args) m F)"
      using  Finite_Set.comp_fun_commute.fold_insert[of "insert_cnt args" F x m] insert by auto
    moreover have "CntAux (Finite_Set.fold (insert_cnt args) m F) = CntAux intermediate_map"
      by(auto simp:intermediate_map_def)
    ultimately have "insert_maggaux args (insert x F) (CntAux m) = CntAux (insert_cnt args x intermediate_map)"
      using  Finite_Set.comp_fun_commute.fold_insert[of "insert_cnt args" F x m]
      by auto
    then have "valid_maggaux args (insert_maggaux args (insert x F) (aggaux.CntAux m)) (X \<union> insert x F)"
      using valid_a
      by auto
    then show ?case
      by (auto simp: args_def)
  qed
next
case (SumAux x)
  then show ?case sorry
next
  case (MinAux x)
  then show ?case sorry
next
  case (MaxAux x)
  then show ?case sorry
next
  case (MedAux x)
  then show ?case sorry
qed

lemma valid_insert_maggaux: "valid_maggaux args aux X \<Longrightarrow> finite Y \<Longrightarrow>
    table (aggargs_b args + aggargs_n args) (aggargs_cols args) Y \<Longrightarrow>
    type_restr args Y \<Longrightarrow> X \<inter> Y = {} \<Longrightarrow>
    valid_maggaux args (insert_maggaux args Y aux) (X \<union> Y)"
  using valid_insert_maggaux_unfolded by (cases args) fast

lemma valid_aggmap_empty_data: "valid_aggmap g b f m X \<Longrightarrow> X = {} \<longleftrightarrow> Mapping.keys m = {}"
  by auto

lemma flatten_multiset_not_empty: 
  assumes valid_map: "valid_aggmap g b f m X"
  and finite: "finite X"
  and in_map: "k \<in> Mapping.keys m"
  shows "flatten_multiset (group_multiset k b f X) \<noteq> []"
proof -
  define M where [simp]: "M = group_multiset k b f X"
  obtain c where c_def: "ID ccompare = Some (c :: (event_data \<times> enat) comparator)" 
    by (simp add: ID_def ccompare_prod_def ccompare_event_data_def ccompare_enat_def split:if_splits option.splits)
  note c = ID_ccompare'[OF c_def] 
  note c_class = comparator.linorder[OF c]
  define M_list where [simp]: "M_list = linorder.sorted_list_of_set (le_of_comp c) M"
  obtain elem where elem_prop: "elem \<in> X \<and> drop b elem = k" using in_map valid_map imageE[of k "drop b" X] by auto
  then obtain m where m_prop: "(meval_trm f elem, m) \<in> M" 
    by (auto simp: Let_def) fastforce
  define group where [simp]: "group = Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) (Set.filter (\<lambda>x. drop b x = k) X)"
  have "ecard group \<noteq> 0" using finite elem_prop by (auto simp:ecard_def zero_enat_def) 
  then have m_pos: "m > 0 \<and> m \<noteq> \<infinity>" 
    using elem_prop m_prop finite  by (auto simp: Let_def ecard_def)
  then have "the_enat m > 0"
    apply(auto simp: the_enat_def)
    using enat_0_iff(1) by blast
  then obtain n where n_def: "the_enat m = Suc n" using gr0_implies_Suc by auto
  have finite_m: "finite M" using finite by (auto simp: Let_def)
  then have "(meval_trm f elem, m) \<in> set (linorder.sorted_list_of_set (le_of_comp c) M)"
    using m_prop linorder.set_sorted_list_of_set[OF c_class] by auto
  then show ?thesis 
    using finite_m n_def by (simp add:flatten_multiset_def csorted_list_of_set_def c_def) force
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
      by auto
  next
    case False
    then have assm_map: "\<not>(g0 \<and> Mapping.keys m = {})" using valid_aggmap_empty_data[of _ b f m X] SumAux by fastforce
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
      define group where [simp]: "group = Set.filter (\<lambda>x. drop b x = k) X"
      define M where [simp]: "M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group"
      have "Mapping.lookup m k = Some (length (flatten_multiset M), foldl plus (snd \<omega>) (flatten_multiset M))" 
        using SumAux k_assm True by (simp add: Let_def lookup_default_def)
      then have "result = k[y:= Some (eval_agg_op \<omega> M)]" 
        using k_assm True by auto (metis (no_types, lifting) eval_agg_op.simps(4) prod.exhaust_sel)
      then show "result \<in> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> X"
        using k_assm SumAux by (auto simp add: Let_def eval_agg_def eval_aggargs_def)
    next
      fix result
      assume "result \<in> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> X"
      then obtain k where k_assm: "(k \<in> (drop b) ` X \<and> result = (let group = Set.filter (\<lambda>x. drop b x = k) X;
                                                                   M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group
                                                                 in k[y:=Some (eval_agg_op \<omega> M)]))" 
        unfolding eval_aggargs_def eval_agg_def empty_table_def using False by auto
      define group where [simp]: "group = Set.filter (\<lambda>x. drop b x = k) X"
      define M where [simp]: "M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group"
      have key_in_map: "k \<in> Mapping.keys m"
        using SumAux by auto (metis k_assm)
      then have "Mapping.lookup m k = Some (length (flatten_multiset M), foldl plus (snd \<omega>) (flatten_multiset M))"
        using SumAux True by (simp add: Let_def lookup_default_def)
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
      define group where [simp]: "group = Set.filter (\<lambda>x. drop b x = k) X"
      define M where [simp]: "M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group"
      have not_empty: "flatten_multiset M \<noteq> []" 
        using flatten_multiset_not_empty[of _ b f m X k] SumAux k_assm False 
        by (auto simp: Let_def) force
      have "Mapping.lookup m k = Some (length (flatten_multiset M), foldl plus (EInt 0) (flatten_multiset M))" 
        using SumAux k_assm agg_type by (simp add: Let_def lookup_default_def)
      then have "result = k[y:= Some (eval_agg_op \<omega> M)]" 
        using k_assm agg_type not_empty SumAux aux_def
        by(auto simp add: Let_def split:list.splits)
      then show "result \<in> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> X"
        using k_assm SumAux by (auto simp add: Let_def eval_agg_def eval_aggargs_def)
    next
      fix result
      assume "result \<in> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> X"
      then obtain k where k_assm: "(k \<in> (drop b) ` X \<and> result = (let group = Set.filter (\<lambda>x. drop b x = k) X;
                                                                   M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group
                                                                 in k[y:=Some (eval_agg_op \<omega> M)]))" 
        unfolding eval_aggargs_def eval_agg_def empty_table_def using assm_reg by auto
      define group where [simp]: "group = Set.filter (\<lambda>x. drop b x = k) X"
      define M where [simp]: "M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group"
      have "k \<in> Mapping.keys m" using k_assm SumAux 
      by (metis (no_types, lifting) aggaux.simps(27) valid_aggmap_def valid_maggaux.simps)
      then have not_empty: "flatten_multiset M \<noteq> []" 
        using flatten_multiset_not_empty[of _ b f m X k] SumAux k_assm False 
        unfolding group_multiset_def Let_def M_def group_def by fastforce
      have key_in_map: "k \<in> Mapping.keys m"
        using SumAux by auto (metis k_assm)
      then have "Mapping.lookup m k = Some (length (flatten_multiset M), foldl plus (EInt 0) (flatten_multiset M))"
        using SumAux False by (simp add: Let_def lookup_default_def)
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
      using CntAux by auto
  next
    case(False)
    then have assm_map: "\<not>(g0 \<and> Mapping.keys m = {})" using CntAux by auto
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
      define group where [simp]: "group = Set.filter (\<lambda>x. drop b x = k) X"
      define M where [simp]: "M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group"
      have "Mapping.lookup m k = Some (length (flatten_multiset M))" 
        using CntAux k_assm 
        by (simp add: Let_def lookup_default_def)
      then have "result = k[y:= Some (eval_agg_op \<omega> M)]" 
        using k_assm agg_type 
        by (metis eval_agg_op.simps(1) option.simps(5) prod.collapse)
      then show "result \<in> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> X"
        using k_assm CntAux
        by (auto simp add: Let_def eval_agg_def eval_aggargs_def)
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
      define group where [simp]: "group = Set.filter (\<lambda>x. drop b x = k) X"
      define M where [simp]: "M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group"
      have "Mapping.lookup m k = Some (length (flatten_multiset M))"
        using CntAux k_assm
        by (simp add: Let_def lookup_default_def)
      then have "result = (case Mapping.lookup m k of
                             Some i \<Rightarrow> k[y:=Some (EInt (integer_of_int i))]
                           | None \<Rightarrow> k)"
        using agg_type k_assm
        unfolding M_def group_def
        by (metis (no_types, lifting) eval_agg_op.simps(1) option.simps(5) prod.collapse)
      then show  "result \<in> result_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (CntAux m)"
        using CntAux k_assm by auto
    qed
  qed
qed

lemma valid_result_maggaux: "valid_maggaux args aux X \<Longrightarrow> result_maggaux args aux = eval_aggargs args X"
  using valid_result_maggaux_unfolded by (cases args) fast

end
