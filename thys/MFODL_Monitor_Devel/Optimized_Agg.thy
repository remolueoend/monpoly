theory Optimized_Agg
  imports Monitor
  Ordered_Statistics_Tree
begin


fun less_eq_event_data' where
  "less_eq_event_data' (EInt x) (EInt y) \<longleftrightarrow> x \<le> y"
| "less_eq_event_data' (EInt _) _ \<longleftrightarrow> True"
| "less_eq_event_data' (EFloat _) (EInt _) \<longleftrightarrow> False"
| "less_eq_event_data' (EFloat x) (EFloat y) \<longleftrightarrow> lle_double x y"
| "less_eq_event_data' (EFloat _) (EString _) \<longleftrightarrow> True"
| "less_eq_event_data' (EString x) (EString y) \<longleftrightarrow> x \<le> y"
| "less_eq_event_data' (EString _) _ \<longleftrightarrow> False"

fun less_event_data' :: "event_data \<Rightarrow> event_data \<Rightarrow> bool"  where
  "less_event_data' (EFloat x) (EFloat y) \<longleftrightarrow> lless_double x y" |
  "less_event_data' x y \<longleftrightarrow> less_eq_event_data' x y \<and> \<not> (y = x)"

lemma lin1: "less_event_data' x y = (less_eq_event_data' x y \<and> \<not> less_eq_event_data' y x)"
proof(cases x)
case (EInt x1) then show ?thesis by (cases y) auto
next case (EFloat x2) then show ?thesis by (cases y) auto
next case (EString x3) then show ?thesis by (cases y) auto
qed

lemma lin2: "less_eq_event_data' x x"
  by(cases x) auto

interpretation event_data_linorder : linorder less_eq_event_data' less_event_data'
  using lin1 lin2  sorry

instantiation event_data :: linorder 
begin
instance sorry
end

type_synonym 'a agg_map = "(event_data tuple, 'a) mapping"

datatype aggaux = CntAux "nat agg_map" | 
                  SumAux "(nat \<times> event_data) agg_map" | 
                  RankAux "(event_data wbt) agg_map"

definition group where [simp]:
  "group k b X = Set.filter (\<lambda>x. drop b x = k) X"

definition group_multiset where [simp]:
  "group_multiset k b f X = (let group = group k b X in
                      (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group)"

definition valid_finite_mset where
  "valid_finite_mset X = ((\<forall>k x y. x \<noteq> y \<and> (k, x) \<in> X \<longrightarrow> (k, y) \<notin> X) \<and> 
                              (\<forall>k x. (k, x) \<in> X \<longrightarrow> x \<noteq> \<infinity>))"

fun mset_conv :: "(event_data \<times> enat) set  \<Rightarrow> event_data multiset" where
  "mset_conv s = Finite_Set.fold (\<lambda> (t, m) b. (replicate_mset (the_enat m) t) + b) {#} s"

definition valid_aggmap :: "('a option \<Rightarrow> (event_data \<times> enat) set \<Rightarrow>  bool) \<Rightarrow> nat \<Rightarrow> Formula.trm \<Rightarrow> (event_data option list, 'a) mapping \<Rightarrow> event_data option list set \<Rightarrow> bool" where [simp]:
  "valid_aggmap P b f m X \<longleftrightarrow> (\<forall>k. k \<in> (drop b) ` X \<longleftrightarrow> k \<in> Mapping.keys m) \<and>
                    (\<forall>k. k \<in> Mapping.keys m \<longrightarrow> (let M = group_multiset k b f X
                    in P (Mapping.lookup m k) M))"

fun valid_maggaux :: "aggargs \<Rightarrow> aggaux \<Rightarrow> event_data table \<Rightarrow> bool" where
  "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> aux X = 
  (finite X \<and>
  (let aggtype = fst \<omega> in case aux of 
      CntAux m \<Rightarrow>
        (aggtype = Formula.Agg_Cnt) \<and> 
        (valid_aggmap (\<lambda>k s. 
                      k = Some(length(flatten_multiset(s)))) 
                      b f m X)
    | SumAux m \<Rightarrow> (aggtype = Formula.Agg_Sum \<or> aggtype = Formula.Agg_Avg) \<and> (type_restr \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> X) \<and>
                  (let y0 = (if aggtype = Formula.Agg_Sum then snd \<omega> else EInt 0) in
                  (valid_aggmap 
                  (\<lambda>k s. k = Some(length(flatten_multiset(s)), foldl plus y0 (flatten_multiset s))) 
                  b f m X))
    | RankAux m \<Rightarrow> (aggtype = Formula.Agg_Min \<or> aggtype = Formula.Agg_Max \<or> aggtype = Formula.Agg_Med) \<and>
                   valid_aggmap 
                   (\<lambda>k s. (case k of Some(t) \<Rightarrow> valid_wbt_mset t (mset_conv s) |
                                     None \<Rightarrow> False)) 
                   b f m X))"

fun init_maggaux :: "aggargs \<Rightarrow> aggaux" where
  "init_maggaux args =
  (let aggtype = fst (aggargs_\<omega> args) in case aggtype of
      Formula.Agg_Cnt \<Rightarrow> CntAux Mapping.empty
    | Formula.Agg_Sum \<Rightarrow> SumAux Mapping.empty
    | Formula.Agg_Min \<Rightarrow> RankAux Mapping.empty
    | Formula.Agg_Max \<Rightarrow> RankAux Mapping.empty
    | Formula.Agg_Avg \<Rightarrow> SumAux Mapping.empty
    | Formula.Agg_Med \<Rightarrow> RankAux Mapping.empty)"

fun insert_cnt :: "aggargs \<Rightarrow>  event_data tuple \<Rightarrow> nat agg_map \<Rightarrow> nat agg_map" where
  "insert_cnt args t m = (let group = drop (aggargs_b args) t 
                          in case (Mapping.lookup m group) of
                            Some i \<Rightarrow> Mapping.update group (i + 1) m |
                            None \<Rightarrow> Mapping.update group 1 m)"

fun insert_sum :: "aggargs \<Rightarrow> event_data tuple \<Rightarrow> (nat \<times> event_data) agg_map \<Rightarrow> (nat \<times> event_data) agg_map" where
  "insert_sum args t m = (let group = drop (aggargs_b args) t;
                              aggtype = fst (aggargs_\<omega> args);
                              y0 = (if aggtype = Formula.Agg_Sum then snd (aggargs_\<omega> args) else EInt 0);
                              term = meval_trm (aggargs_f args) t
                          in case (Mapping.lookup m group) of
                            Some (cnt, agg_sum) \<Rightarrow> Mapping.update group (cnt + 1, agg_sum + term) m |
                            None \<Rightarrow> Mapping.update group (1, y0 + term) m)"

fun insert_rank :: "aggargs \<Rightarrow> event_data tuple \<Rightarrow> (event_data wbt) agg_map \<Rightarrow> (event_data wbt) agg_map" where
  "insert_rank args t m = (let group = drop (aggargs_b args) t;
                               term = meval_trm (aggargs_f args) t
                           in case (Mapping.lookup m group) of
                            Some t \<Rightarrow> Mapping.update group (insert term t) m |
                            None \<Rightarrow> Mapping.update group (insert term Leaf) m)"

fun insert_maggaux :: "aggargs \<Rightarrow> event_data table \<Rightarrow> aggaux \<Rightarrow> aggaux" where
  "insert_maggaux args data aux = (case aux of
    CntAux m \<Rightarrow> CntAux (Finite_Set.fold (insert_cnt args) m data)
  | SumAux m \<Rightarrow> SumAux (Finite_Set.fold (insert_sum args) m data)
  | RankAux m \<Rightarrow> RankAux (Finite_Set.fold (insert_rank args) m data))"

fun delete_cnt :: "aggargs \<Rightarrow> event_data tuple \<Rightarrow> nat agg_map \<Rightarrow> nat agg_map" where
  "delete_cnt args t m = (let group = drop (aggargs_b args) t
                       in case (Mapping.lookup m group) of
                         Some i \<Rightarrow> (if i = 1 then Mapping.delete group m 
                                    else Mapping.update group (i - 1) m)
                       | None \<Rightarrow> m)"

fun delete_sum :: "aggargs \<Rightarrow> event_data tuple \<Rightarrow> (nat \<times> event_data) agg_map \<Rightarrow> (nat \<times> event_data) agg_map" where
  "delete_sum args t m = (let group = drop (aggargs_b args) t;
                              term = meval_trm (aggargs_f args) t
                          in case (Mapping.lookup m group) of
                            Some (cnt, agg_sum) \<Rightarrow> (if cnt = 1 then Mapping.delete group m
                                                    else Mapping.update group (cnt - 1, agg_sum - term) m)
                          | None \<Rightarrow> m)"

fun delete_rank :: "aggargs \<Rightarrow> event_data tuple \<Rightarrow> (event_data wbt) agg_map \<Rightarrow> (event_data wbt) agg_map" where
  "delete_rank args t m = (let group = drop (aggargs_b args) t;
                               term = meval_trm (aggargs_f args) t
                           in case (Mapping.lookup m group) of
                            Some (Node Leaf _ Leaf) \<Rightarrow> Mapping.delete group m |
                            Some t \<Rightarrow> Mapping.update group (delete term t) m |
                            None \<Rightarrow> m)"

fun delete_maggaux :: "aggargs \<Rightarrow> event_data table \<Rightarrow> aggaux \<Rightarrow> aggaux" where
  "delete_maggaux args data aux = (case aux of
    CntAux m \<Rightarrow> CntAux (Finite_Set.fold (delete_cnt args) m data)
  | SumAux m \<Rightarrow> SumAux (Finite_Set.fold (delete_sum args) m data)
  | RankAux m \<Rightarrow> RankAux (Finite_Set.fold (delete_rank args) m data))"

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
  | RankAux m \<Rightarrow> (if g0 \<and> Mapping.keys m = {}
                      then singleton_table n y (eval_agg_op \<omega> {})
                      else if fst \<omega> = Formula.Agg_Min
                      then (\<lambda>k. (case Mapping.lookup m k of 
                                   Some t \<Rightarrow> k[y:=Some (select t 0)]
                                 | None \<Rightarrow> k)) ` Mapping.keys m
                      else if fst \<omega> = Formula.Agg_Max
                      then (\<lambda>k. (case Mapping.lookup m k of
                                   Some t \<Rightarrow> k[y:=Some (select t (size t - 1))]
                                 | None \<Rightarrow> k)) ` Mapping.keys m
                      else (\<lambda>k. (case Mapping.lookup m k of
                                   Some t \<Rightarrow> (let u = size t;
                                              u' = u div 2;
      aggval = (if even u then (double_of_event_data (select t (u' - 1)) + double_of_event_data (select t u') / double_of_int 2)
                          else double_of_event_data (select t u')) in
                                              k[y:=Some (EFloat aggval)])
                                 | None \<Rightarrow> k)) ` Mapping.keys m))"

fun plus' :: "event_data \<Rightarrow> event_data \<Rightarrow> event_data" where
  "plus' (EInt x) (EInt y) = EInt (x + y)"
| "plus' (_::event_data)  _ = EFloat nan"

fun minus' :: "event_data \<Rightarrow> event_data \<Rightarrow> event_data" where
  "minus' (EInt x) (EInt y) = EInt (y - x)"
| "minus' (_::event_data) _ = EFloat nan"


lemma iter_plus'_int: 
  assumes "t \<in> range EInt" and "y \<in> range EInt"
  shows "(plus' t ^^ n) y \<in> range EInt"
  using assms by (induction n) auto

lemma iter_minus'_int:
  assumes "t \<in> range EInt" and "y \<in> range EInt"
  shows "(minus' t ^^ n) y \<in> range EInt"
  using assms by (induction n) auto

lemma plus'_minus'_comm: 
  assumes "y0 \<in> range EInt" and "t \<in> range EInt"
  shows "(minus' t ^^ n) (plus' t y0)  = plus' t ((minus' t ^^ n) y0)"
proof(induction n)
case 0
  then show ?case by auto
next
  case (Suc n)
  have "(minus' t ^^ n) y0 \<in> range EInt" using iter_minus'_int assms by auto
  then show ?case using assms Suc by auto
qed

lemma plus'_minus'_comm': 
  assumes "y0 \<in> range EInt" and "t \<in> range EInt"
  shows "(plus' t ^^ n) (minus' t y0)  = minus' t ((plus' t ^^ n) y0)"
proof(induction n)
case 0
  then show ?case by auto
next
  case (Suc n)
  have "(plus' t ^^ n) y0 \<in> range EInt" using iter_plus'_int assms by auto
  then show ?case using assms Suc by auto
qed

lemma plus'_minus'_id:
  assumes "t \<in> range EInt" and "y0 \<in> range EInt"
  shows "((minus' t) ^^ n \<circ> (plus' t) ^^ n) y0 = y0"
  using Suc plus'_minus'_comm iter_plus'_int assms by (induction n) auto

lemma plus'_minus'_minus:
  assumes "t \<in> range EInt" and "y0 \<in> range EInt"
  shows "((plus' t) ^^ i \<circ> ((minus' t) ^^ (i + 1))) y0 = minus' t y0"
proof(induction i)
case 0
  then show ?case by auto
next
  case (Suc i)
  have "minus' t ((minus' t ^^ i) y0) \<in> range EInt" using assms iter_minus'_int by(auto simp: funpow_swap1)
  then show ?case using plus'_minus'_comm' assms  Suc by(auto) 
qed

lemma plus_plus'_equiv:
  assumes "x \<in> range EInt" and "y \<in> range EInt"
  shows "plus x y = plus' x y"
  using assms by auto

lemma minus_minus'_equiv:
  assumes "x \<in> range EInt" and "y \<in> range EInt"
  shows "minus x y = minus' y x"
  using assms by auto

lemma plus'_aux: "\<And>y x. plus' y \<circ> plus' x = plus' x \<circ> plus' y"
proof
  fix xa x y
  show "(plus' y \<circ> plus' x) xa = (plus' x \<circ> plus' y) xa"
  proof(cases xa)
    case (EInt x1)
    then have xa_int: "xa = EInt x1" by auto
    then show ?thesis
    proof(cases x)
      case (EInt x1)
      then have x_int: "x = EInt x1" by auto
      then show ?thesis
      proof(cases y)
        case (EInt x1)
        then show ?thesis using xa_int x_int by auto
      next
        case (EFloat x2)
        then show ?thesis by auto
      next
        case (EString x3)
        then show ?thesis by auto
      qed
    next
      case (EFloat x2)
      then show ?thesis by auto
    next
      case (EString x3)
      then show ?thesis by auto
    qed
  next
    case (EFloat x2)
    then show ?thesis by auto
  next
    case (EString x3)
    then show ?thesis by auto
  qed
qed

lemma minus'_aux: "\<And>y x. minus' y \<circ> minus' x = minus' x \<circ> minus' y"
proof
  fix xa x y
  show "(minus' y \<circ> minus' x) xa = (minus' x \<circ> minus' y) xa"
  proof(cases xa)
    case (EInt x1)
    then have xa_int: "xa = EInt x1" by auto
    then show ?thesis
    proof(cases x)
      case (EInt x1)
      then have x_int: "x = EInt x1" by auto
      then show ?thesis
      proof(cases y)
        case (EInt x1)
        then show ?thesis using xa_int x_int by auto
      next
        case (EFloat x2)
        then show ?thesis by auto
      next
        case (EString x3)
        then show ?thesis by auto
      qed
    next
      case (EFloat x2)
      then show ?thesis by auto
    next
      case (EString x3)
      then show ?thesis by auto
    qed
  next
    case (EFloat x2)
    then show ?thesis by auto
  next
    case (EString x3)
    then show ?thesis by auto
  qed
qed

lemma comp_fun_commute_plus': "comp_fun_commute plus'"
  using plus'_aux by(unfold_locales) auto

lemma comp_fun_commute_minus': "comp_fun_commute minus'"
  using minus'_aux by(unfold_locales) auto

lemma comm_plus': "plus' x y = plus' y x"
  by (smt (verit, best) add.commute plus'.elims plus'.simps(1))

lemma unique_term_multiset: "(t, y1) \<in> group_multiset k b f X \<Longrightarrow> y2 \<noteq> y1 \<Longrightarrow> (t, y2) \<notin> group_multiset k b f X"
proof rule
  assume term_in: "(t, y1) \<in> group_multiset k b f X" and not_eq: "y2 \<noteq> y1" and term_in_2: "(t, y2) \<in> group_multiset k b f X"
  define group where [simp]: "group = Set.filter (\<lambda>x. drop b x = k) X"
  have "y2 = ecard (Set.filter (\<lambda>x. meval_trm f x = t) group)" using term_in_2 by auto
  moreover have "y1 = ecard (Set.filter (\<lambda>x. meval_trm f x = t) group)" using term_in by auto
  ultimately show False using not_eq by auto
qed

lemma valid_init_maggaux_unfolded: "safe_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> \<Longrightarrow> valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (init_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr>) {}"
  (*by (cases "fst \<omega>") (auto simp: type_restr_def Let_def)*)
  sorry

lemma valid_init_maggaux': "safe_aggargs args \<Longrightarrow> valid_maggaux args (init_maggaux args) {}"
  using valid_init_maggaux_unfolded by (cases args) fast

definition valid_sumaux_maps where "valid_sumaux_maps = {m::(nat \<times> event_data) agg_map. \<forall>k a b. Mapping.lookup m k = Some (a, b) \<longrightarrow> b \<in> range EInt}"

fun insert_sum_comm :: "aggargs \<Rightarrow> event_data tuple \<Rightarrow> (nat \<times> event_data) agg_map \<Rightarrow> (nat \<times> event_data) agg_map" where
  "insert_sum_comm args t m = (let group = drop (aggargs_b args) t;
                              aggtype = fst (aggargs_\<omega> args);
                              y0 = (if aggtype = Formula.Agg_Sum then snd (aggargs_\<omega> args) else EInt 0);
                                         term = meval_trm (aggargs_f args) t in 
                        (if term \<in> range EInt then (case (Mapping.lookup m group) of
                        Some (cnt, agg_sum) \<Rightarrow> Mapping.update group (cnt + 1, plus' term agg_sum) m
                      | None \<Rightarrow> Mapping.update group (1, plus' y0 term) m) else m))"

fun delete_sum_comm :: "aggargs \<Rightarrow> event_data tuple \<Rightarrow> (nat \<times> event_data) agg_map \<Rightarrow> (nat \<times> event_data) agg_map" where
  "delete_sum_comm args t m = (let group = drop (aggargs_b args) t;
                              term = meval_trm (aggargs_f args) t in 
                           (if term \<in> range EInt then (case (Mapping.lookup m group) of
                            Some (cnt, agg_sum) \<Rightarrow> (if cnt = 1 then Mapping.delete group m
                                                    else Mapping.update group (cnt - 1, minus' term agg_sum) m)
                          | None \<Rightarrow> m) else m))"

lemma flatten_multiset_eint:
  assumes "\<And> t m. (t, m) \<in> M \<Longrightarrow> t \<in> range EInt"
  and "finite M"
  shows "set (flatten_multiset M) \<subseteq> range EInt"
proof
  obtain c where c_def: "ID ccompare = Some (c :: (event_data \<times> enat) comparator)" 
    by (simp add: ID_def ccompare_prod_def ccompare_event_data_def ccompare_enat_def split:if_splits option.splits)
  note c = ID_ccompare'[OF c_def] 
  note c_class = comparator.linorder[OF c]
  fix x
  assume "x \<in> set (flatten_multiset M)"
  then obtain b where [simp]: "(x, b) \<in> set (csorted_list_of_set M)" by (auto simp:flatten_multiset_def)
  then have "(x, b) \<in> M" using assms(2) linorder.set_sorted_list_of_set[OF c_class] by(auto simp:csorted_list_of_set_def c_def)
  then show "x \<in> range EInt" using assms by auto
qed

lemma valid_maggaux_valid_map:
  assumes "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (SumAux m) X"
  shows "m \<in> valid_sumaux_maps"
proof -
  have "\<And>k l s. Mapping.lookup m k = Some (l, s) \<Longrightarrow> s \<in> range EInt"
  proof -
    fix k l s
    assume assm: "Mapping.lookup m k = Some (l, s)"
    define y0 where "y0 = (if fst \<omega> = Formula.Agg_Sum then snd \<omega> else EInt 0)"
    define M where "M = flatten_multiset(group_multiset k b f X)"
    have "k \<in> Mapping.keys m" by (simp add: assm keys_is_none_rep)
    then have s_def: "s = foldl (+) y0 (M)" 
      using assms y0_def assm by(auto simp: M_def)
    have "\<And>t m. (t, m) \<in> group_multiset k b f X \<Longrightarrow> t \<in> range EInt"
      using assms by(auto simp: type_restr_def image_subset_iff)
    moreover have "finite (group_multiset k b f X)"
      using assms by simp
    ultimately have "set(M) \<subseteq> range EInt"
      using flatten_multiset_eint by (auto simp:M_def)
    moreover have "y0 \<in> range EInt" using assms
      by(auto simp:y0_def type_restr_def)
    ultimately show "s \<in> range EInt" using s_def
      by(induction M arbitrary: y0) auto
  qed
  then show ?thesis by (auto simp:valid_sumaux_maps_def)
qed

lemma insert_sum_equiv:
  assumes "meval_trm (aggargs_f args) t \<in> range EInt"
  and "snd (aggargs_\<omega> args) \<in> range EInt"
  and "m \<in> valid_sumaux_maps"
  shows "insert_sum args t m = insert_sum_comm args t m"
  using assms plus_plus'_equiv comm_plus' by (auto simp: valid_sumaux_maps_def split:option.splits) 

lemma delete_sum_equiv:
  assumes "meval_trm (aggargs_f args) t \<in> range EInt"
  and "snd (aggargs_\<omega> args) \<in> range EInt"
  and "m \<in> valid_sumaux_maps"
  shows "delete_sum args t m = delete_sum_comm args t m"
  using assms minus_minus'_equiv comm_plus' by (auto simp: valid_sumaux_maps_def split:option.splits) 

lemma insert_sum_comm: "(insert_sum_comm args x \<circ> insert_sum_comm args y) m  = (insert_sum_comm args y \<circ> insert_sum_comm args x) m"
  unfolding insert_sum_comm.simps Let_def
  using comp_fun_commute_plus' comp_fun_commute.fun_left_comm[of plus'] comm_plus'
  by(transfer) (auto split:option.splits)

lemma insert_cnt_comm: "(insert_cnt args x \<circ> insert_cnt args y) m  = (insert_cnt args y \<circ> insert_cnt args x) m"
  unfolding insert_cnt.simps Let_def by(transfer) (auto split:option.splits)


lemma delete_sum_comm: "(delete_sum_comm args x \<circ> delete_sum_comm args y) m  = (delete_sum_comm args y \<circ> delete_sum_comm args x) m"
  unfolding delete_sum_comm.simps Let_def
  using comp_fun_commute_minus' comp_fun_commute.fun_left_comm[of minus'] 
  by(transfer) (auto split:option.splits)

lemma delete_cnt_comm: "(delete_cnt args x \<circ> delete_cnt args y) m  = (delete_cnt args y \<circ> delete_cnt args x) m"
  unfolding delete_cnt.simps Let_def
  by(transfer) (auto split:option.splits)


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

lemma sumaux_finite_set_fold_eq:
  assumes "\<And>a b. a \<in> X \<Longrightarrow> b \<in> valid_sumaux_maps \<Longrightarrow> f a b = g a b"
  and "(\<And>a b. a \<in> X \<Longrightarrow>
          b \<in> valid_sumaux_maps \<Longrightarrow>
          g a b \<in> valid_sumaux_maps)"
  and "finite X"
  and "m \<in> valid_sumaux_maps"
  shows "Finite_Set.fold f m X = Finite_Set.fold g m X"
proof -
  have "fold_graph f m X = fold_graph g m X" using assms fold_graph_closed_eq[of X "{m. (\<forall> k a b. (Mapping.lookup m k = Some (a, b) \<longrightarrow> b \<in> range EInt))}" f g m] 
    by (auto simp:valid_sumaux_maps_def)
  then show ?thesis using assms by(simp add: Finite_Set.fold_def)
qed

lemma fold_eq:
  assumes commute_f: "comp_fun_commute f"
  and comm_f: "\<And>x y. f x y = f y x"
  shows "foldl f y0 xs = fold f xs y0"
  using assms by (induction xs arbitrary: y0) auto

lemma foldl_flatten_multiset:
  assumes finite_m: "finite M"
  assumes commute_f: "comp_fun_commute f"
  and comm_f: "\<And>x y. f x y = f y x"
  shows "foldl f y0 (flatten_multiset M)  = Finite_Set.fold (\<lambda> (t, m) y. ((f t) ^^ (the_enat m)) y) y0 M"
  using assms fold_flatten_multiset fold_eq by (simp add: fold_eq fold_flatten_multiset)

lemma length_fold: "length xs = fold (\<lambda> _ n. n + 1) xs 0"
  by (induction xs) (auto simp:fold_commute_apply)

lemma plus'_iter_one_enat: "((plus') (meval_trm f elem) ^^ the_enat 1) = (plus') (meval_trm f elem)"
  by (simp add: enat_defs(2))

lemma minus'_iter_one_enat: "((minus') (meval_trm f elem) ^^ the_enat 1) = (minus') (meval_trm f elem)"
  by (simp add: enat_defs(2))

lemma other_evals_unchanged:
  assumes elem_group: "drop b elem = k"
  and diff_group: "x \<noteq> meval_trm f elem"
  shows "(x, y) \<in> group_multiset k b f (Set.insert elem X) \<longleftrightarrow> (x, y) \<in> group_multiset k b f X"
proof
  define old_group where [simp]: "old_group = group k b X"
  define new_group where [simp]: "new_group = group k b (X \<union> {elem})"
  have aux1: "\<And>x. x \<noteq> meval_trm f elem \<Longrightarrow> Set.filter (\<lambda>xa. meval_trm f xa = x) new_group = Set.filter (\<lambda>xa. meval_trm f xa = x) old_group" by auto
  assume assm: "(x, y) \<in> group_multiset k b f (Set.insert elem X)"
  then have x_old_eval: "x \<in> meval_trm f ` old_group" using diff_group by auto
  have "y = ecard (Set.filter (\<lambda>xa. meval_trm f xa = x) new_group)" using assm by auto
  then have "y =  ecard (Set.filter (\<lambda>xa. meval_trm f xa = x) old_group)" using aux1 diff_group by auto
  then show "(x, y) \<in>  group_multiset k b f X" using x_old_eval by auto
next
  define old_group where [simp]: "old_group = group k b X"
  define new_group where [simp]: "new_group = group k b (X \<union> {elem})"
  have aux1: "\<And>x. x \<noteq> meval_trm f elem \<Longrightarrow> Set.filter (\<lambda>xa. meval_trm f xa = x) new_group = Set.filter (\<lambda>xa. meval_trm f xa = x) old_group" by auto
  assume assm: "(x, y) \<in>  group_multiset k b f X"
  then have x_old_eval: "x \<in> meval_trm f ` old_group" by auto
  have "y = ecard (Set.filter (\<lambda>xa. meval_trm f xa = x) old_group)" using assm by auto
  then have "y =  ecard (Set.filter (\<lambda>xa. meval_trm f xa = x) new_group)" using aux1 diff_group by auto
  then show "(x, y) \<in> group_multiset k b f (Set.insert elem X)" using x_old_eval by auto
qed

lemma multiset_new_term_insert:
  assumes elem_group: "drop b elem = k"
  and new_term_eval: "Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) (group k b X) = {}"
  shows "group_multiset k b f (Set.insert elem X) = Set.insert (meval_trm f elem, 1) (group_multiset k b f X)"
proof -
  define updated_data where [simp]: "updated_data = X \<union> {elem}"
  define old_group where [simp]: "old_group = group k b X"
  define new_group where [simp]: "new_group = group k b updated_data"
  define old_evals where "old_evals = meval_trm f ` old_group"
  have aux: "Set.filter (\<lambda>x. drop b x = k) (Set.insert elem X) = Set.insert elem old_group" using elem_group by auto
  have aux1: "\<And>x. x \<noteq> meval_trm f elem \<Longrightarrow> Set.filter (\<lambda>xa. meval_trm f xa = x) new_group = Set.filter (\<lambda>xa. meval_trm f xa = x) old_group" by auto
  have aux2: "meval_trm f elem \<notin> old_evals" using new_term_eval by (auto simp: old_evals_def)
  moreover have "Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) new_group = {elem}" using new_term_eval elem_group by auto
  moreover have "ecard {elem} = 1" using enat_1 by (auto simp:ecard_def)
  moreover have "(\<lambda>x. (x, ecard (Set.filter (\<lambda>xa. meval_trm f xa = x) new_group))) ` old_evals = 
                 (\<lambda>x. (x, ecard (Set.filter (\<lambda>xa. meval_trm f xa = x) old_group))) ` old_evals"
    using other_evals_unchanged by (metis (mono_tags, lifting) aux1 aux2 image_cong)
  ultimately show "group_multiset k b f (Set.insert elem X) = Set.insert (meval_trm f elem, 1) (group_multiset k b f X)" using aux
    by(simp add: old_evals_def)
qed

lemma single_term_in_multiset:
  assumes elem_group: "drop b elem = k"
  and single_term_eval: "Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) (group k b X) = {elem}"
  shows "(meval_trm f elem, 1) \<in> group_multiset k b f X"
proof -
  have "elem \<in> group k b X" using single_term_eval elem_group by(simp add:Set.filter_def) blast
  then obtain v' where v'_def: "(meval_trm f elem, v') \<in> group_multiset k b f X" by auto fastforce
  then have "v' = ecard (Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) (group k b X))" by auto
  then have v'_val: "v' = 1" using single_term_eval by(simp add: ecard_def one_enat_def) 
  then show "(meval_trm f elem, 1) \<in> group_multiset k b f X" using v'_def by auto
qed

lemma multiset_single_term_remove:
  assumes elem_group: "drop b elem = k"
  and single_term_eval: "Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) (group k b X) = {elem}"
  shows "group_multiset k b f (X - {elem}) = (group_multiset k b f X) - {(meval_trm f elem, 1)}"
proof (rule set_eqI, rule iffI)
  fix x
  assume x_in_M: "x \<in> group_multiset k b f (X - {elem})"
  then obtain t v where x_def: "x = (t, v)" by fastforce
  have "t \<in> meval_trm f ` group k b (X - {elem})" using x_def x_in_M by auto
  moreover have "elem \<notin> group k b (X - {elem})" by auto
  ultimately have noteq: "t \<noteq> meval_trm f elem" using imageE single_term_eval by auto
  then have "x \<noteq> (meval_trm f elem, 1)" using x_def by force
  moreover have "x \<in> group_multiset k b f X"
    using  x_def by (metis Set.remove_def elem_group insert_Diff_single noteq other_evals_unchanged x_in_M)
  ultimately show "x \<in>  (group_multiset k b f X) - {(meval_trm f elem, 1)}" 
    by auto
next
  fix x
  assume x_in_oldM: "x \<in> (group_multiset k b f X) - {(meval_trm f elem, 1)}"
  then obtain t v where x_def: "x = (t, v)" by (meson surj_pair)
  have "elem \<in> group k b X" using single_term_eval elem_group by(simp add:Set.filter_def) blast
  have "(meval_trm f elem, 1) \<in> group_multiset k b f X" using single_term_in_multiset elem_group single_term_eval by auto
  then have "t \<noteq> meval_trm f elem" using  x_def x_in_oldM by (metis DiffE insertI1 unique_term_multiset)
  then show "x \<in> group_multiset k b f (X - {elem})" using x_def 
    by (metis Set.member_remove Set.remove_def elem_group insert_Diff_single other_evals_unchanged x_in_oldM)
qed

lemma multiset_multiple_term_remove:
  assumes elem_group: "drop b elem = k"
  and old_term_eval: "Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) (group k b X) \<noteq> {elem}"
  and old_val: "(meval_trm f elem, y) \<in> group_multiset k b f X" 
  and inside: "elem \<in> X"
  and finite: "finite X"
  shows "group_multiset k b f (X - {elem}) = 
         Set.insert (meval_trm f elem, y - 1) ((group_multiset k b f X) - {(meval_trm f elem, y)})"
proof (rule set_eqI, rule iffI)
  fix x
  assume x_in_M: "x \<in> group_multiset k b f (X - {elem})"
  then obtain t v where x_def: "x = (t, v)" by fastforce
  define updated_data where "updated_data = X - {elem}"
  define old_group where "old_group = group k b X"
  define new_group where "new_group = group k b updated_data"
  define old_evals where "old_evals = meval_trm f ` old_group"
  have "Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) (group k b X) \<noteq> {}" using inside elem_group by auto
  then obtain elem' where elem'_def:  "elem' \<in> Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) (group k b X) \<and> elem \<noteq> elem'" 
    using old_term_eval by blast
  have group_ins: "new_group = old_group - {elem}" using elem_group by (auto simp: new_group_def old_group_def updated_data_def)
  have y_card: "y = ecard (Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) old_group)" using old_val by (auto simp: old_group_def)
  have "Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) new_group = (Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) old_group) - {elem}"
    using group_ins by fastforce
  then have correct_card: "y - 1 = ecard (Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) new_group)" 
    using y_card by (simp add: ecard_def elem_group enat_defs(2) inside old_group_def)
  obtain v' where v'_def: "(meval_trm f elem, v') \<in> group_multiset k b f updated_data" using elem'_def 
    by(simp add: updated_data_def) (metis (mono_tags) Set.member_filter imageI insert_Diff_single insert_iff)
  then have "v' = y - 1" using correct_card by (auto simp: new_group_def)
  then have aux1: "(meval_trm f elem, y - 1) \<in> group_multiset k b f updated_data" using v'_def by auto
  have "y \<noteq> y - 1" using y_card by (smt (z3) Diff_insert_absorb Optimized_Agg.group_def cancel_comm_monoid_add_class.diff_cancel card.insert card_Diff_singleton_if diff_add_inverse2 ecard_def elem'_def enat.inject enat_defs(2) finite_Diff finite_filter idiff_enat_enat local.finite mk_disjoint_insert old_group_def plus_1_eq_Suc zero_neq_one)
  then have aux2: "(meval_trm f elem, y) \<notin> group_multiset k b f (updated_data)" 
    using unique_term_multiset[of "meval_trm f elem" "y - 1" k b f updated_data y] y_card aux1 by auto
  show "x \<in> Set.insert (meval_trm f elem, y - 1) ((group_multiset k b f X) - {(meval_trm f elem, y)})"
  proof (cases "t = meval_trm f elem")
    case True
    then have "v = y - 1" using x_in_M x_def aux1 using unique_term_multiset updated_data_def by blast
    then show ?thesis using x_def x_in_M True by auto
  next
    case False
    then show ?thesis using other_evals_unchanged by (metis Diff_iff elem_group insertI2 insert_Diff inside old.prod.inject singletonD x_def x_in_M)
  qed
next
  fix x
  assume x_in_oldM: "x \<in> Set.insert (meval_trm f elem, y - 1) ((group_multiset k b f X) - {(meval_trm f elem, y)})"
  then obtain t v where x_def: "x = (t, v)" by force
  define updated_data where "updated_data = X - {elem}"
  define old_group where "old_group = group k b X"
  define new_group where "new_group = group k b updated_data"
  define old_evals where "old_evals = meval_trm f ` old_group"
  have "Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) (group k b X) \<noteq> {}" using inside elem_group by auto
  then obtain elem' where elem'_def:  "elem' \<in> Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) (group k b X) \<and> elem \<noteq> elem'" 
    using old_term_eval by blast
  have group_ins: "new_group = old_group - {elem}" using elem_group by (auto simp: new_group_def old_group_def updated_data_def)
  have y_card: "y = ecard (Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) old_group)" using old_val by (auto simp: old_group_def)
  have "Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) new_group = (Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) old_group) - {elem}"
    using group_ins by fastforce
  then have correct_card: "y - 1 = ecard (Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) new_group)" 
    using y_card by (simp add: ecard_def elem_group enat_defs(2) inside old_group_def)
  obtain v' where v'_def: "(meval_trm f elem, v') \<in> group_multiset k b f updated_data" using elem'_def 
    by(simp add: updated_data_def) (metis (mono_tags) Set.member_filter imageI insert_Diff_single insert_iff)
  then have "v' = y - 1" using correct_card by (auto simp: new_group_def)
  then have aux1: "(meval_trm f elem, y - 1) \<in> group_multiset k b f updated_data" using v'_def by auto
  show "x \<in> group_multiset k b f (X - {elem})" 
  proof (cases "t = meval_trm f elem")
    case True
    then have "v = y - 1" using x_in_oldM x_def by (metis DiffE insertE old.prod.inject old_val singleton_iff unique_term_multiset)
    then show ?thesis using True aux1 x_def updated_data_def by fastforce
  next
    case False
    then show ?thesis by (metis DiffD1 elem_group insertE insert_Diff inside old.prod.inject other_evals_unchanged x_def x_in_oldM)
  qed
qed


lemma multiset_old_term_insert:
  assumes elem_group: "drop b elem = k"
  and old_term_eval: "Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) (group k b X) \<noteq> {}"
  and old_val: "(meval_trm f elem, y) \<in> group_multiset k b f X" 
  and disjoint: "elem \<notin> X"
  and finite: "finite X"
  shows "group_multiset k b f (Set.insert elem X) = 
         Set.insert (meval_trm f elem, y + 1) ((group_multiset k b f X) - {(meval_trm f elem, y)})"
proof (rule set_eqI, rule iffI)
  fix x
  assume x_in_M: "x \<in> group_multiset k b f (Set.insert elem X)"
  then obtain t v where x_def: "x = (t, v)" by fastforce
  define updated_data where [simp]: "updated_data = X \<union> {elem}"
  define old_group where [simp]: "old_group = group k b X"
  define new_group where [simp]: "new_group = group k b updated_data"
  define old_evals where "old_evals = meval_trm f ` old_group"
  have group_ins: "new_group = Set.insert elem old_group" using elem_group by auto
  have y_card: "y = ecard (Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) old_group)" using old_val by auto
  moreover have "Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) (Set.insert elem (Set.filter (\<lambda>x. drop b x = k) X)) =
                 Set.insert elem  (Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) (Set.filter (\<lambda>x. drop b x = k) X))" by auto
  moreover have "elem \<notin> Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) (Set.filter (\<lambda>x. drop b x = k) X)" by (meson Set.member_filter disjoint)
  ultimately have correct_card: "y + 1 = ecard (Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) new_group)" 
    using eSuc_enat plus_1_eSuc(2) group_ins by(auto simp: ecard_def) 
  then have aux1: "(meval_trm f elem, y + 1) \<in> group_multiset k b f (Set.insert elem X)" using group_ins by auto
  have aux2: "(meval_trm f elem, y) \<notin> group_multiset k b f (Set.insert elem X)" 
    using unique_term_multiset[of "meval_trm f elem" "y + 1" k b f updated_data y] aux1 y_card
    by simp (meson ecard_def finite_filter finite valid_maggaux.simps)
  show "x \<in> Set.insert (meval_trm f elem, y + 1) ((group_multiset k b f X) - {(meval_trm f elem, y)})"
  proof (cases "t = meval_trm f elem")
    case True
    then have "v = y + 1" using x_in_M x_def aux1 using unique_term_multiset by blast
    then show ?thesis using x_def x_in_M True by auto
  next
    case False
    then show ?thesis using other_evals_unchanged 
      by (metis DiffI elem_group insertI2 old.prod.inject singleton_iff x_def x_in_M)
  qed
next
  fix x
  assume x_in_oldM: "x \<in> Set.insert (meval_trm f elem, y + 1) ((group_multiset k b f X) - {(meval_trm f elem, y)})"
  then obtain t v where x_def: "x = (t, v)" by force
  define updated_data where [simp]: "updated_data = X \<union> {elem}"
  define old_group where [simp]: "old_group = group k b X"
  define new_group where [simp]: "new_group = group k b updated_data"
  define old_evals where "old_evals = meval_trm f ` old_group"
  have group_ins: "new_group = Set.insert elem old_group" using elem_group by auto
  have y_card: "y = ecard (Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) old_group)" using old_val by auto
  moreover have "Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) (Set.insert elem (Set.filter (\<lambda>x. drop b x = k) X)) =
                 Set.insert elem  (Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) (Set.filter (\<lambda>x. drop b x = k) X))" by auto
  moreover have "elem \<notin> Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) (Set.filter (\<lambda>x. drop b x = k) X)" by (meson Set.member_filter disjoint)
  ultimately have correct_card: "y + 1 = ecard (Set.filter (\<lambda>xa. meval_trm f xa = meval_trm f elem) new_group)" 
    using eSuc_enat plus_1_eSuc(2) group_ins by(auto simp: ecard_def) 
  then have aux1: "(meval_trm f elem, y + 1) \<in> group_multiset k b f (Set.insert elem X)" using group_ins by auto
  show "x \<in> group_multiset k b f (Set.insert elem X)" 
  proof (cases "t = meval_trm f elem")
    case True
    then have "v = y + 1" using x_in_oldM x_def by (metis DiffE insertE old.prod.inject old_val singleton_iff unique_term_multiset)
    then show ?thesis using True aux1 x_def by blast
  next
    case False
    then show ?thesis by (metis DiffD1 elem_group insertE old.prod.inject other_evals_unchanged x_def x_in_oldM)
  qed
qed

lemma length_flatten_multiset: 
  assumes "finite M"
  shows "length (flatten_multiset M) = Finite_Set.fold (\<lambda> (t, m) y. y + (the_enat m)) 0 M"
  using length_fold[of "flatten_multiset M"] fold_flatten_multiset[of M "(\<lambda>_ n. n + 1)" 0]
  by (simp add: fold_flatten_multiset assms comp_fun_commute.intro) (meson add.commute)

lemma length_flatten_multiset':
  assumes "finite X"
  shows "length (flatten_multiset(group_multiset k b f X)) = card (group k b X)"
  using assms
proof(induction X)
  case empty
  then have "group k b {} = {}" by auto
  then show ?case using length_flatten_multiset by auto
next
  case (insert elem F)
  define updated_data where [simp]: "updated_data = Set.insert elem F"
  define group where [simp]: "group = Set.filter (\<lambda>x. drop b x = k) updated_data"
  define M where [simp]: "M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group"
  define old_group where [simp]: "old_group = Set.filter (\<lambda>x. drop b x = k) F"
  define old_M where [simp]: "old_M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) old_group))) ` meval_trm f ` old_group"
  define old_evals where "old_evals = meval_trm f ` old_group"
  interpret comp_fun_commute "\<lambda>(t, m) y. y + the_enat m" by unfold_locales auto
  have both_finite: "finite M \<and> finite old_M" using insert by auto
  show ?case
  proof(cases "drop b elem = k")
    case True
    then have group_elem: "drop b elem = k" by auto
    have "length(flatten_multiset(M)) = length(flatten_multiset(old_M)) + 1" 
    proof(cases "Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) old_group = {}")
      case True
      then have "M = Set.insert (meval_trm f elem, 1) old_M" using multiset_new_term_insert True group_elem by simp
      moreover have "(meval_trm f elem, 1) \<notin> old_M" using True by auto
      ultimately show ?thesis using both_finite length_flatten_multiset by (simp add: enat_defs(2) length_flatten_multiset)
    next
      case False
      then obtain y where y_def: "(meval_trm f elem, y) \<in> old_M" 
        by (smt (z3) Collect_empty_eq Set.filter_def image_eqI old_M_def)
      then obtain xa where xa_def: "y = ecard (Set.filter (\<lambda>x. meval_trm f x = meval_trm f xa) (Set.filter (\<lambda>x. drop b x = drop b xa) F))" 
        by(auto)
      have aux1: "finite (Set.filter (\<lambda>x. meval_trm f x = meval_trm f xa) (Set.filter (\<lambda>x. drop b x = drop b xa) F))" using insert by auto
      then obtain i where i_def: "y = i" by auto
      have finite_remove: "finite (old_M - {(meval_trm f elem, y)})" using both_finite finite_Diff  by (auto simp: Set.remove_def)
      have finite_insert: "finite (Set.insert (meval_trm f elem, y) old_M)" using both_finite by blast
      have M_insert_remove_def: "M = Set.insert (meval_trm f elem, y + 1) (old_M - {(meval_trm f elem, y)})" 
        using multiset_old_term_insert group_elem False y_def insert
        by(simp only: M_def old_M_def group_def old_group_def updated_data_def group_multiset_def Let_def Optimized_Agg.group_def) auto
      then have aux: "length(flatten_multiset(Set.insert (meval_trm f elem, y) old_M)) = length(flatten_multiset(old_M - {(meval_trm f elem, y)})) + i" 
        using both_finite finite_insert finite_remove Finite_Set.comp_fun_commute.fold_insert_remove[of "\<lambda>(t, m) y. y + the_enat m" old_M 0 "(meval_trm f elem, y)"]
        by (simp only: length_flatten_multiset) (metis aux1 comp_fun_commute_axioms ecard_def i_def old.prod.case plus_enat_simps(1) the_enat.simps xa_def)
      have "(meval_trm f elem, y + 1) \<notin> old_M - {(meval_trm f elem, y)}" using y_def by auto
      then show ?thesis using both_finite finite_remove M_insert_remove_def i_def Finite_Set.comp_fun_commute.fold_insert[of "\<lambda>(t, m) y. y + the_enat m" "old_M - {(meval_trm f elem, y)}" "(meval_trm f elem, y + 1)" 0]
        by (smt (z3) add.commute add.left_commute aux1 case_prod_conv comp_fun_commute_axioms ecard_def fold_insert_remove insert_absorb length_flatten_multiset one_enat_def plus_enat_simps(1) the_enat.simps xa_def y_def)
    qed
    moreover have "group = Set.insert elem old_group"
      using True insert by(auto) 
    ultimately show ?thesis using insert by auto
  next
    case False
    then have aux: "Optimized_Agg.group k b (Set.insert elem F) = Optimized_Agg.group k b F" by auto
    then have "group_multiset k b f (Set.insert elem F) = group_multiset k b f F" by auto
    then show ?thesis using aux insert by auto
  qed
qed

lemma foldl_eint_equival: 
  assumes "set X \<subseteq> range EInt"
  and "y0 \<in> range EInt"
  shows "foldl (+) y0 X = foldl (plus') y0 X"
  using assms
proof(induction X arbitrary: y0)
case Nil
  then show ?case by auto
next
  case (Cons a X)
  then show ?case using Cons by auto
qed

lemma finite_set_fold_int:
  assumes "finite M" and "\<And>t m. (t, m) \<in> M \<Longrightarrow> t \<in> range EInt" and "y0 \<in> range EInt"
  shows "(Finite_Set.fold (\<lambda>(t, m). plus' t ^^ the_enat m) y0 M) \<in> range EInt"
  using assms
proof(induction M)
case empty
  then show ?case by auto
next
  case (insert x F)
  then obtain t m where x_def: "x = (t, m)" by (meson surj_pair)
  have "t \<in> range EInt" using assms(2) insert x_def by blast
  moreover have plus'_comp_commute: "comp_fun_commute (\<lambda>(t, m) y. ((plus' t) ^^ (the_enat m)) y)"
    using cmp_comm[of plus'] comp_fun_commute_plus' by(unfold_locales) auto
  ultimately show ?case 
    using x_def iter_plus'_int insert Finite_Set.comp_fun_commute.fold_insert[of "\<lambda>(t, m) y. ((plus' t) ^^ (the_enat m)) y" F x]  by auto metis
qed

lemma valid_insert_sum_unfolded:
  assumes valid_before: "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (SumAux m) X" 
  and disjoint: "elem \<notin> X"
  and type_restr: "type_restr \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> {elem}"
  shows "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> 
        (SumAux (insert_sum \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> elem m)) (X \<union> {elem})"
proof - 
  define updated_map where [simp]: "updated_map = insert_sum \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> elem m"
  define updated_data where [simp]: "updated_data = X \<union> {elem}"
  interpret comp_fun_commute "\<lambda>(t, m) y. y + the_enat m" 
    by(unfold_locales) auto
  have len_commute: "comp_fun_commute (\<lambda>(t, m) y. y + the_enat m)" by unfold_locales
  have plus'_comp_commute: "comp_fun_commute (\<lambda>(t, m) y. ((plus' t) ^^ (the_enat m)) y)"
    using cmp_comm[of plus'] comp_fun_commute_plus' by(unfold_locales) auto
  have valid_finite: "finite updated_data" using valid_before by auto
  have valid_key_invariant: "\<And>k. k \<in> (drop b) ` updated_data \<longleftrightarrow> k \<in> Mapping.keys updated_map"
  proof (rule iffI)
    fix k
    assume assm: "k \<in> (drop b) ` updated_data"
    show "k \<in>  Mapping.keys updated_map"
      using valid_before assm
      by (cases "k \<in> (drop b) ` X") (auto split:option.splits)
  next
    fix k
    assume assm: "k \<in> Mapping.keys updated_map"
    show "k \<in> (drop b) ` updated_data"
      using valid_before assm
      by (cases "k \<in> Mapping.keys m") (auto split:option.splits)
  qed
  have valid_value_invariant: "\<And>k. k \<in> Mapping.keys updated_map \<longrightarrow> Mapping.lookup updated_map k = 
          (let group = Set.filter (\<lambda>x. drop b x = k) updated_data;
           M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group;
           M_list = flatten_multiset M;
           aggtype = fst \<omega>;
           y0 = (if aggtype = Formula.Agg_Sum then snd \<omega> else EInt 0)
          in Some (length M_list, foldl plus y0 M_list))"
  proof rule
    fix k
    define group where [simp]: "group = Set.filter (\<lambda>x. drop b x = k) updated_data"
    define M where [simp]: "M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group"
    define old_group where [simp]: "old_group = Set.filter (\<lambda>x. drop b x = k) X"
    define old_M where [simp]: "old_M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) old_group))) ` meval_trm f ` old_group"
    define old_evals where "old_evals = meval_trm f ` old_group"
    define y0 where [simp]: "y0 = (if fst \<omega>  = Formula.Agg_Sum then snd \<omega> else EInt 0)"
    define term' where [simp]: "term' = meval_trm f elem"
    assume assm: "k \<in> Mapping.keys updated_map"
    have finite: "finite M" using valid_before by auto
    have y0_int: "y0 \<in> range EInt" using type_restr valid_before by (auto simp: type_restr_def)
    have multiset_int: "\<And>t m. (t, m) \<in> M \<Longrightarrow> t \<in> range EInt" using type_restr valid_before by (auto simp: type_restr_def image_subset_iff)  
    then have M_int: "set (flatten_multiset M) \<subseteq> range EInt" using flatten_multiset_eint[of M] finite by auto
    have old_multiset_int: "\<And>t m. (t, m) \<in> old_M \<Longrightarrow> t \<in> range EInt" using type_restr valid_before by (auto simp: type_restr_def image_subset_iff)  
    then have M_old_int: "set (flatten_multiset old_M) \<subseteq> range EInt" using flatten_multiset_eint[of old_M] finite valid_before by auto
    show "Mapping.lookup updated_map k = 
          (let group = Set.filter (\<lambda>x. drop b x = k) updated_data;
           M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group;
           M_list = flatten_multiset M;
           aggtype = fst \<omega>;
           y0 = (if aggtype = Formula.Agg_Sum then snd \<omega> else EInt 0)
          in Some (length M_list, foldl plus y0 M_list))"
    proof (cases "k \<in> Mapping.keys m")
      case False
      then have map_val: "Mapping.lookup updated_map k = Some (1, y0 + term')" 
        using assm valid_before by (auto simp: keys_is_none_rep lookup_update' split:option.splits)
      have "drop b elem = k" 
        using assm False 
        by(auto simp: split:option.splits)
      then have group_single_elem: "group = {elem}" 
        using False valid_before image_iff
        by auto fastforce+
      then have M_single: "M = Set.insert (meval_trm f elem, enat 1) {}"
        using group_single_elem unfolding M_def Set.filter_def ecard_def by (auto cong: conj_cong)
      then have correct_len: "length(flatten_multiset(M)) = 1" 
        using length_flatten_multiset[of M] Finite_Set.comp_fun_commute.fold_insert by simp
      have "foldl plus y0 (flatten_multiset M) = foldl (plus') y0 (flatten_multiset M)"
        using foldl_eint_equival y0_int M_int by auto
      moreover have "foldl (plus') y0 (flatten_multiset M) = Finite_Set.fold (\<lambda>(t, m). (plus') t ^^ the_enat m) y0 M"
        using foldl_flatten_multiset[of M plus' y0] comp_fun_commute_plus' comm_plus'  finite by auto
      moreover have "Finite_Set.fold (\<lambda>(t, m). plus' t ^^ the_enat m) y0 (Set.insert (meval_trm f elem, enat 1) {}) = plus' y0 term'"
        using  Finite_Set.comp_fun_commute.fold_insert[of "\<lambda>(t, m). plus' t ^^ the_enat m"] finite plus'_comp_commute comm_plus' by auto
      moreover have "meval_trm f elem \<in> range EInt" using valid_before multiset_int M_single by blast
      ultimately have "foldl plus y0 (flatten_multiset(M)) = y0 + term'" using M_single y0_int by force
      then show ?thesis using map_val correct_len by simp
    next
      case True
      then have in_map: "k \<in> Mapping.keys m" by auto
      show ?thesis
      proof(cases "drop b elem = k")
        case True
        then have elem_group: "drop b elem = k" by auto
        then have newgroup_def: "group = Set.insert elem old_group" by auto
        have both_finite: "finite old_M \<and> finite M" using valid_before by auto
        obtain len sum where lookup_val: "Mapping.lookup m k = Some(len, sum)" 
          by (metis domIff in_map keys_dom_lookup not_Some_eq prod.exhaust_sel)
        have len_def: "len = length(flatten_multiset(old_M))" using lookup_val in_map valid_before by auto
        moreover have sum_def: "sum = foldl plus y0 (flatten_multiset old_M)" using lookup_val in_map valid_before by auto
        ultimately have "Mapping.lookup updated_map k = Some (len + 1, sum + term')"
          using lookup_val True by(simp add: lookup_update)
        moreover have "length(flatten_multiset(M)) = length(flatten_multiset(old_M)) + 1"
        proof(cases "Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) old_group = {}")
          case True
          then have "M = Set.insert (meval_trm f elem, 1) old_M" using multiset_new_term_insert elem_group by simp
          moreover have "(meval_trm f elem, 1) \<notin> old_M" using True by auto
          ultimately show ?thesis using both_finite by (auto simp:length_flatten_multiset one_enat_def)
        next
          case False
          then obtain y where y_def: "(meval_trm f elem, y) \<in> old_M" 
            by (smt (z3) Collect_empty_eq Set.filter_def image_eqI old_M_def)
          then obtain i where i_def: "y = enat i" 
            by (smt (z3) Pair_inject ecard_def finite_filter image_iff old_M_def old_group_def valid_before valid_maggaux.simps)
          have finite_remove: "finite (old_M - {(meval_trm f elem, y)})" using both_finite finite_Diff  by (auto simp: Set.remove_def)
          have finite_insert: "finite (Set.insert (meval_trm f elem, y) old_M)" using both_finite by blast
          have M_insert_remove_def: "M = Set.insert (meval_trm f elem, y + 1) (old_M - {(meval_trm f elem, y)})" 
            using multiset_old_term_insert[of b elem k f X y] elem_group False y_def valid_before disjoint
            by(simp only: M_def old_M_def group_def old_group_def updated_data_def group_multiset_def Let_def Optimized_Agg.group_def) auto          
          then have aux: "length(flatten_multiset(Set.insert (meval_trm f elem, y) old_M)) = length(flatten_multiset(old_M - {(meval_trm f elem, y)})) + i" 
            using both_finite length_flatten_multiset finite_insert i_def len_commute
            Finite_Set.comp_fun_commute.fold_insert_remove[of "\<lambda>(t, m) y. y + the_enat m" old_M 0 "(meval_trm f elem, y)"] by auto
          have "(meval_trm f elem, y + 1) \<notin> old_M - {(meval_trm f elem, y)}" using y_def by auto
          then show ?thesis using len_commute both_finite finite_remove M_insert_remove_def i_def Finite_Set.comp_fun_commute.fold_insert[of "\<lambda>(t, m) y. y + the_enat m" "old_M - {(meval_trm f elem, y)}" "(meval_trm f elem, y + 1)" 0]
            by (metis (mono_tags, lifting) aux case_prod_conv group_cancel.add1 insert_absorb length_flatten_multiset one_enat_def plus_enat_simps(1) the_enat.simps y_def)
        qed
        
        moreover have "foldl plus y0 (flatten_multiset M) = (foldl plus y0 (flatten_multiset old_M)) + term'"
        proof(cases "Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) old_group = {}")
          case True
          then have "M = Set.insert (meval_trm f elem, 1) old_M" using multiset_new_term_insert elem_group by simp
          moreover have "(meval_trm f elem, 1) \<notin> old_M" using True by auto
          moreover have "foldl (+) y0 (flatten_multiset M) = Finite_Set.fold (\<lambda>(t, m). (plus') t ^^ the_enat m) y0 M"
            using foldl_flatten_multiset foldl_eint_equival M_int y0_int both_finite comm_plus' comp_fun_commute_plus' by(simp)
          moreover have "foldl (+) y0 (flatten_multiset old_M) = Finite_Set.fold (\<lambda>(t, m). (plus') t ^^ the_enat m) y0 old_M" 
            using foldl_flatten_multiset foldl_eint_equival M_old_int y0_int both_finite comm_plus' comp_fun_commute_plus' by simp
          moreover have "(Finite_Set.fold (\<lambda>(t, m). plus' t ^^ the_enat m) y0 old_M) \<in> range EInt" 
            using finite_set_fold_int  both_finite old_multiset_int y0_int by blast
          moreover have "meval_trm f elem \<in> range EInt" using calculation(1) multiset_int by blast
          ultimately show ?thesis
            using  both_finite plus_plus'_equiv plus'_iter_one_enat plus'_comp_commute type_restr comm_plus'
              Finite_Set.comp_fun_commute.fold_insert[of "\<lambda>(t, m). (plus') t ^^ the_enat m"] by simp
        next
          case False
          then obtain y where y_def: "(meval_trm f elem, y) \<in> old_M" 
            by (smt (z3) Collect_empty_eq Set.filter_def image_eqI old_M_def)
          then obtain i where i_def: "y = enat i" 
            by (smt (z3) Pair_inject ecard_def finite_filter image_iff old_M_def old_group_def valid_before valid_maggaux.simps)
          have finite_remove: "finite (old_M - {(meval_trm f elem, y)})" using both_finite finite_Diff  by (auto simp: Set.remove_def)
          have finite_insert: "finite (Set.insert (meval_trm f elem, y) old_M)" using both_finite by blast
          have M_insert_remove_def: "M = Set.insert (meval_trm f elem, y + 1) (old_M - {(meval_trm f elem, y)})" 
            using multiset_old_term_insert[of b elem k f X y] elem_group False y_def valid_before disjoint
            by(simp only: M_def old_M_def group_def old_group_def updated_data_def group_multiset_def Let_def Optimized_Agg.group_def) auto 
          have foldl_plus_plus'_equiv: "foldl (+) y0 (flatten_multiset M) = foldl (plus') y0 (flatten_multiset M)" using foldl_eint_equival M_int y0_int by auto
          have aux1: "foldl (plus') y0 (flatten_multiset (Set.insert (term', y) old_M)) = Finite_Set.fold (\<lambda>(t, m). (plus') t ^^ the_enat m) y0 (Set.insert (term', y) old_M)"
            using foldl_flatten_multiset[of "Set.insert (term', y) old_M" plus' y0] finite_insert comp_fun_commute_plus' comm_plus' by auto
          moreover have foldl_remove_equiv: "foldl plus' y0 (flatten_multiset(old_M - {(term', y)})) = Finite_Set.fold (\<lambda>(t, m). (plus') t ^^ the_enat m) y0 (old_M - {(term', y)})"
            using foldl_flatten_multiset[of "old_M - {(term', y)}" plus' y0] finite_insert comp_fun_commute_plus' comm_plus' by auto
          ultimately have aux: "foldl plus' y0 (flatten_multiset(Set.insert (term', y) old_M)) = ((plus' term') ^^ (the_enat y)) (foldl plus' y0 (flatten_multiset(old_M - {(term', y)})))" 
            using  finite_insert plus'_comp_commute Finite_Set.comp_fun_commute.fold_insert_remove[of "\<lambda>(t, m). (plus') t ^^ the_enat m"] by auto
          moreover have term'_int: "term' \<in> range EInt" using old_multiset_int term'_def y_def by blast
          moreover have "foldl plus' y0 (flatten_multiset(old_M - {(term', y)})) \<in> range EInt" 
            using foldl_remove_equiv by (metis DiffD1 finite_remove finite_set_fold_int old_multiset_int term'_def y0_int)
          ultimately have aux: "foldl plus' y0 (flatten_multiset(old_M - {(term', y)})) = ((minus' term') ^^ (the_enat y)) (foldl plus' y0 (flatten_multiset(old_M)))"
            using plus'_minus'_id by (metis comp_apply insert_absorb term'_def y_def)
          moreover have "(term', y + 1) \<notin> old_M - {(term', y)}" using y_def by auto
          ultimately have "Finite_Set.fold (\<lambda>(t, m). (plus') t ^^ the_enat m) y0 M = ((plus' term') ^^ (i + 1)) (((minus' term') ^^ i) (foldl plus' y0 (flatten_multiset(old_M))))"
            using Finite_Set.comp_fun_commute.fold_insert[of "\<lambda>(t, m). plus' t ^^ the_enat m"] plus'_comp_commute finite_remove i_def
            by(simp only: M_insert_remove_def term'_def) (metis (no_types, lifting) case_prod_conv foldl_remove_equiv one_enat_def plus_enat_simps(1) term'_def the_enat.simps)
          moreover have "foldl (plus') y0 (flatten_multiset(M)) = Finite_Set.fold (\<lambda>(t, m). (plus') t ^^ the_enat m) y0 M"
            using foldl_flatten_multiset[of M plus' y0] both_finite comp_fun_commute_plus' comm_plus' by auto
          ultimately have "foldl (plus') y0 (flatten_multiset(M)) = plus' term' (foldl plus' y0 (flatten_multiset(old_M)))"
            using aux1 by (smt (z3) add.commute aux comp_eq_dest_lhs comp_fun_commute.fold_insert comp_fun_commute.fold_insert_remove finite_remove foldl_remove_equiv funpow_add i_def insert_Diff insert_Diff_single old.prod.case one_enat_def plus'_comp_commute plus'_iter_one_enat term'_def the_enat.simps y_def)
          moreover have "foldl plus' y0 (flatten_multiset(old_M)) \<in> range EInt" 
            by (metis aux1 both_finite finite_set_fold_int insert_absorb old_multiset_int term'_def y0_int y_def)
          ultimately show ?thesis 
            using plus_plus'_equiv foldl_plus_plus'_equiv term'_int M_old_int comm_plus' foldl_eint_equival y0_int by auto
        qed
        ultimately show ?thesis using len_def sum_def by auto
      next
        case False
        then have same_group: "group = old_group" by auto
        then have "M = old_M" by auto
        then have "Mapping.lookup updated_map k = Mapping.lookup m k" 
          using False by (auto split:option.splits simp: lookup_update')
        then show ?thesis using valid_before same_group in_map 
          by auto
      qed
    qed
  qed
  have valid_type_restr: "type_restr \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (Set.insert elem X)"
    using valid_before type_restr by (auto simp:type_restr_def)
  show ?thesis using valid_value_invariant valid_key_invariant valid_finite valid_before valid_type_restr
    by auto
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
      by (cases "k \<in> (drop b) ` X") (auto split:option.splits)
  next
    fix k
    assume assm: "k \<in> Mapping.keys updated_map"
    show "k \<in> (drop b) ` updated_data"
      using valid_before assm
      by (cases "k \<in> Mapping.keys m") (auto split:option.splits)
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
        using assm by (auto simp: keys_is_none_rep lookup_update' split:option.splits)
      have "drop b elem = k" 
        using assm False 
        by(auto  split:option.splits)
      then have group_single_elem: "group = {elem}" 
        using False valid_before image_iff
        by fastforce
      then have "M = Set.insert (meval_trm f elem, enat 1) {}"
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
        then have newgroup_def: "group = Set.insert elem old_group" by auto
        have both_finite: "finite old_M \<and> finite M" using valid_before by auto
        have "length(flatten_multiset(M)) = length(flatten_multiset(old_M)) + 1"
        proof(cases "Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) old_group = {}")
          case True
          then have "M = Set.insert (meval_trm f elem, 1) old_M" using multiset_new_term_insert elem_group by simp
          moreover have "(meval_trm f elem, 1) \<notin> old_M" using True by auto
          ultimately show ?thesis using both_finite by (auto simp:length_flatten_multiset one_enat_def)
        next
          case False
          then obtain y where y_def: "(meval_trm f elem, y) \<in> old_M" 
            by (smt (z3) Collect_empty_eq Set.filter_def image_eqI old_M_def)
          then obtain i where i_def: "y = enat i" 
            by (smt (z3) Pair_inject ecard_def finite_filter image_iff old_M_def old_group_def valid_before valid_maggaux.simps)
          have finite_remove: "finite (old_M - {(meval_trm f elem, y)})" using both_finite finite_Diff  by (auto simp: Set.remove_def)
          have finite_insert: "finite (Set.insert (meval_trm f elem, y) old_M)" using both_finite by blast
          have M_insert_remove_def: "M = Set.insert (meval_trm f elem, y + 1) (old_M - {(meval_trm f elem, y)})" 
            using multiset_old_term_insert[of b elem k f X y] elem_group False y_def valid_before disjoint
            by(simp only: M_def old_M_def group_def old_group_def updated_data_def group_multiset_def Let_def Optimized_Agg.group_def) auto          
          then have aux: "length(flatten_multiset(Set.insert (meval_trm f elem, y) old_M)) = length(flatten_multiset(old_M - {(meval_trm f elem, y)})) + i" 
            using both_finite finite_insert finite_remove 
            Finite_Set.comp_fun_commute.fold_insert_remove[of "\<lambda>(t, m) y. y + the_enat m" old_M 0 "(meval_trm f elem, y)"]
            by (simp only: length_flatten_multiset) (metis comp_fun_commute_axioms i_def old.prod.case the_enat.simps)
          have "(meval_trm f elem, y + 1) \<notin> old_M - {(meval_trm f elem, y)}" using y_def by auto
          then show ?thesis using both_finite finite_remove M_insert_remove_def i_def Finite_Set.comp_fun_commute.fold_insert[of "\<lambda>(t, m) y. y + the_enat m" "old_M - {(meval_trm f elem, y)}" "(meval_trm f elem, y + 1)" 0]
            by (metis (mono_tags, lifting) aux case_prod_conv comp_fun_commute_axioms group_cancel.add1 insert_absorb length_flatten_multiset one_enat_def plus_enat_simps(1) the_enat.simps y_def)
        qed
        moreover obtain len where len_def: "Mapping.lookup m k = Some len \<and> len = length(flatten_multiset(old_M))" 
          using valid_before in_map by auto
        then have "Mapping.lookup updated_map k = Some (len + 1)" by (simp add: elem_group lookup_update)
        ultimately show ?thesis by (simp add: len_def)
      next
        case False
        then have same_group: "group = old_group" by auto
        then have "M = old_M" by auto
        then have "Mapping.lookup updated_map k = Mapping.lookup m k" 
          using False by (auto split:option.splits simp: lookup_update')
        then show ?thesis using valid_before same_group in_map 
          by auto
      qed
    qed
  qed
  show ?thesis using valid_value_invariant valid_key_invariant valid_finite valid_before
    by auto
qed

lemma valid_insert_maggaux_unfolded: 
  "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> aux X \<Longrightarrow>
  finite Y \<Longrightarrow>
  X \<inter> Y = {} \<Longrightarrow>
  type_restr \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> Y \<Longrightarrow>
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
    then have "Finite_Set.fold (insert_cnt args) m (Set.insert x F) = insert_cnt args x (Finite_Set.fold (insert_cnt args) m F)"
      using  Finite_Set.comp_fun_commute.fold_insert[of "insert_cnt args" F x m] insert by auto
    moreover have "CntAux (Finite_Set.fold (insert_cnt args) m F) = CntAux intermediate_map"
      by(auto simp:intermediate_map_def)
    ultimately have "insert_maggaux args (Set.insert x F) (CntAux m) = CntAux (insert_cnt args x intermediate_map)"
      using  Finite_Set.comp_fun_commute.fold_insert[of "insert_cnt args" F x m]
      by auto
    then have "valid_maggaux args (insert_maggaux args (Set.insert x F) (CntAux m)) (X \<union> Set.insert x F)"
      using valid_a
      by auto
    then show ?case
      by (auto simp: args_def)
  qed
next
  case (SumAux m)
  have disjoint: "X \<inter> Y = {}" using SumAux by auto
  have valid_before: "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (SumAux m) X" using SumAux by auto
  have type_restr: "type_restr \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> Y" using SumAux by auto
  have finite_y: "finite Y" using SumAux by auto
  then show ?case using disjoint type_restr valid_before
  proof(induction Y)
    case empty
    then show ?case using SumAux by auto
  next
    case (insert x F)
    define args where "args = \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr>"
    interpret comp_fun_commute "insert_sum_comm args"
      using insert_sum_comm by unfold_locales auto
    obtain intermediate_map where intermediate_map_def: "SumAux intermediate_map = insert_maggaux args F (SumAux m)" by auto
    then have intermediate_map_def': "intermediate_map = Finite_Set.fold (insert_sum args) m F" by auto
    have "X \<inter> F = {}" using insert(4) by auto
    moreover have "type_restr args F" using insert(5)  by (cases "fst \<omega>") (auto simp: args_def type_restr_def) 
    moreover have "valid_maggaux args (SumAux m) X" using valid_before by (auto simp:args_def)
    ultimately have valid_int: "valid_maggaux args (SumAux intermediate_map) (X \<union> F)" using insert(3) by(simp only:intermediate_map_def args_def)
    moreover have "x \<notin> X \<union> F" using insert(2) insert.prems(1) by auto
    moreover have type_x: "type_restr args {x}" using insert(5) by (cases "fst \<omega>") (auto simp: args_def type_restr_def) 
    ultimately have valid_a: "valid_maggaux args (SumAux (insert_sum args x intermediate_map)) (X \<union> F \<union> {x})" 
      using valid_insert_sum_unfolded[of cols n g0 y \<omega> b f intermediate_map "(X \<union> F)" x] by(auto simp: args_def)
    have y0_int: "snd (aggargs_\<omega> args) \<in> range EInt" using insert(5) SumAux.prems(1) by (auto simp: type_restr_def args_def)
    have aux1: "(\<And>a b. a \<in> (Set.insert x F) \<Longrightarrow> b \<in> valid_sumaux_maps \<Longrightarrow> insert_sum args a b = insert_sum_comm args a b)" 
    proof -
      fix a b
      assume a_def: "a \<in> (Set.insert x F)" and b_def: "b \<in> valid_sumaux_maps"
      have "meval_trm (aggargs_f args) a \<in> range EInt" using insert(5) a_def SumAux.prems(1) by(auto simp: type_restr_def  args_def split:option.splits) (auto) 
      then show "insert_sum args a b = insert_sum_comm args a b" using y0_int b_def insert_sum_equiv[of args a b] by auto
    qed
    moreover have aux2: "(\<And>a b. a \<in> (Set.insert x F) \<Longrightarrow> b \<in> valid_sumaux_maps \<Longrightarrow> insert_sum_comm args a b \<in> valid_sumaux_maps)"
    proof -
      fix a b
      assume "a \<in> (Set.insert x F)" and "b \<in> valid_sumaux_maps"
      then show "insert_sum_comm args a b \<in> valid_sumaux_maps"
        using y0_int 
        apply(auto simp: valid_sumaux_maps_def lookup_update' split:option.splits) 
        by fastforce+
    qed
    moreover have valid_m: "m \<in> valid_sumaux_maps" using valid_maggaux_valid_map SumAux(1) by blast
    ultimately have "Finite_Set.fold (insert_sum args) m (Set.insert x F) = Finite_Set.fold (insert_sum_comm args) m (Set.insert x F)"
      using sumaux_finite_set_fold_eq[of "(Set.insert x F)" "insert_sum args" "insert_sum_comm args" m] insert by auto
    moreover have "Finite_Set.fold (insert_sum args) m F = Finite_Set.fold (insert_sum_comm args) m F"
      using sumaux_finite_set_fold_eq[of F "insert_sum args" "insert_sum_comm args" m] using insert aux1 aux2 valid_m by auto
    moreover have "Finite_Set.fold (insert_sum_comm args) m (Set.insert x F) = insert_sum_comm args x (Finite_Set.fold (insert_sum_comm args) m F)"
      using  Finite_Set.comp_fun_commute.fold_insert[of "insert_sum_comm args" F x m] insert by auto
    moreover have "Finite_Set.fold (insert_sum args) m F \<in> valid_sumaux_maps" 
      using valid_maggaux_valid_map[of cols n g0 y \<omega> b f intermediate_map "X \<union> F"] intermediate_map_def' valid_int by(simp only:args_def)
    moreover have "meval_trm (aggargs_f args) x \<in> range EInt" 
      using type_x SumAux.prems(1) by(auto simp: type_restr_def args_def split:option.splits)
    ultimately have "Finite_Set.fold (insert_sum args) m (Set.insert x F) = insert_sum args x (Finite_Set.fold (insert_sum args) m F)"
      using insert_sum_equiv[of args x "Finite_Set.fold (insert_sum args) m F"] y0_int by auto
    then have "insert_maggaux args (Set.insert x F) (SumAux m) = SumAux (insert_sum args x intermediate_map)"
      using intermediate_map_def' by auto
    then have "valid_maggaux args (insert_maggaux args (Set.insert x F) (SumAux m)) (X \<union> Set.insert x F)"
      using valid_a by auto
    then show ?case by (simp only: args_def)
  qed
next
  case (RankAux x) 
  then show ?case sorry
qed

lemma valid_insert_maggaux': "valid_maggaux args aux X \<Longrightarrow> finite Y \<Longrightarrow>
    table (aggargs_b args + aggargs_n args) (aggargs_cols args) Y \<Longrightarrow>
    type_restr args Y \<Longrightarrow> X \<inter> Y = {} \<Longrightarrow>
    valid_maggaux args (insert_maggaux args Y aux) (X \<union> Y)"
  using valid_insert_maggaux_unfolded by (cases args) fast

lemma valid_delete_sum_unfolded:
  assumes valid_before: "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (SumAux m) X" 
  and in_set: "elem \<in> X"
  and type_restr: "type_restr \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> {elem}"
  shows "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> 
        (SumAux (delete_sum \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> elem m)) (X - {elem})"
proof - 
  define updated_map where [simp]: "updated_map = delete_sum \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> elem m"
  define updated_data where [simp]: "updated_data = X - {elem}"
  interpret comp_fun_commute "\<lambda>(t, m) y. y + the_enat m" 
    by(unfold_locales) auto
  have len_commute: "comp_fun_commute (\<lambda>(t, m) y. y + the_enat m)" by unfold_locales
  have plus'_comp_commute: "comp_fun_commute (\<lambda>(t, m) y. ((plus' t) ^^ (the_enat m)) y)"
    using cmp_comm[of plus'] comp_fun_commute_plus' by(unfold_locales) auto
  have valid_finite: "finite updated_data" using valid_before by auto
  have valid_key_invariant: "\<And>k. k \<in> (drop b) ` updated_data \<longleftrightarrow> k \<in> Mapping.keys updated_map"
  proof (rule iffI)
    fix k
    assume assm: "k \<in> (drop b) ` updated_data"
    show "k \<in>  Mapping.keys updated_map"
    proof(cases "drop b elem = k")
      case True
      then show ?thesis using length_flatten_multiset' assm valid_before 
        apply(auto split:option.splits)
        by (smt (z3) Set.member_filter card_eq_Suc_0_ex1 imageI in_set option.inject prod.inject) (smt (z3) Set.member_filter card_eq_Suc_0_ex1 imageI in_set option.inject prod.inject)
    next
      case False
      then have "k \<in> (drop b) ` X" using assm valid_before by auto
      then have "k \<in> Mapping.keys m" using valid_before by auto
      then show ?thesis using False by(auto split:option.splits)
    qed
  next
    fix k
    assume assm: "k \<in> Mapping.keys updated_map"
    then have in_map: "k \<in> Mapping.keys m" by(auto split:option.splits) (smt (z3) Diff_iff is_none_simps(2) keys_delete keys_is_none_rep lookup_update_neq)
    then have in_set: "k \<in> (drop b) ` X" using valid_before by auto
    show "k \<in> (drop b) ` updated_data"
    proof(cases "drop b elem = k")
      case True
      then obtain l s where l_def: "Mapping.lookup m k = Some (l, s)" using in_map by (metis domIff keys_dom_lookup not_None_eq prod.exhaust_sel)
      then have not_1: "l \<noteq> 1" using assm in_map True by(auto split:option.splits)
      then have "l = length (flatten_multiset (group_multiset k b f X))" using l_def valid_before in_map by auto
      then have "card (group k b X) \<noteq> 1" using length_flatten_multiset' valid_before not_1 by auto
      moreover have "group k b X \<noteq> {}" using True assms by auto
      ultimately obtain k' where "k' \<in> group k b X \<and> k' \<noteq> elem" by (metis is_singletonI' is_singleton_altdef)
      then show ?thesis by auto
    next
      case False
      then show ?thesis using in_set by auto
    qed
  qed
  have valid_value_invariant: "\<And>k. k \<in> Mapping.keys updated_map \<longrightarrow> Mapping.lookup updated_map k = 
          (let group = Set.filter (\<lambda>x. drop b x = k) updated_data;
           M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group;
           M_list = flatten_multiset M;
           aggtype = fst \<omega>;
           y0 = (if aggtype = Formula.Agg_Sum then snd \<omega> else EInt 0)
          in Some (length M_list, foldl plus y0 M_list))"
  proof rule
    fix k
    define group where [simp]: "group = Set.filter (\<lambda>x. drop b x = k) updated_data"
    define M where [simp]: "M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group"
    define old_group where [simp]: "old_group = Set.filter (\<lambda>x. drop b x = k) X"
    define old_M where [simp]: "old_M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) old_group))) ` meval_trm f ` old_group"
    define old_evals where "old_evals = meval_trm f ` old_group"
    define y0 where [simp]: "y0 = (if fst \<omega>  = Formula.Agg_Sum then snd \<omega> else EInt 0)"
    define term' where [simp]: "term' = meval_trm f elem"
    assume assm: "k \<in> Mapping.keys updated_map"
    then have in_old: "k \<in> Mapping.keys m" by(auto split:option.splits) (smt (z3) Diff_iff insert_iff is_none_simps(2) keys_delete keys_is_none_rep keys_update)
    have multiset_int: "\<And>t m. (t, m) \<in> M \<Longrightarrow> t \<in> range EInt" using type_restr valid_before by (auto simp: type_restr_def image_subset_iff)  
    then have M_int: "set (flatten_multiset M) \<subseteq> range EInt" using flatten_multiset_eint[of M]  valid_finite by auto
    have old_multiset_int: "\<And>t m. (t, m) \<in> old_M \<Longrightarrow> t \<in> range EInt" using type_restr valid_before by (auto simp: type_restr_def image_subset_iff)  
    then have M_old_int: "set (flatten_multiset old_M) \<subseteq> range EInt" using flatten_multiset_eint[of old_M] finite valid_before by auto
    have y0_int: "y0 \<in> range EInt" using type_restr valid_before by (auto simp: type_restr_def)
    have both_finite: "finite M \<and> finite old_M" using valid_finite by auto
    show "Mapping.lookup updated_map k = 
          (let group = Set.filter (\<lambda>x. drop b x = k) updated_data;
           M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group;
           M_list = flatten_multiset M;
           aggtype = fst \<omega>;
           y0 = (if aggtype = Formula.Agg_Sum then snd \<omega> else EInt 0)
          in Some (length M_list, foldl plus y0 M_list))"
    proof(cases "drop b elem = k")
      case True
      then have grp_def: "group = Set.remove elem old_group" by auto
      have elem_group: "drop b elem = k" using True by auto
      have "length(flatten_multiset(M)) = card group" using length_flatten_multiset' valid_before
        by(simp only: M_def old_M_def group_multiset_def Let_def) (auto)
      moreover have "length(flatten_multiset(old_M)) = card old_group" using length_flatten_multiset' valid_before
        by(simp only: M_def old_M_def group_multiset_def Let_def) (auto)
      ultimately have len: "length(flatten_multiset(M)) = length(flatten_multiset(old_M)) - 1" using grp_def in_set
        by(auto) (smt (z3) One_nat_def Set.member_filter Set.remove_def True card_Diff_singleton finite_filter valid_before valid_maggaux.simps)
      obtain len sum where ls_def: "Mapping.lookup m k = Some (len, sum)" using in_old by (metis domIff keys_dom_lookup not_Some_eq prod.exhaust_sel)
      then have l_def: "len = length(flatten_multiset(old_M))" using valid_before in_old by auto
      have len_not_1: "len \<noteq> 1" using assm ls_def elem_group by(auto split:option.splits)
      have s_def: "sum = foldl plus y0 (flatten_multiset old_M)" using ls_def valid_before in_old by auto
      have "foldl plus y0 (flatten_multiset M) = (foldl plus y0 (flatten_multiset old_M)) - term'"
      proof(cases "Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) old_group = {elem}")
        case True
        have "group_multiset k b f (X - {elem}) = group_multiset k b f X - {(meval_trm f elem, 1)}"
          using multiset_single_term_remove elem_group True by auto
        then have M_remove_def: "M = old_M - {(meval_trm f elem, 1)}" by simp
        have in_M: "(meval_trm f elem, 1) \<in> old_M" using single_term_in_multiset True elem_group by auto
        have fold_eq1: "foldl (+) y0 (flatten_multiset M) = Finite_Set.fold (\<lambda>(t, m). (plus') t ^^ the_enat m) y0 M"
          using foldl_flatten_multiset foldl_eint_equival M_int y0_int both_finite comm_plus' comp_fun_commute_plus' by(simp)
        have fold_eq2: "foldl (+) y0 (flatten_multiset old_M) = Finite_Set.fold (\<lambda>(t, m). (plus') t ^^ the_enat m) y0 old_M" 
          using foldl_flatten_multiset foldl_eint_equival M_old_int y0_int both_finite comm_plus' comp_fun_commute_plus' by simp
        have "Finite_Set.fold (\<lambda>(t, m). plus' t ^^ the_enat m) y0 (Set.insert (meval_trm f elem, 1) (old_M - {(meval_trm f elem, 1)})) =
              (plus' term' ^^ 1) (Finite_Set.fold (\<lambda>(t, m). plus' t ^^ the_enat m) y0 (old_M - {(meval_trm f elem, 1)} - {(meval_trm f elem, 1)}))"
          using Finite_Set.comp_fun_commute.fold_insert_remove[of "\<lambda>(t, m). (plus') t ^^ the_enat m" "old_M - {(meval_trm f elem, 1)}" y0 "(meval_trm f elem, 1)"]
            plus'_comp_commute M_remove_def by(simp) (smt (z3) finite_filter finite_imageI plus'_iter_one_enat valid_before valid_maggaux.elims(2))
        then have aux: "Finite_Set.fold (\<lambda>(t, m). (plus') t ^^ the_enat m) y0 old_M = (plus' term' ^^ 1) (Finite_Set.fold (\<lambda>(t, m). (plus') t ^^ the_enat m) y0 M)"
          using in_M by (metis Diff_idemp M_remove_def insert_Diff)
        moreover have fold_eint: "(Finite_Set.fold (\<lambda>(t, m). (plus') t ^^ the_enat m) y0 M) \<in> range EInt"  using both_finite finite_set_fold_int multiset_int y0_int by blast
        moreover have term'_eint: "term' \<in> range EInt" using in_M old_multiset_int term'_def by blast
        ultimately have "Finite_Set.fold (\<lambda>(t, m). (plus') t ^^ the_enat m) y0 M = (minus' term' ^^ 1) (Finite_Set.fold (\<lambda>(t, m). (plus') t ^^ the_enat m) y0 old_M)"
          using plus'_minus'_id by auto
        then have "Finite_Set.fold (\<lambda>(t, m). (plus') t ^^ the_enat m) y0 M = (Finite_Set.fold (\<lambda>(t, m). (plus') t ^^ the_enat m) y0 old_M) - term'" 
        by (metis fold_eint aux term'_eint iter_plus'_int minus'_iter_one_enat minus_minus'_equiv one_enat_def term'_def the_enat.simps)
        then show ?thesis using fold_eq1 fold_eq2 by auto
      next
        case False
        then obtain y where y_def: "(meval_trm f elem, y) \<in> old_M" using elem_group in_set by fastforce
        then obtain i where i_def: "y = enat i" by (smt (z3) Pair_inject ecard_def finite_filter image_iff old_M_def old_group_def valid_before valid_maggaux.simps)
        have "Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) (Set.filter (\<lambda>x. drop b x = drop b elem) X) \<noteq> {}" using in_set by force
        then have i_not_zero: "i \<noteq> 0" using y_def by(auto) (smt (z3) Set.member_filter card_eq_0_iff ecard_def enat_0_iff(2) finite.emptyI finite.insertI finite_Diff2 finite_filter i_def insert_absorb insert_not_empty updated_data_def valid_finite)
        then obtain i' where i'_def: "i' = i - 1" by auto
        then have i'_aux: "i' + 1 = i" using i_not_zero by auto
        have finite_remove: "finite (old_M - {(meval_trm f elem, y)})" using both_finite finite_Diff  by (auto simp: Set.remove_def)
        have finite_insert: "finite (Set.insert (meval_trm f elem, y) old_M)" using both_finite by blast
        have "finite X" using valid_before by auto
        moreover have "Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) (Optimized_Agg.group k b X) \<noteq> {elem}" using False by auto
        ultimately have "group_multiset k b f (X - {elem}) = Set.insert (meval_trm f elem, y - 1) (group_multiset k b f X - {(meval_trm f elem, y)})"
          using multiset_multiple_term_remove elem_group in_set False y_def by simp
        then have M_insert_remove_def: "M = Set.insert (meval_trm f elem, y - 1) (old_M - {(meval_trm f elem, y)})" 
          by simp
        have foldl_plus_plus'_equiv: "foldl (+) y0 (flatten_multiset M) = foldl (plus') y0 (flatten_multiset M)" using foldl_eint_equival M_int y0_int by auto
        have aux1: "foldl (plus') y0 (flatten_multiset (Set.insert (term', y) old_M)) = Finite_Set.fold (\<lambda>(t, m). (plus') t ^^ the_enat m) y0 (Set.insert (term', y) old_M)"
          using foldl_flatten_multiset[of "Set.insert (term', y) old_M" plus' y0] finite_insert comp_fun_commute_plus' comm_plus' by auto
        moreover have foldl_remove_equiv: "foldl plus' y0 (flatten_multiset(old_M - {(term', y)})) = Finite_Set.fold (\<lambda>(t, m). (plus') t ^^ the_enat m) y0 (old_M - {(term', y)})"
          using foldl_flatten_multiset[of "old_M - {(term', y)}" plus' y0] finite_insert comp_fun_commute_plus' comm_plus' by auto
        ultimately have aux: "foldl plus' y0 (flatten_multiset(Set.insert (term', y) old_M)) = ((plus' term') ^^ (the_enat y)) (foldl plus' y0 (flatten_multiset(old_M - {(term', y)})))" 
          using  finite_insert plus'_comp_commute Finite_Set.comp_fun_commute.fold_insert_remove[of "\<lambda>(t, m). (plus') t ^^ the_enat m"] by auto
        moreover have term'_int: "term' \<in> range EInt" using old_multiset_int term'_def y_def by blast
        moreover have "foldl plus' y0 (flatten_multiset(old_M - {(term', y)})) \<in> range EInt" 
          using foldl_remove_equiv by (metis DiffD1 finite_remove finite_set_fold_int old_multiset_int term'_def y0_int)
        ultimately have aux: "foldl plus' y0 (flatten_multiset(old_M - {(term', y)})) = ((minus' term') ^^ (the_enat y)) (foldl plus' y0 (flatten_multiset(old_M)))"
          using plus'_minus'_id by (metis comp_apply insert_absorb term'_def y_def)
        moreover have "(term', y - 1) \<notin> old_M - {(term', y)}" using y_def by auto
        ultimately have "Finite_Set.fold (\<lambda>(t, m). (plus') t ^^ the_enat m) y0 M = ((plus' term') ^^ i') (((minus' term') ^^ (i' + 1)) (foldl plus' y0 (flatten_multiset(old_M))))"
          using Finite_Set.comp_fun_commute.fold_insert[of "\<lambda>(t, m). plus' t ^^ the_enat m"] plus'_comp_commute finite_remove i_def i'_def i'_aux
          by(simp only: M_insert_remove_def term'_def) (metis (no_types, lifting) foldl_remove_equiv idiff_enat_enat old.prod.case one_enat_def term'_def the_enat.simps)
        moreover have "foldl (plus') y0 (flatten_multiset(M)) = Finite_Set.fold (\<lambda>(t, m). (plus') t ^^ the_enat m) y0 M"
          using foldl_flatten_multiset[of M plus' y0] both_finite comp_fun_commute_plus' comm_plus' by auto
        ultimately have "foldl (plus') y0 (flatten_multiset(M)) = minus' term' (foldl plus' y0 (flatten_multiset(old_M)))"
          using aux1 plus'_minus'_minus by (metis both_finite comp_eq_dest_lhs finite_set_fold_int insert_absorb old_multiset_int term'_def y0_int y_def)
        moreover have "foldl plus' y0 (flatten_multiset(old_M)) \<in> range EInt" 
          by (metis aux1 both_finite finite_set_fold_int insert_absorb old_multiset_int term'_def y0_int y_def)
        ultimately show ?thesis using M_old_int foldl_eint_equival foldl_plus_plus'_equiv minus_minus'_equiv term'_int y0_int by auto
      qed
      moreover have "Mapping.lookup updated_map k = Some (len - 1, sum - term')" using ls_def elem_group len_not_1
        by(auto simp: lookup_update split:option.splits) 
      ultimately show ?thesis using len l_def s_def by auto
    next
      case False
      then have "group = old_group" by auto
      moreover have "Mapping.lookup updated_map k = Mapping.lookup m k" using False 
        by(auto simp: lookup_update' split:option.splits) (metis lookup_update' update_delete)
      ultimately show ?thesis using valid_before in_old by auto
    qed
  qed
  have "type_restr \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> X"
    using valid_before by auto
  then have valid_type_restr: "type_restr \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (X - {elem})"
    using valid_before by (auto simp: type_restr_def) blast+
  show ?thesis using valid_value_invariant valid_key_invariant valid_finite valid_before valid_type_restr
    by auto
qed

lemma valid_delete_cnt_unfolded: 
  assumes valid_before: "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (CntAux m) X" 
  and in_set: "elem \<in> X"
  shows "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> 
        (CntAux (delete_cnt \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> elem m)) (X - {elem})"
proof - 
  define updated_map where [simp]: "updated_map = delete_cnt \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> elem m"
  define updated_data where [simp]: "updated_data = X - {elem}"
  interpret comp_fun_commute "\<lambda>(t, m) y. y + the_enat m" 
    by(unfold_locales) auto
  have valid_finite: "finite updated_data" using valid_before by auto
  have valid_key_invariant: "\<And>k. k \<in> (drop b) ` updated_data \<longleftrightarrow> k \<in> Mapping.keys updated_map"
  proof (rule iffI)
    fix k
    assume assm: "k \<in> (drop b) ` updated_data"
    show "k \<in>  Mapping.keys updated_map"
    proof(cases "drop b elem = k")
      case True
      then show ?thesis using length_flatten_multiset' assm valid_before 
        by(auto split:option.splits) (smt (z3) Set.member_filter card_eq_Suc_0_ex1 in_set is_none_simps(2) keys_is_none_rep option.inject)
    next
      case False
      then show ?thesis 
        using valid_before assm
        by(auto simp only: updated_map_def delete_cnt.simps Let_def updated_data_def split:option.splits) auto
    qed
  next
    fix k
    assume assm: "k \<in> Mapping.keys updated_map"
    show "k \<in> (drop b) ` updated_data"
    proof (cases "k \<in> Mapping.keys m")
      case True
      then show ?thesis using length_flatten_multiset' assm valid_before 
        apply(auto split:option.splits) by(fastforce) (smt (z3) Diff_iff Set.member_filter card_eq_Suc_0_ex1 empty_iff image_iff insert_iff keys_delete option.sel)
    next
      case False
      then show ?thesis using valid_before assm
        by(auto) (smt (verit, best) imageI in_set insertCI insert_Diff insert_absorb keys_delete keys_update option.simps(5))
    qed 
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
    then have in_old: "k \<in> Mapping.keys m" by(auto split:option.splits) (smt (z3) Diff_iff insert_iff is_none_simps(2) keys_delete keys_is_none_rep keys_update)
    show "Mapping.lookup updated_map k = 
          (let group = Set.filter (\<lambda>x. drop b x = k) updated_data;
           M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group
          in Some (length (flatten_multiset M)))"
    proof(cases "drop b elem = k")
      case True
      then have grp_def: "group = Set.remove elem old_group" by auto
      have "length(flatten_multiset(M)) = card group" using length_flatten_multiset' valid_before
        by(simp only: M_def old_M_def group_multiset_def Let_def) (auto)
      moreover have "length(flatten_multiset(old_M)) = card old_group" using length_flatten_multiset' valid_before
        by(simp only: M_def old_M_def group_multiset_def Let_def) (auto)
      ultimately have len: "length(flatten_multiset(M)) = length(flatten_multiset(old_M)) - 1" using grp_def in_set
        by(auto) (smt (z3) One_nat_def Set.member_filter Set.remove_def True card_Diff_singleton finite_filter valid_before valid_maggaux.simps)
      obtain i where i_def: "Mapping.lookup m k = Some i" using in_old by (metis default_def lookup_default)
      then have i_def': "i = length(flatten_multiset(old_M))" using valid_before in_old by auto
      then have "Mapping.lookup updated_map k = Some (i - 1)" using True assm i_def by(auto simp: lookup_update split:option.splits)
      then show ?thesis using len i_def' by(simp) 
    next
      case False
      then have "group = old_group" by auto
      moreover have "Mapping.lookup updated_map k = Mapping.lookup m k" using False 
        by(auto simp: lookup_update' split:option.splits) (metis lookup_update' update_delete)
      ultimately show ?thesis using valid_before in_old by auto
    qed
  qed
  show ?thesis using valid_value_invariant valid_key_invariant valid_finite valid_before
    by auto
qed

lemma valid_delete_maggaux_unfolded: 
  "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> aux X \<Longrightarrow>
  Y \<subseteq> X  \<Longrightarrow>
  valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> 
  (delete_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> Y aux) (X - Y)" 
proof(induction aux)
  case (CntAux m)
  have subset: "Y \<subseteq> X" using CntAux by auto
  have finite_y: "finite Y" using CntAux rev_finite_subset by auto
  then show ?case using subset
  proof(induction Y)
    case empty
    then show ?case using CntAux by auto
  next
    case (insert x F)
    define args where "args = \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr>"
    interpret comp_fun_commute "delete_cnt args"
      using delete_cnt_comm by unfold_locales auto
    obtain intermediate_map where intermediate_map_def: "CntAux intermediate_map = delete_maggaux args F (CntAux m)" by auto
    have valid_a: "valid_maggaux args (CntAux (delete_cnt args x intermediate_map)) (X - F - {x})" 
      using valid_delete_cnt_unfolded[of cols n g0 y \<omega> b f intermediate_map "X - F" x] insert args_def intermediate_map_def by(auto)
    then have "Finite_Set.fold (delete_cnt args) m (Set.insert x F) = delete_cnt args x (Finite_Set.fold (delete_cnt args) m F)"
      using Finite_Set.comp_fun_commute.fold_insert insert by auto
    moreover have "CntAux (Finite_Set.fold (delete_cnt args) m F) = CntAux intermediate_map"
      by(auto simp:intermediate_map_def)
    ultimately have "delete_maggaux args (Set.insert x F) (CntAux m) = CntAux (delete_cnt args x intermediate_map)"
      using  Finite_Set.comp_fun_commute.fold_insert by auto
    then have "valid_maggaux args (delete_maggaux args (Set.insert x F) (CntAux m)) (X - Set.insert x F)"
      using valid_a by (metis Diff_insert)
    then show ?case
      by (auto simp: args_def)
  qed
next
  case (SumAux m)
  have subset: "Y \<subseteq> X" using SumAux by auto
  have valid_before: "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (SumAux m) X" using SumAux by auto
  have finite_y: "finite Y" using subset valid_before finite_subset by auto
  then show ?case using subset 
  proof(induction Y)
    case empty
    then show ?case using SumAux by auto
  next
    case (insert x F)
    define args where "args = \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr>"
    interpret comp_fun_commute "delete_sum_comm args"
      using delete_sum_comm by unfold_locales auto
    have x_in_X: "x \<in> X" using insert by auto
    obtain intermediate_map where intermediate_map_def: "SumAux intermediate_map = delete_maggaux args F (SumAux m)" by auto
    then have intermediate_map_def': "intermediate_map = Finite_Set.fold (delete_sum args) m F" by auto
    have F_subs: "F \<subseteq> X" using insert(4) by auto
    moreover have "valid_maggaux args (SumAux m) X" using valid_before by (auto simp:args_def)
    ultimately have valid_int: "valid_maggaux args (SumAux intermediate_map) (X - F)" using insert(3) by(simp only:intermediate_map_def args_def)
    moreover have "x \<in> X - F" using insert(2) insert.prems(1) by auto
    moreover have type_x: "type_restr args {x}" using valid_before x_in_X apply (cases "fst \<omega>") apply(auto simp: args_def type_restr_def) by blast blast
    ultimately have valid_a: "valid_maggaux args (SumAux (delete_sum args x intermediate_map)) (X - F - {x})" 
      using valid_delete_sum_unfolded using args_def by blast
    have y0_int: "snd (aggargs_\<omega> args) \<in> range EInt" using valid_before SumAux.prems(1) by (auto simp: type_restr_def args_def)
    have aux1: "(\<And>a b. a \<in> (Set.insert x F) \<Longrightarrow> b \<in> valid_sumaux_maps \<Longrightarrow> delete_sum args a b = delete_sum_comm args a b)" 
    proof -
      fix a b
      assume a_def: "a \<in> (Set.insert x F)" and b_def: "b \<in> valid_sumaux_maps"
      have "meval_trm (aggargs_f args) a \<in> range EInt" using valid_before a_def SumAux.prems(1) x_in_X insert(4) F_subs
        apply(auto simp: type_restr_def  args_def split:option.splits) apply(auto) by blast blast
      then show "delete_sum args a b = delete_sum_comm args a b" using y0_int b_def delete_sum_equiv[of args a b] by auto
    qed
    moreover have aux2: "(\<And>a b. a \<in> (Set.insert x F) \<Longrightarrow> b \<in> valid_sumaux_maps \<Longrightarrow> delete_sum_comm args a b \<in> valid_sumaux_maps)"
    proof -
      fix a b
      assume "a \<in> (Set.insert x F)" and "b \<in> valid_sumaux_maps"
      then show "delete_sum_comm args a b \<in> valid_sumaux_maps"
        using y0_int 
        apply(auto simp: valid_sumaux_maps_def lookup_update' split:option.splits) 
        apply (metis Diff_iff insert_iff is_none_simps(2) keys_delete keys_is_none_rep lookup_update' update_delete)
        using minus'.simps(1) apply blast
        apply (metis Diff_iff insertI1 is_none_simps(2) keys_delete keys_is_none_rep lookup_update' update_delete)
        using minus'.simps(1) by blast
    qed
    moreover have valid_m: "m \<in> valid_sumaux_maps" using valid_maggaux_valid_map SumAux(1) by blast
    ultimately have "Finite_Set.fold (delete_sum args) m (Set.insert x F) = Finite_Set.fold (delete_sum_comm args) m (Set.insert x F)"
      using sumaux_finite_set_fold_eq[of "(Set.insert x F)" "delete_sum args" "delete_sum_comm args" m] insert by auto
    moreover have "Finite_Set.fold (delete_sum args) m F = Finite_Set.fold (delete_sum_comm args) m F"
      using sumaux_finite_set_fold_eq[of F "delete_sum args" "delete_sum_comm args" m] using insert aux1 aux2 valid_m by auto
    moreover have "Finite_Set.fold (delete_sum_comm args) m (Set.insert x F) = delete_sum_comm args x (Finite_Set.fold (delete_sum_comm args) m F)"
      using  Finite_Set.comp_fun_commute.fold_insert[of "delete_sum_comm args" F x m] insert by auto
    moreover have "Finite_Set.fold (delete_sum args) m F \<in> valid_sumaux_maps" 
      using valid_maggaux_valid_map[of cols n g0 y \<omega> b f intermediate_map "X - F"] intermediate_map_def' valid_int by(simp only:args_def)
    moreover have "meval_trm (aggargs_f args) x \<in> range EInt" 
      using type_x SumAux.prems(1) by(auto simp: type_restr_def args_def split:option.splits)
    ultimately have "Finite_Set.fold (delete_sum args) m (Set.insert x F) = delete_sum args x (Finite_Set.fold (delete_sum args) m F)"
      using insert_sum_equiv[of args x "Finite_Set.fold (delete_sum args) m F"] y0_int delete_sum_equiv by auto
    then have "delete_maggaux args (Set.insert x F) (SumAux m) = SumAux (delete_sum args x intermediate_map)"
      using intermediate_map_def' by auto
    then have "valid_maggaux args (delete_maggaux args (Set.insert x F) (SumAux m)) (X - Set.insert x F)"
      using valid_a by (metis Diff_insert)
    then show ?case by (simp only: args_def)
  qed
next
  case (RankAux x)
  then show ?case sorry
qed

lemma valid_delete_maggaux': "valid_maggaux args aux X \<Longrightarrow>
    table (aggargs_b args + aggargs_n args) (aggargs_cols args) Y \<Longrightarrow> Y \<subseteq> X \<Longrightarrow>
    valid_maggaux args (delete_maggaux args Y aux) (X - Y)"
  using valid_delete_maggaux_unfolded by (cases args) blast

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
    by auto fastforce
  define group where [simp]: "group = Set.filter (\<lambda>x. meval_trm f x = meval_trm f elem) (Set.filter (\<lambda>x. drop b x = k) X)"
  have "ecard group \<noteq> 0" using finite elem_prop by (auto simp:ecard_def zero_enat_def) 
  then have m_pos: "m > 0 \<and> m \<noteq> \<infinity>" 
    using elem_prop m_prop finite  by (auto simp: ecard_def)
  then have "the_enat m > 0"
    apply(auto simp: the_enat_def)
    using enat_0_iff(1) by blast
  then obtain n where n_def: "the_enat m = Suc n" using gr0_implies_Suc by auto
  have finite_m: "finite M" using finite by auto
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
        using SumAux k_assm True by (simp add: lookup_default_def)
      then have "result = k[y:= Some (eval_agg_op \<omega> M)]" 
        using k_assm True by auto (metis (no_types, lifting) eval_agg_op.simps(4) prod.exhaust_sel)
      then show "result \<in> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> X"
        using k_assm SumAux by (auto simp add: eval_agg_def eval_aggargs_def)
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
        using SumAux apply(auto) using k_assm by presburger+
      then have "Mapping.lookup m k = Some (length (flatten_multiset M), foldl plus (snd \<omega>) (flatten_multiset M))"
        using SumAux True by (simp add: lookup_default_def)
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
        by auto
      have "Mapping.lookup m k = Some (length (flatten_multiset M), foldl plus (EInt 0) (flatten_multiset M))" 
        using SumAux k_assm agg_type by (simp add: lookup_default_def)
      then have "result = k[y:= Some (eval_agg_op \<omega> M)]" 
        using k_assm agg_type not_empty SumAux aux_def
        by(auto split:list.splits)
      then show "result \<in> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> X"
        using k_assm SumAux by (auto simp add: eval_agg_def eval_aggargs_def)
    next
      fix result
      assume "result \<in> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> X"
      then obtain k where k_assm: "(k \<in> (drop b) ` X \<and> result = (let group = Set.filter (\<lambda>x. drop b x = k) X;
                                                                   M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group
                                                                 in k[y:=Some (eval_agg_op \<omega> M)]))" 
        unfolding eval_aggargs_def eval_agg_def empty_table_def using assm_reg by auto
      define group where [simp]: "group = Set.filter (\<lambda>x. drop b x = k) X"
      define M where [simp]: "M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group"
      have "k \<in> Mapping.keys m" using k_assm SumAux by auto
      then have not_empty: "flatten_multiset M \<noteq> []" 
        using flatten_multiset_not_empty[of _ b f m X k] SumAux k_assm False 
        unfolding group_multiset_def Let_def M_def group_def by fastforce
      have key_in_map: "k \<in> Mapping.keys m"
        using SumAux \<open>k \<in> Mapping.keys m\<close> by force
      then have "Mapping.lookup m k = Some (length (flatten_multiset M), foldl plus (EInt 0) (flatten_multiset M))"
        using SumAux False by (simp add: lookup_default_def)
      then have "result = (case Mapping.lookup m k of 
                             Some (cnt, agg_sum) \<Rightarrow> k[y:=Some (EFloat ((double_of_event_data agg_sum) / (double_of_int cnt)))]
                          | None \<Rightarrow> k)"
        using False k_assm not_empty aux_def unfolding M_def group_def 
        by(auto split:list.splits)
      then show  "result \<in> result_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (SumAux m)"
        using key_in_map False by auto
    qed
  qed
qed
next 
  case(RankAux m)
  then show ?case sorry
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
        by (simp add: lookup_default_def)
      then have "result = k[y:= Some (eval_agg_op \<omega> M)]" 
        using k_assm agg_type 
        by (metis eval_agg_op.simps(1) option.simps(5) prod.collapse)
      then show "result \<in> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> X"
        using k_assm CntAux
        by (auto simp add: eval_agg_def eval_aggargs_def)
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
        by (simp add: lookup_default_def)
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

lemma valid_result_maggaux': "valid_maggaux args aux X \<Longrightarrow> result_maggaux args aux = eval_aggargs args X"
  using valid_result_maggaux_unfolded by (cases args) fast

interpretation maggaux valid_maggaux init_maggaux insert_maggaux delete_maggaux result_maggaux
  using valid_init_maggaux' valid_insert_maggaux' valid_delete_maggaux' valid_result_maggaux' by unfold_locales auto

end
