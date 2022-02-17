section \<open>The algorithm\<close>

theory Generic_Join
  imports MFOTL_Monitor_Devel.Table
begin

type_synonym 'a atable = "nat set \<times> 'a table"
type_synonym 'a query = "'a atable set"
type_synonym vertices = "nat set"

type_synonym 'a satable = "nat set \<times> ('a tuple \<Rightarrow> 'a tuple set)"
type_synonym 'a squery = "nat set \<times> nat set \<times> 'a satable set"

subsection \<open>Generic algorithm\<close>

locale getIJ =
  fixes getIJ :: "'a query \<Rightarrow> 'a query \<Rightarrow> vertices \<Rightarrow> vertices \<times> vertices"
  assumes coreProperties: "card V \<ge> 2 \<Longrightarrow> getIJ Q_pos Q_neg V = (I, J) \<Longrightarrow>
    card I \<ge> 1 \<and> card J \<ge> 1 \<and> V = I \<union> J \<and> I \<inter> J = {}"
begin

lemma getIJProperties:
  assumes "card V \<ge> 2"
  assumes "(I, J) = getIJ Q_pos Q_neg V"
  shows "card I \<ge> 1" and "card J \<ge> 1" and "card I < card V" and "card J < card V"
    and "V = I \<union> J" and "I \<inter> J = {}"
proof -
  show "1 \<le> card I" using coreProperties[of V Q_pos Q_neg I J] assms by auto
  show "1 \<le> card J" using coreProperties[of V Q_pos Q_neg I J] assms by auto
  show "card I < card V" by (metis (no_types, lifting) Int_ac(3) One_nat_def Suc_le_lessD assms(1)
        assms(2) card_gt_0_iff card_seteq dual_order.trans getIJ.coreProperties getIJ_axioms leI
        le_iff_inf one_le_numeral sup_ge1 sup_ge2)
  show "card J < card V" by (metis One_nat_def Suc_1 assms(1) assms(2) card_gt_0_iff card_seteq
        getIJ.coreProperties getIJ_axioms leI le_0_eq le_iff_inf nat.simps(3) sup_ge1 sup_ge2)
  show "V = I \<union> J" by (metis assms(1) assms(2) getIJ.coreProperties getIJ_axioms)
  show "I \<inter> J = {}" by (metis assms(1) assms(2) getIJ_axioms getIJ_def)
qed

fun projectTable :: "vertices \<Rightarrow> 'a atable \<Rightarrow> 'a atable" where
  "projectTable V (s, t) = (s \<inter> V, Set.image (restrict V) t)"

fun filterQuery :: "vertices \<Rightarrow> 'a query \<Rightarrow> 'a query" where
  "filterQuery V Q = Set.filter (\<lambda>(s, _). \<not> Set.is_empty (s \<inter> V)) Q"

fun filterQueryNeg :: "vertices \<Rightarrow> 'a query \<Rightarrow> 'a query" where
  "filterQueryNeg V Q = Set.filter (\<lambda>(A, _). A \<subseteq> V) Q"

fun projectQuery :: "vertices \<Rightarrow> 'a query \<Rightarrow> 'a query" where
  "projectQuery V s = Set.image (projectTable V) s"

fun isSameIntersection :: "'a tuple \<Rightarrow> nat set \<Rightarrow> 'a tuple \<Rightarrow> bool" where
  "isSameIntersection t1 s t2 = (restrict s t1 = restrict s t2)"

fun semiJoin :: "'a atable \<Rightarrow> (nat set \<times> 'a tuple) \<Rightarrow> 'a atable" where
  "semiJoin (s, tab) (st, tup) = (s, Set.filter (isSameIntersection tup (s \<inter> st)) tab)"

fun newQuery :: "vertices \<Rightarrow> 'a query \<Rightarrow> (nat set \<times> 'a tuple) \<Rightarrow> 'a query" where
  "newQuery V Q (st, t) = Set.image (\<lambda>tab. projectTable V (semiJoin tab (st, t))) Q"

fun merge_option :: "'a option \<times> 'a option \<Rightarrow> 'a option" where
  "merge_option (None, None) = None"
| "merge_option (Some x, None) = Some x"
| "merge_option (None, Some x) = Some x"
| "merge_option (Some a, Some b) = Some a"
(* Last case shouldn't happen but useful for proof *)

fun merge :: "'a tuple \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple" where
  "merge t1 t2 = map merge_option (zip t1 t2)"

function (sequential) genericJoin :: "vertices \<Rightarrow> 'a query \<Rightarrow> 'a query \<Rightarrow> 'a table" where
  "genericJoin V Q_pos Q_neg =
    (if card V \<le> 1 then
      (\<Inter>(_, x) \<in> Q_pos. x) - (\<Union>(_, x) \<in> Q_neg. x)
    else
      let (I, J) = getIJ Q_pos Q_neg V in
      let Q_I_pos = projectQuery I (filterQuery I Q_pos) in
      let Q_I_neg = filterQueryNeg I Q_neg in
      let R_I = genericJoin I Q_I_pos Q_I_neg in
      let Q_J_neg = Q_neg - Q_I_neg in
      let Q_J_pos = filterQuery J Q_pos in
      let X = {(t, genericJoin J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t)))
        | t . t \<in> R_I} in
      (\<Union>(t, x) \<in> X. {merge xx t | xx . xx \<in> x}))"
by pat_completeness auto
termination
  by (relation "measure (\<lambda>(V, Q_pos, Q_neg). card V)") (auto simp add: getIJProperties)

fun squery_of_query :: "vertices \<Rightarrow> vertices \<Rightarrow> 'a query \<Rightarrow> 'a squery" where
  "squery_of_query I J Q = (I, J, Set.image (\<lambda>(V, T).
    (V, Equiv_Relations.proj (Set.image (\<lambda>t. (restrict (V \<inter> I) t, restrict J t)) T))) Q)"

fun query_of_squery :: "'a squery \<Rightarrow> 'a tuple \<Rightarrow> 'a query" where
  "query_of_squery (I, J, SQ) t = Set.image (\<lambda>(V, f). (V \<inter> J, f (restrict (V \<inter> I) t))) SQ"

lemma squery_correct: "t \<in> R \<Longrightarrow> newQuery J Q (I, t) = query_of_squery (squery_of_query I J
  (Set.image (\<lambda>(V, T). let R' = restrict (V \<inter> I) ` R in
    (V, Set.filter (\<lambda>t. restrict (V \<inter> I) t \<in> R') T)) Q)) t"
  by (auto simp: Equiv_Relations.proj_def image_image intro!: image_cong rev_image_eqI) simp+

lemma genericJoin_code[code]:
  "genericJoin V Q_pos Q_neg =
    (if card V \<le> 1 then
      (\<Inter>(_, x) \<in> Q_pos. x) - (\<Union>(_, x) \<in> Q_neg. x)
    else
      let (I, J) = getIJ Q_pos Q_neg V in
      let Q_I_pos = projectQuery I (filterQuery I Q_pos) in
      let Q_I_neg = filterQueryNeg I Q_neg in
      let R_I = genericJoin I Q_I_pos Q_I_neg in
      (if Set.is_empty R_I then {} else
        let Q_J_neg = Q_neg - Q_I_neg in
        let Q_J_pos = filterQuery J Q_pos in
        let SQ_J_pos = squery_of_query I J (Set.image (\<lambda>(V, T).
          let V' = V \<inter> I; R' = restrict V' ` R_I in
          (V, Set.filter (\<lambda>t. restrict V' t \<in> R') T)) Q_J_pos) in
        let SQ_J_neg = squery_of_query I J (Set.image (\<lambda>(V, T).
          let V' = V \<inter> I; R' = restrict V' ` R_I in
          (V, Set.filter (\<lambda>t. restrict V' t \<in> R') T)) Q_J_neg) in
        let X = {(t, genericJoin J (query_of_squery SQ_J_pos t) (query_of_squery SQ_J_neg t))
          | t . t \<in> R_I} in
        (\<Union>(t, x) \<in> X. {merge xx t | xx . xx \<in> x})))"
  by (subst genericJoin.simps)
     (fastforce simp only: Let_def Set.is_empty_def squery_correct split: if_splits)

fun wrapperGenericJoin :: "'a query \<Rightarrow> 'a query \<Rightarrow> 'a table" where
  "wrapperGenericJoin Q_pos Q_neg =
    (if ((\<exists>(A, X)\<in>Q_pos. Set.is_empty X) \<or> (\<exists>(A, X)\<in>Q_neg. Set.is_empty A \<and> \<not> Set.is_empty X)) then
      {}
    else
      let Q = Set.filter (\<lambda>(A, _). \<not> Set.is_empty A) Q_pos in
      if Set.is_empty Q then
        (\<Inter>(A, X)\<in>Q_pos. X) -  (\<Union>(A, X)\<in>Q_neg. X)
      else
        let V = (\<Union>(A, X)\<in>Q. A) in
        let Qn = Set.filter (\<lambda>(A, _). A \<subseteq> V \<and> card A \<ge> 1) Q_neg in
        genericJoin V Q Qn)"

end

subsection \<open>An instantation\<close>

fun score :: "'a query \<Rightarrow> nat \<Rightarrow> nat" where
  "score Q i = sum (\<lambda>(_, x). card x) (Set.filter (\<lambda>(sign, _). i \<in> sign) Q)"

fun arg_max_list :: "('a \<Rightarrow> ('b::linorder)) \<Rightarrow> 'a list \<Rightarrow> 'a" where
  "arg_max_list f [x] = x"
| "arg_max_list f (x#y#zs) = (let m = arg_max_list f (y#zs) in if f m \<le> f x then x else m)"

lemma arg_max_list_element:
  assumes "length l \<ge> 1" shows "arg_max_list f l \<in> set l"
  using assms
  by (induction l rule: induct_list012) (auto simp: Let_def)

fun max_getIJ :: "'a query \<Rightarrow> 'a query \<Rightarrow> vertices \<Rightarrow> vertices \<times> vertices" where
  "max_getIJ Q_pos Q_neg V = (let x = arg_max_list (score Q_pos) (sorted_list_of_set V) in ({x}, V - {x}))"

lemma max_getIJ_coreProperties:
  assumes "card V \<ge> 2"
  assumes "(I, J) = max_getIJ Q_pos Q_neg V"
  shows "card I \<ge> 1 \<and> card J \<ge> 1 \<and> V = I \<union> J \<and> I \<inter> J = {}"
proof -
  have "finite V" using assms(1) card.infinite by force
  define l where "l = sorted_list_of_set V"
  then have "length l \<ge> 1" by (metis Suc_1 Suc_le_lessD \<open>finite V\<close> assms(1) distinct_card
        distinct_sorted_list_of_set less_imp_le set_sorted_list_of_set)
  show ?thesis
  proof -
    define x where "x = arg_max_list (score Q_pos) l"
    then have "x \<in> (set l)" using \<open>1 \<le> length l\<close> arg_max_list_element by blast
    then have "x \<in> V" by (simp add: \<open>finite V\<close> l_def)
    moreover have "(I, J) = ({x}, V - {x})" 
    proof -
      have "(I, J) =  (let x = arg_max_list (score Q_pos) (sorted_list_of_set V) in ({x}, V - {x}))" by (simp add: assms(2))
      then show ?thesis by (metis l_def x_def)
    qed
    then show ?thesis using Pair_inject \<open>finite V\<close> assms(1) calculation by auto
  qed
qed

global_interpretation New_max: getIJ max_getIJ
  defines New_max_getIJ_genericJoin = "New_max.genericJoin"
  and New_max_getIJ_wrapperGenericJoin = "New_max.wrapperGenericJoin"
  by standard (metis max_getIJ_coreProperties)

end
