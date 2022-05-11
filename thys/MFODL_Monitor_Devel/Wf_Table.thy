theory Wf_Table
  imports "Containers.Containers" "HOL-Library.Code_Target_Nat" "Optimized_Join" Cluster Mapping_Code
begin

lemma table_restrict[simp]: "table n (A \<inter> {..<n}) X \<longleftrightarrow> table n A X"
  by (auto simp: table_def wf_tuple_def)

(* permute *)

fun fv_vars_rec :: "nat \<Rightarrow> nat option list \<Rightarrow> nat set" where
  "fv_vars_rec n [] = {}"
| "fv_vars_rec n (x # xs) = fv_vars_rec (Suc n) xs \<union> (case x of Some _ \<Rightarrow> {n} | _ \<Rightarrow> {})"

definition "fv_vars = fv_vars_rec 0"

definition "permute ns = (\<lambda>t. map (map_option (\<lambda>n. the (t ! n))) ns)"

lemma fv_vars_rec_set: "x \<in> fv_vars_rec n ns \<Longrightarrow> x \<in> {n..<n + length ns}"
  by (induction ns arbitrary: n) (fastforce split: option.splits)+

lemma fv_vars_rec_iff: "x \<le> i \<Longrightarrow> i - x < length ns \<Longrightarrow> ns ! (i - x) = None \<longleftrightarrow> i \<notin> fv_vars_rec x ns"
proof (induction ns arbitrary: x)
  case (Cons n ns)
  then show ?case
  proof (cases "i - x")
    case (Suc j)
    have prems: "Suc x \<le> i" "i - Suc x < length ns"
      using Cons(2,3) Suc
      by auto
    have j_def: "j = i - Suc x"
      using Suc
      by auto
    show ?thesis
      using Suc
      by (auto simp: Cons(1)[OF prems, folded j_def] split: option.splits)
  qed (auto split: option.splits dest: fv_vars_rec_set)
qed auto

lemma wf_tuple_permute:
  assumes "wf_tuple n A t"
  shows "wf_tuple (length ns) (fv_vars ns) (permute ns t)"
  using fv_vars_rec_iff[where ?x=0]
  by (auto simp: wf_tuple_def permute_def fv_vars_def)

(* wf_table *)

typedef 'a wf_table = "{(n :: nat, A :: nat set, T :: 'a option list set) |
  n A T. table n A T}"
  by (rule exI[of _ "(0, {}, {})"]) (auto simp: table_def)

setup_lifting type_definition_wf_table

lift_definition wf_table_sig :: "'a wf_table \<Rightarrow> (nat \<times> nat set)" is "\<lambda>(n, A, T). (n, A)" .

lift_definition wf_table_set :: "'a wf_table \<Rightarrow> 'a option list set" is "\<lambda>(n, A, T). T" .

lemma wf_table_eqI:
  assumes "wf_table_sig t = wf_table_sig t'" "wf_table_set t = wf_table_set t'"
  shows "t = t'"
  using assms
  by transfer auto

lift_definition wf_table_of_set :: "nat \<Rightarrow> nat set \<Rightarrow> 'a option list set \<Rightarrow> 'a wf_table" is
  "\<lambda>n A T. (n, A, Set.filter (wf_tuple n A) T)"
  by (auto simp: Let_def table_def)

lemma wf_table_sig_of_set: "wf_table_sig (wf_table_of_set n A T) = (n, A)"
  by transfer auto

lemma wf_table_set_of_set: "wf_table_set (wf_table_of_set n A T) = Set.filter (wf_tuple n A) T"
  by transfer auto

lemma wf_table_set_table: "wf_table_sig t = (n, A) \<Longrightarrow> table n A (wf_table_set t)"
  by transfer auto

lift_definition wf_table_union :: "'a wf_table \<Rightarrow> 'a wf_table \<Rightarrow> 'a wf_table" is
  "\<lambda>(n, A, T) (n', A', T'). if n = n' \<and> A = A' then (n, A, T \<union> T') else (n, A, T)"
  by auto

lemma wf_table_sig_union: "wf_table_sig (wf_table_union t1 t2) = wf_table_sig t1"
  by transfer (auto split: if_splits)

lemma wf_table_set_union: "wf_table_sig t1 = wf_table_sig t2 \<Longrightarrow> wf_table_set (wf_table_union t1 t2) = wf_table_set t1 \<union> wf_table_set t2"
  by transfer auto

lemma wf_table_set_union_deg: "\<not>wf_table_sig t1 = wf_table_sig t2 \<Longrightarrow> wf_table_set (wf_table_union t1 t2) = wf_table_set t1"
  by transfer (auto split: if_splits)

lemma wf_table_set_union': "wf_table_set (wf_table_union t1 t2) =
  (if wf_table_sig t1 = wf_table_sig t2 then wf_table_set t1 \<union> wf_table_set t2 else wf_table_set t1)"
  using wf_table_set_union wf_table_set_union_deg
  by (fastforce split: if_splits)

lift_definition wf_table_join :: "'a wf_table \<Rightarrow> 'a wf_table \<Rightarrow> 'a wf_table" is
  "\<lambda>(n, A, T) (n', A', T'). if n = n' then (n, A \<union> A', bin_join n A T True A' T') else (n, A, T)"
  by (fastforce simp del: bin_join.simps simp: bin_join_table intro: join_table)

lemma wf_table_sig_join: "wf_table_sig (wf_table_join t1 t2) = (case wf_table_sig t1 of (n, A) \<Rightarrow> case wf_table_sig t2 of (n', A') \<Rightarrow>
  if n = n' then (n, A \<union> A') else wf_table_sig t1)"
  by transfer auto

lemma wf_table_set_join: "wf_table_sig t1 = (n, A) \<Longrightarrow> wf_table_sig t2 = (n', A') \<Longrightarrow> n = n' \<Longrightarrow>
  wf_table_set (wf_table_join t1 t2) = join (wf_table_set t1) True (wf_table_set t2)"
  by transfer (auto simp del: bin_join.simps simp: bin_join_table)

lemma wf_table_set_join_deg: "wf_table_sig t1 = (n, A) \<Longrightarrow> wf_table_sig t2 = (n', A') \<Longrightarrow> \<not>n = n' \<Longrightarrow>
  wf_table_set (wf_table_join t1 t2) = wf_table_set t1"
  by transfer auto

lemma wf_table_set_join': "wf_table_set (wf_table_join t1 t2) = (case wf_table_sig t1 of (n, A) \<Rightarrow> case wf_table_sig t2 of (n', A') \<Rightarrow>
  if n = n' then join (wf_table_set t1) True (wf_table_set t2) else wf_table_set t1)"
  using wf_table_set_join wf_table_set_join_deg
  by (fastforce split: if_splits)

lift_definition wf_table_antijoin :: "'a wf_table \<Rightarrow> 'a wf_table \<Rightarrow> 'a wf_table" is
  "\<lambda>(n, A, T) (n', A', T'). if n = n' \<and> A' \<subseteq> A then (n, A \<union> A', bin_join n A T False A' T') else (n, A, T)"
  by (fastforce simp del: bin_join.simps simp: bin_join_table intro: join_table)

lemma wf_table_sig_antijoin: "wf_table_sig (wf_table_antijoin t1 t2) = wf_table_sig t1"
  by transfer (auto split: if_splits)

lemma wf_table_set_antijoin: "wf_table_sig t1 = (n, A) \<Longrightarrow> wf_table_sig t2 = (n, A') \<Longrightarrow> A' \<subseteq> A \<Longrightarrow>
  wf_table_set (wf_table_antijoin t1 t2) = join (wf_table_set t1) False (wf_table_set t2)"
  by transfer (auto simp del: bin_join.simps simp: bin_join_table)

lemma wf_table_set_antijoin_deg: "wf_table_sig t1 = (n, A) \<Longrightarrow> wf_table_sig t2 = (n', A') \<Longrightarrow> \<not>(n = n' \<and> A' \<subseteq> A) \<Longrightarrow>
  wf_table_set (wf_table_antijoin t1 t2) = wf_table_set t1"
  by transfer (auto split: if_splits)

lemma wf_table_set_antijoin': "wf_table_set (wf_table_antijoin t1 t2) = (case wf_table_sig t1 of (n, A) \<Rightarrow> case wf_table_sig t2 of (n', A') \<Rightarrow>
  if n = n' \<and> A' \<subseteq> A then join (wf_table_set t1) False (wf_table_set t2) else wf_table_set t1)"
  using wf_table_set_antijoin wf_table_set_antijoin_deg
  by (fastforce split: if_splits)

lift_definition wf_table_permute :: "nat option list \<Rightarrow> 'a wf_table \<Rightarrow> 'a wf_table" is
  "\<lambda>ns (n, A, T). (length ns, fv_vars ns, permute ns ` T)"
  using fv_vars_rec_set[where ?n=0, folded fv_vars_def]
  by (fastforce simp: table_def intro: wf_tuple_permute)

lemma wf_table_sig_permute: "wf_table_sig (wf_table_permute ns t) = (length ns, fv_vars ns)"
  by transfer auto

lemma wf_table_set_permute: "wf_table_set (wf_table_permute ns t) = permute ns ` wf_table_set t"
  by transfer auto

(* wf_idx *)

typedef 'a wf_idx = "{(n :: nat, A :: nat set, I :: nat set, T :: ('a option list, 'a option list set) mapping) |
  n A I T. I \<subseteq> A \<and> (\<forall>x Y. Mapping.lookup T x = Some Y \<longrightarrow> table n A Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict I z))}"
  by (rule exI[of _ "(0, {}, {}, Mapping.empty)"]) (auto simp: table_def)

setup_lifting type_definition_wf_idx

lift_definition wf_idx_sig :: "'a wf_idx \<Rightarrow> (nat \<times> nat set)" is "\<lambda>(n, A, I, T). (n, A)" .

lift_definition wf_idx_cols :: "'a wf_idx \<Rightarrow> nat set" is "\<lambda>(n, A, I, T). I" .

lift_definition wf_idx_set :: "'a wf_idx \<Rightarrow> 'a option list set" is "\<lambda>(n, A, I, T). set_of_idx T" .

(* conversion wf_table \<longleftrightarrow> idx *)

definition "idx_create T X = cluster (Some \<circ> restrict X) T"

lemma set_of_idx_cluster: "set_of_idx (cluster (Some \<circ> f) X) = X"
  by transfer (auto simp: ran_def)

lemma idx_create:
  assumes "table n C T"
  shows "set_of_idx (idx_create T X) = T"
    "\<And>x Y. Mapping.lookup (idx_create T X) x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict X z)"
proof -
  show "set_of_idx (idx_create T X) = T"
    by (auto simp: idx_create_def set_of_idx_cluster)
  show "\<And>x Y. Mapping.lookup (idx_create T X) x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict X z)"
    using assms
    unfolding idx_create_def table_def
    by (transfer fixing: n C X) (auto simp: Map_To_Mapping.map_apply_def split: if_splits)
qed

lift_definition wf_idx_of_table :: "nat set \<Rightarrow> 'a wf_table \<Rightarrow> 'a wf_idx" is
  "\<lambda>I (n, A, T). let I' = I \<inter> A in (n, A, I', idx_create T I')"
  by (auto simp: Let_def idx_create)

lemma wf_idx_sig_of_table[simp]: "wf_idx_sig (wf_idx_of_table I t) = wf_table_sig t"
  by transfer (auto simp: Let_def)

lemma wf_idx_set_of_table[simp]: "wf_idx_set (wf_idx_of_table I t) = wf_table_set t"
  by transfer (auto simp: Let_def idx_create(1))

lift_definition wf_table_of_idx :: "'a wf_idx \<Rightarrow> 'a wf_table" is
  "\<lambda>(n, A, I, T). (n, A, set_of_idx T)"
  by transfer (auto simp: Map_To_Mapping.map_apply_def ran_def table_def)

lemma wf_table_sig_of_idx[simp]: "wf_table_sig (wf_table_of_idx t) = wf_idx_sig t"
  by transfer auto

lemma wf_table_set_of_idx[simp]: "wf_table_set (wf_table_of_idx t) = wf_idx_set t"
  by transfer auto

lemma table_filter: "table n C (Set.filter (wf_tuple n C) T)"
  by (auto simp: table_def)

lift_definition wf_idx_of_set :: "nat \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> 'a option list set \<Rightarrow> 'a wf_idx" is
  "\<lambda>n A I T. let A' = A ; I' = I \<inter> A' in (n, A', I', idx_create (Set.filter (wf_tuple n A') T) I')"
  by (auto simp: Let_def idx_create[OF table_filter])

lemma wf_idx_sig_of_set: "wf_idx_sig (wf_idx_of_set n A I T) = (n, A )"
  by transfer (auto simp: Let_def)

lemma wf_idx_set_of_set: "wf_idx_set (wf_idx_of_set n A I T) = Set.filter (wf_tuple n A) T"
  by transfer (auto simp: Let_def idx_create[OF table_filter])

definition idx_reindex :: "nat set \<Rightarrow> nat set \<Rightarrow> ('a option list, 'a option list set) mapping \<Rightarrow>
  ('a option list, 'a option list set) mapping" where
  "idx_reindex I'' I T = (if I = I'' then T else idx_create (set_of_idx T) I'')"

lemma idx_reindex:
  assumes "\<And>x Y. Mapping.lookup T x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict I z)"
  shows "set_of_idx (idx_reindex I' I T) = set_of_idx T"
    "\<And>x Y. Mapping.lookup (idx_reindex I' I T) x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict I' z)"
proof -
  have table_set_of_idx: "table n C (set_of_idx T)"
    using assms
    by transfer (auto simp: Map_To_Mapping.map_apply_def table_def ran_def)
  show "set_of_idx (idx_reindex I' I T) = set_of_idx T"
    by (auto simp: idx_reindex_def idx_create(1)[OF table_set_of_idx])
  show "\<And>x Y. Mapping.lookup (idx_reindex I' I T) x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict I' z)"
    using assms
    by (auto simp: idx_reindex_def dest: idx_create(2)[OF table_set_of_idx] split: if_splits)
qed

lift_definition wf_idx_reindex :: "nat set \<Rightarrow> 'a wf_idx \<Rightarrow> 'a wf_idx" is
  "\<lambda>I' (n, A, I, T). let I'' = I \<inter> I' in (n, A, I'', idx_reindex I'' I T)"
  using idx_reindex
  by (auto simp: Let_def) blast+

lemma wf_idx_sig_reindex: "wf_idx_sig (wf_idx_reindex I T) = wf_idx_sig T"
  by transfer (auto simp: Let_def)

lemma wf_idx_set_reindex: "wf_idx_set (wf_idx_reindex I T) = wf_idx_set T"
  apply transfer
  using idx_reindex
  by (auto simp: Let_def) blast+

definition "idx_union = Mapping.combine (\<union>)"

lemma idx_union:
  assumes "\<And>x Y. Mapping.lookup T x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict X z)"
    "\<And>x Y. Mapping.lookup T' x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict X z)"
  shows "set_of_idx (idx_union T T') = set_of_idx T \<union> set_of_idx T'"
    "\<And>x Y. Mapping.lookup (idx_union T T') x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict X z)"
proof -
  show "set_of_idx (idx_union T T') = set_of_idx T \<union> set_of_idx T'"
    unfolding idx_union_def
    apply (transfer)
    apply (auto simp: ran_def combine_options_def split: option.splits)
      apply (metis UnE option.exhaust)
     apply (metis IntE Un_Int_eq(1) option.discI option.sel)
    apply (metis IntE Un_Int_eq(2) option.discI option.sel)
    done
  show "\<And>x Y. Mapping.lookup (idx_union T T') x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict X z)"
    using assms
    unfolding idx_union_def
    by (transfer fixing: n C X) (auto simp: Map_To_Mapping.map_apply_def combine_options_def split: option.splits)
qed

lemma idx_union_reindex:
  assumes "\<And>x Y. Mapping.lookup T x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict X z)"
    "\<And>x Y. Mapping.lookup T' x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict X' z)"
  shows "set_of_idx (idx_union (idx_reindex I X T) (idx_reindex I X' T')) = set_of_idx T \<union> set_of_idx T'"
    "\<And>x Y. Mapping.lookup (idx_union (idx_reindex I X T) (idx_reindex I X' T')) x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict I z)"
proof -
  note I1 = idx_reindex[where ?T=T and ?I=X, OF assms(1)]
  note I2 = idx_reindex[where ?T=T' and ?I=X', OF assms(2)]
  show "set_of_idx (idx_union (idx_reindex I X T) (idx_reindex I X' T')) = set_of_idx T \<union> set_of_idx T'"
    "\<And>x Y. Mapping.lookup (idx_union (idx_reindex I X T) (idx_reindex I X' T')) x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict I z)"
    using idx_union[where ?T="idx_reindex I X T" and ?T'="idx_reindex I X' T'", OF I1(2) I2(2)] I1(1) I2(1)
    by auto
qed

lift_definition wf_idx_union :: "'a wf_idx \<Rightarrow> 'a wf_idx \<Rightarrow> 'a wf_idx" is
  "\<lambda>(n, A, I, T) (n', A', I', T'). if n = n' \<and> A = A' then
      (let I'' = I \<inter> I'; i = idx_reindex I'' I T; i' = (idx_reindex I'' I' T') in (n, A, I'', idx_union i i'))
    else (n, A, I, T)"
  using idx_reindex(2) idx_union_reindex(2)
  by (auto simp: Let_def) blast+

lemma wf_idx_sig_union: "wf_idx_sig (wf_idx_union t1 t2) = wf_idx_sig t1"
  by transfer (auto simp: Let_def split: if_splits)

lemma wf_idx_set_union: "wf_idx_sig t1 = wf_idx_sig t2 \<Longrightarrow> wf_idx_set (wf_idx_union t1 t2) = wf_idx_set t1 \<union> wf_idx_set t2"
  apply transfer
  using idx_union_reindex(1)
  by (auto simp: Let_def split: prod.splits if_splits) blast+

lemma wf_idx_set_union_deg: "\<not>wf_idx_sig t1 = wf_idx_sig t2 \<Longrightarrow> wf_idx_set (wf_idx_union t1 t2) = wf_idx_set t1"
  by transfer (auto split: if_splits)

lemma wf_idx_set_union': "wf_idx_set (wf_idx_union t1 t2) =
  (if wf_idx_sig t1 = wf_idx_sig t2 then wf_idx_set t1 \<union> wf_idx_set t2 else wf_idx_set t1)"
  using wf_idx_set_union wf_idx_set_union_deg
  by (fastforce split: if_splits)

definition "idx_join n A T A' T' = Mapping.filter (\<lambda>_ T. T \<noteq> {}) (mapping_join (\<lambda>T T'. bin_join n A T True A' T') T T')"

lemma these_iff: "z \<in> Option.these (f ` (X \<times> Y)) \<longleftrightarrow> (\<exists>x \<in> X. \<exists>y \<in> Y. f (x, y) = Some z)"
  by (force simp: Option.these_def)

lemma idx_join:
  fixes T T' :: "('a option list, 'a option list set) mapping"
  assumes "A \<subseteq> B" "A \<subseteq> C"
    "\<And>x Y. Mapping.lookup T x = Some Y \<Longrightarrow> table n B Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A z)"
    "\<And>x Y. Mapping.lookup T' x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A z)"
  shows "set_of_idx (idx_join n B T C T') = join (set_of_idx T) True (set_of_idx T')"
    "\<And>x Y. Mapping.lookup (idx_join n B T C T') x = Some Y \<Longrightarrow> table n (B \<union> C) Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A z)"
proof -
  show "set_of_idx (idx_join n B T C T') = join (set_of_idx T) True (set_of_idx T')"
    using assms(3,4)
    unfolding idx_join_def
    apply (transfer fixing: n A B C)
  proof (rule set_eqI, rule iffI)
    fix T T' :: "'a option list \<Rightarrow> 'a option list set option"
    fix x
    assume restrict: "\<And>x Y. Map_To_Mapping.map_apply T x = Some Y \<Longrightarrow> table n B Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A z)"
      "\<And>x Y. Map_To_Mapping.map_apply T' x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A z)"
    assume "x \<in> \<Union> (ran (\<lambda>k. case case T k of None \<Rightarrow> None | Some y \<Rightarrow>
      (case T' k of None \<Rightarrow> None | Some y' \<Rightarrow> Some (bin_join n B y True C y')) of
      None \<Rightarrow> None | Some v \<Rightarrow> if v \<noteq> {} then Some v else None))"
    then obtain a Y Y' where a_def: "T a = Some Y" "T' a = Some Y'" "x \<in> bin_join n B Y True C Y'"
      by (auto simp: ran_def split: option.splits if_splits)
    then show "x \<in> join (\<Union> (ran T)) True (\<Union> (ran T'))"
      using restrict
      by (auto simp: Map_To_Mapping.map_apply_def ran_def Table.join_def these_iff bin_join_table simp del: bin_join.simps)
  next
    fix T T' :: "'a option list \<Rightarrow> 'a option list set option"
    fix x
    assume restrict: "\<And>x Y. Map_To_Mapping.map_apply T x = Some Y \<Longrightarrow> table n B Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A z)"
      "\<And>x Y. Map_To_Mapping.map_apply T' x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A z)"
    assume "x \<in> join (\<Union> (ran T)) True (\<Union> (ran T'))"
    then obtain a a' Y Y' where a_def: "T a = Some Y" "T' a' = Some Y'" "x \<in> join Y True Y'"
      by (fastforce simp: ran_def Table.join_def these_iff split: if_splits)
    then have a'_def: "a' = a"
      using assms
      by (auto simp: Table.join_def table_def these_iff join1_Some_restrict dest!: restrict[unfolded Map_To_Mapping.map_apply_def])
         (metis New_max.nested_include_restrict join1_Some_restrict)
    show "x \<in> \<Union> (ran (\<lambda>k. case case T k of None \<Rightarrow> None | Some y \<Rightarrow>
      (case T' k of None \<Rightarrow> None | Some y' \<Rightarrow> Some (bin_join n B y True C y')) of
      None \<Rightarrow> None | Some v \<Rightarrow> if v \<noteq> {} then Some v else None))"
      using a_def restrict
      apply (auto simp: ran_def a'_def simp del: bin_join.simps split: option.splits)
      apply (rule exI[of _ "join Y True Y'"])
      apply (auto simp: Map_To_Mapping.map_apply_def Table.join_def these_iff bin_join_table simp del: bin_join.simps intro!: exI[of _ a])
      apply (auto simp: Option.these_def dest!: spec[of _ "Some x"])
      apply (metis SigmaI image_eqI)
      done
  qed
  show "\<And>x Y. Mapping.lookup (idx_join n B T C T') x = Some Y \<Longrightarrow> table n (B \<union> C) Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A z)"
    using assms
    unfolding idx_join_def
    apply (transfer fixing: n A B C)
    apply (auto simp: Map_To_Mapping.map_apply_def bin_join_table simp del: bin_join.simps split: option.splits if_splits)
    apply (auto simp: table_def)
     apply (smt (z3) join_restrict)
     apply (auto simp: Table.join_def these_iff split: if_splits)
    apply (smt (z3) New_max.nested_include_restrict join1_Some_restrict)
    done
qed

lemma idx_join_reindex:
  fixes T T' :: "('a option list, 'a option list set) mapping"
  assumes "I \<subseteq> B" "I \<subseteq> C"
    "\<And>x Y. Mapping.lookup T x = Some Y \<Longrightarrow> table n B Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A z)"
    "\<And>x Y. Mapping.lookup T' x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A' z)"
  shows "set_of_idx (idx_join n B (idx_reindex I A T) C (idx_reindex I A' T')) = join (set_of_idx T) True (set_of_idx T')"
    "\<And>x Y. Mapping.lookup (idx_join n B (idx_reindex I A T) C (idx_reindex I A' T')) x = Some Y \<Longrightarrow> table n (B \<union> C) Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict I z)"
proof -
  note I1 = idx_reindex[where ?T=T and ?I=A, OF assms(3)]
  note I2 = idx_reindex[where ?T=T' and ?I=A', OF assms(4)]
  show "set_of_idx (idx_join n B (idx_reindex I A T) C (idx_reindex I A' T')) = join (set_of_idx T) True (set_of_idx T')"
    "\<And>x Y. Mapping.lookup (idx_join n B (idx_reindex I A T) C (idx_reindex I A' T')) x = Some Y \<Longrightarrow> table n (B \<union> C) Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict I z)"
    using idx_join[where ?T="idx_reindex I A T" and ?T'="idx_reindex I A' T'" and ?n=n and ?B=B and ?C=C and ?A=I, OF assms(1-2) I1(2) I2(2)] I1(1) I2(1)
    by auto
qed

lift_definition wf_idx_join :: "'a wf_idx \<Rightarrow> 'a wf_idx \<Rightarrow> 'a wf_idx" is
  "\<lambda>(n, A, I, T) (n', A', I', T'). if n = n' then
    (let I'' = I \<inter> I'; i = idx_reindex I'' I T; i' = idx_reindex I'' I' T' in (n, A \<union> A', I'', idx_join n A i A' i'))
  else (n, A, I, T)"
  subgoal premises prems for prod1 prod2
  proof -
    obtain n A I T where prod1_def: "prod1 = (n, A, I, T)"
      by (cases prod1) auto
    obtain n' A' I' T' where prod2_def: "prod2 = (n', A', I', T')"
      by (cases prod2) auto
    show ?thesis
      using prems
    proof (cases "n = n'")
      case n_def: True
      show ?thesis
        using idx_reindex(2) idx_join_reindex(2)[where ?I="I \<inter> I'" and ?T=T and ?T'=T' and ?n=n and ?B=A and ?C=A' and ?A=I and ?A'=I',
            OF inf.coboundedI1 inf.coboundedI2] prems
        by (auto simp: Let_def n_def prod1_def prod2_def)
    qed (auto simp: prod1_def prod2_def)
  qed
  done

lemma wf_idx_sig_join: "wf_idx_sig (wf_idx_join t1 t2) = (case wf_idx_sig t1 of (n, A) \<Rightarrow> case wf_idx_sig t2 of (n', A') \<Rightarrow>
  if n = n' then (n, A \<union> A') else wf_idx_sig t1)"
  by transfer (auto simp: Let_def split: if_splits)

lemma wf_idx_set_join: "wf_idx_sig t1 = (n, A) \<Longrightarrow> wf_idx_sig t2 = (n', A') \<Longrightarrow> n = n' \<Longrightarrow>
  wf_idx_set (wf_idx_join t1 t2) = join (wf_idx_set t1) True (wf_idx_set t2)"
  apply transfer
  subgoal premises prems for prod1 n A prod2 n' A'
  proof -
    obtain I T where prod1_def: "prod1 = (n, A, I, T)"
      using prems
      by (cases prod1) auto
    obtain I' T' where prod2_def: "prod2 = (n, A', I', T')"
      using prems
      by (cases prod2) auto
    show ?thesis
      using idx_join_reindex(1)[where ?I="I \<inter> I'" and ?T=T and ?T'=T' and ?n=n and ?B=A and ?C=A' and ?A=I and ?A'=I',
          OF inf.coboundedI1 inf.coboundedI2] prems
      by (auto simp: Let_def prod1_def prod2_def)
  qed
  done

lemma wf_idx_set_join_deg: "wf_idx_sig t1 = (n, A) \<Longrightarrow> wf_idx_sig t2 = (n', A') \<Longrightarrow> \<not>n = n' \<Longrightarrow>
  wf_idx_set (wf_idx_join t1 t2) = wf_idx_set t1"
  by transfer (auto simp: Let_def)

lemma wf_idx_set_join': "wf_idx_set (wf_idx_join t1 t2) = (case wf_idx_sig t1 of (n, A) \<Rightarrow> case wf_idx_sig t2 of (n', A') \<Rightarrow>
  if n = n' then join (wf_idx_set t1) True (wf_idx_set t2) else wf_idx_set t1)"
  using wf_idx_set_join wf_idx_set_join_deg
  by (fastforce split: if_splits)

definition "idx_antijoin n A T A' T' = Mapping.combine (\<union>) (mapping_antijoin T T') (Mapping.filter (\<lambda>_ T. T \<noteq> {}) (mapping_join (\<lambda>T T'. bin_join n A T False A' T') T T'))"

lemma idx_antijoin:
  fixes T T' :: "('a option list, 'a option list set) mapping"
  assumes "A \<subseteq> B" "A \<subseteq> C" "C \<subseteq> B"
    "\<And>x Y. Mapping.lookup T x = Some Y \<Longrightarrow> table n B Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A z)"
    "\<And>x Y. Mapping.lookup T' x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A z)"
  shows "set_of_idx (idx_antijoin n B T C T') = join (set_of_idx T) False (set_of_idx T')"
    "\<And>x Y. Mapping.lookup (idx_antijoin n B T C T') x = Some Y \<Longrightarrow> table n B Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A z)"
proof -
  show "set_of_idx (idx_antijoin n B T C T') = join (set_of_idx T) False (set_of_idx T')"
    using assms(4,5)
    unfolding idx_antijoin_def
    apply (transfer fixing: n A B C)
  proof (rule set_eqI, rule iffI)
    fix T T' :: "'a option list \<Rightarrow> 'a option list set option"
    fix x
    assume restrict: "\<And>x Y. Map_To_Mapping.map_apply T x = Some Y \<Longrightarrow> table n B Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A z)"
      "\<And>x Y. Map_To_Mapping.map_apply T' x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A z)"
    assume "x \<in> \<Union> (ran (\<lambda>x. combine_options (\<union>)
      (case T x of None \<Rightarrow> None | Some y \<Rightarrow> (case T' x of None \<Rightarrow> Some y | Some x \<Rightarrow> Map.empty x))
      (case case T x of None \<Rightarrow> None | Some y \<Rightarrow>
        (case T' x of None \<Rightarrow> None | Some y' \<Rightarrow> Some (bin_join n B y False C y')) of
      None \<Rightarrow> None | Some v \<Rightarrow> if v \<noteq> {} then Some v else None)))"
    then obtain a Y where a_def: "T a = Some Y" "case T' a of None \<Rightarrow> x \<in> Y | Some Y' \<Rightarrow> x \<in> join Y False Y'"
      using restrict
      by (auto simp: Map_To_Mapping.map_apply_def ran_def bin_join_table simp del: bin_join.simps split: option.splits if_splits)
    then show "x \<in> join (\<Union> (ran T)) False (\<Union> (ran T'))"
      using restrict assms(2)
      apply (auto simp: ran_def Table.join_def table_def these_iff Map_To_Mapping.map_apply_def split: option.splits)
      apply (metis New_max.nested_include_restrict join1_Some_restrict option.simps(3))
      apply (smt (z3) New_max.nested_include_restrict join1_Some_restrict option.sel restrict_idle)
      done
  next
    fix T T' :: "'a option list \<Rightarrow> 'a option list set option"
    fix x
    assume "\<And>x Y. Map_To_Mapping.map_apply T x = Some Y \<Longrightarrow> table n B Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A z)"
      "\<And>x Y. Map_To_Mapping.map_apply T' x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A z)"
      "x \<in> join (\<Union> (ran T)) False (\<Union> (ran T'))"
    then obtain a Y where a_def: "T a = Some Y" "case T' a of None \<Rightarrow> x \<in> Y | Some Y' \<Rightarrow> x \<in> bin_join n B Y False C Y'"
      apply (auto simp: ran_def Table.join_def these_iff Map_To_Mapping.map_apply_def split: if_splits)
      subgoal premises prems for X a
        using prems(1)[OF prems(6)] prems(2,3,4,5,6)
        apply (cases "T' a")
         apply (auto simp: Table.join_def these_iff bin_join_table simp del: bin_join.simps)
        apply blast
        done
      done
    show "x \<in> \<Union> (ran (\<lambda>x. combine_options (\<union>)
      (case T x of None \<Rightarrow> None | Some y \<Rightarrow> (case T' x of None \<Rightarrow> Some y | Some x \<Rightarrow> Map.empty x))
      (case case T x of None \<Rightarrow> None | Some y \<Rightarrow>
        (case T' x of None \<Rightarrow> None | Some y' \<Rightarrow> Some (bin_join n B y False C y')) of
      None \<Rightarrow> None | Some v \<Rightarrow> if v \<noteq> {} then Some v else None)))"
      using a_def
      apply (auto simp: ran_def simp del: bin_join.simps split: option.splits)
      subgoal
        by (rule exI[of _ Y]) (auto simp del: bin_join.simps)
      subgoal for Y'
        by (rule exI[of _ "bin_join n B Y False C Y'"]) (auto simp: Table.join_def these_iff simp del: bin_join.simps)
      done
  qed
  show "\<And>x Y. Mapping.lookup (idx_antijoin n B T C T') x = Some Y \<Longrightarrow> table n B Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A z)"
    using assms
    unfolding idx_antijoin_def
    by (transfer fixing: n A B C) (auto simp: Map_To_Mapping.map_apply_def Table.join_def table_def bin_join_table simp del: bin_join.simps split: option.splits if_splits)
qed

lemma idx_antijoin_reindex:
  fixes T T' :: "('a option list, 'a option list set) mapping"
  assumes "I \<subseteq> B" "I \<subseteq> C" "C \<subseteq> B"
    "\<And>x Y. Mapping.lookup T x = Some Y \<Longrightarrow> table n B Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A z)"
    "\<And>x Y. Mapping.lookup T' x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A' z)"
  shows "set_of_idx (idx_antijoin n B (idx_reindex I A T) C (idx_reindex I A' T')) = join (set_of_idx T) False (set_of_idx T')"
    "\<And>x Y. Mapping.lookup (idx_antijoin n B (idx_reindex I A T) C (idx_reindex I A' T')) x = Some Y \<Longrightarrow> table n B Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict I z)"
proof -
  note I1 = idx_reindex[where ?T=T and ?I=A, OF assms(4)]
  note I2 = idx_reindex[where ?T=T' and ?I=A', OF assms(5)]
  show "set_of_idx (idx_antijoin n B (idx_reindex I A T) C (idx_reindex I A' T')) = join (set_of_idx T) False (set_of_idx T')"
    "\<And>x Y. Mapping.lookup (idx_antijoin n B (idx_reindex I A T) C (idx_reindex I A' T')) x = Some Y \<Longrightarrow> table n B Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict I z)"
    using idx_antijoin[where ?T="idx_reindex I A T" and ?T'="idx_reindex I A' T'" and ?n=n and ?B=B and ?C=C and ?A=I, OF assms(1-3) I1(2) I2(2)] I1(1) I2(1)
    by auto
qed

lemma mapping_antijoin:
  fixes T T' :: "('a option list, 'a option list set) mapping"
  assumes "C \<subseteq> B"
    "\<And>x Y. Mapping.lookup T x = Some Y \<Longrightarrow> table n B Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict C z)"
    "\<And>x Y. Mapping.lookup T' x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict C z)"
  shows "set_of_idx (mapping_antijoin T T') = join (set_of_idx T) False (set_of_idx T')"
    "\<And>x Y. Mapping.lookup (mapping_antijoin T T') x = Some Y \<Longrightarrow> table n B Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict C z)"
proof -
  show "set_of_idx (mapping_antijoin T T') = join (set_of_idx T) False (set_of_idx T')"
    using assms
    apply (transfer fixing: n B C)
  proof (rule set_eqI, rule iffI)
    fix T T' :: "'a option list \<Rightarrow> 'a option list set option"
    fix x
    assume restrict: "\<And>x Y. Map_To_Mapping.map_apply T x = Some Y \<Longrightarrow> table n B Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict C z)"
      "\<And>x Y. Map_To_Mapping.map_apply T' x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict C z)"
    assume "x \<in> \<Union> (ran (\<lambda>x. case T x of None \<Rightarrow> None | Some y \<Rightarrow>
      (case T' x of None \<Rightarrow> Some y | Some y' \<Rightarrow> Map.empty x)))"
    then obtain a Y where a_def: "T a = Some Y" "T' a = None" "x \<in> Y"
      by (auto simp: ran_def split: option.splits)
    then show "x \<in> join (\<Union> (ran T)) False (\<Union> (ran T'))"
      using restrict
      by (auto simp: Map_To_Mapping.map_apply_def ran_def Table.join_def these_iff table_def)
         (metis New_max.restrict_idle_include dual_order.refl join1_Some_restrict option.simps(3))
  next
    fix T T' :: "'a option list \<Rightarrow> 'a option list set option"
    fix x
    assume restrict: "\<And>x Y. Map_To_Mapping.map_apply T x = Some Y \<Longrightarrow> table n B Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict C z)"
      "\<And>x Y. Map_To_Mapping.map_apply T' x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict C z)"
    assume "x \<in> join (\<Union> (ran T)) False (\<Union> (ran T'))"
    then obtain a Y where a_def: "T a = Some Y" "Y \<noteq> {}" "case T' a of None \<Rightarrow> x \<in> Y | Some Y' \<Rightarrow> x \<in> join Y False Y'"
      apply (auto simp: ran_def Table.join_def these_iff Map_To_Mapping.map_apply_def split: if_splits)
      subgoal premises prems for X a
        using prems(1)[OF prems(4)] prems(2,3,4)
        by (cases "T' a") (auto simp: Table.join_def these_iff)
      done
    show "x \<in> \<Union> (ran (\<lambda>x. case T x of None \<Rightarrow> None | Some y \<Rightarrow> (case T' x of None \<Rightarrow> Some y | Some x \<Rightarrow> Map.empty x)))"
      using a_def
      apply (auto simp: ran_def split: option.splits)
       apply (metis option.inject option.simps(3))
      subgoal for Y' z
        using assms(1) restrict(1)[of a Y] restrict(2)[of a Y']
        apply (auto dest!: spec[of _ "join Y False Y'"] spec[of _ a])
        apply (auto simp: Map_To_Mapping.map_apply_def Table.join_def these_iff table_def)
        apply (smt (z3) join1_Some_restrict restrict_idle sup.absorb_iff1)
        done
      done
  qed
  show "\<And>x Y. Mapping.lookup (mapping_antijoin T T') x = Some Y \<Longrightarrow> table n B Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict C z)"
    using assms
    unfolding idx_join_def
    by (transfer fixing: n B C) (auto simp: Map_To_Mapping.map_apply_def bin_join_table simp del: bin_join.simps split: option.splits)
qed

lemma mapping_antijoin_reindex:
  fixes T T' :: "('a option list, 'a option list set) mapping"
  assumes "C \<subseteq> B"
    "\<And>x Y. Mapping.lookup T x = Some Y \<Longrightarrow> table n B Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict A z)"
    "\<And>x Y. Mapping.lookup T' x = Some Y \<Longrightarrow> table n C Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict C z)"
  shows "set_of_idx (mapping_antijoin (idx_reindex C A T) T') = join (set_of_idx T) False (set_of_idx T')"
    "\<And>x Y. Mapping.lookup (mapping_antijoin (idx_reindex C A T) T') x = Some Y \<Longrightarrow> table n B Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict C z)"
proof -
  note I1 = idx_reindex[OF assms(2), of T C]
  show "set_of_idx (mapping_antijoin (idx_reindex C A T) T') = join (set_of_idx T) False (set_of_idx T')"
    "\<And>x Y. Mapping.lookup (mapping_antijoin (idx_reindex C A T) T') x = Some Y \<Longrightarrow> table n B Y \<and> Y \<noteq> {} \<and> (\<forall>z \<in> Y. x = restrict C z)"
    using mapping_antijoin[where ?T="idx_reindex C A T" and ?T'="T'" and ?n=n and ?B=B and ?C=C, OF assms(1) I1(2) assms(3)] I1(1)
    by auto
qed

lift_definition wf_idx_antijoin :: "'a wf_idx \<Rightarrow> 'a wf_idx \<Rightarrow> 'a wf_idx" is
  "\<lambda>(n, A, I, T) (n', A', I', T'). if n = n' \<and> A' \<subseteq> A then
    (let I'' = I \<inter> I' in if I'' = A' then (let i = idx_reindex I'' I T in (n, A, I'', mapping_antijoin i T'))
     else (let i = idx_reindex I'' I T; i' = idx_reindex I'' I' T' in (n, A, I'', idx_antijoin n A i A' i')))
  else (n, A, I, T)"
  subgoal premises prems for prod1 prod2
  proof -
    obtain n A I T where prod1_def: "prod1 = (n, A, I, T)"
      by (cases prod1) auto
    obtain n' A' I' T' where prod2_def: "prod2 = (n', A', I', T')"
      by (cases prod2) auto
    show ?thesis
      using prems
    proof (cases "n = n'")
      case n_def: True
      show ?thesis
      proof (cases "A' = I \<inter> I'")
        case A'_def: True
        have sub: "I \<inter> I' \<subseteq> A" "I \<inter> I' = I'"
          using prems
          by (auto simp: Let_def n_def A'_def prod1_def prod2_def)
        show ?thesis
          using prems idx_reindex(2) mapping_antijoin_reindex(2)[where ?T=T and ?T'=T' and ?n=n and ?B=A and ?C="I \<inter> I'" and ?A=I, OF sub(1)]
          by (auto simp: Let_def n_def A'_def sub(2) prod1_def prod2_def)
      next
        case False
        then show ?thesis
          using prems idx_reindex(2) idx_antijoin_reindex(2)[where ?I="I \<inter> I'" and ?T=T and ?T'=T' and ?n=n and ?B=A and ?C=A' and ?A=I and ?A'=I',
              OF inf.coboundedI1 inf.coboundedI2]
          by (auto simp: Let_def n_def prod1_def prod2_def)
      qed
    qed (auto simp: prod1_def prod2_def)
  qed
  done

lemma wf_idx_sig_antijoin: "wf_idx_sig (wf_idx_antijoin t1 t2) = wf_idx_sig t1"
  by transfer (auto simp: Let_def split: if_splits)

lemma wf_idx_set_antijoin: "wf_idx_sig t1 = (n, A) \<Longrightarrow> wf_idx_sig t2 = (n', A') \<Longrightarrow> n = n' \<Longrightarrow> A' \<subseteq> A \<Longrightarrow>
  wf_idx_set (wf_idx_antijoin t1 t2) = join (wf_idx_set t1) False (wf_idx_set t2)"
  apply transfer
  subgoal premises prems for prod1 n A prod2 n' A'
  proof -
    obtain I T where prod1_def: "prod1 = (n, A, I, T)"
      using prems
      by (cases prod1) auto
    obtain I' T' where prod2_def: "prod2 = (n, A', I', T')"
      using prems
      by (cases prod2) auto
    show ?thesis
    proof (cases "A' = I \<inter> I'")
      case A'_def: True
      have sub: "I \<inter> I' \<subseteq> A" "I \<inter> I' = I'"
        using prems
        by (auto simp: Let_def A'_def prod1_def prod2_def)
      show ?thesis
        using mapping_antijoin_reindex(1)[where ?T=T and ?T'=T' and ?n=n and ?B=A and ?C="I \<inter> I'" and ?A=I, OF sub(1)] prems
        by (auto simp: Let_def A'_def sub(2) prod1_def prod2_def)
    next
      case False
      then show ?thesis
        using idx_antijoin_reindex(1)[where ?I="I \<inter> I'" and ?T=T and ?T'=T' and ?n=n and ?B=A and ?C=A' and ?A=I and ?A'=I',
            OF inf.coboundedI1 inf.coboundedI2] prems
        by (auto simp: Let_def prod1_def prod2_def)
    qed
  qed
  done

lemma wf_idx_set_antijoin_deg: "wf_idx_sig t1 = (n, A) \<Longrightarrow> wf_idx_sig t2 = (n', A') \<Longrightarrow>
  \<not>(n = n' \<and> A' \<subseteq> A) \<Longrightarrow> wf_idx_set (wf_idx_antijoin t1 t2) = wf_idx_set t1"
  by transfer (auto split: if_splits)

lemma wf_idx_set_antijoin': "wf_idx_set (wf_idx_antijoin t1 t2) = (case wf_idx_sig t1 of (n, A) \<Rightarrow> case wf_idx_sig t2 of (n', A') \<Rightarrow>
  if n = n' \<and> A' \<subseteq> A then join (wf_idx_set t1) False (wf_idx_set t2) else wf_idx_set t1)"
  using wf_idx_set_antijoin wf_idx_set_antijoin_deg
  by (fastforce split: if_splits)

(* wf_set *)

typedef 'a wf_set = "{(n :: nat, A :: nat set, T :: 'a option list set) |
  n A T. table n A T}"
  by (rule exI[of _ "(0, {}, {})"]) (auto simp: table_def)

setup_lifting type_definition_wf_set

lift_definition wf_set_sig :: "'a wf_set \<Rightarrow> (nat \<times> nat set)" is "\<lambda>(n, A, T). (n, A)" .

lift_definition wf_set_set :: "'a wf_set \<Rightarrow> 'a option list set" is "\<lambda>(n, A, T). T" .

(* conversion wf_table \<longleftrightarrow> set *)

lift_definition wf_table_of_wf_set :: "'a wf_set \<Rightarrow> 'a wf_table" is "\<lambda>t. t" .

lemma wf_set_sig[simp]: "wf_table_sig (wf_table_of_wf_set t) = wf_set_sig t"
  by transfer auto

lemma wf_set_set[simp]: "wf_table_set (wf_table_of_wf_set t) = wf_set_set t"
  by transfer auto

lift_definition wf_set_of_set :: "nat \<Rightarrow> nat set \<Rightarrow> 'a option list set \<Rightarrow> 'a wf_set" is
  "\<lambda>n A T. (n, A , Set.filter (wf_tuple n A) T)"
  by (auto simp: Let_def table_def)

lemma wf_set_sig_of_set: "wf_set_sig (wf_set_of_set n A T) = (n, A )"
  by transfer auto

lemma wf_set_set_of_set: "wf_set_set (wf_set_of_set n A T) = Set.filter (wf_tuple n A) T"
  by transfer auto

lift_definition wf_set_union :: "'a wf_set \<Rightarrow> 'a wf_set \<Rightarrow> 'a wf_set" is
  "\<lambda>(n, A, T) (n', A', T'). if n = n' \<and> A = A' then (n, A, T \<union> T') else (n, A, T)"
  by auto

lemma wf_set_sig_union: "wf_set_sig (wf_set_union t1 t2) = wf_set_sig t1"
  by transfer auto

lemma wf_set_set_union: "wf_set_sig t1 = wf_set_sig t2 \<Longrightarrow> wf_set_set (wf_set_union t1 t2) =
  wf_set_set t1 \<union> wf_set_set t2"
  by transfer auto

lemma wf_set_set_union_deg: "\<not>wf_set_sig t1 = wf_set_sig t2 \<Longrightarrow> wf_set_set (wf_set_union t1 t2) = wf_set_set t1"
  by transfer (auto split: if_splits)

lemma wf_set_set_union': "wf_set_set (wf_set_union t1 t2) =
  (if wf_set_sig t1 = wf_set_sig t2 then wf_set_set t1 \<union> wf_set_set t2 else wf_set_set t1)"
  using wf_set_set_union wf_set_set_union_deg
  by (fastforce split: if_splits)

lift_definition wf_set_join :: "'a wf_set \<Rightarrow> 'a wf_set \<Rightarrow> 'a wf_set" is
  "\<lambda>(n, A, T) (n', A', T'). if n = n' then (n, A \<union> A', bin_join n A T True A' T') else (n, A, T)"
  by (fastforce simp del: bin_join.simps simp: bin_join_table intro: join_table)

lemma wf_set_sig_join: "wf_set_sig (wf_set_join t1 t2) = (case wf_set_sig t1 of (n, A) \<Rightarrow> case wf_set_sig t2 of (n', A') \<Rightarrow>
  if n = n' then (n, A \<union> A') else wf_set_sig t1)"
  by transfer auto

lemma wf_set_set_join: "wf_set_sig t1 = (n, A) \<Longrightarrow> wf_set_sig t2 = (n', A') \<Longrightarrow> n = n' \<Longrightarrow>
  wf_set_set (wf_set_join t1 t2) = join (wf_set_set t1) True (wf_set_set t2)"
  by transfer (auto simp del: bin_join.simps simp: bin_join_table)

lemma wf_set_set_join_deg: "wf_set_sig t1 = (n, A) \<Longrightarrow> wf_set_sig t2 = (n', A') \<Longrightarrow> \<not>n = n' \<Longrightarrow>
  wf_set_set (wf_set_join t1 t2) = wf_set_set t1"
  by transfer auto

lemma wf_set_set_join': "wf_set_set (wf_set_join t1 t2) = (case wf_set_sig t1 of (n, A) \<Rightarrow> case wf_set_sig t2 of (n', A') \<Rightarrow>
  if n = n' then join (wf_set_set t1) True (wf_set_set t2) else wf_set_set t1)"
  using wf_set_set_join wf_set_set_join_deg
  by (fastforce split: if_splits)

lift_definition wf_set_antijoin :: "'a wf_set \<Rightarrow> 'a wf_set \<Rightarrow> 'a wf_set" is
  "\<lambda>(n, A, T) (n', A', T'). if n = n' \<and> A' \<subseteq> A then (n, A \<union> A', bin_join n A T False A' T') else (n, A, T)"
  by (fastforce simp del: bin_join.simps simp: bin_join_table intro: join_table)

lemma wf_set_sig_antijoin: "wf_set_sig (wf_set_antijoin t1 t2) = wf_set_sig t1"
  by transfer auto

lemma wf_set_set_antijoin: "wf_set_sig t1 = (n, A) \<Longrightarrow> wf_set_sig t2 = (n, A') \<Longrightarrow> A' \<subseteq> A \<Longrightarrow>
  wf_set_set (wf_set_antijoin t1 t2) = join (wf_set_set t1) False (wf_set_set t2)"
  by transfer (auto simp del: bin_join.simps simp: bin_join_table)

lemma wf_set_set_antijoin_deg: "wf_set_sig t = (n, A) \<Longrightarrow> wf_set_sig t' = (n', A') \<Longrightarrow> \<not>(n = n' \<and> A' \<subseteq> A) \<Longrightarrow>
  wf_set_set (wf_set_antijoin t t') = wf_set_set t"
  by transfer (auto split: if_splits)

lemma wf_set_set_antijoin': "wf_set_set (wf_set_antijoin t1 t2) = (case wf_set_sig t1 of (n, A) \<Rightarrow> case wf_set_sig t2 of (n', A') \<Rightarrow>
  if n = n' \<and> A' \<subseteq> A then join (wf_set_set t1) False (wf_set_set t2) else wf_set_set t1)"
  using wf_set_set_antijoin wf_set_set_antijoin_deg
  by (fastforce split: if_splits)

lift_definition wf_set_permute :: "nat option list \<Rightarrow> 'a wf_set \<Rightarrow> 'a wf_set" is
  "\<lambda>ns (n, A, T). (length ns, fv_vars ns, permute ns ` T)"
  using fv_vars_rec_set[where ?n=0, folded fv_vars_def]
  by (fastforce simp: table_def intro: wf_tuple_permute)

lemma wf_set_sig_permute: "wf_set_sig (wf_set_permute ns t) = (length ns, fv_vars ns)"
  by transfer auto

lemma wf_set_set_permute: "wf_set_set (wf_set_permute ns t) = permute ns ` wf_set_set t"
  by transfer auto

(* conversion wf_set \<longleftrightarrow> idx *)

lift_definition wf_idx_of_wf_set :: "nat set \<Rightarrow> 'a wf_set \<Rightarrow> 'a wf_idx" is
  "\<lambda>I (n, A, T). let I' = I \<inter> A in (n, A, I', idx_create T I')"
  by (auto simp: Let_def idx_create)

lemma wf_idx_sig_of_wf_set[simp]: "wf_idx_sig (wf_idx_of_wf_set I t) = wf_set_sig t"
  by transfer (auto simp: Let_def)

lemma wf_idx_set_of_wf_set[simp]: "wf_idx_set (wf_idx_of_wf_set I t) = wf_set_set t"
  by transfer (auto simp: Let_def idx_create(1))

lemma wf_table_of_idx_of_wf_set[simp]: "wf_table_of_idx (wf_idx_of_wf_set (wf_idx_cols i) t') = wf_table_of_wf_set t'"
  by (auto intro!: wf_table_eqI)

lift_definition wf_set_of_idx :: "'a wf_idx \<Rightarrow> 'a wf_set" is
  "\<lambda>(n, A, I, T). (n, A, set_of_idx T)"
  by transfer (auto simp: Map_To_Mapping.map_apply_def ran_def table_def)

lemma wf_set_sig_of_idx[simp]: "wf_set_sig (wf_set_of_idx t) = wf_idx_sig t"
  by transfer auto

lemma wf_set_set_of_idx[simp]: "wf_set_set (wf_set_of_idx t) = wf_idx_set t"
  by transfer auto

(* code setup *)

code_datatype wf_table_of_wf_set wf_table_of_idx

lemmas wf_table_sig_code[code] = wf_table_sig_of_idx wf_set_sig
lemmas wf_table_set_code[code] = wf_table_set_of_idx wf_set_set

lemma wf_table_of_set_code[code]: "wf_table_of_set n A T = wf_table_of_wf_set (wf_set_of_set n A T)"
  by transfer auto

lemma wf_table_union_code[code]:
  "wf_table_union (wf_table_of_idx i) (wf_table_of_idx i') = wf_table_of_idx (wf_idx_union i i')"
  "wf_table_union (wf_table_of_idx i) (wf_table_of_wf_set t') = wf_table_of_idx (wf_idx_union i (wf_idx_of_wf_set (wf_idx_cols i) t'))"
  "wf_table_union (wf_table_of_wf_set t) (wf_table_of_wf_set t') = wf_table_of_wf_set (wf_set_union t t')"
  "wf_table_union (wf_table_of_wf_set t) (wf_table_of_idx i') = wf_table_of_idx (wf_idx_union (wf_idx_of_wf_set (wf_idx_cols i') t) i')"
  by (auto simp: wf_table_sig_union wf_idx_sig_union wf_set_sig_union wf_table_set_union' wf_idx_set_union' wf_set_set_union' intro!: wf_table_eqI)

lemma wf_table_join_code[code]:
  "wf_table_join (wf_table_of_idx i) (wf_table_of_idx i') = wf_table_of_idx (wf_idx_join i i')"
  "wf_table_join (wf_table_of_idx i) (wf_table_of_wf_set t') = wf_table_of_idx (wf_idx_join i (wf_idx_of_wf_set (wf_idx_cols i) t'))"
  "wf_table_join (wf_table_of_wf_set t) (wf_table_of_wf_set t') = wf_table_of_wf_set (wf_set_join t t')"
  "wf_table_join (wf_table_of_wf_set t) (wf_table_of_idx i') = wf_table_of_idx (wf_idx_join (wf_idx_of_wf_set (wf_idx_cols i') t) i')"
  by (auto simp: wf_table_sig_join wf_idx_sig_join wf_set_sig_join wf_table_set_join' wf_idx_set_join' wf_set_set_join' intro!: wf_table_eqI split: prod.splits)

lemma wf_table_antijoin_code[code]:
  "wf_table_antijoin (wf_table_of_idx i) (wf_table_of_idx i') = wf_table_of_idx (wf_idx_antijoin i i')"
  "wf_table_antijoin (wf_table_of_idx i) (wf_table_of_wf_set t') = wf_table_of_idx (wf_idx_antijoin i (wf_idx_of_wf_set (wf_idx_cols i) t'))"
  "wf_table_antijoin (wf_table_of_wf_set t) (wf_table_of_wf_set t') = wf_table_of_wf_set (wf_set_antijoin t t')"
  "wf_table_antijoin (wf_table_of_wf_set t) (wf_table_of_idx i') = wf_table_of_idx (wf_idx_antijoin (wf_idx_of_wf_set (wf_idx_cols i') t) i')"
  by (auto simp: wf_table_sig_antijoin wf_idx_sig_antijoin wf_set_sig_antijoin wf_table_set_antijoin' wf_idx_set_antijoin' wf_set_set_antijoin' intro!: wf_table_eqI split: prod.splits if_splits)

lemma wf_idx_set_wf: "wf_idx_sig t = (n, A) \<Longrightarrow> x \<in> wf_idx_set t \<Longrightarrow> wf_tuple n A x"
  apply transfer
  apply (auto simp: table_def inf_absorb1)
  apply transfer
  apply (auto simp: Map_To_Mapping.map_apply_def ran_def)
  done

lemma wf_table_set_wf: "wf_table_sig t = (n, A) \<Longrightarrow> x \<in> wf_table_set t \<Longrightarrow> wf_tuple n A x"
  by transfer (auto simp: table_def inf_absorb1)

lemma wf_table_permute_code[code]:
  "wf_table_permute ns (wf_table_of_wf_set t) = wf_table_of_wf_set (wf_set_permute ns t)"
  "wf_table_permute ns (wf_table_of_idx i) = (case wf_idx_sig i of (n, A) \<Rightarrow>
    wf_table_of_wf_set (wf_set_permute ns (wf_set_of_set n A (wf_idx_set i))))"
proof -
  show "wf_table_permute ns (wf_table_of_wf_set t) = wf_table_of_wf_set (wf_set_permute ns t)"
    by transfer auto
  show "wf_table_permute ns (wf_table_of_idx i) = (case wf_idx_sig i of (n, A) \<Rightarrow>
    wf_table_of_wf_set (wf_set_permute ns (wf_set_of_set n A (wf_idx_set i))))"
    by (auto simp: wf_table_sig_permute wf_set_sig_permute wf_table_set_permute wf_set_set_permute wf_set_set_of_set intro!: wf_table_eqI split: prod.splits)
       (auto dest: wf_idx_set_wf)
qed

definition wf_table_idx :: "nat set \<Rightarrow> 'a wf_table \<Rightarrow> 'a wf_table" where
  "wf_table_idx I T = T"

lemma wf_table_idx_code[code]:
  "wf_table_idx I (wf_table_of_idx i) = wf_table_of_idx (wf_idx_reindex I i)"
  "wf_table_idx I (wf_table_of_wf_set t) = wf_table_of_idx (wf_idx_of_wf_set I t)"
proof -
  show "wf_table_idx I (wf_table_of_idx i) = wf_table_of_idx (wf_idx_reindex I i)"
    by (rule wf_table_eqI) (auto simp: wf_table_idx_def wf_idx_sig_reindex wf_idx_set_reindex)
  show "wf_table_idx I (wf_table_of_wf_set t) = wf_table_of_idx (wf_idx_of_wf_set I t)"
    by (rule wf_table_eqI) (auto simp: wf_table_idx_def)
qed

end
