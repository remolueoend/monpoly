theory Proj_Code
  imports "Containers.Containers"
begin

definition images :: "('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b set) set" where
  "images X = (\<lambda>a. (a, {b. (a, b) \<in> X})) ` fst ` X"

lemma images_iff_proj: "(a, B) \<in> images X \<longleftrightarrow> B \<noteq> {} \<and> Equiv_Relations.proj X a = B"
  by (force simp: Equiv_Relations.proj_def images_def)

lemma proj_empty_iff: "Equiv_Relations.proj X a = {} \<longleftrightarrow> a \<notin> fst ` X"
  using image_iff
  by (fastforce simp: Equiv_Relations.proj_def Image_def)

lemma proj_iff_images: "B \<noteq> {} \<Longrightarrow> Equiv_Relations.proj X a = B \<longleftrightarrow> (a, B) \<in> images X"
  by (auto simp: images_iff_proj)

lemma proj_iff_images': "Equiv_Relations.proj X a = B \<longleftrightarrow>
  (if B = {} then a \<notin> fst ` X else (a, B) \<in> images X)"
  by (auto simp: proj_empty_iff proj_iff_images)

lemma fst_imagesI: "(a, b) \<in> X \<Longrightarrow> a \<in> fst ` images X"
  by (auto simp: images_def) (metis (mono_tags, lifting) fstI image_iff)

definition flatten :: "('a \<times> 'b set) set \<Rightarrow> ('a \<times> 'b) set" where
  "flatten X = \<Union>((\<lambda>(a, B). (\<lambda>b. (a, b)) ` B) ` X)"

lemma flatten_empty[simp]: "flatten {} = {}"
  by (auto simp: flatten_def)

lemma images_flatten:
  assumes "\<And>a. (a, {}) \<notin> X" "\<And>a B B'. (a, B) \<in> X \<Longrightarrow> (a, B') \<in> X \<Longrightarrow> B = B'"
  shows "images (flatten X) = X"
proof (rule set_eqI, rule iffI)
  fix aB
  assume aB_X: "aB \<in> X"
  obtain a B where aB_def: "aB = (a, B)"
    by fastforce
  obtain b where "b \<in> B"
    using assms(1) aB_X
    by (fastforce simp: aB_def)
  then have b_def: "(a, b) \<in> flatten X"
    using aB_X
    by (auto simp: aB_def flatten_def)
  show "aB \<in> images (flatten X)"
    using b_def assms(2)[OF aB_X[unfolded aB_def]]
    by (auto simp: aB_def images_iff_proj Equiv_Relations.proj_def flatten_def)
next
  fix aB
  assume aB_X: "aB \<in> images (flatten X)"
  obtain a B where aB_def: "aB = (a, B)"
    by fastforce
  obtain B' where B'_def: "(a, B') \<in> X" "\<And>b. (a, b) \<in> flatten X \<longleftrightarrow> b \<in> B"
    using aB_X
    by (auto simp: flatten_def aB_def images_iff_proj Equiv_Relations.proj_def)
  have "B = B'"
  proof (rule set_eqI, rule iffI)
    fix b
    assume "b \<in> B"
    then have "(a, b) \<in> flatten X"
      using B'_def(2)
      by auto
    then obtain B'' where B''_def: "(a, B'') \<in> X" "b \<in> B''"
      by (auto simp: flatten_def)
    show "b \<in> B'"
      using assms(2)[OF B'_def(1) B''_def(1)] B''_def(2)
      by auto
  next
    fix b'
    assume "b' \<in> B'"
    then show "b' \<in> B"
      using B'_def
      by (auto simp: flatten_def)
  qed
  then show "aB \<in> X"
    using B'_def(1)
    by (auto simp: aB_def)
qed

context ord
begin

definition add_to_rbt :: "'a \<times> 'b \<Rightarrow> ('a, 'b set) rbt \<Rightarrow> ('a, 'b set) rbt" where
  "add_to_rbt = (\<lambda>(a, b) t. case rbt_lookup t a of None \<Rightarrow> rbt_insert a {b} t
  | Some X \<Rightarrow> rbt_insert a (X \<union> {b}) t)"

definition rbt_set_to_rbt :: "('a \<times> 'b, unit) rbt \<Rightarrow> ('a, 'b set) rbt" where
  "rbt_set_to_rbt t = RBT_Impl.fold (\<lambda>ab _. add_to_rbt ab) t RBT_Impl.Empty"

end

context linorder
begin

lemma is_rbt_add_to_rbt: "is_rbt t \<Longrightarrow> is_rbt (add_to_rbt ab t)"
  by (auto simp: add_to_rbt_def split: prod.splits option.splits)

lemma is_rbt_fold_add_to_rbt:
  "is_rbt t' \<Longrightarrow> is_rbt (RBT_Impl.fold (\<lambda>ab _. add_to_rbt ab) t t')"
  by (induction t arbitrary: t') (auto 0 0 simp: is_rbt_add_to_rbt)

lemma is_rbt_rbt_set_to_rbt: "is_rbt (rbt_set_to_rbt t)"
  using is_rbt_fold_add_to_rbt Empty_is_rbt
  by (fastforce simp: rbt_set_to_rbt_def)

lemma rbt_insert_entries_None: "is_rbt t \<Longrightarrow> rbt_lookup t k = None \<Longrightarrow>
  set (RBT_Impl.entries (rbt_insert k v t)) = set (RBT_Impl.entries t) \<union> {(k, v)}"
  by (auto simp: rbt_lookup_in_tree[symmetric] rbt_lookup_rbt_insert split: if_splits)

lemma rbt_insert_entries_Some: "is_rbt t \<Longrightarrow> rbt_lookup t k = Some v' \<Longrightarrow>
  set (RBT_Impl.entries (rbt_insert k v t)) = set (RBT_Impl.entries t) - {(k, v')} \<union> {(k, v)}"
  by (auto simp: rbt_lookup_in_tree[symmetric] rbt_lookup_rbt_insert split: if_splits)

lemma flatten_add_to_rbt: assumes "is_rbt t"
  shows "flatten (set (RBT_Impl.entries (add_to_rbt ab t))) =
    {ab} \<union> flatten (set (RBT_Impl.entries t))"
proof -
  obtain a b where ab_def: "ab = (a, b)"
    by fastforce
  show ?thesis
  proof (cases "rbt_lookup t a")
    case None
    show ?thesis
      by (auto simp: add_to_rbt_def ab_def None flatten_def rbt_insert_entries_None[OF assms None])
  next
    case (Some B)
    show ?thesis
      by (auto simp: add_to_rbt_def ab_def Some flatten_def rbt_insert_entries_Some[OF assms Some]
          split: prod.splits)
         (meson assms Some image_iff is_rbt_rbt_sorted rbt_lookup_in_tree)
  qed
qed

lemma nonempty_add_to_rbt: "is_rbt t \<Longrightarrow> (a, {}) \<notin> set (RBT_Impl.entries t) \<Longrightarrow>
    (a, {}) \<notin> set (RBT_Impl.entries (add_to_rbt ab t))"
  by (auto simp: add_to_rbt_def rbt_insert_entries_None split: prod.splits option.splits)
     (smt insert_not_empty is_rbt_rbt_sorted rbt_insert_rbt_sorted rbt_lookup_in_tree
      rbt_lookup_rbt_insert map_upd_Some_unfold)

lemma flatten_fold_add_to_rbt: "is_rbt t' \<Longrightarrow> (a, {}) \<notin> set (RBT_Impl.entries t') \<Longrightarrow>
  flatten (set (RBT_Impl.entries (RBT_Impl.fold (\<lambda>ab _. add_to_rbt ab) t t'))) =
  set (RBT_Impl.keys t) \<union> flatten (set (RBT_Impl.entries t')) \<and>
  (a, {}) \<notin> set (RBT_Impl.entries (RBT_Impl.fold (\<lambda>ab _. add_to_rbt ab) t t'))"
proof (induction t arbitrary: t')
  case (Branch c t1 ab v t2)
  show ?case
    by (auto simp: Branch(1)[OF Branch(3,4)]
        flatten_add_to_rbt[OF is_rbt_fold_add_to_rbt[OF Branch(3)]]
        Branch(2)[OF is_rbt_add_to_rbt[OF is_rbt_fold_add_to_rbt[OF Branch(3)]],
        OF nonempty_add_to_rbt[OF is_rbt_fold_add_to_rbt[OF Branch(3)], of a t1]])
qed auto

lemma flatten_rbt_set_to_mapping: "flatten (set (RBT_Impl.entries (rbt_set_to_rbt t))) =
  set (RBT_Impl.keys t)"
  by (auto simp: rbt_set_to_rbt_def flatten_fold_add_to_rbt)

lemma nonempty_rbt_set_to_mapping: "(a, {}) \<notin> set (RBT_Impl.entries (rbt_set_to_rbt t))"
  by (auto simp: rbt_set_to_rbt_def flatten_fold_add_to_rbt)

lemma images_rbt_set_to_mapping:
  "images (set (RBT_Impl.keys t)) = set (RBT_Impl.entries (rbt_set_to_rbt t))"
proof -
  have "images (flatten (set (RBT_Impl.entries (rbt_set_to_rbt t)))) =
    set (RBT_Impl.entries (rbt_set_to_rbt t))"
    by (rule images_flatten)
       (auto simp: is_rbt_rbt_set_to_rbt rbt_sorted_entries_right_unique
        nonempty_rbt_set_to_mapping)
  then show ?thesis
    unfolding flatten_rbt_set_to_mapping[of t]
    by simp
qed

lemma proj_rbt_set_to_mapping:
  "Equiv_Relations.proj (set (RBT_Impl.keys t)) a =
  (case map_of (RBT_Impl.entries (rbt_set_to_rbt t)) a of None \<Rightarrow> {} | Some X \<Rightarrow> X)"
  by (auto simp: proj_iff_images' split: option.splits)
     (auto simp: images_rbt_set_to_mapping[symmetric] images_iff_proj
      map_of_eq_None_iff dest: map_of_SomeD intro: fst_imagesI)

end

context 
  fixes c :: "'a comparator"
begin

definition add_to_rbt_comp :: "'a \<times> 'b \<Rightarrow> ('a, 'b set) rbt \<Rightarrow> ('a, 'b set) rbt" where
  "add_to_rbt_comp = (\<lambda>(a, b) t. case rbt_comp_lookup c t a of None \<Rightarrow> rbt_comp_insert c a {b} t
  | Some X \<Rightarrow> rbt_comp_insert c a (X \<union> {b}) t)"

definition rbt_set_to_rbt_comp :: "('a \<times> 'b, unit) rbt \<Rightarrow> ('a, 'b set) rbt" where
  "rbt_set_to_rbt_comp t = RBT_Impl.fold (\<lambda>ab _. add_to_rbt_comp ab) t RBT_Impl.Empty"

context
  assumes c: "comparator c"
begin

lemma add_to_rbt_comp: "add_to_rbt_comp = ord.add_to_rbt (lt_of_comp c)"
  unfolding add_to_rbt_comp_def ord.add_to_rbt_def rbt_comp_lookup[OF c] rbt_comp_insert[OF c]
  by simp

lemma rbt_set_to_rbt_comp: "rbt_set_to_rbt_comp = ord.rbt_set_to_rbt (lt_of_comp c)"
  unfolding rbt_set_to_rbt_comp_def ord.rbt_set_to_rbt_def add_to_rbt_comp
  by simp

end

end

lemma rbt_comp_lookup_map_of:
  fixes t :: "('a :: ccompare, 'b) rbt"
  assumes "ID ccompare = (Some c :: 'a comparator option)"
    and "ord.is_rbt (lt_of_comp c) t"
  shows "rbt_comp_lookup c t = map_of (RBT_Impl.entries t)"
proof -
  have c: "comparator (c :: 'a comparator)"
    using ID_ccompare'[OF assms(1)] .
  show ?thesis
    using linorder.map_of_entries[OF comparator.linorder[OF c]] assms(2)
    unfolding rbt_comp_lookup[OF c] ord.is_rbt_def
    by fastforce
qed

lemma dom_rbt_comp_lookup:
  fixes t :: "('a :: ccompare, 'b) rbt"
  assumes "ID ccompare = (Some c :: 'a comparator option)"
    and "ord.is_rbt (lt_of_comp c) t"
  shows "dom (rbt_comp_lookup c t) = set (RBT_Impl.keys t)"
proof -
  have c: "comparator (c :: 'a comparator)"
    using ID_ccompare'[OF assms(1)] .
  show ?thesis
    using linorder.rbt_lookup_keys[OF comparator.linorder[OF c]] assms(2)
    unfolding rbt_comp_lookup[OF c] ord.is_rbt_def
    by auto
qed

lemma comparator_prod:
  assumes "ID ccompare = (Some ccomp :: 'a :: ccompare comparator option)"
    "ID ccompare = (Some ccomp :: 'b :: ccompare comparator option)"
  shows "ID ccompare = (Some ccomp :: ('a \<times> 'b) comparator option)"
  using assms
  by (auto simp: ccompare_prod_def ID_Some split: option.splits)

lemma comparator_set:
  assumes "ID ccompare = (Some ccomp :: 'a :: ccompare comparator option)"
  shows "ID ccompare = (Some ccomp :: 'a set comparator option)"
  using assms
  by (auto simp: ccompare_set_def ID_Some)
     (metis (no_types, lifting) ID_code map_option_is_None option.collapse option.simps(3))

lemma dom_map_of_map: "distinct xs \<Longrightarrow> dom (map_of (map (\<lambda>x. (x, ())) xs)) = set xs"
  by (induction xs) auto

lemma distinct_map_fstD: "distinct (map fst xs) \<Longrightarrow> distinct xs"
  by (induction xs) auto

context linorder
begin

lemma rbt_bulkload_keys: "distinct xs \<Longrightarrow>
  set (RBT_Impl.keys (rbt_bulkload (map (\<lambda>x. (x, ())) xs))) = set xs"
  by (simp add: rbt_lookup_keys[symmetric] rbt_lookup_rbt_bulkload dom_map_of_map)

end

definition mapping_to_set :: "('a :: ccompare, 'b :: ccompare set) rbt \<Rightarrow>
  ('a \<times> 'b set) set_rbt" where
  "mapping_to_set t = RBT_Mapping2.bulkload (map (\<lambda>x. (x, ())) (RBT_Impl.entries t))"

lemma ccomps:
  assumes "ID ccompare = (Some c :: 'a :: ccompare comparator option)"
    "ID ccompare = (Some c' :: 'b :: ccompare comparator option)"
  shows "ID ccompare = (Some ccomp :: ('a \<times> 'b) comparator option)"
    "ID ccompare = (Some ccomp :: ('a \<times> 'b set) comparator option)"
  subgoal
    using comparator_prod assms
    by force
  subgoal
    using comparator_prod comparator_set assms
    by (metis option.collapse option.simps(3))
  done

lemma proj_code[code]:
  fixes t :: "('a :: ccompare \<times> 'b :: ccompare) set_rbt"
  shows "Equiv_Relations.proj (RBT_set t) = (case ID CCOMPARE('a) of None \<Rightarrow>
    Code.abort (STR ''proj: ccompare = None'') (\<lambda>_. Equiv_Relations.proj (RBT_set t))
  | Some c \<Rightarrow> (case ID CCOMPARE('b) of None \<Rightarrow>
    Code.abort (STR ''proj: ccompare = None'') (\<lambda>_. Equiv_Relations.proj (RBT_set t))
  | Some _ \<Rightarrow> let m = rbt_set_to_rbt_comp c (RBT_Mapping2.impl_of t) in
    (\<lambda>a. (case rbt_comp_lookup c m a of None \<Rightarrow> {} | Some X \<Rightarrow> X))))"
proof -
  {
    fix t c c'
    assume assms: "ord.is_rbt cless (t :: ('a \<times> 'b, unit) rbt) \<or>
      ID ccompare = (None :: ('a \<times> 'b) comparator option)"
      "ID ccompare = (Some c :: 'a comparator option)"
      "ID ccompare = (Some c' :: 'b comparator option)"
    note cab_ID_ccomp = ccomps(1)[OF assms(2,3)]
    have is_rbt_t: "ord.is_rbt cless t"
      using cab_ID_ccomp mapping_comparator assms(1)
      by auto
    have c: "comparator (c :: 'a comparator)"
      using ID_ccompare'[OF assms(2)] .
    note c_class = comparator.linorder[OF c]
    have rbt_comp_lookup: "rbt_comp_lookup c (rbt_set_to_rbt_comp c t) =
      map_of (RBT_Impl.entries (ord.rbt_set_to_rbt (lt_of_comp c) t))"
      unfolding rbt_comp_lookup_map_of[OF assms(2) linorder.is_rbt_rbt_set_to_rbt[OF c_class]]
        rbt_set_to_rbt_comp[OF c]
      by (rule refl)
    note linorder.proj_rbt_set_to_mapping[OF comparator.linorder[OF c], of t, folded rbt_comp_lookup]
      dom_rbt_comp_lookup[OF cab_ID_ccomp is_rbt_t]
  }
  note rw = this
  show ?thesis
    unfolding RBT_set_def
    using rw
    by transfer (auto split: option.splits)
qed

lemma images_code[code]:
  fixes t :: "('a :: ccompare \<times> 'b :: ccompare) set_rbt"
  shows "images (RBT_set t) = (case ID CCOMPARE('a) of None \<Rightarrow>
    Code.abort (STR ''images: ccompare = None'') (\<lambda>_. images (RBT_set t))
    | Some c \<Rightarrow> (case ID CCOMPARE('b) of None \<Rightarrow>
    Code.abort (STR ''images: ccompare = None'') (\<lambda>_. images (RBT_set t))
    | Some _ \<Rightarrow> RBT_set (mapping_to_set (rbt_set_to_rbt_comp c (RBT_Mapping2.impl_of t)))))"
proof -
  {
    fix t c c'
    assume assms: "ord.is_rbt cless (t :: ('a \<times> 'b, unit) rbt) \<or>
      ID ccompare = (None :: ('a \<times> 'b) comparator option)"
      "ID ccompare = (Some c :: 'a comparator option)"
      "ID ccompare = (Some c' :: 'b comparator option)"
    note cab_ID_ccomp = ccomps(1)[OF assms(2,3)]
    note cab_set_ID_ccomp = ccomps(2)[OF assms(2,3)]
    have is_rbt_t: "ord.is_rbt cless t"
      using cab_ID_ccomp mapping_comparator assms(1)
      by auto
    have c: "comparator (c :: 'a comparator)"
      using ID_ccompare'[OF assms(2)] .
    have cab_set_ccomp: "comparator (ccomp :: ('a \<times> 'b set) comparator)"
      using ID_ccompare'[OF cab_set_ID_ccomp] .
    note c_class = comparator.linorder[OF c]
    note cab_set_class = comparator.linorder[OF cab_set_ccomp]
    have distinct: "distinct (RBT_Impl.entries (ord.rbt_set_to_rbt (lt_of_comp c) t))"
      using linorder.distinct_entries[OF c_class, of "ord.rbt_set_to_rbt (lt_of_comp c) t"]
        linorder.is_rbt_rbt_set_to_rbt[OF c_class, of t]
      by (auto simp: ord.is_rbt_def dest: distinct_map_fstD)
    have "images (dom (rbt_comp_lookup ccomp t)) = dom (rbt_comp_lookup ccomp
      (rbt_comp_bulkload ccomp (map (\<lambda>x. (x, ())) (RBT_Impl.entries (rbt_set_to_rbt_comp c t)))))"
      by (simp add: dom_rbt_comp_lookup[OF cab_ID_ccomp is_rbt_t]
          linorder.images_rbt_set_to_mapping[OF c_class]
          rbt_set_to_rbt_comp[OF c] rbt_comp_bulkload[OF cab_set_ccomp]
          dom_rbt_comp_lookup[OF cab_set_ID_ccomp linorder.rbt_bulkload_is_rbt[OF cab_set_class]]
          linorder.rbt_bulkload_keys[OF cab_set_class distinct])
  }
  then show ?thesis
    unfolding RBT_set_def mapping_to_set_def
    by transfer (simp split: option.splits)
qed

end