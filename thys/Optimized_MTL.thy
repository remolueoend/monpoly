(*<*)
theory Optimized_MTL
  imports Monitor
begin
(*>*)

lemma less_enat_iff: "a < enat i \<longleftrightarrow> (\<exists>j. a = enat j \<and> j < i)"
  by (cases a) auto

(* Optimized joins *)

definition join_mask :: "nat \<Rightarrow> nat set \<Rightarrow> bool list" where
  "join_mask n X = map (\<lambda>i. i \<in> X) [0..<n]"

fun proj_tuple :: "bool list \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple" where
  "proj_tuple [] [] = []"
| "proj_tuple (True # bs) (a # as) = a # proj_tuple bs as"
| "proj_tuple (False # bs) (a # as) = None # proj_tuple bs as"
| "proj_tuple (b # bs) [] = []"
| "proj_tuple [] (a # as) = []"

lemma proj_tuple_replicate: "(\<And>i. i \<in> set bs \<Longrightarrow> \<not>i) \<Longrightarrow> length bs = length as \<Longrightarrow>
  proj_tuple bs as = replicate (length bs) None"
  by (induction bs as rule: proj_tuple.induct) fastforce+

lemma proj_tuple_join_mask_empty: "length as = n \<Longrightarrow>
  proj_tuple (join_mask n {}) as = replicate n None"
  using proj_tuple_replicate[of "join_mask n {}"] by (auto simp add: join_mask_def)

lemma proj_tuple_alt: "proj_tuple bs as = map2 (\<lambda>b a. if b then a else None) bs as"
  by (induction bs as rule: proj_tuple.induct) auto

lemma map2_map: "map2 f (map g [0..<length as]) as = map (\<lambda>i. f (g i) (as ! i)) [0..<length as]"
  by (rule nth_equalityI) auto

lemma proj_tuple_join_mask_restrict: "length as = n \<Longrightarrow>
  proj_tuple (join_mask n X) as = restrict X as"
  by (auto simp add: restrict_def proj_tuple_alt join_mask_def map2_map)

lemma wf_tuple_proj_idle:
  assumes wf: "wf_tuple n X as"
  shows "proj_tuple (join_mask n X) as = as"
  using proj_tuple_join_mask_restrict[of as n X, unfolded restrict_idle[OF wf]] wf
  by (auto simp add: wf_tuple_def)

lemma wf_tuple_change_base:
  assumes wf: "wf_tuple n X as"
  and mask: "join_mask n X = join_mask n Y"
  shows "wf_tuple n Y as"
  using wf mask by (auto simp add: wf_tuple_def join_mask_def)

definition proj_tuple_in_join :: "bool \<Rightarrow> bool list \<Rightarrow> 'a tuple \<Rightarrow> 'a table \<Rightarrow> bool" where
  "proj_tuple_in_join pos bs as t = (if pos then proj_tuple bs as \<in> t else proj_tuple bs as \<notin> t)"

abbreviation "join_cond pos t \<equiv> (\<lambda>as. if pos then as \<in> t else as \<notin> t)"

abbreviation "join_filter_cond pos t \<equiv> (\<lambda>as _. join_cond pos t as)"

lemma proj_tuple_in_join_mask_idle:
  assumes wf: "wf_tuple n X as"
  shows "proj_tuple_in_join pos (join_mask n X) as t \<longleftrightarrow> join_cond pos t as"
  using wf_tuple_proj_idle[OF wf] by (auto simp add: proj_tuple_in_join_def)

lemma join_sub:
  assumes "L \<subseteq> R" "table n L t1" "table n R t2"
  shows "join t2 pos t1 = {as \<in> t2. proj_tuple_in_join pos (join_mask n L) as t1}"
  using assms proj_tuple_join_mask_restrict[of _ n L] join_restrict[of t2 n R t1 L pos]
    wf_tuple_length restrict_idle
  by (auto simp add: table_def proj_tuple_in_join_def sup.absorb1) fastforce+

lemma join_eq:
  assumes tab: "table n R t1" "table n R t2"
  shows "join t2 pos t1 = (if pos then t2 \<inter> t1 else t2 - t1)"
  using join_sub[OF _ tab, of pos] tab(2) proj_tuple_in_join_mask_idle[of n R _ pos t1]
  by (auto simp add: table_def)

lemma join_empty:
  assumes tab: "table n {} t1" "table n R t2"
  shows "join t2 pos t1 = (if (pos \<longleftrightarrow> replicate n None \<in> t1) then t2 else {})"
  using join_sub[OF _ tab, of pos] tab(2)
  by (auto simp add: table_def proj_tuple_in_join_def wf_tuple_length proj_tuple_join_mask_empty)

lemma mmulti_join_one:
  assumes "table n A X" "wf_set n A"
  shows "mmulti_join [A] [] [X] = X"
  using assms mmulti_join_correct[of "[A]" n "[]" "[X]"]
  by (auto simp add: table_def restrict_idle simp del: mmulti_join.simps)

lemma join_restrict_True: "table n A t \<Longrightarrow> table n A' t' \<Longrightarrow>
  wf_tuple n Z x \<Longrightarrow> A \<union> A' \<subseteq> Z \<Longrightarrow> restrict (A \<union> A') x \<in> join t True t' \<longleftrightarrow>
  restrict A x \<in> t \<and> restrict A' x \<in> t'"
  using join_restrict[of t n A t' A' True "restrict (A \<union> A') x"]
    wf_tuple_restrict_simple[of n Z x "A \<union> A'"]
  by (auto simp add: table_def Int_absorb2 Generic_Join_Correctness.New_max.restrict_nested)

lemmas restrict_nested = Generic_Join_Correctness.New_max.restrict_nested

lemma mmulti_join_step_True:
  assumes "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) (A # A' # A_pos) (t # t' # L)"
    "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) A_neg L_neg"
  shows "mmulti_join (A # A' # A_pos) A_neg (t # (t' # L) @ L_neg) =
    mmulti_join ((A \<union> A') # A_pos) A_neg (join t True t' # L @ L_neg)"
proof (rule set_eqI, rule iffI)
  fix x
  assume "x \<in> mmulti_join (A # A' # A_pos) A_neg (t # (t' # L) @ L_neg)"
  then have x_mmulti_join_dest: "wf_tuple n (\<Union>A\<in>set (A # A' # A_pos). A) x"
    "list_all2 (\<lambda>A. (\<in>) (restrict A x)) (A # A' # A_pos) (t # t' # L)"
    "list_all2 (\<lambda>A. (\<notin>) (restrict A x)) A_neg L_neg"
    using mmulti_join_correct[of "A # A' # A_pos" n A_neg "t # t' # L @ L_neg" x] assms
    by (auto simp add: list_all2_appendI simp del: mmulti_join.simps dest: list_all2_lengthD)
  moreover have "table n (A \<union> A') (join t True t')" "wf_set n (A \<union> A')"
    using join_table[of n A t A' t' True "A \<union> A'"] assms by (auto simp add: wf_set_def)
  moreover have "restrict (A \<union> A') x \<in> join t True t'"
    using join_restrict_True[of n A t A' t'] assms x_mmulti_join_dest
    by (auto simp add: list_all2_appendI dest: list_all2_lengthD)
  ultimately show "x \<in> mmulti_join ((A \<union> A') # A_pos) A_neg (join t True t' # L @ L_neg)"
    using mmulti_join_correct[of "(A \<union> A') # A_pos" n A_neg "join t True t' # L @ L_neg"] assms
    by (auto simp add: wf_tuple_def list_all2_appendI dest: list_all2_lengthD)
next
  fix x
  assume "x \<in> mmulti_join ((A \<union> A') # A_pos) A_neg (join t True t' # L @ L_neg)"
  then have x_mmulti_join_dest: "wf_tuple n (\<Union>A\<in>set ((A \<union> A') # A_pos). A) x"
    "list_all2 (\<lambda>A. (\<in>) (restrict A x)) ((A \<union> A') # A_pos) (join t True t' # L)"
    "list_all2 (\<lambda>A. (\<notin>) (restrict A x)) A_neg L_neg"
    using mmulti_join_correct[of "(A \<union> A') # A_pos" n A_neg "join t True t' # L @ L_neg" x] assms
      join_table[of n A t A' t' True "A \<union> A'"]
    by (auto simp add: wf_set_def list_all2_appendI simp del: mmulti_join.simps
        dest!: list_all2_lengthD) fastforce+
  moreover have "restrict A x \<in> t" "restrict A' x \<in> t'"
    using x_mmulti_join_dest join_restrict_True[of n A t A' t' _ x] assms by auto
  ultimately show "x \<in> mmulti_join (A # A' # A_pos) A_neg (t # (t' # L) @ L_neg)"
    using mmulti_join_correct[of "A # A' # A_pos" n A_neg "t # (t' # L) @ L_neg" x] assms
    by (auto simp add: wf_tuple_def list_all2_appendI dest: list_all2_lengthD)
qed

lemma mmulti_join_True_fold:
  assumes "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) A_pos L"
    "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) A_neg L_neg"
    "table n A t" "wf_set n A"
  shows "mmulti_join (A # A_pos) A_neg (t # L @ L_neg) =
    mmulti_join [\<Union>(set (A # A_pos))] A_neg ((foldl (\<lambda>r a. join r True a) t L) # L_neg)"
  using assms
proof (induction A_pos L arbitrary: A t rule: list_all2_induct)
  case Nil
  then show ?case
    by auto
next
  case (Cons A' A_pos t' L)
  have mm_step: "mmulti_join (A # A' # A_pos) A_neg (t # (t' # L) @ L_neg) =
    mmulti_join ((A \<union> A') # A_pos) A_neg (join t True t' # L @ L_neg)"
    using mmulti_join_step_True Cons by blast
  have set_unfold: "\<Union> (set (A # A' # A_pos)) = \<Union>(set ((A \<union> A') # A_pos))"
    by auto
  have "table n (A \<union> A') (join t True t')"
    using join_table[of n A t A' t' True "A \<union> A'"] Cons by auto
  moreover have "wf_set n (A \<union> A')"
    using Cons by (auto simp add: wf_set_def)
  ultimately show ?case
    unfolding mm_step set_unfold foldl.simps
    using Cons(3)[of "A \<union> A'" "join t True t'"] Cons by blast
qed

lemma mmulti_join_step_False:
  assumes "table n A t" "wf_set n A" "table n A' t'" "wf_set n A'" "A' \<subseteq> A"
    "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) A_neg L_neg"
    "\<And>An. An \<in> set A_neg \<Longrightarrow> An \<subseteq> A"
  shows "mmulti_join [A] (A' # A_neg) (t # t' # L_neg) =
    mmulti_join [A] A_neg (join t False t' # L_neg)"
proof (rule set_eqI, rule iffI)
  fix x
  assume "x \<in> mmulti_join [A] (A' # A_neg) (t # t' # L_neg)"
  then have x_mmulti_join_dest: "wf_tuple n A x" "restrict A x \<in> t"
    "list_all2 (\<lambda>A. (\<notin>) (restrict A x)) (A' # A_neg) (t' # L_neg)"
    using mmulti_join_correct[of "[A]" n "A' # A_neg" "t # t' # L_neg" x] assms
    by (auto simp add: list_all2_appendI simp del: mmulti_join.simps dest: list_all2_lengthD)
  moreover have "table n A (join t False t')"
    using join_table[OF assms(1,3), of False] assms(5) by (auto simp add: table_def)
  moreover have "restrict A x \<in> join t False t'"
  proof -
    have "restrict A (restrict A x) \<in> t"
      using x_mmulti_join_dest(2) by (auto simp add: restrict_nested)
    moreover have "restrict A' (restrict A x) \<notin> t'"
      using restrict_idle[OF x_mmulti_join_dest(1)] x_mmulti_join_dest(3) by auto
    ultimately show ?thesis
      using join_restrict[of t n A t' A' False "restrict A x"]
        wf_tuple_restrict[OF x_mmulti_join_dest(1), of A A] assms(1,3,5)
      by (auto simp add: table_def sup.absorb1)
  qed
  ultimately show "x \<in> mmulti_join [A] A_neg (join t False t' # L_neg)"
    using mmulti_join_correct[of "[A]" n "A_neg" "join t False t' # L_neg" x] assms
    by (auto simp add: list_all2_appendI simp del: mmulti_join.simps dest: list_all2_lengthD)
next
  fix x
  assume assm: "x \<in> mmulti_join [A] A_neg (join t False t' # L_neg)"
  then have x_mmulti_join_dest: "wf_tuple n (\<Union>A\<in>set [A]. A) x" "restrict A x \<in> join t False t'"
    "list_all2 (\<lambda>A. (\<notin>) (restrict A x)) A_neg L_neg"
    using mmulti_join_correct[of "[A]" n A_neg "join t False t' # L_neg" x] assms(2,5,6)
      join_table[OF assms(1,3), of False]
    by (auto simp add: list_all2_appendI simp del: mmulti_join.simps dest: list_all2_lengthD)
  moreover have "restrict A x \<in> t" "restrict A' x \<notin> t'"
    using join_restrict[of t n A t' A' False "restrict A x"] assms(1,3,5) x_mmulti_join_dest(2)
    by (auto simp add: table_def restrict_nested Int_absorb2)
  ultimately show "x \<in> mmulti_join [A] (A' # A_neg) (t # t' # L_neg)"
    using mmulti_join_correct[of "[A]" n "A' # A_neg" "t # t' # L_neg" x] assms
    by (auto simp add: list_all2_appendI simp del: mmulti_join.simps dest: list_all2_lengthD)
qed

lemma mmulti_join_False_fold:
  assumes "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) A_neg L_neg"
    "table n A t" "wf_set n A"
    "\<And>An. An \<in> set A_neg \<Longrightarrow> An \<subseteq> A"
  shows "mmulti_join [A] A_neg (t # L_neg) = foldl (\<lambda>r a. join r False a) t L_neg"
  using assms
proof (induction A_neg L_neg arbitrary: t rule: list_all2_induct)
  case Nil
  show ?case
    using mmulti_join_one[OF Nil(1,2)] by auto
next
  case (Cons A' A_neg t' L_neg)
  have "mmulti_join [A] (A' # A_neg) (t # t' # L_neg) =
    mmulti_join [A] A_neg (join t False t' # L_neg)"
    using mmulti_join_step_False[OF Cons(4,5) _ _ _ Cons(2)] Cons(1,6) by auto
  moreover have "\<dots> = foldl (\<lambda>r. join r False) t (t' # L_neg)"
    using Cons(3)[of "join t False t'"] Cons(1,5,6) join_table[OF Cons(4), of A' t' False A]
    by auto
  finally show ?case .
qed

lemma fold_join_table:
  assumes "list_all2 (\<lambda>A X. table n A X) A_pos L_pos" "table n A t"
  shows "table n (\<Union>(set (A # A_pos))) (foldl (\<lambda>r. join r True) t L_pos)"
  using assms
proof (induction A_pos L_pos arbitrary: A t rule: list_all2_induct)
  case (Cons A' A_pos t' L_pos)
  show ?case
    using Cons(3)[of "A \<union> A'" "join t True t'", OF join_table[OF Cons(4,1)]]
    by (auto simp add: Un_assoc)
qed auto

lemma list_all2_weaken: "list_all2 P xs ys \<Longrightarrow> (\<And>x y. P x y \<Longrightarrow> P' x y) \<Longrightarrow>
  list_all2 P' xs ys"
  by (induction xs ys rule: list_all2_induct) auto

lemma mmulti_join_fold:
  assumes "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) (A # A_pos @ A_neg) (t # L_pos @ L_neg)"
    "\<And>An. An \<in> set A_neg \<Longrightarrow> An \<subseteq> \<Union>(set (A # A_pos))" "length A_pos = length L_pos"
  shows "mmulti_join (A # A_pos) A_neg (t # L_pos @ L_neg) = foldl (\<lambda>r a. join r False a)
    (foldl (\<lambda>r a. join r True a) t L_pos) L_neg"
proof -
  have list_all2_pos: "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) A_pos L_pos"
    using assms(1,3) by (auto simp add: list_all2_Cons1 list_all2_append1)
  have tab_Un: "table n (\<Union>(set (A # A_pos))) (foldl (\<lambda>r. join r True) t L_pos)"
    using fold_join_table[OF list_all2_weaken[OF list_all2_pos, of "table n"]] assms(1)
    by (auto simp add: list_all2_Cons1 list_all2_append1)
  have wf_set_Un: "wf_set n (\<Union>(set (A # A_pos)))"
    using assms(1)
    by (auto simp add: wf_set_def list_all2_Cons1 list_all2_append1)
       (metis (no_types, lifting) list_all2_Cons1 list_all2_append1 split_list)
  have "mmulti_join (A # A_pos) A_neg (t # L_pos @ L_neg) = mmulti_join [\<Union>(set (A # A_pos))]
    A_neg (foldl (\<lambda>r. join r True) t L_pos # L_neg)"
    using mmulti_join_True_fold[of n A_pos L_pos]
      assms by (auto simp add: list_all2_append1 simp del: mmulti_join.simps)
  moreover have "\<dots> = foldl (\<lambda>r a. join r False a)
    (foldl (\<lambda>r a. join r True a) t L_pos) L_neg"
    using mmulti_join_False_fold[of n A_neg L_neg]
      assms tab_Un wf_set_Un by (auto simp add: list_all2_append1 simp del: mmulti_join.simps)
  finally show ?thesis .
qed

lemma foldl_commute_base: "(\<And>a b c. P a \<Longrightarrow> P b \<Longrightarrow> P c \<Longrightarrow> f (f a c) b = f (f a b) c) \<Longrightarrow>
  (\<And>a b. P a \<Longrightarrow> P b \<Longrightarrow> P (f a b)) \<Longrightarrow>
  (\<And>a. a \<in> set (x # y # xs @ ys) \<Longrightarrow> P a) \<Longrightarrow>
  foldl f x (xs @ y # ys) = foldl f x (y # xs @ ys)"
proof (induction xs arbitrary: x)
  case (Cons z zs)
  have shift: "f (f x z) y = f (f x y) z"
    using Cons(2)[OF Cons(4) Cons(4) Cons(4), of x y z, simplified] .
  have "foldl f x ((z # zs) @ y # ys) = foldl f (f x z) (zs @ y # ys)"
    by simp
  moreover have "\<dots> = foldl f (f x z) (y # zs @ ys)"
    using Cons(1)[of "f x z"] Cons(2,3,4) by fastforce
  moreover have "\<dots> = foldl f x (y # z # zs @ ys)"
    by (auto simp add: shift)
  ultimately show ?case
    by auto
qed auto

lemma foldl_commute: "(\<And>a b c. P a \<Longrightarrow> P b \<Longrightarrow> P c \<Longrightarrow> f (f a c) b = f (f a b) c) \<Longrightarrow>
  (\<And>a b. P a \<Longrightarrow> P b \<Longrightarrow> P (f a b)) \<Longrightarrow>
  (\<And>a. a \<in> set (e # x # y # xs @ ys @ zs) \<Longrightarrow> P a) \<Longrightarrow>
  foldl f e (zs @ x # xs @ y # ys) = foldl f e (zs @ x # y # xs @ ys)"
  apply (induction zs arbitrary: e)
  subgoal for e
    using foldl_commute_base[of P f "f e x" y xs ys]
    by force
  by force

lemma foldl_assoc: "(\<And>a b c. P a \<Longrightarrow> P b \<Longrightarrow> P c \<Longrightarrow> f (f a b) c = f a (f b c)) \<Longrightarrow>
  (\<And>a b. P a \<Longrightarrow> P b \<Longrightarrow> P (f a b)) \<Longrightarrow>
  (\<And>a. a \<in> set (e # x # y # ys @ zs) \<Longrightarrow> P a) \<Longrightarrow>
  foldl f e (zs @ x # y # ys) = foldl f e (zs @ f x y # ys)"
  by (induction zs arbitrary: e) force+

lemma join_True_commute: "table n A t \<Longrightarrow> table n A' t' \<Longrightarrow> table n A'' t'' \<Longrightarrow>
  join (join t True t'') True t' = join (join t True t') True t''"
  using join_restrict[of t n A t' A' True] join_restrict[of t n A t'' A'' True]
    join_restrict[of "join t True t'" n "A \<union> A'" t'' A'' True]
    join_restrict[of "join t True t''" n "A \<union> A''" t' A' True]
    join_table[of n A t A' t' True "A \<union> A'"]
    join_table[of n A t A'' t'' True "A \<union> A''"]
  by (auto simp add: table_def sup_assoc sup_commute sup_left_commute restrict_nested
      wf_tuple_restrict_simple Int_absorb2 sup.order_iff)

lemma join_True_assoc: "table n A t \<Longrightarrow> table n A' t' \<Longrightarrow> table n A'' t'' \<Longrightarrow>
  join (join t True t') True t'' = join t True (join t' True t'')"
  using join_restrict[of t n A t' A' True] join_restrict[of t' n A' t'' A'' True]
    join_restrict[of "join t True t'" n "A \<union> A'" t'' A'' True]
    join_restrict[of t n A "join t' True t''" "A' \<union> A''" True]
  by (auto simp add: table_def sup_assoc restrict_nested wf_tuple_restrict_simple Int_absorb2)
     (metis sup.cobounded1 sup_assoc wf_tuple_restrict_simple)

lemma join_False_commute: "table n A t \<Longrightarrow> table n A' t' \<Longrightarrow> A' \<subseteq> A \<Longrightarrow>
  table n A'' t'' \<Longrightarrow> A'' \<subseteq> A \<Longrightarrow>
  join (join t False t') False t'' = join (join t False t'') False t'"
  using join_restrict[of t n A t' A' False] join_restrict[of t n A t'' A'' False]
    join_restrict[of "join t False t'" n A t'' A'' False]
    join_restrict[of "join t False t''" n A t' A' False]
  by (auto simp add: table_def sup.order_iff restrict_nested Int_absorb2)

(* Optimized since data structure *)

type_synonym 'a queue = "'a list \<times> 'a list"

definition linearize :: "'a queue \<Rightarrow> 'a list" where
  "linearize q = (case q of (ls, fs) \<Rightarrow> ls @ rev fs)"

definition empty_queue :: "'a queue" where
  "empty_queue = ([], [])"

lemma empty_queue_rep: "linearize empty_queue = []"
  unfolding empty_queue_def by (simp add: linearize_def)

definition prepend_queue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "prepend_queue a q = (case q of (ls, fs) \<Rightarrow> (a # ls, fs))"

lemma prepend_queue_rep: "linearize (prepend_queue a q) = a # linearize q"
  by (auto simp add: linearize_def prepend_queue_def split: prod.splits)

definition append_queue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "append_queue a q = (case q of (ls, fs) \<Rightarrow> (ls, a # fs))"

lemma append_queue_rep: "linearize (append_queue a q) = linearize q @ [a]"
  by (auto simp add: linearize_def append_queue_def split: prod.splits)

fun safe_hd :: "'a queue \<Rightarrow> 'a option \<times> 'a queue" where
  "safe_hd ([], []) = (None, ([], []))"
| "safe_hd ([], fs) = (let ls = rev fs in (Some (hd ls), (ls, [])))"
| "safe_hd (a # as, fs) = (Some a, (a # as, fs))"

lemma safe_hd_rep: "safe_hd q = (\<alpha>, q') \<Longrightarrow> linearize q = linearize q' \<and>
  (case \<alpha> of None \<Rightarrow> linearize q = [] | Some a \<Rightarrow> linearize q \<noteq> [] \<and> a = hd (linearize q))"
  by (auto simp add: linearize_def Let_def split: prod.splits option.splits elim: safe_hd.elims)

lemma safe_hd_Cons: "xs \<noteq> [] \<Longrightarrow> safe_hd (xs, []) = (Some (hd xs), (xs, []))"
  by (cases xs) auto

lemma safe_hd_idem: "safe_hd q = (a, q') \<Longrightarrow> safe_hd q' = (a, q')"
  by (auto simp add: Let_def safe_hd_Cons elim: safe_hd.elims)

fun tl_queue :: "'a queue \<Rightarrow> 'a queue" where
  "tl_queue ([], fs) = (tl (rev fs), [])"
| "tl_queue (a # as, fs) = (as, fs)"

lemma tl_queue_rep: "linearize (tl_queue q) = tl (linearize q)"
  by (auto simp add: linearize_def split: prod.splits elim: tl_queue.elims)

lemma length_tl_queue_rep: "linearize q \<noteq> [] \<Longrightarrow>
  length (linearize (tl_queue q)) < length (linearize q)"
  unfolding tl_queue_rep by simp

lemma length_tl_queue_safe_hd:
  assumes "safe_hd q = (Some a, q')"
  shows "length (linearize (tl_queue q')) < length (linearize q)"
  using safe_hd_rep[OF assms] by (auto simp add: length_tl_queue_rep)

function dropWhile_queue :: "('a \<Rightarrow> bool) \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "dropWhile_queue f q = (case safe_hd q of (None, q') \<Rightarrow> q'
  | (Some a, q') \<Rightarrow> if f a then dropWhile_queue f (tl_queue q') else q')"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(f, q). length (linearize q))") (fastforce split: prod.splits)+

lemma dropWhile_hd_tl: "xs \<noteq> [] \<Longrightarrow>
  dropWhile P xs = (if P (hd xs) then dropWhile P (tl xs) else xs)"
  by (cases xs) auto

lemma dropWhile_queue_rep: "linearize (dropWhile_queue f q) = dropWhile f (linearize q)"
  by (induction f q rule: dropWhile_queue.induct)
     (auto simp add: safe_hd_idem tl_queue_rep dropWhile_hd_tl
      split: prod.splits option.splits dest: safe_hd_rep)

function takeWhile_queue :: "('a \<Rightarrow> bool) \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "takeWhile_queue f q = (case safe_hd q of (None, q') \<Rightarrow> q'
  | (Some a, q') \<Rightarrow> if f a
    then prepend_queue a (takeWhile_queue f (tl_queue q'))
    else empty_queue)"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(f, q). length (linearize q))") (fastforce split: prod.splits)+

lemma takeWhile_hd_tl: "xs \<noteq> [] \<Longrightarrow>
  takeWhile P xs = (if P (hd xs) then hd xs # takeWhile P (tl xs) else [])"
  by (cases xs) auto

lemma takeWhile_queue_rep: "linearize (takeWhile_queue f q) = takeWhile f (linearize q)"
  by (induction f q rule: takeWhile_queue.induct)
     (auto simp add: prepend_queue_rep tl_queue_rep empty_queue_rep takeWhile_hd_tl
      split: prod.splits option.splits dest: safe_hd_rep)

function takedropWhile_queue :: "('a \<Rightarrow> bool) \<Rightarrow> 'a queue \<Rightarrow> 'a queue \<times> 'a list" where
  "takedropWhile_queue f q = (case safe_hd q of (None, q') \<Rightarrow> (q', [])
  | (Some a, q') \<Rightarrow> if f a
    then (case takedropWhile_queue f (tl_queue q') of (q'', as) \<Rightarrow> (q'', a # as))
    else (q', []))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(f, q). length (linearize q))") (fastforce split: prod.splits)+

lemma takedropWhile_queue_fst: "fst (takedropWhile_queue f q) = dropWhile_queue f q"
  apply (induction f q rule: takedropWhile_queue.induct)
  by (auto split: prod.splits) (auto simp add: case_prod_unfold split: option.splits)

lemma takedropWhile_queue_snd: "snd (takedropWhile_queue f q) = takeWhile f (linearize q)"
  apply (induction f q rule: takedropWhile_queue.induct)
  by (auto split: prod.splits)
     (auto simp add: case_prod_unfold tl_queue_rep takeWhile_hd_tl
      split: option.splits dest: safe_hd_rep)

type_synonym 'a mmsaux = "ts \<times> ts \<times> \<I> \<times> bool list \<times> bool list \<times>
  (ts \<times> 'a table) queue \<times> (ts \<times> 'a table) queue \<times>
  (('a tuple, ts) mapping) \<times> (('a tuple, ts) mapping)"

fun time_mmsaux :: "'a mmsaux \<Rightarrow> ts" where
  "time_mmsaux aux = (case aux of (nt, _) \<Rightarrow> nt)"

definition ts_tuple_rel :: "(ts \<times> 'a table) set \<Rightarrow> (ts \<times> 'a tuple) set" where
  "ts_tuple_rel ys = {(t, as). \<exists>X. as \<in> X \<and> (t, X) \<in> ys}"

lemma finite_fst_ts_tuple_rel: "finite (fst ` {tas \<in> ts_tuple_rel (set xs). P tas})"
proof -
  have "fst ` {tas \<in> ts_tuple_rel (set xs). P tas} \<subseteq> fst ` ts_tuple_rel (set xs)"
    by auto
  moreover have "\<dots> \<subseteq> set (map fst xs)"
    by (force simp add: ts_tuple_rel_def)
  finally show ?thesis
    using finite_subset by blast
qed

lemma ts_tuple_rel_ext_Cons: "tas \<in> ts_tuple_rel {(nt, X)} \<Longrightarrow>
  tas \<in> ts_tuple_rel (set ((nt, X) # tass))"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_ext_Cons': "tas \<in> ts_tuple_rel (set tass) \<Longrightarrow>
  tas \<in> ts_tuple_rel (set ((nt, X) # tass))"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_intro: "as \<in> X \<Longrightarrow> (t, X) \<in> ys \<Longrightarrow> (t, as) \<in> ts_tuple_rel ys"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_dest: "(t, as) \<in> ts_tuple_rel ys \<Longrightarrow> \<exists>X. (t, X) \<in> ys \<and> as \<in> X"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_Un: "ts_tuple_rel (ys \<union> zs) = ts_tuple_rel ys \<union> ts_tuple_rel zs"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_ext: "tas \<in> ts_tuple_rel {(nt, X)} \<Longrightarrow>
  tas \<in> ts_tuple_rel (set ((nt, Y \<union> X) # tass))"
proof -
  assume assm: "tas \<in> ts_tuple_rel {(nt, X)}"
  then obtain as where tas_def: "tas = (nt, as)" "as \<in> X"
    by (cases tas) (auto simp add: ts_tuple_rel_def)
  then have "as \<in> Y \<union> X"
    by auto
  then show "tas \<in> ts_tuple_rel (set ((nt, Y \<union> X) # tass))"
    unfolding tas_def(1)
    apply (rule ts_tuple_rel_intro)
    by auto
qed

lemma ts_tuple_rel_ext': "tas \<in> ts_tuple_rel (set ((nt, X) # tass)) \<Longrightarrow>
  tas \<in> ts_tuple_rel (set ((nt, X \<union> Y) # tass))"
proof -
  assume assm: "tas \<in> ts_tuple_rel (set ((nt, X) # tass))"
  then have "tas \<in> ts_tuple_rel {(nt, X)} \<union> ts_tuple_rel (set tass)"
    using ts_tuple_rel_Un by force
  then show "tas \<in> ts_tuple_rel (set ((nt, X \<union> Y) # tass))"
    apply (rule UnE)
    using ts_tuple_rel_ext Un_commute apply metis
    using ts_tuple_rel_ext_Cons' by fastforce
qed

lemma ts_tuple_rel_mono: "ys \<subseteq> zs \<Longrightarrow> ts_tuple_rel ys \<subseteq> ts_tuple_rel zs"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_filter: "ts_tuple_rel (set (filter (\<lambda>(t, X). P t) xs)) =
  {(t, X) \<in> ts_tuple_rel (set xs). P t}"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_set_filter: "x \<in> ts_tuple_rel (set (filter P xs)) \<Longrightarrow>
  x \<in> ts_tuple_rel (set xs)"
  by (auto simp add: ts_tuple_rel_def)

definition valid_tuple :: "(('a tuple, ts) mapping) \<Rightarrow> (ts \<times> 'a tuple) \<Rightarrow> bool" where
  "valid_tuple tuple_since = (\<lambda>(t, as). case Mapping.lookup tuple_since as of None \<Rightarrow> False
  | Some t' \<Rightarrow> t \<ge> t')"

definition safe_max :: "'a :: linorder set \<Rightarrow> 'a option" where
  "safe_max X = (if X = {} then None else Some (Max X))"

lemma safe_max_empty: "safe_max X = None \<longleftrightarrow> X = {}"
  by (simp add: safe_max_def)

lemma safe_max_empty_dest: "safe_max X = None \<Longrightarrow> X = {}"
  by (simp add: safe_max_def split: if_splits)

lemma safe_max_Some_intro: "x \<in> X \<Longrightarrow> \<exists>y. safe_max X = Some y"
  using safe_max_empty by auto

lemma safe_max_Some_dest_in: "finite X \<Longrightarrow> safe_max X = Some x \<Longrightarrow> x \<in> X"
  using Max_in by (auto simp add: safe_max_def split: if_splits)

lemma safe_max_Some_dest_le: "finite X \<Longrightarrow> safe_max X = Some x \<Longrightarrow> y \<in> X \<Longrightarrow> y \<le> x"
  using Max_ge by (auto simp add: safe_max_def split: if_splits)

fun valid_mmsaux :: "Monitor.window \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> 'a mmsaux \<Rightarrow> 'a Monitor.msaux \<Rightarrow>
  bool" where
  "valid_mmsaux w n L R (nt, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) ys \<longleftrightarrow>
    L \<subseteq> R \<and> maskL = join_mask n L \<and> maskR = join_mask n R \<and>
    (\<forall>(t, X) \<in> set ys. table n R X) \<and>
    table n R (Mapping.keys tuple_in) \<and> table n R (Mapping.keys tuple_since) \<and>
    (\<forall>as \<in> \<Union>(snd ` (set (linearize data_prev))). wf_tuple n R as) \<and>
    nt = current w \<and> I = ivl w \<and>
    ts_tuple_rel (set ys) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since tas} \<and>
    sorted (map fst (linearize data_prev)) \<and>
    (\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt \<and> nt - t < left I) \<and>
    sorted (map fst (linearize data_in)) \<and>
    (\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt \<and> nt - t \<ge> left I) \<and>
    (\<forall>as. Mapping.lookup tuple_in as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since tas \<and> as = snd tas})) \<and>
    (\<forall>as \<in> Mapping.keys tuple_since. case Mapping.lookup tuple_since as of Some t \<Rightarrow> t \<le> nt)"

lemma Mapping_lookup_filter_keys: "k \<in> Mapping.keys (Mapping.filter f m) \<Longrightarrow>
  Mapping.lookup (Mapping.filter f m) k = Mapping.lookup m k"
  by (metis default_def insert_subset keys_default keys_filter lookup_default lookup_default_filter)

lemma Mapping_filter_keys: "(\<forall>k \<in> Mapping.keys m. P (Mapping.lookup m k)) \<Longrightarrow>
  (\<forall>k \<in> Mapping.keys (Mapping.filter f m). P (Mapping.lookup (Mapping.filter f m) k))"
  using Mapping_lookup_filter_keys Mapping.keys_filter by fastforce

lemma Mapping_filter_keys_le: "(\<And>x. P x \<Longrightarrow> P' x) \<Longrightarrow>
  (\<forall>k \<in> Mapping.keys m. P (Mapping.lookup m k)) \<Longrightarrow> (\<forall>k \<in> Mapping.keys m. P' (Mapping.lookup m k))"
  by auto

lemma Mapping_keys_dest: "x \<in> Mapping.keys f \<Longrightarrow> \<exists>y. Mapping.lookup f x = Some y"
  by (simp add: domD keys_dom_lookup)

lemma Mapping_keys_intro: "Mapping.lookup f x \<noteq> None \<Longrightarrow> x \<in> Mapping.keys f"
  by (simp add: domIff keys_dom_lookup)

lemma valid_mmsaux_tuple_in_keys: "valid_mmsaux w n L R
  (nt, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) ys \<Longrightarrow>
  Mapping.keys tuple_in = snd ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
  valid_tuple tuple_since tas}"
  by (auto intro!: Mapping_keys_intro safe_max_Some_intro
      dest!: Mapping_keys_dest safe_max_Some_dest_in[OF finite_fst_ts_tuple_rel])+

fun init_mmsaux :: "\<I> \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> 'a mmsaux" where
  "init_mmsaux I n L R = (0, 0, I, join_mask n L, join_mask n R,
  empty_queue, empty_queue, Mapping.empty, Mapping.empty)"

lemma valid_init_mmsaux: "L \<subseteq> R \<Longrightarrow> valid_mmsaux (init_window I) n L R (init_mmsaux I n L R) []"
  by (auto simp add: init_window_def empty_queue_rep ts_tuple_rel_def join_mask_def
      Mapping.lookup_empty safe_max_def table_def)

abbreviation "filter_cond X' ts t' \<equiv> (\<lambda>as _. \<not> (as \<in> X' \<and> Mapping.lookup ts as = Some t'))"

lemma dropWhile_filter:
  "sorted (map fst xs) \<Longrightarrow> \<forall>t \<in> fst ` set xs. t \<le> nt \<Longrightarrow>
  dropWhile (\<lambda>(t, X). enat (nt - t) > c) xs = filter (\<lambda>(t, X). enat (nt - t) \<le> c) xs"
  apply (induction xs)
  using iffD1[OF filter_id_conv[symmetric], symmetric, of _ "\<lambda>(t, X). enat (nt - t) \<le> c"]
  dual_order.trans by auto fastforce

lemma dropWhile_filter':
  fixes nt :: nat
  shows "sorted (map fst xs) \<Longrightarrow> \<forall>t \<in> fst ` set xs. t \<le> nt \<Longrightarrow>
  dropWhile (\<lambda>(t, X). nt - t \<ge> c) xs = filter (\<lambda>(t, X). nt - t < c) xs"
  apply (induction xs)
  using iffD1[OF filter_id_conv[symmetric], symmetric, of _ "\<lambda>(t, X). nt - t < c"]
  dual_order.trans by auto fastforce

lemma takeWhile_filter:
  "sorted (map fst xs) \<Longrightarrow> \<forall>t \<in> fst ` set xs. t \<le> nt \<Longrightarrow>
  takeWhile (\<lambda>(t, X). enat (nt - t) > c) xs = filter (\<lambda>(t, X). enat (nt - t) > c) xs"
  apply (induction xs)
  using iffD1[OF filter_empty_conv[symmetric], symmetric, of _ "\<lambda>(t, X). enat (nt - t) > c"]
  less_enat_iff by auto fastforce

lemma takeWhile_filter':
  fixes nt :: nat
  shows "sorted (map fst xs) \<Longrightarrow> \<forall>t \<in> fst ` set xs. t \<le> nt \<Longrightarrow>
  takeWhile (\<lambda>(t, X). nt - t \<ge> c) xs = filter (\<lambda>(t, X). nt - t \<ge> c) xs"
  apply (induction xs)
  using iffD1[OF filter_empty_conv[symmetric], symmetric, of _ "\<lambda>(t, X). nt - t \<ge> c"]
  less_enat_iff by auto fastforce

lemma fold_Mapping_filter_None: "Mapping.lookup ts as = None \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) ts. Mapping.filter
  (filter_cond X ts t) ts) ds ts) as = None"
  by (induction ds arbitrary: ts) (auto simp add: Mapping.lookup_filter)

lemma Mapping_lookup_filter_Some_P: "Mapping.lookup (Mapping.filter P m) k = Some v \<Longrightarrow> P k v"
  by (auto simp add: Mapping.lookup_filter split: option.splits if_splits)

lemma Mapping_lookup_filter_None: "(\<And>v. \<not>P k v) \<Longrightarrow>
  Mapping.lookup (Mapping.filter P m) k = None"
  by (auto simp add: Mapping.lookup_filter split: option.splits)

lemma Mapping_lookup_filter_Some: "(\<And>v. P k v) \<Longrightarrow>
  Mapping.lookup (Mapping.filter P m) k = Mapping.lookup m k"
  by (auto simp add: Mapping.lookup_filter split: option.splits)

lemma Mapping_lookup_filter_not_None: "Mapping.lookup (Mapping.filter P m) k \<noteq> None \<Longrightarrow>
  Mapping.lookup (Mapping.filter P m) k = Mapping.lookup m k"
  by (auto simp add: Mapping.lookup_filter split: option.splits)

lemma fold_Mapping_filter_Some_None: "Mapping.lookup ts as = Some t \<Longrightarrow>
  as \<in> X \<Longrightarrow> (t, X) \<in> set ds \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) ts. Mapping.filter (filter_cond X ts t) ts) ds ts) as = None"
proof (induction ds arbitrary: ts)
  case (Cons a ds)
  show ?case
  proof (cases a)
    case (Pair t' X')
    with Cons show ?thesis
      using fold_Mapping_filter_None[of "Mapping.filter (filter_cond X' ts t') ts" as ds]
        Mapping_lookup_filter_not_None[of "filter_cond X' ts t'" ts as]
        fold_Mapping_filter_None[OF Mapping_lookup_filter_None, of _ as ds ts]
      by (cases "Mapping.lookup (Mapping.filter (filter_cond X' ts t') ts) as = None") auto
  qed
qed simp

lemma fold_Mapping_filter_Some_Some: "Mapping.lookup ts as = Some t \<Longrightarrow>
  (\<And>X. (t, X) \<in> set ds \<Longrightarrow> as \<notin> X) \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) ts. Mapping.filter (filter_cond X ts t) ts) ds ts) as = Some t"
proof (induction ds arbitrary: ts)
  case (Cons a ds)
  then show ?case
  proof (cases a)
    case (Pair t' X')
    with Cons show ?thesis
      using Mapping_lookup_filter_Some[of "filter_cond X' ts t'" as ts] by auto
  qed
qed simp

fun filter_mmsaux :: "ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "filter_mmsaux nt (t, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (let data_prev' = dropWhile_queue (\<lambda>(t, X). enat (nt - t) > right I) data_prev;
    (data_in, discard) = takedropWhile_queue (\<lambda>(t, X). enat (nt - t) > right I) data_in;
    tuple_in = fold (\<lambda>(t, X) tuple_in. Mapping.filter
      (filter_cond X tuple_in t) tuple_in) discard tuple_in in
    (t, gc, I, maskL, maskR, data_prev', data_in, tuple_in, tuple_since))"

lemma valid_filter_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux w n L R
    (ot, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and nt_mono: "nt \<ge> current w"
  and new_window: "w' = w\<lparr>earliest := if nt \<ge> right (ivl w)
    then the_enat (nt - right (ivl w)) else earliest w\<rparr>"
  shows "valid_mmsaux w' n L R (filter_mmsaux nt
    (ot, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))
    (filter (\<lambda>(t, rel). enat (nt - t) \<le> right (ivl w)) auxlist)"
proof -
  define data_in' where "data_in' \<equiv>
    fst (takedropWhile_queue (\<lambda>(t, X). enat (nt - t) > right I) data_in)"
  define data_prev' where "data_prev' \<equiv>
    dropWhile_queue (\<lambda>(t, X). enat (nt - t) > right I) data_prev"
  define discard where "discard \<equiv>
    snd (takedropWhile_queue (\<lambda>(t, X). enat (nt - t) > right I) data_in)"
  define tuple_in' where "tuple_in' \<equiv> fold (\<lambda>(t, X) tuple_in. Mapping.filter
    (\<lambda>as _. \<not>(as \<in> X \<and> Mapping.lookup tuple_in as = Some t)) tuple_in) discard tuple_in"
  have tuple_in_Some_None: "\<And>as t X. Mapping.lookup tuple_in as = Some t \<Longrightarrow>
    as \<in> X \<Longrightarrow> (t, X) \<in> set discard \<Longrightarrow> Mapping.lookup tuple_in' as = None"
    using fold_Mapping_filter_Some_None unfolding tuple_in'_def by fastforce
  have tuple_in_Some_Some: "\<And>as t. Mapping.lookup tuple_in as = Some t \<Longrightarrow>
    (\<And>X. (t, X) \<in> set discard \<Longrightarrow> as \<notin> X) \<Longrightarrow> Mapping.lookup tuple_in' as = Some t"
    using fold_Mapping_filter_Some_Some unfolding tuple_in'_def by fastforce
  have tuple_in_None_None: "\<And>as. Mapping.lookup tuple_in as = None \<Longrightarrow>
    Mapping.lookup tuple_in' as = None"
    using fold_Mapping_filter_None unfolding tuple_in'_def by fastforce
  have tuple_in'_keys: "\<And>as. as \<in> Mapping.keys tuple_in' \<Longrightarrow> as \<in> Mapping.keys tuple_in"
    using tuple_in_Some_None tuple_in_Some_Some tuple_in_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping_keys_dest)
  have F1: "sorted (map fst (linearize data_in))" "\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt"
    using valid_before nt_mono by auto
  have F2: "sorted (map fst (linearize data_prev))" "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt"
    using valid_before nt_mono by auto
  have lin_data_in': "linearize data_in' =
    filter (\<lambda>(t, X). enat (nt - t) \<le> right I) (linearize data_in)"
    unfolding data_in'_def[unfolded takedropWhile_queue_fst] dropWhile_queue_rep
      dropWhile_filter[OF F1] ..
  then have set_lin_data_in': "set (linearize data_in') \<subseteq> set (linearize data_in)"
    by auto
  have "sorted (map fst (linearize data_in))"
    using valid_before by auto
  then have sorted_lin_data_in': "sorted (map fst (linearize data_in'))"
    unfolding lin_data_in' using sorted_filter by auto
  have discard_alt: "discard = filter (\<lambda>(t, X). enat (nt - t) > right I) (linearize data_in)"
    unfolding discard_def[unfolded takedropWhile_queue_snd] takeWhile_filter[OF F1] ..
  have lin_data_prev': "linearize data_prev' =
    filter (\<lambda>(t, X). enat (nt - t) \<le> right I) (linearize data_prev)"
    unfolding data_prev'_def[unfolded takedropWhile_queue_fst] dropWhile_queue_rep
      dropWhile_filter[OF F2] ..
  have "sorted (map fst (linearize data_prev))"
    using valid_before by auto
  then have sorted_lin_data_prev': "sorted (map fst (linearize data_prev'))"
    unfolding lin_data_prev' using sorted_filter by auto
  have lookup_tuple_in': "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in')). valid_tuple tuple_since tas \<and> as = snd tas})"
  proof -
    fix as
    show "Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in')). valid_tuple tuple_since tas \<and> as = snd tas})"
    proof (cases "Mapping.lookup tuple_in as")
      case None
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas} = {}"
        using valid_before by (auto dest!: safe_max_empty_dest)
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas} = {}"
        using ts_tuple_rel_mono[OF set_lin_data_in'] by auto
      then show ?thesis
        unfolding tuple_in_None_None[OF None] using iffD2[OF safe_max_empty, symmetric] by blast
    next
      case (Some t)
      show ?thesis
      proof (cases "\<exists>X. (t, X) \<in> set discard \<and> as \<in> X")
        case True
        then obtain X where X_def: "(t, X) \<in> set discard" "as \<in> X"
          by auto
        have "enat (nt - t) > right I"
          using X_def(1) unfolding discard_alt by simp
        moreover have "\<And>t'. (t', as) \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
          valid_tuple tuple_since (t', as) \<Longrightarrow> t' \<le> t"
          using valid_before Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff)
        ultimately have "{tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since tas \<and> as = snd tas} = {}"
          unfolding lin_data_in' using ts_tuple_rel_set_filter
          by (auto simp add: ts_tuple_rel_def)
             (meson diff_le_mono2 enat_ord_simps(2) leD le_less_trans)
        then show ?thesis
          unfolding tuple_in_Some_None[OF Some X_def(2,1)]
          using iffD2[OF safe_max_empty, symmetric] by blast
      next
        case False
        then have lookup_Some: "Mapping.lookup tuple_in' as = Some t"
          using tuple_in_Some_Some[OF Some] by auto
        have t_as: "(t, as) \<in> ts_tuple_rel (set (linearize data_in))"
          "valid_tuple tuple_since (t, as)"
          using valid_before Some by (auto dest: safe_max_Some_dest_in[OF finite_fst_ts_tuple_rel])
        then obtain X where X_def: "as \<in> X" "(t, X) \<in> set (linearize data_in)"
          by (auto simp add: ts_tuple_rel_def)
        have "(t, X) \<in> set (linearize data_in')"
          using X_def False unfolding discard_alt lin_data_in' by auto
        then have t_in_fst: "t \<in> fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since tas \<and> as = snd tas}"
          using t_as(2) X_def(1) by (auto simp add: ts_tuple_rel_def image_iff)
        have "\<And>t'. (t', as) \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
          valid_tuple tuple_since (t', as) \<Longrightarrow> t' \<le> t"
          using valid_before Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff)
        then have "Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since tas \<and> as = snd tas}) = t"
          using Max_eqI[OF finite_fst_ts_tuple_rel, OF _ t_in_fst]
            ts_tuple_rel_mono[OF set_lin_data_in'] by fastforce
        then show ?thesis
          unfolding lookup_Some using t_in_fst by (auto simp add: safe_max_def)
      qed
    qed
  qed
  have table_in: "table n R (Mapping.keys tuple_in')"
    using tuple_in'_keys valid_before by (auto simp add: table_def)
  have "ts_tuple_rel (set auxlist) =
    {as \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since as}"
    using valid_before by auto
  then have "ts_tuple_rel (set (filter (\<lambda>(t, rel). enat (nt - t) \<le> right I) auxlist)) =
    {as \<in> ts_tuple_rel (set (linearize data_prev') \<union> set (linearize data_in')).
    valid_tuple tuple_since as}"
    unfolding lin_data_prev' lin_data_in' ts_tuple_rel_Un ts_tuple_rel_filter by auto
  then show ?thesis
    using data_prev'_def data_in'_def tuple_in'_def discard_def valid_before nt_mono new_window
      sorted_lin_data_prev' sorted_lin_data_in' lin_data_prev' lin_data_in' lookup_tuple_in'
      table_in
    by (auto simp only: valid_mmsaux.simps filter_mmsaux.simps Let_def split: prod.splits) auto
      (* takes long *)
qed

lemma valid_filter_mmsaux: "valid_mmsaux w n L R aux auxlist \<Longrightarrow> nt \<ge> current w \<Longrightarrow>
  w' = w\<lparr>earliest := if nt \<ge> right (ivl w) then the_enat (nt - right (ivl w)) else earliest w\<rparr> \<Longrightarrow>
  valid_mmsaux w' n L R (filter_mmsaux nt aux)
  (filter (\<lambda>(t, rel). enat (nt - t) \<le> right (ivl w)) auxlist)"
  using valid_filter_mmsaux_unfolded by (cases aux) fast

fun join_mmsaux :: "bool \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "join_mmsaux pos X (t, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (if maskL = maskR then
      (let tuple_in = Mapping.filter (join_filter_cond pos X) tuple_in;
      tuple_since = Mapping.filter (join_filter_cond pos X) tuple_since in
      (t, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))
    else if (\<forall>i \<in> set maskL. \<not>i) then
      (let nones = replicate (length maskL) None;
      take_all = (pos \<longleftrightarrow> nones \<in> X);
      tuple_in = (if take_all then tuple_in else Mapping.empty);
      tuple_since = (if take_all then tuple_since else Mapping.empty) in
      (t, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))
    else
      (let tuple_in = Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_in;
      tuple_since = Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_since in
      (t, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)))"

fun join_mmsaux_abs :: "bool \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "join_mmsaux_abs pos X (t, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (let tuple_in = Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_in;
    tuple_since = Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_since in
    (t, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))"

lemma Mapping_filter_cong:
  assumes cong: "(\<And>k v. k \<in> Mapping.keys m \<Longrightarrow> f k v = f' k v)"
  shows "Mapping.filter f m = Mapping.filter f' m"
proof -
  have "\<And>k. Mapping.lookup (Mapping.filter f m) k = Mapping.lookup (Mapping.filter f' m) k"
    using cong
    by (fastforce simp add: Mapping.lookup_filter intro: Mapping_keys_intro split: option.splits)
  then show ?thesis
    by (simp add: mapping_eqI)
qed

lemma join_mmsaux_abs_eq:
  assumes valid_before: "valid_mmsaux w n L R
    (nt, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and table_left: "table n L X"
  shows "join_mmsaux pos X (nt, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    join_mmsaux_abs pos X (nt, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)"
proof (cases "maskL = maskR")
  case True
  have keys_wf_in: "\<And>as. as \<in> Mapping.keys tuple_in \<Longrightarrow> wf_tuple n L as"
    using wf_tuple_change_base valid_before True by (fastforce simp add: table_def)
  have cong_in: "\<And>as n. as \<in> Mapping.keys tuple_in \<Longrightarrow>
    proj_tuple_in_join pos maskL as X \<longleftrightarrow> join_cond pos X as"
    using proj_tuple_in_join_mask_idle[OF keys_wf_in] valid_before
    by (auto simp only: valid_mmsaux.simps)
  have keys_wf_since: "\<And>as. as \<in> Mapping.keys tuple_since \<Longrightarrow> wf_tuple n L as"
    using wf_tuple_change_base valid_before True by (fastforce simp add: table_def)
  have cong_since: "\<And>as n. as \<in> Mapping.keys tuple_since \<Longrightarrow>
    proj_tuple_in_join pos maskL as X \<longleftrightarrow> join_cond pos X as"
    using proj_tuple_in_join_mask_idle[OF keys_wf_since] valid_before
    by (auto simp only: valid_mmsaux.simps)
  show ?thesis
    using True Mapping_filter_cong[OF cong_in, of tuple_in "\<lambda>k _. k"]
      Mapping_filter_cong[OF cong_since, of tuple_since "\<lambda>k _. k"]
    by auto
next
  case False
  then show ?thesis
  proof (cases "\<forall>i \<in> set maskL. \<not>i")
    case True
    have length_maskL: "length maskL = n"
      using valid_before by (auto simp add: join_mask_def)
    have proj_rep: "\<And>as. wf_tuple n R as \<Longrightarrow> proj_tuple maskL as = replicate (length maskL) None"
      using True proj_tuple_replicate by (force simp add: length_maskL wf_tuple_def)
    have keys_wf_in: "\<And>as. as \<in> Mapping.keys tuple_in \<Longrightarrow> wf_tuple n R as"
      using valid_before by (auto simp add: table_def)
    have keys_wf_since: "\<And>as. as \<in> Mapping.keys tuple_since \<Longrightarrow> wf_tuple n R as"
      using valid_before by (auto simp add: table_def)
    have "\<And>as. Mapping.lookup (Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X)
      tuple_in) as = Mapping.lookup (if (pos \<longleftrightarrow> replicate (length maskL) None \<in> X)
      then tuple_in else Mapping.empty) as"
      using proj_rep[OF keys_wf_in]
      by (auto simp add: Mapping.lookup_filter Mapping.lookup_empty proj_tuple_in_join_def
          Mapping_keys_intro split: option.splits)
    moreover have "\<And>as. Mapping.lookup (Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X)
      tuple_since) as = Mapping.lookup (if (pos \<longleftrightarrow> replicate (length maskL) None \<in> X)
      then tuple_since else Mapping.empty) as"
      using proj_rep[OF keys_wf_since]
      by (auto simp add: Mapping.lookup_filter Mapping.lookup_empty proj_tuple_in_join_def
          Mapping_keys_intro split: option.splits)
    ultimately show ?thesis
      using False True by (auto simp add: mapping_eqI Let_def)
  qed auto
qed

lemma valid_join_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux w n L R
    (nt, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and table_left: "table n L X"
  shows "valid_mmsaux w n L R
    (join_mmsaux pos X (nt, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))
    (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist)"
proof -
  define tuple_in' where "tuple_in' \<equiv>
    Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_in"
  define tuple_since' where "tuple_since' \<equiv>
    Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_since"
  have tuple_in_None_None: "\<And>as. Mapping.lookup tuple_in as = None \<Longrightarrow>
    Mapping.lookup tuple_in' as = None"
    unfolding tuple_in'_def using Mapping_lookup_filter_not_None by fastforce
  have tuple_in'_keys: "\<And>as. as \<in> Mapping.keys tuple_in' \<Longrightarrow> as \<in> Mapping.keys tuple_in"
    using tuple_in_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping_keys_dest)
  have tuple_since_None_None: "\<And>as. Mapping.lookup tuple_since as = None \<Longrightarrow>
    Mapping.lookup tuple_since' as = None"
    unfolding tuple_since'_def using Mapping_lookup_filter_not_None by fastforce
  have tuple_since'_keys: "\<And>as. as \<in> Mapping.keys tuple_since' \<Longrightarrow> as \<in> Mapping.keys tuple_since"
    using tuple_since_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping_keys_dest)
  have ts_tuple_rel': "ts_tuple_rel (set (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist)) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since' tas}"
  proof (rule set_eqI, rule iffI)
    fix tas
    assume assm: "tas \<in> ts_tuple_rel (set (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist))"
    then obtain t as Z where tas_def: "tas = (t, as)" "as \<in> join Z pos X" "(t, Z) \<in> set auxlist"
      "(t, join Z pos X) \<in> set (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist)"
      by (fastforce simp add: ts_tuple_rel_def)
    from tas_def(3) have table_Z: "table n R Z"
      using valid_before by auto
    have proj: "as \<in> Z" "proj_tuple_in_join pos maskL as X"
      using tas_def(2) join_sub[OF _ table_left table_Z] valid_before by auto
    then have "(t, as) \<in> ts_tuple_rel (set (auxlist))"
      using tas_def(3) by (auto simp add: ts_tuple_rel_def)
    then have tas_in: "(t, as) \<in> ts_tuple_rel
      (set (linearize data_prev) \<union> set (linearize data_in))" "valid_tuple tuple_since (t, as)"
      using valid_before by auto
    then obtain t' where t'_def: "Mapping.lookup tuple_since as = Some t'" "t \<ge> t'"
      by (auto simp add: valid_tuple_def split: option.splits)
    then have valid_tuple_since': "valid_tuple tuple_since' (t, as)"
      using proj(2)
      by (auto simp add: tuple_since'_def Mapping_lookup_filter_Some valid_tuple_def)
    show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
      valid_tuple tuple_since' tas}"
      using tas_in valid_tuple_since' unfolding tas_def(1)[symmetric] by auto
  next
    fix tas
    assume assm: "tas \<in> {tas \<in> ts_tuple_rel
      (set (linearize data_prev) \<union> set (linearize data_in)). valid_tuple tuple_since' tas}"
    then obtain t as where tas_def: "tas = (t, as)" "valid_tuple tuple_since' (t, as)"
      by (auto simp add: ts_tuple_rel_def)
    from tas_def(2) have "valid_tuple tuple_since (t, as)"
      unfolding tuple_since'_def using Mapping_lookup_filter_not_None
      by (force simp add: valid_tuple_def split: option.splits)
    then have "(t, as) \<in> ts_tuple_rel (set auxlist)"
      using valid_before assm tas_def(1) by auto
    then obtain Z where Z_def: "as \<in> Z" "(t, Z) \<in> set auxlist"
      by (auto simp add: ts_tuple_rel_def)
    then have table_Z: "table n R Z"
      using valid_before by auto
    from tas_def(2) have "proj_tuple_in_join pos maskL as X"
      unfolding tuple_since'_def using Mapping_lookup_filter_Some_P
      by (fastforce simp add: valid_tuple_def split: option.splits)
    then have as_in_join: "as \<in> join Z pos X"
      using join_sub[OF _ table_left table_Z] Z_def(1) valid_before by auto
    then show "tas \<in> ts_tuple_rel (set (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist))"
      using Z_def unfolding tas_def(1) by (auto simp add: ts_tuple_rel_def)
  qed
  have lookup_tuple_in': "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since' tas \<and> as = snd tas})"
  proof -
    fix as
    show "Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since' tas \<and> as = snd tas})"
    proof (cases "Mapping.lookup tuple_in as")
      case None
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas} = {}"
        using valid_before by (auto dest!: safe_max_empty_dest)
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since' tas \<and> as = snd tas} = {}"
        using Mapping_lookup_filter_not_None
        by (fastforce simp add: valid_tuple_def tuple_since'_def split: option.splits)
      then show ?thesis
        unfolding tuple_in_None_None[OF None] using iffD2[OF safe_max_empty, symmetric] by blast
    next
      case (Some t)
      show ?thesis
      proof (cases "proj_tuple_in_join pos maskL as X")
        case True
        then have lookup_tuple_in': "Mapping.lookup tuple_in' as = Some t"
          using Some unfolding tuple_in'_def by (simp add: Mapping_lookup_filter_Some)
        have "(t, as) \<in> ts_tuple_rel (set (linearize data_in))" "valid_tuple tuple_since (t, as)"
          using valid_before Some by (auto dest: safe_max_Some_dest_in[OF finite_fst_ts_tuple_rel])
        then have t_in_fst: "t \<in> fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
          valid_tuple tuple_since' tas \<and> as = snd tas}"
          using True by (auto simp add: image_iff valid_tuple_def tuple_since'_def
            Mapping_lookup_filter_Some split: option.splits)
        have "\<And>t'. valid_tuple tuple_since' (t', as) \<Longrightarrow> valid_tuple tuple_since (t', as)"
          using Mapping_lookup_filter_not_None
          by (fastforce simp add: valid_tuple_def tuple_since'_def split: option.splits)
        then have "\<And>t'. (t', as) \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
          valid_tuple tuple_since' (t', as) \<Longrightarrow> t' \<le> t"
          using valid_before Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff)
        then have "Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
          valid_tuple tuple_since' tas \<and> as = snd tas}) = t"
          using Max_eqI[OF finite_fst_ts_tuple_rel[of "linearize data_in"],
            OF _ t_in_fst] by fastforce
        then show ?thesis
          unfolding lookup_tuple_in' using t_in_fst by (auto simp add: safe_max_def)
      next
        case False
        then have lookup_tuple': "Mapping.lookup tuple_in' as = None"
          "Mapping.lookup tuple_since' as = None"
          unfolding tuple_in'_def tuple_since'_def
          by (auto simp add: Mapping_lookup_filter_None)
        then have "\<And>tas. \<not>(valid_tuple tuple_since' tas \<and> as = snd tas)"
          by (auto simp add: valid_tuple_def split: option.splits)
        then show ?thesis
          unfolding lookup_tuple' by (auto simp add: safe_max_def)
      qed
    qed
  qed
  have table_join': "\<And>t ys. (t, ys) \<in> set auxlist \<Longrightarrow> table n R (join ys pos X)"
  proof -
    fix t ys
    assume "(t, ys) \<in> set auxlist"
    then have table_ys: "table n R ys"
      using valid_before by auto
    show "table n R (join ys pos X)"
      using join_table[OF table_ys table_left, of pos R] valid_before by auto
  qed
  have table_in': "table n R (Mapping.keys tuple_in')"
    using tuple_in'_keys valid_before by (auto simp add: table_def)
  have table_since': "table n R (Mapping.keys tuple_since')"
    using tuple_since'_keys valid_before by (auto simp add: table_def)
  show ?thesis
    unfolding join_mmsaux_abs_eq[OF valid_before table_left]
    using valid_before ts_tuple_rel' lookup_tuple_in' tuple_in'_def tuple_since'_def table_join'
      Mapping_filter_keys[of tuple_since "\<lambda>as. case as of Some t \<Rightarrow> t \<le> nt"]
      table_in' table_since' by auto
qed

lemma valid_join_mmsaux: "valid_mmsaux w n L R aux auxlist \<Longrightarrow> table n L X \<Longrightarrow>
  valid_mmsaux w n L R (join_mmsaux pos X aux) (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist)"
  using valid_join_mmsaux_unfolded by (cases aux) fast

setup_lifting type_definition_mapping

lift_definition upd_set :: "('a, 'b) mapping \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>m f X a. if a \<in> X then Some (f a) else m a" .

lemma Mapping_lookup_upd_set: "Mapping.lookup (upd_set m f X) a =
  (if a \<in> X then Some (f a) else Mapping.lookup m a)"
  by (simp add: Mapping.lookup.rep_eq upd_set.rep_eq)

lemma Mapping_upd_set_keys: "Mapping.keys (upd_set m f X) = Mapping.keys m \<union> X"
  by (auto simp add: Mapping_lookup_upd_set dest!: Mapping_keys_dest intro: Mapping_keys_intro)

lemma fold_append_queue_rep: "linearize (fold (\<lambda>x q. append_queue x q) xs q) = linearize q @ xs"
  by (induction xs arbitrary: q) (auto simp add: append_queue_rep)

lemma Max_Un_absorb:
  assumes "finite X" "X \<noteq> {}" "finite Y" "(\<And>x y. y \<in> Y \<Longrightarrow> x \<in> X \<Longrightarrow> y \<le> x)"
  shows "Max (X \<union> Y) = Max X"
proof -
  have Max_X_in_X: "Max X \<in> X"
    using Max_in[OF assms(1,2)] .
  have Max_X_in_XY: "Max X \<in> X \<union> Y"
    using Max_in[OF assms(1,2)] by auto
  have fin: "finite (X \<union> Y)"
    using assms(1,3) by auto
  have Y_le_Max_X: "\<And>y. y \<in> Y \<Longrightarrow> y \<le> Max X"
    using assms(4)[OF _ Max_X_in_X] .
  have XY_le_Max_X: "\<And>y. y \<in> X \<union> Y \<Longrightarrow> y \<le> Max X"
    using Max_ge[OF assms(1)] Y_le_Max_X by auto
  show ?thesis
    using Max_eqI[OF fin XY_le_Max_X Max_X_in_XY] by auto
qed

lemma Mapping_lookup_fold_upd_set_idle: "{(t, X) \<in> set xs. as \<in> Z X t} = {} \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z X t)) xs m) as = Mapping.lookup m as"
  apply (induction xs arbitrary: m)
  by auto (metis (no_types, lifting) Mapping_lookup_upd_set)

lemma Mapping_lookup_fold_upd_set_max: "{(t, X) \<in> set xs. as \<in> Z X t} \<noteq> {} \<Longrightarrow>
  sorted (map fst xs) \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z X t)) xs m) as =
  Some (Max (fst ` {(t, X) \<in> set xs. as \<in> Z X t}))"
proof (induction xs arbitrary: m)
  case (Cons x xs)
  obtain t X where tX_def: "x = (t, X)"
    by (cases x) auto
  have set_fst_eq: "(fst ` {(t, X). (t, X) \<in> set (x # xs) \<and> as \<in> Z X t}) =
    ((fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t}) \<union>
    (if as \<in> Z X t then {t} else {}))"
    using image_iff by (fastforce simp add: tX_def split: if_splits)
  show ?case
  proof (cases "{(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t} \<noteq> {}")
    case True
    have "{(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t} \<subseteq> set xs"
      by auto
    then have fin: "finite (fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t})"
      by (simp add: finite_subset)
    have "Max (insert t (fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t})) =
      Max (fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t})"
      using Max_Un_absorb[OF fin, of "{t}"] True Cons(3) tX_def by auto
    then show ?thesis
      using Cons True unfolding set_fst_eq by auto
  next
    case False
    then have empty: "{(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t} = {}"
      by auto
    then have "as \<in> Z X t"
      using Cons(2) set_fst_eq by fastforce
    then show ?thesis
      using Mapping_lookup_fold_upd_set_idle[OF empty] unfolding set_fst_eq empty
      by (auto simp add: Mapping_lookup_upd_set tX_def)
  qed
qed simp

fun add_new_ts_mmsaux :: "ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_ts_mmsaux nt (t, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (let (data_prev, move) = takedropWhile_queue (\<lambda>(t, X). nt - t \<ge> left I) data_prev;
    data_in = fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in) move data_in;
    tuple_in = fold (\<lambda>(t, X) tuple_in. upd_set tuple_in (\<lambda>_. t)
      {as \<in> X. valid_tuple tuple_since (t, as)}) move tuple_in in
    (nt, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))"

lemma Mapping_keys_fold_upd_set: "k \<in> Mapping.keys (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z t X))
  xs m) \<Longrightarrow> k \<in> Mapping.keys m \<or> (\<exists>(t, X) \<in> set xs. k \<in> Z t X)"
  by (induction xs arbitrary: m) (fastforce simp add: Mapping_upd_set_keys)+

lemma valid_add_new_ts_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux w n L R
    (ot, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and nt_mono: "nt \<ge> current w"
  and new_window: "w' = w\<lparr>latest := if nt \<ge> left (ivl w)
    then nt - left (ivl w) else latest w, current := nt\<rparr>"
  shows "valid_mmsaux w' n L R (add_new_ts_mmsaux nt
    (ot, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)) auxlist"
proof -
  define data_prev' where "data_prev' \<equiv> dropWhile_queue (\<lambda>(t, X). nt - t \<ge> left I) data_prev"
  define move where "move \<equiv> takeWhile (\<lambda>(t, X). nt - t \<ge> left I) (linearize data_prev)"
  define data_in' where "data_in' \<equiv> fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in)
    move data_in"
  define tuple_in' where "tuple_in' \<equiv> fold (\<lambda>(t, X) tuple_in. upd_set tuple_in (\<lambda>_. t)
      {as \<in> X. valid_tuple tuple_since (t, as)}) move tuple_in"
  have tuple_in'_keys: "\<And>as. as \<in> Mapping.keys tuple_in' \<Longrightarrow> as \<in> Mapping.keys tuple_in \<or>
    (\<exists>(t, X)\<in>set move. as \<in> {as \<in> X. valid_tuple tuple_since (t, as)})"
    using Mapping_keys_fold_upd_set[of _ "\<lambda>t X. {as \<in> X. valid_tuple tuple_since (t, as)}"]
    by (auto simp add: tuple_in'_def)
  have F1: "sorted (map fst (linearize data_in))" "\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt"
    "\<forall>t \<in> fst ` set (linearize data_in). t \<le> ot \<and> ot - t \<ge> left I"
    using valid_before nt_mono by auto
  have F2: "sorted (map fst (linearize data_prev))" "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt"
    "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> ot \<and> ot - t < left I"
    using valid_before nt_mono by auto
  have lin_data_prev': "linearize data_prev' =
    filter (\<lambda>(t, X). nt - t < left I) (linearize data_prev)"
    unfolding data_prev'_def dropWhile_queue_rep dropWhile_filter'[OF F2(1,2)] ..
  have move_filter: "move = filter (\<lambda>(t, X). nt - t \<ge> left I) (linearize data_prev)"
    unfolding move_def takeWhile_filter'[OF F2(1,2)] ..
  then have sorted_move: "sorted (map fst move)"
    using sorted_filter F2 by auto
  have "\<forall>t\<in>fst ` set move. t \<le> ot \<and> ot - t < left I"
    using move_filter F2(3) set_filter by auto
  then have fst_set_before: "\<forall>t\<in>fst ` set (linearize data_in). \<forall>t'\<in>fst ` set move. t \<le> t'"
    using F1(3) by fastforce
  then have fst_ts_tuple_rel_before: "\<forall>t\<in>fst ` ts_tuple_rel (set (linearize data_in)).
    \<forall>t'\<in>fst ` ts_tuple_rel (set move). t \<le> t'"
    by (fastforce simp add: ts_tuple_rel_def)
  have sorted_lin_data_prev': "sorted (map fst (linearize data_prev'))"
    unfolding lin_data_prev' using sorted_filter F2 by auto
  have lin_data_in': "linearize data_in' = linearize data_in @ move"
    unfolding data_in'_def using fold_append_queue_rep by fastforce
  have sorted_lin_data_in': "sorted (map fst (linearize data_in'))"
    unfolding lin_data_in' using F1(1) sorted_move fst_set_before by (simp add: sorted_append)
  have set_lin_prev'_in': "set (linearize data_prev') \<union> set (linearize data_in') =
    set (linearize data_prev) \<union> set (linearize data_in)"
    using lin_data_prev' lin_data_in' move_filter by auto
  have ts_tuple_rel': "ts_tuple_rel (set auxlist) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev') \<union> set (linearize data_in')).
    valid_tuple tuple_since tas}"
    unfolding set_lin_prev'_in' using valid_before by auto
  have lookup': "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in')).
    valid_tuple tuple_since tas \<and> as = snd tas})"
  proof -
    fix as
    show "Mapping.lookup tuple_in' as = safe_max (fst `
      {tas \<in> ts_tuple_rel (set (linearize data_in')).
      valid_tuple tuple_since tas \<and> as = snd tas})"
    proof (cases "{(t, X) \<in> set move. as \<in> X \<and> valid_tuple tuple_since (t, as)} = {}")
      case True
      have move_absorb: "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas} =
        {tas \<in> ts_tuple_rel (set (linearize data_in @ move)).
        valid_tuple tuple_since tas \<and> as = snd tas}"
        using True by (auto simp add: ts_tuple_rel_def)
      have "Mapping.lookup tuple_in as =
        safe_max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas})"
        using valid_before by auto
      then have "Mapping.lookup tuple_in as =
        safe_max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas})"
        unfolding lin_data_in' move_absorb .
      then show ?thesis
        using Mapping_lookup_fold_upd_set_idle[of "move" as
          "\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)}"] True
        unfolding tuple_in'_def by auto
    next
      case False
      have split: "fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas} =
        fst ` {tas \<in> ts_tuple_rel (set move). valid_tuple tuple_since tas \<and> as = snd tas} \<union>
        fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas}"
        unfolding lin_data_in' set_append ts_tuple_rel_Un by auto
      have max_eq: "Max (fst ` {tas \<in> ts_tuple_rel (set move).
        valid_tuple tuple_since tas \<and> as = snd tas}) =
        Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas})"
        unfolding split
        apply (rule Max_Un_absorb[OF finite_fst_ts_tuple_rel _ finite_fst_ts_tuple_rel, symmetric])
        using False fst_ts_tuple_rel_before by (fastforce simp add: ts_tuple_rel_def)+
      have "fst ` {(t, X). (t, X) \<in> set move \<and> as \<in> {as \<in> X. valid_tuple tuple_since (t, as)}} =
        fst ` {tas \<in> ts_tuple_rel (set move). valid_tuple tuple_since tas \<and> as = snd tas}"
        by (auto simp add: ts_tuple_rel_def image_iff)
      then have "Mapping.lookup tuple_in' as = Some (Max (fst ` {tas \<in> ts_tuple_rel (set move).
        valid_tuple tuple_since tas \<and> as = snd tas}))"
        using Mapping_lookup_fold_upd_set_max[of "move" as
          "\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)}", OF _ sorted_move] False
        unfolding tuple_in'_def by (auto simp add: ts_tuple_rel_def)
      then show ?thesis
        unfolding max_eq using False
        by (auto simp add: safe_max_def lin_data_in' ts_tuple_rel_def)
    qed
  qed
  have table_in': "table n R (Mapping.keys tuple_in')"
  proof -
    {
      fix as
      assume assm: "as \<in> Mapping.keys tuple_in'"
      have "wf_tuple n R as"
        using tuple_in'_keys[OF assm]
      proof (rule disjE)
        assume "as \<in> Mapping.keys tuple_in"
        then show "wf_tuple n R as"
          using valid_before by (auto simp add: table_def)
      next
        assume "\<exists>(t, X)\<in>set move. as \<in> {as \<in> X. valid_tuple tuple_since (t, as)}"
        then obtain t X where tX_def: "(t, X) \<in> set move" "as \<in> X"
          by auto
        then have "as \<in> \<Union>(snd ` set (linearize data_prev))"
          unfolding move_def using set_takeWhileD by force
        then show "wf_tuple n R as"
          using valid_before by auto
      qed
    }
    then show ?thesis
      by (auto simp add: table_def)
  qed
  have data_prev'_move: "(data_prev', move) =
    takedropWhile_queue (\<lambda>(t, X). nt - t \<ge> left I) data_prev"
    using takedropWhile_queue_fst takedropWhile_queue_snd data_prev'_def move_def
    by (metis surjective_pairing)
  moreover have "valid_mmsaux w' n L R (nt, gc, I, maskL, maskR, data_prev', data_in',
    tuple_in', tuple_since) auxlist"
    using lin_data_prev' sorted_lin_data_prev' lin_data_in' move_filter sorted_lin_data_in'
      nt_mono valid_before ts_tuple_rel' lookup' new_window table_in'
    by (auto simp only: valid_mmsaux.simps split: option.splits) auto
      (* takes long *)
  ultimately show ?thesis
    by (auto simp only: add_new_ts_mmsaux.simps Let_def data_in'_def tuple_in'_def
        split: prod.splits)
qed

lemma valid_add_new_ts_mmsaux: "valid_mmsaux w n L R aux auxlist \<Longrightarrow> nt \<ge> current w \<Longrightarrow>
  w' = w\<lparr>latest := if nt \<ge> left (ivl w) then nt - left (ivl w) else latest w, current := nt\<rparr> \<Longrightarrow>
  valid_mmsaux w' n L R (add_new_ts_mmsaux nt aux) auxlist"
  using valid_add_new_ts_mmsaux_unfolded by (cases aux) fast

fun add_new_table_mmsaux :: "'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_table_mmsaux X (t, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (let tuple_since = upd_set tuple_since (\<lambda>_. t) (X - Mapping.keys tuple_since) in
    (if 0 \<ge> left I then (t, gc, I, maskL, maskR, data_prev, append_queue (t, X) data_in,
      upd_set tuple_in (\<lambda>_. t) X, tuple_since)
    else (t, gc, I, maskL, maskR, append_queue (t, X) data_prev, data_in, tuple_in, tuple_since)))"

lemma valid_add_new_table_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux w n L R
    (nt, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and table_X: "table n R X"
  shows "valid_mmsaux w n L R (add_new_table_mmsaux X
    (nt, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))
    (case auxlist of
      [] => [(nt, X)]
    | ((t, y) # ts) \<Rightarrow> if t = nt then (t, y \<union> X) # ts else (nt, X) # auxlist)"
proof -
  define tuple_in' where "tuple_in' \<equiv> upd_set tuple_in (\<lambda>_. nt) X"
  define tuple_since' where "tuple_since' \<equiv> upd_set tuple_since (\<lambda>_. nt)
    (X - Mapping.keys tuple_since)"
  define data_prev' where "data_prev' \<equiv> append_queue (nt, X) data_prev"
  define data_in' where "data_in' \<equiv> append_queue (nt, X) data_in"
  define auxlist' where "auxlist' \<equiv> (case auxlist of
    [] => [(nt, X)]
    | ((t, y) # ts) \<Rightarrow> if t = nt then (t, y \<union> X) # ts else (nt, X) # auxlist)"
  have table_in': "table n R (Mapping.keys tuple_in')"
    using table_X valid_before by (auto simp add: table_def tuple_in'_def Mapping_upd_set_keys)
  have table_since': "table n R (Mapping.keys tuple_since')"
    using table_X valid_before by (auto simp add: table_def tuple_since'_def Mapping_upd_set_keys)
  have tuple_since'_keys: "Mapping.keys tuple_since \<subseteq> Mapping.keys tuple_since'"
    using Mapping_upd_set_keys by (fastforce simp add: tuple_since'_def)
  have lin_data_prev': "linearize data_prev' = linearize data_prev @ [(nt, X)]"
    unfolding data_prev'_def append_queue_rep ..
  have wf_data_prev': "\<And>as. as \<in> \<Union>(snd ` (set (linearize data_prev'))) \<Longrightarrow> wf_tuple n R as"
    unfolding lin_data_prev' using table_X valid_before by (auto simp add: table_def)
  have lin_data_in': "linearize data_in' = linearize data_in @ [(nt, X)]"
    unfolding data_in'_def append_queue_rep ..
  have table_auxlist': "\<forall>(t, X) \<in> set auxlist'. table n R X"
    using table_X table_Un valid_before
    by (auto simp add: auxlist'_def split: list.splits if_splits)
  have lookup_tuple_since': "\<forall>as \<in> Mapping.keys tuple_since'.
    case Mapping.lookup tuple_since' as of Some t \<Rightarrow> t \<le> nt"
    unfolding tuple_since'_def using valid_before Mapping_lookup_upd_set[of tuple_since]
    by (auto dest: Mapping_keys_dest intro!: Mapping_keys_intro split: if_splits option.splits)
  have ts_tuple_rel_auxlist': "ts_tuple_rel (set auxlist') =
    ts_tuple_rel (set auxlist) \<union> ts_tuple_rel {(nt, X)}"
    unfolding auxlist'_def
    using ts_tuple_rel_ext ts_tuple_rel_ext' ts_tuple_rel_ext_Cons ts_tuple_rel_ext_Cons'
    apply (auto simp only: split: list.splits if_splits)
         apply (auto simp add: ts_tuple_rel_def)[5]
    by fastforce
  have valid_tuple_nt_X: "\<And>tas. tas \<in> ts_tuple_rel {(nt, X)} \<Longrightarrow> valid_tuple tuple_since' tas"
    using valid_before by (auto simp add: ts_tuple_rel_def valid_tuple_def tuple_since'_def
        Mapping_lookup_upd_set dest: Mapping_keys_dest split: option.splits)
  have valid_tuple_mono: "\<And>tas. valid_tuple tuple_since tas \<Longrightarrow> valid_tuple tuple_since' tas"
    by (auto simp add: valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
        intro: Mapping_keys_intro split: option.splits)
  have ts_tuple_rel_auxlist': "ts_tuple_rel (set auxlist') =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in) \<union> {(nt, X)}).
    valid_tuple tuple_since' tas}"
  proof (rule set_eqI, rule iffI)
    fix tas
    assume assm: "tas \<in> ts_tuple_rel (set auxlist')"
    show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
      set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
      using assm[unfolded ts_tuple_rel_auxlist' ts_tuple_rel_Un]
    proof (rule UnE)
      assume assm: "tas \<in> ts_tuple_rel (set auxlist)"
      then have "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in)). valid_tuple tuple_since tas}"
        using valid_before by auto
      then show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
        using assm by (auto simp only: ts_tuple_rel_Un intro: valid_tuple_mono)
    next
      assume assm: "tas \<in> ts_tuple_rel {(nt, X)}"
      show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
        using assm valid_before by (auto simp add: ts_tuple_rel_Un tuple_since'_def
            valid_tuple_def Mapping_lookup_upd_set ts_tuple_rel_def dest: Mapping_keys_dest
            split: option.splits if_splits)
    qed
  next
    fix tas
    assume assm: "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
      set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
    then have "tas \<in> (ts_tuple_rel (set (linearize data_prev) \<union>
      set (linearize data_in)) - ts_tuple_rel {(nt, X)}) \<union> ts_tuple_rel {(nt, X)}"
      by (auto simp only: ts_tuple_rel_Un)
    then show "tas \<in> ts_tuple_rel (set auxlist')"
    proof (rule UnE)
      assume assm': "tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in)) - ts_tuple_rel {(nt, X)}"
      then have tas_in: "tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in))"
        by (auto simp only: ts_tuple_rel_def)
      obtain t as where tas_def: "tas = (t, as)"
        by (cases tas) auto
      have "t \<in> fst ` (set (linearize data_prev) \<union> set (linearize data_in))"
        using assm' unfolding tas_def by (force simp add: ts_tuple_rel_def)
      then have t_le_nt: "t \<le> nt"
        using valid_before by auto
      have valid_tas: "valid_tuple tuple_since' tas"
        using assm by auto
      have "valid_tuple tuple_since tas"
      proof (cases "as \<in> Mapping.keys tuple_since")
        case True
        then show ?thesis
          using valid_tas tas_def by (auto simp add: valid_tuple_def tuple_since'_def
              Mapping_lookup_upd_set split: option.splits if_splits)
      next
        case False
        then have "t = nt" "as \<in> X"
          using valid_tas t_le_nt unfolding tas_def
          by (auto simp add: valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
              intro: Mapping_keys_intro split: option.splits if_splits)
        then have "False"
          using assm' unfolding tas_def ts_tuple_rel_def by (auto simp only: ts_tuple_rel_def)
        then show ?thesis
          by simp
      qed
      then show "tas \<in> ts_tuple_rel (set auxlist')"
        using tas_in valid_before by (auto simp add: ts_tuple_rel_auxlist')
    qed (auto simp only: ts_tuple_rel_auxlist')
  qed
  show ?thesis
  proof (cases "0 \<ge> left I")
    case True
    then have add_def: "add_new_table_mmsaux X (nt, gc, I, maskL, maskR, data_prev, data_in,
      tuple_in, tuple_since) = (nt, gc, I, maskL, maskR, data_prev, data_in',
      tuple_in', tuple_since')"
      using data_in'_def tuple_in'_def tuple_since'_def by auto
    have left_I: "left I = 0"
      using True by auto
    have "\<forall>t \<in> fst ` set (linearize data_in'). t \<le> nt \<and> nt - t \<ge> left I"
      using valid_before True by (auto simp add: lin_data_in')
    moreover have "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
      {tas \<in> ts_tuple_rel (set (linearize data_in')).
      valid_tuple tuple_since' tas \<and> as = snd tas})"
    proof -
      fix as
      show "Mapping.lookup tuple_in' as = safe_max (fst `
        {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since' tas \<and> as = snd tas})"
      proof (cases "as \<in> X")
        case True
        have "valid_tuple tuple_since' (nt, as)"
          using True valid_before by (auto simp add: valid_tuple_def tuple_since'_def
              Mapping_lookup_upd_set dest: Mapping_keys_dest split: option.splits)
        moreover have "(nt, as) \<in> ts_tuple_rel (insert (nt, X) (set (linearize data_in)))"
          using True by (auto simp add: ts_tuple_rel_def)
        ultimately have nt_in: "nt \<in> fst ` {tas \<in> ts_tuple_rel (insert (nt, X)
          (set (linearize data_in))). valid_tuple tuple_since' tas \<and> as = snd tas}"
        proof -
          assume a1: "valid_tuple tuple_since' (nt, as)"
          assume "(nt, as) \<in> ts_tuple_rel (insert (nt, X) (set (linearize data_in)))"
          then have "\<exists>p. nt = fst p \<and> p \<in> ts_tuple_rel (insert (nt, X)
            (set (linearize data_in))) \<and> valid_tuple tuple_since' p \<and> as = snd p"
            using a1 by simp
          then show "nt \<in> fst ` {p \<in> ts_tuple_rel (insert (nt, X) (set (linearize data_in))).
            valid_tuple tuple_since' p \<and> as = snd p}"
            by blast
        qed
        moreover have "\<And>t. t \<in> fst ` {tas \<in> ts_tuple_rel (insert (nt, X)
          (set (linearize data_in))). valid_tuple tuple_since' tas \<and> as = snd tas} \<Longrightarrow> t \<le> nt"
          using valid_before by (auto split: option.splits)
            (metis (no_types, lifting) eq_imp_le fst_conv insertE ts_tuple_rel_dest)
        ultimately have "Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)
          \<union> set [(nt, X)]). valid_tuple tuple_since' tas \<and> as = snd tas}) = nt"
          using Max_eqI[OF finite_fst_ts_tuple_rel[of "linearize data_in'"],
              unfolded lin_data_in' set_append] by auto
        then show ?thesis
          using nt_in True
          by (auto simp add: tuple_in'_def Mapping_lookup_upd_set safe_max_def lin_data_in')
      next
        case False
        have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
          valid_tuple tuple_since tas \<and> as = snd tas} =
          {tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since' tas \<and> as = snd tas}"
          using False by (fastforce simp add: lin_data_in' ts_tuple_rel_def valid_tuple_def
              tuple_since'_def Mapping_lookup_upd_set intro: Mapping_keys_intro
              split: option.splits if_splits)
        then show ?thesis
          using valid_before False by (auto simp add: tuple_in'_def Mapping_lookup_upd_set)
      qed
    qed
    ultimately show ?thesis
      using assms table_auxlist' sorted_append[of "map fst (linearize data_in)"]
        lookup_tuple_since' ts_tuple_rel_auxlist' table_in' table_since'
      unfolding add_def auxlist'_def[symmetric]
      by (auto simp only: valid_mmsaux.simps lin_data_in') auto
  next
    case False
    then have add_def: "add_new_table_mmsaux X (nt, gc, I, maskL, maskR, data_prev, data_in,
      tuple_in, tuple_since) = (nt, gc, I, maskL, maskR, data_prev', data_in,
      tuple_in, tuple_since')"
      using data_prev'_def tuple_since'_def by auto
    have left_I: "left I > 0"
      using False by auto
    have "\<forall>t \<in> fst ` set (linearize data_prev'). t \<le> nt \<and> nt - t < left I"
      using valid_before False by (auto simp add: lin_data_prev')
    moreover have "\<And>as. {tas \<in> ts_tuple_rel (set (linearize data_in)).
      valid_tuple tuple_since tas \<and> as = snd tas} =
      {tas \<in> ts_tuple_rel (set (linearize data_in)).
      valid_tuple tuple_since' tas \<and> as = snd tas}"
    proof (rule set_eqI, rule iffI)
      fix as tas
      assume assm: "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since' tas \<and> as = snd tas}"
      then obtain t Z where Z_def: "tas = (t, as)" "as \<in> Z" "(t, Z) \<in> set (linearize data_in)"
        "valid_tuple tuple_since' (t, as)"
        by (auto simp add: ts_tuple_rel_def)
      show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas}"
      using assm
      proof (cases "as \<in> Mapping.keys tuple_since")
        case False
        then have "t \<ge> nt"
          using Z_def(4) by (auto simp add: valid_tuple_def tuple_since'_def
              Mapping_lookup_upd_set intro: Mapping_keys_intro split: option.splits if_splits)
        then show ?thesis
          using Z_def(3) valid_before left_I by auto
      qed (auto simp add: valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
           dest: Mapping_keys_dest split: option.splits)
    qed (auto simp add: Mapping_lookup_upd_set valid_tuple_def tuple_since'_def
         intro: Mapping_keys_intro split: option.splits)
    ultimately show ?thesis
      using assms table_auxlist' sorted_append[of "map fst (linearize data_prev)"]
        False lookup_tuple_since' ts_tuple_rel_auxlist' table_in' table_since' wf_data_prev'
        valid_before
      unfolding add_def auxlist'_def[symmetric]
      by (auto simp only: valid_mmsaux.simps lin_data_prev') fastforce+
        (* takes long *)
  qed
qed

lemma valid_add_new_table_mmsaux:
  assumes valid_before: "valid_mmsaux w n L R aux auxlist"
  and table_X: "table n R X"
  and time: "time_mmsaux aux = nt"
  shows "valid_mmsaux w n L R (add_new_table_mmsaux X aux)
    (case auxlist of
      [] => [(nt, X)]
    | ((t, y) # ts) \<Rightarrow> if t = nt then (t, y \<union> X) # ts else (nt, X) # auxlist)"
proof -
  obtain gc I maskL maskR data_prev data_in tuple_in tuple_since where aux_def:
    "aux = (nt, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)"
    using time by (cases aux) auto
  show ?thesis
    using valid_add_new_table_mmsaux_unfolded[OF valid_before[unfolded aux_def] table_X]
    unfolding aux_def .
qed

fun gc_mmsaux :: "'a mmsaux \<Rightarrow> 'a mmsaux" where
  "gc_mmsaux (nt, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (let all_tuples = \<Union>(snd ` (set (linearize data_prev) \<union> set (linearize data_in)));
    tuple_since' = Mapping.filter (\<lambda>as _. as \<in> all_tuples) tuple_since in
    (nt, nt, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since'))"

lemma valid_gc_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux w n L R (nt, gc, I, maskL, maskR, data_prev, data_in,
    tuple_in, tuple_since) ys"
  shows "valid_mmsaux w n L R (gc_mmsaux (nt, gc, I, maskL, maskR, data_prev, data_in,
    tuple_in, tuple_since)) ys"
proof -
  define all_tuples where "all_tuples \<equiv> \<Union>(snd ` (set (linearize data_prev) \<union>
    set (linearize data_in)))"
  define tuple_since' where "tuple_since' \<equiv> Mapping.filter (\<lambda>as _. as \<in> all_tuples) tuple_since"
  have tuple_since_None_None: "\<And>as. Mapping.lookup tuple_since as = None \<Longrightarrow>
    Mapping.lookup tuple_since' as = None"
    unfolding tuple_since'_def using Mapping_lookup_filter_not_None by fastforce
  have tuple_since'_keys: "\<And>as. as \<in> Mapping.keys tuple_since' \<Longrightarrow> as \<in> Mapping.keys tuple_since"
    using tuple_since_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping_keys_dest)
  then have table_since': "table n R (Mapping.keys tuple_since')"
    using valid_before by (auto simp add: table_def)
  have data_cong: "\<And>tas. tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
    set (linearize data_in)) \<Longrightarrow> valid_tuple tuple_since' tas = valid_tuple tuple_since tas"
  proof -
    fix tas
    assume assm: "tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
    set (linearize data_in))"
    define t where "t \<equiv> fst tas"
    define as where "as \<equiv> snd tas"
    have "as \<in> all_tuples"
      using assm by (force simp add: as_def all_tuples_def ts_tuple_rel_def)
    then have "Mapping.lookup tuple_since' as = Mapping.lookup tuple_since as"
      by (auto simp add: tuple_since'_def Mapping.lookup_filter split: option.splits)
    then show "valid_tuple tuple_since' tas = valid_tuple tuple_since tas"
      by (auto simp add: valid_tuple_def as_def split: option.splits) metis
  qed
  then have data_in_cong: "\<And>tas. tas \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
    valid_tuple tuple_since' tas = valid_tuple tuple_since tas"
    by (auto simp add: ts_tuple_rel_Un)
  have "ts_tuple_rel (set ys) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since' tas}"
    using data_cong valid_before by auto
  moreover have "(\<forall>as. Mapping.lookup tuple_in as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since' tas \<and> as = snd tas}))"
    using valid_before by auto (meson data_in_cong)
  moreover have "(\<forall>as \<in> Mapping.keys tuple_since'. case Mapping.lookup tuple_since' as of
    Some t \<Rightarrow> t \<le> nt)"
    using Mapping.keys_filter valid_before
    by (auto simp add: tuple_since'_def Mapping.lookup_filter split: option.splits
        intro!: Mapping_keys_intro dest: Mapping_keys_dest)
  ultimately show ?thesis
    using all_tuples_def tuple_since'_def valid_before table_since' by auto
qed

lemma valid_gc_mmsaux: "valid_mmsaux w n L R aux ys \<Longrightarrow> valid_mmsaux w n L R (gc_mmsaux aux) ys"
  using valid_gc_mmsaux_unfolded by (cases aux) fast

fun add_new_mmsaux :: "nat \<times> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_mmsaux (nt, X) (t, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (if enat (nt - gc) > right I then
      add_new_table_mmsaux X (add_new_ts_mmsaux nt (gc_mmsaux (t, gc, I, maskL, maskR,
      data_prev, data_in, tuple_in, tuple_since)))
    else
      add_new_table_mmsaux X (add_new_ts_mmsaux nt (t, gc, I, maskL, maskR, data_prev, data_in,
      tuple_in, tuple_since)))"

lemma valid_add_new_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux w n L R
    (t, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and nt_mono: "nt \<ge> current w"
  and new_window: "w' = w\<lparr>latest := if nt \<ge> left (ivl w) then nt - left (ivl w)
    else latest w, current := nt\<rparr>"
  and table_X: "table n R X"
  shows "valid_mmsaux w' n L R (add_new_mmsaux (nt, X)
    (t, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))
    (case auxlist of
      [] => [(nt, X)]
    | ((t, y) # ts) \<Rightarrow> if t = nt then (t, y \<union> X) # ts else (nt, X) # auxlist)"
  using valid_add_new_table_mmsaux[OF valid_add_new_ts_mmsaux[OF valid_before nt_mono new_window]
    table_X]
    valid_add_new_table_mmsaux[OF valid_add_new_ts_mmsaux[OF valid_gc_mmsaux nt_mono new_window,
    OF valid_before] table_X]
  by (auto simp only: valid_mmsaux.simps time_mmsaux.simps add_new_mmsaux.simps
      add_new_ts_mmsaux.simps gc_mmsaux.simps Let_def split: if_splits prod.splits)

lemma valid_add_new_mmsaux: "valid_mmsaux w n L R aux auxlist \<Longrightarrow> nt \<ge> current w \<Longrightarrow>
  table n R X \<Longrightarrow> w' = w\<lparr>latest := if nt \<ge> left (ivl w) then nt - left (ivl w)
  else latest w, current := nt\<rparr> \<Longrightarrow> valid_mmsaux w' n L R (add_new_mmsaux (nt, X) aux)
  (case auxlist of
    [] => [(nt, X)]
  | ((t, y) # ts) \<Rightarrow> if t = nt then (t, y \<union> X) # ts else (nt, X) # auxlist)"
  using valid_add_new_mmsaux_unfolded by (cases aux) fast

lemma foldr_ts_tuple_rel:
  "as \<in> foldr (\<union>) (concat (map (\<lambda>(t, rel). if P t then [rel] else []) auxlist)) {} \<longleftrightarrow>
  (\<exists>t. (t, as) \<in> ts_tuple_rel (set auxlist) \<and> P t)"
proof (rule iffI)
  assume assm: "as \<in> foldr (\<union>) (concat (map (\<lambda>(t, rel). if P t then [rel] else []) auxlist)) {}"
  then obtain t X where tX_def: "P t" "as \<in> X" "(t, X) \<in> set auxlist"
    by (auto elim!: in_foldr_UnE)
  then show "\<exists>t. (t, as) \<in> ts_tuple_rel (set auxlist) \<and> P t"
    by (auto simp add: ts_tuple_rel_def)
next
  assume assm: "\<exists>t. (t, as) \<in> ts_tuple_rel (set auxlist) \<and> P t"
  then obtain t X where tX_def: "P t" "as \<in> X" "(t, X) \<in> set auxlist"
    by (auto simp add: ts_tuple_rel_def)
  show "as \<in> foldr (\<union>) (concat (map (\<lambda>(t, rel). if P t then [rel] else []) auxlist)) {}"
    using in_foldr_UnI[OF tX_def(2)] tX_def assm by (induction auxlist) force+
qed

lemma image_snd: "(a, b) \<in> X \<Longrightarrow> b \<in> snd ` X"
  by force

fun result_mmsaux :: "'a mmsaux \<Rightarrow> 'a table" where
  "result_mmsaux (nt, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
  Mapping.keys tuple_in"

lemma valid_result_mmsaux_unfolded:
  assumes "valid_mmsaux w n L R
    (t, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  shows "result_mmsaux (t, gc, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
  foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, left (ivl w) \<le> current w - t] {}"
  using valid_mmsaux_tuple_in_keys[OF assms] assms
  apply (auto simp add: image_Un ts_tuple_rel_Un foldr_ts_tuple_rel image_snd)
   apply (fastforce intro!: ts_tuple_rel_intro dest!: ts_tuple_rel_dest)+
  done

lemma valid_result_mmsaux: "valid_mmsaux w n L R aux auxlist \<Longrightarrow>
  result_mmsaux aux = foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, left (ivl w) \<le> current w - t] {}"
  using valid_result_mmsaux_unfolded by (cases aux) fast

end