theory SWA
  imports Main
begin

instantiation option :: (semigroup_add) semigroup_add begin

fun plus_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "plus_option None _ = None"
| "plus_option _ None = None"
| "plus_option (Some a) (Some b) = Some (a + b)"

instance proof
  fix a b c :: "'a option"
  show "a + b + c = a + (b + c)"
    by (induct a b rule: plus_option.induct; cases c)
      (auto simp: algebra_simps)
qed

end

lemma (in semigroup_add) fold_add_add: "fold (+) xs (x + y) = fold (+) xs x + y"
  by (induct xs arbitrary: x) (auto simp: add_assoc[symmetric])

context begin

qualified datatype 'a tree =
  Leaf
| Node (l: nat) (r: nat) (val: "'a option") (lchild: "'a tree") (rchild: "'a tree")
where
  "l Leaf = 0"
| "r Leaf = 0"
| "val Leaf = None"
| "lchild Leaf = Leaf"
| "rchild Leaf = Leaf"

lemma neq_Leaf_if_l_gt0: "0 < l t \<Longrightarrow> t \<noteq> Leaf"
  by auto

primrec discharge :: "'a tree \<Rightarrow> 'a tree" where
  "discharge Leaf = Leaf"
| "discharge (Node i j _ t u) = Node i j None t u"

lemma map_tree_eq_Leaf_iff: "map_tree f t = Leaf \<longleftrightarrow> t = Leaf"
  by (cases t)
    (auto split: option.splits)

lemma l_map_tree_eq_l[simp]: "l (map_tree f t) = l t"
  by (cases t)
    (auto split: option.splits)

lemma r_map_tree_eq_r[simp]: "r (map_tree f t) = r t"
  by (cases t)
    (auto split: option.splits)

lemma val_map_tree_neq_None: "val t \<noteq> None \<Longrightarrow> val (map_tree f t) \<noteq> None"
  by (cases t) auto

fun update_rightmost :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "update_rightmost _ Leaf = Leaf"
| "update_rightmost f (Node i j a t u) = Node i j (map_option f a) t (update_rightmost f u)"

lemma update_rightmost_eq_Leaf_iff: "update_rightmost f t = Leaf \<longleftrightarrow> t = Leaf"
  by (cases t)
    (auto split: option.splits)

lemma l_update_rightmost_eq_l[simp]: "l (update_rightmost f t) = l t"
  by (cases t)
    (auto split: option.splits)

lemma r_update_rightmost_eq_r[simp]: "r (update_rightmost f t) = r t"
  by (cases t)
    (auto split: option.splits)

lemma val_update_rightmost_neq_None: "val t \<noteq> None \<Longrightarrow> val (update_rightmost f t) \<noteq> None"
  by (cases t) auto

fun combine :: "'a :: semigroup_add SWA.tree \<Rightarrow> 'a SWA.tree \<Rightarrow> 'a SWA.tree" where
  "combine t Leaf = t"
| "combine Leaf t = t"
| "combine t u = Node (l t) (r u) (val t + val u) (discharge t) u"

lemma combine_non_Leaves: "\<lbrakk>t \<noteq> Leaf; u \<noteq> Leaf\<rbrakk> \<Longrightarrow> combine t u = Node (SWA.l t) (SWA.r u) (val t + val u) (discharge t) u"
proof -
  assume assms: "t \<noteq> Leaf" "u \<noteq> Leaf"
  from assms have "combine t u = Node (l (Node (l t) (r t) (val t) (lchild t) (rchild t))) (r (Node (l u) (r u) (val u) (lchild u) (rchild u))) (val (Node (l t) (r t) (val t) (lchild t) (rchild t)) + val (Node (l u) (r u) (val u) (lchild u) (rchild u))) (discharge (Node (l t) (r t) (val t) (lchild t) (rchild t))) (Node (l u) (r u) (val u) (lchild u) (rchild u))"
    by (metis (no_types) combine.simps(3) tree.exhaust_sel)
  with assms show ?thesis
    by simp
qed

lemma r_combine_non_Leaves: "\<lbrakk>t \<noteq> Leaf; u \<noteq> Leaf\<rbrakk> \<Longrightarrow> r (combine t u) = r u"
  by (simp add: combine_non_Leaves)

type_synonym window = "nat \<times> nat"

definition window :: "'a list \<Rightarrow> window \<Rightarrow> bool" where
  "window as = (\<lambda>(l, r). 0 < l \<and> l \<le> r \<and> r \<le> length as)"

definition windows :: "'a list \<Rightarrow> window list \<Rightarrow> bool" where
  "windows as ws = ((\<forall>w \<in> set ws. window as w) \<and>
    sorted (map fst ws) \<and> sorted (map snd ws))"

function reusables :: "'a tree \<Rightarrow> window \<Rightarrow> 'a tree list" where
  "reusables t w = (if fst w > r t then [] else if fst w = l t then [t]
     else let v = lchild t; u = rchild t in if fst w \<ge> l u then
       reusables u w else u # reusables v w)"
  by auto
termination
  by (relation "measure (\<lambda>p. size (fst p))")
    (auto simp: lchild_def rchild_def split: tree.splits)

declare reusables.simps[simp del]

lemma reusables_Leaf[simp]: "0 < fst w \<Longrightarrow> reusables Leaf w = []"
  by (simp add: reusables.simps)

primrec well_shaped :: "'a tree \<Rightarrow> bool" where
  "well_shaped Leaf = True"
| "well_shaped (Node i j _ t u) = (i \<le> j \<and> (i = j \<longrightarrow> t = Leaf \<and> u = Leaf) \<and>
    (i < j \<longrightarrow> t \<noteq> Leaf \<and> u \<noteq> Leaf \<and> well_shaped t \<and> well_shaped u \<and>
      i = l t \<and> j = r u \<and> Suc (r t) = l u))"

lemma l_lchild_eq_l_if_well_shaped[simp]:
  "well_shaped t \<Longrightarrow> l t < r t \<Longrightarrow> l (lchild t) = l t"
  by (induct t) auto

lemma r_rchild_eq_r_if_well_shaped[simp]:
  "well_shaped t \<Longrightarrow> l t < r t \<Longrightarrow> r (rchild t) = r t"
  by (induct t) auto

lemma r_lchild_eq_l_rchild_if_well_shaped:
  "well_shaped t \<Longrightarrow> l t < r t \<Longrightarrow> r (lchild t) = l (rchild t) - 1"
  by (induct t) auto

lemma well_shaped_lchild[simp]: "well_shaped t \<Longrightarrow> well_shaped (lchild t)"
  by (induct t) auto

lemma well_shaped_rchild[simp]: "well_shaped t \<Longrightarrow> well_shaped (rchild t)"
  by (induct t) auto

lemma well_shaped_map_tree: "well_shaped t \<Longrightarrow> well_shaped (map_tree f t)"
  by (induction t)
    (auto simp: map_tree_eq_Leaf_iff split: option.split)

lemma well_shaped_update_rightmost: "well_shaped t \<Longrightarrow> well_shaped (update_rightmost f t)"
  by (induction t)
    (auto simp: update_rightmost_eq_Leaf_iff split: option.split)

definition adjacent where
  "adjacent w ts = (Leaf \<notin> set ts \<and>
     list_all2 (\<lambda>t u. l t = Suc (r u)) (butlast ts) (tl ts) \<and>
     (ts = [] \<or> (l (last ts) = fst w \<and> r (hd ts) = snd w)))"

lemma adjacent_Nil[simp]: "adjacent w []"
  unfolding adjacent_def by simp

lemma adjacent_Cons: "adjacent w (t # ts) =
  (t \<noteq> Leaf \<and> r t = snd w \<and> (case ts of [] \<Rightarrow> l t = fst w
     | u # us \<Rightarrow> adjacent (fst w, r u) ts \<and> l t = Suc (r u)))"
  unfolding adjacent_def by (auto split: list.splits)

lemma adjacent_ConsI: "\<lbrakk>t \<noteq> Leaf; r t = snd w;
  (case ts of [] \<Rightarrow> l t = fst w
     | u # us \<Rightarrow> adjacent (fst w, r u) ts \<and> l t = Suc (r u))\<rbrakk> \<Longrightarrow>
adjacent w (t # ts)"
  by (simp add: adjacent_Cons)

lemma adjacent_singleton: "t \<noteq> Leaf \<Longrightarrow> adjacent (l t, r t) [t]"
  unfolding adjacent_def by simp

lemma append_Cons_eq_append_append: "xs @ y # ys = xs @ [y] @ ys"
  by simp

lemma list_all2_append_singletonI: "\<lbrakk>list_all2 P xs ys; P x y\<rbrakk> \<Longrightarrow> list_all2 P (xs @ [x]) (ys @ [y])"
  by (simp add: list_all2_appendI)

lemma list_all2_Cons_append_singletonI: "\<lbrakk>xs \<noteq> []; list_all2 P (x # butlast xs) ys; P (last xs) y\<rbrakk> \<Longrightarrow> list_all2 P (x # xs) (ys @ [y])"
  using list_all2_append_singletonI by fastforce

lemma adjacent_appendI: "\<lbrakk>0 < fst w; fst w \<le> snd w;
  (case us of [] \<Rightarrow> adjacent w ts
    | u # us' \<Rightarrow> adjacent (Suc (r u), snd w) ts \<and> adjacent (fst w, (case ts of [] \<Rightarrow> snd w | ts \<Rightarrow> r u)) (u # us'))\<rbrakk> \<Longrightarrow>
  adjacent w (ts @ us)"
  unfolding adjacent_def
  apply (auto simp add: butlast_append intro: list_all2_Cons_append_singletonI split: list.splits if_splits)
  by (subst (2) append_Cons_eq_append_append)
    (auto simp only: append.simps(2)[symmetric] append_assoc[symmetric] intro!: list_all2_appendI list_all2_Cons_append_singletonI)

lemma adjacent_Cons_implies_adjacent: "adjacent (a, b) (t # ts) \<Longrightarrow> adjacent (a, l t - Suc 0) ts"
  by (cases ts)
    (simp_all add: adjacent_def)

context
  fixes as :: "'a :: semigroup_add list"
  and ws :: "window list"
begin

abbreviation atomic where
  "atomic i \<equiv> Node i i (Some (nth as (i - 1))) Leaf Leaf"

abbreviation atomics :: "nat \<Rightarrow> nat \<Rightarrow> 'a tree list" where
  "atomics i j \<equiv> map atomic (rev [i ..< Suc j])"

definition slide :: "'a tree \<Rightarrow> window \<Rightarrow> 'a tree" where
  "slide t w =
    (let
      ts = atomics (max (fst w) (Suc (r t))) (snd w);
      ts' = reusables t w
    in fold combine (ts @ ts') Leaf)"

primrec iterate :: "'a tree \<Rightarrow> window list \<Rightarrow> 'a list" where
  "iterate t [] = []"
| "iterate t (w # xs) = (let t' = slide t w in the (val t') # iterate t' xs)"

definition sliding_window :: "'a list" where
  "sliding_window = iterate Leaf ws"

abbreviation sum where
  "sum i j \<equiv> fold (+) (rev (map (nth as) [i - 1 ..< j - 1])) (nth as (j - 1))"

primrec well_valued0 :: "'a tree \<Rightarrow> bool" where
  "well_valued0 Leaf = True"
| "well_valued0 (Node i j a t u) = (0 < i \<and> j \<le> length as \<and> (a \<noteq> None \<longrightarrow> a = Some (sum i j)) \<and>
    well_valued0 t \<and> well_valued0 u \<and> (u = Leaf \<or> val u \<noteq> None))"

abbreviation well_valued :: "'a tree \<Rightarrow> bool" where
  "well_valued t \<equiv> (well_valued0 t \<and> (t \<noteq> Leaf \<longrightarrow> val t \<noteq> None))"

definition valid :: "'a tree \<Rightarrow> bool" where
  "valid t = (well_shaped t \<and> well_valued t)"

lemma valid_Leaf: "valid Leaf"
  unfolding valid_def by auto

lemma add_sum:
  assumes "i > 0" "j \<ge> i" "k > j"
  shows "sum i j + sum (Suc j) k = sum i k"
proof -
  have *: "[i - 1 ..< k - 1] = [i - 1..< j] @ [j..< k - 1]"
    using assms upt_add_eq_append[of "i - 1" "j - 1" "k - j"]
    by (cases j) (auto simp: upt_conv_Cons)
  then show ?thesis using assms
    by (cases j) (auto simp: fold_add_add)
qed

lemma well_valued0_rchild_if_well_valued0[simp]: "well_valued0 t \<Longrightarrow> well_valued0 (rchild t)"
  by (induct t) auto

lemma well_valued0_lchild_if_well_valued0[simp]: "well_valued0 t \<Longrightarrow> well_valued0 (lchild t)"
  by (induct t) auto

lemma valid_rchild_if_valid: "valid t \<Longrightarrow> valid (rchild t)"
  by (metis tree.exhaust_sel tree.sel(9) valid_def well_shaped_rchild well_valued0.simps(2))

lemma val_eq_Some_sum_if_valid_neq_Leaf: "\<lbrakk>valid t; t \<noteq> Leaf\<rbrakk> \<Longrightarrow> val t = Some (sum (l t) (r t))"
  by (auto simp: valid_def foldr_conv_fold)
    (metis One_nat_def option.distinct(1) option.inject tree.exhaust_sel well_valued0.simps(2))

lemma butlast_rev: "butlast (rev xs) = rev (tl xs)"
  by (induct xs) auto

(* fact (b) part 1 *)
lemma adjacent_atomics: "adjacent (i, j) (atomics i j)"
  unfolding adjacent_def by (auto 0 1 simp: last_map last_rev nth_tl butlast_rev
    map_butlast[symmetric] list_all2_conv_all_nth nth_Cons' rev_nth nth_append)

(* fact (b) part 2 *)
lemma valid_atomics: "\<lbrakk>t \<in> set (atomics i j); 0 < i; j \<le> length as\<rbrakk> \<Longrightarrow> valid t"
  by (auto simp: valid_def)

lemma r_lchild_le_r: "well_shaped t \<Longrightarrow> r (lchild t) \<le> r t"
  apply (induct t)
  apply (auto simp: not_less not_le)
  by (metis Suc_eq_plus1_left order.trans le_add2 tree.exhaust_sel well_shaped.simps(2))

lemma reusables_neq_Nil_if_well_shaped_and_overlapping:
  "\<lbrakk>well_shaped t; l t \<le> fst w; r t \<le> snd w; fst w \<le> r t\<rbrakk> \<Longrightarrow> reusables t w \<noteq> []"
  by (induction t w rule: reusables.induct) (simp add: reusables.simps Let_def)

lemma reusables_lchild_neq_Nil_under_some_conditions:
  "\<lbrakk>well_shaped t; l t \<le> fst w; r t \<le> snd w; fst w \<noteq> l t; r t \<ge> fst w; l (rchild t) > fst w\<rbrakk> \<Longrightarrow>
    reusables (lchild t) w \<noteq> []"
  apply (rule reusables_neq_Nil_if_well_shaped_and_overlapping)
     apply (simp_all add: r_lchild_eq_l_rchild_if_well_shaped r_lchild_le_r)
  using r_lchild_eq_l_rchild_if_well_shaped r_lchild_le_r by fastforce

(* fact (a) part 1 *)
lemma adjacent_reusables: "\<lbrakk>0 < fst w; well_shaped t; l t \<le> fst w; r t \<le> snd w\<rbrakk> \<Longrightarrow>
  adjacent (fst w, r t) (reusables t w)"
proof (induction t w rule: reusables.induct)
  case (1 t w)
  show ?case
  proof (cases "fst w > r t")
    case False
    with 1 show ?thesis
    proof (cases "fst w = l t")
      case False
      then show ?thesis
      proof (cases "fst w \<ge> l (rchild t)")
        case True
        with 1 \<open>fst w \<noteq> l t\<close> show ?thesis by (subst reusables.simps) auto
      next
        case False
        with 1 \<open>fst w \<noteq> l t\<close> \<open>\<not> fst w > r t\<close> obtain x xs where *: "reusables (lchild t) w = x # xs"
          by (cases "reusables (lchild t) w") (auto simp: reusables_lchild_neq_Nil_under_some_conditions)
        with 1(2-6) \<open>fst w \<noteq> l t\<close> \<open>\<not> fst w > r t\<close> \<open>\<not> l (rchild t) \<le> fst w\<close>
        have "adjacent (fst w, r (lchild t)) (x # xs)"
          by (simp add: adjacent_Cons r_lchild_le_r dual_order.trans)
        with 1 \<open>fst w \<noteq> l t\<close> \<open>\<not> fst w > r t\<close> * show ?thesis
          by (subst reusables.simps)
            (auto simp add: Let_def adjacent_Cons r_lchild_eq_l_rchild_if_well_shaped)
      qed
    qed (auto simp: reusables.simps intro!: adjacent_singleton)
  qed (auto simp: reusables.simps)
qed

(* unused *)
lemma well_valued0_reusables: "\<lbrakk>0 < fst w; well_shaped t; well_valued0 t; l t \<le> fst w; r t \<le> snd w\<rbrakk> \<Longrightarrow> \<forall>t' \<in> set (reusables t w). well_valued0 t'"
  apply (induction t w rule: reusables.induct)
  apply (subst reusables.simps)
   apply (auto simp: Let_def)
  using le_trans r_lchild_le_r by blast

lemma valid_rchild_if_well_valued0: "\<lbrakk>well_shaped t; well_valued0 t\<rbrakk> \<Longrightarrow> valid (rchild t)"
  by (metis tree.exhaust_sel tree.sel(9) valid_def well_shaped_rchild well_valued0.simps(2))

lemma valid_reusables_under_some_conditions:
  "\<lbrakk>0 < fst w; well_valued0 t; well_shaped t; l t < fst w; r t \<le> snd w\<rbrakk> \<Longrightarrow>
    \<forall>t' \<in> set (reusables t w). valid t'"
proof (induction t w rule: reusables.induct)
  case (1 t w)
  show ?case
  proof (cases "fst w > r t")
    case False
    with 1 show ?thesis
    proof (cases "fst w = l t")
    next
      case False
      then show ?thesis
      proof (cases "fst w \<ge> l (rchild t)")
        case True
        with 1 \<open>fst w \<noteq> l t\<close> \<open>\<not> fst w > r t\<close> have *: "Ball (set (reusables (rchild t) w)) valid"
          by (metis (no_types, lifting) ball_empty dual_order.strict_trans2 leI le_neq_implies_less list.set(1) r_rchild_eq_r_if_well_shaped reusables.simps set_ConsD valid_rchild_if_well_valued0 well_shaped_rchild well_valued0_rchild_if_well_valued0)
        from 1 \<open>fst w \<noteq> l t\<close> \<open>\<not> fst w > r t\<close> True have "reusables t w = reusables (rchild t) w"
          by (subst reusables.simps)
            simp
        with 1 * show ?thesis
          by simp
      next
        case False
        with 1 \<open>fst w \<noteq> l t\<close> \<open>\<not> fst w > r t\<close> have *: "Ball (set (reusables (lchild t) w)) valid"
          by (metis dual_order.strict_trans2 l_lchild_eq_l_if_well_shaped leI order_trans r_lchild_le_r well_shaped_lchild well_valued0_lchild_if_well_valued0)
        with 1 have valid_rchild: "valid (rchild t)"
          by (simp add: valid_rchild_if_well_valued0)
        with 1 \<open>fst w \<noteq> l t\<close> \<open>\<not> fst w > r t\<close> False have "reusables t w = rchild t # reusables (lchild t) w"
          by (subst reusables.simps) presburger
        with 1 \<open>fst w \<noteq> l t\<close> \<open>\<not> fst w > r t\<close> False * valid_rchild show ?thesis
          by (metis set_ConsD)
      qed
    qed (auto simp: reusables.simps)
  qed (auto simp: reusables.simps)
qed

(* fact (a) part 2 *)
lemma valid_reusables:
  assumes "0 < fst w" "valid t" "l t \<le> fst w" "r t \<le> snd w"
  shows "\<forall>t' \<in> set (reusables t w). valid t'"
proof (cases "l t < fst w")
  case True
  with assms show ?thesis
    using valid_def valid_reusables_under_some_conditions by blast
next
  case False
  with assms show ?thesis
    by (simp add: reusables.simps)
qed

lemma valid_combine_if_valid: "\<lbrakk>l a > 0; valid a; valid z; a \<noteq> Leaf; z \<noteq> Leaf; l z = Suc (r a)\<rbrakk> \<Longrightarrow>
  valid (combine a z)"
  apply (auto simp add: valid_def combine_non_Leaves)
  apply (metis le_trans nat_le_linear not_less_eq_eq tree.collapse well_shaped.simps(2))
  apply (metis not_less_eq_eq tree.exhaust_sel well_shaped.simps(2))
  apply (metis discharge.simps(2) tree.distinct(1) tree.exhaust_sel)
  apply (metis discharge.simps(2) tree.collapse well_shaped.simps(2))
  apply (metis discharge.simps(2) tree.exhaust_sel tree.sel(2))
  apply (metis discharge.simps(2) tree.collapse tree.sel(4))
  apply (metis tree.collapse well_valued0.simps(2))
  subgoal premises prems for va vz
  proof -
    from prems have "l a > 0" by simp
    moreover from prems have "r a \<ge> l a"
      by (metis tree.collapse well_shaped.simps(2))
    moreover have "r z > r a"
      by (metis Suc_le_lessD prems(3) prems(4) prems(6) tree.collapse well_shaped.simps(2))
    ultimately have *: "sum (l a) (r a) + sum (Suc (r a)) (r z) = sum (l a) (r z)"
      by (frule add_sum)
    from prems have "va = sum (l a) (r a)"
      by (metis option.discI option.inject tree.collapse well_valued0.simps(2))
    moreover from prems have "vz = sum (Suc (r a)) (r z)"
      by (metis option.discI option.inject prems(2) prems(3) prems(8) prems(9) tree.collapse well_valued0.simps(2))
    moreover have "fold (+) (rev (map ((!) as) [l a - Suc 0..<r z - Suc 0])) (as ! (r z - Suc 0)) = sum (l a) (r z)"
      by simp
    ultimately show ?thesis
      using * by (auto simp: add_sum)
  qed
  by (metis discharge.simps(2) tree.collapse well_valued0.simps(2))

lemma combine_neq_Leaf_if_both_non_Leaf: "\<lbrakk>a \<noteq> Leaf; z \<noteq> Leaf\<rbrakk> \<Longrightarrow>
  combine a z \<noteq> Leaf"
  by (simp add: combine_non_Leaves)

(* generalized version of fact (c) *)
lemma valid_fold_combine: "\<lbrakk>0 < fst w; ts = h # ts'; \<forall>t \<in> set ts. valid t; adjacent (fst w, l h - 1) ts';
    valid z; z \<noteq> Leaf; l z = (case ts' of [] \<Rightarrow> fst w | t\<^sub>1 # ts'' \<Rightarrow> Suc (r t\<^sub>1)); r z = snd w\<rbrakk> \<Longrightarrow>
      valid (fold combine ts' z) \<and>
      l (fold combine ts' z) = fst w \<and> r (fold combine ts' z) = snd w"
  apply (induction ts' arbitrary: z ts h)
   apply simp
  apply simp
  apply (subgoal_tac "valid a")
  apply (subgoal_tac "adjacent (fst w, l a - Suc 0) ts'")
  apply (subgoal_tac "valid (combine a z)")
  apply (subgoal_tac "combine a z \<noteq> Leaf")
  apply (subgoal_tac "l (combine a z) = (case ts' of [] \<Rightarrow> fst w | t\<^sub>1 # ts'' \<Rightarrow> Suc (r t\<^sub>1))")
  apply (subgoal_tac "r (combine a z) = snd w")
        apply simp_all
      apply (subst r_combine_non_Leaves)
        apply (auto simp add: adjacent_def) []
       apply simp_all
     apply (split list.splits)
  apply (auto simp add: adjacent_def combine_non_Leaves) []
    apply (rule combine_neq_Leaf_if_both_non_Leaf)
     apply (simp add: adjacent_Cons)
    apply assumption
   apply (rule valid_combine_if_valid)
  by (auto simp: adjacent_Cons split: list.splits)

(* fact (c) *)
lemma valid_fold_combine_Leaf:
  assumes "0 < fst w" "ts = h # ts'" "\<forall>t \<in> set ts. valid t" "adjacent w ts"
  shows "valid (fold combine ts Leaf) \<and>
  l (fold combine ts Leaf) = fst w \<and> r (fold combine ts Leaf) = snd w"
proof -
  from assms(2) have "fold combine ts Leaf = fold combine ts' h"
    by simp
  moreover have "valid (fold combine ts' h) \<and>
    l (fold combine ts' h) = fst w \<and> r (fold combine ts' h) = snd w"
  proof (rule valid_fold_combine)
    from assms show "0 < fst w" "ts = h # ts'" "\<forall>t \<in> set ts. valid t" "valid h" "h \<noteq> Leaf" "r h = snd w"
      "l h = (case ts' of [] \<Rightarrow> fst w | t\<^sub>1 # ts'' \<Rightarrow> Suc (r t\<^sub>1))"
      by (simp_all add: adjacent_Cons list.case_eq_if)
    from assms show "adjacent (fst w, l h - 1) ts'"
      by (metis One_nat_def adjacent_Cons_implies_adjacent prod.collapse)
  qed
  ultimately show ?thesis by simp
qed

lemma adjacent_append_atomics_reusables:
  "\<lbrakk>0 < fst w; fst w \<le> snd w; valid t; l t \<le> fst w; r t \<le> snd w\<rbrakk> \<Longrightarrow>
    adjacent w (atomics (max (fst w) (Suc (r t))) (snd w) @ reusables t w)"
  apply (rule adjacent_appendI)
    apply auto
  apply (split list.split)+
  apply safe
  apply (metis (no_types, lifting) adjacent_atomics leI max.absorb1 not_less_eq prod.collapse reusables_neq_Nil_if_well_shaped_and_overlapping valid_def)
     apply simp
  apply (metis (no_types, lifting) Suc_leI Suc_n_not_le_n Zero_not_Suc adjacent_reusables le_neq_implies_less max.bounded_iff order_trans upt_eq_Nil_conv valid_def)
  subgoal
  proof -
    fix x21 :: "'a tree" and x21a :: "'a tree" and x22 :: "'a tree list" and z :: nat and zs :: "nat list" and x22a :: "'a tree list"
    assume a1: "0 < fst w"
    assume a2: "l t \<le> fst w"
    assume a3: "r t \<le> snd w"
    assume a4: "valid t"
    assume a5: "reusables t w = x21 # x22a"
    have f6: "\<forall>p ts. adjacent p ts = ((Leaf::'a tree) \<notin> set ts \<and> list_all2 (\<lambda>t ta. l t = Suc (r ta)) (butlast ts) (tl ts) \<and> (ts = [] \<or> l (last ts) = fst p \<and> r (hd ts) = snd p))"
      using adjacent_def by blast
    then have f7: "Leaf \<notin> set (atomics (max (fst w) (Suc (r t))) (snd w)) \<and> list_all2 (\<lambda>t ta. l t = Suc (r ta)) (butlast (atomics (max (fst w) (Suc (r t))) (snd w))) (tl (atomics (max (fst w) (Suc (r t))) (snd w))) \<and> (atomics (max (fst w) (Suc (r t))) (snd w) = [] \<or> l (last (atomics (max (fst w) (Suc (r t))) (snd w))) = fst (max (fst w) (Suc (r t)), snd w) \<and> r (hd (atomics (max (fst w) (Suc (r t))) (snd w))) = snd (max (fst w) (Suc (r t)), snd w))"
      using adjacent_atomics by presburger
    have "adjacent (fst w, r t) (reusables t w)"
      using a4 a3 a2 a1 by (simp add: adjacent_reusables valid_def)
      then have f8: "r x21 = r t"
        using a5 by (simp add: adjacent_Cons)
      have "max (fst w) (Suc (r t)) = Suc (r t)"
        using a5 by (metis (no_types) Suc_n_not_le_n list.simps(3) max.bounded_iff max_def_raw not_le_imp_less reusables.simps)
      then show "adjacent (Suc (r x21), snd w) (atomics (max (fst w) (Suc (r t))) (snd w))"
        using f8 f7 f6 by presburger
    qed
  by (metis (mono_tags, hide_lams) adjacent_Cons adjacent_reusables snd_conv valid_def)

lemma valid_append_atomics_reusables: "\<lbrakk>0 < fst w; valid t; l t \<le> fst w; r t \<le> snd w; snd w \<le> length as\<rbrakk> \<Longrightarrow>
  \<forall>t \<in> set (atomics (max (fst w) (Suc (r t))) (snd w) @ reusables t w). valid t"
  by (auto simp only: set_append valid_reusables dest: valid_atomics split: if_splits)

lemma append_atomics_reusables_neq_Nil: "\<lbrakk>0 < fst w; fst w \<le> snd w; valid t; l t \<le> fst w; r t \<le> snd w\<rbrakk> \<Longrightarrow>
  atomics (max (fst w) (Suc (r t))) (snd w) @ reusables t w \<noteq> []"
  by (simp add: reusables_neq_Nil_if_well_shaped_and_overlapping valid_def)

(* lemma 1 *)
lemma valid_slide:
  assumes "0 < fst w" "fst w \<le> snd w" "valid t" "l t \<le> fst w" "r t \<le> snd w" "snd w \<le> length as"
  shows "valid (slide t w) \<and> l (slide t w) = fst w \<and> r (slide t w) = snd w"
proof -
  from assms have non_empty: "atomics (max (fst w) (Suc (r t))) (snd w) @ reusables t w \<noteq> []"
    using append_atomics_reusables_neq_Nil by blast
  from assms have adjacent: "adjacent w (atomics (max (fst w) (Suc (r t))) (snd w) @ reusables t w)"
    using adjacent_append_atomics_reusables by blast
  from assms have valid: "\<forall>t \<in> set (atomics (max (fst w) (Suc (r t))) (snd w) @ reusables t w). valid t"
    using valid_append_atomics_reusables by blast
  have *: "slide t w = fold combine (atomics (max (fst w) (Suc (r t))) (snd w) @ reusables t w) Leaf"
    by (simp add: slide_def)
  from assms(1) non_empty adjacent valid show "valid (slide t w) \<and> l (slide t w) = fst w \<and> r (slide t w) = snd w"
    apply (simp only: * neq_Nil_conv)
    using valid_fold_combine_Leaf by blast
qed

lemma iterate_eq_map_sum: "\<lbrakk>valid t; windows as xs; (case xs of [] \<Rightarrow> True | x # xs' \<Rightarrow> l t \<le> fst x \<and> r t \<le> snd x)\<rbrakk> \<Longrightarrow>
  iterate t xs = map (\<lambda>w. sum (fst w) (snd w)) xs"
  by (induction xs arbitrary: t)
    (auto simp: valid_slide windows_def window_def val_eq_Some_sum_if_valid_neq_Leaf neq_Leaf_if_l_gt0 split: list.split)

(* theorem 2: functional correctness *)
lemma correctness: "windows as ws \<Longrightarrow> sliding_window = map (\<lambda>w. sum (fst w) (snd w)) ws"
  by (auto simp only: sliding_window_def intro!: iterate_eq_map_sum)
    (auto simp: valid_def split: list.split)

end

thm correctness

value[code] "sliding_window [2,4,5,2 :: nat] [(1, 3), (1, 4), (2, 4)]"

value[code] "slide [2,4,5,2 :: nat] Leaf (1, 3)"


lemma fold_distr: "(\<forall>x y. f (x + y) = f x + f y) \<Longrightarrow> f (fold (+) list e) = fold (+) (map f list) (f e)"
  by (induction list arbitrary: e) auto

lemma map_rev_map_nth_eq: "\<forall>x \<in> set xs. x < length as \<Longrightarrow> map f (rev (map ((!) as) xs)) = rev (map ((!) (map f as)) xs)"
  by (simp add: rev_map)

lemma f_nth_eq_map_f_nth: "\<lbrakk>as \<noteq> []; length as \<ge> n\<rbrakk> \<Longrightarrow> f (as ! (n - Suc 0)) = map f as ! (n - Suc 0)"
  by (cases "n = length as") auto

lemma well_valued0_map_map_tree: "\<lbrakk>\<forall>x y. f (x + y) = f x + f y; well_shaped t; well_valued0 as t; as \<noteq> []\<rbrakk> \<Longrightarrow> well_shaped (map_tree f t) \<and> well_valued0 (map f as) (map_tree f t)"
proof (induction t)
  case (Node i j a t1 t2)
  then show ?case
    apply (auto simp:  map_tree_eq_Leaf_iff well_shaped_map_tree val_map_tree_neq_None) (* slow 8 sec *)
     apply (simp add: fold_distr)
     apply (subst map_rev_map_nth_eq)
     apply auto
    done
qed simp

lemma valid_map_map_tree: "\<lbrakk>\<forall>x y. f (x + y) = f x + f y; valid as t\<rbrakk> \<Longrightarrow> valid (map f as) (map_tree f t)"
  apply (cases "as \<noteq> []")
   apply (metis map_tree_eq_Leaf_iff val_map_tree_neq_None valid_def well_valued0_map_map_tree)
  by (metis le_zero_eq list.size(3) tree.exhaust_sel map_tree_eq_Leaf_iff valid_Leaf valid_def well_shaped.simps(2) well_valued0.simps(2))

lemma valid_Nil_iff: "valid [] t \<longleftrightarrow> t = Leaf"
  unfolding valid_def
proof
  assume "well_shaped t \<and> well_valued [] t"
  then show "t = Leaf"
    by (metis le_neq_implies_less list.size(3) not_less_zero tree.collapse well_shaped.simps(2) well_valued0.simps(2))
qed simp

(* alternative slide interface which takes only new inputs *)
abbreviation atomic' where
  "atomic' as b idx \<equiv> Node b b (Some (nth as idx)) Leaf Leaf"

abbreviation atomics' :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a tree list" where
  "atomics' as i j sidx \<equiv> map (\<lambda>b. atomic' as b (b - sidx)) (rev [i ..< Suc j])"

definition slide' :: "'a :: semigroup_add list \<Rightarrow> 'a tree \<Rightarrow> window \<Rightarrow> 'a tree" where
"slide' as t w =
    (let
      ts = atomics' as (max (fst w) (Suc (r t))) (snd w) (Suc (r t));
      ts' = reusables t w
    in fold combine (ts @ ts') Leaf)"

(* examples from paper *)
value[code] "slide' [2,4,5,2 :: nat] Leaf (1, 3)"
value[code] "slide' [2,4,5,2 :: nat] Leaf (1, 4)"
value[code] "slide' [2,4,5,2 :: nat] Leaf (2, 4)"
value[code] "slide' [2 :: nat] (slide' [2,4,5 :: nat] Leaf (1, 3)) (1, 4)"
value[code] "slide' [] (slide' [2 :: nat] (slide' [2,4,5 :: nat] Leaf (1, 3)) (1, 4)) (2, 4)"
value[code] "slide' [2,4,5 :: nat] Leaf (1, 3)"
value[code] "slide' [2 :: nat] (slide' [2,4,5 :: nat] Leaf (1, 3)) (2, 4)"

(* unused *)
lemma atomics_eq_atomics': "\<lbrakk>0 < i; length as \<ge> j\<rbrakk> \<Longrightarrow> atomics as i j = atomics' (drop (i-1) as) i j i"
  by auto

(* unused *)
lemma atomics'_generalized: "\<lbrakk>0 < i; length as \<ge> Suc j - k; n + k \<le> i\<rbrakk> \<Longrightarrow> atomics' as i j k = atomics' (drop n as) i j (k+n)"
  by auto

lemma slide_eq_slide':
  assumes "0 < fst w" "fst w \<le> snd w" "valid as t" "r t = length as" "l t \<le> fst w" "r t \<le> snd w" "snd w \<le> length (as @ as')"
  shows "slide (as @ as') t w = slide' as' t w"
proof (cases "r t = snd w")
  case True
  with assms have *: "atomics' (as @ as') (max (fst w) (Suc (r t))) (snd w) 1 = []"
    by simp
  from True assms have "atomics' as' (max (fst w) (Suc (r t))) (snd w) (Suc (r t)) = []"
    by simp
  with * show ?thesis
    unfolding slide_def slide'_def by simp
next
  case False
  with assms have "r t < snd w"
    by simp
  with assms have "atomic' (as @ as') (snd w) (snd w - Suc 0) = atomic' as' (snd w) (snd w - Suc (length as))"
    by (simp add: leD nth_append)
  with assms have *: "\<forall>i. i \<in> set ([max (fst w) (Suc (length as))..<snd w]) \<longrightarrow> atomic' (as @ as') i (i - Suc 0) = atomic' as' i (i - Suc (length as))"
    by (smt Suc_diff_diff Suc_diff_le Suc_pred atLeastLessThan_iff diff_is_0_eq dual_order.order_iff_strict leD max.bounded_iff max_def_raw nth_append set_upt)
  then have "map (\<lambda>i. atomic' (as @ as') i (i - Suc 0)) (rev [max (fst w) (Suc (length as))..<snd w]) = map (\<lambda>b. atomic' as' b (b - Suc (r t))) (rev [max (fst w) (Suc (r t))..<snd w])"
    by (simp add: assms(4))
  with assms have "atomics' (as @ as') (max (fst w) (Suc (r t))) (snd w) 1 = atomics' as' (max (fst w) (Suc (r t))) (snd w) (Suc (r t))"
    by (smt One_nat_def Suc_pred atLeastLessThan_iff diff_Suc_Suc dual_order.order_iff_strict dual_order.strict_trans1 leD map_eq_conv max_def_raw not_less_eq nth_append set_rev set_upt)
  then show ?thesis
    unfolding slide_def slide'_def
    by presburger
qed

lemma sum_eq_sum_append: "\<lbrakk>0 < i; i \<le> j; j \<le> length as\<rbrakk> \<Longrightarrow> sum as i j = sum (as @ as') i j"
proof -
  assume assms: "0 < i" "i \<le> j" "j \<le> length as"
  then have *: "rev (map ((!) as) [i - Suc 0..<j - Suc 0]) = rev (map ((!) (as@as')) [i - Suc 0..<j - Suc 0])"
    by (auto simp: nth_append)
  from assms have "as ! (j - Suc 0) = (as @ as') ! (j - Suc 0)"
    by (auto simp: nth_append)
  then show ?thesis
    by (simp add: *)
qed

lemma well_valued0_append: "\<lbrakk>well_shaped t; well_valued0 as t\<rbrakk> \<Longrightarrow> well_valued0 (as @ as') t"
proof (induction t)
  case (Node i j a t1 t2)
  then show ?case
    using sum_eq_sum_append by (smt length_append less_le trans_le_add1 tree.sel(8) well_shaped.simps(2) well_shaped_lchild well_valued0.simps(2))
qed simp

lemma valid_append: "valid as t \<Longrightarrow> valid (as @ as') t"
  unfolding valid_def
  by (auto intro: well_valued0_append)

lemma valid_slide_append: "\<lbrakk>0 < fst w; fst w \<le> snd w; valid as t; l t \<le> fst w; r t \<le> snd w; snd w \<le> length as + length as'\<rbrakk> \<Longrightarrow>
  valid (as @ as') (slide (as @ as') t w) \<and> l (slide (as @ as') t w) = fst w \<and> r (slide (as @ as') t w) = snd w"
  by (auto simp: valid_append valid_slide)

(* correctness of alternative slide interface *)
lemma valid_slide':
  assumes "0 < fst w" "fst w \<le> snd w" "valid as t" "length as = r t" "length as' \<ge> snd w - r t" "l t \<le> fst w" "r t \<le> snd w"
  shows "valid (as @ as') (slide' as' t w) \<and> l (slide' as' t w) = fst w \<and> r (slide' as' t w) = snd w"
proof -
  from assms have "valid (as @ as') (slide (as @ as') t w) \<and> l (slide (as @ as') t w) = fst w \<and> r (slide (as @ as') t w) = snd w"
    using valid_slide_append by (metis add_le_cancel_left le_add_diff_inverse)
  with assms show ?thesis
    using slide_eq_slide' by (metis add_le_cancel_left le_add_diff_inverse length_append)
qed

lemma sum_eq_sum_prepend: "\<lbrakk>0 < i; i \<le> j; length xs < i; length ys = length xs\<rbrakk> \<Longrightarrow> sum (xs @ as) i j = sum (ys @ as) i j"
proof -
  assume assms: "0 < i" "i \<le> j" "length xs < i" "length ys = length xs"
  then have *: "rev (map ((!) (xs @ as)) [i - Suc 0..<j - Suc 0]) = rev (map ((!) (ys @ as)) [i - Suc 0..<j - Suc 0])"
    by (auto simp: nth_append)
  from assms have "(xs @ as) ! (j - Suc 0) = (ys @ as) ! (j - Suc 0)"
    by (auto simp: nth_append)
  then show ?thesis
    by (simp add: *)
qed

lemma well_valued0_prepend: "\<lbrakk>length xs \<le> l t - 1; length ys = length xs; well_shaped t; well_valued0 (xs @ as) t\<rbrakk> \<Longrightarrow> well_valued0 (ys @ as) t"
proof (induction t)
  case (Node i j a t1 t2)
  then have well_valued0_t1: "well_valued0 (ys @ as) t1"
    by auto
  from Node have "well_valued0 (ys @ as) t2"
    apply auto
     apply (metis One_nat_def Suc_pred diff_Suc_1 le_Suc_eq le_Suc_ex trans_le_add1 tree.exhaust_sel well_shaped.simps(2))
    by (metis One_nat_def diff_Suc_1 diff_le_self le_trans tree.exhaust_sel well_shaped.simps(2))
  with Node well_valued0_t1 show ?case
  proof -
    have f1: "0 < i \<and> j \<le> length (xs @ as) \<and> (a = None \<or> a = Some (SWA.sum (xs @ as) i j)) \<and> well_valued0 (xs @ as) t1 \<and> well_valued0 (xs @ as) t2 \<and> (t2 = Leaf \<or> val t2 \<noteq> None)"
      by (meson \<open>well_valued0 (xs @ as) (Node i j a t1 t2)\<close> well_valued0.simps(2))
    then have f2: "j \<le> length (ys @ as)"
      by (simp add: \<open>length ys = length xs\<close>)
    have "a = None \<or> a = Some (SWA.sum (ys @ as) i j)"
      using f1 by (metis Node.prems(1) Node.prems(2) Node.prems(3) One_nat_def Suc_pred le_imp_less_Suc sum_eq_sum_prepend tree.sel(2) well_shaped.simps(2))
    then show ?thesis
      using f2 f1 \<open>well_valued0 (ys @ as) t2\<close> well_valued0.simps(2) well_valued0_t1 by blast
  qed
qed simp

lemma valid_prepend: "\<lbrakk>length xs \<le> l t - 1; length ys = length xs; valid (xs @ as) t\<rbrakk> \<Longrightarrow> valid (ys @ as) t"
  unfolding valid_def
  by (auto intro: well_valued0_prepend)

lemma take_eq_append_take_take_drop: "m \<le> n \<Longrightarrow> take n xs = take m xs @ take (n-m) (drop m xs)"
proof (induction xs)
  case (Cons a xs)
  then show ?case
    by (metis le_add_diff_inverse take_add)
qed simp

lemma well_valued0_take_r: "\<lbrakk>well_shaped t; well_valued0 as t\<rbrakk> \<Longrightarrow> well_valued0 (take (r t) as) t"
proof (induction t)
  case (Node i j a t1 t2)
  from Node have well_valued0_t1: "well_valued0 (take j as) t1"
  proof -
    from Node have "r t1 \<le> j"
      using r_lchild_le_r by (metis tree.sel(4) tree.sel(8))
    with Node have "take j as = take (r t1) as @ take (j - r t1) (drop (r t1) as)"
      using take_eq_append_take_take_drop[of "r t1" j as] by simp
    with Node show ?thesis
      by (auto intro!: well_valued0_append)
  qed
  from Node have well_valued0_t2: "well_valued0 (take j as) t2"
    by auto
  from Node have sum_eq: "fold (+) (rev (map ((!) as) [l t1 - Suc 0..<r t2 - Suc 0])) (as ! (r t2 - Suc 0)) =
      fold (+) (rev (map ((!) (take (r t2) as)) [l t1 - Suc 0..<r t2 - Suc 0])) (as ! (r t2 - Suc 0))"
    using sum_eq_sum_append
    by (smt One_nat_def append_take_drop_id diff_Suc_less dual_order.strict_iff_order dual_order.strict_trans1 length_upt list.simps(8) list.size(3) nth_append tree.exhaust_sel tree.sel(3) upt_0 well_shaped.simps(2) well_valued0.simps(2))
  from Node well_valued0_t1 well_valued0_t2 sum_eq show ?case
    by auto
qed simp

lemma valid_take_r: "valid as t \<Longrightarrow> valid (take (r t) as) t"
  unfolding valid_def
  by (auto intro: well_valued0_take_r)

lemma well_valued0_butlast: "\<lbrakk>well_shaped t; well_valued0 as t; r t < length as\<rbrakk> \<Longrightarrow> well_valued0 (butlast as) t"
proof (induction t)
  case (Node i j a t1 t2)
  then  have r_le_length: "j \<le> length (butlast as)"
    by simp
  from Node have "i > 0"
    by simp
  with r_le_length Node have sum_eq: "sum as i j = sum (butlast as) i j"
    by (metis append_butlast_last_id le_zero_eq less_imp_le_nat list.size(3) neq_iff sum_eq_sum_append well_shaped.simps(2))
  from Node have "r t1 < length as"
    by (metis dual_order.strict_trans2 r_lchild_le_r tree.sel(8))
  with Node r_le_length show ?case
    by (metis (no_types, lifting) dual_order.strict_iff_order sum_eq tree.sel(10) tree.sel(4) well_shaped.simps(2) well_shaped_rchild well_valued0.simps(2))
qed simp

lemma well_valued0_append_butlast_lchild: "\<lbrakk>well_shaped t; well_valued0 as t\<rbrakk> \<Longrightarrow> well_valued0 (butlast as @ [last as + x]) (lchild t)"
proof (cases t)
  case (Node i j a t1 t2)
  assume assms: "well_shaped t" "well_valued0 as t"
  from Node assms have "r t1 < length as"
    by (smt Suc_le_lessD dual_order.antisym dual_order.strict_iff_order dual_order.trans tree.exhaust_sel tree.sel(3) well_shaped.simps(2) well_valued0.simps(2))
  with Node assms show ?thesis
    by (auto simp: well_valued0_butlast well_valued0_append)
qed simp

lemma sum_update_rightmost: "\<lbrakk>0 < i; i \<le> j; length as = j\<rbrakk> \<Longrightarrow> sum as i j + x = sum (butlast as @ [last as + x]) i j"
  by (smt atLeastLessThan_iff fold_add_add last_conv_nth length_butlast list.size(3) map_eq_conv not_le nth_append nth_append_length nth_butlast set_upt)

lemma well_valued0_update_rightmost: "\<lbrakk>well_shaped t; well_valued0 as t; length as = r t\<rbrakk> \<Longrightarrow> well_valued0 (butlast as @ [last as + x]) (update_rightmost (\<lambda>a. a + x) t)"
proof (induction t)
  case Leaf
  then show ?case
    by (auto simp add: valid_Leaf)
next
  case (Node i j a t1 t2)
  then have well_valued0_t1: "well_valued0 (butlast as @ [last as + x]) t1"
    using well_valued0_append_butlast_lchild by (metis tree.sel(8))
  from Node have well_valued0_t2: "well_valued0 (butlast as @ [last as + x]) (update_rightmost ((\<lambda>a. a + x)) t2)"
    by (metis \<open>well_valued0 (butlast as @ [last as + x]) t1\<close> dual_order.strict_iff_order tree.sel(4) update_rightmost.simps(1) well_shaped.simps(2) well_valued0.simps(2))
  with well_valued0_t1 Node show ?case
    using sum_update_rightmost
    by (cases a)
      (auto simp: val_update_rightmost_neq_None)
qed

(* correctness of update_rightmost *)
lemma valid_update_rightmost: "\<lbrakk>valid as t; length as = r t\<rbrakk> \<Longrightarrow> valid (butlast as @ [last as + x]) (update_rightmost (\<lambda>a. a + x) t)"
  unfolding valid_def
  using well_valued0_update_rightmost by (metis update_rightmost.simps(1) val_update_rightmost_neq_None well_shaped_update_rightmost)

end

lemma sum_alt:
  "0 < i \<Longrightarrow> i \<le> j \<Longrightarrow> sum (as :: _ :: monoid_add list) i j = fold (+) (rev ((map (nth as) [i - 1 ..< j]))) 0"
  by (induct j) auto

lemma fold_filter:
  fixes xs :: "_ :: monoid_add list"
  shows "fold (+) xs z = fold (+) (filter (\<lambda>x. x \<noteq> 0) xs) z"
  by (induct xs arbitrary: z) auto

instantiation set :: (type) semigroup_add begin
definition plus_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where "plus_set = (\<union>)"
instance proof qed (auto simp: plus_set_def)
end

instantiation set :: (type) monoid_add begin
definition zero_set :: "'a set" where "zero_set = {}"
instance proof qed (auto simp: zero_set_def plus_set_def)
end

end