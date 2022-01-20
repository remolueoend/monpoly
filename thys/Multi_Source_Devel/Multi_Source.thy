(*<*)
theory Multi_Source
  imports
    "MFOTL_Monitor_Devel.Abstract_Monitor"
    "HOL-Library.BNF_Corec"
    "HOL-Library.DAList"
begin
(*>*)

section \<open>Parallel monitoring of multiple input traces\<close>

subsection \<open>Composition of nondeterministic functions\<close>

text \<open>
  We represent nondeterministic functions by functions that return sets of
  possible results. The sets can be empty, indicating partiality.
  Nondeterministic functions are used both for modelling assumptions about
  the environment of the monitor and for modellings its parallel
  implementation.

  Function composition is written from left to right in this section:
\<close>

notation fcomp (infixr "\<circ>>" 55)

text \<open>Lifting deterministic functions:\<close>

definition determ :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b set" where
  "determ f = (\<lambda>x. {f x})"

lemma in_determ_iff_eq[simp]: "y \<in> determ f x \<longleftrightarrow> y = f x"
  by (simp add: determ_def)

lemma eq_determI: "f \<le> determ g \<Longrightarrow> (\<And>x. f x \<noteq> {}) \<Longrightarrow> f = determ g"
  by (fastforce simp: le_fun_def fun_eq_iff determ_def)

text \<open>Composition operator for non-deterministic functions:\<close>

definition kleisli_set :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('b \<Rightarrow> 'c set) \<Rightarrow> 'a \<Rightarrow> 'c set" where
  "kleisli_set f g = (\<lambda>x. \<Union> (g ` f x))"

notation kleisli_set (infixr "\<circ>\<then>" 55)

lemma kleisli_set_assoc: "f \<circ>\<then> (g \<circ>\<then> h) = (f \<circ>\<then> g) \<circ>\<then> h"
  by (auto simp: kleisli_set_def)

lemma determ_fcomp_eq_kleisli: "determ (f \<circ>> g) = determ f \<circ>\<then> determ g"
  by (auto simp: kleisli_set_def)

lemma kleisli_set_mono: "f \<le> f' \<Longrightarrow> g \<le> g' \<Longrightarrow> f \<circ>\<then> g \<le> f' \<circ>\<then> g'"
  by (fastforce simp: le_fun_def kleisli_set_def)

lemma in_kleisli_set_iff: "z \<in> (f \<circ>\<then> g) x \<longleftrightarrow> (\<exists>y. z \<in> g y \<and> y \<in> f x)"
  by (auto simp: kleisli_set_def)

text \<open>Lifting nondeterministic functions to lists:\<close>

definition mapM_set :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a list \<Rightarrow> 'b list set" where
  "mapM_set f xs = listset (map f xs)"

lemma in_listset_iff: "xs \<in> listset As \<longleftrightarrow> list_all2 (\<in>) xs As"
  by (induction As arbitrary: xs) (auto simp: set_Cons_def list_all2_Cons2)

lemma in_mapM_set_iff: "xs \<in> mapM_set f ys \<longleftrightarrow> list_all2 (\<lambda>x y. x \<in> f y) xs ys"
  by (simp add: mapM_set_def in_listset_iff list.rel_map)

lemma mapM_set_mono: "f \<le> f' \<Longrightarrow> mapM_set f \<le> mapM_set f'"
  by (fastforce simp: le_fun_def in_mapM_set_iff elim!: list.rel_mono_strong)

lemma mapM_set_determ: "mapM_set (determ f) = determ (map f)"
  by (auto simp: fun_eq_iff in_mapM_set_iff list.rel_map(2)[where g=f, symmetric] list.rel_eq
      intro!: list.rel_refl)

lemma kleisli_mapM_set: "mapM_set f \<circ>\<then> mapM_set g = mapM_set (f \<circ>\<then> g)"
proof (intro ext set_eqI iffI)
  fix x z
  assume "z \<in> (mapM_set f \<circ>\<then> mapM_set g) x"
  then obtain y where "list_all2 (\<lambda>a b. a \<in> f b) y x" and "list_all2 (\<lambda>a b. a \<in> g b) z y"
    by (auto simp: kleisli_set_def in_mapM_set_iff)
  then have "list_all2 (\<lambda>a b. a \<in> (f \<circ>\<then> g) b) z x"
    by (auto simp: kleisli_set_def elim: list_all2_trans[rotated])
  then show "z \<in> mapM_set (f \<circ>\<then> g) x"
    by (simp add: in_mapM_set_iff)
next
  fix x z
  assume "z \<in> mapM_set (f \<circ>\<then> g) x"
  then have "list_all2 ((\<lambda>a b. a \<in> g b) OO (\<lambda>a b. a \<in> f b)) z x"
    by (simp add: in_mapM_set_iff in_kleisli_set_iff relcompp_apply[abs_def])
  then obtain y where "z \<in> mapM_set g y" and "y \<in> mapM_set f x"
    by (auto simp: in_mapM_set_iff list.rel_compp)
  then show "z \<in> (mapM_set f \<circ>\<then> mapM_set g) x"
    by (auto simp: kleisli_set_def)
qed

lemma map_in_mapM_setI: "(\<And>x. x \<in> set xs \<Longrightarrow> f x \<in> g x) \<Longrightarrow> map f xs \<in> mapM_set g xs"
  by (auto simp: in_mapM_set_iff list.rel_map intro!: list.rel_refl_strong)

text \<open>
  The composite function \<^term>\<open>f \<circ>\<then> g\<close> returns all values that can be
  reached via some intermediate value in the image of \<^term>\<open>f\<close>. However,
  \<^term>\<open>g\<close> may not be defined (i.e., return an empty set) on other values
  in this image. Therefore, \<^term>\<open>f \<circ>\<then> g\<close> is not suitable for statements
  about the total correctness of a system composed of \<^term>\<open>f\<close> and \<^term>\<open>g\<close>,
  which fails whenever \<^term>\<open>g\<close> fails.

  We introduce a stronger composition operator that fails if the second
  function fails on any possible output of the first function (for a fixed
  input).
\<close>

definition strong_kleisli :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('b \<Rightarrow> 'c set) \<Rightarrow> 'a \<Rightarrow> 'c set" where
  "strong_kleisli f g = (\<lambda>x. if {} \<in> g ` f x then {} else \<Union>(g ` f x))"

notation strong_kleisli (infixr "!\<then>" 55)

lemma strong_kleisli_assoc: "f !\<then> (g !\<then> h) = (f !\<then> g) !\<then> h"
  by (fastforce simp: fun_eq_iff strong_kleisli_def)

lemma strong_kleisli_le_kleisli_set: "f !\<then> g \<le> f \<circ>\<then> g"
  by (auto simp: le_fun_def strong_kleisli_def kleisli_set_def)

lemma strong_kleisli_not_emptyI: "y \<in> f x \<Longrightarrow> (\<And>z. z \<in> f x \<Longrightarrow> g z \<noteq> {}) \<Longrightarrow> (f !\<then> g) x \<noteq> {}"
  by (auto simp: strong_kleisli_def)

lemma strong_kleisli_mono: "f x \<subseteq> f' x \<Longrightarrow> (\<And>y. y \<in> f' x \<Longrightarrow> g y \<subseteq> g' y) \<Longrightarrow>
  (\<And>y. y \<in> f' x \<Longrightarrow> g' y \<noteq> {}) \<Longrightarrow> (f !\<then> g) x \<subseteq> (f' !\<then> g') x"
  by (auto 6 0 simp: strong_kleisli_def)

text \<open>The next lemma does not hold for \<^term>\<open>(\<circ>\<then>)\<close>:\<close>

lemma strong_kleisli_singleton_conv:
  "(f !\<then> g) x = {z} \<longleftrightarrow> (\<exists>y. y \<in> f x) \<and> (\<forall>y. y \<in> f x \<longrightarrow> g y = {z})"
  by (auto simp: strong_kleisli_def dest: equalityD1)


subsection \<open>Indexed traces\<close>

record 'a itsdb = \<comment> \<open>indexed, time-stamped database\<close>
  db :: "'a set"
  ts :: nat
  idx :: nat

text \<open>
  We introduce the notion of an index which lies in between time-points and
  time-stamps. This allows for a unified treatment of different synchronization
  guarantees. The index must increase monotonically and it must refine the
  time-stamps:
\<close>

typedef 'a itrace = "{s :: 'a itsdb stream.
  ssorted (smap idx s) \<and> sincreasing (smap ts s) \<and>
  (\<forall>i j. idx (s !! i) \<le> idx (s !! j) \<longrightarrow> ts (s !! i) \<le> ts (s !! j))}"
  by (rule exI[where x="smap (\<lambda>x. \<lparr>db={}, ts=x, idx=x\<rparr>) nats"])
    (auto simp: stream.map_comp stream.map_ident cong: stream.map_cong)

setup_lifting type_definition_itrace

subsubsection \<open>Projection functions\<close>

lift_definition i\<Gamma> :: "'a itrace \<Rightarrow> nat \<Rightarrow> 'a set" is "\<lambda>s i. db (s !! i)" .
lift_definition i\<tau> :: "'a itrace \<Rightarrow> nat \<Rightarrow> nat" is "\<lambda>s i. ts (s !! i)" .
lift_definition i\<iota> :: "'a itrace \<Rightarrow> nat \<Rightarrow> nat" is "\<lambda>s i. idx (s !! i)" .

lemma i\<iota>_mono: "i \<le> j \<Longrightarrow> i\<iota> \<sigma> i \<le> i\<iota> \<sigma> j"
  by transfer (simp add: ssorted_iff_mono)

lemma ex_i\<tau>_gr: "\<exists>j>i. x < i\<tau> \<sigma> j"
  by transfer (auto dest!: sincreasing_grD)

lemma i\<iota>_refines_i\<tau>: "i\<iota> \<sigma> i \<le> i\<iota> \<sigma> j \<Longrightarrow> i\<tau> \<sigma> i \<le> i\<tau> \<sigma> j"
  by transfer simp

lemma i\<iota>_eq_imp_i\<tau>_eq: "i\<iota> \<sigma> i = i\<iota> \<sigma> j \<Longrightarrow> i\<tau> \<sigma> i = i\<tau> \<sigma> j"
  by (simp add: i\<iota>_refines_i\<tau> antisym)

lemma i\<tau>_mono: "i \<le> j \<Longrightarrow> i\<tau> \<sigma> i \<le> i\<tau> \<sigma> j"
  using i\<iota>_refines_i\<tau>[OF i\<iota>_mono] .

subsubsection \<open>Generalized collapse\<close>

text \<open>
  The generalized collapse of an indexed trace is obtained by merging all
  time-points with the same index. The result has well-defined time-stamps
  because we require that indexes refine time-stamps.
\<close>

definition least_i\<iota> :: "'a itrace \<Rightarrow> nat" where
  "least_i\<iota> \<sigma> = (LEAST i. \<exists>j. i = i\<iota> \<sigma> j)"

definition next_i\<iota> :: "'a itrace \<Rightarrow> nat \<Rightarrow> nat" where
  "next_i\<iota> \<sigma> i = (LEAST i'. i' > i \<and> (\<exists>j. i' = i\<iota> \<sigma> j))"

definition i\<tau>_of_i\<iota> :: "'a itrace \<Rightarrow> nat \<Rightarrow> nat" where
  "i\<tau>_of_i\<iota> \<sigma> i = i\<tau> \<sigma> (LEAST j. i = i\<iota> \<sigma> j)"

definition collapse' :: "'a itrace \<Rightarrow> ('a set \<times> nat) stream" where
  "collapse' \<sigma> = smap (\<lambda>i. (\<Union>j \<in> i\<iota> \<sigma> -` {i}. i\<Gamma> \<sigma> j, i\<tau>_of_i\<iota> \<sigma> i))
    (siterate (next_i\<iota> \<sigma>) (least_i\<iota> \<sigma>))"

lemma ex_eq_i\<iota>: "\<exists>i'\<ge>i. \<exists>j. i' = i\<iota> \<sigma> j"
proof (induction i)
  case 0
  show ?case by auto
next
  case (Suc i)
  then obtain i' j where IH: "i' \<ge> i \<and> i' = i\<iota> \<sigma> j" by blast
  obtain j' where "i\<tau> \<sigma> j < i\<tau> \<sigma> j'"
    using ex_i\<tau>_gr by blast
  then have "i\<iota> \<sigma> j < i\<iota> \<sigma> j'"
    using i\<iota>_refines_i\<tau> le_less_linear by (blast dest: leD)
  with IH have "Suc i \<le> i\<iota> \<sigma> j'"
    by (simp add: Suc_leI)
  then show ?case by blast
qed

lemma ex_eq_i\<iota>_strict: "\<exists>i'>i. \<exists>j. i' = i\<iota> \<sigma> j"
  using ex_eq_i\<iota> by (blast dest: Suc_le_lessD)

lemma ex_funpow_next_i\<iota>1: "\<exists>j. (next_i\<iota> \<sigma> ^^ n) (least_i\<iota> \<sigma>) = i\<iota> \<sigma> j"
proof (cases n)
  case 0
  then show ?thesis
    by (auto simp: least_i\<iota>_def intro: LeastI_ex[where P="\<lambda>i. \<exists>j. i = i\<iota> \<sigma> j"])
next
  case (Suc n)
  have "\<exists>j. next_i\<iota> \<sigma> i = i\<iota> \<sigma> j" for i
    using ex_eq_i\<iota>_strict[of i \<sigma>]
    by (auto 0 3 simp: next_i\<iota>_def intro: LeastI2_ex[where P="\<lambda>i'. i < i' \<and> (\<exists>j. i' = i\<iota> \<sigma> j)"])
  with Suc show ?thesis by simp
qed

lemma ex_funpow_next_i\<iota>2: "\<exists>n. (next_i\<iota> \<sigma> ^^ n) (least_i\<iota> \<sigma>) = i\<iota> \<sigma> j"
proof (induction j)
  case 0
  have "(next_i\<iota> \<sigma> ^^ 0) (least_i\<iota> \<sigma>) = i\<iota> \<sigma> 0"
    using i\<iota>_mono by (auto simp: least_i\<iota>_def intro: Least_equality)
  then show ?case ..
next
  case (Suc j)
  show ?case proof (cases "i\<iota> \<sigma> (Suc j) = i\<iota> \<sigma> j")
    case True
    with Suc.IH show ?thesis by simp
  next
    case False
    then have "i\<iota> \<sigma> j < i\<iota> \<sigma> (Suc j)"
      by (metis le_less lessI i\<iota>_mono)
    then have "next_i\<iota> \<sigma> (i\<iota> \<sigma> j) = i\<iota> \<sigma> (Suc j)"
      by (auto simp: next_i\<iota>_def intro!: Least_equality) (meson leD i\<iota>_mono not_less_eq_eq)
    moreover obtain n where "(next_i\<iota> \<sigma> ^^ n) (least_i\<iota> \<sigma>) = i\<iota> \<sigma> j"
      using Suc.IH ..
    ultimately have "(next_i\<iota> \<sigma> ^^ Suc n) (least_i\<iota> \<sigma>) = i\<iota> \<sigma> (Suc j)"
      by simp
    then show ?thesis ..
  qed
qed

lemma less_next_i\<iota>: "i < next_i\<iota> \<sigma> i"
  using ex_eq_i\<iota>_strict[of i \<sigma>]
  by (fastforce simp: next_i\<iota>_def intro: LeastI2_ex[where P="\<lambda>i'. i < i' \<and> (\<exists>j. i' = i\<iota> \<sigma> j)"])

lemma mono_funpow_next_i\<iota>: "a \<le> b \<Longrightarrow> (next_i\<iota> \<sigma> ^^ a) (least_i\<iota> \<sigma>) \<le> (next_i\<iota> \<sigma> ^^ b) (least_i\<iota> \<sigma>)"
proof (induction b)
  case 0
  then show ?case by simp
next
  case (Suc b)
  show ?case proof (cases "Suc b = a")
    case True
    then show ?thesis by simp
  next
    case False
    with Suc have "(next_i\<iota> \<sigma> ^^ a) (least_i\<iota> \<sigma>) \<le> (next_i\<iota> \<sigma> ^^ b) (least_i\<iota> \<sigma>)"
      by simp
    then show ?thesis
      using less_next_i\<iota>[THEN less_imp_le]
      by (auto intro: order.trans)
  qed
qed

lemma le_funpow_next_i\<iota>: "(next_i\<iota> \<sigma> ^^ a) (least_i\<iota> \<sigma>) \<le> (next_i\<iota> \<sigma> ^^ b) (least_i\<iota> \<sigma>) \<Longrightarrow> a \<le> b"
proof (induction a arbitrary: b)
  case 0
  show ?case by simp
next
  case (Suc a)
  then show ?case
    by (metis antisym funpow.simps(2) leD less_next_i\<iota> linear mono_funpow_next_i\<iota> not_less_eq_eq o_apply)
qed

lemma i\<tau>_of_i\<iota>_mono:
  assumes "i\<iota> \<sigma> a \<le> i\<iota> \<sigma> b"
  shows "i\<tau>_of_i\<iota> \<sigma> (i\<iota> \<sigma> a) \<le> i\<tau>_of_i\<iota> \<sigma> (i\<iota> \<sigma> b)"
proof -
  have "(LEAST j. i\<iota> \<sigma> a = i\<iota> \<sigma> j) \<le> (LEAST j. i\<iota> \<sigma> b = i\<iota> \<sigma> j)"
  proof (cases "i\<iota> \<sigma> a = i\<iota> \<sigma> b")
    case True
    then show ?thesis by simp
  next
    case False
    with assms have "i\<iota> \<sigma> a < i\<iota> \<sigma> b" by simp
    show ?thesis proof (rule LeastI2_ex[where P="\<lambda>j. i\<iota> \<sigma> b = i\<iota> \<sigma> j"])
      fix c
      have "(LEAST j. i\<iota> \<sigma> a = i\<iota> \<sigma> j) \<le> a"
        by (simp add: Least_le)
      also assume "i\<iota> \<sigma> b = i\<iota> \<sigma> c"
      then have "i\<iota> \<sigma> a < i\<iota> \<sigma> c"
        using \<open>i\<iota> \<sigma> a < i\<iota> \<sigma> b\<close> by simp
      then have "a < c"
        using i\<iota>_mono le_less_linear by (blast dest: leD)
      finally show "(LEAST j. i\<iota> \<sigma> a = i\<iota> \<sigma> j) \<le> c"
        by simp
    qed blast
  qed
  then show ?thesis by (simp add: i\<tau>_of_i\<iota>_def i\<tau>_mono)
qed

lemma i\<tau>_of_i\<iota>_eq: "i\<tau>_of_i\<iota> \<sigma> (i\<iota> \<sigma> j) = i\<tau> \<sigma> j"
  by (fastforce simp: i\<tau>_of_i\<iota>_def intro: i\<iota>_eq_imp_i\<tau>_eq LeastI2_ex[where P="\<lambda>j'. i\<iota> \<sigma> j = i\<iota> \<sigma> j'"])

lift_definition collapse :: "'a itrace \<Rightarrow> 'a trace" is collapse'
proof (intro conjI)
  fix \<sigma> :: "'a itrace"
  have "i\<tau>_of_i\<iota> \<sigma> ((next_i\<iota> \<sigma> ^^ a) (least_i\<iota> \<sigma>)) \<le> i\<tau>_of_i\<iota> \<sigma> ((next_i\<iota> \<sigma> ^^ b) (least_i\<iota> \<sigma>))"
    if "a \<le> b" for a b
  proof -
    obtain ja where a_eq: "(next_i\<iota> \<sigma> ^^ a) (least_i\<iota> \<sigma>) = i\<iota> \<sigma> ja"
      using ex_funpow_next_i\<iota>1 ..
    obtain jb where b_eq: "(next_i\<iota> \<sigma> ^^ b) (least_i\<iota> \<sigma>) = i\<iota> \<sigma> jb"
      using ex_funpow_next_i\<iota>1 ..
    have "(next_i\<iota> \<sigma> ^^ a) (least_i\<iota> \<sigma>) \<le> (next_i\<iota> \<sigma> ^^ b) (least_i\<iota> \<sigma>)"
      using \<open>a \<le> b\<close> by (rule mono_funpow_next_i\<iota>)
    then show ?thesis
      unfolding a_eq b_eq by (rule i\<tau>_of_i\<iota>_mono)
  qed
  then show "ssorted (smap snd (collapse' \<sigma>))"
    by (simp add: ssorted_iff_mono collapse'_def)

  have "\<exists>a. x < i\<tau>_of_i\<iota> \<sigma> ((next_i\<iota> \<sigma> ^^ a) (least_i\<iota> \<sigma>))" for x
  proof -
    obtain ja where "x < i\<tau> \<sigma> ja"
      using ex_i\<tau>_gr by blast
    moreover obtain a where a_eq: "(next_i\<iota> \<sigma> ^^ a) (least_i\<iota> \<sigma>) = i\<iota> \<sigma> ja"
      using ex_funpow_next_i\<iota>2 ..
    ultimately have "x < i\<tau>_of_i\<iota> \<sigma> ((next_i\<iota> \<sigma> ^^ a) (least_i\<iota> \<sigma>))"
      by (simp add: i\<tau>_of_i\<iota>_eq)
    then show ?thesis ..
  qed
  then show "sincreasing (smap snd (collapse' \<sigma>))"
    by (simp add: sincreasing_def collapse'_def)
qed

text \<open>Alternative characterisation of \<^term>\<open>collapse\<close> via a mapping function.\<close>

definition collapse_map :: "'a itrace \<Rightarrow> nat \<Rightarrow> nat" where
  "collapse_map \<sigma> i = (THE n. (next_i\<iota> \<sigma> ^^ n) (least_i\<iota> \<sigma>) = i\<iota> \<sigma> i)"

lemma collapse_map_ex1: "\<exists>!n. (next_i\<iota> \<sigma> ^^ n) (least_i\<iota> \<sigma>) = i\<iota> \<sigma> i"
  by (metis ex_funpow_next_i\<iota>2 antisym le_funpow_next_i\<iota> order_refl)

lemma surj_collapse_map: "surj (collapse_map \<sigma>)"
proof (rule surjI)
  fix n
  define f where "f = (\<lambda>n. LEAST i. (next_i\<iota> \<sigma> ^^ n) (least_i\<iota> \<sigma>) = i\<iota> \<sigma> i)"
  have *: "(next_i\<iota> \<sigma> ^^ n) (least_i\<iota> \<sigma>) = i\<iota> \<sigma> (f n)"
    unfolding f_def by (rule LeastI_ex[OF ex_funpow_next_i\<iota>1])
  moreover have "n' = n" if "(next_i\<iota> \<sigma> ^^ n') (least_i\<iota> \<sigma>) = i\<iota> \<sigma> (f n)" for n'
    by (metis antisym le_funpow_next_i\<iota> eq_refl * that)
  ultimately show "collapse_map \<sigma> (f n) = n"
    unfolding collapse_map_def by (rule the_equality)
qed

lemma mono_collapse_map: "mono (collapse_map \<sigma>)"
proof
  fix i i' :: nat
  assume "i \<le> i'"
  then have *: "i\<iota> \<sigma> i \<le> i\<iota> \<sigma> i'" by (rule i\<iota>_mono)
  show "collapse_map \<sigma> i \<le> collapse_map \<sigma> i'"
    unfolding collapse_map_def
    apply (rule the1I2[OF collapse_map_ex1])
    apply (rule the1I2[OF collapse_map_ex1])
    by (metis le_funpow_next_i\<iota> *)
qed

lemma collapse_map_eq: "(next_i\<iota> \<sigma> ^^ collapse_map \<sigma> i) (least_i\<iota> \<sigma>) = i\<iota> \<sigma> i"
  unfolding collapse_map_def using collapse_map_ex1 by (rule theI')

lemma collapse_map_consistent: "i\<iota> \<sigma> i = i\<iota> \<sigma> i' \<longleftrightarrow> collapse_map \<sigma> i = collapse_map \<sigma> i'"
  (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  then show ?R using collapse_map_ex1 by (auto simp: collapse_map_def)
next
  assume ?R
  then show ?L using collapse_map_eq by metis
qed

lemma less_i\<iota>D: "i\<iota> \<sigma> i < i\<iota> \<sigma> j \<Longrightarrow> i < j"
  by (metis i\<iota>_mono leD le_less_linear)

lemma unique_collapse_map:
  assumes "surj f" and "mono f" and consistent: "\<And>i i'. i\<iota> \<sigma> i = i\<iota> \<sigma> i' \<longleftrightarrow> f i = f i'"
  shows "f = collapse_map \<sigma>"
proof -
  have *: "(next_i\<iota> \<sigma> ^^ f i) (least_i\<iota> \<sigma>) = i\<iota> \<sigma> i" for i
  proof (induction i)
    case 0
    obtain x where "f x = 0"
      using \<open>surj f\<close> by (metis surjE)
    have "f 0 \<le> f x" using \<open>mono f\<close> by (simp add: monoD)
    then have "f 0 = 0" using \<open>f x = 0\<close> by simp
    then show ?case by (auto simp: least_i\<iota>_def intro: Least_equality i\<iota>_mono)
  next
    case (Suc i)
    show ?case proof (cases "f (Suc i) = f i")
      case True
      then show ?thesis using Suc.IH consistent by simp
    next
      case False
      have 1: "f (Suc i) = Suc (f i)"
      proof -
        obtain x where "f x = Suc (f i)"
          using \<open>surj f\<close> by (metis surjE)
        then have "i < x"
          using mono_strict_invE[OF \<open>mono f\<close>, of i x] by simp
        then have "f (Suc i) \<le> f x"
          using \<open>mono f\<close> by (simp add: monoD)
        moreover have "f (Suc i) \<ge> f i"
          using \<open>mono f\<close> by (simp add: monoD)
        ultimately show ?thesis
          using False \<open>f x = Suc (f i)\<close> by simp
      qed
      then have "i\<iota> \<sigma> i < i\<iota> \<sigma> (Suc i)"
        by (metis Suc_n_not_le_n consistent i\<iota>_mono linear order.not_eq_order_implies_strict)
      then have "next_i\<iota> \<sigma> (i\<iota> \<sigma> i) = i\<iota> \<sigma> (Suc i)"
        by (auto simp: next_i\<iota>_def intro!: Least_equality i\<iota>_mono dest: less_i\<iota>D)
      then show ?thesis using Suc.IH 1 by simp
    qed
  qed
  moreover have "n = f i" if "(next_i\<iota> \<sigma> ^^ n) (least_i\<iota> \<sigma>) = i\<iota> \<sigma> i" for n i
    using * collapse_map_ex1 that by blast
  ultimately show ?thesis
    by (auto simp: fun_eq_iff collapse_map_def intro!: the_equality[symmetric])
qed

lemma \<tau>_collapse: "\<tau> (collapse \<sigma>) (collapse_map \<sigma> i) = i\<tau> \<sigma> i"
  by (simp add: \<tau>.rep_eq collapse.rep_eq collapse'_def collapse_map_eq i\<tau>_of_i\<iota>_eq)

lemma \<Gamma>_collapse: "\<Gamma> (collapse \<sigma>) j = \<Union>{i\<Gamma> \<sigma> i | i. collapse_map \<sigma> i = j}"
  by (auto simp: \<Gamma>.rep_eq collapse.rep_eq collapse'_def collapse_map_eq)
    (metis collapse_map_eq collapse_map_ex1)

lemma collapse_alt:
  assumes "surj f" and "mono f" and "\<And>i i'. i\<iota> \<sigma> i = i\<iota> \<sigma> i' \<longleftrightarrow> f i = f i'"
    and \<tau>_c: "\<And>i. \<tau> c (f i) = i\<tau> \<sigma> i" and \<Gamma>_c: "\<And>j. \<Gamma> c j = \<Union>{i\<Gamma> \<sigma> i | i. f i = j}"
  shows "c = collapse \<sigma>"
proof -
  from assms(1-3) have f_eq: "f = collapse_map \<sigma>"
    by (rule unique_collapse_map)
  show ?thesis
  proof (rule trace_eqI)
    fix j
    show "\<Gamma> c j = \<Gamma> (collapse \<sigma>) j"
      unfolding \<Gamma>_c \<Gamma>_collapse f_eq ..
  next
    fix j
    obtain i where "collapse_map \<sigma> i = j"
      using surj_collapse_map by (metis surjE)
    moreover have "\<tau> c (f i) = \<tau> (collapse \<sigma>) (collapse_map \<sigma> i)"
      unfolding \<tau>_c \<tau>_collapse ..
    ultimately show "\<tau> c j = \<tau> (collapse \<sigma>) j"
      by (simp add: f_eq)
  qed
qed

subsubsection \<open>Adequacy\<close>

text \<open>
  An indexed trace is adequate for a specification if the trace satisfies
  essentially the same valuations as its collapse, modulo the mapping of
  stream positions.
\<close>

lift_definition forget_idx :: "'a itrace \<Rightarrow> 'a trace" is "smap (\<lambda>x. (db x, ts x))"
  by (simp add: stream.map_comp comp_def ssorted_iff_mono)

definition (in fo_spec) adequate :: "'a itrace \<Rightarrow> bool" where
  "adequate \<sigma> \<longleftrightarrow> (\<forall>v i. sat (collapse \<sigma>) v i \<longleftrightarrow> (\<exists>j. collapse_map \<sigma> j = i \<and> sat (forget_idx \<sigma>) v j))"

lemma (in fo_spec) adequate_verdicts_collapse: "adequate \<sigma> \<Longrightarrow>
  verdicts (collapse \<sigma>) = apfst (collapse_map \<sigma>) ` verdicts (forget_idx \<sigma>)"
  unfolding adequate_def verdicts_def by (auto intro: rev_image_eqI)

lemma (in cosafety_monitor) adequate_verdicts_collapse_M: "traces = UNIV \<Longrightarrow> adequate \<sigma> \<Longrightarrow>
  M_limit (collapse \<sigma>) = apfst (collapse_map \<sigma>) ` M_limit (forget_idx \<sigma>)"
  using adequate_verdicts_collapse by (simp add: M_limit_eq)

subsubsection \<open>Adding indexes\<close>

text \<open>Time-points as indexes:\<close>

lift_definition add_timepoints :: "'a trace \<Rightarrow> 'a itrace" is
  "smap2 (\<lambda>i (db, ts). \<lparr>db=db, ts=ts, idx=i\<rparr>) nats"
  by (auto simp: split_beta smap2_szip stream.map_comp smap_szip_fst[of id, simplified]
      stream.map_ident smap_szip_snd ssorted_iff_mono cong: stream.map_cong)

lemma i\<Gamma>_timepoints[simp]: "i\<Gamma> (add_timepoints \<sigma>) = \<Gamma> \<sigma>"
  by transfer (simp add: split_beta)

lemma i\<tau>_timepoints[simp]: "i\<tau> (add_timepoints \<sigma>) = \<tau> \<sigma>"
  by transfer (simp add: split_beta)

lemma i\<iota>_timepoints[simp]: "i\<iota> (add_timepoints \<sigma>) = id"
  by transfer (simp add: split_beta id_def)

lemma least_i\<iota>_timepoints[simp]: "least_i\<iota> (add_timepoints \<sigma>) = 0"
  by (simp add: least_i\<iota>_def)

lemma next_i\<iota>_timepoints[simp]: "next_i\<iota> (add_timepoints \<sigma>) = Suc"
  by (simp add: fun_eq_iff next_i\<iota>_def Least_equality)

lemma i\<tau>_of_i\<iota>_timepoints[simp]: "i\<tau>_of_i\<iota> (add_timepoints \<sigma>) = \<tau> \<sigma>"
  by (simp add: fun_eq_iff i\<tau>_of_i\<iota>_def Least_equality)

lemma all_snth_eq_imp_eq: "(\<And>n. a !! n = b !! n) \<Longrightarrow> a = b"
  by (metis stream.map_cong stream_smap_nats)

lemma snth_Rep_trace: "Rep_trace \<sigma> !! i = (\<Gamma> \<sigma> i, \<tau> \<sigma> i)"
  by transfer simp

lemma collapse_add_timepoints: "collapse (add_timepoints \<sigma>) = \<sigma>"
proof -
  have "collapse' (add_timepoints \<sigma>) = Rep_trace \<sigma>"
    by (auto simp: collapse'_def snth_Rep_trace intro: all_snth_eq_imp_eq)
  then show ?thesis
    by (intro Rep_trace_inject[THEN iffD1]) (simp add: collapse.rep_eq)
qed

text \<open>Time-stamps as indexes:\<close>

lift_definition add_timestamps :: "'a trace \<Rightarrow> 'a itrace" is
  "smap (\<lambda>(db, ts). \<lparr>db=db, ts=ts, idx=ts\<rparr>)"
  by (auto simp: split_beta stream.map_comp cong: stream.map_cong)

lemma i\<Gamma>_timestamps[simp]: "i\<Gamma> (add_timestamps \<sigma>) = \<Gamma> \<sigma>"
  by transfer (simp add: split_beta)

lemma i\<tau>_timestamps[simp]: "i\<tau> (add_timestamps \<sigma>) = \<tau> \<sigma>"
  by transfer (simp add: split_beta)

lemma i\<iota>_timestamps[simp]: "i\<iota> (add_timestamps \<sigma>) = \<tau> \<sigma>"
  by transfer (simp add: split_beta)

lemma collapse_add_timestamps_alt:
  assumes "surj f" and "mono f" and consistent_lr: "\<And>i i'. \<tau> \<sigma> i = \<tau> \<sigma> i' \<Longrightarrow> f i = f i'"
    and \<tau>_c: "\<And>i. \<tau> c (f i) = \<tau> \<sigma> i" and \<Gamma>_c: "\<And>j. \<Gamma> c j = \<Union>{\<Gamma> \<sigma> i | i. f i = j}"
  shows "collapse (add_timestamps \<sigma>) = c"
proof -
  have "\<tau> \<sigma> i = \<tau> \<sigma> i' \<longleftrightarrow> f i = f i'" for i i'
    using consistent_lr \<tau>_c by metis
  then show ?thesis
    using collapse_alt[where \<sigma>="add_timestamps \<sigma>", OF \<open>surj f\<close> \<open>mono f\<close>] \<tau>_c \<Gamma>_c
    by auto
qed

subsubsection \<open>Slicing\<close>

lift_definition map_i\<Gamma> :: "('a set \<Rightarrow> 'b set) \<Rightarrow> 'a itrace \<Rightarrow> 'b itrace" is
  "\<lambda>f. smap (\<lambda>x. \<lparr>db = f (db x), ts = ts x, idx = idx x\<rparr>)"
  by (simp add: stream.map_comp cong: stream.map_cong)

lemma i\<Gamma>_map_i\<Gamma>[simp]: "i\<Gamma> (map_i\<Gamma> f \<sigma>) i = f (i\<Gamma> \<sigma> i)"
  by transfer simp

lemma i\<tau>_map_i\<Gamma>[simp]: "i\<tau> (map_i\<Gamma> f \<sigma>) i = i\<tau> \<sigma> i"
  by transfer simp

lemma i\<iota>_map_i\<Gamma>[simp]: "i\<iota> (map_i\<Gamma> f \<sigma>) i = i\<iota> \<sigma> i"
  by transfer simp

definition islice :: "'a set list \<Rightarrow> 'a itrace \<Rightarrow> 'a itrace list" where
  "islice Xs \<sigma> = map (\<lambda>X. map_i\<Gamma> ((\<inter>) X) \<sigma>) Xs"


subsection \<open>Traces with watermarks\<close>

record 'a wtsdb = "'a itsdb" + wmark :: nat \<comment> \<open>watermarked, time-stamped database\<close>

text \<open>
  Watermarks must increase monotonically and they must be unbounded. We allow
  out-of-order indexes in watermarked traces, but each watermark sets a lower
  bound on all future indexes.
\<close>

definition wtracep :: "('a, 'b) wtsdb_scheme stream \<Rightarrow> bool" where
  "wtracep s \<longleftrightarrow> ssorted (smap wmark s) \<and> sincreasing (smap wmark s) \<and> sincreasing (smap ts s) \<and>
    (\<forall>i j. idx (s !! i) \<le> idx (s !! j) \<longrightarrow> ts (s !! i) \<le> ts (s !! j)) \<and>
    (\<forall>i. \<forall>j>i. wmark (s !! i) \<le> idx (s !! j))"

definition "dummy_raw_wtrace = smap (\<lambda>x. \<lparr>db={}, ts=x, idx=x, wmark=x\<rparr>) nats"

lemma wtracep_dummy: "wtracep dummy_raw_wtrace"
  by (auto simp: wtracep_def dummy_raw_wtrace_def stream.map_comp stream.map_ident
      cong: stream.map_cong)

typedef 'a wtrace = "{s :: 'a wtsdb stream. wtracep s}"
  by (auto intro!: exI[where x=dummy_raw_wtrace] wtracep_dummy)

setup_lifting type_definition_wtrace

subsubsection \<open>Projection functions\<close>

lift_definition w\<Gamma> :: "'a wtrace \<Rightarrow> nat \<Rightarrow> 'a set" is "\<lambda>s i. db (s !! i)" .
lift_definition w\<tau> :: "'a wtrace \<Rightarrow> nat \<Rightarrow> nat" is "\<lambda>s i. ts (s !! i)" .
lift_definition w\<iota> :: "'a wtrace \<Rightarrow> nat \<Rightarrow> nat" is "\<lambda>s i. idx (s !! i)" .
lift_definition w\<beta> :: "'a wtrace \<Rightarrow> nat \<Rightarrow> nat" is "\<lambda>s i. wmark (s !! i)" .

lemma w\<iota>_refines_w\<tau>: "w\<iota> \<sigma> i \<le> w\<iota> \<sigma> j \<Longrightarrow> w\<tau> \<sigma> i \<le> w\<tau> \<sigma> j"
  by transfer (simp add: wtracep_def)

lemma ex_w\<tau>_gr: "\<exists>j>i. x < w\<tau> \<sigma> j"
  by transfer (auto simp: wtracep_def dest!: sincreasing_grD)

lemma ex_w\<iota>_eq: "\<exists>x>i. \<exists>j. x = w\<iota> \<sigma> j"
proof (transfer fixing: i)
  fix s :: "'a wtsdb stream"
  assume "wtracep s"
  then obtain j where "i < wmark (s !! j)"
    by (auto simp: wtracep_def less_eq_Suc_le dest!: sincreasing_grD)
  also have "wmark (s !! j) \<le> idx (s !! Suc j)"
    using \<open>wtracep s\<close> by (simp add: wtracep_def del: snth.simps)
  finally have "i < idx (s !! Suc j)" .
  then show "\<exists>x>i. \<exists>j. x = idx (s !! j)"
    by blast
qed

lemma w\<iota>_bound: "\<exists>b. \<forall>j. i = w\<iota> \<sigma> j \<longrightarrow> j \<le> b"
proof (transfer fixing: i)
  fix s :: "'a wtsdb stream"
  assume "wtracep s"
  then obtain b where "i < wmark (s !! b)"
    by (auto simp: wtracep_def less_eq_Suc_le dest!: sincreasing_grD)
  then have "\<forall>j. i = idx (s !! j) \<longrightarrow> j \<le> b"
    using \<open>wtracep s\<close> le_less_linear
    by (fastforce simp: wtracep_def)
  then show "\<exists>b. \<forall>j. i = idx (s !! j) \<longrightarrow> j \<le> b" ..
qed

subsubsection \<open>Preserving the index order\<close>

lift_definition add_wmarks :: "'a itrace \<Rightarrow> 'a wtrace" is
  "smap (\<lambda>x. \<lparr>db=db x, ts=ts x, idx=idx x, wmark=idx x\<rparr>)"
proof  (simp add: wtracep_def stream.map_comp ssorted_iff_mono cong: stream.map_cong, clarify)
  fix s :: "'a itsdb stream"
  assume 1: "sincreasing (smap ts s)"
  assume "\<forall>i j. idx (s !! i) \<le> idx (s !! j) \<longrightarrow> ts (s !! i) \<le> ts (s !! j)"
  then have 2: "idx (s !! i) < idx (s !! j)" if "ts (s !! i) < ts (s !! j)" for i j
    using leD le_less_linear that by blast
  show "sincreasing (smap idx s)"
  proof (rule sincreasingI)
    fix x
    show "\<exists>i. x < smap idx s !! i"
    proof (induction x)
      case 0
      obtain j where "ts (s !! 0) < ts (s !! j)"
        using 1 by (auto simp: sincreasing_def)
      then show ?case
        using order.strict_trans1[OF le0 2] by (auto simp del: snth.simps)
    next
      case (Suc x)
      then obtain i where "x < idx (s !! i)" by auto
      moreover obtain j where "ts (s !! i) < ts (s !! j)"
        using 1 by (auto simp: sincreasing_def)
      ultimately show ?case
        using order.strict_trans1[OF Suc_leI 2] by auto
    qed
  qed
qed

subsubsection \<open>Relaxing the index order\<close>

locale relax_orderp =
  fixes \<sigma> :: "'a itrace" and \<sigma>' :: "'a wtrace"
  assumes
    sound_reordering: "\<forall>j. \<exists>i. w\<iota> \<sigma>' j = i\<iota> \<sigma> i \<and> w\<tau> \<sigma>' j = i\<tau> \<sigma> i \<and> w\<Gamma> \<sigma>' j = i\<Gamma> \<sigma> i" and
    complete_reordering: "\<forall>i. \<exists>j. w\<iota> \<sigma>' j = i\<iota> \<sigma> i \<and> w\<tau> \<sigma>' j = i\<tau> \<sigma> i \<and> w\<Gamma> \<sigma>' j = i\<Gamma> \<sigma> i"

definition relax_order :: "'a itrace \<Rightarrow> 'a wtrace set" where
  "relax_order \<sigma> = {\<sigma>'. relax_orderp \<sigma> \<sigma>'}"

lemma add_wmarks_relax_order: "add_wmarks \<sigma> \<in> relax_order \<sigma>"
  by (simp add: relax_order_def relax_orderp_def, transfer) auto

subsubsection \<open>Slicing\<close>

lift_definition map_w\<Gamma> :: "('a set \<Rightarrow> 'b set) \<Rightarrow> 'a wtrace \<Rightarrow> 'b wtrace" is
  "\<lambda>f. smap (\<lambda>x. \<lparr>db = f (db x), ts = ts x, idx = idx x, wmark = wmark x\<rparr>)"
  by (simp add: wtracep_def stream.map_comp cong: stream.map_cong)

lemma w\<Gamma>_map_w\<Gamma>[simp]: "w\<Gamma> (map_w\<Gamma> f \<sigma>) i = f (w\<Gamma> \<sigma> i)"
  by transfer simp

lemma w\<tau>_map_w\<Gamma>[simp]: "w\<tau> (map_w\<Gamma> f \<sigma>) i = w\<tau> \<sigma> i"
  by transfer simp

lemma w\<iota>_map_w\<Gamma>[simp]: "w\<iota> (map_w\<Gamma> f \<sigma>) i = w\<iota> \<sigma> i"
  by transfer simp

definition wslice :: "'a set list \<Rightarrow> 'a wtrace \<Rightarrow> 'a wtrace list" where
  "wslice Xs \<sigma> = map (\<lambda>X. map_w\<Gamma> ((\<inter>) X) \<sigma>) Xs"


subsection \<open>Input model\<close>

text \<open>
  The basic assumption is that the collection of multiple input traces can be
  explained in terms of a single trace (which may not be unique). We introduce
  nondeterministic functions that model the possible inputs that can be
  obtained from this trace.
\<close>

subsubsection \<open>Ordered partition\<close>

locale ipartitionp =
  fixes \<sigma> :: "'a itrace" and n :: nat and ps :: "'a itrace list"
  assumes
    n_greater_0: "n > 0" and
    length_ps_eq_n: "length ps = n" and
    sound_partition: "\<forall>k<n. \<forall>j. \<exists>i. i\<iota> (ps ! k) j = i\<iota> \<sigma> i \<and> i\<tau> (ps ! k) j = i\<tau> \<sigma> i \<and> i\<Gamma> (ps ! k) j \<subseteq> i\<Gamma> \<sigma> i" and
    complete_partition1: "\<forall>i. \<exists>k<n. \<exists>j. i\<iota> (ps ! k) j = i\<iota> \<sigma> i \<and> i\<tau> (ps ! k) j = i\<tau> \<sigma> i" and
    complete_partition2: "\<forall>i. \<forall>f \<in> i\<Gamma> \<sigma> i. \<exists>k<n. \<exists>j. i\<iota> (ps ! k) j = i\<iota> \<sigma> i \<and> i\<tau> (ps ! k) j = i\<tau> \<sigma> i \<and> f \<in> i\<Gamma> (ps ! k) j"

definition ipartition :: "nat \<Rightarrow> 'a itrace \<Rightarrow> 'a itrace list set" where
  "ipartition n \<sigma> = {ps. ipartitionp \<sigma> n ps}"

text \<open>We show that round-robin distribution is an instance of ordered partition.\<close>

primcorec sskip :: "nat \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
  "sskip n s = (case s of x ## s' \<Rightarrow> x ## sskip n (sdrop n s'))"

lemma smap_sskip: "smap f (sskip n s) = sskip n (smap f s)"
  by (coinduction arbitrary: s) (auto simp: stream.case_eq_if)

lemma snth_sskip: "sskip n s !! i = s !! (i * Suc n)"
  by (induction i arbitrary: s) (simp_all add: stream.case_eq_if sdrop_snth ac_simps)

lemma sincreasing_sskip:
  assumes "sincreasing s" and "ssorted s"
  shows "sincreasing (sskip n s)"
proof (rule sincreasingI)
  fix x
  obtain i where 1: "x < s !! i"
    using \<open>sincreasing s\<close> by (auto simp: sincreasing_def)
  have "i \<le> Suc (i div Suc n) * Suc n"
    using dividend_less_div_times[of "Suc n" i] by simp
  with 1 have "x < s !! (Suc (i div Suc n) * Suc n)"
    using \<open>ssorted s\<close> by (blast dest: ssorted_monoD intro: order.strict_trans2)
  then have "x < sskip n s !! Suc (i div Suc n)"
    unfolding snth_sskip .
  then show "\<exists>i. x < sskip n s !! i" ..
qed

lift_definition round_robin :: "nat \<Rightarrow> 'a itrace \<Rightarrow> 'a itrace list" is
  "\<lambda>n s. map (\<lambda>k. sskip (n-1) (sdrop k s)) [0..<n]"
  by (auto simp add: list.pred_set smap_sskip snth_sskip sdrop_snth sdrop_smap[symmetric]
      ssorted_iff_mono simp del: sdrop_smap intro!: sincreasing_sskip sincreasing_sdrop)

lemma length_round_robin[simp]: "length (round_robin n \<sigma>) = n"
  by transfer simp

lemma ix_round_robin:
  assumes "k < n"
  shows "i\<Gamma> (round_robin n \<sigma> ! k) j = i\<Gamma> \<sigma> (k + j * n)" and
    "i\<tau> (round_robin n \<sigma> ! k) j = i\<tau> \<sigma> (k + j * n)" and
    "i\<iota> (round_robin n \<sigma> ! k) j = i\<iota> \<sigma> (k + j * n)"
  using assms by (simp_all add: i\<Gamma>.rep_eq i\<tau>.rep_eq i\<iota>.rep_eq round_robin.rep_eq
      nth_map[where f=Rep_itrace, symmetric] snth_sskip sdrop_snth)

lemma round_robin_ipartition:
  assumes "n > 0"
  shows "round_robin n \<sigma> \<in> ipartition n \<sigma>"
proof -
  have "\<exists>k<n. \<exists>j. i\<iota> (round_robin n \<sigma> ! k) j = i\<iota> \<sigma> i \<and> i\<tau> (round_robin n \<sigma> ! k) j = i\<tau> \<sigma> i" for i
  proof -
    let ?k = "i mod n"
    let ?j = "i div n"
    have "?k < n \<and> i\<iota> (round_robin n \<sigma> ! ?k) ?j = i\<iota> \<sigma> i \<and> i\<tau> (round_robin n \<sigma> ! ?k) ?j = i\<tau> \<sigma> i"
      using \<open>n > 0\<close> by (simp add: ix_round_robin)
    then show ?thesis by blast
  qed
  moreover have "\<exists>k<n. \<exists>j. i\<iota> (round_robin n \<sigma> ! k) j = i\<iota> \<sigma> i \<and> i\<tau> (round_robin n \<sigma> ! k) j = i\<tau> \<sigma> i \<and>
      f \<in> i\<Gamma> (round_robin n \<sigma> ! k) j" if "f \<in> i\<Gamma> \<sigma> i" for i f
  proof -
    let ?k = "i mod n"
    let ?j = "i div n"
    have "?k < n \<and> i\<iota> (round_robin n \<sigma> ! ?k) ?j = i\<iota> \<sigma> i \<and> i\<tau> (round_robin n \<sigma> ! ?k) ?j = i\<tau> \<sigma> i \<and>
      f \<in> i\<Gamma> (round_robin n \<sigma> ! ?k) ?j"
      using \<open>n > 0\<close> that by (simp add: ix_round_robin)
    then show ?thesis by blast
  qed
  ultimately have "ipartitionp \<sigma> n (round_robin n \<sigma>)"
    using \<open>n > 0\<close> by (auto simp: ipartitionp_def ix_round_robin)
  then show ?thesis by (simp add: ipartition_def)
qed

subsubsection \<open>Out-of-order partition\<close>

locale wpartitionp =
  fixes \<sigma> :: "'a itrace" and n :: nat and ps :: "'a wtrace list"
  assumes
    n_greater_0: "n > 0" and
    length_ps_eq_n: "length ps = n" and
    sound_partition: "\<forall>k<n. \<forall>j. \<exists>i. w\<iota> (ps ! k) j = i\<iota> \<sigma> i \<and> w\<tau> (ps ! k) j = i\<tau> \<sigma> i \<and> w\<Gamma> (ps ! k) j \<subseteq> i\<Gamma> \<sigma> i" and
    complete_partition1: "\<forall>i. \<exists>k<n. \<exists>j. w\<iota> (ps ! k) j = i\<iota> \<sigma> i \<and> w\<tau> (ps ! k) j = i\<tau> \<sigma> i" and
    complete_partition2: "\<forall>i. \<forall>f \<in> i\<Gamma> \<sigma> i. \<exists>k<n. \<exists>j. w\<iota> (ps ! k) j = i\<iota> \<sigma> i \<and> w\<tau> (ps ! k) j = i\<tau> \<sigma> i \<and> f \<in> w\<Gamma> (ps ! k) j"

definition wpartition :: "nat \<Rightarrow> 'a itrace \<Rightarrow> 'a wtrace list set" where
  "wpartition n \<sigma> = {ps. wpartitionp \<sigma> n ps}"

text \<open>
  Totality of \<^term>\<open>wpartition n\<close> for \<^term>\<open>n > 0\<close> can be derived from
  the following alternative characterization in terms of \<^term>\<open>ipartition\<close>
  and \<^term>\<open>relax_order\<close>.
\<close>

subsubsection \<open>Separation of partitioning and relaxed order\<close>

text \<open>
  We define an auxiliary function that sorts the elements of a watermarked
  trace by their index.
\<close>

definition wsort_init :: "'a wtrace \<Rightarrow> nat" where
  "wsort_init \<sigma> = (LEAST j. (LEAST i. \<exists>j. i = w\<iota> \<sigma> j) = w\<iota> \<sigma> j)"

definition wsort_step :: "'a wtrace \<Rightarrow> nat \<Rightarrow> nat" where
  "wsort_step \<sigma> j = (if \<exists>j'>j. w\<iota> \<sigma> j = w\<iota> \<sigma> j'
    then LEAST j'. j' > j \<and> w\<iota> \<sigma> j = w\<iota> \<sigma> j'
    else LEAST j'. (LEAST i. i > w\<iota> \<sigma> j \<and> (\<exists>j. i = w\<iota> \<sigma> j)) = w\<iota> \<sigma> j')"

definition wsort_indexes :: "'a wtrace \<Rightarrow> nat stream" where
  "wsort_indexes \<sigma> = siterate (wsort_step \<sigma>) (wsort_init \<sigma>)"

lemma snth_wsort_indexes_Suc: "wsort_indexes \<sigma> !! Suc n = (let j = wsort_indexes \<sigma> !! n in
  if \<exists>j'>j. w\<iota> \<sigma> j = w\<iota> \<sigma> j'
    then LEAST j'. j' > j \<and> w\<iota> \<sigma> j = w\<iota> \<sigma> j'
    else LEAST j'. (LEAST i. i > w\<iota> \<sigma> j \<and> (\<exists>j. i = w\<iota> \<sigma> j)) = w\<iota> \<sigma> j')"
  by (auto simp add: wsort_indexes_def snth.simps[symmetric] wsort_step_def Let_def
      simp del: siterate.sel snth.simps)

lemma ex_snth_wsort_indexes: "\<exists>i. wsort_indexes \<sigma> !! i = j"
proof (induction "w\<iota> \<sigma> j" arbitrary: j rule: less_induct)
  case less
  then show ?case
  proof (induction j rule: less_induct)
    case (less j)
    note outer_IH = less.prems
    show ?case proof (cases "\<exists>j'<j. w\<iota> \<sigma> j' = w\<iota> \<sigma> j")
      case True
      define j' where "j' = (GREATEST j'. j' < j \<and> w\<iota> \<sigma> j' = w\<iota> \<sigma> j)"
      have 1: "j' < j" "w\<iota> \<sigma> j' = w\<iota> \<sigma> j"
        using GreatestI_ex_nat[of "\<lambda>j'. j' < j \<and> w\<iota> \<sigma> j' = w\<iota> \<sigma> j", of j, OF True]
        by (auto simp: j'_def)
      then obtain i where "wsort_indexes \<sigma> !! i = j'"
        using less.IH[of j'] outer_IH by auto
      then have "wsort_indexes \<sigma> !! Suc i = j"
        unfolding snth_wsort_indexes_Suc
        using 1 apply auto
        apply (rule Least_equality)
         apply simp
        apply (metis (mono_tags, lifting) Greatest_le_nat j'_def leD le_less_linear less_or_eq_imp_le)
        done
      then show ?thesis ..
    next
      case least_j: False
      show ?thesis proof (cases "\<exists>i<w\<iota> \<sigma> j. \<exists>j'. i = w\<iota> \<sigma> j'")
        case True
        define i' where "i' = (GREATEST i'. i' < w\<iota> \<sigma> j \<and> (\<exists>j'. i' = w\<iota> \<sigma> j'))"
        have 1: "i' < w\<iota> \<sigma> j" "\<exists>j'. i' = w\<iota> \<sigma> j'"
          using GreatestI_ex_nat[where P="\<lambda>i'. i' < w\<iota> \<sigma> j \<and> (\<exists>j'. i' = w\<iota> \<sigma> j')", of "w\<iota> \<sigma> j", OF True]
          by (auto simp: i'_def)
        define j' where "j' = (GREATEST j'. i' = w\<iota> \<sigma> j')"
        have 2: "\<not> (\<exists>j''>j'. i' = w\<iota> \<sigma> j'')"
          apply (clarsimp simp: j'_def not_le[symmetric])
          apply (erule notE)
          apply (insert w\<iota>_bound[of i' \<sigma>])
          apply (blast intro: Greatest_le_nat)
          done
        have "i' = w\<iota> \<sigma> j'"
          unfolding j'_def
          using GreatestI_ex_nat[of "\<lambda>j'. i' = w\<iota> \<sigma> j'", OF 1(2)] w\<iota>_bound[of i']
          by blast
        with 1 have "w\<iota> \<sigma> j' < w\<iota> \<sigma> j"
          by simp
        then obtain k where 3: "wsort_indexes \<sigma> !! k = j'"
          using outer_IH by auto
        have "wsort_indexes \<sigma> !! Suc k = j"
          unfolding snth_wsort_indexes_Suc 3
          using 2 \<open>i' = w\<iota> \<sigma> j'\<close> apply auto
          apply (rule Least_equality)
          subgoal 4
            apply (rule Least_equality)
            using \<open>w\<iota> \<sigma> j' < w\<iota> \<sigma> j\<close> apply blast
            apply (metis (mono_tags, lifting) Greatest_le_nat i'_def leD le_less_linear nat_le_linear)
            done
          using 4 le_less_linear least_j by auto
        then show ?thesis ..
      next
        case False
        with least_j have "wsort_indexes \<sigma> !! 0 = j"
          apply (simp add: wsort_indexes_def wsort_init_def)
          apply (rule Least_equality)
          subgoal 1
            apply (rule Least_equality)
             apply blast
            using le_less_linear apply blast
            done
          using 1 le_less_linear least_j by auto
        then show ?thesis ..
      qed
    qed
  qed
qed

lift_definition wnth :: "'a wtrace \<Rightarrow> nat \<Rightarrow> 'a wtsdb" is snth .

lemma idx_wnth_w\<iota>[simp]: "idx (wnth \<sigma> i) = w\<iota> \<sigma> i"
  by transfer simp

lemma ts_wnth_w\<tau>[simp]: "ts (wnth \<sigma> i) = w\<tau> \<sigma> i"
  by transfer simp

lemma db_wnth_w\<Gamma>[simp]: "db (wnth \<sigma> i) = w\<Gamma> \<sigma> i"
  by transfer simp

lift_definition wsort :: "'a wtrace \<Rightarrow> 'a itrace" is
  "\<lambda>\<sigma>. smap (\<lambda>i. itsdb.truncate (wnth \<sigma> i)) (wsort_indexes \<sigma>)"
  apply (simp add: stream.map_comp itsdb.defs w\<iota>_refines_w\<tau> cong: stream.map_cong)
  apply (intro conjI)
  subgoal for \<sigma>
    apply (clarsimp simp: ssorted_iff_mono)
    subgoal for i j
      apply (induction j)
       apply (simp add: wsort_indexes_def)
      subgoal for j
        apply (cases "Suc j = i")
         apply simp
        apply simp
        apply (erule order_trans)
        apply (simp add: snth.simps[symmetric] del: siterate.sel snth.simps add: wsort_indexes_def)
        apply (subst wsort_step_def)
        apply auto
         apply (rule LeastI2_ex)
          apply blast
         apply simp
        apply (rule LeastI2_ex[where P="\<lambda>i'. w\<iota> \<sigma> ((wsort_step \<sigma> ^^ j) (wsort_init \<sigma>)) < i' \<and> (\<exists>j. i' = w\<iota> \<sigma> j)"])
        apply (rule ex_w\<iota>_eq)
        apply (metis (mono_tags, lifting) LeastI order.order_iff_strict)
        done
      done
    done
  subgoal for \<sigma>
    apply (rule sincreasingI)
    apply simp
    subgoal for x
      apply (rule ex_w\<tau>_gr[of 0 x \<sigma>, THEN exE])
      subgoal for j
        apply (rule ex_snth_wsort_indexes[of \<sigma> j, THEN exE])
        apply auto
        done
      done
    done
  done

lemma ix_wsort1: "\<exists>i. i\<iota> (wsort \<sigma>) j = w\<iota> \<sigma> i \<and> i\<tau> (wsort \<sigma>) j = w\<tau> \<sigma> i \<and>
  i\<Gamma> (wsort \<sigma>) j = w\<Gamma> \<sigma> i"
  by (auto simp: i\<iota>.rep_eq i\<tau>.rep_eq i\<Gamma>.rep_eq wsort.rep_eq itsdb.defs)

lemma ix_wsort2: "\<exists>j. i\<iota> (wsort \<sigma>) j = w\<iota> \<sigma> i \<and> i\<tau> (wsort \<sigma>) j = w\<tau> \<sigma> i \<and>
  i\<Gamma> (wsort \<sigma>) j = w\<Gamma> \<sigma> i"
  using ex_snth_wsort_indexes[of \<sigma> i]
  by (auto simp: i\<iota>.rep_eq i\<tau>.rep_eq i\<Gamma>.rep_eq wsort.rep_eq itsdb.defs)

lemma wpartition_split: "wpartition n = ipartition n !\<then> mapM_set relax_order"
proof (rule antisym)
  show "wpartition n \<le> ipartition n !\<then> mapM_set relax_order"
    apply (auto simp: le_fun_def strong_kleisli_def ipartition_def)
    subgoal for a b c
      apply (drule equals0D[OF sym])
      apply (erule notE)
      apply (rule map_in_mapM_setI)
      apply (rule add_wmarks_relax_order)
      done
    subgoal for \<sigma> ps
      apply (erule thin_rl)
      apply (rule exI[where x="map wsort ps"])
      apply (auto simp: wpartition_def wpartitionp_def ipartitionp_def
          in_mapM_set_iff relax_order_def relax_orderp_def cong: conj_cong)
      subgoal for k j by (rule exE[OF ix_wsort1[of "ps ! k" j]]) simp
      subgoal for i
        apply (drule spec[where x=i and P="\<lambda>i. \<exists>k<length ps. _ i k"])
        apply clarify
        subgoal for k j
          apply (rule exI)
          apply (rule conjI)
           apply assumption
          apply (rule exE[OF ix_wsort2[of "ps ! k" j]])
          apply auto
          done
        done
      subgoal for i f
        apply (drule spec[where x=i and P="\<lambda>i. \<forall>f\<in>i\<Gamma> \<sigma> i. _ i f"])
        apply (drule (1) bspec)
        apply clarify
        subgoal for k j
          apply (rule exI)
          apply (rule conjI)
           apply assumption
          apply (rule exE[OF ix_wsort2[of "ps ! k" j]])
          apply auto
          done
        done
      subgoal
        apply (simp add: list.rel_map)
        apply (rule list.rel_refl_strong)
        apply (metis ix_wsort1 ix_wsort2)
        done
      done
    done
  have "ipartition n \<circ>\<then> mapM_set relax_order \<le> wpartition n"
    by (auto simp: le_fun_def kleisli_set_def ipartition_def ipartitionp_def
        in_mapM_set_iff relax_order_def relax_orderp_def list_all2_conv_all_nth
        wpartition_def wpartitionp_def) metis+
  then show "ipartition n !\<then> mapM_set relax_order \<le> wpartition n"
    using order.trans strong_kleisli_le_kleisli_set by blast
qed

subsubsection \<open>Complete definition of the input model\<close>

text \<open>
  Here, we collect all conditions imposed by the input model and express them
  in terms of plain streams.
\<close>

locale wpartitionp_alt =
  fixes \<sigma> :: "'a itrace" and n :: nat and ps :: "'a wtsdb stream list"
  assumes
    n_greater_0: "n > 0" and
    length_ps_eq_n: "length ps = n" and
    sorted_wmark: "\<forall>k<n. ssorted (smap wmark (ps ! k))" and
    increasing_wmark: "\<forall>k<n. sincreasing (smap wmark (ps ! k))" and
    increasing_ts: "\<forall>k<n. sincreasing (smap ts (ps ! k))" and
    wmark_le_idx: "\<forall>k<n. \<forall>i. \<forall>j>i. wmark (ps ! k !! i) \<le> idx (ps ! k !! j)" and
    sound_partition: "\<forall>k<n. \<forall>j. \<exists>i. idx (ps ! k !! j) = i\<iota> \<sigma> i \<and> ts (ps ! k !! j) = i\<tau> \<sigma> i \<and> db (ps ! k !! j) \<subseteq> i\<Gamma> \<sigma> i" and
    complete_partition1: "\<forall>i. \<exists>k<n. \<exists>j. idx (ps ! k !! j) = i\<iota> \<sigma> i \<and> ts (ps ! k !! j) = i\<tau> \<sigma> i" and
    complete_partition2: "\<forall>i. \<forall>f \<in> i\<Gamma> \<sigma> i. \<exists>k<n. \<exists>j. idx (ps ! k !! j) = i\<iota> \<sigma> i \<and> ts (ps ! k !! j) = i\<tau> \<sigma> i \<and> f \<in> db (ps ! k !! j)"
begin

lift_definition ps' :: "'a wtrace list" is ps
  apply (auto simp: list.pred_set wtracep_def in_set_conv_nth length_ps_eq_n
      sorted_wmark increasing_wmark increasing_ts wmark_le_idx)
  subgoal for j j' k
    apply (frule sound_partition[rule_format, of _ j])
    apply (frule sound_partition[rule_format, of _ j'])
    using i\<iota>_refines_i\<tau> by auto
  done

lemma length_ps'[simp]: "length ps' = n"
  by (transfer fixing: n) (rule length_ps_eq_n)

lemma Rep_wtrace_nth_ps': "k < n \<Longrightarrow> Rep_wtrace (ps' ! k) = ps ! k"
  by (metis length_ps' nth_map ps'.rep_eq)

lemma wx_nth_ps':
  "k < n \<Longrightarrow> w\<iota> (ps' ! k) i = idx (ps ! k !! i)"
  "k < n \<Longrightarrow> w\<tau> (ps' ! k) i = ts (ps ! k !! i)"
  "k < n \<Longrightarrow> w\<Gamma> (ps' ! k) i = db (ps ! k !! i)"
  by (simp_all add: w\<iota>.rep_eq w\<tau>.rep_eq w\<Gamma>.rep_eq Rep_wtrace_nth_ps')

lemma wpartitionp_ps': "wpartitionp \<sigma> n ps'"
  using n_greater_0 sound_partition complete_partition1 complete_partition2
  by unfold_locales (simp_all add: wx_nth_ps' cong: ex_cong1 conj_cong)

end


subsection \<open>Multiplexed traces with watermarks\<close>

subsubsection \<open>"Infinitely often" predicate for streams\<close>

definition infinitely :: "('a \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> bool" where
  "infinitely P s \<longleftrightarrow> (\<forall>i. \<exists>j\<ge>i. P (s !! j))"

lemma infinitely_stl: "infinitely P (stl s) \<longleftrightarrow> infinitely P s"
  unfolding infinitely_def
proof
  assume L: "\<forall>i. \<exists>j\<ge>i. P (stl s !! j)"
  show "\<forall>i. \<exists>j\<ge>i. P (s !! j)" proof
    fix i
    from L obtain j where "j \<ge> i \<and> P (stl s !! j)" by blast
    then have "Suc j \<ge> i \<and> P (s !! Suc j)" by simp
    then show "\<exists>j\<ge>i. P (s !! j)" ..
  qed
next
  assume R: "\<forall>i. \<exists>j\<ge>i. P (s !! j)"
  show "\<forall>i. \<exists>j\<ge>i. P (stl s !! j)" proof
    fix i
    from R obtain j where "j \<ge> Suc i \<and> P (s !! j)" by blast
    then obtain j' where "j' \<ge> i \<and> P (s !! Suc j')"
      by (blast dest: Suc_le_D)
    then show "\<exists>j\<ge>i. P (stl s !! j)" by auto
  qed
qed

lemma infinitely_sset_stl: "infinitely P s \<Longrightarrow> \<exists>x \<in> sset (stl s). P x"
  by (fastforce simp: infinitely_def dest!: Suc_le_D)

subsubsection \<open>Multiplexed traces\<close>

record 'a mwtsdb = "'a wtsdb" + origin :: nat

text \<open>
  A multiplexed trace is an interleaving of finitely many traces (with
  watermarks). The different subtraces are identified by their \<^term>\<open>origin\<close>.
  Each subtrace must satisfy the ordering conditions associated with
  watermarked traces.
\<close>

lemma sdrop_while_id_conv: "stream_all P s \<Longrightarrow> sdrop_while (Not \<circ> P) s = s"
  by (subst sdrop_while_sdrop_LEAST) simp_all

lemma sfilter_id_conv: "stream_all P s \<Longrightarrow> sfilter P s = s"
  by (coinduction arbitrary: s) (auto simp: sdrop_while_id_conv stl_sset)

typedef 'a mwtrace = "{s :: 'a mwtsdb stream. finite (origin ` sset s) \<and>
  (\<forall>k \<in> origin ` sset s. infinitely (\<lambda>x. origin x = k) s \<and> wtracep (sfilter (\<lambda>x. origin x = k) s))}"
  apply (rule exI[where x="smap (\<lambda>x. \<lparr>db={}, ts=x, idx=x, wmark=x, origin=0\<rparr>) nats"])
  apply (auto simp: infinitely_def stream.set_map image_image)
  apply (subst sfilter_id_conv)
   apply (simp add: stream.set_map)
  apply (auto simp: wtracep_def stream.map_comp stream.map_ident cong: stream.map_cong)
  done

setup_lifting type_definition_mwtrace

subsubsection \<open>Projection functions\<close>

lemma wtracep_stlI: "wtracep s \<Longrightarrow> wtracep (stl s)"
  apply (auto simp add: wtracep_def smap_simps[symmetric] simp del: smap_simps
      elim: ssorted.cases sincreasing_stl)
   apply (metis snth.simps(2))
  by (metis Suc_mono snth.simps(2))

lemma sfilter_stl_cases:
  obtains "P (shd s)" "sfilter P (stl s) = stl (sfilter P s)" |
    "\<not> P (shd s)" "sfilter P (stl s) = sfilter P s"
  by (cases s) (auto simp: sfilter_Stream)

lift_definition mwnth :: "'a mwtrace \<Rightarrow> nat \<Rightarrow> 'a mwtsdb" is snth .
lift_definition mwhd :: "'a mwtrace \<Rightarrow> 'a mwtsdb" is shd .
lift_definition mwtl :: "'a mwtrace \<Rightarrow> 'a mwtrace" is stl
  apply (auto 0 3 simp: infinitely_stl intro: stl_sset elim: finite_subset[rotated])
  subgoal for s x
    by (rule sfilter_stl_cases[of "\<lambda>y. origin y = origin x" s])
      (auto simp del: sfilter.simps intro!: wtracep_stlI stl_sset)
  done

lemma mwnth_zero: "mwnth \<sigma> 0 = mwhd \<sigma>"
  by transfer simp

lemma mwnth_Suc: "mwnth \<sigma> (Suc i) = mwnth (mwtl \<sigma>) i"
  by transfer simp

lift_definition mworigins :: "'a mwtrace \<Rightarrow> nat set" is "\<lambda>s. origin ` sset s" .

lemma mworigins_not_empty[simp]: "mworigins \<sigma> \<noteq> {}"
  by transfer (simp add: sset_range)

lemma finite_mworigins[simp]: "finite (mworigins \<sigma>)"
  by transfer simp

lemma origin_mwhd: "origin (mwhd \<sigma>) \<in> mworigins \<sigma>"
  by transfer (simp add: shd_sset)

lemma origin_mwnth: "origin (mwnth \<sigma> i) \<in> mworigins \<sigma>"
  by transfer simp

lemma mworigins_mwtl: "mworigins (mwtl \<sigma>) = mworigins \<sigma>"
  apply transfer
  apply (auto intro: stl_sset)
  apply (drule (1) bspec)
  apply clarify
  apply (drule infinitely_sset_stl)
  by (metis imageI)

lift_definition dummy_mwtrace :: "'a mwtrace" is "smap (\<lambda>x. \<lparr>db={}, ts=x, idx=x, wmark=x, origin=0\<rparr>) nats"
  by (auto simp: stream.set_map image_image infinitely_def sfilter_id_conv
      wtracep_def stream.map_comp stream.map_ident cong: stream.map_cong)

lemma mworigins_dummy: "mworigins dummy_mwtrace = {0}"
  by transfer (simp add: stream.set_map image_image)

lemma wtracep_smap_truncate: "wtracep (smap wtsdb.truncate s) \<longleftrightarrow> wtracep s"
  by (simp add: wtracep_def stream.map_comp wtsdb.truncate_def cong: stream.map_cong)

lift_definition mwproject :: "nat \<Rightarrow> 'a mwtrace \<Rightarrow> 'a wtrace" is
  "\<lambda>k s. if k \<in> origin ` sset s then smap wtsdb.truncate (sfilter (\<lambda>x. origin x = k) s)
    else dummy_raw_wtrace"
  by (auto simp: wtracep_smap_truncate wtracep_dummy)

subsubsection \<open>Merge\<close>

text \<open>
  A multiplexed trace is obtained by nondeterministically merging a list of
  watermarked traces.
\<close>

definition merge :: "'a wtrace list \<Rightarrow> 'a mwtrace set" where
  "merge \<sigma>s = {\<sigma>. mworigins \<sigma> = {..<length \<sigma>s} \<and> (\<forall>k < length \<sigma>s. mwproject k \<sigma> = \<sigma>s ! k)}"

text \<open>Below, we show that round-robin merging is one possible realization.\<close>

definition merge_rr' :: "nat \<Rightarrow> 'a wtsdb stream list \<Rightarrow> 'a mwtsdb stream" where
  "merge_rr' i0 xs = smap (\<lambda>i. wtsdb.extend (xs ! (i mod length xs) !! (i div length xs))
    \<lparr>origin = i mod length xs\<rparr>) (fromN i0)"

lemma origin_sset_merge_rr': "xs \<noteq> [] \<Longrightarrow> origin ` sset (merge_rr' 0 xs) = {..<length xs}"
  by (auto simp: sset_range image_image merge_rr'_def wtsdb.defs
      intro: image_eqI[of x _ x for x])

lemma mod_nat_cancel_left: "0 < (b::nat) \<Longrightarrow> (b - a mod b + a) mod b = 0"
  by (metis le_add_diff_inverse2 mod_add_right_eq mod_le_divisor mod_self)

lemma infinitely_origin_merge_rr': "k < length xs \<Longrightarrow>
  infinitely (\<lambda>x. origin x = k) (merge_rr' i0 xs)"
  apply (clarsimp simp: infinitely_def merge_rr'_def wtsdb.defs)
  subgoal for i
    apply (rule exI[where x="k + (length xs - (i mod length xs)) + i + (length xs - (i0 mod length xs))"])
    apply auto
    apply (subst (3) add.assoc)
    apply (subst mod_add_eq[symmetric])
    apply (subst mod_nat_cancel_left)
     apply auto
    apply (subst add.assoc)
    apply (subst mod_add_eq[symmetric])
    apply (subst mod_nat_cancel_left)
     apply auto
    done
  done

lemma infinitely_exD: "infinitely P s \<Longrightarrow> \<exists>i. P (s !! i)"
  by (auto simp: infinitely_def)

lemma all_eq_snth_eqI: "(\<And>n. a !! n = b !! n) \<Longrightarrow> a = b"
  by (coinduction arbitrary: a b) (simp del: snth.simps add: snth.simps[symmetric])

lemma mod_nat_cancel_left_add:
  assumes "0 < (c::nat)"
  shows "(c - b mod c + (a + b) mod c) mod c = a mod c"
proof -
  have "(c - b mod c + (a + b) mod c) mod c = (c - b mod c + a mod c + b mod c) mod c"
    by (metis (no_types, opaque_lifting) add.commute group_cancel.add2 mod_add_left_eq)
  also have "\<dots> = ((c - b mod c + b mod c) mod c + a mod c) mod c"
    by (metis (no_types, opaque_lifting) add.commute group_cancel.add2 mod_add_eq mod_add_right_eq)
  finally show ?thesis
    using assms by (simp add: mod_nat_cancel_left)
qed

lemma sdrop_while_merge_rr': "k < length xs \<Longrightarrow>
  sdrop_while (Not \<circ> (\<lambda>x. origin x = k)) (merge_rr' i0 xs) =
  merge_rr' (i0 + (length xs - i0 mod length xs + k) mod length xs) xs"
  apply (subgoal_tac "(LEAST n. origin (merge_rr' i0 xs !! n) = k) =
    (length xs - i0 mod length xs + k) mod length xs")
  subgoal
    apply (simp add: sdrop_while_sdrop_LEAST[OF infinitely_exD, OF infinitely_origin_merge_rr'])
    apply (rule all_eq_snth_eqI)
    apply (simp add: sdrop_snth merge_rr'_def ac_simps)
    done
  subgoal
    apply (auto simp: merge_rr'_def wtsdb.defs mod_add_left_eq intro!: Least_equality)
     apply (subst add.assoc)
     apply (subst add.commute)
     apply (subst add.assoc)
     apply (subst (2) add.commute)
     apply (subst mod_add_eq[symmetric])
     apply (subst mod_nat_cancel_left)
      apply auto[]
     apply simp
    apply (subst mod_nat_cancel_left_add)
     apply auto
    done
  done

lemma sfilter_origin_merge_rr': "k < length xs \<Longrightarrow>
  sfilter (\<lambda>x. origin x = k) (merge_rr' i xs) =
  sdrop ((i + (length xs - i mod length xs + k) mod length xs) div length xs)
    (smap (\<lambda>x. wtsdb.extend x \<lparr>origin=k\<rparr>) (xs ! k))"
  apply (coinduction arbitrary: i)
  subgoal for i
    apply safe
     apply (simp add: sdrop_while_merge_rr')
     apply (simp add: merge_rr'_def)
     apply (subgoal_tac "(i + (length xs - i mod length xs + k) mod length xs) mod length xs = k")
      apply simp
    subgoal 1
      apply (subst mod_add_right_eq)
      apply (subst add.assoc[symmetric])
      apply (subst add.commute)
      apply (subst mod_add_eq[symmetric])
      apply (subst mod_nat_cancel_left)
       apply auto
      done
    apply (rule exI[where x="Suc (i + (length xs - i mod length xs + k) mod length xs)"])
    apply (rule conjI)
     apply (simp add: sdrop_while_merge_rr')
     apply (simp add: merge_rr'_def)
    apply (frule 1)
    apply (simp del: sdrop.simps add: sdrop.simps[symmetric])
    apply (rule arg_cong[where f="\<lambda>x. smap _ (sdrop x _)"])
    apply (subst (3) Suc_eq_plus1)
    apply (subst (4) mod_add_eq[symmetric])
    apply clarsimp
    apply (subgoal_tac "(length xs - Suc k mod length xs + k) mod length xs = length xs - 1")
     apply simp
     apply (metis (no_types, lifting) Suc_pred add.commute add_gr_0
        div_add_self1 length_0_conv length_greater_0_conv not_less_zero plus_1_eq_Suc)
    by (smt Suc_lessI add.right_neutral add_Suc_right diff_Suc_1 diff_less
        le_add_diff_inverse2 length_greater_0_conv list.size(3) mod_add_self1 mod_if mod_le_divisor
        not_less_zero zero_less_one)
  done

lemma wtsdb_truncate_extend: "wtsdb.truncate (wtsdb.extend x y) = x"
  by (simp add: wtsdb.defs)

lift_definition merge_rr :: "'a wtrace list \<Rightarrow> 'a mwtrace" is
 "\<lambda>xs. if xs = [] then smap (\<lambda>x. \<lparr>db={}, ts=x, idx=x, wmark=x, origin=0\<rparr>) nats
    else merge_rr' 0 xs"
  apply (auto simp: stream.set_map image_image sfilter_id_conv origin_sset_merge_rr')
     apply (auto simp add: infinitely_def)[]
    apply (subst wtracep_smap_truncate[symmetric])
    apply (simp add: stream.map_comp wtsdb.defs wtracep_dummy[unfolded dummy_raw_wtrace_def]
      cong: stream.map_cong)
   apply (rule infinitely_origin_merge_rr')
  using origin_sset_merge_rr' apply auto[]
  subgoal for xs x
    apply (subgoal_tac "origin x < length xs")
     apply (simp add: sfilter_origin_merge_rr'[where i=0, simplified])
     apply (subst wtracep_smap_truncate[symmetric])
     apply (simp add: stream.map_comp wtsdb_truncate_extend stream.map_ident
        list.pred_set cong: stream.map_cong)
    using origin_sset_merge_rr' apply auto[]
    done
  done

lemma merge_rr_merge: "xs \<noteq> [] \<Longrightarrow> merge_rr xs \<in> merge xs"
  apply (simp add: merge_def)
  apply (rule conjI)
  subgoal by transfer (simp add: origin_sset_merge_rr')
  subgoal
    apply clarify
    apply (rule Rep_wtrace_inject[THEN iffD1])
    apply (auto simp: mwproject.rep_eq merge_rr.rep_eq
        sfilter_origin_merge_rr'[where i=0, simplified] stream.map_comp
        wtsdb_truncate_extend stream.map_ident cong: stream.map_cong)[]
    using origin_sset_merge_rr'[of "map Rep_wtrace xs"] apply auto
    done
  done


subsection \<open>Reorder algorithm\<close>

subsubsection \<open>Additional facts about associative lists\<close>

lift_definition keyset :: "('a, 'b) alist \<Rightarrow> 'a set" is "\<lambda>xs. fst ` set xs" .

lemma keyset_empty[simp]: "keyset DAList.empty = {}"
  by transfer simp

lemma keyset_update[simp]: "keyset (DAList.update k v al) = insert k (keyset al)"
  by transfer (simp add: dom_update)

lemma keyset_filter_impl: "keyset (DAList.filter P al) = fst ` (set (filter P (DAList.impl_of al)))"
  by transfer simp

lemma DAList_filter_id_conv: "DAList.filter P al = al \<longleftrightarrow> (\<forall>x \<in> set (DAList.impl_of al). P x)"
  by (transfer fixing: P) (rule filter_id_conv)

lemma alist_set_impl: "alist.set al = snd ` set (DAList.impl_of al)"
  by transfer force

lemma finite_keyset[simp]: "finite (keyset al)"
  by (simp add: keyset.rep_eq)

lemma finite_alist_set[simp]: "finite (alist.set al)"
  by (simp add: alist_set_impl)

lemma alist_set_empty_conv: "alist.set al = {} \<longleftrightarrow> keyset al = {}"
  by (simp add: alist_set_impl keyset.rep_eq)

lemma keyset_empty_eq_conv: "keyset al = {} \<longleftrightarrow> al = DAList.empty"
  by transfer simp

lemma in_alist_set_conv: "x \<in> alist.set al \<longleftrightarrow> (\<exists>k \<in> keyset al. DAList.lookup al k = Some x)"
  by (transfer fixing: x) force

lemma lookup_in_alist_set: "k \<in> keyset al \<Longrightarrow> the (DAList.lookup al k) \<in> alist.set al"
  by (transfer fixing: k) force

lemma keyset_map_default: "keyset (DAList.map_default k v f al) = insert k (keyset al)"
  by (transfer fixing: k v f) (simp add: dom_map_default)

lemma map_default_neq_empty[simp]: "DAList.map_default k v f al \<noteq> DAList.empty"
  apply (transfer fixing: k v f)
  subgoal for xs
    by (induction xs) simp_all
  done


subsubsection \<open>Algorithm\<close>

record 'a raw_reorder_state =
  wmarks :: "(nat, nat) alist"
  buffer :: "(nat, ('a set \<times> nat)) alist"

definition reorder_update :: "'a mwtsdb \<Rightarrow> 'a raw_reorder_state \<Rightarrow> 'a raw_reorder_state" where
  "reorder_update x st = \<lparr>wmarks = DAList.update (origin x) (wmark x) (wmarks st),
    buffer = DAList.map_default (idx x) (db x, ts x) (\<lambda>(d, t). (d \<union> db x, t)) (buffer st)\<rparr>"

definition reorder_flush :: "'a raw_reorder_state \<Rightarrow> ('a set \<times> nat) list \<times> 'a raw_reorder_state" where
  "reorder_flush st = (let w = Min (alist.set (wmarks st)) in
    (map snd (sort_key fst (filter (\<lambda>x. fst x < w) (DAList.impl_of (buffer st)))),
      st\<lparr>buffer := DAList.filter (\<lambda>x. fst x \<ge> w) (buffer st)\<rparr>))"

text \<open>Basic state invariants, needed for the productivity proof:\<close>

typedef 'a reorder_state = "{(st :: 'a raw_reorder_state, \<sigma> :: 'a mwtrace).
  keyset (wmarks st) = mworigins \<sigma> \<and> (\<forall>i \<in> keyset (buffer st). Min (alist.set (wmarks st)) \<le> i) \<and>
  (\<forall>k \<in> mworigins \<sigma>. \<forall>i. the (DAList.lookup (wmarks st) k) \<le> w\<iota> (mwproject k \<sigma>) i) \<and>
  (\<forall>k \<in> mworigins \<sigma>. \<forall>i. the (DAList.lookup (wmarks st) k) \<le> w\<beta> (mwproject k \<sigma>) i)}"
  by (rule exI[where x="(\<lparr>wmarks=DAList.update 0 0 DAList.empty, buffer=DAList.empty\<rparr>, dummy_mwtrace)"])
    (simp add: mworigins_dummy)

setup_lifting type_definition_reorder_state

lemma mwproject_mwtl: "origin (mwhd \<sigma>) \<noteq> k \<Longrightarrow> mwproject k (mwtl \<sigma>) = mwproject k \<sigma>"
  apply transfer
  apply (auto dest: stl_sset)
  subgoal for \<sigma> x x' by (cases \<sigma>) (simp add: sfilter_Stream)
  by (metis image_eqI insert_iff stream.collapse stream.simps(8))

lemma wmark_mwhd_le_w\<iota>: "wmark (mwhd \<sigma>) \<le> w\<iota> (mwproject (origin (mwhd \<sigma>)) (mwtl \<sigma>)) i"
  apply (transfer fixing: i)
  apply auto
  subgoal for \<sigma> x
    apply (auto simp: wtracep_def wtsdb.defs dest!: stl_sset)
    apply (drule (1) bspec)
    apply clarify
    apply (drule spec[of "\<lambda>i. \<forall>j. i < j \<longrightarrow> _ i j" 0])
    apply (drule spec[of "\<lambda>j. 0 < j \<longrightarrow> _ j" "Suc i"])
    apply (simp add: sdrop_while.simps)
    done
  subgoal using image_iff infinitely_sset_stl shd_sset by fastforce
  done

lemma wmark_mwhd_le_w\<beta>: "wmark (mwhd \<sigma>) \<le> w\<beta> (mwproject (origin (mwhd \<sigma>)) (mwtl \<sigma>)) i"
  apply (transfer fixing: i)
  apply auto
  subgoal for \<sigma> x
    apply (auto simp: wtracep_def wtsdb.defs dest!: stl_sset)
    apply (drule (1) bspec)
    apply clarify
    apply (drule ssorted_monoD[where i=0 and j="Suc i"])
     apply (simp_all add: sdrop_while.simps)
    done
  subgoal using image_iff infinitely_sset_stl shd_sset by fastforce
  done

lift_definition reorder_step :: "'a reorder_state \<Rightarrow> ('a set \<times> nat) list \<times> 'a reorder_state" is
  "\<lambda>(st, \<sigma>). let (xs, st') = reorder_flush (reorder_update (mwhd \<sigma>) st) in (xs, (st', mwtl \<sigma>))"
  by (auto simp: split_beta Let_def reorder_update_def reorder_flush_def origin_mwhd mworigins_mwtl
      lookup_update mwproject_mwtl wmark_mwhd_le_w\<iota> wmark_mwhd_le_w\<beta> keyset_filter_impl)

text \<open>
  \<^term>\<open>reorder_step\<close> consumes one element of the input trace, producing
  zero or more ordered output elements. In order to show that always eventually
  one more element is produced, we define a variant on the algorithm's state.
\<close>

definition next_to_emit :: "'a raw_reorder_state \<Rightarrow> 'a mwtrace \<Rightarrow> nat" where
  "next_to_emit st \<sigma> = (if buffer st = DAList.empty then idx (mwhd \<sigma>) else Min (keyset (buffer st)))"

definition next_to_release :: "'a raw_reorder_state \<Rightarrow> 'a mwtrace \<Rightarrow> nat \<Rightarrow> nat" where
  "next_to_release st \<sigma> k = (if next_to_emit st \<sigma> < the (DAList.lookup (wmarks st) k) then 0
    else Suc (LEAST i. origin (mwnth \<sigma> i) = k \<and> next_to_emit st \<sigma> < wmark (mwnth \<sigma> i)))"

lift_definition reorder_variant :: "'a reorder_state \<Rightarrow> nat" is
  "\<lambda>(st, \<sigma>). Max (next_to_release st \<sigma> ` keyset (wmarks st))" .

lemma sort_key_empty_conv: "sort_key f xs = [] \<longleftrightarrow> xs = []"
  by (induction xs) simp_all

lemma w\<beta>_mwproject_mwhd: "w\<beta> (mwproject (origin (mwhd \<sigma>)) \<sigma>) 0 = wmark (mwhd \<sigma>)"
  apply transfer
  subgoal for \<sigma>
    by (cases \<sigma>) (auto simp: wtsdb.defs sfilter_Stream)
  done

lemma Least_less_Least: "\<exists>x::'a::wellorder. Q x \<Longrightarrow> (\<And>x. Q x \<Longrightarrow> \<exists>y. P y \<and> y < x) \<Longrightarrow> Least P < Least Q"
  by (metis LeastI2 less_le_trans not_le_imp_less not_less_Least)

lemma infinitely_sdrop: "infinitely P s \<Longrightarrow> infinitely P (sdrop n s)"
  apply (auto simp add: infinitely_def sdrop_snth)
  subgoal for i
    apply (drule spec[of _ "i + n"])
    apply clarify
    subgoal for j by (rule exI[of _ "j - n"]) simp
    done
  done

lemma ex_snth_sfilter: "infinitely P s \<Longrightarrow> \<exists>j. sfilter P s !! i = s !! j \<and> P (s !! j)"
  apply (induction i arbitrary: s)
   apply (simp add: sdrop_while_sdrop_LEAST infinitely_exD)
  using LeastI_ex infinitely_exD apply force
  apply (simp add: sdrop_while_sdrop_LEAST infinitely_exD)
  subgoal for i s
    apply (drule meta_spec)
    apply (drule meta_mp)
     apply (rule infinitely_sdrop[where n="LEAST n. P (s !! n)"])
     apply (erule infinitely_stl[THEN iffD2])
    apply (clarsimp simp add: sdrop_snth snth.simps(2)[symmetric] simp del: snth.simps(2))
    apply (rule exI)
    apply (rule conjI[OF refl])
    apply assumption
    done
  done

lemma ex_snth_sfilter2: "P (s !! i) \<Longrightarrow> \<exists>j. sfilter P s !! j = s !! i"
  apply (induction i arbitrary: s)
  subgoal for s
    by (metis Least_eq_0 sdrop_simps(1) sdrop_while_sdrop_LEAST sfilter.sel(1) snth.simps(1))
  subgoal for i s
    by (cases s) (metis sfilter_Stream snth_Stream)
  done

lemma ex_wmark_greater: "k \<in> mworigins \<sigma> \<Longrightarrow> \<exists>i. origin (mwnth \<sigma> i) = k \<and> w < wmark (mwnth \<sigma> i)"
  apply (transfer fixing: k w)
  apply (clarsimp simp: wtracep_def)
  subgoal for \<sigma> x
    apply (drule (1) bspec)
    apply clarify
    apply (drule sincreasing_grD[of "smap wmark _" 0 w])
    apply clarify
    subgoal for i
      apply (frule ex_snth_sfilter[where i=i])
      apply auto
      done
    done
  done

lemma reorder_termination: "fst (reorder_step st) = [] \<Longrightarrow>
  reorder_variant (snd (reorder_step st)) < reorder_variant st"
  apply transfer
  apply (clarsimp split: prod.splits)
  subgoal premises assms for st \<sigma> st'
  proof -
    note step_eq = \<open>_ = ([], st')\<close>
    note w\<beta>_inv = \<open>\<forall>k\<in>mworigins \<sigma>. \<forall>i. the (DAList.lookup (wmarks st) k) \<le> w\<beta> (mwproject k \<sigma>) i\<close>
    let ?x = "mwhd \<sigma>"
    let ?st1 = "reorder_update ?x st"

    have [simp]: "keyset (wmarks st) \<noteq> {}"
      using \<open>keyset (wmarks st) = mworigins \<sigma>\<close> by simp

    have 1: "wmarks (reorder_update ?x st) = DAList.update (origin ?x) (wmark ?x) (wmarks st)"
      by (simp add: reorder_update_def)
    then have wmarks_st': "wmarks st' = \<dots>"
      using step_eq by (auto simp: reorder_flush_def Let_def)
    then have "keyset (wmarks st') = mworigins \<sigma>"
      using \<open>keyset (wmarks st) = mworigins \<sigma>\<close>
      by (simp add: insert_absorb origin_mwhd)

    from 1 have Min_wmarks_st1: "Min (alist.set (wmarks ?st1)) \<ge> Min (alist.set (wmarks st))"
      apply (clarsimp simp: alist_set_empty_conv Min_le_iff in_alist_set_conv)
      subgoal for w
        apply (cases "w = wmark (mwhd \<sigma>)")
        subgoal
          apply simp
          apply (rule bexI[where x="the (DAList.lookup (wmarks st) (origin (mwhd \<sigma>)))"])
           apply (rule w\<beta>_inv[THEN bspec[of _ _ "origin (mwhd \<sigma>)"], OF origin_mwhd, THEN spec[of _ 0],
                simplified w\<beta>_mwproject_mwhd])
          apply (auto simp: \<open>keyset (wmarks st) = mworigins \<sigma>\<close> origin_mwhd intro!: lookup_in_alist_set)
          done
        apply (auto 0 3 simp: lookup_update in_alist_set_conv split: if_splits intro: bexI[where x=w])
        done
      done

    have buffer_st'_eq: "buffer st' = buffer (reorder_update ?x st)"
      using step_eq
      by (auto simp: reorder_flush_def Let_def sort_key_empty_conv filter_empty_conv
          DAList_filter_id_conv not_less)
    have buffer_st1_eq: "buffer (reorder_update ?x st) =
      DAList.map_default (idx ?x) (db ?x, ts ?x) (\<lambda>(d, t). (d \<union> db ?x, t)) (buffer st)"
      by (simp add: reorder_update_def)

    have "\<forall>i \<in> keyset (buffer ?st1). Min (alist.set (wmarks ?st1)) \<le> i"
      using step_eq
      by (simp add: reorder_flush_def Let_def sort_key_empty_conv filter_empty_conv
          keyset.rep_eq not_less)
    then have "\<forall>i \<in> keyset (buffer ?st1). Min (alist.set (wmarks st)) \<le> i"
      using Min_wmarks_st1 by auto
    then have "Min (alist.set (wmarks st)) \<le> next_to_emit st \<sigma>"
      by (auto simp: buffer_st1_eq keyset_map_default next_to_emit_def keyset_empty_eq_conv)
    then obtain k1 where
      "k1 \<in> mworigins \<sigma>" and
      "the (DAList.lookup (wmarks st) k1) \<le> next_to_emit st \<sigma>"
      by (auto simp: Min_le_iff alist_set_empty_conv in_alist_set_conv
          \<open>keyset (wmarks st) = mworigins \<sigma>\<close>)
    then have next_k1: "next_to_release st \<sigma> k1 > 0"
      by (simp add: next_to_release_def)

    have next_st': "next_to_emit st' (mwtl \<sigma>) \<le> next_to_emit st \<sigma>"
      by (auto simp: next_to_emit_def buffer_st'_eq buffer_st1_eq keyset_map_default
          keyset_empty_eq_conv intro!: Min_antimono)

    have "\<exists>k' \<in> mworigins \<sigma>. next_to_release st' (mwtl \<sigma>) k < next_to_release st \<sigma> k'"
      if "k \<in> mworigins \<sigma>" for k
    proof (cases "next_to_release st \<sigma> k")
      case 0
      note next_st'
      also have "next_to_emit st \<sigma> < the (DAList.lookup (wmarks st) k)"
        using 0 by (simp add: next_to_release_def split: if_splits)
      also have "\<dots> \<le> the (DAList.lookup (wmarks st') k)"
        by (clarsimp simp: wmarks_st' lookup_update
            intro!: w\<beta>_inv[THEN bspec[of _ _ "origin (mwhd \<sigma>)"], OF origin_mwhd, THEN spec[of _ 0],
              simplified w\<beta>_mwproject_mwhd])
      finally have "next_to_release st' (mwtl \<sigma>) k = 0"
        by (simp add: next_to_release_def)
      then show ?thesis using next_k1 \<open>k1 \<in> mworigins \<sigma>\<close> by auto
    next
      let ?least = "\<lambda>st \<sigma>. (LEAST i. origin (mwnth \<sigma> i) = k \<and> next_to_emit st \<sigma> < wmark (mwnth \<sigma> i))"
      case (Suc i)
      then have i_eq: "i = ?least st \<sigma>"
        by (simp add: next_to_release_def split: if_splits)
      have 1: "?least st' (mwtl \<sigma>) < ?least st \<sigma>"
        if *: "next_to_emit st' (mwtl \<sigma>) \<ge> the (DAList.lookup (wmarks st') k)"
      proof (rule Least_less_Least[OF ex_wmark_greater, OF \<open>k \<in> mworigins \<sigma>\<close>], safe)
        fix j
        assume "next_to_emit st \<sigma> < wmark (mwnth \<sigma> j)" "k = origin (mwnth \<sigma> j)"
        then have **: "next_to_emit st' (mwtl \<sigma>) < wmark (mwnth \<sigma> j)"
          using next_st' by (elim order.strict_trans1)
        have "j \<noteq> 0" proof
          assume "j = 0"
          then have "the (DAList.lookup (wmarks st') k) = wmark (mwnth \<sigma> 0)"
            using \<open>k = origin (mwnth \<sigma> j)\<close>
            by (simp add: wmarks_st' lookup_update mwnth_zero)
          with * ** show False by (simp add: \<open>j = 0\<close>)
        qed
        then obtain i where "j = Suc i" by (cases j) simp_all
        then show "\<exists>i. (origin (mwnth (mwtl \<sigma>) i) = origin (mwnth \<sigma> j) \<and>
              next_to_emit st' (mwtl \<sigma>) < wmark (mwnth (mwtl \<sigma>) i)) \<and> i < j"
          using ** by (auto simp: mwnth_Suc)
      qed
      show ?thesis
        apply (rule bexI[OF _ \<open>k \<in> mworigins \<sigma>\<close>])
        apply (simp add: Suc)
        apply (simp add: next_to_release_def i_eq not_less 1)
        done
    qed
    then show ?thesis
      unfolding \<open>keyset (wmarks st') = mworigins \<sigma>\<close>
      by simp (auto simp: Max_gr_iff \<open>keyset (wmarks st') = mworigins \<sigma>\<close>)
  qed
  done

friend_of_corec shift :: "'a list \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
  "shift xs s = (case xs of [] \<Rightarrow> shd s | x # _ \<Rightarrow> x) ## (case xs of [] \<Rightarrow> stl s | _ # ys \<Rightarrow> shift ys s)"
  subgoal by (simp split: list.split)
  subgoal by transfer_prover
  done

corecursive reorder :: "'a reorder_state \<Rightarrow> ('a set \<times> nat) stream" where
  "reorder st = (let (xs, st') = reorder_step st in
    case xs of
      [] \<Rightarrow> reorder st'
    | x # xs' \<Rightarrow> x ## xs' @- reorder st')"
  by (relation "measure reorder_variant") (simp_all add: reorder_termination)

lift_definition init_alist :: "'a::linorder set \<Rightarrow> 'b \<Rightarrow> ('a, 'b) alist" is
  "\<lambda>K v. if finite K then map (\<lambda>k. (k, v)) (sorted_list_of_set K) else []"
  by (simp cong: map_cong)

lemma keyset_init_alist: "finite K \<Longrightarrow> keyset (init_alist K v) = K"
  by transfer (simp add: image_image)

lemma lookup_init_alist: "finite K \<Longrightarrow> k \<in> K \<Longrightarrow> DAList.lookup (init_alist K v) k = Some v"
  by transfer (simp add: map_of_map_restrict)

lift_definition init_reorder_state :: "'a mwtrace \<Rightarrow> 'a reorder_state" is
  "\<lambda>\<sigma>. (\<lparr>wmarks = init_alist (mworigins \<sigma>) 0, buffer = DAList.empty\<rparr>, \<sigma>)"
  by (simp add: keyset_init_alist lookup_init_alist)

definition reorder' :: "'a mwtrace \<Rightarrow> 'a trace" where
  "reorder' \<sigma> = Abs_trace (reorder (init_reorder_state \<sigma>))"

subsubsection \<open>Specification\<close>

definition least_idx :: "'a mwtrace \<Rightarrow> nat \<Rightarrow> nat" where
  "least_idx \<sigma> i0 = (LEAST i. i0 \<le> i \<and> (\<exists>j. i = idx (mwnth \<sigma> j)))"

definition idx_stream :: "'a mwtrace \<Rightarrow> nat stream" where
  "idx_stream \<sigma> = siterate (least_idx \<sigma> \<circ> Suc) (least_idx \<sigma> 0)"

definition collapse_idx :: "'a mwtrace \<Rightarrow> nat \<Rightarrow> 'a set" where
  "collapse_idx \<sigma> i = (\<Union>{d. \<exists>j. i = idx (mwnth \<sigma> j) \<and> d = db (mwnth \<sigma> j)})"

definition ts_of_idx :: "'a mwtrace \<Rightarrow> nat \<Rightarrow> nat" where
  "ts_of_idx \<sigma> i = ts (mwnth \<sigma> (LEAST j. i = idx (mwnth \<sigma> j)))"

definition reorder_alt :: "'a mwtrace \<Rightarrow> ('a set \<times> nat) stream" where
  "reorder_alt \<sigma> = smap (\<lambda>i. (collapse_idx \<sigma> i, ts_of_idx \<sigma> i)) (idx_stream \<sigma>)"

subsubsection \<open>Equivalence of specification and implementation\<close>

definition collapse_reorder_state :: "'a raw_reorder_state \<Rightarrow> 'a mwtrace \<Rightarrow> (nat \<times> 'a set \<times> nat) set" where
  "collapse_reorder_state st \<sigma>' =
    {(i, (d \<union> (collapse_idx \<sigma>' i), t)) | i d t. (i, (d, t)) \<in> set (DAList.impl_of (buffer st))} \<union>
    {(i, (collapse_idx \<sigma>' i, ts_of_idx \<sigma>' i)) | i. i \<notin> keyset (buffer st) \<and> (\<exists>j. i = idx (mwnth \<sigma>' j))}"

lift_definition reorder_state_rel :: "'a mwtrace \<Rightarrow> 'a reorder_state \<Rightarrow> nat \<Rightarrow> bool" is
  "\<lambda>\<sigma> (st, \<sigma>') n. collapse_reorder_state st \<sigma>' = {(i, collapse_idx \<sigma> i, ts_of_idx \<sigma> i) | i. i \<in> sset (sdrop n (idx_stream \<sigma>))}" .

lemma ex_idx_eq: "\<exists>x\<ge>y. \<exists>j. x = idx (mwnth \<sigma> j)"
  apply (transfer fixing: y)
  subgoal for \<sigma>
    apply (clarsimp simp: wtracep_def)
    apply (drule bspec[where x="shd \<sigma>"])
     apply (simp add: shd_sset)
    apply clarify
    apply (drule sincreasing_grD[of "smap wmark _" 0 y])
    apply (thin_tac "\<forall>i j. _ i j")
    apply clarsimp
    subgoal for i
      apply (drule spec)+
      apply (drule mp)
       apply (rule lessI[of i])
      apply (drule (1) order.strict_trans2)
      by (metis order.order_iff_strict ex_snth_sfilter)
    done
  done

lemma sset_idx_stream: "sset (idx_stream \<sigma>) = {i. \<exists>j. i = idx (mwnth \<sigma> j)}"
  apply (auto simp: idx_stream_def sset_siterate)
  subgoal for n
    apply (induction n)
     apply (simp add: least_idx_def)
     apply (rule LeastI)
     apply blast
    apply clarsimp
    subgoal for n j
    apply (thin_tac _)
    apply (simp add: least_idx_def)
      apply (insert LeastI_ex[where P="\<lambda>i. Suc (idx (mwnth \<sigma> j)) \<le> i \<and> (\<exists>j. i = idx (mwnth \<sigma> j))"])
      apply (drule meta_mp)
      apply (rule ex_idx_eq)
      apply simp
      done
    done
  subgoal for j proof -
    have "\<And>i'. i' \<le> i \<Longrightarrow> \<exists>j. i' = idx (mwnth \<sigma> j) \<Longrightarrow>
      \<exists>n. i' = ((least_idx \<sigma> \<circ> Suc) ^^ n) (least_idx \<sigma> 0)" for i
      apply (induction i)
       apply (auto simp: least_idx_def intro!: exI[where x=0])[]
      subgoal for i i'
        apply (cases "i' = Suc i"; simp)
        apply (cases "\<exists>i''. i'' \<le> i \<and> (\<exists>j. i'' = idx (mwnth \<sigma> j))")
        subgoal
          apply clarsimp
          apply (drule meta_spec[where x="GREATEST i''. i'' \<le> i \<and> (\<exists>j. i'' = idx (mwnth \<sigma> j))"])
          apply (drule meta_mp)
           apply (metis (mono_tags, lifting) GreatestI_ex_nat)
          apply (drule meta_mp)
           apply (smt GreatestI_ex_nat)
          apply clarify
          subgoal for j j' n
            apply (rule exI[where x="Suc n"])
            apply (clarsimp simp: least_idx_def)
            apply (rule Least_equality[symmetric])
             apply (smt GreatestI_nat not_less_eq_eq)
            by (metis (mono_tags, lifting) Greatest_le_nat not_less_eq_eq)
          done
        subgoal
          apply (rule exI[where x=0])
          apply (auto simp: least_idx_def)
          by (smt Least_equality less_Suc_eq_le not_less)
        done
      done
    then show ?thesis by auto
  qed
  done

lemma reorder_state_rel_init: "reorder_state_rel \<sigma> (init_reorder_state \<sigma>) 0"
  by transfer (simp add: collapse_reorder_state_def DAList.empty.rep_eq sset_idx_stream)

lemma set_map_default: "set (DAList.impl_of (DAList.map_default k v f al)) =
  {case DAList.lookup al k of None \<Rightarrow> (k, v) | Some v' \<Rightarrow> (k, f v')} \<union>
  {x. x \<in> set (DAList.impl_of al) \<and> fst x \<noteq> k}"
  apply (transfer fixing: k v f)
  subgoal for xs by (induction xs) (auto simp: image_iff)
  done

lemma lookup_None_set_conv: "DAList.lookup al k = None \<longleftrightarrow> k \<notin> fst ` set (DAList.impl_of al)"
  by (transfer fixing: k) (simp add: map_of_eq_None_iff)

lemma lookup_Some_set_conv: "DAList.lookup al k = Some v \<longleftrightarrow> (k, v) \<in> set (DAList.impl_of al)"
  by (transfer fixing: k v) simp

lemma collapse_idx_mwtl: "collapse_idx \<sigma> i =
  (if i = idx (mwhd \<sigma>) then db (mwhd \<sigma>) \<union> collapse_idx (mwtl \<sigma>) i else collapse_idx (mwtl \<sigma>) i)"
  apply (auto simp: collapse_idx_def)
      apply (metis mwnth_Suc mwnth_zero not0_implies_Suc)
     apply (metis mwnth_zero)
    apply (metis mwnth_Suc)
   apply (metis mwnth_Suc mwnth_zero not0_implies_Suc)
  apply (metis mwnth_Suc)
  done

lemma ts_of_idx_mwtl: "(\<exists>j. i = idx (mwnth \<sigma> j)) \<Longrightarrow> ts_of_idx \<sigma> i =
  (if i = idx (mwhd \<sigma>) then ts (mwhd \<sigma>) else ts_of_idx (mwtl \<sigma>) i)"
  apply (auto simp: ts_of_idx_def mwnth_zero)
  apply (subgoal_tac "(LEAST j. i = idx (mwnth \<sigma> j)) = Suc (LEAST j. i = idx (mwnth (mwtl \<sigma>) j))")
   apply (simp add: mwnth_Suc)
  apply simp
  apply (subst mwnth_Suc[symmetric])
  apply (rule Least_Suc[OF refl])
  apply (simp add: mwnth_zero)
  done

lemma alist_eq_key_imp_eq: "(k, v) \<in> set (DAList.impl_of al) \<Longrightarrow> (k, v') \<in> set (DAList.impl_of al) \<Longrightarrow> v = v'"
  by (transfer fixing: k v v') (simp add: eq_key_imp_eq_value)

coinductive sdistinct :: "'a stream \<Rightarrow> bool" where
  "shd s \<notin> sset (stl s) \<Longrightarrow> sdistinct (stl s) \<Longrightarrow> sdistinct s"

lemma sdistinct_sdrop[simp]: "sdistinct s \<Longrightarrow> sdistinct (sdrop n s)"
  by (induction n arbitrary: s) (auto elim: sdistinct.cases)

lemma sdistinct_siterate_increasing: "(\<And>x::_::preorder. x < f x) \<Longrightarrow> sdistinct (siterate f x)"
  apply (coinduction arbitrary: x)
  apply (auto simp: sset_siterate)
  subgoal for x n
    apply (subgoal_tac "\<And>x. x < (f ^^ n) (f x)")
     apply (metis less_irrefl)
    apply (thin_tac "_ = _")
    apply (induction n)
     apply (auto intro: less_trans)
    done
  done

lemma sdistinct_idx_stream: "sdistinct (idx_stream \<sigma>)"
  apply (clarsimp simp: idx_stream_def least_idx_def Suc_le_eq intro!: sdistinct_siterate_increasing)
  apply (rule LeastI2_ex)
  using Suc_le_lessD ex_idx_eq apply blast
  apply simp
  done

lemma ssorted_idx_stream: "ssorted (idx_stream \<sigma>)"
  apply (auto simp: idx_stream_def least_idx_def intro!: ssorted_siterate)
  apply (rule LeastI2_ex)
  apply (rule ex_idx_eq)
  apply simp
  done

lemma w\<iota>_mwproject: "\<exists>j'. w\<iota> (mwproject (origin (mwnth \<sigma> j)) \<sigma>) j' = idx (mwnth \<sigma> j)"
  apply (transfer fixing: j)
  subgoal for s
    apply (insert ex_snth_sfilter2[where P="\<lambda>x. origin x = origin (s !! j)", OF refl])
    apply (auto simp: wtsdb.defs)
    apply metis
    done
  done

lemma sset_ssorted_ge_shd: "x \<in> sset s \<Longrightarrow> ssorted (smap f s) \<Longrightarrow> f (shd s) \<le> f x"
  by (induction x s rule: sset_induct) (auto elim: ssorted.cases)

lemma set_sorted_distinct_gr: "y \<in> set xs \<Longrightarrow> sorted (map f (x # xs)) \<Longrightarrow>
  distinct (map f (x # xs)) \<Longrightarrow> f x < f y"
  by (metis image_eqI image_set list.simps(9) strict_sorted_iff strict_sorted_simps(2))

lemma sorted_distinct_prefix_lemma: "ssorted (smap f s) \<Longrightarrow> sdistinct (smap f s) \<Longrightarrow>
  sorted (map f xs) \<Longrightarrow> distinct (map f xs) \<Longrightarrow>
  set xs \<subseteq> sset s \<Longrightarrow> (\<And>x. x \<in> sset s \<Longrightarrow> x \<in> set xs \<or> (\<forall>y\<in>set xs. f x > f y)) \<Longrightarrow>
  stake (length xs) s = xs \<and> sset (sdrop (length xs) s) = {x \<in> sset s. \<forall>y\<in>set xs. f x > f y}"
proof (induction xs arbitrary: s)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  then have "x \<in> sset s" by simp
  have "shd s = x"
    apply (rule disjE[OF Cons.prems(6)[OF shd_sset]])
     apply simp
     apply (erule (1) disjE)
     apply (subgoal_tac "f x < f (shd s)")
    using sset_ssorted_ge_shd[OF \<open>x \<in> sset s\<close> Cons.prems(1)] apply auto[]
     apply (erule set_sorted_distinct_gr[where f=f, OF _ Cons.prems(3,4)])
    apply clarsimp
    using sset_ssorted_ge_shd[OF \<open>x \<in> sset s\<close> Cons.prems(1)] apply auto[]
    done
  moreover have "stake (length xs) (stl s) = xs \<and> sset (sdrop (length xs) (stl s)) =
      {x \<in> sset (stl s). \<forall>y\<in>set xs. f y < f x}"
    apply (rule Cons.IH)
    using Cons.prems(1) apply (auto elim: ssorted.cases)[]
    using Cons.prems(2) apply (auto elim: sdistinct.cases)[]
    using Cons.prems(3) apply simp
    using Cons.prems(4) apply simp
     apply (rule subsetI)
    subgoal for y
      apply (subgoal_tac "y \<noteq> shd s")
       apply (metis Cons.prems(5) insert_iff set_subset_Cons stream.collapse stream.simps(8) subsetD)
      using Cons.prems(4) \<open>shd s = x\<close> apply auto
      done
    subgoal for y
      apply (subgoal_tac "y \<noteq> shd s")
      using Cons.prems(6) \<open>shd s = x\<close> stl_sset apply fastforce
      apply (rule sdistinct.cases[OF Cons.prems(2)])
      by (metis (no_types, lifting) Cons.prems(1) leD less_le shd_sset sset_ssorted_ge_shd
          ssorted.cases stream.map_sel(1) stream.map_sel(2))
    done
  ultimately show ?case
    apply (auto simp: stl_sset)
     apply (metis (mono_tags, lifting) Cons.prems(1) Cons.prems(2) leD le_neq_trans
        sdistinct.cases shd_sset sset_ssorted_ge_shd ssorted.cases stl_sset stream.map_sel(1) stream.map_sel(2))
    by (metis neq_iff stream.sel(1) stream.sel(2) stream.set_cases)
qed

lemma map_insort_key_same: "map f (insort_key f x xs) = insort (f x) (map f xs)"
  by (induction xs) simp_all

lemma map_sort_key_same: "map f (sort_key f xs) = sort (map f xs)"
  by (induction xs) (simp_all add: map_insort_key_same)

lemma sset_sdrop_subset: "sset (sdrop n s) \<subseteq> sset s"
  by (metis Un_subset_iff order_refl sset_shift stake_sdrop)

lemma reorder_state_rel_step: "reorder_state_rel \<sigma> st n \<Longrightarrow>
  reorder_step st = (xs, st') \<Longrightarrow> xs = stake (length xs) (sdrop n (reorder_alt \<sigma>)) \<and>
    reorder_state_rel \<sigma> st' (n + length xs)"
  apply (transfer fixing: \<sigma> n xs)
  apply (clarsimp split: prod.splits)
  subgoal premises assms for st \<sigma>' st2
  proof (rule conjI)
    note w\<iota>_inv2 = \<open>\<forall>k\<in>mworigins (mwtl \<sigma>'). \<forall>i. the (DAList.lookup (wmarks st2) k) \<le> w\<iota> (mwproject k (mwtl \<sigma>')) i\<close>
    note old_state = \<open>collapse_reorder_state st \<sigma>' =
      {(i, collapse_idx \<sigma> i, ts_of_idx \<sigma> i) |i. i \<in> sset (sdrop n (idx_stream \<sigma>))}\<close>
    note step_eq = \<open>_ = (xs, st2)\<close>
    let ?x = "mwhd \<sigma>'"

    define st1 where "st1 = reorder_update ?x st"
    have wmarks_st1: "wmarks st1 = wmarks st2"
      using step_eq by (auto simp: st1_def reorder_flush_def Let_def)
    have buffer_st1: "buffer st1 =
      DAList.map_default (idx ?x) (db ?x, ts ?x) (\<lambda>(d, t). (d \<union> db ?x, t)) (buffer st)"
      by (simp add: st1_def reorder_update_def)

    have 1: "{(i, collapse_idx \<sigma>' i, ts_of_idx \<sigma>' i) |i. i \<notin> keyset (buffer st) \<and> (\<exists>j. i = idx (mwnth \<sigma>' j))} =
      {(i, collapse_idx \<sigma>' i, if i = idx (mwhd \<sigma>') then ts (mwhd \<sigma>') else ts_of_idx (mwtl \<sigma>') i) |
        i. i \<notin> keyset (buffer st) \<and> (\<exists>j. i = idx (mwnth \<sigma>' j))}"
      by (simp only: ts_of_idx_mwtl cong: rev_conj_cong)
    have 2: "(\<exists>j. i = idx (mwnth \<sigma>' j)) \<longleftrightarrow> i = idx (mwhd \<sigma>') \<or> (\<exists>j. i = idx (mwnth (mwtl \<sigma>') j))" for i
      apply safe
        apply (metis nat.exhaust mwnth_zero mwnth_Suc)
       apply (metis mwnth_zero)
      apply (metis mwnth_Suc)
      done
    have "collapse_reorder_state st1 (mwtl \<sigma>') = collapse_reorder_state st \<sigma>'"
      unfolding collapse_reorder_state_def buffer_st1 set_map_default keyset_map_default 1
      apply (subst (3 4) collapse_idx_mwtl)
      unfolding 2 keyset.rep_eq
      by (auto simp: lookup_None_set_conv lookup_Some_set_conv fst_eq_Domain Domain.simps
          split: option.split dest: alist_eq_key_imp_eq)
    note st1 = trans[OF this old_state]

    define w where "w = Min (alist.set (wmarks st1))"
    have less_w_less_idx: "i < w \<Longrightarrow> i < idx (mwnth (mwtl \<sigma>') j)" for i j
      apply (insert w\<iota>_inv2[rule_format, of "origin (mwnth (mwtl \<sigma>') j)", OF origin_mwnth])
      apply (unfold w_def wmarks_st1)
      apply (subst (asm) Min_gr_iff)
        apply simp
       apply (simp add: alist_set_empty_conv \<open>keyset (wmarks st2) = mworigins (mwtl \<sigma>')\<close>)
      apply (drule bspec[where x="the (DAList.lookup (wmarks st2) (origin (mwnth (mwtl \<sigma>') j)))"])
       apply (simp add: \<open>keyset (wmarks st2) = mworigins (mwtl \<sigma>')\<close> lookup_in_alist_set origin_mwnth)
      apply (erule order.strict_trans2)
      apply (rule exE[OF w\<iota>_mwproject[of "mwtl \<sigma>'" j]])
      subgoal for i
        apply (drule meta_spec[where x=i])
        apply simp
        done
      done
    then have less_w_complete: "i < w \<Longrightarrow> collapse_idx (mwtl \<sigma>') i = {}" for i
      by (auto simp: collapse_idx_def)
    have xs_eq: "xs = map snd (sort_key fst (filter (\<lambda>x. fst x < w) (DAList.impl_of (buffer st1))))"
      using step_eq by (simp add: reorder_flush_def st1_def w_def Let_def)

    let ?\<sigma>_ext = "sdrop n (smap (\<lambda>i. (i, (collapse_idx \<sigma> i, ts_of_idx \<sigma> i))) (idx_stream \<sigma>))"
    let ?xs_ext = "sort_key fst (filter (\<lambda>x. fst x < w) (DAList.impl_of (buffer st1)))"
    have 3: "stake (length xs) ?\<sigma>_ext = ?xs_ext \<and>
      sset (sdrop (length xs) ?\<sigma>_ext) = {x \<in> sset ?\<sigma>_ext. \<forall>y\<in>set ?xs_ext. fst x > fst y}"
      apply (simp only: xs_eq length_map)
      apply (rule sorted_distinct_prefix_lemma[where f=fst])
           apply (simp add: stream.map_comp stream.map_ident ssorted_sdrop ssorted_idx_stream cong: stream.map_cong)
          apply (simp add: stream.map_comp stream.map_ident sdistinct_idx_stream cong: stream.map_cong)
         apply simp
        apply (simp add: map_sort_key_same distinct_map_filter)
       apply clarsimp
      subgoal for i d t
        apply (subgoal_tac "(i, d, t) \<in> {(i, collapse_idx \<sigma> i, ts_of_idx \<sigma> i) |i. i \<in> sset (sdrop n (idx_stream \<sigma>))}")
        subgoal by (simp add: stream.set_map)
        subgoal
          apply (insert st1[unfolded collapse_reorder_state_def])
          apply (drule equalityD1)
          apply (erule subsetD)
           apply (rule UnI1)
          apply (rule CollectI)
          apply (intro exI conjI[rotated])
           apply assumption
          apply (simp add: less_w_complete)
          done
        done
      apply (auto simp: stream.set_map not_less)
      subgoal for i i' d t
        apply (insert st1[unfolded collapse_reorder_state_def])
        apply (drule Set.equalityD2)
        apply (drule subsetD)
         apply (intro CollectI exI conjI)
          apply (rule refl)
         apply assumption
        apply (erule UnE)
         apply (clarsimp simp: less_w_complete)
        apply (frule (1) order.strict_trans1)
        using less_w_less_idx apply blast
        done
      done
    from 3[THEN conjunct1, symmetric] show "xs = stake (length xs) (sdrop n (reorder_alt \<sigma>))"
      by (simp add: xs_eq reorder_alt_def)

    have buffer_st2: "buffer st2 = DAList.filter (\<lambda>x. w \<le> fst x) (buffer st1)"
      using step_eq by (auto simp: w_def st1_def reorder_flush_def Let_def)
    have "sset (sdrop (n + length xs) (idx_stream \<sigma>)) =
      {x \<in> sset (sdrop n (idx_stream \<sigma>)). \<forall>y \<in> set (alist.impl_of (buffer st1)).
        fst y < w \<longrightarrow> fst y < x}"
      using arg_cong[where f="image fst", OF 3[THEN conjunct2]]
      apply (simp add: stream.set_map[symmetric] stream.map_comp stream.map_ident cong: stream.map_cong)
      apply (auto 0 3 simp: stream.set_map intro: rev_image_eqI)
      done
    also have "\<dots> = {x \<in> sset (sdrop n (idx_stream \<sigma>)). w \<le> x}"
      apply auto
      apply (insert st1[unfolded collapse_reorder_state_def, THEN Set.equalityD2])
      apply (drule subsetD)
       apply (intro CollectI exI conjI)
        apply (rule refl)
       apply assumption
      apply auto
      using le_less_linear less_w_less_idx by blast
    finally have 4: "sset (sdrop (n + length xs) (idx_stream \<sigma>)) = {x \<in> sset (sdrop n (idx_stream \<sigma>)). w \<le> x}" .
    show "collapse_reorder_state st2 (mwtl \<sigma>') =
      {(i, collapse_idx \<sigma> i, ts_of_idx \<sigma> i) |i. i \<in> sset (sdrop (n + length xs) (idx_stream \<sigma>))}"
      apply (simp add: collapse_reorder_state_def buffer_st2 DAList.filter.rep_eq)
      apply (safe; clarsimp)
      subgoal for i d t
        apply (insert st1[unfolded collapse_reorder_state_def, THEN equalityD1])
        apply (drule subsetD)
         apply (intro UnI1 CollectI exI conjI)
          apply (rule refl)
         apply assumption
        apply (clarsimp simp: 4)
        done
      subgoal for j
        apply (simp add: 4 keyset_filter_impl image_Collect)
        apply (erule disjE)
        subgoal
          apply (insert st1[unfolded collapse_reorder_state_def, THEN equalityD1])
          apply (drule subsetD)
           apply (rule UnI2[of "(idx (mwnth (mwtl \<sigma>') j), _, _)"])
           apply (intro CollectI exI conjI)
             apply (rule refl)
            apply (clarsimp simp: keyset.rep_eq)
           apply (rule refl)
          apply clarsimp
          using le_less_linear less_w_less_idx by blast
        subgoal
          using le_less_linear less_w_less_idx by auto
        done
      subgoal for i
        apply (insert st1[unfolded collapse_reorder_state_def, THEN Set.equalityD2])
        apply (drule subsetD)
         apply (intro CollectI exI conjI)
          apply (rule refl)
         apply (rule subsetD[OF sset_sdrop_subset])
         apply simp
        apply (auto simp: 4 keyset.rep_eq DAList.filter.rep_eq)
        done
      done
  qed
  done

lemma reorder_eq_alt: "reorder_state_rel \<sigma> st n \<Longrightarrow> reorder st = sdrop n (reorder_alt \<sigma>)"
  apply (coinduction arbitrary: st \<sigma> n rule: reorder.coinduct)
  subgoal for st \<sigma> n
    apply (induction st rule: reorder.inner_induct)
    subgoal premises ind for st
      apply (cases "fst (reorder_step st)")
      subgoal
        apply (frule ind(1))
         apply (rule reorder_state_rel_step[where xs="[]", simplified, OF ind(2)])
         apply (auto intro: prod_eqI)[]
        apply (subst (1 3) reorder.code)
        apply (simp add: split_beta)
        done
      subgoal for x xs
        apply (insert reorder_state_rel_step[where xs="x # xs" and st'="snd (reorder_step st)", OF ind(2)])
        apply (drule meta_mp)
         apply (auto intro: prod_eqI)[]
        apply (subst (1 3) reorder.code)
        apply (clarsimp simp: split_beta)
        apply (subst stake_sdrop[where n="length xs" and s="sdrop n (stl (reorder_alt \<sigma>))", symmetric])
        apply (erule shift.friend.cong_shift)
        apply (force intro: reorder.cong_base)
        done
      done
    done
  done

lemma reorder'_eq_alt: "reorder' \<sigma> = Abs_trace (reorder_alt \<sigma>)"
  using reorder_eq_alt[OF reorder_state_rel_init, of \<sigma>] by (simp add: reorder'_def)


subsection \<open>Proof of correctness\<close>

subsubsection \<open>Switching lemmas\<close>

text \<open>\<^term>\<open>relax_order\<close> and slicing:\<close>

lemma map_w\<Gamma>_relax_order: "\<sigma>' \<in> relax_order \<sigma> \<Longrightarrow> map_w\<Gamma> f \<sigma>' \<in> relax_order (map_i\<Gamma> f \<sigma>)"
  by (fastforce simp: relax_order_def relax_orderp_def)

lemma relax_order_wslice:
  "relax_order \<circ>\<then> determ (wslice Xs) \<le> determ (islice Xs) \<circ>\<then> mapM_set relax_order"
  by (auto simp: le_fun_def kleisli_set_def determ_def in_mapM_set_iff
      wslice_def islice_def in_set_zip intro!: list_all2I map_w\<Gamma>_relax_order)

text \<open>\<^term>\<open>relax_order\<close> and \<^term>\<open>transpose\<close>:\<close>

lemma list_all2_transposeI: "list_all2 (list_all2 P) xss yss \<Longrightarrow> list_all2 (list_all2 P) (transpose xss) (transpose yss)"
  apply (rule list_all2_all_nthI)
  subgoal 1
    unfolding length_transpose
    by (induction xss yss pred: list_all2) (auto dest: list_all2_lengthD)
  subgoal for i
    apply (frule 1)
    apply (simp add: nth_transpose list.rel_map length_transpose)
    apply (thin_tac "_ < _")
    apply (thin_tac "_ = _")
    apply (induction xss yss pred: list_all2)
    apply (auto simp: list_all2_Cons1 dest: list_all2_nthD list_all2_lengthD)
    done
  done

lemma mapM_mapM_transpose:
  "(mapM_set (mapM_set f) \<circ>\<then> determ transpose) \<le> determ transpose \<circ>\<then> mapM_set (mapM_set f)"
  by (auto simp: le_fun_def kleisli_set_def in_mapM_set_iff intro!: list_all2_transposeI)

text \<open>\<^term>\<open>ipartition\<close> and slicing:\<close>

lemma length_islice[simp]: "length (islice Xs \<sigma>) = length Xs"
  by (simp add: islice_def)

lemma foldr_const_max: "foldr (\<lambda>x. max c) xs (a::_::linorder) = (if xs = [] then a else max c a)"
  by (induction xs) simp_all

lemma i\<tau>_islice[simp]: "k < length Xs \<Longrightarrow> i\<tau> (islice Xs \<sigma> ! k) j = i\<tau> \<sigma> j"
  by (simp add: islice_def)

lemma i\<iota>_islice[simp]: "k < length Xs \<Longrightarrow> i\<iota> (islice Xs \<sigma> ! k) j = i\<iota> \<sigma> j"
  by (simp add: islice_def)

lemma i\<Gamma>_islice[simp]: "k < length Xs \<Longrightarrow> i\<Gamma> (islice Xs \<sigma> ! k) j = Xs ! k \<inter> i\<Gamma> \<sigma> j"
  by (simp add: islice_def)

lemma in_ipartition_lengthD: "ps \<in> ipartition n \<sigma> \<Longrightarrow> length ps = n \<and> n > 0"
  by (simp add: ipartition_def ipartitionp_def)

lemma ipartition_islice_transpose:
  "ipartition n \<circ>\<then> determ (map (islice Xs)) \<circ>\<then> determ transpose \<le>
    determ (islice Xs) \<circ>\<then> mapM_set (ipartition n)"
  apply (clarsimp simp: le_fun_def kleisli_set_def in_mapM_set_iff Bex_def)
  apply (rule list_all2_all_nthI)
  subgoal 1 for \<sigma> ps
    apply (subgoal_tac "ps \<noteq> []")
     apply (simp add: length_transpose foldr_map foldr_const_max cong: foldr_cong)
    apply (drule in_ipartition_lengthD)
    apply clarsimp
    done
  subgoal for \<sigma> ps k
    apply (frule 1)
    apply (simp add: nth_transpose cong: map_cong)
    apply (auto simp: ipartition_def ipartitionp_def cong: conj_cong)
    by (meson le_infI2)
  done

text \<open>Slicing and \<^term>\<open>collapse\<close>:\<close>

lemma least_i\<iota>_map_i\<Gamma>: "least_i\<iota> (map_i\<Gamma> f \<sigma>) = least_i\<iota> \<sigma>"
  by (transfer fixing: f) (simp add: least_i\<iota>_def)

lemma next_i\<iota>_map_i\<Gamma>: "next_i\<iota> (map_i\<Gamma> f \<sigma>) = next_i\<iota> \<sigma>"
  by (transfer fixing: f) (simp add: fun_eq_iff next_i\<iota>_def)

lemma map_\<Gamma>_inter_collapse: "map_\<Gamma> (\<lambda>Y. X \<inter> Y) (collapse \<sigma>) = collapse (map_i\<Gamma> (\<lambda>Y. X \<inter> Y) \<sigma>)"
  apply (rule Rep_trace_inject[THEN iffD1])
  apply (simp add: map_\<Gamma>.rep_eq collapse.rep_eq collapse'_def stream.map_comp
      least_i\<iota>_map_i\<Gamma> next_i\<iota>_map_i\<Gamma> cong: stream.map_cong)
  apply (rule stream.map_cong[OF refl])
  apply (auto simp: i\<tau>_of_i\<iota>_def)
  done

abbreviation "tslice Xs \<equiv> (\<lambda>\<sigma>. map (\<lambda>X. map_\<Gamma> ((\<inter>) X) \<sigma>) Xs)"

lemma islice_collapse_swap: "islice Xs \<circ>> map collapse = collapse \<circ>> tslice Xs"
  by (clarsimp simp: fun_eq_iff islice_def split_beta
      map_\<Gamma>_inter_collapse zip_replicate2 cong: map_cong)


subsubsection \<open>Reordering obtains the collapsed trace\<close>

text \<open>Direct characterization of merged out-of-order partition:\<close>

locale mwpartitionp =
  fixes \<sigma> :: "'a itrace" and n :: nat and \<sigma>' :: "'a mwtrace"
  assumes
    n_greater_0: "n > 0" and
    mworigins_eq_n: "mworigins \<sigma>' = {0..<n}" and
    sound_partition: "\<forall>j. \<exists>i. idx (mwnth \<sigma>' j) = i\<iota> \<sigma> i \<and> ts (mwnth \<sigma>' j) = i\<tau> \<sigma> i \<and> db (mwnth \<sigma>' j) \<subseteq> i\<Gamma> \<sigma> i" and
    complete_partition1: "\<forall>i. \<exists>j. idx (mwnth \<sigma>' j) = i\<iota> \<sigma> i \<and> ts (mwnth \<sigma>' j) = i\<tau> \<sigma> i" and
    complete_partition2: "\<forall>i. \<forall>f \<in> i\<Gamma> \<sigma> i. \<exists>j. idx (mwnth \<sigma>' j) = i\<iota> \<sigma> i \<and> ts (mwnth \<sigma>' j) = i\<tau> \<sigma> i \<and> f \<in> db (mwnth \<sigma>' j)"

definition mwpartition :: "nat \<Rightarrow> 'a itrace \<Rightarrow> 'a mwtrace set" where
  "mwpartition n \<sigma> = {\<sigma>'. mwpartitionp \<sigma> n \<sigma>'}"

lemma mwproject_eqD: "mwproject k \<sigma>' = \<sigma> \<Longrightarrow> k \<in> mworigins \<sigma>' \<Longrightarrow>
  (\<forall>j. origin (mwnth \<sigma>' j) = k \<longrightarrow> (\<exists>i. idx (mwnth \<sigma>' j) = w\<iota> \<sigma> i \<and> ts (mwnth \<sigma>' j) = w\<tau> \<sigma> i \<and> db (mwnth \<sigma>' j) = w\<Gamma> \<sigma> i)) \<and>
  (\<forall>i. \<exists>j. origin (mwnth \<sigma>' j) = k \<and> idx (mwnth \<sigma>' j) = w\<iota> \<sigma> i \<and> ts (mwnth \<sigma>' j) = w\<tau> \<sigma> i \<and> db (mwnth \<sigma>' j) = w\<Gamma> \<sigma> i)"
  apply (transfer fixing: k)
  apply (auto simp: wtsdb.defs)
  subgoal for \<sigma>' x j
    apply (insert ex_snth_sfilter2[of "\<lambda>y. origin y = origin x" \<sigma>' j])
    apply clarsimp
    subgoal for i
      apply (rule exI[where x=i])
      apply simp
      done
    done
  subgoal for \<sigma>' x i
    apply (insert ex_snth_sfilter[of "\<lambda>y. origin y = origin x" \<sigma>' i])
    apply clarsimp
    subgoal for j
      apply (rule exI[where x=j])
      apply simp
      done
    done
  done

lemma ipartition_relax_merge: "ipartition n \<circ>\<then> mapM_set relax_order \<circ>\<then> merge \<le> mwpartition n"
  apply (clarsimp simp: le_fun_def kleisli_set_def merge_def ipartition_def
      ipartitionp_def in_mapM_set_iff list_all2_conv_all_nth relax_order_def relax_orderp_def
      mwpartition_def mwpartitionp_def)
  apply (safe; simp?)
  subgoal for \<sigma> \<sigma>' ps' ps j
    apply (drule spec[where P="\<lambda>k. k < length ps' \<longrightarrow> _ k" and x="origin (mwnth \<sigma>' j)"])+
    apply (subgoal_tac "origin (mwnth \<sigma>' j) < length ps'")
     defer
    using origin_mwnth apply fastforce
    apply simp
    apply (drule mwproject_eqD)
     apply (simp add: origin_mwnth)
    apply clarsimp
    by metis
  subgoal for \<sigma> \<sigma>' ps' ps i
    apply (drule spec[where P="\<lambda>i. \<exists>k<length ps'. _ i k" and x=i])
    apply clarify
    subgoal for k j
      apply (drule spec[where P="\<lambda>k. k < length ps' \<longrightarrow> _ k" and x=k])
      apply clarsimp
      apply (drule mwproject_eqD)
       apply blast
      by metis
    done
  subgoal for \<sigma> \<sigma>' ps' ps i f
    apply (drule spec[where P="\<lambda>i. \<forall>f\<in>i\<Gamma> \<sigma> i. \<exists>k<length ps'. _ i f k" and x=i])
    apply (drule (1) bspec)
    apply clarify
    subgoal for k j
      apply (drule spec[where P="\<lambda>k. k < length ps' \<longrightarrow> _ k" and x=k])
      apply clarsimp
      apply (drule mwproject_eqD)
       apply blast
      by metis
    done
  done

lemma mwpartition_reorder': "mwpartition n \<circ>\<then> determ reorder' \<le> determ (collapse)"
  apply (clarsimp simp: le_fun_def kleisli_set_def reorder'_eq_alt collapse.abs_eq mwpartition_def)
  apply (rule arg_cong[where f=Abs_trace])
  apply (simp add: reorder_alt_def collapse'_def idx_stream_def)
  apply (rule stream.map_cong)
   apply (rule arg_cong2[where f=siterate])
  subgoal for \<sigma> \<sigma>'
    by (clarsimp simp: fun_eq_iff least_idx_def next_i\<iota>_def mwpartitionp_def Suc_le_eq)
      metis
  subgoal for \<sigma> \<sigma>'
    by (simp add: least_idx_def least_i\<iota>_def mwpartitionp_def) metis
  subgoal for \<sigma> \<sigma>' i
    apply (clarsimp simp: collapse_idx_def ts_of_idx_def i\<tau>_of_i\<iota>_def mwpartitionp_def)
    apply safe
    subgoal by fastforce
    subgoal for f j
      apply (drule spec[where P="\<lambda>i. \<forall>f\<in>i\<Gamma> \<sigma> i. _ i f" and x=j])
      apply (drule (1) bspec)
      apply clarsimp
      by metis
    subgoal
      apply (rule LeastI2_ex[where P="\<lambda>j. i = i\<iota> \<sigma> j"])
       apply (clarsimp simp: sset_siterate)
       apply (rule ex_funpow_next_i\<iota>1)
      apply simp
      apply (rule LeastI2_ex)
       apply metis
      apply simp
      apply (metis i\<iota>_eq_imp_i\<tau>_eq)
      done
    done
  done

subsubsection \<open>Main result\<close>

definition multi_source_slicer :: "'a set list \<Rightarrow> 'a wtrace list \<Rightarrow> 'a trace list set" where
  "multi_source_slicer Xs = determ (map (wslice Xs)) !\<then> determ transpose !\<then>
    mapM_set merge !\<then> determ (map reorder')"

lemma not_Nil_in_transpose: "[] \<notin> set (transpose xss)"
  apply (clarsimp simp: in_set_conv_nth nth_transpose length_transpose filter_empty_conv)
  apply (induction xss)
   apply (auto simp: less_max_iff_disj)
  done

theorem multi_source_correctness:
  assumes "0 < n"
  shows "wpartition n !\<then> multi_source_slicer Xs = determ (collapse \<circ>> tslice Xs)"
proof (rule eq_determI)
  have lhs_eq: "wpartition n !\<then> multi_source_slicer Xs = ipartition n !\<then> mapM_set relax_order !\<then>
    determ (map (wslice Xs)) !\<then> determ transpose !\<then> mapM_set merge !\<then>
    determ (map reorder')" (is "_ = ?lhs")
    unfolding multi_source_slicer_def strong_kleisli_assoc wpartition_split ..
  also have "\<dots> \<le> ipartition n \<circ>\<then> mapM_set relax_order \<circ>\<then>
    determ (map (wslice Xs)) \<circ>\<then> determ transpose \<circ>\<then> mapM_set merge \<circ>\<then>
    determ (map reorder')"
    by (intro order_trans[OF strong_kleisli_le_kleisli_set] kleisli_set_mono order_refl)
  also have "\<dots> \<le> ipartition n \<circ>\<then> determ (map (islice Xs)) \<circ>\<then> mapM_set (mapM_set relax_order) \<circ>\<then>
    determ transpose \<circ>\<then> mapM_set merge \<circ>\<then> determ (map reorder')"
  proof -
    have "mapM_set relax_order \<circ>\<then> determ (map (wslice Xs)) \<le> determ (map (islice Xs)) \<circ>\<then> mapM_set (mapM_set relax_order)"
      by (auto simp: determ_fcomp_eq_kleisli mapM_set_determ[symmetric] kleisli_mapM_set
          relax_order_wslice intro!: mapM_set_mono)
    then show ?thesis
      by (subst (2 6) kleisli_set_assoc) (intro kleisli_set_mono order_refl)
  qed
  also have "\<dots> \<le> ipartition n \<circ>\<then> determ (map (islice Xs)) \<circ>\<then> determ transpose \<circ>\<then>
    mapM_set (mapM_set relax_order) \<circ>\<then> mapM_set merge \<circ>\<then> determ (map reorder')"
    by (subst (3 7) kleisli_set_assoc) (intro kleisli_set_mono mapM_mapM_transpose order_refl)
  also have "\<dots> \<le> determ (islice Xs) \<circ>\<then> mapM_set (ipartition n) \<circ>\<then>
    mapM_set (mapM_set relax_order) \<circ>\<then> mapM_set merge \<circ>\<then> determ (map reorder')"
    by (subst (1 2 5) kleisli_set_assoc)
      (intro kleisli_set_mono[OF ipartition_islice_transpose] order_refl)
  also have "\<dots> \<le> determ (islice Xs) \<circ>\<then> mapM_set (mwpartition n) \<circ>\<then> determ (map reorder')"
    by (subst (2 3) kleisli_set_assoc)
      (auto simp: kleisli_mapM_set ipartition_relax_merge intro!: kleisli_set_mono mapM_set_mono)
  also have "\<dots> \<le> determ (islice Xs) \<circ>\<then> determ (map collapse)"
    apply (rule kleisli_set_mono[OF order_refl])
    apply (unfold mapM_set_determ[symmetric] kleisli_mapM_set)
    apply (rule mapM_set_mono)
    apply (rule mwpartition_reorder')
    done
  also have "\<dots> \<le> determ (collapse \<circ>> tslice Xs)"
    by (simp add: determ_fcomp_eq_kleisli[symmetric] islice_collapse_swap)
  finally show "wpartition n !\<then> multi_source_slicer Xs \<le> determ (collapse \<circ>> tslice Xs)" .

  have "\<And>x. ?lhs x \<noteq> {}"
    apply (rule strong_kleisli_not_emptyI)
     apply (rule round_robin_ipartition[OF \<open>0 < n\<close>])
    apply (rule strong_kleisli_not_emptyI)
     apply (rule map_in_mapM_setI)
     apply (rule add_wmarks_relax_order)
    apply (rule strong_kleisli_not_emptyI)
     apply (subst in_determ_iff_eq, rule refl)
    apply (rule strong_kleisli_not_emptyI)
     apply (subst in_determ_iff_eq, rule refl)
    apply (rule strong_kleisli_not_emptyI)
     apply (rule map_in_mapM_setI)
     apply (rule merge_rr_merge)
     apply (auto simp: not_Nil_in_transpose)
    done
  then show "\<And>x. (wpartition n !\<then> multi_source_slicer Xs) x \<noteq> {}"
    unfolding lhs_eq .
qed

corollary ordered_multi_source_correctness:
  assumes "0 < n"
  shows "ipartition n !\<then> determ (map add_wmarks) !\<then> multi_source_slicer Xs =
    determ (collapse \<circ>> tslice Xs)" (is "?impl = ?spec")
proof (rule eq_determI)
  have 1: "\<And>a b c. b \<in> ipartition n a \<Longrightarrow> c \<in> mapM_set relax_order b \<Longrightarrow> multi_source_slicer Xs c \<noteq> {}"
    using multi_source_correctness[OF assms, of Xs]
    by (auto 0 3 simp add: determ_def fun_eq_iff wpartition_split strong_kleisli_def
        split: if_splits)

  have "?impl \<le> ipartition n !\<then> mapM_set relax_order !\<then> multi_source_slicer Xs"
    apply (rule le_funI)
    apply (rule strong_kleisli_mono[OF order_refl])
     apply (rule strong_kleisli_mono[OF _ order_refl])
      apply (auto simp: determ_def add_wmarks_relax_order intro!: map_in_mapM_setI)[]
     apply (erule (1) 1)
    apply (rule strong_kleisli_not_emptyI)
     apply (rule map_in_mapM_setI[OF add_wmarks_relax_order])
    apply (erule (1) 1)
    done
  then show "?impl \<le> ?spec"
    unfolding multi_source_correctness[OF assms, symmetric] wpartition_split strong_kleisli_assoc .

  show "\<And>x. ?impl x \<noteq> {}"
    apply (rule strong_kleisli_not_emptyI)
     apply (rule round_robin_ipartition[OF assms])
    apply (rule strong_kleisli_not_emptyI)
     apply simp
    apply (erule 1)
    apply simp
    apply (rule map_in_mapM_setI[OF add_wmarks_relax_order])
    done
qed

subsubsection \<open>Corollaries\<close>

corollary partially_ordered_multi_source:
  assumes "ipartitionp \<sigma> n ps"
  shows "multi_source_slicer Xs (map add_wmarks ps) = {tslice Xs (collapse \<sigma>)}"
  using ordered_multi_source_correctness[OF ipartitionp.n_greater_0, OF assms, unfolded fun_eq_iff
      determ_def strong_kleisli_singleton_conv ipartition_def, simplified, rule_format,
      THEN conjunct2, rule_format, OF assms] .

corollary totally_ordered_multi_source:
  assumes "ipartitionp (add_timepoints \<sigma>) n ps"
  shows "multi_source_slicer Xs (map add_wmarks ps) = {tslice Xs \<sigma>}"
  using partially_ordered_multi_source[OF assms, unfolded collapse_add_timepoints] .

corollary watermarked_multi_source:
  assumes "wpartitionp \<sigma> n ps"
  shows "multi_source_slicer Xs ps = {tslice Xs (collapse \<sigma>)}"
  using multi_source_correctness[OF wpartitionp.n_greater_0[OF assms], unfolded fun_eq_iff
      determ_def strong_kleisli_singleton_conv wpartition_def, simplified, rule_format,
      THEN conjunct2, rule_format, OF assms] .

subsubsection \<open>Integration with the slicing framework\<close>

context sliceable_fo_spec
begin

lemma tslice_relevant_events: "tslice (map relevant_events Xs) \<sigma> = map (\<lambda>X. slice X \<sigma>) Xs"
  by (simp add: Int_commute cong: map_\<Gamma>_cong)

definition multi_source_monitor :: "'b list set list \<Rightarrow> 'a wtrace list \<Rightarrow> (nat \<times> 'b tuple) set set" where
  "multi_source_monitor Xs = multi_source_slicer (map relevant_events Xs) \<circ>\<then>
    determ (map2 (\<lambda>X. verdicts \<circ>> verdict_filter X) Xs \<circ>> (Union \<circ> set))"

theorem multi_source_monitor_eq:
  assumes "\<Union>(set Xs) = UNIV" and "wpartitionp \<sigma> n ps" and [simp]: "traces = UNIV"
  shows "multi_source_monitor Xs ps = {verdicts (collapse \<sigma>)}"
proof -
  let ?Xs' = "map relevant_events Xs"
  have "multi_source_slicer ?Xs' ps = {tslice ?Xs' (collapse \<sigma>)}"
    using watermarked_multi_source[OF assms(2)] .
  then show ?thesis
    unfolding tslice_relevant_events
    by (simp add: multi_source_monitor_def kleisli_set_def determ_def
        map2_map_map[where f=id, simplified] del: set_map)
      (simp add: union_verdicts_slice[OF assms(1)])
qed

end

locale multi_source = sliceable_fo_spec + cosafety_monitor
begin

definition multi_source_monitor_M :: "'b list set list \<Rightarrow> 'a wtrace list \<Rightarrow> (nat \<times> 'b tuple) set set" where
  "multi_source_monitor_M Xs = multi_source_slicer (map relevant_events Xs) \<circ>\<then>
    determ (map2 (\<lambda>X. M_limit \<circ>> verdict_filter X) Xs \<circ>> (Union \<circ> set))"

corollary multi_source_monitor_eq_alt: "\<Union>(set Xs) = UNIV \<Longrightarrow> wpartitionp_alt \<sigma> n ps \<Longrightarrow> traces = UNIV \<Longrightarrow>
  multi_source_monitor_M Xs (wpartitionp_alt.ps' ps) = {M_limit (collapse \<sigma>)}"
  unfolding multi_source_monitor_M_def
  using multi_source_monitor_eq[OF _ wpartitionp_alt.wpartitionp_ps', unfolded multi_source_monitor_def]
  by (simp add: M_limit_eq)

end

(*<*)
end
(*>*)
