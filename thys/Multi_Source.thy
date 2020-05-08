theory Multi_Source
  imports Trace "HOL-Library.BNF_Corec" "HOL-Library.DAList"
begin

notation fcomp (infixr "\<circ>>" 55)

lemma map_fcomp_map: "map f \<circ>> map g = map (f \<circ>> g)"
  by (simp add: fcomp_comp)

definition determ :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b set" where
  "determ f = (\<lambda>x. {f x})"

lemma in_determ_iff_eq[simp]: "y \<in> determ f x \<longleftrightarrow> y = f x"
  by (simp add: determ_def)

definition kleisli_set :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('b \<Rightarrow> 'c set) \<Rightarrow> 'a \<Rightarrow> 'c set" where
  "kleisli_set f g = (\<lambda>x. \<Union> (g ` f x))"

notation kleisli_set (infixr "\<circ>\<then>" 55)

lemma kleisli_set_assoc: "f \<circ>\<then> (g \<circ>\<then> h) = (f \<circ>\<then> g) \<circ>\<then> h"
  by (auto simp: kleisli_set_def)

lemma determ_fcomp: "determ (f \<circ>> g) = f \<circ>> determ g"
  by auto

lemma fcomp_kleisli: "f \<circ>> g = determ f \<circ>\<then> g"
  by (auto simp: kleisli_set_def)

lemma kleisli_set_mono: "f \<le> f' \<Longrightarrow> g \<le> g' \<Longrightarrow> f \<circ>\<then> g \<le> f' \<circ>\<then> g'"
  by (fastforce simp: le_fun_def kleisli_set_def)

lemma kleisli_set_mono_strong: "f \<le> f' \<Longrightarrow> (\<And>x y. y \<in> f' x \<Longrightarrow> g y \<subseteq> g' y) \<Longrightarrow>
  f \<circ>\<then> g \<le> f' \<circ>\<then> g'"
  by (fastforce simp: le_fun_def kleisli_set_def)

definition mapM_set :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a list \<Rightarrow> 'b list set" where
  "mapM_set f xs = listset (map f xs)"

lemma in_listset_iff: "xs \<in> listset As \<longleftrightarrow> list_all2 (\<in>) xs As"
  by (induction As arbitrary: xs) (auto simp: set_Cons_def list_all2_Cons2)

lemma in_mapM_set_iff: "xs \<in> mapM_set f ys \<longleftrightarrow> list_all2 (\<lambda>x y. x \<in> f y) xs ys"
  by (simp add: mapM_set_def in_listset_iff list.rel_map)

lemma mapM_set_mono: "f \<le> f' \<Longrightarrow> mapM_set f \<le> mapM_set f'"
  by (fastforce simp: le_fun_def in_mapM_set_iff elim!: list.rel_mono_strong)

lemma mapM_set_determ: "mapM_set (determ f) = determ (map f)"
  by (auto simp: fun_eq_iff in_mapM_set_iff list.rel_map list.rel_map(2)[where g=f, symmetric]
      list.rel_eq intro!: list.rel_refl)

lemma kleisli_mapM_set: "mapM_set f \<circ>\<then> mapM_set g = mapM_set (f \<circ>\<then> g)"
  apply (auto simp: fun_eq_iff kleisli_set_def in_mapM_set_iff)
   apply (auto elim: list_all2_trans[rotated])[]
  apply (insert list.rel_compp[where R="\<lambda>x y. x \<in> g y" and S="\<lambda>x y. x \<in> f y"])
  by (simp add: Bex_def relcompp_apply[abs_def] fun_eq_iff in_mapM_set_iff conj_commute)

lemma map_in_mapM_setI: "(\<And>x. x \<in> set xs \<Longrightarrow> f x \<in> g x) \<Longrightarrow> map f xs \<in> mapM_set g xs"
  by (auto simp: in_mapM_set_iff list.rel_map intro!: list.rel_refl_strong)

definition strong_kleisli :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('b \<Rightarrow> 'c set) \<Rightarrow> 'a \<Rightarrow> 'c set" where
  "strong_kleisli f g = (\<lambda>x. if {} \<in> g ` f x then {} else \<Union>(g ` f x))"

notation strong_kleisli (infixr "!\<then>" 55)

lemma strong_kleisli_assoc: "f !\<then> (g !\<then> h) = (f !\<then> g) !\<then> h"
  by (auto 0 3 simp: fun_eq_iff strong_kleisli_def)

lemma fcomp_strong_kleisli: "f \<circ>> g = determ f !\<then> g"
  by (auto simp: fun_eq_iff strong_kleisli_def)

lemma strong_kleisli_le_kleisli_set: "f !\<then> g \<le> f \<circ>\<then> g"
  by (auto simp: le_fun_def strong_kleisli_def kleisli_set_def)

lemma strong_kleisli_not_emptyI: "y \<in> f x \<Longrightarrow> (\<And>z. z \<in> f x \<Longrightarrow> g z \<noteq> {}) \<Longrightarrow> (f !\<then> g) x \<noteq> {}"
  by (auto simp: strong_kleisli_def)

lemma strong_kleisli_mono: "f x \<subseteq> f' x \<Longrightarrow> (\<And>y. y \<in> f' x \<Longrightarrow> g y \<subseteq> g' y) \<Longrightarrow>
  (\<And>y. y \<in> f' x \<Longrightarrow> g' y \<noteq> {}) \<Longrightarrow> (f !\<then> g) x \<subseteq> (f' !\<then> g') x"
  by (auto simp: strong_kleisli_def) blast

lemma strong_kleisli_singleton_conv:
  "(f !\<then> g) x = {z} \<longleftrightarrow> (\<exists>y. y \<in> f x) \<and> (\<forall>y. y \<in> f x \<longrightarrow> g y = {z})"
  by (auto simp: strong_kleisli_def split: if_splits dest: equalityD1)

lemma eq_determI: "f \<le> determ g \<Longrightarrow> (\<And>x. f x \<noteq> {}) \<Longrightarrow> f = determ g"
  by (fastforce simp: le_fun_def fun_eq_iff determ_def)


record 'a itsdb =
  db :: "'a set"
  ts :: nat
  idx :: nat

typedef 'a itrace = "{s :: 'a itsdb stream.
  ssorted (smap idx s) \<and> sincreasing (smap ts s) \<and>
  (\<forall>i j. idx (s !! i) \<le> idx (s !! j) \<longrightarrow> ts (s !! i) \<le> ts (s !! j))}"
  by (rule exI[where x="smap (\<lambda>x. \<lparr>db={}, ts=x, idx=x\<rparr>) nats"])
    (auto simp: stream.map_comp stream.map_ident cong: stream.map_cong)

setup_lifting type_definition_itrace

lift_definition i\<Gamma> :: "'a itrace \<Rightarrow> nat \<Rightarrow> 'a set" is "\<lambda>s i. db (s !! i)" .
lift_definition i\<tau> :: "'a itrace \<Rightarrow> nat \<Rightarrow> nat" is "\<lambda>s i. ts (s !! i)" .
lift_definition i\<iota> :: "'a itrace \<Rightarrow> nat \<Rightarrow> nat" is "\<lambda>s i. idx (s !! i)" .

lift_definition map_i\<Gamma> :: "('a set \<Rightarrow> 'b set) \<Rightarrow> 'a itrace \<Rightarrow> 'b itrace" is
  "\<lambda>f. smap (\<lambda>x. \<lparr>db = f (db x), ts = ts x, idx = idx x\<rparr>)"
  by (simp add: stream.map_comp cong: stream.map_cong)

lemma i\<Gamma>_map_i\<Gamma>[simp]: "i\<Gamma> (map_i\<Gamma> f \<sigma>) i = f (i\<Gamma> \<sigma> i)"
  by transfer simp

lemma i\<tau>_map_i\<Gamma>[simp]: "i\<tau> (map_i\<Gamma> f \<sigma>) i = i\<tau> \<sigma> i"
  by transfer simp

lemma i\<iota>_map_i\<Gamma>[simp]: "i\<iota> (map_i\<Gamma> f \<sigma>) i = i\<iota> \<sigma> i"
  by transfer simp

lemma mono_i\<iota>: "i \<le> j \<Longrightarrow> i\<iota> \<sigma> i \<le> i\<iota> \<sigma> j"
  by transfer (simp add: ssorted_iff_mono)

lemma i\<tau>_increasing: "\<exists>j>i. i\<tau> \<sigma> i < i\<tau> \<sigma> j"
  by transfer (simp add: sincreasing_def)

lemma i\<iota>_refines_i\<tau>: "i\<iota> \<sigma> i \<le> i\<iota> \<sigma> j \<Longrightarrow> i\<tau> \<sigma> i \<le> i\<tau> \<sigma> j"
  by transfer simp

lemma mono_i\<tau>: "i \<le> j \<Longrightarrow> i\<tau> \<sigma> i \<le> i\<tau> \<sigma> j"
  using i\<iota>_refines_i\<tau>[OF mono_i\<iota>] .

lemma i\<iota>_not_stable: "\<exists>j>i. i\<iota> \<sigma> i \<noteq> i\<iota> \<sigma> j"
proof -
  obtain j where "i < j" and "i\<tau> \<sigma> i < i\<tau> \<sigma> j"
    using i\<tau>_increasing by blast
  moreover have "i\<iota> \<sigma> i \<le> i\<iota> \<sigma> j"
    using \<open>i < j\<close> by (simp add: mono_i\<iota>)
  ultimately show ?thesis
    using i\<iota>_refines_i\<tau>[of \<sigma> j i] by auto
qed

lift_definition add_timepoints :: "'a trace \<Rightarrow> 'a itrace" is
  "smap2 (\<lambda>i (db, ts). \<lparr>db=db, ts=ts, idx=i\<rparr>) nats"
  by (auto simp: split_beta smap2_szip stream.map_comp smap_szip_fst[of id, simplified]
      stream.map_ident smap_szip_snd ssorted_iff_mono cong: stream.map_cong)

lift_definition add_timestamps :: "'a trace \<Rightarrow> 'a itrace" is
  "smap (\<lambda>(db, ts). \<lparr>db=db, ts=ts, idx=ts\<rparr>)"
  by (auto simp: split_beta stream.map_comp cong: stream.map_cong)

definition next_i\<iota> :: "'a itrace \<Rightarrow> nat \<Rightarrow> nat" where
  "next_i\<iota> \<sigma> i = Inf {j. i < j \<and> i\<iota> \<sigma> i \<noteq> i\<iota> \<sigma> j}"

lemma Suc_le_next_i\<iota>: "Suc i \<le> next_i\<iota> \<sigma> i"
  using i\<iota>_not_stable by (auto simp: next_i\<iota>_def intro!: cInf_greatest)

lemma le_next_i\<iota>: "i \<le> next_i\<iota> \<sigma> i"
  using Suc_le_next_i\<iota> Suc_leD by blast

lemma mono_next_i\<iota>: "i \<le> i' \<Longrightarrow> next_i\<iota> \<sigma> i \<le> next_i\<iota> \<sigma> i'"
  unfolding next_i\<iota>_def
  apply (rule cInf_mono)
  using i\<iota>_not_stable apply auto
  by (metis le_eq_less_or_eq order.strict_trans)

definition collapse' :: "nat \<Rightarrow> 'a itrace \<Rightarrow> ('a set \<times> nat) stream" where
  "collapse' i0 \<sigma> = smap (\<lambda>i. (\<Union>i' \<in> i\<iota> \<sigma> -` {i\<iota> \<sigma> i}. i\<Gamma> \<sigma> i', i\<tau> \<sigma> i)) (siterate (next_i\<iota> \<sigma>) i0)"

lift_definition collapse :: "'a itrace \<Rightarrow> 'a trace" is "collapse' 0"
proof
  fix \<sigma> :: "'a itrace"
  have "ssorted (smap snd (collapse' i \<sigma>))" for i
    by (coinduction arbitrary: i) (auto simp: collapse'_def intro: mono_i\<tau> le_next_i\<iota>)
  then show "ssorted (smap snd (collapse' 0 \<sigma>))" .

  have "\<exists>k>j. smap snd (collapse' i \<sigma>) !! j < smap snd (collapse' i \<sigma>) !! k" for i j
  proof (induction j arbitrary: i)
    case 0
    obtain k where "i\<tau> \<sigma> i < i\<tau> \<sigma> k" using i\<tau>_increasing by blast
    moreover have "\<exists>k'. k \<le> (next_i\<iota> \<sigma> ^^ (Suc k')) i"
    proof (induction k)
      case 0
      show ?case by simp
    next
      case (Suc k)
      then obtain k' where "k \<le> (next_i\<iota> \<sigma> ^^ (Suc k')) i" ..
      then have "Suc k \<le> (next_i\<iota> \<sigma> ^^ (Suc (Suc k'))) i"
        by (auto intro: Suc_le_next_i\<iota>[THEN order_trans] mono_next_i\<iota>)
      then show ?case ..
    qed
    then have "\<exists>k'. i\<tau> \<sigma> k \<le> i\<tau> \<sigma> ((next_i\<iota> \<sigma> ^^ (Suc k')) i)"
      using mono_i\<tau> by blast
    ultimately show ?case
      by (auto simp add: collapse'_def simp del: funpow.simps elim: order.strict_trans2)
  next
    case (Suc j)
    from Suc.IH[of "next_i\<iota> \<sigma> i"] show ?case
      by (simp add: collapse'_def) (metis Suc_mono funpow.simps(2) funpow_swap1 o_apply)
  qed
  then show "sincreasing (smap snd (collapse' 0 \<sigma>))"
    by (simp add: sincreasing_def)
qed

lemma i\<Gamma>_timepoints[simp]: "i\<Gamma> (add_timepoints \<sigma>) = \<Gamma> \<sigma>"
  by transfer (simp add: split_beta)

lemma i\<tau>_timepoints[simp]: "i\<tau> (add_timepoints \<sigma>) = \<tau> \<sigma>"
  by transfer (simp add: split_beta)

lemma i\<iota>_timepoints[simp]: "i\<iota> (add_timepoints \<sigma>) = id"
  by transfer (simp add: split_beta id_def)

lemma next_i\<iota>_timepoints[simp]: "next_i\<iota> (add_timepoints \<sigma>) = Suc"
  by (fastforce simp: next_i\<iota>_def intro: antisym cInf_lower cInf_greatest)

lemma snth_Rep_trace: "Rep_trace \<sigma> !! i = (\<Gamma> \<sigma> i, \<tau> \<sigma> i)"
  by transfer simp

lemma collapse_add_timepoints: "collapse (add_timepoints \<sigma>) = \<sigma>"
proof -
  have "collapse' i (add_timepoints \<sigma>) = sdrop i (Rep_trace \<sigma>)" for i
    by (coinduction arbitrary: i) (auto simp: collapse'_def snth_Rep_trace)
  then show ?thesis
    by (intro Rep_trace_inject[THEN iffD1]) (simp add: collapse.rep_eq)
qed


locale itrace_partition =
  fixes \<sigma> :: "'a itrace" and n :: nat and ps :: "'a itrace list"
  assumes
    n_greater_0: "n > 0" and
    length_ps_eq_n: "length ps = n" and
    sound_partition: "\<forall>k<n. \<forall>j. \<exists>i. i\<iota> (ps ! k) j = i\<iota> \<sigma> i \<and> i\<tau> (ps ! k) j = i\<tau> \<sigma> i \<and> i\<Gamma> (ps ! k) j \<subseteq> i\<Gamma> \<sigma> i" and
    complete_partition1: "\<forall>i. \<exists>k<n. \<exists>j. i\<iota> (ps ! k) j = i\<iota> \<sigma> i \<and> i\<tau> (ps ! k) j = i\<tau> \<sigma> i" and
    complete_partition2: "\<forall>i. \<forall>f \<in> i\<Gamma> \<sigma> i. \<exists>k<n. \<exists>j. i\<iota> (ps ! k) j = i\<iota> \<sigma> i \<and> i\<tau> (ps ! k) j = i\<tau> \<sigma> i \<and> f \<in> i\<Gamma> (ps ! k) j"

definition partition :: "nat \<Rightarrow> 'a itrace \<Rightarrow> 'a itrace list set" where
  "partition n \<sigma> = {ps. itrace_partition \<sigma> n ps}"

primcorec sskip :: "nat \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
  "sskip n s = (case s of x ## s' \<Rightarrow> x ## sskip n (sdrop n s'))"

lemma smap_sskip: "smap f (sskip n s) = sskip n (smap f s)"
  by (coinduction arbitrary: s) (auto simp: stream.case_eq_if)

lemma snth_sskip: "sskip n s !! i = s !! (i * Suc n)"
  by (induction i arbitrary: s)
    (simp_all add: stream.case_eq_if sdrop_snth ac_simps)

lemma ssorted_sskip: "ssorted s \<Longrightarrow> ssorted (sskip n s)"
  by (simp add: ssorted_iff_mono snth_sskip add_mono)

lemma sincreasing_sskip: "sincreasing s \<Longrightarrow> ssorted s \<Longrightarrow> sincreasing (sskip n s)"
  apply (auto simp add: sincreasing_def ssorted_iff_mono snth_sskip)
  subgoal for i
    apply (drule spec[of _ "i + i * n"])
    by (metis le_add1 le_less_trans not_le)
  done

lift_definition round_robin :: "nat \<Rightarrow> 'a itrace \<Rightarrow> 'a itrace list" is
  "\<lambda>n s. map (\<lambda>k. sskip (n-1) (sdrop k s)) [0..<n]"
  apply (auto simp: list.pred_set smap_sskip snth_sskip sdrop_snth)
   apply (metis ssorted_sskip ssorted_sdrop sdrop_smap)
  apply (rule sincreasing_sskip)
   apply (subst sdrop_smap[symmetric])
   apply (erule sincreasing_sdrop)
  apply (subst sdrop_smap[symmetric])
  apply (rule ssorted_sdrop)
  apply (auto simp: ssorted_iff_mono)[]
  done

lemma length_round_robin[simp]: "length (round_robin n \<sigma>) = n"
  by transfer simp

lemma ix_round_robin:
  assumes "k < n"
  shows "i\<Gamma> (round_robin n \<sigma> ! k) j = i\<Gamma> \<sigma> (k + j * n)" and
    "i\<tau> (round_robin n \<sigma> ! k) j = i\<tau> \<sigma> (k + j * n)" and
    "i\<iota> (round_robin n \<sigma> ! k) j = i\<iota> \<sigma> (k + j * n)"
  using assms by (simp_all add: i\<Gamma>.rep_eq i\<tau>.rep_eq i\<iota>.rep_eq round_robin.rep_eq
      nth_map[where f=Rep_itrace, symmetric] snth_sskip sdrop_snth)

lemma round_robin_partition: "n > 0 \<Longrightarrow> round_robin n \<sigma> \<in> partition n \<sigma>"
  apply (simp add: partition_def)
  apply unfold_locales
      apply (auto simp: ix_round_robin Let_def)
  subgoal for i
    apply (rule exI[where x="i mod n"])
    apply simp
    apply (rule exI[where x="i div n"])
    apply (simp add: ix_round_robin)
    done
  subgoal for i
    apply (rule exI[where x="i mod n"])
    apply simp
    apply (rule exI[where x="i div n"])
    apply (simp add: ix_round_robin)
    done
  done


record 'a wtsdb = "'a itsdb" + wmark :: nat

definition wtracep :: "('a, 'b) wtsdb_scheme stream \<Rightarrow> bool" where
  "wtracep s \<longleftrightarrow> ssorted (smap wmark s) \<and> sincreasing (smap wmark s) \<and> sincreasing (smap ts s) \<and>
    (\<forall>i j. idx (s !! i) \<le> idx (s !! j) \<longrightarrow> ts (s !! i) \<le> ts (s !! j)) \<and>
    (\<forall>i. \<forall>j>i. wmark (s !! i) \<le> idx (s !! j))"

definition "dummy_raw_wtrace = smap (\<lambda>x. \<lparr>db={}, ts=x, idx=x, wmark=x\<rparr>) nats"

lemma wtracep_dummy: "wtracep dummy_raw_wtrace"
  by (auto simp: wtracep_def dummy_raw_wtrace_def stream.map_comp stream.map_ident cong: stream.map_cong)

typedef 'a wtrace = "{s :: 'a wtsdb stream. wtracep s}"
  by (auto intro!: exI[where x=dummy_raw_wtrace] wtracep_dummy)

setup_lifting type_definition_wtrace

lift_definition w\<Gamma> :: "'a wtrace \<Rightarrow> nat \<Rightarrow> 'a set" is "\<lambda>s i. db (s !! i)" .
lift_definition w\<tau> :: "'a wtrace \<Rightarrow> nat \<Rightarrow> nat" is "\<lambda>s i. ts (s !! i)" .
lift_definition w\<iota> :: "'a wtrace \<Rightarrow> nat \<Rightarrow> nat" is "\<lambda>s i. idx (s !! i)" .
lift_definition w\<beta> :: "'a wtrace \<Rightarrow> nat \<Rightarrow> nat" is "\<lambda>s i. wmark (s !! i)" .

lift_definition map_w\<Gamma> :: "('a set \<Rightarrow> 'b set) \<Rightarrow> 'a wtrace \<Rightarrow> 'b wtrace" is
  "\<lambda>f. smap (\<lambda>x. \<lparr>db = f (db x), ts = ts x, idx = idx x, wmark = wmark x\<rparr>)"
  by (simp add: wtracep_def stream.map_comp cong: stream.map_cong)

lemma w\<Gamma>_map_w\<Gamma>[simp]: "w\<Gamma> (map_w\<Gamma> f \<sigma>) i = f (w\<Gamma> \<sigma> i)"
  by transfer simp

lemma w\<tau>_map_w\<Gamma>[simp]: "w\<tau> (map_w\<Gamma> f \<sigma>) i = w\<tau> \<sigma> i"
  by transfer simp

lemma w\<iota>_map_w\<Gamma>[simp]: "w\<iota> (map_w\<Gamma> f \<sigma>) i = w\<iota> \<sigma> i"
  by transfer simp

locale relaxed_order =
  fixes \<sigma> :: "'a itrace" and \<sigma>' :: "'a wtrace"
  assumes
    sound_reordering: "\<forall>j. \<exists>i. w\<iota> \<sigma>' j = i\<iota> \<sigma> i \<and> w\<tau> \<sigma>' j = i\<tau> \<sigma> i \<and> w\<Gamma> \<sigma>' j = i\<Gamma> \<sigma> i" and
    complete_reordering: "\<forall>i. \<exists>j. w\<iota> \<sigma>' j = i\<iota> \<sigma> i \<and> w\<tau> \<sigma>' j = i\<tau> \<sigma> i \<and> w\<Gamma> \<sigma>' j = i\<Gamma> \<sigma> i"

definition relax_order :: "'a itrace \<Rightarrow> 'a wtrace set" where
  "relax_order \<sigma> = {\<sigma>'. relaxed_order \<sigma> \<sigma>'}"

lift_definition id_wtrace :: "'a itrace \<Rightarrow> 'a wtrace" is
  "smap (\<lambda>x. \<lparr>db=db x, ts=ts x, idx=idx x, wmark=idx x\<rparr>)"
  by (simp add: wtracep_def stream.map_comp ssorted_iff_mono sincreasing_def cong: stream.map_cong)
    (meson not_le)

lemma id_wtrace_relax_order: "id_wtrace \<sigma> \<in> relax_order \<sigma>"
  by (simp add: relax_order_def relaxed_order_def) (transfer; auto)+


definition islice :: "('a \<Rightarrow> 'b set \<Rightarrow> 'c set) \<Rightarrow> 'a list \<Rightarrow> 'b itrace \<Rightarrow> 'c itrace list" where
  "islice f xs \<sigma> = map2 (\<lambda>x. map_i\<Gamma> (f x)) xs (replicate (length xs) \<sigma>)"

definition wslice :: "('a \<Rightarrow> 'b set \<Rightarrow> 'c set) \<Rightarrow> 'a list \<Rightarrow> 'b wtrace \<Rightarrow> 'c wtrace list" where
  "wslice f xs \<sigma> = map2 (\<lambda>x. map_w\<Gamma> (f x)) xs (replicate (length xs) \<sigma>)"

lemma map_w\<Gamma>_relax_order: "\<sigma>' \<in> relax_order \<sigma> \<Longrightarrow> map_w\<Gamma> f \<sigma>' \<in> relax_order (map_i\<Gamma> f \<sigma>)"
  by (fastforce simp: relax_order_def relaxed_order_def)

lemma relax_order_wslice:
  "relax_order \<circ>\<then> determ (wslice f xs) \<le> determ (islice f xs) \<circ>\<then> mapM_set relax_order"
  by (auto simp: le_fun_def kleisli_set_def determ_def in_mapM_set_iff
      wslice_def islice_def in_set_zip intro!: list_all2I map_w\<Gamma>_relax_order)


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


definition infinitely :: "('a \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> bool" where
  "infinitely P s \<longleftrightarrow> (\<forall>i. \<exists>j\<ge>i. P (s !! j))"

lemma infinitely_stl: "infinitely P (stl s) \<longleftrightarrow> infinitely P s"
  apply (auto simp: infinitely_def)
  apply (metis le_Suc_eq snth.simps(2))
  using Suc_le_D by fastforce

lemma infinitely_sset_stl: "infinitely P s \<Longrightarrow> \<exists>x \<in> sset (stl s). P x"
  by (fastforce simp: infinitely_def dest!: Suc_le_D)

lemma sdrop_while_id_conv: "stream_all P s \<Longrightarrow> sdrop_while (Not \<circ> P) s = s"
  by (subst sdrop_while_sdrop_LEAST) simp_all

lemma sfilter_id_conv: "stream_all P s \<Longrightarrow> sfilter P s = s"
  by (coinduction arbitrary: s) (auto simp: sdrop_while_id_conv stl_sset)

record 'a mwtsdb = "'a wtsdb" + origin :: nat

typedef 'a mwtrace = "{s :: 'a mwtsdb stream. finite (origin ` sset s) \<and>
  (\<forall>k \<in> origin ` sset s. infinitely (\<lambda>x. origin x = k) s \<and> wtracep (sfilter (\<lambda>x. origin x = k) s))}"
  apply (rule exI[where x="smap (\<lambda>x. \<lparr>db={}, ts=x, idx=x, wmark=x, origin=0\<rparr>) nats"])
  apply (auto simp: infinitely_def stream.set_map image_image)
  apply (subst sfilter_id_conv)
   apply (simp add: stream.set_map)
  apply (auto simp: wtracep_def stream.map_comp stream.map_ident cong: stream.map_cong)
  done

setup_lifting type_definition_mwtrace

lemma wtracep_stlI: "wtracep s \<Longrightarrow> wtracep (stl s)"
  apply (auto simp: wtracep_def sincreasing_def elim: ssorted.cases)
     apply (metis Suc_leI Suc_le_D Suc_le_lessD less_Suc_eq_le snth.simps(2))
    apply (metis Suc_leI Suc_le_D Suc_le_lessD less_Suc_eq_le snth.simps(2))
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

definition linearize :: "'a wtrace list \<Rightarrow> 'a mwtrace set" where
  "linearize \<sigma>s = {\<sigma>. mworigins \<sigma> = {..<length \<sigma>s} \<and> (\<forall>k < length \<sigma>s. mwproject k \<sigma> = \<sigma>s ! k)}"

definition linearize_rr' :: "nat \<Rightarrow> 'a wtsdb stream list \<Rightarrow> 'a mwtsdb stream" where
  "linearize_rr' i0 xs = smap (\<lambda>i. wtsdb.extend (xs ! (i mod length xs) !! (i div length xs))
    \<lparr>origin = i mod length xs\<rparr>) (fromN i0)"

lemma origin_sset_linearize_rr': "xs \<noteq> [] \<Longrightarrow> origin ` sset (linearize_rr' 0 xs) = {..<length xs}"
  by (auto simp: sset_range image_image linearize_rr'_def wtsdb.defs
      intro: image_eqI[of x _ x for x])

lemma mod_nat_cancel_left: "0 < (b::nat) \<Longrightarrow> (b - a mod b + a) mod b = 0"
  by (metis le_add_diff_inverse2 mod_add_right_eq mod_le_divisor mod_self)

lemma infinitely_origin_linearize_rr': "k < length xs \<Longrightarrow>
  infinitely (\<lambda>x. origin x = k) (linearize_rr' i0 xs)"
  apply (clarsimp simp: infinitely_def linearize_rr'_def wtsdb.defs)
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
    by (metis (no_types, hide_lams) add.commute group_cancel.add2 mod_add_left_eq)
  also have "\<dots> = ((c - b mod c + b mod c) mod c + a mod c) mod c"
    by (metis (no_types, hide_lams) add.commute group_cancel.add2 mod_add_eq mod_add_right_eq)
  finally show ?thesis
    using assms by (simp add: mod_nat_cancel_left)
qed

lemma sdrop_while_linearize_rr': "k < length xs \<Longrightarrow>
  sdrop_while (Not \<circ> (\<lambda>x. origin x = k)) (linearize_rr' i0 xs) =
  linearize_rr' (i0 + (length xs - i0 mod length xs + k) mod length xs) xs"
  apply (subgoal_tac "(LEAST n. origin (linearize_rr' i0 xs !! n) = k) =
    (length xs - i0 mod length xs + k) mod length xs")
  subgoal
    apply (simp add: sdrop_while_sdrop_LEAST[OF infinitely_exD, OF infinitely_origin_linearize_rr'])
    apply (rule all_eq_snth_eqI)
    apply (simp add: sdrop_snth linearize_rr'_def ac_simps)
    done
  subgoal
    apply (auto simp: linearize_rr'_def wtsdb.defs mod_add_left_eq intro!: Least_equality)
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

lemma sfilter_origin_linearize_rr': "k < length xs \<Longrightarrow>
  sfilter (\<lambda>x. origin x = k) (linearize_rr' i xs) =
  sdrop ((i + (length xs - i mod length xs + k) mod length xs) div length xs)
    (smap (\<lambda>x. wtsdb.extend x \<lparr>origin=k\<rparr>) (xs ! k))"
  apply (coinduction arbitrary: i)
  subgoal for i
    apply safe
     apply (simp add: sdrop_while_linearize_rr')
     apply (simp add: linearize_rr'_def)
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
     apply (simp add: sdrop_while_linearize_rr')
     apply (simp add: linearize_rr'_def)
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

lift_definition linearize_rr :: "'a wtrace list \<Rightarrow> 'a mwtrace" is
 "\<lambda>xs. if xs = [] then smap (\<lambda>x. \<lparr>db={}, ts=x, idx=x, wmark=x, origin=0\<rparr>) nats
    else linearize_rr' 0 xs"
  apply (auto simp: stream.set_map image_image sfilter_id_conv origin_sset_linearize_rr')
     apply (auto simp add: infinitely_def)[]
    apply (subst wtracep_smap_truncate[symmetric])
    apply (simp add: stream.map_comp wtsdb.defs wtracep_dummy[unfolded dummy_raw_wtrace_def]
      cong: stream.map_cong)
   apply (rule infinitely_origin_linearize_rr')
  using origin_sset_linearize_rr' apply auto[]
  subgoal for xs x
    apply (subgoal_tac "origin x < length xs")
     apply (simp add: sfilter_origin_linearize_rr'[where i=0, simplified])
     apply (subst wtracep_smap_truncate[symmetric])
     apply (simp add: stream.map_comp wtsdb_truncate_extend stream.map_ident
        list.pred_set cong: stream.map_cong)
    using origin_sset_linearize_rr' apply auto[]
    done
  done

lemma linearize_rr_linearize: "xs \<noteq> [] \<Longrightarrow> linearize_rr xs \<in> linearize xs"
  apply (simp add: linearize_def)
  apply (rule conjI)
  subgoal by transfer (simp add: origin_sset_linearize_rr')
  subgoal
    apply clarify
    apply (rule Rep_wtrace_inject[THEN iffD1])
    apply (auto simp: mwproject.rep_eq linearize_rr.rep_eq
        sfilter_origin_linearize_rr'[where i=0, simplified] stream.map_comp
        wtsdb_truncate_extend stream.map_ident cong: stream.map_cong)[]
    using origin_sset_linearize_rr'[of "map Rep_wtrace xs"] apply auto
    done
  done


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

lift_definition keyset :: "('a, 'b) alist \<Rightarrow> 'a set" is "\<lambda>xs. fst ` set xs" .

lemma keyset_empty[simp]: "keyset DAList.empty = {}"
  by transfer simp

lemma keyset_update[simp]: "keyset (DAList.update k v al) = insert k (keyset al)"
  by transfer (simp add: dom_update)

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

lemma keyset_filter_impl: "keyset (DAList.filter P al) = fst ` (set (filter P (DAList.impl_of al)))"
  by transfer simp

lift_definition reorder_step :: "'a reorder_state \<Rightarrow> ('a set \<times> nat) list \<times> 'a reorder_state" is
  "\<lambda>(st, \<sigma>). let (xs, st') = reorder_flush (reorder_update (mwhd \<sigma>) st) in (xs, (st', mwtl \<sigma>))"
  by (auto simp: split_beta Let_def reorder_update_def reorder_flush_def origin_mwhd mworigins_mwtl
      lookup_update mwproject_mwtl wmark_mwhd_le_w\<iota> wmark_mwhd_le_w\<beta> keyset_filter_impl)

friend_of_corec shift :: "'a list \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
  "shift xs s = (case xs of [] \<Rightarrow> shd s | x # _ \<Rightarrow> x) ## (case xs of [] \<Rightarrow> stl s | _ # ys \<Rightarrow> shift ys s)"
  subgoal by (simp split: list.split)
  subgoal by transfer_prover
  done

definition next_to_emit :: "'a raw_reorder_state \<Rightarrow> 'a mwtrace \<Rightarrow> nat" where
  "next_to_emit st \<sigma> = (if buffer st = DAList.empty then idx (mwhd \<sigma>) else Min (keyset (buffer st)))"

definition next_to_release :: "'a raw_reorder_state \<Rightarrow> 'a mwtrace \<Rightarrow> nat \<Rightarrow> nat" where
  "next_to_release st \<sigma> k = (if next_to_emit st \<sigma> < the (DAList.lookup (wmarks st) k) then 0
    else Suc (LEAST i. origin (mwnth \<sigma> i) = k \<and> next_to_emit st \<sigma> < wmark (mwnth \<sigma> i)))"

lift_definition reorder_variant :: "'a reorder_state \<Rightarrow> nat" is
  "\<lambda>(st, \<sigma>). Max (next_to_release st \<sigma> ` keyset (wmarks st))" .

lemma sort_key_empty_conv: "sort_key f xs = [] \<longleftrightarrow> xs = []"
  by (induction xs) simp_all

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

lemma w\<beta>_mwproject_mwhd: "w\<beta> (mwproject (origin (mwhd \<sigma>)) \<sigma>) 0 = wmark (mwhd \<sigma>)"
  apply transfer
  subgoal for \<sigma>
    by (cases \<sigma>) (auto simp: wtsdb.defs sfilter_Stream)
  done

lemma Least_less_Least: "\<exists>x::'a::wellorder. Q x \<Longrightarrow> (\<And>x. Q x \<Longrightarrow> \<exists>y. P y \<and> y < x) \<Longrightarrow> Least P < Least Q"
  by (metis LeastI2 less_le_trans not_le_imp_less not_less_Least)

lemma sincreasing_ex_greater: "sincreasing s \<Longrightarrow> \<exists>i\<ge>j. (x::nat) < s !! i"
  unfolding sincreasing_def
  apply (induction x)
   apply simp_all
   apply (meson dual_order.strict_implies_order less_eq_nat.simps(1) order.strict_trans1)
  by (meson less_trans_Suc order.order_iff_strict order.trans)

lemma infinitely_exists: "infinitely P s \<Longrightarrow> \<exists>i. P (s !! i)"
  by (auto simp: infinitely_def)

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
   apply (simp add: sdrop_while_sdrop_LEAST infinitely_exists)
  using LeastI_ex infinitely_exists apply force
  apply (simp add: sdrop_while_sdrop_LEAST infinitely_exists)
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
    apply (drule sincreasing_ex_greater[where s="smap wmark _" and x=w])
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

definition reorder' :: "'a mwtrace \<Rightarrow> ('a set \<times> nat) stream" where
  "reorder' \<sigma> = reorder (init_reorder_state \<sigma>)"


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

definition collapse_reorder_state :: "'a raw_reorder_state \<Rightarrow> 'a mwtrace \<Rightarrow>  (nat \<times> 'a set \<times> nat) set" where
  "collapse_reorder_state st \<sigma>' =
    {(i, (d \<union> (collapse_idx \<sigma>' i), t)) | i d t. (i, (d, t)) \<in> set (DAList.impl_of (buffer st))} \<union>
    {(i, (collapse_idx \<sigma>' i, ts_of_idx \<sigma>' i)) | i. i \<notin> keyset (buffer st) \<and> (\<exists>j. i = idx (mwnth \<sigma>' j))}"

lift_definition reorder_state_rel :: "'a mwtrace \<Rightarrow> 'a reorder_state \<Rightarrow> nat \<Rightarrow> bool" is
  "\<lambda>\<sigma> (st, \<sigma>') n. collapse_reorder_state st \<sigma>' = {(i, collapse_idx \<sigma> i, ts_of_idx \<sigma> i) | i. i \<in> sset (sdrop n (idx_stream \<sigma>))}" .

lemma ex_idx_ge: "\<exists>x\<ge>y. \<exists>j. x = idx (mwnth \<sigma> j)"
  apply (transfer fixing: y)
  subgoal for \<sigma>
    apply (clarsimp simp: wtracep_def)
    apply (drule bspec[where x="shd \<sigma>"])
     apply (simp add: shd_sset)
    apply clarify
    apply (drule sincreasing_ex_greater[where x=y])
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
      apply (rule ex_idx_ge)
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

lemma set_stake_subset: "set (stake n s) \<subseteq> sset s"
proof (induction n arbitrary: s)
  case (Suc n)
  with stl_sset show ?case by (fastforce simp: shd_sset)
qed simp

lemma distinct_stake[simp]: "sdistinct s \<Longrightarrow> distinct (stake n s)"
proof (induction n arbitrary: s)
  case (Suc n)
  then have "shd s \<notin> sset (stl s)"
    by (blast elim: sdistinct.cases)
  then have "shd s \<notin> set (stake n (stl s))"
    using set_stake_subset by fastforce
  moreover have "distinct (stake n (stl s))"
    using Suc by (blast elim: sdistinct.cases)
  ultimately show ?case by simp
qed simp

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
  using Suc_le_lessD ex_idx_ge apply blast
  apply simp
  done

lemma ssorted_idx_stream: "ssorted (idx_stream \<sigma>)"
  apply (auto simp: idx_stream_def least_idx_def intro!: ssorted_siterate)
  apply (rule LeastI2_ex)
  apply (rule ex_idx_ge)
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
  by (smt distinct.simps(2) image_eqI less_le_trans list.simps(9) not_less_iff_gr_or_eq set_map sorted.simps(2))

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
        apply (drule equalityD2)
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
      apply (insert st1[unfolded collapse_reorder_state_def, THEN equalityD2])
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
        apply (insert st1[unfolded collapse_reorder_state_def, THEN equalityD2])
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

lemma reorder'_eq_alt: "reorder' = reorder_alt"
  using reorder_eq_alt[OF reorder_state_rel_init] by (auto simp: reorder'_def fun_eq_iff)


locale wtrace_partition =
  fixes \<sigma> :: "'a itrace" and n :: nat and ps :: "'a wtrace list"
  assumes
    n_greater_0: "n > 0" and
    length_ps_eq_n: "length ps = n" and
    sound_partition: "\<forall>k<n. \<forall>j. \<exists>i. w\<iota> (ps ! k) j = i\<iota> \<sigma> i \<and> w\<tau> (ps ! k) j = i\<tau> \<sigma> i \<and> w\<Gamma> (ps ! k) j \<subseteq> i\<Gamma> \<sigma> i" and
    complete_partition1: "\<forall>i. \<exists>k<n. \<exists>j. w\<iota> (ps ! k) j = i\<iota> \<sigma> i \<and> w\<tau> (ps ! k) j = i\<tau> \<sigma> i" and
    complete_partition2: "\<forall>i. \<forall>f \<in> i\<Gamma> \<sigma> i. \<exists>k<n. \<exists>j. w\<iota> (ps ! k) j = i\<iota> \<sigma> i \<and> w\<tau> (ps ! k) j = i\<tau> \<sigma> i \<and> f \<in> w\<Gamma> (ps ! k) j"

definition wpartition :: "nat \<Rightarrow> 'a itrace \<Rightarrow> 'a wtrace list set" where
  "wpartition n \<sigma> = {ps. wtrace_partition \<sigma> n ps}"

definition least_w\<iota> :: "'a wtrace \<Rightarrow> nat \<Rightarrow> nat" where
  "least_w\<iota> \<sigma> i0 = (LEAST i. i0 \<le> i \<and> (\<exists>j. i = w\<iota> \<sigma> j))"

definition w\<iota>_stream :: "'a wtrace \<Rightarrow> nat stream" where
  "w\<iota>_stream \<sigma> = siterate (least_w\<iota> \<sigma> \<circ> Suc) (least_w\<iota> \<sigma> 0)"

definition collapse_w :: "'a wtrace \<Rightarrow> nat \<Rightarrow> 'a set" where
  "collapse_w \<sigma> i = (\<Union>{d. \<exists>j. i = w\<iota> \<sigma> j \<and> d = w\<Gamma> \<sigma> j})"

definition ts_of_w :: "'a wtrace \<Rightarrow> nat \<Rightarrow> nat" where
  "ts_of_w \<sigma> i = w\<tau> \<sigma> (LEAST j. i = w\<iota> \<sigma> j)"

lemma ex_w\<iota>_ge: "\<exists>x\<ge>i. \<exists>j. x = w\<iota> \<sigma> j"
  apply (transfer fixing: i)
  apply (clarsimp simp: wtracep_def)
  apply (drule sincreasing_ex_greater[where j=0 and x=i])
  by (metis gt_ex le_trans less_imp_le_nat smap_alt)

lemma le_least_w\<iota>: "i \<le> least_w\<iota> \<sigma> i"
  unfolding least_w\<iota>_def
  apply (subgoal_tac "i \<le> (LEAST x. i \<le> x \<and> (\<exists>j. x = w\<iota> \<sigma> j)) \<and>
          (\<exists>j. (LEAST x. i \<le> x \<and> (\<exists>j. x = w\<iota> \<sigma> j)) = w\<iota> \<sigma> j)")
   apply (erule conjunct1)
  apply (rule LeastI_ex)
  by (rule ex_w\<iota>_ge)

lemma ssorted_w\<iota>_stream: "ssorted (w\<iota>_stream \<sigma>)"
  by (auto simp: w\<iota>_stream_def intro!: ssorted_siterate order_trans[OF _ le_least_w\<iota>])

lemma sincreasing_w\<iota>_stream: "sincreasing (w\<iota>_stream \<sigma>)"
  by (auto simp: w\<iota>_stream_def intro!: sincreasing_siterate order.strict_trans2[OF _ le_least_w\<iota>])

lemma mono_ts_of_w: "i \<le> j \<Longrightarrow> \<exists>k. i = w\<iota> \<sigma> k \<Longrightarrow> \<exists>k. j = w\<iota> \<sigma> k \<Longrightarrow> ts_of_w \<sigma> i \<le> ts_of_w \<sigma> j"
  unfolding ts_of_w_def
  apply (transfer fixing: i j)
  subgoal for \<sigma>
    apply (clarsimp simp: wtracep_def)
    apply (drule spec2[where P="\<lambda>i j. _ i j \<longrightarrow> ts (_ i) \<le> _ j"])
    apply (erule mp)
    by (metis (mono_tags, lifting) LeastI)
  done

lemma ex_snth_w\<iota>_stream: "\<exists>k. w\<iota>_stream \<sigma> !! i = w\<iota> \<sigma> k"
  apply (induction i)
   apply (auto simp add: w\<iota>_stream_def least_w\<iota>_def simp del: snth.simps intro: LeastI)
  subgoal for i k
    apply (insert LeastI_ex[where P="\<lambda>i. Suc (w\<iota> \<sigma> k) \<le> i \<and> (\<exists>j. i = w\<iota> \<sigma> j)"])
    apply (drule meta_mp)
     apply (rule ex_w\<iota>_ge)
    apply (erule conjunct2)
    done
  done

lemma le_w\<iota>_le_w\<tau>: "w\<iota> \<sigma> i \<le> w\<iota> \<sigma> j \<Longrightarrow> w\<tau> \<sigma> i \<le> w\<tau> \<sigma> j"
  by transfer (simp add: wtracep_def)

lemma w\<tau>_increasing: "\<exists>j>i. w\<tau> \<sigma> i < w\<tau> \<sigma> j"
  by transfer (simp add: wtracep_def sincreasing_def)

lift_definition reorder_w :: "'a wtrace \<Rightarrow> 'a itrace" is
  "\<lambda>\<sigma>. smap (\<lambda>i. \<lparr>db=collapse_w \<sigma> i, ts=ts_of_w \<sigma> i, idx=i\<rparr>) (w\<iota>_stream \<sigma>)"
  apply (simp add: stream.map_comp stream.map_ident ssorted_w\<iota>_stream cong: stream.map_cong)
  subgoal for \<sigma>
    apply safe
    subgoal
      apply (clarsimp simp: sincreasing_def ts_of_w_def)
      subgoal for i
        apply (insert w\<tau>_increasing[of "LEAST j. w\<iota>_stream \<sigma> !! i = w\<iota> \<sigma> j" \<sigma>])
        apply clarify
        subgoal for j
          apply (insert sincreasing_w\<iota>_stream[THEN sincreasing_ex_greater, of "Suc i" "w\<iota> \<sigma> j" \<sigma>])
          apply (clarsimp simp: Suc_le_eq)
          subgoal for k
            apply (rule exI[where x=k])
            apply simp
            apply (subgoal_tac "w\<tau> \<sigma> j \<le> w\<tau> \<sigma> (LEAST j. w\<iota>_stream \<sigma> !! k = w\<iota> \<sigma> j)")
             apply (erule (1) order.strict_trans2)
            apply (rule le_w\<iota>_le_w\<tau>)
            by (metis (mono_tags, lifting) LeastI_ex ex_snth_w\<iota>_stream le_less_linear less_not_sym)
          done
        done
      done
    subgoal for i j
      apply (erule mono_ts_of_w)
       apply (rule ex_snth_w\<iota>_stream)+
      done
    done
  done

lemma wpartition_split: "wpartition n \<le> partition n !\<then> mapM_set relax_order"
  apply (auto simp: le_fun_def strong_kleisli_def partition_def)
  subgoal sorry
  subgoal for \<sigma> ps
    apply (rule exI[where x="map reorder_w ps"])
    apply (auto simp: wpartition_def wtrace_partition_def
        itrace_partition_def in_mapM_set_iff relax_order_def relaxed_order_def)
    sorry (* TODO *)
  done

lemma wpartition_split': "partition n \<circ>\<then> mapM_set relax_order \<le> wpartition n"
  by (auto simp: le_fun_def kleisli_set_def partition_def itrace_partition_def
      in_mapM_set_iff relax_order_def relaxed_order_def list_all2_conv_all_nth
      wpartition_def wtrace_partition_def) metis+

lemma wpartition_eq: "wpartition n = partition n !\<then> mapM_set relax_order"
  apply (rule antisym)
   apply (rule wpartition_split)
  apply (rule order_trans)
   apply (rule strong_kleisli_le_kleisli_set)
  apply (rule wpartition_split')
  done


lemma length_islice[simp]: "length (islice f xs \<sigma>) = length xs"
  by (simp add: islice_def)

lemma in_partition_lengthD: "ps \<in> partition n \<sigma> \<Longrightarrow> length ps = n \<and> n > 0"
  by (simp add: partition_def itrace_partition_def)

lemma foldr_const_max: "foldr (\<lambda>x. max c) xs (a::_::linorder) = (if xs = [] then a else max c a)"
  by (induction xs) simp_all

lemma i\<tau>_islice[simp]: "k < length xs \<Longrightarrow> i\<tau> (islice f xs \<sigma> ! k) j = i\<tau> \<sigma> j"
  by (simp add: islice_def)

lemma i\<iota>_islice[simp]: "k < length xs \<Longrightarrow> i\<iota> (islice f xs \<sigma> ! k) j = i\<iota> \<sigma> j"
  by (simp add: islice_def)

lemma i\<Gamma>_islice[simp]: "k < length xs \<Longrightarrow> i\<Gamma> (islice f xs \<sigma> ! k) j = f (xs ! k) (i\<Gamma> \<sigma> j)"
  by (simp add: islice_def)

lemma partition_islice_transpose:
  "partition n \<circ>\<then> determ (map (islice (\<inter>) xs)) \<circ>\<then> determ transpose \<le>
    determ (islice (\<inter>) xs) \<circ>\<then> mapM_set (partition n)"
  apply (clarsimp simp: le_fun_def kleisli_set_def in_mapM_set_iff Bex_def)
  apply (rule list_all2_all_nthI)
  subgoal 1 for \<sigma> ps
    apply (subgoal_tac "ps \<noteq> []")
     apply (simp add: length_transpose foldr_map foldr_const_max cong: foldr_cong)
    apply (drule in_partition_lengthD)
    apply clarsimp
    done
  subgoal for \<sigma> ps k
    apply (frule 1)
    apply (simp add: nth_transpose cong: map_cong)
    apply (auto simp: partition_def itrace_partition_def cong: conj_cong)
    by (meson le_infI2)
  done


locale mwtrace_partition =
  fixes \<sigma> :: "'a itrace" and n :: nat and \<sigma>' :: "'a mwtrace"
  assumes
    n_greater_0: "n > 0" and
    mworigins_eq_n: "mworigins \<sigma>' = {0..<n}" and
    sound_partition: "\<forall>j. \<exists>i. idx (mwnth \<sigma>' j) = i\<iota> \<sigma> i \<and> ts (mwnth \<sigma>' j) = i\<tau> \<sigma> i \<and> db (mwnth \<sigma>' j) \<subseteq> i\<Gamma> \<sigma> i" and
    complete_partition1: "\<forall>i. \<exists>j. idx (mwnth \<sigma>' j) = i\<iota> \<sigma> i \<and> ts (mwnth \<sigma>' j) = i\<tau> \<sigma> i" and
    complete_partition2: "\<forall>i. \<forall>f \<in> i\<Gamma> \<sigma> i. \<exists>j. idx (mwnth \<sigma>' j) = i\<iota> \<sigma> i \<and> ts (mwnth \<sigma>' j) = i\<tau> \<sigma> i \<and> f \<in> db (mwnth \<sigma>' j)"

definition mwpartition :: "nat \<Rightarrow> 'a itrace \<Rightarrow> 'a mwtrace set" where
  "mwpartition n \<sigma> = {\<sigma>'. mwtrace_partition \<sigma> n \<sigma>'}"

lemma ex_snth_sfilter_eq: "infinitely P s \<Longrightarrow> P (s !! i) \<Longrightarrow>
  \<exists>j. sfilter P s !! j = s !! i"
  apply (induction i arbitrary: s)
  subgoal for s
    by (cases s) (auto simp: sfilter_Stream intro!: exI[where x=0])
  subgoal for i s
    apply simp
    apply (drule meta_spec[where x="stl s"])
    apply (drule meta_mp)
     apply (simp add: infinitely_stl)
    apply (drule (1) meta_mp)
    by (metis sfilter_stl_cases snth.simps(2))
  done

lemma mwproject_eqD: "mwproject k \<sigma>' = \<sigma> \<Longrightarrow> k \<in> mworigins \<sigma>' \<Longrightarrow>
  (\<forall>j. origin (mwnth \<sigma>' j) = k \<longrightarrow> (\<exists>i. idx (mwnth \<sigma>' j) = w\<iota> \<sigma> i \<and> ts (mwnth \<sigma>' j) = w\<tau> \<sigma> i \<and> db (mwnth \<sigma>' j) = w\<Gamma> \<sigma> i)) \<and>
  (\<forall>i. \<exists>j. origin (mwnth \<sigma>' j) = k \<and> idx (mwnth \<sigma>' j) = w\<iota> \<sigma> i \<and> ts (mwnth \<sigma>' j) = w\<tau> \<sigma> i \<and> db (mwnth \<sigma>' j) = w\<Gamma> \<sigma> i)"
  apply (transfer fixing: k)
  apply (auto simp: wtsdb.defs)
  subgoal for \<sigma>' x j
    apply (insert ex_snth_sfilter_eq[of "\<lambda>y. origin y = origin x" \<sigma>' j])
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

lemma partition_relax_linearize: "partition n \<circ>\<then> mapM_set relax_order \<circ>\<then> linearize \<le> mwpartition n"
  apply (clarsimp simp: le_fun_def kleisli_set_def linearize_def partition_def
      itrace_partition_def in_mapM_set_iff list_all2_conv_all_nth relax_order_def relaxed_order_def
      mwpartition_def mwtrace_partition_def)
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


lemma mwpartition_least_idx: "\<sigma>' \<in> mwpartition n \<sigma> \<Longrightarrow> least_idx \<sigma>' 0 = i\<iota> \<sigma> 0"
  apply (clarsimp simp: mwpartition_def mwtrace_partition_def least_idx_def)
  apply (rule Least_equality)
   apply metis
  by (metis mono_i\<iota> zero_le)

lemma i\<iota>_eq_imp_i\<tau>_eq: "i\<iota> \<sigma> i = i\<iota> \<sigma> j \<Longrightarrow> i\<tau> \<sigma> i = i\<tau> \<sigma> j"
  by (transfer fixing: i j) (simp add: eq_iff)

lift_definition mwnext :: "'a mwtrace \<Rightarrow> 'a mwtrace" is "\<lambda>s. sfilter (\<lambda>x. idx (shd s) < idx x) s"
  oops

lemma stl_reorder_alt: "stl (reorder_alt \<sigma>) = reorder_alt (mwnext \<sigma>)"
  oops

lemma mwpartition_reorder': "mwpartition n \<circ>\<then> determ reorder' \<le> determ (collapse \<circ>> Rep_trace)"
  apply (clarsimp simp: le_fun_def kleisli_set_def collapse.rep_eq reorder'_eq_alt)
  subgoal for \<sigma> \<sigma>'
    apply (coinduction arbitrary: \<sigma> \<sigma>')
    apply safe
     apply (auto simp: reorder_alt_def collapse'_def
        collapse_idx_def idx_stream_def mwpartition_least_idx)[]
       apply (fastforce simp: mwpartition_def mwtrace_partition_def)
      apply (clarsimp simp: mwpartition_def mwtrace_partition_def)
      apply metis
    subgoal for \<sigma> \<sigma>'
      apply (clarsimp simp: mwpartition_def mwtrace_partition_def ts_of_idx_def)
      apply (insert LeastI_ex[where P="\<lambda>j. i\<iota> \<sigma> 0 = idx (mwnth \<sigma>' j)"])
      apply (drule meta_mp)
       apply metis
      apply (drule spec[where x="LEAST j. i\<iota> \<sigma> 0 = idx (mwnth \<sigma>' j)"])
      apply (auto intro!: i\<iota>_eq_imp_i\<tau>_eq)
      done
    sorry (* TODO *)
  done


definition tslice :: "('a \<Rightarrow> 'b set \<Rightarrow> 'c set) \<Rightarrow> 'a list \<Rightarrow> 'b trace \<Rightarrow> 'c trace list" where
  "tslice f xs \<sigma> = map2 (\<lambda>x. map_\<Gamma> (f x)) xs (replicate (length xs) \<sigma>)"

lemma next_i\<iota>_map_i\<Gamma>: "next_i\<iota> (map_i\<Gamma> f \<sigma>) = next_i\<iota> \<sigma>"
  by (transfer fixing: f) (simp add: fun_eq_iff next_i\<iota>_def)

lemma map_\<Gamma>_inter_collapse: "map_\<Gamma> (\<lambda>Y. X \<inter> Y) (collapse \<sigma>) = collapse (map_i\<Gamma> (\<lambda>Y. X \<inter> Y) \<sigma>)"
  apply (rule Rep_trace_inject[THEN iffD1])
  apply (simp add: map_\<Gamma>.rep_eq collapse.rep_eq collapse'_def stream.map_comp
      next_i\<iota>_map_i\<Gamma>)
  apply (rule stream.map_cong[OF refl])
  apply auto
  using i\<iota>_map_i\<Gamma> apply blast
  using i\<iota>_map_i\<Gamma> apply blast
  done

lemma islice_collapse_swap: "islice (\<inter>) xs \<circ>> map collapse = collapse \<circ>> tslice (\<inter>) xs"
  by (clarsimp simp: fun_eq_iff islice_def tslice_def split_beta
      map_\<Gamma>_inter_collapse zip_replicate2 cong: map_cong)

lemma not_Nil_in_transpose: "[] \<notin> set (transpose xss)"
  apply (clarsimp simp: in_set_conv_nth nth_transpose length_transpose filter_empty_conv)
  apply (induction xss)
   apply (auto simp: less_max_iff_disj)
  done


definition multi_source_slicer :: "'a set list \<Rightarrow> 'a wtrace list \<Rightarrow> 'a trace list set" where
  "multi_source_slicer xs = determ (map (wslice (\<inter>) xs)) !\<then> determ transpose !\<then>
    mapM_set linearize !\<then> determ (map (reorder' \<circ>> Abs_trace))"

theorem multi_source_correctness:
  assumes "0 < n"
  shows "wpartition n !\<then> multi_source_slicer xs = determ (collapse \<circ>> tslice (\<inter>) xs)"
proof (rule eq_determI)
  have lhs_eq: "wpartition n !\<then> multi_source_slicer xs = partition n !\<then> mapM_set relax_order !\<then>
    determ (map (wslice (\<inter>) xs)) !\<then> determ transpose !\<then> mapM_set linearize !\<then>
    determ (map (reorder' \<circ>> Abs_trace))" (is "_ = ?lhs")
    unfolding multi_source_slicer_def strong_kleisli_assoc wpartition_eq ..
  also have "\<dots> \<le> partition n \<circ>\<then> mapM_set relax_order \<circ>\<then>
    determ (map (wslice (\<inter>) xs)) \<circ>\<then> determ transpose \<circ>\<then> mapM_set linearize \<circ>\<then>
    determ (map (reorder' \<circ>> Abs_trace))"
    by (intro order_trans[OF strong_kleisli_le_kleisli_set] kleisli_set_mono order_refl)
  also have "\<dots> \<le> partition n \<circ>\<then> determ (map (islice (\<inter>) xs)) \<circ>\<then> mapM_set (mapM_set relax_order) \<circ>\<then>
    determ transpose \<circ>\<then> mapM_set linearize \<circ>\<then> determ (map (reorder' \<circ>> Abs_trace))"
  proof -
    have "mapM_set relax_order \<circ>\<then> determ (map (wslice (\<inter>) xs)) \<le> determ (map (islice (\<inter>) xs)) \<circ>\<then> mapM_set (mapM_set relax_order)"
      by (auto simp: fcomp_kleisli mapM_set_determ[symmetric] kleisli_mapM_set relax_order_wslice
          intro!: mapM_set_mono)
    then show ?thesis
      by (subst (2 6) kleisli_set_assoc) (intro kleisli_set_mono order_refl)
  qed
  also have "\<dots> \<le> partition n \<circ>\<then> determ (map (islice (\<inter>) xs)) \<circ>\<then> determ transpose \<circ>\<then>
    mapM_set (mapM_set relax_order) \<circ>\<then> mapM_set linearize \<circ>\<then> determ (map (reorder' \<circ>> Abs_trace))"
    by (subst (3 7) kleisli_set_assoc) (intro kleisli_set_mono mapM_mapM_transpose order_refl)
  also have "\<dots> \<le> determ (islice (\<inter>) xs) \<circ>\<then> mapM_set (partition n) \<circ>\<then>
    mapM_set (mapM_set relax_order) \<circ>\<then> mapM_set linearize \<circ>\<then> determ (map (reorder' \<circ>> Abs_trace))"
    by (subst (1 2 5) kleisli_set_assoc)
      (intro kleisli_set_mono[OF partition_islice_transpose] order_refl)
  also have "\<dots> \<le> determ (islice (\<inter>) xs) \<circ>\<then> mapM_set (mwpartition n) \<circ>\<then> determ (map (reorder' \<circ>> Abs_trace))"
    by (subst (2 3) kleisli_set_assoc)
      (auto simp: kleisli_mapM_set partition_relax_linearize intro!: kleisli_set_mono mapM_set_mono)
  also have "\<dots> \<le> determ (islice (\<inter>) xs) \<circ>\<then> determ (map collapse)"
    apply (rule kleisli_set_mono[OF order_refl])
    apply (unfold mapM_set_determ[symmetric] kleisli_mapM_set)
    apply (rule mapM_set_mono)
    apply (unfold determ_fcomp fcomp_kleisli kleisli_set_assoc)
    apply (rule order_trans[OF kleisli_set_mono])
      apply (rule mwpartition_reorder')
     apply (rule order_refl)
    apply (simp add: kleisli_set_def determ_def trace.Rep_trace_inverse)
    done
  also have "\<dots> \<le> determ (collapse \<circ>> tslice (\<inter>) xs)"
    by (simp add: fcomp_kleisli[symmetric] determ_fcomp[symmetric] islice_collapse_swap)
  finally show "wpartition n !\<then> multi_source_slicer xs \<le> determ (collapse \<circ>> tslice (\<inter>) xs)" .

  have "\<And>x. ?lhs x \<noteq> {}"
    apply (rule strong_kleisli_not_emptyI)
     apply (rule round_robin_partition[OF \<open>0 < n\<close>])
    apply (rule strong_kleisli_not_emptyI)
     apply (rule map_in_mapM_setI)
     apply (rule id_wtrace_relax_order)
    apply (rule strong_kleisli_not_emptyI)
     apply (subst in_determ_iff_eq, rule refl)
    apply (rule strong_kleisli_not_emptyI)
     apply (subst in_determ_iff_eq, rule refl)
    apply (rule strong_kleisli_not_emptyI)
     apply (rule map_in_mapM_setI)
     apply (rule linearize_rr_linearize)
     apply (auto simp: not_Nil_in_transpose)
    done
  then show "\<And>x. (wpartition n !\<then> multi_source_slicer xs) x \<noteq> {}"
    unfolding lhs_eq .
qed

lemma id_wtrace_le_relax: "determ id_wtrace \<le> relax_order"
  by (simp add: le_fun_def determ_def id_wtrace_relax_order)

corollary ordered_multi_source_correctness:
  assumes "0 < n"
  shows "partition n !\<then> determ (map id_wtrace) !\<then> multi_source_slicer xs =
    determ (collapse \<circ>> tslice (\<inter>) xs)" (is "?impl = ?spec")
proof (rule eq_determI)
  have 1: "\<And>a b c. b \<in> partition n a \<Longrightarrow> c \<in> mapM_set relax_order b \<Longrightarrow> multi_source_slicer xs c \<noteq> {}"
    using multi_source_correctness[OF assms, of xs]
    by (auto 0 3 simp add: determ_def fun_eq_iff wpartition_eq strong_kleisli_def
        split: if_splits)

  have "?impl \<le> partition n !\<then> mapM_set relax_order !\<then> multi_source_slicer xs"
    apply (rule le_funI)
    apply (rule strong_kleisli_mono[OF order_refl])
     apply (rule strong_kleisli_mono[OF _ order_refl])
      apply (auto simp: determ_def id_wtrace_relax_order intro!: map_in_mapM_setI)[]
     apply (erule (1) 1)
    apply (rule strong_kleisli_not_emptyI)
     apply (rule map_in_mapM_setI[OF id_wtrace_relax_order])
    apply (erule (1) 1)
    done
  then show "?impl \<le> ?spec"
    unfolding multi_source_correctness[OF assms, symmetric] wpartition_eq strong_kleisli_assoc .

  show "\<And>x. ?impl x \<noteq> {}"
    apply (rule strong_kleisli_not_emptyI)
     apply (rule round_robin_partition[OF assms])
    apply (rule strong_kleisli_not_emptyI)
     apply simp
    apply (erule 1)
    apply simp
    apply (rule map_in_mapM_setI[OF id_wtrace_relax_order])
    done
qed

corollary totally_ordered_multi_source:
  assumes "0 < n" and "itrace_partition (add_timepoints \<sigma>) n ps"
  shows "multi_source_slicer xs (map id_wtrace ps) = {tslice (\<inter>) xs \<sigma>}"
  using ordered_multi_source_correctness[OF assms(1), unfolded fun_eq_iff determ_def
      strong_kleisli_singleton_conv partition_def, simplified, rule_format, THEN conjunct2,
      rule_format, OF assms(2), unfolded collapse_add_timepoints] .

corollary watermarked_multi_source:
  assumes "0 < n" and "wtrace_partition \<sigma> n ps"
  shows "multi_source_slicer xs ps = {tslice (\<inter>) xs (collapse \<sigma>)}"
  using multi_source_correctness[OF assms(1), unfolded fun_eq_iff determ_def
      strong_kleisli_singleton_conv wpartition_def, simplified, rule_format, THEN conjunct2,
      rule_format, OF assms(2)] .

end
