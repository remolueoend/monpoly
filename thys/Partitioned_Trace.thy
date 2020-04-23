theory Partitioned_Trace
  imports Trace "HOL-Library.Monad_Syntax"
begin

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

lemma collapse_timepoints[simp]: "collapse (add_timepoints \<sigma>) = \<sigma>"
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

typedef 'a wtrace = "{s :: 'a wtsdb stream.
  ssorted (smap wmark s) \<and> sincreasing (smap ts s) \<and>
  (\<forall>i j. idx (s !! i) \<le> idx (s !! j) \<longrightarrow> ts (s !! i) \<le> ts (s !! j)) \<and>
  (\<forall>i. \<forall>j\<ge>i. wmark (s !! i) \<le> idx (s !! j))}"
  by (rule exI[where x="smap (\<lambda>x. \<lparr>db={}, ts=x, idx=x, wmark=x\<rparr>) nats"])
    (auto simp: stream.map_comp stream.map_ident cong: stream.map_cong)

setup_lifting type_definition_wtrace

lift_definition w\<Gamma> :: "'a wtrace \<Rightarrow> nat \<Rightarrow> 'a set" is "\<lambda>s i. db (s !! i)" .
lift_definition w\<tau> :: "'a wtrace \<Rightarrow> nat \<Rightarrow> nat" is "\<lambda>s i. ts (s !! i)" .
lift_definition w\<iota> :: "'a wtrace \<Rightarrow> nat \<Rightarrow> nat" is "\<lambda>s i. idx (s !! i)" .
lift_definition w\<beta> :: "'a wtrace \<Rightarrow> nat \<Rightarrow> nat" is "\<lambda>s i. wmark (s !! i)" .

lift_definition map_w\<Gamma> :: "('a set \<Rightarrow> 'b set) \<Rightarrow> 'a wtrace \<Rightarrow> 'b wtrace" is
  "\<lambda>f. smap (\<lambda>x. \<lparr>db = f (db x), ts = ts x, idx = idx x, wmark = wmark x\<rparr>)"
  by (simp add: stream.map_comp cong: stream.map_cong)

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
  by (simp add: stream.map_comp ssorted_iff_mono cong: stream.map_cong)

lemma id_wtrace_relax_order: "id_wtrace \<sigma> \<in> relax_order \<sigma>"
  by (simp add: relax_order_def relaxed_order_def) (transfer; auto)+


lemma in_listset_alt: "xs \<in> listset As \<longleftrightarrow> list_all2 (\<in>) xs As"
  by (induction As arbitrary: xs) (auto simp: set_Cons_def list_all2_Cons2)

lemma map_w\<Gamma>_relax_order: "\<sigma>' \<in> relax_order \<sigma> \<Longrightarrow> map_w\<Gamma> f \<sigma>' \<in> relax_order (map_i\<Gamma> f \<sigma>)"
  by (fastforce simp: relax_order_def relaxed_order_def)

lemma relax_order_slice: "relax_order \<sigma> \<bind> (\<lambda>\<sigma>'. {map2 (\<lambda>x. map_w\<Gamma> (f x)) xs (replicate n \<sigma>')}) \<subseteq>
  listset (map relax_order (map2 (\<lambda>x. map_i\<Gamma> (f x)) xs (replicate n \<sigma>)))"
  by (auto simp: split_beta bind_singleton_conv_image list.rel_map in_listset_alt in_set_zip
      cong: map_cong intro!: list_all2I map_w\<Gamma>_relax_order)

end
