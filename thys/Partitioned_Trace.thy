theory Partitioned_Trace
  imports Trace "HOL-Library.BNF_Corec" "HOL-Library.DAList" "HOL-Library.Extended_Nat"
begin

notation fcomp (infixl "\<circ>>" 60)

definition determ :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b set" where
  "determ f = (\<lambda>x. {f x})"

lemma in_determ_iff_eq[simp]: "y \<in> determ f x \<longleftrightarrow> y = f x"
  by (simp add: determ_def)

definition kleisli_set :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('b \<Rightarrow> 'c set) \<Rightarrow> 'a \<Rightarrow> 'c set" where
  "kleisli_set f g = (\<lambda>x. Set.bind (f x) g)"

notation kleisli_set (infixl "\<circ>\<then>" 55)

lemma kleisli_set_assoc: "f \<circ>\<then> g \<circ>\<then> h = f \<circ>\<then> (g \<circ>\<then> h)"
  by (auto simp: kleisli_set_def Set.bind_def)

lemma determ_kleisli_set: "determ f \<circ>\<then> g = f \<circ>> g"
  by (auto simp: kleisli_set_def Set.bind_def determ_def)

lemma kleisli_set_mono: "f \<le> f' \<Longrightarrow> g \<le> g' \<Longrightarrow> f \<circ>\<then> g \<le> f' \<circ>\<then> g'"
  by (fastforce simp: le_fun_def kleisli_set_def Set.bind_def)

definition mapM_set :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a list \<Rightarrow> 'b list set" where
  "mapM_set f xs = listset (map f xs)"

lemma in_listset_iff: "xs \<in> listset As \<longleftrightarrow> list_all2 (\<in>) xs As"
  by (induction As arbitrary: xs) (auto simp: set_Cons_def list_all2_Cons2)

lemma in_mapM_set_iff: "xs \<in> mapM_set f ys \<longleftrightarrow> list_all2 (\<lambda>x y. x \<in> f y) xs ys"
  by (simp add: mapM_set_def in_listset_iff list.rel_map)

lemma mapM_set_mono: "f \<le> f' \<Longrightarrow> mapM_set f \<le> mapM_set f'"
  by (fastforce simp: le_fun_def in_mapM_set_iff elim!: list.rel_mono_strong)


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

lemma add_timepoints_collapse: "add_timepoints \<circ>> collapse = id"
proof
  fix \<sigma> :: "'a trace"
  have "collapse' i (add_timepoints \<sigma>) = sdrop i (Rep_trace \<sigma>)" for i
    by (coinduction arbitrary: i) (auto simp: collapse'_def snth_Rep_trace)
  then show "(add_timepoints \<circ>> collapse) \<sigma> = id \<sigma>"
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
  "wtracep s \<longleftrightarrow> ssorted (smap wmark s) \<and> sincreasing (smap ts s) \<and>
    (\<forall>i j. idx (s !! i) \<le> idx (s !! j) \<longrightarrow> ts (s !! i) \<le> ts (s !! j)) \<and>
    (\<forall>i. \<forall>j\<ge>i. wmark (s !! i) \<le> idx (s !! j))"

definition "dummy_wtrace = smap (\<lambda>x. \<lparr>db={}, ts=x, idx=x, wmark=x\<rparr>) nats"

lemma wtracep_dummy: "wtracep dummy_wtrace"
  by (auto simp: wtracep_def dummy_wtrace_def stream.map_comp stream.map_ident cong: stream.map_cong)

typedef 'a wtrace = "{s :: 'a wtsdb stream. wtracep s}"
  by (auto intro!: exI[where x=dummy_wtrace] wtracep_dummy)

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
  by (simp add: wtracep_def stream.map_comp ssorted_iff_mono cong: stream.map_cong)

lemma id_wtrace_relax_order: "id_wtrace \<sigma> \<in> relax_order \<sigma>"
  by (simp add: relax_order_def relaxed_order_def) (transfer; auto)+


definition islice :: "('a \<Rightarrow> 'b set \<Rightarrow> 'c set) \<Rightarrow> 'a list \<Rightarrow> 'b itrace \<Rightarrow> 'c itrace list" where
  "islice f xs \<sigma> = map2 (\<lambda>x. map_i\<Gamma> (f x)) xs (replicate (length xs) \<sigma>)"

definition wslice :: "('a \<Rightarrow> 'b set \<Rightarrow> 'c set) \<Rightarrow> 'a list \<Rightarrow> 'b wtrace \<Rightarrow> 'c wtrace list" where
  "wslice f xs \<sigma> = map2 (\<lambda>x. map_w\<Gamma> (f x)) xs (replicate (length xs) \<sigma>)"

lemma map_w\<Gamma>_relax_order: "\<sigma>' \<in> relax_order \<sigma> \<Longrightarrow> map_w\<Gamma> f \<sigma>' \<in> relax_order (map_i\<Gamma> f \<sigma>)"
  by (fastforce simp: relax_order_def relaxed_order_def)

lemma relax_order_wslice:
  "(relax_order \<circ>\<then> determ (wslice f xs)) \<le> (islice f xs \<circ>> mapM_set relax_order)"
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
  "(mapM_set (mapM_set f) \<circ>\<then> determ transpose) \<le> (transpose \<circ>> mapM_set (mapM_set f))"
  by (auto simp: le_fun_def kleisli_set_def in_mapM_set_iff intro!: list_all2_transposeI)


definition infinitely :: "('a \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> bool" where
  "infinitely P s \<longleftrightarrow> (\<forall>i. \<exists>j\<ge>i. P (s !! j))"

lemma infinitely_stl: "infinitely P (stl s) \<longleftrightarrow> infinitely P s"
  apply (auto simp: infinitely_def)
  apply (metis le_Suc_eq snth.simps(2))
  using Suc_le_D by fastforce

lemma sdrop_while_id_conv: "stream_all P s \<Longrightarrow> sdrop_while (Not \<circ> P) s = s"
  by (subst sdrop_while_sdrop_LEAST) simp_all

lemma sfilter_id_conv: "stream_all P s \<Longrightarrow> sfilter P s = s"
  by (coinduction arbitrary: s) (auto simp: sdrop_while_id_conv stl_sset)

record 'a mwtsdb = "'a wtsdb" + origin :: nat

typedef 'a mwtrace = "{s :: 'a mwtsdb stream.
  (\<forall>k \<in> origin ` sset s. infinitely (\<lambda>x. origin x = k) s \<and> wtracep (sfilter (\<lambda>x. origin x = k) s))}"
  apply (rule exI[where x="smap (\<lambda>x. \<lparr>db={}, ts=x, idx=x, wmark=x, origin=0\<rparr>) nats"])
  apply (auto simp: infinitely_def stream.set_map)
  apply (subst sfilter_id_conv)
   apply (simp add: stream.set_map)
  apply (auto simp: wtracep_def stream.map_comp stream.map_ident cong: stream.map_cong)
  done

setup_lifting type_definition_mwtrace

lemma wtracep_stlI: "wtracep s \<Longrightarrow> wtracep (stl s)"
  apply (auto simp: wtracep_def sincreasing_def elim: ssorted.cases)
    apply (metis Suc_leI Suc_le_D Suc_le_lessD less_Suc_eq_le snth.simps(2))
   apply (metis snth.simps(2))
  by force

lemma sfilter_stl_cases:
  obtains "P (shd s)" "sfilter P (stl s) = stl (sfilter P s)" |
    "\<not> P (shd s)" "sfilter P (stl s) = sfilter P s"
  by (cases s) (auto simp: sfilter_Stream)

lift_definition mwnth :: "'a mwtrace \<Rightarrow> nat \<Rightarrow> 'a mwtsdb" is snth .
lift_definition mwhd :: "'a mwtrace \<Rightarrow> 'a mwtsdb" is shd .
lift_definition mwtl :: "'a mwtrace \<Rightarrow> 'a mwtrace" is stl
  apply (auto simp: infinitely_stl stl_sset)
  subgoal for s x
    by (rule sfilter_stl_cases[of "\<lambda>y. origin y = origin x" s])
      (auto simp: stl_sset simp del: sfilter.simps intro!: wtracep_stlI)
  done

lemma wtracep_smap_truncate: "wtracep (smap wtsdb.truncate s) \<longleftrightarrow> wtracep s"
  by (simp add: wtracep_def stream.map_comp wtsdb.truncate_def cong: stream.map_cong)

lift_definition mwproject :: "nat \<Rightarrow> 'a mwtrace \<Rightarrow> 'a wtrace" is
  "\<lambda>k s. if k \<in> origin ` sset s then smap wtsdb.truncate (sfilter (\<lambda>x. origin x = k) s)
    else dummy_wtrace"
  by (simp add: wtracep_smap_truncate wtracep_dummy)

definition linearize :: "'a wtrace list \<Rightarrow> 'a mwtrace set" where
  "linearize \<sigma>s = {\<sigma>. \<sigma>s \<noteq> [] \<and> (\<forall>k < length \<sigma>s. mwproject k \<sigma> = \<sigma>s ! k)}"


record 'a reorder_state =
  wmarks :: "(nat, nat) alist"
  buffer :: "(nat \<times> ('a set \<times> nat)) list"

definition reorder_update :: "'a mwtsdb \<Rightarrow> 'a reorder_state \<Rightarrow> 'a reorder_state" where
  "reorder_update x st = \<lparr>wmarks = DAList.update (origin x) (wmark x) (wmarks st),
    buffer = AList.map_default (idx x) (db x, ts x) (\<lambda>(d, t). (d \<union> db x, t)) (buffer st)\<rparr>"

definition keys_of :: "('a, 'b) alist \<Rightarrow> 'a list" where
  "keys_of al = map fst (DAList.impl_of al)"

definition values_of :: "('a, 'b) alist \<Rightarrow> 'b list" where
  "values_of al = map snd (DAList.impl_of al)"

definition reorder_flush :: "'a reorder_state \<Rightarrow> ('a set \<times> nat) list \<times> 'a reorder_state" where
  "reorder_flush st = (let w = fold min (values_of (wmarks st)) \<infinity> in
    (map snd (takeWhile (\<lambda>x. fst x < w) (buffer st)), st\<lparr>buffer := dropWhile (\<lambda>x. fst x < w) (buffer st)\<rparr>))"

friend_of_corec shift :: "'a list \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
  "shift xs s = (case xs of [] \<Rightarrow> shd s | x # _ \<Rightarrow> x) ## (case xs of [] \<Rightarrow> stl s | _ # ys \<Rightarrow> shift ys s)"
  subgoal by (simp split: list.split)
  subgoal by transfer_prover
  done

fun reorder_variant :: "'a reorder_state \<times> 'a mwtrace \<Rightarrow> nat" where
  "reorder_variant (st, \<sigma>) = Inf {n. \<forall>k \<in> set (keys_of (wmarks st)). \<exists>i\<le>n.
    origin (mwnth \<sigma> i) = k \<and> fold min (values_of (wmarks st)) \<infinity> < wmark (mwnth \<sigma> i)}"

lemma wmarks_reorder: "wmarks (snd (reorder_flush (reorder_update x st))) =
  DAList.update (origin x) (wmark x) (wmarks st)"
  by (simp add: reorder_update_def reorder_flush_def Let_def)

lemma alist_update_fresh: "k \<notin> fst ` set xs \<Longrightarrow> AList.update k v xs = xs @ [(k, v)]"
  by (induction xs) auto

corecursive reorder :: "'a reorder_state \<Rightarrow> 'a mwtrace \<Rightarrow> ('a set \<times> nat) stream" where
  "reorder st \<sigma> = (let (xs, st') = reorder_flush (reorder_update (mwhd \<sigma>) st) in
    case xs of
      [] \<Rightarrow> reorder st' (mwtl \<sigma>)
    | x # xs' \<Rightarrow> x ## xs' @- reorder st' (mwtl \<sigma>))"
  apply (relation "measure reorder_variant")
   apply rule
  apply (simp add: wmarks_reorder)
  oops

end
