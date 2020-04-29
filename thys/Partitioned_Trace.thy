theory Partitioned_Trace
  imports Trace "HOL-Library.BNF_Corec" "HOL-Library.DAList"
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

(* TODO(JS): Show that linearize \<sigma> is not empty. *)


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

lemma sincreasing_ex_greater: "sincreasing s \<Longrightarrow> \<exists>i. (x::nat) < s !! i"
  unfolding sincreasing_def
  apply (induction x)
   apply simp_all
  using gr_implies_not0 apply blast
  using Suc_lessI by fastforce

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

lemma snth_sfilter: "infinitely P s \<Longrightarrow> \<exists>j. sfilter P s !! i = s !! j \<and> P (s !! j)"
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

lemma ex_wmark_greater: "k \<in> mworigins \<sigma> \<Longrightarrow> \<exists>i. origin (mwnth \<sigma> i) = k \<and> w < wmark (mwnth \<sigma> i)"
  apply (transfer fixing: k w)
  apply (clarsimp simp: wtracep_def)
  subgoal for \<sigma> x
    apply (drule (1) bspec)
    apply clarify
    apply (drule sincreasing_ex_greater[where s="smap wmark _" and x=w])
    apply clarify
    subgoal for i
      apply (frule snth_sfilter[where i=i])
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
    then have wmarks_st': "wmarks st' = ..."
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
      also have "... \<le> the (DAList.lookup (wmarks st') k)"
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

corecursive reorder' :: "'a reorder_state \<Rightarrow> ('a set \<times> nat) stream" where
  "reorder' st = (let (xs, st') = reorder_step st in
    case xs of
      [] \<Rightarrow> reorder' st'
    | x # xs' \<Rightarrow> x ## xs' @- reorder' st')"
  by (relation "measure reorder_variant") (simp_all add: reorder_termination)

lift_definition init_reorder_state :: "'a mwtrace \<Rightarrow> 'a reorder_state" is
  "\<lambda>\<sigma>. (\<lparr>wmarks = Finite_Set.fold (\<lambda>k. DAList.update k 0) DAList.empty (mworigins \<sigma>),
    buffer = DAList.empty\<rparr>, \<sigma>)"
  sorry

lift_definition reorder :: "'a mwtrace \<Rightarrow> 'a trace" is "\<lambda>\<sigma>. reorder' (init_reorder_state \<sigma>)"
  sorry

end
