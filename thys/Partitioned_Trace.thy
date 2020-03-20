theory Partitioned_Trace
  imports Generic_Trace
begin

locale partitioned_trace =
  fixes \<sigma> :: "'a set trace" and n :: nat and parts :: "('a set \<times> 'b) trace list" and
    g :: "nat \<Rightarrow> 'a \<Rightarrow> nat \<times> nat"
  defines "n \<equiv> length parts"
  assumes
    sound_timestamps: "\<forall>k<n. \<forall>j. \<exists>i. \<tau> \<sigma> i = \<tau> (parts ! k) j" and
    complete_timestamps: "\<forall>i. \<exists>k<n. \<exists>j. \<tau> \<sigma> i = \<tau> (parts ! k) j" and
    sound_facts: "\<forall>k<n. \<forall>j. \<forall>f \<in> fst (\<Gamma> (parts ! k) j). \<exists>i. g i f = (k, j) \<and> \<tau> \<sigma> i = \<tau> (parts ! k) j \<and> f \<in> \<Gamma> \<sigma> i" and
    complete_facts: "\<forall>i. \<forall>f \<in> \<Gamma> \<sigma> i. \<exists>k<n. \<exists>j. g i f = (k, j) \<and> \<tau> \<sigma> i = \<tau> (parts ! k) j \<and> f \<in> fst (\<Gamma> (parts ! k) j)"
begin

abbreviation "\<tau>_part k j \<equiv> \<tau> (parts ! k) j"
abbreviation "\<Gamma>_part k j \<equiv> fst (\<Gamma> (parts ! k) j)"
abbreviation "\<iota>_part k j \<equiv> snd (\<Gamma> (parts ! k) j)"

end

locale total_order_partition = partitioned_trace _ _ parts g
    for parts :: "('a set \<times> nat) trace list" and g +
  assumes
    sound_index1: "\<forall>k<n. \<forall>j. \<tau> \<sigma> (\<iota>_part k j) = \<tau>_part k j" and
    sound_index2: "\<forall>k<n. \<forall>j. \<forall>f \<in> \<Gamma>_part k j. g (\<iota>_part k j) f = (k, j) \<and> f \<in> \<Gamma> \<sigma> (\<iota>_part k j)" and
    complete_index: "\<forall>i. \<exists>k<n. \<exists>j. \<iota>_part k j = i" and
    mono_index: "\<forall>k<n. \<forall>j j'. j < j' \<longrightarrow> \<iota>_part k j < \<iota>_part k j'"

lemma ssorted_smap_mono: "mono f \<Longrightarrow> ssorted s \<Longrightarrow> ssorted (smap f s)"
  by (coinduction arbitrary: s) (auto elim: ssorted.cases monoE)

locale simple_total_order_partition =
  fixes \<sigma> :: "'a set trace" and n :: nat and h :: "nat \<times> nat \<Rightarrow> nat"
  assumes
    bij_betw_h: "bij_betw h ({0..<n} \<times> UNIV) UNIV" and
    mono_h: "\<forall>k. \<forall>j j'. j < j' \<longrightarrow> h (k, j) < h (k, j')"
begin

lemma mono_h': "h (k, j) < h (k, j') \<Longrightarrow> j < j'"
  by (metis less_asym' mono_h less_linear)

lift_definition part :: "nat \<Rightarrow> ('a set \<times> nat) trace" is
  "\<lambda>k. smap (\<lambda>j. let i = h (k, j) in ((\<Gamma> \<sigma> i, i), \<tau> \<sigma> i)) nats"
  apply (simp add: stream.map_comp comp_def Let_def)
  apply (rule conjI)
   apply (rule ssorted_smap_mono)
    apply (rule monoI)
    apply (rule \<tau>_mono)
    apply (erule le_less[THEN iffD1, THEN disjE])
     apply (rule mono_h[rule_format, THEN less_imp_le])
     apply simp+
  apply (clarsimp simp: sincreasing_def)
  subgoal for k j proof -
    obtain x where 1: "h (k, j) < x" and 2: "\<tau> \<sigma> (h (k, j)) < \<tau> \<sigma> x"
      using \<tau>_less_\<tau> by auto
    obtain j' where 3: "x \<le> h (k, j')"
      apply (induction x)
       apply simp
      by (metis Suc_leI lessI mono_h nat_less_le)
    with 1 have "h (k, j) < h (k, j')" by simp
    then have "j < j'" using mono_h' by simp
    with 2 3 show "\<exists>j'>j. \<tau> \<sigma> (h (k, j)) < \<tau> \<sigma> (h (k, j'))"
      using \<tau>_mono order_less_le_subst1 by fastforce
  qed
  done

lemma \<tau>_part: "\<tau> (part k) j = \<tau> \<sigma> (h (k, j))"
  by (transfer fixing: k j) (simp add: Let_def)

lemma \<Gamma>_part: "\<Gamma> (part k) j = (\<Gamma> \<sigma> (h (k, j)), h (k, j))"
  by (transfer fixing: k j) (simp add: Let_def)

definition parts where "parts = map part [0..<n]"

lemma length_parts[simp]: "length parts = n"
  by (simp add: parts_def)

lemma nth_parts[simp]: "k < n \<Longrightarrow> parts ! k = part k"
  by (simp add: parts_def)

end

lemma bij_betwE2: "bij_betw f A B \<Longrightarrow> y \<in> B \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> y = f x \<Longrightarrow> P) \<Longrightarrow> P"
  using bij_betw_apply bij_betw_inv_into bij_betw_inv_into_right by fastforce

sublocale simple_total_order_partition \<subseteq> total_order_partition \<sigma> n parts "\<lambda>i _. inv_into ({0..<n} \<times> UNIV) h i"
   apply unfold_locales
          apply (simp_all add: \<tau>_part \<Gamma>_part cong: conj_cong)
        apply auto[]
       apply clarify
  subgoal for i
    by (rule bij_betwE2[where y=i, OF bij_betw_h]) auto
      apply clarify
  subgoal for k j f
    by (rule exI[where x="h (k, j)"])
      (simp_all add: bij_betw_inv_into_left[OF bij_betw_h])
     apply clarify
  subgoal for i f
    apply (insert inv_into_into[of i h "{0..<n} \<times> UNIV"])
    apply (drule meta_mp)
    using bij_betw_h bij_betw_imp_surj_on apply force
    apply (auto; drule sym, simp)
     apply (auto simp: bij_betw_inv_into_right[OF bij_betw_h])
    done
    apply (auto simp: bij_betw_inv_into_left[OF bij_betw_h])[]
   apply clarify
  subgoal for i
    by (rule bij_betwE2[where y=i, OF bij_betw_h]) auto
  using mono_h by simp

end
