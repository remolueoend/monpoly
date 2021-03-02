(*<*)
theory Interval
  imports "HOL-Library.Extended_Nat" "HOL-Library.Product_Lexorder"
begin
(*>*)

section \<open>Intervals\<close>

definition upclosed :: "(nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "upclosed mem = (\<forall>l m. mem l \<longrightarrow> l \<le> m \<longrightarrow> mem m)"

definition downclosed :: "(nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "downclosed mem = (\<forall>m r. mem r \<longrightarrow> m \<le> r \<longrightarrow> mem m)"

typedef \<I> = "{(memL, memR, bounded).
  (\<exists>m. memL m \<and> memR m) \<and> upclosed memL \<and> downclosed memR \<and> (bounded \<longleftrightarrow> (\<exists>m. \<not> memR m))}"
  by (intro exI[of _ "(\<lambda>_. True, \<lambda>_. True, False)"]) (auto simp: upclosed_def downclosed_def)

setup_lifting type_definition_\<I>

lift_definition memL :: "\<I> \<Rightarrow> nat \<Rightarrow> bool" is fst .
lift_definition memR :: "\<I> \<Rightarrow> nat \<Rightarrow> bool" is "fst o snd" .
lift_definition bounded :: "\<I> \<Rightarrow> bool" is "snd o snd" .
abbreviation mem :: "\<I> \<Rightarrow> nat \<Rightarrow> bool" where "mem \<I> n \<equiv> memL \<I> n \<and> memR \<I> n"

lemma memL_mono[elim]: "memL I l \<Longrightarrow> l \<le> m \<Longrightarrow> memL I m"
  by transfer (auto simp: upclosed_def)
lemma memR_antimono[elim]: "memR I r \<Longrightarrow> m \<le> r \<Longrightarrow> memR I m"
  by transfer (auto simp: downclosed_def)
lemma memR_zero[simp]: "memR I 0"
  by transfer (auto simp: downclosed_def)
lemma memR_nonzeroD: "\<not> memR I t \<Longrightarrow> t > 0"
  by (erule contrapos_np) simp

lemma bounded_memR: "bounded I \<longleftrightarrow> (\<exists>m. \<not> memR I m)"
  by transfer auto

lift_definition all :: \<I> is "(\<lambda>_. True, \<lambda>_. True, False)" by (auto simp: upclosed_def downclosed_def)
lift_definition point :: "nat \<Rightarrow> \<I>" is "\<lambda>n. ((\<le>) n, (\<ge>) n, True)"
  by (auto simp: upclosed_def downclosed_def not_le)
lift_definition subtract :: "nat \<Rightarrow> \<I> \<Rightarrow> \<I>" is
  "\<lambda>n (memL, memR, b). (\<lambda>i. memL (i + n), \<lambda>i. i = 0 \<or> memR (i + n), b)"
    apply (auto simp: upclosed_def downclosed_def)
   apply (metis add.commute le_iff_add linear)
  by (metis le0 linorder_neqE_nat nat_le_iff_add not_less0)

lemma point_simps[simp]:
  "memL (point n) = (\<le>) n"
  "memR (point n) = (\<ge>) n"
  "bounded (point n) = True"
  by (transfer; auto)+

lemma subtract_simps[simp]:
  "subtract 0 I = I"
  "subtract x (point y) = point (y - x)"
  "memL (subtract x I) n = memL I (n + x)"
  "memR (subtract x I) n = (n = 0 \<or> memR I (n + x))"
  "bounded (subtract x I) = bounded I"
  by (transfer; auto simp: downclosed_def)+

lift_definition interval :: "nat \<Rightarrow> enat \<Rightarrow> \<I>" is
  "\<lambda>l. \<lambda>r. (if enat l \<le> r then (\<lambda>i. l \<le> i, \<lambda>i. enat i \<le> r, r \<noteq> \<infinity>) else (\<lambda>_. True, \<lambda>_. True, False))"
  using enat_iless
  by (auto simp: upclosed_def downclosed_def not_le order_subst2)

(*<*)
end
(*>*)