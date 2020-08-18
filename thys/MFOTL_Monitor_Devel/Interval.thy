(*<*)
theory Interval
  imports "HOL-Library.Extended_Nat" "HOL-Library.Product_Lexorder"
begin
(*>*)

section \<open>Intervals\<close>

typedef \<I> = "{(i :: nat, j :: enat). i \<le> j}"
  by (intro exI[of _ "(0, \<infinity>)"]) auto

setup_lifting type_definition_\<I>

lift_definition all :: \<I> is "(0, \<infinity>)" by simp
lift_definition left :: "\<I> \<Rightarrow> nat" is fst .
lift_definition right :: "\<I> \<Rightarrow> enat" is snd .
lift_definition point :: "nat \<Rightarrow> \<I>" is "\<lambda>n. (n, enat n)" by simp
lift_definition subtract :: "nat \<Rightarrow> \<I> \<Rightarrow> \<I>" is
  "\<lambda>n (i, j). (i - n, j - enat n)" by (auto simp: diff_enat_def split: enat.splits)
abbreviation mem where "mem n I \<equiv> (left I \<le> n \<and> n \<le> right I)"

lemma left_right: "left I \<le> right I"
  by transfer auto

lemma point_simps[simp]:
  "left (point n) = n"
  "right (point n) = n"
  by (transfer; auto)+

lemma subtract_simps[simp]:
  "left (subtract n I) = left I - n"
  "right (subtract n I) = right I - n"
  "subtract 0 I = I"
  "subtract x (point y) = point (y - x)"
  by (transfer; auto)+

definition interval :: "nat \<Rightarrow> enat \<Rightarrow> \<I>" where
  "interval l r = (if l \<le> r then Abs_\<I> (l, r) else undefined)"

lemma [code abstract]: "Rep_\<I> (interval l r) = (if l \<le> r then (l, r) else Rep_\<I> undefined)"
  unfolding interval_def using Abs_\<I>_inverse by simp

(*<*)
end
(*>*)