theory Tree_List
  imports Order_Statistic_Tree
  "Containers.Set_Impl"
begin


typedef 'a treelist = "UNIV :: 'a list set" ..
setup_lifting type_definition_treelist



(* Lifting all required operations *)
lift_definition empty_treelist :: "'a treelist" is "[]" .
lift_definition insert_treelist :: "'a::linorder \<Rightarrow> 'a treelist \<Rightarrow> 'a treelist" is insort .
lift_definition get_treelist :: "'a::linorder treelist \<Rightarrow> nat \<Rightarrow> 'a" is "\<lambda>l n. (sort l) ! n" . 
lift_definition length_treelist :: "'a::linorder treelist \<Rightarrow> nat" is length .
lift_definition remove_treelist :: "'a::linorder \<Rightarrow> 'a treelist => 'a treelist" is del_list .
lift_definition mset_treelist :: "'a::linorder treelist \<Rightarrow> 'a multiset" is mset .
lift_definition unpack :: "'a::linorder treelist \<Rightarrow> 'a list" is id .
lift_definition set_treelist :: "'a::linorder treelist \<Rightarrow> 'a set" is set .
lift_definition sort_treelist :: "'a::linorder treelist \<Rightarrow> 'a treelist" is sort .
lift_definition sorted_treelist :: "'a::linorder treelist \<Rightarrow> bool" is sorted .
lift_definition cons_treelist :: "'a::linorder \<Rightarrow> 'a treelist \<Rightarrow> 'a treelist" is Cons .

lemma mset_treelist_insert:
  "mset_treelist (insert_treelist i t) = {#i#} + mset_treelist t"
  by (simp add: Sorting.mset_insort insert_treelist.rep_eq mset_treelist.rep_eq)

lemma mset_treelist_empty:
  "mset_treelist empty_treelist = {#}"
  by (simp add: empty_treelist_def mset_treelist.abs_eq)

lemma treelist_length_eq:
  "length_treelist x = length (unpack (sort_treelist x))" by transfer auto

lift_definition Collapse :: "'a::linorder wf_wbt \<Rightarrow> 'a treelist" is "inorder" .

code_datatype Collapse

derive (eq) ceq treelist

lemma empty_treelist_code[code]: "empty_treelist = Collapse empty_tree"
  by transfer simp

lemma insert_treelist_code[code]: "insert_treelist x (Collapse y) = Collapse (tree_insert x y)"
  by transfer (simp add: inorder_insert)

lemma sorted_sort_inv: "sorted xs \<Longrightarrow> sort xs = xs"
  by (simp add: sorted_sort_id)

lemma get_treelist_code[code]: "get_treelist (Collapse y) n = tree_select y n"
  by transfer (simp add: sorted_sort_inv valid_select_wbt)

lemma length_treelist_code[code]: "length_treelist (Collapse y) = tree_size y"
  by transfer simp

lemma remove_treelist_code[code]: "remove_treelist x (Collapse y) = Collapse (tree_remove x y)"
  by(transfer) (simp add: inorder_delete)

end