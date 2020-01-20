(*<*)
theory Event_Data
  imports
    "HOL-Library.Char_ord"
    "HOL-Library.Extended_Nat"
    Code_Double
    Deriving.Derive
    Containers.Set_Impl
begin
(*>*)

derive (eq) ceq enat

instantiation enat :: ccompare begin
definition ccompare_enat :: "enat comparator option" where
  "ccompare_enat = Some (\<lambda>x y. if x = y then order.Eq else if x < y then order.Lt else order.Gt)"

instance by intro_classes
    (auto simp: ccompare_enat_def split: if_splits intro!: comparator.intro)
end


datatype event_data = EInt int | EFloat double | EString string

derive (eq) ceq event_data
derive ccompare event_data

instantiation event_data :: ord
begin

fun less_eq_event_data where
  "EInt x \<le> EInt y \<longleftrightarrow> x \<le> y"
| "EInt x \<le> EFloat y \<longleftrightarrow> double_of_int x \<le> y"
| "EInt _ \<le> EString _ \<longleftrightarrow> False"
| "EFloat x \<le> EInt y \<longleftrightarrow> x \<le> double_of_int y"
| "EFloat x \<le> EFloat y \<longleftrightarrow> x \<le> y"
| "EFloat _ \<le> EString _ \<longleftrightarrow> False"
| "EString x \<le> EString y \<longleftrightarrow> lexordp_eq x y"
| "EString _ \<le> _ \<longleftrightarrow> False"

definition less_event_data :: "event_data \<Rightarrow> event_data \<Rightarrow> bool"  where
  "less_event_data x y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"

instance ..

end

instantiation event_data :: plus
begin

fun plus_event_data where
  "EInt x + EInt y = EInt (x + y)"
| "EInt x + EFloat y = EFloat (double_of_int x + y)"
| "EFloat x + EInt y = EFloat (x + double_of_int y)"
| "EFloat x + EFloat y = EFloat (x + y)"
| "(_::event_data) + _ = EFloat nan"

instance ..

end

definition flatten_multiset :: "('a::ccompare \<times> enat) set \<Rightarrow> 'a list" where
  "flatten_multiset M = concat (map (\<lambda>(x, c). replicate (the_enat c) x)
    (csorted_list_of_set M))"

definition sum_agg :: "event_data \<Rightarrow> (event_data \<times> enat) set \<Rightarrow> event_data" where
  "sum_agg y0 M = foldl plus y0 (flatten_multiset M)"

definition count_agg :: "(event_data \<times> enat) set \<Rightarrow> event_data" where
  "count_agg M = EInt (length (flatten_multiset M))"

primrec double_of_event_data :: "event_data \<Rightarrow> double" where
  "double_of_event_data (EInt x) = double_of_int x"
| "double_of_event_data (EFloat x) = x"
| "double_of_event_data (EString _) = nan"

definition average_agg :: "(event_data \<times> enat) set \<Rightarrow> event_data" where
  "average_agg M = EFloat (let xs = flatten_multiset M in case xs of
      [] \<Rightarrow> 0
    | _ \<Rightarrow> double_of_event_data (foldl plus (EInt 0) xs) / double_of_int (length xs))"

definition min_agg :: "event_data \<Rightarrow> (event_data \<times> enat) set \<Rightarrow> event_data" where
  "min_agg y0 M = (case flatten_multiset M of
    [] \<Rightarrow> y0
  | x # xs \<Rightarrow> foldl min x xs)"

definition max_agg :: "event_data \<Rightarrow> (event_data \<times> enat) set \<Rightarrow> event_data" where
  "max_agg y0 M = (case flatten_multiset M of
    [] \<Rightarrow> y0
  | x # xs \<Rightarrow> foldl max x xs)"

definition median_agg :: "(event_data \<times> enat) set \<Rightarrow> event_data" where
  "median_agg M = EFloat (let xs = flatten_multiset M; u = length xs in
    if u = 0 then 0 else
      let u' = u div 2 in
      if even u then
        (double_of_event_data (xs ! (u'-1)) + double_of_event_data (xs ! u') / double_of_int 2)
      else double_of_event_data (xs ! u'))"

(*<*)
end
(*>*)
