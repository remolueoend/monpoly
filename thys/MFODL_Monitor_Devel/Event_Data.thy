(*<*)
theory Event_Data
  imports
    "HOL-Library.Char_ord"
    Code_Double
    Deriving.Derive
begin
(*>*)

section \<open>Code adaptation for 8-bit strings\<close>

typedef string8 = "UNIV :: char list set" ..

setup_lifting type_definition_string8

instantiation string8 :: "{equal, linorder}"
begin

lift_definition equal_string8 :: "string8 \<Rightarrow> string8 \<Rightarrow> bool" is HOL.equal .
lift_definition less_eq_string8 :: "string8 \<Rightarrow> string8 \<Rightarrow> bool" is ord_class.lexordp_eq .
lift_definition less_string8 :: "string8 \<Rightarrow> string8 \<Rightarrow> bool" is ord_class.lexordp .

instance by intro_classes
    (transfer; auto simp: equal_eq lexordp_conv_lexordp_eq lexordp_eq_linear
      intro: lexordp_eq_refl lexordp_eq_trans lexordp_eq_antisym)+

end

lifting_forget string8.lifting

declare [[code drop: "HOL.equal :: string8 \<Rightarrow> _" "(\<le>) :: string8 \<Rightarrow> _" "(<) :: string8 \<Rightarrow> _"]]

code_printing
  type_constructor string8 \<rightharpoonup> (OCaml) "string"
  | constant "HOL.equal :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (OCaml) "Pervasives.(=)"
  | constant "(\<le>) :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (OCaml) "Pervasives.(<=)"
  | constant "(<) :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (OCaml) "Pervasives.(<)"

code_printing
  type_constructor string8 \<rightharpoonup> (Eval) "string"
  | constant "HOL.equal :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (Eval) infixl 6 "="
  | constant "(\<le>) :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (Eval) infixl 6 "<="
  | constant "(<) :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (Eval) infixl 6 "<"

derive (eq) ceq string8
derive (linorder) compare string8
derive (compare) ccompare string8


section \<open>Event parameters\<close>

definition div_to_zero :: "integer \<Rightarrow> integer \<Rightarrow> integer" where
  "div_to_zero x y = (let z = fst (Code_Numeral.divmod_abs x y) in
    if (x < 0) \<noteq> (y < 0) then - z else z)"

definition mod_to_zero :: "integer \<Rightarrow> integer \<Rightarrow> integer" where
  "mod_to_zero x y = (let z = snd (Code_Numeral.divmod_abs x y) in
    if x < 0 then - z else z)"

lemma "b \<noteq> 0 \<Longrightarrow> div_to_zero a b * b + mod_to_zero a b = a"
  unfolding div_to_zero_def mod_to_zero_def Let_def
  by (auto simp: minus_mod_eq_mult_div[symmetric] div_minus_right mod_minus_right ac_simps)


datatype event_data = EInt integer | EFloat double | EString string8

derive (eq) ceq event_data
derive ccompare event_data

instantiation event_data :: "{ord, plus, minus, uminus, times, divide, modulo}"
begin

fun less_eq_event_data where
  "EInt x \<le> EInt y \<longleftrightarrow> x \<le> y"
| "EInt x \<le> EFloat y \<longleftrightarrow> double_of_integer x \<le> y"
| "EInt _ \<le> EString _ \<longleftrightarrow> False"
| "EFloat x \<le> EInt y \<longleftrightarrow> x \<le> double_of_integer y"
| "EFloat x \<le> EFloat y \<longleftrightarrow> x \<le> y"
| "EFloat _ \<le> EString _ \<longleftrightarrow> False"
| "EString x \<le> EString y \<longleftrightarrow> x \<le> y"
| "EString _ \<le> _ \<longleftrightarrow> False"

definition less_event_data :: "event_data \<Rightarrow> event_data \<Rightarrow> bool"  where
  "less_event_data x y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"

fun plus_event_data where
  "EInt x + EInt y = EInt (x + y)"
| "EInt x + EFloat y = EFloat (double_of_integer x + y)"
| "EFloat x + EInt y = EFloat (x + double_of_integer y)"
| "EFloat x + EFloat y = EFloat (x + y)"
| "(_::event_data) + _ = EFloat nan"

fun minus_event_data where
  "EInt x - EInt y = EInt (x - y)"
| "EInt x - EFloat y = EFloat (double_of_integer x - y)"
| "EFloat x - EInt y = EFloat (x - double_of_integer y)"
| "EFloat x - EFloat y = EFloat (x - y)"
| "(_::event_data) - _ = EFloat nan"

fun uminus_event_data where
  "- EInt x = EInt (- x)"
| "- EFloat x = EFloat (- x)"
| "- (_::event_data) = EFloat nan"

fun times_event_data where
  "EInt x * EInt y = EInt (x * y)"
| "EInt x * EFloat y = EFloat (double_of_integer x * y)"
| "EFloat x * EInt y = EFloat (x * double_of_integer y)"
| "EFloat x * EFloat y = EFloat (x * y)"
| "(_::event_data) * _ = EFloat nan"

fun divide_event_data where
  "EInt x div EInt y = EInt (div_to_zero x y)"
| "EInt x div EFloat y = EFloat (double_of_integer x div y)"
| "EFloat x div EInt y = EFloat (x div double_of_integer y)"
| "EFloat x div EFloat y = EFloat (x div y)"
| "(_::event_data) div _ = EFloat nan"

fun modulo_event_data where
  "EInt x mod EInt y = EInt (mod_to_zero x y)"
| "(_::event_data) mod _ = EFloat nan"

instance ..

end

primrec integer_of_event_data :: "event_data \<Rightarrow> integer" where
  "integer_of_event_data (EInt x) = x"
| "integer_of_event_data (EFloat x) = integer_of_double x"
| "integer_of_event_data (EString _) = 0"

primrec double_of_event_data :: "event_data \<Rightarrow> double" where
  "double_of_event_data (EInt x) = double_of_integer x"
| "double_of_event_data (EFloat x) = x"
| "double_of_event_data (EString _) = nan"

(*<*)
end
(*>*)
