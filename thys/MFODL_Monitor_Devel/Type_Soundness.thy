theory Type_Soundness
  imports Typing
begin
context fixes 
undef_plus :: "event_data \<Rightarrow> event_data \<Rightarrow> event_data" 
assumes undef_plus_sound:  "\<And>x y. EInt x + EInt y = undef_plus (EInt x) (EInt y)" 
    "\<And> x y . EFloat x + EFloat y = undef_plus (EFloat x) (EFloat y)"
begin

primrec eval_trm' :: "Formula.env \<Rightarrow> Formula.trm \<Rightarrow> event_data" where
  "eval_trm' v (Var x) = v ! x"
| "eval_trm' v (Const x) = x"
| "eval_trm' v (Plus x y) = undef_plus (eval_trm' v x) ( eval_trm' v y)"
| "eval_trm' v (Minus x y) = eval_trm' v x - eval_trm' v y"
| "eval_trm' v (UMinus x) = - eval_trm' v x"
| "eval_trm' v (Mult x y) = eval_trm' v x * eval_trm' v y"
| "eval_trm' v (Div x y) = eval_trm' v x div eval_trm' v y"
| "eval_trm' v (Mod x y) = eval_trm' v x mod eval_trm' v y"
| "eval_trm' v (F2i x) = EInt (integer_of_event_data (eval_trm' v x))"
| "eval_trm' v (I2f x) = EFloat (double_of_event_data (eval_trm' v x))"

fun sat' :: "Formula.trace \<Rightarrow> (Formula.name \<rightharpoonup> nat \<Rightarrow> event_data list set) \<Rightarrow> Formula.env \<Rightarrow> nat \<Rightarrow> 't Formula.formula \<Rightarrow> bool" where
"sat' x = undefined"

end
end