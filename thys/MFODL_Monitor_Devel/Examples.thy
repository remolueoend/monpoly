(*<*)
theory Examples
  imports Monitor_Impl
begin
(*>*)

section \<open>Examples\<close>

abbreviation "TT \<equiv> Formula.Eq (Formula.Const (EInt 0)) (Formula.Const (EInt 0))"
abbreviation "Eventually I \<psi> \<equiv> Formula.Until TT I \<psi>"

abbreviation "p \<equiv> STR ''p''"
abbreviation "A \<equiv> STR ''A''"
abbreviation "B \<equiv> STR ''B''"

definition \<phi>\<^sub>e\<^sub>x :: "ty Formula.formula" where
  "\<phi>\<^sub>e\<^sub>x = Formula.Let p (Eventually (interval 0 10) (Formula.Pred A [Formula.Var 0]))
  (Formula.Pred p [Formula.Var 0])"

definition \<phi>\<^sub>e\<^sub>x\<^sub>2 :: "ty Formula.formula" where
  "\<phi>\<^sub>e\<^sub>x\<^sub>2 = Formula.Let p (Formula.And (Eventually (interval 0 10) (Formula.Pred B [Formula.Var 0])) (Eventually (interval 0 10) (Formula.Pred A [Formula.Var 0])))
  (Formula.Pred p [Formula.Var 0])"

lemma "mmonitorable \<phi>\<^sub>e\<^sub>x" by eval
lemma "mmonitorable \<phi>\<^sub>e\<^sub>x\<^sub>2" by eval

definition "s0 = minit \<phi>\<^sub>e\<^sub>x"
definition "m1 = mstep (Mapping.update (A, 1) [{[Some (EInt 0)], [Some (EInt 1)]}] Mapping.empty, 1) s0"
definition "m2 = mstep (Mapping.empty, 2) (snd m1)"
definition "m3 = mstep (Mapping.update (A, 1) [{[Some (EInt 2)]}] Mapping.empty, 2) (snd m2)"
definition "m4 = mstep (Mapping.update (A, 1) [{[Some (EInt 5)]}] Mapping.empty, 12) (snd m3)"
definition "m5 = mstep (Mapping.update (A, 1) [{[Some (EInt 6)]}] Mapping.empty, 13) (snd m4)"

value s0
value m1
value m2
value m3
value m4
value m5

(*<*)
end
(*>*)
