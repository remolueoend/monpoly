(*<*)
theory Examples
  imports Monitor_Code
begin
(*>*)

section \<open>Examples\<close>

abbreviation "Eventually I \<psi> \<equiv> Formula.Until Formula.TT I \<psi>"

definition "\<phi>\<^sub>e\<^sub>x = Formula.And_Not (Formula.Pred ''A'' [Formula.Var 0])
  (Eventually (interval 1 2) (Formula.Exists (Formula.Pred ''B'' [Formula.Var 1, Formula.Var 0])))"
(*
lemma "mmonitorable \<phi>\<^sub>e\<^sub>x" by eval
*)
text \<open>Offline monitoring:\<close>

lift_definition \<pi>\<^sub>e\<^sub>x :: "string Formula.prefix" is
  "[ ({(''A'', [''d'']), (''A'', [''e''])}, 1)
   , ({(''B'', [''d'', ''f''])}, 2)
   , ({(''B'', [''e'', ''f''])}, 5)
  ]"
  by simp

lemma "monitor \<phi>\<^sub>e\<^sub>x \<pi>\<^sub>e\<^sub>x = {(0, [Some ''e''])}" by eval

text \<open>Online monitoring:\<close>

definition "m1 = mstep ({(''A'', [''d'']), (''A'', [''e''])}, 1) (minit \<phi>\<^sub>e\<^sub>x)"
definition "m2 = mstep ({(''B'', [''d'', ''f''])}, 2) (snd m1)"
definition "m3 = mstep ({(''B'', [''e'', ''f''])}, 5) (snd m2)"

lemma "fst m1 = {}" by eval
lemma "fst m2 = {}" by eval
lemma "fst m3 = {(0, [Some ''e''])}" by eval

text \<open>Operation of the monitor:\<close>

value "minit \<phi>\<^sub>e\<^sub>x"
value "\<lparr>
  mstate_i = 0,
  mstate_m =
    MAnd (MPred ''A'' [Formula.Var 0]) False
     (MUntil True (MRel {[None]}) (interval 1 2) (MExists (MPred ''B'' [Formula.Var 1, Formula.Var 0]))
       ([], []) [] [])
     ([], []),
  mstate_n = 1\<rparr> :: char list mstate"

value "mstate_m (snd m1)"
value "MAnd (MPred ''A'' [Formula.Var 0]) False
  (MUntil True (MRel {[None]}) (interval 1 2) (MExists (MPred ''B'' [Formula.Var 1, Formula.Var 0]))
    ([], []) [] [(1, {[None]}, {})])
  ([{[Some ''d''], [Some ''e'']}], []) :: char list mformula"

value "mstate_m (snd m2)"
value "MAnd (MPred ''A'' [Formula.Var 0]) False
  (MUntil True (MRel {[None]}) (interval 1 2) (MExists (MPred ''B'' [Formula.Var 1, Formula.Var 0]))
   ([], []) [] [(1, {[None]}, {[Some ''d'']}), (2, {[None]}, {})])
  ([{[Some ''d''], [Some ''e'']}, {}], []) :: char list mformula"

value "mstate_m (snd m3)"
value "MAnd (MPred ''A'' [Formula.Var 0]) False
  (MUntil True (MRel {[None]}) (interval 1 2) (MExists (MPred ''B'' [Formula.Var 1, Formula.Var 0]))
    ([], []) [] [(5, {[None]}, {})])
  ([{}], []) :: char list mformula"

(*<*)
end
(*>*)
