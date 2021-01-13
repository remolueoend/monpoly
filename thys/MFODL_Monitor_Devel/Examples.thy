(*<*)
theory Examples
  imports Monitor_Impl IEEE_Floating_Point.Conversion_IEEE_Float
begin
(*>*)

ML \<open>
structure TermOfDouble =
struct
fun term_of_double x =
  (case Real.class x of
    IEEEReal.NAN => @{const nan}
  | IEEEReal.INF => if Real.signBit x then @{term "- infinity"} else @{term "infinity"}
  | _ => case Real.toManExp x of {man = m, exp = e} =>
    let
      val i = Real.floor (Real.* (m, Math.pow (2.0, 53.0)));
      val e = IntInf.- (e, 53);
    in
      @{term abs_double} $ (@{term "of_finite_Float :: Float.float \<Rightarrow> (11, 52) float"} $ 
        (@{term Float} $ HOLogic.mk_number @{typ int} i $ HOLogic.mk_number @{typ int} e))
    end);
end;

structure TermOfString8 =
struct
fun term_of_string8 x =
  @{term Abs_string8} $ HOLogic.mk_string x;
end;
\<close>

declare [[code drop: "Code_Evaluation.term_of :: double \<Rightarrow> _"]]
declare [[code drop: "Code_Evaluation.term_of :: string8 \<Rightarrow> _"]]

code_printing
  constant "Code_Evaluation.term_of :: double \<Rightarrow> term" \<rightharpoonup> (Eval) "TermOfDouble.term'_of'_double"
| constant "Code_Evaluation.term_of :: string8 \<Rightarrow> term" \<rightharpoonup> (Eval) "TermOfString8.term'_of'_string8"



section \<open>Examples\<close>

abbreviation "TT \<equiv> Formula.Eq (Formula.Const (EInt 0)) (Formula.Const (EInt 0))"
abbreviation "Eventually I \<psi> \<equiv> Formula.Until TT I \<psi>"

context includes string8.lifting begin
lift_definition p :: string8 is "''p''" .
lift_definition A :: string8 is "''A''" .
lift_definition B :: string8 is "''B''" .
end

declare [[code drop: p A]]

code_printing
  code_module ConcreteStrings \<rightharpoonup> (Eval)
\<open>
signature CONCRETESTRINGS = sig
val p : string;
val a : string;
val b : string
end
structure ConcreteStrings : CONCRETESTRINGS = struct
val p = "p";
val a = "A";
val b = "B";
end
\<close>

code_printing
  constant p \<rightharpoonup> (Eval) "ConcreteStrings.p"
  | constant A \<rightharpoonup> (Eval) "ConcreteStrings.a"
| constant B \<rightharpoonup> (Eval) "ConcreteStrings.b"

definition "\<phi>\<^sub>e\<^sub>x = Formula.Let p (Eventually (interval 0 10) (Formula.Pred A [Formula.Var 0]))
  (Formula.Pred p [Formula.Var 0])"
definition "\<phi>\<^sub>e\<^sub>x\<^sub>2 = Formula.Let p (Formula.And (Eventually (interval 0 10) (Formula.Pred B [Formula.Var 0])) (Eventually (interval 0 10) (Formula.Pred A [Formula.Var 0])))
  (Formula.Pred p [Formula.Var 0])"

lemma "mmonitorable \<phi>\<^sub>e\<^sub>x" by eval
lemma "mmonitorable \<phi>\<^sub>e\<^sub>x\<^sub>2" by eval

definition "s0 = minit \<phi>\<^sub>e\<^sub>x"
definition "m1 = mstep (Mapping.update A [{[EInt 0], [EInt 1]}] Mapping.empty, 1) s0"
definition "m2 = mstep (Mapping.empty, 2) (snd m1)"
definition "m3 = mstep (Mapping.update A [{[EInt 2]}] Mapping.empty, 2) (snd m2)"
definition "m4 = mstep (Mapping.update A [{[EInt 5]}] Mapping.empty, 12) (snd m3)"
definition "m5 = mstep (Mapping.update A [{[EInt 6]}] Mapping.empty, 13) (snd m4)"

value s0
value m1
value m2
value m3
value m4
value m5

(*<*)
end
(*>*)
