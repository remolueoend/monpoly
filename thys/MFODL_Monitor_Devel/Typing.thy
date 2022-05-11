(*<*)
theory Typing
  imports Safety
  Error_Monad
begin
(*>*)

section \<open>Typing\<close>

subsection \<open>Types\<close>

fun ty_of :: "event_data \<Rightarrow> ty" where
  "ty_of (EInt _) = TInt"
| "ty_of (EFloat _) = TFloat"
| "ty_of (EString _) = TString"


definition "numeric_ty = {TInt, TFloat}"

subsection \<open>Terms\<close>

type_synonym 'a option_err = "String.literal + 'a"
type_synonym tyenv = "nat \<Rightarrow> ty"

inductive wty_trm :: "tyenv \<Rightarrow> Formula.trm \<Rightarrow> ty \<Rightarrow> bool" ("(_)/ \<turnstile> (_) :: _" [50,50,50] 50)
  for E where
  Var: "E x = t \<Longrightarrow> E \<turnstile> Formula.Var x :: t"
| Const: "ty_of x = t \<Longrightarrow> E \<turnstile> Formula.Const x :: t"
| Plus: "E \<turnstile> x :: t \<Longrightarrow> E \<turnstile> y :: t \<Longrightarrow> t \<in> numeric_ty \<Longrightarrow> E \<turnstile> Formula.Plus x y :: t"
| Minus: "E \<turnstile> x :: t \<Longrightarrow> E \<turnstile> y :: t \<Longrightarrow> t \<in> numeric_ty \<Longrightarrow> E \<turnstile> Formula.Minus x y :: t"
| UMinus: "E \<turnstile> x :: t \<Longrightarrow> t \<in> numeric_ty \<Longrightarrow> E \<turnstile>  Formula.UMinus x :: t"
| Mult: "E \<turnstile> x :: t \<Longrightarrow> E \<turnstile> y :: t \<Longrightarrow> t \<in> numeric_ty \<Longrightarrow> E \<turnstile> Formula.Mult x y :: t"
| Div: "E \<turnstile> x :: t \<Longrightarrow> E \<turnstile> y :: t \<Longrightarrow> t \<in> numeric_ty \<Longrightarrow> E \<turnstile> Formula.Div x y :: t"
| Mod:"E \<turnstile> x :: TInt \<Longrightarrow> E \<turnstile> y :: TInt \<Longrightarrow> E \<turnstile> Formula.Mod x y :: TInt"
| F2i: "E \<turnstile> x ::  TFloat \<Longrightarrow> E \<turnstile> Formula.F2i x :: TInt"
| I2f: "E \<turnstile> x ::  TInt \<Longrightarrow> E \<turnstile> Formula.I2f x :: TFloat"


lemma ty_of_plus: "ty_of x = t \<Longrightarrow> ty_of y = t \<Longrightarrow> t \<in> numeric_ty \<Longrightarrow> ty_of (x + y) = t"
  by (cases x; cases y) (simp_all add: numeric_ty_def)

lemma ty_of_minus: "ty_of x = t \<Longrightarrow> ty_of y = t \<Longrightarrow> t \<in> numeric_ty \<Longrightarrow> ty_of (x - y) = t"
  by (cases x; cases y) (simp_all add: numeric_ty_def)

lemma ty_of_uminus: "ty_of x = t \<Longrightarrow> ty_of y = t \<Longrightarrow> t \<in> numeric_ty \<Longrightarrow> ty_of (-x) = t"
  by (cases x) (simp_all add: numeric_ty_def)
lemma ty_of_mult: "ty_of x = t \<Longrightarrow> ty_of y = t \<Longrightarrow> t \<in> numeric_ty \<Longrightarrow> ty_of (x * y) = t"
  by (cases x; cases y) (simp_all add: numeric_ty_def)

lemma ty_of_div: "ty_of x = t \<Longrightarrow> ty_of y = t \<Longrightarrow> t \<in> numeric_ty \<Longrightarrow> ty_of (x div y) = t"
  by (cases x; cases y) (simp_all add: numeric_ty_def)

lemma ty_of_mod: "ty_of x = TInt \<Longrightarrow> ty_of y = TInt \<Longrightarrow> ty_of (x mod y) = TInt"
  by (cases x; cases y) simp_all

lemma ty_of_eval_trm: "E \<turnstile> x :: t \<Longrightarrow> \<forall>y\<in>fv_trm x. ty_of (v ! y) = E y \<Longrightarrow> 
ty_of (Formula.eval_trm v x) = t"
  by (induction pred: wty_trm) (simp_all add: ty_of_plus ty_of_minus ty_of_uminus 
      ty_of_mult ty_of_div ty_of_mod)

lemma  value_of_eval_trm: "E \<turnstile> x :: TInt \<Longrightarrow> \<forall>y\<in>fv_trm x. ty_of (v ! y) = E y \<Longrightarrow> 
\<exists> z .(Formula.eval_trm v x) = EInt z"
"E \<turnstile> x :: TFloat \<Longrightarrow> \<forall>y\<in>fv_trm x. ty_of (v ! y) = E y \<Longrightarrow> 
\<exists> z .(Formula.eval_trm v x) = EFloat z"
"E \<turnstile> x :: TString \<Longrightarrow> \<forall>y\<in>fv_trm x. ty_of (v ! y) = E y \<Longrightarrow> 
\<exists> z .(Formula.eval_trm v x) = EString z"
  subgoal using ty_of_eval_trm by (cases "Formula.eval_trm v x") fastforce+
  subgoal using ty_of_eval_trm by (cases "Formula.eval_trm v x") fastforce+
  subgoal using ty_of_eval_trm by (cases "Formula.eval_trm v x") fastforce+
  done

lemma wty_trm_fv_cong:
  assumes "\<And>y. y \<in> fv_trm x \<Longrightarrow> E y = E' y"
  shows "E \<turnstile> x :: t \<longleftrightarrow> E' \<turnstile> x :: t"
proof -
  have "E \<turnstile> x :: t \<Longrightarrow> (\<And>y. y \<in> fv_trm x \<Longrightarrow> E y = E' y) \<Longrightarrow> E' \<turnstile> x :: t" for E E'
    by (induction pred: wty_trm) (auto intro: wty_trm.intros)
  with assms show ?thesis by auto
qed

lemma wty_trm_eq_binop:
  assumes 
    IH: "E \<turnstile> x1 :: t \<Longrightarrow> E' \<turnstile> x1 :: t \<Longrightarrow> \<forall>y. y \<in> fv_trm x1 \<longrightarrow> E y = E' y"
        "E \<turnstile> x2 :: t \<Longrightarrow> E' \<turnstile> x2 :: t \<Longrightarrow> \<forall>y. y \<in> fv_trm x2 \<longrightarrow> E y = E' y" and
    wty: "E \<turnstile> trm x1 x2 :: t" 
         "E' \<turnstile> trm x1 x2 :: t"  and
    binop: "trm \<in> {trm.Plus, trm.Minus, trm.Mult, trm.Div, trm.Mod}"
  shows "\<forall>y. y \<in> fv_trm (trm x1 x2) \<longrightarrow> E y = E' y"
proof -
   have wty:
    "E \<turnstile> x1 :: t" "E \<turnstile> x2 :: t"
    "E' \<turnstile> x1 :: t" "E' \<turnstile> x2 :: t"
    using binop wty by(auto intro!:wty_trm.intros elim:wty_trm.cases)
  show ?thesis using IH(1)[OF wty(1,3)] IH(2)[OF wty(2, 4)] binop by auto
qed

lemma wty_trm_eq:
  "E \<turnstile> x :: t \<Longrightarrow> E' \<turnstile> x :: t \<Longrightarrow> \<forall>y. y \<in> fv_trm x \<longrightarrow> E y = E' y"
proof(induction x arbitrary: t)
  case (Plus x1 x2)
  show ?case using wty_trm_eq_binop[where ?trm = trm.Plus, OF Plus] by blast
next
  case (Minus x1 x2)
  show ?case using wty_trm_eq_binop[where ?trm = trm.Minus, OF Minus] by blast
next
  case (UMinus x)
  then show ?case by(auto intro!:wty_trm.intros elim:wty_trm.cases)
next
  case (Mult x1 x2)
  show ?case using wty_trm_eq_binop[where ?trm = trm.Mult, OF Mult] by blast
next
  case (Div x1 x2)
  show ?case using wty_trm_eq_binop[where ?trm = trm.Div, OF Div] by blast
next
  case (Mod x1 x2)
  show ?case using wty_trm_eq_binop[where ?trm = trm.Mod, OF Mod] by blast
qed (auto intro!:wty_trm.intros elim:wty_trm.cases)


subsection \<open>Formulas\<close>

type_synonym sig = "(Formula.name \<times> nat) \<rightharpoonup> ty list"

definition wty_tuple :: "ty list \<Rightarrow> event_data list \<Rightarrow> bool" where
  "wty_tuple = list_all2 (\<lambda>t x. ty_of x = t)"

definition wty_event :: "sig \<Rightarrow> Formula.name \<Rightarrow> event_data list \<Rightarrow> bool" where
  "wty_event S p xs \<longleftrightarrow> (case S (p, length xs) of Some ts \<Rightarrow> wty_tuple ts xs | None \<Rightarrow> False)"

definition wty_envs :: "sig \<Rightarrow> Formula.trace \<Rightarrow> (Formula.name \<times> nat \<rightharpoonup> Formula.env \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "wty_envs S \<sigma> V \<longleftrightarrow> (\<forall>i.
    (\<forall>(p,xs) \<in> \<Gamma> \<sigma> i. (p, length xs) \<notin> dom V \<longrightarrow> wty_event S p xs) \<and>
    (\<forall>p xs. (((p, length xs) \<in> dom V \<and> the (V (p, length xs)) xs i) \<longrightarrow> wty_event S p xs)))"

abbreviation wty_trace :: "sig \<Rightarrow> Formula.trace \<Rightarrow> bool" where
  "wty_trace S \<sigma> \<equiv> wty_envs S \<sigma> Map.empty"

definition wty_db :: "sig \<Rightarrow> (Formula.name \<times> event_data list) set \<Rightarrow> bool" where
  "wty_db S db \<longleftrightarrow> (\<forall>(p, xs) \<in> db. wty_event S p xs)"

lift_definition wty_prefix :: "sig \<Rightarrow> Formula.prefix \<Rightarrow> bool" is
  "\<lambda>S \<pi>. \<forall>x\<in>set \<pi>. wty_db S (fst x)" .

lemma wty_pnil: "wty_prefix S pnil"
  by (transfer fixing: S) simp

lemma wty_psnoc: "wty_prefix S \<pi> \<Longrightarrow> wty_db S (fst x) \<Longrightarrow> last_ts \<pi> \<le> snd x \<Longrightarrow>
  wty_prefix S (psnoc \<pi> x)"
  by (transfer fixing: S x) simp

lemma wty_envs_\<Gamma>_D: "wty_envs S \<sigma> V \<Longrightarrow> (p, length xs) \<notin> dom V \<Longrightarrow> (p, xs) \<in> \<Gamma> \<sigma> i \<Longrightarrow> S (p, length xs) = Some ts \<Longrightarrow>
  wty_tuple ts xs"
  by (fastforce simp: wty_envs_def wty_event_def split: option.splits)

lemma wty_envs_V_D: "wty_envs S \<sigma> V \<Longrightarrow> (p, length xs) \<in> dom V \<Longrightarrow> the (V (p, length xs)) xs i \<Longrightarrow> S (p, length xs) = Some ts \<Longrightarrow>
  wty_tuple ts xs"
  by (fastforce simp: wty_envs_def wty_event_def split: option.splits)

declare regex.pred_mono[mono]

definition agg_env :: "tyenv \<Rightarrow> ty list \<Rightarrow> tyenv " where
"agg_env E tys =  (\<lambda>z. if z < length tys then tys ! z else E (z - length tys))"

fun t_res :: "Formula.agg_type \<Rightarrow> ty \<Rightarrow> ty" where
"t_res Formula.Agg_Sum t = t"
| "t_res Formula.Agg_Cnt _ = TInt"
| "t_res Formula.Agg_Avg _ = TFloat"
| "t_res agg_type.Agg_Med _ = TFloat "
| "t_res Formula.Agg_Min t = t"
| "t_res Formula.Agg_Max t = t"

fun agg_trm_type :: "Formula.agg_type \<Rightarrow> ty set" where
"agg_trm_type Formula.Agg_Sum = numeric_ty"
| "agg_trm_type Formula.Agg_Cnt = UNIV"
| "agg_trm_type Formula.Agg_Avg = numeric_ty"
| "agg_trm_type Formula.Agg_Med = numeric_ty"
| "agg_trm_type Formula.Agg_Min = UNIV"
| "agg_trm_type Formula.Agg_Max = UNIV"


inductive wty_formula :: "sig \<Rightarrow> tyenv \<Rightarrow> ty Formula.formula \<Rightarrow> bool" ("(_),/ (_)/ \<turnstile> (_)" [50,50,50] 50) where
  Pred: "S (p, length tms) = Some tys \<Longrightarrow> list_all2 (\<lambda>tm ty. E \<turnstile> tm :: ty) tms tys \<Longrightarrow> S, E \<turnstile> Formula.Pred p tms"
| Let: "S, E' \<turnstile> \<phi> \<Longrightarrow> S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E \<turnstile> \<psi> \<Longrightarrow> S, E \<turnstile> Formula.Let p \<phi> \<psi>"
| LetPast: "S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E' \<turnstile> \<phi> \<Longrightarrow> 
    S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E \<turnstile> \<psi> \<Longrightarrow> S, E \<turnstile> Formula.LetPast p \<phi> \<psi>"
| Eq: "E \<turnstile> x :: t \<Longrightarrow> E \<turnstile> y :: t \<Longrightarrow> S, E \<turnstile> Formula.Eq x y"
| Less: "E \<turnstile> x :: t \<Longrightarrow> E \<turnstile> y :: t \<Longrightarrow> S, E \<turnstile> Formula.Less x y"
| LessEq: "E \<turnstile> x :: t \<Longrightarrow> E \<turnstile> y :: t \<Longrightarrow> S, E \<turnstile> Formula.LessEq x y"
| Neg: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> Formula.Neg \<phi>"
| Or: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> \<psi> \<Longrightarrow> S, E \<turnstile> Formula.Or \<phi> \<psi>"
| And: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> \<psi> \<Longrightarrow> S, E \<turnstile> Formula.And \<phi> \<psi>" 
| Ands: "\<forall>\<phi> \<in> set \<phi>s. S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> Formula.Ands \<phi>s"
| Exists: "S, case_nat t E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> Formula.Exists t \<phi>"
| Agg: "E y = t_res agg_type t \<Longrightarrow> agg_env E tys  \<turnstile> f :: t \<Longrightarrow> S, agg_env E tys \<turnstile> \<phi>  \<Longrightarrow>
   t \<in> agg_trm_type agg_type \<Longrightarrow> d = t_res agg_type t \<Longrightarrow>
          S, E \<turnstile> Formula.Agg y (agg_type, d) tys f \<phi>"
| Prev: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> Formula.Prev \<I> \<phi>"
| Next: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> Formula.Next \<I> \<phi>"
| Since: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> \<psi> \<Longrightarrow> S, E \<turnstile> Formula.Since \<phi> \<I> \<psi>" 
| Until: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> \<psi> \<Longrightarrow> S, E \<turnstile> Formula.Until \<phi> \<I> \<psi>" 
| MatchP: "Regex.pred_regex (\<lambda>\<phi>. S, E \<turnstile> \<phi>) r \<Longrightarrow> S, E \<turnstile> Formula.MatchP I r"
| MatchF: "Regex.pred_regex (\<lambda>\<phi>. S, E \<turnstile> \<phi>) r \<Longrightarrow> S, E \<turnstile> Formula.MatchF I r"
| TP: "E \<turnstile> t :: TInt \<Longrightarrow> S, E \<turnstile> Formula.TP t"
| TS: "E \<turnstile> t :: TInt \<Longrightarrow> S, E \<turnstile> Formula.TS t"

lemma wty_regexatms_atms:
  assumes "safe_formula (Formula.MatchP I r) \<or> safe_formula (Formula.MatchF I r)"
  shows "(\<forall>x \<in> Regex.atms r. S, E \<turnstile> x) \<longleftrightarrow> (\<forall>x \<in> atms r. S, E \<turnstile> x)"
proof -
  have "\<forall>x \<in> Regex.atms r. S, E \<turnstile> x" if "\<forall>x \<in> atms r. S, E \<turnstile> x"
    "Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
      (g = Lax \<and> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))) m g r" for m g
    using that
    apply (induction r arbitrary: m g)
        apply auto
    subgoal for x
      by (cases "safe_formula x") (auto split: formula.splits intro: wty_formula.intros)
    subgoal for r1 r2 m g x
      by (cases m) auto
    subgoal for r1 r2 m g x
      by (cases m) auto
    done
  moreover have "\<forall>x \<in> Regex.atms r. S, E \<turnstile> x \<Longrightarrow> \<forall>x \<in> atms r. S, E \<turnstile> x"
    by (induction r) (auto split: formula.splits elim: wty_formula.cases)
  ultimately show ?thesis
    using assms
    by fastforce
qed

lemma wty_formula_fv_cong:
  assumes "\<And>y. y \<in> fv \<phi> \<Longrightarrow> E y = E' y"
  and "wf_formula \<phi>"
  shows "S, E \<turnstile> \<phi> \<longleftrightarrow> S, E' \<turnstile> \<phi>"
proof -
  have "S, E \<turnstile> \<phi> \<Longrightarrow> (\<And>y. y \<in> fv \<phi> \<Longrightarrow> E y = E' y) \<Longrightarrow> wf_formula \<phi> \<Longrightarrow> S, E' \<turnstile> \<phi>" for E E'
  proof (induction arbitrary: E' pred: wty_formula)
    case (Pred S p tys E tms)
    then show ?case
      by (fastforce intro!: wty_formula.Pred
          elim!: list.rel_mono_strong wty_trm_fv_cong[THEN iffD1, rotated])
  next 
    case(Let S E'' \<phi>  p E  \<psi>)
    then show ?case
      using fvi.simps(2) apply(auto intro!: wty_formula.Let) 
      using Let.IH(2) by blast
  next
    case(Eq E x t y' S)
    then show ?case by (fastforce intro!: wty_formula.Eq
          elim!: wty_trm_fv_cong[THEN iffD1, rotated])
  next
     case(Less E x t y' S)
    then show ?case by (fastforce intro!: wty_formula.Less
          elim!:  wty_trm_fv_cong[THEN iffD1, rotated])
  next
    case(LessEq E x t y' S)
    then show ?case by (fastforce intro!: wty_formula.LessEq
          elim!: wty_trm_fv_cong[THEN iffD1, rotated])
  next
    case(Neg E S \<phi>)
    then show ?case by (simp add: wty_formula.Neg)
  next 
    case(Or E S \<phi> \<psi>)
    thus ?case by (simp add: wty_formula.Or)
  next 
    case(And E S \<phi> \<psi>)
    thus ?case by (simp add: wty_formula.And)
  next 
    case(Ands E S \<phi>s)
    from this show ?case by(auto simp: list_all_iff intro!:wty_formula.intros) 
  next
    case (Exists S t E \<phi>)
    then show ?case
      by (fastforce simp: fvi_Suc intro!: wty_formula.Exists[where t=t] split: nat.split)
  next
    case (Agg E s agg_type t tys f S \<phi> d)
    from Agg.prems Agg.hyps(1) have part1: "E' s = t_res agg_type t" by auto
    from Agg  have  aggenv: "\<forall>y\<in> Formula.fvi_trm (length tys) f. E y = E' y" by (auto simp: agg_env_def)
    from this have "\<forall>y\<in> Formula.fvi_trm 0 f. y\<ge> length tys \<longrightarrow>  E (y - length tys)  = E' (y - length tys) " by (meson fvi_trm_iff_fv_trm fvi_trm_minus fvi_trm_plus)
    from this  Agg.hyps(2) have  "(\<lambda>z. if z < length tys then tys ! z else E' (z - length tys)) \<turnstile> f :: t" using wty_trm_fv_cong
    by (smt (verit, del_insts) agg_env_def not_less) 
  from this have part2: "agg_env E' tys \<turnstile> f :: t" by (auto simp add: agg_env_def)

    from Agg have  "\<forall>y\<in> Formula.fvi (length tys) \<phi>. E y = E' y" by auto
    from this have "\<forall>y\<in> Formula.fvi 0 \<phi>. y\<ge> length tys \<longrightarrow>  (E (y - length tys)  = E' (y - length tys))" using fvi_minus[where b=0] by auto
    from this Agg have part3: " S, agg_env E' tys \<turnstile> \<phi>" by (auto simp: agg_env_def)
    from part1 part2 part3 Agg.hyps(5) Agg.hyps(4) show ?case by (simp add: wty_formula.Agg)
  next
    case (Prev S E \<phi> \<I>)
    thus ?case by (simp add: wty_formula.Prev)
  next
    case (Next S E \<phi>)
    thus ?case by (simp add: wty_formula.Next)

  next 
    case (Since S E \<phi>)
    thus ?case by (simp add: wty_formula.Since)
  next
    case (Until S E \<phi>)
    thus ?case by (simp add: wty_formula.Until)
  next 
    case (MatchP S E r I)
    from this have "regex.pred_regex (\<lambda>\<phi>. S, E' \<turnstile> \<phi>) r" by (induction r) auto
    thus ?case by (auto simp add: wty_formula.MatchP)
 next 
    case (MatchF S E r I)
    from this have "regex.pred_regex (\<lambda>\<phi>. S, E' \<turnstile> \<phi>) r" by (induction r) auto
    thus ?case by (auto simp add: wty_formula.MatchF)
  next
    case (LetPast S p \<phi> E E'' \<psi>)
    have aux: "(\<And>y. y \<in> fv \<psi> \<Longrightarrow> E'' y = E' y)" using LetPast(5) by auto
    have wf: "wf_formula \<psi>" using LetPast(6) by auto
    then have "S((p, Formula.nfv \<phi>) \<mapsto> tabulate E 0 (Formula.nfv \<phi>)), E' \<turnstile> \<psi>" 
      using LetPast(4)[OF aux wf] by fastforce
    then show ?case using LetPast(1) by(auto intro!: wty_formula.intros) 
  next
    case (TS S E t)
    then show ?case using wty_trm_fv_cong fvi.simps(20) wty_formula.TS by blast
  next
    case (TP S E t)
    then show ?case using wty_trm_fv_cong fvi.simps(19) wty_formula.TP by blast
  qed 
  with assms show ?thesis by auto
qed

lemma match_sat_fv: assumes "safe_regex temp Strict r"
    "Regex.match (Formula.sat \<sigma> V v) r j i"
    "x \<in> fv (formula.MatchP I r) \<or> x \<in>fv (formula.MatchF I r)"
  shows "\<exists>\<phi>\<in>atms r. \<exists>k. Formula.sat \<sigma> V v k \<phi> \<and> x \<in> fv \<phi>"
  using assms
  proof (induction r arbitrary:i j)

    case (Plus r1 r2)
  moreover obtain k where "\<exists>j. Regex.match (Formula.sat \<sigma> V v) r1 j k \<or>  Regex.match (Formula.sat \<sigma> V v) r2 j k" using  Plus.prems(2)  by auto
  moreover {
    assume assm: "\<exists>j. Regex.match (Formula.sat \<sigma> V v) r1 j k"
    then have ?case using Plus.prems(1,3) Plus.IH(1)  by (fastforce simp add: atms_def) 
  } moreover {
    assume assm: "\<exists>j. Regex.match (Formula.sat \<sigma> V v) r2 j k"
    from this have ?case using Plus.prems(1,3) Plus.IH(2) by (fastforce simp add: atms_def)
  }
  ultimately show ?case by auto
next
  case (Times r1 r2)
  then show ?case  using Times.prems match_le Times.IH  by (cases temp) fastforce+
qed  auto

lemma finite_fst: assumes "finite  {(x,f x) | x. P x}" shows "finite {x . P x}"
proof -
  have  fstSet: " fst ` {(x, f x) |x. P x} = {x . P x}" by (auto simp add: image_iff)
  show ?thesis using assms fstSet finite_image_iff[of fst "{(x,f x) | x. P x}"] by (auto simp add: inj_on_def)
qed


lemma set_of_flatten_multiset:
  assumes "M = {(x, ecard Zs) | x Zs. Zs = f x \<and> Zs \<noteq> {}}" "finite {x. f x \<noteq> {}}"
  shows "set (flatten_multiset M) \<subseteq> fst ` M"
proof -
  have fin_M: "finite M"
    using assms(2)
    by (auto simp: assms(1))
  obtain c :: "(event_data \<times> enat) comparator" where c: "ID ccompare = Some c"
    by (auto simp: ID_def ccompare_prod_def ccompare_event_data_def ccompare_enat_def)
  show ?thesis
    using fin_M image_iff
    by (fastforce simp: flatten_multiset_def csorted_list_of_set_def c
        linorder.set_sorted_list_of_set[OF ID_ccompare[OF c]])
qed

locale sat_general =
  fixes 
undef_plus :: "event_data \<Rightarrow> event_data \<Rightarrow> event_data" and
undef_minus :: "event_data \<Rightarrow> event_data \<Rightarrow> event_data" and
undef_uminus :: " event_data \<Rightarrow> event_data" and
undef_times :: "event_data \<Rightarrow> event_data \<Rightarrow> event_data" and
undef_divide :: "event_data \<Rightarrow> event_data \<Rightarrow> event_data" and
undef_modulo :: "event_data \<Rightarrow> event_data \<Rightarrow> event_data"  and
undef_double_of_event_data :: "event_data \<Rightarrow> double" and
undef_double_of_event_data_agg :: "event_data \<Rightarrow> double" and
undef_integer_of_event_data :: "event_data \<Rightarrow> integer" and
undef_less_eq :: "event_data \<Rightarrow> event_data \<Rightarrow> bool"
assumes undef_plus_sound:  "\<And>x y. undef_plus (EInt x) (EInt y) = EInt x + EInt y" 
    "\<And> x y . undef_plus (EFloat x) (EFloat y) = EFloat x + EFloat y"
assumes undef_minus_sound:  "\<And>x y. undef_minus (EInt x) (EInt y) = EInt x - EInt y" 
    "\<And> x y . undef_minus (EFloat x) (EFloat y) = EFloat x - EFloat y"
assumes undef_uminus_sound:  "\<And>x . undef_uminus (EInt x) = - EInt x"
   "\<And> x. undef_uminus (EFloat x) = - EFloat x "
assumes undef_times_sound:  "\<And>x y.  undef_times (EInt x) (EInt y) = EInt x * EInt y" 
    "\<And> x y . undef_times (EFloat x) (EFloat y) = EFloat x * EFloat y"
assumes undef_divide_sound:  "\<And>x y. undef_divide (EInt x) (EInt y) = EInt x div EInt y" 
    "\<And> x y .  undef_divide (EFloat x) (EFloat y) = EFloat x div EFloat y"
assumes undef_modulo_sound:  "\<And>x y.  undef_modulo (EInt x) (EInt y) = EInt x mod EInt y"  

assumes undef_double_of_event_data_sound: "\<And>x.  undef_double_of_event_data (EInt x) = double_of_event_data (EInt x)"
assumes undef_double_of_event_data_agg_sound: "\<And>x.  undef_double_of_event_data_agg (EInt x) = double_of_event_data_agg (EInt x)"
"\<And>x.  undef_double_of_event_data_agg (EFloat x) = double_of_event_data_agg (EFloat x)"
assumes undef_integer_of_event_data_sound: "\<And>x. undef_integer_of_event_data (EFloat x) = integer_of_event_data (EFloat x)"

assumes undef_less_eq_sound: "\<And>x y. undef_less_eq (EInt x) (EInt y) \<longleftrightarrow> EInt x \<le> EInt y"
 "\<And>x y. undef_less_eq (EFloat x) (EFloat y) \<longleftrightarrow> EFloat x \<le> EFloat y"
 "\<And> x y. undef_less_eq (EString x) (EString y) \<longleftrightarrow> EString x \<le> EString y"

begin

definition undef_less :: "event_data \<Rightarrow> event_data \<Rightarrow> bool"  where
  "undef_less x y \<longleftrightarrow> undef_less_eq x y \<and> \<not> undef_less_eq y x"

definition undef_min :: "event_data \<Rightarrow> event_data \<Rightarrow> event_data" where
  "undef_min a b = (if undef_less_eq a b then a else b)"

definition undef_max :: "event_data \<Rightarrow> event_data \<Rightarrow> event_data" where
  "undef_max a b = (if undef_less_eq a b then b else a)"

primrec eval_trm' :: "Formula.env \<Rightarrow> Formula.trm \<Rightarrow> event_data" where
  "eval_trm' v (Formula.Var x) = v ! x"
| "eval_trm' v (Formula.Const x) = x"
| "eval_trm' v (Formula.Plus x y) = undef_plus (eval_trm' v x) ( eval_trm' v y)"
| "eval_trm' v (Formula.Minus x y) = undef_minus (eval_trm' v x) ( eval_trm' v y)"
| "eval_trm' v (Formula.UMinus x) = undef_uminus (eval_trm' v x)"
| "eval_trm' v (Formula.Mult x y) = undef_times (eval_trm' v x) (eval_trm' v y)"
| "eval_trm' v (Formula.Div x y) = undef_divide (eval_trm' v x) (eval_trm' v y)"
| "eval_trm' v (Formula.Mod x y) = undef_modulo (eval_trm' v x) (eval_trm' v y)"
| "eval_trm' v (Formula.F2i x) = EInt (undef_integer_of_event_data (eval_trm' v x))"
| "eval_trm' v (Formula.I2f x) = EFloat (undef_double_of_event_data (eval_trm' v x))"

fun eval_agg_op' :: "ty Formula.agg_op \<Rightarrow> (event_data \<times> enat) set \<Rightarrow> event_data" where
  "eval_agg_op' (agg_type.Agg_Cnt, ty) M = (let y0 = aggreg_default_value agg_type.Agg_Cnt ty in
    case (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (xs,_) \<Rightarrow> EInt (integer_of_int (length xs)))"
| "eval_agg_op' (agg_type.Agg_Min, ty) M = (let y0 = aggreg_default_value agg_type.Agg_Min ty in 
    case  (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (x # xs,_) \<Rightarrow> foldl undef_min x xs)"
| "eval_agg_op' (agg_type.Agg_Max, ty) M = (let y0 = aggreg_default_value agg_type.Agg_Max ty in 
    case  (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (x # xs,_) \<Rightarrow> foldl undef_max x xs)"
| "eval_agg_op' (agg_type.Agg_Sum, ty) M = (let y0 = aggreg_default_value agg_type.Agg_Sum ty in 
    case  (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (x # xs,_) \<Rightarrow> foldl undef_plus x xs)"
| "eval_agg_op' (agg_type.Agg_Avg, ty) M =(let y0 = aggreg_default_value agg_type.Agg_Avg ty in 
    case  (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (x#xs,_) \<Rightarrow> EFloat ( undef_double_of_event_data_agg (foldl undef_plus x xs) / double_of_int (length (x#xs))))"
| "eval_agg_op' (agg_type.Agg_Med, ty) M =(let y0 = aggreg_default_value agg_type.Agg_Med ty in 
    case (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (xs,_) \<Rightarrow> EFloat (let u = length xs;  u' = u div 2 in
          if even u then
            (undef_double_of_event_data_agg (xs ! (u'-1)) + undef_double_of_event_data_agg (xs ! u')) / double_of_int 2
          else undef_double_of_event_data_agg (xs ! u')))"

fun sat' :: "Formula.trace \<Rightarrow> (Formula.name \<times> nat \<rightharpoonup> Formula.env \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> Formula.env \<Rightarrow> nat \<Rightarrow> ty Formula.formula \<Rightarrow> bool" where
  "sat' \<sigma> V v i (Formula.Pred r ts) = (case V (r, length ts) of
       None \<Rightarrow> (r, map (eval_trm' v) ts) \<in> \<Gamma> \<sigma> i
     | Some X \<Rightarrow> X (map (eval_trm' v) ts) i)"
| "sat' \<sigma> V v i (Formula.Let p \<phi> \<psi>) = sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> \<lambda>w j. sat' \<sigma> V w j \<phi>)) v i \<psi>"
| "sat' \<sigma> V v i (Formula.LetPast p \<phi> \<psi>) =
    (let pn = (p, Formula.nfv \<phi>) in
    sat' \<sigma> (V(pn \<mapsto> letpast_sat (\<lambda>X u k. sat' \<sigma> (V(pn \<mapsto> X)) u k \<phi>))) v i \<psi>)"
| "sat' \<sigma> V v i (Formula.Eq t1 t2) =  (eval_trm' v t1 = eval_trm' v t2)"
| "sat' \<sigma> V v i (Formula.Less t1 t2) = undef_less (eval_trm' v t1) (eval_trm' v t2)"
| "sat' \<sigma> V v i (Formula.LessEq t1 t2) = undef_less_eq (eval_trm' v t1) (eval_trm' v t2)"
| "sat' \<sigma> V v i (Formula.Neg \<phi>) = (\<not> sat' \<sigma> V v i \<phi>)"
| "sat' \<sigma> V v i (Formula.Or \<phi> \<psi>) = (sat' \<sigma> V v i \<phi> \<or> sat' \<sigma> V v i \<psi>)"
| "sat' \<sigma> V v i (Formula.And \<phi> \<psi>) = (sat' \<sigma> V v i \<phi> \<and> sat' \<sigma> V v i \<psi>)"
| "sat' \<sigma> V v i (Formula.Ands l) = (\<forall>\<phi> \<in> set l. sat' \<sigma> V v i \<phi>)"
| "sat' \<sigma> V v i (Formula.Exists t \<phi>) = (\<exists>z. sat' \<sigma> V (z # v) i \<phi>)"
| "sat' \<sigma> V v i (Formula.Agg y \<omega> tys f \<phi>) =
    (let M = {(x, ecard Zs) | x Zs. Zs = {zs. length zs = length tys \<and> sat' \<sigma> V (zs @ v) i \<phi> \<and> eval_trm' (zs @ v) f = x} \<and> Zs \<noteq> {}}
    in (M = {} \<longrightarrow> fv \<phi> \<subseteq> {0..< length tys}) \<and> v ! y = eval_agg_op' \<omega> M)"
| "sat' \<sigma> V v i (Formula.Prev I \<phi>) = (case i of 0 \<Rightarrow> False | Suc j \<Rightarrow> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat' \<sigma> V v j \<phi>)"
| "sat' \<sigma> V v i (Formula.Next I \<phi>) = (mem I ((\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i)) \<and> sat' \<sigma> V v (Suc i) \<phi>)"
| "sat' \<sigma> V v i (Formula.Since \<phi> I \<psi>) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat' \<sigma> V v j \<psi> \<and> (\<forall>k \<in> {j <.. i}. sat' \<sigma> V v k \<phi>))"
| "sat' \<sigma> V v i (Formula.Until \<phi> I \<psi>) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat' \<sigma> V v j \<psi> \<and> (\<forall>k \<in> {i ..< j}. sat' \<sigma> V v k \<phi>))"
| "sat' \<sigma> V v i (Formula.MatchP I r) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Regex.match (sat' \<sigma> V v) r j i)"
| "sat' \<sigma> V v i (Formula.MatchF I r) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Regex.match (sat' \<sigma> V v) r i j)"
| "sat' \<sigma> V v i (Formula.TP t) = (eval_trm' v t = EInt (integer_of_nat i))"
| "sat' \<sigma> V v i (Formula.TS t) = (eval_trm' v t = EInt (integer_of_nat (\<tau> \<sigma> i)))"

lemma eval_trm_sound: 
  assumes "E \<turnstile> f :: t"  "\<forall>y\<in>fv_trm f. ty_of (v ! y) = E y"
  shows "Formula.eval_trm v f = eval_trm' v f"
  using assms  
  apply  (induction  rule: wty_trm.induct) apply (auto simp add: numeric_ty_def)
  subgoal for x y  using  value_of_eval_trm[of E x v] value_of_eval_trm[of E y v] by (auto simp add: undef_plus_sound)
    subgoal for x y  using  value_of_eval_trm[of E x v] value_of_eval_trm[of E y v] by (auto simp add: undef_plus_sound)
  subgoal for x y
    using  value_of_eval_trm[of E x v] value_of_eval_trm[of E y v] by (auto simp add: undef_minus_sound) 
 subgoal for x y
   using  value_of_eval_trm[of E x v] value_of_eval_trm[of E y v] by (auto simp add: undef_minus_sound)
 subgoal for x 
   using  value_of_eval_trm[of E x v]  by (auto simp add: undef_uminus_sound)
 subgoal for x 
   using  value_of_eval_trm[of E x v]  by (auto simp add: undef_uminus_sound)
  subgoal for x y  using  value_of_eval_trm[of E x v] value_of_eval_trm[of E y v] by (auto simp add: undef_times_sound)
  subgoal for x y  using  value_of_eval_trm[of E x v] value_of_eval_trm[of E y v] by (auto simp add: undef_times_sound)
  subgoal for x y  using  value_of_eval_trm[of E x v] value_of_eval_trm[of E y v] by (auto simp add: undef_divide_sound)
  subgoal for x y  using  value_of_eval_trm[of E x v] value_of_eval_trm[of E y v] by (auto simp add: undef_divide_sound)
  subgoal for x y  using  value_of_eval_trm[of E x v] value_of_eval_trm[of E y v] by (auto simp add: undef_modulo_sound)
  subgoal for x  using  value_of_eval_trm[of E x v] by (auto simp add: undef_integer_of_event_data_sound)
  subgoal for x  using  value_of_eval_trm[of E x v] by (auto simp add: undef_double_of_event_data_sound)
  done


lemma poly_value_of: "E \<turnstile> x :: t\<Longrightarrow> E \<turnstile> y :: t \<Longrightarrow> \<forall>w\<in>fv_trm x \<union> fv_trm y. ty_of (v ! w) = E w \<Longrightarrow> 
(\<exists> z z'.(eval_trm' v x) = EInt z \<and> eval_trm' v y = EInt z'\<and> (Formula.eval_trm v x) = EInt z \<and> Formula.eval_trm v y = EInt z') \<or>
 (\<exists> z z'.(eval_trm' v x) = EFloat z \<and> eval_trm' v y = EFloat z' \<and> (Formula.eval_trm v x) = EFloat z \<and> Formula.eval_trm v y = EFloat z' ) \<or> 
(\<exists> z z'.(eval_trm' v x) = EString z \<and> eval_trm' v y = EString z' \<and> (Formula.eval_trm v x) = EString z \<and> Formula.eval_trm v y = EString z') "
  using value_of_eval_trm[of E x v] value_of_eval_trm[of E y v] eval_trm_sound[of E x _ v] eval_trm_sound[of E y _ v] 
  by (cases t)  auto 


lemma nfv_exists: " Formula.nfv \<phi> \<le> Suc (Formula.nfv (Formula.Exists t \<phi>))"
   apply (auto simp add: Formula.nfv_def fvi_Suc) 
  by (metis Max.coboundedI finite_fvi finite_imageI finite_insert fvi_Suc imageI insertCI list_decode.cases)

lemma match_safe_wty_nfv: assumes "\<phi> \<in> atms r"   "safe_formula (formula.MatchP I r) \<or> safe_formula (formula.MatchF I r)" " S, E \<turnstile> formula.MatchP I r \<or>  S, E \<turnstile> formula.MatchF I r"
  shows "S, E \<turnstile> \<phi>"
proof -
    from assms(3) assms(2) show  "S, E \<turnstile> \<phi>" using  Regex.Regex.regex.pred_set[of "(\<lambda>\<phi>. S, E \<turnstile> \<phi>)"] assms(1) wty_regexatms_atms  
      by (auto elim: wty_formula.cases)
  qed

lemma match_sat'_fv: assumes "safe_regex temp Strict r"
    "Regex.match (sat' \<sigma> V v) r j i"
    "x \<in> fv (formula.MatchP I r) \<or> x \<in>fv (formula.MatchF I r)"
  shows "\<exists>\<phi>\<in>atms r. \<exists>k. sat' \<sigma> V v k \<phi> \<and> x \<in> fv \<phi>"
  using assms
  proof (induction r arbitrary:i j)

    case (Plus r1 r2)
  moreover obtain k where "\<exists>j. Regex.match (sat' \<sigma> V v) r1 j k \<or>  Regex.match (sat' \<sigma> V v) r2 j k" using  Plus.prems(2)  by auto
  moreover {
    assume assm: "\<exists>j. Regex.match (sat' \<sigma> V v) r1 j k"
    then have ?case using Plus.prems(1,3) Plus.IH(1)  by (fastforce simp add: atms_def) 
  } moreover {
    assume assm: "\<exists>j. Regex.match (sat' \<sigma> V v) r2 j k"
    from this have ?case using Plus.prems(1,3) Plus.IH(2) by (fastforce simp add: atms_def)
  }
  ultimately show ?case by auto
next
  case (Times r1 r2)
  then show ?case  using Times.prems match_le Times.IH  by (cases temp) fastforce+
qed  auto

lemma wty_event_letpast:
  assumes
    wty_envs: "wty_envs S \<sigma> V" and
    letpast_sat: "letpast_sat (\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>) xs i" and
    wty: "S((p, Formula.nfv \<phi>) \<mapsto> tabulate E 0 (Formula.nfv \<phi>)), E \<turnstile> \<phi>" and
    IH: "\<And>S E V v i x. S, E \<turnstile> \<phi> \<Longrightarrow> wty_envs S \<sigma> V \<Longrightarrow> sat' \<sigma> V v i \<phi> \<Longrightarrow> x \<in> fv \<phi> \<Longrightarrow> ty_of (v ! x) = E x" and
    eq: "length xs = Formula.nfv \<phi>" and
    fv_subs: "{0..<Formula.nfv \<phi>} \<subseteq> fv \<phi>"
  shows "wty_event (S((p, Formula.nfv \<phi>) \<mapsto> tabulate E 0 (Formula.nfv \<phi>))) p xs" 
  using assms
proof(induction i arbitrary:xs rule: less_induct)
  case (less x)
  let ?tys = "tabulate E 0 (Formula.nfv \<phi>)"
  let ?V' = "(V((p, length xs) \<mapsto> \<lambda>a b. b < x \<and> letpast_sat (\<lambda>X v i. sat' \<sigma> (V((p, length xs) \<mapsto> X)) v i \<phi>) a b))"
  {
    fix pa xsa i
    assume "(pa, xsa) \<in> \<Gamma> \<sigma> i" and
           "(pa, length xsa) \<notin> dom ?V'"
    then have "wty_event (S((p, Formula.nfv \<phi>) \<mapsto> ?tys)) pa xsa"
      using less(2,6) wty_event_def wty_envs_def apply(auto split:option.splits) by blast+
  } moreover {
    fix pa xsa i
    assume in_V': "(pa, length xsa) \<in> dom ?V'" and
           valid: "the (?V' (pa, length xsa)) xsa i"
    have "wty_event (S((p, Formula.nfv \<phi>) \<mapsto> ?tys)) pa xsa"
    proof(cases "pa = p")
      case p_eq: True
      then show ?thesis
      proof(cases "length xsa = Formula.nfv \<phi>")
        case True
        have eq: "(pa, length xsa) = (p, Formula.nfv \<phi>)"
          unfolding True p_eq by simp
        have sat: "letpast_sat (\<lambda>X u k. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) u k \<phi>) xsa i" and
             less': "i < x"
          using valid unfolding eq less(6) by auto
        show ?thesis using less(1)[OF less' wty_envs sat wty _ True fv_subs] IH unfolding p_eq by blast
      next
        case False
        then show ?thesis using less(2,6) in_V' valid wty_envs_def wty_event_def by auto
      qed
    next
      case False
      then show ?thesis using less(2) in_V' valid wty_envs_def wty_event_def by auto
    qed
  } ultimately have wty_envs: "wty_envs (S((p, Formula.nfv \<phi>) \<mapsto> ?tys)) \<sigma> ?V'"
    unfolding wty_envs_def by blast
  show ?case using less(5)[OF less(4) wty_envs iffD1[OF letpast_sat.simps less(3), folded less(6)]] less(6-7) fvi_less_nfv
    by(auto simp:wty_event_def wty_tuple_def list_all2_conv_all_nth)
qed

lemma wty_envs_update:
  assumes
    safe: "safe_formula \<phi>" and
    wty_envs: "wty_envs S \<sigma> V" and
    wty: "S((p, Formula.nfv \<phi>) \<mapsto> tabulate E 0 (Formula.nfv \<phi>)), E \<turnstile> \<phi>" and
    fvi_subs: "{0..<Formula.nfv \<phi>} \<subseteq> fv \<phi>" and
    IH: "\<And>S E V v i x. safe_formula \<phi> \<Longrightarrow> S, E \<turnstile> \<phi> \<Longrightarrow> wty_envs S \<sigma> V \<Longrightarrow> sat' \<sigma> V v i \<phi> \<Longrightarrow> x \<in> fv \<phi> \<Longrightarrow> ty_of (v ! x) = E x"
  shows 
    "wty_envs (S((p, Formula.nfv \<phi>) \<mapsto> tabulate E 0 (Formula.nfv \<phi>))) \<sigma>
     (V((p, Formula.nfv \<phi>) \<mapsto> letpast_sat (\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>)))"
proof -
  let ?tys = "tabulate E 0 (Formula.nfv \<phi>)"
  let ?V' = "(V((p, Formula.nfv \<phi>) \<mapsto> letpast_sat (\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>)))"
  {
    fix pa xs i
    assume "(pa, xs) \<in> \<Gamma> \<sigma> i" and
           "(pa, length xs) \<notin> dom ?V'"
    then have "wty_event (S((p, Formula.nfv \<phi>) \<mapsto> ?tys)) pa xs"
      using wty_envs wty_event_def wty_envs_def apply(auto split:option.splits) by blast+
  } moreover {
    fix pa xs i
    assume in_V': "(pa, length xs) \<in> dom ?V'" and
           valid: "the (?V' (pa, length xs)) xs i"
    have "wty_event (S((p, Formula.nfv \<phi>) \<mapsto> ?tys)) pa xs"
    proof(cases "pa = p")
      case p_eq: True
      then show ?thesis
      proof(cases "length xs = Formula.nfv \<phi>")
        case True
        have eq: "(pa, length xs) = (p, Formula.nfv \<phi>)"
          unfolding True p_eq by simp
        have sat: "letpast_sat (\<lambda>X u k. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) u k \<phi>) xs i" using valid unfolding eq by auto
        show ?thesis using wty_event_letpast[OF wty_envs sat wty _ True fvi_subs] IH safe unfolding p_eq by blast
      next
        case False
        then show ?thesis using wty_envs in_V' valid wty_envs_def wty_event_def by auto
      qed
    next
      case False
      then show ?thesis using wty_envs in_V' valid wty_envs_def wty_event_def by auto
    qed
  } ultimately show ?thesis unfolding wty_envs_def by blast
qed

(*Theorem 3.7*)
lemma ty_of_sat'_safe: "safe_formula \<phi> \<Longrightarrow> S, E \<turnstile> \<phi> \<Longrightarrow> wty_envs S \<sigma> V \<Longrightarrow> 
  sat' \<sigma> V v i \<phi> \<Longrightarrow> x \<in> Formula.fv \<phi> \<Longrightarrow> ty_of (v ! x) = E x" (*Theorem 3.7*)
proof (induction arbitrary: S E V v i x rule: safe_formula_induct)
  case (Eq_Const c d)
  then show ?case by auto
next
  case (Eq_Var1 c xa)
  from Eq_Var1.prems(1) obtain t where 
    tys: " E \<turnstile> (trm.Const c) :: t" "E \<turnstile> (trm.Var xa) :: t"
    by cases
  from Eq_Var1(4) have x_eq: "x = xa" by auto
  from this `E \<turnstile> (trm.Var xa) :: t` have eq1: "E x = t" using  wty_trm.cases by fastforce
  have "v ! x = c" using Eq_Var1(3) x_eq by auto
  moreover have "ty_of c = t" using tys(1) by(auto elim:wty_trm.cases)
  ultimately show ?case using eq1 by auto
next
  case (Eq_Var2 c xa)
    from Eq_Var2.prems(1) obtain t where 
      tys: "E \<turnstile> (trm.Const c) :: t" "E \<turnstile> (trm.Var xa) :: t"
    by cases
  from Eq_Var2(4) have x_eq: "x = xa" by auto
  from this `E \<turnstile> (trm.Var xa) :: t` have eq1: "E x = t" using  wty_trm.cases by fastforce
  have "v ! x = c" using Eq_Var2(3) x_eq by auto
  moreover have "ty_of c = t" using tys(1) by(auto elim:wty_trm.cases)
  ultimately show ?case using eq1 by auto
next
  case (Pred p tms)
  from Pred.prems(1) obtain tys where
    S_p: "S (p, length tms) = Some tys" and
    xs_ts: "list_all2 (\<lambda>tm ty. E \<turnstile> tm :: ty) tms tys"
    by cases
  let ?xs = "map (eval_trm' v) tms"
  have wty_xs: "wty_tuple tys ?xs"
  proof (cases "(p, length ?xs) \<in> dom V")
    case True
    then have "the (V (p, length ?xs)) ?xs i"
      using Pred.prems(3) by auto
    with True show ?thesis
      using Pred.prems(2) by (auto simp: S_p dest!: wty_envs_V_D)
  next
    case False
    then have "(p, ?xs) \<in> \<Gamma> \<sigma> i"
      using Pred.prems(3) by (auto split: option.splits)
    with False show ?thesis
      using Pred.prems(2) by (auto simp: S_p dest!: wty_envs_\<Gamma>_D)
  qed
  from Pred obtain k where k: "k < length tms" "tms ! k = Formula.Var x"
    by (fastforce simp: trm.is_Var_def trm.is_Const_def in_set_conv_nth)
  with Pred.prems have "v ! x = ?xs ! k" by simp
  with wty_xs k have "ty_of (v ! x) = tys ! k"
    by (auto simp: wty_tuple_def list_all2_conv_all_nth)
  also have "\<dots> = E x"
    using xs_ts k
    by (fastforce simp: list_all2_conv_all_nth elim: wty_trm.cases)
  finally show ?case .
next
  case (Let p \<phi> \<psi>)
  let ?V' = "V((p, Formula.nfv \<phi>) \<mapsto> \<lambda>w j. sat' \<sigma> V w j \<phi>)"
  from Let.prems(1) obtain E' where
    wty_\<phi>: "S, E' \<turnstile> \<phi>" and
    wty_\<psi>: "S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E \<turnstile> \<psi>"
    by (cases pred: wty_formula)
  let ?S' = "S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>))"
  let ?tys = "tabulate E' 0 (Formula.nfv \<phi>)"
  {
    fix v' i
    assume "length v' = Formula.nfv \<phi>" and "sat' \<sigma> V v' i \<phi>"
    then have "wty_tuple ?tys v'"
      using Let.IH(1) wty_\<phi> Let.prems(2) Let.hyps(1)
      by (auto simp: wty_tuple_def list_all2_conv_all_nth)
  }
  note aux = this
  {
    fix pa xs i
    assume "(pa, xs) \<in> \<Gamma> \<sigma> i" and
      "(pa, length xs) \<notin> dom ?V'"
    then have "wty_event ?S' pa xs" 
      using Let.prems(2) wty_envs_def wty_event_def by fastforce
  } moreover {
    fix pa xs i
    assume in_V: "(pa, length xs) \<in> dom ?V'" and
      valid: "the (?V' (pa, length xs)) xs i"
    have "wty_event ?S' pa xs"
    proof(cases "pa = p")
      case p_eq: True
      then show ?thesis
      proof(cases "length xs = Formula.nfv \<phi>")
        case True
        have sat: "sat' \<sigma> V xs i \<phi>" using valid[unfolded p_eq True] by auto
        show ?thesis using aux[OF True sat] 
          unfolding p_eq wty_event_def True by auto
      next
        case False
        then show ?thesis using Let.prems(2) in_V valid wty_envs_def wty_event_def by auto
      qed
    next
      case False
      then show ?thesis using Let.prems(2) in_V valid wty_envs_def wty_event_def by auto
    qed
  }
  ultimately have "wty_envs ?S' \<sigma> ?V'"
    unfolding wty_envs_def by blast
  from Let.prems(3) have "sat' \<sigma> ?V' v i \<psi>" by simp
  from Let.prems(4) have "x \<in> fv \<psi>" by simp
  show ?case by (rule Let.IH(2)) fact+
next
  case (And_assign \<phi> \<psi>)
  from And_assign.prems(1) have phi1: "S, E \<turnstile> \<phi>" by cases
  from And_assign.prems(3) have phi2: "sat' \<sigma> V v i \<psi>" by auto
  from And_assign.prems(4) have "x \<in> fv \<phi> \<or> x \<in> fv \<psi>" by auto
  from this show ?case
  proof cases
    assume "x \<in> fv \<phi>"
    from this And_assign phi1 phi2 show ?case by auto
  next
    assume x_not_\<phi>: "x \<notin> fv \<phi>"
    from this And_assign.prems(4) have "x \<in> fv \<psi>" by auto
    from And_assign.hyps(2) obtain a b where \<psi>_eq: "\<psi> = Formula.Eq a b"
      by (auto simp: safe_assignment_def split: formula.splits)
    moreover {
      assume a_def: "a = Formula.Var x"
      from this  x_not_\<phi> have fvb: "fv_trm b \<subseteq> fv \<phi>" using And_assign(2) by  (auto simp: safe_assignment_def \<psi>_eq split: trm.splits) 
      have eval:" v! x = eval_trm' v b" using And_assign(6) a_def \<psi>_eq by auto
      have Ebx: "E \<turnstile> b :: E  x"  using And_assign(4) by (auto simp: \<psi>_eq a_def elim: wty_trm.cases wty_formula.cases)
      have "(\<lambda>y. ty_of (v ! y)) \<turnstile> b :: E x" apply (rule  iffD1[OF wty_trm_fv_cong,OF _ Ebx]) apply (subst eq_commute) 
        apply (rule And_assign(3)) using And_assign fvb by (auto elim: wty_formula.cases) 
      then have ?case using ty_of_eval_trm unfolding eval
        using And_assign(4) by (auto simp: \<psi>_eq a_def eval_trm_sound elim: wty_formula.cases)
    }
    moreover {
     assume a_def: "b = Formula.Var x"
      from this  x_not_\<phi> have fvb: "fv_trm a \<subseteq> fv \<phi>" using And_assign(2) by  (auto simp: safe_assignment_def \<psi>_eq split: trm.splits) 
      have eval:" v! x = eval_trm' v a" using And_assign(6) a_def \<psi>_eq by auto
      have Ebx: "E \<turnstile> a :: E  x"  using And_assign(4) by (auto simp: \<psi>_eq a_def elim: wty_trm.cases wty_formula.cases)
      have "(\<lambda>y. ty_of (v ! y)) \<turnstile> a :: E x" apply (rule  iffD1[OF wty_trm_fv_cong,OF _ Ebx]) apply (subst eq_commute) 
        apply (rule And_assign(3)) using And_assign fvb by (auto elim: wty_formula.cases) 
      then have ?case using ty_of_eval_trm unfolding eval
        using And_assign(4)  by (auto simp: \<psi>_eq a_def eval_trm_sound elim: wty_formula.cases)
    }
    moreover
      have "a = Formula.Var x \<or> b = Formula.Var x" using And_assign(2) And_assign(7) x_not_\<phi> by (auto simp: \<psi>_eq safe_assignment_def split: Formula.trm.splits) 
    ultimately show ?case by auto
qed
 next
  case (And_safe \<phi> \<psi>)
  from And_safe.prems(1) obtain "S, E \<turnstile> \<phi>" and "S, E \<turnstile> \<psi>" by cases
  from And_safe.prems(3) have "sat' \<sigma> V v i \<phi>" and "sat' \<sigma> V v i \<psi>"
    by simp_all
  from And_safe.prems(4) consider (in_\<phi>) "x \<in> fv \<phi>" | (in_\<psi>) "x \<in> fv \<psi>" by auto
  then show ?case
  proof cases
    case in_\<phi>
    show ?thesis by (rule And_safe.IH(1)) fact+
  next
    case in_\<psi>
    show ?thesis by (rule And_safe.IH(2)) fact+
  qed
next
  case (And_constraint \<phi> \<psi>)
  have xfree: "x \<in> fv \<phi>" using And_constraint(4) And_constraint(10) by auto
  from And_constraint(7) have "S, E \<turnstile> \<phi>" by cases
  from this xfree And_constraint(6,8-9,10) show ?case by auto
next
  case (And_Not \<phi> \<psi>)
  from And_Not.prems(4) And_Not.hyps(4) have xfree: "x \<in> fv \<phi>" by auto
  from And_Not.prems(1) have "S, E \<turnstile> \<phi>" by cases
  from this xfree And_Not  show ?case by auto 
next
  case (Ands l pos neg)
  from Ands have "\<exists>\<phi> \<in> set l . x \<in> fv \<phi>" by auto
  from this obtain \<psi> where psidef: "\<psi> \<in> set l \<and> x \<in> fv \<psi>" by blast
  from this have "\<exists>\<phi>\<in>set pos. x \<in>fv  \<phi>" 
  proof cases
    assume "safe_formula \<psi>"
    then have "\<psi> \<in> set pos" using Ands(1) by (auto simp add: psidef)
    thus "\<exists>\<phi>\<in>set pos. x \<in>fv  \<phi>" using psidef by auto
  next
    assume " \<not> safe_formula \<psi>"
    then have "\<psi> \<in> set neg" using Ands(1) by (auto simp add: psidef)
    thus "\<exists>\<phi>\<in>set pos. x \<in>fv  \<phi>" using Ands(1) Ands(5) psidef by auto
  qed
  from this obtain \<phi> where phidef: "\<phi> \<in> set pos \<and> x \<in> fv \<phi>" by blast
  from this Ands(1) have phi_in_l: "\<phi> \<in> set l" by auto
  from phidef Ands(6) have phi_IH: "S, E \<turnstile> \<phi> \<Longrightarrow>
    wty_envs S \<sigma> V \<Longrightarrow>
    sat' \<sigma> V v i \<phi> \<Longrightarrow> x \<in> fv \<phi> \<Longrightarrow> ty_of (v ! x) = E x"
        using list_all2_iff by (smt (verit, ccfv_SIG) Ball_set_list_all)
      from Ands.prems(1) have  "\<forall>\<phi> \<in> set l. S, E \<turnstile> \<phi>" by cases
      from this phi_in_l have p1: "S, E \<turnstile> \<phi>"  by auto
      from phi_in_l Ands.prems(3) have p3: "sat' \<sigma> V v i \<phi>" by auto
  from  phi_IH p1 Ands.prems(2) p3 phidef  show ?case by auto
next
  case (Neg \<phi>)
  from Neg show ?case by auto
next
  case (Or \<phi> \<psi>)
  from Or.prems(3) have " (sat' \<sigma> V v i \<phi>) \<or>( sat' \<sigma> V v i \<psi>)" by auto
  from this show ?case 
  proof
    assume assm: "(sat' \<sigma> V v i \<phi>)"
  from Or(1) Or.prems(4) have xfv: "x \<in> fv \<phi>" by auto
  from Or.prems(1) have "S, E \<turnstile> \<phi>" by cases
  from this assm Or.prems(2,3) Or(4) xfv show ?case by auto
next 
  assume assm: "( sat' \<sigma> V v i \<psi>)"
 from Or(1) Or.prems(4) have xfv: "x \<in> fv \<psi>" by auto
  from Or.prems(1) have "S, E \<turnstile> \<psi>" by cases
  from this assm Or.prems(2,3) Or(5) xfv show ?case by auto
qed
next
  case (Exists t \<phi>)
  from Exists.prems(1) obtain t where "S, case_nat t E \<turnstile> \<phi>" by cases
  from Exists.prems(3) obtain z where "sat' \<sigma> V (z#v) i \<phi>" by auto
  from Exists.prems(4) have "Suc x \<in> fv \<phi>" by (simp add: fvi_Suc)
  have "ty_of ((z#v) ! Suc x) = case_nat t E (Suc x)"
    by (rule Exists.IH) (simp?, fact)+
  then show ?case by simp
next
  case (Agg y \<omega> tys f \<phi>)
  have case_split:" x \<in> Formula.fvi (length tys) \<phi> \<or> x \<in> Formula.fvi_trm (length tys) f \<or> x = y" using Agg.prems(4) by auto
  moreover {
    assume asm: "x \<in> Formula.fvi (length tys) \<phi>"
    from this have "\<not> fv \<phi> \<subseteq> {0..< length tys}" using fvi_iff_fv[of x "length tys" \<phi>] by auto
    from this have M: "{(x, ecard Zs) | 
  x Zs. Zs = {zs. length zs = length tys \<and> sat' \<sigma> V (zs @ v) i \<phi> \<and> eval_trm' (zs @ v) f = x} \<and> Zs \<noteq> {}} \<noteq> {}" using Agg.prems(3) by auto
    from this obtain zs where sat: "sat' \<sigma> V (zs @ v) i \<phi> \<and> length zs = length tys" by auto
    have "ty_of ((zs@v) ! (x + length tys)) = agg_env E tys (x + length tys)"
      apply (rule Agg.IH[of \<phi> S "agg_env E tys" V "zs @ v" i "x+ length tys"]) using Agg.prems(1) Agg(4) sat asm Agg.prems(1-2) fvi_iff_fv
      by (auto elim: wty_formula.cases)
    from this have ?case apply (auto simp add: agg_env_def) by (metis add.commute nth_append_length_plus sat)
  } 
  moreover {
    assume "x \<notin> Formula.fvi (length tys) \<phi>"
    from this have eq: "x = y" using Agg(3) case_split fvi_iff_fv fvi_trm_iff_fv_trm by blast
    obtain d agg_type where omega_def: "\<omega> = (agg_type, d)" using surjective_pairing by blast
    from Agg.prems(1) this have  "\<exists>t .E y = t_res agg_type t" by cases auto
    from this eq obtain t where t_def: "E x = t_res agg_type t" by blast
    from  Agg.prems(1) have
 ty_of_d: "d = t_res agg_type t" apply cases using eq omega_def t_def by auto
    from Agg.prems(3) eq obtain M where  M_def: "M = {(x, ecard Zs) | x Zs. Zs = {zs. length zs = length tys \<and> sat' \<sigma> V (zs @ v) i \<phi>
        \<and> eval_trm' (zs @ v) f = x} \<and> Zs \<noteq> {}}"  "v!x = eval_agg_op' \<omega> M" by auto
   
        {
           assume finite_M: "finite_multiset M"
    from this   have finite_set:"finite {x. {zs. length zs = length tys \<and> sat' \<sigma> V (zs @ v) i \<phi> \<and> eval_trm' (zs @ v) f = x} \<noteq> {}}"
       using finite_fst by (auto simp add: finite_multiset_def M_def ) 
    have flatten: "set (flatten_multiset M) \<subseteq> fst ` M" using finite_set  set_of_flatten_multiset[of M
 "(\<lambda>x . {zs . length zs = length tys \<and> sat' \<sigma> V (zs @ v) i \<phi> \<and> eval_trm' (zs @ v) f = x} )"]
       by (auto simp add:  M_def) 
    from this  have evaltrm: "z \<in> set (flatten_multiset M) \<Longrightarrow>  \<exists> zs. length zs = length tys \<and> sat' \<sigma> V (zs @ v) i \<phi> \<and> eval_trm' (zs @ v) f = z" 
      for z using  M_def by (auto simp add: image_def)
     have th2: ?case if minmaxsum: "agg_type = agg_type.Agg_Min \<or> agg_type = agg_type.Agg_Max \<or> agg_type = agg_type.Agg_Sum" and alist_def: " flatten_multiset
     {(x, ecard {zs. length zs = length tys \<and> sat' \<sigma> V (zs @ v) i \<phi> \<and> eval_trm' (zs @ v) f = x}) |x.
      \<exists>xa. sat' \<sigma> V (xa @ v) i \<phi> \<and> length xa = length tys \<and> eval_trm' (xa @ v) f = x} =
    a # list"  for a list
     proof -
      have ty_of_list: "z=a \<or> z \<in> set list \<Longrightarrow> \<exists>zs .ty_of (eval_trm' (zs @ v) f) = t \<and> ty_of z = t" for z
      proof -
          assume z_def: "z=a \<or> z \<in> set list"
        from z_def obtain zs where zs_def: " length zs = length tys \<and> sat' \<sigma> V (zs @ v) i \<phi> \<and> eval_trm' (zs @ v) f = z" using alist_def evaltrm M_def by auto
        from Agg.prems(1) have wty_f: " agg_env E tys  \<turnstile> f :: t" apply cases  using omega_def t_def minmaxsum eq  by auto  
        have fv_ty:"\<forall>y\<in>fv_trm f. ty_of ((zs @ v) ! y) = agg_env E tys y"
        proof 
          fix y
          assume assm: "y \<in> fv_trm f"
          have  sat: "sat' \<sigma> V (zs @ v) i \<phi>"  using zs_def by auto 
          show "ty_of ((zs @ v) ! y) = agg_env E tys y" using zs_def assm Agg(3,4) Agg.prems(1-2) sat  Agg.IH[of \<phi> S "agg_env E tys" V "zs@v" i y]
            by (auto elim: wty_formula.cases)
        qed      
        have ty_of_z: "ty_of (eval_trm' (zs @ v) f) = t" using wty_f fv_ty   ty_of_eval_trm[of "agg_env E tys" f t "zs@v" ]
          by (auto simp add: eval_trm_sound)
        from this zs_def show  ?thesis by auto
      qed 
      from this obtain zs where zs_def: "ty_of (eval_trm' (zs @ v) f) = t" by auto
      from ty_of_list have indass: "ty_of a = t \<and> (\<forall>z \<in> set list . ty_of z = t)" by auto
     
      from this have foldl_evaltrm: "foldfun = min \<or> foldfun = max
        \<Longrightarrow> ty_of (foldl foldfun a list) = ty_of (eval_trm' (zs @ v) f)" for foldfun using indass 
          proof  (induction list arbitrary: a foldfun)
            case Nil
            then show ?case using zs_def by auto
          next
            case (Cons aa tail)
             have minmax: " ty_of (foldl foldfun (foldfun a aa) tail) = ty_of (eval_trm' (zs @ v) f)"
              using Cons.IH[of _ "foldfun a aa"] Cons apply auto 
               apply (metis min_def) by (metis max_def) 
              then show ?case by auto
            qed

          from indass have foldl_evaltrm_Sum: 
              "t \<in> numeric_ty \<Longrightarrow> ty_of (foldl undef_plus a list) = ty_of (eval_trm' (zs@v) f)" 
              proof (induction list arbitrary: a)
                  case (Cons aa tail)
                  from this have "ty_of (undef_plus a aa) = t"  apply (cases aa)  apply ( auto simp add: numeric_ty_def ty_of_plus)
                     apply (cases a) apply (auto simp add: undef_plus_sound)
                    by (cases a)(auto simp add: undef_plus_sound)

                  then show ?case using Cons.prems(1) Cons.IH[of "undef_plus a aa"] apply auto 
                    by (metis Cons.prems(2) list.set_intros(2))
                qed (auto simp add: zs_def)

 from indass have foldl_evaltrm_Min: 
              " ty_of (foldl undef_min a list) = t" 
              proof (induction list arbitrary: a)
                  case (Cons aa tail)
            from this have "ty_of (undef_min a aa) = t"  apply (cases aa) by ( auto simp add: numeric_ty_def undef_min_def undef_less_eq_sound)
                  then show ?case using Cons.prems(1) Cons.IH[of "undef_min a aa"] by auto 
                qed auto

 from indass have foldl_evaltrm_Max: 
              " ty_of (foldl undef_max a list) = t" 
              proof (induction list arbitrary: a)
                  case (Cons aa tail)
            from this have "ty_of (undef_max a aa) = t"  apply (cases aa) by ( auto simp add: numeric_ty_def undef_max_def undef_less_eq_sound)
                  then show ?case using Cons.prems(1) Cons.IH[of "undef_max a aa"] by auto 
              qed auto
           from Agg.prems(1) t_def eq omega_def have num_ty: "agg_type = agg_type.Agg_Sum \<Longrightarrow> t \<in> numeric_ty" by cases auto
         
    
            from  num_ty  finite_M foldl_evaltrm foldl_evaltrm_Sum foldl_evaltrm_Min foldl_evaltrm_Max show  ?thesis apply (cases agg_type)
               by (auto simp add: M_def  alist_def omega_def finite_multiset_def   
                      t_def zs_def   split: list.splits) 
   
           qed
           from  finite_M th2  M_def t_def omega_def have ?case 
             using ty_of_d by (cases agg_type) (auto simp:Let_def aggreg_default_value_def split:list.splits ty.splits)
        }
        moreover{
             assume not_finite: "\<not> finite_multiset M"
             from this t_def  M_def  omega_def have  ?case 
               using ty_of_d by(cases agg_type) (auto simp add: Let_def aggreg_default_value_def split: list.splits ty.splits) 
         }
         ultimately have ?case by auto 
     
  } 
  ultimately show ?case by auto
next
  
  case (Prev I \<phi>)
   from Prev.prems(1) have wty: "S, E \<turnstile> \<phi>" by cases
  from Prev.prems(3) have forall_j: "\<forall>j . i = Suc j \<longrightarrow> sat' \<sigma> V v j \<phi>" by auto
  from this have "sat' \<sigma> V v (Nat.pred i) \<phi>" using Prev.prems by (auto split: nat.splits)
  from this wty Prev.prems(2-4) Prev.IH show ?case by auto
next
  case (Next I \<phi>)
  from Next.prems(1,2-4) Next.IH show ?case by (auto elim: wty_formula.cases)
next
  case (Since \<phi> I \<psi>)
  from Since(1,9) have xfv: "x \<in> fv \<psi>" by auto
  from this  Since.prems(1,2-4) Since.IH show ?case by (auto elim: wty_formula.cases)
next
  case (Not_Since \<phi> I \<psi>)
  from Not_Since.prems(1) have wty: "S, E \<turnstile> \<psi>" by cases
  from Not_Since(1,10) have xfv: "x \<in> fv \<psi>" by auto
  from this wty Not_Since.prems(2-4) Not_Since.IH show ?case by auto
next
  case (Until \<phi> I \<psi>)
  from Until(1,9) have xfv: "x \<in> fv \<psi>" by auto
  from this  Until.prems(1,2-4) Until.IH show ?case by (auto elim: wty_formula.cases)
next
  case (Not_Until \<phi> I \<psi>)
 from Not_Until.prems(1) have wty: "S, E \<turnstile> \<psi>" by cases
  from Not_Until(1,10) have xfv: "x \<in> fv \<psi>" by auto
  from this wty Not_Until.prems(2-4) Not_Until.IH show ?case by auto
next
  case (MatchP I r)
  from MatchP.prems(3) have "(\<exists>j. Regex.match (sat' \<sigma> V v) r j i)" by auto
    from this  MatchP(1)  MatchP.prems(4) obtain \<phi> j where phidef: "\<phi> \<in> atms r" "sat' \<sigma> V v j \<phi>" "x \<in> fv \<phi> " using match_sat'_fv  by auto blast
    from   MatchP.prems(1) MatchP(1)  MatchP.prems(4) phidef(1)  have wty: "S, E \<turnstile> \<phi>" 
      using  match_safe_wty_nfv[of \<phi> r I S E] by (smt (z3) le_add_same_cancel2 length_tabulate match_safe_wty_nfv(1) nfv_simps(11) safe_formula.simps(17) zero_le)
    from MatchP.IH MatchP.prems have IH: "S, E \<turnstile> \<phi> \<Longrightarrow>\<phi> \<in> atms r \<Longrightarrow>
     sat' \<sigma> V v j \<phi> \<Longrightarrow> x \<in> fv \<phi> \<Longrightarrow> ty_of (v ! x ) = E x"
    for \<phi> E  v  x by blast
   show ?case apply (rule IH) using wty  MatchP.prems(4) phidef by auto
 
next
  case (MatchF I r)
  from MatchF.prems(3) have "(\<exists>j. Regex.match (sat' \<sigma> V v) r  i j)" by auto
  from this  MatchF(1)  MatchF.prems(4) obtain \<phi> j where phidef: " \<phi> \<in> atms r" " sat' \<sigma> V v j \<phi>" "x \<in> fv \<phi> " using match_sat'_fv  by auto blast
  from   MatchF.prems(1) MatchF(1)  MatchF.prems(4) phidef(1)  have wty: "S, E \<turnstile> \<phi>" 
    using  match_safe_wty_nfv[of \<phi> r I S E] by (smt (z3) bot_nat_0.extremum bot_nat_def le_add_same_cancel2 length_tabulate match_safe_wty_nfv(1) safe_formula.simps(18))
  from MatchF.IH MatchF.prems have IH: "S, E \<turnstile> \<phi> \<Longrightarrow>\<phi> \<in> atms r \<Longrightarrow>
   sat' \<sigma> V v j \<phi> \<Longrightarrow> x \<in> fv \<phi> \<Longrightarrow> ty_of (v ! x ) = E x"
   for \<phi> E  v  x by blast
  show ?case apply (rule IH) using wty MatchF.prems(4)  phidef by auto
next
  case (LetPast p \<phi> \<psi>)
  obtain E' where 
    wty_phi: "S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E' \<turnstile> \<phi>" and
    wty_psi: "S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E \<turnstile> \<psi>"
    using LetPast.prems(1) by(auto elim:wty_formula.cases)
  let ?tys = "tabulate E' 0 (Formula.nfv \<phi>)"
  let ?V' = "V((p, Formula.nfv \<phi>) \<mapsto> letpast_sat (\<lambda>X u k. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) u k \<phi>))"
  have x_fv: "x \<in> fv \<psi>" using LetPast.prems(4) by auto
  note sat' = LetPast.prems(3)[unfolded sat'.simps Let_def]
  have wty_envs:  
    "wty_envs (S((p, Formula.nfv \<phi>) \<mapsto> ?tys)) \<sigma> ?V'" 
    using wty_envs_update[OF LetPast(3, 8) wty_phi LetPast(2)] LetPast(5) by auto
  show ?case using LetPast.IH(2)[OF wty_psi wty_envs sat' x_fv] by auto
next
  case (TP t)
  then show ?case by(cases t) (auto elim!:wty_formula.cases wty_trm.cases)
next
  case (TS t)
  then show ?case by(cases t) (auto elim!:wty_formula.cases wty_trm.cases)
qed

end

interpretation  sat_inst: sat_general "(+)" "(-)" "uminus" "(*)" "(div)" "(mod)" "Event_Data.double_of_event_data" "Event_Data.double_of_event_data_agg" "Event_Data.integer_of_event_data" "(\<le>)"
  by unfold_locales  auto

lemma eval_trm_inst: "sat_inst.eval_trm' = Formula.eval_trm"
proof -
  have  "sat_inst.eval_trm' v f = Formula.eval_trm v f" for v f
  by (induction f)  auto 
  then show ?thesis  by auto
qed 

lemma eval_agg_op_inst: "sat_inst.eval_agg_op' (\<omega>, d) M  = Formula.eval_agg_op (\<omega>, d) M"
  apply (cases \<omega>) apply (auto simp:Let_def) apply(induction "flatten_multiset M")  apply(cases \<omega>) apply(auto split: list.splits) 
    apply (smt (verit) foldl_cong min_def sat_inst.undef_min_def sat_inst.undef_min_def) 
   apply(cases "finite_multiset M") apply(auto) by (metis (full_types) foldl_cong max_def sat_inst.undef_max_def)

lemma sat_inst_of_sat': "Formula.sat \<sigma> V v i \<phi> = sat_inst.sat' \<sigma> V v i \<phi>"
 apply (induction \<phi> arbitrary: v V i)  apply  (auto simp add: eval_trm_inst less_event_data_def sat_inst.undef_less_def  split: nat.splits)
  using eval_trm_inst apply presburger
                      apply (metis eval_trm_inst) 
  using eval_agg_op_inst apply presburger+  by  (metis match_cong_strong)+


(*Theorem 3.7 instantiated with sat*)
lemma ty_of_sat_safe: "safe_formula \<phi> \<Longrightarrow> S, E \<turnstile> \<phi> \<Longrightarrow> wty_envs S \<sigma> V \<Longrightarrow> 
  Formula.sat \<sigma> V v i \<phi> \<Longrightarrow> x \<in> Formula.fv \<phi> \<Longrightarrow> ty_of (v ! x) = E x"
  using  sat_inst.sat_general_axioms sat_inst_of_sat'
    sat_general.ty_of_sat'_safe[of  "(+)" "(-)" "uminus" "(*)" "(div)" "(mod)" double_of_event_data double_of_event_data_agg integer_of_event_data "(\<le>)"]  
  by auto 

lemma wty_envs_letpast_update:
  "{0..<Formula.nfv \<phi>} \<subseteq> fv \<phi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> S((p, Formula.nfv \<phi>) \<mapsto> tabulate E 0 (Formula.nfv \<phi>)), E \<turnstile> \<phi> \<Longrightarrow> wty_envs S \<sigma> V \<Longrightarrow>
  wty_envs (S((p, Formula.nfv \<phi>) \<mapsto> tabulate E 0 (Formula.nfv \<phi>))) \<sigma>
     (V((p, Formula.nfv \<phi>) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>)))"
  using sat_general.wty_envs_update[OF sat_inst.sat_general_axioms, folded sat_inst_of_sat'] ty_of_sat_safe 
  by auto
  

lemma rel_regex_fv_aux: "regex.rel_regex (\<lambda>a b. \<forall>x. Formula.fvi x a = Formula.fvi x b) r r' \<Longrightarrow>
  Regex.fv_regex (Formula.fvi x) r = Regex.fv_regex (Formula.fvi x) r'"
  by (induction r r' rule: regex.rel_induct) auto

lemma rel_formula_fv: "formula.rel_formula f \<phi> \<phi>' \<Longrightarrow> Formula.fvi b \<phi> = Formula.fvi b \<phi>'"
proof (induction \<phi> \<phi>' arbitrary: b rule: formula.rel_induct)
  case (Ands l l')
  then show ?case
    by (induction l l' rule: list.rel_induct) auto
qed (auto simp add: list_all2_lengthD rel_regex_fv_aux)

lemma rel_regex_fv: "regex.rel_regex (formula.rel_formula f) r r' \<Longrightarrow>
  Regex.fv_regex (Formula.fvi x) r = Regex.fv_regex (Formula.fvi x) r'"
  by (induction r r' rule: regex.rel_induct) (auto simp: rel_formula_fv)

lemma rel_regex_fv_cong: "Regex.rel_regex (\<lambda>a b. P a b) r r' \<Longrightarrow> (\<And>\<phi> \<phi>'. P \<phi> \<phi>' \<Longrightarrow> fv \<phi> = fv \<phi>') \<Longrightarrow>
  fv_regex r = fv_regex r'"
  by (induction r r' rule: regex.rel_induct) auto

lemma rel_regex_safe_aux: "safe_regex m g r \<Longrightarrow>
  (\<And>\<phi> \<phi>'. \<phi> \<in> atms r \<Longrightarrow> P \<phi> \<phi>' \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<phi>') \<Longrightarrow>
  (\<And>\<phi> \<phi>'. P \<phi> \<phi>' \<Longrightarrow> fv \<phi> = fv \<phi>') \<Longrightarrow>
  (\<And>\<phi> \<phi>'. P (formula.Neg \<phi>) \<phi>' \<Longrightarrow> (case \<phi>' of formula.Neg \<phi>'' \<Rightarrow> P \<phi> \<phi>'' | _ \<Rightarrow> False)) \<Longrightarrow>
  Regex.rel_regex (\<lambda>a b. P a b) r r' \<Longrightarrow> safe_regex m g r'"
proof (induction m g r arbitrary: r' rule: safe_regex_induct)
  case (Skip m g n)
  then show ?case
    by (cases r') auto
next
  case (Test m g \<phi>)
  then show ?case
    apply (cases r')
        apply auto
    subgoal for \<psi>
      apply (cases "safe_formula \<phi>")
       apply simp
      apply (cases \<phi>)
                      apply (auto)
      subgoal for \<phi>' 
        using Test(4)[of \<phi>' \<psi>]
        by (cases \<psi>) auto
      done
    done
next
  case (Plus m g r s)
  then show ?case
    using rel_regex_fv_cong[OF _ Plus(5)]
    by (cases r') auto
next
  case (TimesF g r s)
  then show ?case
    using rel_regex_fv_cong[OF _ TimesF(5)]
    by (cases r') auto
next
  case (TimesP g r s)
  then show ?case
    using rel_regex_fv_cong[OF _ TimesP(5)]
    by (cases r') auto
next
  case (Star m g r)
  then show ?case
    using rel_regex_fv_cong[OF _ Star(4)]
    by (cases r') auto
qed

lemma list_all2_setD1: "list_all2 f xs ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<exists>y \<in> set ys. f x y"
  by (induction xs ys rule: list.rel_induct) auto

lemma list_all2_setD2: "list_all2 f xs ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> \<exists>x \<in> set xs. f x y"
  by (induction xs ys rule: list.rel_induct) auto

lemma rel_regex_regex_atms: "Regex.rel_regex f r r' \<Longrightarrow> x \<in> Regex.atms r \<Longrightarrow> \<exists>x' \<in> Regex.atms r'. f x x'"
  by (induction r r' rule: regex.rel_induct) auto

lemma rel_regex_regex_atms': "Regex.rel_regex f r r' \<Longrightarrow> x \<in> Regex.atms r' \<Longrightarrow> \<exists>x' \<in> Regex.atms r. f x' x"
  by (induction r r' rule: regex.rel_induct) auto

lemma rel_formula_safe_letpast: "formula.rel_formula f \<phi> \<psi> \<Longrightarrow> safe_letpast p \<phi> = safe_letpast p \<psi>"
proof (induction \<phi> arbitrary: \<psi> rule: safe_letpast.induct)
  case (1 p t1 t2)
  then show ?case by(cases \<psi>) auto
next
  case (2 p t1 t2)
  then show ?case by(cases \<psi>) auto
next
  case (3 p t1 t2)
  then show ?case by(cases \<psi>) auto
next
  case (4 p e ts)
  then show ?case by(cases \<psi>) auto
next
  case (5 p e \<phi> \<psi>)
  then show ?case by(cases \<psi>; auto) (metis Formula.nfv_def rel_formula_fv)+
next
  case (6 p e \<phi> \<psi>)
  then show ?case by(cases \<psi>; auto) (metis Formula.nfv_def rel_formula_fv)+
next
  case (7 p \<phi>)
  then show ?case by(cases \<psi>) auto
next
  case (8 p \<phi> \<psi>)
  then show ?case by(cases \<psi>) auto
next
  case (9 p \<phi> \<psi>)
  then show ?case by(cases \<psi>) auto
next
  case (10 p l)
  then obtain l' where 
    \<psi>_def: "\<psi> = formula.Ands l'" and
    all_rel: "list_all2 (formula.rel_formula f) l l'"
    by (cases \<psi>) auto
  have "(safe_letpast p ` set l) = (safe_letpast p ` set l')"
    using list_all2_setD1[OF all_rel] list_all2_setD2[OF all_rel] 10(1) image_iff
    by auto fastforce+
  then show ?case unfolding \<psi>_def by(auto)
next
  case (11 p t \<phi>)
  then show ?case by(cases \<psi>) auto
next
  case (12 p y \<omega> tys f \<phi>)
  then show ?case by(cases \<psi>) auto
next
  case (13 p I \<phi>)
  then show ?case by(cases \<psi>) auto
next
  case (14 p I \<phi>)
  then show ?case by(cases \<psi>) auto
next
  case (15 p \<phi> I \<psi>)
  then show ?case by(cases \<psi>) auto
next
  case (16 p \<phi> I \<psi>)
  then show ?case by(cases \<psi>) auto
next
  case (17 p I r)
  then obtain r' where 
    \<psi>_def: "\<psi> = formula.MatchP I r'" and
    all_rel: "regex.rel_regex (formula.rel_formula f) r r'"
    by(cases \<psi>) auto
  have "(safe_letpast p ` regex.atms r) = (safe_letpast p ` regex.atms r')"
    using image_iff rel_regex_regex_atms[OF all_rel] rel_regex_regex_atms'[OF all_rel] 17(1) 
    by auto fastforce+ 
  then show ?case unfolding \<psi>_def by auto
next
  case (18 p I r)
  then obtain r' where 
    \<psi>_def: "\<psi> = formula.MatchF I r'" and
    all_rel: "regex.rel_regex (formula.rel_formula f) r r'"
    by(cases \<psi>) auto
  have "(safe_letpast p ` regex.atms r) = (safe_letpast p ` regex.atms r')"
    using image_iff rel_regex_regex_atms[OF all_rel] rel_regex_regex_atms'[OF all_rel] 18(1) 
    by auto fastforce+ 
  then show ?case unfolding \<psi>_def by auto
next
  case (19 p t)
  then show ?case by(cases \<psi>) auto
next
  case (20 p t)
  then show ?case by(cases \<psi>) auto
qed

lemma rel_formula_safe: "safe_formula \<phi> \<Longrightarrow> formula.rel_formula f \<phi> \<psi> \<Longrightarrow> safe_formula \<psi>"
proof (induction \<phi> arbitrary: \<psi> rule: safe_formula_induct)
  case (Eq_Const c d)
  then show ?case
    by (cases \<psi>) auto
next
  case (Eq_Var1 c x)
  then show ?case
    by (cases \<psi>) auto
next
  case (Eq_Var2 c x)
  then show ?case
    by (cases \<psi>) auto
next
  case (Pred e ts)
  then show ?case
    by (cases \<psi>) auto
next
  case (Let p \<phi>' \<phi> \<psi> )
  then show ?case
    by (cases \<psi>) (auto simp: Formula.nfv_def rel_formula_fv)
next
  case (And_assign \<phi> \<phi>' \<psi>)
  then show ?case
    apply (cases \<psi>)
                    apply (auto simp: rel_formula_fv)
     apply (auto simp: safe_assignment_def split: formula.splits)
    done
next
  case (And_safe \<phi> \<psi>)
  then show ?case
    by (cases \<psi>) auto
next
  case (And_constraint \<phi> \<phi>' \<psi>)
  moreover have "is_constraint \<phi>' \<Longrightarrow> formula.rel_formula f \<phi>' \<psi>' \<Longrightarrow> is_constraint \<psi>'" for \<psi>'
    by (cases \<phi>' rule: is_constraint.cases; cases \<psi>' rule: is_constraint.cases) auto
  ultimately show ?case
    by (cases \<psi>) (auto simp: rel_formula_fv)
next
  case (And_Not \<phi> \<phi>' \<psi>)
  then show ?case
    by (cases \<psi>) (auto simp: rel_formula_fv elim!: formula.rel_cases[of _ "formula.Neg \<phi>'"])
next
  case (Ands l pos neg \<psi>)
  obtain l' pos' neg' where \<psi>_def: "\<psi> = formula.Ands l'" "partition safe_formula l' = (pos', neg')"
    "list_all2 (formula.rel_formula f) l l'"
    using Ands(8)
    by (cases \<psi>) auto
  note part = partition_P[OF \<psi>_def(2)] partition_set[OF Ands(1)[symmetric], symmetric]
    partition_set[OF \<psi>_def(2), symmetric]
  have pos_pos': "\<exists>p' \<in> set pos'. formula.rel_formula f p p'" if "p \<in> set pos" for p
    using that list_all2_setD1[OF \<psi>_def(3), of p] part Ands(6)
    by (auto simp: list_all_def)
  have neg'_neg: "\<exists>n \<in> set neg. formula.rel_formula f n n'" if "n' \<in> set neg'" for n'
    using that list_all2_setD2[OF \<psi>_def(3), of n'] part Ands(6)
    by (auto simp: list_all_def)
  have "pos' \<noteq> []"
    using Ands(2) pos_pos'
    by fastforce
  moreover have "safe_formula (remove_neg x')" if "x' \<in> set neg'" for x'
  proof -
    have "formula.rel_formula f (remove_neg g) (remove_neg h)" if "formula.rel_formula f g h" for g h
      using that
      by (cases g; cases h) auto
    then show ?thesis
      using neg'_neg[OF that] Ands(4,7)
      by (auto simp: list_all_def dest!: bspec spec[of _ "remove_neg x'"])
  qed
  moreover have "\<exists>p' \<in> set pos'. x \<in> fv p'" if n': "n' \<in> set neg'" "x \<in> fv n'" for x n'
  proof -
    obtain n where n_def: "n \<in> set neg" "x \<in> fv n"
      using neg'_neg[OF n'(1)] n'(2)
      by (auto simp: rel_formula_fv)
    then obtain p where p_def: "p \<in> set pos" "x \<in> fv p"
      using Ands(5)
      by auto
    show ?thesis
      using pos_pos'[OF p_def(1)] p_def(2)
      by (auto simp: rel_formula_fv)
  qed
  ultimately show ?case
    by (auto simp: \<psi>_def(1,2) list_all_def simp del: partition_filter_conv)
next
  case orig: (Neg \<phi>)
  then show ?case
  proof(cases \<psi>)
    case (Neg \<psi>')
    have *: "formula.rel_formula f \<phi> \<psi>'"
      using orig(4)[unfolded Neg] by auto
    then have fv: "fv \<psi>' = {}" using orig(1) rel_formula_fv by blast
    have aux: "fv \<psi>' = {} \<Longrightarrow> safe_formula \<psi>' \<Longrightarrow> safe_formula (Formula.Neg \<psi>')"
    proof(cases \<psi>')
      fix x y
      assume fv: "fv \<psi>' = {}" and safe: "safe_formula \<psi>'" and eq:  "\<psi>' = formula.Eq x y" 
      show "safe_formula (formula.Neg \<psi>')"
      proof(cases "x \<in> range Formula.Var")
        case True
        then obtain x' where x_def: "x = Formula.Var x'" by auto
        show ?thesis
        proof(cases "y \<in> range Formula.Var")
          case True
          then obtain y' where y_def: "y = Formula.Var y'" by auto
          obtain x'' y'' where "\<phi> = formula.Eq (Formula.Var x'') (Formula.Var y'')"
            using * unfolding eq x_def y_def by (cases \<phi>; auto)
          moreover have "x'' = x'" "y'' = y'" using * unfolding calculation eq x_def y_def by auto
          ultimately show ?thesis using orig(2) unfolding eq x_def y_def safe_formula.simps by auto
        next
          case False
          then show ?thesis using safe fv unfolding eq by(cases y) auto
        qed
      next
        case False
        then show ?thesis using safe fv unfolding eq by(cases x) auto 
      qed
    qed (auto)
    show ?thesis using aux[OF fv orig(3)[OF *]] Neg by auto
  qed auto
next
  case (Or \<phi> \<phi>' \<psi>)
  then show ?case
    by (cases \<psi>) (auto simp: rel_formula_fv)
next
  case (Exists \<phi> t)
  then show ?case
    by (cases \<psi>) (auto simp: rel_formula_fv)
next
  case (Agg y \<omega> tys t \<phi>)
  then show ?case
    using list_all2_lengthD[of f tys]
    by (cases \<psi>) (auto simp: rel_formula_fv)
next
  case (Prev I \<phi>)
  then show ?case
    by (cases \<psi>) auto
next
  case (Next I \<phi>)
  then show ?case
    by (cases \<psi>) auto
next
  case (Since \<phi> I \<phi>' \<psi>)
  then show ?case
    by (cases \<psi>) (auto simp: rel_formula_fv)
next
  case (Not_Since \<phi> I \<phi>' \<psi>)
  then show ?case
    by (cases \<psi>) (auto simp: rel_formula_fv elim!: formula.rel_cases[of _ "formula.Neg \<phi>"])
next
  case (Until \<phi> I \<phi>' \<psi>)
  then show ?case
    by (cases \<psi>) (auto simp: rel_formula_fv)
next
  case (Not_Until \<phi> I \<phi>' \<psi>)
  then show ?case
    by (cases \<psi>) (auto simp: rel_formula_fv elim!: formula.rel_cases[of _ "formula.Neg \<phi>"])
next
  case (MatchP I r)
  have "regex.rel_regex (formula.rel_formula f) r r' \<Longrightarrow> safe_regex Past Strict r'" for r'
    apply (rule rel_regex_safe_aux[OF MatchP(1), where ?P="formula.rel_formula f"])
    using MatchP(2)     
    by (auto simp: rel_formula_fv split: formula.splits)
  then show ?case
    using MatchP
    by (cases \<psi>) auto
next
  case (MatchF I r)
  have "regex.rel_regex (formula.rel_formula f) r r' \<Longrightarrow> safe_regex Futu Strict r'" for r'
    apply (rule rel_regex_safe_aux[OF MatchF(1), where ?P="formula.rel_formula f"])
    using MatchF(2)
    by (auto simp: rel_formula_fv split: formula.splits)
  then show ?case
    using MatchF
    by (cases \<psi>) auto
next
  case (LetPast p \<phi> \<psi>')
  obtain \<phi>' \<psi>'' where \<psi>_def: "\<psi> = formula.LetPast p \<phi>' \<psi>''"
    using LetPast(7) by (cases \<psi>; auto)
  have rels: "formula.rel_formula f \<phi> \<phi>'" "formula.rel_formula f \<psi>' \<psi>''"
    using LetPast(7)[unfolded \<psi>_def] by auto
  have safes: "safe_formula \<phi>'" "safe_formula \<psi>''" using LetPast(5)[OF rels(1)] LetPast(6)[OF rels(2)] by auto
  have "fv \<phi> = fv \<phi>'" using rels(1) rel_formula_fv by blast
  moreover have nfv_eq: "Formula.nfv \<phi> = Formula.nfv \<phi>'" using calculation by (simp add: Formula.nfv_def)
  ultimately have fvi: "{0..<Formula.nfv \<phi>'} \<subseteq> fv \<phi>'" using LetPast(2) by auto
  thm rel_formula_fv[OF rels(1), of 0]
  have "safe_letpast (p, Formula.nfv \<phi>') \<phi>' \<le> PastRec" 
    using LetPast.hyps(1)[unfolded rel_formula_safe_letpast[OF rels(1)]] nfv_eq by force
  then show ?case unfolding \<psi>_def safe_formula.simps using safes fvi by auto
next
  case (TP t)
  then show ?case by (cases \<psi>; auto)
next
  case (TS t)
  then show ?case by (cases \<psi>; auto)
qed

lemma list_all2_swap: "list_all2 f xs ys \<Longrightarrow> list_all2 (\<lambda>x y. f y x) ys xs"
  by (induction xs ys rule: list.rel_induct) auto

lemma rel_regex_swap: "regex.rel_regex f r r' \<Longrightarrow> regex.rel_regex (\<lambda>x y. f y x) r' r"
  by (induction r r' rule: regex.rel_induct) auto

lemma rel_formula_swap: "formula.rel_formula f x y \<Longrightarrow> formula.rel_formula (\<lambda>x y. f y x) y x"
  by (induction x y rule: formula.rel_induct) (auto intro: list_all2_swap rel_regex_swap)

lemma rel_regex_safe:
  assumes "Regex.rel_regex (formula.rel_formula f) r r'" "safe_regex m g r"
  shows "safe_regex m g r'"
proof -
  have rel_Neg: "\<And>\<phi> \<phi>'. formula.rel_formula f (formula.Neg \<phi>) \<phi>' \<Longrightarrow>
    case \<phi>' of formula.Neg x \<Rightarrow> formula.rel_formula f \<phi> x | _ \<Rightarrow> False"
    by (auto split: formula.splits)
  show ?thesis
    using rel_regex_safe_aux[OF _ _ _ rel_Neg assms(1)] rel_formula_safe assms(2)
    by (fastforce simp: rel_formula_fv)
qed

lemma rel_regex_atms:
  assumes "Regex.rel_regex (formula.rel_formula f) r r'" "x \<in> atms r"
  shows "\<exists>x' \<in> atms r'. formula.rel_formula f x x'"
proof -
  obtain \<phi> where \<phi>_def: "\<phi> \<in> Regex.atms r" "safe_formula \<phi> \<Longrightarrow> \<phi> = x"
    "\<not>safe_formula \<phi> \<Longrightarrow> \<phi> = formula.Neg x"
    using assms(2)
    by (auto simp: atms_def) (force split: formula.splits)
  obtain x' where x'_def: "x' \<in> regex.atms r'" "formula.rel_formula f \<phi> x'"
    using rel_regex_regex_atms[OF assms(1) \<phi>_def(1)]
    by auto
  show ?thesis
  proof (cases "safe_formula \<phi>")
    case True
    then show ?thesis
      using x'_def rel_formula_safe[OF True x'_def(2)]
      by (auto simp: \<phi>_def(2)[OF True] atms_def intro!: UN_I[OF x'_def(1)] bexI[of _ x'])
  next
    case False
    obtain x'' where x''_def: "x' = formula.Neg x''" "formula.rel_formula f x x''"
      using x'_def(2)
      by (cases x') (auto simp: \<phi>_def(3)[OF False])    
    show ?thesis
      using x''_def(2) rel_formula_safe[OF _ rel_formula_swap[OF x'_def(2)]] False
      unfolding atms_def
      by (fastforce simp: x''_def intro!: UN_I[OF x'_def(1)] bexI[of _ x''])
  qed
qed

lemma fv_safe_regex_atms: "safe_regex m g r \<Longrightarrow> x \<in> Regex.fv_regex Formula.fv r \<Longrightarrow>
  \<exists>\<phi> \<in> atms r. safe_formula \<phi> \<and> x \<in> Formula.fv \<phi>"
proof (induction r)
  case (Test z)
  then show ?case
    by (cases z) (auto simp: atms_def)
next
  case (Times r1 r2)
  then show ?case
    by (cases m) auto
qed auto

lemma pred_regex_wty_formula: "regex.pred_regex (wty_formula S E) r \<Longrightarrow> \<phi> \<in> atms r \<Longrightarrow> S, E \<turnstile> \<phi>"
  by (induction r) (auto split: if_splits formula.splits elim: wty_formula.cases)

lemma wty_trm_cong_aux: "E \<turnstile> t :: typ \<Longrightarrow> E \<turnstile> t :: typ' \<Longrightarrow> typ = typ'"
proof (induction t "typ" arbitrary: typ' rule: wty_trm.induct)
  case (Plus x t y)
  have "E \<turnstile> x :: typ'"
    using Plus(6)
    by (auto elim: wty_trm.cases)
  then show ?case
    using Plus(4)
    by auto
next
  case (Minus x t y)
  have "E \<turnstile> x :: typ'"
    using Minus(6)
    by (auto elim: wty_trm.cases)
  then show ?case
    using Minus(4)
    by auto
next
  case (UMinus x t)
  then show ?case
    by (fastforce elim!: wty_trm.cases[of E "trm.UMinus x" typ'])
next
  case (Mult x t y)
  have "E \<turnstile> x :: typ'"
    using Mult(6)
    by (auto elim: wty_trm.cases)
  then show ?case
    using Mult(4)
    by auto
next
  case (Div x t y)
  have "E \<turnstile> x :: typ'"
    using Div(6)
    by (auto elim: wty_trm.cases)
  then show ?case
    using Div(4)
    by auto
next
  case (Mod x y)
  have "E \<turnstile> x :: typ'"
    using Mod(5)
    by (auto elim: wty_trm.cases)
  then show ?case
    using Mod(3)
    by auto
next
  case (F2i x)
  then show ?case
    by (fastforce elim!: wty_trm.cases[of E "trm.F2i x" typ'])
next
  case (I2f x)
  then show ?case
    by (fastforce elim!: wty_trm.cases[of E "trm.I2f x" typ'])
qed (auto elim: wty_trm.cases)

lemma wty_trm_cong: " (\<And>y. y \<in> fv_trm t \<Longrightarrow> E y = E' y) \<Longrightarrow>
  E \<turnstile> t :: typ \<Longrightarrow> E' \<turnstile> t :: typ' \<Longrightarrow> typ = typ'"
  using wty_trm_fv_cong wty_trm_cong_aux
  by blast

lemma wty_safe_assignment_dest: "wty_formula S E \<psi> \<Longrightarrow> safe_assignment X \<psi> \<Longrightarrow> x \<in> fv \<psi> - X \<Longrightarrow>
  \<exists>t. E \<turnstile> t :: E x \<and> fv_trm t \<subseteq> X \<and> (\<psi> = formula.Eq (trm.Var x) t \<or> \<psi> = formula.Eq t (trm.Var x))"
  by (auto simp: safe_assignment_def elim!: wty_formula.cases[of S E \<psi>])
     (auto elim!: wty_trm.cases[of E "trm.Var x"] split: trm.splits)

(*Lemma 5.1
lemma rel_formula_wty_unique_fv: "safe_formula \<phi> \<Longrightarrow> wty_formula S E \<phi> \<Longrightarrow> wty_formula S E' \<phi>' \<Longrightarrow>
  Formula.rel_formula f \<phi> \<phi>' \<Longrightarrow> x \<in> fv \<phi> \<Longrightarrow> E x = E' x"
proof (induction \<phi> arbitrary: S E E' \<phi>' x rule: safe_formula_induct)
  case (Eq_Var1 c y)
  then show ?case
    by (auto elim!: wty_formula.cases[of S E "formula.Eq (trm.Const c) (trm.Var y)"] wty_formula.cases[of S E' \<phi>'])
       (auto elim!: wty_trm.cases[of E] wty_trm.cases[of E'])
next
  case (Eq_Var2 c y)
  then show ?case
    by (auto elim!: wty_formula.cases[of S E "formula.Eq (trm.Var y) (trm.Const c)"] wty_formula.cases[of S E' \<phi>'])
       (auto elim!: wty_trm.cases[of E] wty_trm.cases[of E'])
next
  case (Pred e ts)
  then show ?case
    apply (auto elim!: wty_formula.cases[of S E "formula.Pred e ts"] wty_formula.cases[of S E' \<phi>'])
    subgoal for t tys
      apply (cases t)
               apply (auto simp: list_all2_conv_all_nth elim!: wty_trm.cases[of _ "trm.Var x"])
      apply (auto simp: in_set_conv_nth)
      apply (auto dest!: spec elim!: wty_trm.cases[of _ "trm.Var x"])
      done
    done
next
  case (Let p \<phi> \<phi>' S E E' \<alpha>)
  obtain \<psi> \<psi>' where \<alpha>_def: "\<alpha> = formula.Let p \<psi> \<psi>'"
    "formula.rel_formula f \<phi> \<psi>" "formula.rel_formula f \<phi>' \<psi>'"
    using Let(8)
    by (cases \<alpha>) auto
  obtain F where F_def: "S, F \<turnstile> \<phi>"
    "S((p, Formula.nfv \<phi>) \<mapsto> tabulate F 0 (Formula.nfv \<phi>)), E \<turnstile> \<phi>'"
    using Let(6)
    by (auto elim: wty_formula.cases)
  obtain F' where F'_def: "S, F' \<turnstile> \<psi>"
    "S((p, Formula.nfv \<psi>) \<mapsto> tabulate F' 0 (Formula.nfv \<psi>)), E' \<turnstile> \<psi>'"
    using Let(7)
    by (auto simp: \<alpha>_def(1) elim: wty_formula.cases)
  have nfv: "Formula.nfv \<phi> = Formula.nfv \<psi>"
    using \<alpha>_def(2)
    by (auto simp: Formula.nfv_def rel_formula_fv)
  have tab: "tabulate F 0 (Formula.nfv \<psi>) = tabulate F' 0 (Formula.nfv \<psi>)"
    using Let(1) Let(4)[OF F_def(1) F'_def(1) \<alpha>_def(2)]
    by (auto simp: nfv tabulate_alt)
  show ?case
    using Let(5)[OF F_def(2) F'_def(2)[folded tab nfv] \<alpha>_def(3)] Let(9)
    by auto
next
  case (And_assign \<phi> \<psi> S E E' \<alpha>)
  have case_\<phi>: "E z = E' z" if "z \<in> fv \<phi>" for z
    using And_assign that
    by (auto elim!: wty_formula.cases[of S E "Formula.And \<phi> \<psi>"] wty_formula.cases[of S E' \<alpha>])
  {
    assume notin: "x \<notin> fv \<phi>"
    obtain \<phi>' \<psi>' where \<alpha>_def: "\<alpha> = Formula.And \<phi>' \<psi>'"
      "Formula.rel_formula f \<phi> \<phi>'" "Formula.rel_formula f \<psi> \<psi>'"
      using And_assign
      by (cases \<alpha>) auto
    obtain t where t_def: "E \<turnstile> t :: E x" "fv_trm t \<subseteq> fv \<phi>"
      "\<psi> = formula.Eq (trm.Var x) t \<or> \<psi> = formula.Eq t (trm.Var x)"
      using wty_safe_assignment_dest[of S E \<psi> "fv \<phi>" x] notin And_assign(2,4,7)
      by (auto elim: wty_formula.cases)
    have "safe_assignment (fv \<phi>') \<psi>'"
      using And_assign(2) \<alpha>_def(2,3)
      by (auto simp: rel_formula_fv safe_assignment_def split: formula.splits)
    then obtain t' where t'_def: "E' \<turnstile> t' :: E' x" "fv_trm t' \<subseteq> fv \<phi>'"
      "\<psi>' = formula.Eq (trm.Var x) t' \<or> \<psi>' = formula.Eq t' (trm.Var x)"
      using wty_safe_assignment_dest[of S E' \<psi>' "fv \<phi>'" x] notin And_assign(2,5,7) \<alpha>_def(2,3)
      by (auto simp: \<alpha>_def(1) rel_formula_fv elim: wty_formula.cases)
    have ?case
      using t_def t'_def \<alpha>_def(2,3) wty_trm_cong[of t' E E', OF case_\<phi>]
      by (fastforce simp: rel_formula_fv)
  }
  then show ?case
    using case_\<phi>
    by (cases "x \<in> fv \<phi>") auto
next
  case (And_safe \<phi> \<psi> S E E' \<alpha>)
  then show ?case
    by (auto elim!: wty_formula.cases[of S E "Formula.And \<phi> \<psi>"] wty_formula.cases[of S E' \<alpha>])
next
  case (And_constraint \<phi> \<psi> S E E' \<alpha>)
  then show ?case
    by (auto elim!: wty_formula.cases[of S E "Formula.And \<phi> \<psi>"] wty_formula.cases[of S E' \<alpha>])
next
  case (And_Not \<phi> \<psi> S E E' \<alpha>)
  then show ?case
    by (auto elim!: wty_formula.cases[of S E "Formula.And \<phi> (Formula.Neg \<psi>)"] wty_formula.cases[of S E' \<alpha>])
next
  case (Ands l pos neg S E E' \<psi>)
  obtain l' pos' neg' where \<psi>_def: "\<psi> = formula.Ands l'" "partition safe_formula l' = (pos', neg')"
    "list_all2 (formula.rel_formula f) l l'"
    using Ands(10)
    by (cases \<psi>) auto
  note part = partition_P[OF Ands(1)[symmetric]] partition_P[OF \<psi>_def(2)] partition_set[OF Ands(1)[symmetric], symmetric]
    partition_set[OF \<psi>_def(2), symmetric]
  have pos_pos': "\<exists>p' \<in> set pos'. formula.rel_formula f p p'" if "p \<in> set pos" for p
    using that list_all2_setD1[OF \<psi>_def(3), of p] part rel_formula_safe
    by (fastforce simp: list_all_def)
  obtain p where p_def: "p \<in> set pos" "x \<in> fv p"
    using Ands(5,11) part
    by auto
  then obtain p' where p'_def: "p' \<in> set pos'" "formula.rel_formula f p p'"
    using pos_pos'
    by auto
  show ?case
    using Ands(6,8,9) part(3,4) p_def p'_def
    by (force simp: list_all_def \<psi>_def(1) elim!: wty_formula.cases[of S _ "formula.Ands _"])
next
  case (Neg \<phi>)
  then show ?case
    by (auto elim!: wty_formula.cases[of S E "formula.Neg \<phi>"] wty_formula.cases[of S E' \<phi>'])
next
  case (Or \<phi> \<psi> S E E' \<alpha>)
  then show ?case
    by (auto elim!: wty_formula.cases[of S E "Formula.Or \<phi> \<psi>"] wty_formula.cases[of S E' \<alpha>])
next
  case (Exists t \<phi>)
  then show ?case
    by (fastforce simp: fvi_Suc elim!: wty_formula.cases[of S E "Formula.Exists t \<phi>"] wty_formula.cases[of S E' \<phi>'])
next
  case (Agg y \<omega> tys trm \<phi> S E E' \<psi>)
  obtain agg_type d where \<omega>_def: "\<omega> = (agg_type, d)"
    by fastforce
  obtain t where wty_\<phi>: "S, agg_env E tys \<turnstile> \<phi>" "E y = t_res agg_type t" "agg_env E tys \<turnstile> trm :: t"
    using Agg
    by (auto simp: \<omega>_def elim!: wty_formula.cases[of S E "formula.Agg y (agg_type, d) tys trm \<phi>"])
  obtain tys' \<phi>' d' where \<psi>_def: "\<psi> = formula.Agg y (agg_type, d') tys' trm \<phi>'"
    "formula.rel_formula f \<phi> \<phi>'" "list_all2 f tys tys'" 
    using Agg(8) \<omega>_def
    by (cases \<psi>) auto 
  have tys_tys': "length tys = length tys'"
    using \<psi>_def(3) 
    by (auto simp: list_all2_lengthD)
  obtain t' where wty_\<phi>': "S, agg_env E' tys' \<turnstile> \<phi>'" "E' y = t_res agg_type t'" "agg_env E' tys' \<turnstile> trm :: t'"
    using Agg(7)
    by (auto simp: \<psi>_def(1) \<omega>_def elim!: wty_formula.cases[of S E' "formula.Agg y (agg_type, d') tys' trm \<phi>'"])
  note IH = Agg(5)[OF order.refl Agg(4) wty_\<phi>(1) wty_\<phi>'(1) \<psi>_def(2)]
  {
    assume x: "x \<in> fv (formula.Agg y \<omega> tys trm \<phi>)" "x \<noteq> y"
    have x_fv_\<phi>: "x + length tys \<in> fv \<phi>"
      using Agg(3) x
      by (auto simp: fvi_iff_fv[where ?b="length tys"] fvi_trm_iff_fv_trm[where ?b="length tys"])
    have "E x = E' x"
      using IH[OF x_fv_\<phi>]
      by (auto simp: agg_env_def tys_tys')
  }
  then show ?case
    using Agg(3,9) wty_\<phi>(3) wty_\<phi>'(3) wty_trm_cong[of trm "agg_env E tys" "agg_env E' tys'", OF IH]
    by (cases "x = y") (auto simp: \<psi>_def(1) wty_\<phi>(2) wty_\<phi>'(2))
next
  case (Prev I \<phi>)
  then show ?case
    by (auto elim!: wty_formula.cases[of S E "formula.Prev I \<phi>"] wty_formula.cases[of S E' \<phi>'])
next
  case (Next I \<phi>)
  then show ?case
    by (auto elim!: wty_formula.cases[of S E "formula.Next I \<phi>"] wty_formula.cases[of S E' \<phi>'])
next
  case (Since \<phi> I \<psi> S E E' \<alpha>)
  then show ?case
    by (auto elim!: wty_formula.cases[of S E "Formula.Since \<phi> I \<psi>"] wty_formula.cases[of S E' \<alpha>])
next
  case (Not_Since \<phi> I \<psi> S E E' \<alpha>)
  then show ?case
    by (auto elim!: wty_formula.cases[of S E "Formula.Since (Formula.Neg \<phi>) I \<psi>"] wty_formula.cases[of S E' \<alpha>])
next
  case (Until \<phi> I \<psi> S E E' \<alpha>)
  then show ?case
    by (auto elim!: wty_formula.cases[of S E "Formula.Until \<phi> I \<psi>"] wty_formula.cases[of S E' \<alpha>])
next
  case (Not_Until \<phi> I \<psi> S E E' \<alpha>)
  then show ?case
    by (auto elim!: wty_formula.cases[of S E "Formula.Until (Formula.Neg \<phi>) I \<psi>"] wty_formula.cases[of S E' \<alpha>])
next
  case (MatchP I r)
  obtain r' where r'_def: "\<phi>' = formula.MatchP I r'" "Regex.rel_regex (formula.rel_formula f) r r'"
    using MatchP(5)
    by (cases \<phi>') auto
  obtain a where a_def: "a \<in> atms r" "x \<in> fv a"
    using MatchP(6) fv_safe_regex_atms[OF MatchP(1)]
    by force
  obtain a' where a'_def: "a' \<in> atms r'" "formula.rel_formula f a a'"
    using rel_regex_atms[OF r'_def(2) a_def(1)]
    by auto
  have wty: "S, E \<turnstile> a" "S, E' \<turnstile> a'"
    using MatchP(3,4) a_def(1) a'_def(1)
    by (auto simp: r'_def(1) elim!: wty_formula.cases[of S E "formula.MatchP I r"]
        wty_formula.cases[of S E' "formula.MatchP I r'"] intro: pred_regex_wty_formula)
  show ?case
    using MatchP(2) a_def(1) wty a'_def(2) a_def(2)
    by auto
next
  case (MatchF I r)
  obtain r' where r'_def: "\<phi>' = formula.MatchF I r'" "Regex.rel_regex (formula.rel_formula f) r r'"
    using MatchF(5)
    by (cases \<phi>') auto
  obtain a where a_def: "a \<in> atms r" "x \<in> fv a"
    using MatchF(6) fv_safe_regex_atms[OF MatchF(1)]
    by force
  obtain a' where a'_def: "a' \<in> atms r'" "formula.rel_formula f a a'"
    using rel_regex_atms[OF r'_def(2) a_def(1)]
    by auto
  have wty: "S, E \<turnstile> a" "S, E' \<turnstile> a'"
    using MatchF(3,4) a_def(1) a'_def(1)
    by (auto simp: r'_def(1) elim!: wty_formula.cases[of S E "formula.MatchF I r"]
        wty_formula.cases[of S E' "formula.MatchF I r'"] intro: pred_regex_wty_formula)
  show ?case
    using MatchF(2) a_def(1) wty a'_def(2) a_def(2)
    by auto
next
  case (LetPast p \<phi> \<psi> S E E' \<alpha>)
  obtain \<phi>' \<psi>' where \<alpha>_def: "\<alpha> = formula.LetPast p \<phi>' \<psi>'"
    "formula.rel_formula f \<phi> \<phi>'" "formula.rel_formula f \<psi> \<psi>'"
    using LetPast(9)
    by (cases \<alpha>) auto
  obtain F where F_def: "S((p, Formula.nfv \<phi>) \<mapsto> tabulate F 0 (Formula.nfv \<phi>)), F \<turnstile> \<phi>"
    "S((p, Formula.nfv \<phi>) \<mapsto> tabulate F 0 (Formula.nfv \<phi>)), E \<turnstile> \<psi>"
    using LetPast(7) by (auto elim: wty_formula.cases)
  obtain F' where F'_def: "S((p, Formula.nfv \<phi>') \<mapsto> tabulate F' 0 (Formula.nfv \<phi>')), F' \<turnstile> \<phi>'"
    "S((p, Formula.nfv \<phi>') \<mapsto> tabulate F' 0 (Formula.nfv \<phi>')), E' \<turnstile> \<psi>'"
    using LetPast(8) unfolding \<alpha>_def(1)
    by (auto elim: wty_formula.cases)
  have nfv: "Formula.nfv \<phi> = Formula.nfv \<phi>'"
    using \<alpha>_def(2)
    by (auto simp: Formula.nfv_def rel_formula_fv)
  have tab: "tabulate F 0 (Formula.nfv \<phi>) = tabulate F' 0 (Formula.nfv \<phi>)"
    using LetPast(1) LetPast(5) sorry
  show ?case sorry
next
  case (TP t)
  then show ?case 
    using wty_trm_eq
    by (auto elim!: wty_formula.cases[of S E "formula.TP t"] wty_formula.cases[of S E' \<phi>'])
next
  case (TS t)
  then show ?case
    using wty_trm_eq
    by (auto elim!: wty_formula.cases[of S E "formula.TS t"] wty_formula.cases[of S E' \<phi>'])
qed auto *)

lemma safe_regex_regex_atms_dest:
  assumes "safe_regex m g r" "a \<in> regex.atms r"
  shows "safe_formula a \<and> a \<in> atms r \<or> (\<not>safe_formula a \<and> (case a of formula.Neg \<phi> \<Rightarrow> \<phi> \<in> atms r | _ \<Rightarrow> False))"
  using assms
proof (induction m g r rule: safe_regex.induct)
  case (2 m g \<phi>)
  then show ?case
    by (cases "safe_formula a") (auto split: formula.splits)
next
  case (3 m g r s)
  then show ?case
    by (cases a) auto
next
  case (4 g r s)
  then show ?case
    by (cases a) auto
next
  case (5 g r s)
  then show ?case
    by (cases a) auto
next
  case (6 m g r)
  then show ?case
    by (cases a) auto
qed (auto split: formula.splits)

(*Lemma 5.2
lemma rel_formula_wty_unique_bv_aux: "safe_formula \<phi> \<Longrightarrow> wty_formula S E \<phi> \<Longrightarrow> wty_formula S E' \<phi>' \<Longrightarrow>
  Formula.rel_formula f \<phi> \<phi>' \<Longrightarrow> Formula.rel_formula (=) \<phi> \<phi>'"
proof (induction \<phi> arbitrary: S E E' \<phi>' rule: safe_formula_induct)
  case (Eq_Const c d)
  then show ?case
    by (cases \<phi>') auto
next
  case (Eq_Var1 c x)
  then show ?case
    by (cases \<phi>') auto
next
  case (Eq_Var2 c x)
  then show ?case
    by (cases \<phi>') auto
next
  case (Pred e ts)
  then show ?case
    by (cases \<phi>') auto
next
  case (Let p \<phi> \<phi>' S E E' \<alpha>)
  obtain \<psi> \<psi>' where \<alpha>_def: "\<alpha> = formula.Let p \<psi> \<psi>'"
    "formula.rel_formula f \<phi> \<psi>" "formula.rel_formula f \<phi>' \<psi>'"
    using Let(8)
    by (cases \<alpha>) auto
  obtain F where F_def: "S, F \<turnstile> \<phi>"
    "S((p, Formula.nfv \<phi>) \<mapsto> tabulate F 0 (Formula.nfv \<phi>)), E \<turnstile> \<phi>'"
    using Let(6)
    by (auto elim: wty_formula.cases)
  obtain F' where F'_def: "S, F' \<turnstile> \<psi>"
    "S((p, Formula.nfv \<psi>) \<mapsto> tabulate F' 0 (Formula.nfv \<psi>)), E' \<turnstile> \<psi>'"
    using Let(7)
    by (auto simp: \<alpha>_def(1) elim: wty_formula.cases)
  have nfv: "Formula.nfv \<phi> = Formula.nfv \<psi>"
    using \<alpha>_def(2)
    by (auto simp: Formula.nfv_def rel_formula_fv)
  have tab: "tabulate F 0 (Formula.nfv \<psi>) = tabulate F' 0 (Formula.nfv \<psi>)"
    using Let(1) rel_formula_wty_unique_fv[OF Let(2) F_def(1) F'_def(1) \<alpha>_def(2)]
    by (auto simp: nfv tabulate_alt)
  show ?case
    using Let(4)[OF F_def(1) F'_def(1) \<alpha>_def(2)]
      Let(5)[OF F_def(2) F'_def(2)[folded tab nfv] \<alpha>_def(3)]
    by (auto simp: \<alpha>_def(1))
next
  case (And_assign \<phi> \<psi>)
  then show ?case
    apply (cases \<phi>')
                    apply (auto elim!: wty_formula.cases[of _ _ "formula.And _ _"])
    subgoal for x' y'
      by (cases \<psi>; cases y') (auto simp: safe_assignment_def)
    done
next
  case (And_safe \<phi> \<psi>)
  then show ?case
    by (cases \<phi>') (auto elim!: wty_formula.cases[of _ _ "formula.And _ _"])
next
  case (And_constraint \<phi> \<psi>)
  then show ?case
    apply (cases \<phi>')
                    apply (auto elim!: wty_formula.cases[of _ _ "formula.And _ _"])
    subgoal for x' y'
      by (cases \<psi> rule: is_constraint.cases; cases y' rule: is_constraint.cases) auto
    done
next
  case (And_Not \<phi> \<psi>)
  then show ?case
    apply (cases \<phi>') apply (auto elim!: wty_formula.cases[of _ _ "formula.And _ _"])
    subgoal for x y z
      by (cases z) (auto elim!: wty_formula.cases[of _ _ "formula.Neg _"])
    done
next
  case (Ands l pos neg)
  have not_safe: "(case z of formula.Neg \<phi> \<Rightarrow> True | _ \<Rightarrow> False)" if "\<not>safe_formula z" "z \<in> set l" for z
    using Ands that
    by (cases z) (auto simp: list_all_def simp del: safe_formula.simps)
  have "formula.rel_formula (=) z z'"
    if prems: "z \<in> set l" "z' \<in> set l'" "formula.rel_formula f z z'" "\<phi>' = formula.Ands l'" for z z' l'
  proof (cases "safe_formula z")
    case True
    then show ?thesis
      using Ands that
      by (fastforce simp: list_all_def elim!: wty_formula.cases[of _ _ "formula.Ands _"])
  next
    case False
    obtain \<phi> where z_def: "z = formula.Neg \<phi>"
      using not_safe[OF False prems(1)]
      by (auto split: formula.splits)
    show ?thesis
      using prems(3)
      apply (cases z')
                      apply (auto simp: z_def)
      using Ands prems False
      by (fastforce simp: list_all_def z_def elim!: wty_formula.cases[of _ _ "formula.Ands _"] wty_formula.cases[of _ _ "formula.Neg _"] dest!: bspec[of "set l" _ "formula.Neg \<phi>"]
          bspec[of "set l'" _ "formula.Neg _"])
  qed
  then show ?case
    using Ands
    apply (cases \<phi>')
                    apply (auto simp: list_all_def)
    apply (rule list.rel_mono_strong)
     apply fastforce+
    done
next
  case (Neg \<phi>)
  then show ?case
    by (cases \<phi>') (auto elim!: wty_formula.cases[of _ _ "formula.Neg _"])
next
  case (Or \<phi> \<psi>)
  then show ?case
    by (cases \<phi>') (auto elim!: wty_formula.cases[of _ _ "formula.Or _ _"])
next
  case (Exists \<phi> t)
  then show ?case
    using rel_formula_wty_unique_fv[where ?x=0]
    by (cases \<phi>') (fastforce elim!: wty_formula.cases[of _ _ "formula.Exists _ _ "])+
next
  case (Agg y \<omega> tys trm \<phi> S E E' \<psi>)
  obtain agg_type d where split: "\<omega>  = (agg_type, d)" using Agg by (meson surj_pair)
  then obtain tys' \<phi>' d' where \<psi>_def: "\<psi> = formula.Agg y (agg_type, d') tys' trm \<phi>'" "list_all2 f tys tys'" "f d d'"
    using Agg
    by (cases \<psi>) auto
  have safe: "safe_formula (formula.Agg y \<omega> tys trm \<phi>)" using Agg by auto
  have "d = E y" using Agg(6) split by(auto elim:wty_formula.cases)
  moreover have "d' = E' y" using Agg(7)[unfolded \<psi>_def(1)] by(auto elim:wty_formula.cases)
  ultimately have d_eq: "d = d'" 
      using rel_formula_wty_unique_fv[OF safe Agg(6-8)] by auto
  have "agg_env E tys x = agg_env E' tys' x" if "x \<in> fv \<phi>" for x
    using Agg rel_formula_wty_unique_fv[OF Agg(4) _ _ _ that, of S "agg_env E tys" "agg_env E' tys'" \<phi>' f]
    by (auto simp: \<psi>_def(1) elim!: wty_formula.cases[of _ _ "formula.Agg _ _ _ _ _"])
  then have "list_all2 (=) tys tys'"
    using Agg(2) \<psi>_def(2)
    by (fastforce simp: list_all2_conv_all_nth agg_env_def)
  then show ?case
    using Agg split d_eq by (auto simp: \<psi>_def(1) elim!: wty_formula.cases[of _ _ "formula.Agg _ _ _ _ _"])
next
  case (Prev I \<phi>)
  then show ?case
    by (cases \<phi>') (auto elim!: wty_formula.cases[of _ _ "formula.Prev _ _"])
next
  case (Next I \<phi>)
  then show ?case
    by (cases \<phi>') (auto elim!: wty_formula.cases[of _ _ "formula.Next _ _"])
next
  case (Since \<phi> I \<psi>)
  then show ?case
    by (cases \<phi>') (auto elim!: wty_formula.cases[of _ _ "formula.Since _ _ _"])
next
  case (Not_Since \<phi> I \<psi>)
  then show ?case
    apply (cases \<phi>')
                    apply (auto elim!: wty_formula.cases[of _ _ "formula.Since _ _ _"])
    subgoal for x y z
      by (cases y) (auto elim!: wty_formula.cases[of _ _ "formula.Neg _"])
    done
next
  case (Until \<phi> I \<psi>)
  then show ?case
    by (cases \<phi>') (auto elim!: wty_formula.cases[of _ _ "formula.Until _ _ _"])
next
  case (Not_Until \<phi> I \<psi>)
  then show ?case
    apply (cases \<phi>')
                    apply (auto elim!: wty_formula.cases[of _ _ "formula.Until _ _ _"])
    subgoal for x y z
      by (cases y) (auto elim!: wty_formula.cases[of _ _ "formula.Neg _"])
    done
next
  case (MatchP I r)
  obtain r' where r'_def: "\<phi>' = formula.MatchP I r'" "Regex.rel_regex (formula.rel_formula f) r r'"
    using MatchP(5)
    by (cases \<phi>') auto
  show ?case
    using MatchP
    apply (auto simp: r'_def(1))
    apply (rule regex.rel_mono_strong)
     apply assumption
    subgoal for z z'
      using rel_regex_safe[of f r r' Past Strict]
        safe_regex_regex_atms_dest[of Past Strict r z]
        safe_regex_regex_atms_dest[of Past Strict r' z']
      apply (auto elim!: wty_formula.cases[of _ _ "formula.MatchP _ _"])
      using pred_regex_wty_formula[of S E r] pred_regex_wty_formula[of S E' r']
         apply fastforce
        apply (meson rel_formula_safe)
      using rel_formula_safe rel_formula_swap apply blast
      subgoal
        apply (cases z; cases z')
                            apply auto
        using pred_regex_wty_formula[of S E r] pred_regex_wty_formula[of S E' r']
        by (fastforce elim!: wty_formula.cases[of _ _ "formula.Neg _"])+
      done
    done
next
  case (MatchF I r)
  obtain r' where r'_def: "\<phi>' = formula.MatchF I r'" "Regex.rel_regex (formula.rel_formula f) r r'"
    using MatchF(5)
    by (cases \<phi>') auto
  show ?case
    using MatchF
    apply (auto simp: r'_def(1))
    apply (rule regex.rel_mono_strong)
     apply assumption
    subgoal for z z'
      using rel_regex_safe[of f r r' Futu Strict]
        safe_regex_regex_atms_dest[of Futu Strict r z]
        safe_regex_regex_atms_dest[of Futu Strict r' z']
      apply (auto elim!: wty_formula.cases[of _ _ "formula.MatchF _ _"])
      using pred_regex_wty_formula[of S E r] pred_regex_wty_formula[of S E' r']
         apply fastforce
        apply (meson rel_formula_safe)
      using rel_formula_safe rel_formula_swap apply blast
      subgoal
        apply (cases z; cases z')
                            apply auto
        using pred_regex_wty_formula[of S E r] pred_regex_wty_formula[of S E' r']
        by (fastforce elim!: wty_formula.cases[of _ _ "formula.Neg _"])+
      done
    done
next
  case (LetPast p \<phi> \<psi> S E E' \<alpha>)
   obtain \<phi>' \<psi>' where \<alpha>_def: "\<alpha> = formula.LetPast p \<phi>' \<psi>'"
    "formula.rel_formula f \<phi> \<phi>'" "formula.rel_formula f \<psi> \<psi>'"
    using LetPast(9)
    by (cases \<alpha>) auto
  obtain F where F_def: "S((p, Formula.nfv \<phi>) \<mapsto> tabulate F 0 (Formula.nfv \<phi>)), F \<turnstile> \<phi>"
    "S((p, Formula.nfv \<phi>) \<mapsto> tabulate F 0 (Formula.nfv \<phi>)), E \<turnstile> \<psi>"
    using LetPast(7)
    by (auto elim: wty_formula.cases)
  obtain F' where F'_def: "S((p, Formula.nfv \<phi>') \<mapsto> tabulate F' 0 (Formula.nfv \<phi>')), F' \<turnstile> \<phi>'"
    "S((p, Formula.nfv \<phi>') \<mapsto> tabulate F' 0 (Formula.nfv \<phi>')), E' \<turnstile> \<psi>'"
    using LetPast(8)
    by (auto simp: \<alpha>_def(1) elim: wty_formula.cases)
  have nfv: "Formula.nfv \<phi> = Formula.nfv \<phi>'"
    using \<alpha>_def(2)
    by (auto simp: Formula.nfv_def rel_formula_fv)
  have tab: "tabulate F 0 (Formula.nfv \<phi>') = tabulate F' 0 (Formula.nfv \<phi>')"
    sorry
  thm rel_formula_wty_unique_fv
  thm LetPast(5)[OF _ _ \<alpha>_def(2)]
  show ?case using LetPast(5)
next
  case (TP t)
  then show ?case by(cases \<phi>') auto
next
  case (TS t)
  then show ?case by(cases \<phi>') auto
qed*)

lemma list_all2_eq: "list_all2 (=) xs ys \<Longrightarrow> xs = ys"
  by (induction xs ys rule: list.rel_induct) auto

lemma rel_regex_eq: "regex.rel_regex (=) r r' \<Longrightarrow> r = r'"
  by (induction r r' rule: regex.rel_induct) auto

lemma rel_formula_eq: "Formula.rel_formula (=) \<phi> \<phi>' \<Longrightarrow> \<phi> = \<phi>'"
  by (induction \<phi> \<phi>' rule: formula.rel_induct) (auto simp: list_all2_eq rel_regex_eq)

(*lemma rel_formula_wty_unique_bv: "safe_formula \<phi> \<Longrightarrow> wty_formula S E \<phi> \<Longrightarrow> wty_formula S E' \<phi>' \<Longrightarrow>
  Formula.rel_formula f \<phi> \<phi>' \<Longrightarrow> \<phi> = \<phi>'"
  using rel_formula_wty_unique_bv_aux
  by (auto simp: rel_formula_eq)*)


datatype tysym = TAny nat | TNum nat | TCst ty
                                 
type_synonym tysenv = "nat \<Rightarrow> tysym"

type_synonym tyssig = "(Formula.name \<times> nat) \<rightharpoonup> tysym list"

definition agg_tysenv :: "tysenv \<Rightarrow> tysym list \<Rightarrow> tysenv " where
"agg_tysenv E tys =  (\<lambda>z. if z < length tys then tys ! z else E (z - length tys))"

definition new_type_symbol :: "tysym \<Rightarrow> tysym" where
"new_type_symbol t = (case t of TCst t \<Rightarrow> TCst t | TAny n \<Rightarrow> TAny (Suc n)| TNum n \<Rightarrow> TNum (Suc n) )"

fun tyless :: "tysym \<Rightarrow> tysym \<Rightarrow> bool" where 
"tyless (TNum a) (TNum b)  = (a \<le> b)"
| "tyless (TAny a) (TAny b)  = (a \<le> b)"
| "tyless (TNum _) (TAny _) = True"
| "tyless (TCst _) ( _) = True"
| "tyless _ _ = False"

fun type_clash :: "tysym \<Rightarrow> tysym \<Rightarrow> bool" where
"type_clash (TCst t1) (TCst t2) = (t1 \<noteq> t2)"
| "type_clash (TNum _) (TCst TString) = True"
| "type_clash  (TCst TString) (TNum _) = True"
| "type_clash  _ _ = False"

fun min_type :: "tysym \<Rightarrow> tysym \<Rightarrow> (tysym \<times> tysym) option_err" where
"min_type (TNum a) (TNum b)  = return (if a \<le> b then (TNum a, TNum b) else (TNum b, TNum a) )"
| "min_type (TAny a) (TAny b)  = return (if a \<le> b then (TAny a, TAny b) else (TAny b, TAny a) )"
| "min_type ( x) (TAny y) = return (x, TAny y)"
| "min_type (TAny y) x = return (x, TAny y)"
| "min_type (TCst TString) (TNum _) = error (STR '''')"
| "min_type  (TNum _) (TCst TString) = error (STR '''')"
| "min_type (TCst x) (TNum y) = return (TCst x, TNum y)"
| "min_type  (TNum y) (TCst x)= return (TCst x, TNum y)"
| "min_type (TCst x) (TCst y) = (if x = y then return (TCst x, TCst y) else error STR '''')"

lemma min_comm: "min_type a b =  min_type b a"
  by (induction a b rule: min_type.induct)  auto

lemma min_consistent: assumes "min_type a b = return (x,y)" shows "x = a \<and> y=b \<or> x = b \<and> y = a"
  using assms by (induction a b rule: min_type.induct) (auto split: if_splits)

lemma min_const: assumes "min_type (TCst x) y = return (a,b)" shows "a = TCst x"
  using assms by (induction "TCst x" y rule: min_type.induct) (auto split: if_splits)

definition propagate_constraints :: "tysym \<Rightarrow> tysym \<Rightarrow> tysenv \<Rightarrow> tysenv" where
"propagate_constraints t1 t2 E = (let (told,tnew) = if tyless t1 t2 then (t2,t1) else (t1,t2) in (\<lambda>v. if E v = told then tnew else E v) )"

definition update_env :: "tysym \<times> tysym \<Rightarrow> tysenv \<Rightarrow> (tysym \<Rightarrow> tysym)" where
"update_env x E \<equiv> case x of (tnew,told) \<Rightarrow>(\<lambda>v. if v = told then tnew else v) "

fun str_of_tysym where
  "str_of_tysym (TCst TInt) = STR ''int''"
| "str_of_tysym (TCst TFloat) = STR ''float''"
| "str_of_tysym (TCst TString) = STR ''string''"
| "str_of_tysym (TNum _) = STR ''numeric''"
| "str_of_tysym (TAny _) = STR ''any''"

(* takes two types as input, checks if there's no clash, returns updated env and the more specific type*)
definition clash_propagate :: "tysym \<Rightarrow> tysym \<Rightarrow> tysenv \<Rightarrow> (tysym \<Rightarrow> tysym) option_err" where
"clash_propagate t1 t2 E = ((min_type t1 t2) \<bind> (\<lambda>k. return (update_env k E)))
                            <? (STR ''clash of types '' + str_of_tysym t1 + STR '' and '' + str_of_tysym t2)"

lemma clash_prop_comm: "clash_propagate t1 t2 E = return f \<Longrightarrow> clash_propagate t1 t2 E = clash_propagate t2 t1 E"
  using min_comm by (auto simp add: clash_propagate_def)

lemma clash_prop_comm': "clash_propagate t1 t2 E = error e \<Longrightarrow> clash_propagate t2 t1 E \<in> range error"
  using min_comm by (auto simp add: clash_propagate_def split:bind_splits)

lemma trm_f_not_in_fv: assumes  "\<not>(\<exists>n \<in> set xs . E n = t)" shows "foldl (\<lambda>t' n. if E n = t then E2 n else t') t xs = t"
  using assms by (induction xs) auto

lemma trm_f_in_fv: assumes  "n \<in> set xs" "E n = t" "\<forall>n' \<in> set xs . E n' = t \<longrightarrow> E2 n' = E2 n "
  shows "foldl (\<lambda>t' n. if E n = t then E2 n else t') t xs = E2 n"
  using assms(1,3) proof (induction xs rule: rev_induct)
  case (snoc x xs)
  {assume "x = n"
    then have ?case using assms(2) by auto 
  }moreover {assume asm: "x \<noteq> n"
    have " foldl (\<lambda>t' n. if E n = t then E2 n else t') t xs = E2 n" apply (rule snoc.IH) using snoc asm by auto
    then have ?case using asm snoc.prems(2) by auto
    }
  ultimately show ?case by blast
qed auto

lemma trm_f_foldl_id: assumes "\<forall>n \<in> set w . t \<noteq> E n " shows "foldl (\<lambda>t' n. if E n = t then E' n else t') t w = t"
  using assms by (induction w)  auto 

lemma map_regex_size: assumes "\<And>x . x \<in> regex.atms r \<Longrightarrow>   size (f x) = size x" shows "regex.size_regex size r = regex.size_regex size (regex.map_regex f r) "
  using assms by (induction r arbitrary: ) auto

lemma map_regex_map_formula_size[simp]: " size (regex.map_regex (formula.map_formula f) r) = size r"
  by (induction r)  auto

lemma map_formula_size[simp]:"size (formula.map_formula f \<psi>) = size \<psi>" 
  apply (induction \<psi> arbitrary: f) 
 apply auto apply ( simp add: dual_order.eq_iff size_list_pointwise) using map_regex_size  by metis+

definition check_binop :: "((nat \<Rightarrow> tysym) \<Rightarrow> tysym \<Rightarrow> Formula.trm \<Rightarrow> (tysym \<Rightarrow> tysym) option_err) \<Rightarrow> (nat \<Rightarrow> tysym) \<Rightarrow> tysym \<Rightarrow> Formula.trm \<Rightarrow> Formula.trm \<Rightarrow> tysym \<Rightarrow> (tysym \<Rightarrow> tysym) option_err" where
"check_binop check_trm E typ t1 t2 exp_typ  \<equiv> 
  clash_propagate exp_typ typ E \<bind>
  (\<lambda>f. check_trm (f \<circ> E) (f typ) t1 \<bind>
     (\<lambda>f'. check_trm (f' \<circ> f \<circ> E) ((f' \<circ> f) typ) t2 \<bind>
        (\<lambda>f''. return (f'' \<circ> f' \<circ> f))))"

lemma helper[fundef_cong]: "(\<And>E typ t. size t \<le> size t1 + size t2 \<Longrightarrow> check_trm E typ t = check_trm' E typ t) \<Longrightarrow> check_binop check_trm E typ t1 t2 exp_typ = check_binop check_trm' E typ t1 t2 exp_typ"
  by (auto simp add: check_binop_def split: option.split) 

fun check_trm :: "tysenv \<Rightarrow> tysym \<Rightarrow> Formula.trm \<Rightarrow> (tysym \<Rightarrow> tysym) option_err" where
  "check_trm E typ (Formula.Var v) = clash_propagate (E v) typ E"
| "check_trm E typ (Formula.Const c) = clash_propagate (TCst (ty_of c)) typ E"
| "check_trm E typ (Formula.F2i t) =
    clash_propagate typ (TCst TInt) E \<bind>
      (\<lambda>f. check_trm (f \<circ> E) (TCst TFloat) t \<bind>
        (\<lambda>f'. return (\<lambda>t. if t = typ then TCst TInt else (f' \<circ> f) t)))" 
| "check_trm E typ (Formula.I2f t) = 
    clash_propagate typ (TCst TFloat) E \<bind>
      (\<lambda>f. check_trm (f \<circ> E) (TCst TInt) t \<bind>
        (\<lambda>f'. return (\<lambda>t. if t = typ then TCst TFloat else (f' \<circ> f) t)))" 
| "check_trm E typ (Formula.UMinus t) = 
    clash_propagate (TNum 0) (new_type_symbol typ) (new_type_symbol \<circ> E) \<bind>
      (\<lambda>f. check_trm (f \<circ> new_type_symbol \<circ> E) (f (new_type_symbol typ)) t \<bind>
        (\<lambda> f'. return (f' \<circ> f \<circ> new_type_symbol)))"
| "check_trm E typ (Formula.Plus t1 t2) = 
    check_binop check_trm (new_type_symbol \<circ> E) (new_type_symbol typ) t1 t2 (TNum 0) \<bind>
      (\<lambda>f. return (f \<circ> new_type_symbol))" 
| "check_trm E typ (Formula.Minus t1 t2) = 
    check_binop check_trm (new_type_symbol \<circ> E) (new_type_symbol typ) t1 t2 (TNum 0) \<bind>
      (\<lambda>f. return (f \<circ> new_type_symbol))"
| "check_trm E typ (Formula.Mult t1 t2) = 
    check_binop check_trm (new_type_symbol \<circ> E) (new_type_symbol typ) t1 t2 (TNum 0) \<bind>
      (\<lambda>f. return (f \<circ> new_type_symbol))"
| "check_trm E typ (Formula.Div t1 t2) = 
    check_binop check_trm (new_type_symbol \<circ> E) (new_type_symbol typ) t1 t2  (TNum 0) \<bind>
      (\<lambda>f. return (f \<circ> new_type_symbol))"
|"check_trm E typ (Formula.Mod t1 t2) = check_binop check_trm E typ t1 t2 (TCst TInt)"

definition used_tys where
"used_tys E \<phi> \<equiv> E ` fv \<phi> \<union> formula.set_formula \<phi>"

definition wf_f :: "(tysym \<Rightarrow> tysym) \<Rightarrow> bool" where
"wf_f f \<equiv> (\<forall>x. f (TCst x) = TCst x) \<and> (\<forall>n . case f (TNum n) of TCst x \<Rightarrow> x \<in> numeric_ty | TNum x \<Rightarrow> True | _ \<Rightarrow> False)"

lemma wf_f_comp: "wf_f f \<Longrightarrow> wf_f g \<Longrightarrow> wf_f (f \<circ> g)"
apply (auto simp add: comp_def wf_f_def split: tysym.splits) 
  by (metis tysym.exhaust)+ 

lemma[simp]: "wf_f id" 
  unfolding wf_f_def by auto

definition tysenvless where
"tysenvless E' E \<longleftrightarrow> (\<exists>f. wf_f f \<and>  E' = (f \<circ> E))"

lemma tysenvless_trans: "tysenvless E'' E' \<Longrightarrow> tysenvless E' E \<Longrightarrow> tysenvless E'' E"
  apply (auto simp add: tysenvless_def) subgoal for f g apply (rule exI[of _ "f \<circ> g"]) 
    using wf_f_comp by auto done

definition "resultless_trm E' E typ' typ \<longleftrightarrow> (\<exists>f. wf_f f \<and> E' = f \<circ> E \<and> typ' = f typ)"

definition "resultless_trm_f f' f typ  \<longleftrightarrow> (\<exists>g. wf_f (TCst \<circ> g) \<and> f' = g \<circ> f)"
    
lemma tysenvless_resultless_trm: assumes
  "tysenvless E' E" 
  "case typ of TCst t' \<Rightarrow> typ = typ' | TNum n \<Rightarrow> t \<in> numeric_ty \<and> typ' = TCst t \<or> typ' = typ |_  \<Rightarrow> True "
  "(\<forall>x. E x \<noteq> typ) \<or> typ = TCst t"
  shows "resultless_trm E' E typ' typ"
  using assms apply (auto simp add: tysenvless_def resultless_trm_def)  subgoal for g apply (rule exI[of _ "g(typ := typ')" ]) 
    by (auto simp add: wf_f_def split: tysym.splits)  subgoal for g  apply (rule exI[of _ "g(typ := typ')" ]) 
    by (auto simp add: wf_f_def) done

lemma some_min_resless: assumes "min_type typ z = return y"
  "f = update_env y E"
  shows "resultless_trm (f \<circ> E) E (fst y) typ "
proof -
  obtain tnew told where y_def: "y = (tnew,told)" by (cases y)
  define f where "f = (\<lambda>x . if x = told then tnew else x)"
  have wf: "wf_f f" using assms  apply (induction "z"  "typ" rule: min_type.induct)
    by (auto simp add: y_def f_def numeric_ty_def wf_f_def eq_commute[where ?b= "z"] split: if_splits tysym.splits)
  show ?thesis unfolding resultless_trm_def apply (rule exI[of _ f])  
    using assms wf apply (induction "z"  "typ" rule: min_type.induct)
    by (auto simp add: y_def f_def comp_def update_env_def eq_commute[where ?b= "z"] split: if_splits)
qed

lemma resless_newtype: 
  "resultless_trm (new_type_symbol \<circ> E) E  (new_type_symbol typ) typ "
  "resultless_trm E (new_type_symbol \<circ> E) typ (new_type_symbol typ)"
   unfolding resultless_trm_def  apply (rule exI[of _ "new_type_symbol "]) subgoal 
     by (auto simp add:   wf_f_def new_type_symbol_def)
   apply (rule exI[of _ "(\<lambda>x.  case x of TCst t \<Rightarrow> TCst t | TAny n \<Rightarrow> TAny (n-1)| TNum n \<Rightarrow> TNum (n-1) )"]) 
   by (auto simp add: wf_f_def new_type_symbol_def  split: tysym.splits) 


lemma resultless_trm_refl: "resultless_trm E E type type"
  apply (auto simp add: resultless_trm_def ) apply (rule exI[of _ id]) by (auto simp add: wf_f_def)

lemma resultless_trm_trans: assumes " resultless_trm E'' E' type'' type'" "resultless_trm E' E type' type"   
  shows "resultless_trm E'' E type'' type"
  using assms apply (auto simp add: resultless_trm_def) subgoal for f g 
 apply (rule exI[of _ "f \<circ> g"]) 
    using wf_f_comp by auto done

lemma resless_wty_num: assumes 
  "wf_f (TCst \<circ> f')"
  "wf_f f"
  "min_type x (new_type_symbol type) = return (newt, oldt)" 
  "case x of TNum 0 \<Rightarrow> f' type \<in> numeric_ty | TCst t \<Rightarrow> t = f' type | _ \<Rightarrow> False"
  "f = update_env (newt, oldt) (new_type_symbol \<circ> E)"
shows "resultless_trm_f f' (f \<circ> new_type_symbol) type"
proof -
  define f'' where f''_def: "f'' = (\<lambda>t. case t of TCst t \<Rightarrow> f' (TCst t) | TAny n \<Rightarrow> f' (TAny (n - 1))| TNum n \<Rightarrow> f' (TNum (n - 1)))"
  then have f''_eq: "f' t = (f'' \<circ> new_type_symbol) t" "f' type = f'' (new_type_symbol type)" for t
    unfolding new_type_symbol_def by(auto split:tysym.splits)
  have wf_f'': "wf_f (TCst \<circ> f'')" 
    using assms(1) unfolding f''_def wf_f_def by(auto)
  have f_def: "f = (\<lambda>t. if t = oldt then newt else t)" using assms(5)
    by(auto simp:update_env_def)
  define g where g_def: "g = (\<lambda>x. if x = newt then f' type else f'' x)" 
  have "f' t = (g \<circ> f \<circ> new_type_symbol) t" for t
    using assms(4) min_consistent[OF assms(3)] f_def f''_eq(1) assms(1)
    by (auto simp add: wf_f_def g_def new_type_symbol_def split: tysym.splits)
  moreover have "wf_f (TCst \<circ> g)" 
    using assms(4) f''_eq(1) min_consistent[OF assms(3)] wf_f'' 
    by(auto simp: g_def wf_f_def new_type_symbol_def split:tysym.splits nat.splits)  
  ultimately show ?thesis unfolding resultless_trm_f_def by force
qed 

lemma resless_wty_const: assumes 
  "wf_f (TCst \<circ> f')"
  "wf_f f"
  "f' type = typ''"
  "min_type (TCst typ'') type = return (newt, oldt)"
  "f = update_env (newt, oldt) E"
shows  "resultless_trm_f f' f type"
proof -
  note newt_def = min_const[OF assms(4)]
  have oldt_def: "oldt = type"  using min_consistent[OF assms(4)] newt_def by auto
  have f_def: "f = (\<lambda>v. if v = oldt then TCst typ'' else v)" 
    using assms(5)[unfolded min_const[OF assms(4)]] unfolding update_env_def by auto
  define g where g_def: "g = (\<lambda>t. if t = TCst typ'' then typ'' else f' t)"
  then have "f' t = (g \<circ> f) t" for t 
    using assms f_def oldt_def wf_f_def by force
  moreover have "wf_f (TCst \<circ> g)" 
    using assms(1) g_def wf_f_def by auto
  ultimately show ?thesis 
    unfolding resultless_trm_f_def by force
qed

lemma resless_wty_num_dir2: assumes
  "f' newt = typ''"
  "wf_f (TCst \<circ> f')"
  "min_type (TNum n) type = return (newt, oldt)" 
  shows  "typ'' \<in> numeric_ty"
  using assms 
  by (induction "TNum n" "type" rule: min_type.induct)
  (auto simp add: resultless_trm_def  numeric_ty_def new_type_symbol_def wf_f_def split: tysym.splits if_splits) 

lemma wf_f_clash_propagate:
  "clash_propagate ty1 ty2 E = return f \<Longrightarrow> wf_f f" 
  unfolding clash_propagate_def wf_f_def update_env_def
  by(induction ty1 ty2 rule:min_type.induct) (auto simp:numeric_ty_def split:bind_splits if_splits)

lemma resless_wty_const_dir2: assumes 
  "resultless_trm E1 E2 (TCst typ'') newt"
  "min_type (TCst t) type = return (newt, oldt)"
  shows "typ'' = t"
  using assms  min_const[of t type ]
  by (auto simp add: eq_commute[where ?a="Some(newt,oldt)"] resultless_trm_def wf_f_def) 


definition wty_result_trm :: " Formula.trm \<Rightarrow> tysenv \<Rightarrow> tysym \<Rightarrow> tysenv \<Rightarrow> tysym \<Rightarrow> bool" where
 "wty_result_trm  t E' typ' E typ \<longleftrightarrow> resultless_trm E' E typ' typ \<and> 
(\<forall>E'' typ'' .   resultless_trm (TCst \<circ>  E'') E (TCst typ'') typ \<longrightarrow> ( E'' \<turnstile> t :: typ'' \<longleftrightarrow> resultless_trm (TCst \<circ>  E'') E' (TCst typ'') typ' ))"

definition wty_result_fX_trm :: "tysenv \<Rightarrow> tysym \<Rightarrow> Formula.trm  \<Rightarrow> (tysym \<Rightarrow> tysym) \<Rightarrow> bool" where
  "wty_result_fX_trm E typ trm f \<longleftrightarrow> wf_f f \<and> 
(\<forall>f' .  wf_f (TCst \<circ> f') \<longrightarrow> 
  ((f'\<circ> E) \<turnstile> trm :: f' typ) = (\<exists> g. wf_f (TCst \<circ> g) \<and> f' = (g \<circ> f)))"

definition half_wty_trm ::  "tysenv \<Rightarrow> tysym \<Rightarrow> Formula.trm  \<Rightarrow> (tysym \<Rightarrow> tysym) \<Rightarrow> bool" where
"half_wty_trm E typ trm f \<longleftrightarrow> wf_f f \<and> 
(\<forall>f'.  wf_f (TCst \<circ> f') \<longrightarrow> 
  ((f'\<circ> E) \<turnstile> trm :: f' typ) \<longrightarrow> (\<exists> g. wf_f (TCst \<circ> g) \<and> f' = (g \<circ> f)))"

lemma subterm_half_wty: assumes "half_wty_trm E typ trm f" 
 "\<And>f . (f \<circ> E) \<turnstile> subtrm :: (f typ) \<Longrightarrow> (f \<circ> E) \<turnstile> trm :: (f typ)"
shows  "half_wty_trm E typ subtrm f"
  using assms unfolding half_wty_trm_def by auto

lemma check_trm_step0_half: assumes
  "clash_propagate t type E = return f" 
shows "resultless_trm (f \<circ> E) E (f type) type"
proof - 
  obtain  oldt where t_def: "min_type t type = return (f type, oldt)" using assms min_consistent[of t type]
    by (cases "min_type t (type)") (auto simp add: clash_propagate_def update_env_def) 
  then have f_def: "f =  update_env (f type, oldt) E" using assms
    by (cases "min_type (t) (type)") (auto simp add: clash_propagate_def) 
  then show g1: "resultless_trm (f \<circ> E) E (f type) type"
    using some_min_resless[OF t_def[unfolded min_comm[where ?b="type"]] f_def] by simp
qed

lemma check_trm_step0_num: assumes
  "clash_propagate (TNum 0) (new_type_symbol type) (new_type_symbol \<circ> E) = return f" 
  "\<And>f''. ((f'' \<circ> E) \<turnstile> t :: f'' type) \<Longrightarrow> f'' type \<in> numeric_ty" 
  "wf_f (TCst \<circ> f')"
shows 
  "((f' \<circ> E) \<turnstile> t :: f' type) \<Longrightarrow> resultless_trm_f f' (f \<circ> new_type_symbol) type"
  "resultless_trm_f f' (f \<circ> new_type_symbol) type \<Longrightarrow> f' type \<in> numeric_ty"
proof -
  have wf_f: "wf_f f" using assms(1) using wf_f_clash_propagate by fastforce
  obtain oldt where t_def: "min_type (TNum 0) (new_type_symbol type) = return (f (new_type_symbol type), oldt)" using assms(1) min_consistent
    by (cases "min_type (TNum 0) (new_type_symbol type)"; auto simp add: clash_propagate_def update_env_def) metis
  then have f_def: "f = update_env (f (new_type_symbol type), oldt) (new_type_symbol \<circ> E)" using assms(1) 
    by (cases "min_type (TNum 0) (new_type_symbol type)") (auto simp add:  clash_propagate_def)
  show "((f' \<circ> E) \<turnstile> t :: f' type) \<Longrightarrow> resultless_trm_f f' (f \<circ> new_type_symbol) type"
    using resless_wty_num[OF assms(3) wf_f t_def _ f_def] assms(2) by auto
  
  show "resultless_trm_f f' (f \<circ> new_type_symbol) type \<Longrightarrow> f' type \<in> numeric_ty"
  proof -
    assume "resultless_trm_f f' (f \<circ> new_type_symbol) type"
    then obtain g where g_def: "wf_f (TCst \<circ> g)" "f' = g \<circ> (f \<circ> new_type_symbol)" "f' type = (g \<circ> (f \<circ> new_type_symbol)) type" 
      unfolding resultless_trm_f_def by auto
    show "f' type \<in> numeric_ty" using g_def(3) resless_wty_num_dir2[OF _ g_def(1) t_def] by auto
  qed
qed            

lemma check_trm_step0_cst2: assumes
  "clash_propagate (TCst typ'') type E = return f" 
  "wf_f (TCst \<circ> f')"
  "f' type = typ''"
shows 
  "resultless_trm_f f' f type"
proof -
  have wf_f: "wf_f f" using assms(1) using wf_f_clash_propagate by fastforce
  obtain oldt where t_def: "min_type (TCst typ'') type = return (f type, oldt)" using assms(1) min_consistent
    by (cases "min_type (TCst typ'') ( type)"; auto simp add: clash_propagate_def update_env_def) fastforce
  then have f_def: "f =  update_env (f type, oldt) (E)" using assms(1) 
    by (cases "min_type (TCst typ'') ( type)") (auto simp add:  clash_propagate_def)
  show "resultless_trm_f f' f type"
    using resless_wty_const[OF assms(2) wf_f assms(3) t_def f_def] by auto
qed

lemma check_trm_step0_cst: assumes
    "clash_propagate (TCst ty) type E = return f" 
    "\<And>f'' y . (f'' \<circ> E \<turnstile> t :: y) \<longleftrightarrow>  y = ty"
  shows "wty_result_fX_trm E type t f"
proof -
  obtain oldt where t_def: "min_type (TCst ty) type = return (f type, oldt)" 
    using assms(1) 
    by (cases "min_type (TCst ty) type"; auto simp add: clash_propagate_def update_env_def) (metis min_consistent)
  then have f_def: "f = update_env (f type, oldt) E" using assms(1) 
    by(cases "min_type (TCst ty)  type") (auto simp add: clash_propagate_def) 
  { 
    fix f'' type''
    assume wf_f'': "wf_f (TCst \<circ> f'')" and wty: "(f'' \<circ> E) \<turnstile> t :: f'' type" 
    define g where "g = (\<lambda>t. if type = t then ty else f'' t)"
    have wf_g: "wf_f (TCst \<circ> g)" using wty[unfolded assms(2)] wf_f'' g_def by (auto simp add: wf_f_def)
    have g1: "f'' t = (g \<circ> f) t" for t
      using wty[unfolded assms(2)] f_def g_def[unfolded wty[unfolded assms(2), symmetric]]
      by (auto simp add: update_env_def) (smt (verit, ccfv_threshold) comp_apply min_consistent t_def tysym.inject(3) wf_f'' wf_f_def)
    moreover have "f'' type = (g \<circ> f) type" using g1 by auto
    ultimately have "(\<exists>g. wf_f (TCst \<circ> g) \<and> f'' = (g \<circ> f))" using wf_g by force
  }
  then show ?thesis using wf_f_clash_propagate[OF assms(1)] assms(2)
    unfolding wty_result_fX_trm_def
    by (auto simp add: wty_result_trm_def) (metis comp_def min_const t_def tysym.inject(3) wf_f_def)
qed

lemma check_trm_step1: 
  assumes 
    "wty_result_fX_trm (f \<circ> E) (f type) t f'"
    "half_wty_trm E type t f"
  shows "wty_result_fX_trm E type t (f' \<circ> f)"
proof -
  have "wf_f (f' \<circ> f)"
    using assms wf_f_comp unfolding wty_result_fX_trm_def half_wty_trm_def
    by auto
  then show "wty_result_fX_trm E type t (f' \<circ> f)" unfolding wty_result_fX_trm_def half_wty_trm_def
    apply(auto) 
  proof -
    fix fa
    assume fa_assm: "wf_f (TCst \<circ> fa)" "fa \<circ> E \<turnstile> t :: fa type"
    obtain g where g_def: "wf_f (TCst \<circ> g)" "fa = g \<circ> f"
      using assms(2) fa_assm unfolding half_wty_trm_def by auto
    then have "g \<circ> (f \<circ> E) \<turnstile> t :: g (f type)" 
      using fa_assm(2) by (smt (verit, best) comp_eq_dest_lhs image_subset_iff wty_trm_fv_cong)
    then show "\<exists>g. wf_f (TCst \<circ> g) \<and> fa = g \<circ> (f' \<circ> f)"
      using assms(1) g_def unfolding wty_result_fX_trm_def by force
  next
    fix fa g
    assume fa_assm: "wf_f (f' \<circ> f)" "wf_f (TCst \<circ> (g \<circ> (f' \<circ> f)))" "wf_f (TCst \<circ> g)"
    have "(g \<circ> f') \<circ> (f \<circ> E) \<turnstile> t :: (g \<circ> f') (f type)" 
      using assms(1) unfolding wty_result_fX_trm_def by (metis fa_assm(3) fun.map_comp wf_f_comp)
    then show "g \<circ> (f' \<circ> f) \<circ> E \<turnstile> t :: g (f' (f type))" 
      using fa_assm by (smt (verit, best) comp_def image_subset_iff wty_trm_fv_cong)
  qed
qed
     
  

lemma half_wty_trm_trans: assumes 
  "half_wty_trm E typ trm f"
  "half_wty_trm (f \<circ> E) (f typ) trm f'"
shows "half_wty_trm E typ trm (f' \<circ> f)"
proof -
  {
    fix f''
    assume wf: "wf_f (TCst \<circ> f'')" and typed: "f'' \<circ> E \<turnstile> trm :: f'' typ"
    obtain g where g_def: "wf_f (TCst \<circ> g)" "f'' = g \<circ> f"  "f'' typ = (g \<circ> f) typ" 
      using assms(1) wf typed unfolding half_wty_trm_def by blast
    have "g \<circ> (f \<circ> E) \<turnstile> trm :: g (f typ)"
      using typed g_def(2) by (smt (verit, ccfv_SIG) comp_apply g_def(3) image_subset_iff wty_trm_fv_cong)
    then have "(\<exists>g. wf_f (TCst \<circ> g) \<and> f'' = (g \<circ> (f' \<circ> f)))"
      using g_def assms(2) unfolding half_wty_trm_def by force
  }
  then show ?thesis using assms wf_f_comp unfolding half_wty_trm_def by auto
qed

lemma wf_new_type_symbol:
  "wf_f new_type_symbol" 
  by (simp add: new_type_symbol_def wf_f_def)

lemma check_binop_sound: 
  assumes 
  "\<And>E type f. check_trm E type t1 = return f \<Longrightarrow>  wty_result_fX_trm E type t1 f"
  "\<And>E type f. check_trm E type t2 = return f \<Longrightarrow> wty_result_fX_trm E type t2 f"
  "check_trm E type (trm t1 t2) = return f" 
  "trm \<in> {trm.Plus, trm.Minus, trm.Mult, trm.Div, trm.Mod}"
shows "wty_result_fX_trm E type (trm t1 t2) f"
proof -
  define constr where [simp]: "constr = (if trm = trm.Mod then TCst TInt else TNum 0)"
  define E_start where [simp]: "E_start = (if trm = trm.Mod then E else new_type_symbol \<circ> E)"
  define type_start where [simp]: "type_start = (if trm = trm.Mod then type else new_type_symbol type)"
  define P where [simp]: "P = (if trm = trm.Mod then (\<lambda>y.  y = TInt) else (\<lambda>y.  y \<in> numeric_ty))"
  define final_f where [simp]: "final_f = (if trm = trm.Mod then id else new_type_symbol)"
  have neqs: "trm.Plus = trm.Mod = False" "trm.Minus = trm.Mod = False" "trm.Mult = trm.Mod = False" "trm.Div = trm.Mod = False" by (auto simp:fun_eq_iff)
  then obtain f' where f'_def: "clash_propagate constr type_start E_start = return f'" using assms(3-4)
    by (auto simp add: check_binop_def clash_propagate_def split: option.splits if_splits) auto 
  then have constr_int: "constr = TCst TInt \<Longrightarrow> wf_f (TCst \<circ> f'') \<Longrightarrow> resultless_trm_f f'' f' type \<Longrightarrow> f'' type = TInt" for f'' 
    unfolding resultless_trm_f_def by (cases "min_type (TCst TInt) type_start"; auto simp: clash_propagate_def comp_assoc wf_f_def) (smt (verit, best) assms(4) case_prod_conv min_consistent min_const tysym.distinct(5) update_env_def)
  have wf_f': "wf_f f'" using f'_def by (simp add: wf_f_clash_propagate)
  have wf_final: "wf_f final_f" using assms(4) wf_new_type_symbol by(auto)
  obtain f'' where  f''_def: "check_trm (f' \<circ> E_start) (f' type_start) t1 = return f''" 
    using assms f'_def by(auto simp add: check_binop_def clash_propagate_def split: option.splits if_splits) fastforce+
  then obtain f''' where f'''_def: "check_trm (f'' \<circ> f' \<circ> E_start) ((f'' \<circ> f') type_start) t2 = return f'''" 
    using assms f'_def neqs by (auto simp add: check_binop_def clash_propagate_def split: option.splits) fastforce+
  have f_def: "f = f''' \<circ> (f'' \<circ> (f' \<circ> final_f))" using assms(3-4) f'_def f''_def f'''_def neqs
    by(auto simp:check_binop_def comp_assoc split:option.splits)
  note wty_res2 = assms(2)[OF f'''_def]
  note wty_res1 = assms(1)[OF f''_def]
  have correct_type: "f \<circ> E \<turnstile> trm t1 t2 :: f type \<Longrightarrow> P (f type)" for f 
    using assms(4) by (auto elim: wty_trm.cases) 
  have correct_type': "E \<turnstile> trm t1 t2 :: t  \<Longrightarrow> E \<turnstile> t1 :: t \<and> E \<turnstile> t2 :: t" for E t 
    using assms(4) by (auto elim: wty_trm.cases) 
  have "wf_f (f' \<circ> final_f)" using assms(4) wf_f'
    by (auto simp add: wf_f_comp wf_new_type_symbol)
  moreover {
    fix fa
    assume asm: "wf_f (TCst \<circ> fa)" "fa \<circ> E \<turnstile> trm t1 t2 :: fa type"
    then have "\<exists>g. wf_f (TCst \<circ> g) \<and>
               fa = g \<circ> (f' \<circ> final_f)" 
      using 
        check_trm_step0_num[OF _ _ asm(1), of type E f' "trm t1 t2"] correct_type
        check_trm_step0_cst2[OF _ asm(1)]
        correct_type[OF asm(2)] f'_def assms(4) 
      unfolding resultless_trm_f_def by auto
  } ultimately have "half_wty_trm E type (trm t1 t2) (f' \<circ> final_f)"
    unfolding half_wty_trm_def by auto
  moreover have 
    "half_wty_trm (f'' \<circ> (f' \<circ> (final_f \<circ> E))) (f'' (f' (final_f type))) (trm t1 t2) f'''"
    "half_wty_trm (f' \<circ> (final_f \<circ> E)) (f' (final_f type)) (trm t1 t2) f''"
    using wty_res1 wty_res2 correct_type' wf_f_comp assms(4)
    unfolding wty_result_fX_trm_def half_wty_trm_def by(auto simp:comp_assoc)
  ultimately have half_wty: "half_wty_trm E type (trm t1 t2) f" 
    unfolding f_def by(auto simp:comp_assoc simp del: final_f_def intro!:half_wty_trm_trans)
  {
    fix fa
    assume wf_fa: "wf_f (TCst \<circ> fa)"
      and ex_g: "(\<exists>g. wf_f (TCst \<circ> g) \<and> fa = (g \<circ> f))"
    obtain g where g_def:
      "wf_f (TCst \<circ> g)" "fa = (g \<circ> f)"  "fa type = (g \<circ> f) type" using ex_g by auto
    let ?ft1 = "g \<circ> f''' \<circ> f''"
    let ?ft2 = "g \<circ> f'''"
    have wfs: 
      "wf_f (TCst \<circ> ?ft1)"
      "wf_f (TCst \<circ> ?ft2)"
      using wf_final wf_f' wty_res1 wty_res2 wf_f_comp g_def(1) 
      unfolding wty_result_fX_trm_def by (simp add: fun.map_comp)+
    have 
      "(\<exists>g. wf_f (TCst \<circ> g) \<and> (?ft1 = (g \<circ> f'')))"
      "(\<exists>g. wf_f (TCst \<circ> g) \<and> (?ft2 = (g \<circ> f''')))"
       apply (metis comp_assoc g_def(1) wf_f_comp wty_res2 wty_result_fX_trm_def)
      using g_def(1) by blast
    moreover have
      "(?ft1 \<circ> (f' \<circ> E_start) \<turnstile> t1 :: ?ft1 (f' type_start)) = (\<exists>g. wf_f (TCst \<circ> g) \<and> (?ft1 = (g \<circ> f'')))"
      "(?ft2 \<circ> ((f'' \<circ> f') \<circ> E_start) \<turnstile> t2 :: ?ft2 ((f'' \<circ> f') type_start)) = (\<exists>g. wf_f (TCst \<circ> g) \<and> (?ft2 = (g \<circ> f''')))"
      using wty_res1 wty_res2 wfs g_def(1) unfolding wty_result_fX_trm_def by(auto simp:comp_def)
    ultimately have 
      "(g \<circ> f \<circ> E) \<turnstile> t1 :: (g \<circ> f) type" 
      "(g \<circ> f \<circ> E) \<turnstile> t2 :: (g \<circ> f) type" 
      using assms(4) unfolding f_def by(auto simp:comp_assoc) 
    then have wty_terms:
      "(fa \<circ> E) \<turnstile> t1 :: fa type" 
      "(fa \<circ> E) \<turnstile> t2 :: fa type" 
      using g_def(2) by (smt (verit, best) comp_def g_def(3) image_subset_iff wty_trm_fv_cong)+
    have resless: "resultless_trm_f fa (f' \<circ> final_f) type"
      unfolding resultless_trm_f_def using f_def g_def(2) g_def(3) wfs(1) by (auto simp del:final_f_def) force
    have "(fa \<circ> E) \<turnstile> trm t1 t2 :: fa type" 
      using wty_res1 wty_res2 assms(4) wty_terms resless correct_type f'_def neqs
      check_trm_step0_num(2)[OF _ _ wf_fa, of type E f' "trm t1 t2"] constr_int[OF _ wf_fa]
      unfolding wty_result_fX_trm_def by(auto intro!: wty_trm.intros) 
  }
  then show ?thesis using half_wty unfolding wty_result_fX_trm_def half_wty_trm_def by(auto) 
qed

lemma check_conversion_sound: 
  assumes 
    " \<And>E type f. check_trm E type t = return f \<Longrightarrow> wty_result_fX_trm E type t f"
    "check_trm E type (trm t) = return f" 
    "trm = trm.F2i \<or> trm = trm.I2f"
  shows "wty_result_fX_trm E type (trm t) f"
proof - 
  define a where [simp]: "a = (if trm = trm.F2i then TInt else TFloat)"
  define b where [simp]: "b = (if trm = trm.F2i then TFloat else TInt)"
  have neq: "trm.F2i \<noteq> trm.I2f" using trm.distinct by force
  then obtain fp fp' where 
    fp_def: "clash_propagate type (TCst a) E = return fp" and
    fp'_def: "check_trm (fp \<circ> E) (TCst b) t = return fp'" and
    f_def': "f = (\<lambda>k. if k = type then TCst a else (fp' \<circ> fp) k)" 
    using assms(2-3) apply (auto split:bind_splits) using a_def by presburger+
  then have prec_int: "fp type = TCst a" 
    using assms(3) by (cases type) (auto simp add: clash_propagate_def update_env_def split: if_splits)
  have wf_fp: "wf_f fp" using fp_def wf_f_clash_propagate by presburger
  have type'_def: "f type = TCst a" 
    using assms(2,3) by (auto split: bind_splits)
  have type_int: "case type of TCst t \<Rightarrow> t = a | _ \<Rightarrow> True" 
    using fp_def by (cases type) (auto simp add: clash_propagate_def split: if_splits)
  have fp_def': "clash_propagate (TCst a) type E = return fp" 
    using clash_prop_comm fp_def by auto
  have wty: "wty_result_fX_trm (fp \<circ> E) (TCst b) t fp'" 
    using assms(3) assms(1)[OF fp'_def] by auto
  then have wf_fp': "wf_f fp'" using wty_result_fX_trm_def assms(1) fp'_def by blast
  obtain fp'' where f_def: "f = fp'' \<circ> fp' \<circ> fp" "wf_f fp''" using f_def' prec_int wf_f_def wf_fp' by fastforce
  have wtytrm: "(\<And>E'' y. (E'' \<turnstile> trm t :: y) \<longrightarrow> (y = a))" 
    using assms(3) by (auto elim:wty_trm.cases)
  have half: "half_wty_trm E type (trm t) fp"
    using wtytrm check_trm_step0_cst2[OF fp_def'] wf_fp unfolding half_wty_trm_def resultless_trm_f_def by auto
  have fl_def: "fp' (TCst b) = TCst b" 
    using wty unfolding wty_result_fX_trm_def wf_f_def by simp
  have typ''_def: "g (TCst a) = a" if wf_g: "wf_f (TCst \<circ> g)" for g 
    using wf_g unfolding wf_f_def by auto
  have tcst_b_aux: 
    "wf_f (TCst \<circ> f') \<Longrightarrow> (f' \<circ> (fp \<circ> E) \<turnstile> t :: f' (TCst b)) = (\<exists>g. wf_f (TCst \<circ> g) \<and> (f' = g \<circ> fp'))" for f'
    using wty unfolding wty_result_fX_trm_def by auto
  have step1: "wf_f (TCst \<circ> f'') \<Longrightarrow>  (f'' \<circ> E) \<turnstile> trm t :: (f'' type) \<Longrightarrow> resultless_trm_f f'' fp type" for f''
    using wtytrm by (simp add: check_trm_step0_cst2 fp_def'[symmetric]) 
  have step2:
    "wf_f (TCst \<circ> f'') \<Longrightarrow>  (f'' \<circ> E) \<turnstile> trm t :: (f'' type) \<Longrightarrow> (f'' \<circ> E) \<turnstile> t :: b \<Longrightarrow> resultless_trm_f f'' (fp' \<circ> fp) type" for f''
  proof -
    assume wf: "wf_f (TCst \<circ> f'')" and typed: "(f'' \<circ> E) \<turnstile> trm t :: (f'' type)" and typed2: "(f'' \<circ> E) \<turnstile> t :: b"
    obtain g where g_def: "wf_f (TCst \<circ> g)" "f'' = g \<circ> fp" 
      using step1[OF wf typed] unfolding resultless_trm_f_def by auto
    then have "(g \<circ> (fp \<circ> E) \<turnstile> t :: g (TCst b))" 
      using typed2 by (smt (verit, best) assms(3) comp_apply image_subset_iff tysym.inject(3) wf_f_def wty_trm_fv_cong)
    then obtain g' where g'_def: "wf_f (TCst \<circ> g')" "g = g' \<circ> fp'"
      using wty g_def(1) unfolding wty_result_fX_trm_def by auto
    have "f'' type = (g' \<circ> (fp' \<circ> fp)) type" using g'_def(1) prec_int typed wf_f_def wf_fp' wtytrm by force
    moreover have "f'' = g' \<circ> (fp' \<circ> fp)" using g'_def(2) g_def(2) by auto
    ultimately show "resultless_trm_f f'' (fp' \<circ> fp) type" using g'_def g_def unfolding resultless_trm_f_def by auto
  qed
  { 
    fix f' 
    assume wf_f'': "wf_f (TCst \<circ> f')" and wty: "(f' \<circ> E) \<turnstile> trm t :: f' type" 
    then have wty': "(f' \<circ> E) \<turnstile> t :: b" "(f' \<circ> E) \<turnstile> trm t :: a" 
      using assms(3) wtytrm by(auto elim:wty_trm.cases) 
    obtain g where g_def: "wf_f (TCst \<circ> g)" "f' = g \<circ> (fp' \<circ> fp)" "f' type = (g \<circ> (fp' \<circ> fp)) type"
      using step2[OF wf_f'' wty wty'(1)] unfolding resultless_trm_f_def by auto
    have "(\<exists>g. wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>UNIV. f' t = (g \<circ> f) t))" 
      by (metis comp_apply f_def' g_def(1) g_def(2) typ''_def type'_def wty wtytrm)
    then have "(\<exists>g. wf_f (TCst \<circ> g) \<and> f' = (g \<circ> f))" by force 
  }
  moreover 
  {
    fix f'
    assume wf_f': "wf_f (TCst \<circ> f')"
      and ex_g: "(\<exists>g. wf_f (TCst \<circ> g) \<and> (f' = g \<circ> f))"
    obtain g where g_def: "wf_f (TCst \<circ> g)" "f' = (g \<circ> f)"  "f' type = (g \<circ> f) type" using ex_g by auto
    have wf_fa': "wf_f (TCst \<circ> (g \<circ> fp'' \<circ> fp'))" 
      using f_def(2) wf_f_comp wf_fp' g_def(1) by (simp add: fun.map_comp)
    then have type: "g (fp'' (fp' (TCst b))) = b"  
      unfolding wf_f_def by auto
    then have "\<exists>g'. wf_f (TCst \<circ> g') \<and> (g \<circ> fp'' \<circ> fp') = (g' \<circ> fp')" 
      by (metis comp_assoc f_def(2) g_def(1) wf_f_comp)
    then have "(g \<circ> fp'' \<circ> fp' \<circ> fp) \<circ> E \<turnstile> t :: b" 
      using tcst_b_aux[OF wf_fa'] type by (metis comp_eq_dest_lhs rewriteL_comp_comp)
    then have "f' \<circ> E \<turnstile> t :: b" 
      using g_def(2)[unfolded f_def] assms(3) 
      by (smt (verit, best) comp_apply image_subset_iff wty_trm_fv_cong)
    then have "(f' \<circ> E) \<turnstile> (trm t) :: f' type"
      by (metis F2i I2f a_def assms(3) b_def comp_apply ex_g typ''_def type'_def)
  }
  moreover have "wf_f f" unfolding f_def using f_def(2) wf_f_comp wf_fp wf_fp' by presburger
  ultimately show ?thesis unfolding wty_result_fX_trm_def by auto
qed

(*Theorem 4.1*)
lemma check_trm_sound: "check_trm E type t = return f \<Longrightarrow> wty_result_fX_trm E type t f" (*Theorem 4.1*)
proof (induction t arbitrary:  E type f)  
  case (Var x) 
  have f_def: "f = (if f type = type 
                     then update_env (type, E x) E 
                     else update_env (E x, type) E)" 
    using Var  min_consistent update_env_def 
    by(fastforce simp add: clash_propagate_def)
  { 
    fix f'' 
    assume wf_f'': "wf_f (TCst \<circ> f'')" and wty: "(f'' \<circ> E) \<turnstile> trm.Var x :: f'' type" 
    define g where "g = (\<lambda>t. if type = t then f'' type else f'' t)"
    have wf_g: "wf_f (TCst \<circ> g)" using wf_f'' g_def by (auto simp add: wf_f_def)
    have g1: "f'' t = (g \<circ> f) t" for t
      using wty f_def g_def by (auto simp add: update_env_def elim!: wty_trm.cases split:if_splits) 
    moreover have "f'' type = (g \<circ> f) type" using g1 by auto
    ultimately have "(\<exists>g. wf_f (TCst \<circ> g) \<and> (f'' = g \<circ> f))" using wf_g by force
  }
  moreover have
    "wf_f (TCst \<circ> f'') \<Longrightarrow> (\<exists>g. wf_f (TCst \<circ> g) \<and> (f'' = g \<circ> f)) \<Longrightarrow> (f'' \<circ> E) \<turnstile> trm.Var x :: f'' type" 
    for f'' using f_def Var(1)
    by (auto simp add: update_env_def intro!:wty_trm.intros split:if_splits)
  ultimately show ?case 
    using wf_f_clash_propagate[OF Var(1)[unfolded check_trm.simps]] 
    unfolding wty_result_fX_trm_def resultless_trm_def 
    by auto
next
  case (Const x)
  show ?case  apply (rule check_trm_step0_cst[where ty="ty_of x"]) 
    using Const wty_trm.Const wty_trm_cong_aux by auto 
next
  case (UMinus t)
  then obtain f' f'' where 
    f'_def: "clash_propagate (TNum 0) (new_type_symbol type) (new_type_symbol \<circ> E) = return f'" and
    f''_def: "check_trm (f' \<circ> new_type_symbol \<circ> E) (f' (new_type_symbol type)) t = return f''"
    by (auto split: bind_splits)
  have wtynum: "\<And> f'' . f'' \<circ> E \<turnstile> trm.UMinus t :: f'' type \<Longrightarrow> f'' type \<in> numeric_ty" by (auto elim: wty_trm.cases)
  note res = UMinus.IH[OF f''_def] 
  have f_def: "f = f'' \<circ> f' \<circ> new_type_symbol" using f'_def f''_def UMinus(2) by(auto split:option.splits)
  have wty_uminus: "wty_result_fX_trm (f' \<circ> new_type_symbol \<circ> E) ((f' \<circ> new_type_symbol) type) (trm.UMinus t) f''"
    using res unfolding wty_result_fX_trm_def apply(auto elim: wty_trm.cases) 
  proof -
    fix fa g
    assume assm: "\<forall>f'a. wf_f (TCst \<circ> f'a) \<longrightarrow> (f'a \<circ> (f' \<circ> new_type_symbol \<circ> E) \<turnstile> t :: f'a (f' (new_type_symbol type))) = (\<exists>g. wf_f (TCst \<circ> g) \<and> f'a  = g \<circ> f'')"
      "wf_f (TCst \<circ> (g \<circ> f''))" "wf_f (TCst \<circ> g)" 
    have wf: "wf_f (TCst \<circ> (g \<circ> f'' \<circ> f' \<circ> new_type_symbol))" 
      by (metis assm(3) comp_assoc f'_def res wf_f_clash_propagate wf_f_comp wf_new_type_symbol wty_result_fX_trm_def)
    moreover have "g (f'' (f' (new_type_symbol type))) \<in> numeric_ty" 
      using check_trm_step0_num(2)[OF f'_def _ wf] using assm wtynum unfolding resultless_trm_f_def apply(auto) by (meson rewriteR_comp_comp)
    ultimately show "g \<circ> f'' \<circ> (f' \<circ> new_type_symbol \<circ> E) \<turnstile> trm.UMinus t :: g (f'' (f' (new_type_symbol type)))" using assm(3) wty_trm.UMinus by (metis assm(1) assm(2) comp_apply)
  qed
  have half: "half_wty_trm E type (trm.UMinus t) (f' \<circ> new_type_symbol)"
    using check_trm_step0_num(1)[OF f'_def] wtynum res 
    unfolding wty_result_fX_trm_def half_wty_trm_def resultless_trm_f_def 
    apply(auto) using f'_def wf_f_clash_propagate wf_f_comp wf_new_type_symbol by presburger
  show ?case using check_trm_step1[OF wty_uminus half] unfolding f_def by (metis comp_assoc)
qed (auto simp: check_binop_sound check_conversion_sound)

definition map_sig where
  "map_sig f S = map_option (map f) \<circ> S"

lemma map_sig_comp [simp]:
  "map_sig f (map_sig g S) = map_sig (f \<circ> g) S"
  unfolding map_sig_def by (simp add: fun_eq_iff option.map_comp)

definition wty_result_fX :: "tyssig \<Rightarrow> tysenv \<Rightarrow> tysym Formula.formula  \<Rightarrow> (tysym \<Rightarrow> tysym) \<Rightarrow> bool" where
  "wty_result_fX S E \<phi> f \<longleftrightarrow> wf_f f \<and> 
  (\<forall>f''. wf_f (TCst \<circ> f'') \<longrightarrow>
    (map_sig f'' S, (f''\<circ> E) \<turnstile> (formula.map_formula f'' \<phi>)) = (\<exists>g. wf_f (TCst \<circ> g) \<and> (f'' = g \<circ> f)))"

lemma map_regex_fv:  assumes "\<And>x . x \<in> regex.atms x2 \<Longrightarrow>  g (formula.map_formula f x) = g' x"
  shows "Regex.fv_regex g (regex.map_regex (formula.map_formula f) x2) = Regex.fv_regex g' x2" using assms by (induction x2) auto

lemma map_regex_pred:  assumes "\<And>x . x \<in> regex.atms x2 \<Longrightarrow>  g (formula.map_formula f x) = g' x"
  shows "regex.pred_regex g (regex.map_regex (formula.map_formula f) x2) = regex.pred_regex g' x2" using assms by (induction x2) auto

lemma[simp]:  shows "Formula.fvi b (formula.map_formula f \<psi>) = Formula.fvi b \<psi>" 
proof (induction \<psi> arbitrary: b)
  case (MatchF x1 x2)
  show ?case using map_regex_fv[where ?g="Formula.fvi b" and ?f=f] MatchF by auto
  case (MatchP x1 x2)
  show ?case using map_regex_fv[where ?g="Formula.fvi b" and ?f=f] MatchP by auto
qed  auto

lemma [simp]: "wf_f new_type_symbol" unfolding wf_f_def new_type_symbol_def by auto

lemma nfv_map[simp]: "Formula.nfv (formula.map_formula f \<psi>) = Formula.nfv \<psi>" unfolding Formula.nfv_def by auto

lemma[simp]: " wf_formula (formula.map_formula f \<psi>) = wf_formula \<psi>" by (induction \<psi>) (auto simp add: list_all_def map_regex_pred)

lemma
  wf_formula_map:
  "wf_formula \<phi> \<Longrightarrow> wf_formula ((formula.map_formula f) \<phi>)" 
proof(induction \<phi>)
  case (Ands x)
  then show ?case by(auto simp:list_all_iff)
next
  case (MatchF x1 x2)
  then show ?case by auto (metis MatchF.IH map_regex_pred regex.pred_set)
next
  case (MatchP x1 x2)
  then show ?case by auto (metis MatchP.IH map_regex_pred regex.pred_set)
qed auto

lemma used_tys_map[simp]: "used_tys (f \<circ> E) (formula.map_formula f \<psi>) = f ` used_tys E \<psi>"
  by (auto simp: used_tys_def formula.set_map)

lemma eq_refinement_min_type: assumes "\<exists> f g . wf_f f \<and> wf_f g \<and> f typ = g typ'"
  shows "\<exists> t1 t2 . min_type typ typ' = return (t1,t2)"
proof -
  obtain f g where typs: "wf_f f"  "wf_f g" "f typ = g typ'" using assms  by auto
  then show ?thesis unfolding wf_f_def apply (induction "typ" typ' rule: min_type.induct) 
    by (auto  simp add: eq_commute[where ?b=  "g (TAny _)"] eq_commute[where ?b=  "g (TNum _)"] numeric_ty_def 
        split: tysym.splits nat.splits) 
qed

fun trivial_inst :: "(tysym \<Rightarrow> ty)"  where
  "trivial_inst (TCst ty) = ty" |
  "trivial_inst (TNum n) = TInt" |
  "trivial_inst (TAny n) = TInt"

lemma wf_trivial: "wf_f (TCst \<circ> trivial_inst)" 
  unfolding wf_f_def numeric_ty_def by simp

lemma constr_complete: assumes "wf_f f"
  "P ((trivial_inst \<circ> f) type)" 
  "P = (\<lambda>x. x \<in> numeric_ty) \<and> constr = TNum 0 \<and> E_start = new_type_symbol \<circ> E \<and> type_start = new_type_symbol type \<and> (P = (\<lambda>y. y \<in> numeric_ty))
 \<or> P = (\<lambda> x. x =  t) \<and> constr = TCst t \<and> E_start =  E \<and> type_start = type"
  "clash_propagate constr type_start E_start = error e"
shows False
proof -
  have wf1: "wf_f (\<lambda>x.  if x = type_start then f type else x)"
    using assms(1, 3)  unfolding wf_f_def new_type_symbol_def by(auto split:tysym.splits)
  have wf2: "wf_f (\<lambda> x. if x = constr then f type else x)"
    using assms(1-4)  unfolding wf_f_def new_type_symbol_def numeric_ty_def 
    by(auto simp: clash_propagate_def split:tysym.splits)
  have "\<exists>EE tt. min_type constr type_start = return (EE, tt)" 
    apply (rule eq_refinement_min_type)
    apply (rule exI[of _ "(\<lambda> x. if x = constr then f type else x)"])
    apply (rule exI[of _ "(\<lambda>x.  if x = type_start then f type else x)"])
    using wf1 wf2 by auto
  then show False using assms(4) by (auto simp add: clash_propagate_def split: option.splits) 
qed

lemma check_binop_complete: 
  assumes "\<And>E type f e. check_trm E type t1 = error e \<Longrightarrow>  wf_f (TCst \<circ> f) \<Longrightarrow> f \<circ> E \<turnstile> t1 :: f type \<Longrightarrow> False"
    "\<And>E type f e. check_trm E type t2 = error e \<Longrightarrow>  wf_f (TCst \<circ> f) \<Longrightarrow> f \<circ> E \<turnstile> t2 :: f type \<Longrightarrow> False"
    "check_trm E type (trm t1 t2) = error e"
    "wf_f (TCst \<circ> f)"
    "f \<circ> E \<turnstile> trm t1 t2 :: f type"                                                                                                                                                          
    "trm \<in> {trm.Plus, trm.Minus, trm.Mult, trm.Div } \<and> constr = TNum 0 \<and> E_start = new_type_symbol \<circ> E \<and> type_start = new_type_symbol type \<and> (P = (\<lambda>y.  y \<in> numeric_ty) \<and> final_f = new_type_symbol)
 \<or> trm = trm.Mod \<and> constr = TCst TInt \<and> E_start =  E \<and> type_start = type \<and> (P = (\<lambda>y.  y = TInt) \<and> final_f = id)"
shows False
proof -
  have wty_f: "f \<circ> E \<turnstile> t1 :: f type" "f \<circ> E \<turnstile> t2 :: f type"
    using assms(5-6) by (auto elim: wty_trm.cases) 
  have correct_type: "f \<circ> E \<turnstile> trm t1 t2 :: f type \<Longrightarrow> P (f type)" for f 
    using assms(6) by (auto elim: wty_trm.cases) 
  have "P (f type)" using assms(5-6) by(auto elim: wty_trm.cases)
  then have "clash_propagate constr type_start E_start = error e \<Longrightarrow> False" for e
    using constr_complete[OF assms(4), of P type constr E_start E type_start TInt] assms(6) by(auto) 
  then obtain f' where f'_def: "clash_propagate constr type_start E_start = return f'" 
    by (meson obj_sumE)
  have wf_f': "wf_f f'" using f'_def wf_f_clash_propagate by force
  then have wf_end: "wf_f (f' \<circ> final_f)" using assms(6) wf_f_comp by force
  then have half_wty: "half_wty_trm E type (trm t1 t2) (f' \<circ> final_f)"
    unfolding half_wty_trm_def apply (auto) 
  proof -
    fix fa
    assume asm: "wf_f (TCst \<circ> fa)" "fa \<circ> E \<turnstile> trm t1 t2 :: fa type"
    then show "\<exists>g. wf_f (TCst \<circ> g) \<and>
               (fa = g \<circ> (f' \<circ> final_f))" 
      using 
        check_trm_step0_num[OF _ _ asm(1), of type E f' "trm t1 t2"] correct_type
        check_trm_step0_cst2[OF _ asm(1)]
        correct_type[OF asm(2)] f'_def assms(6) 
      unfolding resultless_trm_f_def by auto 
  qed
  obtain g where g_def: "wf_f (TCst \<circ> g)" "f type = (g \<circ> (f' \<circ> final_f)) type"
    "f = (g \<circ> (f' \<circ> final_f))" 
    using half_wty assms(4-5) unfolding half_wty_trm_def by blast
  then have g_typ: "g \<circ> (f' \<circ> final_f \<circ> E) \<turnstile> t1 :: g ((f' \<circ> final_f) type)"
    using wty_f(1) by (smt (verit, ccfv_SIG) comp_def image_subset_iff wty_trm_fv_cong)
  note t1_none = assms(1)[OF _ g_def(1) g_typ]
  obtain f'' where  f''_def: "check_trm (f' \<circ> final_f \<circ> E) ((f' \<circ> final_f) type) t1 = return f''" 
    using t1_none by (meson sumE)
  have half_wty': "half_wty_trm (f' \<circ> final_f \<circ> E) ((f' \<circ> final_f) type) t1 f''"
    using check_trm_sound[OF f''_def] unfolding wty_result_fX_trm_def half_wty_trm_def 
    by(simp add: image_image)
  then have "half_wty_trm (f' \<circ> final_f \<circ> E) ((f' \<circ> final_f) type) (trm t1 t2) f''"
    apply(rule subterm_half_wty) using assms(6) by (auto elim: wty_trm.cases) 
  then have half_wty2: "half_wty_trm (f' \<circ> final_f \<circ> E) ((f' \<circ> final_f) type) (trm t1 t2) f''"
    by (simp add: image_comp)
  obtain g' where g'_def: "wf_f (TCst \<circ> g')" "f type = (g' \<circ> (f'' \<circ> (f' \<circ> final_f))) type"
    "f = g' \<circ> (f'' \<circ> (f' \<circ> final_f))"
    using half_wty_trm_trans[OF half_wty half_wty2] assms(4-5) unfolding half_wty_trm_def by auto
  then have g'_typ: "g' \<circ> (f'' \<circ> (f' \<circ> final_f) \<circ> E) \<turnstile> t2 :: g' ((f'' \<circ> (f' \<circ> final_f)) type)"
    using wty_f(2) by (smt (verit, ccfv_SIG) comp_def image_subset_iff wty_trm_fv_cong)
  note t2_none = assms(2)[OF _ g'_def(1) g'_typ]
  show False using t2_none assms(3, 6) f'_def f''_def 
    by(auto simp: check_binop_def comp_assoc image_image split:bind_splits) 
qed

lemma check_conversion_complete: assumes   
  "\<And>E type f e. check_trm E type t = error e \<Longrightarrow>  wf_f (TCst \<circ> f) \<Longrightarrow> f \<circ> E \<turnstile> t :: f type \<Longrightarrow> False"
  "check_trm E type (trm t) = error e"
  "f \<circ> E \<turnstile> trm t :: f type"
  "trm = trm.F2i \<and> a = TInt \<and> b = TFloat \<or> trm = trm.I2f \<and> a = TFloat \<and> b = TInt"
  "wf_f (TCst \<circ> f)"
 shows False
proof -
 have cp_none: "clash_propagate (TCst a) type E = error e \<Longrightarrow> False" for e
    apply (rule constr_complete[where ?t=a and ?P="(\<lambda>x. x = a)" and ?type="type" and ?E=E and ?f="TCst \<circ> f"]) 
   using  assms(1-5) by (auto simp add: comp_def elim:wty_trm.cases) 
  then have "min_type type (TCst a) = return (TCst a, type)"
    using min_const min_comm apply(cases type; auto simp:clash_propagate_def)
  using assms(4) min_type.simps(10) min_type.simps(9) apply presburger by fastforce
  then obtain f' where f'_def: "clash_propagate (TCst a) type  E = return f' " "f' type = TCst a"
    using cp_none clash_prop_comm clash_propagate_def by (smt (verit, best) catch_return old.prod.case return_bind update_env_def)
  have fa: "f type = a" using assms(3,4) by(auto elim:wty_trm.cases)
  obtain g where g_def: "wf_f (TCst \<circ> g)" "f = g \<circ> f'"
    using check_trm_step0_cst2[OF f'_def(1) assms(5) fa] unfolding resultless_trm_f_def by auto
  have "f \<circ> E  \<turnstile> t :: b" using assms(3,4) by (auto elim:wty_trm.cases)
  moreover have "g (TCst b) = b" using g_def(1) unfolding wf_f_def by auto
  ultimately have g_typ: "g \<circ> (f' \<circ> E) \<turnstile> t :: g (TCst b)" 
    using assms(3-5) g_def(2) by auto (smt (verit, best) comp_def image_subset_iff wty_trm_fv_cong)+
  show False using cp_none f'_def assms(2, 4) assms(1)[OF _ g_def(1) g_typ] clash_prop_comm
    by (auto split: bind_splits) 
qed

lemma min_restr:
  "min_type t (f type) = return a \<Longrightarrow> wf_f f \<Longrightarrow> min_type t type \<in> range return"
  by(cases "f type"; induction t "type" rule: min_type.induct) (auto simp:wf_f_def numeric_ty_def split:tysym.splits if_splits) 

lemma check_trm_complete':
 "check_trm E type t = error e \<Longrightarrow> wf_f (TCst \<circ> f) \<Longrightarrow> f \<circ> E \<turnstile> t :: f type \<Longrightarrow> False"
proof (induction t arbitrary: E type f e)
  case (Var x)
  have "f (E x) = f type" 
    using Var(3) by (metis comp_apply wty_trm.Var wty_trm_cong_aux)
  then obtain a where *: "min_type (E x) (TCst (f type)) = return a"
    using eq_refinement_min_type by (metis (mono_tags, opaque_lifting) Var.prems(2) comp_def wf_f_def)
  then have "min_type (E x) type \<in> range return" 
    using min_restr[OF _ Var(2)] by auto
  then show ?case using Var(1) by(auto simp:clash_propagate_def)
next
  case (Const x)
  have "f (TCst (ty_of x)) = f type" 
    using Const(3) by (metis Const.prems(2) comp_apply trivial_inst.simps(1) wf_f_def wty_trm.Const wty_trm_cong_aux)
  then obtain a where *: "min_type (TCst (ty_of x)) (TCst (f type)) = return a"
    using eq_refinement_min_type by (metis Const.prems(3) wf_new_type_symbol wty_trm.Const wty_trm_cong_aux)
  then have "min_type (TCst (ty_of x)) type \<in> range return" 
    using min_restr[OF _ Const(2)] by auto
  then show ?case using Const(1)by (auto simp add: clash_propagate_def)
next
  case (Plus t1 t2)
  show ?case 
    using check_binop_complete[where ?trm="trm.Plus", OF _ _ Plus(3) Plus(4-5)]
    by auto (metis Plus.IH(1) Plus.IH(2))
next
case (Minus t1 t2)
  show ?case
    using check_binop_complete[where ?trm="trm.Minus", OF _ _ Minus(3) Minus(4-5)]
    by auto (metis Minus.IH(1) Minus.IH(2))
next
  case (UMinus t)
  have "clash_propagate (TNum 0) (new_type_symbol type) (new_type_symbol \<circ> E) = error e \<Longrightarrow> False " for e
    apply (rule constr_complete[where ?t=TInt and ?P="(\<lambda>x. x \<in> numeric_ty)"]) 
    using  UMinus(2-4)  by (auto simp add: comp_def elim: wty_trm.cases) 
  then obtain f' where f'_def: "clash_propagate (TNum 0) (new_type_symbol type) (new_type_symbol \<circ> E) = return f'"
    using sum.exhaust_sel by blast
  have resless: "resultless_trm_f f (f' \<circ> new_type_symbol) type"
    using check_trm_step0_num(1)[OF f'_def _ UMinus(3-4)] by (smt (verit, best) insert_iff numeric_ty_def trm.distinct(23) trm.distinct(7) wty_trm.simps)
  have none: "check_trm (f' \<circ> new_type_symbol \<circ> E) (f' (new_type_symbol type)) t = error e" 
    using f'_def UMinus(2) by(auto split:bind_splits)
  obtain g where g_def: "wf_f (TCst \<circ> g)" "f = g \<circ> (f' \<circ> new_type_symbol)"
    "f type = (g \<circ> (f' \<circ> new_type_symbol)) type" using resless unfolding resultless_trm_f_def by auto
  have typed': "E \<turnstile> trm.UMinus t :: ty \<Longrightarrow> E  \<turnstile> t :: ty" for E t ty by (auto elim:wty_trm.cases)
  have typed: "g \<circ> (f' \<circ> new_type_symbol \<circ> E) \<turnstile> t :: g (f' (new_type_symbol type))" 
    using typed'[OF UMinus(4)] by (smt (verit, ccfv_SIG) UMinus.prems(2) comp_apply fvi_trm.simps(5) g_def(2) g_def(3) image_subset_iff wty_trm_fv_cong)
  show ?case using UMinus.IH[OF none g_def(1) typed] by auto
next
  case (Mult t1 t2)
  show ?case
    using check_binop_complete[where ?trm="trm.Mult", OF _ _ Mult(3) Mult(4-5)]
    by auto (metis Mult.IH(1) Mult.IH(2))
next                                 
case (Div t1 t2)
  show ?case
    using check_binop_complete[where ?trm="trm.Div", OF _ _ Div(3) Div(4-5)]
    by auto (metis Div.IH(1) Div.IH(2))
next
  case (Mod t1 t2)
  show ?case
    using check_binop_complete[where ?trm="trm.Mod" and ?constr="TCst TInt", OF _ _ Mod(3) Mod(4-5)]
    by auto (metis Mod.IH(1) Mod.IH(2))
next
  case (F2i t)
  show ?case
    using check_conversion_complete[where ?trm=trm.F2i, OF _ F2i(2) F2i(4)]
    using F2i.IH F2i.prems(2) by blast
next
  case (I2f t)
  show ?case
  using check_conversion_complete[where ?trm=trm.I2f, OF _ I2f(2) I2f(4)]
  using I2f.IH I2f.prems(2) by blast 
qed 

(*Theorem 4.3*)
lemma check_trm_complete: 
  "check_trm E type t = error e \<Longrightarrow> wty_result_fX_trm E type t f \<Longrightarrow> False"
proof -
  assume assm: "check_trm E type t = error e" "wty_result_fX_trm E type t f"
  have "wf_f (TCst \<circ> trivial_inst \<circ> f)"
    using assm(2) unfolding wty_result_fX_trm_def using wf_f_comp wf_trivial by presburger
  moreover have "trivial_inst \<circ> f \<circ> E \<turnstile> t :: (trivial_inst \<circ> f) type"
    using assm(2) unfolding wty_result_fX_trm_def by (metis calculation rewriteR_comp_comp wf_trivial)
  ultimately show "False" using check_trm_complete' assm by (metis (no_types, lifting) comp_assoc)
qed

definition check_comparison where
 "check_comparison E t1 t2 \<equiv> 
  check_trm (new_type_symbol \<circ> E) (TAny 0) t1 \<bind>
    (\<lambda> f. check_trm (f \<circ> new_type_symbol \<circ> E) (f (TAny 0)) t2 \<bind> 
      (\<lambda>f'. return (f' \<circ> f \<circ> new_type_symbol)))"

definition check_two_formulas :: "(tyssig \<Rightarrow> tysenv \<Rightarrow> tysym Formula.formula  \<Rightarrow> (tysym \<Rightarrow> tysym) option_err) \<Rightarrow> tyssig \<Rightarrow> tysenv \<Rightarrow> tysym Formula.formula \<Rightarrow> tysym Formula.formula \<Rightarrow> (tysym \<Rightarrow> tysym) option_err" where
"check_two_formulas check S E \<phi> \<psi>  \<equiv> 
  check S E \<phi> \<bind>
    (\<lambda> f. check (map_sig f S) (f \<circ> E) (formula.map_formula f \<psi>) \<bind>
      (\<lambda> f'. return (f' \<circ> f)))"

definition check_ands_f :: "(tyssig \<Rightarrow> tysenv \<Rightarrow> tysym Formula.formula  \<Rightarrow> (tysym \<Rightarrow> tysym) option_err) \<Rightarrow> tyssig \<Rightarrow> tysenv \<Rightarrow>  tysym Formula.formula \<Rightarrow> (tysym \<Rightarrow> tysym) option_err  \<Rightarrow> (tysym \<Rightarrow> tysym) option_err" where
"check_ands_f check S E = 
  (\<lambda>\<phi> f_op . f_op \<bind> 
    (\<lambda> f. check (map_sig f S) (f \<circ> E) (formula.map_formula f \<phi>) \<bind>
      (\<lambda> f'. return (f' \<circ> f))))"

definition check_ands where
"check_ands check S E \<phi>s = foldr (check_ands_f check S E) \<phi>s (return id)"

fun check_pred :: "string8 \<Rightarrow> tysenv \<Rightarrow> Formula.trm list \<Rightarrow> tysym list \<Rightarrow>  (tysym \<Rightarrow> tysym) option_err" where
 "check_pred p E (trm#trms) (t#ts) =
  check_trm E t trm \<bind>
    (\<lambda> f. check_pred p (f \<circ> E) trms (map f ts) \<bind>
      (\<lambda> f'. return (f' \<circ> f)))"
| "check_pred p E [] []  = return id"
| "check_pred p E _ _  = error (STR ''wrong arity for predicate '' + literal_string8 p)"

fun check_regex :: "(tyssig \<Rightarrow> tysenv \<Rightarrow> tysym Formula.formula  \<Rightarrow> (tysym \<Rightarrow> tysym) option_err) \<Rightarrow> tyssig \<Rightarrow> tysenv \<Rightarrow> tysym Formula.formula Regex.regex \<Rightarrow> (tysym \<Rightarrow> tysym) option_err"  where
 "check_regex check S E (Regex.Skip l) = return id"
| "check_regex check S E (Regex.Test \<phi>) = check S E \<phi>"
| "check_regex check S E (Regex.Plus r s) = 
  check_regex check S E r \<bind>
    (\<lambda>f. check_regex check (map_sig f S) (f \<circ> E) (regex.map_regex (formula.map_formula f) s) \<bind>
      (\<lambda>f'. return (f' \<circ> f)))"
| "check_regex check S E (Regex.Times r s) =
  check_regex check S E r \<bind>
    (\<lambda>f. check_regex check (map_sig f S) (f \<circ> E) (regex.map_regex (formula.map_formula f) s) \<bind>
      (\<lambda>f'. return (f' \<circ> f)))"
| "check_regex check S E (Regex.Star r) = check_regex check S E r"

fun agg_trm_tysym :: "Formula.agg_type \<Rightarrow> tysym" where
"agg_trm_tysym Formula.Agg_Sum = TNum 0"
| "agg_trm_tysym Formula.Agg_Cnt = TAny 0"
| "agg_trm_tysym Formula.Agg_Avg = TNum 0"
| "agg_trm_tysym Formula.Agg_Med = TNum 0"
| "agg_trm_tysym Formula.Agg_Min = TAny 0"
| "agg_trm_tysym Formula.Agg_Max = TAny 0"

fun t_res_tysym :: "Formula.agg_type \<Rightarrow> tysym \<Rightarrow> tysym" where
"t_res_tysym Formula.Agg_Sum t = t"
| "t_res_tysym Formula.Agg_Cnt _ = TCst TInt"
| "t_res_tysym Formula.Agg_Avg _ = TCst TFloat"
| "t_res_tysym agg_type.Agg_Med _ = TCst TFloat "
| "t_res_tysym Formula.Agg_Min t = t"
| "t_res_tysym Formula.Agg_Max t = t"


lemma [fundef_cong]: "(\<And> S E \<phi>'. size \<phi>' \<le> size \<phi> + size \<psi> \<Longrightarrow> check S E \<phi>' = check' S E \<phi>') \<Longrightarrow> check_two_formulas check S E \<phi> \<psi> = check_two_formulas check' S E \<phi> \<psi>"
  by (auto simp add: check_two_formulas_def split: option.split ) 

lemma foldl_check_ands_f_fundef_cong: "(\<And> S E \<phi>'.  size \<phi>' \<le> size_list size \<phi>s \<Longrightarrow> check S E \<phi>' = check' S E \<phi>') \<Longrightarrow> foldr (check_ands_f check S E) \<phi>s f = foldr (check_ands_f check' S E) \<phi>s f"
  by (induction \<phi>s arbitrary: f) (auto simp: check_ands_f_def split: option.splits)

lemma [fundef_cong]: "(\<And> S E \<phi>'.  size \<phi>' \<le> size_list size \<phi>s \<Longrightarrow> check S E \<phi>' = check' S E \<phi>') \<Longrightarrow> check_ands check S E \<phi>s = check_ands check' S E \<phi>s"
  using foldl_check_ands_f_fundef_cong[of \<phi>s check]
  by (auto simp: check_ands_def)

lemma[simp]: "regex.size_regex size (regex.map_regex (formula.map_formula x2) s) = regex.size_regex size s"
  by (induction s)  auto

lemma [fundef_cong]: "(\<And> S E \<phi>'. size \<phi>' \<le> regex.size_regex size r \<Longrightarrow> check S E \<phi>' = check' S E \<phi>') \<Longrightarrow> check_regex check S E r = check_regex check' S E r"
  by (induction check S E r  rule: check_regex.induct) (auto split: bind_splits) 

fun check :: "tyssig \<Rightarrow> tysenv \<Rightarrow> tysym Formula.formula \<Rightarrow> (tysym \<Rightarrow> tysym) option_err" where 
  "check S E (Formula.Pred r ts)  = (case S (r, length ts) of 
    None \<Rightarrow> error (STR ''unknown predicate '' + literal_string8 r + STR '' in input formula'')
  | Some tys \<Rightarrow> check_pred r E ts tys)"
| "check S E (Formula.Let p \<phi> \<psi>) =
    (let f0 = new_type_symbol ^^ Formula.nfv \<phi> in
    check (map_sig f0 S) TAny (formula.map_formula f0 \<phi>) \<bind>
      (\<lambda>f1. check (map_sig f1 ((map_sig f0 S)((p, Formula.nfv \<phi>) \<mapsto> map TAny [0..<Formula.nfv \<phi>]))) (f1 \<circ> f0 \<circ> E) (formula.map_formula (f1 \<circ> f0) \<psi>) \<bind>
        (\<lambda>f2. return (f2 \<circ> f1 \<circ> f0))))"
| "check S E (Formula.Eq t1 t2) = check_comparison E t1 t2"
| "check S E (Formula.Less t1 t2) = check_comparison E t1 t2"
| "check S E (Formula.LessEq t1 t2) = check_comparison E t1 t2"
| "check S E (Formula.Neg \<phi>) = check S E \<phi>"
| "check S E (Formula.Or \<phi> \<psi>) = check_two_formulas check S E \<phi> \<psi>"
| "check S E (Formula.And \<phi> \<psi>) = check_two_formulas check S E \<phi> \<psi>"
| "check S E (Formula.Ands \<phi>s) = check_ands check S E \<phi>s" 
| "check S E (Formula.Exists t \<phi>) = check S (case_nat t E) \<phi>" 
| "check S E (Formula.Agg y (agg_type, d) tys trm \<phi>) = 
  check_trm (new_type_symbol \<circ> (agg_tysenv E tys)) (agg_trm_tysym agg_type) trm \<bind>
    (\<lambda>f. check (map_sig (f \<circ> new_type_symbol) S) (f \<circ> new_type_symbol \<circ> (agg_tysenv E tys)) (formula.map_formula (f \<circ> new_type_symbol) \<phi>) \<bind>
      (\<lambda>f'. check_trm (f' \<circ> f \<circ> new_type_symbol \<circ> E) ((f' \<circ> f) (t_res_tysym agg_type (agg_trm_tysym agg_type))) (Formula.Var y) \<bind>
        (\<lambda>f''. check_trm (f'' \<circ> f' \<circ> f \<circ> new_type_symbol \<circ> E) ((f'' \<circ> f' \<circ> f \<circ> new_type_symbol) d) (Formula.Var y) \<bind>
          (\<lambda>f'''. return (f''' \<circ> f'' \<circ> f' \<circ> f \<circ> new_type_symbol)))))"
| "check S E (Formula.Prev I \<phi>) = check S E \<phi>"
| "check S E (Formula.Next I \<phi>) = check S E \<phi>"
| "check S E (Formula.Since \<phi> I \<psi>) = check_two_formulas check S E \<phi> \<psi>"
| "check S E (Formula.Until \<phi> I \<psi>) = check_two_formulas check S E \<phi> \<psi>"
| "check S E (Formula.MatchF I r) = check_regex check S E r"
| "check S E (Formula.MatchP I r) = check_regex check S E r"
| "check S E (Formula.LetPast p \<phi> \<psi>) = 
  (let f0 = new_type_symbol ^^ Formula.nfv \<phi> in
  check (map_sig f0 S((p, Formula.nfv \<phi>) \<mapsto> tabulate TAny 0 (Formula.nfv \<phi>))) TAny (formula.map_formula f0 \<phi>) \<bind>
    (\<lambda>f1. check (map_sig f1 ((map_sig f0 S)((p, Formula.nfv \<phi>) \<mapsto> map TAny [0..<Formula.nfv \<phi>]))) (f1 \<circ> f0 \<circ> E) (formula.map_formula (f1 \<circ> f0) \<psi>) \<bind>
      (\<lambda>f2. return (f2 \<circ> f1 \<circ> f0))))"
| "check S E (Formula.TP t) = check_trm E (TCst TInt) t"
| "check S E (Formula.TS t) = check_trm E (TCst TInt) t" 

lemma safe_formula_map:
  "safe_formula \<phi> \<Longrightarrow> safe_formula (formula.map_formula f \<phi>)"
  by (metis (full_types) formula.rel_eq formula.rel_map(1) rel_formula_safe)

lemma map_sig_subst:
  "map_sig f (S(a \<mapsto> b)) = map_sig f S(a \<mapsto> map f b)"
  by (simp add: map_sig_def)

lemma check_binary_sound: assumes 
  "\<And>\<phi>' S E f'. size \<phi>' \<le> size \<phi> + size \<psi> \<Longrightarrow> check S E \<phi>' = return f' \<Longrightarrow> wf_formula \<phi>' \<Longrightarrow> wty_result_fX S E \<phi>' f'"
  "check S E form = return f'" "wf_formula \<phi>" "wf_formula \<psi>"
  "form \<in> {formula.Or \<phi> \<psi>, formula.And \<phi> \<psi>, formula.Since \<phi> I \<psi>, formula.Until \<phi> I \<psi>}" shows "wty_result_fX S E form f'"
proof -
  obtain f f1 where 
    f_def: "check S E \<phi> = return f" and
    f1_def: "check (map_sig f S) (f \<circ> E) (formula.map_formula f \<psi>) = return f1 \<and> f' = f1 \<circ> f " and
    f'_def: "f' = f1 \<circ> f"
    using assms(2, 5) by (auto simp add: check_two_formulas_def split: bind_splits)
  have wty1: " wty_result_fX S E \<phi> f" apply (rule assms(1)[OF _ f_def])
    using assms(2-)  unfolding used_tys_def
    by (auto simp: check_two_formulas_def split: option.splits)
  have wty2:" wty_result_fX (map_sig f S) (f \<circ> E) (formula.map_formula f \<psi>) f1"
    apply (rule assms(1)) using assms(3,4) f1_def
    by (auto simp add: safe_formula_map)
  have wty_form_iff: "map_sig f'' S, f'' \<circ> E \<turnstile> formula.map_formula f'' form \<longleftrightarrow>
    map_sig f'' S, f'' \<circ> E \<turnstile> formula.map_formula f'' \<phi> \<and> map_sig f'' S, f'' \<circ> E \<turnstile> formula.map_formula f'' \<psi>" for f''
    using assms(5)
    by (auto elim: wty_formula.cases intro: wty_formula.intros)
  show ?thesis
    using wty1 wty2 assms(3) 
    apply (auto simp: f'_def wty_form_iff wty_result_fX_def formula.set_map
        formula.map_comp intro: wf_f_comp)
      apply (smt (z3) comp_apply comp_assoc)
     apply (metis  comp_assoc wf_f_comp)
    subgoal premises prems for g
    proof -
      have "wf_f (TCst \<circ> (g \<circ> f1))"
        by (metis comp_assoc prems(4) prems(7) wf_f_comp)
      then have "(map_sig (g \<circ> f1 \<circ> f) S, (g \<circ> f1 \<circ> f) \<circ> E \<turnstile> formula.map_formula (g \<circ> f1 \<circ> f) \<psi>)"
        using prems(7) spec[OF prems(3), where ?x="g \<circ> f1"]
        by (metis (no_types, lifting) fun.map_comp prems(5))
      then show ?thesis by (simp add: fun.map_comp)
    qed
    done
qed

lemma check_comparison_sound: 
  assumes 
    f_def: "check S E form = return f" and 
    wf: "wf_formula form" and
    type: "form \<in> {formula.Less t1 t2,formula.LessEq t1 t2,formula.Eq t1 t2}"
 shows "wty_result_fX S E form f"
proof -
  obtain f1 f2 where 
    f1_def: "check_trm (new_type_symbol \<circ> E) (TAny 0) t1 = return f1" and
    f2_def: "check_trm (f1 \<circ> new_type_symbol \<circ> E) (f1 (TAny 0)) t2 = return f2"
    using assms(1,3) by (auto simp add: check_comparison_def split: bind_splits)
  have wty1: "wty_result_fX_trm (new_type_symbol \<circ> E)  (TAny 0) t1 f1"  
    using check_trm_sound[OF f1_def] f1_def assms(3) by (auto simp add: used_tys_def)
  have wty2:  "wty_result_fX_trm (f1\<circ> new_type_symbol \<circ> E) (f1 (TAny 0)) t2 f2"
    using check_trm_sound[OF f2_def] assms(3) by (auto simp add: used_tys_def)
  have f'_def: "f = f2 \<circ> f1 \<circ> new_type_symbol" using assms(1,3) f1_def f2_def by (auto simp add: check_comparison_def split: option.splits)
  {
    fix fa
    assume 
      wfa: "wf_f (TCst \<circ> fa)" and
      wty: "map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa form"
    obtain t where wtys: "fa \<circ> E \<turnstile> t1 :: t" "fa \<circ> E \<turnstile> t2 :: t"
      using wty type by(auto elim:wty_formula.cases)
    define nn where nn_def: "nn = (\<lambda>t'. case t' of TAny (Suc n) \<Rightarrow> TAny n  | TAny 0 \<Rightarrow> TCst t | TNum n \<Rightarrow> TNum (n-1) | _ \<Rightarrow> t' )"
    have nn_n: "nn \<circ> new_type_symbol = id"  by (auto simp add: nn_def new_type_symbol_def split: tysym.splits nat.splits)
    have wf_nn: "wf_f nn" by (auto simp add: nn_def wf_f_def)
    have "fa \<circ> nn \<circ> new_type_symbol \<circ> E \<turnstile> t1 :: t" using nn_n wtys(1) by (metis comp_id fun.map_comp)
    moreover have *: "fa (nn (TAny 0)) = t" using wfa nn_def by(auto simp:wf_f_def)
    ultimately have "(fa \<circ> nn) \<circ> (new_type_symbol \<circ> E) \<turnstile> t1 :: (fa \<circ> nn) (TAny 0)" by (simp add: fun.map_comp)
    then obtain g where g_def: "wf_f (TCst \<circ> g)" "fa \<circ> nn = (g \<circ> f1)"
      using wty1 wf_f_comp[OF wfa wf_nn] unfolding wty_result_fX_trm_def by (metis (no_types, opaque_lifting) fun.map_comp)
    then have g_def': "wf_f (TCst \<circ> g)" "fa = g \<circ> f1 \<circ> new_type_symbol" 
      by auto (metis comp_id fun.map_comp nn_n)
    have g_f1_t: "g (f1 (TAny 0)) = t" 
      using g_def(2) wfa * by (metis comp_def)
    have "g \<circ> (f1 \<circ> new_type_symbol \<circ> E) \<turnstile> t2 :: g (f1 (TAny 0))" 
      unfolding g_f1_t using wty_trm_fv_cong[of t2 "fa \<circ> E"] wtys(2) using assms(3) g_def(2)
      by(auto simp:used_tys_def fun.map_comp g_def'(2))
    then have "\<exists>g'. wf_f (TCst \<circ> g') \<and> (g \<circ> f1 \<circ> new_type_symbol = g' \<circ> f2 \<circ> f1 \<circ> new_type_symbol)" 
      using g_def wty2 unfolding wty_result_fX_trm_def by auto 
    then have "\<exists>g. wf_f (TCst \<circ> g) \<and> (fa = g \<circ> f)" by (simp add: f'_def fun.map_comp g_def'(2))
  } moreover {
    fix fa
    assume 
      wfa: "wf_f (TCst \<circ> fa)" and
      wty: "\<exists>g. wf_f (TCst \<circ> g) \<and> fa = (g \<circ> f)"
    obtain g where g_def: "wf_f (TCst \<circ> g)" "fa = g \<circ> f" using wty by auto
    define nn where nn_def: "nn = (\<lambda>t'. case t' of TAny (Suc n) \<Rightarrow> TAny n  | TAny 0 \<Rightarrow> TCst (g (f2 (f1 (TAny 0)))) | TNum n \<Rightarrow> TNum (n-1) | _ \<Rightarrow> t' )"
    have nn_n: "nn \<circ> new_type_symbol = id"  by (auto simp add: nn_def new_type_symbol_def split: tysym.splits nat.splits)
    have wf_nn: "wf_f nn" by (auto simp add: nn_def wf_f_def)
    have eq1: "\<forall>t \<in>  range new_type_symbol. (fa \<circ> nn) t = (g \<circ> f2 \<circ> f1) t"
      using g_def(2) nn_n by(auto simp add: f'_def pointfree_idE)
    moreover have t_eq': "(fa \<circ> nn) (TAny 0) = (g \<circ> f2 \<circ> f1) (TAny 0)" 
      using nn_def wfa wf_f_def by auto
    moreover have "wf_f (TCst \<circ> (fa \<circ> nn))"
      by (metis comp_assoc wf_f_comp wf_nn wfa)
    moreover have wf2: "wf_f (TCst \<circ> (g \<circ> f2))" 
      by (metis comp_assoc g_def(1) wf_f_comp wty2 wty_result_fX_trm_def)
    ultimately have wt1:"(fa \<circ> nn \<circ> (new_type_symbol \<circ> E) \<turnstile> t1 :: fa (nn (TAny 0)))" 
      using wty1 wty unfolding f'_def wty_result_fX_trm_def 
      by (metis (no_types, opaque_lifting) comp_apply comp_id f'_def fun.map_comp g_def(2) nn_n wf_f_comp)
    have "g \<circ> f2 \<circ> (f1 \<circ> new_type_symbol \<circ> E) \<turnstile> t2 :: (g \<circ> f2) (f1 (TAny 0))" 
      using wty2 unfolding wty_result_fX_trm_def using wf2 g_def(1) by blast
    then have "(g \<circ> f2 \<circ> f1) \<circ> (new_type_symbol \<circ> E) \<turnstile> t2 :: fa (nn (TAny 0))" 
      using t_eq' by (simp add: comp_assoc)
    then have wt2: "(fa \<circ> nn \<circ> new_type_symbol \<circ> E \<turnstile> t2 :: fa (nn (TAny 0)))"
      using wty_trm_fv_cong[of t2 "fa \<circ> nn \<circ> new_type_symbol \<circ> E" "g \<circ> f2 \<circ> (f1 \<circ> new_type_symbol \<circ> E)"] eq1 type 
      by(auto simp:used_tys_def fun.map_comp image_subset_iff)
    have "(fa \<circ> E \<turnstile> t2 :: fa (nn (TAny 0)))" "(fa \<circ> E \<turnstile> t1 :: fa (nn (TAny 0)))" 
      using wt1 wt2 by (metis comp_id fun.map_comp nn_n)+
    then have "map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa form" 
      using type by(auto intro!: wty_formula.intros)
  }
  ultimately show ?thesis using wty1 wty2 unfolding wty_result_fX_def f'_def 
    by (auto simp add: wf_f_comp wty_result_fX_trm_def)
qed

lemma check_pred_sound:
  "S (r, length ts) = Some tys \<Longrightarrow> check_pred r E ts tys = return f \<Longrightarrow> wty_result_fX S E (formula.Pred r ts) f"
proof(induction arbitrary: f S rule:check_pred.induct)
  case (1 r E trm trms t ts)
  obtain f' f'' where 
    f'_def: "check_trm E t trm = return f'" and
    f''_def: "check_pred r (f' \<circ> E) trms (map f' ts) = return f''" and
    f_def: "f = f'' \<circ> f'"
    using 1(3) by(auto split:bind_splits)
  define S' where S'_def: "S' = S((r, length trms) \<mapsto> ts)"
  then have sr: "map_sig f' S' (r, length trms) = Some (map f' ts)" by (auto simp:map_sig_def)
  note wty1 = check_trm_sound[OF f'_def]
  note wty2 = 1(1)[OF f'_def, of "map_sig f' S'"] 
  {
    fix fa
    assume wf: "wf_f (TCst \<circ> fa)" and
           wty: "map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa (formula.Pred r (trm # trms))"
    have "map_sig fa S, fa \<circ> E \<turnstile>formula.Pred r (trm # trms)" using wty by auto
    have sr: "map_sig fa S' (r, length trms) = Some (map fa ts)" using S'_def by (auto simp:map_sig_def)
    have la: "list_all2 (wty_trm (fa \<circ> E)) (trm # trms) (fa t # (map fa ts))" 
      using 1(2) wty using wty_formula.intros(1) by(auto simp:map_sig_def elim:wty_formula.cases)
    then have "fa \<circ> E \<turnstile> trm :: fa t" 
      using wf unfolding wf_f_def by auto
    then obtain g where g_def: "wf_f (TCst \<circ> g)" "fa = g \<circ> f'" 
      using wty1 wf unfolding wty_result_fX_trm_def by auto
    {
      fix trm y
      assume assm: "trm \<in> set trms" "y \<in> fv_trm trm"
      have "(fa \<circ> E) y = (g \<circ> (f' \<circ> E)) y" using g_def(2) assm(2) by(auto) 
    }
    then have "trm \<in> set trms \<Longrightarrow> (fa \<circ> E) \<turnstile> trm :: t \<Longrightarrow> (g \<circ> (f' \<circ> E)) \<turnstile> trm :: t" for t trm
      using wty_trm_fv_cong by blast
    then have "list_all2 (wty_trm (g \<circ> (f' \<circ> E))) trms (map fa ts)" 
      using la by auto (metis list.rel_mono_strong)
    then have *: "(map_sig (g \<circ> f') S', (g \<circ> (f' \<circ> E)) \<turnstile> formula.map_formula g (formula.Pred r trms))"
      using wty_formula.intros(1)[of "map_sig fa S'", OF sr] g_def(2) by (auto simp:map_sig_def)
    have "\<exists>g. wf_f (TCst \<circ> g) \<and> fa = g \<circ> f" 
      using wty2 unfolding wty_result_fX_def f_def g_def using * g_def(1) by (smt (verit, ccfv_threshold) S'_def f''_def fun.map_comp fun_upd_apply map_option_o_map_upd map_sig_comp map_sig_def)
  } moreover {
    fix f'''
    assume wf: "wf_f (TCst \<circ> f''')" and
           exg: "\<exists>g. wf_f (TCst \<circ> g) \<and> f''' = g \<circ> f"
    obtain g where g_def: "wf_f (TCst \<circ> g)" "f''' = (g \<circ> f'') \<circ> f'" using exg f_def fun.map_comp by blast
    have wf_comb: "wf_f (TCst \<circ> (g \<circ> f''))" 
      using g_def(1) wty2 unfolding wty_result_fX_def by (metis f''_def fun.map_comp sr wf_f_comp)
    moreover have "f''' t = ((g \<circ> f'') \<circ> f') t" 
      using wf g_def wf_f_def wty1 wty2 wty_result_fX_def wty_result_fX_trm_def by fastforce
    ultimately have t1: "f''' \<circ> E \<turnstile> trm :: f''' t" 
      using wty1 unfolding wty_result_fX_trm_def using g_def(2) local.wf by blast
    have sr: "map_sig (g \<circ> f'' \<circ> f') S' (r, length trms) = Some (map (g \<circ> f'' \<circ> f') ts)"
      using S'_def by(auto simp:map_sig_def)
    have "map_sig (g \<circ> f'' \<circ> f') S', (g \<circ> f'') \<circ> (f' \<circ> E) \<turnstile> (formula.Pred r trms)"
      using wty2 unfolding wty_result_fX_def using wf_comb g_def(1) by (metis (no_types, lifting) S'_def f''_def formula.simps(441) fun_upd_same map_option_o_map_upd map_sig_comp map_sig_def)
    then have la: "list_all2 (wty_trm (g \<circ> f'' \<circ> f' \<circ> E)) trms (map (g \<circ> f'' \<circ> f') ts)" 
      using sr using wty_formula.intros(1)[of "map_sig (g \<circ> f'' \<circ> f') S'", OF sr] by(auto elim:wty_formula.cases simp:comp_assoc)
    {
      fix trm y
      assume assm: "trm \<in> set trms" "y \<in> fv_trm trm"
      have "(g \<circ> f'' \<circ> f' \<circ> E) y = (f''' \<circ> E) y" using g_def(2) by (simp add: assm(2) subset_iff) 
    }
    then have "trm \<in> set trms \<Longrightarrow> (g \<circ> f'' \<circ> f' \<circ> E) \<turnstile> trm :: t \<Longrightarrow> (f''' \<circ> E) \<turnstile> trm :: t" for t trm
      using wty_trm_fv_cong by blast
    then have "list_all2 (wty_trm (f''' \<circ> E)) trms (map f''' ts)" 
      using wty_trm_fv_cong la list.rel_mono_strong g_def(2) by force
    then have *: "list_all2 (wty_trm (f''' \<circ> E)) (trm#trms) (map f''' (t#ts))" 
      using t1 wf wf_f_def by auto
    have sr: "map_sig f''' S (r, length (trm # trms)) = Some (map f''' (t # ts))"
      using 1(2) by(auto simp:map_sig_def)
    have "map_sig f''' S, f''' \<circ> E \<turnstile> formula.map_formula f''' (formula.Pred r (trm # trms))"
      using wty_formula.intros(1)[OF _ *] sr by simp
  }
  moreover have "wf_f f" 
    using wty1 wty2 wf_f_comp unfolding f_def wty_result_fX_trm_def wty_result_fX_def using f''_def sr by presburger
  ultimately show ?case unfolding wty_result_fX_def by auto
next
  case (2 r E)
  then have "f = id" by auto
  moreover have "map_sig f S, f \<circ> E \<turnstile> formula.Pred r []" for f
    using wty_formula.intros(1)[of "map_sig f S" r] 2(1) by (auto simp:map_sig_def)
  ultimately show ?case unfolding wty_result_fX_def by auto
qed auto

lemma check_ands_sound:                                      
  assumes IH: "\<And>\<phi>' S E f'. size \<phi>' \<le> size_list size \<phi>s \<Longrightarrow> check S E \<phi>' = return f' \<Longrightarrow> wf_formula \<phi>' \<Longrightarrow> wty_result_fX S E \<phi>' f'"
  shows "check_ands check S E \<phi>s = return f \<Longrightarrow> wf_formula (Formula.Ands \<phi>s) \<Longrightarrow> wty_result_fX S E (Formula.Ands \<phi>s) f"
  using IH
proof(induction \<phi>s arbitrary: f)
  case Nil
  then show ?case unfolding wty_result_fX_def check_ands_def by auto (simp add: Ands)
next
  case (Cons a \<phi>s)
  obtain f' f'' where 
    f'_def: "foldr (check_ands_f check S E) \<phi>s (return id) = return f'" and
    f''_def:  "check (map_sig f' S) (f' \<circ> E) (formula.map_formula f' a) = return f''" and
    f_def: "f = f'' \<circ> f'"
    using Cons(2) unfolding check_ands_def by(auto simp:check_ands_f_def) fastforce
  then have wty1: "wty_result_fX S E (formula.Ands \<phi>s) f'" 
    using Cons(3-4) by(auto intro!:Cons(1)) (auto simp:check_ands_def used_tys_def image_Un image_subset_iff)
  have wty2: "wty_result_fX (map_sig f' S) (f' \<circ> E) (formula.map_formula f' a) f''" 
    using Cons(3,4) by(auto intro!:Cons(4)[OF _ f''_def])
  have "wf_f f" using wty1 wty2 wf_f_comp f_def unfolding wty_result_fX_def by auto
  moreover {
    fix fa
    assume wf: "wf_f (TCst \<circ> fa)" and
           wty: "(map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa (formula.Ands (a # \<phi>s)))" 
    have tys: "(map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa (formula.Ands \<phi>s))" "(map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa a)" 
      using Ands wty by(auto elim:wty_formula.cases)
    then obtain g where g_def: "wf_f (TCst \<circ> g)" "fa = g \<circ> f'"
      using wty1 wf unfolding wty_result_fX_def by auto
    then have eq: "formula.map_formula g (formula.map_formula f' a) = formula.map_formula fa a"
      using Cons(4) by(auto simp:used_tys_def) (metis (no_types, lifting) formula.map_comp)
    have "y \<in> fv (formula.map_formula fa a) \<Longrightarrow> (g \<circ> (f' \<circ> E)) y = (fa \<circ> E) y" for y
      using Cons(4) g_def(2) by(auto simp:used_tys_def)
    then have "(map_sig g (map_sig f' S), g \<circ> (f' \<circ> E) \<turnstile> formula.map_formula g (formula.map_formula f' a))"
      using eq tys(2) wty_formula_fv_cong[of "formula.map_formula fa a" "g \<circ> (f' \<circ> E)" "fa \<circ> E"] g_def(2) 
      by (simp add: rewriteR_comp_comp)
    then have "\<exists>g. wf_f (TCst \<circ> g) \<and> fa = g \<circ> f" 
      using wty2 wf f_def g_def unfolding wty_result_fX_def by force
  } moreover {
    fix fa
    assume wf: "wf_f (TCst \<circ> fa)" and
           exg: "\<exists>g. wf_f (TCst \<circ> g) \<and> fa = g \<circ> f" 
    obtain g where g_def: "wf_f (TCst \<circ> g)" "fa = g \<circ> f" using exg by auto
    have fst: "(map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa (formula.Ands \<phi>s))" 
      using wf exg wty1 unfolding wty_result_fX_def f_def by (metis (no_types, lifting) fun.map_comp wf_f_comp wty2 wty_result_fX_def)
    then have "(map_sig fa S, fa \<circ> E \<turnstile> (formula.Ands (map (formula.map_formula fa) \<phi>s)))" by simp
    then have fst: " \<forall>\<phi>\<in>set (map (formula.map_formula fa) \<phi>s). map_sig fa S, fa \<circ> E \<turnstile> \<phi>" 
      by(rule wty_formula.cases[of "map_sig fa S" "fa \<circ> E" "formula.Ands (map (formula.map_formula fa) \<phi>s)"]) auto
    have ty: "(map_sig (g \<circ> f'') (map_sig f' S), g \<circ> f'' \<circ> (f' \<circ> E) \<turnstile> formula.map_formula (g \<circ> f'') (formula.map_formula f' a))" 
      using wf exg wty2 g_def(1) unfolding wty_result_fX_def f_def by (metis (no_types, opaque_lifting) comp_assoc wf_f_comp)
    have *: "formula.map_formula (g \<circ> f'') (formula.map_formula f' a) = formula.map_formula fa a"
      using g_def(1) g_def(2)[unfolded f_def] Cons(4) by(auto simp:used_tys_def) (metis (no_types, lifting)  formula.map_comp)
    have "y \<in> fv (formula.map_formula fa a) \<Longrightarrow> (g \<circ> f'' \<circ> (f' \<circ> E)) y = (fa \<circ> E) y" for y
      using g_def(2) Cons(4) f_def by(auto simp:used_tys_def) 
    then have "(map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa a)" 
      using ty[unfolded *] by (simp add: f_def fun.map_comp g_def(2))
    then have "(map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa (formula.Ands (a # \<phi>s)))"
      using fst Ands by auto
  }
  ultimately show ?case unfolding wty_result_fX_def by auto
qed

lemma wty_regex_binop:
  assumes 
    wty1: "wty_result_fX S E (type I r1) f'" and
    wty2: "wty_result_fX (map_sig f' S) (f' \<circ> E) (type I (regex.map_regex (formula.map_formula f') r2)) f''" and
    type: "type = formula.MatchP \<or> type = formula.MatchF" and
    binop: "binop = regex.Plus \<or> binop = regex.Times"
  shows "wty_result_fX S E (type I (binop r1 r2)) (f'' \<circ> f')"
proof -
  have "wf_f (f'' \<circ> f')" using wty1 wty2 wf_f_comp unfolding wty_result_fX_def by auto
  moreover {
    fix fa
    assume 
      wf: "wf_f (TCst \<circ> fa)" and 
      wty: "(map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa (type I (binop r1 r2)))"
    then have "regex.pred_regex (wty_formula (map_sig fa S) (fa \<circ> E)) (regex.map_regex (formula.map_formula fa) (binop r1 r2))"
      using type binop by(auto elim:wty_formula.cases)
    then have wtys:
      "(map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa (type I r1))" 
      "(map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa (type I r2))" 
      using type binop by(auto intro!:wty_formula.intros) 
    then obtain g where g_def: "wf_f (TCst \<circ> g)" "fa = g \<circ> f'"
      using wty1 wf unfolding wty_result_fX_def by auto
    then have aux: "(map_sig fa S, g \<circ> (f' \<circ> E) \<turnstile> formula.map_formula fa (type I r2))"
      using type binop wtys(2) by (simp add: fun.map_comp)
    have "(formula.map_formula g \<circ> formula.map_formula f') x = formula.map_formula (g \<circ> f') x" for x
      by (simp add: formula.map_comp)
    then have comp_eq: "(formula.map_formula g \<circ> formula.map_formula f') = formula.map_formula (g \<circ> f')"
      by auto
    have map_eq: "formula.map_formula fa (type I r2) = formula.map_formula g (type I (regex.map_regex (formula.map_formula f') r2))"
      using g_def(2) type binop UN_subset_iff[of formula.set_formula _] 
      by(auto intro!: regex.map_cong0 formula.map_cong0 simp:used_tys_def regex.map_comp comp_eq)
    have "(\<exists>g. wf_f (TCst \<circ> g) \<and> fa = g \<circ> (f'' \<circ> f'))" 
      using aux[unfolded map_eq] wty2[unfolded wty_result_fX_def] g_def by force
  } moreover {
    fix fa
    assume 
      wf: "wf_f (TCst \<circ> fa)" and 
      exg: "(\<exists>g. wf_f (TCst \<circ> g) \<and> fa = g \<circ> (f'' \<circ> f'))"
    then obtain g where g_def: "wf_f (TCst \<circ> g)" "fa = g \<circ> (f'' \<circ> f')" by auto
    have "(formula.map_formula (g \<circ> f'') \<circ> formula.map_formula f') x = formula.map_formula (g \<circ> f'' \<circ> f') x" for x
      by (simp add: formula.map_comp)
    then have comp_eq: "(formula.map_formula (g \<circ> f'') \<circ> formula.map_formula f') = formula.map_formula (g \<circ> f'' \<circ> f')"
      by auto
    have ty1: "(map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa (type I r1))"
      using wty1 wf exg unfolding wty_result_fX_def by (metis (no_types, lifting) fun.map_comp wf_f_comp wty2 wty_result_fX_def)
    have ty2': "(map_sig (g \<circ> f'') (map_sig f' S), (g \<circ> f'') \<circ> (f' \<circ> E) \<turnstile> formula.map_formula (g \<circ> f'') (type I (regex.map_regex (formula.map_formula f') r2)))" 
      using wty2 wf exg unfolding wty_result_fX_def by (metis (no_types, opaque_lifting) fun.map_comp g_def(1) wf_f_comp)
    have map_eq: "formula.map_formula (g \<circ> f'') (type I (regex.map_regex (formula.map_formula f') r2)) = formula.map_formula fa (type I r2)"
      using type binop UN_subset_iff[of formula.set_formula _] g_def(2)
      by(auto intro!: regex.map_cong0 formula.map_cong0 simp:regex.map_comp comp_eq used_tys_def)
    have ty2: "(map_sig fa S, (fa \<circ> E) \<turnstile> formula.map_formula fa (type I r2))" 
      using ty2'[unfolded map_eq] type binop g_def(2) by (simp add: fun.map_comp)
    have "regex.pred_regex (wty_formula (map_sig fa S) (fa \<circ> E)) (regex.map_regex (formula.map_formula fa) (binop r1 r2))"
      using type binop ty1 ty2 by(auto intro!:wty_formula.intros elim:wty_formula.cases)
    then have "(map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa (type I (binop r1 r2)))" 
      using type binop by(auto intro!:wty_formula.intros)
  }
  ultimately show ?thesis unfolding wty_result_fX_def by auto
qed

lemma star_regex_eq:
  "type = Formula.MatchP \<or> type = Formula.MatchF \<Longrightarrow> (S, E \<turnstile> formula.map_formula f (type I r)) = (S,  E \<turnstile> formula.map_formula f (type I (regex.Star r)))" 
proof 
  assume "type = Formula.MatchP \<or> type = Formula.MatchF" "S, E \<turnstile> formula.map_formula f (type I r)"
  then show "S, E \<turnstile> formula.map_formula f (type I (regex.Star r))" 
    using MatchP MatchF by(auto elim:wty_formula.cases)
next
  assume type: "type = Formula.MatchP \<or> type = Formula.MatchF" "S, E \<turnstile> formula.map_formula f (type I (regex.Star r))" 
  then have "S, E \<turnstile> formula.map_formula f (formula.MatchP I (regex.Star r)) \<or>
              S, E \<turnstile> formula.map_formula f (formula.MatchF I (regex.Star r))"
    by auto
  then have "Regex.pred_regex (\<lambda>\<phi>. S, E \<turnstile> \<phi>) (regex.Star (regex.map_regex (formula.map_formula f) r))"
    by(auto elim:wty_formula.cases) 
  then show "S, E \<turnstile> formula.map_formula f (type I r)"
    using type MatchP MatchF by(auto elim:wty_formula.cases)
qed

lemma check_regex_sound:
  assumes type: "type = Formula.MatchP \<or> type = Formula.MatchF" and
    IH: "\<And>\<phi>' S E f'. size \<phi>' \<le> regex.size_regex size r \<Longrightarrow> check S E \<phi>' = return f' \<Longrightarrow> wf_formula \<phi>' \<Longrightarrow> wty_result_fX S E \<phi>' f'"
  shows "\<phi> = type I r \<Longrightarrow> check_regex check S E r = return f \<Longrightarrow> wf_formula \<phi> \<Longrightarrow> wty_result_fX S E \<phi> f"
  using IH
proof(induction r arbitrary: E f \<phi>)
  case (Skip x)
  then have f_def: "f = id" by auto
  have "Regex.pred_regex (\<lambda>\<phi>. S, E \<turnstile> \<phi>) (regex.Skip x)" for S E
    by auto
  then show ?case 
    using type f_def Skip(1,4) MatchP MatchF 
    unfolding wty_result_fX_def by auto
next
  case (Test x)
  then have f_def: "check S E x = return f"
    by auto
  have wf: "wf_formula x" using Test(1,3) type by auto
  have wty: "wty_result_fX S E x f" using Test(4)[OF _ f_def wf] by auto
  then have "wf_f f" unfolding wty_result_fX_def by auto
  moreover {
    fix fa
    assume wf: "wf_f (TCst \<circ> fa)" and
           ty: "map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa (type I (regex.Test x))"
    then have "map_sig fa S, fa \<circ> E \<turnstile> formula.MatchP I (regex.Test (formula.map_formula fa x)) \<or>
               map_sig fa S, fa \<circ> E \<turnstile> formula.MatchF I (regex.Test (formula.map_formula fa x))"
      using type by auto
    then have "Regex.pred_regex (\<lambda>\<phi>. map_sig fa S, fa \<circ> E \<turnstile> \<phi>) (regex.Test (formula.map_formula fa x))"
       by(auto elim:wty_formula.cases) 
    then have "map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa x"
      by auto
    then have "\<exists>g. wf_f (TCst \<circ> g) \<and> fa = (g \<circ> f)" using wty wf unfolding wty_result_fX_def by auto
  } moreover {
    fix fa
    assume wf: "wf_f (TCst \<circ> fa)" and
           exg: "\<exists>g. wf_f (TCst \<circ> g) \<and> (fa = g \<circ> f)"
    have "map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa (type I (regex.Test x))" 
      using type wf exg wty MatchP MatchF unfolding wty_result_fX_def by auto
  }
  ultimately show ?case 
    using type
    unfolding wty_result_fX_def Test(1) by auto
next
  case (Plus r1 r2)
  obtain f' f'' where f_defs:
    "check_regex check S E r1 = return f'"
    "check_regex check (map_sig f' S) (f' \<circ> E) (regex.map_regex (formula.map_formula f') r2) = return f''"
    "f = f'' \<circ> f'"
    using Plus(4) by(auto split:bind_splits)
  have wfs: "wf_formula (type I r1)" "wf_formula (type I (regex.map_regex (formula.map_formula f') r2))" 
    using Plus(3, 5) type by(auto) (metis map_regex_pred regex.pred_set wf_formula_map)+
  have wtys: 
    "wty_result_fX S E (type I r1) f'" 
    "wty_result_fX (map_sig f' S) (f' \<circ> E) (type I (regex.map_regex (formula.map_formula f') r2)) f''"
    using Plus(6)[OF _ _ wfs(1), of S] type f_defs(1) 
      Plus(6)[OF _ _ wfs(2), of "map_sig f' S"] f_defs(2)
     by(auto simp del:comp_apply)
   show ?case 
     using wty_regex_binop[OF wtys type, of regex.Plus] 
       type Plus(3) f_defs(3) Plus(5)[unfolded Plus(3)]
     by(auto simp del: comp_apply)
next
  case (Times r1 r2)
  obtain f' f'' where f_defs:
    "check_regex check S E r1 = return f'"
    "check_regex check (map_sig f' S) (f' \<circ> E) (regex.map_regex (formula.map_formula f') r2) = return f''"
    "f = f'' \<circ> f'"
    using Times(4) by(auto split:bind_splits)
  have wfs: "wf_formula (type I r1)" "wf_formula (type I (regex.map_regex (formula.map_formula f') r2))" 
    using Times(3, 5) type by(auto) (metis map_regex_pred regex.pred_set wf_formula_map)+
  have wtys: 
    "wty_result_fX S E (type I r1) f'" 
    "wty_result_fX (map_sig f' S) (f' \<circ> E) (type I (regex.map_regex (formula.map_formula f') r2)) f''"
    using Times(6)[OF _ _ wfs(1), of S] type f_defs(1) 
      Times(6)[OF _ _ wfs(2), of "map_sig f' S"] f_defs(2)
     by(auto simp del:comp_apply)
   show ?case 
     using wty_regex_binop[OF wtys type, of regex.Times] 
       type Times(3) f_defs(3) Times(5)[unfolded Times(3)]
     by(auto simp del: comp_apply)
next
  case (Star r)
  then have *: "check S E (type I r) = return f" using type by auto
  have wf: "wf_formula (type I r)" using Star type by auto
  have "wty_result_fX S E (type I r) f"
    using Star(5)[OF _ * wf] type by auto
  then show ?case using star_regex_eq[OF type] unfolding Star(2) wty_result_fX_def
    by auto
qed

lemma new_type_symbol_pow: "new_type_symbol ^^ k =
  (\<lambda>ts. case ts of TCst ty \<Rightarrow> TCst ty | TAny n \<Rightarrow> TAny (n + k) | TNum n \<Rightarrow> TNum (n + k))"
  by (induction k) (auto simp add: fun_eq_iff new_type_symbol_def split: tysym.split)

lemma fv_map:
  "fv \<phi> = fv (formula.map_formula f \<phi>)" by auto

lemma foldl_aux:
  "foldl (+) (a :: nat) rest = foldl (+) 0 rest + a" 
proof(induction rest arbitrary: a)
  case Nil
  then show ?case by auto
next
  case (Cons al rest)
  show ?case unfolding foldl_Cons Cons[of "a + al"] Cons[of "0 + al"] by auto
qed 

(*Theorem 4.6 *)
lemma check_sound_proven: "check S E \<phi> = return f \<Longrightarrow> wf_formula \<phi> \<Longrightarrow> wty_result_fX S E \<phi> f"
proof (induction S E \<phi> arbitrary: f rule: check.induct)
  case (1 S E r ts)
  then show ?case
  proof(cases "S (r, length ts)")
    case None
    then show ?thesis using 1(1) by auto
  next
    case (Some a)
    then have "check_pred r E ts a = return f" using 1(1) by auto
    then show ?thesis using check_pred_sound 1(2) Some by auto
  qed
next
  case (2 S E p \<phi> \<psi>)
  define f0 where "f0 = new_type_symbol ^^ Formula.nfv \<phi>"
  obtain f1 where f1_def: "check (map_sig f0 S) TAny (formula.map_formula f0 \<phi>) = return f1"
    unfolding f0_def using 2(3) by(auto simp add: Let_def split:option.splits)
  obtain f2 where f2_def: "check (map_sig f1 ((map_sig f0 S)((p, Formula.nfv \<phi>) \<mapsto> map TAny [0..<Formula.nfv \<phi>]))) (f1 \<circ> f0 \<circ> E) (formula.map_formula (f1 \<circ> f0) \<psi>) = return f2"
    using 2(3) f0_def f1_def by(auto simp:Let_def split:option.splits if_splits)
  have f_def: "f = f2 \<circ> f1 \<circ> f0"
    using 2(3) f0_def f1_def f2_def by(auto simp:Let_def split:option.splits if_splits)
  have wf_sub: "wf_formula \<phi>" "wf_formula \<psi>"
    using 2(4) by auto
  note wty1 = 2(1)[OF f0_def f1_def wf_formula_map[OF wf_sub(1)]]
  note wty2 = 2(2)[OF f0_def f1_def f2_def wf_formula_map[OF wf_sub(2)]]

  have "wf_f f0"
    unfolding f0_def wf_f_def new_type_symbol_pow by auto
  then have "wf_f f"
    unfolding f_def using wf_f_comp wty1 wty2 wty_result_fX_def by auto
  moreover
  {
    fix fa
    assume 
      wf: "wf_f (TCst \<circ> fa)" and
      wty: "(map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa (formula.Let p \<phi> \<psi>))"
    obtain E' where wty_sub:
      "map_sig fa S, E' \<turnstile> formula.map_formula fa \<phi>" 
      "(map_sig fa S)((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), fa \<circ> E \<turnstile> formula.map_formula fa \<psi>"
      using wty by (auto intro:wty_formula.intros elim:wty_formula.cases)
    define fa' where fa'_def: "fa' = (\<lambda>t. (case t of TAny n \<Rightarrow> if n < Formula.nfv \<phi> then E' n else fa (TAny (n - Formula.nfv \<phi>)) |
                                                     TNum n \<Rightarrow> fa (TNum (n - Formula.nfv \<phi>)) |
                                                     _ \<Rightarrow> fa t))"
    then have wf_fa': "wf_f (TCst \<circ> fa')"
      using wf unfolding wf_f_def by(auto simp:numeric_ty_def)
    have "x \<in> fv \<phi> \<Longrightarrow> (fa' \<circ> TAny) x = E' x" for x
      unfolding fa'_def by (simp add: fvi_less_nfv)
    then have fa'_TAny: "x \<in> fv (formula.map_formula (fa' \<circ> f0) \<phi>) \<Longrightarrow> (fa' \<circ> TAny) x = E' x" for x
      unfolding fv_map[of \<phi> "fa' \<circ> f0"] by auto
    have fa'_f0: "fa' \<circ> f0 = fa"
      unfolding fa'_def f0_def
      by (simp add: fun_eq_iff new_type_symbol_pow split: tysym.splits)
    have wty1': "map_sig fa' (map_sig f0 S), fa' \<circ> TAny \<turnstile> formula.map_formula fa' (formula.map_formula f0 \<phi>)"
      using wty_sub(1)[unfolded fa'_f0[symmetric]] unfolding map_sig_comp[symmetric] formula.map_comp[symmetric]
      using wty_formula_fv_cong[of "formula.map_formula (fa' \<circ> f0) \<phi>" "fa' \<circ> TAny" E', OF fa'_TAny]
      by (simp add: formula.map_comp wf_sub(1))
    then obtain g1 where wf_g1: "wf_f (TCst \<circ> g1)" and fa'_alt: "fa' = g1 \<circ> f1"
      using wty1 wf_fa' unfolding wty_result_fX_def by blast
    have list_eq: "map (fa' \<circ> TAny) [0..<Formula.nfv \<phi>] = map E' [0..<Formula.nfv \<phi>]"
      unfolding fa'_def by simp
    have "map_sig g1 (map_sig f1 (map_sig f0 S((p, Formula.nfv \<phi>) \<mapsto> map TAny [0..<Formula.nfv \<phi>]))),
          g1 \<circ> (f1 \<circ> f0 \<circ> E) \<turnstile> formula.map_formula g1 (formula.map_formula (f1 \<circ> f0) \<psi>)"
      using wty_sub(2)
      by (simp add: tabulate_alt formula.map_comp fa'_f0 map_sig_subst list_eq
          flip: comp_assoc fa'_alt)
    then obtain g2 where wf_g2: "wf_f (TCst \<circ> g2)" and g1_alt: "g1 = g2 \<circ> f2"
      using wty2 wf_g1 unfolding wty_result_fX_def by blast
    then have "fa = g2 \<circ> (f2 \<circ> f1 \<circ> f0)"
      by (simp flip: comp_assoc g1_alt fa'_alt add: fa'_f0)
    then have "\<exists>g. wf_f (TCst \<circ> g) \<and> fa = g \<circ> f"
      unfolding f_def using wf_g2 by blast
  }
  moreover
  {
    fix fa
    assume 
      wf: "wf_f (TCst \<circ> fa)" and
      "\<exists>g. wf_f (TCst \<circ> g) \<and> fa = g \<circ> f"
    then obtain g where wf_g: "wf_f (TCst \<circ> g)" and fa_alt: "fa = g \<circ> (f2 \<circ> f1 \<circ> f0)"
      unfolding f_def by blast
    have wf_g_f2: "wf_f (TCst \<circ> (g \<circ> f2))"
      by (metis comp_assoc wf_f_comp wf_g wty2 wty_result_fX_def)
    have "wf_f (TCst \<circ> (g \<circ> f2 \<circ> f1))"
      by (metis comp_assoc wf_f_comp wf_g wty1 wty2 wty_result_fX_def)
    then have "map_sig (g \<circ> f2 \<circ> f1) (map_sig f0 S), (g \<circ> f2 \<circ> f1) \<circ> TAny
        \<turnstile> formula.map_formula (g \<circ> f2 \<circ> f1) (formula.map_formula f0 \<phi>)"
      using wty1 wf_g_f2 unfolding wty_result_fX_def by blast
    then have 1: "map_sig fa S, (g \<circ> f2 \<circ> f1) \<circ> TAny \<turnstile> formula.map_formula fa \<phi>"
      by (simp add: fa_alt comp_assoc formula.map_comp)
    have "map_sig (g \<circ> f2) (map_sig f1 (map_sig f0 S((p, Formula.nfv \<phi>) \<mapsto> map TAny [0..<Formula.nfv \<phi>]))),
        (g \<circ> f2) \<circ> (f1 \<circ> f0 \<circ> E)
        \<turnstile> formula.map_formula (g \<circ> f2) (formula.map_formula (f1 \<circ> f0) \<psi>)"
      using wty2 wf_g wf_g_f2 unfolding wty_result_fX_def by blast
    then have 2: "(map_sig fa S)((p, Formula.nfv \<phi>) \<mapsto> tabulate ((g \<circ> f2 \<circ> f1) \<circ> TAny) 0 (Formula.nfv \<phi>)), fa \<circ> E
        \<turnstile> formula.map_formula fa \<psi>"
      by (simp add: fa_alt map_sig_subst comp_assoc tabulate_alt formula.map_comp)
    have "map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa (formula.Let p \<phi> \<psi>)"
      using 1 2 by (auto intro!: wty_formula.Let)
  }
  ultimately show ?case
    unfolding wty_result_fX_def by blast
next
  case (3 S E t1 t2) 
  then show ?case using check_comparison_sound by auto
next
  case (4 S E t1 t2)
  then show ?case using check_comparison_sound by auto
next 
  case (5 S E t1 t2)
  then show ?case using check_comparison_sound by auto
next
  case (6 S E \<phi>)
  then have "wty_result_fX S E \<phi> f" unfolding used_tys_def by auto 
  then show ?case  unfolding wty_result_fX_def by (auto intro: wty_formula.intros elim: wty_formula.cases) 
next
  case (7 S E \<phi> \<psi>)
  have safe: "wf_formula \<phi>" "wf_formula \<psi>"
    using 7(3) by auto
  show ?case using check_binary_sound[OF _ 7(2) safe] 7(1) by auto
next 
  case (8 S E \<phi> \<psi>)
  have safe: "wf_formula \<phi>" "wf_formula \<psi>"
    using 8(3) by auto
  show ?case using check_binary_sound[OF _ 8(2) safe] 8(1) by auto
next
  case (9 S E \<phi>s)
  then show ?case using check_ands_sound by simp
next
  case (10 S E t \<phi>) 
  have case_nat_comp: "f'' \<circ> case_nat t E = case_nat (f'' t) (f'' \<circ> E)"   for f'' :: "tysym \<Rightarrow> ty"  by (auto split: nat.splits) 
  show ?case using 10 unfolding wty_result_fX_def apply auto subgoal for f''  apply (drule spec[of _ "f''"]) 
      by (auto simp add: case_nat_comp elim:  wty_formula.cases)
    by (metis Exists case_nat_comp comp_apply)
next
  case (11 S E y agg_type d tys trm \<phi>)
  obtain f' f'' f''' f'''' where 
    f'_def: "check_trm (new_type_symbol \<circ> (agg_tysenv E tys)) (agg_trm_tysym agg_type) trm = return f'" and
    f''_def: "check (map_sig (f' \<circ> new_type_symbol) S) (f' \<circ> new_type_symbol \<circ> (agg_tysenv E tys)) (formula.map_formula (f' \<circ> new_type_symbol) \<phi>) = return f''" and
    f'''_def: "check_trm (f'' \<circ> f' \<circ> new_type_symbol \<circ> E) ((f'' \<circ> f') (t_res_tysym agg_type (agg_trm_tysym agg_type))) (Formula.Var y) = return f'''" and
    f''''_def: "check_trm (f''' \<circ> f'' \<circ> f' \<circ> new_type_symbol \<circ> E) ((f''' \<circ> f'' \<circ> f' \<circ> new_type_symbol) d) (Formula.Var y) = return f''''" and
    f_def: "f = f'''' \<circ> f''' \<circ> f'' \<circ> f' \<circ> new_type_symbol"
    using 11(2) by(auto split:bind_splits) 
  note wty1 = check_trm_sound[OF f'_def]
  have wf: "wf_formula (formula.map_formula (f' \<circ> new_type_symbol) \<phi>)" using 11(3) by auto
  note wty2 = 11(1)[OF f'_def f''_def wf]
  note wty3 = check_trm_sound[OF f'''_def]
  note wty4 = check_trm_sound[OF f''''_def]
  have wfs: "wf_f f'" "wf_f f''" "wf_f f'''" "wf_f f''''" using wty1 wty2 wty3 wty4 unfolding wty_result_fX_def wty_result_fX_trm_def by auto
  {
    fix fa
    assume wf: "wf_f (TCst \<circ> fa)"
    and wty: "(map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa (formula.Agg y (agg_type, d) tys trm \<phi>))"
    obtain t where wtys: 
      "(fa \<circ> E) y = t_res agg_type t" 
      "agg_env (fa \<circ> E) (map fa tys)  \<turnstile> trm :: t" 
      "map_sig fa S, agg_env (fa \<circ> E) (map fa tys) \<turnstile> formula.map_formula fa \<phi>"
      "t \<in> agg_trm_type agg_type" 
      "fa d = t_res agg_type t" using wty by(auto elim:wty_formula.cases)
    define nn where nn_def: "nn = (\<lambda>t'. if t' = (agg_trm_tysym agg_type) then (TCst t) else case t' of TAny n \<Rightarrow> TAny (n - 1) | TNum n \<Rightarrow> TNum (n-1) | _ \<Rightarrow> t' )"
    have nn_n: "nn \<circ> new_type_symbol = id"  by(cases agg_type; auto simp add: nn_def new_type_symbol_def split: tysym.splits nat.splits if_splits)
    have wf_nn: "wf_f nn" using wtys(4) by(cases agg_type; auto simp add: nn_def wf_f_def)
    have env_eq: "agg_env (fa \<circ> E) (map fa tys) = fa \<circ> agg_tysenv E tys" by(auto simp:agg_env_def agg_tysenv_def)
    have "(fa \<circ> nn \<circ> new_type_symbol \<circ> agg_tysenv E tys \<turnstile> trm :: (fa \<circ> nn) (agg_trm_tysym agg_type))"
      using wtys(2) wf unfolding comp_assoc env_eq nn_n by(auto simp:nn_def wf_f_def)
    then obtain g where g_def: 
      "wf_f (TCst \<circ> g)"
      "fa \<circ> nn = g \<circ> f'"
      "(fa \<circ> nn) (agg_trm_tysym agg_type) = (g \<circ> f') (agg_trm_tysym agg_type)" 
      using wf_f_comp[OF wf wf_nn] wty1 unfolding wty_result_fX_trm_def 
      by(auto simp del:comp_apply) (metis (no_types, opaque_lifting) fun.map_comp)
    have eq1: "fa = g \<circ> f' \<circ> new_type_symbol"
      using g_def(2) nn_n by (metis comp_id fun.map_comp)
    have map_eq: "formula.map_formula fa \<phi> = formula.map_formula (g \<circ> (f' \<circ> new_type_symbol)) \<phi>"
      using eq1 11(3) by(auto simp:used_tys_def comp_assoc)
    have "(map_sig (g \<circ> f' \<circ> new_type_symbol) S), (g \<circ> f' \<circ> new_type_symbol \<circ> agg_tysenv E tys) \<turnstile> formula.map_formula fa \<phi>"
      using wtys(3)[unfolded env_eq] eq1 wty_formula_fv_cong by blast
    then obtain g' where g'_def: 
      "wf_f (TCst \<circ> g')" 
      "g = g' \<circ> f''"
      using g_def(1) wty2 unfolding map_eq wty_result_fX_def formula.map_comp[symmetric, of g]
      by (metis (no_types, lifting) fun.map_comp map_sig_comp)
    have "(fa \<circ> E) y = (fa \<circ> nn) (t_res_tysym agg_type (agg_trm_tysym agg_type))" 
      using wtys(1) wf wf_nn by(cases agg_type; auto simp:nn_def wf_f_def)
    then have "(g' \<circ> (f'' \<circ> f' \<circ> new_type_symbol \<circ> E)) y = g' ((f'' \<circ> f') (t_res_tysym agg_type (agg_trm_tysym agg_type)))"
      using g_def(2) g'_def(2) eq1 by fastforce
    then have "(g' \<circ> (f'' \<circ> f' \<circ> new_type_symbol \<circ> E)) \<turnstile> trm.Var y :: g' ((f'' \<circ> f') (t_res_tysym agg_type (agg_trm_tysym agg_type)))" 
      using Var by blast
    then obtain g'' where g''_def:
      "wf_f (TCst \<circ> g'')" 
      "g' = g'' \<circ> f'''"
      using wty3 unfolding wty_result_fX_trm_def using g'_def(1) by blast
    have "(fa \<circ> E) y = fa d" using wtys(1, 5) by auto
    then have "(g'' \<circ> (f''' \<circ> f'' \<circ> f' \<circ> new_type_symbol \<circ> E)) y = g'' ((f''' \<circ> f'' \<circ> f' \<circ> new_type_symbol) d)"
      by (simp add: eq1 g''_def(2) g'_def(2))
    then obtain g''' where g'''_def:
      "wf_f (TCst \<circ> g''')" 
      "g'' = g''' \<circ> f''''"
      using wty4 unfolding wty_result_fX_trm_def by (metis Var g''_def(1))
    have "\<exists>g. wf_f (TCst \<circ> g) \<and> fa = g \<circ> f"
      using g_def(1) eq1 g'_def g''_def g'''_def unfolding f_def by force
  } moreover {
    fix fa
    assume wf: "wf_f (TCst \<circ> fa)"
    and exg: "\<exists>g. wf_f (TCst \<circ> g) \<and> fa = g \<circ> f"
    obtain g where g_def: "wf_f (TCst \<circ> g)" "fa = g \<circ> f" using exg by auto
    define nn where nn_def: "nn = (\<lambda>t'. if t' = (agg_trm_tysym agg_type) then TCst (g (f'''' (f''' (f'' (f' t'))))) else case t' of TAny 0 \<Rightarrow> TCst (g (f'''' (f''' (f'' (f' t'))))) | TNum 0 \<Rightarrow> TCst (g (f'''' (f''' (f'' (f' t'))))) | TAny n \<Rightarrow> TAny (n - 1) | TNum n \<Rightarrow> TNum (n-1) | _ \<Rightarrow> t' )"
    have env_eq: "fa \<circ> agg_tysenv E tys = agg_env (fa \<circ> E) (map fa tys)" by(auto simp:agg_env_def agg_tysenv_def)
    have nn_n: "nn \<circ> new_type_symbol = id" by(cases agg_type; auto simp add: nn_def new_type_symbol_def split: tysym.splits nat.splits if_splits)
    have wf_nn: "wf_f nn" using wf_f_comp[OF g_def(1) wf_f_comp[OF wfs(4) wf_f_comp[OF wfs(3) wf_f_comp[OF wfs(2) wfs(1)]]]] by(cases agg_type; auto simp add: nn_def wf_f_def split:nat.splits) 
    have p1: "\<forall>t \<in> range new_type_symbol. (fa \<circ> nn) t = (g \<circ> f'''' \<circ> f''' \<circ> f'' \<circ> f') t" 
      using g_def(2)[unfolded f_def] by (simp add: nn_n pointfree_idE)
    have "t \<notin> {TAny 0, TNum 0} \<Longrightarrow> t \<in> range new_type_symbol" for t 
      apply(cases t; auto simp: new_type_symbol_def split:tysym.splits) 
      by (metis Suc_pred rangeI tysym.simps(10)) (metis Nat.Suc_pred' rangeI tysym.simps(11))
    then have aux: "t \<notin> range new_type_symbol \<Longrightarrow> t = TAny 0 \<or> t = TNum 0" for t 
      by auto
    have "t \<notin> range new_type_symbol \<Longrightarrow> (fa \<circ> nn) t = (g \<circ> f'''' \<circ> f''' \<circ> f'' \<circ> f') t" for t
    proof -
      assume notin: "t \<notin> range new_type_symbol"
      show "(fa \<circ> nn) t = (g \<circ> f'''' \<circ> f''' \<circ> f'' \<circ> f') t" 
        using aux[OF notin] wf g_def(2) f_def by(auto simp:nn_def wf_f_def)
    qed
    then have fa_eq: "fa \<circ> nn = g \<circ> f'''' \<circ> f''' \<circ> f'' \<circ> f'" using p1 by blast
    then have "(fa \<circ> nn \<circ> (new_type_symbol \<circ> agg_tysenv E tys) \<turnstile> trm :: (fa \<circ> nn) (agg_trm_tysym agg_type))"
      using wty1 unfolding wty_result_fX_trm_def by (metis (full_types) fun.map_comp g_def(1) wf_f_comp wfs(2) wfs(3) wfs(4))
    then have prem1: "(fa \<circ> agg_tysenv E tys) \<turnstile> trm :: (fa \<circ> nn) (agg_trm_tysym agg_type)"
      using nn_n by (metis comp_id fun.map_comp)
    have prem2: "(fa \<circ> nn) (agg_trm_tysym agg_type) \<in> agg_trm_type agg_type" 
      by (smt (z3) UNIV_I agg_trm_type.elims agg_trm_tysym.simps(1) agg_trm_tysym.simps(3) agg_trm_tysym.simps(4) comp_assoc eq_refinement_min_type local.wf min_consistent resless_wty_num_dir2 wf_f_comp wf_nn)
    have "(map_sig (g \<circ> f'''' \<circ> f''' \<circ> f'') (map_sig (f' \<circ> new_type_symbol) S), (g \<circ> f'''' \<circ> f''' \<circ> f'') \<circ> (f' \<circ> new_type_symbol \<circ> agg_tysenv E tys) \<turnstile> formula.map_formula (g \<circ> f'''' \<circ> f''' \<circ> f'') (formula.map_formula (f' \<circ> new_type_symbol) \<phi>))"
      using wty2 unfolding wty_result_fX_def by (metis (no_types, opaque_lifting) fun.map_comp g_def(1) wf_f_comp wfs(3) wfs(4))
    then have prem3: "map_sig fa S, agg_env (fa \<circ> E) (map fa tys) \<turnstile> formula.map_formula fa \<phi>"
      unfolding formula.map_comp comp_assoc g_def(2)[unfolded f_def comp_assoc, symmetric]
      using fa_eq[symmetric] by (metis (mono_tags, lifting) env_eq f_def fun.map_comp g_def(2) map_sig_comp)
    have "((g \<circ> f'''' \<circ> f''') \<circ> (f'' \<circ> f' \<circ> new_type_symbol \<circ> E)  \<turnstile> trm.Var y :: (g \<circ> f'''' \<circ> f''') ((f'' \<circ> f') (t_res_tysym agg_type (agg_trm_tysym agg_type))))"
      using wty3 unfolding wty_result_fX_trm_def by (metis (no_types, opaque_lifting) fun.map_comp g_def(1) wf_f_comp wfs(4))
    then have "(fa \<circ> E)  \<turnstile> trm.Var y :: (fa \<circ> nn) (t_res_tysym agg_type (agg_trm_tysym agg_type))" 
      by (metis (no_types, opaque_lifting) comp_def f_def fa_eq fun.map_comp g_def(2))
    then have "(fa \<circ> E) y = (fa \<circ> nn) (t_res_tysym agg_type (agg_trm_tysym agg_type))" by(auto elim:wty_trm.cases)
    then have prem4: "(fa \<circ> E) y = t_res agg_type ((fa \<circ> nn) (agg_trm_tysym agg_type))"
      using wf_nn wf by(cases agg_type; auto simp:wf_f_def)
    have "((g \<circ> f'''') \<circ> (f''' \<circ> f'' \<circ> f' \<circ> new_type_symbol \<circ> E) \<turnstile> trm.Var y :: ((g \<circ> f'''') ((f''' \<circ> f'' \<circ> f' \<circ> new_type_symbol) d)))" 
      using wty4 unfolding wty_result_fX_trm_def by (metis (no_types, opaque_lifting) comp_apply fun.map_comp g_def(1) wf_f_comp)
    then have "(fa \<circ> E) \<turnstile> trm.Var y :: fa d" by (simp add: f_def fun.map_comp g_def(2))
    then have prem5: "fa d = t_res agg_type ((fa \<circ> nn) (agg_trm_tysym agg_type))"
      using prem4 by(auto elim:wty_trm.cases)
    have "(map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa (formula.Agg y (agg_type, d) tys trm \<phi>))"
      using Agg[OF prem4 prem1[unfolded env_eq] prem3 prem2 prem5] by auto
  }                                        
  moreover have "wf_f f" unfolding f_def using wfs wf_f_comp by force
  ultimately show ?case unfolding wty_result_fX_def by auto
next
  case (12 S E I \<phi>)
  then have "wty_result_fX S E \<phi> f" unfolding used_tys_def by simp 
  then show ?case unfolding wty_result_fX_def by (auto intro: wty_formula.intros elim: wty_formula.cases) 
next
  case (13 S E I \<phi>)
  then have "wty_result_fX S E \<phi> f" unfolding used_tys_def by simp
  then show ?case unfolding wty_result_fX_def by (auto intro: wty_formula.intros elim: wty_formula.cases) 
next
  case (14 S E \<phi> I \<psi>)
  show ?case apply (rule check_binary_sound) using 14 by auto
next
  case (15 S E \<phi> I \<psi>)
  show ?case apply (rule check_binary_sound) using 15 by auto
next 
  case (16 S E I r)
  then show ?case 
    using check_regex_sound by auto
next
  case (17 S E I r)
  then show ?case
    using check_regex_sound by auto
next
  case (18 S E p \<phi> \<psi>)
  define f0 where "f0 = new_type_symbol ^^ Formula.nfv \<phi>"
  obtain f1 f2 where 
    f1_def: "check (map_sig f0 S((p, Formula.nfv \<phi>) \<mapsto> tabulate TAny 0 (Formula.nfv \<phi>))) TAny (formula.map_formula f0 \<phi>) = return f1" and
    f2_def: "check (map_sig f1 ((map_sig f0 S)((p, Formula.nfv \<phi>) \<mapsto> map TAny [0..<Formula.nfv \<phi>]))) (f1 \<circ> f0 \<circ> E) (formula.map_formula (f1 \<circ> f0) \<psi>) = return f2" and
    f_def: "f = f2 \<circ> f1 \<circ> f0"
    unfolding f0_def using 18(3) by(auto simp:Let_def split:bind_splits)
  have wf_sub: "wf_formula \<phi>" "wf_formula \<psi>"
    using 18(4) by auto
  note wty1 = 18(1)[OF f0_def f1_def wf_formula_map[OF wf_sub(1)]]
  note wty2 = 18(2)[OF f0_def f1_def f2_def wf_formula_map[OF wf_sub(2)]]
  have "wf_f f0"
    unfolding f0_def wf_f_def new_type_symbol_pow by auto
  then have "wf_f f"
    unfolding f_def using wf_f_comp wty1 wty2 wty_result_fX_def by auto
  moreover
  {
    fix fa
    assume 
      wf: "wf_f (TCst \<circ> fa)" and
      wty: "(map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa (formula.LetPast p \<phi> \<psi>))"
    obtain E' where wty_sub:
      "(map_sig fa S)((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E' \<turnstile> formula.map_formula fa \<phi>" 
      "(map_sig fa S)((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), fa \<circ> E \<turnstile> formula.map_formula fa \<psi>"
      using wty by (auto intro:wty_formula.intros elim:wty_formula.cases)
    define fa' where fa'_def: "fa' = (\<lambda>t. (case t of TAny n \<Rightarrow> if n < Formula.nfv \<phi> then E' n else fa (TAny (n - Formula.nfv \<phi>)) |
                                                     TNum n \<Rightarrow> fa (TNum (n - Formula.nfv \<phi>)) |
                                                     _ \<Rightarrow> fa t))"
    then have wf_fa': "wf_f (TCst \<circ> fa')"
      using wf unfolding wf_f_def by(auto simp:numeric_ty_def)
    have list_eq: "map (fa' \<circ> TAny) [0..<Formula.nfv \<phi>] = map E' [0..<Formula.nfv \<phi>]"
      unfolding fa'_def by simp
    have fv_eq: "x \<in> fv \<phi> \<Longrightarrow> (fa' \<circ> TAny) x = E' x" for x
      unfolding fa'_def by (simp add: fvi_less_nfv)
    then have fa'_TAny: "x \<in> fv (formula.map_formula (fa' \<circ> f0) \<phi>) \<Longrightarrow> (fa' \<circ> TAny) x = E' x" for x
      unfolding fv_map[of \<phi> "fa' \<circ> f0"] by auto
    have fa'_f0: "fa' \<circ> f0 = fa"
      unfolding fa'_def f0_def
      by (simp add: fun_eq_iff new_type_symbol_pow split: tysym.splits)
    have wty1': "map_sig fa' (map_sig f0 S((p, Formula.nfv \<phi>) \<mapsto> tabulate TAny 0 (Formula.nfv \<phi>))), fa' \<circ> TAny \<turnstile> formula.map_formula fa' (formula.map_formula f0 \<phi>)"
      using wty_sub(1) 
      apply (simp add: tabulate_alt formula.map_comp fa'_f0 map_sig_subst list_eq
          flip: comp_assoc) 
      using fv_eq fv_map wf_formula_map wf_sub(1) wty_formula_fv_cong by blast
    then obtain g1 where wf_g1: "wf_f (TCst \<circ> g1)" and fa'_alt: "fa' = g1 \<circ> f1"
      using wty1 wf_fa' unfolding wty_result_fX_def by auto
    have "map_sig g1 (map_sig f1 (map_sig f0 S((p, Formula.nfv \<phi>) \<mapsto> map TAny [0..<Formula.nfv \<phi>]))),
          g1 \<circ> (f1 \<circ> f0 \<circ> E) \<turnstile> formula.map_formula g1 (formula.map_formula (f1 \<circ> f0) \<psi>)"
      using wty_sub(2)
      by (simp add: tabulate_alt formula.map_comp fa'_f0 map_sig_subst list_eq
          flip: comp_assoc fa'_alt)
    then obtain g2 where wf_g2: "wf_f (TCst \<circ> g2)" and g1_alt: "g1 = g2 \<circ> f2"
      using wty2 wf_g1 unfolding wty_result_fX_def by blast
    then have "fa = g2 \<circ> (f2 \<circ> f1 \<circ> f0)"
      by (simp flip: comp_assoc g1_alt fa'_alt add: fa'_f0)
    then have "\<exists>g. wf_f (TCst \<circ> g) \<and> fa = g \<circ> f"
      unfolding f_def using wf_g2 by blast
  }
  moreover
  {
    fix fa
    assume 
      wf: "wf_f (TCst \<circ> fa)" and
      "\<exists>g. wf_f (TCst \<circ> g) \<and> fa = g \<circ> f"
    then obtain g where wf_g: "wf_f (TCst \<circ> g)" and fa_alt: "fa = g \<circ> (f2 \<circ> f1 \<circ> f0)"
      unfolding f_def by blast
    have wf_g_f2: "wf_f (TCst \<circ> (g \<circ> f2))"
      by (metis comp_assoc wf_f_comp wf_g wty2 wty_result_fX_def)
    have "wf_f (TCst \<circ> (g \<circ> f2 \<circ> f1))"
      by (metis comp_assoc wf_f_comp wf_g wty1 wty2 wty_result_fX_def)
    then have "(map_sig (g \<circ> f2 \<circ> f1)
             (map_sig f0 S((p, Formula.nfv (formula.map_formula f0 \<phi>)) \<mapsto>
              tabulate TAny 0 (Formula.nfv \<phi>))),
            (g \<circ> f2 \<circ> f1) \<circ> TAny \<turnstile> formula.map_formula (g \<circ> f2 \<circ> f1) (formula.map_formula f0 \<phi>))"
      using wty1 wf_g_f2 unfolding wty_result_fX_def by auto
    then have 1: "(map_sig fa S)((p, Formula.nfv \<phi>) \<mapsto> tabulate ((g \<circ> f2 \<circ> f1) \<circ> TAny) 0 (Formula.nfv \<phi>)), (g \<circ> f2 \<circ> f1) \<circ> TAny \<turnstile> formula.map_formula fa \<phi>"
      unfolding fa_alt map_sig_comp[symmetric] map_sig_subst tabulate_alt map_map formula.map_comp comp_assoc by auto
    have "map_sig (g \<circ> f2) (map_sig f1 (map_sig f0 S((p, Formula.nfv \<phi>) \<mapsto> map TAny [0..<Formula.nfv \<phi>]))),
        (g \<circ> f2) \<circ> (f1 \<circ> f0 \<circ> E)
        \<turnstile> formula.map_formula (g \<circ> f2) (formula.map_formula (f1 \<circ> f0) \<psi>)"
      using wty2 wf_g wf_g_f2 unfolding wty_result_fX_def by blast
    then have 2: "(map_sig fa S)((p, Formula.nfv \<phi>) \<mapsto> tabulate ((g \<circ> f2 \<circ> f1) \<circ> TAny) 0 (Formula.nfv \<phi>)), fa \<circ> E
        \<turnstile> formula.map_formula fa \<psi>"
      by (simp add: fa_alt map_sig_subst comp_assoc tabulate_alt formula.map_comp)
    have "map_sig fa S, fa \<circ> E \<turnstile> formula.map_formula fa (formula.LetPast p \<phi> \<psi>)"
      using 1 2 by (auto intro!: wty_formula.LetPast)
  }
  ultimately show ?case
    unfolding wty_result_fX_def by blast
next
  case (19 S E t)
  then have f_def: "check_trm E (TCst TInt) t = return f" by auto
  show ?case using check_trm_sound[OF f_def] 
    unfolding wty_result_fX_trm_def wty_result_fX_def
    by(auto elim!:wty_formula.cases intro!: wty_formula.intros) (auto simp add:wf_f_def)
next case (20 S E t)
  then have f_def: "check_trm E (TCst TInt) t = return f" by auto
  show ?case using check_trm_sound[OF f_def] 
    unfolding wty_result_fX_trm_def wty_result_fX_def
    by(auto elim!:wty_formula.cases intro!: wty_formula.intros) (auto simp add:wf_f_def)
qed 

lemma check_pred_complete:
  "S (r, length ts) = Some tys \<Longrightarrow> list_all2 (wty_trm (f \<circ> E)) ts (map f tys) \<Longrightarrow> check_pred r E ts tys = error e \<Longrightarrow> wf_f (TCst \<circ> f) \<Longrightarrow> False"
proof(induction arbitrary: f S rule:check_pred.induct)
  case (1 r E trm trms t ts)
  then have wty: "f \<circ> E \<turnstile> trm :: f t" using 1(3) by (auto simp del:comp_apply)
  obtain f' where f'_def: "check_trm E t trm = return f'"
    using check_trm_complete'[OF _ 1(5) wty] sum.exhaust_sel by blast
  obtain g where g_def: "wf_f (TCst \<circ> g)" "f = g \<circ> f'" 
    using check_trm_sound[OF f'_def] wty 1(5) unfolding wty_result_fX_trm_def by auto
  define S' where "S' = (\<lambda>k. if k = (r, length trms) then Some ts else None)"
  then have S': "map_sig f' S' (r, length trms) = Some (map f' ts)" by (auto simp:map_sig_def)
  have la2: "list_all2 (wty_trm (g \<circ> (f' \<circ> E))) trms (map g (map f' ts))" 
    using 1(3) unfolding g_def(2) by (metis (no_types, lifting) list.map_comp list.rel_inject(2) list.simps(9) rewriteR_comp_comp)
  show ?case using 1(1)[OF f'_def, of "map_sig f' S'", OF S' la2 _ g_def(1)] 1(4) f'_def by(auto simp del:comp_apply split:bind_splits)
next 
  case (2 E X)
  then show ?case by auto
next
  case ("3_1" E X v va)
  then show ?case by blast
next
  case ("3_2" E X v va)
  then show ?case by force
qed

lemma check_binary_complete: assumes 
  IH: "\<And>\<phi>' S E f e. size \<phi>' \<le> size \<phi> + size \<psi> \<Longrightarrow> check S E \<phi>' = error e \<Longrightarrow> map_sig f S, f \<circ> E \<turnstile> formula.map_formula f \<phi>'\<Longrightarrow> wf_f (TCst \<circ> f) \<Longrightarrow> wf_formula \<phi>' \<Longrightarrow> False" and
  none: "check S E form = error e" and
  wty: "map_sig f S, f \<circ> E \<turnstile> formula.map_formula f form" and
  wf: "wf_f (TCst \<circ> f)" and
  wformula: "wf_formula form" and
  type: "form \<in> {formula.Or \<phi> \<psi>, formula.And \<phi> \<psi>, formula.Since \<phi> I \<psi>, formula.Until \<phi> I \<psi>}" shows "False"
proof -
  have wformulas: "wf_formula \<phi>" "wf_formula \<psi>" using wformula type by auto
  have wtys: "map_sig f S, f \<circ> E \<turnstile> formula.map_formula f \<phi>" "map_sig f S, f \<circ> E \<turnstile> formula.map_formula f \<psi>"
    using wty type by(auto elim:wty_formula.cases)
  obtain f' where f_def: "check S E \<phi> = return f'"
    using IH[OF _ _ wtys(1) wf wformulas(1)] sum.exhaust_sel by auto 
  have "wty_result_fX S E \<phi> f'" using check_sound_proven[OF f_def] wformula type by auto
  then obtain g where g_def: "wf_f (TCst \<circ> g)" "f = g \<circ> f'" unfolding wty_result_fX_def using wtys(1) wf by auto
  have wty': "map_sig g (map_sig f' S), g \<circ> (f' \<circ> E) \<turnstile> formula.map_formula g (formula.map_formula f' \<psi>)" 
    unfolding formula.map_comp using wtys(2) g_def(2) by (simp add: fun.map_comp)
  show ?thesis using IH[OF _ _ wty' g_def(1)] wformulas(2) f_def none type by(auto simp:check_two_formulas_def split:bind_splits)
qed

lemma check_regex_binop_complete:
  assumes 
    type: "type = Formula.MatchP \<or> type = Formula.MatchF" and
    binop: "binop = regex.Plus \<or> binop = regex.Times" and
    IH: "\<And>\<phi>' S E f e. size \<phi>' \<le> regex.size_regex size (binop r1 r2) \<Longrightarrow> check S E \<phi>' = error e \<Longrightarrow> map_sig f S, f \<circ> E \<turnstile> formula.map_formula f \<phi>' \<Longrightarrow> wf_f (TCst \<circ> f) \<Longrightarrow> wf_formula \<phi>' \<Longrightarrow> False" and
    none: "check_regex check S E (binop r1 r2) = error e" and
    wty: "map_sig f S, f \<circ> E \<turnstile> formula.map_formula f (type I (binop r1 r2))" and
    wf: "wf_f (TCst \<circ> f)" and
    wformula: "wf_formula (type I (binop r1 r2))"
  shows "False" 
proof -
  have wfs: "wf_formula (type I r1)" "wf_formula (type I r2)"
    using type binop wformula by auto
  have "regex.pred_regex (wty_formula (map_sig f S) (f \<circ> E)) (regex.map_regex (formula.map_formula f) (binop r1 r2))"
    using type binop wty by (auto elim:wty_formula.cases)
  then have wtys: 
    "(map_sig f S), f \<circ> E \<turnstile> formula.map_formula f (type I r1)"
    "(map_sig f S), f \<circ> E \<turnstile> formula.map_formula f (type I r2)"
    using type binop by (auto intro!: wty_formula.intros)
  obtain f' where f'_def: "check S E (type I r1) = return f'"
    using IH[OF _ _ wtys(1) wf wfs(1)] type binop sum.exhaust_sel by auto blast+
  have wf': "wf_formula (formula.map_formula f' (type I r2))" using wfs(2) type by auto
  obtain g where g_def: "wf_f (TCst \<circ> g)" "f = g \<circ> f'"
    using check_sound_proven[OF f'_def wfs(1)] wf wtys(1) unfolding wty_result_fX_def by auto
  have "(map_sig f S), (g \<circ> f') \<circ> E \<turnstile> formula.map_formula g (formula.map_formula f' (type I r2))"
    unfolding formula.map_comp using g_def(2) type  wtys(2) by blast
  then have wty': "(map_sig g (map_sig f' S)), g \<circ> (f' \<circ> E) \<turnstile> formula.map_formula g (formula.map_formula f' (type I r2))"
    by (simp add: fun.map_comp g_def(2))
  show ?thesis using IH[OF _ _ wty' g_def(1) wf'] f'_def none type binop by(auto split:bind_splits)
qed

lemma check_regex_complete:
  assumes type: "type = Formula.MatchP \<or> type = Formula.MatchF" and
    IH: "\<And>\<phi>' S E f e. size \<phi>' \<le> regex.size_regex size r \<Longrightarrow> check S E \<phi>' = error e \<Longrightarrow> map_sig f S, f \<circ> E \<turnstile> formula.map_formula f \<phi>' \<Longrightarrow> wf_f (TCst \<circ> f) \<Longrightarrow> wf_formula \<phi>' \<Longrightarrow> False"
  shows "\<phi> = type I r \<Longrightarrow> check_regex check S E r = error e \<Longrightarrow> map_sig f S, f \<circ> E \<turnstile> formula.map_formula f \<phi> \<Longrightarrow> wf_f (TCst \<circ> f) \<Longrightarrow> wf_formula \<phi> \<Longrightarrow> False"
  using IH
proof(induction r arbitrary: E f \<phi>)
  case (Skip x)
  then show ?case by auto
next
  case (Test x)
  have "map_sig f S, f \<circ> E \<turnstile> formula.MatchP I (regex.Test (formula.map_formula f x)) \<or>
        map_sig f S, f \<circ> E \<turnstile> formula.MatchF I (regex.Test (formula.map_formula f x))"
    using type Test(1, 3) by (auto simp del: comp_apply)
  then have wty: "map_sig f S, f \<circ> E \<turnstile> formula.map_formula f x" 
    by(auto elim:wty_formula.cases)  
  have wf: "wf_formula x" using Test(1, 5) type by auto
  show ?case using Test(6)[OF _ _ wty Test(4) wf] Test(2) by auto
next
  case (Plus r1 r2)
  show ?case using check_regex_binop_complete[OF type, of regex.Plus, OF _ _ Plus(4-7)[unfolded Plus(3)]] Plus(8) by blast
next
  case (Times r1 r2)
  show ?case using check_regex_binop_complete[OF type, of regex.Times, OF _ _ Times(4-7)[unfolded Times(3)]] Times(8) by blast
next
  case (Star r)
  have wty: "map_sig f S, f \<circ> E \<turnstile> formula.map_formula f (type I r)"
    using star_regex_eq[OF type, of "map_sig f S" "f \<circ> E" f I r] Star(4)[unfolded Star(2)] by auto
  have wf: "wf_formula (type I r)"
    using Star(6)[unfolded Star(2)] type by auto
  then show ?case using Star(3) Star(7)[OF _ _ wty Star(5) wf] type by auto
qed

lemma check_ands_complete:
  assumes IH: "\<And>\<phi> S E f e. size \<phi> \<le> size_list size \<phi>s \<Longrightarrow> check S E \<phi> = error e \<Longrightarrow> map_sig f S, f \<circ> E \<turnstile> formula.map_formula f \<phi> \<Longrightarrow> wf_f (TCst \<circ> f) \<Longrightarrow>  wf_formula \<phi> \<Longrightarrow> False"
  shows "check_ands check S E \<phi>s = error e \<Longrightarrow> map_sig f S, f \<circ> E \<turnstile> formula.map_formula f (Formula.Ands \<phi>s) \<Longrightarrow> wf_f (TCst \<circ> f) \<Longrightarrow> wf_formula (Formula.Ands \<phi>s) \<Longrightarrow> False"
  using IH
proof(induction \<phi>s arbitrary: e)
  case Nil
  then show ?case by(auto simp:check_ands_def)
next
  case (Cons a \<phi>s)
  have wfs: "wf_formula (formula.Ands \<phi>s)" "wf_formula a" using Cons(5) by auto
  have wty_pre: "\<forall>\<phi> \<in> set (a#\<phi>s). map_sig f S, f \<circ> E \<turnstile> formula.map_formula f \<phi>" 
    using Cons(3) by(auto simp del:comp_apply elim:wty_formula.cases)
  then have wtys: "map_sig f S, f \<circ> E \<turnstile> formula.map_formula f (formula.Ands \<phi>s)" "map_sig f S, f \<circ> E \<turnstile> formula.map_formula f a"
    by (auto intro!:wty_formula.intros)
  have "(foldr (check_ands_f check S E) \<phi>s (return id)) = error e \<Longrightarrow> False" for e
    using Cons(1)[OF _  wtys(1) Cons(4) wfs(1)] Cons(6) by (smt (verit, del_insts) check_ands_def dual_order.trans le_add1 le_add_same_cancel2 list.size(2) zero_le)
  then obtain f' where f'_def: "foldr (check_ands_f check S E) \<phi>s (return id) = return f'"
    using sum.exhaust_sel by auto
  then have none: "check (map_sig f' S) (f' \<circ> E) (formula.map_formula f' a) = error e" 
    using Cons(2)[unfolded check_ands_def foldr.simps comp_apply f'_def]
    by(auto simp:check_ands_f_def split:bind_splits)
  have "wty_result_fX S E (formula.Ands \<phi>s) f'" 
    using check_sound_proven[OF _ wfs(1)] f'_def by(auto simp: check_ands_def) 
  then obtain g where g_def: "wf_f (TCst \<circ> g)" "f = g \<circ> f'" 
    using wtys(1) Cons(4) unfolding wty_result_fX_def by auto
  have "map_sig (g \<circ> f') S, (g \<circ> f') \<circ> E \<turnstile> formula.map_formula g (formula.map_formula f' a)"
    unfolding formula.map_comp using wtys(2) g_def(2) by blast
  then have wty': "map_sig g (map_sig f' S), g \<circ> (f' \<circ> E) \<turnstile> formula.map_formula g (formula.map_formula f' a)"
    by (simp add: fun.map_comp)
  show ?case using Cons(6)[OF _ none wty' g_def(1)] wfs(2) by auto
qed

lemma check_comparison_complete: 
  assumes 
    none: "check S E form = error e" and 
    wty: "map_sig f S, f \<circ> E \<turnstile> formula.map_formula f form" and
    wf: "wf_f (TCst \<circ> f)" and
    wformula: "wf_formula form" and
    type: "form \<in> {formula.Less t1 t2,formula.LessEq t1 t2,formula.Eq t1 t2}" 
  shows "False"
proof -
  obtain t where wtys: "f \<circ> E \<turnstile> t1 :: t" "f \<circ> E \<turnstile> t2 :: t" 
    using wty type by(auto elim:wty_formula.cases)
  define nn where nn_def: "nn = (\<lambda>t'. case t' of TAny (Suc n) \<Rightarrow> TAny n  | TAny 0 \<Rightarrow> TCst t | TNum n \<Rightarrow> TNum (n-1) | _ \<Rightarrow> t' )"
  have nn_n: "nn \<circ> new_type_symbol = id"  by (auto simp add: nn_def new_type_symbol_def split: tysym.splits nat.splits)
  have wf_nn: "wf_f nn" by (auto simp add: nn_def wf_f_def)
  have wty'': "f \<circ> nn \<circ> (new_type_symbol \<circ> E) \<turnstile> t1 :: t" "f \<circ> nn \<circ> (new_type_symbol \<circ> E) \<turnstile> t2 :: t"
    using nn_n wtys by (metis comp_id fun.map_comp)+
  have wfnn: "wf_f (TCst \<circ> (f \<circ> nn))" by (metis comp_assoc local.wf wf_f_comp wf_nn)
  have *: "(f \<circ> nn) (TAny 0) = t" using nn_def wf wf_f_def by(auto)
  then have wty': "f \<circ> nn \<circ> (new_type_symbol \<circ> E) \<turnstile> t1 :: (f \<circ> nn) (TAny 0)" using wty'' by auto
  obtain f' where f'_def: "check_trm (new_type_symbol \<circ> E) (TAny 0) t1 = return f'"
    using check_trm_complete'[OF _ wfnn wty'] using sum.exhaust_sel by auto
  obtain g where g_def: "wf_f (TCst \<circ> g)" "f \<circ> nn = g \<circ> f'" 
    using check_trm_sound[OF f'_def] wfnn wty' unfolding wty_result_fX_trm_def by auto
  have "(g \<circ> f') \<circ> (new_type_symbol \<circ> E) \<turnstile> t2 :: (g \<circ> f') (TAny 0)"
    unfolding g_def(2) using wty' g_def(2)  type * wty''(2) by auto
  then have g_aux: "g \<circ> (f' \<circ> new_type_symbol \<circ> E) \<turnstile> t2 :: g (f' (TAny 0))"
    by (simp add: fun.map_comp)
  show "False" using check_trm_complete'[OF _ g_def(1) g_aux] f'_def
    using none type by(auto simp:check_comparison_def split:bind_splits)
qed

lemma check_complete': 
  "check S E \<phi> = error e \<Longrightarrow> map_sig f S, f \<circ> E \<turnstile> formula.map_formula f \<phi> \<Longrightarrow> wf_f (TCst \<circ> f) \<Longrightarrow> wf_formula \<phi> \<Longrightarrow> False"
proof (induction S E \<phi> arbitrary: f e rule: check.induct)
  case (1 S E r ts)
  obtain tys' where prelims: "map_sig f S (r, length ts) = Some tys'" "list_all2 (wty_trm (f \<circ> E)) ts tys'"
    using 1(2) Pred by(auto simp del:comp_apply intro!:wty_formula.intros elim:wty_formula.cases)
  obtain tys where *: "S (r, length ts) = Some tys" "tys' = map f tys" using prelims(1) by(auto simp:map_sig_def)
  then show ?case  using check_pred_complete[of S r, OF *(1) prelims(2)[unfolded *(2)] _ 1(3)]  1(1) by auto
next
  case (2 S E p \<phi> \<psi>)
  define f0 where f0_def: "f0 = new_type_symbol ^^ Formula.nfv \<phi>"
  have wfs: "wf_formula \<phi>" "wf_formula \<psi>" using 2(6) by auto
  obtain E' where wtys:
    "map_sig f S, E' \<turnstile> formula.map_formula f \<phi>"
    "map_sig f S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv (formula.map_formula f \<phi>))), (f \<circ> E) \<turnstile> formula.map_formula f \<psi>"
    using 2(4) by(auto simp del:comp_apply elim:wty_formula.cases)
  define fa' where fa'_def: "fa' = (\<lambda>t. (case t of TAny n \<Rightarrow> if n < Formula.nfv \<phi> then E' n else f (TAny (n - Formula.nfv \<phi>)) |
                                                     TNum n \<Rightarrow> f (TNum (n - Formula.nfv \<phi>)) |
                                                     _ \<Rightarrow> f t))"
  then have wf_fa': "wf_f (TCst \<circ> fa')"
    using 2(5) unfolding wf_f_def by(auto simp:numeric_ty_def)
  moreover have fa'_TAny: "x \<in> fv \<phi> \<Longrightarrow> (fa' \<circ> TAny) x = E' x" for x
    unfolding fa'_def by (simp add: fvi_less_nfv)
  moreover have fa'_f0: "fa' \<circ> f0 = f"
    unfolding fa'_def f0_def
    by (simp add: fun_eq_iff new_type_symbol_pow split: tysym.splits)
  ultimately have wty1': "map_sig fa' (map_sig f0 S), fa' \<circ> TAny \<turnstile> formula.map_formula fa' (formula.map_formula f0 \<phi>)"
    using wtys(1) wty_formula_fv_cong[of "formula.map_formula f \<phi>" E' "fa' \<circ> TAny"]
    by (metis formula.map_comp fv_map map_sig_comp wf_formula_map wfs(1))
  obtain f' where f'_def: "check (map_sig f0 S) TAny (formula.map_formula f0 \<phi>) = return f'" 
    using 2(1)[OF f0_def _ wty1' wf_fa' wf_formula_map[OF wfs(1)]] sum.exhaust_sel by auto
  note wty1 = check_sound_proven[OF f'_def wf_formula_map[OF wfs(1)]] 
  then obtain g1 where wf_g1: "wf_f (TCst \<circ> g1)" and fa'_alt: "fa' = g1 \<circ> f'"
      using wty1' wf_fa' unfolding wty_result_fX_def by blast
  have list_eq: "map (fa' \<circ> TAny) [0..<Formula.nfv \<phi>] = map E' [0..<Formula.nfv \<phi>]"
    unfolding fa'_def by simp
  have wty2': "map_sig g1 (map_sig f' (map_sig f0 S((p, Formula.nfv \<phi>) \<mapsto> map TAny [0..<Formula.nfv \<phi>]))),
          g1 \<circ> (f' \<circ> f0 \<circ> E) \<turnstile> formula.map_formula g1 (formula.map_formula (f' \<circ> f0) \<psi>)"
    using wtys(2)
    by (simp add: tabulate_alt formula.map_comp fa'_f0 map_sig_subst list_eq
          flip: comp_assoc fa'_alt)
  show ?case 
    using 2(2)[OF f0_def f'_def _ wty2' wf_g1 wf_formula_map[OF wfs(2)]] f'_def 2(3) 
    by(auto simp del:comp_apply simp:Let_def f0_def split:bind_splits)
next
  case (3 S E t1 t2)
  then show ?case using check_comparison_complete[OF 3(1-4)] by auto
next
  case (4 S E t1 t2)
  then show ?case using check_comparison_complete[OF 4(1-4)] by auto
next
  case (5 S E t1 t2)
  then show ?case using check_comparison_complete[OF 5(1-4)] by auto
next
  case (6 S E \<phi>)
  have wty: "map_sig f S, f \<circ> E \<turnstile> formula.map_formula f \<phi>" 
    using 6(3) by(auto simp del:comp_apply elim:wty_formula.cases)
  show ?case using 6 using 6(1)[OF _ wty] by(auto simp:used_tys_def)
next
  case (7 S E \<phi> \<psi>)
  show ?case using check_binary_complete[OF _ 7(2-5)] 7(1) by blast
next
  case (8 S E \<phi> \<psi>)
  show ?case using check_binary_complete[OF _ 8(2-5)] 8(1) by blast
next
  case (9 S E \<phi>s)
  show ?case using check_ands_complete[OF _ 9(2-5)[unfolded check.simps]] 9(1) by blast
next
  case (10 S E t \<phi>)
  have wf: "wf_formula \<phi>" using 10(5) by auto
  have "map_sig f S, case_nat (f t) (f \<circ> E) \<turnstile> formula.map_formula f \<phi>"
    using 10(3) by(auto simp del: comp_apply elim:wty_formula.cases)
  then have wty: "map_sig f S, f \<circ> (\<lambda>a. case a of 0 \<Rightarrow> t | Suc x \<Rightarrow> E x) \<turnstile> formula.map_formula f \<phi>"
    unfolding comp_apply Nitpick.case_nat_unfold by (smt (verit, best) local.wf wf_formula_map wty_formula_fv_cong)
  show ?case  using 10(1)[OF _ wty 10(4) wf] 10(2) by auto
next
  case (11 S E y agg_type d tys trm \<phi>)
  have "map_sig f S, f \<circ> E \<turnstile> formula.Agg y (agg_type, f d) (map f tys) trm (formula.map_formula f \<phi>)" 
    using 11(3) by(auto simp del:comp_apply)
  then obtain t where wtys:
    "(f \<circ> E) y = t_res agg_type t"
    "agg_env (f \<circ> E) (map f tys) \<turnstile> trm :: t"
    "map_sig f S, agg_env (f \<circ> E) (map f tys) \<turnstile> formula.map_formula f \<phi>"
    "t \<in> agg_trm_type agg_type"
    "f d = t_res agg_type t"
    by(auto elim:wty_formula.cases)
  have env_eq: "agg_env (f \<circ> E) (map f tys) = f \<circ> agg_tysenv E tys" by(auto simp:agg_env_def agg_tysenv_def)
  define nn where nn_def: "nn = (\<lambda>t'. if t' = (agg_trm_tysym agg_type) then (TCst t) else case t' of TAny n \<Rightarrow> TAny (n - 1) | TNum n \<Rightarrow> TNum (n-1) | _ \<Rightarrow> t' )"
  have nn_n: "nn \<circ> new_type_symbol = id"  by(cases agg_type; auto simp add: nn_def new_type_symbol_def split: tysym.splits nat.splits if_splits)
  have wf_nn: "wf_f nn" using 11(4) wtys(4) by(cases agg_type; auto simp add: nn_def wf_f_def)
  have wty: "(f \<circ> nn) \<circ> (new_type_symbol \<circ> agg_tysenv E tys) \<turnstile> trm :: (f \<circ> nn) (agg_trm_tysym agg_type)"
    using wtys(2)[unfolded env_eq] by (metis "11.prems"(3) comp_apply comp_id fun.map_comp nn_def nn_n tysym.inject(3) wf_f_def)
  note wf_f_nn = wf_f_comp[OF 11(4) wf_nn, unfolded comp_assoc]
  obtain f' where f'_def: "check_trm (new_type_symbol \<circ> agg_tysenv E tys) (agg_trm_tysym agg_type) trm = return f'"
    using check_trm_complete'[OF _ wf_f_nn wty] sum.exhaust_sel by auto
  obtain g where g_def: "wf_f (TCst \<circ> g)" "f \<circ> nn = g \<circ> f'" 
    using check_trm_sound[OF f'_def] wf_f_nn wty unfolding wty_result_fX_trm_def by force
  then have g_def': "f = g \<circ> f' \<circ> new_type_symbol" by (metis comp_id fun.map_comp nn_n)
  note wty = wtys(3)[unfolded env_eq, unfolded g_def' comp_assoc[of g] formula.map_comp[symmetric, of g] map_sig_comp[symmetric, of g]]
  obtain f'' where f''_def: "check (map_sig (f' \<circ> new_type_symbol) S)  (f' \<circ> new_type_symbol \<circ> agg_tysenv E tys) (formula.map_formula (f' \<circ> new_type_symbol) \<phi>) = return f''" 
    using 11(1)[OF f'_def _ wty g_def(1)] 11(5) sum.exhaust_sel by (auto simp del:comp_apply)
  obtain g' where g'_def: "wf_f (TCst \<circ> g')" "g = g' \<circ> f''" 
    using check_sound_proven[OF f''_def] 11(5) wty g_def(1) unfolding wty_result_fX_def by(auto simp del:comp_apply)
  have t_res_eq: "t_res agg_type t = (f \<circ> nn) (t_res_tysym agg_type (agg_trm_tysym agg_type))"
    using 11(4) by(cases agg_type; auto simp:nn_def wf_f_def)
  have wty: "g' \<circ> (f'' \<circ> f' \<circ> new_type_symbol \<circ> E)  \<turnstile> trm.Var y :: g' (f'' (f' (t_res_tysym agg_type (agg_trm_tysym agg_type))))"
    using wtys(1)[unfolded g_def' g'_def(2) comp_assoc[of g'] t_res_eq] by (smt (verit, best) Var comp_def g'_def(2) g_def' g_def(2))
  obtain f''' where f'''_def: "check_trm (f'' \<circ> f' \<circ> new_type_symbol \<circ> E) (f'' (f' (t_res_tysym agg_type (agg_trm_tysym agg_type)))) (trm.Var y) = return f'''" 
    using check_trm_complete'[OF _ g'_def(1) wty] using sum.exhaust_sel by auto 
  obtain g'' where g''_def: "wf_f (TCst \<circ> g'')" "g' = g'' \<circ> f'''" 
    using check_trm_sound[OF f'''_def] wty g'_def(1) unfolding wty_result_fX_trm_def by auto
  have wty: "g'' \<circ> (f''' \<circ> f'' \<circ> f' \<circ> new_type_symbol \<circ> E) \<turnstile> trm.Var y :: g'' (f''' (f'' (f' (new_type_symbol d))))"
    using wtys(1)[unfolded wtys(5)[symmetric] g_def' g'_def(2) g''_def(2)] by (simp add: Var)
  show ?case using f'_def f''_def f'''_def 11(2) using check_trm_complete'[OF _ g''_def(1) wty] 
    by(auto simp del:check_trm.simps split:bind_splits)
next
  case (12 S E I \<phi>)
  have wty: "map_sig f S, f \<circ> E \<turnstile> formula.map_formula f \<phi>" using 12(3) by(auto simp del:comp_apply elim:wty_formula.cases)
  then show ?case using 12(1)[OF _ wty 12(4)] 12(2, 3, 5) by (auto simp:used_tys_def)
next
  case (13 S E I \<phi>)
  have wty: "map_sig f S, f \<circ> E \<turnstile> formula.map_formula f \<phi>" using 13(3) by(auto simp del:comp_apply elim:wty_formula.cases)
  then show ?case using 13(1)[OF _ wty 13(4)] 13(2, 3, 5) by (auto simp:used_tys_def)
next
  case (14 S E \<phi> I \<psi>)
  show ?case using check_binary_complete[OF _ 14(2-5), of \<phi> \<psi>] 14(1) by blast
next
  case (15 S E \<phi> I \<psi>)
  show ?case using check_binary_complete[OF _ 15(2-5), of \<phi> \<psi>] 15(1) by blast
next
  case (16 S E I r)
  show ?case using check_regex_complete[OF _ _ _ 16(2-5)[unfolded check.simps], of formula.MatchF] 16(1) by blast 
next
  case (17 S E I r)
  then show ?case using check_regex_complete[OF _ _ _ 17(2-5)[unfolded check.simps], of formula.MatchP] 17(1) by blast
next
  case (18 S E p \<phi> \<psi>)
  define f0 where f0_def: "f0 = new_type_symbol ^^ Formula.nfv \<phi>"
  have wfs: "wf_formula \<phi>" "wf_formula \<psi>" using 18(6) by auto
  obtain E' where wtys:
    "map_sig f S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv (formula.map_formula f \<phi>))), E' \<turnstile> formula.map_formula f \<phi>"
    "map_sig f S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv (formula.map_formula f \<phi>))), (f \<circ> E) \<turnstile> formula.map_formula f \<psi>"
    using 18(4) by(auto simp del:comp_apply elim:wty_formula.cases)
  define fa' where fa'_def: "fa' = (\<lambda>t. (case t of TAny n \<Rightarrow> if n < Formula.nfv \<phi> then E' n else f (TAny (n - Formula.nfv \<phi>)) |
                                                     TNum n \<Rightarrow> f (TNum (n - Formula.nfv \<phi>)) |
                                                     _ \<Rightarrow> f t))"
  then have wf_fa': "wf_f (TCst \<circ> fa')"
    using 18(5) unfolding wf_f_def by(auto simp:numeric_ty_def)
  have fa'_TAny: "x \<in> fv \<phi> \<Longrightarrow> (fa' \<circ> TAny) x = E' x" for x
    unfolding fa'_def by (simp add: fvi_less_nfv)
  have fa'_f0: "fa' \<circ> f0 = f"
    unfolding fa'_def f0_def
    by (simp add: fun_eq_iff new_type_symbol_pow split: tysym.splits)
  have list_eq: "map (fa' \<circ> TAny) [0..<Formula.nfv \<phi>] = map E' [0..<Formula.nfv \<phi>]"
    unfolding fa'_def by simp
  have wty1': "map_sig fa'
 (map_sig f0 S((p, Formula.nfv (formula.map_formula f0 \<phi>)) \<mapsto> tabulate TAny 0 (Formula.nfv \<phi>))),
fa' \<circ> TAny \<turnstile> formula.map_formula fa' (formula.map_formula f0 \<phi>)"
    using wtys(1) 
      apply (simp add: tabulate_alt formula.map_comp fa'_f0 map_sig_subst list_eq
          flip: comp_assoc) 
    using fv_map wf_formula_map wfs(1) wty_formula_fv_cong fa'_TAny by blast
  obtain f1 where 
    f1_def: "check (map_sig f0 S((p, Formula.nfv \<phi>) \<mapsto> tabulate TAny 0 (Formula.nfv \<phi>))) TAny (formula.map_formula f0 \<phi>) = return f1"
    using 18(1)[OF f0_def _ wty1'[unfolded nfv_map] wf_fa' wf_formula_map[OF wfs(1)]] sum.exhaust_sel by blast
  note wty1 = check_sound_proven[OF f1_def wf_formula_map[OF wfs(1)]] 
  then obtain g1 where wf_g1: "wf_f (TCst \<circ> g1)" and fa'_alt: "fa' = g1 \<circ> f1"
      using wty1'[unfolded nfv_map] wf_fa' unfolding wty_result_fX_def by blast
  have list_eq: "map (fa' \<circ> TAny) [0..<Formula.nfv \<phi>] = map E' [0..<Formula.nfv \<phi>]"
    unfolding fa'_def by simp
  have wty2': "map_sig g1 (map_sig f1 (map_sig f0 S((p, Formula.nfv \<phi>) \<mapsto> map TAny [0..<Formula.nfv \<phi>]))),
          g1 \<circ> (f1 \<circ> f0 \<circ> E) \<turnstile> formula.map_formula g1 (formula.map_formula (f1 \<circ> f0) \<psi>)"
    using wtys(2)
    by (simp add: tabulate_alt formula.map_comp fa'_f0 map_sig_subst list_eq
          flip: comp_assoc fa'_alt)
  show ?case 
    using 18(2)[OF f0_def f1_def _ wty2' wf_g1 wf_formula_map[OF wfs(2)]] f1_def 18(3)
    by(auto simp del:comp_apply simp:Let_def f0_def split:bind_splits)
next
  case (19 S E t)
  then show ?case using check_trm_complete' 
    by(auto simp del:comp_apply elim!:wty_formula.cases; auto simp:wf_f_def) metis
next
  case (20 S E t)
  then show ?case using check_trm_complete' 
    by(auto simp del:comp_apply elim!:wty_formula.cases; auto simp:wf_f_def) metis
qed

lemma check_complete:
  "check S E \<phi> = error e \<Longrightarrow> wty_result_fX S E \<phi> f \<Longrightarrow> wf_formula \<phi> \<Longrightarrow> False"
  using check_complete' by (metis (no_types, lifting) fun.map_comp wf_f_comp wf_trivial wty_result_fX_def)

fun check_wty_regex :: "(tysym Formula.formula \<Rightarrow> bool) \<Rightarrow> tysym Formula.formula Regex.regex \<Rightarrow> bool"  where
"check_wty_regex check_wty_formula (Regex.Skip l) = True"
| "check_wty_regex check_wty_formula (Regex.Test \<phi>)  = check_wty_formula \<phi>"
| "check_wty_regex check_wty_formula (Regex.Plus r s)  = (check_wty_regex check_wty_formula r \<and> check_wty_regex check_wty_formula s)"
| "check_wty_regex check_wty_formula (Regex.Times r s)  = (check_wty_regex check_wty_formula r \<and> check_wty_regex check_wty_formula s)"
| "check_wty_regex check_wty_formula (Regex.Star r)  = check_wty_regex check_wty_formula r"


lemma check_wty_regex_cong[fundef_cong]:
  "(\<And>\<phi>'. size \<phi>' \<le> regex.size_regex size r \<Longrightarrow> check_wty_formula \<phi>' = check_wty_formula' \<phi>') \<Longrightarrow> check_wty_regex check_wty_formula r = check_wty_regex check_wty_formula' r"
  by (induction check_wty_formula r  rule: check_wty_regex.induct) (auto split: option.splits) 

fun check_wty_formula :: "tysym Formula.formula \<Rightarrow> bool"
  where 
  "check_wty_formula (Formula.Let p \<phi> \<psi>) = (check_wty_formula \<phi> \<and> check_wty_formula \<psi>)"
| "check_wty_formula (Formula.Neg \<phi>) = check_wty_formula \<phi>"
| "check_wty_formula (Formula.Or \<phi> \<psi>) = (check_wty_formula \<phi> \<and> check_wty_formula \<psi>)"
| "check_wty_formula (Formula.And \<phi> \<psi>) = (check_wty_formula \<phi> \<and> check_wty_formula \<psi>)"
| "check_wty_formula (Formula.Ands \<phi>s) = foldl (\<and>) True (map check_wty_formula \<phi>s)" 
| "check_wty_formula (Formula.Exists t \<phi>) = check_wty_formula \<phi>" 
| "check_wty_formula (Formula.Agg y (agg_type, d) tys trm \<phi>) = (case d of TCst _ \<Rightarrow> check_wty_formula \<phi> | _ \<Rightarrow> False)"
| "check_wty_formula (Formula.Prev I \<phi>) = check_wty_formula \<phi>"
| "check_wty_formula (Formula.Next I \<phi>) = check_wty_formula \<phi>"
| "check_wty_formula (Formula.Since \<phi> I \<psi>) = (check_wty_formula \<phi> \<and> check_wty_formula \<psi>)"
| "check_wty_formula (Formula.Until \<phi> I \<psi>) = (check_wty_formula \<phi> \<and> check_wty_formula \<psi>)"
| "check_wty_formula (Formula.MatchF I r) = check_wty_regex check_wty_formula r"
| "check_wty_formula (Formula.MatchP I r) =  check_wty_regex check_wty_formula r"
| "check_wty_formula (Formula.LetPast p \<phi> \<psi>) = (check_wty_formula \<phi> \<and> check_wty_formula \<psi>)"
| "check_wty_formula _ = True" 

fun convert_tysym :: "tysym \<Rightarrow> ty" where
  "convert_tysym (TCst a) = a"
| "convert_tysym _ = TFloat"

definition type_check where
  "type_check S \<phi> = 
    check S TAny \<phi> \<bind>
    (\<lambda>f. if check_wty_formula (formula.map_formula f \<phi>)
         then return (formula.map_formula (convert_tysym \<circ> f) \<phi>)
         else error STR ''failed to infer ground type for aggregation result'')"   
end
(*>*)
