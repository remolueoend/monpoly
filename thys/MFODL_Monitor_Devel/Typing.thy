(*<*)
theory Typing
  imports Formula
begin
(*>*)

section \<open>Typing\<close>

subsection \<open>Types\<close>

datatype ty = TInt | TFloat | TString

fun ty_of :: "event_data \<Rightarrow> ty" where
  "ty_of (EInt _) = TInt"
| "ty_of (EFloat _) = TFloat"
| "ty_of (EString _) = TString"

definition "numeric_ty = {TInt, TFloat}"


subsection \<open>Terms\<close>

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
| Mod:"E \<turnstile> x :: t \<Longrightarrow> E \<turnstile> y :: t \<Longrightarrow> t \<in> numeric_ty \<Longrightarrow> E \<turnstile> Formula.Mod x y :: t"
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

lemma ty_of_mod: "ty_of x = t \<Longrightarrow> ty_of y = t \<Longrightarrow> t \<in> numeric_ty \<Longrightarrow> ty_of (x mod y) = t"
  by (cases x; cases y) (simp_all add: numeric_ty_def)

lemma ty_of_eval_trm: "E \<turnstile> x :: t \<Longrightarrow> \<forall>y\<in>fv_trm x. ty_of (v ! y) = E y \<Longrightarrow> 
ty_of (Formula.eval_trm v x) = t"
  by (induction pred: wty_trm) (simp_all add: ty_of_plus ty_of_minus ty_of_uminus 
      ty_of_mult ty_of_div ty_of_mod)

lemma wty_trm_fv_cong:
  assumes "\<And>y. y \<in> fv_trm x \<Longrightarrow> E y = E' y"
  shows "E \<turnstile> x :: t \<longleftrightarrow> E' \<turnstile> x :: t"
proof -
  have "E \<turnstile> x :: t \<Longrightarrow> (\<And>y. y \<in> fv_trm x \<Longrightarrow> E y = E' y) \<Longrightarrow> E' \<turnstile> x :: t" for E E'
    by (induction pred: wty_trm) (auto intro: wty_trm.intros)
  with assms show ?thesis by auto
qed


subsection \<open>Formulas\<close>

type_synonym sig = "Formula.name \<rightharpoonup> ty list"

definition wty_tuple :: "ty list \<Rightarrow> event_data list \<Rightarrow> bool" where
  "wty_tuple = list_all2 (\<lambda>t x. ty_of x = t)"

definition wty_event :: "sig \<Rightarrow> Formula.name \<Rightarrow> event_data list \<Rightarrow> bool" where
  "wty_event S p xs \<longleftrightarrow> (case S p of Some ts \<Rightarrow> wty_tuple ts xs | None \<Rightarrow> False)"

definition wty_envs :: "sig \<Rightarrow> Formula.trace \<Rightarrow> (Formula.name \<rightharpoonup> nat \<Rightarrow> event_data list set) \<Rightarrow> bool" where
  "wty_envs S \<sigma> V \<longleftrightarrow> (\<forall>i.
    (\<forall>(p,xs)\<in>\<Gamma> \<sigma> i. p \<notin> dom V \<longrightarrow> wty_event S p xs) \<and>
    (\<forall>p\<in>dom V. \<forall>xs\<in>the (V p) i. wty_event S p xs))"

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

lemma wty_envs_\<Gamma>_D: "wty_envs S \<sigma> V \<Longrightarrow> p \<notin> dom V \<Longrightarrow> (p, xs) \<in> \<Gamma> \<sigma> i \<Longrightarrow> S p = Some ts \<Longrightarrow>
  wty_tuple ts xs"
  by (fastforce simp: wty_envs_def wty_event_def split: option.splits)

lemma wty_envs_V_D: "wty_envs S \<sigma> V \<Longrightarrow> p \<in> dom V \<Longrightarrow> xs \<in> the (V p) i \<Longrightarrow> S p = Some ts \<Longrightarrow>
  wty_tuple ts xs"
  by (fastforce simp: wty_envs_def wty_event_def split: option.splits)

find_theorems "Regex.pred_regex"
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
  Pred: "S p = Some tys \<Longrightarrow> list_all2 (\<lambda>tm ty. E \<turnstile> tm :: ty) tms tys \<Longrightarrow> S, E \<turnstile> Formula.Pred p tms"
| Let: "S, E' \<turnstile> \<phi> \<Longrightarrow> S(p \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E \<turnstile> \<psi> \<Longrightarrow> S, E \<turnstile> Formula.Let p \<phi> \<psi>"
| Eq: "E \<turnstile> x :: t \<Longrightarrow> E \<turnstile> y :: t \<Longrightarrow> S, E \<turnstile> Formula.Eq x y"
| Less: "E \<turnstile> x :: t \<Longrightarrow> E \<turnstile> y :: t \<Longrightarrow> S, E \<turnstile> Formula.Less x y"
| LessEq: "E \<turnstile> x :: t \<Longrightarrow> E \<turnstile> y :: t \<Longrightarrow> S, E \<turnstile> Formula.LessEq x y"
| Neg: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> Formula.Neg \<phi>"
| Or: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> \<psi> \<Longrightarrow> S, E \<turnstile> Formula.Or \<phi> \<psi>"
| And: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> \<psi> \<Longrightarrow> S, E \<turnstile> Formula.And \<phi> \<psi>" 
| Ands: "\<forall>\<phi> \<in> set \<phi>s. S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> Formula.Ands \<phi>s"
| Exists: "S, case_nat t E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> Formula.Exists t \<phi>"
| Agg: " E s =  t_res agg_type t \<Longrightarrow> agg_env E tys  \<turnstile> f :: t \<Longrightarrow> S, agg_env E tys \<turnstile> \<phi>  \<Longrightarrow>
   t \<in> agg_trm_type agg_type \<Longrightarrow> ty_of d = t_res agg_type t \<Longrightarrow>
          S, E \<turnstile> Formula.Agg s (agg_type, d) tys f \<phi>"
| Prev: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> Formula.Prev \<I> \<phi>"
| Next: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> Formula.Next \<I> \<phi>"
| Since: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> \<psi> \<Longrightarrow> S, E \<turnstile> Formula.Since \<phi> \<I> \<psi>" 
| Until: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> \<psi> \<Longrightarrow> S, E \<turnstile> Formula.Until \<phi> \<I> \<psi>" 
| MatchP: "Regex.pred_regex (\<lambda>\<phi>. S, E \<turnstile> \<phi>) r \<Longrightarrow> S, E \<turnstile> Formula.MatchP I r"
| MatchF: "Regex.pred_regex (\<lambda>\<phi>. S, E \<turnstile> \<phi>) r \<Longrightarrow> S, E \<turnstile> Formula.MatchF I r"

lemma wty_formula_fv_cong:
  assumes "\<And>y. y \<in> fv \<phi> \<Longrightarrow> E y = E' y"
  shows "S, E \<turnstile> \<phi> \<longleftrightarrow> S, E' \<turnstile> \<phi>"
proof -
  have "S, E \<turnstile> \<phi> \<Longrightarrow> (\<And>y. y \<in> fv \<phi> \<Longrightarrow> E y = E' y) \<Longrightarrow> S, E' \<turnstile> \<phi>" for E E'
  proof (induction arbitrary: E' pred: wty_formula)
    case (Pred S p tys E tms)
    then show ?case
      by (fastforce intro!: wty_formula.Pred
          elim!: list.rel_mono_strong wty_trm_fv_cong[THEN iffD1, rotated])
  next 
    case(Let S E'' \<phi>  p E  \<psi>)
    then show ?case
      using fvi.simps(2) wty_formula.Let by blast
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
    from this show ?case  by (metis  wty_formula.Ands fv_subset_Ands subset_eq)
  next
    case (Exists S t E \<phi>)
    then show ?case
      by (fastforce simp: fvi_Suc intro!: wty_formula.Exists[where t=t] split: nat.split)
 (* next 
    case (Sum E s t tys x S \<phi> d E')
    let ?\<psi> = "(formula.Agg s (agg_type.Agg_Sum, d) tys x \<phi>)"
    from Sum.prems Sum.hyps(1) have part1: "E' s = t" by auto
    from Sum have  "\<forall>y\<in> Formula.fvi_trm (length tys) x. E y = E' y" by auto
    from this have "\<forall>y\<in> Formula.fvi_trm 0 x. y\<ge> length tys \<longrightarrow>  E (y - length tys)  = E' (y - length tys) " by (meson fvi_trm_iff_fv_trm fvi_trm_minus fvi_trm_plus)
    from this have "\<forall>y\<in>fv_trm x. (\<lambda>z. if z < length tys then tys ! z else E (z - length tys)) y =
                (\<lambda>z. if z < length tys then tys ! z else E' (z - length tys)) y " by auto
    from this Sum.hyps(2) have part2: "(\<lambda>z. if z < length tys then tys ! z else E' (z - length tys)) \<turnstile> x :: t" using wty_trm_fv_cong by fastforce
    
    from Sum have  "\<forall>y\<in> Formula.fvi (length tys) \<phi>. E y = E' y" by auto
    from this have "\<forall>y\<in> Formula.fvi 0 \<phi>. y\<ge> length tys \<longrightarrow>  (E (y - length tys)  = E' (y - length tys))" using fvi_minus[where b=0] by auto
    from this Sum.hyps(2) Sum.IH have part3: "S,(\<lambda>z. if z < length tys then tys ! z else E' (z - length tys)) \<turnstile> \<phi>" by simp
    from part1 part2 part3 Sum.hyps(4) show ?case by (simp add:  wty_formula.Sum)
*)
  next
    case (Agg E s agg_type t tys f S \<phi> d) (* TODO *)
    have ?case sorry
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
  qed 
  with assms show ?thesis by auto
qed

lemma ty_of_sat_safe: "safe_formula \<phi> \<Longrightarrow> S, E \<turnstile> \<phi> \<Longrightarrow> wty_envs S \<sigma> V \<Longrightarrow> 
  Formula.sat \<sigma> V v i \<phi> \<Longrightarrow> x \<in> Formula.fv \<phi> \<Longrightarrow> Formula.nfv \<phi> \<le> length v \<Longrightarrow> ty_of (v ! x) = E x"
proof (induction arbitrary: S E V v i x rule: safe_formula_induct)
  case (Eq_Const c d)
  then show ?case by auto
next
  case (Eq_Var1 c xa)
  from Eq_Var1.prems(1) obtain t where 
" E \<turnstile> (trm.Const c) :: t" and "E \<turnstile> (trm.Var xa) :: t"
    by cases
  from Eq_Var1(4)  have "x = xa" by auto
  from this `E \<turnstile> (trm.Var xa) :: t` have "E x = t" using  wty_trm.cases by fastforce
  from this Eq_Var1 ` E \<turnstile> (trm.Const c) :: t` show ?case 
    by (metis \<open>x = xa\<close> empty_iff eval_trm.simps(1) fvi_trm.simps(2) sat.simps(3) ty_of_eval_trm)

next
  case (Eq_Var2 c xa)
    from Eq_Var2.prems(1) obtain t where 
" E \<turnstile> (trm.Const c) :: t" and "E \<turnstile> (trm.Var xa) :: t"
    by cases
  from Eq_Var2(4)  have "x = xa" by auto
  from this `E \<turnstile> (trm.Var xa) :: t` have "E x = t" using  wty_trm.cases by fastforce
  from this Eq_Var2 ` E \<turnstile> (trm.Const c) :: t` show ?case
    by (metis \<open>x = xa\<close> empty_iff eval_trm.simps(1) fvi_trm.simps(2) sat.simps(3) ty_of_eval_trm)
  
next
  case (neq_Var xa)
  thus ?case by auto
next
  case (Pred p tms)
  from Pred.prems(1) obtain tys where
    S_p: "S p = Some tys" and
    xs_ts: "list_all2 (\<lambda>tm ty. E \<turnstile> tm :: ty) tms tys"
    by cases
  let ?xs = "map (Formula.eval_trm v) tms"
  have wty_xs: "wty_tuple tys ?xs"
  proof (cases "p \<in> dom V")
    case True
    then have "?xs \<in> the (V p) i"
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
  let ?V' = "V(p \<mapsto> \<lambda>i. {v. length v = Formula.nfv \<phi> \<and> Formula.sat \<sigma> V v i \<phi>})"
  from Let.prems(1) obtain E' where
    wty_\<phi>: "S, E' \<turnstile> \<phi>" and
    wty_\<psi>: "S(p \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E \<turnstile> \<psi>"
    by (cases pred: wty_formula)
  let ?tys = "tabulate E' 0 (Formula.nfv \<phi>)"
  {
    fix v' i
    assume "length v' = Formula.nfv \<phi>" and "Formula.sat \<sigma> V v' i \<phi>"
    then have "wty_tuple ?tys v'"
      using Let.IH(1) wty_\<phi> Let.prems(2) Let.hyps(1)
      by (auto simp: wty_tuple_def list_all2_conv_all_nth)
  }
  with Let.prems(2) have "wty_envs (S(p \<mapsto> ?tys)) \<sigma> ?V'"
    by (auto simp: wty_envs_def wty_event_def)
  from Let.prems(3) have "Formula.sat \<sigma> ?V' v i \<psi>" by simp
  from Let.prems(4) have "x \<in> fv \<psi>" by simp
  from Let have "Formula.nfv \<psi> \<le> length v" by auto
  show ?case by (rule Let.IH(2)) fact+
next
  case (And_assign \<phi> \<psi>)
  from And_assign.prems(1) have phi1: "S, E \<turnstile> \<phi>" by cases
  from And_assign.prems(3) have phi2: "Formula.sat \<sigma> V v i \<psi>" by auto
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
      have eval:" v! x = Formula.eval_trm v b" using And_assign(6) a_def \<psi>_eq by auto
      have Ebx: "E \<turnstile> b :: E  x"  using And_assign(4) by (auto simp: \<psi>_eq a_def elim: wty_trm.cases wty_formula.cases)
      have "(\<lambda>y. ty_of (v ! y)) \<turnstile> b :: E x" apply (rule  iffD1[OF wty_trm_fv_cong,OF _ Ebx]) apply (subst eq_commute) 
        apply (rule And_assign(3)) using And_assign fvb by (auto elim: wty_formula.cases) 
      then have ?case using ty_of_eval_trm unfolding eval
        using And_assign(4) by (auto simp: \<psi>_eq a_def elim: wty_formula.cases)
    }
    moreover {
     assume a_def: "b = Formula.Var x"
      from this  x_not_\<phi> have fvb: "fv_trm a \<subseteq> fv \<phi>" using And_assign(2) by  (auto simp: safe_assignment_def \<psi>_eq split: trm.splits) 
      have eval:" v! x = Formula.eval_trm v a" using And_assign(6) a_def \<psi>_eq by auto
      have Ebx: "E \<turnstile> a :: E  x"  using And_assign(4) by (auto simp: \<psi>_eq a_def elim: wty_trm.cases wty_formula.cases)
      have "(\<lambda>y. ty_of (v ! y)) \<turnstile> a :: E x" apply (rule  iffD1[OF wty_trm_fv_cong,OF _ Ebx]) apply (subst eq_commute) 
        apply (rule And_assign(3)) using And_assign fvb by (auto elim: wty_formula.cases) 
      then have ?case using ty_of_eval_trm unfolding eval
        using And_assign(4) by (auto simp: \<psi>_eq a_def elim: wty_formula.cases)
    }
    moreover
      have "a = Formula.Var x \<or> b = Formula.Var x" using And_assign(2) And_assign(7) x_not_\<phi> by (auto simp: \<psi>_eq safe_assignment_def split: Formula.trm.splits) 
    ultimately show ?case by auto
qed
 next
  case (And_safe \<phi> \<psi>)
  from And_safe.prems(1) obtain "S, E \<turnstile> \<phi>" and "S, E \<turnstile> \<psi>" by cases
  from And_safe.prems(3) have "Formula.sat \<sigma> V v i \<phi>" and "Formula.sat \<sigma> V v i \<psi>"
    by simp_all
  from And_safe.prems(4) consider (in_\<phi>) "x \<in> fv \<phi>" | (in_\<psi>) "x \<in> fv \<psi>" by auto
  then show ?case
  proof cases
    case in_\<phi>
  from And_safe have "Formula.nfv \<phi> \<le> length v" by auto
    show ?thesis by (rule And_safe.IH(1)) fact+
  next
    case in_\<psi>
  from And_safe have "Formula.nfv \<psi> \<le> length v" by auto
    show ?thesis by (rule And_safe.IH(2)) fact+
  qed
next
  case (And_constraint \<phi> \<psi>) (* TODO *)
  from \<open>is_constraint \<psi>\<close> show ?case
    by (cases \<psi> rule: is_constraint.cases)
      (use And_constraint.prems(1) in "auto elim: wty_formula.cases")
next
  case (And_Not \<phi> \<psi>)
  then show ?case by (blast elim: wty_formula.cases) (* TODO *)
next
  case (Ands l pos neg)
  from Ands.prems(1) show ?case by cases (* TODO *)
next
  case (Neg \<phi>)
  from Neg.prems(1) show ?case by cases (* TODO *)
next
  case (Or \<phi> \<psi>)
  from Or.prems(1) show ?case by cases (* TODO *)
next
  case (Exists \<phi>)
  from Exists.prems(1) obtain t where "S, case_nat t E \<turnstile> \<phi>" by cases
  from Exists.prems(3) obtain z where "Formula.sat \<sigma> V (z#v) i \<phi>" by auto
  from Exists.prems(4) have "Suc x \<in> fv \<phi>" by (simp add: fvi_Suc)
  from Exists have "Formula.nfv \<phi> \<le> Suc (length v)" apply (auto simp add: Formula.nfv_def)
    by (metis fvi_Suc le0 old.nat.exhaust)

  have "ty_of ((z#v) ! Suc x) = case_nat t E (Suc x)"
    by (rule Exists.IH) (simp?, fact)+
  then show ?case by simp
next
  case (Agg y \<omega> b f \<phi>)
  from Agg.prems(1) show ?case by cases (* TODO *)
next
  case (Prev I \<phi>)
  from Prev.prems(1) show ?case by cases (* TODO *)
next
  case (Next I \<phi>)
  from Next.prems(1) show ?case by cases (* TODO *)
next
  case (Since \<phi> I \<psi>)
  from Since.prems(1) show ?case by cases (* TODO *)
next
  case (Not_Since \<phi> I \<psi>)
  from Not_Since.prems(1) show ?case by cases (* TODO *)
next
  case (Until \<phi> I \<psi>)
  from Until.prems(1) show ?case by cases (* TODO *)
next
  case (Not_Until \<phi> I \<psi>)
  from Not_Until.prems(1) show ?case by cases (* TODO *)
next
  case (MatchP I r)
  from MatchP.prems(1) show ?case by cases (* TODO *)
next
  case (MatchF I r)
  from MatchF.prems(1) show ?case by cases (* TODO *)
qed

(*<*)
end
(*>*)
