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
| Agg: " E y =  t_res agg_type t \<Longrightarrow> agg_env E tys  \<turnstile> f :: t \<Longrightarrow> S, agg_env E tys \<turnstile> \<phi>  \<Longrightarrow>
   t \<in> agg_trm_type agg_type \<Longrightarrow> ty_of d = t_res agg_type t \<Longrightarrow>
          S, E \<turnstile> Formula.Agg y (agg_type, d) tys f \<phi>"
| Prev: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> Formula.Prev \<I> \<phi>"
| Next: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> Formula.Next \<I> \<phi>"
| Since: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> \<psi> \<Longrightarrow> S, E \<turnstile> Formula.Since \<phi> \<I> \<psi>" 
| Until: "S, E \<turnstile> \<phi> \<Longrightarrow> S, E \<turnstile> \<psi> \<Longrightarrow> S, E \<turnstile> Formula.Until \<phi> \<I> \<psi>" 
| MatchP: "Regex.pred_regex (\<lambda>\<phi>. S, E \<turnstile> \<phi>) r \<Longrightarrow> S, E \<turnstile> Formula.MatchP I r"
| MatchF: "Regex.pred_regex (\<lambda>\<phi>. S, E \<turnstile> \<phi>) r \<Longrightarrow> S, E \<turnstile> Formula.MatchF I r"

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


fun eval_agg_op' :: "Formula.agg_op \<Rightarrow> (event_data \<times> enat) set \<Rightarrow> event_data" where
  "eval_agg_op' (agg_type.Agg_Cnt, y0) M = (case (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (xs,_) \<Rightarrow> EInt (integer_of_int (length xs)))"
| "eval_agg_op' (agg_type.Agg_Min, y0) M = (case  (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (x # xs,_) \<Rightarrow> foldl undef_min x xs)"
| "eval_agg_op' (agg_type.Agg_Max, y0) M = (case  (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (x # xs,_) \<Rightarrow> foldl undef_max x xs)"
| "eval_agg_op' (agg_type.Agg_Sum, y0) M = (case  (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (x # xs,_) \<Rightarrow> foldl undef_plus x xs)"
| "eval_agg_op' (agg_type.Agg_Avg, y0) M =(case  (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (x#xs,_) \<Rightarrow> EFloat ( undef_double_of_event_data_agg (foldl undef_plus x xs) / double_of_int (length (x#xs))))"
| "eval_agg_op' (agg_type.Agg_Med, y0) M =(case (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (xs,_) \<Rightarrow> EFloat (let u = length xs;  u' = u div 2 in
          if even u then
            (undef_double_of_event_data_agg (xs ! (u'-1)) + undef_double_of_event_data_agg (xs ! u') / double_of_int 2)
          else undef_double_of_event_data_agg (xs ! u')))"

fun sat' :: "Formula.trace \<Rightarrow> (Formula.name \<rightharpoonup> nat \<Rightarrow> event_data list set) \<Rightarrow> Formula.env \<Rightarrow> nat \<Rightarrow> 't Formula.formula \<Rightarrow> bool" where
  "sat' \<sigma> V v i (Formula.Pred r ts) = (case V r of
       None \<Rightarrow> (r, map (eval_trm' v) ts) \<in> \<Gamma> \<sigma> i
     | Some X \<Rightarrow> map (eval_trm' v) ts \<in> X i)"
| "sat' \<sigma> V v i (Formula.Let p \<phi> \<psi>) =
    sat' \<sigma> (V(p \<mapsto> \<lambda>i. {v. length v = Formula.nfv \<phi> \<and> sat' \<sigma> V v i \<phi>})) v i \<psi>"
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
   " Formula.nfv (formula.MatchF I r) \<le> length v \<or>  Formula.nfv (formula.MatchP I r) \<le> length v"
  shows "S, E \<turnstile> \<phi>" "Formula.nfv \<phi> \<le> length v"
proof -
 have "\<forall>a \<in> fv \<phi>. a \<in> fv_regex r" using   assms(1)  apply (induction r) apply auto 
      subgoal for \<psi>  apply (cases "safe_formula \<psi>") apply (auto elim: safe_formula.cases) by (cases \<psi>) auto 
      done
    from this assms(4) show  "Formula.nfv \<phi> \<le> length v" by (auto simp add: Formula.nfv_def) 
  next
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



lemma ty_of_sat'_safe: "safe_formula \<phi> \<Longrightarrow> S, E \<turnstile> \<phi> \<Longrightarrow> wty_envs S \<sigma> V \<Longrightarrow> 
  sat' \<sigma> V v i \<phi> \<Longrightarrow> x \<in> Formula.fv \<phi> \<Longrightarrow> Formula.nfv \<phi> \<le> length v \<Longrightarrow> ty_of (v ! x) = E x"
proof (induction arbitrary: S E V v i x rule: safe_formula_induct)
  case (Eq_Const c d)
  then show ?case by auto
next
  case (Eq_Var1 c xa)
   case (Eq_Var1 c xa)
  from Eq_Var1.prems(1) obtain t where 
" E \<turnstile> (trm.Const c) :: t" and "E \<turnstile> (trm.Var xa) :: t"
    by cases
  from Eq_Var1(4)  have "x = xa" by auto
  from this `E \<turnstile> (trm.Var xa) :: t` have "E x = t" using  wty_trm.cases by fastforce
  from this Eq_Var1 ` E \<turnstile> (trm.Const c) :: t` show ?case
    by (metis \<open>x = xa\<close> empty_iff eval_trm'.simps(1) fvi_trm.simps(2) sat'.simps(3) eval_trm_sound ty_of_eval_trm)

next
  case (Eq_Var2 c xa)
    from Eq_Var2.prems(1) obtain t where 
" E \<turnstile> (trm.Const c) :: t" and "E \<turnstile> (trm.Var xa) :: t"
    by cases
  from Eq_Var2(4)  have "x = xa" by auto
  from this `E \<turnstile> (trm.Var xa) :: t` have "E x = t" using  wty_trm.cases by fastforce
  from this Eq_Var2 ` E \<turnstile> (trm.Const c) :: t` show ?case
    by (metis \<open>x = xa\<close> empty_iff eval_trm'.simps(1) fvi_trm.simps(2) sat'.simps(3) eval_trm_sound ty_of_eval_trm)
next
  case (Pred p tms)
  from Pred.prems(1) obtain tys where
    S_p: "S p = Some tys" and
    xs_ts: "list_all2 (\<lambda>tm ty. E \<turnstile> tm :: ty) tms tys"
    by cases
  let ?xs = "map (eval_trm' v) tms"
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
  let ?V' = "V(p \<mapsto> \<lambda>i. {v. length v = Formula.nfv \<phi> \<and> sat' \<sigma> V v i \<phi>})"
  from Let.prems(1) obtain E' where
    wty_\<phi>: "S, E' \<turnstile> \<phi>" and
    wty_\<psi>: "S(p \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E \<turnstile> \<psi>"
    by (cases pred: wty_formula)
  let ?tys = "tabulate E' 0 (Formula.nfv \<phi>)"
  {
    fix v' i
    assume "length v' = Formula.nfv \<phi>" and "sat' \<sigma> V v' i \<phi>"
    then have "wty_tuple ?tys v'"
      using Let.IH(1) wty_\<phi> Let.prems(2) Let.hyps(1)
      by (auto simp: wty_tuple_def list_all2_conv_all_nth)
  }
  with Let.prems(2) have "wty_envs (S(p \<mapsto> ?tys)) \<sigma> ?V'"
    by (auto simp: wty_envs_def wty_event_def)
  from Let.prems(3) have "sat' \<sigma> ?V' v i \<psi>" by simp
  from Let.prems(4) have "x \<in> fv \<psi>" by simp
  from Let have "Formula.nfv \<psi> \<le> length v" by auto
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
  from And_safe have "Formula.nfv \<phi> \<le> length v" by auto
    show ?thesis by (rule And_safe.IH(1)) fact+
  next
    case in_\<psi>
  from And_safe have "Formula.nfv \<psi> \<le> length v" by auto
    show ?thesis by (rule And_safe.IH(2)) fact+
  qed
next
  case (And_constraint \<phi> \<psi>)
  have xfree: "x \<in> fv \<phi>" using And_constraint(4) And_constraint(10) by auto
  from And_constraint(7) have "S, E \<turnstile> \<phi>" by cases
  from this xfree And_constraint(6,8-9,11) show ?case by auto
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
    sat' \<sigma> V v i \<phi> \<Longrightarrow> x \<in> fv \<phi> \<Longrightarrow> Formula.nfv \<phi> \<le> length v \<Longrightarrow> ty_of (v ! x) = E x"
        using list_all2_iff by (smt (verit, ccfv_SIG) Ball_set_list_all)
      from Ands.prems(1) have  "\<forall>\<phi> \<in> set l. S, E \<turnstile> \<phi>" by cases
      from this phi_in_l have p1: "S, E \<turnstile> \<phi>"  by auto
      from phi_in_l Ands.prems(3) have p3: "sat' \<sigma> V v i \<phi>" by auto
      from phi_in_l Ands have p5: "Formula.nfv \<phi> \<le> length v" by auto
  from  phi_IH p1 Ands.prems(2) p3 phidef p5  show ?case by auto
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
  from this assm Or.prems(2,3) Or(4) Or.prems(5) xfv show ?case by auto
next 
  assume assm: "( sat' \<sigma> V v i \<psi>)"
 from Or(1) Or.prems(4) have xfv: "x \<in> fv \<psi>" by auto
  from Or.prems(1) have "S, E \<turnstile> \<psi>" by cases
  from this assm Or.prems(2,3) Or(5) Or.prems(5) xfv show ?case by auto
qed
next
  case (Exists \<phi>)
  from Exists.prems(1) obtain t where "S, case_nat t E \<turnstile> \<phi>" by cases
  from Exists.prems(3) obtain z where "sat' \<sigma> V (z#v) i \<phi>" by auto
  from Exists.prems(4) have "Suc x \<in> fv \<phi>" by (simp add: fvi_Suc)
  from Exists have "Formula.nfv \<phi> \<le> Suc (length v)" apply (auto simp add: Formula.nfv_def)
    by (metis fvi_Suc le0 old.nat.exhaust)

  have "ty_of ((z#v) ! Suc x) = case_nat t E (Suc x)"
    by (rule Exists.IH) (simp?, fact)+
  then show ?case by simp
next
  case (Agg y \<omega> tys f \<phi>)
 have "\<forall>z \<in>Formula.fvi (length tys) \<phi>. Suc z \<le> length v " using Agg.prems(5) by (auto simp add: Formula.nfv_def)
    from this have "\<forall>z \<in>Formula.fv \<phi>. Suc z - length tys \<le> length v "  using  fvi_iff_fv  nat_le_linear 
      by (metis Suc_diff_le diff_add diff_is_0_eq' diff_zero not_less_eq_eq) 
    from this have nfv_tys_v: "Formula.nfv \<phi> \<le> length tys + length v" by (auto simp add: Formula.nfv_def)

  have case_split:" x \<in> Formula.fvi (length tys) \<phi> \<or> x \<in> Formula.fvi_trm (length tys) f \<or> x = y" using Agg.prems(4) by auto
 
  moreover {
    assume asm: "x \<in> Formula.fvi (length tys) \<phi>"
    from this have "\<not> fv \<phi> \<subseteq> {0..< length tys}" using fvi_iff_fv[of x "length tys" \<phi>] by auto
    from this have M: "{(x, ecard Zs) | 
  x Zs. Zs = {zs. length zs = length tys \<and> sat' \<sigma> V (zs @ v) i \<phi> \<and> eval_trm' (zs @ v) f = x} \<and> Zs \<noteq> {}} \<noteq> {}" using Agg.prems(3) by auto
    from this obtain zs where sat: "sat' \<sigma> V (zs @ v) i \<phi> \<and> length zs = length tys" by auto
    from nfv_tys_v have nfv: "Formula.nfv \<phi> \<le> length (zs @ v)"  by (auto simp add: sat)
    have "ty_of ((zs@v) ! (x + length tys)) = agg_env E tys (x + length tys)"
      apply (rule Agg.IH[of \<phi> S "agg_env E tys" V "zs @ v" i "x+ length tys"]) using Agg.prems(1) Agg(4) sat asm nfv Agg.prems(1-2) fvi_iff_fv
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
 ty_of_d: "ty_of d = t_res agg_type t" apply cases using eq omega_def t_def by auto
    from Agg.prems(3) eq obtain M where  M_def: "M = {(x, ecard Zs) | x Zs. Zs = {zs. length zs = length tys \<and> sat' \<sigma> V (zs @ v) i \<phi>
        \<and> eval_trm' (zs @ v) f = x} \<and> Zs \<noteq> {}} \<and> v!x = eval_agg_op' \<omega> M" by auto
   
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
          show "ty_of ((zs @ v) ! y) = agg_env E tys y" using zs_def assm Agg(3,4) Agg.prems(1-2) nfv_tys_v sat  Agg.IH[of \<phi> S "agg_env E tys" V "zs@v" i y]
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
          from  finite_M th2  M_def t_def omega_def  have ?case apply (cases agg_type) 
            by (auto simp add: ty_of_d split: list.splits)        
        }
        moreover{
             assume not_finite: "\<not> finite_multiset M"
         from this t_def  M_def  omega_def have  ?case apply (cases agg_type)
                by ( auto simp add: ty_of_d split: list.splits) 
         }
         ultimately have ?case by auto 
     
  } 
  ultimately show ?case by auto
next
  
  case (Prev I \<phi>)
   from Prev.prems(1) have wty: "S, E \<turnstile> \<phi>" by cases
  from Prev.prems(3) have forall_j: "\<forall>j . i = Suc j \<longrightarrow> sat' \<sigma> V v j \<phi>" by auto
  from this have "sat' \<sigma> V v (Nat.pred i) \<phi>" using Prev.prems by (auto split: nat.splits)
  from this wty Prev.prems(2-5) Prev.IH show ?case by auto
next
  case (Next I \<phi>)
  from Next.prems(1,2-5) Next.IH show ?case by (auto elim: wty_formula.cases)
next
  case (Since \<phi> I \<psi>)
  from Since(1,9) have xfv: "x \<in> fv \<psi>" by auto
  from this  Since.prems(1,2-5) Since.IH show ?case by (auto elim: wty_formula.cases)
next
  case (Not_Since \<phi> I \<psi>)
  from Not_Since.prems(1) have wty: "S, E \<turnstile> \<psi>" by cases
  from Not_Since(1,10) have xfv: "x \<in> fv \<psi>" by auto
  from this wty Not_Since.prems(2-5) Not_Since.IH show ?case by auto
next
  case (Until \<phi> I \<psi>)
  from Until(1,9) have xfv: "x \<in> fv \<psi>" by auto
  from this  Until.prems(1,2-5) Until.IH show ?case by (auto elim: wty_formula.cases)
next
  case (Not_Until \<phi> I \<psi>)
 from Not_Until.prems(1) have wty: "S, E \<turnstile> \<psi>" by cases
  from Not_Until(1,10) have xfv: "x \<in> fv \<psi>" by auto
  from this wty Not_Until.prems(2-5) Not_Until.IH show ?case by auto
next
  case (MatchP I r)
  from MatchP.prems(3) have "(\<exists>j. Regex.match (sat' \<sigma> V v) r j i)" by auto
    from this  MatchP(1)  MatchP.prems(4) obtain \<phi> j where phidef: " \<phi> \<in> atms r" " sat' \<sigma> V v j \<phi>" "x \<in> fv \<phi> " using match_sat'_fv  by auto blast
    from   MatchP.prems(1) MatchP(1)  MatchP.prems(5) phidef(1)  have wty: "S, E \<turnstile> \<phi>" and  nfv:"Formula.nfv \<phi> \<le> length v" 
      using  match_safe_wty_nfv[of \<phi> r I S E v] by auto
    from MatchP.IH MatchP.prems have IH: "S, E \<turnstile> \<phi> \<Longrightarrow>\<phi> \<in> atms r \<Longrightarrow>
     sat' \<sigma> V v j \<phi> \<Longrightarrow> x \<in> fv \<phi> \<Longrightarrow> Formula.nfv \<phi> \<le> length v \<Longrightarrow> ty_of (v ! x ) = E x"
    for \<phi> E  v  x by blast
   show ?case apply (rule IH) using wty nfv  MatchP.prems(5) phidef by auto
 
next
  case (MatchF I r)
 from MatchF.prems(3) have "(\<exists>j. Regex.match (sat' \<sigma> V v) r  i j)" by auto
    from this  MatchF(1)  MatchF.prems(4) obtain \<phi> j where phidef: " \<phi> \<in> atms r" " sat' \<sigma> V v j \<phi>" "x \<in> fv \<phi> " using match_sat'_fv  by auto blast
    from   MatchF.prems(1) MatchF(1)  MatchF.prems(5) phidef(1)  have wty: "S, E \<turnstile> \<phi>" and  nfv:"Formula.nfv \<phi> \<le> length v" 
      using  match_safe_wty_nfv[of \<phi> r I S E v] by auto
    from MatchF.IH MatchF.prems have IH: "S, E \<turnstile> \<phi> \<Longrightarrow>\<phi> \<in> atms r \<Longrightarrow>
     sat' \<sigma> V v j \<phi> \<Longrightarrow> x \<in> fv \<phi> \<Longrightarrow> Formula.nfv \<phi> \<le> length v \<Longrightarrow> ty_of (v ! x ) = E x"
    for \<phi> E  v  x by blast
   show ?case apply (rule IH) using wty nfv  MatchF.prems(5)  phidef by auto

qed

end

interpretation  sat_inst: sat_general "(+)" "(-)" "uminus" "(*)" "(div)" "(mod)" "Event_Data.double_of_event_data" "Event_Data.double_of_event_data_agg" "Event_Data.integer_of_event_data" "(\<le>)"
  by unfold_locales  auto

lemma eval_trm_inst: " sat_inst.eval_trm'  = Formula.eval_trm "
proof -
  have  "sat_inst.eval_trm' v f = Formula.eval_trm v f" for v f
  by (induction f)  auto 
  then show ?thesis  by auto
qed 

lemma eval_agg_op_inst: " sat_inst.eval_agg_op' (\<omega>, d) M  = Formula.eval_agg_op (\<omega>, d) M"
  apply (cases \<omega>)   apply (auto ) apply (induction "flatten_multiset M")  apply (cases \<omega>) apply (auto simp add:  split: list.splits) 
  apply (smt (verit) foldl_cong min_def sat_inst.undef_min_def sat_inst.undef_min_def) 
  by (smt (verit) foldl_cong max_def sat_inst.undef_max_def) 
  

lemma sat_inst_of_sat': "Formula.sat \<sigma> V v i \<phi> = sat_inst.sat' \<sigma> V v i \<phi>"
 apply (induction \<phi> arbitrary: v V i)  apply  (auto simp add: eval_trm_inst less_event_data_def sat_inst.undef_less_def  split: nat.splits)
  using eval_trm_inst apply presburger
                      apply (metis eval_trm_inst) 
  using eval_agg_op_inst apply presburger+  by  (metis match_cong_strong)+


lemma ty_of_sat_safe: "safe_formula \<phi> \<Longrightarrow> S, E \<turnstile> \<phi> \<Longrightarrow> wty_envs S \<sigma> V \<Longrightarrow> 
  Formula.sat \<sigma> V v i \<phi> \<Longrightarrow> x \<in> Formula.fv \<phi> \<Longrightarrow> Formula.nfv \<phi> \<le> length v \<Longrightarrow> ty_of (v ! x) = E x"
  using  sat_inst.sat_general_axioms sat_inst_of_sat'
    sat_general.ty_of_sat'_safe[of  "(+)" "(-)" "uminus" "(*)" "(div)" "(mod)" double_of_event_data double_of_event_data_agg integer_of_event_data "(\<le>)"]  
  by auto  blast

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
      subgoal for \<phi>' x
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
  case (Neg \<phi>)
  then show ?case
    by (cases \<psi>) (auto simp: rel_formula_fv)
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
qed

lemma rel_regex_regex_atms: "Regex.rel_regex f r r' \<Longrightarrow> x \<in> Regex.atms r \<Longrightarrow> \<exists>x' \<in> Regex.atms r'. f x x'"
  by (induction r r' rule: regex.rel_induct) auto

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
    "S(p \<mapsto> tabulate F 0 (Formula.nfv \<phi>)), E \<turnstile> \<phi>'"
    using Let(6)
    by (auto elim: wty_formula.cases)
  obtain F' where F'_def: "S, F' \<turnstile> \<psi>"
    "S(p \<mapsto> tabulate F' 0 (Formula.nfv \<psi>)), E' \<turnstile> \<psi>'"
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
  case (Exists \<phi> t)
  then show ?case
    by (fastforce simp: fvi_Suc elim!: wty_formula.cases[of S E "Formula.Exists t \<phi>"] wty_formula.cases[of S E' \<phi>'])
next
  case (Agg y \<omega> tys trm \<phi> S E E' \<psi>)
  obtain agg_type d where \<omega>_def: "\<omega> = (agg_type, d)"
    by fastforce
  obtain t where wty_\<phi>: "S, agg_env E tys \<turnstile> \<phi>" "E y = t_res agg_type t" "agg_env E tys \<turnstile> trm :: t"
    using Agg
    by (auto simp: \<omega>_def elim!: wty_formula.cases[of S E "formula.Agg y (agg_type, d) tys trm \<phi>"])
  obtain tys' \<phi>' where \<psi>_def: "\<psi> = formula.Agg y \<omega> tys' trm \<phi>'"
    "formula.rel_formula f \<phi> \<phi>'" "list_all2 f tys tys'"
    using Agg(8)
    by (cases \<psi>) auto
  have tys_tys': "length tys = length tys'"
    using \<psi>_def(3)
    by (auto simp: list_all2_lengthD)
  obtain t' where wty_\<phi>': "S, agg_env E' tys' \<turnstile> \<phi>'" "E' y = t_res agg_type t'" "agg_env E' tys' \<turnstile> trm :: t'"
    using Agg(7)
    by (auto simp: \<psi>_def(1) \<omega>_def elim!: wty_formula.cases[of S E' "formula.Agg y (agg_type, d) tys' trm \<phi>'"])
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
qed auto

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
    "S(p \<mapsto> tabulate F 0 (Formula.nfv \<phi>)), E \<turnstile> \<phi>'"
    using Let(6)
    by (auto elim: wty_formula.cases)
  obtain F' where F'_def: "S, F' \<turnstile> \<psi>"
    "S(p \<mapsto> tabulate F' 0 (Formula.nfv \<psi>)), E' \<turnstile> \<psi>'"
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
  obtain tys' \<phi>' where \<psi>_def: "\<psi> = formula.Agg y \<omega> tys' trm \<phi>'" "list_all2 f tys tys'"
    using Agg
    by (cases \<psi>) auto
  have "agg_env E tys x = agg_env E' tys' x" if "x \<in> fv \<phi>" for x
    using Agg rel_formula_wty_unique_fv[of \<phi> S "agg_env E tys" "agg_env E' tys'" \<phi>' f] that
    by (auto simp: \<psi>_def(1) elim!: wty_formula.cases[of _ _ "formula.Agg _ _ _ _ _"])
  then have "list_all2 (=) tys tys'"
    using Agg(2) \<psi>_def(2)
    by (fastforce simp: list_all2_conv_all_nth agg_env_def)
  then show ?case
    using Agg
    by (auto simp: \<psi>_def(1) elim!: wty_formula.cases[of _ _ "formula.Agg _ _ _ _ _"])
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
qed

lemma list_all2_eq: "list_all2 (=) xs ys \<Longrightarrow> xs = ys"
  by (induction xs ys rule: list.rel_induct) auto

lemma rel_regex_eq: "regex.rel_regex (=) r r' \<Longrightarrow> r = r'"
  by (induction r r' rule: regex.rel_induct) auto

lemma rel_formula_eq: "Formula.rel_formula (=) \<phi> \<phi>' \<Longrightarrow> \<phi> = \<phi>'"
  by (induction \<phi> \<phi>' rule: formula.rel_induct) (auto simp: list_all2_eq rel_regex_eq)

lemma rel_formula_wty_unique_bv: "safe_formula \<phi> \<Longrightarrow> wty_formula S E \<phi> \<Longrightarrow> wty_formula S E' \<phi>' \<Longrightarrow>
  Formula.rel_formula f \<phi> \<phi>' \<Longrightarrow> \<phi> = \<phi>'"
  using rel_formula_wty_unique_bv_aux
  by (auto simp: rel_formula_eq)


datatype tysym = TAny nat | TNum nat | TCst ty
                                 
type_synonym tysenv = "nat \<Rightarrow> tysym"

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

fun min_type :: "tysym \<Rightarrow> tysym \<Rightarrow> (tysym \<times> tysym) option" where
"min_type (TNum a) (TNum b)  = Some (if a \<le> b then (TNum a, TNum b) else (TNum b, TNum a) )"
| "min_type (TAny a) (TAny b)  = Some (if a \<le> b then (TAny a, TAny b) else (TAny b, TAny a) )"
| "min_type ( x) (TAny y) = Some ( x, TAny y)"
| "min_type (TAny y) x= Some ( x, TAny y)"
| "min_type (TCst TString) (TNum _) = None"
| "min_type  (TNum _) (TCst TString) = None"
| "min_type (TCst x) (TNum y) = Some (TCst x, TNum y)"
| "min_type  (TNum y) (TCst x)= Some (TCst x, TNum y)"
| "min_type (TCst x) (TCst y) = (if x = y then Some (TCst x, TCst y) else None)"



lemma min_comm: "min_type a b =  min_type b a"
  by (induction a b rule: min_type.induct)  auto

lemma min_consistent: assumes "min_type a b = Some(x,y)" shows "x = a \<and> y=b \<or> x = b \<and> y = a"
  using assms by (induction a b rule: min_type.induct) (auto split: if_splits)

lemma min_const: assumes "min_type (TCst x) y = Some(a,b)" shows "a = TCst x"
  using assms by (induction "TCst x" y rule: min_type.induct) (auto split: if_splits)

definition propagate_constraints :: "tysym \<Rightarrow> tysym \<Rightarrow> tysenv \<Rightarrow> tysenv" where
"propagate_constraints t1 t2 E = (let (told,tnew) = if tyless t1 t2 then (t2,t1) else (t1,t2) in (\<lambda>v. if E v = told then tnew else E v) )"

definition update_env :: "tysym \<times> tysym \<Rightarrow> tysenv \<Rightarrow> tysenv" where
"update_env x E \<equiv> case x of (tnew,told) \<Rightarrow>(\<lambda>v. if E v = told then tnew else E v) "

(* takes two types as input, checks if there's no clash, returns updated env and the more specific type*)
definition clash_propagate :: "tysym \<Rightarrow> tysym \<Rightarrow> tysenv \<Rightarrow> (tysenv*tysym) option" where
"clash_propagate t1 t2 E = (case min_type t1 t2 of Some (newt,oldt) \<Rightarrow> Some ((update_env (newt,oldt) E),newt)| None \<Rightarrow> None ) "

definition clash_propagate2 :: "tysym \<Rightarrow> tysym \<Rightarrow> tysenv \<Rightarrow> (tysenv*tysym) option" where
"clash_propagate2 t1 t2 E = map_option  (\<lambda>x . (update_env x E, fst x)) (min_type t1 t2)"
 
lemma clash_prop_alt: "clash_propagate2 t1 t2 E = clash_propagate t1 t2 E"
  by (auto simp add: clash_propagate2_def clash_propagate_def split: option.splits) 

lemma clash_prop_comm: "clash_propagate2 t1 t2 E = clash_propagate2 t2 t1 E"
  using min_comm by (auto simp add: clash_propagate2_def)


definition trm_f :: "(nat \<Rightarrow> tysym) \<Rightarrow> (nat \<Rightarrow> tysym) \<Rightarrow>nat set \<Rightarrow> (tysym \<Rightarrow> tysym) " where
"trm_f E' E W = (\<lambda>t. foldl (\<lambda> t' n . if E n = t then E' n else t') t (sorted_list_of_set W) )"

lemma trm_f_foldl_id: assumes "\<forall>n \<in> set w . t \<noteq> E n " shows "foldl (\<lambda>t' n. if E n = t then E' n else t') t w = t"
  using assms by (induction w)  auto 

lemma trm_f_id: assumes "\<forall>n' \<in> W .t \<noteq> E n'" "finite W" shows "(trm_f E' E W) t = t"
  unfolding trm_f_def using trm_f_foldl_id[of "sorted_list_of_set W"  "t" E E'] assms set_sorted_list_of_set[of W] 
  by simp

definition check_binop where  (* what if typ < exp_typ? e.g typ = TCst TInt*)
"check_binop check_trm E typ t1 t2 exp_typ  \<equiv> 
(case  min_type exp_typ typ  of Some (newt,oldt) \<Rightarrow> 
  (case check_trm (update_env (newt,oldt) E) newt t1  of
     Some (E', t_typ) \<Rightarrow>
          (case check_trm E' t_typ t2  of
             Some (E'', t_typ2) \<Rightarrow> Some ( E'', t_typ2 )
            | None \<Rightarrow> None ) 
     | None \<Rightarrow> None)
  | None \<Rightarrow> None )"

definition check_binop2 where
"check_binop2 check_trm E typ t1 t2 exp_typ  \<equiv> 
(case  clash_propagate2 exp_typ typ E  of Some (E1,newt) \<Rightarrow> 
  (case check_trm E1 newt t1  of
     Some (E', t_typ) \<Rightarrow> check_trm E' t_typ t2
     | None \<Rightarrow> None)
  | None \<Rightarrow> None )"

lemma [fundef_cong]: "(\<And>  E typ t . size t \<le> size t1 + size t2 \<Longrightarrow> check_trm E typ t = check_trm' E typ t) \<Longrightarrow> check_binop check_trm E typ t1 t2 exp_typ = check_binop check_trm' E typ t1 t2 exp_typ"
 by (auto simp add: check_binop_def split: option.split ) 

lemma [fundef_cong]: "(\<And>  E typ t . size t \<le> size t1 + size t2 \<Longrightarrow> check_trm E typ t = check_trm' E typ t) \<Longrightarrow> check_binop2 check_trm E typ t1 t2 exp_typ = check_binop2 check_trm' E typ t1 t2 exp_typ"
 by (auto simp add: check_binop2_def split: option.split ) 
(*2nd propagate needed?*)
fun check_trm :: "tysenv \<Rightarrow> tysym \<Rightarrow>  Formula.trm  \<Rightarrow> (tysenv * tysym) option" where
"check_trm E typ (Formula.Var v) = clash_propagate2  (E v) typ E "
| "check_trm E typ (Formula.Const c)  =  clash_propagate2 (TCst (ty_of c)) typ  E"
| "check_trm E typ (Formula.F2i t)  =   (case clash_propagate2  typ (TCst TInt) E of Some (E',precise_type) \<Rightarrow> 
 (case check_trm E' (TCst TFloat) t  of Some ( E'', t_typ) \<Rightarrow>
    Some ( E'', TCst TInt)
    | None \<Rightarrow> None) 
| None \<Rightarrow> None)" 
| "check_trm E typ (Formula.I2f t)  =   (case clash_propagate2  typ (TCst TFloat) E of Some (E',precise_type) \<Rightarrow> 
 (case check_trm E' (TCst TInt) t  of Some ( E'', t_typ) \<Rightarrow>
    Some ( E'', TCst TFloat)
    | None \<Rightarrow> None) 
| None \<Rightarrow> None)" 
|"check_trm E typ (Formula.UMinus t)  = (case clash_propagate2 (TNum 0) (new_type_symbol typ) (new_type_symbol \<circ> E) of 
  Some (E', precise_type) \<Rightarrow>  check_trm E' precise_type t
  | None \<Rightarrow> None)"
|"check_trm E typ (Formula.Plus t1 t2)  = check_binop2 check_trm  (new_type_symbol \<circ> E) (new_type_symbol typ) t1 t2  (TNum 0) " 
(* increment typ if its a TNum/TAny? yes! case: E = x:TNum 0, a: TAny 2, b: TAny 3 and \<phi> is x = (a + b)*)
(* added increment back to it, makes proof check_trm_sound easier*)
|"check_trm E typ (Formula.Minus t1 t2)  = check_binop2 check_trm  (new_type_symbol \<circ> E) (new_type_symbol typ) t1 t2  (TNum 0) "
|"check_trm E typ (Formula.Mult t1 t2)  = check_binop2 check_trm  (new_type_symbol \<circ> E)  (new_type_symbol typ) t1 t2  (TNum 0) "
|"check_trm E typ (Formula.Div t1 t2)  = check_binop2 check_trm  (new_type_symbol \<circ> E) (new_type_symbol typ) t1 t2  (TNum 0) "
|"check_trm E typ (Formula.Mod t1 t2)  = check_binop2 check_trm E typ t1 t2  (TCst TInt) "


definition check_comparison where
"check_comparison E t1 t2  \<equiv> (case check_trm   (new_type_symbol \<circ> E) (TAny 0) t1  of
   Some (E',t1_typ ) \<Rightarrow> (case check_trm  E' t1_typ t2  of Some (E'', t2_typ) \<Rightarrow>
   Some ( trm_f E'' E (fv_trm t1 \<union> fv_trm t2) ) | None \<Rightarrow> None)
| None \<Rightarrow> None)"

definition check_two_formulas :: "(sig \<Rightarrow> tysenv \<Rightarrow> tysym Formula.formula  \<Rightarrow>   (tysym \<Rightarrow> tysym) option) \<Rightarrow> sig \<Rightarrow> tysenv  \<Rightarrow> tysym Formula.formula  \<Rightarrow> tysym Formula.formula \<Rightarrow>  (tysym \<Rightarrow> tysym) option" where
"check_two_formulas check S E  \<phi> \<psi>  \<equiv> (case check S E \<phi>  of
   Some f \<Rightarrow> (case check S (f \<circ> E) (formula.map_formula f \<psi>) of Some f' \<Rightarrow> Some (f' \<circ> f) | None \<Rightarrow> None )
   | None \<Rightarrow> None)"

definition check_ands_f :: "(sig \<Rightarrow> tysenv \<Rightarrow> tysym Formula.formula  \<Rightarrow>   (tysym \<Rightarrow> tysym) option) \<Rightarrow> sig \<Rightarrow> tysenv \<Rightarrow>  (tysym \<Rightarrow> tysym) option \<Rightarrow> tysym Formula.formula \<Rightarrow>(tysym \<Rightarrow> tysym) option  " where
"check_ands_f check S E = (\<lambda> f_op \<phi> . case f_op of Some f \<Rightarrow> (case check S (f \<circ> E) (formula.map_formula f \<phi>) of Some f' \<Rightarrow> Some (f' \<circ> f)| None \<Rightarrow> None )
    | None \<Rightarrow> None )"

definition check_ands where
"check_ands check S E \<phi>s = foldl (check_ands_f check S E) (Some id) \<phi>s"

definition highest_bound_TAny where
"highest_bound_TAny \<phi> \<equiv> Max ((\<lambda>t. case t of TAny n \<Rightarrow> n | _ \<Rightarrow> 0) ` formula.set_formula \<phi>)"

definition E_empty where
"E_empty \<phi> = (TAny \<circ> (+) (highest_bound_TAny \<phi> + 1))"

fun check_pred :: "tysenv \<Rightarrow> Formula.trm list \<Rightarrow> tysym list \<Rightarrow>  (tysenv) option" where
"check_pred  E  (f#fs) (t#ts)  = (case check_trm  E t f of
 Some (E', new_t) \<Rightarrow> check_pred  E' fs ts
 | None \<Rightarrow> None)"
|"check_pred  E  [] []  = Some E"
|"check_pred  E  _ _  = None"


fun check_regex :: "(sig \<Rightarrow> tysenv  \<Rightarrow> tysym Formula.formula  \<Rightarrow>   (tysym \<Rightarrow> tysym) option) \<Rightarrow>sig \<Rightarrow> tysenv  \<Rightarrow> tysym Formula.formula Regex.regex  \<Rightarrow>   (tysym \<Rightarrow> tysym) option"  where
"check_regex check S E  (Regex.Skip l)  = Some id"
| "check_regex check S E  (Regex.Test \<phi>)  = check S E  \<phi>"
| "check_regex check S E  (Regex.Plus r s)  = (case check_regex check S E r  of
  Some f \<Rightarrow> (case check_regex check S (f \<circ> E) s of Some f' \<Rightarrow> Some (f' \<circ> f) | None \<Rightarrow> None )
| None \<Rightarrow> None )"
| "check_regex check S E  (Regex.Times r s)  = (case check_regex check S E r  of
  Some f \<Rightarrow> (case check_regex check S (f \<circ> E) s of Some f' \<Rightarrow> Some (f' \<circ> f) | None \<Rightarrow> None )
| None \<Rightarrow> None )"
| "check_regex check S E  (Regex.Star r)  = check_regex check S E r"


fun agg_trm_tysym :: "Formula.agg_type \<Rightarrow> tysym" where
"agg_trm_tysym Formula.Agg_Sum = TNum 0"
| "agg_trm_tysym Formula.Agg_Cnt = TAny 0"
| "agg_trm_tysym Formula.Agg_Avg = TNum 0"
| "agg_trm_tysym Formula.Agg_Med = TNum 0"
| "agg_trm_tysym Formula.Agg_Min = TAny 0"
| "agg_trm_tysym Formula.Agg_Max = TAny 0"

fun agg_ret_tysym :: "Formula.agg_type \<Rightarrow> tysym \<Rightarrow> tysym" where
"agg_ret_tysym Formula.Agg_Sum t = t"
| "agg_ret_tysym Formula.Agg_Cnt _ = TCst TInt"
| "agg_ret_tysym Formula.Agg_Avg _ = TCst TFloat"
| "agg_ret_tysym agg_type.Agg_Med _ = TCst TFloat "
| "agg_ret_tysym Formula.Agg_Min t = t"
| "agg_ret_tysym Formula.Agg_Max t = t"

lemma map_regex_size: assumes "\<And>x . x \<in> regex.atms r \<Longrightarrow>   size (f x) =size x" shows"regex.size_regex size r = regex.size_regex size (regex.map_regex f r) "
  using assms by (induction r arbitrary: ) auto


lemma map_formula_size[simp]:"size (formula.map_formula f \<psi>) = size \<psi>" 
  apply (induction \<psi> arbitrary: f) 
 apply auto apply ( simp add: dual_order.eq_iff size_list_pointwise) using map_regex_size  by metis+


lemma [fundef_cong]: "(\<And> S E \<phi>'  . size \<phi>' \<le> size \<phi> + size \<psi> \<Longrightarrow> check S E \<phi>' = check' S E  \<phi>') \<Longrightarrow> check_two_formulas check S E \<phi> \<psi> = check_two_formulas check' S E \<phi> \<psi>"
  by (auto simp add: check_two_formulas_def split: option.split ) 

lemma foldl_check_ands_f_fundef_cong: "(\<And> S E \<phi>'  .  size \<phi>' \<le> size_list size \<phi>s \<Longrightarrow> check S E \<phi>' = check' S E  \<phi>') \<Longrightarrow> foldl (check_ands_f check S E) f \<phi>s = foldl (check_ands_f check' S E) f \<phi>s"
  by (induction \<phi>s arbitrary: f) (auto simp: check_ands_f_def split: option.splits)

lemma [fundef_cong]: "(\<And> S E \<phi>'  .  size \<phi>' \<le> size_list size \<phi>s \<Longrightarrow> check S E \<phi>' = check' S E  \<phi>') \<Longrightarrow> check_ands check S E \<phi>s = check_ands check' S E \<phi>s"
  using foldl_check_ands_f_fundef_cong[of \<phi>s check]
  by (auto simp: check_ands_def)


lemma [fundef_cong]: "(\<And> S E \<phi>'  . \<phi>' \<in> regex.atms r \<Longrightarrow> check S E  \<phi>' = check' S E  \<phi>') \<Longrightarrow> check_regex check S E  r = check_regex check' S E  r"
   apply (induction r arbitrary: S E ) apply auto 
  by presburger+

(*
definition "check_f f f' W = f " *)

fun check :: "sig \<Rightarrow> tysenv  \<Rightarrow> tysym Formula.formula  \<Rightarrow>   (tysym \<Rightarrow> tysym) option"
  where (*what to do if predicate is not in sigs?*)
  "check S E  (Formula.Pred r ts)  = (case S r of 
  None \<Rightarrow> None 
  | Some tys \<Rightarrow> (case check_pred E ts (map TCst tys) of
        Some E' \<Rightarrow> Some (trm_f E' E (\<Union>t\<in>set ts. fv_trm t ))
        | None \<Rightarrow> None  ))"
| "check S E (Formula.Let p \<phi> \<psi>)  = (case check S (E_empty \<phi>)  \<phi> of 
  Some f \<Rightarrow> if \<forall>x \<in> Formula.fv \<phi> . case f ((E_empty \<phi>) x) of TCst _ \<Rightarrow> True | _ \<Rightarrow> False 
      then  check (S(p \<mapsto> tabulate (\<lambda>x. case f ((E_empty \<phi>) x) of TCst t \<Rightarrow> t ) 0 (Formula.nfv \<phi>))) E \<psi> 
      else None
  | None \<Rightarrow> None)"
| "check S E  (Formula.Eq t1 t2)  = check_comparison E t1 t2 "
| "check S E  (Formula.Less t1 t2)  = check_comparison  E t1 t2 "
| "check S E  (Formula.LessEq t1 t2)  = check_comparison E t1 t2 "
| "check S E  (Formula.Neg \<phi>)  =  check S E \<phi>"
| "check S E   (Formula.Or \<phi> \<psi>)  =  check_two_formulas check S E  \<phi> \<psi>"
| "check S E  (Formula.And \<phi> \<psi>)  = check_two_formulas check S E  \<phi> \<psi>"
| "check S E (Formula.Ands \<phi>s)  = check_ands check S E \<phi>s" 
| "check S E  (Formula.Exists t \<phi>)  =   check S (case_nat  t E)  \<phi> " (*change/check f' somehow?*)
| "check S E  (Formula.Agg y (agg_type, d) tys trm \<phi>)  = (case check_trm  (new_type_symbol \<circ> (agg_tysenv E  tys)) (agg_trm_tysym agg_type) trm of
   Some (E', trm_type) \<Rightarrow> (case check S E' (formula.map_formula (trm_f E' E (fv_trm trm)) \<phi>) of 
       Some  f \<Rightarrow> (case clash_propagate2 ((f \<circ> E'\<circ> (+) (length tys)) y) (TCst (ty_of d) ) (f \<circ> E' \<circ> (+) (length tys)) of 
          Some (E''', ret_t) \<Rightarrow> (case clash_propagate2 ret_t (agg_ret_tysym agg_type trm_type) E''' of 
              Some (E4, t4) \<Rightarrow>  Some  (trm_f E4 E ({y} \<union> fv_trm trm \<union> fv \<phi>) ) 
               | None \<Rightarrow> None )
          | None \<Rightarrow> None)
       | None \<Rightarrow> None)
   | None \<Rightarrow> None)"
| "check S E  (Formula.Prev I \<phi>)  =  check S E \<phi> "
| "check S E (Formula.Next I \<phi>)  =   check S E \<phi> "
| "check S E (Formula.Since \<phi> I \<psi>)  = check_two_formulas check S E  \<phi> \<psi>"
| "check S E (Formula.Until \<phi> I \<psi>) =  check_two_formulas check S E  \<phi> \<psi>  "
| "check S E (Formula.MatchF I r)  = check_regex check S E r"
| "check S E (Formula.MatchP I r)  = check_regex check S E r "

lemma "check (\<lambda>s. None) (\<lambda>n.  TAny n) (Formula.And (Formula.Eq ( trm.Var 3) (trm.Const (EFloat 0))) (Formula.Eq (trm.Const (EInt 5)) (trm.Var 1))  ) = Some (\<lambda>x. if x = TAny 2 \<or> x = TAny 1 then TCst TInt else x)"
  apply (auto simp add: check_comparison_def check_two_formulas_def Formula.TT_def clash_propagate2_def update_env_def case_nat_def case_tysym_def new_type_symbol_def trm_f_def split: nat.splits if_splits tysym.splits option.splits) 
  sorry
primrec newSymsList :: "unit list \<Rightarrow> nat \<Rightarrow> tysym list" where
"newSymsList (_#xs) n =  TAny n #newSymsList xs (n+1) "
| "newSymsList [] n = []"


primrec unitToSymRegex :: "(unit Formula.formula \<Rightarrow> nat \<Rightarrow> tysym Formula.formula * nat) \<Rightarrow> unit Formula.formula Regex.regex \<Rightarrow>  nat \<Rightarrow> tysym Formula.formula Regex.regex * nat" where 
  "unitToSymRegex formulasym (Regex.Skip l) n = (Regex.Skip l, n)"
| "unitToSymRegex formulasym (Regex.Test \<phi>) n = (case formulasym \<phi> n of (\<phi>', k) \<Rightarrow>  (Regex.Test \<phi>',k))"
| "unitToSymRegex formulasym (Regex.Plus r s) n = (case unitToSymRegex formulasym r n of (r',k) \<Rightarrow> 
      (case unitToSymRegex formulasym s k of (s',k') \<Rightarrow> (Regex.Plus r' s' ,k')))"
| "unitToSymRegex formulasym (Regex.Times r s) n = (case unitToSymRegex formulasym r n of (r',k) \<Rightarrow> 
      (case unitToSymRegex formulasym s k of (s',k') \<Rightarrow> (Regex.Times r' s' ,k')))"
| "unitToSymRegex formulasym (Regex.Star r) n = (case unitToSymRegex formulasym r n of (r',k) \<Rightarrow> (Regex.Star r', k))"

lemma [fundef_cong]: "(\<And> n \<phi>' . \<phi>' \<in> regex.atms r \<Longrightarrow> formulasym \<phi>' n = formulasym' \<phi>' n) \<Longrightarrow> unitToSymRegex formulasym r n = unitToSymRegex formulasym' r n"
   by (induction r arbitrary: n) auto 
  


primrec unitToSymAnds :: "(unit Formula.formula \<Rightarrow> nat \<Rightarrow> tysym Formula.formula * nat) \<Rightarrow> unit Formula.formula list \<Rightarrow> nat \<Rightarrow> tysym Formula.formula list * nat" where
"unitToSymAnds formulasym (\<phi>#\<phi>s) n = (case formulasym \<phi> n of (\<phi>',k) \<Rightarrow> ( case unitToSymAnds formulasym \<phi>s k of (\<phi>'s, l) \<Rightarrow>  (  \<phi>'#\<phi>'s, l)))"
|"unitToSymAnds formulasym [] n = ([] ,n)"

lemma [fundef_cong]: "(\<And> \<phi> n .  \<phi> \<in> set \<phi>s  \<Longrightarrow> formulasym \<phi> n = formulasym' \<phi> n) \<Longrightarrow> unitToSymAnds formulasym \<phi>s n = unitToSymAnds formulasym' \<phi>s n"
 by (induction \<phi>s arbitrary: n)  auto

fun unitToSym :: "unit Formula.formula \<Rightarrow> nat \<Rightarrow> tysym Formula.formula * nat"  where
"unitToSym (Formula.Exists () \<phi>) n = (case unitToSym \<phi> (n+1) of (\<phi>',k) \<Rightarrow> (Formula.Exists (TAny n) \<phi>', k))"
| "unitToSym (Formula.Agg y \<omega> tys f  \<phi>) n = 
  (case unitToSym \<phi> (n+ length tys) of (\<phi>',k) \<Rightarrow> (Formula.Agg y \<omega> (newSymsList tys n) f \<phi>', k))"
|  "unitToSym (Formula.Pred r ts) n = (Formula.Pred r ts, n)"
| "unitToSym (Formula.Let p \<phi> \<psi>) n = (case unitToSym \<phi> n of (\<phi>',k) \<Rightarrow> 
      (case unitToSym \<psi> k of (\<psi>',k') \<Rightarrow> (Formula.Let p \<phi>' \<psi>' ,k')))"
| "unitToSym (Formula.Eq t1 t2) n  = (Formula.Eq t1 t2, n) "
| "unitToSym (Formula.Less t1 t2) n = (Formula.Less t1 t2, n)"
| "unitToSym (Formula.LessEq t1 t2) n = (Formula.LessEq t1 t2, n)"
| "unitToSym (Formula.Neg \<phi>) n  = (case unitToSym \<phi> n of (\<phi>',k) \<Rightarrow>(Formula.Neg \<phi>',k)) "
| "unitToSym (Formula.Or \<phi> \<psi>) n = (case unitToSym \<phi> n of (\<phi>',k) \<Rightarrow> 
      (case unitToSym \<psi> k of (\<psi>',k') \<Rightarrow> (Formula.Or \<phi>' \<psi>' ,k')))"
| "unitToSym (Formula.And \<phi> \<psi>) n = (case unitToSym \<phi> n of (\<phi>',k) \<Rightarrow> 
      (case unitToSym \<psi> k of (\<psi>',k') \<Rightarrow> (Formula.And \<phi>' \<psi>' ,k')))"
| "unitToSym (Formula.Ands \<phi>s) n = (case  unitToSymAnds unitToSym \<phi>s n of (\<phi>'s, k) \<Rightarrow>  (Formula.Ands \<phi>'s,k))"
| "unitToSym (Formula.Prev I \<phi>) n = (case unitToSym \<phi> n of (\<phi>',k) \<Rightarrow>(Formula.Prev I \<phi>',k)) "
| "unitToSym (Formula.Next I \<phi>) n = (case unitToSym \<phi> n of (\<phi>',k) \<Rightarrow>(Formula.Next I \<phi>',k))"
| "unitToSym (Formula.Since \<phi> I \<psi>) n = (case unitToSym \<phi> n of (\<phi>',k) \<Rightarrow> 
      (case unitToSym \<psi> k of (\<psi>',k') \<Rightarrow> (Formula.Since \<phi>' I \<psi>' ,k')))"
| "unitToSym (Formula.Until \<phi> I \<psi>) n = (case unitToSym \<phi> n of (\<phi>',k) \<Rightarrow> 
      (case unitToSym \<psi> k of (\<psi>',k') \<Rightarrow> (Formula.Until \<phi>' I \<psi>' ,k')))"
| "unitToSym (Formula.MatchF I r) n = (case unitToSymRegex unitToSym r n of (r',k) \<Rightarrow> (Formula.MatchF I r',k))"
| "unitToSym (Formula.MatchP I r) n = (case unitToSymRegex unitToSym r n of (r',k) \<Rightarrow> (Formula.MatchP I r',k))"


(* definition check_safe :: "sig \<Rightarrow> unit Formula.formula \<Rightarrow> (tyenv * ty Formula.formula) option" where
  "check_safe S \<phi> = map_option 
  (\<lambda>(E,\<phi>).  ((\<lambda>x. case E x of TCst t' \<Rightarrow> t'), Formula.map_formula (\<lambda>t. case t of TCst t' \<Rightarrow> t') \<phi>))
     (case unitToSym \<phi> 0 of (\<phi>', n ) \<Rightarrow> check S (\<lambda> k. TAny (n + k) ) \<phi>')" *)

definition wf_f :: "(tysym \<Rightarrow> tysym) \<Rightarrow> bool" where
"wf_f f \<equiv> (\<forall>x. f (TCst x) = TCst x) \<and> (\<forall>n . case f (TNum n) of TCst x \<Rightarrow> x \<in> numeric_ty | TNum x \<Rightarrow> True | _ \<Rightarrow> False)"

lemma wf_f_comp: "wf_f f \<Longrightarrow> wf_f g \<Longrightarrow> wf_f (f \<circ> g)"
apply (auto simp add: comp_def wf_f_def split: tysym.splits) 
  by (metis tysym.exhaust)+ 

lemma[simp]: "wf_f id" 
  unfolding wf_f_def by auto
(*
definition tysenvless :: "tysenv \<Rightarrow> tysenv \<Rightarrow> bool" where
  "tysenvless E E' \<longleftrightarrow> (\<forall>x. tyless  (E x) (E' x))"
*)

definition tysenvless :: "tysenv \<Rightarrow> tysenv \<Rightarrow> bool" where
"tysenvless E' E \<longleftrightarrow> (\<exists>f . wf_f f \<and> E' = f \<circ> E )"

lemma tysenvless_trans: "tysenvless E'' E' \<Longrightarrow> tysenvless E' E \<Longrightarrow> tysenvless E'' E"
  apply (auto simp add: tysenvless_def) subgoal for f g apply (rule exI[of _ "f \<circ> g"]) 
    using wf_f_comp by auto done

definition "resultless_trm E' E typ' typ \<longleftrightarrow> (\<exists> f. wf_f f \<and>   E' = f \<circ> E  \<and> typ' = f typ)"

definition "resultless_trm_f E' E typ' typ f W  \<longleftrightarrow> wf_f f \<and> (\<forall>x \<in> W.   E' x  = (f \<circ> E) x) \<and> typ' = f typ"

lemma resultless_trm_f_correct: "resultless_trm E' E typ' typ \<Longrightarrow>  finite W
   \<Longrightarrow>  resultless_trm_f E' E typ' typ (trm_f E' E W) W"
  unfolding resultless_trm_def resultless_trm_f_def trm_f_def using set_sorted_list_of_set sorry


  

lemma tysenvless_resultless_trm: assumes
 "tysenvless E' E" "case typ of TCst t' \<Rightarrow> typ = typ' | TNum n \<Rightarrow> t \<in> numeric_ty \<and> typ' = TCst t \<or> typ' = typ |_  \<Rightarrow> True "
  "(\<forall>x. E x \<noteq> typ) \<or> typ = TCst t"
  shows "resultless_trm E' E typ' typ"
  using assms apply (auto simp add: tysenvless_def resultless_trm_def)  subgoal for g apply (rule exI[of _ "g(typ := typ')" ]) 
    by (auto simp add: wf_f_def split: tysym.splits)  subgoal for g  apply (rule exI[of _ "g(typ := typ')" ]) 
    by (auto simp add: wf_f_def) done

lemma resultless_trm_tysenvless: assumes "resultless_trm  E'' E' t t'"
  shows "tysenvless  E'' E'"
  using assms unfolding resultless_trm_def tysenvless_def by auto


lemma some_min_resless: assumes "min_type typ z = Some y"
  shows "resultless_trm (update_env y E) E (fst y) typ "
proof -
  obtain tnew told where y_def: "y = (tnew,told)" by (cases y)
  define f where "f = (\<lambda>x . if x = told then tnew else x)"
  have wf: "wf_f f" using assms  apply (induction "z"  "typ" rule: min_type.induct)
    by (auto simp add: y_def f_def numeric_ty_def wf_f_def eq_commute[where ?b= "z"] split: if_splits tysym.splits)
  show ?thesis unfolding resultless_trm_def apply (rule exI[of _ f])  
    using assms wf apply (induction "z"  "typ" rule: min_type.induct)
    by (auto simp add: y_def f_def comp_def update_env_def eq_commute[where ?b= "z"] split: if_splits)
qed

lemma resless_newtype: "resultless_trm (new_type_symbol \<circ> E) E  (new_type_symbol typ) typ "
 "resultless_trm E (new_type_symbol \<circ> E) typ (new_type_symbol typ)"
   unfolding resultless_trm_def  apply (rule exI[of _ "new_type_symbol "]) subgoal 
     by (auto simp add:   wf_f_def new_type_symbol_def)
   apply (rule exI[of _ "(\<lambda>x.  case x of TCst t \<Rightarrow> TCst t | TAny n \<Rightarrow> TAny (n-1)| TNum n \<Rightarrow> TNum (n-1) )"]) 
   by (auto simp add: wf_f_def new_type_symbol_def  split: tysym.splits) 


(*
Decision for F2i / I2f:

lemma " (case clash_propagate2  typ (TCst TInt) E of Some (E',precise_type) \<Rightarrow> 
 (case check_trm E' (TCst TFloat) t  of Some ( E'', t_typ) \<Rightarrow>
    Some ( E'', TCst TInt)
    | None \<Rightarrow> None) 
| None \<Rightarrow> None) = (case check_trm E (TCst TFloat) t  of Some ( E', t_typ) \<Rightarrow> clash_propagate2  typ (TCst TInt) E' | None \<Rightarrow> None)"
   using min_const apply (auto simp add: clash_propagate2_def min_comm[where ?b="TCst TInt"] split: option.splits )
   oops

lemma "t = trm.Var x \<Longrightarrow> E x = TAny 0 \<Longrightarrow> typ = TAny 0 \<Longrightarrow> (case clash_propagate2  typ (TCst TInt) E of Some (E',precise_type) \<Rightarrow> 
 (case check_trm E' (TCst TFloat) t  of Some ( E'', t_typ) \<Rightarrow>
    Some ( E'', TCst TInt)
    | None \<Rightarrow> None) 
| None \<Rightarrow> None) = (case check_trm E (TCst TFloat) t  of Some ( E', t_typ) \<Rightarrow> clash_propagate2  typ (TCst TInt) E' | None \<Rightarrow> None) \<Longrightarrow> False"
    by (auto simp add: clash_propagate2_def  update_env_def split: option.splits) 
*)

lemma resultless_trm_refl: "resultless_trm E E type type"
  apply (auto simp add: resultless_trm_def ) apply (rule exI[of _ id]) by (auto simp add: wf_f_def)

lemma resultless_trm_trans: assumes " resultless_trm E'' E' type'' type'" "resultless_trm E' E type' type"   
  shows "resultless_trm E'' E type'' type"
  using assms apply (auto simp add: resultless_trm_def) subgoal for f g 
 apply (rule exI[of _ "f \<circ> g"]) 
    using wf_f_comp by auto done


(*
lemma resultless_trm_trans_typeless: assumes " resultless_trm E'' E' type'' type1" "resultless_trm E' E type2 type"   
  shows "resultless_trm E'' E type'' type"
  using assms apply (auto simp add: resultless_trm_def) subgoal for f g 
 apply (rule exI[of _ "f \<circ> g"]) 
    using wf_f_comp apply auto done
*)
lemma assumes "resultless_trm (TCst \<circ> E'') E (TCst type'') type" "resultless_trm E' E type' type" 
"E'' \<turnstile> t :: type''"   " check_trm E type t = Some (E', type')"
shows "resultless_trm (TCst \<circ> E'') E'  (TCst type'') type'"
   using assms apply (induction t ) apply (auto simp add: resultless_trm_def clash_propagate2_def elim: wty_trm.cases)  
  oops
lemma resless_all_const_eq: "resultless_trm (TCst \<circ> E'') E ty1 ty2 \<Longrightarrow> E x = TCst t \<Longrightarrow> E'' x =  t"
  unfolding resultless_trm_def wf_f_def  
  by (metis comp_eq_elim tysym.inject(3))

lemma resless_all_numeric: "resultless_trm (TCst \<circ> E'') E ty1 ty2 \<Longrightarrow> E x = TNum n \<Longrightarrow> E'' x \<in> numeric_ty"
  unfolding resultless_trm_def wf_f_def 
  by (metis comp_eq_elim tysym.simps(12))



lemma resless_wty_num: assumes " resultless_trm (TCst \<circ> E'') E (TCst typ'') type"
    "Some (newt, oldt) = min_type x (new_type_symbol type)" "case x of TNum 0 \<Rightarrow> typ'' \<in> numeric_ty | TCst t \<Rightarrow> t = typ'' | _ \<Rightarrow> False"
  shows  "resultless_trm (TCst \<circ> E'') (update_env (newt, oldt) (new_type_symbol \<circ> E)) (TCst typ'') newt"
proof -
  have newtype_E: "resultless_trm (TCst \<circ> E'') (new_type_symbol \<circ> E) (TCst typ'') (new_type_symbol type)" apply (rule resultless_trm_trans[where ?E'=E]) 
    using assms(1) resless_newtype(2) by auto
  then obtain f where f_def: "wf_f f \<and> TCst \<circ> E'' = f \<circ>  new_type_symbol \<circ> E \<and> TCst typ'' = f  (new_type_symbol type)"  unfolding resultless_trm_def  by (auto simp add: comp_def)
  define g where g_def: "g = (\<lambda>x. if x = newt then TCst typ'' else f x)"
  show ?thesis using assms(2-3) f_def  apply (auto simp add: resultless_trm_def) apply (rule exI[of _ g])
   apply (auto simp add: wf_f_def g_def split: tysym.splits nat.splits) 
    apply (metis min_consistent tysym.distinct(5) tysym.inject(3)) apply (rule ext) subgoal for  x
       apply (auto simp add: update_env_def new_type_symbol_def comp_def split:if_splits tysym.splits)  
      apply (metis min_consistent tysym.distinct(1))
      apply (metis min_consistent tysym.distinct(1))
      apply (metis Suc_neq_Zero min_consistent tysym.inject(2)) 
      apply (metis Suc_neq_Zero min_consistent tysym.inject(2)) 
      apply (metis min_consistent tysym.distinct(5) tysym.inject(3))
      by (metis min_consistent tysym.distinct(5) tysym.inject(3)) 
    apply (metis min_const tysym.inject(3)) 
    apply (metis min_const) apply (rule ext) subgoal for  x
       apply (auto simp add: update_env_def new_type_symbol_def comp_def split:if_splits tysym.splits) 
      apply (metis min_consistent) 
      apply (metis min_const)
      apply (metis min_consistent)
      apply (metis min_const)
      apply (metis min_consistent tysym.inject(3))
      by (metis min_const tysym.inject(3)) done
      
    (*apply (metis min_consistent tysym.distinct(5))
     apply (metis tysym.simps(12)) apply (rule ext) subgoal for  x
       apply (auto simp add: update_env_def new_type_symbol_def comp_def split:if_splits tysym.splits)  
      apply (metis min_consistent tysym.distinct(1))
            apply (metis min_consistent tysym.distinct(1))
      apply (metis Suc_neq_Zero min_consistent tysym.inject(2)) 
         apply (metis Suc_neq_Zero min_consistent tysym.inject(2))
      apply (metis min_consistent tysym.distinct(5) tysym.inject(3)) 
      by (metis min_consistent tysym.distinct(5) tysym.inject(3)) done *)

qed 

lemma resless_wty_const: assumes " resultless_trm (TCst \<circ> E'') E (TCst typ'') type"
    "Some (newt, oldt) = min_type (TCst typ'') type"
  shows  "resultless_trm (TCst \<circ> E'') (update_env (newt, oldt) E) (TCst typ'') newt"
proof -
  obtain f where f_def: "wf_f f" "f \<circ> E = TCst \<circ> E''" "f type = TCst typ''" using assms(1) by (auto simp add: resultless_trm_def)
  show ?thesis  unfolding resultless_trm_def apply (rule exI[of _ f]) using assms(2) f_def min_const[of typ'' type] 
    apply (auto  simp add: eq_commute[where ?a="Some(newt,oldt)"] wf_f_def  ) apply (rule ext) subgoal for x
      using min_consistent[of "TCst typ''" type] 
      apply (auto simp add:  update_env_def comp_def ) 
      apply (metis tysym.inject(3)) 
      apply metis 
      apply (metis tysym.inject(3))
  by metis done 
qed

lemma resless_wty_num_dir2: assumes
"resultless_trm E1 E2 (TCst typ'') newt"
    "Some (newt, oldt) = min_type (TNum n) ty" 
  shows  " typ'' \<in> numeric_ty"
  using assms 
  by (induction "TNum n" "ty" rule: min_type.induct)
  (auto simp add: resultless_trm_def  numeric_ty_def new_type_symbol_def wf_f_def split: tysym.splits if_splits) 
  
lemma resless_wty_const_dir2: assumes 
"resultless_trm E1 E2 (TCst typ'') newt"
    "Some (newt, oldt) = min_type (TCst t) type"
  shows "typ'' = t"
  using assms  min_const[of t type ]
  by (auto simp add: eq_commute[where ?a="Some(newt,oldt)"] resultless_trm_def wf_f_def) 


(*
attempt wty_result_trm using wty_result_trm0 



definition wty_result_trm0 :: " tysenv \<Rightarrow> tysym \<Rightarrow> tysenv \<Rightarrow> tysym \<Rightarrow> bool" where
"wty_result_trm0 E typ E' typ' \<longleftrightarrow> resultless_trm E' E typ' typ  \<and> 
(\<forall>E'' typ'' .   resultless_trm (TCst \<circ>  E'') E (TCst typ'') typ \<longrightarrow> resultless_trm (TCst \<circ>  E'') E' (TCst typ'') typ' )"

definition wty_result_trm :: " Formula.trm \<Rightarrow> tysenv \<Rightarrow> tysym \<Rightarrow> tysenv \<Rightarrow> tysym \<Rightarrow> bool" where
"wty_result_trm t E typ E' typ' \<longleftrightarrow> wty_result_trm0 E typ E' typ' \<and> 
  (\<forall>E'' typ'' .   resultless_trm (TCst \<circ>  E'') E (TCst typ'') typ \<longrightarrow>  resultless_trm (TCst \<circ>  E'') E' (TCst typ'') typ' \<longrightarrow>  E'' \<turnstile> t :: typ'') "


lemma wty_result_trm_correct: "wty_result_trm t E typ E' typ' = wty_result_trm_old  t E typ E' typ'"
  apply (auto simp add: wty_result_trm_def wty_result_trm_old_def wty_result_trm0_def) subgoal for E'' typ''   sorry sorry

*)
definition wty_result_trm :: " Formula.trm \<Rightarrow> tysenv \<Rightarrow> tysym \<Rightarrow> tysenv \<Rightarrow> tysym \<Rightarrow> bool" where
 "wty_result_trm  t E' typ' E typ \<longleftrightarrow> resultless_trm E' E typ' typ \<and> 
(\<forall>E'' typ'' .   resultless_trm (TCst \<circ>  E'') E (TCst typ'') typ \<longrightarrow> ( E'' \<turnstile> t :: typ'' \<longleftrightarrow> resultless_trm (TCst \<circ>  E'') E' (TCst typ'') typ' ))"
 
definition half_wty_trm ::  " Formula.trm \<Rightarrow> tysenv \<Rightarrow> tysym \<Rightarrow> tysenv \<Rightarrow> tysym \<Rightarrow> bool" where
"half_wty_trm t E' type' E type \<longleftrightarrow> resultless_trm E' E type' type \<and> 
(\<forall> E'' typ'' . (resultless_trm (TCst \<circ> E'') E (TCst typ'') type \<longrightarrow>
       E'' \<turnstile> t :: typ'' \<longrightarrow> resultless_trm (TCst \<circ> E'') E' (TCst typ'') type'))"

lemma wty_result_trm_alt: "wty_result_trm t  E' typ' E typ \<longleftrightarrow>  (resultless_trm E' E typ' typ \<and> 
(\<forall>E'' typ'' .   ( E'' \<turnstile> t :: typ'' \<and>  resultless_trm (TCst \<circ>  E'') E (TCst typ'') typ \<longleftrightarrow> resultless_trm (TCst \<circ>  E'') E' (TCst typ'') typ' )))"
  apply (auto simp add: wty_result_trm_def) 
  using resultless_trm_trans by blast+

(* Attempt for check_trm_step0 without term t:

lemma check_trm_step0_num: assumes
  "Some (E1, precise_type) = clash_propagate2 (TNum 0) (new_type_symbol type) (new_type_symbol \<circ> E)" 
  "typ'' \<in> numeric_ty"
shows " resultless_trm E1 E precise_type type "
  "(resultless_trm (TCst \<circ> E'') E (TCst typ'') type \<Longrightarrow>  resultless_trm (TCst \<circ> E'') E1 (TCst typ'') precise_type)" 

(* 2 subgoals for "wty_result_trm t E type E1 precise_type "
      cant show other direction of 2nd subgoal only typ'' \<in> numeric_ty *)
proof -
  obtain  oldt where t_def: "Some (precise_type,oldt) = min_type (TNum 0) (new_type_symbol type)" using assms(1)
    by (cases "min_type (TNum 0) (new_type_symbol type)")   (auto simp add:  clash_propagate2_def ) 
  then have E1_def: "E1 =  update_env (precise_type, oldt) (new_type_symbol \<circ> E)" using assms(1) 
    apply (cases "min_type (TNum 0) (new_type_symbol type)")  by (auto simp add:  clash_propagate2_def ) 
  then show f1: "resultless_trm E1 E precise_type type"
    using  t_def resultless_trm_trans[of "update_env (precise_type, oldt) (new_type_symbol \<circ> E)"] resless_newtype[of E type] 
      some_min_resless[of "new_type_symbol type" "TNum 0" "(precise_type,oldt)" "new_type_symbol \<circ> E"]
    by  (auto simp add: min_comm[where ?b="new_type_symbol type"])

  then show "(resultless_trm (TCst \<circ> E'') E (TCst typ'') type \<Longrightarrow>
       resultless_trm (TCst \<circ> E'') E1 (TCst typ'') precise_type) " using 
    assms(2) t_def E1_def resless_wty_num[of E'' E typ'' type precise_type oldt "TNum 0"]
    by auto
qed

sketch of additional lemma one would then need:

lemma resless_num: assumes "Some (E1,precise_type) = clash_propagate2 (TNum 0) (new_type_symbol type) (new_type_symbol \<circ> E)"
"wf_f f \<and> TCst typ'' = f precise_type"
shows "typ'' \<in> numeric_ty"
  using assms unfolding clash_propagate2_def apply(cases " map_option (\<lambda>x. (update_env x (new_type_symbol \<circ> E), fst x)) (min_type (TNum 0) (new_type_symbol type))")
   apply auto apply (cases "new_type_symbol type") apply (auto simp add: wf_f_def numeric_ty_def) sorry


*)

lemma subterm_half_wty: assumes "half_wty_trm t E' type' E type" 
 "\<And> E'' type'' . E'' \<turnstile> subtrm :: type'' \<Longrightarrow>  E'' \<turnstile> t :: type'' "
shows  "half_wty_trm subtrm E' type' E type"
  using assms unfolding half_wty_trm_def by (auto)

lemma check_trm_step0_half: assumes
  "Some (E', type') = clash_propagate2 t type  E" 
shows " resultless_trm E' E type' type "
   
  (* 2 subgoals for "wty_result_trm t E type E1 precise_type "
      cant show other direction of 2nd subgoal only typ'' \<in> numeric_ty *)
proof -  
 obtain  oldt where t_def: "Some (type',oldt) = min_type (t) type" using assms
    by (cases "min_type t (type)") (auto simp add:  clash_propagate2_def ) 
  then have E1_def: "E' =  update_env (type', oldt) ( E)" using assms
    by (cases "min_type (t) (type)")   (auto simp add:  clash_propagate2_def ) 
  then show g1: "resultless_trm E' E type' type"
    using  t_def resultless_trm_trans[of "update_env (type', oldt) ( E)"]  
      some_min_resless[of "type" "t" "(type',oldt)" " E"]
    by  (auto simp add: min_comm[where ?b="type"])
qed

lemma check_trm_step0_num: assumes
  "Some (E1, precise_type) = clash_propagate2 (TNum 0) (new_type_symbol type) (new_type_symbol \<circ> E)" 
  "\<And>E''. (E'' \<turnstile> t :: typ'') \<Longrightarrow> typ'' \<in> numeric_ty" 
shows " resultless_trm E1 E precise_type type "
  "(resultless_trm (TCst \<circ> E'') E (TCst typ'') type \<Longrightarrow>
       E'' \<turnstile> t :: typ'' \<Longrightarrow>  resultless_trm (TCst \<circ> E'') E1 (TCst typ'') precise_type)" 
  "(resultless_trm (TCst \<circ> E'') E (TCst typ'') type \<Longrightarrow>
       resultless_trm (TCst \<circ> E'') E1 (TCst typ'') precise_type \<Longrightarrow> typ'' \<in> numeric_ty)"
  (* 2 subgoals for "wty_result_trm t E type E1 precise_type "
      cant show other direction of 2nd subgoal only typ'' \<in> numeric_ty *)
proof -
  obtain  oldt where t_def: "Some (precise_type,oldt) = min_type (TNum 0) (new_type_symbol type)" using assms(1)
    by (cases "min_type (TNum 0) (new_type_symbol type)")   (auto simp add:  clash_propagate2_def ) 
  then have E1_def: "E1 =  update_env (precise_type, oldt) (new_type_symbol \<circ> E)" using assms(1) 
    apply (cases "min_type (TNum 0) (new_type_symbol type)")  by (auto simp add:  clash_propagate2_def ) 
  then show f1: "resultless_trm E1 E precise_type type"
    using  t_def resultless_trm_trans[of "update_env (precise_type, oldt) (new_type_symbol \<circ> E)"] resless_newtype[of E type] 
      some_min_resless[of "new_type_symbol type" "TNum 0" "(precise_type,oldt)" "new_type_symbol \<circ> E"]
    by  (auto simp add: min_comm[where ?b="new_type_symbol type"])

  then show "(resultless_trm (TCst \<circ> E'') E (TCst typ'') type \<Longrightarrow>
       E'' \<turnstile> t :: typ'' \<Longrightarrow>  resultless_trm (TCst \<circ> E'') E1 (TCst typ'') precise_type) " using 
    assms(2)[of E'' ] t_def E1_def resless_wty_num[of E'' E typ'' type precise_type oldt "TNum 0"]
    by auto

  show "(resultless_trm (TCst \<circ> E'') E (TCst typ'') type \<Longrightarrow>
       resultless_trm (TCst \<circ> E'') E1 (TCst typ'') precise_type \<Longrightarrow> typ'' \<in> numeric_ty)"
    using t_def  resless_wty_num_dir2[of "TCst \<circ> E''" E1 typ'' precise_type oldt 0 "new_type_symbol type"]
    by auto
qed

lemma check_trm_step0_cst2: assumes
  "Some (E1, precise_type) = clash_propagate2 (TCst typ'') type  E" 
shows " resultless_trm E1 E precise_type type "
  "(resultless_trm (TCst \<circ> E'') E (TCst typ'') type \<Longrightarrow>  resultless_trm (TCst \<circ> E'') E1 (TCst typ'') precise_type)" 

proof -
  obtain  oldt where t_def: "Some (precise_type,oldt) = min_type (TCst typ'') ( type)" using assms(1)
    by (cases "min_type (TCst typ'') ( type)")   (auto simp add:  clash_propagate2_def ) 
  then have E1_def: "E1 =  update_env (precise_type, oldt) (E)" using assms(1) 
    apply (cases "min_type (TCst typ'') ( type)")  by (auto simp add:  clash_propagate2_def ) 
  then show f1: "resultless_trm E1 E precise_type type"
    using  t_def resultless_trm_trans[of "update_env (precise_type, oldt) ( E)"] resless_newtype[of E type] 
      some_min_resless[of " type" "TCst typ''" "(precise_type,oldt)" " E"]
    by  (auto simp add: min_comm[where ?b=" type"])

  then show "(resultless_trm (TCst \<circ> E'') E (TCst typ'') type \<Longrightarrow>
       resultless_trm (TCst \<circ> E'') E1 (TCst typ'') precise_type) " using 
     t_def E1_def resless_wty_const[of E'' E typ'' type precise_type oldt ]
    by auto
qed

lemma check_trm_step0_cst: assumes
    "Some (E1, precise_type) = clash_propagate2 (TCst ty) type  E" 
    "\<And>E'' y . (E'' \<turnstile> t :: y) \<longleftrightarrow>  y = ty"
  shows "wty_result_trm t E1 precise_type E type "
proof -
  obtain  oldt where t_def: "Some (precise_type,oldt) = min_type (TCst ty) type" using assms(1)
    by (cases "min_type (TCst ty)  type")   (auto simp add:  clash_propagate2_def ) 
  then have E1_def: "E1 =  update_env (precise_type, oldt)  E" using assms(1) 
    apply (cases "min_type (TCst ty)  type")  by (auto simp add:  clash_propagate2_def ) 
  then have f1: "resultless_trm E1 E precise_type type"
      using  t_def resultless_trm_trans[of "update_env (precise_type, oldt)  E"]  
        some_min_resless[of "type" "TCst ty" "(precise_type,oldt)" E]
      by  (auto simp add: min_comm[where ?b=" type"])
    then show ?thesis   apply (auto simp add: wty_result_trm_def) subgoal for E'' typ''
        using assms(2)[of E'' typ''] t_def E1_def resless_wty_const[of E'' E typ'' type precise_type oldt]
        by auto subgoal for E'' typ'' using E1_def t_def 
         resless_wty_const_dir2[of "TCst \<circ> E''" E1 typ'' precise_type oldt ] assms(2)
        by auto done
    qed

lemma check_trm_step1: assumes "wty_result_trm t E' type' E1 precise_type"
"half_wty_trm t E1 precise_type E type"
    shows "wty_result_trm t E' type' E type"
  using assms(1,2) resultless_trm_trans[of E'] unfolding half_wty_trm_def apply (auto simp add: wty_result_trm_def) subgoal for E'' typ''
      using resultless_trm_trans[of "TCst \<circ> E''"]  by blast 
    subgoal for E'' typ'' using resultless_trm_trans[of "TCst \<circ> E''"] by auto done

lemma half_wty_trm_trans: assumes 
"half_wty_trm t E' type' E1 type1"
"half_wty_trm  t E1 type1 E type"
shows "half_wty_trm t E' type' E type"
  using assms resultless_trm_trans apply (auto simp add: half_wty_trm_def)
  by blast

lemma check_binop_sound: assumes "\<And>E E' type type' . check_trm E type t1 = Some (E', type') \<Longrightarrow> wty_result_trm t1 E' type' E type"
  "\<And>E E' type type' . check_trm E type t2 = Some (E', type') \<Longrightarrow> wty_result_trm t2 E' type' E type"
  "check_trm E type (trm t1 t2) = Some (E', type')" 
  "trm \<in> {trm.Plus, trm.Minus, trm.Mult, trm.Div } \<and> constr = TNum 0 \<and> E_start = new_type_symbol \<circ> E \<and> type_start = new_type_symbol type \<and> (P = (\<lambda>y.  y \<in> numeric_ty))
 \<or> trm = trm.Mod \<and> constr = TCst TInt \<and> E_start =  E \<and> type_start = type \<and> (P = (\<lambda>y.  y = TInt))"
shows " wty_result_trm (trm t1 t2) E' type' E type"
proof -
  obtain E_constr constr_type where constr_def: "Some (E_constr, constr_type) = clash_propagate2 constr type_start E_start" using assms
    by (auto simp add: check_binop2_def clash_propagate2_def split: option.splits)
  then have constr_int: "constr = TCst TInt \<Longrightarrow> resultless_trm (TCst \<circ> E'') E_constr (TCst typ'') constr_type \<Longrightarrow>
   typ'' = TInt" for E'' typ'' unfolding clash_propagate2_def using         resless_wty_const_dir2[where ?t=TInt and ?typ''=typ'' and ?newt=constr_type and ?E1.0="TCst \<circ> E''" and ?E2.0=E_constr]
    apply (cases "min_type (TCst TInt) type_start") by auto  metis
 obtain E1 t_typ where  E1_def: "Some (E1,t_typ) = check_trm E_constr constr_type t1" using assms   constr_def
   by (auto simp add: check_binop2_def clash_propagate2_def split: option.splits) 
  then have E'_def: "Some (E',type') = check_trm E1 t_typ t2" using assms  constr_def
    by (auto simp add: check_binop2_def clash_propagate2_def split: option.splits)
  have wtynum: "\<And>E'' y. E'' \<turnstile> trm t1 t2 :: y  \<Longrightarrow> P y" using assms(4) by (auto elim: wty_trm.cases) 
  have wty_res2: "wty_result_trm t2 E' type' E1 t_typ" using E'_def assms(2)  by auto
  have wty_res1: "wty_result_trm t1  E1 t_typ E_constr constr_type" using E1_def constr_def assms(1) by auto
  have half_wty: "half_wty_trm  (trm t1 t2) E' type' E type"  apply (rule half_wty_trm_trans[where ?E1.0=E1 and ?type1.0=t_typ]) defer 1
 apply (rule half_wty_trm_trans[where ?E1.0=E_constr and ?type1.0=constr_type]) apply (cases "trm t1 t2")
    using   wty_res1 wty_res2 constr_def wtynum check_trm_step0_cst2 check_trm_step0_num[of E_constr constr_type type E "trm t1 t2"] assms(4)
    by (auto simp add: half_wty_trm_def wty_result_trm_def elim:wty_trm.cases )
  show ?thesis  using  half_wty  wty_res1 wty_res2 apply (auto simp add: half_wty_trm_def wty_result_trm_def ) subgoal for E'' typ''
      apply (cases "trm t1 t2")  using   assms(4) resultless_trm_trans[of "TCst \<circ> E''" E' "TCst typ''" type' E1 t_typ]
        resultless_trm_trans[of "TCst \<circ> E''" E1 "TCst typ''" t_typ E_constr constr_type]
               apply (auto intro!: wty_trm.intros) using check_trm_step0_num(3)  constr_def wtynum apply blast+ 
      using  wty_trm.Mod[where ?E=E'' and ?x=t1 and ?y=t2 ] constr_int[of E'' typ''] by (auto intro: wty_trm.intros)
       done
qed


lemma check_conversion_sound: assumes " \<And>E type  E' type'. check_trm E type t = Some (E', type') \<Longrightarrow> wty_result_trm t E' type' E type"
    "check_trm E type (trm t) = Some (E', type')" "trm = trm.F2i \<and> a = TInt \<and> b = TFloat \<or> trm = trm.I2f \<and> a = TFloat \<and> b = TInt"
  shows "wty_result_trm (trm t) E' type' E type"
proof - 
   obtain E1 precise_type where E1_def: "Some (E1, precise_type) = clash_propagate2 type (TCst a) E" using assms(2,3) by (auto split: option.splits)
  then have prec_int: "precise_type = TCst a" using assms(3) by (cases type) (auto simp add: clash_propagate2_def split: if_splits)
  have type'_def: "type' = TCst a" using assms(2,3) by (auto split: option.splits)
  have type_int: "case type of TCst t \<Rightarrow> t = a | _ \<Rightarrow> True" using E1_def by (cases type)(auto simp add: clash_propagate2_def split: if_splits)
  obtain fl_type where E2_def: "check_trm E1 (TCst b) t = Some (E', fl_type) " using E1_def assms(2,3) by (auto split: option.splits) 
  have wtytrm: "(\<And>E'' y. (E'' \<turnstile> trm t :: y) \<longrightarrow> (y = a))" using assms(3) by (auto elim:wty_trm.cases)
   have half: "half_wty_trm (trm t) E1 precise_type E type" using assms E1_def check_trm_step0_cst2[of E1 precise_type a type E]  
    wtytrm clash_prop_comm by (auto simp add: half_wty_trm_def)  blast+ 
   have wty: "wty_result_trm t E' fl_type E1 (TCst b)"using E2_def assms(3) assms(1)[of E1 "TCst b" E' fl_type] by auto
   then have fl_def: "fl_type = TCst b" unfolding wty_result_trm_def resultless_trm_def wf_f_def by auto
     have E'_less: "tysenvless E' E1"  using wty half resultless_trm_tysenvless
       by (auto simp add: wty_result_trm_def half_wty_trm_def  )
     have typ''_def: "resultless_trm (TCst \<circ> E'') E' (TCst typ'') (TCst a) \<Longrightarrow> typ'' = a" for E'' typ'' using assms(3) 
       unfolding resultless_trm_def wf_f_def by auto 
     have " resultless_trm (TCst \<circ> E'') E (TCst typ'') type \<Longrightarrow>  E'' \<turnstile> trm t :: typ'' \<Longrightarrow>  resultless_trm (TCst \<circ> E'') E1 (TCst b) (TCst b)"
       for  E'' typ'' apply (rule tysenvless_resultless_trm)  
         using half assms(3)   unfolding resultless_trm_def half_wty_trm_def wty_result_trm_def tysenvless_def by (cases typ'') auto  
       then  have  "  E'' \<turnstile> trm t :: typ'' \<Longrightarrow> resultless_trm (TCst \<circ> E'') E (TCst typ'') type \<Longrightarrow>
          (E'' \<turnstile> t :: b) = resultless_trm (TCst \<circ> E'') E' (TCst b) fl_type"
         for E'' typ'' using wty assms(3) unfolding wty_result_trm_def by auto  
       then have sub2:" E'' \<turnstile> trm t :: typ'' \<Longrightarrow> resultless_trm (TCst \<circ> E'') E (TCst typ'') type \<Longrightarrow>
          (E'' \<turnstile> t :: b)  =  resultless_trm (TCst \<circ> E'') E' (TCst typ'') (TCst a)" for E'' typ''
         using tysenvless_resultless_trm[of "TCst \<circ> E''" E' a  "TCst typ''" "TCst a"] assms(3)  unfolding resultless_trm_def tysenvless_def 
         by (auto simp add: fl_def wf_f_def elim: wty_trm.cases)
     have "(\<forall>x. E1 x \<noteq> type) \<or> type = TCst a" using E1_def min_const assms(3) apply (auto simp add: clash_propagate2_def) subgoal for x 
         by (cases "E1 x") (auto simp add: update_env_def split: if_splits)
        subgoal for x 
         by (cases "E1 x") (auto simp add: update_env_def split: if_splits) done
 then have " resultless_trm E' E1 (TCst a) precise_type"  using E'_less
       tysenvless_resultless_trm[of E' E1 a "TCst a" precise_type] wf_f_comp type_int assms(3)
   unfolding type'_def by (cases type) (auto simp add: prec_int wty_result_trm_def half_wty_trm_def numeric_ty_def ) 
  moreover have "resultless_trm E1  E precise_type type" using prec_int half    by (auto simp add: half_wty_trm_def resultless_trm_def) 

  ultimately have " resultless_trm E' E (TCst a) type" by ( rule resultless_trm_trans ) 
  then show ?thesis using E'_less wty wf_f_comp resultless_trm_trans[of ]  assms(3) 
    unfolding type'_def  apply (auto simp add: prec_int wty_result_trm_def half_wty_trm_def ) subgoal for E'' typ''
      using sub2[of E'' typ''] by (auto elim: wty_trm.cases)
    subgoal for E'' typ''  using wty   tysenvless_resultless_trm[of "TCst \<circ> E''" E' b "TCst b" "TCst b"] unfolding wty_result_trm_def
      using typ''_def[of E'' typ''] resultless_trm_tysenvless resultless_trm_trans[of "TCst \<circ> E''"]  by (auto simp add: fl_def intro!: wty_trm.intros) 
    subgoal for E'' typ''
      using sub2[of E'' typ''] by (auto elim: wty_trm.cases)
    subgoal for E'' typ''  using wty   tysenvless_resultless_trm[of "TCst \<circ> E''" E' b "TCst b" "TCst b"] unfolding wty_result_trm_def
      using typ''_def[of E'' typ''] resultless_trm_tysenvless resultless_trm_trans[of "TCst \<circ> E''"]  by (auto simp add: fl_def intro!: wty_trm.intros)
    done
qed

lemma check_trm_sound: " check_trm  E type t = Some (E', type') \<Longrightarrow> wty_result_trm t  E' type' E type"
proof (induction t arbitrary:  E type E' type')                                     
  case (Var x) 
 have  wtyres1: "resultless_trm E' E type' type" apply (rule check_trm_step0_half[where ?t="E x"])using Var by auto
  { assume assm: "type' = type"
      then have E'_def: "E' = update_env (type,E x) E" using Var  apply (auto simp add: clash_propagate2_def)
      using min_consistent by blast
    { fix E'' type'' fa
    assume wty: "E'' \<turnstile> trm.Var x :: type''" and  fa_def: "wf_f fa "   "TCst  \<circ> E'' = fa \<circ> E "  "TCst type'' = fa type"
    let ?g = "(\<lambda>t. if type = t then TCst type'' else fa t)"
    have g1: "wf_f ?g" using   fa_def by (auto simp add: wf_f_def) 
    have "(fa \<circ> E) xa = ((\<lambda>t. if type = t then TCst type'' else fa t) \<circ> (\<lambda>v. if E v = E x then type else E v)) xa " for xa
      using fa_def wty by (auto simp add: comp_def elim!: wty_trm.cases) metis
     then have g2: " TCst  \<circ> E'' = ?g \<circ> E'" using  Var fa_def E'_def by (auto simp add:  update_env_def) 
      have res_less'': "resultless_trm (TCst \<circ> E'') E' (TCst type'') type'"  using g1 g2 fa_def assm by (auto simp add: wf_f_def resultless_trm_def)
    }

    moreover have "resultless_trm (TCst \<circ>  E'') E' (TCst type'') type' \<Longrightarrow> E'' \<turnstile> trm.Var x :: type''" 
      for E'' type'' using E'_def assm     apply (cases type'')
          apply (auto  simp add: resultless_trm_def wf_f_def update_env_def comp_def intro!:wty_trm.intros) 
        by (metis tysym.inject(3))+    
 
      ultimately have ?case  using assm wtyres1  apply (auto simp add:  wty_result_trm_def resultless_trm_def) by metis 
    } moreover {
      assume assm: "type' = E x"
      then have E'_def: "E' = update_env (E x,type) E" using Var  apply (auto simp add: clash_propagate2_def)
      using min_consistent by blast
    { fix E'' type'' fa
    assume wty: "E'' \<turnstile> trm.Var x :: type''" and  fa_def: "wf_f fa "   "TCst  \<circ> E'' = fa \<circ> E "  "TCst type'' = fa type"
    let ?g = "(\<lambda>t. if E x = t then TCst type'' else fa t)"
    have g1: "wf_f ?g" using   fa_def apply (auto simp add: wf_f_def) 
      by (metis comp_eq_dest wty wty_trm.Var wty_trm_cong_aux)+ 
    have " (fa \<circ> E) y = (?g \<circ> (E')) y " for y
      using fa_def wty E'_def by (auto simp add: update_env_def comp_def elim!: wty_trm.cases) metis
     then have g2: " TCst  \<circ> E'' = ?g \<circ> E'" using  E'_def fa_def by auto
      have res_less'': "resultless_trm (TCst \<circ> E'') E' (TCst type'') type'"  using g1 g2 fa_def assm by (auto simp add: wf_f_def resultless_trm_def)
    }
moreover
    {
      fix fa type'' E''
      assume  " TCst type'' = fa type'" "wf_f fa" "TCst \<circ> E'' = fa \<circ> (E')"
      from this have " E'' \<turnstile> trm.Var x :: type''"  using  assm E'_def
          apply (auto  simp add: wf_f_def update_env_def comp_def  intro!:wty_trm.intros ) 
        by (metis tysym.inject(3))
    } 
 ultimately have ?case using assm wtyres1  apply (auto simp add:  wty_result_trm_def resultless_trm_def)  by metis 
    } ultimately show ?case using min_consistent Var by (auto simp add: clash_propagate2_def)
next
  case (Const x)
  show ?case  apply (rule check_trm_step0_cst[where ty="ty_of x"]) 
    using Const wty_trm.Const wty_trm_cong_aux by auto 
next
  case (Plus t1 t2)
  then show ?case by (rule check_binop_sound) auto
next
  case (Minus t1 t2)
  then show ?case  by (rule check_binop_sound) auto
next

  case (UMinus t)
  then obtain E1 precise_type where E1_def: "Some (E1, precise_type) = clash_propagate2 (TNum 0) (new_type_symbol type) (new_type_symbol \<circ> E)" by (auto split: option.splits)
  have wtynum: "\<And> E'' y . E'' \<turnstile> trm.UMinus t :: y \<Longrightarrow> y \<in> numeric_ty" by (auto elim: wty_trm.cases)
  have res_E1_E': "wty_result_trm t E' type' E1 precise_type"  apply  (rule UMinus.IH) using UMinus(2) E1_def by (auto split: option.splits)
  show ?case apply (rule check_trm_step1[where ?E1.0=E1 and ?precise_type=precise_type]) 
    using  res_E1_E' E1_def wtynum check_trm_step0_num[of E1 precise_type type E "trm.UMinus t" ] 
      apply (auto simp add: half_wty_trm_def wty_result_trm_def elim: wty_trm.cases) subgoal for E'' typ'' 
      using check_trm_step0_num(2-3)[of E1 precise_type type E "trm.UMinus t" typ'' E''] resultless_trm_trans[of "TCst \<circ> E''"]
      by (auto  intro: wty_trm.intros) done
next
  case (Mult t1 t2)
  then show ?case by (rule check_binop_sound) auto
next
  case (Div t1 t2)
  then show ?case by (rule check_binop_sound) auto
next
  case (Mod t1 t2)
  then show ?case by (rule check_binop_sound[where ?constr="TCst TInt"]) auto
next
  case (F2i t)
  then show ?case by (rule check_conversion_sound) auto
next
  case (I2f t)
  then show ?case by (rule check_conversion_sound[where ?a=TFloat])  auto
qed 

lemma exists_refinement: "\<exists> E'' typ'' .resultless_trm (TCst \<circ> E'') E (TCst typ'') typ "
  unfolding resultless_trm_def wf_f_def apply auto apply (rule exI[of _ "(\<lambda>x. case E x of  TCst t \<Rightarrow>  t | TNum n \<Rightarrow>  TInt | TAny n \<Rightarrow>  TInt)" ])
  apply (rule exI[of _ "case typ of  TCst t \<Rightarrow>  t | _ \<Rightarrow>  TInt" ]) 
  apply (rule exI[of _ "(\<lambda>x. case x of  TCst t \<Rightarrow>  TCst t | TNum n \<Rightarrow> TCst TInt | TAny n \<Rightarrow>  TCst TInt)"])
  unfolding numeric_ty_def by (auto split: tysym.splits)


lemma exists_coarser: "\<exists> E typ .resultless_trm (TCst \<circ> E'') E (TCst typ'') typ "
  unfolding resultless_trm_def wf_f_def apply auto apply (rule exI[of _ "TCst \<circ> E''" ])
  apply (rule exI[of _ "TCst typ''" ]) 
  apply (rule exI[of _ id]) by (auto)


lemma eq_refinement_min_type: assumes "\<exists> f g . wf_f f \<and> wf_f g \<and> f typ = g typ'"
  shows "\<exists> t1 t2 . min_type typ typ' = Some (t1,t2)"
proof -
  obtain f g where typs: "wf_f f"  "wf_f g" "f typ = g typ'" using assms  by auto
  then show ?thesis unfolding wf_f_def apply (induction "typ" typ' rule: min_type.induct) 
    by (auto  simp add: eq_commute[where ?b=  "g (TAny _)"] eq_commute[where ?b=  "g (TNum _)"] numeric_ty_def 
        split: tysym.splits nat.splits) 
qed


lemma assumes " \<exists> f . wf_f f \<and>  f typ' = typ"
  shows "\<exists> t1 t2 . min_type typ typ' = Some (t1,t2)"
  apply (rule eq_refinement_min_type) using assms apply auto subgoal for f 
     unfolding wf_f_def by (rule exI[of _ id])  auto done

lemma constr_complete: assumes "resultless_trm (TCst \<circ> E'') E (TCst typ'') typ"
  "P typ''" 
  "P = (\<lambda>x. x \<in> numeric_ty) \<and> constr = TNum 0 \<and> E_start = new_type_symbol \<circ> E \<and> type_start = new_type_symbol typ \<and> (P = (\<lambda>y. y \<in> numeric_ty))
 \<or> P = (\<lambda> x. x =  t) \<and> constr = TCst t \<and> E_start =  E \<and> type_start = typ"
  " clash_propagate2 constr type_start E_start = None"
shows False
proof -
  obtain f where f_def: "wf_f f \<and> f typ = TCst typ''" using assms(1) unfolding resultless_trm_def by auto
  have "\<exists> EE tt. min_type  constr type_start = Some(EE,tt)" apply (rule eq_refinement_min_type)
    apply (rule exI[of _ "(\<lambda> x. if x = constr then TCst typ'' else x)"])
    apply (rule exI[of _ "(\<lambda>x.  if x = type_start then f typ else x)"])
    using f_def assms(2,3)   unfolding wf_f_def new_type_symbol_def 
    by (auto simp add:  split: tysym.splits) 
  then show False using assms(4) by (auto simp add: clash_propagate2_def  split: option.splits) 
qed

lemma check_binop_complete: 
  assumes "\<And>E typ E'' typ''. check_trm E typ t1 = None \<Longrightarrow> resultless_trm (TCst \<circ> E'') E (TCst typ'') typ \<Longrightarrow> E'' \<turnstile> t1 :: typ'' \<Longrightarrow> False"
    "\<And>E typ E'' typ''. check_trm E typ t2 = None \<Longrightarrow> resultless_trm (TCst \<circ> E'') E (TCst typ'') typ \<Longrightarrow> E'' \<turnstile> t2 :: typ'' \<Longrightarrow> False"
    "check_trm E typ (trm t1 t2) = None"
    "resultless_trm (TCst \<circ> E'') E (TCst typ'') typ"
    " E'' \<turnstile> trm t1 t2 :: typ''" 
    "trm \<in> {trm.Plus, trm.Minus, trm.Mult, trm.Div } \<and> constr = TNum 0 \<and> E_start = new_type_symbol \<circ> E \<and> type_start = new_type_symbol typ \<and> P = (\<lambda>x. x \<in> numeric_ty)
 \<or> trm = trm.Mod \<and> constr = TCst TInt \<and> E_start =  E \<and> type_start = typ \<and> P = (\<lambda> x. x =  TInt)"
  shows False
proof -
  have "clash_propagate2 constr type_start E_start = None \<Longrightarrow>  False"
    apply (rule constr_complete[where ?t=TInt and ?P=P]) using assms(4-6)  by (auto elim: wty_trm.cases)
    then obtain E1 t_typ where some_cp: " Some(E1, t_typ) = clash_propagate2 constr type_start E_start" by fastforce
    then have half: "half_wty_trm (trm t1 t2) E1 t_typ E  typ "
      unfolding half_wty_trm_def apply (cases "trm t1 t2") using  assms(6) check_trm_step0_num(1-2)[of E1 t_typ " typ" E "trm t1 t2"]
        check_trm_step0_cst2
      by (auto simp add:  elim:wty_trm.cases)  
    then have "resultless_trm (TCst \<circ> E'') E1 (TCst typ'') t_typ" unfolding half_wty_trm_def
      using assms(5,6)  by (auto simp add:  assms(4) elim:wty_trm.cases)
    then have t1_none: " check_trm E1 t_typ t1 = None \<Longrightarrow> False" using assms(1)[of E1 t_typ E'' typ''] assms(5,6)
      by (auto simp add: comp_def elim:wty_trm.cases)
    have half2: "check_trm E1 t_typ t1 = Some(E',type') \<Longrightarrow> half_wty_trm  (trm t1 t2) E' type' E1 t_typ" for E' type'
      apply (rule subterm_half_wty[where ?t=t1]) using check_trm_sound assms(6) unfolding half_wty_trm_def wty_result_trm_def
      by (auto elim: wty_trm.cases) 
    have E'_less: "check_trm E1 t_typ t1 = Some(E',type') \<Longrightarrow> resultless_trm (TCst \<circ> E'') E' (TCst typ'') type'" for E' type'
      using assms(5,6) half_wty_trm_trans[OF half2 half] unfolding half_wty_trm_def 
      by (auto simp add: assms(4) elim: wty_trm.cases) 
    have t2_none: "check_trm E1 t_typ t1 = Some(E',type') \<Longrightarrow> False"  for E' type' 
      apply  (rule assms(2)[of E' type']) using assms(3,5,6) some_cp E'_less
      by (auto simp add: comp_def check_binop2_def split: option.splits elim:wty_trm.cases)
    show False using t1_none t2_none  by fast
  qed

lemma check_conversion_complete: assumes   
  "\<And>E typ E'' typ'' . check_trm E typ t = None \<Longrightarrow> resultless_trm (TCst \<circ> E'') E (TCst typ'') typ \<Longrightarrow> E'' \<turnstile> t :: typ'' \<Longrightarrow> False"
    "check_trm E typ (trm t) = None"
    "resultless_trm (TCst \<circ> E'') E (TCst typ'') typ"
   " E'' \<turnstile> trm t :: typ''"
"trm = trm.F2i \<and> a = TInt \<and> b = TFloat \<or> trm = trm.I2f \<and> a = TFloat \<and> b = TInt"
 shows False
proof -
 have cp_none: "clash_propagate2 typ (TCst a)  E = None \<Longrightarrow> False "
    apply (simp add: clash_prop_comm[where ?t1.0="typ"])
         apply (rule constr_complete[where ?t=a and ?P="(\<lambda>x. x = a)" and ?typ="typ" and ?E''=E'' and ?E=E and ?typ''=typ'']) 
    using  assms(2-5)  by (auto simp add: comp_def elim:wty_trm.cases) 
  then obtain E_constr where constr_def: "clash_propagate2 typ (TCst a)  E = Some (E_constr, TCst a)"
    using clash_propagate2_def min_comm min_const by fastforce
  have  "resultless_trm ( TCst \<circ> E'') E_constr (TCst a) (TCst a)" apply (rule check_trm_step0_cst2(2)[where ?E=E and ?type="typ"]) 
    using constr_def assms(3-5) by (auto simp add: comp_def clash_prop_comm[where ?t1.0="typ"] elim: wty_trm.cases) 
  then have  resless: "resultless_trm ( TCst \<circ> E'') E_constr (TCst b) (TCst b)"
    using tysenvless_resultless_trm[OF resultless_trm_tysenvless] by force 
   have  "check_trm E_constr (TCst b) t = None \<Longrightarrow> False"  apply (rule assms(1)[where ?typ="TCst b"]) using assms(2-5)
      using resless by (auto simp add: comp_def elim: wty_trm.cases) 
  then show False using cp_none assms(2,5) constr_def by (auto simp add: clash_propagate2_def split: option.splits) 
qed

lemma check_trm_complete: " check_trm  E typ t = None \<Longrightarrow> resultless_trm (TCst \<circ> E'') E (TCst typ'') typ \<Longrightarrow> E'' \<turnstile> t :: typ'' \<Longrightarrow> False"
proof (induction t arbitrary:  E "typ" E'' typ'')
  case (Var x)
   have "\<exists> f . wf_f f \<and> TCst (typ'')  = f (E x) \<and> (TCst typ'') = f typ " using Var(2-3) 
    apply (auto simp add: resultless_trm_def comp_def elim!: wty_trm.cases)  by metis
  then show ?case using eq_refinement_min_type[of "E x" "typ"] Var(1) by (auto simp add: clash_propagate2_def) fastforce   
next
  case (Const x)
  then show ?case using eq_refinement_min_type[of "TCst (ty_of x)" "typ"] 
    by (auto simp add: clash_propagate2_def resultless_trm_def wf_f_def elim!: wty_trm.cases ) metis  
next
  case (Plus t1 t2)
 then show ?case by (rule check_binop_complete[where ?trm="trm.Plus"]) (auto simp add: comp_def)
next
case (Minus t1 t2)
  then show ?case by (rule check_binop_complete[where ?trm="trm.Minus"]) (auto simp add: comp_def)
next
  case (UMinus t)
  have "clash_propagate2 (TNum 0) (new_type_symbol typ) (new_type_symbol \<circ> E) = None \<Longrightarrow> False "
         apply (rule constr_complete[where ?t=TInt and ?P="(\<lambda>x. x \<in> numeric_ty)"]) 
    using  UMinus(2-4)  by (auto simp add: comp_def elim: wty_trm.cases) 
  then obtain E_constr constr_type where constr_def: " Some(E_constr, constr_type) = clash_propagate2 (TNum 0) (new_type_symbol typ) (new_type_symbol \<circ> E)"
    by fastforce
  have resless: "resultless_trm (TCst \<circ> E'') E_constr (TCst typ'') constr_type" 
    by (rule check_trm_step0_num(2)[OF constr_def _ UMinus(3) UMinus(4)]) (auto elim:wty_trm.cases) 
  have "check_trm E_constr constr_type t = None " using UMinus(2) constr_def 
  by (auto simp add: eq_commute[where ?a="Some(E_constr, constr_type)"] clash_propagate2_def)
    then show ?case apply (rule UMinus.IH[OF _ resless]) using UMinus(4) by (auto elim: wty_trm.cases)
next
  case (Mult t1 t2)
  then show ?case by (rule check_binop_complete[where ?trm="trm.Mult"]) (auto simp add: comp_def)
next                                 
case (Div t1 t2)
  then show ?case by (rule check_binop_complete[where ?trm="trm.Div"]) (auto simp add: comp_def)
next
  case (Mod t1 t2)
  then show ?case by (rule check_binop_complete[where ?trm="trm.Mod" and ?constr="TCst TInt"]) (auto simp add: comp_def)
next
  case (F2i t)
  then show ?case by (rule check_conversion_complete[where ?trm=trm.F2i]) (auto simp add: comp_def)  
next
  case (I2f t)
  then show ?case by (rule check_conversion_complete[where ?trm=trm.I2f and ?a=TFloat]) (auto simp add: comp_def)  
qed 

definition resultless_f :: "(nat \<Rightarrow> tysym) \<Rightarrow> (nat \<Rightarrow> tysym) \<Rightarrow> tysym Formula.formula \<Rightarrow> tysym Formula.formula \<Rightarrow> (tysym \<Rightarrow> tysym) \<Rightarrow> nat set \<Rightarrow> bool" where
"resultless_f E' E \<phi>' \<phi> f W \<longleftrightarrow> ( wf_f f \<and> (\<forall>x \<in> W.   E' x  = (f \<circ> E) x)  \<and> formula.rel_formula (\<lambda>x y. x = f y) \<phi>' \<phi>)"  


definition resultless :: "(nat \<Rightarrow> tysym) \<Rightarrow> (nat \<Rightarrow> tysym) \<Rightarrow> tysym Formula.formula \<Rightarrow> tysym Formula.formula  \<Rightarrow> nat set \<Rightarrow> bool" where 
"resultless E' E \<phi>' \<phi> W \<longleftrightarrow> (\<exists>f.  wf_f f \<and> (\<forall>x \<in> W.   E' x  = (f \<circ> E) x)  \<and> formula.rel_formula (\<lambda>x y. x = f y) \<phi>' \<phi>)"  

lemma resultless_trans: "resultless_f E'' E' \<phi>'' \<phi>' f' W \<Longrightarrow> resultless_f  E1 E  \<phi>  \<phi> f W \<Longrightarrow> resultless_f E'' E \<phi>'' \<phi> f' W"
  unfolding resultless_f_def apply auto 
  oops
  find_theorems  formula.rel_formula

lemma ex_unary_resless:  "resultless (TCst \<circ> E'') E (formula.map_formula TCst \<phi>'') (formula.Neg \<phi>) (fv \<phi>) \<Longrightarrow>\<exists>\<phi>'. resultless (TCst \<circ> E'') E (formula.map_formula TCst \<phi>') \<phi> (fv \<phi>) \<and> Formula.Neg \<phi>' = \<phi>'' "
  "resultless (TCst \<circ> E'') E (formula.map_formula TCst \<phi>'') (formula.Next n \<phi>) (fv \<phi>) \<Longrightarrow>\<exists>\<phi>'. resultless (TCst \<circ> E'') E (formula.map_formula TCst \<phi>') \<phi> (fv \<phi>) \<and> Formula.Next n \<phi>' = \<phi>'' "
  "resultless (TCst \<circ> E'') E (formula.map_formula TCst \<phi>'') (formula.Prev n \<phi>) (fv \<phi>) \<Longrightarrow>\<exists>\<phi>'. resultless (TCst \<circ> E'') E (formula.map_formula TCst \<phi>') \<phi> (fv \<phi>) \<and> Formula.Prev n \<phi>' = \<phi>'' "  
proof -
  show  "resultless (TCst \<circ> E'') E (formula.map_formula TCst \<phi>'') (formula.Neg \<phi>) (fv \<phi>) \<Longrightarrow>\<exists>\<phi>'. resultless (TCst \<circ> E'') E (formula.map_formula TCst \<phi>') \<phi> (fv \<phi>) \<and> Formula.Neg \<phi>' = \<phi>'' " 
    unfolding resultless_def by (cases \<phi>'')  auto  
  show "resultless (TCst \<circ> E'') E (formula.map_formula TCst \<phi>'') (formula.Next n \<phi>) (fv \<phi>) \<Longrightarrow>\<exists>\<phi>'. resultless (TCst \<circ> E'') E (formula.map_formula TCst \<phi>') \<phi> (fv \<phi>) \<and> Formula.Next n \<phi>' = \<phi>'' "
    unfolding resultless_def by (cases \<phi>'')  auto  
  show "resultless (TCst \<circ> E'') E (formula.map_formula TCst \<phi>'') (formula.Prev n \<phi>) (fv \<phi>) \<Longrightarrow>\<exists>\<phi>'. resultless (TCst \<circ> E'') E (formula.map_formula TCst \<phi>') \<phi> (fv \<phi>) \<and> Formula.Prev n \<phi>' = \<phi>'' "  
    unfolding resultless_def by (cases \<phi>'')  auto  
qed

definition wty_result :: "sig \<Rightarrow> tysenv \<Rightarrow> tysym Formula.formula \<Rightarrow> tysenv \<Rightarrow> tysym Formula.formula \<Rightarrow> (tysym \<Rightarrow> tysym) \<Rightarrow> bool" where
  "wty_result S E' \<phi>' E \<phi> f \<longleftrightarrow> resultless_f E' E \<phi>' \<phi> f (Formula.fv \<phi>) \<and> 
(\<forall>E'' \<phi>'' .  resultless (TCst \<circ> E'') E (Formula.map_formula TCst \<phi>'') \<phi> (Formula.fv \<phi>) \<longrightarrow> (S, E'' \<turnstile> \<phi>'') = resultless (TCst \<circ>  E'') E' (Formula.map_formula TCst \<phi>'') \<phi>' (Formula.fv \<phi>))"

definition wty_result_f :: "sig \<Rightarrow> tysenv \<Rightarrow> tysym Formula.formula  \<Rightarrow> (tysym \<Rightarrow> tysym) \<Rightarrow> bool" where
  "wty_result_f S E \<phi> f \<longleftrightarrow> wf_f f \<and> 
(\<forall>f'' .  wf_f (TCst \<circ> f'') \<longrightarrow> (S, (f''\<circ> E) \<turnstile> (formula.map_formula  f'' \<phi>)) = (\<exists> g. wf_f (TCst \<circ> g) \<and> f'' = g \<circ> f))"

(*
lemma resultless_simple_unary: assumes  "form \<in> {formula.Neg, formula.Next n, formula.Prev n}" (**)shows "resultless E' E \<phi>1 \<phi> \<longleftrightarrow> resultless E' E (form \<phi>1) (form \<phi>)"
  using assms unfolding resultless_def by auto
*)

lemma wty_unary: "form \<in> {formula.Neg, formula.Next n, formula.Prev n} \<Longrightarrow>  wty_result S E' (formula.map_formula f' \<phi>) E \<phi> f' \<Longrightarrow> wty_result S E' (form (formula.map_formula f' \<phi>)) E (form \<phi>) f'"
  unfolding wty_result_def resultless_f_def  apply (auto simp add: ) subgoal for E'' \<phi>''   using ex_unary_resless(1)[where ?E''=E'' and ?E=E and ?\<phi>''=\<phi>'' and ?\<phi>= \<phi>] apply auto  subgoal for \<phi>' 
      apply (drule spec[of _ E'']) by (drule spec[of _ \<phi>'])  (auto simp add: resultless_def elim: wty_formula.cases ) done 
  subgoal for E'' \<phi>''   using  ex_unary_resless[where ?E''=E'' and ?E=E and ?\<phi>''=\<phi>'' and ?\<phi>= \<phi>]
    by auto ( simp add: Neg resultless_def) 
 subgoal for E'' \<phi>''   using ex_unary_resless(2)[where ?E''=E'' and ?E=E and ?\<phi>''=\<phi>'' and ?n=n and ?\<phi>= \<phi>] apply auto  subgoal for \<phi>' 
      apply (drule spec[of _ E'']) by (drule spec[of _ \<phi>'])  (auto simp add: resultless_def elim: wty_formula.cases ) done 
  subgoal for E'' \<phi>''   using  ex_unary_resless(2)[where ?E''=E'' and ?E=E and ?n=n and ?\<phi>''=\<phi>'' and ?\<phi>= \<phi>]
    by auto ( simp add: Next resultless_def) 
 subgoal for E'' \<phi>''   using ex_unary_resless(3)[where ?E''=E'' and ?E=E and ?\<phi>''=\<phi>'' and ?n=n and ?\<phi>= \<phi>] apply auto  subgoal for \<phi>' 
      apply (drule spec[of _ E'']) by (drule spec[of _ \<phi>'])  (auto simp add: resultless_def elim: wty_formula.cases ) done 
  subgoal for E'' \<phi>''   using  ex_unary_resless(3)[where ?E''=E'' and ?E=E and ?n=n and ?\<phi>''=\<phi>'' and ?\<phi>= \<phi>]
    by auto ( simp add: Prev resultless_def) done

(*
lemma subformula_wty: assumes "wty_result S E' \<phi>1' E \<phi>1" "\<And>E'' \<phi>'' . S, E'' \<turnstile> \<phi>1'' \<longleftrightarrow> S, E'' \<turnstile> \<phi>''" shows "wty_result S E' \<phi>' E \<phi> "
  oops
*)

lemma assumes "wf_f (\<lambda>t. foldl (\<lambda>t' n. if  (E n) = t then E1 n else t') t w)" "set w' \<subset> set w" shows "wf_f (\<lambda>t. foldl (\<lambda>t' n. if  (E n) = t then E1 n else t') t w')"
  using assms
  sorry

lemma wf_trm_f_union: assumes "distinct w " "distinct w1" "distinct w2" "set w = set w1 \<union> set w2" shows
"wf_f (\<lambda>t. foldl (\<lambda>t' n. if new_type_symbol (E n) = t then E1 n else t') t w1) \<Longrightarrow>
    wf_f (\<lambda>t. foldl (\<lambda>t' n. if E1 n = t then E2 n else t') t  w2) \<Longrightarrow> wf_f (\<lambda>t. foldl (\<lambda>t' n. if E n = t then E2 n else t') t w)" unfolding trm_f_def
  using assms
proof (induction w arbitrary: w1 w2 )
  case Nil
  then show ?case by auto
next
  case (Cons a w)
  have "wf_f (\<lambda>t. foldl (\<lambda>t' n. if E n = t then E2 n else t') t w)" 
    apply (rule Cons.IH[where ?w1.0="[x \<leftarrow> w1 . x \<noteq> a]" and ?w2.0="[x \<leftarrow> w2 . x \<noteq> a]" ])  using Cons 
         apply (auto simp add: wf_f_def) sorry
  then show ?case sorry
  oops
 
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

lemma resultless_trm_f_resultless_trm: assumes "resultless_trm_f E' E typ' typ  (trm_f E' E W) W" 
  shows " tysenvless E' E"
  using assms unfolding tysenvless_def resultless_trm_f_def trm_f_def apply auto apply (rule exI[of _])
  apply auto apply (rule ext)
  subgoal for n
  proof -
    { assume "\<not>(\<exists>n' \<in> W . E n' = E n)"

    
    }{ assume "(\<exists>n' \<in> W . E n' = E n)"
      then obtain n' where "n' \<in> W \<and> E n' = E n" by auto
    then have "\<forall>n1 \<in> W . E n1 = E n' \<longrightarrow> E' n1 = E' n'"  using assms unfolding resultless_trm_f_def by auto 

    }
      
      
    have "((\<lambda>t. foldl (\<lambda>t' n. if E n = t then E' n else t') t (sorted_list_of_set W)) \<circ> E) n = E' n"
      using trm_f_in_fv
      oops
(*
lemma trm_f_comp: assumes "finite w1" "finite w2" "\<And> n n' . E n = E n' \<Longrightarrow> E1 n = E1 n' " 
  "\<And> n n' . E1 n = E1 n' \<Longrightarrow> E2 n = E2 n' "
  shows "trm_f E2 E ( w1 \<union>  w2) = trm_f E2 E1 w2 \<circ> trm_f E1  E w1" 
apply (rule ext) subgoal for t
  proof -
    have E_E2: "\<And> n n' . E n = E n' \<Longrightarrow> E2 n = E2 n'" using assms(3-4) by blast
    {assume "\<exists>n \<in> w1 \<inter> w2 . E n = t"
      then obtain n where n_def: "n \<in> w1 \<and> n \<in> w2  \<and> E n = t" by auto
      have " foldl (\<lambda>t' n. if E n = t then E2 n else t') t (sorted_list_of_set (w1 \<union> w2)) = E2 n" 
        apply (rule trm_f_in_fv) 
        using n_def  set_sorted_list_of_set[where ?A="w1 \<union> w2"] E_E2 assms(1,2)  by auto
      have p1: "foldl (\<lambda>t' n. if  E n = t then E1 n else t') t (sorted_list_of_set w1) = E1 n"
        apply (rule trm_f_in_fv)
        using n_def set_sorted_list_of_set[OF assms(1)] assms(3) by auto 
        have "n \<in> w2 \<Longrightarrow> trm_f E2 E1 w2  (trm_f E1  E w1 t) = E2 n " unfolding trm_f_def apply (rule trm_f_in_fv)
          using  n_def set_sorted_list_of_set[OF assms(2)] 
            apply blast  using p1 apply auto using  assms(4) by blast
        have E2_1: "trm_f E2 E1 w2  (trm_f E1  E w1 t) = E2 n " unfolding trm_f_def apply (rule trm_f_in_fv)
          using  n_def set_sorted_list_of_set[OF assms(2)] 
            apply blast  using p1 apply auto using  assms(4) by blast
        have ?thesis using
        sorry
      }
      {assume "\<not>(\<exists>n \<in> w1 \<union> w2 . E n = t)"
      
      }
qed
*)

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

lemma[simp]: "Formula.nfv (formula.map_formula f \<psi>) = Formula.nfv \<psi>" unfolding Formula.nfv_def by auto

lemma[simp]: " wf_formula (formula.map_formula f \<psi>) = wf_formula \<psi>" by (induction \<psi>) (auto simp add: list_all_def map_regex_pred)

lemma case_nat_comp: "f'' \<circ> case_nat t E =  case_nat (f'' t) (f'' \<circ> E)" unfolding comp_def by (rule ext) (auto split: nat.splits)

lemma check_binary_sound: assumes 
  "\<And>\<phi>' S E f' . size \<phi>' \<le> size \<phi> + size \<psi> \<Longrightarrow> check S E \<phi>' = Some f' \<Longrightarrow> wf_formula \<phi>' \<Longrightarrow> wty_result_f S E \<phi>' f'"
  "check S E form = Some f'" 
  "wf_formula form" "form \<in> {formula.Or \<phi> \<psi>, formula.And \<phi> \<psi>, formula.Since \<phi> I \<psi>, formula.Until \<phi> I \<psi>}" shows " wty_result_f S E form f'"
proof -
  obtain  f where f_def: "check S E \<phi> = Some  f" using assms by (auto simp add: check_two_formulas_def split: option.splits)
  then  have wty1: " wty_result_f S E \<phi> f"
    using assms by auto
  obtain f1 where  f1_def: "check S (f\<circ>E) (formula.map_formula f \<psi>) = Some  f1 \<and> f' = f1 \<circ> f " using assms(2,4) f_def by (auto simp add: check_two_formulas_def split: option.splits)
  have wty2:" wty_result_f S (f\<circ>E) (formula.map_formula f \<psi>) f1"
    apply (rule assms(1)) using assms(3,4) f1_def by (auto simp add: comp_def)
  show ?thesis using wty1 wty2 unfolding wty_result_f_def using wf_f_comp f1_def
    using assms(4) 
    apply (auto simp add: comp_assoc formula.map_comp
        elim!: wty_formula.cases[where ?a3.0="formula.Or _ _"] wty_formula.cases[where ?a3.0="formula.And _ _"]
        wty_formula.cases[where ?a3.0="formula.Since _ _ _"] wty_formula.cases[where ?a3.0="formula.Until _  _ _"]) 
           apply fastforce apply (auto simp add: o_assoc intro!: wty_formula.intros)
    by (metis (no_types, lifting) comp_assoc)+
qed

lemma[simp]:  "foldl
     (check_ands_f S E \<phi>)
     None \<phi>s = None" unfolding check_ands_f_def by (induction \<phi>s)  auto 
lemma[simp]:  "foldl
     (\<lambda>f_op \<phi>'.
         case f_op of None \<Rightarrow> None
         | Some f \<Rightarrow> (case S E (f \<circ> \<phi>) (formula.map_formula f \<phi>') of None \<Rightarrow> None | Some f' \<Rightarrow> Some (f' \<circ> f)))
     None \<phi>s =
    None"  by (induction \<phi>s)  auto 

(*
lemma check_ands_f_comp_dist: "\<And>g g' a. (check_ands_f S E) (Some (g \<circ> g')) a = Some (g \<circ> (the ((check_ands_f S E) (Some g') a)))"

lemma foldl_fun: assumes "\<And>g g' a. f (g \<circ> g') a = g \<circ> (f g' a)" "f \<noteq> undefined" shows"foldl f (g\<circ>g') xs (x) = foldl f g xs (g' x)" 
  using assms proof (induction xs arbitrary: g' g f)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  have "foldl f (f (\<lambda>a. g (g' a)) a) xs x = foldl f (f g a) xs (g' x)" apply (rule Cons.IH)
  then show ?case apply auto
qed 
*)
lemma check_ands_f_comp: "check_ands_f check S E (Some f) \<phi> = Some f' \<Longrightarrow> \<exists>g. g \<circ>f = f'"
  unfolding check_ands_f_def by (auto split: option.splits)


lemma check_ands_comp: " foldl (check_ands_f check S E) (Some f) \<phi>s= Some f' \<Longrightarrow>  \<exists>g. g \<circ>f = f'"
  unfolding check_ands_def
  apply (induction \<phi>s arbitrary: f' f E )
  apply auto
  using fun.map_id apply blast subgoal for \<phi> \<phi>s f' f E 
  apply (cases "check_ands_f check S E (Some f) \<phi>") apply auto   unfolding check_ands_f_def 
      apply (auto simp add: formula.map_id split: option.splits) 
        by fastforce
      done


lemma wty_formula_ands_snoc: "S,E \<turnstile> Formula.Ands (\<phi>s @ [\<phi>]) \<Longrightarrow> S,E \<turnstile> (Formula.Ands \<phi>s)"
by (auto elim!: wty_formula.cases[of _ _ "Formula.Ands _"]intro!: wty_formula.intros)

lemma check_ands_sound: assumes "(\<And>\<phi>' Sa Ea f'.
        size \<phi>' \<le> size_list size \<phi>s \<Longrightarrow> check Sa Ea \<phi>' = Some f' \<Longrightarrow> wf_formula \<phi>' \<Longrightarrow> wty_result_f Sa Ea \<phi>' f')"
  "foldl (check_ands_f check S E) (Some id) \<phi>s = Some f'"
  "list_all wf_formula \<phi>s" shows " wty_result_f S  E (formula.Ands \<phi>s) f'"
  using assms  proof (induction \<phi>s arbitrary: E f'  rule: rev_induct)
  case Nil
  then show ?case by (auto simp add: comp_def wty_result_f_def intro: wty_formula.intros split: option.splits)
      (simp add: wf_f_def)
next
  case (snoc a \<phi>s) 
  have "\<exists>f. foldl (check_ands_f check S E) (Some id) \<phi>s = Some f" using snoc(3)
    unfolding check_ands_def check_ands_f_def by (auto simp: id_simps(1) split: option.splits)
  then obtain f where f_def: "foldl (check_ands_f check S E) (Some id) \<phi>s = Some f" by auto
  then have "\<exists>fa. Some fa =check S (f \<circ> E) (formula.map_formula f a)" using snoc(3) unfolding check_ands_def
      check_ands_f_def
    by (auto simp: id_simps(1) split: option.splits) 
  then obtain fa where fa_def: "Some fa =check S (f \<circ> E) (formula.map_formula f a)" by auto
  then  have f'_comp:"f' = fa \<circ> f" using snoc(3) f_def unfolding check_ands_f_def
    by (auto simp: id_simps(1) split: option.splits) 
  have wty_fa: "wty_result_f S (f \<circ>E) (formula.map_formula f a) fa" apply (rule snoc(2)) using fa_def snoc(4)
    by (auto simp add: comp_def)
  have wty_f: "wty_result_f S E (formula.Ands \<phi>s) f" apply (rule snoc.IH) using snoc f_def by (auto simp: id_simps(1))
  then show ?case using Cons wty_fa f'_comp wf_f_comp unfolding wty_result_f_def
    apply auto 
    subgoal for f''
      using wty_formula_ands_snoc[of S "f'' \<circ> E" " map (formula.map_formula f'') \<phi>s" "formula.map_formula f'' a"]
      by (auto simp add: o_assoc formula.map_comp 
          elim!:wty_formula.cases[of _ _ "Formula.Ands _"] intro!: wty_formula.intros) 
    apply (auto simp add: formula.map_comp o_assoc intro!: wty_formula.intros ) 
     apply blast
    subgoal for g x apply (drule spec[of _ "g \<circ> fa \<circ> f"]  ) using wf_f_comp 
      apply (auto simp add: fun.map_comp   elim: wty_formula.cases)
      by (drule spec[of "(\<lambda>ga. wf_f (TCst \<circ> ga) \<longrightarrow> g \<circ> fa \<circ> f \<noteq> ga \<circ> f)" " g \<circ> fa" ])  (auto simp add: o_assoc)
    done
qed 

lemma wf_resultless_trm: "wf_f (TCst \<circ> f'') \<Longrightarrow> resultless_trm (TCst \<circ> (f'' \<circ> E)) E (TCst (f'' t)) t" 
  unfolding resultless_trm_def by (auto simp add: o_assoc)

lemma basecase_helper: assumes "wf_f (TCst \<circ> f'')" shows" \<exists>g. wf_f (TCst \<circ> g) \<and> f'' = g \<circ> f'"
proof -
  have f2: "\<forall>n f na. TAny n \<noteq> (TCst \<circ> f) (na::nat)"
    by simp
  have "\<forall>E E' n. resultless_trm (TCst \<circ> f'' \<circ> E) E ((TCst \<circ> (f'' \<circ> E')) n) (E' n)"
    using assms resultless_trm_def by force
  then show ?thesis
    using f2 by (metis finite_fvi_trm resultless_trm_f_correct resultless_trm_f_def trm_f_id)
qed

lemma "False"
proof -
  define f'' where f''_def: "f'' = (\<lambda>x .case x of TAny _ \<Rightarrow> TInt | TNum n \<Rightarrow> TInt | TCst t \<Rightarrow> t)"
  define f' :: "tysym \<Rightarrow> tysym" where f'_def: "f' =  (\<lambda>x . TCst TFloat)"
  have wf_f'': "wf_f (TCst \<circ> f'')" unfolding wf_f_def f''_def numeric_ty_def by auto
  obtain g where  g_def: "wf_f (TCst \<circ> g) \<and> f'' = g \<circ> f'" using basecase_helper[OF wf_f''] by (auto simp add: f''_def f'_def)
  then have "f'' x = g (f' x)" for x by auto
  from this[of "TCst TInt"] have False using g_def unfolding wf_f_def f''_def sorry
  oops

lemma check_comparison_sound:
  assumes " check_comparison E x1 x2 = Some f'" 
    "form = Formula.Eq \<and> form_ty = Formula.Eq \<or> form = Formula.Less \<and> form_ty = Formula.Less \<or> form = Formula.LessEq \<and> form_ty = Formula.LessEq"
  shows " wty_result_f S E (form x1 x2) f'"
proof - find_theorems tysenvless
  obtain E1 t1 where E1_def: "check_trm (new_type_symbol \<circ> E) (TAny 0) x1 =  Some (E1,t1)" using assms 
    by (auto simp add: check_comparison_def split: option.splits)
  then obtain E2 t2 where E2_def: "check_trm E1 t1 x2 = Some (E2, t2)" using assms
    by (auto simp add: check_comparison_def split: option.splits)
  have wty1: "wty_result_trm x1 E1 t1 (new_type_symbol \<circ> E) (TAny 0)" apply (rule check_trm_sound) using E1_def by auto
  have wty2: "wty_result_trm x2 E2 t2 E1 t1" apply (rule check_trm_sound) using  E2_def by auto
  have f'_def: "f' = trm_f E2 E (fv_trm x1 \<union> fv_trm x2)" using E2_def E1_def assms by (auto simp add: check_comparison_def split: option.splits)
  have  "resultless_trm_f E2 E (TCst TInt) (TCst TInt) f' (fv_trm x1 \<union> fv_trm x2)" unfolding f'_def
    apply (rule resultless_trm_f_correct[OF  resultless_trm_trans[where ?E'=E1 and ?type'="TCst TInt"]]) 
     apply (rule tysenvless_resultless_trm[OF  resultless_trm_tysenvless[where ?t=t2 and t'=t1]]) 
    using wty2 unfolding wty_result_trm_def apply auto 
    apply (rule tysenvless_resultless_trm[OF tysenvless_trans[OF resultless_trm_tysenvless[where ?t=t1 and ?t'="TAny 0"]]])
    using wty1 unfolding wty_result_trm_def apply (auto split: tysym.splits ty.splits)
    using resless_newtype(1) resultless_trm_tysenvless by blast 
  then have wf_f':"wf_f f'" unfolding resultless_trm_f_def by auto
  have "resultless_trm E2 (new_type_symbol \<circ> E) ( t2) (TAny 0)" 
    apply (rule resultless_trm_trans[where ?E'=E1 and ?type'="t1"]) using wty1 wty2 unfolding wty_result_f_def wty_result_trm_def  
    by auto 
  show "wty_result_f S E (form x1 x2) f'" using wty1 wf_f' wty2
    unfolding wty_result_f_def wty_result_trm_def 
    apply auto 
    subgoal for f'' 
    proof -
      assume a1: "wf_f (TCst \<circ> f'')"
      have f2: "\<forall>n f na. TAny n \<noteq> (TCst \<circ> f) (na::nat)"
        by simp
      have "\<forall>E E' n. resultless_trm (TCst \<circ> f'' \<circ> E) E ((TCst \<circ> (f'' \<circ> E')) n) (E' n)"
        using a1 resultless_trm_def by force
      then show ?thesis
        using f2 by (metis finite_fvi_trm resultless_trm_f_correct resultless_trm_f_def trm_f_id)
    qed subgoal for g
    proof -
      assume a1: "wf_f (TCst \<circ> g)"
      have f2: "\<forall>n f na. TAny n \<noteq> (TCst \<circ> f) (na::nat)"
        by simp
      have "\<forall>f fa n. resultless_trm (TCst \<circ> g \<circ> (f::nat \<Rightarrow> tysym)) f ((TCst \<circ> (g \<circ> fa)) (n::nat)) (fa n)"
        using a1 resultless_trm_def by fastforce
      then show ?thesis
        using f2 by (metis (no_types) finite_fvi_trm resultless_trm_f_correct resultless_trm_f_def trm_f_id)
    qed
    done 
qed

lemma finite_bound_vars[simp]: "finite (formula.set_formula \<phi>)" by (induction \<phi>)  auto


lemma E_empty_resultless_f: assumes "wf_f (TCst \<circ>f)" "S,E \<turnstile> formula.map_formula f \<phi>"
  shows  " \<exists>f''. wf_f (TCst \<circ> f'') \<and> (S, f'' \<circ> (E_empty \<phi>) \<turnstile> formula.map_formula f'' \<phi>)"
  apply (rule exI[of _ "(\<lambda>t. case t of TAny n \<Rightarrow> if n \<le> highest_bound_TAny \<phi> then f t else  E (n - highest_bound_TAny \<phi>  - 1 ) | _ \<Rightarrow> f t)"])
proof -
  define g where g_def: "g = (\<lambda>t. case t of TAny n \<Rightarrow> if n \<le> highest_bound_TAny \<phi> then f t else  E (n - highest_bound_TAny \<phi>  - 1 ) | _ \<Rightarrow> f t)"
  have wf: "wf_f (TCst \<circ> g)" using assms(1)
    unfolding highest_bound_TAny_def wf_f_def g_def  by auto
  have fv_same: "\<And>y. y \<in> fv (formula.map_formula g \<phi>) \<Longrightarrow> E y =  (g \<circ> (E_empty \<phi>)) y" 
    using g_def  unfolding E_empty_def by auto
  have inset: "TAny n \<in> formula.set_formula \<phi> \<Longrightarrow> n \<in> (\<lambda>t. case t of TAny n \<Rightarrow> n | _ \<Rightarrow> 0) ` formula.set_formula \<phi>" for n
    using image_iff by fastforce
  then have "t \<in> formula.set_formula \<phi> \<Longrightarrow> f t = 
     g t" for t
    unfolding highest_bound_TAny_def g_def by (auto split: tysym.splits)
  then have map_eq: "formula.map_formula f \<phi> = formula.map_formula g \<phi>" by (rule formula.map_cong0)  auto
  have "(S, E \<turnstile> formula.map_formula g \<phi>) = (S, g \<circ> (E_empty \<phi>) \<turnstile> formula.map_formula g \<phi>)"
    by (rule wty_formula_fv_cong[OF fv_same])
   then show "wf_f
     (TCst \<circ>
      (\<lambda>t. case t of TAny n \<Rightarrow> if n \<le> highest_bound_TAny \<phi> then f t else E (n - highest_bound_TAny \<phi> - 1) | _ \<Rightarrow> f t)) \<and>
    S, (\<lambda>t. case t of TAny n \<Rightarrow> if n \<le> highest_bound_TAny \<phi> then f t else E (n - highest_bound_TAny \<phi> - 1) | _ \<Rightarrow> f t) \<circ>
       (E_empty \<phi>)
    \<turnstile> formula.map_formula
        (\<lambda>t. case t of TAny n \<Rightarrow> if n \<le> highest_bound_TAny \<phi> then f t else E (n - highest_bound_TAny \<phi> - 1) | _ \<Rightarrow> f t) \<phi>"
     using wf assms(2)  by (auto simp add: E_empty_def map_eq g_def ) 
  qed 

definition pred_wty_result_f where
"pred_wty_result_f E' E ts tys f \<equiv> wf_f f \<and> tysenvless E' E \<and>
(\<forall>f'' .  wf_f (TCst \<circ> f'') \<longrightarrow> (list_all2 (\<lambda>tm ty. f'' \<circ> E \<turnstile> tm :: ty) ts (map (\<lambda>t. case t of TCst t' \<Rightarrow> t') tys)) = (\<exists> g. wf_f (TCst \<circ> g) \<and> f'' = g \<circ> f)) "

lemma check_pred_sound: assumes  "check_pred  E ts tys = Some E'" "\<forall>t \<in> set tys . case t of TCst _ \<Rightarrow> True | _ \<Rightarrow> False" 
  shows "pred_wty_result_f E' E ts tys (trm_f E' E (\<Union> (fv_trm ` set ts)))"
(*"list_all2 (\<lambda>tm ty. E \<turnstile> tm :: ty) tms tys"*)
  using assms
proof (induction E ts tys  arbitrary: E' rule: check_pred.induct)
  case (1 E t ts ty tys)
  then obtain E1 ret_t where E1_def: " check_trm E ty t = Some (E1, ret_t)" by (auto split: option.splits)
   define f' where f'_def: "f' = (trm_f E' E (\<Union> (fv_trm ` set (t#ts))))" 
   have wty:"wty_result_trm t E1 ret_t E ty" using E1_def by (rule check_trm_sound)
  then have "resultless_trm_f E1 E ret_t ty (trm_f E1 E (fv_trm t)) (fv_trm t)" 
    unfolding wty_result_trm_def using resultless_trm_f_correct  by auto
   have pred_wty:" pred_wty_result_f  E' E1 ts tys (trm_f E' E1 (\<Union> (fv_trm ` set ts)))" apply (rule 1(1))
     using E1_def 1 by (auto split: option.splits tysym.splits) 
   then have tysenv: "tysenvless E' E1" unfolding pred_wty_result_f_def tysenvless_def  by auto 
   have "resultless_trm_f E' E  (TCst TInt) (TCst TInt) f' (\<Union> (fv_trm ` set (t#ts)))"
     unfolding f'_def
     apply (rule resultless_trm_f_correct[OF tysenvless_resultless_trm[OF tysenvless_trans[where ?E'=E1]]]) 
     using wty tysenv resultless_trm_tysenvless
     unfolding  wty_result_trm_def by auto 

   then have wf:"wf_f f'" unfolding resultless_trm_f_def by simp
   have "wf_f (TCst \<circ> f'') \<Longrightarrow>
    f'' \<circ> E \<turnstile> t :: (case ty of TCst t' \<Rightarrow> t') \<Longrightarrow>
    list_all2 (wty_trm (f'' \<circ> E)) ts (map (case_tysym (\<lambda>a. undefined) (\<lambda>a. undefined) (\<lambda>t'. t')) tys)
    \<Longrightarrow> \<exists>g. wf_f (TCst \<circ> g) \<and> f'' = g \<circ> trm_f E' E (fv_trm t \<union> \<Union> (fv_trm ` set ts))" for f''
     using wty pred_wty unfolding  wty_result_trm_def apply auto apply (drule spec[of _ "f'' \<circ> E"])
     apply (drule spec[of _ "f''  ty"]) using wf_resultless_trm[of f'' E ty ]
     apply auto 
     subgoal unfolding pred_wty_result_f_def 
       apply (auto simp add: resultless_trm_def[where ?E'="(TCst \<circ> (f'' \<circ> E))" and ?E=E]) 
       sorry
     apply (cases ty) using 1(3) apply auto unfolding wf_f_def by auto
     sorry
    show ?case using wf pred_wty wty tysenvless_trans[OF tysenv resultless_trm_tysenvless[where ?E'=E and ?t=ret_t and ?t'=ty]]
     unfolding pred_wty_result_f_def wty_result_trm_def wty_result_f_def  apply (simp add: f'_def)
     apply auto subgoal for f''   sorry

qed (auto simp add: pred_wty_result_f_def trm_f_def id_simps(1) intro: wty_formula.intros)

lemma check_sound: "check S E \<phi> = Some f'  \<Longrightarrow> wf_formula \<phi>  \<Longrightarrow> wty_result_f S E \<phi> f'"
(*\<and> (\<forall>t . t \<notin>  formula.set_formula \<phi> \<and> \<not>( \<exists>x \<in> fv \<phi>. t = E x) \<longrightarrow> f t = f' t)
\<and> (\<forall>t. \<forall>x \<in> fv \<phi> . f t = (E x) \<longrightarrow> f' t = f' (E x)  )
 \<and> (\<forall>t. f' t = f' (f t)) *)
  proof (induction S E \<phi> arbitrary: f' rule:  check.induct)
    case (1 S E r ts)
    then show ?case apply (auto) sorry
  next find_theorems fv wty_formula
    case (2 S E p \<phi> \<psi>)   
    then obtain f where f_def: "Some f = check S (E_empty \<phi>) \<phi> " by (auto split: option.splits)
    then have wty1: "wty_result_f S (E_empty \<phi>) \<phi> f " using 2(1,4) by auto
    have "\<forall>x\<in>fv \<phi>. case f (E x) of TCst x \<Rightarrow> True | _ \<Rightarrow> False" using 2(3) f_def by (auto split: option.splits if_splits)
    then have "  wf_f (TCst \<circ> f'') \<Longrightarrow> S, E' \<turnstile> formula.map_formula f'' \<phi> \<Longrightarrow> (\<forall> x \<in> fv \<phi> .(\<lambda>x. case f (E x) of TCst t \<Rightarrow> t) x = E' x)" for E' f'' 
      using wty1   unfolding wty_result_f_def   E_empty_def highest_bound_TAny_def apply (auto split: tysym.splits) 
      using comp_apply comp_assoc 
    sorry 
    find_theorems tabulate
     have "wty_result_f (S(p \<mapsto> tabulate (\<lambda>x. case f (E x) of TCst t \<Rightarrow> t) 0 (Formula.nfv \<phi>))) E \<psi> f'"
       apply (rule 2(2)[of f]) using f_def 2 
          by (auto simp add: fun_upd_def split: option.splits if_splits) 
        then show ?case using wty1 unfolding wty_result_f_def
          apply (auto  elim!: wty_formula.cases[of _ _ "Formula.Let _ _ _"] intro!: wty_formula.intros)
          subgoal for f'' E'
            using E_empty_resultless_f[of f'' S E' \<phi> ] apply auto 
            subgoal for g
          sorry
        next
    case (3 S E x1 x2) 
    then show ?case using check_comparison_sound[where ?form=Formula.Eq and ?form_ty=Formula.Eq] by auto
  next
    case (4 S E t1 t2)
    then show ?case using check_comparison_sound[where ?form=Formula.Less and ?form_ty=Formula.Less] by auto
  next
    case (5 S E t1 t2)
    then show ?case using check_comparison_sound[where ?form=Formula.LessEq and ?form_ty=Formula.LessEq] by auto
  next
    case (6 S E \<phi>)
   then have "wty_result_f S E \<phi> f'" by auto
  then show ?case   unfolding wty_result_f_def by (auto intro: wty_formula.intros elim: wty_formula.cases)
next

    case (7 S E \<phi> \<psi>)
  then obtain  f where f_def: "check S E \<phi> = Some  f" by (auto simp add: check_two_formulas_def split: option.splits)
  then  have wty1: " wty_result_f S E  \<phi> f"
    using 7(1) 7(3) by auto
  obtain f1 where  f1_def: "check S (f\<circ>E) (formula.map_formula f \<psi>) = Some  f1 \<and> f' = f1 \<circ> f " using 7(2) f_def by (auto simp add: check_two_formulas_def split: option.splits)
   have wty2:" wty_result_f S (f\<circ>E) (formula.map_formula f \<psi>) f1"
    apply (rule 7(1)) using 7(3) f1_def by (auto simp add: comp_def)
   show ?case using wty1 wty2 unfolding wty_result_f_def using wf_f_comp f1_def
     apply (auto simp add: comp_assoc formula.map_comp elim!: wty_formula.cases[of _ _ "formula.Or _ _"]) 
      apply fastforce apply (auto simp add: o_assoc intro!: wty_formula.intros(7)) 
     subgoal for g apply (rule exI[of _ "g \<circ> f1"])
       by (auto  simp add: o_assoc) done
 next 
    case (8 S E \<phi> \<psi>)
    then show ?case by (rule check_binary_sound) auto 
  next
    case (9 S E \<phi>s)
    then show ?case using check_ands_sound by (auto simp add: check_ands_def ) 
  next
    case (10 S E t \<phi>)
    then show ?case unfolding wty_result_f_def
   by (auto simp add: case_nat_comp intro!: wty_formula.intros(10) elim!: wty_formula.cases[of _ _ "formula.Exists _ _"])
  next
    case (11 S E y agg_type d tys trm \<phi>)
    then obtain E' trm_type where 
      "Some (E', trm_type) = check_trm (new_type_symbol \<circ> agg_tysenv E tys) (agg_trm_tysym agg_type) trm"
      by (auto split: option.splits)
    then obtain f where "Some f = check S E' (formula.map_formula (trm_f E' E (fv_trm trm)) \<phi>)"
      using 11(2) by (auto split: option.splits)
     show ?case using 11 unfolding wty_result_f_def apply auto sorry
  next
    case (12 S E I \<phi>)
     then have "wty_result_f S E \<phi> f'" by auto
  then show ?case   unfolding wty_result_f_def by (auto intro: wty_formula.intros elim: wty_formula.cases)
  next
    case (13 S E I \<phi>)
  then have "wty_result_f S E \<phi> f'" by auto
  then show ?case   unfolding wty_result_f_def by (auto intro: wty_formula.intros elim: wty_formula.cases) 
next
    case (14 S E \<phi> I \<psi>)
    then show ?case by (rule check_binary_sound) auto 
  next
    case (15 S E \<phi> I \<psi>)
    then show ?case by (rule check_binary_sound) auto 
  next
    case (16 S E I r)
    then show ?case sorry
  next
    case (17 S E I r)
    then show ?case sorry
  qed

(*
    case (Pred x1 x2)
  then show ?case sorry
next
  case (Let x1 \<phi>1 \<phi>2)
  then show ?case sorry
next
  find_theorems resultless_trm_f
  case (Eq x1 x2)
  then obtain E1 t1 where E1_def: "check_trm (new_type_symbol \<circ> E) (TAny 0) x1 =  Some (E1,t1)" by (auto simp add: check_comparison_def split: option.splits)
  then obtain E2 t2 where E2_def: "check_trm E1 t1 x2 = Some (E2, t2)" using Eq(1) by (auto simp add: check_comparison_def split: option.splits)
  have wty1: "wty_result_trm x1 E1 t1 (new_type_symbol \<circ> E) (TAny 0)" apply (rule check_trm_sound) using E1_def by auto
  have wty2: "wty_result_trm x2 E2 t2 E1 t1" apply (rule check_trm_sound) using  E2_def by auto
  have "resultless_trm_f E1 (new_type_symbol \<circ> E) t1 (TAny 0) (trm_f E1 (new_type_symbol \<circ> E) (fv_trm x1))  (fv_trm x1)" apply (rule resultless_trm_f_correct)
    using wty1 unfolding wty_result_trm_def by auto
  then have wf1: "wf_f (trm_f E1 (new_type_symbol \<circ> E) (fv_trm x1))" unfolding resultless_trm_f_def by auto
   have "resultless_trm_f E2 E1 t2 t1 (trm_f E2 E1 (fv_trm x2))  (fv_trm x2)" apply (rule resultless_trm_f_correct)
    using wty2 unfolding wty_result_trm_def by auto
  then have wf2: "wf_f (trm_f E2 E1 (fv_trm x2))" unfolding resultless_trm_f_def by auto
  have f'_def: "f' = trm_f E2 E (fv_trm x1 \<union> fv_trm x2)" using E2_def E1_def Eq(1) by (auto simp add: check_comparison_def split: option.splits)
  have "f' = (trm_f E1 (new_type_symbol \<circ> E) (fv_trm x1)) \<circ>(trm_f E2 E1 (fv_trm x2))" 
  have "wf_f f'" apply (simp add: f'_def trm_f_def) 
    apply (rule wf_trm_f_union[where ?w1.0="sorted_list_of_set (fv_trm x1)" and ?w2.0="sorted_list_of_set (fv_trm x2)" and ?E1.0=E1]) 
    using wf1 wf2 unfolding trm_f_def by auto
  then have "wty_result_f S E (formula.Eq x1 x2) f'" using wty1 wty2 unfolding wty_result_f_def wty_result_trm_def  apply (auto ) subgoal for f'' 
      apply (drule spec[of _ "f''\<circ>E"] )  apply (drule spec[of _ "f'' t1"] ) 
   show ?case using Eq apply (auto simp add: check_comparison_def split: option.splits)
  next
case (Less x1 x2)
  then show ?case sorry
next
  case (LessEq x1 x2)
  then show ?case sorry
next
  case (Neg \<phi>)
  then have "wty_result_f S E \<phi> f'" by auto
  then show ?case   unfolding wty_result_f_def by (auto intro: wty_formula.intros elim: wty_formula.cases)
next
  case (Or \<phi>1 \<phi>2)
  then obtain  f where f_def: "check S E \<phi>1 = Some  f" by (auto simp add: check_two_formulas_def split: option.splits)
  then  have " wty_result_f S E  \<phi>1 f"
    apply (rule Or.IH) using Or(4) by auto
  obtain f1 where  "check S (f\<circ>E) (formula.map_formula f \<phi>2) = Some  f1 \<and> f' = f1 \<circ> f " using Or(3) f_def by (auto simp add: check_two_formulas_def split: option.splits)
  then have " wty_result_f S (f\<circ>E) (formula.map_formula f \<phi>2) f1"
    apply (rule Or.IH) using Or(4) by auto
    then show ?case apply (auto simp add: check_two_formulas_def) sorry
next
  case (And \<phi>1 \<phi>2)
  then show ?case sorry
next
  case (Ands x)
  then show ?case sorry
next
  case (Exists x1 \<phi>)
  then show ?case sorry
next
  case (Agg x1 x2 x3 x4 \<phi>)
  then show ?case sorry
next
  case (Prev x1 \<phi>)
  then have "wty_result_f S E \<phi> f'" by auto
  then show ?case   unfolding wty_result_f_def by (auto intro: wty_formula.intros elim: wty_formula.cases)
next
  case (Next x1 \<phi>)
  then have "wty_result_f S E \<phi> f'" by auto
  then show ?case   unfolding wty_result_f_def by (auto intro: wty_formula.intros elim: wty_formula.cases)
next
  case (Since \<phi>1 x2 \<phi>2)
  then show ?case sorry
next
  case (Until \<phi>1 x2 \<phi>2)
  then show ?case sorry
next
  case (MatchF x1 x2)
  then show ?case sorry
next
  case (MatchP x1 x2)
  then show ?case sorry
qed
*)
(*
  case (Neg \<phi>)
  have eq: " S,E'' \<turnstile> \<phi>'' \<longleftrightarrow> S,E'' \<turnstile> (formula.Neg \<phi>'')" for E'' \<phi>'' by (auto elim:wty_formula.cases intro: wty_formula.intros)
  obtain \<phi>1 where \<phi>1_def:"check S E \<phi> = Some (E', \<phi>1)" using Neg(2) by (auto split: option.splits) 
  then have  wty: "wty_result S E' \<phi>1 E \<phi>" apply (rule Neg(1)) using Neg(3) by auto
  have \<phi>'_def: "\<phi>' = formula.Neg \<phi>1" using \<phi>1_def Neg(2) by auto
  have  ex_sub: "resultless (TCst \<circ> E'') E (formula.map_formula TCst \<phi>'') (formula.Neg \<phi>) \<Longrightarrow> (\<exists> \<phi>'''.   \<phi>'' =  formula.Neg  \<phi>''')" for E'' \<phi>''
    unfolding resultless_def apply auto subgoal for f apply (rule  rel_funE[of " formula.rel_formula (\<lambda>x y. x = f y)" " (=)" formula.is_Neg formula.is_Neg]) using
        formula.disc_transfer(6) apply auto by (cases \<phi>'') auto done
  show ?case using wty resultless_simple_unary  unfolding wty_result_def    apply (auto simp add:  \<phi>'_def)  
      apply blast subgoal for E'' \<phi>''  using ex_sub[of E'' \<phi>''] eq by auto metis subgoal for E'' \<phi>'' using ex_sub[of E'' \<phi>''] 
      by auto (metis wty_formula.Neg) done

next
  case (Or \<phi>1 \<phi>2)
  have "S,E'' \<turnstile> \<phi>1' \<and> S,E'' \<turnstile> \<phi>2' \<longleftrightarrow> S,E'' \<turnstile> (formula.Or \<phi>1' \<phi>2') " for E'' \<phi>1' \<phi>2' by (auto elim: wty_formula.cases intro: wty_formula.intros)
   obtain E1 \<phi>1' where E1_def: "check S E \<phi>1 = Some (E1, \<phi>1')" using Or(3) by (auto simp add: check_two_formulas_def split: option.splits) 
   then obtain \<phi>2' where E2_def: "check S E1 \<phi>2 = Some (E', \<phi>2')" using Or(3) by (auto simp add: check_two_formulas_def split: option.splits) 
   have wty1: "wty_result S E1 \<phi>1' E \<phi>1 " apply (rule  Or(1)) using E1_def Or(4) by auto
   have wty2: "wty_result S E' \<phi>2' E1 \<phi>2 " apply (rule  Or(2)) using E2_def Or(4) by auto
   have \<phi>'_def: "\<phi>' = formula.Or \<phi>1' \<phi>2'" using Or(3) E1_def E2_def by (auto simp add: check_two_formulas_def)
   show ?case using wty1 wty2 resultless_trans[of E' E1 \<phi>1']  unfolding wty_result_def \<phi>'_def apply auto sorry
next
*)


(*
lemma check_safe_sound: "safe_formula \<phi> \<Longrightarrow> check_safe S \<phi> = Some (E', \<phi>') \<Longrightarrow>
  wty_formula S E' \<phi>' \<and> formula.rel_formula (\<lambda>_ _. True) \<phi> \<phi>'"
  sorry (* using check_sound[of S Map.empty "formula.map_formula Map.empty \<phi>" E' \<phi>']
  by (auto simp: check_safe_def wty_result_def formula.rel_map)
*) *)
lemma check_complete: "check S E \<phi> = None \<Longrightarrow> wf_formula \<phi> \<Longrightarrow> resultless (TCst \<circ> E') E (Formula.map_formula TCst \<phi>') \<phi> (Formula.fv \<phi>) \<Longrightarrow> S, E' \<turnstile> \<phi>' \<Longrightarrow>
   False"
  sorry

lemma rel_regex_mono_trans:
  "regex.rel_regex (\<lambda>a b. \<forall>x. R a x \<longrightarrow> R' b x) x y \<Longrightarrow> regex.rel_regex R x z \<Longrightarrow> regex.rel_regex R' y z"
proof (induction x y arbitrary: z rule: regex.rel_induct)
  case (Skip a1 b1)
  then show ?case
    by (cases z) auto
next
  case (Test a2 b2)
  then show ?case
    by (cases z) auto
next
  case (Plus a31 a32 b31 b32)
  then show ?case
    by (cases z) auto
next
  case (Times a41 a42 b41 b42)
  then show ?case
    by (cases z) auto
next
  case (Star a5 b5)
  then show ?case
    by (cases z) auto
qed

lemma rel_formula_trans:
  assumes Rtrans: "\<And>x y z. R x y \<Longrightarrow> R x z \<Longrightarrow> R' y z"
  shows "formula.rel_formula R x y \<Longrightarrow> formula.rel_formula R x z \<Longrightarrow> formula.rel_formula R' y z"
proof (induction x y arbitrary: z rule: formula.rel_induct)
  case (Pred a11 a12 b11 b12)
  then show ?case
    by (cases z) auto
next
  case (Let a21 a22 a23 b21 b22 b23)
  then show ?case
    by (cases z) auto
next
  case (Eq a31 a32 b31 b32)
  then show ?case
    by (cases z) auto
next
  case (Less a41 a42 b41 b42)
  then show ?case
    by (cases z) auto
next
  case (LessEq a51 a52 b51 b52)
  then show ?case
    by (cases z) auto
next
  case (Neg a6 b6)
  then show ?case
    by (cases z) auto
next
  case (Or a71 a72 b71 b72)
  then show ?case
    by (cases z) auto
next
  case (And a81 a82 b81 b82)
  then show ?case
    by (cases z) auto
next
  case (Ands a9 b9)
  then show ?case
    by (cases z) (auto simp: list_all2_conv_all_nth)
next
  case (Exists a101 a102 b101 b102)
  then show ?case
    using Rtrans
    by (cases z) auto
next
  case (Agg a111 a112 a113 a114 a115 b111 b112 b113 b114 b115)
  then show ?case
    using Rtrans
    by (cases z) (auto simp: list_all2_conv_all_nth)
next
  case (Prev a121 a122 b121 b122)
  then show ?case
    by (cases z) auto
next
  case (Next a131 a132 b131 b132)
  then show ?case
    by (cases z) auto
next
  case (Since a141 a142 a143 b141 b142 b143)
  then show ?case
    by (cases z) auto
next
  case (Until a151 a152 a153 b151 b152 b153)
  then show ?case
    by (cases z) auto
next
  case (MatchF a161 a162 b161 b162)
  then show ?case
    by (cases z) (auto intro: rel_regex_mono_trans)
next
  case (MatchP a171 a172 b171 b172)
  then show ?case
    by (cases z) (auto intro: rel_regex_mono_trans)
qed

(*
lemma safe_check_complete:
  assumes "safe_formula \<phi>" "wty_result S E \<phi> E' \<phi>'"
  shows "check S E \<phi> = Some (E', \<phi>')"
  sorry (*
proof -
  have safe: "safe_formula \<phi>'"
    using assms
    by (auto simp: wty_result_def rel_formula_safe)
  show ?thesis
    using rel_formula_wty_unique_bv[OF safe] rel_formula_wty_unique_fv[OF safe] assms(2)
      rel_formula_trans[of _ "\<lambda>_ _. True"]
    by (auto simp: wty_result_def rel_formula_fv intro!: check_complete) blast+
qed *)

lemma check_safe_complete:
  assumes "safe_formula \<phi>" "wty_formula S E' \<phi>'" "formula.rel_formula f \<phi> \<phi>'"
  shows "check_safe S \<phi> = Some (E', \<phi>')"
  sorry (*
proof -
  have safe: "safe_formula (formula.map_formula Map.empty \<phi>)"
    by (rule rel_formula_safe[OF assms(1) rel_formula_swap])
       (auto simp add: formula.rel_map intro: formula.rel_refl)
  then show ?thesis
    using assms(2,3)
    by (auto simp: check_safe_def wty_result_def extends_def formula.rel_map
        intro!: safe_check_complete intro: formula.rel_mono_strong)
qed *)
*)
(*<*)
end
(*>*)
