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

(*Theorem 3.7*)
lemma ty_of_sat'_safe: "safe_formula \<phi> \<Longrightarrow> S, E \<turnstile> \<phi> \<Longrightarrow> wty_envs S \<sigma> V \<Longrightarrow> 
  sat' \<sigma> V v i \<phi> \<Longrightarrow> x \<in> Formula.fv \<phi> \<Longrightarrow> Formula.nfv \<phi> \<le> length v \<Longrightarrow> ty_of (v ! x) = E x" (*Theorem 3.7*)
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

(*Theorem 3.7 instantiated with sat*)
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

(*Lemma 5.1*)
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

(*Lemma 5.2*)
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

fun min_type :: "tysym \<Rightarrow> tysym \<rightharpoonup> tysym \<times> tysym" where
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

definition update_env :: "tysym \<times> tysym \<Rightarrow> tysenv \<Rightarrow> (tysym \<Rightarrow> tysym)" where
"update_env x E \<equiv> case x of (tnew,told) \<Rightarrow>(\<lambda>v. if v = told then tnew else v) "

(* takes two types as input, checks if there's no clash, returns updated env and the more specific type*)
definition clash_propagate :: "tysym \<Rightarrow> tysym \<Rightarrow> tysenv \<Rightarrow> (tysym \<Rightarrow> tysym) option" where
"clash_propagate t1 t2 E = (case min_type t1 t2 of Some (newt,oldt) \<Rightarrow> Some (update_env (newt,oldt) E)| None \<Rightarrow> None) "

definition clash_propagate2 :: "tysym \<Rightarrow> tysym \<Rightarrow> tysenv \<rightharpoonup> (tysym \<Rightarrow> tysym)" where
"clash_propagate2 t1 t2 E = map_option  (\<lambda>x . (update_env x E)) (min_type t1 t2)"
 
lemma clash_prop_alt: "clash_propagate2 t1 t2 E = clash_propagate t1 t2 E"
  by (auto simp add: clash_propagate2_def clash_propagate_def split: option.splits) 

lemma clash_prop_comm: "clash_propagate2 t1 t2 E = clash_propagate2 t2 t1 E"
  using min_comm by (auto simp add: clash_propagate2_def)


definition trm_f :: "(nat \<Rightarrow> tysym) \<Rightarrow> (nat \<Rightarrow> tysym) \<Rightarrow>nat set \<Rightarrow> tysym set \<Rightarrow> (tysym \<Rightarrow> tysym) " where
"trm_f E' E W X= undefined"
(*(\<lambda>t. foldl (\<lambda> t' n . if E n = t then E' n else t') t (sorted_list_of_set W) )*)
definition trm_f_new :: "(nat \<Rightarrow> tysym) \<Rightarrow> (nat \<Rightarrow> tysym) \<Rightarrow>tysym \<Rightarrow> tysym \<Rightarrow>nat set  \<Rightarrow> tysym set \<Rightarrow> (tysym \<Rightarrow> tysym) " where
"trm_f_new E' E typ' typ W X = undefined"
(* "trm_f_new E' E typ' typ  W = (\<lambda>t. if t = typ then typ' else foldl (\<lambda> t' n
. if E n = t then E' n else t') t (sorted_list_of_set W) )" *)


lemma trm_f_not_in_fv: assumes  "\<not>(\<exists>n \<in> set xs . E n = t)" shows "foldl (\<lambda>t' n. if E n = t then E2 n else t') t xs = t"
  using assms by (induction xs) auto

(*lemma trm_f_not_in_fv_high:   assumes  "\<not>(\<exists>n \<in> W . E n = t)" "finite W" shows "trm_f E2 E W X t = t"
 unfolding trm_f_def apply (rule trm_f_not_in_fv) using  assms by (auto simp add: set_sorted_list_of_set[OF assms(2)])*)

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

(*lemma trm_f_in_fv_high:   assumes  "n \<in> W" "E n = t" "finite W" "\<forall>n' \<in>W . E n' = t \<longrightarrow> E2 n' = E2 n "
    shows "trm_f E2 E W t =  E2 n"
  unfolding trm_f_def apply (rule trm_f_in_fv) using  assms(1,2) apply (auto simp add:  set_sorted_list_of_set[OF assms(3)])
  using assms(4)
  by blast
*)

lemma trm_f_foldl_id: assumes "\<forall>n \<in> set w . t \<noteq> E n " shows "foldl (\<lambda>t' n. if E n = t then E' n else t') t w = t"
  using assms by (induction w)  auto 
(*
lemma trm_f_id: assumes "\<forall>n' \<in> W .t \<noteq> E n'" "finite W" shows "(trm_f E' E W) t = t"
  unfolding trm_f_def using trm_f_foldl_id[of "sorted_list_of_set W"  "t" E E'] assms set_sorted_list_of_set[of W] 
  by simp *)



lemma map_regex_size: assumes "\<And>x . x \<in> regex.atms r \<Longrightarrow>   size (f x) = size x" shows "regex.size_regex size r = regex.size_regex size (regex.map_regex f r) "
  using assms by (induction r arbitrary: ) auto

lemma map_regex_map_formula_size[simp]: " size (regex.map_regex (formula.map_formula f) r) = size r"
  by (induction r)  auto

lemma map_formula_size[simp]:"size (formula.map_formula f \<psi>) = size \<psi>" 
  apply (induction \<psi> arbitrary: f) 
 apply auto apply ( simp add: dual_order.eq_iff size_list_pointwise) using map_regex_size  by metis+


definition check_binop where  (* what if typ < exp_typ? e.g typ = TCst TInt*)
"check_binop check_trm E typ t1 t2 exp_typ X \<equiv> 
(case  min_type exp_typ typ of Some (newt,oldt) \<Rightarrow> 
  (case check_trm ((update_env (newt,oldt) E) \<circ> E) newt X t1 of
     Some f' \<Rightarrow>
          (case check_trm (f' \<circ> (update_env (newt,oldt) E) \<circ> E) (f' newt) X t2 of
             Some f'' \<Rightarrow> Some f''
            | None \<Rightarrow> None ) 
     | None \<Rightarrow> None)
  | None \<Rightarrow> None )"

definition check_binop2 where
"check_binop2 check_trm E typ t1 t2 exp_typ X  \<equiv> 
(case clash_propagate2 exp_typ typ E of Some f \<Rightarrow> 
  (case check_trm (f \<circ> E) (f typ) (f ` X) t1  of
     Some f' \<Rightarrow> (case check_trm (f' \<circ> f \<circ> E) ((f' \<circ> f) typ) ((f' \<circ> f) ` X) t2 of
        Some f'' \<Rightarrow> Some (f'' \<circ> f' \<circ> f)
        | None \<Rightarrow> None)
     | None \<Rightarrow> None)
  | None \<Rightarrow> None )"

lemma [fundef_cong]: "(\<And>E typ t X. size t \<le> size t1 + size t2 \<Longrightarrow> check_trm E typ X t = check_trm' E typ X t) \<Longrightarrow> check_binop check_trm E typ t1 t2 exp_typ X = check_binop check_trm' E typ t1 t2 exp_typ X"
  by (auto simp add: check_binop_def split: option.split) 

lemma [fundef_cong]: "(\<And>E typ t X. size t \<le> size t1 + size t2 \<Longrightarrow> check_trm E typ X t = check_trm' E typ X t) \<Longrightarrow> check_binop2 check_trm E typ t1 t2 exp_typ X = check_binop2 check_trm' E typ t1 t2 exp_typ X"
  unfolding check_binop2_def by(auto split:option.splits)
(*2nd propagate needed?*)

fun check_trm :: "tysenv \<Rightarrow> tysym \<Rightarrow> tysym set \<Rightarrow> Formula.trm  \<Rightarrow> (tysym \<Rightarrow> tysym) option" where
"check_trm E typ X (Formula.Var v) = clash_propagate2  (E v) typ E "
| "check_trm E typ X (Formula.Const c)  =  clash_propagate2 (TCst (ty_of c)) typ  E"
| "check_trm E typ X (Formula.F2i t) =
    (case clash_propagate2 typ (TCst TInt) E of Some f \<Rightarrow> 
      (case check_trm (f \<circ> E) (TCst TFloat) (f ` X) t of Some f' \<Rightarrow>
        Some (\<lambda>t. if t = typ then TCst TInt else (f' \<circ> f) t)
    | None \<Rightarrow> None) 
  | None \<Rightarrow> None)" 
| "check_trm E typ X (Formula.I2f t) = 
    (case clash_propagate2 typ (TCst TFloat) E of Some f \<Rightarrow> 
      (case check_trm (f \<circ> E) (TCst TInt) (f ` X) t of Some f' \<Rightarrow>
        Some (\<lambda>t. if t = typ then TCst TFloat else (f' \<circ> f) t)
    | None \<Rightarrow> None) 
  | None \<Rightarrow> None)" 
|"check_trm E typ X (Formula.UMinus t) = 
    (case clash_propagate2 (TNum 0) (new_type_symbol typ) (new_type_symbol \<circ> E) of 
      Some f \<Rightarrow> (case check_trm (f \<circ> new_type_symbol \<circ> E) (f (new_type_symbol typ)) (f ` new_type_symbol ` X) t of
        Some f' \<Rightarrow> Some (f' \<circ> f \<circ> new_type_symbol)
      | None \<Rightarrow> None)
  | None \<Rightarrow> None)"
|"check_trm E typ X (Formula.Plus t1 t2) = 
    (case check_binop2 check_trm (new_type_symbol \<circ> E) (new_type_symbol typ) t1 t2 (TNum 0) (new_type_symbol ` X) of
      Some f \<Rightarrow> Some (f \<circ> new_type_symbol)
  | None \<Rightarrow> None)" 
|"check_trm E typ X (Formula.Minus t1 t2) = 
    (case check_binop2 check_trm (new_type_symbol \<circ> E) (new_type_symbol typ) t1 t2 (TNum 0) (new_type_symbol ` X) of
      Some f \<Rightarrow> Some (f \<circ> new_type_symbol)
  | None \<Rightarrow> None)"
|"check_trm E typ X (Formula.Mult t1 t2) = 
    (case check_binop2 check_trm (new_type_symbol \<circ> E) (new_type_symbol typ) t1 t2 (TNum 0) (new_type_symbol ` X) of
      Some f \<Rightarrow> Some (f \<circ> new_type_symbol)
  | None \<Rightarrow> None)"
|"check_trm E typ X (Formula.Div t1 t2) = 
    (case check_binop2 check_trm (new_type_symbol \<circ> E) (new_type_symbol typ) t1 t2  (TNum 0) (new_type_symbol ` X) of
      Some f \<Rightarrow> Some (f \<circ> new_type_symbol)
  | None \<Rightarrow> None)"
|"check_trm E typ X (Formula.Mod t1 t2) = check_binop2 check_trm E typ t1 t2  (TCst TInt) X"

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

definition "resultless_trm_f f' f typ X  \<longleftrightarrow> (\<exists>g. wf_f (TCst \<circ> g) \<and> (\<forall>t \<in> X. f' t  = (g \<circ> f) t) \<and> f' typ = (g \<circ> f) typ)"
    
lemma tysenvless_resultless_trm: assumes
  "tysenvless E' E" 
  "case typ of TCst t' \<Rightarrow> typ = typ' | TNum n \<Rightarrow> t \<in> numeric_ty \<and> typ' = TCst t \<or> typ' = typ |_  \<Rightarrow> True "
  "(\<forall>x. E x \<noteq> typ) \<or> typ = TCst t"
  shows "resultless_trm E' E typ' typ"
  using assms apply (auto simp add: tysenvless_def resultless_trm_def)  subgoal for g apply (rule exI[of _ "g(typ := typ')" ]) 
    by (auto simp add: wf_f_def split: tysym.splits)  subgoal for g  apply (rule exI[of _ "g(typ := typ')" ]) 
    by (auto simp add: wf_f_def) done

lemma some_min_resless: assumes "min_type typ z = Some y"
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
  "Some (newt, oldt) = min_type x (new_type_symbol type)" 
  "case x of TNum 0 \<Rightarrow> f' type \<in> numeric_ty | TCst t \<Rightarrow> t = f' type | _ \<Rightarrow> False"
  "f = update_env (newt, oldt) (new_type_symbol \<circ> E)"
shows "resultless_trm_f f' (f \<circ> new_type_symbol) type X"
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
    using assms(4) min_consistent[OF assms(3)[symmetric]] f_def f''_eq(1) assms(1)
    by (auto simp add: wf_f_def g_def new_type_symbol_def split: tysym.splits)
  moreover have "wf_f (TCst \<circ> g)" 
    using assms(4) f''_eq(1) min_consistent[OF assms(3)[symmetric]] wf_f'' 
    by(auto simp: g_def wf_f_def new_type_symbol_def split:tysym.splits nat.splits)  
  ultimately show ?thesis unfolding resultless_trm_f_def by auto
qed 

lemma resless_wty_const: assumes 
  "wf_f (TCst \<circ> f')"
  "wf_f f"
  "f' type = typ''"
  "Some (newt, oldt) = min_type (TCst typ'') type"
  "f = update_env (newt, oldt) E"
shows  "resultless_trm_f f' f type X"
proof -
  note newt_def = min_const[OF assms(4)[symmetric]]
  have oldt_def: "oldt = type"  using min_consistent[OF assms(4)[symmetric]] newt_def by auto
  have f_def: "f = (\<lambda>v. if v = oldt then TCst typ'' else v)" 
    using assms(5)[unfolded min_const[OF assms(4)[symmetric]]] unfolding update_env_def by auto
  define g where g_def: "g = (\<lambda>t. if t = TCst typ'' then typ'' else f' t)"
  then have "f' t = (g \<circ> f) t" for t 
    using assms f_def oldt_def wf_f_def by force
  moreover have "wf_f (TCst \<circ> g)" 
    using assms(1) g_def wf_f_def by auto
  ultimately show ?thesis 
    unfolding resultless_trm_f_def by auto
qed

lemma resless_wty_num_dir2: assumes
  "f' newt = typ''"
  "wf_f (TCst \<circ> f')"
  "Some (newt, oldt) = min_type (TNum n) type" 
  shows  "typ'' \<in> numeric_ty"
  using assms 
  by (induction "TNum n" "type" rule: min_type.induct)
  (auto simp add: resultless_trm_def  numeric_ty_def new_type_symbol_def wf_f_def split: tysym.splits if_splits) 

lemma wf_f_clash_propagate2:
  assumes "clash_propagate2 ty1 ty2 E = Some f"
  shows "wf_f f" 
  using assms unfolding wf_f_def clash_propagate2_def update_env_def 
  apply(auto split:prod.splits if_splits tysym.splits) 
  apply (metis min_comm min_consistent min_const) 
  using min_consistent apply fastforce 
  by (metis (full_types) insert_iff min_comm min_consistent min_type.simps(7) numeric_ty_def option.discI ty.exhaust)
  
lemma resless_wty_const_dir2: assumes 
  "resultless_trm E1 E2 (TCst typ'') newt"
  "Some (newt, oldt) = min_type (TCst t) type"
  shows "typ'' = t"
  using assms  min_const[of t type ]
  by (auto simp add: eq_commute[where ?a="Some(newt,oldt)"] resultless_trm_def wf_f_def) 


definition wty_result_trm :: " Formula.trm \<Rightarrow> tysenv \<Rightarrow> tysym \<Rightarrow> tysenv \<Rightarrow> tysym \<Rightarrow> bool" where
 "wty_result_trm  t E' typ' E typ \<longleftrightarrow> resultless_trm E' E typ' typ \<and> 
(\<forall>E'' typ'' .   resultless_trm (TCst \<circ>  E'') E (TCst typ'') typ \<longrightarrow> ( E'' \<turnstile> t :: typ'' \<longleftrightarrow> resultless_trm (TCst \<circ>  E'') E' (TCst typ'') typ' ))"

definition wty_result_fX_trm :: "tysenv \<Rightarrow> tysym \<Rightarrow> Formula.trm  \<Rightarrow> (tysym \<Rightarrow> tysym) \<Rightarrow> tysym set \<Rightarrow> bool" where
  "wty_result_fX_trm E typ trm f X \<longleftrightarrow> wf_f f \<and> 
(\<forall>f' .  wf_f (TCst \<circ> f') \<longrightarrow> 
  ((f'\<circ> E) \<turnstile> trm :: f' typ) = (\<exists> g. wf_f (TCst \<circ> g) \<and>(\<forall>t \<in> X. f' t = (g \<circ> f) t) \<and> f' typ = (g \<circ> f) typ ))"

definition half_wty_trm ::  "tysenv \<Rightarrow> tysym \<Rightarrow> Formula.trm  \<Rightarrow> (tysym \<Rightarrow> tysym) \<Rightarrow> tysym set \<Rightarrow> bool" where
"half_wty_trm E typ trm f X \<longleftrightarrow> wf_f f \<and> 
(\<forall>f' .  wf_f (TCst \<circ> f') \<longrightarrow> 
  ((f'\<circ> E) \<turnstile> trm :: f' typ) \<longrightarrow> (\<exists> g. wf_f (TCst \<circ> g) \<and>(\<forall>t \<in> X. f' t = (g \<circ> f) t) \<and> f' typ = (g \<circ> f) typ ))"

lemma subterm_half_wty: assumes "half_wty_trm E typ trm f X" 
 "\<And>f . (f \<circ> E) \<turnstile> subtrm :: (f typ) \<Longrightarrow> (f \<circ> E) \<turnstile> trm :: (f typ)"
shows  "half_wty_trm E typ subtrm f X"
  using assms unfolding half_wty_trm_def by auto

lemma check_trm_step0_half: assumes
  "clash_propagate2 t type E = Some f" 
shows "resultless_trm (f \<circ> E) E (f type) type"
proof - 
  obtain  oldt where t_def: "min_type t type = Some (f type, oldt)" using assms min_consistent[of t type]
    by (cases "min_type t (type)") (auto simp add: clash_propagate2_def update_env_def) 
  then have f_def: "f =  update_env (f type, oldt) E" using assms
    by (cases "min_type (t) (type)") (auto simp add: clash_propagate2_def) 
  then show g1: "resultless_trm (f \<circ> E) E (f type) type"
    using some_min_resless[OF t_def[unfolded min_comm[where ?b="type"]] f_def] by simp
qed

lemma check_trm_step0_num: assumes
  "Some f = clash_propagate2  (TNum 0) (new_type_symbol type) (new_type_symbol \<circ> E)" 
  "\<And>f''. ((f'' \<circ> E) \<turnstile> t :: f'' type) \<Longrightarrow> f'' type \<in> numeric_ty" 
  "wf_f (TCst \<circ> f')"
shows 
  "((f' \<circ> E) \<turnstile> t :: f' type) \<Longrightarrow> resultless_trm_f f' (f \<circ> new_type_symbol) type X"
  "resultless_trm_f f' (f \<circ> new_type_symbol) type X \<Longrightarrow> f' type \<in> numeric_ty"
proof -
  have wf_f: "wf_f f" using assms(1) using wf_f_clash_propagate2 by fastforce
  obtain oldt where t_def: "Some (f (new_type_symbol type), oldt) = min_type (TNum 0) (new_type_symbol type)" using assms(1) min_consistent
    by (cases "min_type (TNum 0) (new_type_symbol type)"; auto simp add: clash_propagate2_def update_env_def) metis
  then have f_def: "f =  update_env (f (new_type_symbol type), oldt) (new_type_symbol \<circ> E)" using assms(1) 
    by (cases "min_type (TNum 0) (new_type_symbol type)") (auto simp add:  clash_propagate2_def)
  show "((f' \<circ> E) \<turnstile> t :: f' type) \<Longrightarrow> resultless_trm_f f' (f \<circ> new_type_symbol) type X"
    using resless_wty_num[OF assms(3) wf_f t_def _ f_def] assms(2) by auto
  
  show "resultless_trm_f f' (f \<circ> new_type_symbol) type X \<Longrightarrow> f' type \<in> numeric_ty"
  proof -
    assume "resultless_trm_f f' (f \<circ> new_type_symbol) type X"
    then obtain g where g_def: "wf_f (TCst \<circ> g)" "\<forall>t\<in>X. f' t = (g \<circ> (f \<circ> new_type_symbol)) t" "f' type = (g \<circ> (f \<circ> new_type_symbol)) type" 
      unfolding resultless_trm_f_def by auto
    show "f' type \<in> numeric_ty" using g_def(3) resless_wty_num_dir2[OF _ g_def(1) t_def] by auto
  qed
qed            

lemma check_trm_step0_cst2: assumes
  "Some f = clash_propagate2 (TCst typ'') type E" 
  "wf_f (TCst \<circ> f')"
  "f' type = typ''"
shows 
  "resultless_trm_f f' f type X"
proof -
  have wf_f: "wf_f f" using assms(1) using wf_f_clash_propagate2 by fastforce
  obtain oldt where t_def: "Some (f type, oldt) = min_type (TCst typ'') ( type)" using assms(1) min_consistent
    by (cases "min_type (TCst typ'') ( type)"; auto simp add: clash_propagate2_def update_env_def) fastforce
  then have f_def: "f =  update_env (f type, oldt) (E)" using assms(1) 
    by (cases "min_type (TCst typ'') ( type)") (auto simp add:  clash_propagate2_def)
  show "resultless_trm_f f' f type X"
    using resless_wty_const[OF assms(2) wf_f assms(3) t_def f_def] by auto
qed

lemma check_trm_step0_cst: assumes
    "clash_propagate2 (TCst ty) type E = Some f" 
    "\<And>f'' y . (f'' \<circ> E \<turnstile> t :: y) \<longleftrightarrow>  y = ty"
  shows "wty_result_fX_trm E type t f X"
proof -
  obtain oldt where t_def: "min_type (TCst ty) type = Some (f type, oldt)" 
    using assms(1) 
    by (cases "min_type (TCst ty) type"; auto simp add: clash_propagate2_def update_env_def) (metis min_consistent)
  then have f_def: "f = update_env (f type, oldt) E" using assms(1) 
    by(cases "min_type (TCst ty)  type") (auto simp add: clash_propagate2_def) 
  { 
    fix f'' type''
    assume wf_f'': "wf_f (TCst \<circ> f'')" and wty: "(f'' \<circ> E) \<turnstile> t :: f'' type" 
    define g where "g = (\<lambda>t. if type = t then ty else f'' t)"
    have wf_g: "wf_f (TCst \<circ> g)" using wty[unfolded assms(2)] wf_f'' g_def by (auto simp add: wf_f_def)
    have g1: "f'' t = (g \<circ> f) t" for t
      using wty[unfolded assms(2)] f_def g_def[unfolded wty[unfolded assms(2), symmetric]]
      by (auto simp add: update_env_def) (smt (verit, ccfv_threshold) comp_apply min_consistent t_def tysym.inject(3) wf_f'' wf_f_def)
    moreover have "f'' type = (g \<circ> f) type" using g1 by auto
    ultimately have "(\<exists>g. wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>X. f'' t = (g \<circ> f) t) \<and> f'' type = (g \<circ> f) type)" using wf_g by auto
  }
  then show ?thesis using wf_f_clash_propagate2[OF assms(1)] assms(2)
    unfolding wty_result_fX_trm_def
    by (auto simp add: wty_result_trm_def) (metis comp_def min_const t_def tysym.inject(3) wf_f_def)
qed

lemma check_trm_step1: 
  assumes 
    "wty_result_fX_trm (f \<circ> E) (f type) t f' (f ` X)"
    "half_wty_trm E type t f X"
    "E ` fv_trm t \<subseteq> X"
  shows "wty_result_fX_trm E type t (f' \<circ> f) X"
proof -
  have "wf_f (f' \<circ> f)"
    using assms wf_f_comp unfolding wty_result_fX_trm_def half_wty_trm_def
    by auto
  then show "wty_result_fX_trm E type t (f' \<circ> f) X" unfolding wty_result_fX_trm_def half_wty_trm_def
    apply(auto) 
  proof -
    fix fa
    assume fa_assm: "wf_f (TCst \<circ> fa)" "fa \<circ> E \<turnstile> t :: fa type"
    obtain g where g_def: "wf_f (TCst \<circ> g)" "\<forall>t\<in>X. fa t = (g \<circ> f) t" "fa type = (g \<circ> f) type"
      using assms(2) fa_assm unfolding half_wty_trm_def by auto
    then have "g \<circ> (f \<circ> E) \<turnstile> t :: g (f type)" 
      using fa_assm(2) assms(3) by (smt (verit, best) comp_eq_dest_lhs image_subset_iff wty_trm_fv_cong)
    then show "\<exists>g. wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>X. fa t = g (f' (f t))) \<and> fa type = g (f' (f type))"
      using assms(1) g_def unfolding wty_result_fX_trm_def by simp
  next
    fix fa g
    assume fa_assm: "wf_f (f' \<circ> f)" "wf_f (TCst \<circ> fa)" "wf_f (TCst \<circ> g)" "\<forall>t\<in>X. fa t = g (f' (f t))" "fa type = g (f' (f type))"
    have "(g \<circ> f') \<circ> (f \<circ> E) \<turnstile> t :: (g \<circ> f') (f type)" 
      using assms(1) unfolding wty_result_fX_trm_def by (metis fa_assm(3) fun.map_comp wf_f_comp)
    then show "fa \<circ> E \<turnstile> t :: g (f' (f type))" 
      using fa_assm assms(3) by (smt (verit, best) comp_def image_subset_iff wty_trm_fv_cong)
  qed
qed
     
  

lemma half_wty_trm_trans: assumes 
  "half_wty_trm E typ trm f X"
  "half_wty_trm (f \<circ> E) (f typ) trm f' (f ` X)"
  "E ` fv_trm trm \<subseteq> X"
shows "half_wty_trm E typ trm (f' \<circ> f) X"
proof -
  {
    fix f''
    assume wf: "wf_f (TCst \<circ> f'')" and typed: "f'' \<circ> E \<turnstile> trm :: f'' typ"
    obtain g where g_def: "wf_f (TCst \<circ> g)" "\<forall>t\<in>X. f'' t = (g \<circ> f) t"  "f'' typ = (g \<circ> f) typ" 
      using assms(1) wf typed unfolding half_wty_trm_def by blast
    have "g \<circ> (f \<circ> E) \<turnstile> trm :: g (f typ)"
      using typed g_def(2) assms(3) by (smt (verit, ccfv_SIG) comp_apply g_def(3) image_subset_iff wty_trm_fv_cong)
    then have "(\<exists>g. wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>X. f'' t = (g \<circ> (f' \<circ> f)) t) \<and> f'' typ = (g \<circ> (f' \<circ> f)) typ)"
      using g_def assms(2) unfolding half_wty_trm_def by simp
  }
  then show ?thesis using assms wf_f_comp unfolding half_wty_trm_def by auto
qed

lemma wf_new_type_symbol:
  "wf_f new_type_symbol" 
  by (simp add: new_type_symbol_def wf_f_def)

lemma check_binop_sound: 
  assumes 
  "\<And>E type f X. check_trm E type X t1 = Some f \<Longrightarrow>  E ` fv_trm t1 \<subseteq> X \<Longrightarrow>  wty_result_fX_trm E type t1 f X"
  "\<And>E type f X. check_trm E type X t2 = Some f \<Longrightarrow>  E ` fv_trm t2 \<subseteq> X \<Longrightarrow> wty_result_fX_trm E type t2 f X"
  "check_trm E type X (trm t1 t2) = Some f" 
  "trm \<in> {trm.Plus, trm.Minus, trm.Mult, trm.Div } \<and> constr = TNum 0 \<and> E_start = new_type_symbol \<circ> E \<and> type_start = new_type_symbol type \<and> (P = (\<lambda>y.  y \<in> numeric_ty) \<and> X_start = new_type_symbol ` X \<and> final_f = new_type_symbol)
 \<or> trm = trm.Mod \<and> constr = TCst TInt \<and> E_start =  E \<and> type_start = type \<and> (P = (\<lambda>y.  y = TInt) \<and> X_start = X \<and> final_f = id)"
  "E ` fv_trm (trm t1 t2) \<subseteq> X"
shows "wty_result_fX_trm E type (trm t1 t2) f X"
proof -
  have fvi: "E ` fv_trm t1 \<subseteq> X" "E ` fv_trm t2 \<subseteq> X" using assms(4-5) by force+
  obtain f' where f'_def: "Some f' = clash_propagate2 constr type_start E_start" using assms
    by (auto simp add: check_binop2_def clash_propagate2_def split: option.splits)
  then have constr_int: "constr = TCst TInt \<Longrightarrow> wf_f (TCst \<circ> f'') \<Longrightarrow> resultless_trm_f f'' f' type X \<Longrightarrow> f'' type = TInt" for f'' 
    unfolding resultless_trm_f_def by (cases "min_type (TCst TInt) type_start"; auto simp: clash_propagate2_def comp_assoc wf_f_def) (smt (verit, best) assms(4) case_prod_conv min_consistent min_const tysym.distinct(5) update_env_def)
  have wf_f': "wf_f f'" using f'_def by (simp add: wf_f_clash_propagate2)
  have wf_final: "wf_f final_f" using assms(4) wf_new_type_symbol by(auto)
  obtain f'' where  f''_def: "Some f'' = check_trm (f' \<circ> E_start) (f' type_start) (f' ` X_start) t1" 
    using assms f'_def by (auto simp add: check_binop2_def clash_propagate2_def split: option.splits) 
  then obtain f''' where f'''_def: "Some f''' = check_trm (f'' \<circ> f' \<circ> E_start) ((f'' \<circ> f') type_start) ((f'' \<circ> f') ` X_start) t2" 
    using assms f'_def
    by (auto simp add: check_binop2_def clash_propagate2_def split: option.splits)
  have f_def: "f = f''' \<circ> (f'' \<circ> (f' \<circ> final_f))" using assms(3-4) f'_def f''_def f'''_def
    by(auto simp:check_binop2_def split:option.splits) fastforce+
  have *: "(f'' \<circ> f' \<circ> E_start) ` fv_trm t2 \<subseteq> (f'' \<circ> f') ` X_start" 
          "(f' \<circ> E_start) ` fv_trm t1 \<subseteq> f' ` X_start"
    using assms(4-5) by auto blast+
  note wty_res2 = assms(2)[OF f'''_def[symmetric] *(1)]
  note wty_res1 = assms(1)[OF f''_def[symmetric] *(2)]
  have correct_type: "f \<circ> E \<turnstile> trm t1 t2 :: f type \<Longrightarrow> P (f type)" for f 
    using assms(4) by (auto elim: wty_trm.cases) 
  have correct_type': "E \<turnstile> trm t1 t2 :: t  \<Longrightarrow> E \<turnstile> t1 :: t \<and> E \<turnstile> t2 :: t" for E t 
    using assms(4) by (auto elim: wty_trm.cases) 
  have "wf_f (f' \<circ> final_f)" using assms(4) wf_f'
    by (auto simp add: wf_f_comp wf_new_type_symbol) 
  then have "half_wty_trm E type (trm t1 t2) (f' \<circ> final_f) X"
    unfolding half_wty_trm_def apply (auto) 
  proof -
    fix fa
    assume asm: "wf_f (TCst \<circ> fa)" "fa \<circ> E \<turnstile> trm t1 t2 :: fa type"
    then show "\<exists>g. wf_f (TCst \<circ> g) \<and>
               (\<forall>t\<in>X. fa t = g (f' (final_f t))) \<and>
               fa type = g (f' (final_f type))" 
      using 
        check_trm_step0_num[OF _ _ asm(1), of f' type E "trm t1 t2"] correct_type
        check_trm_step0_cst2[OF _ asm(1)]
        correct_type[OF asm(2)] f'_def assms(4) 
      unfolding resultless_trm_f_def by auto metis
  qed
  moreover have 
    "half_wty_trm (f'' \<circ> (f' \<circ> (final_f \<circ> E))) (f'' (f' (final_f type))) (trm t1 t2) f''' ((\<lambda>x. f'' (f' (final_f x))) ` X)"
    "half_wty_trm (f' \<circ> (final_f \<circ> E)) (f' (final_f type)) (trm t1 t2) f'' ((\<lambda>x. f' (final_f x)) ` X)"
    using wty_res1 wty_res2 correct_type' wf_f_comp assms(4)
    unfolding wty_result_fX_trm_def half_wty_trm_def by(auto simp:comp_assoc) blast+
  ultimately have half_wty: "half_wty_trm E type (trm t1 t2) f X" 
    using assms(5)
    unfolding f_def by(auto simp:comp_assoc intro!:half_wty_trm_trans)
  {
    fix fa
    assume wf_fa: "wf_f (TCst \<circ> fa)"
      and ex_g: "(\<exists>g. wf_f (TCst \<circ> g) \<and> (\<forall>t \<in> X. fa t = (g \<circ> f) t) \<and> fa type = (g \<circ> f) type)"
    obtain g where g_def:
      "wf_f (TCst \<circ> g)" "(\<forall>t \<in> X. fa t = (g \<circ> f) t)"  "fa type = (g \<circ> f) type" using ex_g by auto
    let ?ft1 = "g \<circ> f''' \<circ> f''"
    let ?ft2 = "g \<circ> f'''"
    have wfs: 
      "wf_f (TCst \<circ> ?ft1)"
      "wf_f (TCst \<circ> ?ft2)"
      using wf_final wf_f' wty_res1 wty_res2 wf_f_comp g_def(1) 
      unfolding wty_result_fX_trm_def by (simp add: fun.map_comp)+
    have 
      "(\<exists>g. wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>f' ` X_start. ?ft1 t = (g \<circ> f'') t) \<and> ?ft1 (f' type_start) = (g \<circ> f'') (f' type_start))"
      "(\<exists>g. wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>(f'' \<circ> f') ` X_start. ?ft2 t = (g \<circ> f''') t) \<and> ?ft2 ((f'' \<circ> f') type_start) = (g \<circ> f''') ((f'' \<circ> f') type_start))"
       apply (metis comp_assoc g_def(1) wf_f_comp wty_res2 wty_result_fX_trm_def)
      using g_def(1) by blast
    moreover have
      "(?ft1 \<circ> (f' \<circ> E_start) \<turnstile> t1 :: ?ft1 (f' type_start)) = (\<exists>g. wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>f' ` X_start. ?ft1 t = (g \<circ> f'') t) \<and> ?ft1 (f' type_start) = (g \<circ> f'') (f' type_start))"
      "(?ft2 \<circ> ((f'' \<circ> f') \<circ> E_start) \<turnstile> t2 :: ?ft2 ((f'' \<circ> f') type_start)) = (\<exists>g. wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>(f'' \<circ> f') ` X_start. ?ft2 t = (g \<circ> f''') t) \<and> ?ft2 ((f'' \<circ> f') type_start) = (g \<circ> f''') ((f'' \<circ> f') type_start))"
      using wty_res1 wty_res2 wfs g_def(1) unfolding wty_result_fX_trm_def by auto force+
    ultimately have 
      "(g \<circ> f \<circ> E) \<turnstile> t1 :: (g \<circ> f) type" 
      "(g \<circ> f \<circ> E) \<turnstile> t2 :: (g \<circ> f) type" 
      using assms(4) unfolding f_def by(auto simp:comp_assoc) 
    then have wty_terms:
      "(fa \<circ> E) \<turnstile> t1 :: fa type" 
      "(fa \<circ> E) \<turnstile> t2 :: fa type" 
      using g_def(2) fvi by (smt (verit, best) comp_def g_def(3) image_subset_iff wty_trm_fv_cong)+
    have resless: "resultless_trm_f fa (f' \<circ> final_f) type X"
      unfolding resultless_trm_f_def using f_def g_def(2) g_def(3) wfs(1) by auto
    have "(fa \<circ> E) \<turnstile> trm t1 t2 :: fa type" 
      using wty_res1 wty_res2 assms(4) wty_terms resless correct_type f'_def 
      check_trm_step0_num(2)[OF _ _ wf_fa, of f' type E "trm t1 t2"] constr_int[OF _ wf_fa]
      unfolding wty_result_fX_trm_def by(auto intro!: wty_trm.intros) 
  }
  then show ?thesis using half_wty unfolding wty_result_fX_trm_def half_wty_trm_def by(auto) 
qed

lemma check_conversion_sound: 
  assumes 
    " \<And>E type X f. check_trm E type X t = Some f \<Longrightarrow> E ` fv_trm t \<subseteq> X \<Longrightarrow>  wty_result_fX_trm E type t f X"
    "check_trm E type X (trm t) = Some f" 
    "trm = trm.F2i \<and> a = TInt \<and> b = TFloat \<or> trm = trm.I2f \<and> a = TFloat \<and> b = TInt"
    "E ` fv_trm t \<subseteq> X"
  shows "wty_result_fX_trm E type (trm t) f X"
proof - 
  obtain fp where fp_def: "Some fp = clash_propagate2 type (TCst a) E" 
    using assms(2-3) by (auto split: option.splits)
  then have prec_int: "fp type = TCst a" 
    using assms(3) by (cases type) (auto simp add: clash_propagate2_def update_env_def split: if_splits)
  have wf_fp: "wf_f fp" using fp_def wf_f_clash_propagate2 by presburger
  have type'_def: "f type = TCst a" 
    using assms(2,3) by (auto split: option.splits)
  have type_int: "case type of TCst t \<Rightarrow> t = a | _ \<Rightarrow> True" 
    using fp_def by (cases type)(auto simp add: clash_propagate2_def split: if_splits)
  have fp_def': "Some fp = clash_propagate2 (TCst a) type E" 
    using clash_prop_comm fp_def by auto
  obtain fp' where fp'_def: "check_trm (fp \<circ> E) (TCst b) (fp ` X) t = Some fp'" 
    using fp_def assms(2-4) by (auto split: option.splits)
  have wty: "wty_result_fX_trm (fp \<circ> E) (TCst b) t fp' (fp ` X)" 
    using assms(3-4) assms(1)[OF fp'_def] by auto
  then have wf_fp': "wf_f fp'" using wty_result_fX_trm_def assms(1) fp'_def by blast
  have f_def': "f = (\<lambda>k. if k = type then TCst a else (fp' \<circ> fp) k)" 
    using assms(2-3) fp_def fp'_def by(auto split:option.splits)
  then obtain fp'' where f_def: "f = fp'' \<circ> fp' \<circ> fp" "wf_f fp''" using prec_int wf_f_def wf_fp' by fastforce
  have wtytrm: "(\<And>E'' y. (E'' \<turnstile> trm t :: y) \<longrightarrow> (y = a))" 
    using assms(3) by (auto elim:wty_trm.cases)
  have half: "half_wty_trm E type (trm t) fp X"
    using wtytrm check_trm_step0_cst2[OF fp_def'] wf_fp unfolding half_wty_trm_def resultless_trm_f_def by auto
  have fl_def: "fp' (TCst b) = TCst b" 
    using wty unfolding wty_result_fX_trm_def wf_f_def by simp
  have typ''_def: "g (TCst a) = a" if wf_g: "wf_f (TCst \<circ> g)" for g 
    using wf_g unfolding wf_f_def by auto
  have tcst_b_aux: 
    "wf_f (TCst \<circ> f') \<Longrightarrow> (f' \<circ> (fp \<circ> E) \<turnstile> t :: f' (TCst b)) = (\<exists>g. wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>(fp ` X). f' t = (g \<circ> fp') t) \<and> f' (TCst b) = (g \<circ> fp') (TCst b))" for f'
    using wty unfolding wty_result_fX_trm_def by auto
  have step1: "wf_f (TCst \<circ> f'') \<Longrightarrow>  (f'' \<circ> E) \<turnstile> trm t :: (f'' type) \<Longrightarrow> resultless_trm_f f'' fp type X" for f''
    by (simp add: check_trm_step0_cst2 fp_def' wtytrm) 
  have step2:
    "wf_f (TCst \<circ> f'') \<Longrightarrow>  (f'' \<circ> E) \<turnstile> trm t :: (f'' type) \<Longrightarrow> (f'' \<circ> E) \<turnstile> t :: b \<Longrightarrow> resultless_trm_f f'' (fp' \<circ> fp) type X" for f''
  proof -
    assume wf: "wf_f (TCst \<circ> f'')" and typed: "(f'' \<circ> E) \<turnstile> trm t :: (f'' type)" and typed2: "(f'' \<circ> E) \<turnstile> t :: b"
    obtain g where g_def: "wf_f (TCst \<circ> g)" "(\<forall>t\<in>X. f'' t = (g \<circ> fp) t)" "f'' type = (g \<circ> fp) type" 
      using step1[OF wf typed] unfolding resultless_trm_f_def by auto
    then have "(g \<circ> (fp \<circ> E) \<turnstile> t :: g (TCst b))" 
      using typed2 by (smt (verit, best) assms(4) comp_apply image_subset_iff tysym.inject(3) wf_f_def wty_trm_fv_cong)
    then obtain g' where g'_def: "wf_f (TCst \<circ> g')" "\<forall>t\<in>(fp ` X). g t = (g' \<circ> fp') t" "g (TCst b) = (g' \<circ> fp') (TCst b)"
      using wty g_def(1) unfolding wty_result_fX_trm_def by auto
    have "f'' type = (g' \<circ> (fp' \<circ> fp)) type" using g'_def(1) prec_int typed wf_f_def wf_fp' wtytrm by force
    moreover have "\<forall>t\<in>X. f'' t = (g' \<circ> (fp' \<circ> fp)) t" using g'_def(2) g_def(2) by auto
    ultimately show "resultless_trm_f f'' (fp' \<circ> fp) type X" using g'_def g_def unfolding resultless_trm_f_def by auto
  qed
  { 
    fix f' 
    assume wf_f'': "wf_f (TCst \<circ> f')" and wty: "(f' \<circ> E) \<turnstile> trm t :: f' type" 
    then have wty': "(f' \<circ> E) \<turnstile> t :: b" "(f' \<circ> E) \<turnstile> trm t :: a" 
      using assms(3) wtytrm by(auto elim:wty_trm.cases) 
    obtain g where g_def: "wf_f (TCst \<circ> g)" "\<forall>t\<in>X. f' t = (g \<circ> (fp' \<circ> fp)) t" "f' type = (g \<circ> (fp' \<circ> fp)) type"
      using step2[OF wf_f'' wty wty'(1)] unfolding resultless_trm_f_def by auto
    have "(\<exists>g. wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>X. f' t = (g \<circ> f) t) \<and> f' type = (g \<circ> f) type)" 
      by (metis comp_apply f_def' g_def(1) g_def(2) typ''_def type'_def wty wtytrm)
  }
  moreover 
  {
    fix f'
    assume wf_f': "wf_f (TCst \<circ> f')"
      and ex_g: "(\<exists>g. wf_f (TCst \<circ> g) \<and> (\<forall>t \<in> X. f' t = (g \<circ> f) t) \<and> f' type = (g \<circ> f) type)"
    obtain g where g_def: "wf_f (TCst \<circ> g)" "(\<forall>t \<in> X. f' t = (g \<circ> f) t)"  "f' type = (g \<circ> f) type" using ex_g by auto
    have wf_fa': "wf_f (TCst \<circ> (g \<circ> fp'' \<circ> fp'))" 
      using f_def(2) wf_f_comp wf_fp' g_def(1) by (simp add: fun.map_comp)
    then have type: "g (fp'' (fp' (TCst b))) = b"  
      unfolding wf_f_def by auto
    then have "\<exists>g'. wf_f (TCst \<circ> g') \<and> (\<forall>t\<in>(fp ` X). (g \<circ> fp'' \<circ> fp') t = (g' \<circ> fp') t) \<and> (g \<circ> fp'' \<circ> fp') (TCst b) = (g' \<circ> fp') (TCst b)" 
      by (metis comp_assoc f_def(2) g_def(1) wf_f_comp)
    then have "(g \<circ> fp'' \<circ> fp' \<circ> fp) \<circ> E \<turnstile> t :: b" 
      using tcst_b_aux[OF wf_fa'] type by (metis comp_eq_dest_lhs rewriteL_comp_comp)
    then have "f' \<circ> E \<turnstile> t :: b" 
      using g_def(2)[unfolded f_def] assms(4) 
      by (smt (verit, best) comp_apply image_subset_iff wty_trm_fv_cong)
    then have "(f' \<circ> E) \<turnstile> (trm t) :: f' type"
      by (metis F2i I2f assms(3) comp_apply g_def(1) g_def(3) typ''_def type'_def)
  }
  moreover have "wf_f f" unfolding f_def using f_def(2) wf_f_comp wf_fp wf_fp' by presburger
  ultimately show ?thesis unfolding wty_result_fX_trm_def by auto
qed

(*Theorem 4.1*)
lemma check_trm_sound: "check_trm  E type X t = Some f \<Longrightarrow> E ` fv_trm t \<subseteq> X \<Longrightarrow> wty_result_fX_trm E type t f X" (*Theorem 4.1*)
proof (induction t arbitrary:  E type f X)  
  case (Var x) 
  have f_def: "f = (if f type = type 
                     then update_env (type, E x) E 
                     else update_env (E x, type) E)" 
    using Var  min_consistent update_env_def 
    by(fastforce simp add: clash_propagate2_def)
  { 
    fix f'' 
    assume wf_f'': "wf_f (TCst \<circ> f'')" and wty: "(f'' \<circ> E) \<turnstile> trm.Var x :: f'' type" 
    define g where "g = (\<lambda>t. if type = t then f'' type else f'' t)"
    have wf_g: "wf_f (TCst \<circ> g)" using wf_f'' g_def by (auto simp add: wf_f_def)
    have g1: "f'' t = (g \<circ> f) t" for t
      using wty f_def g_def by (auto simp add: update_env_def elim!: wty_trm.cases split:if_splits) 
    moreover have "f'' type = (g \<circ> f) type" using g1 by auto
    ultimately have "(\<exists>g. wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>X. f'' t = (g \<circ> f) t) \<and> f'' type = (g \<circ> f) type)" using wf_g by auto
  }
  moreover have
    "wf_f (TCst \<circ> f'') \<Longrightarrow> (\<exists>g. wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>X. f'' t = (g \<circ> f) t) \<and> f'' type = (g \<circ> f) type) \<Longrightarrow> (f'' \<circ> E) \<turnstile> trm.Var x :: f'' type" 
    for f'' using f_def Var(2)
    by (auto simp add: update_env_def intro!:wty_trm.intros split:if_splits)
  ultimately show ?case 
    using wf_f_clash_propagate2[OF Var(1)[unfolded check_trm.simps]] 
    unfolding wty_result_fX_trm_def resultless_trm_def 
    by auto
next
  case (Const x)
  show ?case  apply (rule check_trm_step0_cst[where ty="ty_of x"]) 
    using Const wty_trm.Const wty_trm_cong_aux by auto 
next
  case (Plus t1 t2)
  then show ?case
    using check_binop_sound[OF Plus(1-2)] Plus.prems(1)
    by auto fastforce
next
  case (Minus t1 t2)
  then show ?case 
    using check_binop_sound[OF Minus(1-2)] Minus.prems(1)
    by auto fastforce
next
  case (UMinus t)
  then obtain f' where f'_def: "Some f' = clash_propagate2 (TNum 0) (new_type_symbol type) (new_type_symbol \<circ> E)" 
    by (auto split: option.splits)
  then obtain f'' where f''_def: "check_trm (f' \<circ> new_type_symbol \<circ> E) (f' (new_type_symbol type)) (f' ` new_type_symbol ` X) t = Some f''"
    using UMinus by (auto split: option.splits)
  have wtynum: "\<And> f'' . f'' \<circ> E \<turnstile> trm.UMinus t :: f'' type \<Longrightarrow> f'' type \<in> numeric_ty" by (auto elim: wty_trm.cases)
  have fvi: "(f' \<circ> new_type_symbol \<circ> E) ` fv_trm t \<subseteq> f' ` new_type_symbol ` X" using UMinus.prems(2) by auto
  note res = UMinus.IH[OF f''_def fvi] 
  have f_def: "f = f'' \<circ> f' \<circ> new_type_symbol" using f'_def f''_def UMinus(2) by(auto split:option.splits)
  have wty_uminus: "wty_result_fX_trm (f' \<circ> new_type_symbol \<circ> E) ((f' \<circ> new_type_symbol) type) (trm.UMinus t) f'' ((f' \<circ> new_type_symbol) ` X)"
    using res unfolding wty_result_fX_trm_def apply(auto elim: wty_trm.cases) 
  proof -
    fix fa g
    assume assm: "\<forall>f'a. wf_f (TCst \<circ> f'a) \<longrightarrow> (f'a \<circ> (f' \<circ> new_type_symbol \<circ> E) \<turnstile> t :: f'a (f' (new_type_symbol type))) = (\<exists>g. wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>X. f'a (f' (new_type_symbol t)) = g (f'' (f' (new_type_symbol t)))) \<and> f'a (f' (new_type_symbol type)) = g (f'' (f' (new_type_symbol type))))"
      "wf_f (TCst \<circ> fa)" "wf_f (TCst \<circ> g)" 
      "\<forall>t\<in>X. fa (f' (new_type_symbol t)) = g (f'' (f' (new_type_symbol t)))"
      "fa (f' (new_type_symbol type)) = g (f'' (f' (new_type_symbol type)))"
    have wf: "wf_f (TCst \<circ> (g \<circ> f'' \<circ> f' \<circ> new_type_symbol))" 
      by (metis assm(3) comp_assoc f'_def res wf_f_clash_propagate2 wf_f_comp wf_new_type_symbol wty_result_fX_trm_def)
    have "fa \<circ> (f' \<circ> new_type_symbol \<circ> E) \<turnstile> t :: fa (f' (new_type_symbol type))" using assm by auto
    moreover have "g (f'' (f' (new_type_symbol type))) \<in> numeric_ty" 
      using check_trm_step0_num(2)[OF f'_def _ wf] using assm wtynum unfolding resultless_trm_f_def by auto metis
    ultimately show "fa \<circ> (f' \<circ> new_type_symbol \<circ> E) \<turnstile> trm.UMinus t :: g (f'' (f' (new_type_symbol type)))" using assm(5) wty_trm.UMinus by auto
  qed
  have half: "half_wty_trm E type (trm.UMinus t) (f' \<circ> new_type_symbol) X"
    using check_trm_step0_num(1)[OF f'_def] wtynum res 
    unfolding wty_result_fX_trm_def half_wty_trm_def resultless_trm_f_def 
    apply(auto) using f'_def wf_f_clash_propagate2 wf_f_comp wf_new_type_symbol by presburger
  show ?case using check_trm_step1[OF wty_uminus half UMinus(3)] unfolding f_def by (metis comp_assoc)
next
  case (Mult t1 t2)
  show ?case 
    using check_binop_sound[OF Mult(1-2)] 
    apply(auto) using Mult.prems(1) Mult.prems(2) by presburger
next
  case (Div t1 t2)
  show ?case 
    using check_binop_sound[OF Div(1-2)] 
    apply(auto) using Div.prems(1) Div.prems(2) by presburger
next
  case (Mod t1 t2)
  then show ?case 
    using check_binop_sound[OF Mod(1-2), where ?constr="TCst TInt"] Mod.prems(1)
    by auto 
next
  case (F2i t)
  have *: "trm.F2i = trm.F2i \<and> TInt = TInt \<and> TFloat = TFloat \<or> trm.F2i = trm.I2f \<and> TInt = TFloat \<and> TFloat = TInt" by auto
  have **: "E ` fv_trm t \<subseteq> X" using F2i(3) by auto
  show ?case using check_conversion_sound[OF F2i(1) F2i(2) * **] by auto
next
  case (I2f t)
  have *: "trm.I2f = trm.F2i \<and> TFloat = TInt \<and> TInt = TFloat \<or> trm.I2f = trm.I2f \<and> TFloat = TFloat \<and> TInt = TInt" by auto
  have **: "E ` fv_trm t \<subseteq> X" using I2f(3) by auto
  show ?case using check_conversion_sound[OF I2f(1) I2f(2) * **] by auto
qed 


definition wty_result_fX :: "sig \<Rightarrow> tysenv \<Rightarrow> tysym Formula.formula  \<Rightarrow> (tysym \<Rightarrow> tysym) \<Rightarrow> tysym set \<Rightarrow> bool" where
  "wty_result_fX S E \<phi> f X \<longleftrightarrow> wf_f f \<and> 
(\<forall>f'' .  wf_f (TCst \<circ> f'') \<longrightarrow> 
  (S, (f''\<circ> E) \<turnstile> (formula.map_formula  f'' \<phi>)) = (\<exists> g. wf_f (TCst \<circ> g) \<and>(\<forall>t \<in> X. f'' t = (g \<circ> f) t)))"

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

lemma[simp]: "Formula.nfv (formula.map_formula f \<psi>) = Formula.nfv \<psi>" unfolding Formula.nfv_def by auto

lemma[simp]: " wf_formula (formula.map_formula f \<psi>) = wf_formula \<psi>" by (induction \<psi>) (auto simp add: list_all_def map_regex_pred)

lemma used_tys_map[simp]: "used_tys (f \<circ> E) (formula.map_formula f \<psi>) = f ` used_tys E \<psi>"
  by (auto simp: used_tys_def formula.set_map)

lemma map_formula_f_cong: "(\<And>t. t \<in> X \<Longrightarrow> f t = g t) \<Longrightarrow> formula.set_formula \<psi> \<subseteq> X \<Longrightarrow>
  formula.map_formula f \<psi> = formula.map_formula g \<psi>"
  apply (induction \<psi>)
                  apply auto
  subgoal for r
    by (induction r) auto
  subgoal for r
    by (induction r) auto
  done

lemma wty_map_formula_cong: "S, f \<circ> E \<turnstile> formula.map_formula f \<psi> \<Longrightarrow> used_tys E \<psi> \<subseteq> X \<Longrightarrow>
       (\<And>t. t \<in> X \<Longrightarrow> f t = g t) \<Longrightarrow> S, g \<circ> E \<turnstile> formula.map_formula g \<psi>"
  apply (rule iffD1[OF wty_formula_fv_cong, where ?E1="f \<circ> E"])
   apply (auto simp: used_tys_def)[1]
  using map_formula_f_cong[of X f g]
  by (auto simp: used_tys_def)



lemma eq_refinement_min_type: assumes "\<exists> f g . wf_f f \<and> wf_f g \<and> f typ = g typ'"
  shows "\<exists> t1 t2 . min_type typ typ' = Some (t1,t2)"
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
  "clash_propagate2 constr type_start E_start = None"
shows False
proof -
  have wf1: "wf_f (\<lambda>x.  if x = type_start then f type else x)"
    using assms(1, 3)  unfolding wf_f_def new_type_symbol_def by(auto split:tysym.splits)
  have wf2: "wf_f (\<lambda> x. if x = constr then f type else x)"
    using assms(1-4)  unfolding wf_f_def new_type_symbol_def numeric_ty_def 
    by(auto simp: clash_propagate2_def split:tysym.splits)
  have "\<exists>EE tt. min_type constr type_start = Some(EE, tt)" 
    apply (rule eq_refinement_min_type)
    apply (rule exI[of _ "(\<lambda> x. if x = constr then f type else x)"])
    apply (rule exI[of _ "(\<lambda>x.  if x = type_start then f type else x)"])
    using wf1 wf2 by auto
  then show False using assms(4) by (auto simp add: clash_propagate2_def  split: option.splits) 
qed

lemma check_binop_complete: 
  assumes "\<And>E type f X. check_trm E type X t1 = None \<Longrightarrow> E ` fv_trm t1 \<subseteq> X \<Longrightarrow>  wf_f (TCst \<circ> f) \<Longrightarrow> f \<circ> E \<turnstile> t1 :: f type \<Longrightarrow> False"
    "\<And>E type f X. check_trm E type X t2 = None \<Longrightarrow> E ` fv_trm t2 \<subseteq> X \<Longrightarrow>  wf_f (TCst \<circ> f) \<Longrightarrow> f \<circ> E \<turnstile> t2 :: f type \<Longrightarrow> False"
    "check_trm E type X (trm t1 t2) = None"
    "wf_f (TCst \<circ> f)"
    "f \<circ> E \<turnstile> trm t1 t2 :: f type"
    "trm \<in> {trm.Plus, trm.Minus, trm.Mult, trm.Div } \<and> constr = TNum 0 \<and> E_start = new_type_symbol \<circ> E \<and> type_start = new_type_symbol type \<and> (P = (\<lambda>y.  y \<in> numeric_ty) \<and> X_start = new_type_symbol ` X \<and> final_f = new_type_symbol)
 \<or> trm = trm.Mod \<and> constr = TCst TInt \<and> E_start =  E \<and> type_start = type \<and> (P = (\<lambda>y.  y = TInt) \<and> X_start = X \<and> final_f = id)"
  "E ` fv_trm (trm t1 t2) \<subseteq> X"
shows False
proof -
  have wty_f: "f \<circ> E \<turnstile> t1 :: f type" "f \<circ> E \<turnstile> t2 :: f type"
    using assms(5-6) by (auto elim: wty_trm.cases) 
  have correct_type: "f \<circ> E \<turnstile> trm t1 t2 :: f type \<Longrightarrow> P (f type)" for f 
    using assms(6) by (auto elim: wty_trm.cases) 
  have "P (f type)" using assms(5-6) by(auto elim: wty_trm.cases)
  then have "clash_propagate2 constr type_start E_start = None \<Longrightarrow>  False"
    using constr_complete[OF assms(4), of P type constr E_start E type_start TInt] assms(6) by(auto) 
  then obtain f' where f'_def: "Some f' = clash_propagate2 constr type_start E_start" by fastforce
  have wf_f': "wf_f f'" using f'_def wf_f_clash_propagate2 by force
  then have wf_end: "wf_f (f' \<circ> final_f)" using assms(6) wf_f_comp by force
  then have half_wty: "half_wty_trm E type (trm t1 t2) (f' \<circ> final_f) X"
    unfolding half_wty_trm_def apply (auto) 
  proof -
    fix fa
    assume asm: "wf_f (TCst \<circ> fa)" "fa \<circ> E \<turnstile> trm t1 t2 :: fa type"
    then show "\<exists>g. wf_f (TCst \<circ> g) \<and>
               (\<forall>t\<in>X. fa t = g (f' (final_f t))) \<and>
               fa type = g (f' (final_f type))" 
      using 
        check_trm_step0_num[OF _ _ asm(1), of f' type E "trm t1 t2"] correct_type
        check_trm_step0_cst2[OF _ asm(1)]
        correct_type[OF asm(2)] f'_def assms(6) 
      unfolding resultless_trm_f_def by auto metis
  qed
  have fvi': "E ` fv_trm t1 \<subseteq> X" "E ` fv_trm t2 \<subseteq> X"
    using assms(6-7) by auto 
  have fvi: 
    "(f \<circ> E) ` fv_trm t1 \<subseteq> (f ` X)" 
    "(f \<circ> E) ` fv_trm t2 \<subseteq>  (f ` X)" for f
    using assms(6-7) by auto blast+
  obtain g where g_def: "wf_f (TCst \<circ> g)" "f type = (g \<circ> (f' \<circ> final_f)) type"
    "\<forall>t\<in>X. f t = (g \<circ> (f' \<circ> final_f)) t" 
    using half_wty assms(4-5) unfolding half_wty_trm_def by blast
  then have g_typ: "g \<circ> (f' \<circ> final_f \<circ> E) \<turnstile> t1 :: g ((f' \<circ> final_f) type)"
    using wty_f(1) fvi'(1) by (smt (verit, ccfv_SIG) comp_def image_subset_iff wty_trm_fv_cong)
  note t1_none = assms(1)[OF _ fvi(1) g_def(1) g_typ]
  obtain f'' where  f''_def: "check_trm (f' \<circ> final_f \<circ> E) ((f' \<circ> final_f) type) (f' ` final_f ` X) t1 = Some f''" 
    using t1_none by (metis image_comp not_Some_eq)
  have half_wty': "half_wty_trm (f' \<circ> final_f \<circ> E) ((f' \<circ> final_f) type) t1 f'' (f' ` final_f ` X)"
    using check_trm_sound[OF f''_def] fvi(1)[of "f' \<circ> final_f"] unfolding wty_result_fX_trm_def half_wty_trm_def 
    by(simp add: image_image)
  then have "half_wty_trm (f' \<circ> final_f \<circ> E) ((f' \<circ> final_f) type) (trm t1 t2) f'' (f' ` final_f ` X)"
    apply(rule subterm_half_wty) using assms(6) by (auto elim: wty_trm.cases) 
  then have half_wty2: "half_wty_trm (f' \<circ> final_f \<circ> E) ((f' \<circ> final_f) type) (trm t1 t2) f'' ((f' \<circ> final_f) ` X)"
    by (simp add: image_comp)
  obtain g' where g'_def: "wf_f (TCst \<circ> g')" "f type = (g' \<circ> (f'' \<circ> (f' \<circ> final_f))) type"
    "\<forall>t\<in>X. f t = (g' \<circ> (f'' \<circ> (f' \<circ> final_f))) t"
    using half_wty_trm_trans[OF half_wty half_wty2 assms(7)] assms(4-5) unfolding half_wty_trm_def by auto
  then have g'_typ: "g' \<circ> (f'' \<circ> (f' \<circ> final_f) \<circ> E) \<turnstile> t2 :: g' ((f'' \<circ> (f' \<circ> final_f)) type)"
    using wty_f(2) fvi'(2) by (smt (verit, ccfv_SIG) comp_def image_subset_iff wty_trm_fv_cong)
  note t2_none = assms(2)[OF _ fvi(2) g'_def(1) g'_typ]
  show False using t2_none assms(3, 6) f'_def f''_def 
    by(auto simp: check_binop2_def comp_assoc image_image split:option.splits) 
qed

lemma check_conversion_complete: assumes   
  "\<And>E type f X. check_trm E type X t = None \<Longrightarrow> E ` fv_trm t \<subseteq> X \<Longrightarrow>  wf_f (TCst \<circ> f) \<Longrightarrow> f \<circ> E \<turnstile> t :: f type \<Longrightarrow> False"
  "check_trm E type X (trm t) = None"
  "f \<circ> E \<turnstile> trm t :: f type"
  "E ` fv_trm (trm t) \<subseteq> X"
  "trm = trm.F2i \<and> a = TInt \<and> b = TFloat \<or> trm = trm.I2f \<and> a = TFloat \<and> b = TInt"
  "wf_f (TCst \<circ> f)"
 shows False
proof -
 have cp_none: "clash_propagate2 type (TCst a)  E = None \<Longrightarrow> False"
    apply (simp add: clash_prop_comm[where ?t1.0="type"])
    apply (rule constr_complete[where ?t=a and ?P="(\<lambda>x. x = a)" and ?type="type" and ?E=E and ?f="TCst \<circ> f"]) 
   using  assms(1-6) by (auto simp add: comp_def elim:wty_trm.cases) 
  then have "min_type type (TCst a) = Some (TCst a, type)"
    using min_const min_comm by (smt (z3) clash_propagate2_def min_type.elims option.map(1))
  then obtain f' where f'_def: "Some f' = clash_propagate2 (TCst a) type  E" "f' type = TCst a"
    unfolding clash_prop_comm clash_propagate2_def by(auto simp:update_env_def)
  have fa: "f type = a" using assms(3,5) by(auto elim:wty_trm.cases)
  obtain g where g_def: "wf_f (TCst \<circ> g)" "\<forall>t\<in>X. f t = (g \<circ> f') t" "f type = (g \<circ> f') type"
    using check_trm_step0_cst2[OF f'_def(1) assms(6) fa] unfolding resultless_trm_f_def by auto
  have fvi: "(f' \<circ> E) ` fv_trm t \<subseteq> f' ` X" using assms(4,5) by auto blast+
  have "f \<circ> E  \<turnstile> t :: b" using assms(3,5) by (auto elim:wty_trm.cases)
  moreover have "g (TCst b) = b" using g_def(1) unfolding wf_f_def by auto
  ultimately have g_typ: "g \<circ> (f' \<circ> E) \<turnstile> t :: g (TCst b)" 
    using assms(3-5) g_def(2) by auto (smt (verit, best) comp_def image_subset_iff wty_trm_fv_cong)+
  show False using cp_none f'_def assms(2, 5) assms(1)[OF _ fvi g_def(1) g_typ] clash_prop_comm
    by (auto  split: option.splits) 
qed

lemma min_restr:
  assumes "min_type t (f type) = Some a" and "wf_f f"
  shows "min_type t type \<in> range Some"
  using assms unfolding wf_f_def 
  apply(cases "t"; cases type; cases "f type"; auto split:tysym.splits if_splits)
   apply (metis min_comm min_type.simps(11) min_type.simps(12) min_type.simps(8) notin_range_Some option.simps(3) ty.exhaust)
  by (metis assms(2) eq_refinement_min_type notin_range_Some option.simps(3))

lemma check_trm_complete':
 "check_trm  E type X t = None \<Longrightarrow> E ` fv_trm t \<subseteq> X \<Longrightarrow> wf_f (TCst \<circ> f) \<Longrightarrow> f \<circ> E \<turnstile> t :: f type \<Longrightarrow> False"
proof (induction t arbitrary:  E type X f)
  case (Var x)
  have "f (E x) = f type" 
    using Var(4) by (metis comp_apply wty_trm.Var wty_trm_cong_aux)
  then obtain a where *: "min_type (E x) (TCst (f type)) = Some a"
    using eq_refinement_min_type by (metis (mono_tags, lifting) Var.prems(1) Var.prems(3) check_trm.simps(1) clash_propagate2_def comp_def option.distinct(1) option.map(2))
  then have "min_type (E x) type \<in> range Some" 
    using min_restr[OF _ Var(3)] by auto
  then show ?case using Var(1) by(auto simp:clash_propagate2_def)
next
  case (Const x)
  have "f (TCst (ty_of x)) = f type" 
    using Const(4) by (metis Const.prems(3) comp_apply trivial_inst.simps(1) wf_f_def wty_trm.Const wty_trm_cong_aux)
  then obtain a where *: "min_type (TCst (ty_of x)) (TCst (f type)) = Some a"
    using eq_refinement_min_type by (metis Const.prems(4) wf_new_type_symbol wty_trm.Const wty_trm_cong_aux)
  then have "min_type (TCst (ty_of x)) type \<in> range Some" 
    using min_restr[OF _ Const(3)] by auto
  then show ?case using Const(1)by (auto simp add: clash_propagate2_def)
next
  case (Plus t1 t2)
  show ?case 
    using check_binop_complete[where ?trm="trm.Plus", OF _ _ Plus(3) Plus(5-6) _ Plus(4)]
    by auto (metis Plus.IH(1) Plus.IH(2))
next
case (Minus t1 t2)
  show ?case
    using check_binop_complete[where ?trm="trm.Minus", OF _ _ Minus(3) Minus(5-6) _ Minus(4)]
    by auto (metis Minus.IH(1) Minus.IH(2))
next
  case (UMinus t)
  have "clash_propagate2 (TNum 0) (new_type_symbol type) (new_type_symbol \<circ> E) = None \<Longrightarrow> False "
    apply (rule constr_complete[where ?t=TInt and ?P="(\<lambda>x. x \<in> numeric_ty)"]) 
    using  UMinus(2-5)  by (auto simp add: comp_def elim: wty_trm.cases) 
  then obtain f' where f'_def: " Some f' = clash_propagate2 (TNum 0) (new_type_symbol type) (new_type_symbol \<circ> E)"
    by fastforce
  have resless: "resultless_trm_f f (f' \<circ> new_type_symbol) type X"
    using check_trm_step0_num(1)[OF f'_def _ UMinus(4-5)] by (smt (verit, best) insert_iff numeric_ty_def trm.distinct(23) trm.distinct(7) wty_trm.simps)
  have none: "check_trm (f' \<circ> new_type_symbol \<circ> E) (f' (new_type_symbol type)) (f' ` new_type_symbol ` X) t = None " 
    using f'_def UMinus(2) by(auto split:option.splits)
  have fvi: "(f' \<circ> new_type_symbol \<circ> E) ` fv_trm t \<subseteq> f' ` new_type_symbol ` X" 
    using UMinus(3) by auto
  obtain g where g_def: "wf_f (TCst \<circ> g)" "\<forall>t\<in>X. f t = (g \<circ> (f' \<circ> new_type_symbol)) t"
    "f type = (g \<circ> (f' \<circ> new_type_symbol)) type" using resless unfolding resultless_trm_f_def by auto
  have typed': "E \<turnstile> trm.UMinus t :: ty \<Longrightarrow> E  \<turnstile> t :: ty" for E t ty by (auto elim:wty_trm.cases)
  have typed: "g \<circ> (f' \<circ> new_type_symbol \<circ> E) \<turnstile> t :: g (f' (new_type_symbol type))" 
    using typed'[OF UMinus(5)] by (smt (verit, ccfv_SIG) UMinus.prems(2) comp_apply fvi_trm.simps(5) g_def(2) g_def(3) image_subset_iff wty_trm_fv_cong)
  show ?case using UMinus.IH[OF none fvi g_def(1) typed] by auto
next
  case (Mult t1 t2)
  show ?case
    using check_binop_complete[where ?trm="trm.Mult", OF _ _ Mult(3) Mult(5-6) _ Mult(4)]
    by auto (metis Mult.IH(1) Mult.IH(2))
next                                 
case (Div t1 t2)
  show ?case
    using check_binop_complete[where ?trm="trm.Div", OF _ _ Div(3) Div(5-6) _ Div(4)]
    by auto (metis Div.IH(1) Div.IH(2))
next
  case (Mod t1 t2)
  show ?case
    using check_binop_complete[where ?trm="trm.Mod" and ?constr="TCst TInt", OF _ _ Mod(3) Mod(5-6) _ Mod(4)]
    by auto (metis Mod.IH(1) Mod.IH(2))
next
  case (F2i t)
  show ?case
    using check_conversion_complete[where ?trm=trm.F2i, OF _ F2i(2) F2i(5) F2i(3) _ F2i(4)]
    by (metis F2i.IH) 
next
  case (I2f t)
  show ?case
  using check_conversion_complete[where ?trm=trm.I2f, OF _ I2f(2) I2f(5) I2f(3) _ I2f(4)]
  by (metis I2f.IH)  
qed 

(*Theorem 4.3*)
lemma check_trm_complete: 
  "check_trm E type X t = None \<Longrightarrow> E ` fv_trm t \<subseteq> X \<Longrightarrow> wty_result_fX_trm E type t f X \<Longrightarrow> False"
proof -
  assume assm: "check_trm E type X t = None" "E ` fv_trm t \<subseteq> X" "wty_result_fX_trm E type t f X"
  have "wf_f (TCst \<circ> trivial_inst \<circ> f)"
    using assm(3) unfolding wty_result_fX_trm_def using wf_f_comp wf_trivial by presburger
  moreover have "trivial_inst \<circ> f \<circ> E \<turnstile> t :: (trivial_inst \<circ> f) type"
    using assm(3) unfolding wty_result_fX_trm_def by (metis calculation rewriteR_comp_comp wf_trivial)
  ultimately show "False" using check_trm_complete' assm by (metis (no_types, lifting) comp_assoc)
qed

definition check_comparison where
"check_comparison E X t1 t2  \<equiv> (case check_trm (new_type_symbol \<circ> E) (TAny 0) (new_type_symbol ` X) t1  of
   Some f \<Rightarrow> (case check_trm (f \<circ> new_type_symbol \<circ> E) (f (TAny 0)) ((f \<circ> new_type_symbol) `X) t2 of Some f' \<Rightarrow> Some (f' \<circ> f \<circ> new_type_symbol) | None \<Rightarrow> None )
| None \<Rightarrow> None)"

definition check_two_formulas :: "(sig \<Rightarrow> tysenv \<Rightarrow> tysym set \<Rightarrow> tysym Formula.formula  \<Rightarrow>   (tysym \<Rightarrow> tysym) option) \<Rightarrow> sig \<Rightarrow> tysenv  \<Rightarrow> tysym set  \<Rightarrow> tysym Formula.formula  \<Rightarrow> tysym Formula.formula \<Rightarrow>  (tysym \<Rightarrow> tysym) option" where
"check_two_formulas check S E X \<phi> \<psi>  \<equiv> (case check S E X \<phi>  of
   Some f \<Rightarrow> (case check S (f \<circ> E) (f ` X) (formula.map_formula f \<psi>) of Some f' \<Rightarrow> Some (f' \<circ> f) | None \<Rightarrow> None )
   | None \<Rightarrow> None)"

definition check_ands_f :: "(sig \<Rightarrow> tysenv \<Rightarrow> tysym set \<Rightarrow> tysym Formula.formula  \<Rightarrow>   (tysym \<Rightarrow> tysym) option) \<Rightarrow> sig \<Rightarrow> tysenv \<Rightarrow> tysym set \<Rightarrow>  (tysym \<Rightarrow> tysym) option \<Rightarrow> tysym Formula.formula \<Rightarrow>(tysym \<Rightarrow> tysym) option  " where
"check_ands_f check S E X = (\<lambda> f_op \<phi> . case f_op of Some f \<Rightarrow> (case check S (f \<circ> E) (f ` X)(formula.map_formula f \<phi>) of Some f' \<Rightarrow> Some (f' \<circ> f)| None \<Rightarrow> None )
    | None \<Rightarrow> None )"

definition check_ands where
"check_ands check S E X \<phi>s = foldl (check_ands_f check S E X) (Some id) \<phi>s"

definition highest_bound_TAny where
"highest_bound_TAny \<phi> \<equiv> Max ((\<lambda>t. case t of TAny n \<Rightarrow> n | _ \<Rightarrow> 0) ` formula.set_formula \<phi>)"

definition E_empty where
"E_empty \<phi> = (TAny \<circ> (+) (highest_bound_TAny \<phi> + 1))"

fun check_pred :: "tysenv \<Rightarrow> tysym set \<Rightarrow> Formula.trm list \<Rightarrow> ty list \<Rightarrow>  (tysym \<Rightarrow> tysym) option" where
"check_pred  E  X (trm#trms) (t#ts)  = (case check_trm  E (TCst t) X trm of
 Some f \<Rightarrow> (case check_pred  (f\<circ>E) (f `X) trms ts of Some f' \<Rightarrow> Some (f' \<circ>f) | None \<Rightarrow> None)
 | None \<Rightarrow> None)"
|"check_pred  E  X [] []  = Some id"
|"check_pred  E X  _ _  = None"

fun check_regex :: "(sig \<Rightarrow> tysenv  \<Rightarrow> tysym set \<Rightarrow> tysym Formula.formula  \<Rightarrow>   (tysym \<Rightarrow> tysym) option) \<Rightarrow>sig \<Rightarrow> tysenv  \<Rightarrow> tysym set \<Rightarrow> tysym Formula.formula Regex.regex  \<Rightarrow>   (tysym \<Rightarrow> tysym) option"  where
"check_regex check S E X (Regex.Skip l)  = Some id"
| "check_regex check S E X (Regex.Test \<phi>)  = check S E X \<phi>"
| "check_regex check S E X (Regex.Plus r s)  = (case check_regex check S E X r  of
  Some f \<Rightarrow> (case check_regex check S (f \<circ> E) (f ` X) (regex.map_regex (formula.map_formula f) s) of Some f' \<Rightarrow> Some (f' \<circ> f) | None \<Rightarrow> None )
| None \<Rightarrow> None )"
| "check_regex check S E X (Regex.Times r s)  = (case check_regex check S E X r  of
  Some f \<Rightarrow> (case check_regex check S (f \<circ> E) (f ` X) (regex.map_regex (formula.map_formula f) s) of Some f' \<Rightarrow> Some (f' \<circ> f) | None \<Rightarrow> None )
| None \<Rightarrow> None )"
| "check_regex check S E X (Regex.Star r)  = check_regex check S E X r"


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


lemma [fundef_cong]: "(\<And> S E \<phi>' X . size \<phi>' \<le> size \<phi> + size \<psi> \<Longrightarrow> check S E X \<phi>' = check' S E X \<phi>') \<Longrightarrow> check_two_formulas check S E X \<phi> \<psi> = check_two_formulas check' S E X \<phi> \<psi>"
  by (auto simp add: check_two_formulas_def split: option.split ) 

lemma foldl_check_ands_f_fundef_cong: "(\<And> S E \<phi>' X .  size \<phi>' \<le> size_list size \<phi>s \<Longrightarrow> check S E X \<phi>' = check' S E X \<phi>') \<Longrightarrow> foldl (check_ands_f check S E X) f \<phi>s = foldl (check_ands_f check' S E X) f \<phi>s"
  by (induction \<phi>s arbitrary: f) (auto simp: check_ands_f_def split: option.splits)

lemma [fundef_cong]: "(\<And> S E \<phi>' X .  size \<phi>' \<le> size_list size \<phi>s \<Longrightarrow> check S E X \<phi>' = check' S E X \<phi>') \<Longrightarrow> check_ands check S E X \<phi>s = check_ands check' S E X \<phi>s"
  using foldl_check_ands_f_fundef_cong[of \<phi>s check]
  by (auto simp: check_ands_def)

lemma[simp]: "regex.size_regex size (regex.map_regex (formula.map_formula x2) s) = regex.size_regex size s"
  by (induction s)  auto

lemma [fundef_cong]: "(\<And> S E \<phi>' X . size \<phi>' \<le> regex.size_regex size r \<Longrightarrow> check S E X \<phi>' = check' S E X \<phi>') \<Longrightarrow> check_regex check S E X r = check_regex check' S E X r"
   by (induction check S E X r  rule: check_regex.induct) (auto split: option.splits)    
  


fun check :: "sig \<Rightarrow> tysenv \<Rightarrow> tysym set  \<Rightarrow> tysym Formula.formula  \<Rightarrow>   (tysym \<Rightarrow> tysym) option"
  where (*what to do if predicate is not in sigs?*)
  "check S E X (Formula.Pred r ts)  = (case S r of 
  None \<Rightarrow> None 
  | Some tys \<Rightarrow>  check_pred E X ts tys)"
| "check S E X (Formula.Let p \<phi> \<psi>)  = (case check S (E_empty \<phi>) (used_tys (E_empty \<phi>) \<phi>) \<phi> of 
  Some f \<Rightarrow> if \<forall>x \<in> Formula.fv \<phi> . case f ((E_empty \<phi>) x) of TCst _ \<Rightarrow> True | _ \<Rightarrow> False 
      then  check (S(p \<mapsto> tabulate (\<lambda>x. case f ((E_empty \<phi>) x) of TCst t \<Rightarrow> t ) 0 (Formula.nfv \<phi>))) E X \<psi> 
      else None  | None \<Rightarrow> None)"
| "check S E X (Formula.Eq t1 t2)  = check_comparison E X t1 t2 "
| "check S E X (Formula.Less t1 t2)  = check_comparison  E X t1 t2 "
| "check S E X (Formula.LessEq t1 t2)  = check_comparison E X t1 t2 "
| "check S E X (Formula.Neg \<phi>)  =  check S E X \<phi>"
| "check S E X (Formula.Or \<phi> \<psi>)  =  check_two_formulas check S E X \<phi> \<psi>"
| "check S E X (Formula.And \<phi> \<psi>)  = check_two_formulas check S E X \<phi> \<psi>"
| "check S E X (Formula.Ands \<phi>s)  = check_ands check S E X \<phi>s" 
| "check S E X (Formula.Exists t \<phi>)  =   check S (case_nat  t E) X \<phi> " 
| "check S E X (Formula.Agg y (agg_type, d) tys trm \<phi>)  = undefined"
| "check S E X (Formula.Prev I \<phi>)  =  check S E X \<phi> "
| "check S E X (Formula.Next I \<phi>)  =   check S E X \<phi> "
| "check S E X (Formula.Since \<phi> I \<psi>)  = check_two_formulas check S E X \<phi> \<psi>"
| "check S E X (Formula.Until \<phi> I \<psi>) =  check_two_formulas check S E X \<phi> \<psi>  "
| "check S E X (Formula.MatchF I r)  = check_regex check S E X r"
| "check S E X (Formula.MatchP I r)  = check_regex check S E X r "


inductive proven_frm :: "'t Formula.formula \<Rightarrow> bool"
 where
Eq: "proven_frm (Formula.Eq x y)"
| Less: "proven_frm (Formula.Less x y)"
| LessEq: "proven_frm (Formula.LessEq x y)"
| Neg: "proven_frm \<phi> \<Longrightarrow> proven_frm ( Formula.Neg \<phi>)"
| Or: "proven_frm \<phi> \<Longrightarrow>proven_frm  \<psi> \<Longrightarrow>proven_frm ( Formula.Or \<phi> \<psi>)"
| And: "proven_frm \<phi> \<Longrightarrow>proven_frm  \<psi> \<Longrightarrow>proven_frm ( Formula.And \<phi> \<psi>)"
| Exists: "proven_frm \<phi> \<Longrightarrow> proven_frm  (Formula.Exists t \<phi>)"
| Prev: "proven_frm \<phi> \<Longrightarrow>proven_frm ( Formula.Prev \<I> \<phi>)"
| Next: "proven_frm \<phi> \<Longrightarrow>proven_frm ( Formula.Next \<I> \<phi>)"
| Since: "proven_frm \<phi> \<Longrightarrow>proven_frm  \<psi> \<Longrightarrow>proven_frm (Formula.Since \<phi> \<I> \<psi>)" 
| Until: "proven_frm \<phi> \<Longrightarrow>proven_frm  \<psi> \<Longrightarrow>proven_frm (Formula.Until \<phi> \<I> \<psi>)"

lemma proven_frm_map: "proven_frm (formula.map_formula f \<psi>) \<Longrightarrow> proven_frm \<psi>"
  by (induction \<psi> )  (auto intro: proven_frm.intros elim: proven_frm.cases ) 
 lemma proven_frm_map2: " proven_frm \<psi> \<Longrightarrow> proven_frm (formula.map_formula f \<psi>)"
   by (induction \<psi> )  (auto intro: proven_frm.intros elim: proven_frm.cases ) 

lemma check_binary_sound: assumes 
  "\<And>\<phi>' S E f' X. size \<phi>' \<le> size \<phi> + size \<psi> \<Longrightarrow> check S E X \<phi>' = Some f' \<Longrightarrow> proven_frm \<phi>' \<Longrightarrow> used_tys E \<phi>' \<subseteq> X \<Longrightarrow> wty_result_fX S E \<phi>' f' X"
  "check S E X form = Some f'" "used_tys E form \<subseteq> X"
  "proven_frm form" "form \<in> {formula.Or \<phi> \<psi>, formula.And \<phi> \<psi>, formula.Since \<phi> I \<psi>, formula.Until \<phi> I \<psi>}" shows " wty_result_fX S E form f' X"
proof -
  obtain  f where f_def: "check S E X \<phi> = Some  f" using assms by (auto simp add: check_two_formulas_def split: option.splits)
  have wty1: " wty_result_fX S E \<phi> f X" apply (rule assms(1)[OF _ f_def])
    using assms(2-)  unfolding used_tys_def
    by (auto simp: check_two_formulas_def  intro:proven_frm.intros elim: proven_frm.cases split: option.splits)
  obtain f1 where  f1_def: "check S (f\<circ>E) (f `X) (formula.map_formula f \<psi>) = Some  f1 \<and> f' = f1 \<circ> f "
    using assms(2,4,5) f_def
    by (auto simp add: check_two_formulas_def split: option.splits)
  have used_tys_form: "used_tys E form = used_tys E \<phi> \<union> used_tys E \<psi>"
    using assms(5)
    by (auto simp: used_tys_def)
  then have aux: "used_tys (f \<circ> E) (formula.map_formula f \<psi>) \<subseteq> f ` X"
    using assms(3,5) by auto
  have wty2:" wty_result_fX S (f\<circ>E) (formula.map_formula f \<psi>) f1 (f ` X)"
    apply (rule assms(1)) using assms(3,4,5) f1_def aux
    by (auto simp add: proven_frm_map2 comp_def intro:proven_frm.intros elim:proven_frm.cases) 
  have f'_def: "f' = f1 \<circ> f"
    by (auto simp: f1_def)
  have wty_form_iff: "S, f'' \<circ> E \<turnstile> formula.map_formula f'' form \<longleftrightarrow>
    S, f'' \<circ> E \<turnstile> formula.map_formula f'' \<phi> \<and> S, f'' \<circ> E \<turnstile> formula.map_formula f'' \<psi>" for f''
    using assms(5)
    by (auto elim: wty_formula.cases intro: wty_formula.intros)
  show ?thesis
    using wty1 wty2 assms(3) wty_map_formula_cong[of S _ E] 
    apply (auto simp: f'_def used_tys_form wty_form_iff wty_result_fX_def formula.set_map
        formula.map_comp intro: wf_f_comp) 
      apply (smt (z3) comp_apply comp_assoc)
     apply (metis comp_apply comp_assoc wf_f_comp)
    subgoal premises prems for f'' g
    proof -
      have "wf_f (TCst \<circ> (g \<circ> f1))"
        using prems(4,9) wf_f_comp[OF prems(9,4)]
        by (auto simp: comp_assoc)
      then have "(S, (g \<circ> f1 \<circ> f) \<circ> E \<turnstile> formula.map_formula (g \<circ> f1 \<circ> f) \<psi>)"
        using prems(9) spec[OF prems(5), where ?x="g \<circ> f1"]
        by (auto simp: comp_assoc)
      then show ?thesis
        using prems(7)
        apply (rule wty_map_formula_cong)
        using prems(10)
        by auto
    qed
    done
qed

lemma check_comparison_sound: assumes "check S E X form = Some f'"
    "wf_formula form"
   " used_tys E form \<subseteq> X" 
"form \<in> {formula.Less t1 t2,formula.LessEq t1 t2,formula.Eq t1 t2}"
 shows " wty_result_fX S E (formula.Eq t1 t2) f' X"
proof -
 obtain f1 where f1_def: "Some f1 = check_trm (new_type_symbol \<circ> E) (TAny 0) (new_type_symbol ` X) t1" using assms(1,4) by (auto simp add: check_comparison_def split: option.splits)
    then obtain f2 where f2_def: "Some f2 = check_trm (f1 \<circ> new_type_symbol \<circ> E) (f1 (TAny 0)) ((f1 \<circ> new_type_symbol)` X) t2 " using assms(1,4) by (auto simp add: check_comparison_def split: option.splits)
    have wty1: "wty_result_fX_trm (new_type_symbol \<circ> E)  (TAny 0) t1 f1 (new_type_symbol ` X)"  apply (rule check_trm_sound) using f1_def assms(3,4) by (auto simp add: used_tys_def)  fastforce+
    have wty2:  "wty_result_fX_trm (f1\<circ> new_type_symbol \<circ> E) (f1 (TAny 0)) t2 f2 ((f1 \<circ> new_type_symbol) `X)" apply (rule check_trm_sound) using f2_def assms(3,4) by (auto simp add: used_tys_def)  fastforce+
    have f'_def: "f' = f2 \<circ> f1 \<circ> new_type_symbol" using assms(1,4) f1_def f2_def by (auto simp add: check_comparison_def split: option.splits)
   
    show ?thesis using wty1 wty2
      apply (auto simp add: f'_def wty_result_fX_trm_def wty_result_fX_def check_comparison_def split: option.splits 
            elim!: wty_formula.cases )
      subgoal using wf_f_comp[OF _ wf_f_comp[of f1 new_type_symbol], of f2] by (auto simp add: comp_def) subgoal
premises prems  for f'' t
      proof - 
        thm prems 
        define nn where "nn = (\<lambda>t'. case t' of TAny (Suc n) \<Rightarrow> TAny n  | TAny 0 \<Rightarrow> TCst t | TNum n \<Rightarrow> TNum (n-1) | _ \<Rightarrow> t' )"
        have nn_n: "nn \<circ> new_type_symbol = id"  by (auto simp add: nn_def new_type_symbol_def split: tysym.splits nat.splits)
        have wf_nn: "wf_f nn" by (auto simp add: nn_def wf_f_def)
        have "f'' \<circ> nn \<circ> new_type_symbol \<circ> E \<turnstile> t1 :: f'' (nn (TAny 0))" using prems(6)
          apply (auto simp add: comp_assoc nn_n) using prems(5) unfolding nn_def wf_f_def by (auto split: tysym.splits)
        then have "(\<exists>g. wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>X. (f'') t = g (f1 (new_type_symbol t))) \<and> f'' (nn (TAny 0)) = g (f1  (TAny 0)))" using prems(2) wf_f_comp[OF prems(5) wf_nn]
          apply  (auto simp add: nn_n  o_assoc)  by (drule spec[of _ "f'' \<circ>nn"])  (simp add: nn_n pointfree_idE rewriteR_comp_comp)
        then obtain g  where g_def: "wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>X. (f'') t = g (f1 (new_type_symbol t))) \<and> f'' (nn (TAny 0)) = g (f1  (TAny 0))" by auto
        have g_f1_t: "g (f1 (TAny 0)) = t" using g_def nn_def prems(5) wf_f_def by (auto split: tysym.splits)
        have "g \<circ> (f1 \<circ> new_type_symbol \<circ> E) \<turnstile> t2 :: g (f1 (TAny 0))" using prems(7) g_def apply (auto simp add: g_f1_t)
          apply (rule iffD1[OF wty_trm_fv_cong, of _ "f''\<circ>E"]) using assms(3,4) unfolding used_tys_def by fastforce+
          then have "\<exists>g'. wf_f (TCst \<circ> g') \<and> (\<forall>t\<in>X. g (f1 (new_type_symbol t)) = g' (f2 (f1 (new_type_symbol t))))" using g_def prems(4,7) 
          by auto 
         then show ?thesis by (simp add: g_def)
       qed
       subgoal premises prems for f'' g
       proof -
         thm prems
         define nn where "nn = (\<lambda>t'. case t' of TAny (Suc n) \<Rightarrow> TAny n  | TAny 0 \<Rightarrow> TCst (g (f2 (f1 (TAny 0)))) | TNum n \<Rightarrow> TNum (n-1) | _ \<Rightarrow> t' )"
        have nn_n: "nn \<circ> new_type_symbol = id"  by (auto simp add: nn_def new_type_symbol_def split: tysym.splits nat.splits)
        have wf_nn: "wf_f nn" by (auto simp add: nn_def wf_f_def)

        have wt1:"(f'' \<circ> nn \<circ> (new_type_symbol \<circ> E) \<turnstile> t1 :: f''(nn (TAny 0)))" using spec[OF prems(2), of "f'' \<circ> nn"] wf_f_comp[OF prems(5) wf_nn]
          apply (auto simp add: o_assoc) apply (rule exI[of _ "g\<circ>f2"]) using prems(7) wf_f_comp[OF prems(6) prems(3) ] nn_n 
          apply (auto simp add: comp_assoc) 
           apply (metis pointfree_idE) using prems(5) unfolding nn_def wf_f_def by auto  
        have t_eq: "g (f2 (f1 (TAny 0))) = f''(nn (TAny 0))" using prems(5) unfolding nn_def wf_f_def by auto
        have "g \<circ> f2 \<circ> (f1 \<circ> new_type_symbol \<circ> E) \<turnstile> t2 :: (g \<circ> f2) (f1 (TAny 0))" using spec[OF prems(4), of "g \<circ> f2"] 
             wf_f_comp[OF prems(6) prems(3)]  prems(6,7) by (auto simp add: o_assoc)
        then have wt2:"g \<circ> f2 \<circ> (f1 \<circ> new_type_symbol \<circ> E) \<turnstile> t2 :: f''(nn (TAny 0))" by (auto simp add: t_eq)
        show ?thesis  apply (auto  intro!: wty_formula.intros(3-5)[where ?t="f''(nn (TAny 0))"])
           apply (rule iffD1[OF wty_trm_fv_cong wt1]) using prems(7) assms(3) unfolding used_tys_def apply auto apply ( simp add: nn_n pointfree_idE)
          apply (rule iffD1[OF wty_trm_fv_cong wt2]) using prems(7) assms(3,4) unfolding used_tys_def by (fastforce simp add: nn_n pointfree_idE)
      qed done
  qed

(*Theorem 4.6 *)              
lemma check_sound_proven:  "check S E X \<phi> = Some f'  \<Longrightarrow> proven_frm \<phi> \<Longrightarrow> used_tys E \<phi> \<subseteq> X  \<Longrightarrow> wty_result_fX S E \<phi> f' X"
proof (induction S E X \<phi> arbitrary: f' rule:  check.induct)
   case (3 S E X t1 t2) 
      obtain f1 where f1_def: "Some f1 = check_trm (new_type_symbol \<circ> E) (TAny 0) (new_type_symbol ` X) t1" using 3(1) by (auto simp add: check_comparison_def split: option.splits)
    then obtain f2 where f2_def: "Some f2 = check_trm (f1 \<circ> new_type_symbol \<circ> E) (f1 (TAny 0)) ((f1 \<circ> new_type_symbol)` X) t2 " using 3(1) by (auto simp add: check_comparison_def split: option.splits)
    have wty1: "wty_result_fX_trm (new_type_symbol \<circ> E)  (TAny 0) t1 f1 (new_type_symbol ` X)"  apply (rule check_trm_sound) using f1_def 3(3) by (auto simp add: used_tys_def)
    have wty2:  "wty_result_fX_trm (f1\<circ> new_type_symbol \<circ> E) (f1 (TAny 0)) t2 f2 ((f1 \<circ> new_type_symbol) `X)" 
      apply (rule check_trm_sound) using f2_def 3(3) by (auto simp add: used_tys_def)
    have f'_def: "f' = f2 \<circ> f1 \<circ> new_type_symbol" using 3(1) f1_def f2_def by (auto simp add: check_comparison_def split: option.splits)
    show ?case using wty1 wty2 
      apply (auto simp add: f'_def wty_result_fX_trm_def wty_result_fX_def check_comparison_def split: option.splits 
            elim!: wty_formula.cases )
      subgoal using wf_f_comp[OF _ wf_f_comp[of f1 new_type_symbol], of f2] by (auto simp add: comp_def) subgoal
premises prems  for f'' t
      proof - 
        thm prems 
        define nn where "nn = (\<lambda>t'. case t' of TAny (Suc n) \<Rightarrow> TAny n  | TAny 0 \<Rightarrow> TCst t | TNum n \<Rightarrow> TNum (n-1) | _ \<Rightarrow> t' )"
        have nn_n: "nn \<circ> new_type_symbol = id"  by (auto simp add: nn_def new_type_symbol_def split: tysym.splits nat.splits)
        have wf_nn: "wf_f nn" by (auto simp add: nn_def wf_f_def)
        have "f'' \<circ> nn \<circ> new_type_symbol \<circ> E \<turnstile> t1 :: f'' (nn (TAny 0))" using prems(6)
          apply (auto simp add: comp_assoc nn_n) using prems(5) unfolding nn_def wf_f_def by (auto split: tysym.splits)
        then have "(\<exists>g. wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>X. (f'') t = g (f1 (new_type_symbol t))) \<and> f'' (nn (TAny 0)) = g (f1  (TAny 0)))" using prems(2) wf_f_comp[OF prems(5) wf_nn]
          apply  (auto simp add: nn_n  o_assoc)  by (drule spec[of _ "f'' \<circ>nn"])  (simp add: nn_n pointfree_idE rewriteR_comp_comp)
        then obtain g  where g_def: "wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>X. (f'') t = g (f1 (new_type_symbol t))) \<and> f'' (nn (TAny 0)) = g (f1  (TAny 0))" by auto
        have g_f1_t: "g (f1 (TAny 0)) = t" using g_def nn_def prems(5) wf_f_def by (auto split: tysym.splits)
        have "g \<circ> (f1 \<circ> new_type_symbol \<circ> E) \<turnstile> t2 :: g (f1 (TAny 0))" using prems(7) g_def apply (auto simp add: g_f1_t)
          apply (rule iffD1[OF wty_trm_fv_cong, of _ "f''\<circ>E"]) using 3(3) unfolding used_tys_def by auto
          then have "\<exists>g'. wf_f (TCst \<circ> g') \<and> (\<forall>t\<in>X. g (f1 (new_type_symbol t)) = g' (f2 (f1 (new_type_symbol t))))" using g_def prems(4,7) 
          by auto 
         then show ?thesis by (simp add: g_def)
       qed
       subgoal premises prems for f'' g
       proof -
         thm prems
         define nn where "nn = (\<lambda>t'. case t' of TAny (Suc n) \<Rightarrow> TAny n  | TAny 0 \<Rightarrow> TCst (g (f2 (f1 (TAny 0)))) | TNum n \<Rightarrow> TNum (n-1) | _ \<Rightarrow> t' )"
        have nn_n: "nn \<circ> new_type_symbol = id"  by (auto simp add: nn_def new_type_symbol_def split: tysym.splits nat.splits)
        have wf_nn: "wf_f nn" by (auto simp add: nn_def wf_f_def)

        have wt1:"(f'' \<circ> nn \<circ> (new_type_symbol \<circ> E) \<turnstile> t1 :: f''(nn (TAny 0)))" using spec[OF prems(2), of "f'' \<circ> nn"] wf_f_comp[OF prems(5) wf_nn]
          apply (auto simp add: o_assoc) apply (rule exI[of _ "g\<circ>f2"]) using prems(7) wf_f_comp[OF prems(6) prems(3) ] nn_n 
          apply (auto simp add: comp_assoc) 
           apply (metis pointfree_idE) using prems(5) unfolding nn_def wf_f_def by auto  
        have t_eq: "g (f2 (f1 (TAny 0))) = f''(nn (TAny 0))" using prems(5) unfolding nn_def wf_f_def by auto
        have "g \<circ> f2 \<circ> (f1 \<circ> new_type_symbol \<circ> E) \<turnstile> t2 :: (g \<circ> f2) (f1 (TAny 0))" using spec[OF prems(4), of "g \<circ> f2"] 
             wf_f_comp[OF prems(6) prems(3)]  prems(6,7) by (auto simp add: o_assoc)
        then have wt2:"g \<circ> f2 \<circ> (f1 \<circ> new_type_symbol \<circ> E) \<turnstile> t2 :: f''(nn (TAny 0))" by (auto simp add: t_eq)
        show ?thesis  apply (auto  intro!: wty_formula.intros(3-5)[where ?t="f''(nn (TAny 0))"])
           apply (rule iffD1[OF wty_trm_fv_cong wt1]) using prems(7) 3(3) unfolding used_tys_def apply auto apply ( simp add: nn_n pointfree_idE)
          apply (rule iffD1[OF wty_trm_fv_cong wt2]) using prems(7) 3(3) unfolding used_tys_def by (auto simp add: nn_n pointfree_idE)
       qed done
  next
    case (4 S E X t1 t2)
    obtain f1 where f1_def: "Some f1 = check_trm (new_type_symbol \<circ> E) (TAny 0) (new_type_symbol ` X) t1" using 4(1) by (auto simp add: check_comparison_def split: option.splits)
    then obtain f2 where f2_def: "Some f2 = check_trm (f1 \<circ> new_type_symbol \<circ> E) (f1 (TAny 0)) ((f1 \<circ> new_type_symbol)` X) t2 " using 4(1) by (auto simp add: check_comparison_def split: option.splits)
    have wty1: "wty_result_fX_trm (new_type_symbol \<circ> E)  (TAny 0) t1 f1 (new_type_symbol ` X)"  apply (rule check_trm_sound) using f1_def 4(3) by (auto simp add: used_tys_def)
    have wty2:  "wty_result_fX_trm (f1\<circ> new_type_symbol \<circ> E) (f1 (TAny 0)) t2 f2 ((f1 \<circ> new_type_symbol) `X)" apply (rule check_trm_sound) using f2_def 4(3) by (auto simp add: used_tys_def)
    have f'_def: "f' = f2 \<circ> f1 \<circ> new_type_symbol" using 4(1) f1_def f2_def by (auto simp add: check_comparison_def split: option.splits)
    show ?case using wty1 wty2 
      apply (auto simp add: f'_def wty_result_fX_trm_def wty_result_fX_def check_comparison_def split: option.splits 
            elim!: wty_formula.cases )
      subgoal using wf_f_comp[OF _ wf_f_comp[of f1 new_type_symbol], of f2] by (auto simp add: comp_def) subgoal
premises prems  for f'' t
      proof - 
        thm prems 
        define nn where "nn = (\<lambda>t'. case t' of TAny (Suc n) \<Rightarrow> TAny n  | TAny 0 \<Rightarrow> TCst t | TNum n \<Rightarrow> TNum (n-1) | _ \<Rightarrow> t' )"
        have nn_n: "nn \<circ> new_type_symbol = id"  by (auto simp add: nn_def new_type_symbol_def split: tysym.splits nat.splits)
        have wf_nn: "wf_f nn" by (auto simp add: nn_def wf_f_def)
        have "f'' \<circ> nn \<circ> new_type_symbol \<circ> E \<turnstile> t1 :: f'' (nn (TAny 0))" using prems(6)
          apply (auto simp add: comp_assoc nn_n) using prems(5) unfolding nn_def wf_f_def by (auto split: tysym.splits)
        then have "(\<exists>g. wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>X. (f'') t = g (f1 (new_type_symbol t))) \<and> f'' (nn (TAny 0)) = g (f1  (TAny 0)))" using prems(2) wf_f_comp[OF prems(5) wf_nn]
          apply  (auto simp add: nn_n  o_assoc)  by (drule spec[of _ "f'' \<circ>nn"])  (simp add: nn_n pointfree_idE rewriteR_comp_comp)
        then obtain g  where g_def: "wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>X. (f'') t = g (f1 (new_type_symbol t))) \<and> f'' (nn (TAny 0)) = g (f1  (TAny 0))" by auto
        have g_f1_t: "g (f1 (TAny 0)) = t" using g_def nn_def prems(5) wf_f_def by (auto split: tysym.splits)
        have "g \<circ> (f1 \<circ> new_type_symbol \<circ> E) \<turnstile> t2 :: g (f1 (TAny 0))" using prems(7) g_def apply (auto simp add: g_f1_t)
          apply (rule iffD1[OF wty_trm_fv_cong, of _ "f''\<circ>E"]) using 4(3) unfolding used_tys_def by auto
          then have "\<exists>g'. wf_f (TCst \<circ> g') \<and> (\<forall>t\<in>X. g (f1 (new_type_symbol t)) = g' (f2 (f1 (new_type_symbol t))))" using g_def prems(4,7) 
          by auto 
         then show ?thesis by (simp add: g_def)
       qed
       subgoal premises prems for f'' g
       proof -
         thm prems
         define nn where "nn = (\<lambda>t'. case t' of TAny (Suc n) \<Rightarrow> TAny n  | TAny 0 \<Rightarrow> TCst (g (f2 (f1 (TAny 0)))) | TNum n \<Rightarrow> TNum (n-1) | _ \<Rightarrow> t' )"
        have nn_n: "nn \<circ> new_type_symbol = id"  by (auto simp add: nn_def new_type_symbol_def split: tysym.splits nat.splits)
        have wf_nn: "wf_f nn" by (auto simp add: nn_def wf_f_def)

        have wt1:"(f'' \<circ> nn \<circ> (new_type_symbol \<circ> E) \<turnstile> t1 :: f''(nn (TAny 0)))" using spec[OF prems(2), of "f'' \<circ> nn"] wf_f_comp[OF prems(5) wf_nn]
          apply (auto simp add: o_assoc) apply (rule exI[of _ "g\<circ>f2"]) using prems(7) wf_f_comp[OF prems(6) prems(3) ] nn_n 
          apply (auto simp add: comp_assoc) 
           apply (metis pointfree_idE) using prems(5) unfolding nn_def wf_f_def by auto  
        have t_eq: "g (f2 (f1 (TAny 0))) = f''(nn (TAny 0))" using prems(5) unfolding nn_def wf_f_def by auto
        have "g \<circ> f2 \<circ> (f1 \<circ> new_type_symbol \<circ> E) \<turnstile> t2 :: (g \<circ> f2) (f1 (TAny 0))" using spec[OF prems(4), of "g \<circ> f2"] 
             wf_f_comp[OF prems(6) prems(3)]  prems(6,7) by (auto simp add: o_assoc)
        then have wt2:"g \<circ> f2 \<circ> (f1 \<circ> new_type_symbol \<circ> E) \<turnstile> t2 :: f''(nn (TAny 0))" by (auto simp add: t_eq)
        show ?thesis  apply (auto  intro!: wty_formula.intros(3-5)[where ?t="f''(nn (TAny 0))"])
           apply (rule iffD1[OF wty_trm_fv_cong wt1]) using prems(7) 4(3) unfolding used_tys_def apply auto apply ( simp add: nn_n pointfree_idE)
          apply (rule iffD1[OF wty_trm_fv_cong wt2]) using prems(7) 4(3) unfolding used_tys_def by (auto simp add: nn_n pointfree_idE)
       qed done
  next 
    case (5 S E X t1 t2)
       obtain f1 where f1_def: "Some f1 = check_trm (new_type_symbol \<circ> E) (TAny 0) (new_type_symbol ` X) t1" using 5(1) by (auto simp add: check_comparison_def split: option.splits)
    then obtain f2 where f2_def: "Some f2 = check_trm (f1 \<circ> new_type_symbol \<circ> E) (f1 (TAny 0)) ((f1 \<circ> new_type_symbol)` X) t2 " using 5(1) by (auto simp add: check_comparison_def split: option.splits)
    have wty1: "wty_result_fX_trm (new_type_symbol \<circ> E)  (TAny 0) t1 f1 (new_type_symbol ` X)"  apply (rule check_trm_sound) using f1_def 5(3) by (auto simp add: used_tys_def)
    have wty2:  "wty_result_fX_trm (f1\<circ> new_type_symbol \<circ> E) (f1 (TAny 0)) t2 f2 ((f1 \<circ> new_type_symbol) `X)" 
      apply (rule check_trm_sound) using f2_def 5(3) by (auto simp add: used_tys_def)
    have f'_def: "f' = f2 \<circ> f1 \<circ> new_type_symbol" using 5(1) f1_def f2_def by (auto simp add: check_comparison_def split: option.splits)
    show ?case using wty1 wty2 
      apply (auto simp add: f'_def wty_result_fX_trm_def wty_result_fX_def check_comparison_def split: option.splits 
            elim!: wty_formula.cases )
      subgoal using wf_f_comp[OF _ wf_f_comp[of f1 new_type_symbol], of f2] by (auto simp add: comp_def) subgoal
premises prems  for f'' t
      proof - 
        thm prems 
        define nn where "nn = (\<lambda>t'. case t' of TAny (Suc n) \<Rightarrow> TAny n  | TAny 0 \<Rightarrow> TCst t | TNum n \<Rightarrow> TNum (n-1) | _ \<Rightarrow> t' )"
        have nn_n: "nn \<circ> new_type_symbol = id"  by (auto simp add: nn_def new_type_symbol_def split: tysym.splits nat.splits)
        have wf_nn: "wf_f nn" by (auto simp add: nn_def wf_f_def)
        have "f'' \<circ> nn \<circ> new_type_symbol \<circ> E \<turnstile> t1 :: f'' (nn (TAny 0))" using prems(6)
          apply (auto simp add: comp_assoc nn_n) using prems(5) unfolding nn_def wf_f_def by (auto split: tysym.splits)
        then have "(\<exists>g. wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>X. (f'') t = g (f1 (new_type_symbol t))) \<and> f'' (nn (TAny 0)) = g (f1  (TAny 0)))" using prems(2) wf_f_comp[OF prems(5) wf_nn]
          apply  (auto simp add: nn_n  o_assoc)  by (drule spec[of _ "f'' \<circ>nn"])  (simp add: nn_n pointfree_idE rewriteR_comp_comp)
        then obtain g  where g_def: "wf_f (TCst \<circ> g) \<and> (\<forall>t\<in>X. (f'') t = g (f1 (new_type_symbol t))) \<and> f'' (nn (TAny 0)) = g (f1  (TAny 0))" by auto
        have g_f1_t: "g (f1 (TAny 0)) = t" using g_def nn_def prems(5) wf_f_def by (auto split: tysym.splits)
        have "g \<circ> (f1 \<circ> new_type_symbol \<circ> E) \<turnstile> t2 :: g (f1 (TAny 0))" using prems(7) g_def apply (auto simp add: g_f1_t)
          apply (rule iffD1[OF wty_trm_fv_cong, of _ "f''\<circ>E"]) using 5(3) unfolding used_tys_def by auto
          then have "\<exists>g'. wf_f (TCst \<circ> g') \<and> (\<forall>t\<in>X. g (f1 (new_type_symbol t)) = g' (f2 (f1 (new_type_symbol t))))" using g_def prems(4,7) 
          by auto 
         then show ?thesis by (simp add: g_def)
       qed
       subgoal premises prems for f'' g
       proof -
         thm prems
         define nn where "nn = (\<lambda>t'. case t' of TAny (Suc n) \<Rightarrow> TAny n  | TAny 0 \<Rightarrow> TCst (g (f2 (f1 (TAny 0)))) | TNum n \<Rightarrow> TNum (n-1) | _ \<Rightarrow> t' )"
        have nn_n: "nn \<circ> new_type_symbol = id"  by (auto simp add: nn_def new_type_symbol_def split: tysym.splits nat.splits)
        have wf_nn: "wf_f nn" by (auto simp add: nn_def wf_f_def)

        have wt1:"(f'' \<circ> nn \<circ> (new_type_symbol \<circ> E) \<turnstile> t1 :: f''(nn (TAny 0)))" using spec[OF prems(2), of "f'' \<circ> nn"] wf_f_comp[OF prems(5) wf_nn]
          apply (auto simp add: o_assoc) apply (rule exI[of _ "g\<circ>f2"]) using prems(7) wf_f_comp[OF prems(6) prems(3) ] nn_n 
          apply (auto simp add: comp_assoc) 
           apply (metis pointfree_idE) using prems(5) unfolding nn_def wf_f_def by auto  
        have t_eq: "g (f2 (f1 (TAny 0))) = f''(nn (TAny 0))" using prems(5) unfolding nn_def wf_f_def by auto
        have "g \<circ> f2 \<circ> (f1 \<circ> new_type_symbol \<circ> E) \<turnstile> t2 :: (g \<circ> f2) (f1 (TAny 0))" using spec[OF prems(4), of "g \<circ> f2"] 
             wf_f_comp[OF prems(6) prems(3)]  prems(6,7) by (auto simp add: o_assoc)
        then have wt2:"g \<circ> f2 \<circ> (f1 \<circ> new_type_symbol \<circ> E) \<turnstile> t2 :: f''(nn (TAny 0))" by (auto simp add: t_eq)
        show ?thesis  apply (auto  intro!: wty_formula.intros(3-5)[where ?t="f''(nn (TAny 0))"])
           apply (rule iffD1[OF wty_trm_fv_cong wt1]) using prems(7) 5(3) unfolding used_tys_def apply auto apply ( simp add: nn_n pointfree_idE)
          apply (rule iffD1[OF wty_trm_fv_cong wt2]) using prems(7) 5(3) unfolding used_tys_def by (auto simp add: nn_n pointfree_idE)
       qed done
  next
    case (6 S E X \<phi>)
  then have "wty_result_fX S E \<phi> f' X" unfolding used_tys_def by (auto elim: proven_frm.cases) 
   then show ?case  unfolding wty_result_fX_def by (auto intro: wty_formula.intros elim: wty_formula.cases) 
next

  case (7 S E \<phi> \<psi>)
     show ?case apply (rule check_binary_sound) using 7 by auto
 next 
    case (8 S E \<phi> \<psi>)
    show ?case apply (rule check_binary_sound) using 8 by auto
  next
    case (10 S E X t \<phi>) 
    have prv: "proven_frm \<phi>" using 10(3) by cases
    have case_nat_comp: "f'' \<circ> case_nat t E = case_nat (f'' t) (f'' \<circ> E)"   for f'' :: "tysym \<Rightarrow> ty"  by (auto split: nat.splits) 
     have "used_tys (case_nat t E) \<phi> \<subseteq> X" using 10  unfolding  used_tys_def by (auto split: nat.splits) (meson fvi_Suc image_subset_iff)
    then show ?case using 10 prv unfolding wty_result_fX_def apply auto subgoal for f''  apply (drule spec[of _ "f''"]) 
        by (auto simp add: case_nat_comp elim:  wty_formula.cases)
      by (metis case_nat_comp wty_formula.Exists)
next
  case (12 S E X I \<phi>)
  then have "wty_result_fX S E \<phi> f' X" unfolding used_tys_def by (auto elim: proven_frm.cases) 
  then show ?case  unfolding wty_result_fX_def by (auto intro: wty_formula.intros elim: wty_formula.cases) 
next
  case (13 S E X I \<phi>)
then have "wty_result_fX S E \<phi> f' X" unfolding used_tys_def by (auto elim: proven_frm.cases) 
   then show ?case  unfolding wty_result_fX_def by (auto intro: wty_formula.intros elim: wty_formula.cases) 
next
  case (14 S E X \<phi> I \<psi>)
  show ?case apply (rule check_binary_sound) using 14 by auto
next
  case (15 S E X \<phi> I \<psi>)
  show ?case apply (rule check_binary_sound) using 15 by auto
qed (auto elim: proven_frm.cases)

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

(*<*)
end
(*>*)
