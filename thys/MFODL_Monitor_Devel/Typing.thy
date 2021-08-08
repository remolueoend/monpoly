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
     Some (E', t_typ) \<Rightarrow>
          (case check_trm E' t_typ t2  of
             Some (E'', t_typ2) \<Rightarrow> Some ( E'', t_typ2 )
            | None \<Rightarrow> None ) 
     | None \<Rightarrow> None)
  | None \<Rightarrow> None )"

lemma [fundef_cong]: "(\<And>  E typ t . size t \<le> size t1 + size t2 \<Longrightarrow> check_trm E typ t = check_trm' E typ t) \<Longrightarrow> check_binop check_trm E typ t1 t2 exp_typ = check_binop check_trm' E typ t1 t2 exp_typ"
 by (auto simp add: check_binop_def split: option.split ) 

lemma [fundef_cong]: "(\<And>  E typ t . size t \<le> size t1 + size t2 \<Longrightarrow> check_trm E typ t = check_trm' E typ t) \<Longrightarrow> check_binop2 check_trm E typ t1 t2 exp_typ = check_binop2 check_trm' E typ t1 t2 exp_typ"
 by (auto simp add: check_binop2_def split: option.split ) 
(*2nd propagate needed?*)
fun check_trm :: "tysenv \<Rightarrow> tysym \<Rightarrow> Formula.trm  \<Rightarrow> (tysenv * tysym) option" where
"check_trm E typ (Formula.Var v) = clash_propagate2 typ (E v) E "
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
|"check_trm E typ (Formula.UMinus t)  = (case clash_propagate2 (TNum 0) typ (new_type_symbol \<circ> E) of 
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
"check_comparison S E \<omega> t1 t2  \<equiv> (case check_trm   (new_type_symbol \<circ> E) (TAny 0) t1  of
   Some (E',t1_typ ) \<Rightarrow> (case check_trm  E' t1_typ t2  of Some (E'', t2_typ) \<Rightarrow> Some (propagate_constraints t1_typ t2_typ E'', (\<omega> t1 t2) ) | None \<Rightarrow> None)
| None \<Rightarrow> None)"

definition check_two_formulas where
"check_two_formulas check S E \<phi> \<psi>  \<equiv> (case check S E \<phi>  of
   Some (E', \<phi>') \<Rightarrow> (case check S E' \<psi>  of 
        Some (E'', \<psi>') \<Rightarrow> Some (E'',  \<phi>', \<psi>') 
        | None \<Rightarrow> None) 
   | None \<Rightarrow> None)"

primrec check_ands :: "(sig \<Rightarrow> tysenv \<Rightarrow> tysym Formula.formula  \<Rightarrow>  (tysenv * tysym Formula.formula) option) \<Rightarrow>sig \<Rightarrow> tysenv \<Rightarrow>  tysym Formula.formula list \<Rightarrow>  (tysenv * tysym Formula.formula list) option" where
"check_ands check S E (\<phi>#\<phi>s)  = (case check S E \<phi>  of
 Some (E',\<phi>') \<Rightarrow> (case check_ands check S E' \<phi>s  of 
    Some (E'', \<phi>'s) \<Rightarrow> Some(E'', \<phi>'#\<phi>'s)
    |None \<Rightarrow> None)
 | None \<Rightarrow> None)"
|"check_ands check S E []  = Some (E,[])"

fun check_pred :: "sig \<Rightarrow> tysenv \<Rightarrow> Formula.trm list \<Rightarrow> tysym list \<Rightarrow>  (tysenv) option" where
"check_pred  S E (f#fs) (t#ts)  = (case check_trm  E t f  of
 Some (E', new_t) \<Rightarrow> Some E'
 | None \<Rightarrow> None)"
|"check_pred  S E [] []  = Some E"
|"check_pred  S E _ _  = None"


fun check_regex :: "(sig \<Rightarrow> tysenv \<Rightarrow> tysym Formula.formula  \<Rightarrow>  (tysenv * tysym Formula.formula) option) \<Rightarrow>sig \<Rightarrow> tysenv \<Rightarrow>  tysym Formula.formula Regex.regex  \<Rightarrow>  (tysenv * tysym Formula.formula Regex.regex) option"  where
"check_regex check S E (Regex.Skip l)  = Some (E, Regex.Skip l)"
| "check_regex check S E (Regex.Test \<phi>)  = (case check S E \<phi>  of Some (E', \<phi>') \<Rightarrow>Some (E', Regex.Test \<phi>')| None \<Rightarrow> None )"
| "check_regex check S E (Regex.Plus r s)  = (case check_regex check S E r  of
  Some(E', r') \<Rightarrow> (case check_regex check S E' s  of
      Some(E'',s') \<Rightarrow> Some(E'',Regex.Plus r' s'))
| None \<Rightarrow> None )"
| "check_regex check S E (Regex.Times r s)  = (case check_regex check S E r  of
  Some(E', r') \<Rightarrow> (case check_regex check S E' s  of
      Some(E'',s') \<Rightarrow> Some(E'',Regex.Times r' s'))
| None \<Rightarrow> None )"
| "check_regex check S E (Regex.Star r)  = (case check_regex check S E r  of
  Some(E', r') \<Rightarrow>  Some(E',Regex.Star r')
| None \<Rightarrow> None )"


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

lemma [fundef_cong]: "(\<And> S E \<phi>' . size \<phi>' \<le> size \<phi> + size \<psi> \<Longrightarrow> check S E \<phi>' = check' S E \<phi>') \<Longrightarrow> check_two_formulas check S E \<phi> \<psi> = check_two_formulas check' S E \<phi> \<psi>"
  by (auto simp add: check_two_formulas_def split: option.split) 

lemma [fundef_cong]: "(\<And> S E \<phi>' . \<phi>' \<in> regex.atms r \<Longrightarrow> check S E \<phi>' = check' S E \<phi>') \<Longrightarrow> check_regex check S E r = check_regex check' S E r"
   apply (induction r arbitrary: S E) apply auto 
  by presburger+

lemma [fundef_cong]: "(\<And> S E \<phi>' .  \<phi>' \<in> set \<phi>s  \<Longrightarrow> check S E \<phi>' = check' S E \<phi>') \<Longrightarrow> check_ands check S E \<phi>s = check_ands check' S E \<phi>s"
  apply (induction \<phi>s arbitrary: E) apply auto
  by presburger


fun check :: "sig \<Rightarrow> tysenv \<Rightarrow> tysym Formula.formula  \<Rightarrow>  (tysenv * tysym Formula.formula) option"
  where (*what to do if predicate is not in sigs?*)
  "check S E (Formula.Pred r ts)  = (case S r of 
  None \<Rightarrow> None 
  | Some tys \<Rightarrow> (case check_pred S E ts (map TCst tys) of
        Some E' \<Rightarrow> Some (E',Formula.Pred r ts) 
        | None \<Rightarrow> None  ))"
| "check S E (Formula.Let p \<phi> \<psi>)  = (case check S (\<lambda>n. TAny n) \<phi> of 
  Some (E', \<phi>') \<Rightarrow> if \<forall>x \<in> Formula.fv \<phi> . case E' x of TCst _ \<Rightarrow> True | _ \<Rightarrow> False 
      then  (case check (S(p \<mapsto> tabulate (\<lambda>x. case E' x of TCst t \<Rightarrow> t ) 0 (Formula.nfv \<phi>))) E \<psi> of 
          Some (E'', \<psi>') \<Rightarrow> Some(E'', Formula.Let p \<phi>' \<psi>')
          | None \<Rightarrow> None) 
      else None
  | None \<Rightarrow> None)"
| "check S E (Formula.Eq t1 t2)  = check_comparison S E Formula.Eq t1 t2 "
| "check S E (Formula.Less t1 t2)  = check_comparison S E Formula.Less t1 t2 "
| "check S E (Formula.LessEq t1 t2)  = check_comparison S E Formula.LessEq t1 t2 "
| "check S E (Formula.Neg \<phi>)  = (case check S E \<phi>  of Some (E', \<phi>') \<Rightarrow> Some (E',Formula.Neg \<phi>') | None \<Rightarrow> None)"
| "check S E (Formula.Or \<phi> \<psi>)  = (case check_two_formulas check S E \<phi> \<psi> of Some (E', \<phi>',\<psi>') \<Rightarrow> Some (E', Formula.Or \<phi>' \<psi>') | None \<Rightarrow> None) "
| "check S E (Formula.And \<phi> \<psi>)  = (case check_two_formulas check S E \<phi> \<psi> of Some (E', \<phi>',\<psi>') \<Rightarrow> Some (E', Formula.And \<phi>' \<psi>') | None \<Rightarrow> None)"
| "check S E (Formula.Ands \<phi>s)  = (case check_ands check S E \<phi>s  of Some (E',\<phi>'s) \<Rightarrow> Some (E', Formula.Ands \<phi>'s) | None \<Rightarrow> None)"
| "check S E (Formula.Exists t \<phi>)  = (case check S (case_nat t E) \<phi> of Some(E', \<phi>') \<Rightarrow> Some (E'\<circ> (+) 1, Formula.Exists (E' 0) \<phi>') | None \<Rightarrow> None)"
| "check S E (Formula.Agg y (agg_type, d) tys f \<phi>)  = (case check_trm  (new_type_symbol \<circ> (agg_tysenv E tys )) (agg_trm_tysym agg_type) f of
   Some (E', trm_type) \<Rightarrow> (case check S E' \<phi> of 
       Some (E'', \<phi>') \<Rightarrow> (case clash_propagate ((E''\<circ> (+) (length tys)) y) (TCst (ty_of d) ) (E''\<circ> (+) (length tys)) of 
          Some (E''', ret_t) \<Rightarrow> (case clash_propagate ret_t (agg_ret_tysym agg_type trm_type) E''' of 
              Some (E4, t4) \<Rightarrow>  Some (E4, Formula.Agg y (agg_type,d) (tabulate E'' 0 (Formula.nfv \<phi>) ) f \<phi>' )
               | None \<Rightarrow> None )
          | None \<Rightarrow> None)
       | None \<Rightarrow> None)
   | None \<Rightarrow> None)"
| "check S E (Formula.Prev I \<phi>)  =  (case check S E \<phi>  of Some (E', \<phi>') \<Rightarrow> Some (E',Formula.Prev I \<phi>') | None \<Rightarrow> None)"
| "check S E (Formula.Next I \<phi>)  =  (case check S E \<phi>  of Some (E', \<phi>') \<Rightarrow> Some (E',Formula.Next I \<phi>') | None \<Rightarrow> None)"
| "check S E (Formula.Since \<phi> I \<psi>)  = (case check_two_formulas check S E \<phi> \<psi> of Some (E', \<phi>',\<psi>') \<Rightarrow> Some (E', Formula.Since \<phi>' I \<psi>') | None \<Rightarrow> None) "
| "check S E (Formula.Until \<phi> I \<psi>) =  (case check_two_formulas check S E \<phi> \<psi> of Some (E', \<phi>',\<psi>') \<Rightarrow> Some (E', Formula.Until \<phi>' I \<psi>') | None \<Rightarrow> None) "
| "check S E (Formula.MatchF I r)  = (case check_regex check S E r  of Some (E', r') \<Rightarrow> Some (E', Formula.MatchF I r') | None \<Rightarrow> None )"
| "check S E (Formula.MatchP I r)  = (case check_regex check S E r  of Some (E', r') \<Rightarrow> Some (E', Formula.MatchP I r') | None \<Rightarrow> None )"


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


definition check_safe :: "sig \<Rightarrow> unit Formula.formula \<Rightarrow> (tyenv * ty Formula.formula) option" where
  "check_safe S \<phi> = map_option 
  (\<lambda>(E,\<phi>).  ((\<lambda>x. case E x of TCst t' \<Rightarrow> t'), Formula.map_formula (\<lambda>t. case t of TCst t' \<Rightarrow> t') \<phi>))
     (case unitToSym \<phi> 0 of (\<phi>', n ) \<Rightarrow> check S (\<lambda> k. TAny (n + k) ) \<phi>')"

definition tysenvless :: "tysenv \<Rightarrow> tysenv \<Rightarrow> bool" where
  "tysenvless E E' \<longleftrightarrow> (\<forall>x. tyless  (E x) (E' x))"

definition wf_f :: "(tysym \<Rightarrow> tysym) \<Rightarrow> bool" where
"wf_f f \<equiv> (\<forall>x. f (TCst x) = TCst x) \<and> (\<forall>n . case f (TNum n) of TCst x \<Rightarrow> x \<in> numeric_ty | TNum x \<Rightarrow> True | _ \<Rightarrow> False)"

definition "resultless_trm E' E typ' typ \<longleftrightarrow> (\<exists> f. wf_f f \<and>   E' = f \<circ> E  \<and> typ' = f typ)"


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


lemma min_comm: "min_type a b =  min_type b a"
  by (induction a b rule: min_type.induct)  auto

lemma min_consistent: assumes "min_type a b = Some(x,y)" shows "x = a \<and> y=b \<or> x = b \<and> y = a"
  using assms by (induction a b rule: min_type.induct) (auto split: if_splits)

lemma min_const: assumes "min_type (TCst x) y = Some(a,b)" shows "a = TCst x"
  using assms by (induction "TCst x" y rule: min_type.induct) (auto split: if_splits)
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
 
lemma resultless_trm_trans: assumes " resultless_trm E'' E' type'' type'" "resultless_trm E' E type' type"   
  shows "resultless_trm E'' E type'' type"
proof -
  obtain f where  f_def: "wf_f f" " E' = f \<circ> E " "type' = f type" using assms by (auto simp add: resultless_trm_def)
  obtain g where  g_def: "wf_f g"  "E'' = g \<circ> E'"  "type'' = g type'" using assms by (auto simp add: resultless_trm_def)
  have "wf_f (g \<circ> f)" using f_def(1) g_def(1)  apply (auto simp add: wf_f_def split: tysym.splits) by (metis tysym.exhaust)+
  moreover have "E'' = g \<circ> f \<circ> E" using f_def(2) g_def(2) by auto
    ultimately show ?thesis using f_def(3) g_def(3) by (auto simp add: resultless_trm_def)
  qed

lemma assumes "resultless_trm (TCst \<circ> E'') E (TCst type'') type" "resultless_trm E' E type' type" 
"E'' \<turnstile> t :: type''"   " check_trm E type t = Some (E', type')"
shows "resultless_trm (TCst \<circ> E'') E'  (TCst type'') type'"
   using assms apply (induction t ) apply (auto simp add: resultless_trm_def clash_propagate2_def elim: wty_trm.cases)  
  oops


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
    "Some (newt, oldt) = min_type (TNum 0) (new_type_symbol type)" 
  shows  " typ'' \<in> numeric_ty"
  using assms 
  apply (induction "TNum 0" "new_type_symbol type" rule: min_type.induct)
  by (auto simp add: resultless_trm_def  numeric_ty_def new_type_symbol_def wf_f_def split: tysym.splits ) 

lemma resless_wty_const_dir2: assumes 
"resultless_trm E1 E2 (TCst typ'') newt"
    "Some (newt, oldt) = min_type (TCst t) type"
  shows "typ'' = t"
  using assms  min_const[of t type ]
  by (auto simp add: eq_commute[where ?a="Some(newt,oldt)"] resultless_trm_def wf_f_def) 

definition wty_result_trm :: " Formula.trm \<Rightarrow> tysenv \<Rightarrow> tysym \<Rightarrow> tysenv \<Rightarrow> tysym \<Rightarrow> bool" where
 "wty_result_trm  t E typ E' typ' \<longleftrightarrow> resultless_trm E' E typ' typ \<and> 
(\<forall>E'' typ'' .   resultless_trm (TCst \<circ>  E'') E (TCst typ'') typ \<longrightarrow> ( E'' \<turnstile> t :: typ'' \<longleftrightarrow> resultless_trm (TCst \<circ>  E'') E' (TCst typ'') typ' ))"

lemma wty_result_trm_alt: "wty_result_trm t E typ E' typ' \<longleftrightarrow>  (resultless_trm E' E typ' typ \<and> 
(\<forall>E'' typ'' .   ( E'' \<turnstile> t :: typ'' \<and>  resultless_trm (TCst \<circ>  E'') E (TCst typ'') typ \<longleftrightarrow> resultless_trm (TCst \<circ>  E'') E' (TCst typ'') typ' )))"
  apply (auto simp add: wty_result_trm_def) 
  using resultless_trm_trans by blast+


lemma assumes
    "Some (E1, precise_type) = clash_propagate2 (TNum 0) (new_type_symbol type) (new_type_symbol \<circ> E)" 
    "\<And>E'' y . (E'' \<turnstile> t :: y) \<Longrightarrow> y \<in> numeric_ty"
  shows "wty_result_trm t E type E1 precise_type "
proof -
  obtain  oldt where t_def: "Some (precise_type,oldt) = min_type (TNum 0) (new_type_symbol type)" using assms(1)
    by (cases "min_type (TNum 0) (new_type_symbol type)")   (auto simp add:  clash_propagate2_def ) 
  then have E1_def: "E1 =  update_env (precise_type, oldt) (new_type_symbol \<circ> E)" using assms(1) 
    apply (cases "min_type (TNum 0) (new_type_symbol type)")  by (auto simp add:  clash_propagate2_def ) 
  then have f1: "resultless_trm E1 E precise_type type"
      using  t_def resultless_trm_trans[of "update_env (precise_type, oldt) (new_type_symbol \<circ> E)"] resless_newtype[of E type] 
        some_min_resless[of "new_type_symbol type" "TNum 0" "(precise_type,oldt)" "new_type_symbol \<circ> E"]
      by  (auto simp add: min_comm[where ?b="new_type_symbol type"])
    then show ?thesis    apply (auto simp add:    wty_result_trm_def) subgoal for E'' typ''
        using assms(1) assms(2)[of E'' typ''] resless_wty_num[of E'' E typ'' type precise_type oldt ]
    
    sorry
  qed
lemma assumes   " E'' \<turnstile> t :: typ''"
  "resultless_trm (TCst \<circ> E'') E (TCst typ'') type" 
  "resultless_trm E' E type' type"
shows "resultless_trm (TCst \<circ> E'') E' (TCst typ'') type'" 
  using assms apply (induction t)  apply (auto simp add: wty_result_trm_def resultless_trm_def  elim: wty_trm.cases) subgoal for x f fa 
    apply (rule exI[of _ " (\<lambda>t. if type' = t then TCst typ'' else f t)"])
    apply (auto simp add:  wf_f_def split: ty.splits tysym.splits) 
    oops

lemma check_mod_sound: assumes "\<And>E E' type type' . check_trm E type t1 = Some (E', type') \<Longrightarrow> wty_result_trm t1 E type E' type'"
  "\<And>E E' type type' . check_trm E type t2 = Some (E', type') \<Longrightarrow> wty_result_trm t2 E type E' type'"
    "check_trm E type (trm.Mod t1 t2) = Some (E', type')" 
shows " wty_result_trm (trm.Mod t1 t2) E type E' type'"
proof -
  obtain newt oldt where t_def: "Some (newt,oldt) = min_type (TCst TInt)  type" using assms   by (auto simp add: check_binop2_def clash_propagate2_def  split: option.splits)
    then have upd: "resultless_trm (update_env (newt, oldt) E) E newt type " using  some_min_resless[of " type" "TCst TInt" "(newt,oldt)" "E"] 
      by  (auto simp add: min_comm[where ?b="type"])
    obtain E1 t_typ where  E1_def: "Some (E1,t_typ) = check_trm (update_env (newt, oldt) E) newt t1" using assms   t_def
      by (auto simp add: check_binop2_def clash_propagate2_def split: option.splits) 
    then have E'_def: "Some (E',type') = check_trm E1 t_typ t2" using assms  t_def by (auto simp add: check_binop2_def clash_propagate2_def split: option.splits) 
   have wty_res2: "wty_result_trm t2 E1 t_typ E' type'" using E'_def assms(2)  by auto
    have wty_res1: "wty_result_trm t1 (update_env (newt, oldt) E) newt E1 t_typ" using E1_def t_def assms(1) by auto
     { 
      fix E'' typ''
      assume wty: " E'' \<turnstile> trm.Mod t1 t2 :: typ''"
      assume "resultless_trm (TCst \<circ> E'') E (TCst typ'') type"
      then have "resultless_trm (TCst \<circ> E'') E' (TCst typ'') type'" 
        using t_def resless_wty_const  wty_res1 wty_res2  wty  assms(3)
        unfolding wty_result_trm_def  by (auto elim: wty_trm.cases)
    }moreover{
      fix E'' typ''
      assume resE': "resultless_trm (TCst \<circ> E'') E' (TCst typ'') type'"
      assume resE: "resultless_trm (TCst \<circ> E'') E (TCst typ'') type"
      have  "resultless_trm  (TCst \<circ> E'') E1  (TCst typ'') t_typ" "resultless_trm (TCst \<circ> E'') (update_env (newt, oldt) E) (TCst typ'') newt" 
        using resultless_trm_trans[of "TCst \<circ> E''" E' _ _ E1 ] resE' resultless_trm_trans wty_res1 wty_res2  t_def
         apply (auto simp add: wty_result_trm_def) 
        by blast
      then have " E'' \<turnstile> trm.Mod t1 t2 :: typ''"  using    assms wty_res2 wty_res1 t_def resE' resultless_trm_trans
          resless_wty_const_dir2[of "TCst \<circ> E''" "update_env (newt, oldt) E" typ'' newt oldt TInt type ]
        by (auto simp add: wty_result_trm_def  Mod ) 
    }
    
    ultimately show ?thesis using wty_res1 wty_res2 resultless_trm_trans[of E' E1 type' t_typ "update_env (newt, oldt) E" newt]
        resultless_trm_trans[of E' "update_env (newt, oldt)  E"  type' newt E type ] upd
      by (auto simp add: check_binop_def wty_result_trm_def ) 
  qed

lemma check_binop_sound: assumes "\<And>E E' type type' . check_trm E type t1 = Some (E', type') \<Longrightarrow> wty_result_trm t1 E type E' type'"
  "\<And>E E' type type' . check_trm E type t2 = Some (E', type') \<Longrightarrow> wty_result_trm t2 E type E' type'"
  "check_trm E type (trm t1 t2) = Some (E', type')" "trm \<in> {trm.Plus, trm.Minus, trm.Mult, trm.Div}"
shows " wty_result_trm (trm t1 t2) E type E' type'"
proof -
  obtain newt oldt where t_def: "Some (newt,oldt) = min_type (TNum 0) (new_type_symbol type)" using assms
    by (auto simp add: check_binop2_def clash_propagate2_def split: option.splits)
    then have f1: "resultless_trm (update_env (newt, oldt) (new_type_symbol \<circ> E)) E newt type"
      using t_def resultless_trm_trans[of "update_env (newt, oldt) (new_type_symbol \<circ> E)"] resless_newtype[of E type] 
        some_min_resless[of "new_type_symbol type" "TNum 0" "(newt,oldt)" "new_type_symbol \<circ> E"]
      by  (auto simp add: min_comm[where ?b="new_type_symbol type"])
    obtain E1 t_typ where  E1_def: "Some (E1,t_typ) = check_trm (update_env (newt, oldt) (new_type_symbol \<circ> E)) newt t1" using assms   t_def
      by (auto simp add: check_binop2_def clash_propagate2_def split: option.splits) 
    then have E'_def: "Some (E',type') = check_trm E1 t_typ t2" using assms  t_def by (auto simp add: check_binop2_def clash_propagate2_def split: option.splits)
    have wty_res2: "wty_result_trm t2 E1 t_typ E' type'" using E'_def assms(2)  by auto
    have wty_res1: "wty_result_trm t1 (update_env (newt, oldt) (new_type_symbol \<circ> E)) newt E1 t_typ" using E1_def t_def assms(1) by auto
    { 
      fix E'' typ''
      assume wty: " E'' \<turnstile> trm t1 t2 :: typ''"
      assume "resultless_trm (TCst \<circ> E'') E (TCst typ'') type"
      then have "resultless_trm (TCst \<circ> E'') E' (TCst typ'') type'" 
        using t_def resless_wty_num  wty_res1 wty_res2 resultless_trm_trans wty  assms(4)
        unfolding wty_result_trm_def  by (auto elim: wty_trm.cases)
    }moreover{
      fix E'' typ''
      assume resE': "resultless_trm (TCst \<circ> E'') E' (TCst typ'') type'"
      assume resE: "resultless_trm (TCst \<circ> E'') E (TCst typ'') type"
      have  reses: "resultless_trm  (TCst \<circ> E'') E1  (TCst typ'') t_typ" "resultless_trm (TCst \<circ> E'') (update_env (newt, oldt) (new_type_symbol \<circ> E)) (TCst typ'') newt" 
        using resultless_trm_trans[of "TCst \<circ> E''" E' _ _ E1 ] resE' resultless_trm_trans wty_res1 wty_res2 
         apply (auto simp add: wty_result_trm_def)  by blast       
      then have " E'' \<turnstile> trm t1 t2 :: typ''"  using   assms(4) wty_res2 wty_res1 resE' resE resless_wty_num_dir2[of "TCst \<circ> E''" "(update_env (newt, oldt) (new_type_symbol \<circ> E))"] t_def
        by (auto simp add: wty_result_trm_def intro: wty_trm.intros) 
    }
    ultimately show ?thesis using f1 wty_res1 wty_res2 resultless_trm_trans[of E' E1 type' t_typ "update_env (newt, oldt) (new_type_symbol \<circ> E)" newt]
        resultless_trm_trans[of E' "update_env (newt, oldt) (new_type_symbol \<circ> E)"  type' newt E type ]
      by (auto simp add: check_binop_def wty_result_trm_def )

qed

lemma check_trm_sound: " check_trm  E type t = Some (E', type') \<Longrightarrow> wty_result_trm t E type E' type'"
  thm tysym.inject
proof (induction t arbitrary:  E type E' type')                                     
  case (Var x)
  {
    fix fa type'' E''
    assume  fa_def: " TCst type'' = fa type'" "wf_f fa"  "TCst \<circ> E'' = fa \<circ> (E')"
    from this have " E'' \<turnstile> trm.Var x :: type''" 
      using Var fa_def(3)  using min_consistent
                  apply (auto simp add:  clash_propagate2_def  eq_commute[where ?b= "E x"] comp_def  update_env_def intro!: wty_trm.Var split: if_splits ) 
      by (metis tysym.inject(3))
  }moreover
  { fix f type'' E'' 
    assume  "E'' \<turnstile> trm.Var x :: type''"
    then have x_type: "E'' x = type''" by cases
    assume  f_def: "wf_f f" " TCst \<circ> E'' = f \<circ> E " "TCst type'' = f type"
    define g where g_def: "g = (\<lambda>t. if type' = t then TCst type'' else f t)"
    have "resultless_trm (TCst \<circ> E'') (E') (TCst type'') type'" 
      using  x_type f_def  Var apply (auto simp add: clash_propagate2_def resultless_trm_def) apply (rule exI[of _ g])
      apply (auto simp add: update_env_def g_def comp_def wf_f_def  split: if_splits dest!: min_consistent) 
      by metis+  
  }
  ultimately show ?case using Var some_min_resless
    by (auto simp add: clash_propagate2_def wty_result_trm_def resultless_trm_def)
next
  case (Const x)
   { fix f type'' E'' 
    assume  "E'' \<turnstile> trm.Const x :: type''"
    then have x_type: "ty_of x = type''" by cases
    assume  f_def: "wf_f f" " TCst \<circ> E'' = f \<circ> E " "TCst type'' = f type"
    define g where g_def: "g = (\<lambda>t. if type' = t then TCst type'' else f t)"
    have "resultless_trm (TCst \<circ> E'') (E') (TCst type'') type'" 
      using  x_type f_def  Const apply (auto simp add: clash_propagate2_def resultless_trm_def) apply (rule exI[of _ g])
      apply (auto simp add: update_env_def g_def comp_def wf_f_def  split: if_splits dest!: min_consistent) 
      by metis+  
  } moreover{
 fix fa type'' E''
    assume  fa_def: "wf_f fa" " TCst type'' = fa type'"   "TCst \<circ> E'' = fa \<circ> (E')"
    from this have " E'' \<turnstile> trm.Const x :: type''" 
      using Const fa_def(3)  using min_const
      apply (auto simp add:  clash_propagate2_def  wf_f_def comp_def  update_env_def intro!: wty_trm.Const split: if_splits  )   
      by (metis tysym.inject(3))
  }
   ultimately show ?case  using Const some_min_resless min_comm by (auto simp add: clash_propagate2_def wty_result_trm_def resultless_trm_def) 
   next
     case (Plus t1 t2)
     then show ?case using check_binop_sound by auto
     next
case (Minus t1 t2)
     then show ?case using check_binop_sound by auto
next
  case (UMinus t)
  then obtain E1 precise_type where E1_def: "Some (E1, precise_type) = clash_propagate2 (TNum 0) type (new_type_symbol \<circ> E)" by (auto split: option.splits)
  have "wty_result_trm t E1 precise_type E' type'"  apply  (rule UMinus.IH) using UMinus(2) E1_def by (auto split: option.splits) 
  then show ?case using E1_def UMinus apply (auto simp add: clash_propagate2_def wty_result_trm_def)
next
  case (Mult t1 t2)
     then show ?case using check_binop_sound by auto
next
  case (Div t1 t2)
     then show ?case using check_binop_sound by auto
next
case (Mod t1 t2)
     then show ?case using check_mod_sound by auto
next
  case (F2i t)
  then show ?case sorry
next
  case (I2f t)
  then show ?case sorry
qed 

(*
 case (Var x)
  { assume assm: "tyless type (E x)"
    then have t': "type' = type" using Var apply  (auto simp add: clash_propagate_def) by (cases " type_clash type (E x)") auto
    let ?f = "(\<lambda>t. if E x = t then type else t)" 
    have "wf_f ?f" using assm Var apply (auto simp add: clash_propagate_def wf_f_def numeric_ty_def split: tysym.splits) 
      apply (meson option.distinct(1)) subgoal for x3 n by (cases x3)  auto done
    moreover have f_E': "?f \<circ> E = E'" using Var assm by (auto simp add: clash_propagate_def split: if_splits) 
    moreover have "type' = ?f type" using  t' by auto
    ultimately have  "resultless_trm E' E type' type" by (auto simp add: resultless_trm_def) 
    moreover { fix E'' type'' fa
    assume wty: "E'' \<turnstile> trm.Var x :: type''" and  fa_def: "wf_f fa "   "TCst  \<circ> E'' = fa \<circ> E "  "TCst type'' = fa type"
    let ?g = "(\<lambda>t. if type = t then TCst type'' else fa t)"
    have g1: "wf_f ?g" using   fa_def by (auto simp add: wf_f_def) 
    have "\<And>y. (fa \<circ> E) y = ((\<lambda>t. if type = t then TCst type'' else fa t) \<circ> ((\<lambda>t. if E x = t then type else t) \<circ> E)) y " 
      using fa_def wty apply auto
       by (metis comp_eq_elim wty_trm.Var wty_trm_cong_aux)
     then have g2: " TCst  \<circ> E'' = ?g \<circ> E'" using  f_E' fa_def by auto
      have res_less'': "resultless_trm (TCst \<circ> E'') E' (TCst type'') type'"  using g1 g2 fa_def t' by (auto simp add: wf_f_def resultless_trm_def)
    }
moreover
    {
      fix fa type'' E''
      assume  " TCst type'' = fa type" "wf_f fa" "TCst \<circ> E'' = fa \<circ> (?f \<circ> E)"
      from this have " E'' \<turnstile> trm.Var x :: type''" apply (cases type'') using  t' apply (auto  simp add: wf_f_def split: ty.splits) 
        by (smt (z3) comp_def tysym.inject wty_trm.Var)+
    }
    ultimately have ?case  using f_E' t'  apply (auto simp add: clash_propagate_def wty_result_trm_def resultless_trm_def) 
        subgoal for f E'' type'' fa   using resultless_trm_trans[of "TCst \<circ> E''" E' "TCst type''" type' E type] by (auto simp add: resultless_trm_def) done
    } moreover {
      assume assm: "\<not> tyless type (E x)"
    then have t': "type' = E x" using Var apply  (auto simp add: clash_propagate_def) by (cases " type_clash type (E x)") auto
    let ?f = "(\<lambda>t. if type = t then E x else t)" 
    have "wf_f ?f" using assm Var apply (auto simp add: clash_propagate_def wf_f_def numeric_ty_def split: tysym.splits )
      subgoal for x2 xa by (cases x2)  auto done
    moreover have f_E': "?f \<circ> E = E'" using Var assm apply (auto simp add: clash_propagate_def) by (cases " type_clash type (E x)") auto
    moreover have "type' = ?f type" using  t' by auto
    ultimately have  "resultless_trm E' E type' type" by (auto simp add: resultless_trm_def) 
    moreover { fix E'' type'' fa
    assume wty: "E'' \<turnstile> trm.Var x :: type''" and  fa_def: "wf_f fa "   "TCst  \<circ> E'' = fa \<circ> E "  "TCst type'' = fa type"
    let ?g = "(\<lambda>t. if E x = t then TCst type'' else fa t)"
    have g1: "wf_f ?g" using   fa_def apply (auto simp add: wf_f_def) 
      by (metis comp_eq_dest wty wty_trm.Var wty_trm_cong_aux)+ 
    have "\<And>y. (fa \<circ> E) y = (?g \<circ> (?f \<circ> E)) y " 
      using fa_def wty apply auto
       by (metis comp_eq_elim wty_trm.Var wty_trm_cong_aux)
     then have g2: " TCst  \<circ> E'' = ?g \<circ> E'" using  f_E' fa_def by auto
     have g3: "TCst type'' = ?g type'" using fa_def t' by auto
      have res_less'': "resultless_trm (TCst \<circ> E'') E' (TCst type'') type'"  using g1 g2 fa_def t' by (auto simp add: wf_f_def resultless_trm_def)
    }
moreover
    {
      fix fa type'' E''
      assume  " TCst type'' = fa type'" "wf_f fa" "TCst \<circ> E'' = fa \<circ> (?f \<circ> E)"
      from this have " E'' \<turnstile> trm.Var x :: type''" apply (cases type'') using  t' apply (auto  simp add: wf_f_def split: ty.splits) 
          by (smt (z3) comp_def tysym.inject wty_trm.Var)+
    } 
 ultimately have ?case  using f_E' t'  apply (auto simp add: clash_propagate_def wty_result_trm_def resultless_trm_def) 
        subgoal for f E'' type'' fa  using resultless_trm_trans[of "TCst \<circ> E''" E' "TCst type''" type' E type] by (auto simp add: resultless_trm_def) done
    } ultimately show ?case by auto
next
  case (Const x)
 
  have no_tc: "\<not> type_clash  (TCst (ty_of x)) type" using Const by (auto simp add: clash_propagate_def )
  let ?f = "(\<lambda>t. if t = type  then TCst (ty_of x) else t)"
  have "wf_f ?f" using Const no_tc apply (auto simp add: wf_f_def clash_propagate_def numeric_ty_def) by (cases x)  auto
  moreover have f_E': "E' = ?f \<circ> E" using Const  no_tc by (auto simp add:  clash_propagate_def ) 
  ultimately have "resultless_trm E' E type' type" using Const no_tc by (auto simp add:  clash_propagate_def resultless_trm_def) 
  moreover {
      fix fa type'' E''
      assume  " TCst type'' = fa type'" "wf_f fa" "TCst \<circ> E'' = fa \<circ> (E')"
      from this have " E'' \<turnstile> trm.Const x :: type''" apply (cases type'') using Const no_tc  by (auto  simp add:  wf_f_def clash_propagate_def wty_trm.Const)
    }
    moreover {
      fix E'' type'' fa
    assume wty: "E'' \<turnstile> trm.Const x :: type''" and  fa_def: "wf_f fa "   "TCst  \<circ> E'' = fa \<circ> E "  "TCst type'' = fa type"
    have " \<And>y. (fa \<circ> E) y = (fa \<circ> ((\<lambda>t. if t = type then TCst (ty_of x) else t) \<circ> E)) y "  using wty fa_def by (auto simp add: wf_f_def elim: wty_trm.cases)
      then have g2: " TCst  \<circ> E'' = fa \<circ> E'" using  f_E' fa_def by auto 
      have g3: "TCst type'' = fa type'" using fa_def wty Const no_tc  apply  (auto simp add: clash_propagate_def wf_f_def elim!: wty_trm.cases) by metis
     have res_less'': "resultless_trm (TCst \<circ> E'') E' (TCst type'') type'"  using g2 g3 fa_def(1)  by (auto simp add: resultless_trm_def) 
    }
    ultimately show ?case using Const    no_tc apply (auto simp add:  wty_result_trm_def clash_propagate_def resultless_trm_def)
      subgoal for f E'' type'' fa  using resultless_trm_trans[of "TCst \<circ> E''" E' "TCst type''" type' E type] by (auto simp add: resultless_trm_def) done
next 
  case (Plus t1 t2)
  let ?prec_type = "if tyless (TNum 0) type then TNum 0 else type"
  obtain E_temp t1_typ where temp: " check_trm (propagate_constraints type ?prec_type (new_type_symbol E)) ?prec_type t1 = Some (E_temp, t1_typ)" using Plus
    apply  (auto simp add: check_binop_def )  apply (cases "type_clash type (TNum 0)") apply auto
    by (cases " check_trm (propagate_constraints type ?prec_type (new_type_symbol E)) ?prec_type t1")  auto
 then obtain E'' t2_typ where final: "check_trm (propagate_constraints t1_typ ?prec_type E_temp) t1_typ t2 = Some (E', type')" using Plus  apply  (auto simp add: check_binop_def )  apply (cases "type_clash type (TNum 0)") apply auto
    apply (cases " check_trm (propagate_constraints type ?prec_type (new_type_symbol E)) ?prec_type t1")  apply auto by (cases " check_trm (propagate_constraints t1_typ ?prec_type E_temp) t1_typ t2")  auto
   then have "wty_result_trm t2 (propagate_constraints t1_typ ?prec_type E_temp) t1_typ E' type'"
     by (rule Plus(2))
   show ?case using Plus apply (auto simp add: check_binop_def  )
next
*)

lemma check_trm_complete: " check_trm  E typ t = None \<Longrightarrow> wty_result_trm t E typ E' typ' \<Longrightarrow> False"
  sorry

definition "resultless E' E \<phi>' \<phi>  \<longleftrightarrow> (\<exists> f. wf_f f \<and>   E' = f \<circ> E \<and> formula.rel_formula (\<lambda>x y. x = f y) \<phi>' \<phi>)"  

definition wty_result :: "sig \<Rightarrow> tysenv \<Rightarrow> tysym Formula.formula \<Rightarrow> tysenv \<Rightarrow> tysym Formula.formula \<Rightarrow> bool" where
  "wty_result S E \<phi> E' \<phi>' \<longleftrightarrow> resultless E' E \<phi>' \<phi> \<and> 
(\<forall>E'' \<phi>'' .   S, E'' \<turnstile> \<phi>'' \<longleftrightarrow> resultless (TCst \<circ>  E'') E' (Formula.map_formula TCst \<phi>'') \<phi>' )"

lemma check_sound: "wf_formula \<phi> \<Longrightarrow> check S E \<phi> = Some (E', \<phi>') \<Longrightarrow> wty_result S E \<phi> E' \<phi>'"
  sorry

lemma check_safe_sound: "safe_formula \<phi> \<Longrightarrow> check_safe S \<phi> = Some (E', \<phi>') \<Longrightarrow>
  wty_formula S E' \<phi>' \<and> formula.rel_formula (\<lambda>_ _. True) \<phi> \<phi>'"
  sorry (* using check_sound[of S Map.empty "formula.map_formula Map.empty \<phi>" E' \<phi>']
  by (auto simp: check_safe_def wty_result_def formula.rel_map)
*)
lemma check_complete: "check S E \<phi> = None \<Longrightarrow> wf_formula \<phi> \<Longrightarrow> wty_result S E \<phi> E' \<phi>' \<Longrightarrow>
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

(*<*)
end
(*>*)
