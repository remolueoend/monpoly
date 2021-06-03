theory Type_Soundness
  imports Typing
begin
context fixes 
undef_plus :: "event_data \<Rightarrow> event_data \<Rightarrow> event_data" and
undef_minus :: "event_data \<Rightarrow> event_data \<Rightarrow> event_data" and
undef_uminus :: " event_data \<Rightarrow> event_data" and
undef_times :: "event_data \<Rightarrow> event_data \<Rightarrow> event_data" and
undef_divide :: "event_data \<Rightarrow> event_data \<Rightarrow> event_data" and
undef_modulo :: "event_data \<Rightarrow> event_data \<Rightarrow> event_data"  and
undef_double_of_event_data :: "event_data \<Rightarrow> double" and
undef_integer_of_event_data :: "event_data \<Rightarrow> integer" and
undef_less_eq :: "event_data \<Rightarrow> event_data \<Rightarrow> bool" and
undef_eq :: "event_data \<Rightarrow> event_data \<Rightarrow> bool"
assumes undef_plus_sound:  "\<And>x y. EInt x + EInt y = undef_plus (EInt x) (EInt y)" 
    "\<And> x y . EFloat x + EFloat y = undef_plus (EFloat x) (EFloat y)"
assumes undef_minus_sound:  "\<And>x y. EInt x - EInt y = undef_minus (EInt x) (EInt y)" 
    "\<And> x y . EFloat x - EFloat y = undef_minus (EFloat x) (EFloat y)"
assumes undef_uminus_sound:  "\<And>x . - EInt x = undef_uminus (EInt x)"
   "\<And> x. - EFloat x = undef_uminus (EFloat x)"
assumes undef_times_sound:  "\<And>x y. EInt x * EInt y = undef_times (EInt x) (EInt y)" 
    "\<And> x y . EFloat x * EFloat y = undef_times (EFloat x) (EFloat y)"
assumes undef_divide_sound:  "\<And>x y. EInt x div EInt y = undef_divide (EInt x) (EInt y)" 
    "\<And> x y . EFloat x div EFloat y = undef_divide (EFloat x) (EFloat y)"
assumes undef_modulo_sound:  "\<And>x y. EInt x mod EInt y = undef_modulo (EInt x) (EInt y)"  
assumes undef_eq_sound: "\<And>x y. EInt x = EInt y \<longleftrightarrow> undef_eq (EInt x) (EInt y)"
 "\<And>x y. EFloat x = EFloat y \<longleftrightarrow> undef_eq (EFloat x) (EFloat y)"
 "\<And> x y. EString x = EString y \<longleftrightarrow> undef_eq (EString x) (EString y)"

assumes undef_double_of_event_data_sound: "\<And>x. double_of_event_data (EInt x) = undef_double_of_event_data (EInt x)"
assumes undef_integer_of_event_data_sound: "\<And>x. integer_of_event_data (EFloat x) = undef_integer_of_event_data (EFloat x)"

assumes undef_less_eq_sound: "\<And>x y. EInt x \<le> EInt y \<longleftrightarrow> undef_less_eq (EInt x) (EInt y)"
 "\<And>x y. EFloat x \<le> EFloat y \<longleftrightarrow> undef_less_eq (EFloat x) (EFloat y)"
 "\<And> x y. EString x \<le> EString y \<longleftrightarrow> undef_less_eq (EString x) (EString y)"

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
    | (x#xs,_) \<Rightarrow> EFloat ( undef_double_of_event_data (foldl undef_plus x xs) / double_of_int (length (x#xs))))"
| "eval_agg_op' (agg_type.Agg_Med, y0) M =(case (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (xs,_) \<Rightarrow> EFloat (let u = length xs;  u' = u div 2 in
          if even u then
            (undef_double_of_event_data (xs ! (u'-1)) + undef_double_of_event_data (xs ! u') / double_of_int 2)
          else undef_double_of_event_data (xs ! u')))"

fun sat' :: "Formula.trace \<Rightarrow> (Formula.name \<rightharpoonup> nat \<Rightarrow> event_data list set) \<Rightarrow> Formula.env \<Rightarrow> nat \<Rightarrow> 't Formula.formula \<Rightarrow> bool" where
  "sat' \<sigma> V v i (Formula.Pred r ts) = (case V r of
       None \<Rightarrow> (r, map (eval_trm' v) ts) \<in> \<Gamma> \<sigma> i
     | Some X \<Rightarrow> map (eval_trm' v) ts \<in> X i)"
| "sat' \<sigma> V v i (Formula.Let p \<phi> \<psi>) =
    sat' \<sigma> (V(p \<mapsto> \<lambda>i. {v. length v = Formula.nfv \<phi> \<and> sat' \<sigma> V v i \<phi>})) v i \<psi>"
| "sat' \<sigma> V v i (Formula.Eq t1 t2) = undef_eq (eval_trm' v t1) (eval_trm' v t2)"
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
  sorry
lemma soundness:
  assumes "S,E \<turnstile> \<phi>"  "\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y"
  shows "Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> sat' \<sigma> V v i \<phi>" 
 using assms  proof (induction \<phi> arbitrary: v V i S )
case (Pred x1 x2)
  then show ?case sorry
next
  case (Eq E x1 t x2)
  from this have fv_x1: " \<forall>y\<in>fv_trm x1. ty_of (v ! y) = E y " by auto
  from Eq have fv_x2: " \<forall>y\<in>fv_trm x2. ty_of (v ! y) = E y " by auto
  from Eq fv_x2 show ?case using eval_trm_sound  ty_of_eval_trm  apply (cases t)
    using value_of_eval_trm[of E x2 v  ] value_of_eval_trm[of E x1 v  ]
    undef_eq_sound apply auto 
    by blast+

next
  case (Less E x1 t x2)
  sorry
next
  case (LessEq E x1 t x2)
  sorry
next
  case (Agg x1 x2 x3 x4 \<phi>)
  then show ?case sorry
next
  find_theorems Regex.pred_regex regex.atms
  case (MatchF S E x2 x1) 
  from this have "Ball (regex.atms x2) ( \<lambda>\<phi> . S, E \<turnstile> \<phi> \<and> (\<forall>x. (\<forall>ya\<in>fv \<phi>. ty_of (x ! ya) = E ya) \<longrightarrow> (\<forall>xa xb. Formula.sat \<sigma> xa x xb \<phi> = local.sat' \<sigma> xa x xb \<phi>)))"
    by (simp add: regex.pred_set)
  from MatchF have "\<And> \<phi> . \<phi> \<in>  regex.atms x2 \<Longrightarrow> \<forall>ya\<in>fv \<phi>. ty_of (v ! ya) = E ya" apply (auto simp add: regex.pred_set)
  from this have r: "\<phi> \<in> regex.atms x2 \<Longrightarrow> Formula.sat \<sigma> V5 v5 i5 \<phi> = local.sat' \<sigma> V5 v5 i5 \<phi>" for \<phi> V5 v5 i5
    using regex.pred_set apply auto sledgehammer sorry
  then show ?case  using match_cong[OF refl r, where ?r=x2] by auto 
(*   ?x2a5 \<in> regex.atms x2 \<Longrightarrow> Formula.sat \<sigma> ?V5 ?v5 ?i5 ?x2a5 = local.sat' \<sigma> ?V5 ?v5 ?i5 ?x2a5
  then show ?case  using match_cong[OF refl MatchF, where ?r=x2 and ?x2a6="\<lambda>i j. j"] by auto *)
next
  case (MatchP x1 x2) then show ?case sorry
  (*then show ?case  using match_cong[OF refl MatchP, where ?r=x2 and ?x2a6="\<lambda>i j. j"] by auto *)

qed (auto split: nat.splits)

end
end