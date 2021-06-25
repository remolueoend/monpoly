theory Type_Soundness
  imports Typing
begin

context sat_general
begin

lemma safe_neg_eq: "safe_formula (Formula.Neg (Formula.Eq x1 x2)) \<Longrightarrow> safe_formula  (Formula.Eq x1 x2) \<or>
(Formula.sat \<sigma> V v i  (Formula.Neg (Formula.Eq x1 x2)) \<longleftrightarrow> sat' \<sigma> V v i  (Formula.Neg (Formula.Eq x1 x2))) "
  by (cases x1; cases x2) auto
                                                                              
lemma foldl_eq_type: assumes " \<forall>x\<in>set (x22). ty_of x = t" "ty_of x21 = t" "t \<in> agg_trm_type agg_op" 
    "undef_op = undef_min \<and> op = min \<and>  agg_op=Formula.Agg_Min \<or> 
undef_op = undef_max \<and> op = max\<and>  agg_op=Formula.Agg_Max \<or>
 undef_op = undef_plus \<and> op= (+)\<and>  agg_op=Formula.Agg_Sum"
  shows "foldl undef_op x21 x22 = foldl op x21 x22" 
proof -
  {assume "undef_op = undef_min \<and> op = min \<or> undef_op = undef_max \<and> op = max"
    from this assms(1-2) have ?thesis
     proof (induction x22 arbitrary: x21 t)
       case (Cons a x22)
       then show ?case   apply (simp add: min_def undef_min_def max_def undef_max_def) 
         using undef_less_eq_sound  by (cases x21; cases a) fastforce+ 
     qed auto
   }
   moreover 
   {
     assume "undef_op = undef_plus \<and> op = (+) \<and>  agg_op=Formula.Agg_Sum"
 from this assms(1-3) have ?thesis
     proof (induction x22 arbitrary: x21 t)
       case (Cons a x22)
       then show ?case using undef_plus_sound   apply (cases x21; cases a) apply (auto simp add: numeric_ty_def)
         
         using ty_of.simps by blast+
     qed auto
   }
   ultimately show ?thesis  using assms(4) by auto
 qed

lemma eval_agg_op_sound: 
  assumes "M={(x, ecard Zs) | x Zs. Zs =
   {zs. length zs = length tys \<and> Formula.sat \<sigma> V (zs @ v) i \<phi> \<and> Formula.eval_trm (zs @ v) f = x} \<and> Zs \<noteq> {}}"
"S, E \<turnstile> formula.Agg y (agg_op,d) tys f \<phi> " "wty_envs S \<sigma> V" "fv_trm f \<subseteq> fv \<phi>" "Formula.nfv \<phi> \<le> length tys + length v"
"safe_formula \<phi>" 
shows "eval_agg_op (agg_op,d) M = eval_agg_op' (agg_op,d) M"
proof -
  from assms(2) obtain t where t_def: "agg_env E tys  \<turnstile> f :: t" and t_wty:"t \<in> agg_trm_type agg_op" by cases auto
 have fv_wty: "y\<in>fv_trm f \<Longrightarrow> length zs = length tys \<Longrightarrow> Formula.sat \<sigma> V (zs @ v) i \<phi> \<Longrightarrow> ty_of ((zs @ v) ! y) = agg_env E tys y" for y zs apply (rule ty_of_sat_safe)
        using    assms by (auto elim: wty_formula.cases)
      then  have wty_M: "\<forall>(x,card) \<in>  M . ty_of x = t" using assms(1)  t_def by (auto dest!: ty_of_eval_trm )
      have "finite_multiset M \<Longrightarrow>set (flatten_multiset M) \<subseteq> fst ` M" apply (rule set_of_flatten_multiset)
        using finite_set 
       apply (auto simp add:  assms(1)) using finite_fst by (auto simp add: finite_multiset_def assms(1) ) 
      then have wty_flatten: "finite_multiset M \<Longrightarrow> \<forall>x \<in> set (flatten_multiset M) . ty_of x = t"  using wty_M 
        by fastforce

    show ?thesis 
      apply (cases agg_op) apply (auto split: list.splits) using 
      subgoal for x21 x22
        apply (cases "finite_multiset M")
         using wty_flatten apply auto apply (thin_tac "flatten_multiset M = x21 # x22") apply (induction x22) 
        using undef_less_eq_sound  assms(1)  apply (auto simp add: undef_min_def split: ty.splits) subgoal for a x23
          by (cases x21; cases a) (auto simp add: undef_min_def min_def) 
        subgoal for a x23
          apply (cases x21; cases a) apply (auto simp add: undef_min_def min_def) sledgehammer
        subgoal for x21 x22
apply (cases "finite_multiset M")
         using wty_flatten apply auto  apply (induction x22 arbitrary: x21) 
        using undef_less_eq_sound  assms(1)  apply (auto simp add: undef_min_def split: ty.splits) subgoal for a x23
          by (cases x21; cases a) (auto simp add: undef_min_def min_def)

lemma soundness:
  assumes   "safe_formula \<phi>"  "S,E \<turnstile> \<phi>" "\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y" "wty_envs S \<sigma> V"
   "Formula.nfv \<phi> \<le> length v"
 shows "Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> sat' \<sigma> V v i \<phi>" 

 using assms proof (induction arbitrary: v V i S E rule: safe_formula_induct)

  case (Pred e tms)
  from Pred(2)  obtain p  tys where obt: "S p = Some tys \<and> list_all2 (\<lambda>tm ty. E \<turnstile> tm :: ty) tms tys" by cases auto
   from this  Pred  have tms_wty: "x \<in> set tms \<Longrightarrow> \<exists>t \<in> set tys. E \<turnstile> x :: t " for x 
     by (metis in_set_conv_nth list_all2_conv_all_nth)
   have eval_tms_eq: "map (Formula.eval_trm v) tms = map (eval_trm' v) tms" using tms_wty Pred(3) by (auto dest!: eval_trm_sound)
  then show ?case using Pred(1)  apply (auto simp add: trm.is_Var_def trm.is_Const_def)
    by (metis eval_tms_eq )+
    
  next 
    case (Let p \<phi> \<psi>) 
    obtain E' where  psi_wty: "S(p \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E \<turnstile> \<psi>" and phi_wty:"S, E' \<turnstile> \<phi>" using Let.prems(1) by cases auto

    have wtyenv: " x\<in>\<Gamma> \<sigma> i\<Longrightarrow> (case x of (p, xs) \<Rightarrow> p \<notin> dom V \<longrightarrow> (case S p of None \<Rightarrow> False | Some ts \<Rightarrow> wty_tuple ts xs))" for x i
      using Let.prems(3) by  (auto simp add: wty_envs_def wty_event_def wty_tuple_def) 
    have ty_of_phi: "x \<in> Formula.fv \<phi> \<Longrightarrow>  Formula.sat \<sigma> V xs i \<phi> \<Longrightarrow> length xs = Formula.nfv \<phi> \<Longrightarrow> ty_of (xs!x) = E' x" 
      for x xs apply (rule ty_of_sat_safe) using Let phi_wty by auto 
    have "x \<in> Formula.fv \<phi> \<Longrightarrow>  Formula.sat \<sigma> V xs i \<phi> \<Longrightarrow> length xs = Formula.nfv \<phi> \<Longrightarrow> (tabulate E' 0 (Formula.nfv \<phi>)!x) = ty_of (xs!x)"
      for x xs using ty_of_phi[of x xs]  apply (auto simp add: Formula.nfv_def split: nat.splits)
      by (metis Formula.nfv_def add.left_neutral fvi_less_nfv nth_tabulate)
    then  have list_all_tab:"length xs = Formula.nfv \<phi> \<Longrightarrow>
    Formula.sat \<sigma> V xs i \<phi> \<or> sat' \<sigma> V xs i \<phi> \<Longrightarrow> list_all2 (\<lambda>t x. ty_of x = t) (tabulate E' 0 (Formula.nfv \<phi>)) xs " for xs i 
    proof -
      assume a1: "Formula.sat \<sigma> V xs i \<phi> \<or> sat' \<sigma> V xs i \<phi>"
      assume a2: "length xs = Formula.nfv \<phi>"
      obtain nn :: "event_data list \<Rightarrow> ty list \<Rightarrow> (ty \<Rightarrow> event_data \<Rightarrow> bool) \<Rightarrow> nat" where
        "\<forall>x0 x1 x2. (\<exists>v3<length x1. \<not> x2 (x1 ! v3) (x0 ! v3)) = (nn x0 x1 x2 < length x1 \<and> \<not> x2 (x1 ! nn x0 x1 x2) (x0 ! nn x0 x1 x2))"
        by moura
      then have "\<forall>p ts es. (\<not> list_all2 p ts es \<or> length ts = length es \<and> (\<forall>n. \<not> n < length ts \<or> p (ts ! n) (es ! n))) \<and> (list_all2 p ts es \<or> length ts \<noteq> length es \<or> nn es ts p < length ts \<and> \<not> p (ts ! nn es ts p) (es ! nn es ts p))"
        by (metis (no_types) list_all2_conv_all_nth)
      then show ?thesis
        using a2 a1 
        by (smt (z3) Let.hyps(1) Let.hyps(2) Let.prems(3) add.left_neutral atLeastLessThan_iff dual_order.refl length_tabulate less_nat_zero_code not_less nth_tabulate phi_wty subset_eq ty_of_sat'_safe ty_of_sat_safe)
    qed
    have phi_case: "length v5 = Formula.nfv \<phi> \<Longrightarrow>  sat' \<sigma> V v5 i5 \<phi> = Formula.sat \<sigma> V v5 i5 \<phi> " for v5 i5
    proof -
      assume len_v5: "length v5 = Formula.nfv \<phi>"
      {
        assume sat: " Formula.sat \<sigma> V v5 i5 \<phi>"
        have "y \<in> fv \<phi> \<Longrightarrow> ty_of (v5 ! y) = E' y" for y apply (rule ty_of_sat_safe) using Let sat len_v5 phi_wty by auto
        then have " Formula.sat \<sigma> V v5 i5 \<phi> = sat' \<sigma> V v5 i5 \<phi> " 
          using phi_wty Let len_v5 by auto
      }moreover {
          assume sat': "sat' \<sigma> V v5 i5 \<phi>"
        have "y \<in> fv \<phi> \<Longrightarrow> ty_of (v5 ! y) = E' y" for y apply (rule ty_of_sat'_safe) using Let sat' len_v5 phi_wty by auto
        then have " Formula.sat \<sigma> V v5 i5 \<phi> = sat' \<sigma> V v5 i5 \<phi> "   
          using phi_wty Let len_v5 by auto
      }
      ultimately show ?thesis by auto
    qed
    have V_eq: "V(p \<mapsto> \<lambda>i. {v. length v = Formula.nfv \<phi> \<and> Formula.sat \<sigma> V v i \<phi>}) = V(p \<mapsto> \<lambda>i. {v. length v = Formula.nfv \<phi> \<and> sat' \<sigma> V v i \<phi>})"
      using phi_case  by fastforce
    have "Formula.sat \<sigma> (V(p \<mapsto> \<lambda>i. {v. length v = Formula.nfv \<phi> \<and> Formula.sat \<sigma> V v i \<phi>})) v i \<psi> = sat' \<sigma> (V(p \<mapsto> \<lambda>i. {v. length v = Formula.nfv \<phi> \<and> Formula.sat \<sigma> V v i \<phi>})) v i \<psi>"     
      apply (rule Let.IH(2))
      using  psi_wty    phi_wty Let.prems apply (auto simp add: wty_envs_def wty_event_def wty_tuple_def domIff)
      subgoal for i a b apply (cases "a = p") by auto  subgoal for i xs using list_all_tab[of  xs i] by auto done
  then show ?case by (auto simp add: V_eq)
next
  case (And_assign \<phi> \<psi>)
  obtain t1 t2 where eq: "\<psi> = formula.Eq t1 t2" using And_assign(2) by (auto simp add: safe_assignment_def split: formula.splits)
  obtain t where t_def: "E \<turnstile> t1 :: t \<and> E \<turnstile> t2 :: t" using  And_assign(4) by (auto simp add: eq  elim: wty_formula.cases)
  have " Formula.sat \<sigma> V v i \<psi> = sat' \<sigma> V v i \<psi>" using  t_def And_assign(4,5) by (auto simp add: eq dest: poly_value_of )
  then show ?case using And_assign by (auto elim: wty_formula.cases)

next
  case (And_constraint \<phi> \<psi>)
  have phi_eq: "Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" using And_constraint by (auto elim: wty_formula.cases)
  have psi_wty: "S, E \<turnstile> \<psi>" using And_constraint(7) by (auto elim: wty_formula.cases)
   show ?case using phi_eq And_constraint(5,8)  psi_wty
    by (cases \<psi> rule: is_constraint.cases)
   (auto simp add: undef_less_eq_sound undef_less_def less_event_data_def dest: poly_value_of  elim!: wty_formula.cases)
next
  case (And_Not \<phi> \<psi>)
  have "S, E \<turnstile> \<psi>" using And_Not.prems(1) by (auto elim: wty_formula.cases)
  then show ?case using And_Not by (auto elim: wty_formula.cases)
next
  case (Ands l pos neg)
  have pos_IH: "\<phi> \<in> set pos \<Longrightarrow> S, E \<turnstile> \<phi> \<Longrightarrow> (\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y) \<Longrightarrow> Formula.nfv \<phi> \<le> length v \<Longrightarrow>  wty_envs S \<sigma> V
\<Longrightarrow>  Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for \<phi> using Ands.IH(1) Ball_set_list_all   by (smt (verit, best))
    have pos_case: "\<phi> \<in> set pos \<Longrightarrow>  Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi> " for \<phi> using Ands pos_IH by (auto elim: wty_formula.cases)
  have neg_IH: "\<phi> \<in> set (map remove_neg neg) \<Longrightarrow> S, E \<turnstile> \<phi> \<Longrightarrow> (\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y) \<Longrightarrow> Formula.nfv \<phi> \<le> length v \<Longrightarrow>  wty_envs S \<sigma> V
\<Longrightarrow>  Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for \<phi> using Ands.IH(2) Ball_set_list_all 
    by (smt (verit, best))
  have "\<phi> \<in> set ( neg) \<Longrightarrow> S, E \<turnstile> \<phi> \<and> (\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y) \<and> Formula.nfv \<phi> \<le> length v " for \<phi> using Ands by (auto elim: wty_formula.cases)
  then have "\<phi> \<in> set ( map remove_neg neg) \<Longrightarrow> S, E \<turnstile> \<phi> \<and> (\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y) \<and> Formula.nfv \<phi> \<le> length v" for \<phi> 
    apply (auto simp add: Formula.nfv_def )
    subgoal for x by (cases x) (auto elim: wty_formula.cases) done
  then have remove_neg_case: "\<phi> \<in> set (map remove_neg neg) \<Longrightarrow>  Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi> " for \<phi> using Ands.prems(3) neg_IH by auto
  have remove_neg_sat: " (Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi> )= ( Formula.sat \<sigma> V v i (remove_neg \<phi>) = sat' \<sigma> V v i (remove_neg \<phi>))  " 
    for \<phi>  by (cases \<phi>)  auto
   have neg_case: "\<phi> \<in> set neg\<Longrightarrow>  Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for \<phi> 
    using  remove_neg_case[of "remove_neg \<phi>"]  by ( auto simp add:  remove_neg_sat[of \<phi>] )    
  then show ?case using pos_case neg_case Ands(1) by auto

next
  case (Exists \<phi> t)
 {
    fix za
    assume  assm: "Formula.sat \<sigma> V (za # v) i \<phi>" 
    from Exists.prems(1) have wty: "S, case_nat t E \<turnstile> \<phi>" by cases
    have nfv: " Formula.nfv \<phi> \<le> Suc (length v)" using Exists(6) nfv_exists[of \<phi> t] by auto
    have "0 \<in> fv \<phi> \<Longrightarrow> ty_of za = t" 
      using ty_of_sat_safe[where ?E="case_nat t E" and ?S=S and ?\<phi>=\<phi> and ?v="za#v" and ?V=V and ?i=i and ?\<sigma>=\<sigma> and ?x=0]  
      Exists(1,5)  nfv assm wty by auto 
    then have "\<forall>y\<in>fv \<phi>. ty_of ((za # v) ! y) = (case y of 0 \<Rightarrow> t | Suc x \<Rightarrow> E x)" using  Exists.prems(2)   by (auto simp add:  fvi_Suc split: nat.splits )

    from this  have "local.sat' \<sigma> V (za # v) i \<phi>" using Exists.IH[of S "case_nat t E" "za#v" V i] Exists(5) wty nfv assm by auto
  }
  moreover {
   fix za
    assume  assm: "sat' \<sigma> V (za # v) i \<phi>" 
    from Exists.prems(1) have wty: "S, case_nat t E \<turnstile> \<phi>" by cases
    have nfv: " Formula.nfv \<phi> \<le> Suc (length v)" using Exists(6) nfv_exists[of \<phi> t] by auto
    have "0 \<in> fv \<phi> \<Longrightarrow> ty_of za = t" 
      using ty_of_sat'_safe[where ?E="case_nat t E" and ?S=S and ?\<phi>=\<phi> and ?v="za#v" and ?V=V and ?i=i and ?\<sigma>=\<sigma> and ?x=0]  
      Exists(1,5)  nfv assm wty by auto 
    then have "\<forall>y\<in>fv \<phi>. ty_of ((za # v) ! y) = (case y of 0 \<Rightarrow> t | Suc x \<Rightarrow> E x)" using  Exists.prems(2)   by (auto simp add:  fvi_Suc split: nat.splits )

    from this  have "Formula.sat \<sigma> V (za # v) i \<phi>" using Exists.IH[of S "case_nat t E" "za#v" V i] Exists(5) wty nfv assm by auto
  }
  ultimately show ?case   by auto 
next
  case (Agg y \<omega> tys f \<phi>) 
  (*{
    assume assm: "Formula.sat \<sigma> V v i (formula.Agg y \<omega> tys f \<phi>)"
    have " \<forall>a\<in>Formula.fvi (length tys) \<phi>.  a < length v " using Agg.prems(4)  apply (auto simp add: Formula.nfv_def) using Suc_le_lessD by blast
    then have "\<forall>a\<in>Formula.fv \<phi>.  a < length tys + length v" using fvi_plus_bound[of 0 "length tys" \<phi> "length v"] by auto
    then have  "\<forall>a\<in>Formula.fv \<phi>.  a - length v < length tys"  using diff_less_eq finite_fvi   sorry
    then have "sat' \<sigma> V v i (formula.Agg y \<omega> tys f \<phi>)" using  assm Agg apply (auto simp add: Formula.nfv_def) sorry
  }
  moreover {
    assume "sat' \<sigma> V v i (formula.Agg y \<omega> tys f \<phi>)"
  }
  ultimately show ?case apply auto sorry*)
    have phi_wty: "S, agg_env E tys \<turnstile> \<phi>" using Agg.prems(1) by (auto elim: wty_formula.cases)
 have " a \<in> fv \<phi> \<Longrightarrow> Suc a \<le> length tys + length v" for a 
      using Agg(9)  fvi_plus_bound[of 0 "length tys" \<phi> "length v"] apply (auto simp add: Formula.nfv_def)
      by (metis Un_iff not_less not_less_eq_eq)  
    then have nfv:" Formula.nfv \<phi> \<le> length tys + length v" by (auto simp add: Formula.nfv_def)
  have phi_case: "length zs = length tys \<Longrightarrow> Formula.sat \<sigma> V (zs @ v) i \<phi> =  sat' \<sigma> V (zs @ v) i \<phi>" for zs 

  proof -
    assume len_zs:"length zs = length tys"
    {
      assume sat: " Formula.sat \<sigma> V (zs @ v) i \<phi>"
      have fv_wty: "y \<in> fv \<phi> \<Longrightarrow> ty_of ((zs @ v) ! y) = agg_env E tys y" for y
        using ty_of_sat_safe Agg(4,8) sat len_zs phi_wty nfv by  (auto simp add: Formula.nfv_def)
       have " Formula.sat \<sigma> V (zs @ v) i \<phi> = sat' \<sigma> V (zs @ v) i \<phi> " 
          using phi_wty Agg(4,5,8) len_zs nfv fv_wty by auto 
    }
    moreover{
      assume sat':"sat' \<sigma> V (zs @ v) i \<phi>"
      have fv_wty: "y \<in> fv \<phi> \<Longrightarrow> ty_of ((zs @ v) ! y) = agg_env E tys y" for y 
        using ty_of_sat'_safe Agg(4,8) sat' len_zs phi_wty nfv by  (auto simp add: Formula.nfv_def)
       have " Formula.sat \<sigma> V (zs @ v) i \<phi> = sat' \<sigma> V (zs @ v) i \<phi> " 
          using phi_wty Agg(4,5,8) len_zs nfv fv_wty by auto 
      }
      ultimately show ?thesis by auto
    qed
    have "Formula.eval_trm (zs @ v) f = eval_trm' (zs @ v) f"  if a1:"Formula.sat \<sigma> V (zs @ v) i \<phi>" and a2:"length zs = length tys" for zs
    proof -
      have fv_wty: "y\<in>fv_trm f \<Longrightarrow> ty_of ((zs @ v) ! y) = agg_env E tys y" for y 
        using ty_of_sat_safe  Agg(3,4,8) a1 a2 phi_wty nfv by auto 
       show ?thesis using Agg.prems(1) fv_wty by (auto dest: eval_trm_sound elim: wty_formula.cases) 
     qed
    then have 
 "{(x, ecard Zs) | x Zs. Zs = {zs. length zs = length tys \<and> Formula.sat \<sigma> V (zs @ v) i \<phi> \<and> Formula.eval_trm (zs @ v) f = x} \<and> Zs \<noteq> {}}
= {(x, ecard Zs) | x Zs. Zs = {zs. length zs = length tys \<and> sat' \<sigma> V (zs @ v) i \<phi> \<and> eval_trm' (zs @ v) f = x} \<and> Zs \<noteq> {}}"
    using phi_case  by (smt (z3) Collect_cong) 
  moreover
  obtain agg_op d where omega_def:"\<omega> = (agg_op,d)" using Agg.prems(1) by cases auto
  moreover
  have eval_agg_op_case: "eval_agg_op (agg_op,d) M = eval_agg_op' (agg_op,d) M" for M  using eval_agg_op_sound by auto 
  ultimately show ?case by auto

next
  case (Since \<phi> I \<psi>)
  have phi_eq: "Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for i using Since by (auto elim: wty_formula.cases)
  have psi_eq: "Formula.sat \<sigma> V v i \<psi> = sat' \<sigma> V v i \<psi>" for i  using Since by (auto elim: wty_formula.cases)
  show ?case by (auto simp add: phi_eq psi_eq) 
next
  case (Not_Since \<phi> I \<psi>)
  have phi_eq: "Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for i apply (rule Not_Since.IH(1)) using Not_Since by (auto elim: wty_formula.cases)
  have psi_eq: "Formula.sat \<sigma> V v i \<psi> = sat' \<sigma> V v i \<psi>" for i  using Not_Since by (auto elim: wty_formula.cases)
  show ?case by (auto simp add: phi_eq psi_eq)
next
  case (Until \<phi> I \<psi>)
  have phi_eq: "Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for i using Until by (auto elim: wty_formula.cases)
  have psi_eq: "Formula.sat \<sigma> V v i \<psi> = sat' \<sigma> V v i \<psi>" for i  using Until by (auto elim: wty_formula.cases)
  show ?case by (auto simp add: phi_eq psi_eq)
next
  case (Not_Until \<phi> I \<psi>)
  have phi_eq: "Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for i apply (rule Not_Until.IH(1)) using Not_Until by (auto elim: wty_formula.cases)
  have psi_eq: "Formula.sat \<sigma> V v i \<psi> = sat' \<sigma> V v i \<psi>" for i  using Not_Until by (auto elim: wty_formula.cases)
  show ?case by (auto simp add: phi_eq psi_eq) 
next
  case (MatchP I r)
  from  MatchP(1) have "safe_regex Past Strict r \<or>safe_regex Past Lax r " by auto
  from this have atms_safe: " \<phi> \<in> regex.atms r \<Longrightarrow> safe_formula \<phi> \<or> (\<exists> \<psi>. \<phi> = Formula.Neg \<psi> \<and> safe_formula \<psi>)" for \<phi>
    using case_NegE  by (induction r) auto
  have atms_regex_atms: " \<phi> \<in> atms r \<or> ( \<exists> \<psi>. \<phi> = Formula.Neg \<psi> \<and>  \<psi>\<in> atms r)" if assm: " \<phi> \<in> regex.atms r" for \<phi> 
    using assm atms_safe apply (induction r) by auto
  from MatchP(4) have  " (\<phi> \<in> atms r \<Longrightarrow>\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y)" for \<phi> apply auto apply (induction r ) 
        apply (auto) subgoal for x y apply (cases "safe_formula x") by (auto split: formula.splits  ) done
    from this  MatchP have IH: "\<phi>\<in>atms r \<Longrightarrow>Formula.sat \<sigma> V v i5 \<phi> = sat' \<sigma> V v i5 \<phi>" for \<phi> i5
      using match_safe_wty_nfv[of \<phi> r I S E v  ] by auto
     have other_IH: "\<phi> \<in> regex.atms r \<Longrightarrow> Formula.sat \<sigma> V v i5 \<phi> = sat' \<sigma> V v i5 \<phi>" for \<phi> i5 
      using atms_regex_atms[of \<phi>] IH by auto 
  then show ?case  using match_cong[OF refl other_IH, where ?r=r] by auto 
next
  case (MatchF I r)
   from  MatchF(1) have "safe_regex Futu Strict r \<or>safe_regex Futu Lax r " by auto
  from this have atms_safe: " \<phi> \<in> regex.atms r \<Longrightarrow> safe_formula \<phi> \<or> (\<exists> \<psi>. \<phi> = Formula.Neg \<psi> \<and> safe_formula \<psi>)" for \<phi>
    using case_NegE  by (induction r) auto
  have atms_regex_atms: " \<phi> \<in> atms r \<or> ( \<exists> \<psi>. \<phi> = Formula.Neg \<psi> \<and>  \<psi>\<in> atms r)" if assm: " \<phi> \<in> regex.atms r" for \<phi> 
    using assm atms_safe apply (induction r) by auto
  from MatchF(4) have  " (\<phi> \<in> atms r \<Longrightarrow>\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y)" for \<phi> apply auto apply (induction r ) 
        apply (auto) subgoal for x y apply (cases "safe_formula x") by (auto split: formula.splits  ) done
    from this  MatchF have IH: "\<phi>\<in>atms r \<Longrightarrow>Formula.sat \<sigma> V v i5 \<phi> = sat' \<sigma> V v i5 \<phi>" for \<phi> i5
      using match_safe_wty_nfv[of \<phi> r I S E v  ] by auto
     have other_IH: "\<phi> \<in> regex.atms r \<Longrightarrow> Formula.sat \<sigma> V v i5 \<phi> = sat' \<sigma> V v i5 \<phi>" for \<phi> i5 
      using atms_regex_atms[of \<phi>] IH by auto 
  then show ?case  using match_cong[OF refl other_IH, where ?r=r] by auto 
qed (auto elim: wty_formula.cases split: nat.splits)

(*

 using assms  proof (induction S E \<phi>  arbitrary: v V i rule: wty_formula.induct)

  case (Pred S p tys E tms )
  from  Pred  have tms_wty: "x \<in> set tms \<Longrightarrow> \<exists>t \<in> set tys. E \<turnstile> x :: t " for x by (metis Pred.hyps(2) in_set_conv_nth list_all2_conv_all_nth)
   have eval_tms_eq: "map (Formula.eval_trm v) tms = map (eval_trm' v) tms" using  tms_wty Pred(3) apply auto
     subgoal for x using eval_trm_sound[of E x _ v] by auto done
  then show ?case apply auto by (metis eval_tms_eq )+
next
  case (Eq E x t y S)
  then show ?case using eval_trm_sound by auto 
next
  case (Less E x1 t x2)
  then show ?case using eval_trm_sound  ty_of_eval_trm value_of_eval_trm[of E x2 v  ] value_of_eval_trm[of E x1 v  ] 
    by (cases t) (auto simp add: undef_less_def undef_less_eq_sound less_event_data_def)
next
  case (LessEq E x1 t x2)
  then show ?case using eval_trm_sound  ty_of_eval_trm value_of_eval_trm[of E x2 v  ] value_of_eval_trm[of E x1 v  ]
    by (cases t) (auto simp add: undef_less_eq_sound) 
next 
  case (Let S E \<phi> p E' \<psi>)
  {
    fix v' i'
    assume assm: " Formula.sat \<sigma> V v' i' \<phi>"
    have "\<forall>y\<in>fv \<phi>. ty_of (v' ! y) = E y" sorry
    then have "local.sat' \<sigma> V v' i' \<phi>" using Let.IH[of v' V i'] assm by auto
  }
 moreover{
    fix v' i'
    assume assm: "local.sat' \<sigma> V v' i' \<phi>"
    have "\<forall>y\<in>fv \<phi>. ty_of (v' ! y) = E y" sorry
    then have "Formula.sat \<sigma> V v' i' \<phi>" using Let.IH[of v' V i'] assm by auto
  }
  ultimately have "length v' = Formula.nfv \<phi> \<Longrightarrow>  Formula.sat \<sigma> V v' i' \<phi> =  local.sat' \<sigma> V v' i' \<phi>" for v' i' by auto
  from this  have " (\<lambda>a. if a = p then Some (\<lambda>i. {v. length v = Formula.nfv \<phi> \<and> Formula.sat \<sigma> V v i \<phi>}) else V a) 
  = V(p \<mapsto> \<lambda>i. {v. length v = Formula.nfv \<phi> \<and> local.sat' \<sigma> V v i \<phi>})" by fastforce

  then show ?case using Let by auto
next
  case (Agg E y agg_type t tys f S \<phi> d)
  then show ?case  apply auto sorry

next
  case (Neg S E \<phi>)
  from Neg.prems(2) have "safe_formula \<phi> \<or> ?case" using safe_neg_eq by (cases \<phi>)  auto 
  then show ?case using Neg by auto

next
  case (And S E \<phi> \<psi>)
  have phi_eq: "Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> sat' \<sigma> V v i \<phi>" using And by auto
  have "\<psi> = Formula.Eq(Formula.Var x1 ) t \<or> \<psi> = Formula.Eq t (Formula.Var x1 )  \<Longrightarrow> safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> Formula.eval_trm v t = eval_trm' v t " for x1 t
    using And(2,5) eval_trm_sound by (auto simp add: safe_assignment_def elim!: wty_formula.cases)
  then  have safe_case: " safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> safe_formula \<psi> \<or>?case " apply (cases \<psi>) using And(2,5) phi_eq
    by (auto simp add: safe_assignment_def split: trm.splits elim!: wty_formula.cases)
  have is_const_case: "is_constraint \<psi> \<Longrightarrow> ?case" using phi_eq And(2,5-6)  eval_trm_sound[where ?E=E] undef_less_eq_sound apply (cases \<psi> rule: is_constraint.cases)
                    apply (auto simp add: undef_less_def elim: wty_formula.cases) 
    subgoal for x41 x42   apply (auto  elim!: wty_formula.cases  ) apply (drule poly_value_of[where ?v=v]) apply (auto simp add: less_event_data_def) done
    subgoal for x41 x42   apply (auto  elim!: wty_formula.cases  ) apply (drule poly_value_of[where ?v=v]) apply (auto simp add: less_event_data_def) done
    subgoal for x41 x42   apply (auto  elim!: wty_formula.cases  ) apply (drule poly_value_of[where ?v=v]) apply (auto simp add: less_event_data_def) done
    subgoal for x41 x42   apply (auto  elim!: wty_formula.cases  ) apply (drule poly_value_of[where ?v=v]) apply (auto simp add: less_event_data_def) done
    subgoal for x41 x42   apply (auto  elim!: wty_formula.cases  ) apply (drule poly_value_of[where ?v=v]) apply (auto simp add: less_event_data_def) done
    subgoal for x41 x42   apply (auto  elim!: wty_formula.cases  ) apply (drule poly_value_of[where ?v=v]) apply (auto simp add: less_event_data_def) done
    subgoal for x41 x42   apply (auto  elim!: wty_formula.cases  ) apply (drule poly_value_of[where ?v=v]) apply (auto simp add: less_event_data_def) done
    subgoal for x41 x42   apply (auto  elim!: wty_formula.cases  ) apply (drule poly_value_of[where ?v=v]) apply (auto simp add: less_event_data_def) done
    subgoal for x41 x42   apply (auto  elim!: wty_formula.cases  ) apply (drule poly_value_of[where ?v=v]) apply (auto simp add: less_event_data_def) done
    subgoal for x41 x42   apply (auto  elim!: wty_formula.cases  ) apply (drule poly_value_of[where ?v=v]) apply (auto simp add: less_event_data_def) done
    subgoal for x41 x42   by (auto  elim!: wty_formula.cases  )
    subgoal for x41 x42   by (auto  elim!: wty_formula.cases  )
    subgoal for x41 x42   by (auto  elim!: wty_formula.cases  )
    subgoal for x41 x42   by (auto  elim!: wty_formula.cases  )
    subgoal for x41 x42   by (auto  elim!: wty_formula.cases  )
    subgoal for x41 x42   by (auto  elim!: wty_formula.cases  )
    subgoal for x41 x42   apply (auto  elim!: wty_formula.cases  ) apply (drule poly_value_of[where ?v=v]) apply (auto simp add: less_event_data_def) done
    subgoal for x41 x42   apply (auto  elim!: wty_formula.cases  ) apply (drule poly_value_of[where ?v=v]) apply (auto simp add: less_event_data_def) done
    subgoal for x41 x42   apply (auto  elim!: wty_formula.cases  ) apply (drule poly_value_of[where ?v=v]) apply (auto simp add: less_event_data_def) done
    subgoal for x41 x42   apply (auto  elim!: wty_formula.cases  ) apply (drule poly_value_of[where ?v=v]) apply (auto simp add: less_event_data_def) done
    subgoal for x41 x42   apply (auto  elim!: wty_formula.cases  ) apply (drule poly_value_of[where ?v=v]) apply (auto simp add: less_event_data_def) done
    subgoal for x41 x42   apply (auto  elim!: wty_formula.cases  ) apply (drule poly_value_of[where ?v=v]) apply (auto simp add: less_event_data_def) done
    subgoal for x41 x42   apply (auto  elim!: wty_formula.cases  ) apply (drule poly_value_of[where ?v=v]) apply (auto simp add: less_event_data_def) done
    subgoal for x41 x42   apply (auto  elim!: wty_formula.cases  ) apply (drule poly_value_of[where ?v=v]) apply (auto simp add: less_event_data_def) done
    subgoal for x41 x42   apply (auto  elim!: wty_formula.cases  ) apply (drule poly_value_of[where ?v=v]) apply (auto simp add: less_event_data_def) done
    subgoal for x41 x42   apply (auto  elim!: wty_formula.cases  ) apply (drule poly_value_of[where ?v=v]) apply (auto simp add: less_event_data_def) done
    done

  have "safe_formula \<psi> \<or>  (case \<psi> of formula.Neg x \<Rightarrow> safe_formula x | _ \<Rightarrow> False) \<or> ?case" 
    using And.prems(2) safe_case is_const_case  by auto
  moreover have "safe_formula \<psi> \<Longrightarrow> ?case" using And  by auto 
  ultimately show ?case apply (auto ) sorry
next
  case (Ands \<phi>s S E)
  then show ?case sorry
next
  case (Exists S t E \<phi> )
   {
    fix za
    assume  assm: "Formula.sat \<sigma> V (za # v) i \<phi>" 
    have nfv: " Formula.nfv \<phi> \<le> Suc (length v)" using Exists(6) nfv_exists[of \<phi> t] by auto
    have "0 \<in> fv \<phi> \<Longrightarrow> ty_of za = t" 
      using ty_of_sat_safe[where ?E="case_nat t E" and ?S=S and ?\<phi>=\<phi> and ?v="za#v" and ?V=V and ?i=i and ?\<sigma>=\<sigma> and ?x=0]  
      Exists(1,4-5)  nfv assm by auto 
    then have "\<forall>y\<in>fv \<phi>. ty_of ((za # v) ! y) = (case y of 0 \<Rightarrow> t | Suc x \<Rightarrow> E x)" using Exists(3)   by (auto simp add:  fvi_Suc split: nat.splits )

    from this  have "local.sat' \<sigma> V (za # v) i \<phi>" using Exists.IH[of "za#v" V i] Exists(4-5) nfv assm by auto
  }
  moreover {
    fix za
   assume  assm: "local.sat' \<sigma> V (za # v) i \<phi>" 
 have nfv: " Formula.nfv \<phi> \<le> Suc (length v)" using Exists(6) nfv_exists[of \<phi> t] by auto
    have "0 \<in> fv \<phi> \<Longrightarrow> ty_of za = t" 
      using ty_of_sat'_safe[where ?E="case_nat t E" and ?S=S and ?\<phi>=\<phi> and ?v="za#v" and ?V=V and ?i=i and ?\<sigma>=\<sigma> and ?x=0]  
      Exists(1,4-5)  nfv assm by auto
    from this have "\<forall>y\<in>fv \<phi>. ty_of ((za # v) ! y) = (case y of 0 \<Rightarrow> t | Suc x \<Rightarrow> E x)" using Exists(3) assm by (auto simp add: fvi_Suc split: nat.splits )
    from this have " Formula.sat \<sigma> V (za # v) i \<phi>" using Exists.IH[of "za#v" V i] Exists(4-6) nfv_exists[of \<phi> t] assm by auto
  }
  ultimately show ?case   by auto 

next

  case (Since S E \<phi> \<psi> \<I>)
  then show ?case sorry
next
  case (Until S E \<phi> \<psi> \<I>)
  then show ?case sorry
next

  case (MatchF S E x2 x1) 
  from this  have other_IH: "\<phi> \<in> regex.atms x2 \<Longrightarrow> Formula.sat \<sigma> V5 v i5 \<phi> = local.sat' \<sigma> V5 v i5 \<phi>" for \<phi> V5 i5 
    using MatchF apply (auto simp add: regex.pred_set fv_regex_alt) sorry
  then show ?case  using match_cong[OF refl other_IH, where ?r=x2] by auto 
next
  case (MatchP S E x2 x1)
    from this  have other_IH: "\<phi> \<in> regex.atms x2 \<Longrightarrow> Formula.sat \<sigma> V5 v i5 \<phi> = local.sat' \<sigma> V5 v i5 \<phi>" for \<phi> V5 i5 
    apply (auto simp add: regex.pred_set fv_regex_alt) sorry
  then show ?case  using match_cong[OF refl other_IH, where ?r=x2] by auto 
qed  (auto split: nat.splits) 

*)
end
end