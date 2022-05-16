(*<*)
theory Formula
  imports
    Event_Data
    Regex
    "MFOTL_Monitor_Devel.Interval"
    "MFOTL_Monitor_Devel.Trace"
    "MFOTL_Monitor_Devel.Abstract_Monitor"
    "HOL-Library.Mapping"
    Containers.Set_Impl
begin
(*>*)

section \<open>Metric first-order dynamic logic\<close>


subsection \<open> Instantiations \<close>

derive (eq) ceq enat

instantiation enat :: ccompare begin
definition ccompare_enat :: "enat comparator option" where
  "ccompare_enat = Some (\<lambda>x y. if x = y then order.Eq else if x < y then order.Lt else order.Gt)"

instance by intro_classes
    (auto simp: ccompare_enat_def split: if_splits intro!: comparator.intro)
end

instantiation enat :: card_UNIV begin
definition "finite_UNIV = Phantom(enat) False"
definition "card_UNIV = Phantom(enat) 0"
instance by intro_classes (simp_all add: finite_UNIV_enat_def card_UNIV_enat_def infinite_UNIV_char_0)
end

datatype rec_safety = Unused | PastRec | NonFutuRec | AnyRec

instantiation rec_safety :: "{finite, bounded_semilattice_sup_bot, monoid_mult, mult_zero}"
begin

fun less_eq_rec_safety where
  "Unused \<le> _ = True"
| "PastRec \<le> PastRec = True"
| "PastRec \<le> NonFutuRec = True"
| "PastRec \<le> AnyRec = True"
| "NonFutuRec \<le> NonFutuRec = True"
| "NonFutuRec \<le> AnyRec = True"
| "AnyRec \<le> AnyRec = True"
| "(_::rec_safety) \<le> _ = False"

definition "(x::rec_safety) < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"

definition [code_unfold]: "\<bottom> = Unused"

fun sup_rec_safety where
  "AnyRec \<squnion> _ = AnyRec"
| "_ \<squnion> AnyRec = AnyRec"
| "NonFutuRec \<squnion> _ = NonFutuRec"
| "_ \<squnion> NonFutuRec = NonFutuRec"
| "PastRec \<squnion> _ = PastRec"
| "_ \<squnion> PastRec = PastRec"
| "Unused \<squnion> Unused = Unused"

definition [code_unfold]: "0 = Unused"
definition [code_unfold]: "1 = NonFutuRec"

fun times_rec_safety where
  "Unused * _ = Unused"
| "_ * Unused = Unused"
| "AnyRec * _ = AnyRec"
| "_ * AnyRec = AnyRec"
| "PastRec * _ = PastRec"
| "_ * PastRec = PastRec"
| "NonFutuRec * NonFutuRec = NonFutuRec"

instance proof
  fix x y z :: rec_safety
  have "x \<in> {Unused, PastRec, NonFutuRec, AnyRec}" for x
    by (cases x) simp_all
  then have UNIV_alt: "UNIV = \<dots>" by blast
  show "finite (UNIV :: rec_safety set)"
    unfolding UNIV_alt by blast
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_rec_safety_def
    by (cases x; cases y) simp_all
  show "x \<le> x"
    by (cases x) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) simp_all
  show "x \<le> x \<squnion> y"
    by (cases x; cases y) simp_all
  show "y \<le> x \<squnion> y"
    by (cases x; cases y) simp_all
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    by (cases x; cases y; cases z) simp_all
  show "\<bottom> \<le> x"
    unfolding bot_rec_safety_def
    by (cases x) simp_all
  show "(x * y) * z = x * (y * z)"
    by (cases x; cases y; cases z) simp_all
  show "1 * x = x"
    unfolding one_rec_safety_def
    by (cases x) simp_all
  show "x * 1 = x"
    unfolding one_rec_safety_def
    by (cases x) simp_all
  show "0 * x = 0"
    unfolding zero_rec_safety_def by simp
  show "x * 0 = 0"
    unfolding zero_rec_safety_def
    by (cases x) simp_all
qed

end

instantiation rec_safety :: Sup
begin

definition "\<Squnion> A = Finite_Set.fold (\<squnion>) Unused A"

instance ..

end

lemma (in semilattice_sup) comp_fun_idem_on_sup: "comp_fun_idem_on UNIV sup"
  using comp_fun_idem_sup by (simp add: comp_fun_idem_def')

lemma Sup_rec_safety_empty[simp]: "\<Squnion> {} = Unused"
  by (simp add: Sup_rec_safety_def)

lemma Sup_rec_safety_insert[simp]: "\<Squnion>(insert (x::rec_safety) A) = x \<squnion> \<Squnion>A"
  by (simp add: Sup_rec_safety_def comp_fun_idem_on.fold_insert_idem[OF comp_fun_idem_on_sup])

lemma Sup_rec_safety_union: "\<Squnion>((A::rec_safety set) \<union> B) = \<Squnion>A \<squnion> \<Squnion>B"
  unfolding Sup_rec_safety_def
  using finite[of A]
  by (induction A rule: finite_induct) (simp_all flip: bot_rec_safety_def
      add: comp_fun_idem_on.fold_insert_idem[OF comp_fun_idem_on_sup] sup_assoc)


context begin

subsection \<open>Syntax and semantics\<close>

qualified type_synonym name = string8
qualified type_synonym event = "(name \<times> event_data list)"
qualified type_synonym database = "event set"
qualified type_synonym prefix = "database prefix"
qualified type_synonym trace = "database trace"

qualified type_synonym env = "event_data list"

subsubsection \<open>Terms\<close>

qualified datatype trm = is_Var: Var nat | is_Const: Const event_data
  | Plus trm trm | Minus trm trm | UMinus trm | Mult trm trm | Div trm trm | Mod trm trm
  | F2i trm | I2f trm

lemma trm_exhaust: "(\<And>x. t = Var x \<Longrightarrow> P (Var x)) 
  \<Longrightarrow> (\<And>a. t = Const a \<Longrightarrow> P (Const a))
  \<Longrightarrow> (\<And>t1 t2. t = Plus t1 t2 \<Longrightarrow> P (Plus t1 t2))
  \<Longrightarrow> (\<And>t1 t2. t = Minus t1 t2 \<Longrightarrow> P (Minus t1 t2))
  \<Longrightarrow> (\<And>t1. t = UMinus t1 \<Longrightarrow> P (UMinus t1))
  \<Longrightarrow> (\<And>t1 t2. t = Mult t1 t2 \<Longrightarrow> P (Mult t1 t2))
  \<Longrightarrow> (\<And>t1 t2. t = Div t1 t2 \<Longrightarrow> P (Div t1 t2))
  \<Longrightarrow> (\<And>t1 t2. t = Mod t1 t2 \<Longrightarrow> P (Mod t1 t2))
  \<Longrightarrow> (\<And>t1. t = F2i t1 \<Longrightarrow> P (F2i t1))
  \<Longrightarrow> (\<And>t1. t = I2f t1 \<Longrightarrow> P (I2f t1))
  \<Longrightarrow> P t"
  by (cases t, simp_all)

text \<open> In this implementation of MFODL, to use De Bruijn indices, binding operators increase the
value of the bounding number @{term b} (that starts at $0$) and this number is subtracted from
all free variables (type @{typ nat}) greater than @{term b}. For instance, the free variable of
$\exists.\ P\, (Var 0) \land Q\, (Var 1)$ is @{term "Var 0"} because the existential makes $b=1$
and this value is subtracted from $Q$s argument while that of $P$ is not even taken into account. \<close>


qualified primrec fvi_trm :: "nat \<Rightarrow> trm \<Rightarrow> nat set" where
  "fvi_trm b (Var x) = (if b \<le> x then {x - b} else {})"
| "fvi_trm b (Const _) = {}"
| "fvi_trm b (Plus x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (Minus x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (UMinus x) = fvi_trm b x"
| "fvi_trm b (Mult x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (Div x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (Mod x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (F2i x) = fvi_trm b x"
| "fvi_trm b (I2f x) = fvi_trm b x"

abbreviation "fv_trm \<equiv> fvi_trm 0"

qualified primrec eval_trm :: "env \<Rightarrow> trm \<Rightarrow> event_data" where
  "eval_trm v (Var x) = v ! x"
| "eval_trm v (Const x) = x"
| "eval_trm v (Plus x y) = eval_trm v x + eval_trm v y"
| "eval_trm v (Minus x y) = eval_trm v x - eval_trm v y"
| "eval_trm v (UMinus x) = - eval_trm v x"
| "eval_trm v (Mult x y) = eval_trm v x * eval_trm v y"
| "eval_trm v (Div x y) = eval_trm v x div eval_trm v y"
| "eval_trm v (Mod x y) = eval_trm v x mod eval_trm v y"
| "eval_trm v (F2i x) = EInt (integer_of_event_data (eval_trm v x))"
| "eval_trm v (I2f x) = EFloat (double_of_event_data (eval_trm v x))"

lemma eval_trm_fv_cong: "\<forall>x\<in>fv_trm t. v ! x = v' ! x \<Longrightarrow> eval_trm v t = eval_trm v' t"
  by (induction t) simp_all


subsubsection \<open>Formulas\<close>

text \<open> Aggregation operators @{term "Agg nat agg_op nat trm formula"} are special
formulas with five parameters:
\begin{itemize}
\item Variable @{term "y::nat"} that saves the value of the aggregation operation.
\item Type of aggregation (sum, avg, min, max, ...).
\item Binding number @{term "b::nat"} for many variables in the next two arguments.
\item Term @{term "t::trm"} that represents an operation to be aggregated.
\item Formula @{term "\<phi>"} that restricts the domain where the aggregation takes place.
\end{itemize} \<close>

datatype ty = TInt | TFloat | TString

qualified datatype agg_type = Agg_Cnt | Agg_Min | Agg_Max | Agg_Sum | Agg_Avg | Agg_Med
qualified type_synonym 't agg_op = "agg_type \<times> 't"

definition flatten_multiset :: "(event_data \<times> enat) set \<Rightarrow> event_data list" where
  "flatten_multiset M = concat (map (\<lambda>(x, c). replicate (the_enat c) x) (csorted_list_of_set M))"

definition finite_multiset :: "(event_data \<times> enat) set \<Rightarrow> bool" where
"finite_multiset M = (finite M \<and> \<not>(\<exists>s. (s,\<infinity>) \<in> M ))"

definition aggreg_default_value :: "agg_type \<Rightarrow> ty \<Rightarrow> event_data" where
  "aggreg_default_value op t = (case (op, t) of
    (Agg_Min, TFloat) \<Rightarrow> EFloat Code_Double.infinity |
    (Agg_Max, TFloat) \<Rightarrow> EFloat (-Code_Double.infinity) |
    (_, TFloat) \<Rightarrow> EFloat 0 |
    (_, TInt) \<Rightarrow> EInt 0 |
    (_, TString) \<Rightarrow> EString empty_string)"

fun eval_agg_op :: "ty agg_op \<Rightarrow> (event_data \<times> enat) set \<Rightarrow> event_data" where
  "eval_agg_op (Agg_Cnt, ty) M = (let y0 = aggreg_default_value Agg_Cnt ty in
    case (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (xs,_) \<Rightarrow> EInt (integer_of_int (length xs)))"
| "eval_agg_op (Agg_Min, ty) M = (let y0 = aggreg_default_value Agg_Min ty in
    case  (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (x # xs,_) \<Rightarrow> foldl min x xs)"
| "eval_agg_op (Agg_Max, ty) M = (let y0 = aggreg_default_value Agg_Max ty in 
    case  (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (x # xs,_) \<Rightarrow> foldl max x xs)"
| "eval_agg_op (agg_type.Agg_Sum, ty) M = (let y0 = aggreg_default_value Agg_Sum ty in
    case  (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (x # xs,_) \<Rightarrow> foldl (+) x xs)"
| "eval_agg_op (Agg_Avg, ty) M =(let y0 = aggreg_default_value Agg_Avg ty in 
    case  (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (x#xs,_) \<Rightarrow> EFloat ( double_of_event_data_agg (foldl plus x xs) / double_of_int (length (x#xs))))"
| "eval_agg_op (Agg_Med, ty) M =(let y0 = aggreg_default_value Agg_Med ty in
    case (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (xs,_) \<Rightarrow> EFloat (let u = length xs;  u' = u div 2 in
          if even u then
            (double_of_event_data_agg (xs ! (u'-1)) + double_of_event_data_agg (xs ! u')) / double_of_int 2
          else double_of_event_data_agg (xs ! u')))"

qualified datatype (discs_sels) 't formula = Pred name "trm list"
  | Let name "'t formula" "'t formula"
  | LetPast name "'t formula" "'t formula"
  | Eq trm trm | Less trm trm | LessEq trm trm
  | Neg "'t formula" | Or "'t formula" "'t formula" | And "'t formula" "'t formula" | Ands "'t formula list" | Exists 't "'t formula"
  | Agg nat "'t agg_op" "'t list" trm "'t formula"
  | Prev \<I> "'t formula" | Next \<I> "'t formula"
  | Since "'t formula" \<I> "'t formula" | Until "'t formula" \<I> "'t formula"
  | MatchF \<I> "'t formula Regex.regex" | MatchP \<I> "'t formula Regex.regex"
  | TP trm | TS trm

qualified definition "FF = Eq (Const (EInt 0)) (Const (EInt 1))"
qualified definition "TT \<equiv> Eq (Const (EInt 0)) (Const (EInt 0))"

qualified fun fvi :: "nat \<Rightarrow> 't formula \<Rightarrow> nat set" where
  "fvi b (Pred r ts) = (\<Union>t\<in>set ts. fvi_trm b t)"
| "fvi b (Let p \<phi> \<psi>) = fvi b \<psi>"
| "fvi b (LetPast p \<phi> \<psi>) = fvi b \<psi>"
| "fvi b (Eq t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (Less t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (LessEq t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (Neg \<phi>) = fvi b \<phi>"
| "fvi b (Or \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (And \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Ands \<phi>s) = (let xs = map (fvi b) \<phi>s in \<Union>x\<in>set xs. x)"
| "fvi b (Exists t \<phi>) = fvi (Suc b) \<phi>"
| "fvi b (Agg y \<omega> tys f \<phi>) = fvi (b + length tys) \<phi> \<union> fvi_trm (b + length tys) f \<union> (if b \<le> y then {y - b} else {})"
| "fvi b (Prev I \<phi>) = fvi b \<phi>"
| "fvi b (Next I \<phi>) = fvi b \<phi>"
| "fvi b (Since \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Until \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (MatchF I r) = Regex.fv_regex (fvi b) r"
| "fvi b (MatchP I r) = Regex.fv_regex (fvi b) r"
| "fvi b (TP t) = fvi_trm b t"
| "fvi b (TS t) = fvi_trm b t"

abbreviation "fv \<equiv> fvi 0"
abbreviation "fv_regex \<equiv> Regex.fv_regex fv"

lemma fv_abbrevs[simp]: "fv TT = {}" "fv FF = {}"
  unfolding TT_def FF_def by auto

lemma fv_subset_Ands: "\<phi> \<in> set \<phi>s \<Longrightarrow> fv \<phi> \<subseteq> fv (Ands \<phi>s)"
  by auto

lemma finite_fvi_trm[simp]: "finite (fvi_trm b t)"
  by (induction t) simp_all

lemma finite_fvi[simp]: "finite (fvi b \<phi>)"
  by (induction \<phi> arbitrary: b) simp_all

lemma fvi_trm_plus: "x \<in> fvi_trm (b + c) t \<longleftrightarrow> x + c \<in> fvi_trm b t"
  by (induction t) auto

lemma fvi_trm_minus: "x \<in> fvi_trm b t \<and> x \<ge> c \<longrightarrow> x-c \<in> fvi_trm (b+c) t"
  by (induction t) auto

lemma fvi_trm_iff_fv_trm: "x \<in> fvi_trm b t \<longleftrightarrow> x + b \<in> fv_trm t"
  using fvi_trm_plus[where b=0 and c=b] by simp_all

lemma fvi_plus: "x \<in> fvi (b + c) \<phi> \<longleftrightarrow> x + c \<in> fvi b \<phi>"
proof (induction \<phi> arbitrary: b rule: formula.induct)
  case (Exists \<phi>)
  then show ?case by force
next
  case (Agg y \<omega> tys f \<phi>)
  let ?b' = "length tys"
  have *: "b + c + ?b' = b + ?b' + c" by simp
  from Agg show ?case by (force simp: * fvi_trm_plus)
qed (auto simp add: fvi_trm_plus fv_regex_commute[where g = "\<lambda>x. x + c"])

lemma fvi_minus: "x \<in> fvi b \<phi> \<and> x \<ge> c \<longrightarrow> x - c \<in> fvi (b+c) \<phi>"
  by (simp add: fvi_plus)

lemma fvi_Suc: "x \<in> fvi (Suc b) \<phi> \<longleftrightarrow> Suc x \<in> fvi b \<phi>"
  using fvi_plus[where c=1] by simp

lemma fvi_plus_bound:
  assumes "\<forall>i\<in>fvi (b + c) \<phi>. i < n"
  shows "\<forall>i\<in>fvi b \<phi>. i < c + n"
proof
  fix i
  assume "i \<in> fvi b \<phi>"
  show "i < c + n"
  proof (cases "i < c")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain i' where "i = i' + c"
      using nat_le_iff_add by (auto simp: not_less)
    with assms \<open>i \<in> fvi b \<phi>\<close> show ?thesis by (simp add: fvi_plus)
  qed
qed

lemma fvi_Suc_bound:
  assumes "\<forall>i\<in>fvi (Suc b) \<phi>. i < n"
  shows "\<forall>i\<in>fvi b \<phi>. i < Suc n"
  using assms fvi_plus_bound[where c=1] by simp

lemma fvi_iff_fv: "x \<in> fvi b \<phi> \<longleftrightarrow> x + b \<in> fv \<phi>"
  using fvi_plus[where b=0 and c=b] by simp_all

qualified definition nfv :: "'t formula \<Rightarrow> nat" where
  "nfv \<phi> = Max (insert 0 (Suc ` fv \<phi>))"

qualified abbreviation nfv_regex where
  "nfv_regex \<equiv> Regex.nfv_regex fv"

qualified definition envs :: "'t formula \<Rightarrow> env set" where
  "envs \<phi> = {v. length v = nfv \<phi>}"

lemma nfv_simps[simp]:
  "nfv (Let p \<phi> \<psi>) = nfv \<psi>"
  "nfv (LetPast p \<phi> \<psi>) = nfv \<psi>"
  "nfv (Neg \<phi>) = nfv \<phi>"
  "nfv (Or \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (And \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Prev I \<phi>) = nfv \<phi>"
  "nfv (Next I \<phi>) = nfv \<phi>"
  "nfv (Since \<phi> I \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Until \<phi> I \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (MatchP I r) = Regex.nfv_regex fv r"
  "nfv (MatchF I r) = Regex.nfv_regex fv r"
  "nfv_regex (Regex.Skip n) = 0"
  "nfv_regex (Regex.Test \<phi>) = Max (insert 0 (Suc ` fv \<phi>))"
  "nfv_regex (Regex.Plus r s) = max (nfv_regex r) (nfv_regex s)"
  "nfv_regex (Regex.Times r s) = max (nfv_regex r) (nfv_regex s)"
  "nfv_regex (Regex.Star r) = nfv_regex r"
  unfolding nfv_def Regex.nfv_regex_def by (simp_all add: image_Un Max_Un[symmetric])

lemma nfv_Ands[simp]: "nfv (Ands l) = Max (insert 0 (nfv ` set l))"
proof (induction l)
  case Nil
  then show ?case unfolding nfv_def by simp
next
  case (Cons a l)
  have "fv (Ands (a # l)) = fv a \<union> fv (Ands l)" by simp
  then have "nfv (Ands (a # l)) = max (nfv a) (nfv (Ands l))"
    unfolding nfv_def
    by (auto simp: image_Un Max.union[symmetric])
  with Cons.IH show ?case
    by (cases l) auto
qed

lemma fvi_less_nfv: "\<forall>i\<in>fv \<phi>. i < nfv \<phi>"
  unfolding nfv_def
  by (auto simp add: Max_gr_iff intro: max.strict_coboundedI2)

lemma fvi_less_nfv_regex: "\<forall>i\<in>fv_regex \<phi>. i < nfv_regex \<phi>"
  unfolding Regex.nfv_regex_def
  by (auto simp add: Max_gr_iff intro: max.strict_coboundedI2)

fun contains_pred :: "name \<times> nat \<Rightarrow> 't formula \<Rightarrow> bool" where
   "contains_pred p (Eq t1 t2) = False"
|  "contains_pred p (Less t1 t2) = False"
|  "contains_pred p (LessEq t1 t2) = False"
|  "contains_pred p (Pred e ts) = (p = (e, length ts))"
|  "contains_pred p (Let e \<phi> \<psi>) = ((contains_pred p \<phi> \<and> contains_pred (e, nfv \<phi>) \<psi>) \<or> (p \<noteq> (e, nfv \<phi>) \<and> contains_pred p \<psi>))"
|  "contains_pred p (LetPast e \<phi> \<psi>) =  (p \<noteq> (e, nfv \<phi>) \<and> ((contains_pred p \<phi> \<and> contains_pred (e, nfv \<phi>) \<psi>) \<or> contains_pred p \<psi>))"
|  "contains_pred p (Neg \<phi>) = contains_pred p \<phi>"
|  "contains_pred p (Or \<phi> \<psi>) = (contains_pred p \<phi> \<or> contains_pred p \<psi>)"
|  "contains_pred p (And \<phi> \<psi>) = (contains_pred p \<phi> \<or> contains_pred p \<psi>)"
|  "contains_pred p (Ands l) = (\<exists>\<phi>\<in>set l. contains_pred p \<phi>)"
|  "contains_pred p (Exists t \<phi>) = contains_pred p \<phi>"
|  "contains_pred p (Agg y \<omega> tys f \<phi>) = contains_pred p \<phi>"
|  "contains_pred p (Prev I \<phi>) = contains_pred p \<phi>"
|  "contains_pred p (Next I \<phi>) = contains_pred p \<phi>"
|  "contains_pred p (Since \<phi> I \<psi>) = (contains_pred p \<phi> \<or> contains_pred p \<psi>)"
|  "contains_pred p (Until \<phi> I \<psi>) = (contains_pred p \<phi> \<or> contains_pred p \<psi>)"
|  "contains_pred p (MatchP I r) = (\<exists>\<phi>\<in>Regex.atms r. contains_pred p \<phi>)"
|  "contains_pred p (MatchF I r) =  (\<exists>\<phi>\<in>Regex.atms r. contains_pred p \<phi>)"
|  "contains_pred p (TP t) = False"
|  "contains_pred p (TS t) = False"


subsubsection \<open>Semantics\<close>

definition "ecard A = (if finite A then card A else \<infinity>)"

declare conj_cong[fundef_cong]
fun letpast_sat where
  "letpast_sat sat v (i::nat) = sat (\<lambda>w j. j < i \<and> letpast_sat sat w j) v i"
declare letpast_sat.simps[simp del]

lemma V_subst_letpast_sat:
  "(\<And>X v j. j \<le> i \<Longrightarrow> f X v j = g X v j) \<Longrightarrow>
  Formula.letpast_sat f v i = Formula.letpast_sat g v i"
  by (induct f v i rule: letpast_sat.induct) (subst (1 2) letpast_sat.simps, auto cong: conj_cong)

qualified fun sat :: "trace \<Rightarrow> (name \<times> nat \<rightharpoonup> env \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> env \<Rightarrow> nat \<Rightarrow> ty formula \<Rightarrow> bool" where
  "sat \<sigma> V v i (Pred r ts) = (case V (r, length ts) of
       None \<Rightarrow> (r, map (eval_trm v) ts) \<in> \<Gamma> \<sigma> i
     | Some X \<Rightarrow> X (map (eval_trm v) ts) i)"
| "sat \<sigma> V v i (Let p \<phi> \<psi>) = sat \<sigma> (V((p, nfv \<phi>) \<mapsto> \<lambda>w j. sat \<sigma> V w j \<phi>)) v i \<psi>"
| "sat \<sigma> V v i (LetPast p \<phi> \<psi>) =
    (let pn = (p, nfv \<phi>) in
    sat \<sigma> (V(pn \<mapsto> letpast_sat (\<lambda>X u k. sat \<sigma> (V(pn \<mapsto> X)) u k \<phi>))) v i \<psi>)"
| "sat \<sigma> V v i (Eq t1 t2) = (eval_trm v t1 = eval_trm v t2)"
| "sat \<sigma> V v i (Less t1 t2) = (eval_trm v t1 < eval_trm v t2)"
| "sat \<sigma> V v i (LessEq t1 t2) = (eval_trm v t1 \<le> eval_trm v t2)"
| "sat \<sigma> V v i (Neg \<phi>) = (\<not> sat \<sigma> V v i \<phi>)"
| "sat \<sigma> V v i (Or \<phi> \<psi>) = (sat \<sigma> V v i \<phi> \<or> sat \<sigma> V v i \<psi>)"
| "sat \<sigma> V v i (And \<phi> \<psi>) = (sat \<sigma> V v i \<phi> \<and> sat \<sigma> V v i \<psi>)"
| "sat \<sigma> V v i (Ands l) = (\<forall>\<phi> \<in> set l. sat \<sigma> V v i \<phi>)"
| "sat \<sigma> V v i (Exists t \<phi>) = (\<exists>z. sat \<sigma> V (z # v) i \<phi>)"
| "sat \<sigma> V v i (Agg y \<omega> tys f \<phi>) =
    (let M = {(x, ecard Zs) | x Zs. Zs = {zs. length zs = length tys \<and> sat \<sigma> V (zs @ v) i \<phi> \<and> eval_trm (zs @ v) f = x} \<and> Zs \<noteq> {}}
    in (M = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<length tys}) \<and> v ! y = eval_agg_op \<omega> M)"
| "sat \<sigma> V v i (Prev I \<phi>) = (case i of 0 \<Rightarrow> False | Suc j \<Rightarrow> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<phi>)"
| "sat \<sigma> V v i (Next I \<phi>) = (mem I ((\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i)) \<and> sat \<sigma> V v (Suc i) \<phi>)"
| "sat \<sigma> V v i (Since \<phi> I \<psi>) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<psi> \<and> (\<forall>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>))"
| "sat \<sigma> V v i (Until \<phi> I \<psi>) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat \<sigma> V v j \<psi> \<and> (\<forall>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>))"
| "sat \<sigma> V v i (MatchP I r) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Regex.match (sat \<sigma> V v) r j i)"
| "sat \<sigma> V v i (MatchF I r) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Regex.match (sat \<sigma> V v) r i j)"
| "sat \<sigma> V v i (TP t) = (eval_trm v t = EInt (integer_of_nat i))"
| "sat \<sigma> V v i (TS t) = (eval_trm v t = EInt (integer_of_nat (\<tau> \<sigma> i)))"

lemma sat_abbrevs[simp]:
  "sat \<sigma> V v i TT" "\<not> sat \<sigma> V v i FF"
  unfolding TT_def FF_def by auto

lemma sat_Ands: "sat \<sigma> V v i (Ands l) \<longleftrightarrow> (\<forall>\<phi>\<in>set l. sat \<sigma> V v i \<phi>)"
  by (simp add: list_all_iff)

lemma sat_Until_rec: "sat \<sigma> V v i (Until \<phi> I \<psi>) \<longleftrightarrow>
  memL I 0 \<and> sat \<sigma> V v i \<psi> \<or>
  (memR I (\<Delta> \<sigma> (i + 1)) \<and> sat \<sigma> V v i \<phi> \<and> sat \<sigma> V v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>))"
  (is "?L \<longleftrightarrow> ?R")
proof (rule iffI; (elim disjE conjE)?)
  assume ?L
  then obtain j where j: "i \<le> j" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "sat \<sigma> V v j \<psi>" "\<forall>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>"
    by auto
  then show ?R
  proof (cases "i = j")
    case False
    with j(1,2) have "memR I (\<Delta> \<sigma> (i + 1))"
      by (auto elim: order_trans[rotated] simp: diff_le_mono)
    moreover from False j(1,4) have "sat \<sigma> V v i \<phi>" by auto
    moreover from False j have "sat \<sigma> V v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>)"
      by (auto intro!: exI[of _ j])
    ultimately show ?thesis by blast
  qed simp
next
  assume \<Delta>: "memR I (\<Delta> \<sigma> (i + 1))" and now: "sat \<sigma> V v i \<phi>" and
   "next": "sat \<sigma> V v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>)"
  from "next" obtain j where j: "i + 1 \<le> j" "mem ((subtract (\<Delta> \<sigma> (i + 1)) I)) (\<tau> \<sigma> j - \<tau> \<sigma> (i + 1))"
      "sat \<sigma> V v j \<psi>" "\<forall>k \<in> {i + 1 ..< j}. sat \<sigma> V v k \<phi>"
    by (auto simp: diff_le_mono memL_mono)
  from \<Delta> j(1,2) have "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    by auto
  with now j(1,3,4) show ?L by (auto simp: le_eq_less_or_eq[of i] intro!: exI[of _ j])
qed auto

lemma sat_Since_rec: "sat \<sigma> V v i (Since \<phi> I \<psi>) \<longleftrightarrow>
  mem I 0 \<and> sat \<sigma> V v i \<psi> \<or>
  (i > 0 \<and> memR I (\<Delta> \<sigma> i) \<and> sat \<sigma> V v i \<phi> \<and> sat \<sigma> V v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>))"
  (is "?L \<longleftrightarrow> ?R")
proof (rule iffI; (elim disjE conjE)?)
  assume ?L
  then obtain j where j: "j \<le> i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" "sat \<sigma> V v j \<psi>" "\<forall>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>"
    by auto
  then show ?R
  proof (cases "i = j")
    case False
    with j(1) obtain k where [simp]: "i = k + 1"
      by (cases i) auto
    with j(1,2) False have "memR I (\<Delta> \<sigma> i)"
      by (auto elim: order_trans[rotated] simp: diff_le_mono2 le_Suc_eq)
    moreover from False j(1,4) have "sat \<sigma> V v i \<phi>" by auto
    moreover from False j have "sat \<sigma> V v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>)"
      by (auto intro!: exI[of _ j])
    ultimately show ?thesis by auto
  qed simp
next
  assume i: "0 < i" and \<Delta>: "memR I (\<Delta> \<sigma> i)" and now: "sat \<sigma> V v i \<phi>" and
   "prev": "sat \<sigma> V v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>)"
  from "prev" obtain j where j: "j \<le> i - 1" "mem (subtract (\<Delta> \<sigma> i) I) (\<tau> \<sigma> (i - 1) - \<tau> \<sigma> j)"
      "sat \<sigma> V v j \<psi>" "\<forall>k \<in> {j <.. i - 1}. sat \<sigma> V v k \<phi>"
    by (auto simp: diff_le_mono2 memL_mono)
  from \<Delta> i j(1,2) have "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)"
    by auto
  with now i j(1,3,4) show ?L by (auto simp: le_Suc_eq gr0_conv_Suc intro!: exI[of _ j])
qed auto

lemma sat_MatchF_rec: "sat \<sigma> V v i (MatchF I r) \<longleftrightarrow> memL I 0 \<and> Regex.eps (sat \<sigma> V v) i r \<or>
  memR I (\<Delta> \<sigma> (i + 1)) \<and> (\<exists>s \<in> Regex.lpd (sat \<sigma> V v) i r. sat \<sigma> V v (i + 1) (MatchF (subtract (\<Delta> \<sigma> (i + 1)) I) s))"
  (is "?L \<longleftrightarrow> ?R1 \<or> ?R2")
proof (rule iffI; (elim disjE conjE bexE)?)
  assume ?L
  then obtain j where j: "j \<ge> i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" and "Regex.match (sat \<sigma> V v) r i j" by auto
  then show "?R1 \<or> ?R2"
  proof (cases "i < j")
    case True
    with \<open>Regex.match (sat \<sigma> V v) r i j\<close> lpd_match[of i j "sat \<sigma> V v" r]
    obtain s where "s \<in> Regex.lpd (sat \<sigma> V v) i r" "Regex.match (sat \<sigma> V v) s (i + 1) j" by auto
    with True j have ?R2
      by (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j] elim: le_trans[rotated])
    then show ?thesis by blast
  qed (auto simp: eps_match)
next
  assume "memR I (\<Delta> \<sigma> (i + 1))"
  moreover
  fix s
  assume [simp]: "s \<in> Regex.lpd (sat \<sigma> V v) i r" and "sat \<sigma> V v (i + 1) (MatchF (subtract (\<Delta> \<sigma> (i + 1)) I) s)"
  then obtain j where "j > i" "Regex.match (sat \<sigma> V v) s (i + 1) j"
    "mem (subtract (\<Delta> \<sigma> (i + 1)) I) (\<tau> \<sigma> j - \<tau> \<sigma> (Suc i))"
    by (auto simp: diff_le_mono memL_mono Suc_le_eq)
  ultimately show ?L
    by (auto simp: le_diff_conv lpd_match intro!: exI[of _ j] bexI[of _ s])
qed (auto simp: eps_match intro!: exI[of _ i])

lemma sat_MatchP_rec: "sat \<sigma> V v i (MatchP I r) \<longleftrightarrow> memL I 0 \<and> Regex.eps (sat \<sigma> V v) i r \<or>
  i > 0 \<and> memR I (\<Delta> \<sigma> i) \<and> (\<exists>s \<in> Regex.rpd (sat \<sigma> V v) i r. sat \<sigma> V v (i - 1) (MatchP (subtract (\<Delta> \<sigma> i) I) s))"
  (is "?L \<longleftrightarrow> ?R1 \<or> ?R2")
proof (rule iffI; (elim disjE conjE bexE)?)
  assume ?L
  then obtain j where j: "j \<le> i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" and "Regex.match (sat \<sigma> V v) r j i" by auto
  then show "?R1 \<or> ?R2"
  proof (cases "j < i")
    case True
    with \<open>Regex.match (sat \<sigma> V v) r j i\<close> rpd_match[of j i "sat \<sigma> V v" r]
    obtain s where "s \<in> Regex.rpd (sat \<sigma> V v) i r" "Regex.match (sat \<sigma> V v) s j (i - 1)" by auto
    with True j have ?R2
      by (auto simp: diff_le_mono2 intro!: exI[of _ j])
    then show ?thesis by blast
  qed (auto simp: eps_match)
next
  assume "memR I (\<Delta> \<sigma> i)"
  moreover
  fix s
  assume [simp]: "s \<in> Regex.rpd (sat \<sigma> V v) i r" and "sat \<sigma> V v (i - 1) (MatchP (subtract (\<Delta> \<sigma> i) I) s)" "i > 0"
  then obtain j where "j < i" "Regex.match (sat \<sigma> V v) s j (i - 1)"
    "mem (subtract (\<Delta> \<sigma> i) I) (\<tau> \<sigma> (i - 1) - \<tau> \<sigma> j)" by (auto simp: gr0_conv_Suc less_Suc_eq_le)
  ultimately show ?L
    by (auto simp: rpd_match intro!: exI[of _ j] bexI[of _ s])
qed (auto simp: eps_match intro!: exI[of _ i])

lemma sat_Since_0: "sat \<sigma> V v 0 (Since \<phi> I \<psi>) \<longleftrightarrow> memL I 0 \<and> sat \<sigma> V v 0 \<psi>"
  by auto

lemma sat_MatchP_0: "sat \<sigma> V v 0 (MatchP I r) \<longleftrightarrow> memL I 0 \<and> Regex.eps (sat \<sigma> V v) 0 r"
  by (auto simp: eps_match)

lemma sat_Since_point: "sat \<sigma> V v i (Since \<phi> I \<psi>) \<Longrightarrow>
    (\<And>j. j \<le> i \<Longrightarrow> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<Longrightarrow> sat \<sigma> V v i (Since \<phi> (point (\<tau> \<sigma> i - \<tau> \<sigma> j)) \<psi>) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto intro: diff_le_self)

lemma sat_MatchP_point: "sat \<sigma> V v i (MatchP I r) \<Longrightarrow>
    (\<And>j. j \<le> i \<Longrightarrow> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<Longrightarrow> sat \<sigma> V v i (MatchP (point (\<tau> \<sigma> i - \<tau> \<sigma> j)) r) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto intro: diff_le_self)

lemma sat_Since_pointD: "sat \<sigma> V v i (Since \<phi> (point t) \<psi>) \<Longrightarrow> mem I t \<Longrightarrow> sat \<sigma> V v i (Since \<phi> I \<psi>)"
  by auto

lemma sat_MatchP_pointD: "sat \<sigma> V v i (MatchP (point t) r) \<Longrightarrow> mem I t \<Longrightarrow> sat \<sigma> V v i (MatchP I r)"
  by auto

lemma sat_fv_cong: "\<forall>x\<in>fv \<phi>. v!x = v'!x \<Longrightarrow> sat \<sigma> V v i \<phi> = sat \<sigma> V v' i \<phi>"
proof (induct \<phi> arbitrary: V v v' i rule: formula.induct)
  case (Pred n ts)
  show ?case by (simp cong: map_cong eval_trm_fv_cong[OF Pred[simplified, THEN bspec]] split: option.splits)
next
  case (Let p \<phi> \<psi>)
  then show ?case
    by auto
next
  case (Eq x1 x2)
  then show ?case unfolding fvi.simps sat.simps by (metis UnCI eval_trm_fv_cong)
next
  case (Less x1 x2)
  then show ?case unfolding fvi.simps sat.simps by (metis UnCI eval_trm_fv_cong)
next
  case (LessEq x1 x2)
  then show ?case unfolding fvi.simps sat.simps by (metis UnCI eval_trm_fv_cong)
next
  case (Ands l)
  have "\<And>\<phi>. \<phi> \<in> set l \<Longrightarrow> sat \<sigma> V v i \<phi> = sat \<sigma> V v' i \<phi>"
  proof -
    fix \<phi> assume "\<phi> \<in> set l"
    then have "fv \<phi> \<subseteq> fv (Ands l)" using fv_subset_Ands by blast
    then have "\<forall>x\<in>fv \<phi>. v!x = v'!x" using Ands.prems by blast
    then show "sat \<sigma> V v i \<phi> = sat \<sigma> V v' i \<phi>" using Ands.hyps \<open>\<phi> \<in> set l\<close> by blast
  qed
  then show ?case using sat_Ands by blast
next
  case (Exists t \<phi>)
  then show ?case unfolding sat.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
next
  case (Agg y \<omega> tys f \<phi>)
  let ?b = "length tys"
  have "v ! y = v' ! y"
    using Agg.prems by simp
  moreover have "sat \<sigma> V (zs @ v) i \<phi> = sat \<sigma> V (zs @ v') i \<phi>" if "length zs = ?b" for zs
    using that Agg.prems by (simp add: Agg.hyps[where v="zs @ v" and v'="zs @ v'"]
        nth_append fvi_iff_fv(1)[where b= ?b])
  moreover have "eval_trm (zs @ v) f = eval_trm (zs @ v') f" if "length zs = ?b" for zs
    using that Agg.prems by (auto intro!: eval_trm_fv_cong[where v="zs @ v" and v'="zs @ v'"]
        simp: nth_append fvi_iff_fv(1)[where b= ?b] fvi_trm_iff_fv_trm[where b= ?b])
  ultimately show ?case
    by (simp cong: conj_cong)
next
  case (MatchF I r)
  then have "Regex.match (sat \<sigma> V v) r = Regex.match (sat \<sigma> V v') r"
    by (intro match_fv_cong) (auto simp: fv_regex_alt)
  then show ?case
    by auto
next
  case (MatchP I r)
  then have "Regex.match (sat \<sigma> V v) r = Regex.match (sat \<sigma> V v') r"
    by (intro match_fv_cong) (auto simp: fv_regex_alt)
  then show ?case
    by auto
next
  case (TP t)
  then show ?case unfolding fvi.simps sat.simps by (metis eval_trm_fv_cong)
next
  case (TS t)
  then show ?case unfolding fvi.simps sat.simps by (metis eval_trm_fv_cong)
qed (auto 10 0 simp: Let_def split: nat.splits intro!: iff_exI)

lemma sat_the_restrict: "fv \<phi> \<subseteq> A \<Longrightarrow> Formula.sat \<sigma> V (map the (restrict A v)) i \<phi> = Formula.sat \<sigma> V (map the v) i \<phi>"
  by (rule sat_fv_cong) (auto intro!: map_the_restrict)

lemma match_fv_cong:
  "\<forall>x\<in>fv_regex r. v!x = v'!x \<Longrightarrow> Regex.match (sat \<sigma> V v) r = Regex.match (sat \<sigma> V v') r"
  by (rule match_fv_cong, rule sat_fv_cong) (auto simp: fv_regex_alt)

lemma eps_fv_cong:
  "\<forall>x\<in>fv_regex r. v!x = v'!x \<Longrightarrow> Regex.eps (sat \<sigma> V v) i r = Regex.eps (sat \<sigma> V v') i r"
  unfolding eps_match by (erule match_fv_cong[THEN fun_cong, THEN fun_cong])


subsection \<open>Past-only formulas\<close>

fun past_only :: "'t formula \<Rightarrow> bool" where
  "past_only (Pred _ _) = True"
| "past_only (Eq _ _) = True"
| "past_only (Less _ _) = True"
| "past_only (LessEq _ _) = True"
| "past_only (Let _ \<alpha> \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (LetPast _ \<alpha> \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (Neg \<psi>) = past_only \<psi>"
| "past_only (Or \<alpha> \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (And \<alpha> \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (Ands l) = (\<forall>\<alpha>\<in>set l. past_only \<alpha>)"
| "past_only (Exists _ \<psi>) = past_only \<psi>"
| "past_only (Agg _ _ _ _ \<psi>) = past_only \<psi>"
| "past_only (Prev _ \<psi>) = past_only \<psi>"
| "past_only (Next _ _) = False"
| "past_only (Since \<alpha> _ \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (Until \<alpha> _ \<beta>) = False"
| "past_only (MatchP _ r) = Regex.pred_regex past_only r"
| "past_only (MatchF _ _) = False"
| "past_only (TP _) = True"
| "past_only (TS _) = True"

lemma past_only_sat:
  assumes "prefix_of \<pi> \<sigma>" "prefix_of \<pi> \<sigma>'"
  shows "i < plen \<pi> \<Longrightarrow> dom V = dom V' \<Longrightarrow>
     (\<And>p v i. p \<in> dom V \<Longrightarrow> i < plen \<pi> \<Longrightarrow> the (V p) v i = the (V' p) v i) \<Longrightarrow>
     past_only \<phi> \<Longrightarrow> sat \<sigma> V v i \<phi> = sat \<sigma>' V' v i \<phi>"
proof (induction \<phi> arbitrary: V V' v i)
  case (Pred e ts)
  let ?en = "(e, length ts)"
  show ?case proof (cases "V ?en")
    case None
    then have "V' (e, length ts) = None" using \<open>dom V = dom V'\<close> by auto
    with None \<Gamma>_prefix_conv[OF assms(1,2) Pred(1)] show ?thesis by simp
  next
    case (Some a)
    moreover obtain a' where "V' ?en = Some a'"
      using Some \<open>dom V = dom V'\<close> by auto
    moreover have "the (V ?en) w i = the (V' ?en) w i" for w
      using Some Pred(1,3) by (fastforce intro: domI)
    ultimately show ?thesis by simp
  qed
next
  case (Let p \<phi> \<psi>)
  let ?pn = "(p, nfv \<phi>)"
  let ?V = "\<lambda>V \<sigma>. (V(?pn \<mapsto> \<lambda>w j. sat \<sigma> V w j \<phi>))"
  show ?case unfolding sat.simps proof (rule Let.IH(2))
    show "i < plen \<pi>" by fact
    from Let.prems show "past_only \<psi>" by simp
    from Let.prems show "dom (?V V \<sigma>) = dom (?V V' \<sigma>')"
      by (simp del: fun_upd_apply)
  next
    fix p' v i
    assume *: "p' \<in> dom (?V V \<sigma>)" "i < plen \<pi>"
    show "the (?V V \<sigma> p') v i = the (?V V' \<sigma>' p') v i" proof (cases "p' = ?pn")
      case True
      with Let \<open>i < plen \<pi>\<close> show ?thesis by auto
    next
      case False
      with * show ?thesis by (auto intro!: Let.prems(3))
    qed
  qed
next
  case (LetPast p \<phi> \<psi>)
  let ?pn = "(p, nfv \<phi>)"
  let ?V = "\<lambda>V \<sigma>. V(?pn \<mapsto> letpast_sat (\<lambda>X u k. sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>))"
  show ?case unfolding sat.simps Let_def proof (rule LetPast.IH(2))
    show "i < plen \<pi>" by fact
    from LetPast.prems show "past_only \<psi>" by simp
    from LetPast.prems show "dom (?V V \<sigma>) = dom (?V V' \<sigma>')"
      by (simp del: fun_upd_apply)
  next
    fix p' v i'
    assume *: "p' \<in> dom (?V V \<sigma>)" "i' < plen \<pi>"
    show "the (?V V \<sigma> p') v i' = the (?V V' \<sigma>' p') v i'"
    proof (cases "p' = ?pn")
      case True
      then have "?pn \<in> dom (?V V \<sigma>)" by simp
      then have "letpast_sat (\<lambda>X u k. sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>) v j =
            letpast_sat (\<lambda>X u k. sat \<sigma>' (V'(?pn \<mapsto> X)) u k \<phi>) v j"
        if "j < plen \<pi>" for j
        using that
      proof (induct "\<lambda>X u k. sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>" v j rule: letpast_sat.induct)
        case (1 v j)
        show ?case
        proof (subst (1 2) letpast_sat.simps, rule LetPast.IH(1), goal_cases plen dom eq past_only)
          case plen
          from "1" show ?case by simp
        next
          case dom
          from LetPast.prems show ?case by (auto simp add: dom_def)
        next
          case (eq p'' v' j')
          with "1" LetPast.prems(3)[of p'' j' v'] show ?case
            by (cases "p'' = ?pn") fastforce+
        next
          case past_only
          from LetPast.prems show ?case by simp
        qed
      qed
      with True \<open>i' < plen \<pi>\<close>
      show ?thesis by simp
    next
      case False
      with * show ?thesis by (auto intro!: LetPast.prems(3))
    qed
  qed
next
  case (Ands l)
  with \<Gamma>_prefix_conv[OF assms] show ?case by simp
next
  case (Prev I \<phi>)
  with \<tau>_prefix_conv[OF assms] show ?case by (simp split: nat.split)
next
  case (Since \<phi>1 I \<phi>2)
  with \<tau>_prefix_conv[OF assms] show ?case by auto
next
  case (MatchP I r)
  then have "Regex.match (sat \<sigma> V v) r a b = Regex.match (sat \<sigma>' V' v) r a b" if "b < plen \<pi>" for a b
    using that by (intro Regex.match_cong_strong) (auto simp: regex.pred_set)
  with \<tau>_prefix_conv[OF assms] MatchP(2) show ?case by auto
next
  case (TP t)
  with \<tau>_prefix_conv[OF assms] show ?case by simp
next
  case (TS t)
  with \<tau>_prefix_conv[OF assms] show ?case by simp
qed auto


subsection \<open>Well-formed formulas\<close>

fun wf_formula :: "'t formula \<Rightarrow> bool" 
  where "wf_formula (Let p \<phi> \<psi>) = ({0..<nfv \<phi>} \<subseteq> fv \<phi> \<and> wf_formula \<phi> \<and> wf_formula \<psi>)"
| "wf_formula (LetPast p \<phi> \<psi>) = ({0..<nfv \<phi>} \<subseteq> fv \<phi> \<and> wf_formula \<phi> \<and> wf_formula \<psi>)"
| "wf_formula (Neg \<phi>) =  wf_formula \<phi>"
| "wf_formula (Or \<phi> \<psi>) = (wf_formula \<phi> \<and> wf_formula \<psi>)"
| "wf_formula (And \<phi> \<psi>) = (wf_formula \<phi> \<and> wf_formula \<psi> )"
| "wf_formula (Ands l) = (list_all wf_formula l)"
| "wf_formula (Exists x \<phi>) = (wf_formula \<phi> \<and> 0 \<in> fv \<phi>)"
| "wf_formula (Agg y \<omega> tys f \<phi>) = (wf_formula \<phi> \<and> y + length tys \<notin> fv \<phi> \<and> {0..< length tys} \<subseteq> fv \<phi> )"
| "wf_formula (Prev I \<phi>) = (wf_formula \<phi>)"
| "wf_formula (Next I \<phi>) = (wf_formula \<phi>)"
| "wf_formula (Since \<phi> I \<psi>) = (wf_formula \<phi> \<and> wf_formula \<psi>)"
| "wf_formula (Until \<phi> I \<psi>) = (wf_formula \<phi> \<and> wf_formula \<psi>)"
| "wf_formula (MatchP I r) = Regex.pred_regex wf_formula r"
| "wf_formula (MatchF I r) = Regex.pred_regex wf_formula r"
| "wf_formula _ = True"

end (* context *)


subsection \<open> Notation \<close>

context
begin

abbreviation "eval_trm_option v t \<equiv> Formula.eval_trm (map the v) t"

abbreviation "sat_the \<sigma> V v i \<equiv> Formula.sat \<sigma> V (map the v) i"

end

bundle MFODL_no_notation
begin

no_notation trm.Var ("\<^bold>v")
     and trm.Const ("\<^bold>c")

no_notation formula.Pred ("_ \<dagger> _" [85, 85] 85)
     and formula.Eq (infixl "=\<^sub>F" 75)
     and formula.LessEq ("(_/ \<le>\<^sub>F _)" [76,76] 75)
     and formula.Less ("(_/ <\<^sub>F _)" [76,76] 75)
     and formula.Neg ("\<not>\<^sub>F _" [82] 82)
     and formula.And (infixr "\<and>\<^sub>F" 80)
     and formula.Or (infixr "\<or>\<^sub>F" 80)
     and formula.Exists ("\<exists>\<^sub>F:_. _" [70,70] 70)
     and formula.Ands ("\<And>\<^sub>F _" [70] 70)
     and formula.Prev ("\<^bold>Y _ _" [55, 65] 65)
     and formula.Next ("\<^bold>X _ _" [55, 65] 65)
     and formula.Since ("_ \<^bold>S _ _" [60,55,60] 60)
     and formula.Until ("_ \<^bold>U _ _" [60,55,60] 60)

no_notation Formula.fv_trm ("FV\<^sub>t")
     and Formula.fv ("FV")
     and eval_trm_option ("_\<lbrakk>_\<rbrakk>\<^sub>M" [51,89] 89)
     and sat_the ("\<langle>_, _, _, _\<rangle> \<Turnstile>\<^sub>M _" [56, 56, 56, 56, 56] 55)
     and Formula.sat ("\<langle>_, _, _, _\<rangle> \<Turnstile> _" [56, 56, 56, 56, 56] 55)
     and Interval.interval ("\<^bold>[_,_\<^bold>]")

end


bundle MFODL_notation
begin

notation trm.Var ("\<^bold>v")
     and trm.Const ("\<^bold>c")

notation formula.Pred ("_ \<dagger> _" [85, 85] 85)
     and formula.Eq (infixl "=\<^sub>F" 75)
     and formula.LessEq ("(_/ \<le>\<^sub>F _)" [76,76] 75)
     and formula.Less ("(_/ <\<^sub>F _)" [76,76] 75)
     and formula.Neg ("\<not>\<^sub>F _" [82] 82)
     and formula.And (infixr "\<and>\<^sub>F" 80)
     and formula.Or (infixr "\<or>\<^sub>F" 80)
     and formula.Exists ("\<exists>\<^sub>F:_. _" [70,70] 70)
     and formula.Ands ("\<And>\<^sub>F _" [70] 70)
     and formula.Prev ("\<^bold>Y _ _" [55, 65] 65)
     and formula.Next ("\<^bold>X _ _" [55, 65] 65)
     and formula.Since ("_ \<^bold>S _ _" [60,55,60] 60)
     and formula.Until ("_ \<^bold>U _ _" [60,55,60] 60)

notation Formula.fv_trm ("FV\<^sub>t")
     and Formula.fv ("FV")
     and eval_trm_option ("_\<lbrakk>_\<rbrakk>\<^sub>M" [51,89] 89)
     and sat_the ("\<langle>_, _, _, _\<rangle> \<Turnstile>\<^sub>M _" [56, 56, 56, 56, 56] 55)
     and Formula.sat ("\<langle>_, _, _, _\<rangle> \<Turnstile> _" [56, 56, 56, 56, 56] 55)
     and Interval.interval ("\<^bold>[_,_\<^bold>]")

end

unbundle MFODL_notation \<comment> \<open> enable notation \<close>

term "\<^bold>c (EInt 0) =\<^sub>F \<^bold>c (EInt 0)"
term "v\<lbrakk>\<^bold>c t\<rbrakk>\<^sub>M"
term "\<And>\<^sub>F [\<exists>\<^sub>F:t. (trm =\<^sub>F \<^bold>v x) \<and>\<^sub>F (a \<le>\<^sub>F \<^bold>c z), \<phi> \<^bold>U I \<psi>]"

term "\<langle>\<sigma>, V, v, i + length v\<rangle> \<Turnstile>\<^sub>M \<^bold>Y I (\<not>\<^sub>F (P \<dagger> [\<^bold>c a, \<^bold>v 0]) 
  \<and>\<^sub>F (Q \<dagger> [\<^bold>v y])) \<^bold>S (point n) ((\<^bold>X \<^bold>[2,3\<^bold>] (P \<dagger> [\<^bold>c b, \<^bold>v 0])) \<or>\<^sub>F Q \<dagger> [\<^bold>v y])"

unbundle MFODL_no_notation \<comment> \<open> disable notation \<close>


(*<*)
end
(*>*)
