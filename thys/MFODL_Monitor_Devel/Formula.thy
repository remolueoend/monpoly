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

derive (eq) ceq enat

instantiation enat :: ccompare begin
definition ccompare_enat :: "enat comparator option" where
  "ccompare_enat = Some (\<lambda>x y. if x = y then order.Eq else if x < y then order.Lt else order.Gt)"

instance by intro_classes
    (auto simp: ccompare_enat_def split: if_splits intro!: comparator.intro)
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

qualified datatype agg_type = Agg_Cnt | Agg_Min | Agg_Max | Agg_Sum | Agg_Avg | Agg_Med
qualified type_synonym agg_op = "agg_type \<times> event_data"

definition flatten_multiset :: "(event_data \<times> enat) set \<Rightarrow> event_data list" where
  "flatten_multiset M = concat (map (\<lambda>(x, c). replicate (the_enat c) x) (csorted_list_of_set M))"

fun eval_agg_op :: "agg_op \<Rightarrow> (event_data \<times> enat) set \<Rightarrow> event_data" where
  "eval_agg_op (Agg_Cnt, y0) M = (case flatten_multiset M of
      [] \<Rightarrow> y0
    | xs \<Rightarrow> EInt (integer_of_int (length xs)))"
| "eval_agg_op (Agg_Min, y0) M = (case flatten_multiset M of
      [] \<Rightarrow> y0
    | x # xs \<Rightarrow> foldl min x xs)"
| "eval_agg_op (Agg_Max, y0) M = (case flatten_multiset M of
      [] \<Rightarrow> y0
    | x # xs \<Rightarrow> foldl max x xs)"
| "eval_agg_op (agg_type.Agg_Sum, y0) M = (case flatten_multiset M of
      [] \<Rightarrow> y0
    | x # xs \<Rightarrow> foldl plus x xs)"
| "eval_agg_op (Agg_Avg, y0) M =(case flatten_multiset M of
      [] \<Rightarrow> y0
    | x # xs \<Rightarrow> EFloat (double_of_event_data (foldl plus x xs) / double_of_int (length (x # xs))))"
| "eval_agg_op (Agg_Med, y0) M =(case flatten_multiset M of
      [] \<Rightarrow> y0
    | xs \<Rightarrow> EFloat (let u = length xs; u' = u div 2 in
      if even u then
        (double_of_event_data (xs ! (u' - 1)) + double_of_event_data (xs ! u')) / double_of_int 2
      else double_of_event_data (xs ! u')))"

qualified datatype (discs_sels) formula = Pred name "trm list"
  | Let name formula formula
  | LetPast name formula formula
  | Eq trm trm | Less trm trm | LessEq trm trm
  | Neg formula | Or formula formula | And formula formula | Ands "formula list" | Exists formula
  | Agg nat agg_op nat trm formula
  | Prev \<I> formula | Next \<I> formula
  | Since formula \<I> formula | Until formula \<I> formula
  | MatchF \<I> "formula Regex.regex" | MatchP \<I> "formula Regex.regex"

qualified definition "FF = Exists (Neg (Eq (Var 0) (Var 0)))"
qualified definition "TT \<equiv> Neg FF"

qualified fun fvi :: "nat \<Rightarrow> formula \<Rightarrow> nat set" where
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
| "fvi b (Exists \<phi>) = fvi (Suc b) \<phi>"
| "fvi b (Agg y \<omega> b' f \<phi>) = fvi (b + b') \<phi> \<union> fvi_trm (b + b') f \<union> (if b \<le> y then {y - b} else {})"
| "fvi b (Prev I \<phi>) = fvi b \<phi>"
| "fvi b (Next I \<phi>) = fvi b \<phi>"
| "fvi b (Since \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Until \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (MatchF I r) = Regex.fv_regex (fvi b) r"
| "fvi b (MatchP I r) = Regex.fv_regex (fvi b) r"

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

lemma fvi_trm_iff_fv_trm: "x \<in> fvi_trm b t \<longleftrightarrow> x + b \<in> fv_trm t"
  using fvi_trm_plus[where b=0 and c=b] by simp_all

lemma fvi_plus: "x \<in> fvi (b + c) \<phi> \<longleftrightarrow> x + c \<in> fvi b \<phi>"
proof (induction \<phi> arbitrary: b rule: formula.induct)
  case (Exists \<phi>)
  then show ?case by force
next
  case (Agg y \<omega> b' f \<phi>)
  have *: "b + c + b' = b + b' + c" by simp
  from Agg show ?case by (force simp: * fvi_trm_plus)
qed (auto simp add: fvi_trm_plus fv_regex_commute[where g = "\<lambda>x. x + c"])

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

qualified definition nfv :: "formula \<Rightarrow> nat" where
  "nfv \<phi> = Max (insert 0 (Suc ` fv \<phi>))"

qualified abbreviation nfv_regex where
  "nfv_regex \<equiv> Regex.nfv_regex fv"

qualified definition envs :: "formula \<Rightarrow> env set" where
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

subsubsection \<open>Future reach\<close>

fun contains_pred :: "name \<times> nat \<Rightarrow> formula \<Rightarrow> bool" where
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
|  "contains_pred p (Exists \<phi>) = contains_pred p \<phi>"
|  "contains_pred p (Agg y \<omega> b' f \<phi>) = contains_pred p \<phi>"
|  "contains_pred p (Prev I \<phi>) = contains_pred p \<phi>"
|  "contains_pred p (Next I \<phi>) = contains_pred p \<phi>"
|  "contains_pred p (Since \<phi> I \<psi>) = (contains_pred p \<phi> \<or> contains_pred p \<psi>)"
|  "contains_pred p (Until \<phi> I \<psi>) = (contains_pred p \<phi> \<or> contains_pred p \<psi>)"
|  "contains_pred p (MatchP I r) = (\<exists>\<phi>\<in>Regex.atms r. contains_pred p \<phi>)"
|  "contains_pred p (MatchF I r) =  (\<exists>\<phi>\<in>Regex.atms r. contains_pred p \<phi>)"

fun safe_letpast :: "name \<times> nat \<Rightarrow> formula \<Rightarrow> rec_safety" where
   "safe_letpast p (Eq t1 t2) = Unused"
|  "safe_letpast p (Less t1 t2) = Unused"
|  "safe_letpast p (LessEq t1 t2) = Unused"
|  "safe_letpast p (Pred e ts) = (if p = (e, length ts) then NonFutuRec else Unused)"
|  "safe_letpast p (Let e \<phi> \<psi>) =
      (safe_letpast (e, nfv \<phi>) \<psi> * safe_letpast p \<phi>) \<squnion>
      (if p = (e, nfv \<phi>) then Unused else safe_letpast p \<psi>)"
|  "safe_letpast p (LetPast e \<phi> \<psi>) =
      (if p = (e, nfv \<phi>) then Unused else
        (safe_letpast (e, nfv \<phi>) \<psi> * safe_letpast p \<phi>) \<squnion> safe_letpast p \<psi>)"
|  "safe_letpast p (Neg \<phi>) = safe_letpast p \<phi>"
|  "safe_letpast p (Or \<phi> \<psi>) = (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
|  "safe_letpast p (And \<phi> \<psi>) = (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
|  "safe_letpast p (Ands l) = \<Squnion>(safe_letpast p ` set l)"
|  "safe_letpast p (Exists \<phi>) = safe_letpast p \<phi>"
|  "safe_letpast p (Agg y \<omega> b' f \<phi>) = safe_letpast p \<phi>"
|  "safe_letpast p (Prev I \<phi>) = PastRec * safe_letpast p \<phi>"
|  "safe_letpast p (Next I \<phi>) = AnyRec * safe_letpast p \<phi>"
|  "safe_letpast p (Since \<phi> I \<psi>) = safe_letpast p \<phi> \<squnion>
      ((if memL I 0 then NonFutuRec else PastRec) * safe_letpast p \<psi>)"
|  "safe_letpast p (Until \<phi> I \<psi>) = AnyRec * (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
|  "safe_letpast p (MatchP I r) = \<Squnion>(safe_letpast p ` Regex.atms r)"
|  "safe_letpast p (MatchF I r) =  AnyRec * \<Squnion>(safe_letpast p ` Regex.atms r)"

qualified fun future_bounded :: "formula \<Rightarrow> bool" where
  "future_bounded (Pred _ _) = True"
| "future_bounded (Let p \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (LetPast p \<phi> \<psi>) = (safe_letpast (p, nfv \<phi>) \<phi> \<le> PastRec \<and> future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Eq _ _) = True"
| "future_bounded (Less _ _) = True"
| "future_bounded (LessEq _ _) = True"
| "future_bounded (Neg \<phi>) = future_bounded \<phi>"
| "future_bounded (Or \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (And \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Ands l) = list_all future_bounded l"
| "future_bounded (Exists \<phi>) = future_bounded \<phi>"
| "future_bounded (Agg y \<omega> b f \<phi>) = future_bounded \<phi>"
| "future_bounded (Prev I \<phi>) = future_bounded \<phi>"
| "future_bounded (Next I \<phi>) = future_bounded \<phi>"
| "future_bounded (Since \<phi> I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Until \<phi> I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi> \<and> bounded I)"
| "future_bounded (MatchP I r) = Regex.pred_regex future_bounded r"
| "future_bounded (MatchF I r) = (Regex.pred_regex future_bounded r \<and> bounded I)"


subsubsection \<open>Semantics\<close>

definition "ecard A = (if finite A then card A else \<infinity>)"

declare conj_cong[fundef_cong]
fun letpast_sat where
  "letpast_sat sat v (i::nat) = sat (\<lambda>w j. j < i \<and> letpast_sat sat w j) v i"
declare letpast_sat.simps[simp del]

qualified fun sat :: "trace \<Rightarrow> (name \<times> nat \<rightharpoonup> env \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> env \<Rightarrow> nat \<Rightarrow> formula \<Rightarrow> bool" where
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
| "sat \<sigma> V v i (Exists \<phi>) = (\<exists>z. sat \<sigma> V (z # v) i \<phi>)"
| "sat \<sigma> V v i (Agg y \<omega> b f \<phi>) =
    (let M = {(x, ecard Zs) | x Zs. Zs = {zs. length zs = b \<and> sat \<sigma> V (zs @ v) i \<phi> \<and> eval_trm (zs @ v) f = x} \<and> Zs \<noteq> {}}
    in (M = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<b}) \<and> v ! y = eval_agg_op \<omega> M)"
| "sat \<sigma> V v i (Prev I \<phi>) = (case i of 0 \<Rightarrow> False | Suc j \<Rightarrow> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<phi>)"
| "sat \<sigma> V v i (Next I \<phi>) = (mem I ((\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i)) \<and> sat \<sigma> V v (Suc i) \<phi>)"
| "sat \<sigma> V v i (Since \<phi> I \<psi>) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<psi> \<and> (\<forall>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>))"
| "sat \<sigma> V v i (Until \<phi> I \<psi>) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat \<sigma> V v j \<psi> \<and> (\<forall>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>))"
| "sat \<sigma> V v i (MatchP I r) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Regex.match (sat \<sigma> V v) r j i)"
| "sat \<sigma> V v i (MatchF I r) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Regex.match (sat \<sigma> V v) r i j)"

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
  case (Exists \<phi>)
  then show ?case unfolding sat.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
next
  case (Agg y \<omega> b f \<phi>)
  have "v ! y = v' ! y"
    using Agg.prems by simp
  moreover have "sat \<sigma> V (zs @ v) i \<phi> = sat \<sigma> V (zs @ v') i \<phi>" if "length zs = b" for zs
    using that Agg.prems by (simp add: Agg.hyps[where v="zs @ v" and v'="zs @ v'"]
        nth_append fvi_iff_fv(1)[where b=b])
  moreover have "eval_trm (zs @ v) f = eval_trm (zs @ v') f" if "length zs = b" for zs
    using that Agg.prems by (auto intro!: eval_trm_fv_cong[where v="zs @ v" and v'="zs @ v'"]
        simp: nth_append fvi_iff_fv(1)[where b=b] fvi_trm_iff_fv_trm[where b="length zs"])
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
qed (auto 10 0 simp: Let_def split: nat.splits intro!: iff_exI)

lemma match_fv_cong:
  "\<forall>x\<in>fv_regex r. v!x = v'!x \<Longrightarrow> Regex.match (sat \<sigma> V v) r = Regex.match (sat \<sigma> V v') r"
  by (rule match_fv_cong, rule sat_fv_cong) (auto simp: fv_regex_alt)

lemma eps_fv_cong:
  "\<forall>x\<in>fv_regex r. v!x = v'!x \<Longrightarrow> Regex.eps (sat \<sigma> V v) i r = Regex.eps (sat \<sigma> V v') i r"
  unfolding eps_match by (erule match_fv_cong[THEN fun_cong, THEN fun_cong])


subsection \<open>Past-only formulas\<close>

fun past_only :: "formula \<Rightarrow> bool" where
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
| "past_only (Exists \<psi>) = past_only \<psi>"
| "past_only (Agg _ _ _ _ \<psi>) = past_only \<psi>"
| "past_only (Prev _ \<psi>) = past_only \<psi>"
| "past_only (Next _ _) = False"
| "past_only (Since \<alpha> _ \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (Until \<alpha> _ \<beta>) = False"
| "past_only (MatchP _ r) = Regex.pred_regex past_only r"
| "past_only (MatchF _ _) = False"

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
qed auto


subsection \<open>Safe formulas\<close>

fun remove_neg :: "formula \<Rightarrow> formula" where
  "remove_neg (Neg \<phi>) = \<phi>"
| "remove_neg \<phi> = \<phi>"

lemma fvi_remove_neg[simp]: "fvi b (remove_neg \<phi>) = fvi b \<phi>"
  by (cases \<phi>) simp_all

lemma partition_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x\<in>set xs \<Longrightarrow> f x = g x) \<Longrightarrow> partition f xs = partition g ys"
  by (induction xs arbitrary: ys) auto

lemma size_remove_neg[termination_simp]: "size (remove_neg \<phi>) \<le> size \<phi>"
  by (cases \<phi>) simp_all

fun is_constraint :: "formula \<Rightarrow> bool" where
  "is_constraint (Eq t1 t2) = True"
| "is_constraint (Less t1 t2) = True"
| "is_constraint (LessEq t1 t2) = True"
| "is_constraint (Neg (Eq t1 t2)) = True"
| "is_constraint (Neg (Less t1 t2)) = True"
| "is_constraint (Neg (LessEq t1 t2)) = True"
| "is_constraint _ = False"

definition safe_assignment :: "nat set \<Rightarrow> formula \<Rightarrow> bool" where
  "safe_assignment X \<phi> = (case \<phi> of
       Eq (Var x) (Var y) \<Rightarrow> (x \<notin> X \<longleftrightarrow> y \<in> X)
     | Eq (Var x) t \<Rightarrow> (x \<notin> X \<and> fv_trm t \<subseteq> X)
     | Eq t (Var x) \<Rightarrow> (x \<notin> X \<and> fv_trm t \<subseteq> X)
     | _ \<Rightarrow> False)"


fun safe_formula :: "formula \<Rightarrow> bool" where
  "safe_formula (Eq t1 t2) = (is_Const t1 \<and> (is_Const t2 \<or> is_Var t2) \<or> is_Var t1 \<and> is_Const t2)"
| "safe_formula (Neg (Eq (Var x) (Var y))) = (x = y)"
| "safe_formula (Less t1 t2) = False"
| "safe_formula (LessEq t1 t2) = False"
| "safe_formula (Pred e ts) = (\<forall>t\<in>set ts. is_Var t \<or> is_Const t)"
| "safe_formula (Let p \<phi> \<psi>) = ({0..<nfv \<phi>} \<subseteq> fv \<phi> \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
| "safe_formula (LetPast p \<phi> \<psi>) = (safe_letpast (p, nfv \<phi>) \<phi> \<le> PastRec \<and> {0..<nfv \<phi>} \<subseteq> fv \<phi> \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
| "safe_formula (Neg \<phi>) = (fv \<phi> = {} \<and> safe_formula \<phi>)"
| "safe_formula (Or \<phi> \<psi>) = (fv \<psi> = fv \<phi> \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
| "safe_formula (And \<phi> \<psi>) = (safe_formula \<phi> \<and>
    (safe_assignment (fv \<phi>) \<psi> \<or> safe_formula \<psi> \<or>
      fv \<psi> \<subseteq> fv \<phi> \<and> (is_constraint \<psi> \<or> (case \<psi> of Neg \<psi>' \<Rightarrow> safe_formula \<psi>' | _ \<Rightarrow> False))))"
| "safe_formula (Ands l) = (let (pos, neg) = partition safe_formula l in pos \<noteq> [] \<and>
    list_all safe_formula (map remove_neg neg) \<and> \<Union>(set (map fv neg)) \<subseteq> \<Union>(set (map fv pos)))"
| "safe_formula (Exists \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Agg y \<omega> b f \<phi>) = (safe_formula \<phi> \<and> y + b \<notin> fv \<phi> \<and> {0..<b} \<subseteq> fv \<phi> \<and> fv_trm f \<subseteq> fv \<phi>)"
| "safe_formula (Prev I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Next I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Since \<phi> I \<psi>) = (fv \<phi> \<subseteq> fv \<psi> \<and>
    (safe_formula \<phi> \<or> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)) \<and> safe_formula \<psi>)"
| "safe_formula (Until \<phi> I \<psi>) = (fv \<phi> \<subseteq> fv \<psi> \<and>
    (safe_formula \<phi> \<or> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)) \<and> safe_formula \<psi>)"
| "safe_formula (MatchP I r) = Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
     (g = Lax \<and> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))) Past Strict r"
| "safe_formula (MatchF I r) = Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
     (g = Lax \<and> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))) Futu Strict r"

abbreviation "safe_regex \<equiv> Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
  (g = Lax \<and> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)))"

lemma safe_regex_safe_formula:
  "safe_regex m g r \<Longrightarrow> \<phi> \<in> Regex.atms r \<Longrightarrow> safe_formula \<phi> \<or>
  (\<exists>\<psi>. \<phi> = Neg \<psi> \<and> safe_formula \<psi>)"
  by (cases g) (auto dest!: safe_regex_safe[rotated] split: formula.splits[where formula=\<phi>])

lemma safe_abbrevs[simp]: "safe_formula TT" "safe_formula FF"
  unfolding TT_def FF_def by auto

definition safe_neg :: "formula \<Rightarrow> bool" where
  "safe_neg \<phi> \<longleftrightarrow> (\<not> safe_formula \<phi> \<longrightarrow> safe_formula (remove_neg \<phi>))"

definition atms :: "formula Regex.regex \<Rightarrow> formula set" where
  "atms r = (\<Union>\<phi> \<in> Regex.atms r.
     if safe_formula \<phi> then {\<phi>} else case \<phi> of Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {})"

lemma atms_simps[simp]:
  "atms (Regex.Skip n) = {}"
  "atms (Regex.Test \<phi>) = (if safe_formula \<phi> then {\<phi>} else case \<phi> of Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {})"
  "atms (Regex.Plus r s) = atms r \<union> atms s"
  "atms (Regex.Times r s) = atms r \<union> atms s"
  "atms (Regex.Star r) = atms r"
  unfolding atms_def by auto

lemma finite_atms[simp]: "finite (atms r)"
  by (induct r) (auto split: formula.splits)

lemma disjE_Not2: "P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (\<not>P \<Longrightarrow> Q \<Longrightarrow> R) \<Longrightarrow> R"
  by blast

lemma safe_formula_induct[consumes 1, case_names Eq_Const Eq_Var1 Eq_Var2 neq_Var Pred Let LetPast
    And_assign And_safe And_constraint And_Not Ands Neg Or Exists Agg
    Prev Next Since Not_Since Until Not_Until MatchP MatchF]:
  assumes "safe_formula \<phi>"
    and Eq_Const: "\<And>c d. P (Eq (Const c) (Const d))"
    and Eq_Var1: "\<And>c x. P (Eq (Const c) (Var x))"
    and Eq_Var2: "\<And>c x. P (Eq (Var x) (Const c))"
    and neq_Var: "\<And>x. P (Neg (Eq (Var x) (Var x)))"
    and Pred: "\<And>e ts. \<forall>t\<in>set ts. is_Var t \<or> is_Const t \<Longrightarrow> P (Pred e ts)"
    and Let: "\<And>p \<phi> \<psi>. {0..<nfv \<phi>} \<subseteq> fv \<phi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Let p \<phi> \<psi>)"
    and LetPast: "\<And>p \<phi> \<psi>. safe_letpast (p, nfv \<phi>) \<phi> \<le> PastRec \<Longrightarrow> {0..<nfv \<phi>} \<subseteq> fv \<phi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (LetPast p \<phi> \<psi>)"
    and And_assign: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (And \<phi> \<psi>)"
    and And_safe: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow>
      P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And \<phi> \<psi>)"
    and And_constraint: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> \<not> safe_formula \<psi> \<Longrightarrow>
      fv \<psi> \<subseteq> fv \<phi> \<Longrightarrow> is_constraint \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (And \<phi> \<psi>)"
    and And_Not: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) (Neg \<psi>) \<Longrightarrow> \<not> safe_formula (Neg \<psi>) \<Longrightarrow>
      fv (Neg \<psi>) \<subseteq> fv \<phi> \<Longrightarrow> \<not> is_constraint (Neg \<psi>) \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And \<phi> (Neg \<psi>))"
    and Ands: "\<And>l pos neg. (pos, neg) = partition safe_formula l \<Longrightarrow> pos \<noteq> [] \<Longrightarrow>
      list_all safe_formula pos \<Longrightarrow> list_all safe_formula (map remove_neg neg) \<Longrightarrow>
      (\<Union>\<phi>\<in>set neg. fv \<phi>) \<subseteq> (\<Union>\<phi>\<in>set pos. fv \<phi>) \<Longrightarrow>
      list_all P pos \<Longrightarrow> list_all P (map remove_neg neg) \<Longrightarrow> P (Ands l)"
    and Neg: "\<And>\<phi>. fv \<phi> = {} \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Neg \<phi>)"
    and Or: "\<And>\<phi> \<psi>. fv \<psi> = fv \<phi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Or \<phi> \<psi>)"
    and Exists: "\<And>\<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Exists \<phi>)"
    and Agg: "\<And>y \<omega> b f \<phi>. y + b \<notin> fv \<phi> \<Longrightarrow> {0..<b} \<subseteq> fv \<phi> \<Longrightarrow> fv_trm f \<subseteq> fv \<phi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow>
      (\<And>\<phi>'. size \<phi>' \<le> size \<phi> \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> P \<phi>') \<Longrightarrow> P (Agg y \<omega> b f \<phi>)"
    and Prev: "\<And>I \<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Prev I \<phi>)"
    and Next: "\<And>I \<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Next I \<phi>)"
    and Since: "\<And>\<phi> I \<psi>. fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Since \<phi> I \<psi>)"
    and Not_Since: "\<And>\<phi> I \<psi>. fv (Neg \<phi>) \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow>
      \<not> safe_formula (Neg \<phi>) \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Since (Neg \<phi>) I \<psi> )"
    and Until: "\<And>\<phi> I \<psi>. fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Until \<phi> I \<psi>)"
    and Not_Until: "\<And>\<phi> I \<psi>. fv (Neg \<phi>) \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow>
      \<not> safe_formula (Neg \<phi>) \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Until (Neg \<phi>) I \<psi>)"
    and MatchP: "\<And>I r. safe_regex Past Strict r \<Longrightarrow> \<forall>\<phi> \<in> atms r. P \<phi> \<Longrightarrow> P (MatchP I r)"
    and MatchF: "\<And>I r. safe_regex Futu Strict r \<Longrightarrow> \<forall>\<phi> \<in> atms r. P \<phi> \<Longrightarrow> P (MatchF I r)"
  shows "P \<phi>"
using assms(1) proof (induction "size \<phi>" arbitrary: \<phi> rule: nat_less_induct)
  case 1
  then have IH: "size \<psi> < size \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<psi>" "safe_formula \<phi>" for \<psi>
    by auto
  then show ?case
  proof (cases \<phi> rule: safe_formula.cases)
    case (1 t1 t2)
    then show ?thesis using Eq_Const Eq_Var1 Eq_Var2 IH by (auto simp: trm.is_Const_def trm.is_Var_def)
  next
    case (10 \<phi>' \<psi>')
    from IH(2)[unfolded 10] consider
      (a) "safe_assignment (fv \<phi>') \<psi>'"
      | (b) "\<not> safe_assignment (fv \<phi>') \<psi>'" "safe_formula \<psi>'"
      | (c) "fv \<psi>' \<subseteq> fv \<phi>'" "\<not> safe_assignment (fv \<phi>') \<psi>'" "\<not> safe_formula \<psi>'" "is_constraint \<psi>'"
      | (d) \<psi>'' where "fv \<psi>' \<subseteq> fv \<phi>'" "\<not> safe_assignment (fv \<phi>') \<psi>'" "\<not> safe_formula \<psi>'" "\<not> is_constraint \<psi>'"
        "\<psi>' = Neg \<psi>''" "safe_formula \<psi>''"
      by (cases \<psi>') auto
    then show ?thesis proof cases
      case a
      then show ?thesis using IH by (auto simp: 10 intro: And_assign)
    next
      case b
      then show ?thesis using IH by (auto simp: 10 intro: And_safe)
    next
      case c
      then show ?thesis using IH by (auto simp: 10 intro: And_constraint)
    next
      case d
      then show ?thesis using IH by (auto simp: 10 intro!: And_Not)
    qed
  next
    case (11 l)
    obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
    have "pos \<noteq> []" using IH(2) posneg by (simp add: 11)
    moreover have "list_all safe_formula pos" using posneg by (simp add: list.pred_set)
    moreover have safe_remove_neg: "list_all safe_formula (map remove_neg neg)"
      using IH(2) posneg by (auto simp: 11)
    moreover have "list_all P pos"
      using posneg IH(1)
      by (auto simp add: 11 list_all_iff le_imp_less_Suc size_list_estimation')
    moreover have "list_all P (map remove_neg neg)"
      using IH(1) posneg safe_remove_neg
      by (auto simp add: 11 list_all_iff le_imp_less_Suc size_list_estimation' size_remove_neg)
    ultimately show ?thesis using IH Ands posneg by (simp add: 11)
  next
    case (16 \<phi>' I \<psi>')
    with IH show ?thesis
    proof (cases \<phi>')
      case (Ands l)
      then show ?thesis using IH Since
        by (auto simp: 16)
    qed (auto 0 3 simp: 16 elim!: disjE_Not2 intro: Since Not_Since) (*SLOW*)
  next
    case (17 \<phi>' I \<psi>')
    with IH show ?thesis
    proof (cases \<phi>')
      case (Ands l)
      then show ?thesis using IH Until by (auto simp: 17)
    qed (auto 0 3 simp: 17 elim!: disjE_Not2 intro: Until Not_Until) (*SLOW*)
  next
    case (18 I r)
    have case_Neg: "\<phi> \<in> (case x of Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {}) \<Longrightarrow> x = Neg \<phi>" for \<phi> x
      by (auto split: formula.splits)
    {
      fix \<psi>
      assume atms: "\<psi> \<in> atms r"
      then have "safe_formula \<psi>"
        using safe_regex_safe_formula IH(2)
        by (fastforce simp: 18 atms_def)
      moreover have "size \<psi> \<le> regex.size_regex size r"
        using atms
        by (auto simp: atms_def size_regex_estimation' dest!: case_Neg)
      ultimately have "P \<psi>"
        using IH(1)
        by (auto simp: 18)
    }
    then show ?thesis
      using IH(2)
      by (auto simp: 18 intro!: MatchP)
  next
    case (19 I r)
    have case_Neg: "\<phi> \<in> (case x of Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {}) \<Longrightarrow> x = Neg \<phi>" for \<phi> x
      by (auto split: formula.splits)
    {
      fix \<psi>
      assume atms: "\<psi> \<in> atms r"
      then have "safe_formula \<psi>"
        using safe_regex_safe_formula IH(2)
        by (fastforce simp: 19 atms_def)
      moreover have "size \<psi> \<le> regex.size_regex size r"
        using atms
        by (auto simp: atms_def size_regex_estimation' dest!: case_Neg)
      ultimately have "P \<psi>"
        using IH(1)
        by (auto simp: 19)
    }
    then show ?thesis
      using IH(2)
      by (auto simp: 19 intro!: MatchF)
  qed (auto simp: assms)
qed

lemma safe_formula_NegD:
  "safe_formula (Formula.Neg \<phi>) \<Longrightarrow> fv \<phi> = {} \<or> (\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x))"
  by (induct "Formula.Neg \<phi>" rule: safe_formula_induct) auto


subsection \<open>Slicing traces\<close>

qualified fun matches ::
  "env \<Rightarrow> formula \<Rightarrow> name \<times> event_data list \<Rightarrow> bool" where
  "matches v (Pred r ts) e = (fst e = r \<and> map (eval_trm v) ts = snd e)"
| "matches v (Let p \<phi> \<psi>) e =
    ((\<exists>v'. matches v' \<phi> e \<and> matches v \<psi> (p, v')) \<or>
    (fst e \<noteq> p \<or> length (snd e) \<noteq> nfv \<phi>) \<and> matches v \<psi> e)"
| "matches v (LetPast p \<phi> \<psi>) e =
    ((fst e \<noteq> p \<or> length (snd e) \<noteq> nfv \<phi>) \<and>
      (\<exists>e'. (\<lambda>e' e. matches (snd e') \<phi> e \<and> fst e' = p)\<^sup>*\<^sup>* e' e \<and> matches v \<psi> e'))"
| "matches v (Eq _ _) e = False"
| "matches v (Less _ _) e = False"
| "matches v (LessEq _ _) e = False"
| "matches v (Neg \<phi>) e = matches v \<phi> e"
| "matches v (Or \<phi> \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (And \<phi> \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Ands l) e = (\<exists>\<phi>\<in>set l. matches v \<phi> e)"
| "matches v (Exists \<phi>) e = (\<exists>z. matches (z # v) \<phi> e)"
| "matches v (Agg y \<omega> b f \<phi>) e = (\<exists>zs. length zs = b \<and> matches (zs @ v) \<phi> e)"
| "matches v (Prev I \<phi>) e = matches v \<phi> e"
| "matches v (Next I \<phi>) e = matches v \<phi> e"
| "matches v (Since \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Until \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (MatchP I r) e = (\<exists>\<phi> \<in> Regex.atms r. matches v \<phi> e)"
| "matches v (MatchF I r) e = (\<exists>\<phi> \<in> Regex.atms r. matches v \<phi> e)"

lemma matches_cong:
  "\<forall>x\<in>fv \<phi>. v!x = v'!x \<Longrightarrow> matches v \<phi> e = matches v' \<phi> e"
proof (induct \<phi> arbitrary: v v' e)
  case (Pred n ts)
  show ?case
    by (simp cong: map_cong eval_trm_fv_cong[OF Pred(1)[simplified, THEN bspec]])
next
  case (Let p \<phi> \<psi>)
  then show ?case
    by (cases e) (auto 11 0)
next
  case (LetPast p \<phi> \<psi>)
  then show ?case
    by (cases e) (auto 11 0)
next
  case (Ands l)
  have "\<And>\<phi>. \<phi> \<in> (set l) \<Longrightarrow> matches v \<phi> e = matches v' \<phi> e"
  proof -
    fix \<phi> assume "\<phi> \<in> (set l)"
    then have "fv \<phi> \<subseteq> fv (Ands l)" using fv_subset_Ands by blast
    then have "\<forall>x\<in>fv \<phi>. v!x = v'!x" using Ands.prems by blast
    then show "matches v \<phi> e = matches v' \<phi> e" using Ands.hyps \<open>\<phi> \<in> set l\<close> by blast
  qed
  then show ?case by simp
next
  case (Exists \<phi>)
  then show ?case unfolding matches.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
next
  case (Agg y \<omega> b f \<phi>)
  have "matches (zs @ v) \<phi> e = matches (zs @ v') \<phi> e" if "length zs = b" for zs
    using that Agg.prems by (simp add: Agg.hyps[where v="zs @ v" and v'="zs @ v'"]
        nth_append fvi_iff_fv(1)[where b=b])
  then show ?case by auto
qed (auto 9 0 simp add: nth_Cons' fv_regex_alt)

abbreviation relevant_events where "relevant_events \<phi> S \<equiv> {e. S \<inter> {v. matches v \<phi> e} \<noteq> {}}"

lemma sat_slice_strong:
  assumes "v \<in> S" "dom V = dom V'"
    "\<And>p n v i. (p, n) \<in> dom V \<Longrightarrow> (p, v) \<in> relevant_events \<phi> S \<Longrightarrow> n = length v \<Longrightarrow>
      the (V (p, n)) v i = the (V' (p, n)) v i"
  shows "relevant_events \<phi> S - {e. (fst e, length (snd e)) \<in> dom V} \<subseteq> E \<Longrightarrow>
    sat \<sigma> V v i \<phi> \<longleftrightarrow> sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>"
  using assms
proof (induction \<phi> arbitrary: V V' v S i)
  case (Pred r ts)
  let ?rn = "(r, length ts)"
  show ?case proof (cases "V ?rn")
    case None
    then have "V' ?rn = None" using \<open>dom V = dom V'\<close> by auto
    with None Pred(1,2) show ?thesis by (auto simp: domIff dest!: subsetD)
  next
    case (Some a)
    moreover obtain a' where "V' ?rn = Some a'" using Some \<open>dom V = dom V'\<close> by auto
    moreover have "the (V ?rn) (map (eval_trm v) ts) i = the (V' ?rn) (map (eval_trm v) ts) i"
      using Some Pred(2,4) by force
    ultimately show ?thesis by simp
  qed
next
  case (Let p \<phi> \<psi>)
  from Let.prems show ?case unfolding sat.simps
  proof (intro Let(2)[of S], goal_cases relevant v dom V)
    case (V p' n v' i)
    then show ?case
    proof (cases "(p', n) = (p, nfv \<phi>)")
      case True
      with V show ?thesis
        unfolding fun_upd_apply eqTrueI[OF True] if_True option.sel mem_Collect_eq
      proof (intro conj_cong refl Let(1)[where
        S="{v'. (p, v') \<in> relevant_events \<psi> S}" and V=V],
        goal_cases relevant' v' dom' V')
        case relevant'
        then show ?case
          by (elim subset_trans[rotated]) (auto simp: set_eq_iff)
      next
        case v'
        with True show ?case by simp
      next
        case (V' p' v' i)
        then show ?case
          by (intro V(4)) (auto simp: set_eq_iff)
      qed auto
    next
      case False
      from V(3,5,6,7) show ?thesis
        unfolding fun_upd_apply eq_False[THEN iffD2, OF False] if_False
        using False by (intro V(4)) (auto simp add: dom_def)
    qed
  qed (auto simp: dom_def)
next
  case (LetPast p \<phi> \<psi>)
  show ?case unfolding sat.simps Let_def
  proof (intro LetPast.IH(2)[of "S"], goal_cases relevant v dom V)
    case (V p' n v' i')
    show ?case
    proof (cases "(p', n) = (p, nfv \<phi>)")
      case True
      let ?pn = "(p, nfv \<phi>)"
      let ?R = "(\<lambda>e' e. matches (snd e') \<phi> e \<and> fst e' = p)\<^sup>*\<^sup>*"
      have inter_matches_imp_R: "{w. ?R (p, v') (p, w)} \<inter> {w. matches w \<phi> (p'', u)} \<noteq> {} \<Longrightarrow>
        ?R (p, v') (p'', u)" for p'' u
        by (auto intro: rtranclp.rtrancl_into_rtrancl)

      have "letpast_sat (\<lambda>X u k. sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>) w j =
          letpast_sat (\<lambda>X u k. sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) (V'(?pn \<mapsto> X)) u k \<phi>) w j"
        if "?R (p, v') (p, w)" "j \<le> i'" for w j
        using that
      proof (induct "\<lambda>X u k. sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>" w j rule: letpast_sat.induct)
        case (1 w j)
        show ?case
        proof (subst (1 2) letpast_sat.simps,
            rule LetPast.IH(1)[where S="{w. ?R (p, v') (p, w)}"],
            goal_cases relevant R dom eq)
          case relevant
          have "relevant_events \<phi> {w. ?R (p, v') (p, w)} - {e. (fst e, length (snd e)) \<in> insert ?pn (dom V)}
          \<subseteq> relevant_events (LetPast p \<phi> \<psi>) S - {e. (fst e, length (snd e)) \<in> dom V}"
            using V(2) True
            by (fastforce dest!: inter_matches_imp_R)
          also have "insert ?pn (dom V) = dom (V(?pn \<mapsto> \<lambda>w j'. j' < j \<and> letpast_sat (\<lambda>X u k. sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>) w j'))"
            by simp
          finally show ?case
            using LetPast.prems(1) by (rule subset_trans)
        next
          case R
          with 1 show ?case by simp
        next
          case dom
          then show ?case
            using LetPast.prems(3) by (auto simp add: dom_def)
        next
          case (eq p'' n' w' j')
          show ?case proof (cases "(p'', n') = ?pn")
            case True
            moreover have "letpast_sat (\<lambda>X u k. sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>) w' j' =
            letpast_sat (\<lambda>X u k. sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) (V'(?pn \<mapsto> X)) u k \<phi>) w' j'"
              if "j' < j"
              using that eq "1" True
              by (auto split: if_splits dest!: inter_matches_imp_R)
            ultimately show ?thesis
              by (simp cong: conj_cong)
          next
            case False
            then show ?thesis
              using eq V(2) LetPast.prems(4)[of p'' n' w' j'] True
              by (fastforce simp add: dom_def dest!: inter_matches_imp_R)
          qed
        qed
      qed
      then show ?thesis
        by (auto simp add: True)
    next
      case False
      then show ?thesis
        using V LetPast.prems(4)[of p' n v' i']
        by (fastforce simp: dom_def)
    qed
  qed (use LetPast.prems in \<open>auto simp: dom_def\<close>)
next
  case (Or \<phi> \<psi>)
  show ?case using Or.IH[of S V v V'] Or.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (And \<phi> \<psi>)
  show ?case using And.IH[of S V v V'] And.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (Ands l)
  obtain "relevant_events (Ands l) S - {e. (fst e, length (snd e)) \<in> dom V} \<subseteq> E" "v \<in> S"
    using Ands.prems(1) Ands.prems(2) by blast
  then have "{e. S \<inter> {v. matches v (Ands l) e} \<noteq> {}} - {e. (fst e, length (snd e)) \<in> dom V} \<subseteq> E" by simp
  have "\<And>\<phi>. \<phi> \<in> set l \<Longrightarrow> sat \<sigma> V v i \<phi> \<longleftrightarrow> sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>"
  proof -
    fix \<phi> assume "\<phi> \<in> set l"
    have "relevant_events \<phi> S = {e. S \<inter> {v. matches v \<phi> e} \<noteq> {}}" by simp
    have "{e. S \<inter> {v. matches v \<phi> e} \<noteq> {}} \<subseteq> {e. S \<inter> {v. matches v (Ands l) e} \<noteq> {}}" (is "?A \<subseteq> ?B")
    proof (rule subsetI)
      fix e assume "e \<in> ?A"
      then have "S \<inter> {v. matches v \<phi> e} \<noteq> {}" by blast
      moreover have "S \<inter> {v. matches v (Ands l) e} \<noteq> {}"
      proof -
        obtain v where "v \<in> S" "matches v \<phi> e" using calculation by blast
        then show ?thesis using \<open>\<phi> \<in> set l\<close> by auto
      qed
      then show "e \<in> ?B" by blast
    qed
    then have "relevant_events \<phi> S - {e. (fst e, length (snd e)) \<in> dom V} \<subseteq> E"
      using Ands.prems(1) by auto
    then show "sat \<sigma> V v i \<phi> \<longleftrightarrow> sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>"
      using Ands.prems(2,3) \<open>\<phi> \<in> set l\<close>
      by (intro Ands.IH[of \<phi> S V v V' i] Ands.prems(4)) auto
  qed
  show ?case using \<open>\<And>\<phi>. \<phi> \<in> set l \<Longrightarrow> sat \<sigma> V v i \<phi> = sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>\<close> sat_Ands by blast
next
  case (Exists \<phi>)
  have "sat \<sigma> V (z # v) i \<phi> = sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' (z # v) i \<phi>" for z
    using Exists.prems(1-3) by (intro Exists.IH[where S="{z # v | v. v \<in> S}"] Exists.prems(4)) auto
  then show ?case by simp
next
  case (Agg y \<omega> b f \<phi>)
  have "sat \<sigma> V (zs @ v) i \<phi> = sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' (zs @ v) i \<phi>" if "length zs = b" for zs
    using that Agg.prems(1-3) by (intro Agg.IH[where S="{zs @ v | v. v \<in> S}"] Agg.prems(4)) auto
  then show ?case by (simp cong: conj_cong)
next
  case (Prev I \<phi>)
  then show ?case by (auto cong: nat.case_cong)
next
  case (Next I \<phi>)
  then show ?case by simp
next
  case (Since \<phi> I \<psi>)
  show ?case using Since.IH[of S V] Since.prems
   by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (Until \<phi> I \<psi>)
  show ?case using Until.IH[of S V] Until.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (MatchP I r)
  from MatchP.prems(1-3) have "Regex.match (sat \<sigma> V v) r = Regex.match (sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v) r"
    by (intro Regex.match_fv_cong MatchP(1)[of _ S V v] MatchP.prems(4)) auto
  then show ?case
    by auto
next
  case (MatchF I r)
  from MatchF.prems(1-3) have "Regex.match (sat \<sigma> V v) r = Regex.match (sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v) r"
    by (intro Regex.match_fv_cong MatchF(1)[of _ S V v] MatchF.prems(4)) auto
  then show ?case
    by auto
qed simp_all

subsection \<open>Translation to n-ary conjunction\<close>

fun get_and_list :: "formula \<Rightarrow> formula list" where
  "get_and_list (Ands l) = (if l = [] then [Ands l] else l)"
| "get_and_list \<phi> = [\<phi>]"

lemma fv_get_and: "(\<Union>x\<in>(set (get_and_list \<phi>)). fvi b x) = fvi b \<phi>"
  by (induction \<phi> rule: get_and_list.induct) simp_all

lemma safe_get_and: "safe_formula \<phi> \<Longrightarrow> list_all safe_neg (get_and_list \<phi>)"
  by (induction \<phi> rule: get_and_list.induct) (auto simp add: safe_neg_def list_all_iff)

lemma sat_get_and: "sat \<sigma> V v i \<phi> \<longleftrightarrow> list_all (sat \<sigma> V v i) (get_and_list \<phi>)"
  by (induction \<phi> rule: get_and_list.induct) (simp_all add: list_all_iff)

lemma safe_letpast_get_and: "\<Squnion>(safe_letpast p ` set (get_and_list \<phi>)) = safe_letpast p \<phi>"
  by (induction \<phi> rule: get_and_list.induct) (simp_all flip: bot_rec_safety_def)

lemma not_contains_pred_get_and: "\<And>x.\<not>contains_pred p \<phi> \<Longrightarrow> x \<in> set (get_and_list \<phi>) \<Longrightarrow> \<not> contains_pred p x"
  by (induction \<phi> rule: get_and_list.induct) (auto split: if_splits)

primrec convert_multiway :: "formula \<Rightarrow> formula" where
  "convert_multiway (Pred p ts) = (Pred p ts)"
| "convert_multiway (Eq t u) = (Eq t u)"
| "convert_multiway (Less t u) = (Less t u)"
| "convert_multiway (LessEq t u) = (LessEq t u)"
| "convert_multiway (Let p \<phi> \<psi>) = Let p (convert_multiway \<phi>) (convert_multiway \<psi>)"
| "convert_multiway (LetPast p \<phi> \<psi>) = LetPast p (convert_multiway \<phi>) (convert_multiway \<psi>)"
| "convert_multiway (Neg \<phi>) = Neg (convert_multiway \<phi>)"
| "convert_multiway (Or \<phi> \<psi>) = Or (convert_multiway \<phi>) (convert_multiway \<psi>)"
| "convert_multiway (And \<phi> \<psi>) = (if safe_assignment (fv \<phi>) \<psi> then
      And (convert_multiway \<phi>) \<psi>
    else if safe_formula \<psi> then
      Ands (get_and_list (convert_multiway \<phi>) @ get_and_list (convert_multiway \<psi>))
    else if is_constraint \<psi> then
      And (convert_multiway \<phi>) \<psi>
    else Ands (convert_multiway \<psi> # get_and_list (convert_multiway \<phi>)))"
| "convert_multiway (Ands \<phi>s) = Ands (map convert_multiway \<phi>s)"
| "convert_multiway (Exists \<phi>) = Exists (convert_multiway \<phi>)"
| "convert_multiway (Agg y \<omega> b f \<phi>) = Agg y \<omega> b f (convert_multiway \<phi>)"
| "convert_multiway (Prev I \<phi>) = Prev I (convert_multiway \<phi>)"
| "convert_multiway (Next I \<phi>) = Next I (convert_multiway \<phi>)"
| "convert_multiway (Since \<phi> I \<psi>) = Since (convert_multiway \<phi>) I (convert_multiway \<psi>)"
| "convert_multiway (Until \<phi> I \<psi>) = Until (convert_multiway \<phi>) I (convert_multiway \<psi>)"
| "convert_multiway (MatchP I r) = MatchP I (Regex.map_regex convert_multiway r)"
| "convert_multiway (MatchF I r) = MatchF I (Regex.map_regex convert_multiway r)"

abbreviation "convert_multiway_regex \<equiv> Regex.map_regex convert_multiway"

lemma fv_safe_get_and:
  "safe_formula \<phi> \<Longrightarrow> fv \<phi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list \<phi>))). fv x)"
proof (induction \<phi> rule: get_and_list.induct)
  case (1 l)
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  have sub: "(\<Union>x\<in>set neg. fv x) \<subseteq> (\<Union>x\<in>set pos. fv x)" using "1.prems" posneg by simp
  then have "fv (Ands l) \<subseteq> (\<Union>x\<in>set pos. fv x)"
  proof -
    have "fv (Ands l) = (\<Union>x\<in>set pos. fv x) \<union> (\<Union>x\<in>set neg. fv x)" using posneg by auto
    then show ?thesis using sub by simp
  qed
  then show ?case using posneg by auto
qed auto

lemma ex_safe_get_and:
  "safe_formula \<phi> \<Longrightarrow> list_ex safe_formula (get_and_list \<phi>)"
proof (induction \<phi> rule: get_and_list.induct)
  case (1 l)
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  then have "pos \<noteq> []" using "1.prems" by simp
  then obtain x where "x \<in> set pos" by fastforce
  then show ?case using posneg using Bex_set_list_ex by fastforce
qed simp_all

lemma case_NegE: "(case \<phi> of Neg \<phi>' \<Rightarrow> P \<phi>' | _ \<Rightarrow> False) \<Longrightarrow> (\<And>\<phi>'. \<phi> = Neg \<phi>' \<Longrightarrow> P \<phi>' \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (cases \<phi>) simp_all

lemma convert_multiway_remove_neg: "safe_formula (remove_neg \<phi>) \<Longrightarrow> convert_multiway (remove_neg \<phi>) = remove_neg (convert_multiway \<phi>)"
  by (cases \<phi>) (auto elim: case_NegE)

lemma fv_convert_multiway: "fvi b (convert_multiway \<phi>) = fvi b \<phi>"
  by (induction \<phi> arbitrary: b)
    (auto simp add: fv_get_and Un_commute fv_regex_alt regex.set_map)

lemma nfv_convert_multiway: "nfv (convert_multiway \<phi>) = nfv \<phi>"
  unfolding nfv_def by (auto simp: fv_convert_multiway)

lemma get_and_nonempty[simp]: "get_and_list \<phi> \<noteq> []"
  by (induction \<phi>) auto

lemma future_bounded_get_and:
  "list_all future_bounded (get_and_list \<phi>) = future_bounded \<phi>"
  by (induction \<phi>) simp_all

lemma contains_pred_convert_multiway: "\<not> (contains_pred p \<phi>) \<Longrightarrow> \<not>(contains_pred p (convert_multiway \<phi>))"
proof (induction p \<phi> rule: contains_pred.induct)
  case(9 p \<phi> \<psi>)
  then show ?case by (auto simp: not_contains_pred_get_and)
next
  case(17 p I r)
  then show ?case by (auto simp add: regex.set_map)
next
  case(18 p I r)
  then show ?case by (auto simp add: regex.set_map)
qed(auto simp: nfv_convert_multiway)

lemma safe_letpast_convert_multiway: "safe_letpast p (convert_multiway \<phi>) = safe_letpast p \<phi>"
proof (induction p \<phi> rule: safe_letpast.induct)
  case (5 p e \<phi> \<psi>)
  then show?case by (auto simp add: contains_pred_convert_multiway nfv_convert_multiway)
next
  case (6 p e \<phi> \<psi>)
  then show?case by (auto simp add: contains_pred_convert_multiway nfv_convert_multiway)
next
  case(9 p \<phi> \<psi>)
  then show ?case
    by (simp add: image_Un Sup_rec_safety_union safe_letpast_get_and sup_commute)
next
  case(17 p I r)
  then show ?case
    by (simp add: regex.set_map image_image cong: image_cong)
next
  case(18 p I r)
  then show ?case
    by (simp add: regex.set_map image_image cong: image_cong)
qed (auto simp add: image_image)

 (*

    unfolding convert_multiway.simps fvi.simps fv_regex_alt regex.set_map image_image
    by (intro arg_cong[where f=Union, OF image_cong[OF refl]])
      (auto dest!: safe_regex_safe_formula)
qed (auto simp del: convert_multiway.simps(8))

*)

lemma safe_convert_multiway: "safe_formula \<phi> \<Longrightarrow> safe_formula (convert_multiway \<phi>)"
proof (induction \<phi> rule: safe_formula_induct)
  case (LetPast p \<phi> \<psi>)
  then show ?case
    by (auto simp: safe_letpast_convert_multiway nfv_convert_multiway fv_convert_multiway)
next
  case (And_safe \<phi> \<psi>)
  let ?a = "And \<phi> \<psi>"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = Ands (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    using And_safe by simp
  show ?case proof -
    let ?l = "get_and_list ?c\<phi> @ get_and_list ?c\<psi>"
    obtain pos neg where posneg: "(pos, neg) = partition safe_formula ?l" by simp
    then have "list_all safe_formula pos" by (auto simp: list_all_iff)
    have lsafe_neg: "list_all safe_neg ?l"
      using And_safe \<open>safe_formula \<phi>\<close> \<open>safe_formula \<psi>\<close>
      by (simp add: safe_get_and)
    then have "list_all safe_formula (map remove_neg neg)"
    proof -
      have "\<And>x. x \<in> set neg \<Longrightarrow> safe_formula (remove_neg x)"
      proof -
        fix x assume "x \<in> set neg"
        then have "\<not> safe_formula x" using posneg by auto
        moreover have "safe_neg x" using lsafe_neg \<open>x \<in> set neg\<close>
          unfolding safe_neg_def list_all_iff partition_set[OF posneg[symmetric], symmetric]
          by simp
        ultimately show "safe_formula (remove_neg x)" using safe_neg_def by blast
      qed
      then show ?thesis by (auto simp: list_all_iff)
    qed

    have pos_filter: "pos = filter safe_formula (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
      using posneg by simp
    have "(\<Union>x\<in>set neg. fv x) \<subseteq> (\<Union>x\<in>set pos. fv x)"
    proof -
      have 1: "fv ?c\<phi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list ?c\<phi>))). fv x)" (is "_ \<subseteq> ?fv\<phi>")
        using And_safe \<open>safe_formula \<phi>\<close> by (blast intro!: fv_safe_get_and)
      have 2: "fv ?c\<psi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list ?c\<psi>))). fv x)" (is "_ \<subseteq> ?fv\<psi>")
        using And_safe \<open>safe_formula \<psi>\<close> by (blast intro!: fv_safe_get_and)
      have "(\<Union>x\<in>set neg. fv x) \<subseteq> fv ?c\<phi> \<union> fv ?c\<psi>" proof -
        have "\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` (set pos \<union> set neg))"
          by simp
        also have "... \<subseteq> fv (convert_multiway \<phi>) \<union> fv (convert_multiway \<psi>)"
          unfolding partition_set[OF posneg[symmetric], simplified]
          by (simp add: fv_get_and)
        finally show ?thesis .
      qed
      then have "(\<Union>x\<in>set neg. fv x) \<subseteq> ?fv\<phi> \<union> ?fv\<psi>" using 1 2 by blast
      then show ?thesis unfolding pos_filter by simp
    qed
    have "pos \<noteq> []"
    proof -
      obtain x where "x \<in> set (get_and_list ?c\<phi>)" "safe_formula x"
        using And_safe \<open>safe_formula \<phi>\<close> ex_safe_get_and by (auto simp: list_ex_iff)
      then show ?thesis
        unfolding pos_filter by (auto simp: filter_empty_conv)
    qed
    then show ?thesis unfolding b_def
      using \<open>\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` set pos)\<close> \<open>list_all safe_formula (map remove_neg neg)\<close>
        \<open>list_all safe_formula pos\<close> posneg
      by simp
  qed
next
  case (And_Not \<phi> \<psi>)
  let ?a = "And \<phi> (Neg \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = Ands (Neg ?c\<psi> # get_and_list ?c\<phi>)"
    using And_Not by simp
  show ?case proof -
    let ?l = "Neg ?c\<psi> # get_and_list ?c\<phi>"
    note \<open>safe_formula ?c\<phi>\<close>
    then have "list_all safe_neg (get_and_list ?c\<phi>)" by (simp add: safe_get_and)
    moreover have "safe_neg (Neg ?c\<psi>)"
      using \<open>safe_formula ?c\<psi>\<close> by (simp add: safe_neg_def)
    then have lsafe_neg: "list_all safe_neg ?l" using calculation by simp
    obtain pos neg where posneg: "(pos, neg) = partition safe_formula ?l" by simp
    then have "list_all safe_formula pos" by (auto simp: list_all_iff)
    then have "list_all safe_formula (map remove_neg neg)"
    proof -
      have "\<And>x. x \<in> (set neg) \<Longrightarrow> safe_formula (remove_neg x)"
      proof -
        fix x assume "x \<in> set neg"
        then have "\<not> safe_formula x" using posneg by (auto simp del: filter.simps)
        moreover have "safe_neg x" using lsafe_neg \<open>x \<in> set neg\<close>
          unfolding safe_neg_def list_all_iff partition_set[OF posneg[symmetric], symmetric]
          by simp
        ultimately show "safe_formula (remove_neg x)" using safe_neg_def by blast
      qed
      then show ?thesis using Ball_set_list_all by force
    qed

    have pos_filter: "pos = filter safe_formula ?l"
      using posneg by simp
    have neg_filter: "neg = filter (Not \<circ> safe_formula) ?l"
      using posneg by simp
    have "(\<Union>x\<in>(set neg). fv x) \<subseteq> (\<Union>x\<in>(set pos). fv x)"
    proof -
      have fv_neg: "(\<Union>x\<in>(set neg). fv x) \<subseteq> (\<Union>x\<in>(set ?l). fv x)" using posneg by auto
      have "(\<Union>x\<in>(set ?l). fv x) \<subseteq> fv ?c\<phi> \<union> fv ?c\<psi>"
        using \<open>safe_formula \<phi>\<close> \<open>safe_formula \<psi>\<close>
        by (simp add: fv_get_and fv_convert_multiway)
      also have "fv ?c\<phi> \<union> fv ?c\<psi> \<subseteq> fv ?c\<phi>"
        using \<open>fv (Neg \<psi>) \<subseteq> fv \<phi>\<close>
        by (simp add: fv_convert_multiway)
      finally have "(\<Union>x\<in>(set neg). fv x) \<subseteq> fv ?c\<phi>"
        using fv_neg unfolding neg_filter by blast
      then show ?thesis
        unfolding pos_filter
        using fv_safe_get_and[OF And_Not.IH(1)]
        by auto
    qed
    have "pos \<noteq> []"
    proof -
      obtain x where "x \<in> set (get_and_list ?c\<phi>)" "safe_formula x"
        using And_Not.IH \<open>safe_formula \<phi>\<close> ex_safe_get_and by (auto simp: list_ex_iff)
      then show ?thesis
        unfolding pos_filter by (auto simp: filter_empty_conv)
    qed
    then show ?thesis unfolding b_def
      using \<open>\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` set pos)\<close> \<open>list_all safe_formula (map remove_neg neg)\<close>
        \<open>list_all safe_formula pos\<close> posneg
      by simp
  qed
next
  case (Ands l)
  then show ?case
    using convert_multiway_remove_neg fv_convert_multiway
    by (auto simp: list.pred_set filter_map filter_empty_conv subset_eq) metis
next
  case (Neg \<phi>)
  have "safe_formula (Neg \<phi>') \<longleftrightarrow> safe_formula \<phi>'" if "fv \<phi>' = {}" for \<phi>'
    using that by (cases "Neg \<phi>'" rule: safe_formula.cases) simp_all
  with Neg show ?case by (simp add: fv_convert_multiway)
next
  case (MatchP I r)
  then show ?case
    by (auto 0 3 simp: atms_def fv_convert_multiway intro!: safe_regex_map_regex
      elim!: disjE_Not2 case_NegE
      dest: safe_regex_safe_formula split: if_splits)
next
  case (MatchF I r)
  then show ?case
    by (auto 0 3 simp: atms_def fv_convert_multiway intro!: safe_regex_map_regex
      elim!: disjE_Not2 case_NegE
      dest: safe_regex_safe_formula split: if_splits)
qed (auto simp add: fv_convert_multiway nfv_convert_multiway)

lemma future_bounded_remove_neg: "future_bounded (remove_neg \<phi>) = future_bounded \<phi>"
  by (cases \<phi>) auto

lemma future_bounded_convert_multiway: "safe_formula \<phi> \<Longrightarrow> future_bounded (convert_multiway \<phi>) = future_bounded \<phi>"
proof (induction \<phi> rule: safe_formula_induct)
  case (LetPast p \<phi> \<psi>)
  then show ?case by (auto simp: safe_letpast_convert_multiway nfv_convert_multiway)
next
  case (And_safe \<phi> \<psi>)
  let ?a = "And \<phi> \<psi>"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = Ands (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    using And_safe by simp
  have "future_bounded ?a = (future_bounded ?c\<phi> \<and> future_bounded ?c\<psi>)"
    using And_safe by simp
  moreover have "future_bounded ?c\<phi> = list_all future_bounded (get_and_list ?c\<phi>)"
    using \<open>safe_formula \<phi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "future_bounded ?c\<psi> = list_all future_bounded (get_and_list ?c\<psi>)"
    using \<open>safe_formula \<psi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "future_bounded ?b = list_all future_bounded (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    unfolding b_def by simp
  ultimately show ?case by simp
next
  case (And_Not \<phi> \<psi>)
  let ?a = "And \<phi> (Neg \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = Ands (Neg ?c\<psi> # get_and_list ?c\<phi>)"
    using And_Not by simp
  have "future_bounded ?a = (future_bounded ?c\<phi> \<and> future_bounded ?c\<psi>)"
    using And_Not by simp
  moreover have "future_bounded ?c\<phi> = list_all future_bounded (get_and_list ?c\<phi>)"
    using \<open>safe_formula \<phi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "future_bounded ?b = list_all future_bounded (Neg ?c\<psi> # get_and_list ?c\<phi>)"
    unfolding b_def by (simp add: list.pred_map o_def)
  ultimately show ?case by auto
next
  case (MatchP I r)
  then show ?case
    by (fastforce simp: atms_def regex.pred_set regex.set_map ball_Un
        elim: safe_regex_safe_formula[THEN disjE_Not2])
next
  case (MatchF I r)
  then show ?case
    by (fastforce simp: atms_def regex.pred_set regex.set_map ball_Un
        elim: safe_regex_safe_formula[THEN disjE_Not2])
qed (auto simp: list.pred_set convert_multiway_remove_neg future_bounded_remove_neg)

lemma sat_convert_multiway: "safe_formula \<phi> \<Longrightarrow> sat \<sigma> V v i (convert_multiway \<phi>) \<longleftrightarrow> sat \<sigma> V v i \<phi>"
proof (induction \<phi> arbitrary: V v i rule: safe_formula_induct)
  case (And_safe \<phi> \<psi>)
  let ?a = "And \<phi> \<psi>"
  let ?b = "convert_multiway ?a"
  let ?la = "get_and_list (convert_multiway \<phi>)"
  let ?lb = "get_and_list (convert_multiway \<psi>)"
  let ?sat = "sat \<sigma> V v i"
  have b_def: "?b = Ands (?la @ ?lb)" using And_safe by simp
  have "list_all ?sat ?la \<longleftrightarrow> ?sat \<phi>" using And_safe sat_get_and by blast
  moreover have "list_all ?sat ?lb \<longleftrightarrow> ?sat \<psi>" using And_safe sat_get_and by blast
  ultimately show ?case using And_safe by (auto simp: list.pred_set)
next
  case (And_Not \<phi> \<psi>)
  let ?a = "And \<phi> (Neg \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?la = "get_and_list (convert_multiway \<phi>)"
  let ?lb = "convert_multiway \<psi>"
  let ?sat = "sat \<sigma> V v i"
  have b_def: "?b = Ands (Neg ?lb # ?la)" using And_Not by simp
  have "list_all ?sat ?la \<longleftrightarrow> ?sat \<phi>" using And_Not sat_get_and by blast
  then show ?case using And_Not by (auto simp: list.pred_set)
next
  case (Agg y \<omega> b f \<phi>)
  then show ?case
    by (simp add: nfv_def fv_convert_multiway cong: conj_cong)
next
  case (MatchP I r)
  then have "Regex.match (sat \<sigma> V v) (convert_multiway_regex r) = Regex.match (sat \<sigma> V v) r"
    unfolding match_map_regex
    by (intro Regex.match_fv_cong)
      (auto 0 5 simp: atms_def elim!: disjE_Not2 dest!: safe_regex_safe_formula)
  then show ?case
    by auto
next
  case (MatchF I r)
  then have "Regex.match (sat \<sigma> V v) (convert_multiway_regex r) = Regex.match (sat \<sigma> V v) r"
    unfolding match_map_regex
    by (intro Regex.match_fv_cong)
      (auto 0 5 simp: atms_def elim!: disjE_Not2 dest!: safe_regex_safe_formula)
  then show ?case
    by auto
next
  case (Let p \<phi> \<psi>)
  then show ?case
    by (auto simp add: nfv_convert_multiway fun_upd_def)
next
  case (LetPast p \<phi> \<psi>)
  then show ?case
    by (auto simp add: nfv_convert_multiway fun_upd_def)
next
  case (Ands l)
  have sat_remove_neg: "(sat \<sigma> V v i (remove_neg \<phi>) \<longleftrightarrow> sat \<sigma> V v i (remove_neg \<psi>)) \<longleftrightarrow>
        (sat \<sigma> V v i \<phi> \<longleftrightarrow> sat \<sigma> V v i \<psi>)" if "is_Neg \<phi> \<longleftrightarrow> is_Neg \<psi>" for V v i \<phi> \<psi>
    using that by (cases \<phi>; cases \<psi>) (auto simp add: is_Neg_def)
  have is_Neg_cm: "is_Neg (convert_multiway \<phi>) \<longleftrightarrow> is_Neg \<phi>" for \<phi>
    by (cases \<phi>) auto
  from Ands show ?case
    by (fastforce simp: list.pred_set convert_multiway_remove_neg sat_remove_neg[OF is_Neg_cm])
qed (auto cong: nat.case_cong)

lemma sat_the_restrict: "fv \<phi> \<subseteq> A \<Longrightarrow> Formula.sat \<sigma> V (map the (restrict A v)) i \<phi> = Formula.sat \<sigma> V (map the v) i \<phi>"
  by (rule sat_fv_cong) (auto intro!: map_the_restrict)

lemma inj_eval: " \<forall>t\<in>set ts. is_Var t \<or> is_Const t \<Longrightarrow>
    inj_on (\<lambda>v. map (eval_trm (map the v)) ts) {v. wf_tuple n (\<Union> (fv_trm ` set ts)) v}"
  apply(intro inj_onI)
      apply(rule nth_equalityI)
       apply(auto simp add: wf_tuple_def)[]
      subgoal for x y i
        apply(cases "i \<in> (\<Union> (fv_trm ` set ts))")
         apply(subgoal_tac " Var i \<in> set ts")
          apply(simp)
        apply(rotate_tac)
          apply(drule(1) bspec)
          apply(simp add: wf_tuple_def)
          apply (meson option.expand)
         apply(auto simp add: is_Var_def is_Const_def)[]
          apply(simp add: wf_tuple_def)
        by metis
      done

lemma inj_eval2: " \<forall>t\<in>set ts. is_Var t \<or> is_Const t \<Longrightarrow>
    inj_on (\<lambda>v. (e, map (eval_trm (map the v)) ts)) {v. wf_tuple n (\<Union> (fv_trm ` set ts)) v}"
  apply(intro inj_onI)
      apply(rule nth_equalityI)
       apply(auto simp add: wf_tuple_def)[]
      subgoal for x y i
        apply(cases "i \<in> (\<Union> (fv_trm ` set ts))")
         apply(subgoal_tac " Var i \<in> set ts")
          apply(simp)
        apply(rotate_tac)
          apply(drule(1) bspec)
          apply(simp add: wf_tuple_def)
          apply (meson option.expand)
         apply(auto simp add: is_Var_def is_Const_def)[]
          apply(simp add: wf_tuple_def)
        by metis
      done

lemma finite_listset: "(\<And>A. A \<in> set xs \<Longrightarrow> finite A) \<Longrightarrow> finite (listset xs)"
  by (induct xs) (simp_all add: set_Cons_def finite_image_set2)

fun joinN :: "'a tuple list \<Rightarrow> 'a tuple option" where
"joinN [] = Some []"
|"joinN (a#b#cs) =  (case (join1 (a, b)) of None \<Rightarrow> None| Some x \<Rightarrow> joinN (x#cs))"
|"joinN (a#[]) = Some a"

lemma restrict_restrict: "restrict A (restrict B z) = restrict (A\<inter>B) z"
  by(simp add: restrict_def)

lemma in_listset_conv_list_all2: "xs \<in> listset ys \<longleftrightarrow> list_all2 (\<in>) xs ys"
  by (induct ys arbitrary: xs) (auto simp: set_Cons_def list_all2_Cons2)

lemma nth_restrict': "i<length z \<Longrightarrow> (restrict A z)!i = (if i \<in> A then z!i else None)"
  by(simp add: restrict_def)

lemma joinN_Some_restrict:
  fixes as :: "'a tuple list"
  fixes bs :: "nat set list"
  assumes "list_all2 (wf_tuple n) bs as"
  assumes "as\<noteq>[]"
  shows "joinN (as) = Some z \<longleftrightarrow> wf_tuple n (\<Union> (set bs)) z \<and> list_all2 (\<lambda>b a. restrict b z = a) bs as"
  using assms
proof (induct "as" arbitrary: n bs z rule: joinN.induct)
  case 1
  then show ?case
    by(auto)
next
  case (2 a b cs)
  then show ?case
    apply(simp)
    apply(cases "join1 (a, b)")
     apply(simp_all)
     apply(auto simp add: list_all2_Cons2)[]
    subgoal for A B Cs
      using join1_Some_restrict[of n A a B b "(restrict (A\<union>B) z)"] apply(auto simp add: restrict_restrict intro: wf_tuple_restrict_simple)
      done
    subgoal for c
      apply(erule thin_rl)
      apply(clarsimp simp add: list_all2_Cons2)[]
      subgoal for A B Cs
      using join1_Some_restrict[of n A a B b c] 2(1)[of c n "(A\<union>B)#Cs" z] apply(auto simp add: Un_assoc restrict_restrict intro: wf_tuple_restrict_simple)
      apply(subgoal_tac "restrict (A\<union>B) z = restrict (A\<union>B) c")
       apply(simp add: restrict_idle)
      apply(simp add: list_eq_iff_nth_eq nth_restrict')
      apply(simp split: if_splits)
      by (metis nth_restrict)
    done
    done
next
  case (3 a)
  then show ?case
    apply(auto)
      apply(simp add: wf_tuple_def)
      apply (smt (verit, best) in_set_simps(2) list_all2_Cons2 list_all2_Nil2)
      apply(simp add: wf_tuple_def)
     apply (smt (z3) "3.prems" list_all2_Cons2 list_all2_Nil2 restrict_idle)
    apply(simp add: wf_tuple_def)
    apply(auto)
    by (smt (z3) in_set_simps(2) list.inject list_all2_Cons2 list_all2_Nil2 nth_equalityI nth_restrict)
qed

lemma finite_letpast:
  assumes fv: "{0..<nfv \<phi>} \<subseteq> fv \<phi>"
  assumes V: "\<forall>pn\<in>dom V. \<forall>i. finite {v. length v = snd pn \<and> the (V pn) v i}"
  assumes IH: "\<And>V i.
    \<forall>pn\<in>dom V. \<forall>i. finite {v. length v = snd pn \<and> the (V pn) v i} \<Longrightarrow>
    finite {v. wf_tuple (nfv \<phi>) (fv \<phi>) v \<and> sat \<sigma> V (map the v) i \<phi>}"
  shows "finite {v. length v = nfv \<phi> \<and>
    letpast_sat (\<lambda>X u k. sat \<sigma> (V((p, nfv \<phi>) \<mapsto> X)) u k \<phi>) v i}"
proof (induction i rule: less_induct)
  case (less i)
  note fun_upd_apply[simp del]
  show ?case
    apply (rule finite_surj[where f="map the"])
     apply (rule IH[where i=i and V="(V((p, nfv \<phi>) \<mapsto>
          \<lambda>w j. j < i \<and> letpast_sat (\<lambda>X u k. sat \<sigma> (V((p, nfv \<phi>) \<mapsto> X)) u k \<phi>) w j))"])
     apply (intro ballI)
     apply clarsimp
    subgoal for p' n k
      apply (cases "(p', n) = (p, nfv \<phi>)")
       apply (clarsimp simp add: fun_upd_apply)
       apply (cases "k < i")
        apply simp
        apply (rule less[of k])
        apply simp
       apply clarsimp
      apply (subst fun_upd_apply)
      apply (simp only: if_False)
      apply (rule V[rule_format, of "(p', n)", simplified])
      by auto
    apply (intro subsetI)
    subgoal for v
      apply (rule image_eqI[where x="map Some v"])
       apply simp
      apply (subst (asm) letpast_sat.simps)
      using fv by (auto simp: wf_tuple_def)
    done
qed

lemma safe_regex_Past_finite: "safe_regex Past Strict r \<Longrightarrow>
  (\<And>i \<phi>. \<phi> \<in> atms r \<Longrightarrow> finite {v. wf_tuple n (fv \<phi>) v \<and> test v i \<phi>}) \<Longrightarrow>
  finite {v. wf_tuple n (fv_regex r) v \<and> (\<exists>j\<le>i. Regex.match (test v) r j i)}"
  apply (induct Past Strict r arbitrary: i rule: safe_regex.induct)
      apply (auto simp flip: in_unit_table simp add: unit_table_def
        conj_disj_distribL ex_disj_distrib relcompp_apply Un_absorb2)
  subgoal for r s i
  apply (rule finite_subset[rotated])
     apply (rule finite_UN_I[where B="\<lambda>i. {v. wf_tuple n (fv_regex r) v \<and> (\<exists>j\<le>i. Regex.match (test v) r j i)}"])
      apply (rule finite_atLeastAtMost[of 0 i])
     apply assumption
    apply (auto simp: Bex_def)
    apply (meson match_le)
    done
  done

lemma safe_regex_Future_finite: "safe_regex Futu Strict r \<Longrightarrow>
  (\<And>i \<phi>. \<phi> \<in> atms r \<Longrightarrow> finite {v. wf_tuple n (fv \<phi>) v \<and> test v i \<phi>}) \<Longrightarrow>
  finite {v. wf_tuple n (fv_regex r) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) r i j)}"
  apply (induct Futu Strict r arbitrary: i rule: safe_regex.induct)
      apply (auto simp flip: in_unit_table simp add: unit_table_def Bex_def
        conj_disj_distribL ex_disj_distrib relcompp_apply Un_absorb1 intro: rev_finite_subset)
  subgoal for r s i
  apply (rule finite_subset[rotated])
     apply (rule finite_UN_I[where B="\<lambda>i. {v. wf_tuple n (fv_regex s) v \<and> (\<exists>j\<ge>i. j \<le> thr \<and> Regex.match (test v) s i j)}"])
      apply (rule finite_atLeastAtMost[of i thr])
     apply assumption
    apply (auto simp: Bex_def)
    apply (meson match_le order_trans)
    done
  done

lemma safe_formula_finite: "safe_formula \<phi> \<Longrightarrow> future_bounded \<phi> \<Longrightarrow> n\<ge> (nfv \<phi>) \<Longrightarrow> \<forall> i. finite (\<Gamma> \<sigma> i) \<Longrightarrow>
  \<forall>pn\<in>dom V. \<forall>i. finite {v. length v = snd pn \<and> the (V pn) v i} \<Longrightarrow>
  finite {v. wf_tuple n (fv \<phi>) v \<and> sat \<sigma> V (map the v) i \<phi>}"
proof(induct \<phi> arbitrary: i n V rule: safe_formula_induct)
  case (Eq_Const c d)
  then show ?case
    by(simp flip: in_unit_table add: unit_table_def)
next
  case (Eq_Var1 c x)
  then have "finite (singleton_table n x c)"
    unfolding singleton_table_def by(simp)
  then show ?case using Eq_Var1
    apply(elim finite_subset[rotated])
    apply(auto intro: nth_equalityI simp add: singleton_table_def wf_tuple_def tabulate_alt nfv_def Suc_le_eq)
    done
next
  case (Eq_Var2 c x)
  then have "finite (singleton_table n x c)"
    unfolding singleton_table_def by(simp)
  then show ?case
    apply(simp)
    apply(elim finite_subset[rotated])
    apply(auto intro: nth_equalityI simp add: singleton_table_def wf_tuple_def tabulate_alt nfv_def Suc_le_eq)
    done
next
  case (neq_Var x)
  then show ?case by(simp)
next
case (Pred e ts)
  then show ?case
    apply(simp)
    apply(cases "V (e, length ts)")
     apply(simp)
    subgoal
      apply(rule finite_vimage_IntI[of "\<Gamma> \<sigma> i" "\<lambda> v. (e, map (eval_trm (map the v)) ts)" "{v. wf_tuple n (\<Union> (fv_trm ` set ts)) v}", THEN finite_subset[rotated]])
        apply simp
       apply(auto simp add: inj_eval2)
      done
    apply(simp)
    subgoal for a
      apply(rule finite_vimage_IntI[of "{v. length v = length ts \<and> a v i}" "\<lambda> v. map (eval_trm (map the v)) ts" "{v. wf_tuple n (\<Union> (fv_trm ` set ts)) v}", THEN finite_subset[rotated]])
        apply (drule (1) bspec[OF _ domI])
        apply(auto simp add: inj_eval)
      done
    done
next
  case (Let p \<phi> \<psi>)
  then have IH: " finite {v. wf_tuple n (fv \<psi>) v \<and> sat \<sigma> V (map the v) i \<psi>}"
    apply(simp)
    done
  then have IH2: "\<forall>i.  finite (map the ` {v. wf_tuple (nfv \<phi>) (fv \<phi>) v \<and> sat \<sigma> V (map the v) i \<phi>})" using Let
    by(auto)
  then have "\<forall> i. {v. length v = nfv \<phi> \<and> sat \<sigma> V v i \<phi>} = map the ` {v. wf_tuple (nfv \<phi>) (fv \<phi>) v \<and> sat \<sigma> V (map the v) i \<phi>}"
    using Let
    apply(simp)
    by(auto simp add: wf_tuple_def intro!: image_eqI[where x="map Some _"])
   then have " finite {v. wf_tuple n (fv \<psi>) v \<and> sat \<sigma> (V((p, nfv \<phi>) \<mapsto> \<lambda>w j. sat \<sigma> V w j \<phi>)) (map the v) i \<psi>}"
     using Let IH2
    by(auto)
  then show ?case using Let
    apply(elim finite_subset[rotated])
    by(auto)
next
  case (LetPast p \<phi> \<psi>)
  show ?case
    unfolding sat.simps fvi.simps Let_def
    apply (rule LetPast.hyps(6))
    using LetPast apply auto[3]
    apply (intro ballI allI)
    subgoal for pn i
      apply (cases "pn = (p, nfv \<phi>)")
       apply (simp add: dom_def)
       apply (rule finite_letpast)
      using LetPast apply auto[2]
      apply (rule LetPast.hyps(5))
      using LetPast by auto
    done
next
  case (And_assign \<phi> \<psi>)
  then have IH: " finite {v. wf_tuple n (fv \<phi>) v \<and> sat \<sigma> V (map the v) i \<phi>}"
    apply(simp)
    done
  consider x y where "\<psi> = Eq (Var x) (Var y)" and  "(x \<notin> fv \<phi> \<longleftrightarrow> y \<in> fv \<phi>)"
    |x t where "\<psi> = Eq (Var x) t" and "\<not> is_Var t" and "(x \<notin> fv \<phi> \<and> fv_trm t \<subseteq> fv \<phi>)"
    |x t where "\<psi> = Eq t (Var x)" and "\<not> is_Var t" and "(x \<notin> fv \<phi> \<and> fv_trm t \<subseteq> fv \<phi>)"
    using And_assign(2)
    by(simp add: safe_assignment_def is_Var_def split: formula.splits trm.splits)
      then show ?case proof cases
        case 1
        then show ?thesis
          apply(simp)
          apply(cases "(x \<notin> fv \<phi>)")
           apply(simp add: insert_commute insert_absorb)
          thm finite_surj[OF IH, of _ "\<lambda> v. v [x:=v!y]"]
           apply(rule finite_surj[OF IH, of _ "\<lambda> v. v [x:=v!y]"])
           apply(auto)[]
          subgoal for v
            apply(rule rev_image_eqI[of "v [x:=None]"])
             apply(auto)
              apply(simp add: wf_tuple_def)
              apply (metis nth_list_update nth_list_update_neq)
            apply (smt (verit, best) map_update nth_list_update_neq sat_fv_cong)
            apply(rule sym)
            apply(subst list_update_same_conv)
            using And_assign(5) apply(simp add: wf_tuple_def nfv_def)
            apply(simp add: wf_tuple_def)
            apply(subst nth_list_update_neq)
             apply blast
            using And_assign(5) apply(simp add: wf_tuple_def nfv_def)
            by (metis Suc_le_lessD option.expand nth_map)
          apply(simp add: insert_absorb)
           apply(rule finite_surj[OF IH, of _ "\<lambda> v. v [y:=v!x]"])
           apply(auto)[]
          subgoal for v
            apply(rule rev_image_eqI[of "v [y:=None]"])
             apply(auto)
              apply(simp add: wf_tuple_def)
              apply (metis nth_list_update nth_list_update_neq)
            apply (smt (verit, best) map_update nth_list_update_neq sat_fv_cong)
            apply(rule sym)
            apply(subst list_update_same_conv)
            using And_assign(5) apply(simp add: wf_tuple_def nfv_def)
            apply(simp add: wf_tuple_def)
            apply(subst nth_list_update_neq)
             apply blast
            using And_assign(5) apply(simp add: wf_tuple_def nfv_def)
            by (metis Suc_le_eq nth_map option.expand)
          done
      next
        case 2
        then show ?thesis
          apply(simp add: Un_absorb2)
          apply(rule finite_surj[OF IH, of _ "\<lambda> v. v [x:=Some (eval_trm (map the v) t)]"])
          apply(auto)[]
          subgoal for v
            apply(rule rev_image_eqI[of "v [x:=None]"])
             apply(auto)
              apply(simp add: wf_tuple_def)
              apply (metis nth_list_update_eq nth_list_update_neq)
             apply (smt (verit, best) map_update nth_list_update_neq sat_fv_cong)
            apply(rule sym)
            apply(subst list_update_same_conv)
            using And_assign(5) apply(simp_all add: wf_tuple_def nfv_def)
            apply(subst eval_trm_fv_cong[of _ _ "map the v"] )
             apply (metis in_mono map_update nth_list_update_neq)
            by (metis Suc_le_eq option.collapse)
          done
      next
        case 3
        then show ?thesis
          apply(simp add: Un_absorb2)
          apply(rule finite_surj[OF IH, of _ "\<lambda> v. v [x:=Some (eval_trm (map the v) t)]"])
          apply(auto)[]
          subgoal for v
            apply(rule rev_image_eqI[of "v [x:=None]"])
             apply(auto)
              apply(simp add: wf_tuple_def)
              apply (metis nth_list_update_eq nth_list_update_neq)
             apply (smt (verit, best) map_update nth_list_update_neq sat_fv_cong)
            apply(rule sym)
            apply(subst list_update_same_conv)
            using And_assign(5) apply(simp_all add: wf_tuple_def nfv_def)
            apply(subst eval_trm_fv_cong[of _ _ "map the v"] )
             apply (metis in_mono map_update nth_list_update_neq)
            by (metis Suc_le_eq option.collapse)
          done
      qed
next
  case (And_safe \<phi> \<psi>)
  let ?A = "\<lambda>\<phi>. {v | v. wf_tuple n (fv \<phi>) v \<and> sat \<sigma> V (map the v) i \<phi>}"
  let ?p = "\<lambda>v. (restrict (fv \<phi>) v, restrict (fv \<psi>) v)"
  let ?test = "(?A \<phi> \<times> ?A \<psi>)"
  have "finite (?A \<phi>)" and "finite (?A \<psi>)" using And_safe by auto
  then have "finite (?A \<phi> \<times> ?A \<psi>)" ..
  then have "finite (Option.these (join1 ` (?A \<phi> \<times> ?A \<psi>)))"
    by (auto simp: Option.these_def)
  moreover have "{v. wf_tuple n (fv \<phi> \<union> fv \<psi>) v \<and> sat \<sigma> V (map the v) i \<phi> \<and> sat \<sigma> V (map the v) i \<psi>}
      \<subseteq> Option.these (join1 ` (?A \<phi> \<times> ?A \<psi>))" (is "?B \<subseteq> ?B'")
  proof
    fix v
    assume "v \<in> ?B"
    then have "(restrict (fv \<phi>) v, restrict (fv \<psi>) v) \<in> ?A \<phi> \<times> ?A \<psi>"
      by (auto simp: wf_tuple_restrict_simple sat_the_restrict)
    moreover have "join1 (restrict (fv \<phi>) v, restrict (fv \<psi>) v) = Some v"
      using \<open>v \<in> ?B\<close>
      apply (subst join1_Some_restrict)
      by(auto simp: wf_tuple_restrict_simple)
    ultimately show "v \<in> ?B'"
      apply(simp)
      by (force simp: Option.these_def)
  qed
  ultimately show ?case
    by (auto elim!: finite_subset)
next
  case (And_constraint \<phi> \<psi>)
  then have "finite {v. wf_tuple n (fv \<phi>) v \<and> sat \<sigma> V (map the v) i \<phi>}"
    by(simp)
  then show ?case using And_constraint
    apply(elim finite_subset[rotated])
    apply(auto)
    by (metis sup.order_iff)
next
  case (And_Not \<phi> \<psi>)
  then have "finite {v. wf_tuple n (fv \<phi>) v \<and> sat \<sigma> V (map the v) i \<phi>}"
    by(simp)
  then show ?case using And_Not
    apply(elim finite_subset[rotated])
    by(auto simp add: Un_absorb2)
next
  case (Ands l pos neg)
  let ?A = "\<lambda>\<phi>. {v | v. wf_tuple n (fv \<phi>) v \<and> sat \<sigma> V (map the v) i \<phi>}"
  let ?p = "\<lambda>v. (map (\<lambda> \<phi>.(restrict (fv \<phi>) v)) pos)"
  let ?A_list = "listset (map (\<lambda> \<phi>. ?A \<phi>) pos)"
  have "finite (?A_list)" using Ands
    apply(intro finite_listset)
    by(auto simp add:list_all_def)
  then have "finite (Option.these (joinN ` (?A_list)))"
    by(auto simp: Option.these_def)
  moreover have "{v. wf_tuple n (\<Union> (fv ` set l)) v \<and> (\<forall>x\<in>set l. sat \<sigma> V (map the v) i x)}
      \<subseteq> (Option.these (joinN ` (?A_list)))" (is "?B \<subseteq> ?B'")
  proof
    fix v
    assume "v \<in> ?B"
    then have "?p v \<in> ?A_list"
      using Ands(1)
      by (auto simp: sat_the_restrict in_listset_conv_list_all2 list.rel_map intro!: list.rel_refl_strong wf_tuple_restrict_simple)
    moreover have "joinN (?p v) = Some v"
      using \<open>v \<in> ?B\<close> using Ands(1, 5) Ands.hyps(2)
      thm joinN_Some_restrict[of n "map fv pos" "map (\<lambda>\<phi>. restrict (fv \<phi>) v) pos" v]
      apply(subst joinN_Some_restrict[of n "map fv pos" "map (\<lambda>\<phi>. restrict (fv \<phi>) v) pos" v])
       apply(auto simp: wf_tuple_restrict_simple list.rel_map intro!: list.rel_refl_strong wf_tuple_restrict_simple)
      apply(subgoal_tac "\<Union> (fv ` {x \<in> set l. safe_formula x}) = \<Union> (fv ` set l)")
      by(auto)
    ultimately show "v \<in> ?B'"
      apply(simp)
      by (force simp: Option.these_def)
  qed
   ultimately show ?case
    by (auto elim!: finite_subset)
next
  case (Neg \<phi>)
  then show ?case
   by(simp flip: in_unit_table add: unit_table_def)
next
  case (Or \<phi> \<psi>)
  then have "finite {v. wf_tuple n (fv \<phi>) v \<and> sat \<sigma> V (map the v) i \<phi>}"
    by(simp)
  moreover from Or have "finite {v. wf_tuple n (fv \<psi>) v \<and> sat \<sigma> V (map the v) i \<psi>}"
    by(simp)
  ultimately have "finite ({v. wf_tuple n (fv \<phi>) v \<and> sat \<sigma> V (map the v) i \<phi>} \<union> {v. wf_tuple n (fv \<psi>) v \<and> sat \<sigma> V (map the v) i \<psi>})"
    by(simp)
  then show ?case using Or
    apply(elim finite_subset[rotated])
    by(auto)
next
  case (Exists \<phi>)
 then have "finite (fvi (Suc 0) \<phi>)"
   by(simp)
  moreover from Exists have IH: "finite {v. wf_tuple (Suc n) (fv \<phi>) v \<and> sat \<sigma> V (map the v) i \<phi>}"
    by(simp add: nfv_def fvi_Suc_bound Suc_le_eq)
  ultimately show ?case using Exists
    apply(simp)
    apply(rule finite_surj[OF IH, of _ "tl"])
    apply(auto)
    subgoal for v z
      apply(rule image_eqI[of _ _ "(if 0 \<in> fv \<phi> then Some z else None)#v"])
       apply(auto simp add: wf_tuple_def)
      apply (metis fvi_Suc length_nth_simps(3) length_nth_simps(4) less_Suc_eq_0_disj option.discI)
            apply (metis fvi_Suc length_nth_simps(4) less_Suc_eq_0_disj)
            apply (metis fvi_Suc length_nth_simps(4) less_Suc_eq_0_disj)
       apply (metis fvi_Suc length_nth_simps(3) length_nth_simps(4) less_Suc_eq_0_disj)
      apply(erule sat_fv_cong[THEN iffD1, rotated])
      apply(auto simp add: nth_Cons')
      done
    done
next
  case (Agg y \<omega> b f \<phi>)
  from Agg have IH: "finite {v. wf_tuple (n+b) (fv \<phi>) v \<and> sat \<sigma> V (map the v) i \<phi>}"
    by(auto 0 4 simp add: Suc_le_eq ball_Un nfv_def intro!: Agg(5)[of _ "n+b" V i] dest!: fvi_plus_bound[where b=0 and c=b, simplified])
  then have IH_alt: "finite (drop b`{v. wf_tuple (n+b) (fv \<phi>) v \<and> sat \<sigma> V (map the v) i \<phi>})"
    by(auto)
  have drop_b: "finite (drop b`{v. wf_tuple (n+b) (fv \<phi>) v \<and> fv \<phi> = {0..<b}})"
    apply(rule finite_subset[of _ "{replicate n None}"])
     apply(auto simp add: wf_tuple_def list_eq_iff_nth_eq)
    done
  have final_subset: "finite (drop b`{v. wf_tuple (n+b) (fv \<phi>) v \<and> (sat \<sigma> V (map the v) i \<phi> \<or> fv \<phi> = {0..<b})})"
    using drop_b IH_alt
    apply(auto)
    by (smt (z3) Collect_cong drop_b)
  have sat_eq: "sat \<sigma> V (zs @ map the (x[y := None])) i \<phi> = sat \<sigma> V (zs @ map the (x)) i \<phi>" if "length zs = b" and "y<length x" for x zs
    using Agg(1, 7) that
    apply -
    apply(rule sat_fv_cong)
    apply(simp add: nth_append)
    apply(auto simp add: nfv_def Suc_le_eq)
    by (metis add.commute add_diff_inverse_nat map_update nth_list_update_neq)
  have eval_trm_eq: "eval_trm (zs @ map the (x[y := None])) f =  eval_trm (zs @ map the (x)) f" if "length zs = b" and "y<length x" for x zs
using Agg(1, 7) that
    apply -
    apply(rule eval_trm_fv_cong)
    apply(simp add: nth_append)
  apply(auto simp add: nfv_def Suc_le_eq)
  by (metis Agg.hyps(3) add.commute add_diff_inverse_nat map_update nth_list_update_neq subset_iff)
  then show ?case using Agg IH
    apply(simp)
    apply(rule finite_surj[ of "{v. wf_tuple n (fvi b \<phi> \<union> fvi_trm b f) v \<and>
         ((\<forall>a x. length x = b \<longrightarrow> sat \<sigma> V (x @ map the v) i \<phi> \<longrightarrow> eval_trm (x @ map the v) f \<noteq> a) \<longrightarrow>
          fv \<phi> = {0..<b})}" _ "\<lambda> v. v [y:= (Some (eval_agg_op \<omega>
         {(x, ecard
               {zs.
                length zs = b \<and>
                sat \<sigma> V (zs @ map the v) i \<phi> \<and> eval_trm (zs @ map the v) f = x}) |
          x. \<exists>xa. sat \<sigma> V (xa @ map the v) i \<phi> \<and>
                  length xa = b \<and> eval_trm (xa @ map the v) f = x}))]"])
     defer
     apply(intro subsetI)
     apply(clarify)
    subgoal for x
      apply(frule wf_tuple_length)
    apply(rule image_eqI[where x="x[y:=None]"])
       apply(rule sym)
      apply(simp add: ac_simps sat_eq eval_trm_eq nfv_def Suc_le_eq cong: conj_cong Collect_cong)
     apply(subst list_update_same_conv)
      apply(simp add: nfv_def Suc_le_eq wf_tuple_def)
       apply(simp add: nfv_def Suc_le_eq wf_tuple_def)
       apply (metis option.exhaust_sel)
      apply(auto)
      apply(auto simp add: sat_eq eval_trm_eq wf_tuple_def nth_list_update nfv_def Suc_le_eq  fvi_trm_iff_fv_trm[where b="length _"] fvi_iff_fv[where b="length _"])
       apply (meson Agg.hyps(1) fvi_iff_fv)
      by (metis Agg.hyps(1) fvi_trm_iff_fv_trm subset_iff)
    apply(rule finite_subset[of _ "(drop b`{v. wf_tuple (n+b) (fv \<phi>) v \<and> (sat \<sigma> V (map the v) i \<phi> \<or> fv \<phi> = {0..<b})})"])
     apply(intro subsetI)
    apply(clarify)
    subgoal for x
      apply(erule impCE)
       apply(simp)
       apply(elim exE conjE)
      subgoal for zs
        apply(rule image_eqI[where x="map2 (\<lambda> i z. if i \<in> fv \<phi> then Some z else None) [0..<b] zs @ x"])
         apply(simp)
        apply(intro conjI[rotated] CollectI)
        apply(subgoal_tac "sat \<sigma> V (map the (map2 (\<lambda>x y. if x \<in> fv \<phi> then Some y else None) [0..<b] zs @ x)) i \<phi>")
        apply(simp)
         apply(erule sat_fv_cong[THEN iffD1, rotated])
         apply(simp add: nfv_def nth_append)
         apply(auto simp add: wf_tuple_def nth_append nfv_def)
           apply (metis add_diff_inverse_nat fvi_iff_fv le_add1 le_add_diff_inverse2)
        apply (metis bot_nat_0.not_eq_extremum diff_is_0_eq fvi_iff_fv le_add_diff_inverse2 zero_less_diff)
        subgoal for i
          apply(subgoal_tac "i\<in>fv_trm f")
           apply(auto)[]
          by (metis bot_nat_0.not_eq_extremum diff_is_0_eq fvi_trm_iff_fv_trm le_add_diff_inverse2 zero_less_diff)
        done
      apply(subgoal_tac "wf_tuple n {} x")
      subgoal
        apply(subgoal_tac "x \<in> drop b ` {v. wf_tuple (n + b) (fv \<phi>) v \<and> fv \<phi> = {0..<b}}")
          apply blast
        apply(subgoal_tac "x\<in>{v. wf_tuple n {} v}")
        subgoal
          apply(subgoal_tac "{v. wf_tuple n {} v} \<subseteq> drop b ` {v. wf_tuple (n + b) (fv \<phi>) v}")
           apply(auto )[]
          by (auto simp: in_unit_table[symmetric] unit_table_def image_iff nth_append
    intro!: exI[of _ "replicate b (Some undefined) @ replicate n None"] wf_tuple_def[THEN iffD2])
        apply(auto)
        done
      apply(auto simp add: list_eq_iff_nth_eq wf_tuple_def fvi_iff_fv[of _ b] fvi_trm_iff_fv_trm[of _ b])
      done
      using final_subset apply(auto)
      done
next
  case (Prev I \<phi>)
  then have "finite
            {v. wf_tuple n (fv \<phi>) v \<and> sat \<sigma> V (map the v) (i-1) \<phi>}"
    apply(simp)
    done
  then show ?case
    apply(simp)
    apply(cases "i")
     apply(simp)
    apply(simp)
    apply(elim finite_subset[rotated])
    by(auto)
next
  case (Next I \<phi>)
  then have "finite
     {v. wf_tuple n (fv \<phi>) v \<and> sat \<sigma> V (map the v) (Suc i) \<phi>}"
    apply(simp)
    done
  then show ?case using Next
    apply(elim finite_subset[rotated])
    by(auto)
next
  case (Since \<phi> I \<psi>)
  then have "\<forall> j. finite {v. wf_tuple n (fv \<psi>) v \<and> sat \<sigma> V (map the v) j \<psi>}"
    by(simp)
  then have "finite (\<Union> j\<le>i. {v. wf_tuple n (fv \<psi>) v \<and> sat \<sigma> V (map the v) j \<psi>})"
    by(auto)
  then show ?case using Since
    apply(elim finite_subset[rotated])
    by(auto simp add: Un_absorb1)
next
  case (Not_Since \<phi> I \<psi>)
  then have "\<forall> j. finite {v. wf_tuple n (fv \<psi>) v \<and> sat \<sigma> V (map the v) j \<psi>}"
    by(simp)
  then have "finite (\<Union> j\<le>i. {v. wf_tuple n (fv \<psi>) v \<and> sat \<sigma> V (map the v) j \<psi>})"
    by(auto)
  then show ?case using Not_Since
    apply(elim finite_subset[rotated])
    by(auto simp add: Un_absorb1)
next
  case (Until \<phi> I \<psi>)
  then obtain m j where m: "\<not> memR I m" and "m = (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    apply(auto)
    apply(atomize_elim)
    apply(simp add: bounded_memR)
    by (metis (no_types, opaque_lifting) add_diff_cancel_right' diff_le_mono ex_le_\<tau> memR_antimono)
  moreover from Until have "\<forall> j. finite {v. wf_tuple n (fv \<psi>) v \<and> sat \<sigma> V (map the v) j \<psi>}"
    by(simp)
  moreover from Until have "finite (\<Union> j'\<le>j. {v. wf_tuple n (fv \<psi>) v \<and> sat \<sigma> V (map the v) j' \<psi>})"
    by(auto)
  ultimately show ?case using Until
    apply(elim finite_subset[rotated])
    apply(simp add: Un_absorb1)
    apply(auto)
    subgoal for v j2
      apply(cases "(\<tau> \<sigma> j2 - \<tau> \<sigma> i)\<le>m")
      subgoal
        apply(auto)
        apply(subgoal_tac "j2\<le>j")
         apply blast
        by (metis \<tau>_mono diff_le_mono le_antisym nat_le_linear)
      subgoal
        apply(subgoal_tac "\<not> memR I (\<tau> \<sigma> j2 - \<tau> \<sigma> i)")
         apply blast
        apply(auto)
        by (meson memR_antimono nat_le_linear)
      done
    done
next
  case (Not_Until \<phi> I \<psi>)
  then obtain m j where m: "\<not> memR I m" and "m = (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    apply(auto)
    apply(atomize_elim)
    apply(simp add: bounded_memR)
    by (metis (no_types, opaque_lifting) add_diff_cancel_right' diff_le_mono ex_le_\<tau> memR_antimono)
  moreover from Not_Until have "\<forall> j. finite {v. wf_tuple n (fv \<psi>) v \<and> sat \<sigma> V (map the v) j \<psi>}"
    by(simp)
  moreover from Not_Until have "finite (\<Union> j'\<le>j. {v. wf_tuple n (fv \<psi>) v \<and> sat \<sigma> V (map the v) j' \<psi>})"
    by(auto)
  ultimately show ?case using Not_Until
    apply(elim finite_subset[rotated])
    apply(simp add: Un_absorb1)
    apply(auto)
    subgoal for v j2
      apply(cases "(\<tau> \<sigma> j2 - \<tau> \<sigma> i)\<le>m")
      subgoal
        apply(auto)
        apply(subgoal_tac "j2\<le>j")
         apply blast
        by (metis \<tau>_mono diff_le_mono le_antisym nat_le_linear)
      subgoal
        apply(subgoal_tac "\<not> memR I (\<tau> \<sigma> j2 - \<tau> \<sigma> i)")
         apply blast
        apply(auto)
        by (meson memR_antimono nat_le_linear)
      done
    done
next
  case (MatchP I r)
  from MatchP(1,3-) have IH: "finite {v. wf_tuple n (fv \<phi>) v \<and> sat \<sigma> V (map the v) k \<phi>}"
    if "\<phi> \<in> atms r" for k \<phi> using that
    apply (intro MatchP(2)[rule_format, OF that])
       apply (auto simp: regex.pred_set atms_def Regex.nfv_regex_def fv_regex_alt nfv_def)
     apply (auto split: formula.splits)
    done
  from MatchP(3-) show ?case
    by (intro finite_subset[OF _ safe_regex_Past_finite[OF MatchP(1) IH, of i]]) auto
next
  case (MatchF I r)
  then obtain m j where m: "\<not> memR I m" "m = (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    apply(auto)
    apply(atomize_elim)
    apply(simp add: bounded_memR)
    by (metis (no_types, opaque_lifting) add_diff_cancel_right' diff_le_mono ex_le_\<tau> memR_antimono)
  from MatchF(1,3-) have IH: "finite {v. wf_tuple n (fv \<phi>) v \<and> sat \<sigma> V (map the v) k \<phi>}"
    if "\<phi> \<in> atms r" for k \<phi> using that
    apply (intro MatchF(2)[rule_format, OF that])
       apply (auto simp: regex.pred_set atms_def Regex.nfv_regex_def fv_regex_alt nfv_def)
     apply (auto split: formula.splits)
    done
  from MatchF(3-) m show ?case
    apply (intro finite_subset[OF _ safe_regex_Future_finite[OF MatchF(1) IH, of i j]])
     apply clarsimp
     apply (erule bexI[where A = "{i .. j}"])
     apply auto
    apply (meson \<tau>_mono diff_le_mono le_cases memR_antimono)
    done
qed

end (*context*)

interpretation Formula_slicer: abstract_slicer "relevant_events \<phi>" for \<phi> .

lemma sat_slice_iff:
  assumes "v \<in> S"
  shows "Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> Formula.sat (Formula_slicer.slice \<phi> S \<sigma>) V v i \<phi>"
  by (rule sat_slice_strong[OF assms]) auto

lemma Neg_splits:
  "P (case \<phi> of formula.Neg \<psi> \<Rightarrow> f \<psi> | \<phi> \<Rightarrow> g \<phi>) =
   ((\<forall>\<psi>. \<phi> = formula.Neg \<psi> \<longrightarrow> P (f \<psi>)) \<and> ((\<not> Formula.is_Neg \<phi>) \<longrightarrow> P (g \<phi>)))"
  "P (case \<phi> of formula.Neg \<psi> \<Rightarrow> f \<psi> | _ \<Rightarrow> g \<phi>) =
   (\<not> ((\<exists>\<psi>. \<phi> = formula.Neg \<psi> \<and> \<not> P (f \<psi>)) \<or> ((\<not> Formula.is_Neg \<phi>) \<and> \<not> P (g \<phi>))))"
  by (cases \<phi>; auto simp: Formula.is_Neg_def)+

(*<*)
end
(*>*)
