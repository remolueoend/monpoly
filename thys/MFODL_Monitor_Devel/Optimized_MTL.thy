(*<*)
theory Optimized_MTL
  imports Monitor Wf_Table
begin
(*>*)

section \<open>Efficient implementation of temporal operators\<close>

subsection \<open>Optimized queue data structure\<close>

lemma less_enat_iff: "a < enat i \<longleftrightarrow> (\<exists>j. a = enat j \<and> j < i)"
  by (cases a) auto

type_synonym 'a queue_t = "'a list \<times> 'a list"

definition queue_invariant :: "'a queue_t \<Rightarrow> bool" where
  "queue_invariant q = (case q of ([], []) \<Rightarrow> True | (fs, l # ls) \<Rightarrow> True | _ \<Rightarrow> False)"

typedef 'a queue = "{q :: 'a queue_t. queue_invariant q}"
  by (auto simp: queue_invariant_def split: list.splits)

setup_lifting type_definition_queue

lift_definition linearize :: "'a queue \<Rightarrow> 'a list" is "(\<lambda>q. case q of (fs, ls) \<Rightarrow> fs @ rev ls)" .

lift_definition empty_queue :: "'a queue" is "([], [])"
  by (auto simp: queue_invariant_def split: list.splits)

lemma empty_queue_rep: "linearize empty_queue = []"
  by transfer (simp add: empty_queue_def linearize_def)

lift_definition is_empty :: "'a queue \<Rightarrow> bool" is "\<lambda>q. (case q of ([], []) \<Rightarrow> True | _ \<Rightarrow> False)" .

lemma linearize_t_Nil: "(case q of (fs, ls) \<Rightarrow> fs @ rev ls) = [] \<longleftrightarrow> q = ([], [])"
  by (auto split: prod.splits)

lemma is_empty_alt: "is_empty q \<longleftrightarrow> linearize q = []"
  by transfer (auto simp: linearize_t_Nil list.case_eq_if)

fun prepend_queue_t :: "'a \<Rightarrow> 'a queue_t \<Rightarrow> 'a queue_t" where
  "prepend_queue_t a ([], []) = ([], [a])"
| "prepend_queue_t a (fs, l # ls) = (a # fs, l # ls)"
| "prepend_queue_t a (f # fs, []) = undefined"

lift_definition prepend_queue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" is prepend_queue_t
  by (auto simp: queue_invariant_def split: list.splits elim: prepend_queue_t.elims)

lemma prepend_queue_rep: "linearize (prepend_queue a q) = a # linearize q"
  by transfer
    (auto simp add: queue_invariant_def linearize_def elim: prepend_queue_t.elims split: prod.splits)

lift_definition append_queue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" is
  "(\<lambda>a q. case q of (fs, ls) \<Rightarrow> (fs, a # ls))"
  by (auto simp: queue_invariant_def split: list.splits)

lemma append_queue_rep: "linearize (append_queue a q) = linearize q @ [a]"
  by transfer (auto simp add: linearize_def split: prod.splits)

fun safe_last_t :: "'a queue_t \<Rightarrow> 'a option \<times> 'a queue_t" where
  "safe_last_t ([], []) = (None, ([], []))"
| "safe_last_t (fs, l # ls) = (Some l, (fs, l # ls))"
| "safe_last_t (f # fs, []) = undefined"

lift_definition safe_last :: "'a queue \<Rightarrow> 'a option \<times> 'a queue" is safe_last_t
  by (auto simp: queue_invariant_def split: prod.splits list.splits)

lemma safe_last_rep: "safe_last q = (\<alpha>, q') \<Longrightarrow> linearize q = linearize q' \<and>
  (case \<alpha> of None \<Rightarrow> linearize q = [] | Some a \<Rightarrow> linearize q \<noteq> [] \<and> a = last (linearize q))"
  by transfer (auto simp: queue_invariant_def split: list.splits elim: safe_last_t.elims)

fun safe_hd_t :: "'a queue_t \<Rightarrow> 'a option \<times> 'a queue_t" where
  "safe_hd_t ([], []) = (None, ([], []))"
| "safe_hd_t ([], [l]) = (Some l, ([], [l]))"
| "safe_hd_t ([], l # ls) = (let fs = rev ls in (Some (hd fs), (fs, [l])))"
| "safe_hd_t (f # fs, l # ls) = (Some f, (f # fs, l # ls))"
| "safe_hd_t (f # fs, []) = undefined"

lift_definition(code_dt) safe_hd :: "'a queue \<Rightarrow> 'a option \<times> 'a queue" is safe_hd_t
proof -
  fix q :: "'a queue_t"
  assume "queue_invariant q"
  then show "pred_prod \<top> queue_invariant (safe_hd_t q)"
    by (cases q rule: safe_hd_t.cases) (auto simp: queue_invariant_def Let_def split: list.split)
qed

lemma safe_hd_rep: "safe_hd q = (\<alpha>, q') \<Longrightarrow> linearize q = linearize q' \<and>
  (case \<alpha> of None \<Rightarrow> linearize q = [] | Some a \<Rightarrow> linearize q \<noteq> [] \<and> a = hd (linearize q))"
  by transfer
    (auto simp add: queue_invariant_def Let_def hd_append split: list.splits elim: safe_hd_t.elims)

fun replace_hd_t :: "'a \<Rightarrow> 'a queue_t \<Rightarrow> 'a queue_t" where
  "replace_hd_t a ([], []) = ([], [])"
| "replace_hd_t a ([], [l]) = ([], [a])"
| "replace_hd_t a ([], l # ls) = (let fs = rev ls in (a # tl fs, [l]))"
| "replace_hd_t a (f # fs, l # ls) = (a # fs, l # ls)"
| "replace_hd_t a (f # fs, []) = undefined"

lift_definition replace_hd :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" is replace_hd_t
  by (auto simp: queue_invariant_def split: list.splits elim: replace_hd_t.elims)

lemma tl_append: "xs \<noteq> [] \<Longrightarrow> tl xs @ ys = tl (xs @ ys)"
  by simp

lemma replace_hd_rep: "linearize q = f # fs \<Longrightarrow> linearize (replace_hd a q) = a # fs"
proof (transfer fixing: f fs a)
  fix q
  assume "queue_invariant q" and "(case q of (fs, ls) \<Rightarrow> fs @ rev ls) = f # fs"
  then show "(case replace_hd_t a q of (fs, ls) \<Rightarrow> fs @ rev ls) = a # fs"
    by (cases "(a, q)" rule: replace_hd_t.cases) (auto simp: queue_invariant_def tl_append)
qed

fun replace_last_t :: "'a \<Rightarrow> 'a queue_t \<Rightarrow> 'a queue_t" where
  "replace_last_t a ([], []) = ([], [])"
| "replace_last_t a (fs, l # ls) = (fs, a # ls)"
| "replace_last_t a (fs, []) = undefined"

lift_definition replace_last :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" is replace_last_t
  by (auto simp: queue_invariant_def split: list.splits elim: replace_last_t.elims)

lemma replace_last_rep: "linearize q = fs @ [f] \<Longrightarrow> linearize (replace_last a q) = fs @ [a]"
  by transfer (auto simp: queue_invariant_def split: list.splits prod.splits elim!: replace_last_t.elims)

fun tl_queue_t :: "'a queue_t \<Rightarrow> 'a queue_t" where
  "tl_queue_t ([], []) = ([], [])"
| "tl_queue_t ([], [l]) = ([], [])"
| "tl_queue_t ([], l # ls) = (tl (rev ls), [l])"
| "tl_queue_t (a # as, fs) = (as, fs)"

lift_definition tl_queue :: "'a queue \<Rightarrow> 'a queue" is tl_queue_t
  by (auto simp: queue_invariant_def split: list.splits elim!: tl_queue_t.elims)

lemma tl_queue_rep: "linearize (tl_queue q) = tl (linearize q)"
  by transfer (auto simp: tl_append split: prod.splits list.splits elim!: tl_queue_t.elims)

lemma length_tl_queue_rep: "\<not>is_empty q \<Longrightarrow>
  length (linearize (tl_queue q)) < length (linearize q)"
  by transfer (auto split: prod.splits list.splits elim: tl_queue_t.elims)

lemma length_tl_queue_safe_hd:
  assumes "safe_hd q = (Some a, q')"
  shows "length (linearize (tl_queue q')) < length (linearize q)"
  using safe_hd_rep[OF assms]
  by (auto simp add: length_tl_queue_rep is_empty_alt)

function dropWhile_queue :: "('a \<Rightarrow> bool) \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "dropWhile_queue f q = (case safe_hd q of (None, q') \<Rightarrow> q'
  | (Some a, q') \<Rightarrow> if f a then dropWhile_queue f (tl_queue q') else q')"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(f, q). length (linearize q))") (fastforce split: prod.splits)+

lemma dropWhile_hd_tl: "xs \<noteq> [] \<Longrightarrow>
  dropWhile P xs = (if P (hd xs) then dropWhile P (tl xs) else xs)"
  by (cases xs) auto

lemma dropWhile_queue_rep: "linearize (dropWhile_queue f q) = dropWhile f (linearize q)"
  by (induction f q rule: dropWhile_queue.induct)
     (auto simp add: tl_queue_rep dropWhile_hd_tl is_empty_alt
      split: prod.splits option.splits dest: safe_hd_rep)

function takeWhile_queue :: "('a \<Rightarrow> bool) \<Rightarrow> 'a queue \<Rightarrow> ('a queue \<times> 'a queue)" where
  "takeWhile_queue f q = (case safe_hd q of (None, q') \<Rightarrow> (q', q')
  | (Some a, q') \<Rightarrow> if f a
    then let (q'', rem) = takeWhile_queue f (tl_queue q') in (prepend_queue a q'', q')
    else (empty_queue, q'))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(f, q). length (linearize q))") (fastforce split: prod.splits)+

lemma takeWhile_hd_tl: "xs \<noteq> [] \<Longrightarrow>
  takeWhile P xs = (if P (hd xs) then hd xs # takeWhile P (tl xs) else [])"
  by (cases xs) auto

lemma takeWhile_queue_rep_fst: "linearize (fst (takeWhile_queue f q)) = takeWhile f (linearize q)"
proof(induction f q rule: takeWhile_queue.induct)
  case (1 f q)
  then obtain hd rm where safe_hd_eq: "safe_hd q = (hd, rm)" by (meson prod.exhaust_sel)
  then show ?case 
  proof(cases "hd")
    case None
    then show ?thesis using safe_hd_eq by(auto dest: safe_hd_rep)
  next
    case (Some a)
    then show ?thesis 
    proof(cases "f a")
      case True
      then show ?thesis using safe_hd_eq Some 1[OF safe_hd_eq[symmetric] Some True] 
        by(auto simp add: prepend_queue_rep tl_queue_rep  takeWhile_hd_tl is_empty_alt split: prod.splits dest: safe_hd_rep)
    next
      case False
      then show ?thesis using safe_hd_eq Some by(auto simp add: empty_queue_rep takeWhile_hd_tl  dest: safe_hd_rep) 
    qed
  qed
qed

lemma takeWhile_queue_rep_snd: "linearize (snd (takeWhile_queue f q)) = linearize q"
proof(induction f q rule: takeWhile_queue.induct)
  case (1 f q)
  then obtain hd rm where safe_hd_eq: "safe_hd q = (hd, rm)" by (meson prod.exhaust_sel)
  then show ?case 
  proof(cases "hd")
    case None
    then show ?thesis using safe_hd_eq by (simp add: safe_hd_rep)
  next
    case (Some a)
    then show ?thesis
    proof(cases "f a")
      case True
      then show ?thesis apply(auto) using 1[OF safe_hd_eq[symmetric] Some True] safe_hd_eq Some
        by(auto simp: safe_hd_rep split:prod.splits)
    next
      case False
      then show ?thesis using safe_hd_eq Some by (simp add: safe_hd_rep)
    qed
  qed
qed

function takedropWhile_queue :: "('a \<Rightarrow> bool) \<Rightarrow> 'a queue \<Rightarrow> 'a queue \<times> 'a list" where
  "takedropWhile_queue f q = (case safe_hd q of (None, q') \<Rightarrow> (q', [])
  | (Some a, q') \<Rightarrow> if f a
    then (case takedropWhile_queue f (tl_queue q') of (q'', as) \<Rightarrow> (q'', a # as))
    else (q', []))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(f, q). length (linearize q))") (fastforce split: prod.splits)+

lemma takedropWhile_queue_fst: "fst (takedropWhile_queue f q) = dropWhile_queue f q"
proof (induction f q rule: takedropWhile_queue.induct)
  case (1 f q)
  then show ?case
    by (simp split: prod.splits) (auto simp add: case_prod_unfold split: option.splits)
qed

lemma takedropWhile_queue_snd: "snd (takedropWhile_queue f q) = takeWhile f (linearize q)"
proof (induction f q rule: takedropWhile_queue.induct)
  case (1 f q)
  then show ?case
    by (simp split: prod.splits)
      (auto simp add: case_prod_unfold tl_queue_rep takeWhile_hd_tl is_empty_alt
        split: option.splits dest: safe_hd_rep)
qed

lemma not_empty_head_q:
  assumes "\<not>is_empty q"
  shows "\<exists>ts tss. safe_hd q = (Some ts, tss)"
  using assms apply(transfer) apply(auto) 
proof -
  fix xs ys
  assume "queue_invariant ((xs :: 'a list), ys)" "\<not> (case xs of [] \<Rightarrow> (case ys of [] \<Rightarrow> True | a # list \<Rightarrow> False) | aa # list \<Rightarrow> False)"
  then obtain y ys' where "ys = y#ys'" unfolding queue_invariant_def by(auto split:list.splits)
  then show "\<exists>ts aa ba. queue_invariant (aa, ba) \<and> safe_hd_t (xs, ys) = (Some ts, aa, ba) " 
    by(cases xs; cases ys') (auto simp:queue_invariant_def Let_def list.case_eq_if) 
qed

fun pop_t :: "'a queue_t \<Rightarrow> 'a option \<times> 'a queue_t" where
  "pop_t ([], []) = (None, ([], []))"
| "pop_t ([], [y]) = (Some y, ([], []))"
| "pop_t ([], y # ys) = (case rev ys of z # ys' \<Rightarrow> (Some z, (ys', [y])))"
| "pop_t (x # xs, ys) = (Some x, (xs, ys))"

lift_definition (code_dt) pop :: "'a queue \<Rightarrow> 'a option \<times> 'a queue" is pop_t
proof -
  fix q :: "'a queue_t"
  assume "queue_invariant q"
  then show "pred_prod top queue_invariant (pop_t q)"
    by (induction q rule: pop_t.induct)
      (simp_all add: queue_invariant_def split: list.split)
qed

lemma pop_rep: "pop q = (x, q') \<Longrightarrow> (case x of
    None \<Rightarrow> linearize q = [] \<and> q' = q
  | Some y \<Rightarrow> linearize q = y # linearize q')"
  by transfer (auto split: list.splits elim!: pop_t.elims)


subsection \<open>Optimized data structure for Since\<close>

type_synonym 'a mmsaux = "ts \<times> ts \<times> bool list \<times> bool list \<times>
  (ts \<times> 'a table) queue \<times> (ts \<times> 'a table) queue \<times>
  'a table \<times> 'a wf_table \<times> (('a tuple, ts) mapping) \<times> 'a wf_table \<times> (('a tuple, ts) mapping)"

fun time_mmsaux :: "'a mmsaux \<Rightarrow> ts" where
  "time_mmsaux aux = (case aux of (nt, _) \<Rightarrow> nt)"

definition ts_tuple_rel :: "(ts \<times> 'a table) set \<Rightarrow> (ts \<times> 'a tuple) set" where
  "ts_tuple_rel ys = {(t, as). \<exists>X. as \<in> X \<and> (t, X) \<in> ys}"

lemma finite_fst_ts_tuple_rel: "finite (fst ` {tas \<in> ts_tuple_rel (set xs). P tas})"
proof -
  have "fst ` {tas \<in> ts_tuple_rel (set xs). P tas} \<subseteq> fst ` ts_tuple_rel (set xs)"
    by auto
  moreover have "\<dots> \<subseteq> set (map fst xs)"
    by (force simp add: ts_tuple_rel_def)
  finally show ?thesis
    using finite_subset by blast
qed

lemma ts_tuple_rel_ext_Cons: "tas \<in> ts_tuple_rel {(nt, X)} \<Longrightarrow>
  tas \<in> ts_tuple_rel (set ((nt, X) # tass))"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_ext_Cons': "tas \<in> ts_tuple_rel (set tass) \<Longrightarrow>
  tas \<in> ts_tuple_rel (set ((nt, X) # tass))"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_intro: "as \<in> X \<Longrightarrow> (t, X) \<in> ys \<Longrightarrow> (t, as) \<in> ts_tuple_rel ys"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_dest: "(t, as) \<in> ts_tuple_rel ys \<Longrightarrow> \<exists>X. (t, X) \<in> ys \<and> as \<in> X"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_Un: "ts_tuple_rel (ys \<union> zs) = ts_tuple_rel ys \<union> ts_tuple_rel zs"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_ext: "tas \<in> ts_tuple_rel {(nt, X)} \<Longrightarrow>
  tas \<in> ts_tuple_rel (set ((nt, Y \<union> X) # tass))"
proof -
  assume assm: "tas \<in> ts_tuple_rel {(nt, X)}"
  then obtain as where tas_def: "tas = (nt, as)" "as \<in> X"
    by (cases tas) (auto simp add: ts_tuple_rel_def)
  then have "as \<in> Y \<union> X"
    by auto
  then show "tas \<in> ts_tuple_rel (set ((nt, Y \<union> X) # tass))"
    unfolding tas_def(1)
    by (rule ts_tuple_rel_intro) auto
qed

lemma ts_tuple_rel_ext': "tas \<in> ts_tuple_rel (set ((nt, X) # tass)) \<Longrightarrow>
  tas \<in> ts_tuple_rel (set ((nt, X \<union> Y) # tass))"
proof -
  assume assm: "tas \<in> ts_tuple_rel (set ((nt, X) # tass))"
  then have "tas \<in> ts_tuple_rel {(nt, X)} \<union> ts_tuple_rel (set tass)"
    using ts_tuple_rel_Un by force
  then show "tas \<in> ts_tuple_rel (set ((nt, X \<union> Y) # tass))"
  proof
    assume "tas \<in> ts_tuple_rel {(nt, X)}"
    then show ?thesis
      by (auto simp: Un_commute dest!: ts_tuple_rel_ext)
  next
    assume "tas \<in> ts_tuple_rel (set tass)"
    then have "tas \<in> ts_tuple_rel (set ((nt, X \<union> Y) # tass))"
      by (rule ts_tuple_rel_ext_Cons')
    then show ?thesis by simp
  qed
qed

lemma ts_tuple_rel_mono: "ys \<subseteq> zs \<Longrightarrow> ts_tuple_rel ys \<subseteq> ts_tuple_rel zs"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_filter: "ts_tuple_rel (set (filter (\<lambda>(t, X). P t) xs)) =
  {(t, X) \<in> ts_tuple_rel (set xs). P t}"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_set_filter: "x \<in> ts_tuple_rel (set (filter P xs)) \<Longrightarrow>
  x \<in> ts_tuple_rel (set xs)"
  by (auto simp add: ts_tuple_rel_def)

definition valid_tuple :: "(('a tuple, ts) mapping) \<Rightarrow> (ts \<times> 'a tuple) \<Rightarrow> bool" where
  "valid_tuple tuple_since = (\<lambda>(t, as). case Mapping.lookup tuple_since as of None \<Rightarrow> False
  | Some t' \<Rightarrow> t \<ge> t')"

definition safe_max :: "'a :: linorder set \<Rightarrow> 'a option" where
  "safe_max X = (if X = {} then None else Some (Max X))"

lemma safe_max_empty: "safe_max X = None \<longleftrightarrow> X = {}"
  by (simp add: safe_max_def)

lemma safe_max_empty_dest: "safe_max X = None \<Longrightarrow> X = {}"
  by (simp add: safe_max_def split: if_splits)

lemma safe_max_Some_intro: "x \<in> X \<Longrightarrow> \<exists>y. safe_max X = Some y"
  using safe_max_empty by auto

lemma safe_max_Some_dest_in: "finite X \<Longrightarrow> safe_max X = Some x \<Longrightarrow> x \<in> X"
  using Max_in by (auto simp add: safe_max_def split: if_splits)

lemma safe_max_Some_dest_le: "finite X \<Longrightarrow> safe_max X = Some x \<Longrightarrow> y \<in> X \<Longrightarrow> y \<le> x"
  using Max_ge by (auto simp add: safe_max_def split: if_splits)

fun valid_mmsaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a Monitor.msaux \<Rightarrow> bool" where
  "valid_mmsaux args cur (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) ys \<longleftrightarrow>
    (args_L args) \<subseteq> (args_R args) \<and>
    maskL = join_mask (args_n args) (args_L args) \<and>
    maskR = join_mask (args_n args) (args_R args) \<and>
    (\<forall>(t, X) \<in> set ys. table (args_n args) (args_R args) X) \<and>
    table (args_n args) (args_R args) (Mapping.keys tuple_in) \<and>
    table (args_n args) (args_R args) (Mapping.keys tuple_since) \<and>
    (\<forall>as \<in> \<Union>(snd ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as) \<and>
    (\<forall>as \<in> \<Union>(snd ` (set (linearize data_in))). wf_tuple (args_n args) (args_R args) as) \<and>
    cur = nt \<and>
    ts_tuple_rel (set ys) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since tas} \<and>
    sorted (map fst (linearize data_prev)) \<and>
    (\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt \<and> \<not> memL (args_ivl args) (nt - t)) \<and>
    sorted (map fst (linearize data_in)) \<and>
    (\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt \<and> memL (args_ivl args) (nt - t)) \<and>
    table_in = Mapping.keys tuple_in \<and>
    wf_table_sig wf_table_in = (args_n args, args_R args) \<and>
    wf_table_set wf_table_in = Mapping.keys tuple_in \<and>
    wf_table_sig wf_table_since = (args_n args, args_R args) \<and>
    wf_table_set wf_table_since = Mapping.keys tuple_since \<and>
    (\<forall>as. Mapping.lookup tuple_in as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since tas \<and> as = snd tas})) \<and>
    (\<forall>as \<in> Mapping.keys tuple_since. case Mapping.lookup tuple_since as of Some t \<Rightarrow> t \<le> nt)"

lemma Mapping_lookup_filter_keys: "k \<in> Mapping.keys (Mapping.filter f m) \<Longrightarrow>
  Mapping.lookup (Mapping.filter f m) k = Mapping.lookup m k"
  by (metis default_def insert_subset keys_default keys_filter lookup_default lookup_default_filter)

lemma Mapping_filter_keys: "(\<forall>k \<in> Mapping.keys m. P (Mapping.lookup m k)) \<Longrightarrow>
  (\<forall>k \<in> Mapping.keys (Mapping.filter f m). P (Mapping.lookup (Mapping.filter f m) k))"
  using Mapping_lookup_filter_keys Mapping.keys_filter by fastforce

lemma Mapping_filter_keys_le: "(\<And>x. P x \<Longrightarrow> P' x) \<Longrightarrow>
  (\<forall>k \<in> Mapping.keys m. P (Mapping.lookup m k)) \<Longrightarrow> (\<forall>k \<in> Mapping.keys m. P' (Mapping.lookup m k))"
  by auto

lemma Mapping_keys_dest: "x \<in> Mapping.keys f \<Longrightarrow> \<exists>y. Mapping.lookup f x = Some y"
  by (simp add: domD keys_dom_lookup)

lemma Mapping_keys_intro: "Mapping.lookup f x \<noteq> None \<Longrightarrow> x \<in> Mapping.keys f"
  by (simp add: domIff keys_dom_lookup)

lemma valid_mmsaux_tuple_in_keys: "valid_mmsaux args cur
  (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) ys \<Longrightarrow>
  Mapping.keys tuple_in = snd ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
  valid_tuple tuple_since tas}"
  by (auto intro!: Mapping_keys_intro safe_max_Some_intro
      dest!: Mapping_keys_dest safe_max_Some_dest_in[OF finite_fst_ts_tuple_rel])+

definition wf_table_of_set_args :: "args \<Rightarrow> 'a table \<Rightarrow> 'a wf_table" where
  "wf_table_of_set_args args X = wf_table_of_idx (wf_idx_of_set (args_n args) (args_R args) (args_L args) X)"

lemma wf_table_sig_args: "wf_table_sig (wf_table_of_set_args args X) = (args_n args, args_R args)"
  by (auto simp: wf_table_of_set_args_def wf_idx_sig_of_set)

lemma wf_table_of_set_args: "table (args_n args) (args_R args) X \<Longrightarrow>
  wf_table_set (wf_table_of_set_args args X) = X"
  by (auto simp: wf_table_of_set_args_def wf_idx_set_of_set table_def)

lemma wf_table_of_set_args_wf_table_set: "wf_table_sig t = (args_n args, args_R args) \<Longrightarrow>
  wf_table_of_set_args args (wf_table_set t) = t"
  by (auto simp: wf_table_sig_args wf_table_of_set_args[OF wf_table_set_table] intro: wf_table_eqI)

fun init_mmsaux :: "args \<Rightarrow> 'a mmsaux" where
  "init_mmsaux args = (0, 0, join_mask (args_n args) (args_L args),
  join_mask (args_n args) (args_R args), empty_queue, empty_queue,
  {}, wf_table_of_idx (wf_idx_of_set (args_n args) (args_R args) (args_L args) {}), Mapping.empty,
  wf_table_of_set_args args {}, Mapping.empty)"

lemma valid_init_mmsaux: "L \<subseteq> R \<Longrightarrow> valid_mmsaux (init_args I n L R b agg) 0
  (init_mmsaux (init_args I n L R b agg)) []"
  by (auto simp add: init_args_def empty_queue_rep ts_tuple_rel_def join_mask_def
      safe_max_def table_def wf_table_of_set_args_def wf_idx_sig_of_set wf_idx_set_of_set)

abbreviation "filter_cond X' ts t' \<equiv> (\<lambda>as _. \<not> (as \<in> X' \<and> Mapping.lookup ts as = Some t'))"

lemma dropWhile_filter:
  "sorted (map fst xs) \<Longrightarrow> \<forall>t \<in> fst ` set xs. t \<le> nt \<Longrightarrow>
  dropWhile (\<lambda>(t, X). \<not> memR I (nt - t)) xs = filter (\<lambda>(t, X). memR I (nt - t)) xs"
  by (induction xs) (auto 0 3 intro!: filter_id_conv[THEN iffD2, symmetric])

lemma dropWhile_filter':
  fixes nt :: nat
  shows "sorted (map fst xs) \<Longrightarrow> \<forall>t \<in> fst ` set xs. t \<le> nt \<Longrightarrow>
  dropWhile (\<lambda>(t, X). memL I (nt - t)) xs = filter (\<lambda>(t, X). \<not> memL I (nt - t)) xs"
  by (induction xs) (auto 0 3 simp: memL_mono diff_le_mono intro!: filter_id_conv[THEN iffD2, symmetric])

lemma takeWhile_filter:
  "sorted (map fst xs) \<Longrightarrow> \<forall>t \<in> fst ` set xs. t \<le> nt \<Longrightarrow>
  takeWhile (\<lambda>(t, X). \<not> memR I (nt - t)) xs = filter (\<lambda>(t, X). \<not> memR I (nt - t)) xs"
  by (induction xs) (auto 0 3 simp: memR_antimono intro!: filter_empty_conv[THEN iffD2, symmetric])

lemma takeWhile_filter':
  fixes nt :: nat
  shows "sorted (map fst xs) \<Longrightarrow> \<forall>t \<in> fst ` set xs. t \<le> nt \<Longrightarrow>
  takeWhile (\<lambda>(t, X). memL I (nt - t)) xs = filter (\<lambda>(t, X). memL I (nt - t)) xs"
  by (induction xs) (auto 0 3 simp: memL_mono intro!: filter_empty_conv[THEN iffD2, symmetric])

lemma fold_Mapping_filter_None: "Mapping.lookup ts as = None \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) ts. Mapping.filter
  (filter_cond X ts t) ts) ds ts) as = None"
  by (induction ds arbitrary: ts) (auto simp add: Mapping.lookup_filter)

lemma Mapping_lookup_filter_Some_P: "Mapping.lookup (Mapping.filter P m) k = Some v \<Longrightarrow> P k v"
  by (auto simp add: Mapping.lookup_filter split: option.splits if_splits)

lemma Mapping_lookup_filter_None: "(\<And>v. \<not>P k v) \<Longrightarrow>
  Mapping.lookup (Mapping.filter P m) k = None"
  by (auto simp add: Mapping.lookup_filter split: option.splits)

lemma Mapping_lookup_filter_Some: "(\<And>v. P k v) \<Longrightarrow>
  Mapping.lookup (Mapping.filter P m) k = Mapping.lookup m k"
  by (auto simp add: Mapping.lookup_filter split: option.splits)

lemma Mapping_lookup_filter_not_None: "Mapping.lookup (Mapping.filter P m) k \<noteq> None \<Longrightarrow>
  Mapping.lookup (Mapping.filter P m) k = Mapping.lookup m k"
  by (auto simp add: Mapping.lookup_filter split: option.splits)

lemma fold_Mapping_filter_Some_None: "Mapping.lookup ts as = Some t \<Longrightarrow>
  as \<in> X \<Longrightarrow> (t, X) \<in> set ds \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) ts. Mapping.filter (filter_cond X ts t) ts) ds ts) as = None"
proof (induction ds arbitrary: ts)
  case (Cons a ds)
  show ?case
  proof (cases a)
    case (Pair t' X')
    with Cons show ?thesis
      using fold_Mapping_filter_None[of "Mapping.filter (filter_cond X' ts t') ts" as ds]
        Mapping_lookup_filter_not_None[of "filter_cond X' ts t'" ts as]
        fold_Mapping_filter_None[OF Mapping_lookup_filter_None, of _ as ds ts]
      by (cases "Mapping.lookup (Mapping.filter (filter_cond X' ts t') ts) as = None") auto
  qed
qed simp

lemma fold_Mapping_filter_Some_Some: "Mapping.lookup ts as = Some t \<Longrightarrow>
  (\<And>X. (t, X) \<in> set ds \<Longrightarrow> as \<notin> X) \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) ts. Mapping.filter (filter_cond X ts t) ts) ds ts) as = Some t"
proof (induction ds arbitrary: ts)
  case (Cons a ds)
  then show ?case
  proof (cases a)
    case (Pair t' X')
    with Cons show ?thesis
      using Mapping_lookup_filter_Some[of "filter_cond X' ts t'" as ts] by auto
  qed
qed simp

fun filter_set where "filter_set (t, X) (m, Y) =
  (let m' = Mapping.filter (filter_cond X m t) m in (m', Y \<union> (Mapping.keys m - Mapping.keys m')))"

declare filter_set.simps[simp del]

lemma filter_set_sub: "filter_set (t, X) (m, Y) = (m', Y') \<Longrightarrow> Y' \<subseteq> Y \<union> X"
  by (auto simp: filter_set.simps Let_def Mapping_lookup_filter_Some domIff keys_dom_lookup)

lemma fold_filter_set_sub: "fold filter_set xs (m, Y) = (m', Y') \<Longrightarrow> Y' \<subseteq> Y \<union> \<Union>(snd ` set xs)"
proof (induction xs arbitrary: m Y)
  case (Cons a xs)
  show ?case
    using Cons(2)
    by (cases a; cases "filter_set a (m, Y)") (auto dest: Cons(1) filter_set_sub)
qed auto

lemma fold_filter_set_None: "Mapping.lookup ts as = None \<Longrightarrow>
  fold filter_set ds (ts, Y) = (ts', Y') \<Longrightarrow>
  Mapping.lookup ts' as = None \<and> (as \<in> Y' \<longleftrightarrow> as \<in> Y)"
proof (induction ds arbitrary: ts Y)
  case (Cons a ds)
  show ?case
  proof (cases a)
    case (Pair t' X')
    obtain ts'' Y'' where step: "filter_set a (ts, Y) = (ts'', Y'')"
      by fastforce
    show ?thesis
    proof (cases "Mapping.lookup ts'' as")
      case None
      have "as \<in> Y'' \<longleftrightarrow> as \<in> Y"
        using Cons(2) step
        by (auto simp: Pair filter_set.simps Let_def keys_is_none_rep)
      then show ?thesis
        using Cons(1)[OF None] Cons(2,3)
        by (auto simp: step)
    next
      case (Some t'')
      have False
        using Cons(2) Some step Mapping_lookup_filter_not_None
        by (force simp: Pair filter_set.simps Let_def)
      then show ?thesis ..
    qed
  qed
qed simp

lemma fold_filter_set_Some_None: "Mapping.lookup ts as = Some t \<Longrightarrow>
  as \<in> X \<Longrightarrow> (t, X) \<in> set ds \<Longrightarrow> fold filter_set ds (ts, Y) = (ts', Y') \<Longrightarrow>
  Mapping.lookup ts' as = None \<and> as \<in> Y'"
proof (induction ds arbitrary: ts Y)
  case (Cons a ds)
  show ?case
  proof (cases a)
    case (Pair t' X')
    obtain ts'' Y'' where step: "filter_set a (ts, Y) = (ts'', Y'')"
      by fastforce
    show ?thesis
    proof (cases "Mapping.lookup ts'' as")
      case None
      have "as \<in> Y''"
        using Cons(2) None step
        by (auto simp: Pair filter_set.simps Let_def Mapping_keys_intro keys_is_none_rep)
      then have "fold filter_set ds (ts'', Y'') = (ts', Y') \<Longrightarrow> as \<in> Y'"
        by (induction ds arbitrary: ts'' Y'') (auto simp: filter_set.simps Let_def)
      moreover have "fold filter_set ds (ts'', Y'') = (ts', Y') \<Longrightarrow> Mapping.lookup ts' as = None"
        using None Mapping_lookup_filter_not_None
        by (induction ds arbitrary: ts'' Y'') (fastforce simp: filter_set.simps Let_def)+
      ultimately show ?thesis
        using Cons(5)
        by (auto simp: step)
    next
      case (Some t'')
      have lookup_ts'': "Mapping.lookup ts'' as = Some t"
        using Cons(2) step Some Mapping_lookup_filter_not_None
        by (fastforce simp: Pair filter_set.simps Let_def Mapping_lookup_filter_None)
      have set_ds: "(t, X) \<in> set ds"
        using Cons(2,3,4) step Some
        by (auto simp: filter_set.simps Let_def Mapping_lookup_filter_None)
      show ?thesis
        using Cons lookup_ts'' set_ds
        by (auto simp: step)
    qed
  qed
qed simp

lemma fold_filter_set_Some_Some: "Mapping.lookup ts as = Some t \<Longrightarrow>
  (\<And>X. (t, X) \<in> set ds \<Longrightarrow> as \<notin> X) \<Longrightarrow> fold filter_set ds (ts, Y) = (ts', Y') \<Longrightarrow>
  Mapping.lookup ts' as = Some t \<and> (as \<in> Y' \<longleftrightarrow> as \<in> Y)"
proof (induction ds arbitrary: ts Y)
  case (Cons a ds)
  show ?case
  proof (cases a)
    case (Pair t' X')
    obtain ts'' Y'' where step: "filter_set a (ts, Y) = (ts'', Y'')"
      by fastforce
    show ?thesis
    proof (cases "Mapping.lookup ts'' as")
      case None
      have "False"
        using Cons(2,3) None step
        by (auto simp: Pair filter_set.simps Let_def) (smt (z3) Mapping_lookup_filter_Some option.distinct(1) option.inject)
      then show ?thesis ..
    next
      case (Some t'')
      have lookup_ts'': "Mapping.lookup ts'' as = Some t"
        using Cons(2) step Some Mapping_lookup_filter_not_None
        by (fastforce simp: Pair filter_set.simps Let_def Mapping_lookup_filter_None)
      have "as \<in> Y'' \<longleftrightarrow> as \<in> Y"
        using step Mapping_keys_intro Some
        by (force simp: Pair filter_set.simps Let_def)
      then show ?thesis
        using Cons(1)[OF lookup_ts''] Cons(3,4)
        by (auto simp: step)
    qed
  qed
qed simp

fun shift_end :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "shift_end args nt (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    (let I = args_ivl args;
    data_prev' = dropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_prev;
    (data_in, discard) = takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in;
    (tuple_in, del) = fold filter_set discard (tuple_in, {}) in
    (t, gc, maskL, maskR, data_prev', data_in,
     table_in - del, wf_table_antijoin wf_table_in (wf_table_of_set_args args del), tuple_in,
     wf_table_since, tuple_since))"

lemma valid_shift_end_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux args cur
    (ot, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) auxlist"
  and nt_mono: "nt \<ge> cur"
  shows "valid_mmsaux args cur (shift_end args nt
    (ot, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since))
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
proof -
  define I where "I = args_ivl args"
  define data_in' where "data_in' \<equiv>
    fst (takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in)"
  define data_prev' where "data_prev' \<equiv>
    dropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_prev"
  define discard where "discard \<equiv>
    snd (takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in)"
  have set_discard: "\<Union>(snd ` set discard) \<subseteq> \<Union>(snd ` (set (linearize data_in)))"
    by (auto simp: discard_def takedropWhile_queue_snd simp del: takedropWhile_queue.simps dest: set_takeWhileD)
  obtain tuple_in' del where fold_filter_set: "fold filter_set discard (tuple_in, {}) = (tuple_in', del)"
    by (cases "fold filter_set discard (tuple_in, {})") auto
  have tuple_in_Some_None: "Mapping.lookup tuple_in' as = None" "as \<in> del"
    if "Mapping.lookup tuple_in as = Some t" "as \<in> X" "(t, X) \<in> set discard" for as t X
    using fold_filter_set_Some_None[OF _ _ _ fold_filter_set] that
    by auto
  have tuple_in_Some_Some: "Mapping.lookup tuple_in' as = Some t" "as \<notin> del"
    if "Mapping.lookup tuple_in as = Some t" "\<And>X. (t, X) \<in> set discard \<Longrightarrow> as \<notin> X" for as t
    using fold_filter_set_Some_Some[OF _ _ fold_filter_set] that
    by auto
  have tuple_in_None: "Mapping.lookup tuple_in' as = None" "as \<notin> del"
    if "Mapping.lookup tuple_in as = None" for as
    using fold_filter_set_None[OF _ fold_filter_set] that
    by auto
  have tuple_in'_keys: "\<And>as. as \<in> Mapping.keys tuple_in' \<Longrightarrow> as \<in> Mapping.keys tuple_in"
    using tuple_in_Some_None tuple_in_Some_Some tuple_in_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping_keys_dest)
  have F1: "sorted (map fst (linearize data_in))" "\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt"
    using valid_before nt_mono by auto
  have F2: "sorted (map fst (linearize data_prev))" "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt"
    using valid_before nt_mono by auto
  have lin_data_in': "linearize data_in' =
    filter (\<lambda>(t, X). memR I (nt - t)) (linearize data_in)"
    unfolding data_in'_def[unfolded takedropWhile_queue_fst] dropWhile_queue_rep
      dropWhile_filter[OF F1] thm dropWhile_filter[OF F1] ..
  then have set_lin_data_in': "set (linearize data_in') \<subseteq> set (linearize data_in)"
    by auto
  have "sorted (map fst (linearize data_in))"
    using valid_before by auto
  then have sorted_lin_data_in': "sorted (map fst (linearize data_in'))"
    unfolding lin_data_in' using sorted_filter by auto
  have discard_alt: "discard = filter (\<lambda>(t, X). \<not> memR I (nt - t)) (linearize data_in)"
    unfolding discard_def[unfolded takedropWhile_queue_snd] takeWhile_filter[OF F1] ..
  have lin_data_prev': "linearize data_prev' =
    filter (\<lambda>(t, X). memR I (nt - t)) (linearize data_prev)"
    unfolding data_prev'_def[unfolded takedropWhile_queue_fst] dropWhile_queue_rep
      dropWhile_filter[OF F2] ..
  have "sorted (map fst (linearize data_prev))"
    using valid_before by auto
  then have sorted_lin_data_prev': "sorted (map fst (linearize data_prev'))"
    unfolding lin_data_prev' using sorted_filter by auto
  have lookup_tuple_in': "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in')). valid_tuple tuple_since tas \<and> as = snd tas})"
  proof -
    fix as
    show "Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in')). valid_tuple tuple_since tas \<and> as = snd tas})"
    proof (cases "Mapping.lookup tuple_in as")
      case None
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas} = {}"
        using valid_before by (auto dest!: safe_max_empty_dest)
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas} = {}"
        using ts_tuple_rel_mono[OF set_lin_data_in'] by auto
      then show ?thesis
        unfolding tuple_in_None[OF None] using iffD2[OF safe_max_empty, symmetric] by blast
    next
      case (Some t)
      show ?thesis
      proof (cases "\<exists>X. (t, X) \<in> set discard \<and> as \<in> X")
        case True
        then obtain X where X_def: "(t, X) \<in> set discard" "as \<in> X"
          by auto
        have "\<not> memR I (nt - t)"
          using X_def(1) unfolding discard_alt by simp
        moreover have "\<And>t'. (t', as) \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
          valid_tuple tuple_since (t', as) \<Longrightarrow> t' \<le> t"
          using valid_before Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff)
        ultimately have "{tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since tas \<and> as = snd tas} = {}"
          unfolding lin_data_in' using ts_tuple_rel_set_filter
          by (fastforce simp add: ts_tuple_rel_def memR_antimono)
        then show ?thesis
          unfolding tuple_in_Some_None[OF Some X_def(2,1)]
          using iffD2[OF safe_max_empty, symmetric] by blast
      next
        case False
        then have lookup_Some: "Mapping.lookup tuple_in' as = Some t"
          using tuple_in_Some_Some[OF Some] by auto
        have t_as: "(t, as) \<in> ts_tuple_rel (set (linearize data_in))"
          "valid_tuple tuple_since (t, as)"
          using valid_before Some by (auto dest: safe_max_Some_dest_in[OF finite_fst_ts_tuple_rel])
        then obtain X where X_def: "as \<in> X" "(t, X) \<in> set (linearize data_in)"
          by (auto simp add: ts_tuple_rel_def)
        have "(t, X) \<in> set (linearize data_in')"
          using X_def False unfolding discard_alt lin_data_in' by auto
        then have t_in_fst: "t \<in> fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since tas \<and> as = snd tas}"
          using t_as(2) X_def(1) by (auto simp add: ts_tuple_rel_def image_iff)
        have "\<And>t'. (t', as) \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
          valid_tuple tuple_since (t', as) \<Longrightarrow> t' \<le> t"
          using valid_before Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff)
        then have "Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since tas \<and> as = snd tas}) = t"
          using Max_eqI[OF finite_fst_ts_tuple_rel, OF _ t_in_fst]
            ts_tuple_rel_mono[OF set_lin_data_in'] by fastforce
        then show ?thesis
          unfolding lookup_Some using t_in_fst by (auto simp add: safe_max_def)
      qed
    qed
  qed
  have table_in: "table (args_n args) (args_R args) (Mapping.keys tuple_in)"
    and table_in': "table (args_n args) (args_R args) (Mapping.keys tuple_in')"
    using tuple_in'_keys valid_before by (auto simp add: table_def)
  have keys_tuple_in: "table_in = Mapping.keys tuple_in"
    using valid_before
    by auto
  then have keys_tuple_in': "table_in - del = Mapping.keys tuple_in'"
    using tuple_in_None tuple_in'_keys tuple_in_Some_Some tuple_in_Some_None
    by auto (metis Mapping_keys_dest Mapping_keys_intro option.distinct(1))+
  have sig_in: "wf_table_sig wf_table_in = (args_n args, args_R args)"
    and set_in: "wf_table_set wf_table_in = Mapping.keys tuple_in"
    using valid_before
    by auto
  have sig_in'': "wf_table_sig (wf_table_antijoin wf_table_in (wf_table_of_set_args args del)) = (args_n args, args_R args)"
    and sig_since: "wf_table_sig wf_table_since = (args_n args, args_R args)"
    and keys_since: "wf_table_set wf_table_since = Mapping.keys tuple_since"
    using valid_before
    by (auto simp: wf_table_sig_antijoin)
  have "table (args_n args) (args_R args) (\<Union>(snd ` (set (linearize data_in))))"
    using valid_before
    by (auto simp: table_def)
  then have table_del: "table (args_n args) (args_R args) del"
    using fold_filter_set_sub[OF fold_filter_set] set_discard New_max.wf_atable_subset
    by fastforce
  have keys_tuple_in'': "wf_table_set (wf_table_antijoin wf_table_in (wf_table_of_set_args args del)) = Mapping.keys tuple_in'"
    by (auto simp: keys_tuple_in keys_tuple_in'[symmetric] set_in[symmetric]
        wf_table_set_antijoin[OF sig_in wf_table_sig_args subset_refl]
        join_False_alt join_eq[OF table_del wf_table_set_table[OF sig_in]]
        wf_table_set_table[OF wf_table_sig_args] wf_table_of_set_args[OF table_del])
  have "ts_tuple_rel (set auxlist) =
    {as \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since as}"
    using valid_before by auto
  then have "ts_tuple_rel (set (filter (\<lambda>(t, rel). memR I (nt - t)) auxlist)) =
    {as \<in> ts_tuple_rel (set (linearize data_prev') \<union> set (linearize data_in')).
    valid_tuple tuple_since as}"
    unfolding lin_data_prev' lin_data_in' ts_tuple_rel_Un ts_tuple_rel_filter by auto
  then show ?thesis
    using data_prev'_def data_in'_def fold_filter_set discard_def valid_before nt_mono
      sorted_lin_data_prev' sorted_lin_data_in' lin_data_prev' lin_data_in' lookup_tuple_in'
      table_in' keys_tuple_in' sig_in'' keys_tuple_in'' sig_since keys_since unfolding I_def
    by (auto simp only: valid_mmsaux.simps shift_end.simps Let_def split: prod.splits) auto
      (* takes long *)
qed

lemma valid_shift_end_mmsaux: "valid_mmsaux args cur aux auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
  valid_mmsaux args cur (shift_end args nt aux)
  (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
  using valid_shift_end_mmsaux_unfolded by (cases aux) fast

lift_definition upd_set :: "('a, 'b) mapping \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>m f X a. if a \<in> X then Some (f a) else m a" .

lemma Mapping_lookup_upd_set: "Mapping.lookup (upd_set m f X) a =
  (if a \<in> X then Some (f a) else Mapping.lookup m a)"
  by (simp add: Mapping.lookup.rep_eq upd_set.rep_eq)

lemma Mapping_upd_set_keys: "Mapping.keys (upd_set m f X) = Mapping.keys m \<union> X"
  by (auto simp add: Mapping_lookup_upd_set dest!: Mapping_keys_dest intro: Mapping_keys_intro)

lemma fold_append_queue_rep: "linearize (fold (\<lambda>x q. append_queue x q) xs q) = linearize q @ xs"
  by (induction xs arbitrary: q) (auto simp add: append_queue_rep)

lemma Max_Un_absorb:
  assumes "finite X" "X \<noteq> {}" "finite Y" "(\<And>x y. y \<in> Y \<Longrightarrow> x \<in> X \<Longrightarrow> y \<le> x)"
  shows "Max (X \<union> Y) = Max X"
proof -
  have Max_X_in_X: "Max X \<in> X"
    using Max_in[OF assms(1,2)] .
  have Max_X_in_XY: "Max X \<in> X \<union> Y"
    using Max_in[OF assms(1,2)] by auto
  have fin: "finite (X \<union> Y)"
    using assms(1,3) by auto
  have Y_le_Max_X: "\<And>y. y \<in> Y \<Longrightarrow> y \<le> Max X"
    using assms(4)[OF _ Max_X_in_X] .
  have XY_le_Max_X: "\<And>y. y \<in> X \<union> Y \<Longrightarrow> y \<le> Max X"
    using Max_ge[OF assms(1)] Y_le_Max_X by auto
  show ?thesis
    using Max_eqI[OF fin XY_le_Max_X Max_X_in_XY] by auto
qed

lemma Mapping_lookup_fold_upd_set_idle: "{(t, X) \<in> set xs. as \<in> Z X t} = {} \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z X t)) xs m) as = Mapping.lookup m as"
proof (induction xs arbitrary: m)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain x1 x2 where "x = (x1, x2)" by (cases x)
  have "Mapping.lookup (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z X t)) xs (upd_set m (\<lambda>_. x1) (Z x2 x1))) as =
    Mapping.lookup (upd_set m (\<lambda>_. x1) (Z x2 x1)) as"
    using Cons by auto
  also have "Mapping.lookup (upd_set m (\<lambda>_. x1) (Z x2 x1)) as = Mapping.lookup m as"
    using Cons.prems by (auto simp: \<open>x = (x1, x2)\<close> Mapping_lookup_upd_set)
  finally show ?case by (simp add: \<open>x = (x1, x2)\<close>)
qed

lemma Mapping_lookup_fold_upd_set_max: "{(t, X) \<in> set xs. as \<in> Z X t} \<noteq> {} \<Longrightarrow>
  sorted (map fst xs) \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z X t)) xs m) as =
  Some (Max (fst ` {(t, X) \<in> set xs. as \<in> Z X t}))"
proof (induction xs arbitrary: m)
  case (Cons x xs)
  obtain t X where tX_def: "x = (t, X)"
    by (cases x) auto
  have set_fst_eq: "(fst ` {(t, X). (t, X) \<in> set (x # xs) \<and> as \<in> Z X t}) =
    ((fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t}) \<union>
    (if as \<in> Z X t then {t} else {}))"
    using image_iff by (fastforce simp add: tX_def split: if_splits)
  show ?case
  proof (cases "{(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t} \<noteq> {}")
    case True
    have "{(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t} \<subseteq> set xs"
      by auto
    then have fin: "finite (fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t})"
      by (simp add: finite_subset)
    have "Max (insert t (fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t})) =
      Max (fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t})"
      using Max_Un_absorb[OF fin, of "{t}"] True Cons(3) tX_def by auto
    then show ?thesis
      using Cons True unfolding set_fst_eq by auto
  next
    case False
    then have empty: "{(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t} = {}"
      by auto
    then have "as \<in> Z X t"
      using Cons(2) set_fst_eq by fastforce
    then show ?thesis
      using Mapping_lookup_fold_upd_set_idle[OF empty] unfolding set_fst_eq empty
      by (auto simp add: Mapping_lookup_upd_set tX_def)
  qed
qed simp

fun upd_set_keys where "upd_set_keys Z (t, X) (m, Y) = (upd_set m (\<lambda>_. t) (Z X t), Y \<union> Z X t)"

declare upd_set_keys.simps[simp del]

lemma upd_set_keys_sub: "upd_set_keys Z (t, X) (m, Y) = (m', Y') \<Longrightarrow> Y' \<subseteq> Y \<union> Z X t"
  by (auto simp: upd_set_keys.simps Mapping_lookup_filter_Some domIff keys_dom_lookup)

lemma fold_upd_set_keys_sub:
  assumes Z_sub: "\<And>X t. Z X t \<subseteq> X"
  shows "fold (upd_set_keys Z) xs (m, Y) = (m', Y') \<Longrightarrow> Y' \<subseteq> Y \<union> \<Union>(snd ` set xs)"
proof (induction xs arbitrary: m Y)
  case (Cons a xs)
  show ?case
    using Cons(2) Z_sub
    by (cases a; cases "upd_set_keys Z a (m, Y)") (fastforce dest: Cons(1) upd_set_keys_sub)
qed auto

lemma fold_upd_set_keys:
  assumes "fold (upd_set_keys Z) mv (ts, {}) = (ts', Y)"
  shows "ts' = fold (\<lambda>(t, X) ts. upd_set ts (\<lambda>_. t) (Z X t)) mv ts"
    "Mapping.keys ts' = Mapping.keys ts \<union> Y"
proof -
  have fst_fold_upd_set_keys: "fst (fold (upd_set_keys Z) mv (ts, Y0)) = fold (\<lambda>(t, X) ts. upd_set ts (\<lambda>_. t) (Z X t)) mv ts"
    for Y0 :: "'a set"
    by (induction mv arbitrary: ts Y0) (auto simp: upd_set_keys.simps)
  show "ts' = fold (\<lambda>(t, X) ts. upd_set ts (\<lambda>_. t) (Z X t)) mv ts"
    using fst_fold_upd_set_keys[where ?Y0.0="{}"]
    by (auto simp: assms)
  have keys_fold_upd_set_keys: "Y0 \<subseteq> Y \<and> Mapping.keys ts \<subseteq> Mapping.keys ts' \<and> Mapping.keys ts' \<union> Y0 = Mapping.keys ts \<union> Y" if "fold (upd_set_keys Z) mv (ts, Y0) = (ts', Y)" for Y0
    using that
  proof (induction mv arbitrary: ts Y0)
    case (Cons a mv)
    show ?case
    proof (cases a)
      case (Pair t' X')
      show ?thesis
        using Cons(2)
        apply (simp add: Pair upd_set_keys.simps)
        apply (drule Cons(1))
        apply (auto simp: Mapping_upd_set_keys)
        done
    qed
  qed simp
  show "Mapping.keys ts' = Mapping.keys ts \<union> Y"
    using keys_fold_upd_set_keys[OF assms]
    by auto
qed

fun add_new_ts_mmsaux' :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_ts_mmsaux' args nt (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    (let I = args_ivl args;
    (data_prev, move) = takedropWhile_queue (\<lambda>(t, X). memL I (nt - t)) data_prev;
    data_in = fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in) move data_in;
    (tuple_in, add) = fold (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)})) move (tuple_in, {}) in
    (nt, gc, maskL, maskR, data_prev, data_in, table_in \<union> add, wf_table_union wf_table_in (wf_table_of_set_args args add), tuple_in, wf_table_since, tuple_since))"

lemma Mapping_keys_fold_upd_set: "k \<in> Mapping.keys (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z t X))
  xs m) \<Longrightarrow> k \<in> Mapping.keys m \<or> (\<exists>(t, X) \<in> set xs. k \<in> Z t X)"
  by (induction xs arbitrary: m) (fastforce simp add: Mapping_upd_set_keys)+

lemma valid_add_new_ts_mmsaux'_unfolded:
  assumes valid_before: "valid_mmsaux args cur
    (ot, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) auxlist"
  and nt_mono: "nt \<ge> cur"
  shows "valid_mmsaux args nt (add_new_ts_mmsaux' args nt
    (ot, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since)) auxlist"
proof -
  define I where "I = args_ivl args"
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  define data_prev' where "data_prev' \<equiv> dropWhile_queue (\<lambda>(t, X). memL I (nt - t)) data_prev"
  define move where "move \<equiv> takeWhile (\<lambda>(t, X). memL I (nt - t)) (linearize data_prev)"
  define data_in' where "data_in' \<equiv> fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in)
    move data_in"
  obtain tuple_in' add where aux:
    "fold (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)})) move (tuple_in, {}) = (tuple_in', add)"
    by fastforce
  note tuple_in'_def = fold_upd_set_keys(1)[OF aux]
  note add_def = fold_upd_set_keys(2)[OF aux]
  have tuple_in'_keys: "\<And>as. as \<in> Mapping.keys tuple_in' \<Longrightarrow> as \<in> Mapping.keys tuple_in \<or>
    (\<exists>(t, X)\<in>set move. as \<in> {as \<in> X. valid_tuple tuple_since (t, as)})"
    using Mapping_keys_fold_upd_set[of _ "\<lambda>t X. {as \<in> X. valid_tuple tuple_since (t, as)}"]
    by (auto simp add: tuple_in'_def)
  have F1: "sorted (map fst (linearize data_in))" "\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt"
    "\<forall>t \<in> fst ` set (linearize data_in). t \<le> ot \<and> memL I (ot - t)"
    using valid_before nt_mono unfolding I_def by auto
  have F2: "sorted (map fst (linearize data_prev))" "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt"
    "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> ot \<and> \<not> memL I (ot - t)"
    using valid_before nt_mono unfolding I_def by auto
  have lin_data_prev': "linearize data_prev' =
    filter (\<lambda>(t, X). \<not> memL I (nt - t)) (linearize data_prev)"
    unfolding data_prev'_def dropWhile_queue_rep dropWhile_filter'[OF F2(1,2)] ..
  have move_filter: "move = filter (\<lambda>(t, X). memL I (nt - t)) (linearize data_prev)"
    unfolding move_def takeWhile_filter'[OF F2(1,2)] ..
  then have sorted_move: "sorted (map fst move)"
    using sorted_filter F2 by auto
  have "\<forall>t\<in>fst ` set move. t \<le> ot \<and> \<not> memL I (ot - t)"
    using move_filter F2(3) set_filter by auto
  then have fst_set_before: "\<forall>t\<in>fst ` set (linearize data_in). \<forall>t'\<in>fst ` set move. t \<le> t'"
    using F1(3) by (meson le_diff_iff' memL_mono nat_le_linear)
  then have fst_ts_tuple_rel_before: "\<forall>t\<in>fst ` ts_tuple_rel (set (linearize data_in)).
    \<forall>t'\<in>fst ` ts_tuple_rel (set move). t \<le> t'"
    by (fastforce simp add: ts_tuple_rel_def)
  have sorted_lin_data_prev': "sorted (map fst (linearize data_prev'))"
    unfolding lin_data_prev' using sorted_filter F2 by auto
  have lin_data_in': "linearize data_in' = linearize data_in @ move"
    unfolding data_in'_def using fold_append_queue_rep by fastforce
  have sorted_lin_data_in': "sorted (map fst (linearize data_in'))"
    unfolding lin_data_in' using F1(1) sorted_move fst_set_before by (simp add: sorted_append)
  have set_lin_prev'_in': "set (linearize data_prev') \<union> set (linearize data_in') =
    set (linearize data_prev) \<union> set (linearize data_in)"
    using lin_data_prev' lin_data_in' move_filter by auto
  have ts_tuple_rel': "ts_tuple_rel (set auxlist) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev') \<union> set (linearize data_in')).
    valid_tuple tuple_since tas}"
    unfolding set_lin_prev'_in' using valid_before by auto
  have lookup': "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in')).
    valid_tuple tuple_since tas \<and> as = snd tas})"
  proof -
    fix as
    show "Mapping.lookup tuple_in' as = safe_max (fst `
      {tas \<in> ts_tuple_rel (set (linearize data_in')).
      valid_tuple tuple_since tas \<and> as = snd tas})"
    proof (cases "{(t, X) \<in> set move. as \<in> X \<and> valid_tuple tuple_since (t, as)} = {}")
      case True
      have move_absorb: "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas} =
        {tas \<in> ts_tuple_rel (set (linearize data_in @ move)).
        valid_tuple tuple_since tas \<and> as = snd tas}"
        using True by (auto simp add: ts_tuple_rel_def)
      have "Mapping.lookup tuple_in as =
        safe_max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas})"
        using valid_before by auto
      then have "Mapping.lookup tuple_in as =
        safe_max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas})"
        unfolding lin_data_in' move_absorb .
      then show ?thesis
        using Mapping_lookup_fold_upd_set_idle[of "move" as
          "\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)}"] True
        unfolding tuple_in'_def by auto
    next
      case False
      have split: "fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas} =
        fst ` {tas \<in> ts_tuple_rel (set move). valid_tuple tuple_since tas \<and> as = snd tas} \<union>
        fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas}"
        unfolding lin_data_in' set_append ts_tuple_rel_Un by auto
      have max_eq: "Max (fst ` {tas \<in> ts_tuple_rel (set move).
        valid_tuple tuple_since tas \<and> as = snd tas}) =
        Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas})"
        unfolding split using False fst_ts_tuple_rel_before
        by (fastforce simp add: ts_tuple_rel_def
            intro!: Max_Un_absorb[OF finite_fst_ts_tuple_rel _ finite_fst_ts_tuple_rel, symmetric])
      have "fst ` {(t, X). (t, X) \<in> set move \<and> as \<in> {as \<in> X. valid_tuple tuple_since (t, as)}} =
        fst ` {tas \<in> ts_tuple_rel (set move). valid_tuple tuple_since tas \<and> as = snd tas}"
        by (auto simp add: ts_tuple_rel_def image_iff)
      then have "Mapping.lookup tuple_in' as = Some (Max (fst ` {tas \<in> ts_tuple_rel (set move).
        valid_tuple tuple_since tas \<and> as = snd tas}))"
        using Mapping_lookup_fold_upd_set_max[of "move" as
          "\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)}", OF _ sorted_move] False
        unfolding tuple_in'_def by (auto simp add: ts_tuple_rel_def)
      then show ?thesis
        unfolding max_eq using False
        by (auto simp add: safe_max_def lin_data_in' ts_tuple_rel_def)
    qed
  qed
  have table_in': "table n R (Mapping.keys tuple_in')"
  proof -
    {
      fix as
      assume assm: "as \<in> Mapping.keys tuple_in'"
      have "wf_tuple n R as"
        using tuple_in'_keys[OF assm]
      proof (rule disjE)
        assume "as \<in> Mapping.keys tuple_in"
        then show "wf_tuple n R as"
          using valid_before by (auto simp add: table_def n_def R_def)
      next
        assume "\<exists>(t, X)\<in>set move. as \<in> {as \<in> X. valid_tuple tuple_since (t, as)}"
        then obtain t X where tX_def: "(t, X) \<in> set move" "as \<in> X"
          by auto
        then have "as \<in> \<Union>(snd ` set (linearize data_prev))"
          unfolding move_def using set_takeWhileD by force
        then show "wf_tuple n R as"
          using valid_before by (auto simp add: n_def R_def)
      qed
    }
    then show ?thesis
      by (auto simp add: table_def)
  qed
  have table_in: "table (args_n args) (args_R args) (Mapping.keys tuple_in)"
    using valid_before by (auto simp add: table_def)
  have keys_tuple_in: "table_in = Mapping.keys tuple_in"
    using valid_before
    by auto
  note keys_tuple_in' = add_def[symmetric]
  have sig_in: "wf_table_sig wf_table_in = (args_n args, args_R args)"
    and set_in: "wf_table_set wf_table_in = Mapping.keys tuple_in"
    using valid_before
    by auto
  have sig_in'': "wf_table_sig (wf_table_union wf_table_in (wf_table_of_set_args args add)) = (args_n args, args_R args)"
    and sig_since: "wf_table_sig wf_table_since = (args_n args, args_R args)"
    and keys_since: "wf_table_set wf_table_since = Mapping.keys tuple_since"
    using valid_before
    by (auto simp: wf_table_sig_union wf_table_sig_args)
  have "table (args_n args) (args_R args) (\<Union>(snd ` (set (linearize data_prev))))"
    using valid_before
    by (auto simp: table_def)
  moreover have "\<Union> (snd ` set move) \<subseteq> \<Union> (snd ` set (linearize data_prev))"
    by (auto simp: move_filter)
  ultimately have table_add: "table (args_n args) (args_R args) add"
    using fold_upd_set_keys_sub[OF _ aux] New_max.wf_atable_subset
    by fastforce
  have keys_tuple_in'': "wf_table_set (wf_table_union wf_table_in (wf_table_of_set_args args add)) = Mapping.keys tuple_in'"
    by (auto simp: keys_tuple_in keys_tuple_in'[symmetric] set_in[symmetric]
        wf_table_set_union[OF trans[OF sig_in wf_table_sig_args[symmetric]]]
        wf_table_of_set_args[OF table_add])
  have data_prev'_move: "(data_prev', move) =
    takedropWhile_queue (\<lambda>(t, X). memL I (nt - t)) data_prev"
    using takedropWhile_queue_fst takedropWhile_queue_snd data_prev'_def move_def
    by (metis surjective_pairing)
  moreover have "valid_mmsaux args nt (nt, gc, maskL, maskR, data_prev', data_in', table_in \<union> add,
    wf_table_union wf_table_in (wf_table_of_set_args args add), tuple_in', wf_table_since, tuple_since) auxlist"
    using lin_data_prev' sorted_lin_data_prev' lin_data_in' move_filter sorted_lin_data_in'
      nt_mono valid_before ts_tuple_rel' lookup'
      table_in' keys_tuple_in' sig_in'' keys_tuple_in'' sig_since keys_since unfolding I_def
    apply (auto simp only: valid_mmsaux.simps Let_def n_def R_def split: option.splits)
          apply (auto)
    apply (auto simp: memL_mono)
    done
      (* takes long *)
  ultimately show ?thesis
    by (auto simp only: add_new_ts_mmsaux'.simps Let_def data_in'_def aux tuple_in'_def I_def
        split: prod.splits)
qed

lemma valid_add_new_ts_mmsaux': "valid_mmsaux args cur aux auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
  valid_mmsaux args nt (add_new_ts_mmsaux' args nt aux) auxlist"
  using valid_add_new_ts_mmsaux'_unfolded by (cases aux) fast

definition add_new_ts_mmsaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_ts_mmsaux args nt aux = add_new_ts_mmsaux' args nt (shift_end args nt aux)"

lemma valid_add_new_ts_mmsaux:
  assumes "valid_mmsaux args cur aux auxlist" "nt \<ge> cur"
  shows "valid_mmsaux args nt (add_new_ts_mmsaux args nt aux)
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
  using valid_add_new_ts_mmsaux'[OF valid_shift_end_mmsaux[OF assms] assms(2)]
  unfolding add_new_ts_mmsaux_def .

definition mapping_delete_set :: "('a, 'b) mapping \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) mapping" where
  "mapping_delete_set m X = Mapping.filter (join_filter_cond False X) m"

lemma delete_set_lookup: "Mapping.lookup (mapping_delete_set m X) a = (if a \<in> X then
  None else Mapping.lookup m a)"
  by (auto simp: mapping_delete_set_def Mapping.lookup_filter split: option.splits)

lemma delete_set_keys[simp]: "Mapping.keys (mapping_delete_set m X) = Mapping.keys m - X"
  by (auto simp add: delete_set_lookup intro!: Mapping_keys_intro
      dest!: Mapping_keys_dest split: if_splits)

fun join_mmsaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "join_mmsaux args X (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    (let pos = args_pos args in
    (if (\<forall>i \<in> set maskL. \<not>i) then
      (let nones = replicate (length maskL) None;
      take_all = (pos \<longleftrightarrow> nones \<in> X);
      table_in' = (if take_all then table_in else {});
      wf_table_in' = (if take_all then wf_table_in else wf_table_of_set_args args {});
      tuple_in' = (if take_all then tuple_in else Mapping.empty);
      wf_table_since' = (if take_all then wf_table_since else wf_table_of_set_args args {});
      tuple_since' = (if take_all then tuple_since else Mapping.empty) in
      (t, gc, maskL, maskR, data_prev, data_in, table_in', wf_table_in', tuple_in', wf_table_since', tuple_since'))
     else (let wf_X = wf_table_of_idx (wf_idx_of_set (args_n args) (args_L args) (args_L args) X);
      wf_in_del = (if pos then wf_table_antijoin else wf_table_join) wf_table_in wf_X;
      in_del = wf_table_set wf_in_del;
      tuple_in' = mapping_delete_set tuple_in in_del;
      table_in' = table_in - in_del;
      wf_table_in' = wf_table_antijoin wf_table_in wf_in_del;
      wf_since_del = (if pos then wf_table_antijoin else wf_table_join) wf_table_since wf_X;
      since_del = wf_table_set wf_since_del;
      tuple_since' = mapping_delete_set tuple_since since_del;
      wf_table_since' = wf_table_antijoin wf_table_since wf_since_del in
      (t, gc, maskL, maskR, data_prev, data_in, table_in', wf_table_in', tuple_in', wf_table_since', tuple_since'))))"

fun join_mmsaux_abs :: "args \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "join_mmsaux_abs args X (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    (let pos = args_pos args in
    (let tuple_in = Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_in;
    tuple_since = Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_since in
    (t, gc, maskL, maskR, data_prev, data_in,
     Mapping.keys tuple_in, wf_table_of_set_args args (Mapping.keys tuple_in), tuple_in,
     wf_table_of_set_args args (Mapping.keys tuple_since), tuple_since)))"

lemma Mapping_filter_cong:
  assumes cong: "(\<And>k v. k \<in> Mapping.keys m \<Longrightarrow> f k v = f' k v)"
  shows "Mapping.filter f m = Mapping.filter f' m"
proof -
  have "\<And>k. Mapping.lookup (Mapping.filter f m) k = Mapping.lookup (Mapping.filter f' m) k"
    using cong
    by (fastforce simp add: Mapping.lookup_filter intro: Mapping_keys_intro split: option.splits)
  then show ?thesis
    by (simp add: mapping_eqI)
qed

lemma Mapping_keys_filter: "Mapping.keys (Mapping.filter (\<lambda>x _. P x) m) = Set.filter P (Mapping.keys m)"
  by transfer (auto simp: Set.filter_def split: option.splits if_splits)

lemma join_mmsaux_abs_eq:
  assumes valid_before: "valid_mmsaux args cur
    (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) auxlist"
  and table_left: "table (args_n args) (args_L args) X"
  shows "join_mmsaux args X (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    join_mmsaux_abs args X (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since)"
proof -
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  have L_R: "args_L args \<subseteq> args_R args"
    and maskL_def: "join_mask (args_n args) (args_L args) = maskL"
    using valid_before
    by auto
  have table_in_def: "Mapping.keys tuple_in = table_in"
    and table_table_in: "table (args_n args) (args_R args) table_in"
    and table_tuple_since: "table (args_n args) (args_R args) (Mapping.keys tuple_since)"
    using valid_before
    by auto
  have sig_in: "wf_table_sig wf_table_in = (args_n args, args_R args)"
    and set_in: "wf_table_set wf_table_in = Mapping.keys tuple_in"
    and set_args_in: "wf_table_set (wf_table_of_set_args args table_in) = table_in"
    using wf_table_of_set_args valid_before
    by auto
  have sig_since: "wf_table_sig wf_table_since = (args_n args, args_R args)"
    and set_since: "wf_table_set wf_table_since = Mapping.keys tuple_since"
    and set_args_since: "wf_table_set (wf_table_of_set_args args (Mapping.keys tuple_since)) = Mapping.keys tuple_since"
    using wf_table_of_set_args valid_before
    by auto
  show ?thesis
  proof (cases "\<forall>i \<in> set maskL. \<not>i")
    case True
    have length_maskL: "length maskL = n"
      using valid_before by (auto simp add: join_mask_def n_def)
    have proj_rep: "\<And>as. wf_tuple n R as \<Longrightarrow> proj_tuple maskL as = replicate (length maskL) None"
      using True proj_tuple_replicate by (force simp add: length_maskL wf_tuple_def)
    have keys_wf_in: "\<And>as. as \<in> Mapping.keys tuple_in \<Longrightarrow> wf_tuple n R as"
      using valid_before by (auto simp add: table_def n_def R_def)
    have keys_wf_since: "\<And>as. as \<in> Mapping.keys tuple_since \<Longrightarrow> wf_tuple n R as"
      using valid_before by (auto simp add: table_def n_def R_def)
    have "\<And>as. Mapping.lookup (Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X)
      tuple_in) as = Mapping.lookup (if (pos \<longleftrightarrow> replicate (length maskL) None \<in> X)
      then tuple_in else Mapping.empty) as"
      using proj_rep[OF keys_wf_in]
      by (auto simp add: Mapping.lookup_filter proj_tuple_in_join_def
          Mapping_keys_intro split: option.splits)
    then have filter_in: "Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_in =
      (if (pos \<longleftrightarrow> replicate (length maskL) None \<in> X) then tuple_in else Mapping.empty)"
      by (auto intro!: mapping_eqI)
    have "\<And>as. Mapping.lookup (Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X)
      tuple_since) as = Mapping.lookup (if (pos \<longleftrightarrow> replicate (length maskL) None \<in> X)
      then tuple_since else Mapping.empty) as"
      using proj_rep[OF keys_wf_since]
      by (auto simp add: Mapping.lookup_filter proj_tuple_in_join_def
          Mapping_keys_intro split: option.splits)
    then have filter_since: "Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_since =
      (if (pos \<longleftrightarrow> replicate (length maskL) None \<in> X) then tuple_since else Mapping.empty)"
      by (auto intro!: mapping_eqI)
    show ?thesis
      using True
      by (auto simp: Let_def pos_def[symmetric] filter_in filter_since table_in_def wf_table_sig_args
          sig_in set_in set_args_in sig_since set_since set_args_since intro!: wf_table_eqI)
  next
    case False
    define wf_X where "wf_X = wf_table_of_idx (wf_idx_of_set (args_n args) (args_L args) (args_L args) X)"
    define wf_in_del where "wf_in_del = (if pos then wf_table_antijoin else wf_table_join) wf_table_in wf_X"
    define in_del where "in_del = wf_table_set wf_in_del"
    define tuple_in' where "tuple_in' = mapping_delete_set tuple_in in_del"
    define table_in' where "table_in' = table_in - in_del"
    define wf_table_in' where "wf_table_in' = wf_table_antijoin wf_table_in wf_in_del"
    define wf_since_del where "wf_since_del = (if pos then wf_table_antijoin else wf_table_join) wf_table_since wf_X"
    define since_del where "since_del = wf_table_set wf_since_del"
    define tuple_since' where "tuple_since' = mapping_delete_set tuple_since since_del"
    define wf_table_since' where "wf_table_since' = wf_table_antijoin wf_table_since wf_since_del"
    have wf_in_set: "wf_table_set wf_table_in = table_in"
      by (auto simp: set_in table_in_def)
    have wf_X_sig: "wf_table_sig wf_X = (args_n args, args_L args)"
      by (auto simp: wf_X_def wf_idx_sig_of_set)
    have wf_X_set: "wf_table_set wf_X = X"
      using table_left
      by (auto simp: wf_X_def wf_idx_set_of_set table_def)
    have wf_in_del_sig: "wf_table_sig wf_in_del = (args_n args, args_R args)"
      using L_R
      by (auto simp: wf_in_del_def wf_table_sig_join wf_table_sig_antijoin sig_in wf_X_sig)
    have in_del_set: "in_del = join table_in (\<not>pos) X"
      by (auto simp: in_del_def wf_in_del_def wf_table_set_antijoin[OF sig_in wf_X_sig L_R]
          wf_table_set_join[OF sig_in wf_X_sig refl] wf_in_set wf_X_set)
    have table_in': "Mapping.keys tuple_in' = table_in'"
      using keys_filter
      unfolding tuple_in'_def table_in'_def table_in_def[symmetric]
      by auto
    have wf_in'_sig: "wf_table_sig wf_table_in' = (args_n args, args_R args)"
      by (auto simp: wf_table_in'_def wf_table_sig_antijoin sig_in)
    have wf_in'_set: "wf_table_set wf_table_in' = table_in'"
      unfolding wf_table_in'_def table_in'_def wf_table_set_antijoin[OF sig_in wf_in_del_sig subset_refl]
        join_eq[OF wf_table_set_table[OF wf_in_del_sig] wf_table_set_table[OF sig_in]]
      unfolding wf_in_set in_del_def
      by auto
    have tuple_in': "Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_in = tuple_in'"
      unfolding tuple_in'_def
      by (cases pos) (auto simp: mapping_delete_set_def in_del_set table_in_def
          join_sub[OF L_R table_left table_table_in] maskL_def proj_tuple_in_join_def intro!: Mapping_filter_cong)
    have wf_since_del_sig: "wf_table_sig wf_since_del = (args_n args, args_R args)"
      using L_R
      by (auto simp: wf_since_del_def wf_table_sig_join wf_table_sig_antijoin sig_since wf_X_sig)
    have since_del_set: "since_del = join (Mapping.keys tuple_since) (\<not>pos) X"
      by (auto simp: since_del_def wf_since_del_def wf_table_set_antijoin[OF sig_since wf_X_sig L_R]
          wf_table_set_join[OF sig_since wf_X_sig refl] set_since wf_X_set)
    have wf_since'_sig: "wf_table_sig wf_table_since' = (args_n args, args_R args)"
      by (auto simp: wf_table_since'_def wf_table_sig_antijoin sig_since)
    have wf_since'_set: "wf_table_set wf_table_since' = Mapping.keys tuple_since'"
      unfolding wf_table_since'_def wf_table_set_antijoin[OF sig_since wf_since_del_sig subset_refl]
        join_eq[OF wf_table_set_table[OF wf_since_del_sig] wf_table_set_table[OF sig_since]]
      unfolding tuple_since'_def since_del_def set_since
      by auto
    have table_tuple_since': "table (args_n args) (args_R args) (Mapping.keys tuple_since')"
      using table_tuple_since
      by (auto simp: tuple_since'_def table_def)
    have tuple_since': "Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_since = tuple_since'"
      unfolding tuple_since'_def
      by (cases pos) (auto simp: mapping_delete_set_def since_del_set
          join_sub[OF L_R table_left table_tuple_since] maskL_def proj_tuple_in_join_def intro!: Mapping_filter_cong)
    show ?thesis
      using False
      by (auto simp only:join_mmsaux.simps join_mmsaux_abs.simps Let_def pos_def[symmetric] wf_X_def[symmetric]
          wf_in_del_def[symmetric] in_del_def[symmetric] tuple_in'_def[symmetric] table_in'_def[symmetric] wf_table_in'_def[symmetric]
          wf_since_del_def[symmetric] since_del_def[symmetric] tuple_since'_def[symmetric] wf_table_since'_def[symmetric]
          table_in' wf_in'_set[symmetric] wf_table_of_set_args_wf_table_set[OF wf_in'_sig] tuple_in'
          wf_since'_set[symmetric] wf_table_of_set_args_wf_table_set[OF wf_since'_sig] tuple_since' split: if_splits)
  qed
qed

lemma valid_join_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux args cur
    (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) auxlist"
  and table_left': "table (args_n args) (args_L args) X"
  shows "valid_mmsaux args cur
    (join_mmsaux args X (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since))
    (map (\<lambda>(t, rel). (t, join rel (args_pos args) X)) auxlist)"
proof -
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  note table_left = table_left'[unfolded n_def[symmetric] L_def[symmetric]]
  define tuple_in' where "tuple_in' \<equiv>
    Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_in"
  define tuple_since' where "tuple_since' \<equiv>
    Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_since"
  have tuple_in_None_None: "\<And>as. Mapping.lookup tuple_in as = None \<Longrightarrow>
    Mapping.lookup tuple_in' as = None"
    unfolding tuple_in'_def using Mapping_lookup_filter_not_None by fastforce
  have tuple_in'_keys: "\<And>as. as \<in> Mapping.keys tuple_in' \<Longrightarrow> as \<in> Mapping.keys tuple_in"
    using tuple_in_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping_keys_dest)
  have tuple_since_None_None: "\<And>as. Mapping.lookup tuple_since as = None \<Longrightarrow>
    Mapping.lookup tuple_since' as = None"
    unfolding tuple_since'_def using Mapping_lookup_filter_not_None by fastforce
  have tuple_since'_keys: "\<And>as. as \<in> Mapping.keys tuple_since' \<Longrightarrow> as \<in> Mapping.keys tuple_since"
    using tuple_since_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping_keys_dest)
  have ts_tuple_rel': "ts_tuple_rel (set (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist)) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since' tas}"
  proof (rule set_eqI, rule iffI)
    fix tas
    assume assm: "tas \<in> ts_tuple_rel (set (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist))"
    then obtain t as Z where tas_def: "tas = (t, as)" "as \<in> join Z pos X" "(t, Z) \<in> set auxlist"
      "(t, join Z pos X) \<in> set (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist)"
      by (fastforce simp add: ts_tuple_rel_def)
    from tas_def(3) have table_Z: "table n R Z"
      using valid_before by (auto simp add: n_def R_def)
    have proj: "as \<in> Z" "proj_tuple_in_join pos maskL as X"
      using tas_def(2) join_sub[OF _ table_left table_Z] valid_before
      by (auto simp add: n_def L_def R_def pos_def)
    then have "(t, as) \<in> ts_tuple_rel (set (auxlist))"
      using tas_def(3) by (auto simp add: ts_tuple_rel_def)
    then have tas_in: "(t, as) \<in> ts_tuple_rel
      (set (linearize data_prev) \<union> set (linearize data_in))" "valid_tuple tuple_since (t, as)"
      using valid_before by auto
    then obtain t' where t'_def: "Mapping.lookup tuple_since as = Some t'" "t \<ge> t'"
      by (auto simp add: valid_tuple_def split: option.splits)
    then have valid_tuple_since': "valid_tuple tuple_since' (t, as)"
      using proj(2)
      by (auto simp add: tuple_since'_def Mapping_lookup_filter_Some valid_tuple_def)
    show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
      valid_tuple tuple_since' tas}"
      using tas_in valid_tuple_since' unfolding tas_def(1)[symmetric] by auto
  next
    fix tas
    assume assm: "tas \<in> {tas \<in> ts_tuple_rel
      (set (linearize data_prev) \<union> set (linearize data_in)). valid_tuple tuple_since' tas}"
    then obtain t as where tas_def: "tas = (t, as)" "valid_tuple tuple_since' (t, as)"
      by (auto simp add: ts_tuple_rel_def)
    from tas_def(2) have "valid_tuple tuple_since (t, as)"
      unfolding tuple_since'_def using Mapping_lookup_filter_not_None
      by (force simp add: valid_tuple_def split: option.splits)
    then have "(t, as) \<in> ts_tuple_rel (set auxlist)"
      using valid_before assm tas_def(1) by auto
    then obtain Z where Z_def: "as \<in> Z" "(t, Z) \<in> set auxlist"
      by (auto simp add: ts_tuple_rel_def)
    then have table_Z: "table n R Z"
      using valid_before by (auto simp add: n_def R_def)
    from tas_def(2) have "proj_tuple_in_join pos maskL as X"
      unfolding tuple_since'_def using Mapping_lookup_filter_Some_P
      by (fastforce simp add: valid_tuple_def split: option.splits)
    then have as_in_join: "as \<in> join Z pos X"
      using join_sub[OF _ table_left table_Z] Z_def(1) valid_before
      by (auto simp add: n_def L_def R_def pos_def)
    then show "tas \<in> ts_tuple_rel (set (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist))"
      using Z_def unfolding tas_def(1) by (auto simp add: ts_tuple_rel_def)
  qed
  have lookup_tuple_in': "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since' tas \<and> as = snd tas})"
  proof -
    fix as
    show "Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since' tas \<and> as = snd tas})"
    proof (cases "Mapping.lookup tuple_in as")
      case None
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas} = {}"
        using valid_before by (auto dest!: safe_max_empty_dest)
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since' tas \<and> as = snd tas} = {}"
        using Mapping_lookup_filter_not_None
        by (fastforce simp add: valid_tuple_def tuple_since'_def split: option.splits)
      then show ?thesis
        unfolding tuple_in_None_None[OF None] using iffD2[OF safe_max_empty, symmetric] by blast
    next
      case (Some t)
      show ?thesis
      proof (cases "proj_tuple_in_join pos maskL as X")
        case True
        then have lookup_tuple_in': "Mapping.lookup tuple_in' as = Some t"
          using Some unfolding tuple_in'_def by (simp add: Mapping_lookup_filter_Some)
        have "(t, as) \<in> ts_tuple_rel (set (linearize data_in))" "valid_tuple tuple_since (t, as)"
          using valid_before Some by (auto dest: safe_max_Some_dest_in[OF finite_fst_ts_tuple_rel])
        then have t_in_fst: "t \<in> fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
          valid_tuple tuple_since' tas \<and> as = snd tas}"
          using True by (auto simp add: image_iff valid_tuple_def tuple_since'_def
            Mapping_lookup_filter_Some split: option.splits)
        have "\<And>t'. valid_tuple tuple_since' (t', as) \<Longrightarrow> valid_tuple tuple_since (t', as)"
          using Mapping_lookup_filter_not_None
          by (fastforce simp add: valid_tuple_def tuple_since'_def split: option.splits)
        then have "\<And>t'. (t', as) \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
          valid_tuple tuple_since' (t', as) \<Longrightarrow> t' \<le> t"
          using valid_before Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff)
        then have "Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
          valid_tuple tuple_since' tas \<and> as = snd tas}) = t"
          using Max_eqI[OF finite_fst_ts_tuple_rel[of "linearize data_in"],
            OF _ t_in_fst] by fastforce
        then show ?thesis
          unfolding lookup_tuple_in' using t_in_fst by (auto simp add: safe_max_def)
      next
        case False
        then have lookup_tuple': "Mapping.lookup tuple_in' as = None"
          "Mapping.lookup tuple_since' as = None"
          unfolding tuple_in'_def tuple_since'_def
          by (auto simp add: Mapping_lookup_filter_None)
        then have "\<And>tas. \<not>(valid_tuple tuple_since' tas \<and> as = snd tas)"
          by (auto simp add: valid_tuple_def split: option.splits)
        then show ?thesis
          unfolding lookup_tuple' by (auto simp add: safe_max_def)
      qed
    qed
  qed
  have table_join': "\<And>t ys. (t, ys) \<in> set auxlist \<Longrightarrow> table n R (join ys pos X)"
  proof -
    fix t ys
    assume "(t, ys) \<in> set auxlist"
    then have table_ys: "table n R ys"
      using valid_before
      by (auto simp add: n_def L_def R_def pos_def)
    show "table n R (join ys pos X)"
      using join_table[OF table_ys table_left, of pos R] valid_before
      by (auto simp add: n_def L_def R_def pos_def)
  qed
  have table_in': "table n R (Mapping.keys tuple_in')"
    using tuple_in'_keys valid_before
    by (auto simp add: n_def L_def R_def pos_def table_def)
  have table_since': "table n R (Mapping.keys tuple_since')"
    using tuple_since'_keys valid_before
    by (auto simp add: n_def L_def R_def pos_def table_def)
  show ?thesis
    unfolding join_mmsaux_abs_eq[OF valid_before table_left']
    using valid_before ts_tuple_rel' lookup_tuple_in' tuple_in'_def tuple_since'_def table_join'
      Mapping_filter_keys[of tuple_since "\<lambda>as. case as of Some t \<Rightarrow> t \<le> nt"]
      table_in' wf_table_of_set_args[OF table_in'[unfolded n_def R_def]]
      table_since' wf_table_of_set_args[OF table_since'[unfolded n_def R_def]]
    by (auto simp add: n_def L_def R_def pos_def table_def Let_def wf_table_sig_args)
qed

lemma valid_join_mmsaux: "valid_mmsaux args cur aux auxlist \<Longrightarrow>
  table (args_n args) (args_L args) X \<Longrightarrow> valid_mmsaux args cur
  (join_mmsaux args X aux) (map (\<lambda>(t, rel). (t, join rel (args_pos args) X)) auxlist)"
  using valid_join_mmsaux_unfolded by (cases aux) fast

fun gc_mmsaux :: "args \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "gc_mmsaux args (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    (let all_tuples = \<Union>(snd ` (set (linearize data_prev) \<union> set (linearize data_in)));
    tuple_since' = Mapping.filter (\<lambda>as _. as \<in> all_tuples) tuple_since in
    (nt, nt, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in,
     wf_table_of_set_args args (Mapping.keys tuple_since'), tuple_since'))"

lemma valid_gc_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux args cur (nt, gc, maskL, maskR, data_prev, data_in,
    table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) ys"
  shows "valid_mmsaux args cur (gc_mmsaux args (nt, gc, maskL, maskR, data_prev, data_in,
    table_in, wf_table_in, tuple_in, wf_table_since, tuple_since)) ys"
proof -
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  define all_tuples where "all_tuples \<equiv> \<Union>(snd ` (set (linearize data_prev) \<union>
    set (linearize data_in)))"
  define tuple_since' where "tuple_since' \<equiv> Mapping.filter (\<lambda>as _. as \<in> all_tuples) tuple_since"
  have tuple_since_None_None: "\<And>as. Mapping.lookup tuple_since as = None \<Longrightarrow>
    Mapping.lookup tuple_since' as = None"
    unfolding tuple_since'_def using Mapping_lookup_filter_not_None by fastforce
  have tuple_since'_keys: "\<And>as. as \<in> Mapping.keys tuple_since' \<Longrightarrow> as \<in> Mapping.keys tuple_since"
    using tuple_since_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping_keys_dest)
  then have table_since': "table n R (Mapping.keys tuple_since')"
    using valid_before by (auto simp add: table_def n_def R_def)
  have data_cong: "\<And>tas. tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
    set (linearize data_in)) \<Longrightarrow> valid_tuple tuple_since' tas = valid_tuple tuple_since tas"
  proof -
    fix tas
    assume assm: "tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
    set (linearize data_in))"
    define t where "t \<equiv> fst tas"
    define as where "as \<equiv> snd tas"
    have "as \<in> all_tuples"
      using assm by (force simp add: as_def all_tuples_def ts_tuple_rel_def)
    then have "Mapping.lookup tuple_since' as = Mapping.lookup tuple_since as"
      by (auto simp add: tuple_since'_def Mapping.lookup_filter split: option.splits)
    then show "valid_tuple tuple_since' tas = valid_tuple tuple_since tas"
      by (auto simp add: valid_tuple_def as_def split: option.splits) metis
  qed
  then have data_in_cong: "\<And>tas. tas \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
    valid_tuple tuple_since' tas = valid_tuple tuple_since tas"
    by (auto simp add: ts_tuple_rel_Un)
  have "ts_tuple_rel (set ys) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since' tas}"
    using data_cong valid_before by auto
  moreover have "(\<forall>as. Mapping.lookup tuple_in as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since' tas \<and> as = snd tas}))"
    using valid_before by auto (meson data_in_cong)
  moreover have "(\<forall>as \<in> Mapping.keys tuple_since'. case Mapping.lookup tuple_since' as of
    Some t \<Rightarrow> t \<le> nt)"
    using Mapping.keys_filter valid_before
    by (auto simp add: tuple_since'_def Mapping.lookup_filter split: option.splits
        intro!: Mapping_keys_intro dest: Mapping_keys_dest)
  ultimately show ?thesis
    using all_tuples_def tuple_since'_def valid_before table_since'
      wf_table_of_set_args[OF table_since'[unfolded n_def R_def]]
    by (auto simp add: n_def R_def Let_def wf_table_sig_args)
qed

lemma valid_gc_mmsaux: "valid_mmsaux args cur aux ys \<Longrightarrow> valid_mmsaux args cur (gc_mmsaux args aux) ys"
  using valid_gc_mmsaux_unfolded by (cases aux) fast

fun gc_join_mmsaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "gc_join_mmsaux args X (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    (if \<not> memR (args_ivl args) (t - gc) then join_mmsaux args X (gc_mmsaux args (t, gc, maskL, maskR,
      data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since))
    else join_mmsaux args X (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since))"

lemma gc_join_mmsaux_alt: "gc_join_mmsaux args rel1 aux = join_mmsaux args rel1 (gc_mmsaux args aux) \<or>
  gc_join_mmsaux args rel1 aux = join_mmsaux args rel1 aux"
  by (cases aux) (auto simp only: gc_join_mmsaux.simps split: if_splits)

lemma valid_gc_join_mmsaux:
  assumes "valid_mmsaux args cur aux auxlist" "table (args_n args) (args_L args) rel1"
  shows "valid_mmsaux args cur (gc_join_mmsaux args rel1 aux)
    (map (\<lambda>(t, rel). (t, join rel (args_pos args) rel1)) auxlist)"
  using gc_join_mmsaux_alt[of args rel1 aux]
  using valid_join_mmsaux[OF valid_gc_mmsaux[OF assms(1)] assms(2)]
    valid_join_mmsaux[OF assms]
  by auto

definition "minus_keys X m = X - Mapping.keys m"

lemma minus_keys_code[code]: "minus_keys X m = {x \<in> X. case Mapping.lookup m x of None \<Rightarrow> True | _ \<Rightarrow> False}"
  by (auto simp: minus_keys_def Mapping.keys_dom_lookup split: option.splits)

fun add_new_table_mmsaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_table_mmsaux args X (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    (let X' = (minus_keys X tuple_since);
         wf_table_since' = wf_table_union wf_table_since (wf_table_of_set_args args X');
         tuple_since' = upd_set tuple_since (\<lambda>_. t) X' in
    (if memL (args_ivl args) 0 then
      (t, gc, maskL, maskR, data_prev, append_queue (t, X) data_in, table_in \<union> X, wf_table_union wf_table_in (wf_table_of_set_args args X), upd_set tuple_in (\<lambda>_. t) X, wf_table_since', tuple_since')
    else (t, gc, maskL, maskR, append_queue (t, X) data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since', tuple_since')))"

lemma valid_add_new_table_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux args cur
    (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) auxlist"
  and table_X: "table (args_n args) (args_R args) X"
  shows "valid_mmsaux args cur (add_new_table_mmsaux args X
    (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since))
    (case auxlist of
      [] => [(cur, X)]
    | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> X) # ts else (cur, X) # auxlist)"
proof -
  have cur_nt: "cur = nt"
    using valid_before by auto
  define I where "I = args_ivl args"
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  define tuple_in' where "tuple_in' \<equiv> upd_set tuple_in (\<lambda>_. nt) X"
  define X' where "X' \<equiv> X - Mapping.keys tuple_since"
  define wf_table_since' where "wf_table_since' \<equiv> wf_table_union wf_table_since (wf_table_of_set_args args X')"
  define tuple_since' where "tuple_since' \<equiv> upd_set tuple_since (\<lambda>_. nt) X'"
  define data_prev' where "data_prev' \<equiv> append_queue (nt, X) data_prev"
  define data_in' where "data_in' \<equiv> append_queue (nt, X) data_in"
  define auxlist' where "auxlist' \<equiv> (case auxlist of
    [] => [(nt, X)]
    | ((t, y) # ts) \<Rightarrow> if t = nt then (t, y \<union> X) # ts else (nt, X) # auxlist)"
  have table_in': "table n R (Mapping.keys tuple_in')"
    using table_X valid_before
    by (auto simp add: table_def tuple_in'_def Mapping_upd_set_keys n_def R_def)
  have table_since': "table n R (Mapping.keys tuple_since')"
    using table_X valid_before
    by (auto simp add: table_def tuple_since'_def Mapping_upd_set_keys n_def R_def X'_def)
  have tuple_since'_keys: "Mapping.keys tuple_since \<subseteq> Mapping.keys tuple_since'"
    using Mapping_upd_set_keys by (fastforce simp add: tuple_since'_def)
  have lin_data_prev': "linearize data_prev' = linearize data_prev @ [(nt, X)]"
    unfolding data_prev'_def append_queue_rep ..
  have wf_data_prev': "\<And>as. as \<in> \<Union>(snd ` (set (linearize data_prev'))) \<Longrightarrow> wf_tuple n R as"
    unfolding lin_data_prev' using table_X valid_before
    by (auto simp add: table_def n_def R_def)
  have lin_data_in': "linearize data_in' = linearize data_in @ [(nt, X)]"
    unfolding data_in'_def append_queue_rep ..
  have table_auxlist': "\<forall>(t, X) \<in> set auxlist'. table n R X"
    using table_X table_Un valid_before
    by (auto simp add: auxlist'_def n_def R_def split: list.splits if_splits)
  have lookup_tuple_since': "\<forall>as \<in> Mapping.keys tuple_since'.
    case Mapping.lookup tuple_since' as of Some t \<Rightarrow> t \<le> nt"
    unfolding tuple_since'_def using valid_before Mapping_lookup_upd_set[of tuple_since]
    by (auto dest: Mapping_keys_dest intro!: Mapping_keys_intro split: if_splits option.splits)
  have ts_tuple_rel_auxlist': "ts_tuple_rel (set auxlist') =
    ts_tuple_rel (set auxlist) \<union> ts_tuple_rel {(nt, X)}"
    unfolding auxlist'_def
    using ts_tuple_rel_ext ts_tuple_rel_ext' ts_tuple_rel_ext_Cons ts_tuple_rel_ext_Cons'
    by (fastforce simp: ts_tuple_rel_def split: list.splits if_splits)
  have valid_tuple_nt_X: "\<And>tas. tas \<in> ts_tuple_rel {(nt, X)} \<Longrightarrow> valid_tuple tuple_since' tas"
    using valid_before by (auto simp add: X'_def ts_tuple_rel_def valid_tuple_def tuple_since'_def
        Mapping_lookup_upd_set dest: Mapping_keys_dest split: option.splits)
  have valid_tuple_mono: "\<And>tas. valid_tuple tuple_since tas \<Longrightarrow> valid_tuple tuple_since' tas"
    by (auto simp add: X'_def valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
        intro: Mapping_keys_intro split: option.splits)
  have ts_tuple_rel_auxlist': "ts_tuple_rel (set auxlist') =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in) \<union> {(nt, X)}).
    valid_tuple tuple_since' tas}"
  proof (rule set_eqI, rule iffI)
    fix tas
    assume assm: "tas \<in> ts_tuple_rel (set auxlist')"
    show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
      set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
      using assm[unfolded ts_tuple_rel_auxlist' ts_tuple_rel_Un]
    proof (rule UnE)
      assume assm: "tas \<in> ts_tuple_rel (set auxlist)"
      then have "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in)). valid_tuple tuple_since tas}"
        using valid_before by auto
      then show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
        using assm by (auto simp only: ts_tuple_rel_Un intro: valid_tuple_mono)
    next
      assume assm: "tas \<in> ts_tuple_rel {(nt, X)}"
      show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
        using assm valid_before by (auto simp add: X'_def ts_tuple_rel_Un tuple_since'_def
            valid_tuple_def Mapping_lookup_upd_set ts_tuple_rel_def dest: Mapping_keys_dest
            split: option.splits if_splits)
    qed
  next
    fix tas
    assume assm: "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
      set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
    then have "tas \<in> (ts_tuple_rel (set (linearize data_prev) \<union>
      set (linearize data_in)) - ts_tuple_rel {(nt, X)}) \<union> ts_tuple_rel {(nt, X)}"
      by (auto simp only: ts_tuple_rel_Un)
    then show "tas \<in> ts_tuple_rel (set auxlist')"
    proof (rule UnE)
      assume assm': "tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in)) - ts_tuple_rel {(nt, X)}"
      then have tas_in: "tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in))"
        by (auto simp only: ts_tuple_rel_def)
      obtain t as where tas_def: "tas = (t, as)"
        by (cases tas) auto
      have "t \<in> fst ` (set (linearize data_prev) \<union> set (linearize data_in))"
        using assm' unfolding tas_def by (force simp add: ts_tuple_rel_def)
      then have t_le_nt: "t \<le> nt"
        using valid_before by auto
      have valid_tas: "valid_tuple tuple_since' tas"
        using assm by auto
      have "valid_tuple tuple_since tas"
      proof (cases "as \<in> Mapping.keys tuple_since")
        case True
        then show ?thesis
          using valid_tas tas_def by (auto simp add: X'_def valid_tuple_def tuple_since'_def
              Mapping_lookup_upd_set split: option.splits if_splits)
      next
        case False
        then have "t = nt" "as \<in> X"
          using valid_tas t_le_nt unfolding tas_def
          by (auto simp add: X'_def valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
              intro: Mapping_keys_intro split: option.splits if_splits)
        then have "False"
          using assm' unfolding tas_def ts_tuple_rel_def by (auto simp only: ts_tuple_rel_def)
        then show ?thesis
          by simp
      qed
      then show "tas \<in> ts_tuple_rel (set auxlist')"
        using tas_in valid_before by (auto simp add: ts_tuple_rel_auxlist')
    qed (auto simp only: ts_tuple_rel_auxlist')
  qed
  have table_since: "table (args_n args) (args_R args) (Mapping.keys tuple_since)"
    using valid_before by (auto simp add: table_def)
  have keys_tuple_since': "Mapping.keys tuple_since \<union> X' = Mapping.keys tuple_since'"
    using valid_before
    by (auto simp: tuple_since'_def Mapping_upd_set_keys)
  have sig_since: "wf_table_sig wf_table_since = (args_n args, args_R args)"
    and set_since: "wf_table_set wf_table_since = Mapping.keys tuple_since"
    using valid_before
    by auto
  have sig_since'': "wf_table_sig (wf_table_union wf_table_since (wf_table_of_set_args args X')) = (args_n args, args_R args)"
    and sig_since: "wf_table_sig wf_table_since = (args_n args, args_R args)"
    and keys_since: "wf_table_set wf_table_since = Mapping.keys tuple_since"
    using valid_before
    by (auto simp: wf_table_sig_union wf_table_sig_args)
  have table_X': "table (args_n args) (args_R args) X'"
    using assms(2)
    by (auto simp: X'_def table_def)
  have keys_tuple_since'': "wf_table_set (wf_table_union wf_table_since (wf_table_of_set_args args X')) = Mapping.keys tuple_since'"
    by (auto simp: keys_tuple_since'[symmetric] set_since[symmetric]
        wf_table_set_union[OF trans[OF sig_since wf_table_sig_args[symmetric]]]
        wf_table_of_set_args[OF table_X'])
  have table_in: "table (args_n args) (args_R args) (Mapping.keys tuple_in)"
    using valid_before by (auto simp add: table_def)
  have keys_tuple_in: "table_in = Mapping.keys tuple_in"
    using valid_before
    by auto
  have keys_tuple_in': "table_in \<union> X = Mapping.keys tuple_in'"
    using valid_before
    by (auto simp: tuple_in'_def Mapping_upd_set_keys)
  have sig_in: "wf_table_sig wf_table_in = (args_n args, args_R args)"
    and set_in: "wf_table_set wf_table_in = Mapping.keys tuple_in"
    using valid_before
    by auto
  have sig_in'': "wf_table_sig (wf_table_union wf_table_in (wf_table_of_set_args args X)) = (args_n args, args_R args)"
    and sig_since: "wf_table_sig wf_table_since = (args_n args, args_R args)"
    and keys_since: "wf_table_set wf_table_since = Mapping.keys tuple_since"
    using valid_before
    by (auto simp: wf_table_sig_union wf_table_sig_args)
  have keys_tuple_in'': "wf_table_set (wf_table_union wf_table_in (wf_table_of_set_args args X)) = Mapping.keys tuple_in'"
    by (auto simp: keys_tuple_in keys_tuple_in'[symmetric] set_in[symmetric]
        wf_table_set_union[OF trans[OF sig_in wf_table_sig_args[symmetric]]]
        wf_table_of_set_args[OF table_X])
  show ?thesis
  proof (cases "memL I 0")
    case True
    then have add_def: "add_new_table_mmsaux args X (nt, gc, maskL, maskR, data_prev, data_in,
      table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) = (nt, gc, maskL, maskR, data_prev, data_in',
      table_in \<union> X, wf_table_union wf_table_in (wf_table_of_set_args args X), tuple_in', wf_table_since', tuple_since')"
      using data_in'_def tuple_in'_def tuple_since'_def
      by (auto simp: Let_def I_def minus_keys_def wf_table_since'_def X'_def)
    have "\<forall>t \<in> fst ` set (linearize data_in'). t \<le> nt \<and> memL I (nt - t)"
      using valid_before True by (auto simp add: lin_data_in')
    moreover have "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
      {tas \<in> ts_tuple_rel (set (linearize data_in')).
      valid_tuple tuple_since' tas \<and> as = snd tas})"
    proof -
      fix as
      show "Mapping.lookup tuple_in' as = safe_max (fst `
        {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since' tas \<and> as = snd tas})"
      proof (cases "as \<in> X")
        case True
        have "valid_tuple tuple_since' (nt, as)"
          using True valid_before by (auto simp add: X'_def valid_tuple_def tuple_since'_def
              Mapping_lookup_upd_set dest: Mapping_keys_dest split: option.splits)
        moreover have "(nt, as) \<in> ts_tuple_rel (insert (nt, X) (set (linearize data_in)))"
          using True by (auto simp add: ts_tuple_rel_def)
        ultimately have nt_in: "nt \<in> fst ` {tas \<in> ts_tuple_rel (insert (nt, X)
          (set (linearize data_in))). valid_tuple tuple_since' tas \<and> as = snd tas}"
        proof -
          assume a1: "valid_tuple tuple_since' (nt, as)"
          assume "(nt, as) \<in> ts_tuple_rel (insert (nt, X) (set (linearize data_in)))"
          then have "\<exists>p. nt = fst p \<and> p \<in> ts_tuple_rel (insert (nt, X)
            (set (linearize data_in))) \<and> valid_tuple tuple_since' p \<and> as = snd p"
            using a1 by simp
          then show "nt \<in> fst ` {p \<in> ts_tuple_rel (insert (nt, X) (set (linearize data_in))).
            valid_tuple tuple_since' p \<and> as = snd p}"
            by blast
        qed
        moreover have "\<And>t. t \<in> fst ` {tas \<in> ts_tuple_rel (insert (nt, X)
          (set (linearize data_in))). valid_tuple tuple_since' tas \<and> as = snd tas} \<Longrightarrow> t \<le> nt"
          using valid_before by (auto split: option.splits)
            (metis (no_types, lifting) eq_imp_le fst_conv insertE ts_tuple_rel_dest)
        ultimately have "Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)
          \<union> set [(nt, X)]). valid_tuple tuple_since' tas \<and> as = snd tas}) = nt"
          using Max_eqI[OF finite_fst_ts_tuple_rel[of "linearize data_in'"],
              unfolded lin_data_in' set_append] by auto
        then show ?thesis
          using nt_in True
          by (auto simp add: tuple_in'_def Mapping_lookup_upd_set safe_max_def lin_data_in')
      next
        case False
        have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
          valid_tuple tuple_since tas \<and> as = snd tas} =
          {tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since' tas \<and> as = snd tas}"
          using False by (fastforce simp add: X'_def lin_data_in' ts_tuple_rel_def valid_tuple_def
              tuple_since'_def Mapping_lookup_upd_set intro: Mapping_keys_intro
              split: option.splits if_splits)
        then show ?thesis
          using valid_before False by (auto simp add: tuple_in'_def Mapping_lookup_upd_set)
      qed
    qed
    ultimately show ?thesis
      using assms table_auxlist' sorted_append[of "map fst (linearize data_in)"]
        lookup_tuple_since' ts_tuple_rel_auxlist'
        table_in' keys_tuple_in' sig_in'' keys_tuple_in''
        table_since' keys_tuple_since' sig_since'' keys_tuple_since''
      unfolding add_def auxlist'_def[symmetric] wf_table_since'_def[symmetric] cur_nt I_def
      by (auto simp only: valid_mmsaux.simps lin_data_in' n_def R_def) (auto simp: table_def)
  next
    case False
    then have add_def: "add_new_table_mmsaux args X (nt, gc, maskL, maskR, data_prev, data_in,
      table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) = (nt, gc, maskL, maskR, data_prev', data_in,
      table_in, wf_table_in, tuple_in, wf_table_since', tuple_since')"
      using data_prev'_def tuple_since'_def unfolding I_def by (auto simp: Let_def minus_keys_def X'_def wf_table_since'_def)
    have "\<forall>t \<in> fst ` set (linearize data_prev'). t \<le> nt \<and> \<not> memL I (nt - t)"
      using valid_before False by (auto simp add: lin_data_prev' I_def)
    moreover have "\<And>as. {tas \<in> ts_tuple_rel (set (linearize data_in)).
      valid_tuple tuple_since tas \<and> as = snd tas} =
      {tas \<in> ts_tuple_rel (set (linearize data_in)).
      valid_tuple tuple_since' tas \<and> as = snd tas}"
    proof (rule set_eqI, rule iffI)
      fix as tas
      assume assm: "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since' tas \<and> as = snd tas}"
      then obtain t Z where Z_def: "tas = (t, as)" "as \<in> Z" "(t, Z) \<in> set (linearize data_in)"
        "valid_tuple tuple_since' (t, as)"
        by (auto simp add: ts_tuple_rel_def)
      show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas}"
      using assm
      proof (cases "as \<in> Mapping.keys tuple_since")
        case False
        then have "t \<ge> nt"
          using Z_def(4) by (auto simp add: valid_tuple_def tuple_since'_def
              Mapping_lookup_upd_set intro: Mapping_keys_intro split: option.splits if_splits)
        then show ?thesis
          using Z_def(3) valid_before \<open>\<not> memL I 0\<close> unfolding I_def by auto
      qed (auto simp add: X'_def valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
           dest: Mapping_keys_dest split: option.splits)
    qed (auto simp add: X'_def Mapping_lookup_upd_set valid_tuple_def tuple_since'_def
         intro: Mapping_keys_intro split: option.splits)
    ultimately show ?thesis
      using assms table_auxlist' sorted_append[of "map fst (linearize data_prev)"]
        False lookup_tuple_since' ts_tuple_rel_auxlist' wf_data_prev'
        valid_before table_since' keys_tuple_since' sig_since'' keys_tuple_since'' table_in'
      unfolding add_def auxlist'_def[symmetric] wf_table_since'_def[symmetric] cur_nt I_def n_def R_def
        valid_mmsaux.simps
      by (fastforce simp: lin_data_prev') (* SLOW *)
  qed
qed

lemma valid_add_new_table_mmsaux:
  assumes valid_before: "valid_mmsaux args cur aux auxlist"
  and table_X: "table (args_n args) (args_R args) X"
  shows "valid_mmsaux args cur (add_new_table_mmsaux args X aux)
    (case auxlist of
      [] => [(cur, X)]
    | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> X) # ts else (cur, X) # auxlist)"
  using valid_add_new_table_mmsaux_unfolded assms
  by (cases aux) fast

lemma foldr_ts_tuple_rel:
  "as \<in> foldr (\<union>) (concat (map (\<lambda>(t, rel). if P t then [rel] else []) auxlist)) {} \<longleftrightarrow>
  (\<exists>t. (t, as) \<in> ts_tuple_rel (set auxlist) \<and> P t)"
  by (auto simp: foldr_union ts_tuple_rel_def)

lemma image_snd: "(a, b) \<in> X \<Longrightarrow> b \<in> snd ` X"
  by force

fun result_mmsaux :: "args \<Rightarrow> 'a mmsaux \<Rightarrow> 'a table" where
  "result_mmsaux args (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) = table_in"

lemma valid_result_mmsaux_unfolded:
  assumes "valid_mmsaux args cur
    (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) auxlist"
  shows "result_mmsaux args (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {}"
proof -
  have res: "result_mmsaux args (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    snd ` {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since tas}"
    using assms valid_mmsaux_tuple_in_keys[OF assms]
    by auto
  have ts_tuple_rel_in: "(a, b) \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow> memL (args_ivl args) (cur - a)" for a b
    using assms
    by (auto dest!: ts_tuple_rel_dest)
  have ts_tuple_rel_prev: "(a, b) \<in> ts_tuple_rel (set (linearize data_prev)) \<Longrightarrow> \<not>memL (args_ivl args) (cur - a)" for a b
    using assms
    by (auto dest!: ts_tuple_rel_dest)
  have ts_tuple_rel_auxlist: "ts_tuple_rel (set auxlist) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since tas}"
    using assms
    by auto
  show ?thesis
    using ts_tuple_rel_in ts_tuple_rel_prev
    by (auto simp del: result_mmsaux.simps simp: res foldr_ts_tuple_rel ts_tuple_rel_auxlist
        ts_tuple_rel_Un image_snd)+
qed

lemma valid_result_mmsaux: "valid_mmsaux args cur aux auxlist \<Longrightarrow>
  result_mmsaux args aux = foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {}"
  using valid_result_mmsaux_unfolded by (cases aux) fast

definition "result_mmsaux' args aux = eval_args_agg args (result_mmsaux args aux)"

lemma valid_result_mmsaux': "valid_mmsaux args cur aux auxlist \<Longrightarrow>
  result_mmsaux' args aux =
  eval_args_agg args (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {})"
  by (simp add: result_mmsaux'_def valid_result_mmsaux)

interpretation default_msaux: msaux valid_mmsaux init_mmsaux add_new_ts_mmsaux gc_join_mmsaux
  add_new_table_mmsaux result_mmsaux'
  using valid_init_mmsaux valid_add_new_ts_mmsaux valid_gc_join_mmsaux valid_add_new_table_mmsaux
    valid_result_mmsaux'
  by unfold_locales assumption+

subsection \<open>Optimized data structure for Until\<close>

type_synonym tp = nat

type_synonym 'a mmuaux = "tp \<times> ts queue \<times> ('a table \<times> (ts + tp)) queue \<times> nat \<times> bool list \<times> bool list \<times>
  'a table \<times> ('a tuple, tp) mapping \<times> (tp, ('a tuple, ts + tp) mapping) mapping \<times> (tp, ts) mapping \<times> 'a table list"

definition tstp_lt :: "ts + tp \<Rightarrow> ts \<Rightarrow> tp \<Rightarrow> bool" where
  "tstp_lt tstp ts tp = case_sum (\<lambda>ts'. ts' \<le> ts) (\<lambda>tp'. tp' < tp) tstp"

definition ts_tp_lt :: " \<I> \<Rightarrow> ts \<Rightarrow> tp \<Rightarrow> ts + tp \<Rightarrow> bool" where
  "ts_tp_lt I ts tp tstp = case_sum (\<lambda>ts'. memL I (ts' - ts)) (\<lambda>tp'. tp \<le> tp') tstp"

definition tstp_unpack:: "ts + tp \<Rightarrow> nat" where
  "tstp_unpack tstp = case_sum id id tstp"

fun max_tstp :: "ts + tp \<Rightarrow> ts + tp \<Rightarrow> ts + tp" where
  "max_tstp (Inl ts) (Inl ts') = Inl (max ts ts')"
| "max_tstp (Inr tp) (Inr tp') = Inr (max tp tp')"
| "max_tstp (Inl ts) _ = Inl ts"
| "max_tstp _ (Inl ts) = Inl ts"

lemma max_tstp_idem: "max_tstp (max_tstp x y) y = max_tstp x y"
  by (cases x; cases y) auto

lemma max_tstp_idem': "max_tstp x (max_tstp x y) = max_tstp x y"
  by (cases x; cases y) auto

lemma max_tstp_d_d: "max_tstp d d = d"
  by (cases d) auto

lemma max_cases: "(max a b = a \<Longrightarrow> P) \<Longrightarrow> (max a b = b \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis max_def)

lemma max_tstpE: "isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow> (max_tstp tstp tstp' = tstp \<Longrightarrow> P) \<Longrightarrow>
  (max_tstp tstp tstp' = tstp' \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases tstp; cases tstp') (auto elim: max_cases)

lemma max_tstp_intro: "tstp_lt tstp ts tp \<Longrightarrow> tstp_lt tstp' ts tp \<Longrightarrow> isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow>
  tstp_lt (max_tstp tstp tstp') ts tp"
  by (auto simp add: tstp_lt_def max_def split: sum.splits)

lemma max_tstp_intro': "isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow>
  ts_tp_lt I ts' tp' tstp \<Longrightarrow> ts_tp_lt I ts' tp' (max_tstp tstp tstp')"
  by (cases tstp; cases tstp') (auto 0 3 simp add: ts_tp_lt_def max_def split: sum.splits)

lemma max_tstp_intro'': "isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow>
  ts_tp_lt I ts' tp' tstp' \<Longrightarrow> ts_tp_lt I ts' tp' (max_tstp tstp tstp')"
  by (cases tstp; cases tstp') (auto 0 3 simp add: ts_tp_lt_def max_def elim: contrapos_np split: sum.splits)

lemma max_tstp_isl: "isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow> isl (max_tstp tstp tstp') \<longleftrightarrow> isl tstp"
  by (cases tstp; cases tstp') auto

definition filter_a1_map :: "bool \<Rightarrow> tp \<Rightarrow> ('a tuple, tp) mapping \<Rightarrow> 'a table" where
  "filter_a1_map pos tp a1_map =
    {xs \<in> Mapping.keys a1_map. case Mapping.lookup a1_map xs of Some tp' \<Rightarrow>
    (pos \<longrightarrow> tp' \<le> tp) \<and> (\<not>pos \<longrightarrow> tp \<le> tp')}"

definition filter_a2_map :: "\<I> \<Rightarrow> ts \<Rightarrow> tp \<Rightarrow> (tp, ('a tuple, ts + tp) mapping) mapping \<Rightarrow>
  'a table" where
  "filter_a2_map I ts tp a2_map = {xs. \<exists>tp' \<le> tp. (case Mapping.lookup a2_map tp' of Some m \<Rightarrow>
    (case Mapping.lookup m xs of Some tstp \<Rightarrow> ts_tp_lt I ts tp tstp | _ \<Rightarrow> False)
    | _ \<Rightarrow> False)}"

definition ivl_restr_a2_map :: "\<I> \<Rightarrow> ts \<Rightarrow> tp \<Rightarrow> (tp, ('a tuple, ts + tp) mapping) mapping \<Rightarrow> bool" where
  "ivl_restr_a2_map I ts tp a2_map = (case Mapping.lookup a2_map tp of Some m \<Rightarrow>
    (\<forall>xs. (case Mapping.lookup m xs of Some tstp \<Rightarrow> ts_tp_lt I ts tp tstp |
                                                             _ \<Rightarrow> True))
    | _ \<Rightarrow> False)"

definition valid_tstp_map :: "ts \<Rightarrow> tp \<Rightarrow> (tp, ts) mapping \<Rightarrow> bool" where
  "valid_tstp_map ts tp tstp_map = (case Mapping.lookup tstp_map tp of
                                   Some ts' \<Rightarrow> ts = ts' |
                                   None \<Rightarrow> False)"

fun triple_eq_pair :: "('a \<times> 'b \<times> 'c) \<Rightarrow> ('a \<times> 'd) \<Rightarrow> ('d \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'd \<Rightarrow> 'c) \<Rightarrow> bool" where
  "triple_eq_pair (t, a1, a2) (ts', tp') f g \<longleftrightarrow> t = ts' \<and> a1 = f tp' \<and> a2 = g ts' tp'"


fun valid_mmuaux' :: "args \<Rightarrow> ts \<Rightarrow> ts \<Rightarrow> event_data mmuaux \<Rightarrow> event_data muaux \<Rightarrow> bool" where
  "valid_mmuaux' args cur dt (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done) auxlist \<longleftrightarrow>
    args_L args \<subseteq> args_R args \<and>
    maskL = join_mask (args_n args) (args_L args) \<and>
    maskR = join_mask (args_n args) (args_R args) \<and>
    len \<le> tp \<and>
    length (linearize tss) = len \<and> sorted (linearize tss) \<and>
    (\<forall>t \<in> set (linearize tss). t \<le> cur \<and> memR (args_ivl args) (cur - t)) \<and>
    table (args_n args) (args_L args) (Mapping.keys a1_map) \<and>
    Mapping.keys tstp_map = (if len > 0 then {tp - len..tp - 1} else {}) \<and>
    Mapping.keys a2_map = {tp - len..tp} \<and>
    sorted (map (tstp_unpack \<circ> snd) (linearize tables)) \<and>
    (\<forall>tstp \<in> set (map snd (linearize tables)). case tstp of Inl ts \<Rightarrow> ts \<le> cur |
                                                            Inr tp' \<Rightarrow> tp' \<le> tp ) \<and>
    list_all (\<lambda>k. isl k \<longleftrightarrow> \<not> memL (args_ivl args) 0) (map snd (linearize tables)) \<and>
    (case Mapping.lookup a2_map (tp - len) of Some m \<Rightarrow> result = Mapping.keys m | _ \<Rightarrow> False) \<and>
    Mapping.lookup a2_map tp = Some Mapping.empty \<and>
    (\<forall>xs \<in> Mapping.keys a1_map. case Mapping.lookup a1_map xs of Some tp' \<Rightarrow> tp' < tp) \<and>
    (\<forall>tp' \<in> Mapping.keys a2_map. case Mapping.lookup a2_map tp' of Some m \<Rightarrow>
      (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
        \<exists>(table, tstp') \<in> set (linearize tables). tstp = tstp' \<and> xs \<in> table)) \<and>
    (\<forall>tp' \<in> Mapping.keys a2_map. case Mapping.lookup a2_map tp' of Some m \<Rightarrow>
      table (args_n args) (args_R args) (Mapping.keys m) \<and>
      (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
      tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL (args_ivl args) 0))) \<and>
    length done + len = length auxlist \<and>
    rev done = map (eval_args_agg args) (map proj_thd (take (length done) auxlist)) \<and>
    (\<forall>x \<in> set (take (length done) auxlist). check_before (args_ivl args) dt x) \<and>
    sorted (map fst auxlist) \<and>
    (list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map (args_pos args) tp' a1_map)
      (\<lambda>ts' tp'. filter_a2_map (args_ivl args) ts' tp' a2_map)) (drop (length done) auxlist)
      (zip (linearize tss) [tp - len..<tp])) \<and>
    list_all (\<lambda>(ts', tp'). ivl_restr_a2_map (args_ivl args) ts' tp' a2_map \<and> valid_tstp_map ts' tp' tstp_map) (zip (linearize tss) [tp - len..<tp])"

definition valid_mmuaux :: "args \<Rightarrow> ts \<Rightarrow> event_data mmuaux \<Rightarrow> event_data muaux \<Rightarrow>
  bool" where
  "valid_mmuaux args cur = valid_mmuaux' args cur cur"

fun eval_step_mmuaux :: "args \<Rightarrow> event_data mmuaux \<Rightarrow> event_data mmuaux" where
  "eval_step_mmuaux args (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done) =
    (case safe_hd tss of (Some ts, tss') \<Rightarrow>
      (case Mapping.lookup a2_map (tp - len) of Some m \<Rightarrow>
        let I = args_ivl args;
        T = eval_args_agg args result;
        tss' = tl_queue tss';
        (ts', tss'') = case safe_hd tss' of 
              (Some ts', tss'') \<Rightarrow> (ts', tss'') |
              (None, tss'') \<Rightarrow> (0, tss'');
        (tables, taken) = takedropWhile_queue (\<lambda>(table, tstp). \<not> ts_tp_lt I ts' (tp - len + 1) tstp) tables;
        to_del_approx = \<Union>(set (map fst taken));
        to_del = Set.filter (\<lambda>x. case Mapping.lookup m x of Some tstp \<Rightarrow> (\<not>ts_tp_lt I ts' (tp - len + 1) tstp) |
                                                            None \<Rightarrow> False) to_del_approx;
        m'' = mapping_delete_set m to_del;
        result' = if len = 1 then {} else (result - to_del) \<union> (case Mapping.lookup a2_map (tp - len + 1) of Some m' \<Rightarrow> Mapping.keys m');
        a2_map = if len = 1 then Mapping.update tp Mapping.empty a2_map
                 else Mapping.update (tp - len + 1)
          (case Mapping.lookup a2_map (tp - len + 1) of Some m' \<Rightarrow>
          Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') m'' m') a2_map;
        a2_map = Mapping.delete (tp - len) a2_map;
        tstp_map = Mapping.delete (tp - len) tstp_map in
        (tp, tss'', tables, len - 1, maskL, maskR, result', a1_map, a2_map, tstp_map, T # done)))"

lemma Mapping_update_keys: "Mapping.keys (Mapping.update a b m) = Mapping.keys m \<union> {a}"
  by transfer auto

lemma drop_is_Cons_take: "drop n xs = y # ys \<Longrightarrow> take (Suc n) xs = take n xs @ [y]"
proof (induction xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases n) simp_all
qed

lemma list_all_split: "list_all (\<lambda>(x, y). f x y \<and> g x y) xs \<longleftrightarrow> list_all (\<lambda>(x, y). f x y) xs \<and> list_all (\<lambda>(x, y). g x y) xs"
  by (smt (z3) Ball_set case_prodI2 old.prod.case)

lemma list_all2_weaken: "list_all2 f xs ys \<Longrightarrow>
  (\<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> f x y \<Longrightarrow> f' x y) \<Longrightarrow> list_all2 f' xs ys"
  by (induction xs ys rule: list_all2_induct) auto

declare Map_To_Mapping.map_apply_def[simp]

lemma Mapping_lookup_delete: "Mapping.lookup (Mapping.delete k m) k' =
  (if k = k' then None else Mapping.lookup m k')"
  by transfer auto

lemma Mapping_lookup_update: "Mapping.lookup (Mapping.update k v m) k' =
  (if k = k' then Some v else Mapping.lookup m k')"
  by transfer auto

lemma hd_le_set: "sorted xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> x \<in> set xs \<Longrightarrow> hd xs \<le> x"
  by (cases xs) auto

lemma Mapping_lookup_combineE: "Mapping.lookup (Mapping.combine f m m') k = Some v \<Longrightarrow>
  (Mapping.lookup m k = Some v \<Longrightarrow> P) \<Longrightarrow>
  (Mapping.lookup m' k = Some v \<Longrightarrow> P) \<Longrightarrow>
  (\<And>v' v''. Mapping.lookup m k = Some v' \<Longrightarrow> Mapping.lookup m' k = Some v'' \<Longrightarrow>
  f v' v'' = v \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding Mapping.lookup_combine
  by (auto simp add: combine_options_def split: option.splits)

lemma Mapping_keys_filterI: "Mapping.lookup m k = Some v \<Longrightarrow> f k v \<Longrightarrow>
  k \<in> Mapping.keys (Mapping.filter f m)"
  by transfer (auto split: option.splits if_splits)

lemma Mapping_keys_filterD: "k \<in> Mapping.keys (Mapping.filter f m) \<Longrightarrow>
  \<exists>v. Mapping.lookup m k = Some v \<and> f k v"
  by transfer (auto split: option.splits if_splits)

fun lin_ts_mmuaux :: "event_data mmuaux \<Rightarrow> ts list" where
  "lin_ts_mmuaux (tp, tss, len, maskL, maskR, result, a1_map, a2_map, done, done_length) =
    linearize tss"

lemma list_length_eq_split:
  assumes "list = xs @ [x] @ xs'"
  and "length list = length lista"
  shows "\<exists>ys y ys'. lista = ys @ [y] @ ys' \<and> length xs = length ys \<and> length xs' = length ys'"
proof -
  have length_eq: "length xs = length list - length xs' - 1" using assms by auto
  then have s1: "lista = take (length xs) lista @ drop (length list - length xs' - 1) lista" by auto
  have "length lista \<ge> length xs + 1" using assms by auto
  then have "drop (length list - length xs' - 1) lista \<noteq> []" using length_eq assms(2) by auto 
  then obtain b xc where xc_def: "drop (length list - length xs' - 1) lista = [b] @ xc" by (metis append_Cons append_Nil list.exhaust)
  then have "lista = take (length xs) lista @ [b] @ xc" using s1 by auto
  then obtain xb' where split_list_1: "lista = xb' @ [b] @ xc" "length xb' = length xs" "length xc = length xs'"
    using xc_def  by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 add_diff_cancel_left' assms(1) assms(2) diff_add_inverse2 diff_diff_left length_append length_drop length_nth_simps(1) length_nth_simps(2) plus_1_eq_Suc)
  then show ?thesis by metis
qed

lemma list_appendE: "xs = ys @ zs \<Longrightarrow> x \<in> set xs \<Longrightarrow>
  (x \<in> set ys \<Longrightarrow> P) \<Longrightarrow> (x \<in> set zs \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma tstp_le_aux: 
  assumes "Mapping.lookup tstp_map tpa = Some ts"
  and "Mapping.lookup tstp_map tpa' = Some ts'"
  and "tpa \<in> set lista"
  and "tpa' \<in> set lista"
  and "tpa < tpa'"
  and "sorted list"
  and "sorted lista"
  and "length list = length lista"
  and "list_all (\<lambda>(x, y). valid_tstp_map x y tstp_map) (zip list lista)" 
  shows "ts \<le> ts'"
proof -
  obtain yc yb' where split_lista_1: "lista = yb' @ [tpa'] @ yc" using assms(4) by (metis append_Cons append_Nil in_set_conv_decomp_first)
  then obtain xc b xb' where split_list_1: "list = xb' @ [b] @ xc" "length xb' = length yb'" "length xc = length yc"
    using list_length_eq_split[OF split_lista_1 assms(8)[symmetric]] by auto
  have "\<forall>x \<in> set yc. x \<ge> tpa'" using split_lista_1 assms(7) by (metis list.set_intros(1) sorted_append)
  then have "tpa \<in> set yb'" using assms(3) split_lista_1 assms(5) list_appendE by auto
  then obtain ya yb where split_lista_2: "yb' = ya @ [tpa] @ yb" by (metis append_Cons append_Nil in_set_conv_decomp_first)
  then obtain xa a xb where split_list_2: "xb' = xa @ [a] @ xb" "length xa = length ya" "length xb = length yb"
    using list_length_eq_split[OF split_lista_2 split_list_1(2)[symmetric]] by auto
  have "zip list lista = zip xb' yb' @ [(b, tpa')] @ zip xc yc" using split_lista_1 split_list_1 by auto
  moreover have "zip xb' yb' = zip xa ya @ [(a, tpa)] @ zip xb yb" using split_lista_2 split_list_2 by auto
  ultimately have zip_split: "zip list lista = zip xa ya @ [(a, tpa)] @ zip xb yb @ [(b, tpa')] @ zip xc yc" by auto
  then have "(a, tpa) \<in> set (zip list lista)" "(b, tpa') \<in> set (zip list lista)" by auto
  then have eq: "a = ts" "b = ts'" using assms(1-2) list_all_iff[of "\<lambda>(x, y). valid_tstp_map x y tstp_map" "zip list lista"] assms(9) 
    unfolding valid_tstp_map_def by auto
  then have "list = xa @ [ts] @ xb @ [ts'] @ xc" using split_list_1 split_list_2 by auto 
  have "\<forall>x \<in> set xb'. x \<le> ts'" using split_list_1(1)[unfolded eq(2)] assms(6) by (metis append_Cons list.set_intros(1) sorted_append)
  then show ?thesis using split_list_2(1)[unfolded eq(1)] by auto
qed

lemma valid_eval_step_mmuaux':
  assumes "valid_mmuaux' args cur dt aux auxlist"
    "lin_ts_mmuaux aux = ts # tss''" "\<not> memR (args_ivl args) (dt - ts)"
  shows "valid_mmuaux' args cur dt (eval_step_mmuaux args aux) auxlist \<and>
    lin_ts_mmuaux (eval_step_mmuaux args aux) = tss''"
proof -
  define I where "I = args_ivl args"
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  obtain tp len tss tables maskL maskR result a1_map a2_map tstp_map "done" where aux_def:
    "aux = (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done)"
    by (cases aux) auto
  then obtain tss' where safe_hd_eq: "safe_hd tss = (Some ts, tss')"
    using assms(2) safe_hd_rep case_optionE
    by (cases "safe_hd tss") fastforce
  note valid_before = assms(1)[unfolded aux_def]
  have lin_tss_not_Nil: "linearize tss \<noteq> []"
    using safe_hd_rep[OF safe_hd_eq] by auto
  have ts_hd: "ts = hd (linearize tss)"
    using safe_hd_rep[OF safe_hd_eq] by auto
  have lin_tss': "linearize tss' = linearize tss"
    using safe_hd_rep[OF safe_hd_eq] by auto
  have tss'_not_empty: "\<not>is_empty tss'"
    using is_empty_alt[of tss'] lin_tss_not_Nil unfolding lin_tss' by auto
  have len_pos: "len > 0"
    using lin_tss_not_Nil valid_before by auto
  have a2_map_keys: "Mapping.keys a2_map = {tp - len..tp}"
    using valid_before by auto
  have len_tp: "len \<le> tp"
    using valid_before by auto
  have tp_minus_keys: "tp - len \<in> Mapping.keys a2_map"
    using a2_map_keys by auto
  have tp_minus_keys': "tp - len + 1 \<in> Mapping.keys a2_map"
    using a2_map_keys len_pos len_tp by auto
  obtain m where m_def: "Mapping.lookup a2_map (tp - len) = Some m"
    using tp_minus_keys by (auto dest: Mapping_keys_dest)
  have result_def: "result = Mapping.keys m"
    using valid_before
    by (auto simp: m_def)
  have "table n R (Mapping.keys m)"
    "(\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
    tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0))"
    using tp_minus_keys m_def valid_before
    unfolding valid_mmuaux'.simps n_def I_def R_def by fastforce+
  then have m_inst: "table n R (Mapping.keys m)"
    "\<And>xs tstp. Mapping.lookup m xs = Some tstp \<Longrightarrow>
    tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0)"
    using Mapping_keys_intro by fastforce+
  have m_inst_isl: "\<And>xs tstp. Mapping.lookup m xs = Some tstp \<Longrightarrow> isl tstp \<longleftrightarrow> \<not> memL I 0"
    using m_inst(2) by fastforce
  obtain m' where m'_def: "Mapping.lookup a2_map (tp - len + 1) = Some m'"
    using tp_minus_keys' by (auto dest: Mapping_keys_dest)
  have "table n R (Mapping.keys m')"
    "(\<forall>xs \<in> Mapping.keys m'. case Mapping.lookup m' xs of Some tstp \<Rightarrow>
    tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0))"
    using tp_minus_keys' m'_def valid_before
    unfolding valid_mmuaux'.simps I_def n_def R_def by fastforce+
  then have m'_inst: "table n R (Mapping.keys m')"
    "\<And>xs tstp. Mapping.lookup m' xs = Some tstp \<Longrightarrow>
    tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0)"
    using Mapping_keys_intro by fastforce+
  have m'_inst_isl: "\<And>xs tstp. Mapping.lookup m' xs = Some tstp \<Longrightarrow> isl tstp \<longleftrightarrow> \<not> memL I 0"
    using m'_inst(2) by fastforce
  obtain ts' tss''' where ts'_tss'''_def: "(case safe_hd (tl_queue tss') of (Some ts', tss'') \<Rightarrow> (ts', tss'') | (None, tss'') \<Rightarrow> (0, tss'')) = (ts', tss''')"
    by fastforce
  then have ts'_def: "ts' = (case safe_hd (tl_queue tss') of (Some ts', tss'') \<Rightarrow> ts' | (None, tss'') \<Rightarrow> 0)"
    by (auto split: prod.splits option.splits)
  have lin_tss''': "linearize tss''' = linearize (tl_queue tss')"
    using ts'_tss'''_def safe_hd_rep[of "tl_queue tss'"]
    by (auto split: prod.splits option.splits)
  define T where "T = Mapping.keys m"
  define T_agg where "T_agg = eval_args_agg args T"
  have t_agg_eq: "T_agg = eval_args_agg args result"
    using result_def T_def T_agg_def by auto
  define tables' where "tables' = fst (takedropWhile_queue (\<lambda>(table, tstp). \<not> ts_tp_lt I ts' (tp - len + 1) tstp) tables)"
  define taken where "taken = snd (takedropWhile_queue (\<lambda>(table, tstp). \<not> ts_tp_lt I ts' (tp - len + 1) tstp) tables)"
  have tables_split: "linearize tables = taken @ (linearize tables')" 
    unfolding taken_def tables'_def takedropWhile_queue_snd takedropWhile_queue_fst dropWhile_queue_rep by auto
  have "sorted (map (tstp_unpack \<circ> snd) (linearize tables))" using valid_before unfolding I_def valid_mmuaux'.simps by auto
  then have sorted_tables': "sorted (map (tstp_unpack \<circ> snd) (linearize tables'))" unfolding tables_split using sorted_append by auto
  have "list_all (\<lambda>k. isl k = (\<not> memL I 0)) (map snd (linearize tables))" using valid_before unfolding I_def valid_mmuaux'.simps by auto
  then have isl_tables': "list_all (\<lambda>k. isl k = (\<not> memL I 0)) (map snd (linearize tables'))" unfolding tables_split by auto
  have taken_valid: "\<forall>(table, tstp) \<in> set taken. \<not>(ts_tp_lt I ts' (tp - len + 1) tstp)" 
    unfolding taken_def takedropWhile_queue_snd by (meson set_takeWhileD)
  have tables'_valid: "\<forall>(table, tstp) \<in> set (linearize tables'). ts_tp_lt I ts' (tp - len + 1) tstp" 
  proof
    fix x
    assume assm: "x \<in> set (linearize tables')"
    then obtain table_h tstp_h tl where hd_tl: "linearize tables' = (table_h, tstp_h)#tl" by (metis list.set_cases surj_pair)
    obtain table tstp where x_def: "x = (table, tstp)" by fastforce
    have "list_all (\<lambda>k. isl k = (\<not> memL I 0)) (map snd (linearize tables))" using valid_before unfolding I_def by auto
    moreover have "tstp_h \<in> set (map snd (linearize tables))" unfolding tables_split hd_tl by auto
    moreover have "tstp \<in> set (map snd (linearize tables))"  using assm unfolding x_def tables_split by force
    ultimately have isl_eq: "isl tstp_h = isl tstp" by (metis (mono_tags, lifting) list_all_append list_all_simps(1) split_list)
    have "\<forall>x \<in> set (map (tstp_unpack \<circ> snd) (linearize tables')). x \<ge> tstp_unpack tstp_h"
      using sorted_tables' unfolding hd_tl by auto
    moreover have "tstp_unpack tstp \<in> set (map (tstp_unpack \<circ> snd) (linearize tables'))" using assm[unfolded x_def] by force
    ultimately have geq: "tstp_unpack tstp_h \<le> tstp_unpack tstp" by auto
    have "ts_tp_lt I ts' (tp - len + 1) tstp_h" using hd_tl[unfolded tables'_def takedropWhile_queue_fst dropWhile_queue_rep] dropWhile_eq_Cons_conv[of _ "linearize tables"] by auto
    then have "ts_tp_lt I ts' (tp - len + 1) tstp" using isl_eq geq unfolding tstp_unpack_def ts_tp_lt_def by(auto split:sum.splits)
    then show "case x of (table, tstp) \<Rightarrow> ts_tp_lt I ts' (tp - len + 1) tstp" using x_def by auto
  qed
  define to_del_approx where "to_del_approx = \<Union>{x. x \<in> set (map fst taken)}"
  define to_del where "to_del = Set.filter (\<lambda>x. case Mapping.lookup m x of Some tstp \<Rightarrow> (\<not>ts_tp_lt I ts' (tp - len + 1) tstp) |
                                                            None \<Rightarrow> False) to_del_approx"
  define m_del where "m_del = mapping_delete_set m to_del"
  define result' where "result' \<equiv> if len = 1 then {} else (result - to_del) \<union> (case Mapping.lookup a2_map (tp - len + 1) of Some m' \<Rightarrow> Mapping.keys m')"
  define m'' where "m'' = Mapping.filter (\<lambda> _ tstp. ts_tp_lt I ts' (tp - len + 1) tstp) m"
  define mc where "mc = Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') m'' m'"
  define a2_map' where "a2_map' = (if len = 1 then Mapping.update tp Mapping.empty a2_map
                                  else Mapping.update (tp - len + 1) mc a2_map)"
  define a2_map'' where "a2_map'' = Mapping.delete (tp - len) a2_map'"
  define tstp_map' where "tstp_map' = Mapping.delete (tp - len) tstp_map"
  have m_upd_lookup: "\<And>xs tstp. Mapping.lookup m'' xs = Some tstp \<Longrightarrow>
    tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0)"
    unfolding m''_def Let_def Mapping.lookup_filter
    using m_inst(2) by (auto split: option.splits if_splits)
  have mc_lookup: "\<And>xs tstp. Mapping.lookup mc xs = Some tstp \<Longrightarrow>
    tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0)"
    unfolding mc_def Mapping.lookup_combine
    using m_upd_lookup m'_inst(2)
    by (auto simp add: combine_options_def max_tstp_isl intro: max_tstp_intro split: option.splits)
  have mc_keys: "Mapping.keys mc \<subseteq> Mapping.keys m \<union> Mapping.keys m'"
    unfolding mc_def m''_def Mapping.keys_combine 
    using Mapping.keys_filter by fastforce
  have tp_len_assoc: "tp - len + 1 = tp - (len - 1)"
    using len_pos len_tp by auto
  have a2_map''_keys: "Mapping.keys a2_map'' = {tp - (len - 1)..tp}"
    unfolding a2_map''_def a2_map'_def Mapping.keys_delete Mapping_update_keys a2_map_keys
    using tp_len_assoc apply(auto split:if_splits) 
      apply (metis a2_map_keys atLeastAtMost_iff le_antisym le_eq_less_or_eq less_Suc_eq_le)
      apply (metis One_nat_def Suc_diff_eq_diff_pred a2_map_keys atLeastAtMost_iff le_antisym len_pos not_less_eq_eq)
    using a2_map_keys atLeastAtMost_iff apply blast
    by (metis Suc_le_mono a2_map_keys atLeastAtMost_iff le_SucI)
  have lin_tss_Cons: "linearize tss = ts # linearize (tl_queue tss')"
    using lin_tss_not_Nil
    by (auto simp add: tl_queue_rep lin_tss' ts_hd)
  have tp_len_tp_unfold: "[tp - len..<tp] = (tp - len) # [tp - (len - 1)..<tp]"
    unfolding tp_len_assoc[symmetric]
    using len_pos len_tp Suc_diff_le upt_conv_Cons by auto
  have id: "\<And>x. x \<in> {tp - (len - 1) + 1..tp} \<Longrightarrow>
    Mapping.lookup a2_map'' x = Mapping.lookup a2_map x"
    unfolding a2_map''_def a2_map'_def Mapping_lookup_delete Mapping_lookup_update tp_len_assoc
    using len_tp by auto
  have list_all2: "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map)
    (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map))
    (drop (length done) auxlist) (zip (linearize tss) [tp - len..<tp])"
    using valid_before unfolding I_def pos_def by auto
  obtain hd_aux tl_aux where aux_split: "drop (length done) auxlist = hd_aux # tl_aux"
    "case hd_aux of (t, a1, a2) \<Rightarrow> (t, a1, a2) =
    (ts, filter_a1_map pos (tp - len) a1_map, filter_a2_map I ts (tp - len) a2_map)"
    and list_all2': "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map)
      (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map)) tl_aux
      (zip (linearize (tl_queue tss')) [tp - (len - 1)..<tp])"
    using list_all2[unfolded lin_tss_Cons tp_len_tp_unfold zip_Cons_Cons list_all2_Cons2] by auto
  have lookup''_tp_minus: "Mapping.lookup a2_map'' (tp - (len - 1)) = (if len = 1 then Some Mapping.empty
                                                                      else Some mc)"
    unfolding a2_map''_def a2_map'_def Mapping_lookup_delete Mapping_lookup_update
      tp_len_assoc[symmetric]
    using len_tp Mapping.lookup_update'[of _ _ a2_map] by auto
  have filter_a2_map_cong: "\<And>ts' tp'. ts' \<in> set (linearize (tl_queue tss')) \<Longrightarrow>
    tp' \<in> {tp - (len - 1)..<tp} \<Longrightarrow> filter_a2_map I ts' tp' a2_map =
    filter_a2_map I ts' tp' a2_map''"
  proof (rule set_eqI, rule iffI)
    fix ts' tp' xs
    assume assms: "ts' \<in> set (linearize (tl_queue tss'))"
      "tp' \<in> {tp - (len - 1)..<tp}" "xs \<in> filter_a2_map I ts' tp' a2_map"
    obtain tp_bef m_bef tstp where defs: "tp_bef \<le> tp'" "Mapping.lookup a2_map tp_bef = Some m_bef"
      "Mapping.lookup m_bef xs = Some tstp" "ts_tp_lt I ts' tp' tstp"
      using assms(3)[unfolded filter_a2_map_def]
      by (fastforce split: option.splits)
    have not_empty_tl: "\<not>is_empty (tl_queue tss')" using assms(1) is_empty_alt[of "tl_queue tss'"] by auto
    then obtain ts'' tss'' where hd_tl: "safe_hd (tl_queue tss') = (Some ts'', tss'')" 
      using not_empty_head_q[OF not_empty_tl] by auto
    then have ts''_geq: "ts' \<ge> ts''" 
      using hd_le_set[OF _ _ assms(1)] safe_hd_rep[OF hd_tl] lin_tss_Cons valid_before by force
    have tp_bef_in: "tp_bef \<in> {tp - len..tp}"
      using defs(2) valid_before by (auto intro!: Mapping_keys_intro)
    have tp_minus_le: "tp - (len - 1) \<le> tp'"
      using assms(2) by auto
    have len_geq: "len \<ge> 2" using assms(2) by auto
    show "xs \<in> filter_a2_map I ts' tp' a2_map''"
    proof (cases "tp_bef \<le> tp - (len - 1)")
      case True
      show ?thesis
      proof (cases "tp_bef = tp - len")
        case True
        have m_bef_m: "m_bef = m"
          using defs(2) m_def
          unfolding True by auto
        have lookup: "Mapping.lookup m xs = Some tstp"
          using defs(3,4) assms(2) unfolding m_bef_m 
          by (auto 0 3 simp add: Mapping.lookup_filter ts_tp_lt_def intro: Mapping_keys_intro
              split: sum.splits elim: contrapos_np)
        then have "ts_tp_lt I (case safe_hd (tl_queue tss') of (Some ts', tss'') \<Rightarrow> ts' |
                                                                _ \<Rightarrow> 0) (tp - len + 1) tstp"
          using defs(4) tp_minus_le tp_len_assoc hd_tl ts''_geq unfolding ts_tp_lt_def 
          by(auto split:sum.splits prod.splits option.splits) 
        then have "Mapping.lookup m'' xs = Some tstp" using lookup unfolding m''_def Let_def Mapping.lookup_filter I_def ts'_def by auto

        then have "case Mapping.lookup mc xs of None \<Rightarrow> False | Some tstp \<Rightarrow>
          ts_tp_lt I ts' tp' tstp"
          unfolding mc_def Mapping.lookup_combine
          using m'_inst(2) m_upd_lookup
          by (auto simp add: combine_options_def defs(4) intro!: max_tstp_intro'
              dest: Mapping_keys_dest split: option.splits)
        then show ?thesis
          using lookup''_tp_minus tp_minus_le defs len_geq
          unfolding m_bef_m filter_a2_map_def by (auto split: option.splits)
      next
        case False
        then have "tp_bef = tp - (len - 1)"
          using True tp_bef_in by auto
        then have m_bef_m: "m_bef = m'"
          using defs(2) m'_def
          unfolding tp_len_assoc by auto
        have "case Mapping.lookup mc xs of None \<Rightarrow> False | Some tstp \<Rightarrow>
          ts_tp_lt I ts' tp' tstp"
          unfolding mc_def Mapping.lookup_combine
          using m'_inst(2) m_upd_lookup defs(3)[unfolded m_bef_m]
          by (auto simp add: combine_options_def defs(4) intro!: max_tstp_intro''
              dest: Mapping_keys_dest split: option.splits)
        then show ?thesis
          using lookup''_tp_minus tp_minus_le defs len_geq
          unfolding m_bef_m filter_a2_map_def by (auto split: option.splits)
      qed
    next
      case False
      then have "Mapping.lookup a2_map'' tp_bef = Mapping.lookup a2_map tp_bef"
        using id tp_bef_in len_tp by auto
      then show ?thesis
        unfolding filter_a2_map_def
        using defs by auto
    qed
  next
    fix ts' tp' xs
    assume assms: "ts' \<in> set (linearize (tl_queue tss'))" "tp' \<in> {tp - (len - 1)..<tp}"
      "xs \<in> filter_a2_map I ts' tp' a2_map''"
    obtain tp_bef m_bef tstp where defs: "tp_bef \<le> tp'"
      "Mapping.lookup a2_map'' tp_bef = Some m_bef"
      "Mapping.lookup m_bef xs = Some tstp" "ts_tp_lt I ts' tp' tstp"
      using assms(3)[unfolded filter_a2_map_def]
      by (fastforce split: option.splits)
    have len_geq: "len \<ge> 2" using assms(2) by auto
    have tp_bef_in: "tp_bef \<in> {tp - (len - 1)..tp}"
      using defs(2) a2_map''_keys by (auto intro!: Mapping_keys_intro)
    have tp_minus_le: "tp - len \<le> tp'" "tp - (len - 1) \<le> tp'"
      using assms(2) by auto
    show "xs \<in> filter_a2_map I ts' tp' a2_map"
    proof (cases "tp_bef = tp - (len - 1)")
      case True
      have m_beg_mc: "m_bef = mc"
        using defs(2) len_geq Mapping.lookup_update[of _ _ a2_map]
        unfolding True a2_map''_def a2_map'_def tp_len_assoc Mapping_lookup_delete
        by (auto split: if_splits)
      show ?thesis
        using defs(3)[unfolded m_beg_mc mc_def]
      proof (rule Mapping_lookup_combineE)
        assume lassm: "Mapping.lookup m'' xs = Some tstp"
        then show "xs \<in> filter_a2_map I ts' tp' a2_map"
          unfolding m''_def Let_def Mapping.lookup_filter
          using m_def tp_minus_le(1) defs 
          by (auto simp add: filter_a2_map_def split: option.splits if_splits)
      next
        assume lassm: "Mapping.lookup m' xs = Some tstp"
        then show "xs \<in> filter_a2_map I ts' tp' a2_map"
          using m'_def defs(4) tp_minus_le defs
          unfolding filter_a2_map_def tp_len_assoc
          by auto
      next
        fix v' v''
        assume lassms: "Mapping.lookup m'' xs = Some v'" "Mapping.lookup m' xs = Some v''"
          "max_tstp v' v'' = tstp"
        show "xs \<in> filter_a2_map I ts' tp' a2_map"
        proof (rule max_tstpE)
          show "isl v' = isl v''"
            using lassms(1,2) m_upd_lookup m'_inst(2)
            by auto
        next
          assume "max_tstp v' v'' = v'"
          then show "xs \<in> filter_a2_map I ts' tp' a2_map"
            using lassms(1,3) m_def defs tp_minus_le(1)
            unfolding m''_def Let_def tp_len_assoc Mapping.lookup_filter
            by (auto simp add: filter_a2_map_def split: option.splits if_splits)
        next
          assume "max_tstp v' v'' = v''"
          then show "xs \<in> filter_a2_map I ts' tp' a2_map"
            using lassms(2,3) m'_def defs tp_minus_le(2)
            unfolding tp_len_assoc
            by (auto simp add: filter_a2_map_def)
        qed
      qed
    next
      case False
      then have "Mapping.lookup a2_map'' tp_bef = Mapping.lookup a2_map tp_bef"
        using id tp_bef_in by auto
      then show ?thesis
        unfolding filter_a2_map_def
        using defs by auto (metis option.simps(5))
    qed
  qed
  have list_all2'': "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map)
      (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map'')) tl_aux
      (zip (linearize (tl_queue tss')) [tp - (len - 1)..<tp])"
    using filter_a2_map_cong 
    by (intro list_all2_weaken[OF list_all2']) (auto elim!: in_set_zipE split: prod.splits)
  have lookup'': "\<forall>tp' \<in> Mapping.keys a2_map''. case Mapping.lookup a2_map'' tp' of Some m \<Rightarrow>
    table n R (Mapping.keys m) \<and> (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
    tstp_lt tstp cur tp \<and> isl tstp = (\<not> memL I 0))"
  proof (rule ballI)
    fix tp'
    assume assm: "tp' \<in> Mapping.keys a2_map''"
    then obtain f where f_def: "Mapping.lookup a2_map'' tp' = Some f"
      by (auto dest: Mapping_keys_dest)
    have tp'_in: "tp' \<in> {tp - (len - 1)..tp}"
      using assm unfolding a2_map''_keys .
    then have tp'_in_keys: "tp' \<in> Mapping.keys a2_map"
      using valid_before by auto
    have "table n R (Mapping.keys f) \<and>
      (\<forall>xs \<in> Mapping.keys f. case Mapping.lookup f xs of Some tstp \<Rightarrow>
      tstp_lt tstp cur tp \<and> isl tstp = (\<not> memL I 0))"
    proof (cases "tp' = tp - (len - 1)")
      case True
      then have f_mc: "f = (if len = 1 then Mapping.empty else mc)"
        using f_def Mapping.lookup_update'[of _ _ a2_map]
        unfolding a2_map''_def a2_map'_def Mapping_lookup_delete Mapping_lookup_update tp_len_assoc
        by (auto split: if_splits)
      have "table n R (Mapping.keys f)"
        unfolding f_mc
        using mc_keys m_def m'_def m_inst m'_inst
        by (auto simp add: table_def)
      moreover have "\<forall>xs \<in> Mapping.keys f. case Mapping.lookup f xs of Some tstp \<Rightarrow>
        tstp_lt tstp cur tp \<and> isl tstp = (\<not> memL I 0)"
      proof(cases "len = 1")
        case True
        then have "f = Mapping.empty" using f_mc by auto
        then show ?thesis by auto
      next
        case False
        then have eq: "f = mc" using f_mc by auto
        then have "\<forall>xs \<in> Mapping.keys mc. case Mapping.lookup mc xs of Some tstp \<Rightarrow>
        tstp_lt tstp cur tp \<and> isl tstp = (\<not> memL I 0)" using assm Mapping.keys_filter m_inst(2) m_inst_isl m'_inst(2) m'_inst_isl max_tstp_isl
        unfolding m''_def Let_def f_mc mc_def Mapping.lookup_combine
        by (auto simp add: combine_options_def Mapping.lookup_filter
            intro!: max_tstp_intro Mapping_keys_intro dest!: Mapping_keys_dest
            split: option.splits)
      then show ?thesis using eq by auto
    qed
      ultimately show ?thesis
        by auto
    next
      case False
      have "Mapping.lookup a2_map tp' = Some f"
        using tp'_in id[of tp'] f_def False by auto
      then show ?thesis
        using tp'_in_keys valid_before
        unfolding valid_mmuaux'.simps I_def n_def R_def by fastforce
    qed
    then show "case Mapping.lookup a2_map'' tp' of Some m \<Rightarrow>
      table n R (Mapping.keys m) \<and> (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
      tstp_lt tstp cur tp \<and> isl tstp = (\<not> memL I 0))"
      using f_def by auto
  qed
  have tl_aux_def: "tl_aux = drop (length done + 1) auxlist"
    using aux_split(1) by (metis Suc_eq_plus1 add_Suc drop0 drop_Suc_Cons drop_drop)
  have T_eq: "Mapping.keys m = filter_a2_map I ts (tp - len) a2_map"
  proof (rule set_eqI, rule iffI)
    fix xs
    assume "xs \<in> filter_a2_map I ts (tp - len) a2_map"
    then obtain tp_bef m_bef tstp where defs: "tp_bef \<le> tp - len"
      "Mapping.lookup a2_map tp_bef = Some m_bef"
      "Mapping.lookup m_bef xs = Some tstp" "ts_tp_lt I ts (tp - len) tstp"
      by (fastforce simp add: filter_a2_map_def split: option.splits)
    then have tp_bef_minus: "tp_bef = tp - len"
      using valid_before Mapping_keys_intro by force
    have m_bef_m: "m_bef = m"
      using defs(2) m_def
      unfolding tp_bef_minus by auto
    show "xs \<in> Mapping.keys m"
      using defs
      unfolding T_def m_bef_m
      by (auto intro: Mapping_keys_filterI Mapping_keys_intro)
  next
    fix xs
    have "ivl_restr_a2_map I ts (tp - len) a2_map" 
      using valid_before lin_tss_Cons tp_len_tp_unfold I_def by auto
    then have aux: "\<forall>k. case Mapping.lookup m k of Some tstp \<Rightarrow> ts_tp_lt I ts (tp - len) tstp |
                                              None \<Rightarrow> True" 
      unfolding ivl_restr_a2_map_def using m_def by auto
    assume "xs \<in> Mapping.keys m"
    then have "tp - len \<le> tp - len"
       "case Mapping.lookup a2_map (tp - len) of 
          None \<Rightarrow> False | 
          Some m \<Rightarrow> (case Mapping.lookup m xs of None \<Rightarrow> False | Some x \<Rightarrow> ts_tp_lt I ts (tp - len) x)"
      using m_def aux  unfolding T_def by (auto simp add: Mapping_keys_dest split: option.splits)
    then show "xs \<in> filter_a2_map I ts (tp - len) a2_map" unfolding filter_a2_map_def by auto
  qed
  have min_auxlist_done: "min (length auxlist) (length done) = length done"
    using valid_before by auto
  then have "\<forall>x \<in> set (take (length done) auxlist). check_before I dt x"
    "rev done = map (eval_args_agg args) (map proj_thd (take (length done) auxlist))"
    using valid_before unfolding I_def by auto
  then have list_all': "(\<forall>x \<in> set (take (length (result # done)) auxlist). check_before I dt x)"
    "rev (T_agg # done) = map (eval_args_agg args) (map proj_thd (take (length (T # done)) auxlist))"
    using drop_is_Cons_take[OF aux_split(1)] aux_split(2) assms(3) unfolding T_agg_def
    by (auto simp add: T_def T_eq I_def result_def)
  note list_all_split' = list_all_split[of "\<lambda>ts' tp'. ivl_restr_a2_map I ts' tp' a2_map" "\<lambda>ts' tp'. valid_tstp_map ts' tp' tstp_map"]
  note list_all_split'' = list_all_split[of "\<lambda>ts' tp'. ivl_restr_a2_map I ts' tp' a2_map''" "\<lambda>ts' tp'. valid_tstp_map ts' tp' tstp_map'"]
  have ivl_restr: "list_all (\<lambda>(ts', tp'). ivl_restr_a2_map I ts' tp' a2_map \<and> valid_tstp_map ts' tp' tstp_map)
     (zip (linearize tss) [tp - len..<tp])" using valid_before lin_tss' I_def by auto
  then have "list_all (\<lambda>(ts', tp'). ivl_restr_a2_map I ts' tp' a2_map \<and> valid_tstp_map ts' tp' tstp_map) (zip (tl (linearize tss)) [tp - (len - 1)..<tp])"
    using ivl_restr[unfolded lin_tss_Cons tp_len_tp_unfold] lin_tss_Cons by auto
  then have ivl_restr': 
    "list_all (\<lambda>(ts', tp'). ivl_restr_a2_map I ts' tp' a2_map) (zip (tl (linearize tss)) [tp - (len - 1)..<tp])" 
    "list_all (\<lambda>(ts', tp'). valid_tstp_map ts' tp' tstp_map) (zip (tl (linearize tss)) [tp - (len - 1)..<tp])"
    using list_all_split' by auto
  have list_all'': "list_all (\<lambda>(ts', tp'). ivl_restr_a2_map I ts' tp' a2_map'' \<and> valid_tstp_map ts' tp' tstp_map')
     (zip (tl (linearize tss)) [tp - (len - 1)..<tp])" 
  proof (cases "tl (linearize tss)")
    case Nil
    then show ?thesis by auto
  next
    case (Cons a list)
    then have "length (tl (linearize tss)) \<ge> 1" by auto
    then have "len \<ge> 2" using valid_before by auto
    then have tp_len_eq: "[tp - (len - 1)..<tp] = (tp - (len - 1)) # [tp - (len - 1) + 1..<tp]" by (metis Suc_1 Suc_le_lessD diff_less len_pos len_tp less_le_trans upt_eq_Cons_conv zero_less_diff)
    have not_empty_tss: "\<not> Optimized_MTL.is_empty (tl_queue tss')" using Cons is_empty_alt lin_tss_Cons by force
    obtain tss'' where hd_tl: "safe_hd (tl_queue tss') = (Some a, tss'')"
      using not_empty_head_q[OF not_empty_tss] lin_tss_Cons local.Cons safe_hd_rep by fastforce
    have ivl_restr'': "list_all (\<lambda>(ts', tp'). ivl_restr_a2_map I ts' tp' a2_map)
     (zip list [tp - (len - 1) + 1..<tp])" using ivl_restr'(1) Cons tp_len_eq by auto
    have ivl_restr_impl: "\<And>ts' tp'. ts' \<in> set list \<Longrightarrow>
    tp' \<in> {tp - (len - 1) + 1..<tp} \<Longrightarrow> ivl_restr_a2_map I ts' tp' a2_map \<Longrightarrow>
    ivl_restr_a2_map I ts' tp' a2_map''"
    proof -
      fix tsa tpa
      assume assms: "tsa \<in> set list" "tpa \<in> {tp - (len - 1) + 1..<tp}" 
        "ivl_restr_a2_map I tsa tpa a2_map"
      then have *: "tpa \<in> {tp - (len - 1) + 1..tp}" by auto
      show "ivl_restr_a2_map I tsa tpa a2_map''" 
        using id[OF *] assms(3) unfolding ivl_restr_a2_map_def by auto
    qed
    have list_all_eq_1: "list_all (\<lambda>(ts', tp'). ivl_restr_a2_map I ts' tp' a2_map'') (zip list [tp - (len - 1) + 1..<tp])"
      using ivl_restr_impl
      by(intro list.pred_mono_strong[OF ivl_restr'']) (auto elim!: in_set_zipE split: prod.splits)
    have ivl_restr_old: "ivl_restr_a2_map I a (tp - (len - 1)) a2_map" using ivl_restr' unfolding Cons tp_len_eq by auto
    have "ivl_restr_a2_map I a (tp - (len - 1)) a2_map''" unfolding ivl_restr_a2_map_def lookup''_tp_minus mc_def apply(auto simp:Mapping.lookup_combine)
    proof -
      fix xs
      show "case combine_options max_tstp (Mapping.lookup m'' xs) (Mapping.lookup m' xs) of None \<Rightarrow> True
          | Some x \<Rightarrow> ts_tp_lt I a (tp - (len - 1)) x "
      proof (cases "Mapping.lookup m'' xs")
        case none_m'': None
        then show ?thesis
        proof (cases "Mapping.lookup m' xs")
          case None
          then show ?thesis using none_m'' by auto
        next
          case (Some a')
          then have "ts_tp_lt I a (tp - (len - 1)) a'" using m'_def ivl_restr_old unfolding ivl_restr_a2_map_def tp_len_assoc by(auto split:option.splits)
          then show ?thesis using none_m'' Some by auto
        qed
      next
        case some_m'': (Some a')
        then have aux: "ts_tp_lt I a (tp - (len - 1)) a'" unfolding m''_def Let_def Mapping.lookup_filter I_def hd_tl tp_len_assoc ts'_def by(auto split:if_splits option.splits)
        show ?thesis 
        proof (cases "Mapping.lookup m' xs")
          case None
          then show ?thesis using some_m'' aux by auto
        next
          case (Some a'')
          then have "ts_tp_lt I a (tp - (len - 1)) a''" using m'_def ivl_restr_old unfolding ivl_restr_a2_map_def tp_len_assoc by(auto split:option.splits)
          then show ?thesis using some_m'' aux Some unfolding ts_tp_lt_def by(cases a'; cases a''; auto)
        qed
      qed
    qed
    then have split1: "list_all (\<lambda>(ts', tp'). ivl_restr_a2_map I ts' tp' a2_map'') (zip (tl (linearize tss)) [tp - (len - 1)..<tp])" 
      using list_all_eq_1 Cons tp_len_eq by auto
    have tstp_map_impl: "\<And>ts' tp'. ts' \<in> set (tl (linearize tss)) \<Longrightarrow> tp' \<in> {tp - (len - 1)..<tp} \<Longrightarrow> valid_tstp_map ts' tp' tstp_map \<Longrightarrow> valid_tstp_map ts' tp' tstp_map'"
    proof -
      fix ts' tp'
      assume assms: "tp' \<in> {tp - (len - 1)..<tp}" "valid_tstp_map ts' tp' tstp_map"
      have "tp' \<noteq> tp - len" using assms(1) by (metis add.right_neutral add_le_cancel_left atLeastLessThan_iff not_one_le_zero tp_len_assoc)
      then show "valid_tstp_map ts' tp' tstp_map'" using assms(2) unfolding tstp_map'_def valid_tstp_map_def 
        by(auto split:option.splits; transfer; auto)
    qed
    then have split2: "list_all (\<lambda>(ts', tp'). valid_tstp_map ts' tp' tstp_map') (zip (tl (linearize tss)) [tp - (len - 1)..<tp])" 
      by(intro list.pred_mono_strong[OF ivl_restr'(2)]) (auto elim!: in_set_zipE split: prod.splits)
    show ?thesis using split1 split2 list_all_split'' by auto
  qed 
  let ?del_set = "{k \<in> Mapping.keys m. (case Mapping.lookup m k of Some tstp \<Rightarrow> \<not>(ts_tp_lt I ts' (tp - len + 1) tstp) |
                                                                   None \<Rightarrow> False)}"
  have "?del_set = to_del" 
  proof (rule set_eqI, rule iffI)
    fix x
    assume assm: "x \<in> ?del_set"
    then obtain tstp where tstp_defs: "Mapping.lookup m x = Some tstp" "\<not> ts_tp_lt I ts' (tp - len + 1) tstp"
      by(auto split:option.splits)
    have "tp - len \<in> Mapping.keys a2_map" using tp_minus_keys by blast
    then have "\<forall>xs\<in>Mapping.keys m.
             case Mapping.lookup m xs of
             Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables). tstp = tstp' \<and> xs \<in> table" 
      using m_def valid_before unfolding valid_mmuaux'.simps by fastforce
    then have "\<exists>(table, tstp') \<in> set (linearize tables). tstp = tstp' \<and> x \<in> table" using m_def valid_before
      using tstp_defs assm case_prodI2 case_prod_conv mem_Collect_eq option.simps(5) by fastforce
    then obtain table tstp' where defs: "(table, tstp') \<in> set (linearize tables)" "tstp = tstp'" "x \<in> table" by auto
    have "(table, tstp') \<notin> set (linearize tables')" 
    proof(rule ccontr)
      assume "\<not> (table, tstp') \<notin> set (linearize tables')"
      then have "(table, tstp') \<in> set (linearize tables')" by auto
      then have "ts_tp_lt I ts' (tp - len + 1) tstp'" using tables'_valid by auto
      then show "False" using defs(2) tstp_defs(2) by auto
    qed
    then have "(table, tstp') \<in> set taken" using defs(1)[unfolded tables_split] by auto
    then have "x \<in> to_del_approx" unfolding to_del_approx_def using defs(3) by auto force
    then show "x \<in> to_del" unfolding to_del_def using assm by(auto split:option.splits)
  next
    fix x
    assume "x \<in> to_del"
    then have "case Mapping.lookup m x of None \<Rightarrow> False | 
               Some tstp \<Rightarrow> \<not> ts_tp_lt I ts' (tp - len + 1) tstp" 
      unfolding to_del_def by auto
    then show "x \<in> ?del_set" by(auto simp: Mapping_keys_intro split:option.splits)
  qed
  moreover have "Mapping.keys m - Mapping.keys (Mapping.filter (\<lambda>_. ts_tp_lt I ts' (tp - len + 1)) m) = ?del_set"
    by transfer auto
  moreover have "Mapping.filter (\<lambda>_. ts_tp_lt I ts' (tp - len + 1)) m = mapping_delete_set m (Mapping.keys m - Mapping.keys (Mapping.filter (\<lambda>_. ts_tp_lt I ts' (tp - len + 1)) m))"
  proof(rule mapping_eqI) 
    fix x
    show "Mapping.lookup (Mapping.filter (\<lambda>_. ts_tp_lt I ts' (tp - len + 1)) m) x =
          Mapping.lookup (mapping_delete_set m (Mapping.keys m - Mapping.keys (Mapping.filter (\<lambda>_. ts_tp_lt I ts' (tp - len + 1)) m))) x"
      using delete_set_lookup[of m] Mapping.lookup_filter[of _ m] Mapping_keys_filterI[of m] Mapping_keys_filterD[of x _ m]
      by(auto simp add:Mapping_keys_intro split:option.splits) blast
  qed
  ultimately have m_eq: "m'' = m_del" unfolding m''_def m_del_def by auto
  have "takedropWhile_queue (\<lambda>(table, tstp). \<not> ts_tp_lt I ts' (tp - len + 1) tstp) tables = (tables', taken)"
    by (auto simp: tables'_def taken_def)
  then have eval_step_mmuaux_eq: "eval_step_mmuaux args (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map,
    done) = (tp, tss''', tables', len - 1,  maskL, maskR, result', a1_map, a2_map'', tstp_map', T_agg # done)"
    using safe_hd_eq m_def m'_def mc_def a2_map'_def a2_map''_def I_def tstp_map'_def m_eq[unfolded m_del_def to_del_def to_del_approx_def taken_def] tables'_def ts'_tss'''_def[symmetric]
    by (auto simp add: t_agg_eq Let_def result'_def to_del_def to_del_approx_def split:prod.splits) fastforce+
  have lin_ts: "lin_ts_mmuaux (eval_step_mmuaux args aux) = tss''"
    using lin_tss_Cons assms(2) lin_tss''' unfolding aux_def eval_step_mmuaux_eq by auto
  have lookup_old: "Mapping.lookup a2_map tp = Some Mapping.empty" using valid_before by auto
  have len_not_0: "len \<noteq> 0" using valid_before using lin_tss_not_Nil by force
  then have still_empty: "Mapping.lookup a2_map'' tp = Some Mapping.empty" 
  proof(cases "len = 1")
    case True
    then show ?thesis using a2_map''_def a2_map'_def lookup''_tp_minus by force
  next
    case False
    then have "Suc (tp - len) \<noteq> tp" by (metis diff_add_inverse2 diff_diff_cancel len_tp plus_1_eq_Suc)
    then have "Mapping.lookup a2_map' tp = Some Mapping.empty" 
      unfolding a2_map'_def using Mapping.lookup_update'[of _ _ a2_map] lookup_old by(auto)
    then show ?thesis unfolding a2_map''_def using len_not_0 by (metis Mapping_lookup_delete Suc_eq_plus1 diff_le_self not_less_eq_eq tp_len_assoc)
  qed
  have valid_tables': "\<forall>tp' \<in> Mapping.keys a2_map''. case Mapping.lookup a2_map'' tp' of Some m \<Rightarrow>
      (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
        \<exists>(table, tstp') \<in> set (linearize tables'). tstp = tstp' \<and> xs \<in> table)"
  proof 
    fix tp'
    assume in_a2: "tp' \<in> Mapping.keys a2_map''"
    then have tp'_in: "tp' \<in> {tp - len + 1..tp}" using a2_map''_keys tp_len_assoc by auto
    then have tp'_in': "tp' \<in> {tp - len..tp}" by auto
    have second_last_in_zip: "len \<ge> 2 \<Longrightarrow> (ts', tp - len + 1) \<in> set (zip (linearize tss) [tp - len..<tp])"
    proof -
      assume geq_2: "len \<ge> 2"
      have auxa: "length (linearize tss) = length [tp - len..<tp]" using tp_len_assoc valid_before by auto
      have auxb: "tp - (len - 1) \<noteq> tp" using geq_2 tp_len_assoc by auto
      then have eq2: "[tp - (len - 1)..<tp] = (tp - (len - 1))#[tp - (len - 1) + 1 ..<tp]"
        by (metis Suc_eq_plus1 antisym_conv1 diff_le_self upt_conv_Cons)
      moreover have "length (linearize (tl_queue tss')) = len - 1" using auxa len_tp lin_tss_Cons by force
      ultimately have tss'_not_empty: "linearize (tl_queue tss') \<noteq> []" by force
      obtain ts4 tss'' where safe_hd_eq: "safe_hd (tl_queue tss') = (ts4, tss'')" by(cases "safe_hd (tl_queue tss')") auto
      then obtain ts''' where ts3_def: "ts4 = Some ts'''" using safe_hd_rep[OF safe_hd_eq] tss'_not_empty case_optionE by blast
      then have "ts''' = ts'" using safe_hd_eq unfolding ts'_def by auto
      then have safe_hd_final: "safe_hd (tl_queue tss') = (Some ts', tss'')" using safe_hd_eq ts3_def by auto
      have rep_defs: "ts' = hd (linearize (tl_queue tss'))" "linearize (tl_queue tss') = linearize tss''" "linearize (tl_queue tss') \<noteq> []" using safe_hd_rep[OF safe_hd_final] by auto
      have lin_tss'_Cons: "linearize (tl_queue tss') = ts' # linearize (tl_queue (tl_queue tss'))"
        using tl_queue_rep[of "tl_queue tss'"] rep_defs(1) by (simp add: tss'_not_empty)
      have  "(ts', tp - len + 1) \<in> set (zip (linearize (tl_queue tss')) [tp - (len - 1)..<tp])" 
        unfolding eq2 lin_tss'_Cons tp_len_assoc by auto
      then show "(ts', tp - len + 1) \<in> set (zip (linearize tss) [tp - len..<tp])" unfolding lin_tss_Cons tp_len_tp_unfold by auto
    qed
    obtain m_aux where m_aux_def: "Mapping.lookup a2_map'' tp' = Some m_aux" using in_a2 by (meson Mapping_keys_dest)
    show "case Mapping.lookup a2_map'' tp' of Some m \<Rightarrow> \<forall>xs\<in>Mapping.keys m. case Mapping.lookup m xs of
                Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables'). tstp = tstp' \<and> xs \<in> table"
    proof(cases "tp' = tp - len + 1")
      case a: True
      then show ?thesis
      proof(cases "len = 1")
        case True
        then have "Mapping.lookup a2_map'' tp' = Some Mapping.empty" using a len_tp
          unfolding a2_map''_def a2_map'_def Mapping_lookup_delete
          by (auto simp: lookup_update')
        then show ?thesis by auto
      next
        case False
        then have mc: "Mapping.lookup a2_map'' tp' = Some mc" using a Mapping.lookup_update
          unfolding a2_map''_def a2_map'_def Mapping_lookup_delete by(auto)
        have "\<forall>xs\<in>Mapping.keys mc. case Mapping.lookup mc xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables'). tstp = tstp' \<and> xs \<in> table"
        proof 
          fix xs
          assume "xs \<in> Mapping.keys mc"
          then obtain tstp where tstp_def: "Mapping.lookup mc xs = Some tstp" by (meson Mapping_keys_dest)
          then have tstp_combine_def: "Some tstp = combine_options max_tstp (Mapping.lookup m'' xs) (Mapping.lookup m' xs)" unfolding mc_def Mapping.lookup_combine by auto
          have "tp - len + 1 \<in> Mapping.keys a2_map" using m'_def by transfer auto
          then have m'_restr: "\<forall>xs \<in> Mapping.keys m'. case Mapping.lookup m' xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables). tstp = tstp' \<and> xs \<in> table"
            using valid_before m'_def unfolding valid_mmuaux'.simps by (smt (z3) option.case(2))
          have "tp - len \<in> Mapping.keys a2_map" using m_def by transfer auto
          then have m_restr: "\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables). tstp = tstp' \<and> xs \<in> table"
            using valid_before m_def unfolding valid_mmuaux'.simps by (smt (z3) option.case(2))
          have "\<exists>(table, tstp')\<in>set (linearize tables'). tstp = tstp' \<and> xs \<in> table"
          proof(cases "Mapping.lookup m' xs")
            case none_m': None
            
            then show ?thesis
            proof(cases "Mapping.lookup m'' xs")
              case None
              then show ?thesis using none_m' tstp_combine_def by auto
            next
              case (Some a')
              then have eq: "a' = tstp" using tstp_combine_def none_m' by auto
              then have restr_a': "ts_tp_lt I ts' (tp - len + 1) tstp" using Some unfolding m''_def by(transfer) (auto split:option.splits if_splits)
              have m_lookup: "Mapping.lookup m xs = Some a'" using Some unfolding m''_def by(transfer) (auto split:option.splits if_splits)
              have "xs \<in> Mapping.keys m" using Some unfolding m''_def by(transfer) (auto split:option.splits)
              then have "\<exists>(table, tstp')\<in>set (linearize tables). tstp = tstp' \<and> xs \<in> table"
                using m_restr m_lookup eq by fastforce
              then obtain table tstp' where defs: "(table, tstp') \<in> set (linearize tables)" "tstp = tstp'" "xs \<in> table" by auto
              have "(table, tstp') \<notin> set taken" using restr_a' taken_valid defs(2) by auto
              then have "(table, tstp') \<in> set (linearize tables')" using defs(1) unfolding tables_split by auto
              then show ?thesis using defs(2-3) by auto
            qed
          next
            case some_m': (Some a)
            then have in_m': "xs \<in> Mapping.keys m'" by transfer auto
            have "m' \<noteq> Mapping.empty" using in_m' by auto
            then have "len \<noteq> 1" using m'_def valid_before by auto
            then have geq2: "len \<ge> 2" using len_pos by linarith
            have "ivl_restr_a2_map I ts' (tp - len + 1) a2_map" using second_last_in_zip[OF geq2] valid_before list_all_iff[of _ "zip (linearize tss) [tp - len..<tp]"]
              unfolding I_def by(auto) 
            then have restr_a: "ts_tp_lt I ts' (tp - len + 1) a" unfolding ivl_restr_a2_map_def
              using some_m' m'_def by(auto split:option.splits)
            have "\<exists>(table, tstp')\<in>set (linearize tables). a = tstp' \<and> xs \<in> table"
              using m'_restr some_m' in_m' by fastforce
            then obtain table' tstp'' where defs: "(table', tstp'') \<in> set (linearize tables)" "a = tstp''" "xs \<in> table'" by auto
            have "(table', tstp'') \<notin> set taken" using restr_a  taken_valid defs(2) by auto
            then have in_a: "(table', tstp'') \<in> set (linearize tables')" using defs(1) unfolding tables_split by auto
            show ?thesis
            proof(cases "Mapping.lookup m'' xs")
              case None
              then have eq: "a = tstp" using tstp_combine_def some_m' by auto
              then show ?thesis using in_a defs(2-3) by auto
            next
              case (Some a')
              then have "tstp = max_tstp a' a" using tstp_combine_def some_m' by auto
              then have eq: "tstp = a' \<or> tstp = a" by(cases a'; cases a; auto)
              have restr_a': "ts_tp_lt I ts' (tp - len + 1) a'" using Some unfolding m''_def by(transfer) (auto split:option.splits if_splits)
              have m_lookup: "Mapping.lookup m xs = Some a'" using Some unfolding m''_def by(transfer) (auto split:option.splits if_splits)
              have "xs \<in> Mapping.keys m" using Some unfolding m''_def by(transfer) (auto split:option.splits)
              then have "\<exists>(table, tstp')\<in>set (linearize tables). a' = tstp' \<and> xs \<in> table"
                using m_restr m_lookup eq by fastforce
              then obtain table tstp' where defs': "(table, tstp') \<in> set (linearize tables)" "a' = tstp'" "xs \<in> table" by auto
              have "(table, tstp') \<notin> set taken" using restr_a' restr_a taken_valid defs'(2) by auto
              then have "(table, tstp') \<in> set (linearize tables')" using defs'(1) unfolding tables_split by auto
              then show ?thesis using eq defs'(2-3) in_a defs(2-3) by(auto)
            qed
          qed
          then show "case Mapping.lookup mc xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables'). tstp = tstp' \<and> xs \<in> table" using tstp_def by auto
        qed
        then show ?thesis using mc by auto
      qed
    next
      case a: False
      then show ?thesis
      proof(cases "tp' = tp")
        case True
        then have "Mapping.lookup a2_map'' tp' = Some Mapping.empty" using still_empty by auto
        then show ?thesis by auto
      next
        case False
        then have "Mapping.lookup a2_map'' tp' = Mapping.lookup a2_map tp'" using a unfolding a2_map''_def a2_map'_def
          by (smt (z3) Mapping.lookup_update_neq Mapping_lookup_delete a2_map''_def m_aux_def option.simps(3))
        then have *: "Mapping.lookup a2_map tp' = Some m_aux" using m_aux_def by auto
        have "\<forall>tp'\<in>{tp - len..tp}. case Mapping.lookup a2_map tp' of Some m \<Rightarrow> \<forall>xs\<in>Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables). tstp = tstp' \<and> xs \<in> table" using valid_before by auto
        then have old_cond: "\<forall>xs\<in>Mapping.keys m_aux. case Mapping.lookup m_aux xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables). tstp = tstp' \<and> xs \<in> table"
          using  tp'_in' *  by fastforce
        have "\<forall>xs\<in>Mapping.keys m_aux. case Mapping.lookup m_aux xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables'). tstp = tstp' \<and> xs \<in> table"
        proof 
          fix x
          assume assm: "x \<in> Mapping.keys m_aux"
          then obtain tstp where tstp_def: "Mapping.lookup m_aux x = Some tstp" by (meson Mapping_keys_dest)
          then have "\<exists>(table, tstp')\<in>set (linearize tables). tstp = tstp' \<and> x \<in> table" using old_cond assm by fastforce
          then obtain table tstp' where defs: "(table, tstp') \<in> set (linearize tables)" "tstp = tstp'"  "x \<in> table"
            by auto
          have tp': "tp' \<in> set [tp - len..<tp]" using False tp'_in by auto
          moreover have auxa: "length (linearize tss) = length [tp - len..<tp]"
            using tp_len_assoc valid_before by auto
          ultimately obtain ts'' where pair_def: "(ts'', tp') \<in> set (zip (linearize tss) [tp - len..<tp])" 
            by (metis in_set_impl_in_set_zip2)
          have "tp - (len - 1) \<noteq> tp" using False tp'_in by auto
          then have not_1: "len \<noteq> 1" by auto
          have "len \<noteq> 0" using tp' by auto
          then have geq2: "len \<ge> 2" using not_1 by auto
          have in_aux: "(ts', tp - len + 1) \<in> set (zip (linearize tss) [tp - len..<tp])"
            using second_last_in_zip[OF geq2] by auto
          then have "valid_tstp_map ts' (tp - len + 1) tstp_map" using * ivl_restr list_all_iff[of _ "zip (linearize tss) [tp - len..<tp]"] by auto
          then have tstp_lookup: "Mapping.lookup tstp_map (tp - len + 1) = Some ts'" unfolding valid_tstp_map_def by (auto split:option.splits)
          have map2: "ivl_restr_a2_map I ts'' tp' a2_map" "valid_tstp_map ts'' tp' tstp_map" using pair_def * ivl_restr list_all_iff[of _ "zip (linearize tss) [tp - len..<tp]"] by auto
          have tstp_lookup': "Mapping.lookup tstp_map tp' = Some ts''" using map2(2) unfolding valid_tstp_map_def by (auto split:option.splits)
          have list_all_tstp: "list_all (\<lambda>(x, y). valid_tstp_map x y tstp_map) (zip (linearize tss) [tp - len..<tp])"
            using valid_before unfolding I_def[symmetric] valid_mmuaux'.simps list_all_split' by auto
          have in1: "tp - len + 1 \<in> set [tp - len..<tp]" by (meson in_aux in_set_zipE)
          have "ts_tp_lt I ts'' tp' tstp" using map2 unfolding ivl_restr_a2_map_def using * tstp_def by(auto split:option.splits)
          moreover have tp_leq: "tp - len + 1 < tp'" using tp'_in a by auto
          moreover have "ts'' \<ge> ts'" using tstp_le_aux[OF tstp_lookup tstp_lookup' in1 tp' tp_leq _ _ auxa list_all_tstp]
            using valid_before by auto
          ultimately have aux: "ts_tp_lt I ts' (tp - len + 1) tstp" unfolding ts_tp_lt_def by(auto split:sum.splits)
          have "(table, tstp') \<notin> set taken"
          proof(rule ccontr)
            assume "\<not> (table, tstp') \<notin> set taken"
            then have "\<not>(ts_tp_lt I ts' (tp - len + 1) tstp)" using taken_valid using \<open>tstp = tstp'\<close> by fastforce
            then show "False" using aux by auto
          qed
          then have "(table, tstp') \<in> set (linearize tables')" using defs(1) unfolding tables_split by auto
          then show "case Mapping.lookup m_aux x of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables'). tstp = tstp' \<and> x \<in> table" using tstp_def defs(2-3) by auto
        qed
        then show ?thesis using m_aux_def by auto
      qed
    qed
  qed
  have result': "(case Mapping.lookup a2_map'' (tp - (len - 1)) of Some m \<Rightarrow> result' = Mapping.keys m | _ \<Rightarrow> False)"
    using len_not_0 m'_def Suc_diff_le[OF len_tp]
    by (auto simp: a2_map''_def a2_map'_def result'_def result_def mc_def m_eq m_del_def lookup_old Mapping_lookup_delete lookup_update' split: option.splits)
  have "\<forall> (a, b) \<in> set (linearize tables). case b of Inl ts \<Rightarrow> ts \<le> cur | Inr tp' \<Rightarrow> tp' \<le> tp" using valid_before by auto
  moreover have "set (linearize tables') \<subseteq> set (linearize tables)" unfolding tables_split by auto
  ultimately have valid_table_restr: "\<forall>(a, b) \<in> set (linearize tables'). case b of Inl ts \<Rightarrow> ts \<le> cur | Inr tp' \<Rightarrow> tp' \<le> tp" by auto
  have "Mapping.keys tstp_map = {tp - len..tp - 1}" using valid_before len_not_0 by auto
  then have "Mapping.keys tstp_map' = (if len - 1 > 0 then {tp - (len - 1)..tp - 1} else {})" unfolding tstp_map'_def tp_len_assoc[symmetric] using Suc_diff_le by auto
  moreover have "Suc (length auxlist - Suc 0) = length auxlist"
    using assms(2) valid_before
    by (cases auxlist) (auto simp: aux_def)
  ultimately show ?thesis
    using valid_before a2_map''_keys sorted_tl list_all' lookup'' list_all2'' list_all'' lin_ts still_empty sorted_tables' isl_tables' valid_tables' valid_table_restr
    unfolding eval_step_mmuaux_eq valid_mmuaux'.simps tl_aux_def aux_def I_def n_def R_def pos_def
    using lin_tss_not_Nil safe_hd_eq len_pos Suc_diff_le result'_def result'
    by (auto simp add: list.set_sel(2) lin_tss' lin_tss''' tl_queue_rep[of tss'] min_auxlist_done)
qed

lemma done_empty_valid_mmuaux'_intro:
  assumes "valid_mmuaux' args cur dt
    (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done) auxlist"
  shows "valid_mmuaux' args cur dt'
    (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, [])
    (drop (length done) auxlist)"
  using assms sorted_drop by (auto simp add: drop_map[symmetric])

lemma valid_mmuaux'_mono:
  assumes "valid_mmuaux' args cur dt aux auxlist" "dt \<le> dt'"
  shows "valid_mmuaux' args cur dt' aux auxlist"
  using assms less_le_trans by (cases aux) (fastforce simp: memR_antimono)

lemma valid_foldl_eval_step_mmuaux':
  assumes valid_before: "valid_mmuaux' args cur dt aux auxlist"
    "lin_ts_mmuaux aux = tss @ tss'"
    "\<And>ts. ts \<in> set (take (length tss) (lin_ts_mmuaux aux)) \<Longrightarrow> \<not> memR (args_ivl args) (dt - ts)"
  shows "valid_mmuaux' args cur dt (foldl (\<lambda>aux _. eval_step_mmuaux args aux) aux tss) auxlist \<and>
    lin_ts_mmuaux (foldl (\<lambda>aux _. eval_step_mmuaux args aux) aux tss) = tss'"
  using assms
proof (induction tss arbitrary: aux)
  case (Cons ts tss)
  have app_ass: "lin_ts_mmuaux aux = ts # (tss @ tss')"
    using Cons(3) by auto
  have "\<not> memR (args_ivl args) (dt - ts)"
    using Cons by auto
  then have valid_step: "valid_mmuaux' args cur dt (eval_step_mmuaux args aux) auxlist"
    "lin_ts_mmuaux (eval_step_mmuaux args aux) = tss @ tss'"
    using valid_eval_step_mmuaux'[OF Cons(2) app_ass] by auto
  show ?case
    using Cons(1)[OF valid_step] valid_step Cons(4) app_ass by auto
qed auto

lemma sorted_dropWhile_filter: "sorted xs \<Longrightarrow> dropWhile (\<lambda>t. \<not> memR I (nt - t)) xs =
  filter (\<lambda>t. memR I (nt - t)) xs"
proof (induction xs)
  case (Cons x xs)
  then show ?case
  proof (cases "\<not> memR I (nt - x)")
    case False
    then have neg: "memR I (nt - x)"
      by auto
    with Cons have "\<And>z. z \<in> set xs \<Longrightarrow> memR I (nt - z)"
      by (auto simp: diff_le_mono2)
    with False show ?thesis
      using filter_empty_conv by auto
  qed auto
qed auto

fun shift_mmuaux :: "args \<Rightarrow> ts \<Rightarrow> event_data mmuaux \<Rightarrow> event_data mmuaux" where
  "shift_mmuaux args nt (tp, tss, len, maskL, maskR, result, a1_map, a2_map, done, done_length) =
    (let (tss_queue, tss') = takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss in
    foldl (\<lambda>aux _. eval_step_mmuaux args aux) (tp, tss', len, maskL, maskR,
      result, a1_map, a2_map, done, done_length) (linearize tss_queue))"

lemma valid_shift_mmuaux':
  assumes "valid_mmuaux' args cur cur aux auxlist" "nt \<ge> cur"
  shows "valid_mmuaux' args cur nt (shift_mmuaux args nt aux) auxlist \<and>
    (\<forall>ts \<in> set (lin_ts_mmuaux (shift_mmuaux args nt aux)). memR (args_ivl args) (nt - ts))"
proof -
  define I where "I = args_ivl args"
  define pos where "pos = args_pos args"
  have valid_folded: "valid_mmuaux' args cur nt aux auxlist"
    using assms(1,2) valid_mmuaux'_mono unfolding valid_mmuaux_def by blast
  obtain tp len tss tables maskL maskR result a1_map a2_map tstp_map "done" where aux_def:
    "aux = (tp, tss, len, tables, maskL, maskR, result, a1_map, a2_map, tstp_map, done)"
    by (cases aux) auto
  note valid_before = valid_folded[unfolded aux_def]
  define tss_list where "tss_list =
    linearize (fst (takeWhile_queue (\<lambda>t. \<not> memR I (nt - t)) tss))"
  define tss' where "tss' = snd (takeWhile_queue (\<lambda>t. \<not> memR I (nt - t)) tss)"
  let ?aux = "(tp, tss', len, tables, maskL, maskR, result, a1_map, a2_map, tstp_map, done)"
  have tss_list_takeWhile: "tss_list = takeWhile (\<lambda>t. \<not> memR I (nt - t)) (linearize tss)"
    using tss_list_def unfolding takeWhile_queue_rep_fst .
  then obtain tss_list' where tss_list'_def: "linearize tss = tss_list @ tss_list'"
    "tss_list' = dropWhile (\<lambda>t. \<not> memR I (nt - t)) (linearize tss)"
    by auto
  obtain tp' len' tss' tables' maskL' maskR' a1_map' a2_map' "done'" done_length' where
    foldl_aux_def: "(tp', tss', tables', len', maskL', maskR', a1_map', a2_map',
      done', done_length') = foldl (\<lambda>aux _. eval_step_mmuaux args aux) ?aux tss_list"
    by (cases "foldl (\<lambda>aux _. eval_step_mmuaux args aux) ?aux tss_list") auto
  have lin_tss_aux: "lin_ts_mmuaux ?aux = linearize tss"
    unfolding aux_def tss'_def lin_ts_mmuaux.simps takeWhile_queue_rep_snd by auto
  then have valid_aux: "valid_mmuaux' args cur nt ?aux auxlist" using valid_before by(auto)
  have "take (length tss_list) (lin_ts_mmuaux ?aux) = tss_list"
    unfolding lin_tss_aux using tss_list'_def(1) by auto
  then have valid_foldl: "valid_mmuaux' args cur nt
    (foldl (\<lambda>aux _. eval_step_mmuaux args aux) ?aux tss_list) auxlist"
    "lin_ts_mmuaux (foldl (\<lambda>aux _. eval_step_mmuaux args aux) ?aux tss_list) = tss_list'"
    using valid_foldl_eval_step_mmuaux'[OF valid_aux, unfolded lin_tss_aux, OF tss_list'_def(1) ]
       tss_list_takeWhile set_takeWhileD
    unfolding lin_tss_aux I_def by fastforce+
  have shift_mmuaux_eq: "shift_mmuaux args nt aux = foldl (\<lambda>aux _. eval_step_mmuaux args aux) ?aux tss_list"
    using tss_list_def unfolding aux_def I_def tss'_def by (auto split:prod.splits)
  have "\<And>ts. ts \<in> set tss_list' \<Longrightarrow> memR (args_ivl args) (nt - ts)"
    using sorted_dropWhile_filter tss_list'_def(2) valid_before unfolding I_def by auto
  then show ?thesis
    using valid_foldl(1)[unfolded shift_mmuaux_eq[symmetric]]
    unfolding valid_foldl(2)[unfolded shift_mmuaux_eq[symmetric]] by auto
qed

lift_definition upd_set' :: "('a, 'b) mapping \<Rightarrow> 'b \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>m d f X a. (if a \<in> X then (case Mapping.lookup m a of Some b \<Rightarrow> Some (f b) | None \<Rightarrow> Some d)
    else Mapping.lookup m a)" .

lemma upd_set'_lookup: "Mapping.lookup (upd_set' m d f X) a = (if a \<in> X then
  (case Mapping.lookup m a of Some b \<Rightarrow> Some (f b) | None \<Rightarrow> Some d) else Mapping.lookup m a)"
  by (simp add: Mapping.lookup.rep_eq upd_set'.rep_eq)

lemma upd_set'_keys: "Mapping.keys (upd_set' m d f X) = Mapping.keys m \<union> X"
  by (auto simp add: upd_set'_lookup intro!: Mapping_keys_intro
      dest!: Mapping_keys_dest split: option.splits)

lift_definition upd_nested :: "('a, ('b, 'c) mapping) mapping \<Rightarrow>
  'c \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a, ('b, 'c) mapping) mapping" is
  "\<lambda>m d f X a. case Mapping.lookup m a of Some m' \<Rightarrow> Some (upd_set' m' d f {b. (a, b) \<in> X})
  | None \<Rightarrow> if a \<in> fst ` X then Some (upd_set' Mapping.empty d f {b. (a, b) \<in> X}) else None" .

lemma upd_nested_lookup: "Mapping.lookup (upd_nested m d f X) a =
  (case Mapping.lookup m a of Some m' \<Rightarrow> Some (upd_set' m' d f {b. (a, b) \<in> X})
  | None \<Rightarrow> if a \<in> fst ` X then Some (upd_set' Mapping.empty d f {b. (a, b) \<in> X}) else None)"
  by (simp add: Mapping.lookup.abs_eq upd_nested.abs_eq)

lemma upd_nested_keys: "Mapping.keys (upd_nested m d f X) = Mapping.keys m \<union> fst ` X"
  by (auto simp add: upd_nested_lookup Domain.DomainI fst_eq_Domain intro!: Mapping_keys_intro
      dest!: Mapping_keys_dest split: option.splits)

fun add_new_mmuaux :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> event_data mmuaux \<Rightarrow> event_data mmuaux" where
  "add_new_mmuaux args rel1 rel2 nt aux =
    (let (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done) =
    shift_mmuaux args nt aux;
    I = args_ivl args; pos = args_pos args;
    new_tstp = (if memL I 0 then Inr tp else Inl nt);
    tstp_map = Mapping.update tp nt tstp_map;
    tmp = \<Union>((\<lambda>as. case Mapping.lookup a1_map (proj_tuple maskL as) of None \<Rightarrow>
      (if \<not>pos then {(tp - len, as)} else {})
      | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
      else {(max (tp - len) (tp' + 1), as)}) ` rel2) \<union> (if memL I 0 then {tp} \<times> rel2 else {});
    tmp = Set.filter (\<lambda>(tp, as). case Mapping.lookup tstp_map tp of Some ts \<Rightarrow> memL I (nt - ts)) tmp;
    table = snd ` tmp;
    tables = append_queue (table, if memL I 0 then Inr tp else Inl nt) tables;
    a2_map = Mapping.update (tp + 1) Mapping.empty
      (upd_nested a2_map new_tstp (max_tstp new_tstp) tmp);
    a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
      (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
    tss = append_queue nt tss in
    (tp + 1, tss, tables, len + 1, maskL, maskR, result \<union> snd ` (Set.filter (\<lambda>(t, x). t = tp - len) tmp), a1_map, a2_map, tstp_map, done))"

lemma fst_case: "(\<lambda>x. fst (case x of (t, a1, a2) \<Rightarrow> (t, y t a1 a2, z t a1 a2))) = fst"
  by auto

lemma list_all2_in_setE: "list_all2 P xs ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> (\<And>y. y \<in> set ys \<Longrightarrow> P x y \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (fastforce simp: list_all2_iff set_zip in_set_conv_nth)

lemma list_all2_zip: "list_all2 (\<lambda>x y. triple_eq_pair x y f g) xs (zip ys zs) \<Longrightarrow>
  (\<And>y. y \<in> set ys \<Longrightarrow> Q y) \<Longrightarrow> x \<in> set xs \<Longrightarrow> Q (fst x)"
  by (auto simp: in_set_zip elim!: list_all2_in_setE triple_eq_pair.elims)

lemma take_takeWhile: "n \<le> length ys \<Longrightarrow>
  (\<And>y. y \<in> set (take n ys) \<Longrightarrow> P y) \<Longrightarrow>
  (\<And>y. y \<in> set (drop n ys) \<Longrightarrow> \<not>P y) \<Longrightarrow>
  take n ys = takeWhile P ys"
proof (induction ys arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  then show ?case by (cases n) simp_all
qed

lemma valid_add_new_mmuaux:
  assumes valid_before: "valid_mmuaux args cur aux auxlist"
    and tabs: "table (args_n args) (args_L args) rel1" "table (args_n args) (args_R args) rel2"
    and nt_mono: "nt \<ge> cur"
  shows "valid_mmuaux args nt (add_new_mmuaux args rel1 rel2 nt aux)
    (update_until args rel1 rel2 nt auxlist)"
proof -
  define I where "I = args_ivl args"
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  have valid_folded: "valid_mmuaux' args cur nt aux auxlist"
    using assms(1,4) valid_mmuaux'_mono unfolding valid_mmuaux_def by blast
  obtain tp len tss tables maskL maskR result a1_map a2_map tstp_map "done" where shift_aux_def:
    "shift_mmuaux args nt aux = (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done)"
    by (cases "shift_mmuaux args nt aux") auto
  have valid_shift_aux: "valid_mmuaux' args cur nt (tp, tss, tables, len, maskL, maskR,
    result, a1_map, a2_map, tstp_map, done) auxlist"
    "\<And>ts. ts \<in> set (linearize tss) \<Longrightarrow> memR (args_ivl args) (nt - ts)"
    using valid_shift_mmuaux'[OF assms(1)[unfolded valid_mmuaux_def] assms(4)]
    unfolding shift_aux_def by auto
  define new_tstp where "new_tstp = (if memL I 0 then Inr tp else Inl nt)"
  have new_tstp_lt_isl: "tstp_lt new_tstp nt (tp + 1)"
    "isl new_tstp \<longleftrightarrow> \<not> memL I 0"
    by (auto simp add: new_tstp_def tstp_lt_def)
  define tmp where "tmp = \<Union>((\<lambda>as. case Mapping.lookup a1_map (proj_tuple maskL as) of None \<Rightarrow>
    (if \<not>pos then {(tp - len, as)} else {})
    | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
    else {(max (tp - len) (tp' + 1), as)}) ` rel2) \<union> (if memL I 0 then {tp} \<times> rel2 else {})"
  define tstp_map' where "tstp_map' = Mapping.update tp nt tstp_map"
  define tmp' where "tmp' = Set.filter (\<lambda>(tp, as). case Mapping.lookup tstp_map' tp of Some ts \<Rightarrow> memL I (nt - ts)) tmp"
  have a1_map_lookup: "\<And>as tp'. Mapping.lookup a1_map as = Some tp' \<Longrightarrow> tp' < tp"
    using valid_shift_aux(1) Mapping_keys_intro by force
  then have fst_tmp: "\<And>tp'. tp' \<in> fst ` tmp' \<Longrightarrow> tp - len \<le> tp' \<and> tp' < tp + 1"
    unfolding tmp'_def tmp_def by (auto simp add: less_SucI split: option.splits if_splits)
  have snd_tmp: "\<And>tp'. table n R (snd ` tmp')"
    using tabs(2) unfolding tmp'_def tmp_def n_def R_def
    by(auto simp add: table_def split: if_splits option.splits) blast+
  define a2_map' where "a2_map' = Mapping.update (tp + 1) Mapping.empty
    (upd_nested a2_map new_tstp (max_tstp new_tstp) tmp')"
  define a1_map' where "a1_map' = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
    (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1)"
  define tss' where "tss' = append_queue nt tss"
  define tables' where "tables' = append_queue (snd ` tmp', if memL I 0 then Inr tp else Inl nt) tables"
  have add_new_mmuaux_eq: "add_new_mmuaux args rel1 rel2 nt aux = (tp + 1, tss', tables', len + 1,
    maskL, maskR, result \<union> snd ` (Set.filter (\<lambda>(t, x). t = tp - len) tmp'), a1_map', a2_map', tstp_map', done)"
    using shift_aux_def new_tstp_def tmp_def a2_map'_def a1_map'_def tss'_def tmp'_def tables'_def
    unfolding I_def pos_def tstp_map'_def
    by (auto simp only: add_new_mmuaux.simps Let_def)
  have update_until_eq: "update_until args rel1 rel2 nt auxlist =
    (map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if mem I ((nt - t)) then a2 \<union> join rel2 pos a1 else a2)) auxlist) @
    [(nt, rel1, if memL I 0 then rel2 else empty_table)]"
    unfolding update_until_def I_def pos_def by simp
  have len_done_auxlist: "length done \<le> length auxlist"
    using valid_shift_aux by auto
  have auxlist_split: "auxlist = take (length done) auxlist @ drop (length done) auxlist"
    using len_done_auxlist by auto
  have lin_tss': "linearize tss' = linearize tss @ [nt]"
    unfolding tss'_def append_queue_rep by (rule refl)
  have len_lin_tss': "length (linearize tss') = len + 1"
    unfolding lin_tss' using valid_shift_aux by auto
  have tmp: "sorted (linearize tss)" "\<And>t. t \<in> set (linearize tss) \<Longrightarrow> t \<le> cur"
    using valid_shift_aux by auto
  have sorted_lin_tss': "sorted (linearize tss')"
    unfolding lin_tss' using tmp(1) le_trans[OF _ assms(4), OF tmp(2)]
    by (simp add: sorted_append)
  have in_lin_tss: "\<And>t. t \<in> set (linearize tss) \<Longrightarrow>
    t \<le> cur \<and> memR I (cur - t)"
    using valid_shift_aux(1) unfolding I_def by auto
  then have set_lin_tss': "\<forall>t \<in> set (linearize tss'). t \<le> nt \<and> memR I (nt - t)"
    unfolding lin_tss' I_def using le_trans[OF _ assms(4)] valid_shift_aux(2)
    by (auto simp add: not_less)
  have a1_map'_keys: "Mapping.keys a1_map' \<subseteq> Mapping.keys a1_map \<union> rel1"
    unfolding a1_map'_def using Mapping.keys_filter Mapping_upd_set_keys
    by (auto simp add: Mapping_upd_set_keys split: if_splits dest: Mapping_keys_filterD)
  then have tab_a1_map'_keys: "table n L (Mapping.keys a1_map')"
    using valid_shift_aux(1) tabs(1) by (auto simp add: table_def n_def L_def)
  have a2_map_keys: "Mapping.keys a2_map = {tp - len..tp}"
    using valid_shift_aux by auto
  have a2_map'_keys: "Mapping.keys a2_map' = {tp - len..tp + 1}"
    unfolding a2_map'_def Mapping.keys_update upd_nested_keys a2_map_keys using fst_tmp
    by fastforce
  then have a2_map'_keys': "Mapping.keys a2_map' = {tp + 1 - (len + 1)..tp + 1}"
    by auto
  have len_upd_until: "length done + (len + 1) = length (update_until args rel1 rel2 nt auxlist)"
    using valid_shift_aux unfolding update_until_eq by auto
  have set_take_auxlist: "\<And>x. x \<in> set (take (length done) auxlist) \<Longrightarrow> check_before I nt x"
    using valid_shift_aux unfolding I_def by auto
  have list_all2_triple: "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map)
    (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map)) (drop (length done) auxlist)
    (zip (linearize tss) [tp - len..<tp])"
    using valid_shift_aux unfolding I_def pos_def by auto
  have set_drop_auxlist: "\<And>x. x \<in> set (drop (length done) auxlist) \<Longrightarrow> \<not>check_before I nt x"
    using valid_shift_aux(2)[OF list_all2_zip[OF list_all2_triple,
      of "\<lambda>y. y \<in> set (linearize tss)"]]
    unfolding I_def by auto
  have length_done_auxlist: "length done \<le> length auxlist"
    using valid_shift_aux by auto
  have take_auxlist_takeWhile: "take (length done) auxlist = takeWhile (check_before I nt) auxlist"
    using take_takeWhile[OF length_done_auxlist set_take_auxlist set_drop_auxlist] .
  have "length done = length (takeWhile (check_before I nt) auxlist)"
    by (metis (no_types) add_diff_cancel_right' auxlist_split diff_diff_cancel
        length_append length_done_auxlist length_drop take_auxlist_takeWhile)
  then have set_take_auxlist': "\<And>x. x \<in> set (take (length done)
    (update_until args rel1 rel2 nt auxlist)) \<Longrightarrow> check_before I nt x"
    by (metis I_def length_map map_proj_thd_update_until set_takeWhileD takeWhile_eq_take)
  have rev_done: "rev done = map (eval_args_agg args) (map proj_thd (take (length done) auxlist))"
    using valid_shift_aux by auto
  moreover have "\<dots> = map (eval_args_agg args) (map proj_thd (takeWhile (check_before I nt)
    (update_until args rel1 rel2 nt auxlist)))"
    by (simp add: take_auxlist_takeWhile I_def) (metis List.map.compositionality map_proj_thd_update_until)
  finally have rev_done': "rev done = map (eval_args_agg args) (map proj_thd (take (length done)
    (update_until args rel1 rel2 nt auxlist)))"
    by (metis length_map length_rev takeWhile_eq_take)
  have map_fst_auxlist_take: "\<And>t. t \<in> set (map fst (take (length done) auxlist)) \<Longrightarrow> t \<le> nt"
    using set_take_auxlist linear by fastforce
  have map_fst_auxlist_drop: "\<And>t. t \<in> set (map fst (drop (length done) auxlist)) \<Longrightarrow> t \<le> nt"
    using in_lin_tss[OF list_all2_zip[OF list_all2_triple, of "\<lambda>y. y \<in> set (linearize tss)"]]
      assms(4) dual_order.trans by auto blast
  have set_drop_auxlist_cong: "\<And>x t a1 a2. x \<in> set (drop (length done) auxlist) \<Longrightarrow>
    x = (t, a1, a2) \<Longrightarrow> mem I ((nt - t)) \<longleftrightarrow> memL I (nt - t)"
  proof -
    fix x t a1 a2
    assume "x \<in> set (drop (length done) auxlist)" "x = (t, a1, a2)"
    then have "memR I (nt - t)"
      using set_drop_auxlist not_less
      by auto
    then show "mem I (nt - t) \<longleftrightarrow> memL I (nt - t)"
      by auto
  qed
  note list_all_split' = list_all_split[of "\<lambda>ts' tp'. ivl_restr_a2_map I ts' tp' a2_map" "\<lambda>ts' tp'. valid_tstp_map ts' tp' tstp_map"]
  have valid_tstp_map: "list_all (\<lambda>(x, y). valid_tstp_map x y tstp_map) (zip (linearize tss) [tp - len..<tp])" 
    using valid_shift_aux unfolding I_def[symmetric] valid_mmuaux'.simps list_all_split' by auto
  have length_tss: "length (linearize tss) = length [tp - len..<tp]" using valid_shift_aux by auto
  have sorted_fst_auxlist: "sorted (map fst auxlist)"
    using valid_shift_aux by auto
  have set_map_fst_auxlist: "\<And>t. t \<in> set (map fst auxlist) \<Longrightarrow> t \<le> nt"
    using arg_cong[OF auxlist_split, of "map fst", unfolded map_append] map_fst_auxlist_take
      map_fst_auxlist_drop by auto
  have lookup_a1_map_keys: "\<And>xs tp'. Mapping.lookup a1_map xs = Some tp' \<Longrightarrow> tp' < tp"
    using valid_shift_aux Mapping_keys_intro by force
  have lookup_a1_map_keys': "\<forall>xs \<in> Mapping.keys a1_map'.
    case Mapping.lookup a1_map' xs of Some tp' \<Rightarrow> tp' < tp + 1"
    using lookup_a1_map_keys unfolding a1_map'_def
    by (auto simp add: Mapping.lookup_filter Mapping_lookup_upd_set Mapping_upd_set_keys
        split: option.splits dest: Mapping_keys_dest) fastforce+
  have sorted_upd_until: "sorted (map fst (update_until args rel1 rel2 nt auxlist))"
    using sorted_fst_auxlist set_map_fst_auxlist
    unfolding update_until_eq
    by (auto simp add: sorted_append comp_def fst_case)
  have old_tables_restr: "\<forall>(a, b) \<in> set (linearize tables). case b of Inl ts \<Rightarrow> ts \<le> cur |
                                                    Inr tp' \<Rightarrow> tp' \<le> tp" 
    "list_all (\<lambda>k. isl k = (\<not> memL (args_ivl args) 0)) (map snd (linearize tables))"
    "sorted (map (tstp_unpack \<circ> snd) (linearize tables))"
    using valid_shift_aux by auto
  then have sorted_upd_tables: "sorted (map (tstp_unpack \<circ> snd) (linearize tables'))"
  proof(cases "memL I 0")
    case True
    have "\<forall>a \<in> set (map snd (linearize tables)). tstp_unpack a \<le> tp" 
    proof
      fix a
      assume assm: "a \<in> set (map snd (linearize tables))"
      then obtain tp' where "a = Inr tp'" 
        using True old_tables_restr(2) list_all_iff[of _ "map snd (linearize tables)"] I_def 
        by(auto) (metis snd_conv sum.collapse(2))
      then show "tstp_unpack a \<le> tp" using old_tables_restr(1) assm unfolding tstp_unpack_def 
        by(auto split:sum.splits)
    qed
    then show ?thesis unfolding tables'_def append_queue_rep 
      using True sorted_append[of "map (tstp_unpack \<circ> snd) (linearize tables)"] old_tables_restr(3) tstp_unpack_def by auto
  next
    case False
    have "\<forall>a \<in> set (map snd (linearize tables)). tstp_unpack a \<le> cur" 
    proof
      fix a
      assume assm: "a \<in> set (map snd (linearize tables))"
      then obtain ts' where "a = Inl ts'" 
        using False old_tables_restr(2) list_all_iff[of _ "map snd (linearize tables)"] I_def 
        by(auto) (metis snd_conv sum.collapse(1))
      then show "tstp_unpack a \<le> cur" using old_tables_restr(1) assm unfolding tstp_unpack_def 
        by(auto split:sum.splits)
    qed
    then show ?thesis unfolding tables'_def append_queue_rep 
      using nt_mono False sorted_append[of "map (tstp_unpack \<circ> snd) (linearize tables)"] old_tables_restr(3) tstp_unpack_def by auto
  qed
  have new_table_restr1: "\<forall>(a, b) \<in> set (linearize tables'). case b of Inl ts \<Rightarrow> ts \<le> nt |
                                                    Inr tp' \<Rightarrow> tp' \<le> tp + 1" 
    using old_tables_restr(1) nt_mono unfolding tables'_def append_queue_rep 
    by(auto split:prod.splits sum.splits) fastforce+
  have new_table_restr2: "list_all (\<lambda>k. isl k = (\<not> memL (args_ivl args) 0)) (map snd (linearize tables'))" 
    using old_tables_restr(2) unfolding tables'_def append_queue_rep I_def by auto
  have lookup_a2_map: "\<And>tp' m. Mapping.lookup a2_map tp' = Some m \<Longrightarrow>
    table n R (Mapping.keys m) \<and> (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
      tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0))"
    using valid_shift_aux(1) Mapping_keys_intro unfolding I_def n_def R_def by force
  then have lookup_a2_map': "\<And>tp' m xs tstp. Mapping.lookup a2_map tp' = Some m \<Longrightarrow>
    Mapping.lookup m xs = Some tstp \<Longrightarrow> tstp_lt tstp nt tp \<and>
    isl tstp = (\<not> memL I 0)"
    using Mapping_keys_intro assms(4) by (force simp add: tstp_lt_def split: sum.splits)
  have lookup_a2_map'_keys: "\<forall>tp' \<in> Mapping.keys a2_map'.
    case Mapping.lookup a2_map' tp' of Some m \<Rightarrow> table n R (Mapping.keys m) \<and>
    (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
    tstp_lt tstp nt (tp + 1) \<and> isl tstp = (\<not> memL I 0))"
  proof (rule ballI)
    fix tp'
    assume tp'_assm: "tp' \<in> Mapping.keys a2_map'"
    then obtain m' where m'_def: "Mapping.lookup a2_map' tp' = Some m'"
      by (auto dest: Mapping_keys_dest)
    have "table n R (Mapping.keys m') \<and>
      (\<forall>xs \<in> Mapping.keys m'. case Mapping.lookup m' xs of Some tstp \<Rightarrow>
      tstp_lt tstp nt (tp + 1) \<and> isl tstp = (\<not> memL I 0))"
    proof (cases "tp' = tp + 1")
      case True
      show ?thesis
        using m'_def unfolding a2_map'_def True Mapping.lookup_update
        by (auto simp add: table_def)
    next
      case False
      then have tp'_in: "tp' \<in> Mapping.keys a2_map"
        using tp'_assm unfolding a2_map_keys a2_map'_keys by auto
      then obtain m where m_def: "Mapping.lookup a2_map tp' = Some m"
        by (auto dest: Mapping_keys_dest)
      have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp', b) \<in> tmp'}"
        using m_def m'_def unfolding a2_map'_def Mapping.lookup_update_neq[OF False[symmetric]]
          upd_nested_lookup
        by auto
      have "table n R (Mapping.keys m')"
        using lookup_a2_map[OF m_def] snd_tmp unfolding m'_alt upd_set'_keys
        by (auto simp add: table_def)
      moreover have "\<forall>xs \<in> Mapping.keys m'. case Mapping.lookup m' xs of Some tstp \<Rightarrow>
        tstp_lt tstp nt (tp + 1) \<and> isl tstp = (\<not> memL I 0)"
      proof (rule ballI)
        fix xs
        assume xs_assm: "xs \<in> Mapping.keys m'"
        then obtain tstp where tstp_def: "Mapping.lookup m' xs = Some tstp"
          by (auto dest: Mapping_keys_dest)
        have "tstp_lt tstp nt (tp + 1) \<and> isl tstp = (\<not> memL I 0)"
        proof (cases "Mapping.lookup m xs")
          case None
          then show ?thesis
            using tstp_def[unfolded m'_alt upd_set'_lookup] new_tstp_lt_isl
            by (auto split: if_splits)
        next
          case (Some tstp')
          show ?thesis
          proof (cases "xs \<in> {b. (tp', b) \<in> tmp'}")
            case True
            then have tstp_eq: "tstp = max_tstp new_tstp tstp'"
              using tstp_def[unfolded m'_alt upd_set'_lookup] Some
              by auto
            show ?thesis
              using lookup_a2_map'[OF m_def Some] new_tstp_lt_isl
              by (auto simp add: tstp_lt_def tstp_eq max_def split: sum.splits)
          next
            case False
            then show ?thesis
              using tstp_def[unfolded m'_alt upd_set'_lookup] lookup_a2_map'[OF m_def Some] Some
              by (auto simp add: tstp_lt_def split: sum.splits)
          qed
        qed
        then show "case Mapping.lookup m' xs of Some tstp \<Rightarrow>
          tstp_lt tstp nt (tp + 1) \<and> isl tstp = (\<not> memL I 0)"
          using tstp_def by auto
      qed
      ultimately show ?thesis
        by auto
    qed
    then show "case Mapping.lookup a2_map' tp' of Some m \<Rightarrow> table n R (Mapping.keys m) \<and>
      (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
      tstp_lt tstp nt (tp + 1) \<and> isl tstp = (\<not> memL I 0))"
      using m'_def by auto
  qed
  have tp_upt_Suc: "[tp + 1 - (len + 1)..<tp + 1] = [tp - len..<tp] @ [tp]"
    using upt_Suc by auto
  have map_eq: "map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if mem I ((nt - t)) then a2 \<union> join rel2 pos a1 else a2)) (drop (length done) auxlist) =
    map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if memL I (nt - t) then a2 \<union> join rel2 pos a1 else a2)) (drop (length done) auxlist)"
    using set_drop_auxlist_cong by auto
  have "drop (length done) (update_until args rel1 rel2 nt auxlist) =
    map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if mem I ((nt - t)) then a2 \<union> join rel2 pos a1 else a2)) (drop (length done) auxlist) @
    [(nt, rel1, if memL I 0 then rel2 else empty_table)]"
    unfolding update_until_eq using len_done_auxlist drop_map by auto
  note drop_update_until = this[unfolded map_eq]
  have list_all2_old: "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map')
    (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map'))
    (map (\<lambda>(t, a1, a2). (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if memL I (nt - t) then a2 \<union> join rel2 pos a1 else a2)) (drop (length done) auxlist))
    (zip (linearize tss) [tp - len..<tp])"
    unfolding list_all2_map1
    using list_all2_triple
  proof (rule list.rel_mono_strong)
    fix tri pair
    assume tri_pair_in: "tri \<in> set (drop (length done) auxlist)"
      "pair \<in> set (zip (linearize tss) [tp - len..<tp])"
    obtain t a1 a2 where tri_def: "tri = (t, a1, a2)"
      by (cases tri) auto
    obtain ts' tp' where pair_def: "pair = (ts', tp')"
      by (cases pair) auto
    have "valid_tstp_map ts' tp' tstp_map"
       using valid_tstp_map tri_pair_in(2) list_all_iff[of "\<lambda>(x, y). valid_tstp_map x y tstp_map"] 
       unfolding pair_def by auto
    then have tp'_lookup: "Mapping.lookup tstp_map tp' = Some ts'" 
      unfolding valid_tstp_map_def by (auto split:option.splits)
    assume "triple_eq_pair tri pair (\<lambda>tp'. filter_a1_map pos tp' a1_map)
      (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map)"
    then have eqs: "t = ts'" "a1 = filter_a1_map pos tp' a1_map"
      "a2 = filter_a2_map I ts' tp' a2_map"
      unfolding tri_def pair_def by auto
    have tp'_ge: "tp' \<ge> tp - len"
      using tri_pair_in(2) unfolding pair_def
      by (auto elim: in_set_zipE)
    have tp'_lt_tp: "tp' < tp"
      using tri_pair_in(2) unfolding pair_def
      by (auto elim: in_set_zipE)
    have ts'_in_lin_tss: "ts' \<in> set (linearize tss)"
      using tri_pair_in(2) unfolding pair_def
      by (auto elim: in_set_zipE)
    then have ts'_nt: "ts' \<le> nt"
      using valid_shift_aux(1) assms(4) by auto
    then have t_nt: "t \<le> nt"
      unfolding eqs(1) .
    have tp'_set: "tp' \<in> set [tp - len..<tp]" by (simp add: tp'_ge tp'_lt_tp)
    have "table n L (Mapping.keys a1_map)"
      using valid_shift_aux unfolding n_def L_def by auto
    then have a1_tab: "table n L a1"
      unfolding eqs(2) filter_a1_map_def by (auto simp add: table_def)
    note tabR = tabs(2)[unfolded n_def[symmetric] R_def[symmetric]]
    have join_rel2_assms: "L \<subseteq> R" "maskL = join_mask n L"
      using valid_shift_aux unfolding n_def L_def R_def by auto
    have join_rel2_eq: "join rel2 pos a1 = {xs \<in> rel2. proj_tuple_in_join pos maskL xs a1}"
      using join_sub[OF join_rel2_assms(1) a1_tab tabR] join_rel2_assms(2) by auto
    have filter_sub_a2: "\<And>xs m' tp'' tstp. tp'' \<le> tp' \<Longrightarrow>
      Mapping.lookup a2_map' tp'' = Some m' \<Longrightarrow> Mapping.lookup m' xs = Some tstp \<Longrightarrow>
      ts_tp_lt I ts' tp' tstp \<Longrightarrow> (tstp = new_tstp \<Longrightarrow> False) \<Longrightarrow>
      xs \<in> filter_a2_map I ts' tp' a2_map' \<Longrightarrow> xs \<in> a2"
    proof -
      fix xs m' tp'' tstp
      assume m'_def: "tp'' \<le> tp'" "Mapping.lookup a2_map' tp'' = Some m'"
        "Mapping.lookup m' xs = Some tstp" "ts_tp_lt I ts' tp' tstp"
      have tp''_neq: "tp + 1 \<noteq> tp''"
        using le_less_trans[OF m'_def(1) tp'_lt_tp] by auto
      assume new_tstp_False: "tstp = new_tstp \<Longrightarrow> False"
      show "xs \<in> a2"
      proof (cases "Mapping.lookup a2_map tp''")
        case None
        then have m'_alt: "m' = upd_set' Mapping.empty new_tstp (max_tstp new_tstp)
          {b. (tp'', b) \<in> tmp'}"
          using m'_def(2)[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp''_neq]
            upd_nested_lookup] by (auto split: option.splits if_splits)
        then show ?thesis
          using new_tstp_False m'_def(3)[unfolded m'_alt upd_set'_lookup Mapping.lookup_empty]
          by (auto split: if_splits)
      next
        case (Some m)
        then have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp'', b) \<in> tmp'}"
          using m'_def(2)[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp''_neq]
            upd_nested_lookup] by (auto split: option.splits if_splits)
        note lookup_m = Some
        show ?thesis
        proof (cases "Mapping.lookup m xs")
          case None
          then show ?thesis
            using new_tstp_False m'_def(3)[unfolded m'_alt upd_set'_lookup]
            by (auto split: if_splits)
        next
          case (Some tstp')
          have tstp_ok: "tstp = tstp' \<Longrightarrow> xs \<in> a2"
            using eqs(3) lookup_m Some m'_def unfolding filter_a2_map_def by auto
          show ?thesis
          proof (cases "xs \<in> {b. (tp'', b) \<in> tmp'}")
            case True
            then have tstp_eq: "tstp = max_tstp new_tstp tstp'"
              using m'_def(3)[unfolded m'_alt upd_set'_lookup Some] by auto
            show ?thesis
              using lookup_a2_map'[OF lookup_m Some] new_tstp_lt_isl(2)
                tstp_eq new_tstp_False tstp_ok
              by (auto intro: max_tstpE[of new_tstp tstp'])
          next
            case False
            then have "tstp = tstp'"
              using m'_def(3)[unfolded m'_alt upd_set'_lookup Some] by auto
            then show ?thesis
              using tstp_ok by auto
          qed
        qed
      qed
    qed
    have a2_sub_filter: "a2 \<subseteq> filter_a2_map I ts' tp' a2_map'"
    proof (rule subsetI)
      fix xs
      assume xs_in: "xs \<in> a2"
      then obtain tp'' m tstp where m_def: "tp'' \<le> tp'" "Mapping.lookup a2_map tp'' = Some m"
        "Mapping.lookup m xs = Some tstp" "ts_tp_lt I ts' tp' tstp"
        using eqs(3)[unfolded filter_a2_map_def] by (auto split: option.splits)
      have tp''_in: "tp'' \<in> {tp - len..tp}"
        using m_def(2) a2_map_keys by (auto intro!: Mapping_keys_intro)
      then obtain m' where m'_def: "Mapping.lookup a2_map' tp'' = Some m'"
        using a2_map'_keys
        by (metis Mapping_keys_dest One_nat_def add_Suc_right add_diff_cancel_right'
            atLeastatMost_subset_iff diff_zero le_eq_less_or_eq le_less_Suc_eq subsetD)
      have tp''_neq: "tp + 1 \<noteq> tp''"
        using m_def(1) tp'_lt_tp by auto
      have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp'', b) \<in> tmp'}"
        using m'_def[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp''_neq] m_def(2)
          upd_nested_lookup] by (auto split: option.splits if_splits)
      show "xs \<in> filter_a2_map I ts' tp' a2_map'"
      proof (cases "xs \<in> {b. (tp'', b) \<in> tmp'}")
        case True
        then have "Mapping.lookup m' xs = Some (max_tstp new_tstp tstp)"
          unfolding m'_alt upd_set'_lookup m_def(3) by auto
        moreover have "ts_tp_lt I ts' tp' (max_tstp new_tstp tstp)"
          using new_tstp_lt_isl(2) lookup_a2_map'[OF m_def(2,3)]
          by (auto intro: max_tstp_intro''[OF _ m_def(4)])
        ultimately show ?thesis
          unfolding filter_a2_map_def using m_def(1) m'_def m_def(4) by auto
      next
        case False
        then have "Mapping.lookup m' xs = Some tstp"
          unfolding m'_alt upd_set'_lookup m_def(3) by auto
        then show ?thesis
          unfolding filter_a2_map_def using m_def(1) m'_def m_def by auto
      qed
    qed
    have "pos \<Longrightarrow> filter_a1_map pos tp' a1_map' = join a1 True rel1"
    proof -
      assume pos: pos
      note tabL = tabs(1)[unfolded n_def[symmetric] L_def[symmetric]]
      have join_eq: "join a1 True rel1 = a1 \<inter> rel1"
        using join_eq[OF tabL a1_tab] by auto
      show "filter_a1_map pos tp' a1_map' = join a1 True rel1"
        using eqs(2) pos tp'_lt_tp unfolding filter_a1_map_def a1_map'_def join_eq
        by (auto simp add: Mapping.lookup_filter Mapping_lookup_upd_set split: if_splits option.splits
            intro: Mapping_keys_intro dest: Mapping_keys_dest Mapping_keys_filterD)
    qed
    moreover have "\<not>pos \<Longrightarrow> filter_a1_map pos tp' a1_map' = a1 \<union> rel1"
      using eqs(2) tp'_lt_tp unfolding filter_a1_map_def a1_map'_def
      by (auto simp add: Mapping.lookup_filter Mapping_lookup_upd_set intro: Mapping_keys_intro
          dest: Mapping_keys_filterD Mapping_keys_dest split: option.splits)
    moreover have "memL I (nt - t) \<Longrightarrow> filter_a2_map I ts' tp' a2_map' = a2 \<union> join rel2 pos a1"
    proof (rule set_eqI, rule iffI)
      fix xs
      assume in_int: "memL I (nt - t)"
      assume xs_in: "xs \<in> filter_a2_map I ts' tp' a2_map'"
      then obtain m' tp'' tstp where m'_def: "tp'' \<le> tp'" "Mapping.lookup a2_map' tp'' = Some m'"
        "Mapping.lookup m' xs = Some tstp" "ts_tp_lt I ts' tp' tstp"
        unfolding filter_a2_map_def by (fastforce split: option.splits)
      show "xs \<in> a2 \<union> join rel2 pos a1"
      proof (cases "tstp = new_tstp")
        case True
        note tstp_new_tstp = True
        have tp''_neq: "tp + 1 \<noteq> tp''"
          using m'_def(1) tp'_lt_tp by auto
        have tp''_in: "tp'' \<in> {tp - len..tp}"
          using m'_def(1,2) tp'_lt_tp a2_map'_keys
          by (auto intro!: Mapping_keys_intro)
        obtain m where m_def: "Mapping.lookup a2_map tp'' = Some m"
          "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp'', b) \<in> tmp'}"
          using m'_def(2)[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp''_neq]
            upd_nested_lookup] tp''_in a2_map_keys
          by (fastforce dest: Mapping_keys_dest split: option.splits if_splits)
        show ?thesis
        proof (cases "Mapping.lookup m xs = Some new_tstp")
          case True
          then show ?thesis
            using eqs(3) m'_def(1) m_def(1) m'_def tstp_new_tstp
            unfolding filter_a2_map_def by auto
        next
          case False
          then have xs_in_snd_tmp: "xs \<in> {b. (tp'', b) \<in> tmp'}"
            using m'_def(3)[unfolded m_def(2) upd_set'_lookup True]
            by (auto split: if_splits)
          then have xs_in_rel2: "xs \<in> rel2"
            unfolding tmp'_def tmp_def
            by (auto split: if_splits option.splits)
          show ?thesis
          proof (cases pos)
            case True
            obtain tp''' where tp'''_def: "Mapping.lookup a1_map (proj_tuple maskL xs) = Some tp'''"
              "if pos then tp'' = max (tp - len) tp''' else tp'' = max (tp - len) (tp''' + 1)"
              using xs_in_snd_tmp m'_def(1) tp'_lt_tp True
              unfolding tmp'_def tmp_def by (auto split: option.splits if_splits)
            have "proj_tuple maskL xs \<in> a1"
              using eqs(2)[unfolded filter_a1_map_def] True m'_def(1) tp'''_def
              by (auto intro: Mapping_keys_intro)
            then show ?thesis
              using True xs_in_rel2 unfolding proj_tuple_in_join_def join_rel2_eq by auto
          next
            case False
            show ?thesis
            proof (cases "Mapping.lookup a1_map (proj_tuple maskL xs)")
              case None
              then show ?thesis
                using xs_in_rel2 False eqs(2)[unfolded filter_a1_map_def]
                unfolding proj_tuple_in_join_def join_rel2_eq
                by (auto dest: Mapping_keys_dest)
            next
              case (Some tp''')
              then have "tp'' = max (tp - len) (tp''' + 1)"
                using xs_in_snd_tmp m'_def(1) tp'_lt_tp False
                unfolding tmp'_def tmp_def by (auto split: option.splits if_splits)
              then have "tp''' < tp'"
                using m'_def(1) by auto
              then have "proj_tuple maskL xs \<notin> a1"
                using eqs(2)[unfolded filter_a1_map_def] True m'_def(1) Some False
                by (auto intro: Mapping_keys_intro)
              then show ?thesis
                using xs_in_rel2 False unfolding proj_tuple_in_join_def join_rel2_eq by auto
            qed
          qed
        qed
      next
        case False
        then show ?thesis
          using filter_sub_a2[OF m'_def _ xs_in] by auto
      qed
    next
      fix xs
      assume in_int: "memL I (nt - t)"
      assume xs_in: "xs \<in> a2 \<union> join rel2 pos a1"
      then have "xs \<in> a2 \<union> (join rel2 pos a1 - a2)"
        by auto
      then show "xs \<in> filter_a2_map I ts' tp' a2_map'"
      proof (rule UnE)
        assume "xs \<in> a2"
        then show "xs \<in> filter_a2_map I ts' tp' a2_map'"
          using a2_sub_filter by auto
      next
        assume "xs \<in> join rel2 pos a1 - a2"
        then have xs_props: "xs \<in> rel2" "xs \<notin> a2" "proj_tuple_in_join pos maskL xs a1"
          unfolding join_rel2_eq by auto
        have ts_tp_lt_new_tstp: "ts_tp_lt I ts' tp' new_tstp"
          using tp'_lt_tp in_int t_nt eqs(1) unfolding new_tstp_def
          by (auto simp add: ts_tp_lt_def elim: contrapos_np)
        show "xs \<in> filter_a2_map I ts' tp' a2_map'"
        proof (cases pos)
          case True
          then obtain tp''' where tp'''_def: "tp''' \<le> tp'"
            "Mapping.lookup a1_map (proj_tuple maskL xs) = Some tp'''"
            using eqs(2)[unfolded filter_a1_map_def] xs_props(3)[unfolded proj_tuple_in_join_def]
            by (auto dest: Mapping_keys_dest)
          define wtp where "wtp \<equiv> max (tp - len) tp'''"
          have wtp_xs_in: "(wtp, xs) \<in> tmp"
            unfolding wtp_def using tp'''_def tmp_def xs_props(1) True by fastforce
          have wtp_le: "wtp \<le> tp'"
            using tp'''_def(1) tp'_ge unfolding wtp_def by auto
          have wtp_in: "wtp \<in> {tp - len..tp}"
            using tp'''_def(1) tp'_lt_tp unfolding wtp_def by auto
          then have "wtp \<in> (if len > 0 then {tp - len..tp - 1} else {})" using tp'_lt_tp wtp_le by force
          then obtain ts where ts_def: "Mapping.lookup tstp_map wtp = Some ts" 
            using valid_shift_aux unfolding valid_mmuaux'.simps by (metis Mapping_keys_dest)
          have wtp_in': "wtp \<in> set [tp - len..<tp]" using wtp_in wtp_le tp'_lt_tp by auto
          have inL: "memL I (nt - ts)"
          proof(cases "memL I 0")
            case True
            then show ?thesis by auto
          next
            case False
            then have "new_tstp = Inl nt" unfolding new_tstp_def by auto
            moreover have "ts \<le> ts'" 
            proof(cases "wtp = tp'")
              case True
              then show ?thesis using ts_def tp'_lookup by auto
            next
              case False
              then have wtp_le: "wtp < tp'" using wtp_le by auto
              show ?thesis using tstp_le_aux[OF ts_def tp'_lookup wtp_in' tp'_set wtp_le tmp(1) _ length_tss valid_tstp_map] by auto
            qed 
            ultimately show ?thesis using ts_tp_lt_new_tstp unfolding ts_tp_lt_def by auto
          qed
          have wtp_neq: "tp + 1 \<noteq> wtp"
            using wtp_in by auto
          obtain m where m_def: "Mapping.lookup a2_map wtp = Some m"
            using wtp_in a2_map_keys Mapping_keys_dest by fastforce
          obtain m' where m'_def: "Mapping.lookup a2_map' wtp = Some m'"
            using wtp_in a2_map'_keys Mapping_keys_dest by fastforce
          have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (wtp, b) \<in> tmp'}"
            using m'_def[unfolded a2_map'_def Mapping.lookup_update_neq[OF wtp_neq]
              upd_nested_lookup m_def] by auto
          show ?thesis
          proof (cases "Mapping.lookup m xs")
            case None
            thm ts_tp_lt_new_tstp
            have "Mapping.lookup m' xs = Some new_tstp"
              using wtp_xs_in ts_def inL unfolding tmp'_def m'_alt upd_set'_lookup None tstp_map'_def Mapping.lookup_update'
              apply auto using tp'_lt_tp wtp_le by linarith
            then show ?thesis
              unfolding filter_a2_map_def using wtp_le m'_def ts_tp_lt_new_tstp by auto
          next
            case (Some tstp')
            have "Mapping.lookup m' xs = Some (max_tstp new_tstp tstp')"
              using wtp_xs_in ts_def inL unfolding tmp'_def m'_alt upd_set'_lookup Some tstp_map'_def Mapping.lookup_update'
              apply auto using leD tp'_lt_tp wtp_le by blast
            moreover have "ts_tp_lt I ts' tp' (max_tstp new_tstp tstp')"
              using max_tstp_intro' ts_tp_lt_new_tstp lookup_a2_map'[OF m_def Some] new_tstp_lt_isl
              by auto
            ultimately show ?thesis
              using lookup_a2_map'[OF m_def Some] wtp_le m'_def
              unfolding filter_a2_map_def by auto
          qed
        next
          case False
          show ?thesis
          proof (cases "Mapping.lookup a1_map (proj_tuple maskL xs)")
            case None
            then have in_tmp: "(tp - len, xs) \<in> tmp"
              using tmp_def False xs_props(1) by fastforce
            obtain m where m_def: "Mapping.lookup a2_map (tp - len) = Some m"
              using a2_map_keys by (fastforce dest: Mapping_keys_dest)
            obtain m' where m'_def: "Mapping.lookup a2_map' (tp - len) = Some m'"
              using a2_map'_keys by (fastforce dest: Mapping_keys_dest)
            have "tp - len < tp" using le_less_trans tp'_ge tp'_lt_tp by blast
            then have "tp - len \<in> (if len > 0 then {tp - len..tp - 1} else {})" by auto
            then obtain ts where ts_def: "Mapping.lookup tstp_map (tp - len) = Some ts" 
              using valid_shift_aux unfolding valid_mmuaux'.simps by (metis Mapping_keys_dest)
            have inL: "memL I (nt - ts)"
            proof(cases "memL I 0")
              case True
              then show ?thesis by auto
            next
              case False
              then have "new_tstp = Inl nt" unfolding new_tstp_def by auto
              moreover have "ts \<le> ts'"
              proof(cases "tp - len = tp'")
              case True
              then show ?thesis using ts_def tp'_lookup by auto
            next
              case False
              then have wtp_le: "tp - len < tp'" using le_neq_implies_less tp'_ge by presburger
              moreover have "tp - len < tp" using less_trans tp'_lt_tp wtp_le by blast
              ultimately show ?thesis using tstp_le_aux[OF ts_def tp'_lookup _ tp'_set wtp_le tmp(1) _ length_tss valid_tstp_map] by auto
            qed 
              ultimately show ?thesis using ts_tp_lt_new_tstp unfolding ts_tp_lt_def by auto
            qed
            have tp_neq: "tp + 1 \<noteq> tp - len"
              by auto
            have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp - len, b) \<in> tmp'}"
              using m'_def[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp_neq]
                upd_nested_lookup m_def] by auto
            show ?thesis
            proof (cases "Mapping.lookup m xs")
              case None
              have "Mapping.lookup m' xs = Some new_tstp"
                unfolding tmp'_def m'_alt upd_set'_lookup None tstp_map'_def Mapping.lookup_update' 
                using in_tmp inL ts_def apply auto using \<open>tp - len < tp\<close> nat_neq_iff by blast
              then show ?thesis
                unfolding filter_a2_map_def using tp'_ge m'_def ts_tp_lt_new_tstp by auto
            next
              case (Some tstp')
              have "Mapping.lookup m' xs = Some (max_tstp new_tstp tstp')"
                unfolding tmp'_def m'_alt upd_set'_lookup Some tstp_map'_def Mapping.lookup_update'
                using in_tmp ts_def inL using \<open>tp - len < tp\<close> by force
              moreover have "ts_tp_lt I ts' tp' (max_tstp new_tstp tstp')"
                using max_tstp_intro' ts_tp_lt_new_tstp lookup_a2_map'[OF m_def Some] new_tstp_lt_isl
                by auto
              ultimately show ?thesis
                unfolding filter_a2_map_def using tp'_ge m'_def by auto
            qed
          next
            case (Some tp''')
            then have tp'_gt: "tp' > tp'''"
              using xs_props(3)[unfolded proj_tuple_in_join_def] eqs(2)[unfolded filter_a1_map_def]
                False by (auto intro: Mapping_keys_intro)
            define wtp where "wtp \<equiv> max (tp - len) (tp''' + 1)"
            have wtp_xs_in: "(wtp, xs) \<in> tmp"
              unfolding wtp_def tmp_def using xs_props(1) Some False by fastforce
            have wtp_le: "wtp \<le> tp'"
              using tp'_ge tp'_gt unfolding wtp_def by auto
            have wtp_in: "wtp \<in> {tp - len..tp}"
              using tp'_lt_tp tp'_gt unfolding wtp_def by auto
            then have "wtp \<in> (if len > 0 then {tp - len..tp - 1} else {})"
              using tp'_lt_tp wtp_le by force
            then obtain ts where ts_def: "Mapping.lookup tstp_map wtp = Some ts" 
              using valid_shift_aux unfolding valid_mmuaux'.simps by (metis Mapping_keys_dest)
            have wtp_in': "wtp \<in> set [tp - len..<tp]" using wtp_in wtp_le tp'_lt_tp by auto
            have inL: "memL I (nt - ts)"
            proof(cases "memL I 0")
              case True
              then show ?thesis by auto
            next
              case False
              then have "new_tstp = Inl nt" unfolding new_tstp_def by auto
              moreover have "ts \<le> ts'" 
              proof(cases "wtp = tp'")
                case True
                then show ?thesis using ts_def tp'_lookup by auto
              next
                case False
                then have wtp_le: "wtp < tp'" using wtp_le by auto
                show ?thesis using tstp_le_aux[OF ts_def tp'_lookup wtp_in' tp'_set wtp_le tmp(1) _ length_tss valid_tstp_map] by auto
              qed 
              ultimately show ?thesis using ts_tp_lt_new_tstp unfolding ts_tp_lt_def by auto
            qed
            have wtp_neq: "tp + 1 \<noteq> wtp"
              using wtp_in by auto
            obtain m where m_def: "Mapping.lookup a2_map wtp = Some m"
              using wtp_in a2_map_keys Mapping_keys_dest by fastforce
            obtain m' where m'_def: "Mapping.lookup a2_map' wtp = Some m'"
              using wtp_in a2_map'_keys Mapping_keys_dest by fastforce
            have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (wtp, b) \<in> tmp'}"
              using m'_def[unfolded a2_map'_def Mapping.lookup_update_neq[OF wtp_neq]
                upd_nested_lookup m_def] by auto
            show ?thesis
            proof (cases "Mapping.lookup m xs")
              case None
              have "Mapping.lookup m' xs = Some new_tstp"
                using wtp_xs_in ts_def inL unfolding tmp'_def m'_alt upd_set'_lookup None tstp_map'_def Mapping.lookup_update'
                apply auto using leD tp'_lt_tp wtp_le by blast
              then show ?thesis
                unfolding filter_a2_map_def using wtp_le m'_def ts_tp_lt_new_tstp by auto
            next
              case (Some tstp')
              have "Mapping.lookup m' xs = Some (max_tstp new_tstp tstp')"
                using wtp_xs_in ts_def inL unfolding tmp'_def m'_alt upd_set'_lookup Some tstp_map'_def Mapping.lookup_update'
                apply auto using leD tp'_lt_tp wtp_le by blast
              moreover have "ts_tp_lt I ts' tp' (max_tstp new_tstp tstp')"
                using max_tstp_intro' ts_tp_lt_new_tstp lookup_a2_map'[OF m_def Some] new_tstp_lt_isl
                by auto
              ultimately show ?thesis
                using lookup_a2_map'[OF m_def Some] wtp_le m'_def
                unfolding filter_a2_map_def by auto
            qed
          qed
        qed
      qed
    qed
    moreover have "\<not> memL I (nt - t) \<Longrightarrow> filter_a2_map I ts' tp' a2_map' = a2"
    proof (rule set_eqI, rule iffI)
      fix xs
      assume out: "\<not> memL I (nt - t)"
      assume xs_in: "xs \<in> filter_a2_map I ts' tp' a2_map'"
      then obtain m' tp'' tstp where m'_def: "tp'' \<le> tp'" "Mapping.lookup a2_map' tp'' = Some m'"
        "Mapping.lookup m' xs = Some tstp" "ts_tp_lt I ts' tp' tstp"
        unfolding filter_a2_map_def by (fastforce split: option.splits)
      have new_tstp_False: "tstp = new_tstp \<Longrightarrow> False"
        using m'_def t_nt out tp'_lt_tp unfolding eqs(1)
        by (auto simp add: ts_tp_lt_def new_tstp_def split: if_splits elim: contrapos_np)
      show "xs \<in> a2"
        using filter_sub_a2[OF m'_def new_tstp_False xs_in] .
    next
      fix xs
      assume "xs \<in> a2"
      then show "xs \<in> filter_a2_map I ts' tp' a2_map'"
        using a2_sub_filter by auto
    qed
    ultimately show "triple_eq_pair (case tri of (t, a1, a2) \<Rightarrow>
      (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if memL I (nt - t) then a2 \<union> join rel2 pos a1 else a2))
      pair (\<lambda>tp'. filter_a1_map pos tp' a1_map') (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map')"
      using eqs unfolding tri_def pair_def by auto
  qed
  have filter_a1_map_rel1: "filter_a1_map pos tp a1_map' = rel1"
    unfolding filter_a1_map_def a1_map'_def using leD lookup_a1_map_keys
    by (force simp add: a1_map_lookup less_imp_le_nat Mapping.lookup_filter
        Mapping_lookup_upd_set keys_is_none_rep dest: Mapping_keys_filterD
        intro: Mapping_keys_intro split: option.splits)
  have filter_a1_map_rel2: "filter_a2_map I nt tp a2_map' =
    (if memL I 0 then rel2 else empty_table)"
  proof (cases "memL I 0")
    case True
    note left_I_zero = True
    have "\<And>tp' m' xs tstp. tp' \<le> tp \<Longrightarrow> Mapping.lookup a2_map' tp' = Some m' \<Longrightarrow>
      Mapping.lookup m' xs = Some tstp \<Longrightarrow> ts_tp_lt I nt tp tstp \<Longrightarrow> xs \<in> rel2"
    proof -
      fix tp' m' xs tstp
      assume lassms: "tp' \<le> tp" "Mapping.lookup a2_map' tp' = Some m'"
        "Mapping.lookup m' xs = Some tstp" "ts_tp_lt I nt tp tstp"
      have tp'_neq: "tp + 1 \<noteq> tp'"
        using lassms(1) by auto
      have tp'_in: "tp' \<in> {tp - len..tp}"
        using lassms(1,2) a2_map'_keys tp'_neq by (auto intro!: Mapping_keys_intro)
      obtain m where m_def: "Mapping.lookup a2_map tp' = Some m"
        "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp', b) \<in> tmp'}"
        using lassms(2)[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp'_neq]
          upd_nested_lookup] tp'_in a2_map_keys
        by (fastforce dest: Mapping_keys_dest intro: Mapping_keys_intro split: option.splits)
      have "xs \<in> {b. (tp', b) \<in> tmp'}"
      proof (rule ccontr)
        assume "xs \<notin> {b. (tp', b) \<in> tmp'}"
        then have Some: "Mapping.lookup m xs = Some tstp"
          using lassms(3)[unfolded m_def(2) upd_set'_lookup] by auto
        show "False"
          using lookup_a2_map'[OF m_def(1) Some] lassms(4) left_I_zero
          by (auto simp add: tstp_lt_def ts_tp_lt_def split: sum.splits)
      qed
      then show "xs \<in> rel2"
        unfolding tmp'_def tmp_def by (auto split: option.splits if_splits)
    qed
    moreover have "\<And>xs. xs \<in> rel2 \<Longrightarrow> \<exists>m' tstp. Mapping.lookup a2_map' tp = Some m' \<and>
      Mapping.lookup m' xs = Some tstp \<and> ts_tp_lt I nt tp tstp"
    proof -
      fix xs
      assume lassms: "xs \<in> rel2"
      obtain m' where m'_def: "Mapping.lookup a2_map' tp = Some m'"
        using a2_map'_keys by (fastforce dest: Mapping_keys_dest)
      have tp_neq: "tp + 1 \<noteq> tp"
        by auto
      obtain m where m_def: "Mapping.lookup a2_map tp = Some m"
        "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp, b) \<in> tmp'}"
        using m'_def a2_map_keys unfolding a2_map'_def Mapping.lookup_update_neq[OF tp_neq]
          upd_nested_lookup
        by (auto dest: Mapping_keys_dest split: option.splits if_splits)
           (metis Mapping_keys_dest atLeastAtMost_iff diff_le_self le_eq_less_or_eq
            option.simps(3))
      have "tp \<in> Mapping.keys tstp_map'" using valid_shift_aux unfolding valid_mmuaux'.simps
        by (simp add: \<open>\<And>tsa. tsa \<in> set (linearize tss) \<Longrightarrow> memR (args_ivl args) (nt - tsa)\<close> Mapping_lookup_update keys_is_none_rep tstp_map'_def)
      then obtain ts where ts_def: "Mapping.lookup tstp_map' tp = Some ts" 
        using valid_shift_aux unfolding valid_mmuaux'.simps by (meson Mapping_keys_dest)
      have xs_in_tmp: "xs \<in> {b. (tp, b) \<in> tmp'}"
        using lassms left_I_zero ts_def unfolding tstp_map'_def tmp'_def tmp_def by auto
      show "\<exists>m' tstp. Mapping.lookup a2_map' tp = Some m' \<and>
        Mapping.lookup m' xs = Some tstp \<and> ts_tp_lt I nt tp tstp"
      proof (cases "Mapping.lookup m xs")
        case None
        moreover have "Mapping.lookup m' xs = Some new_tstp"
          using xs_in_tmp unfolding m_def(2) upd_set'_lookup None by auto
        moreover have "ts_tp_lt I nt tp new_tstp"
          using left_I_zero new_tstp_def by (auto simp add: ts_tp_lt_def)
        ultimately show ?thesis
          using xs_in_tmp m_def
          unfolding a2_map'_def Mapping.lookup_update_neq[OF tp_neq] upd_nested_lookup by auto
      next
        case (Some tstp')
        moreover have "Mapping.lookup m' xs = Some (max_tstp new_tstp tstp')"
          using xs_in_tmp unfolding m_def(2) upd_set'_lookup Some by auto
        moreover have "ts_tp_lt I nt tp (max_tstp new_tstp tstp')"
          using max_tstpE[of new_tstp tstp'] lookup_a2_map'[OF m_def(1) Some] new_tstp_lt_isl left_I_zero
          by (auto simp add: sum.discI(1) new_tstp_def ts_tp_lt_def tstp_lt_def split: sum.splits)
        ultimately show ?thesis
          using xs_in_tmp m_def
          unfolding a2_map'_def Mapping.lookup_update_neq[OF tp_neq] upd_nested_lookup by auto
      qed
    qed
    ultimately show ?thesis
      unfolding filter_a2_map_def
      using True by (fastforce split: option.splits)
  next
    case False
    note left_I_pos = False
    have "\<And>tp' m xs tstp. tp' \<le> tp \<Longrightarrow> Mapping.lookup a2_map' tp' = Some m \<Longrightarrow>
      Mapping.lookup m xs = Some tstp \<Longrightarrow> \<not>(ts_tp_lt I nt tp tstp)"
    proof -
      fix tp' m' xs tstp
      assume lassms: "tp' \<le> tp" "Mapping.lookup a2_map' tp' = Some m'"
        "Mapping.lookup m' xs = Some tstp"
      from lassms(1) have tp'_neq_Suc_tp: "tp + 1 \<noteq> tp'"
        by auto
      show "\<not>(ts_tp_lt I nt tp tstp)"
      proof (cases "Mapping.lookup a2_map tp'")
        case None
        then have tp'_in_tmp: "tp' \<in> fst ` tmp'" and
          m'_alt: "m' = upd_set' Mapping.empty new_tstp (max_tstp new_tstp) {b. (tp', b) \<in> tmp'}"
          using lassms(2) unfolding a2_map'_def Mapping.lookup_update_neq[OF tp'_neq_Suc_tp]
            upd_nested_lookup by (auto split: if_splits)
        then have "tstp = new_tstp"
          using lassms(3)[unfolded m'_alt upd_set'_lookup]
          by (auto split: if_splits)
        then show ?thesis
          using False by (auto simp add: ts_tp_lt_def new_tstp_def split: if_splits sum.splits)
      next
        case (Some m)
        then have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp', b) \<in> tmp'}"
          using lassms(2) unfolding a2_map'_def Mapping.lookup_update_neq[OF tp'_neq_Suc_tp]
            upd_nested_lookup by auto
        note lookup_a2_map_tp' = Some
        show ?thesis
        proof (cases "Mapping.lookup m xs")
          case None
          then have "tstp = new_tstp"
            using lassms(3) unfolding m'_alt upd_set'_lookup by (auto split: if_splits)
          then show ?thesis
            using False by (auto simp add: ts_tp_lt_def new_tstp_def split: if_splits sum.splits)
        next
          case (Some tstp')
          show ?thesis
          proof (cases "xs \<in> {b. (tp', b) \<in> tmp'}")
            case True
            then have tstp_eq: "tstp = max_tstp new_tstp tstp'"
              using lassms(3)
              unfolding m'_alt upd_set'_lookup Some by auto
            show ?thesis
              using max_tstpE[of new_tstp tstp'] lookup_a2_map'[OF lookup_a2_map_tp' Some] new_tstp_lt_isl left_I_pos
              by (auto simp add: tstp_eq tstp_lt_def ts_tp_lt_def new_tstp_def split: sum.splits)
          next
            case False
            then show ?thesis
              using lassms(3) lookup_a2_map'[OF lookup_a2_map_tp' Some]
                nat_le_linear[of nt "case tstp of Inl ts \<Rightarrow> ts"]
              unfolding m'_alt upd_set'_lookup Some
              by (auto simp add: ts_tp_lt_def tstp_lt_def split: sum.splits)
          qed
        qed
      qed
    qed
    then show ?thesis
      using False by (auto simp add: filter_a2_map_def empty_table_def split: option.splits)
  qed
  have zip_dist: "zip (linearize tss @ [nt]) ([tp - len..<tp] @ [tp]) =
    zip (linearize tss) [tp - len..<tp] @ [(nt, tp)]"
    using valid_shift_aux(1) by auto
  have list_all2': "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map')
    (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map'))
    (drop (length done) (update_until args rel1 rel2 nt auxlist))
    (zip (linearize tss') [tp + 1 - (len + 1)..<tp + 1])"
    unfolding lin_tss' tp_upt_Suc drop_update_until zip_dist
    using filter_a1_map_rel1 filter_a1_map_rel2 list_all2_appendI[OF list_all2_old]
    by auto
  have "Mapping.keys tstp_map = (if len > 0 then {tp - len..tp - 1} else {})" using valid_shift_aux by auto
  then have tstp_map'_keys: "Mapping.keys tstp_map' = (if len + 1 > 0 then {tp + 1 - (len + 1)..tp} else {})" 
    unfolding tstp_map'_def Mapping.keys_update using atLeastAtMost_insertL by auto
  have list_all_old: "list_all (\<lambda>(ts', tp'). ivl_restr_a2_map I ts' tp' a2_map \<and> valid_tstp_map ts' tp' tstp_map) (zip (linearize tss) [tp - len..<tp])"
   using valid_shift_aux unfolding I_def by auto
  then have list_all_old': "list_all (\<lambda>(ts', tp'). ivl_restr_a2_map I ts' tp' a2_map' \<and> valid_tstp_map ts' tp' tstp_map') (zip (linearize tss) [tp - len..<tp])"
  proof (rule list.pred_mono_strong[of "\<lambda>(ts', tp'). ivl_restr_a2_map I ts' tp' a2_map \<and> valid_tstp_map ts' tp' tstp_map"])
    fix z
    assume assms: "z \<in> set (zip (linearize tss) [tp - len..<tp])" "case z of (ts', tp') \<Rightarrow> ivl_restr_a2_map I ts' tp' a2_map \<and> valid_tstp_map ts' tp' tstp_map"
    then obtain ts' tp' where defs: "z = (ts', tp')" "ts' \<in> set (linearize tss)" "tp' \<in> set [tp - len..<tp]"
      by (metis in_set_zipE prod_decode_aux.cases)
    then have restr: "ivl_restr_a2_map I ts' tp' a2_map" "valid_tstp_map ts' tp' tstp_map" using assms(2) by auto
    have "Mapping.keys tstp_map = set [tp - len..<tp]" using valid_shift_aux by(auto) (metis Suc_pred le_0_eq le_imp_less_Suc length_0_conv neq0_conv)
    then obtain ts where ts_def: "Mapping.lookup tstp_map tp' = Some ts" using defs(3) by (metis Mapping_keys_dest)
    then have ts_eq: "ts = ts'" using restr(2) unfolding valid_tstp_map_def by auto
    have neq: "(tp + 1 = tp') = False" using defs(3) by auto
    have tp'_lt_tp: "tp' < tp"
      using defs(3) by auto
    have valid_ivl_restr: "ivl_restr_a2_map I ts' tp' a2_map'"
    proof(cases "Mapping.lookup a2_map tp'")
      case None
      then show ?thesis unfolding a2_map'_def ivl_restr_a2_map_def Mapping.lookup_update' neq upd_nested_lookup tmp'_def
        using ts_def restr(1) by(auto simp: ivl_restr_a2_map_def split:option.splits) 
    next
      case (Some a)
      fix a'
      assume l: "Mapping.lookup a2_map tp' = Some a'"
      show "ivl_restr_a2_map I ts' tp' a2_map'" 
      proof(cases "tp' \<in> fst ` tmp")
        case True
        then show ?thesis 
        proof(cases "memL I (nt - ts)")
          case True
          then have "ts_tp_lt I ts' tp' new_tstp" 
            using tp'_lt_tp defs(3) ts_eq unfolding new_tstp_def
            by (auto simp add: ts_tp_lt_def elim: contrapos_np)
          then show ?thesis using l ts_def unfolding a2_map'_def ivl_restr_a2_map_def Mapping.lookup_update' neq upd_nested_lookup tmp'_def
            using restr(1) upd_set'_lookup[of a'] lookup_a2_map' max_tstp_intro' new_tstp_lt_isl(2)
            by(auto simp: ivl_restr_a2_map_def rev_image_eqI split:option.splits) 
        next
          case False
          then show ?thesis using l ts_def unfolding a2_map'_def ivl_restr_a2_map_def Mapping.lookup_update' neq upd_nested_lookup tmp'_def
          using restr(1) upd_set'_lookup[of a'] by(auto simp: ivl_restr_a2_map_def rev_image_eqI) (metis Mapping_lookup_update nat_less_le option.simps(5) tp'_lt_tp tstp_map'_def)
        qed
      next
        case False
        then show ?thesis using l unfolding a2_map'_def ivl_restr_a2_map_def Mapping.lookup_update' neq upd_nested_lookup tmp'_def
          using restr(1) upd_set'_lookup[of a'] by(auto simp: ivl_restr_a2_map_def rev_image_eqI) 
      qed 
    qed
    have valid_tstp_map: "valid_tstp_map ts' tp' tstp_map'" 
      using restr(2) neq unfolding tstp_map'_def valid_tstp_map_def Mapping.lookup_update'
      apply(auto) using tp'_lt_tp by fastforce
    show "case z of (ts', tp') \<Rightarrow> ivl_restr_a2_map I ts' tp' a2_map' \<and> valid_tstp_map ts' tp' tstp_map'"
      using valid_tstp_map valid_ivl_restr defs(1) by auto
  qed
  obtain m' where m'_def: "Mapping.lookup a2_map' tp = Some m'"
    using a2_map'_keys by (fastforce dest: Mapping_keys_dest)
  have tp_neq: "tp + 1 \<noteq> tp" by auto
  obtain m where m_def: "Mapping.lookup a2_map tp = Some m" "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp, b) \<in> tmp'}"
    using m'_def a2_map_keys unfolding a2_map'_def Mapping.lookup_update_neq[OF tp_neq] upd_nested_lookup
    by (auto dest: Mapping_keys_dest split: option.splits if_splits) (metis Mapping_keys_dest atLeastAtMost_iff diff_le_self le_eq_less_or_eq option.simps(3))
  have m_empty: "m = Mapping.empty" using m_def valid_shift_aux by auto
  have "ivl_restr_a2_map I nt tp a2_map'" 
  proof (cases "memL I 0")
    case True
    show ?thesis unfolding a2_map'_def ivl_restr_a2_map_def Mapping.lookup_update' upd_nested_lookup 
      using m_def apply(auto)
    proof -
      fix xs
      show "case Mapping.lookup (upd_set' m new_tstp (max_tstp new_tstp) {b. (tp, b) \<in> tmp'}) xs of
          None \<Rightarrow> True | Some x \<Rightarrow> ts_tp_lt I nt tp x"
        unfolding upd_set'_lookup new_tstp_def ts_tp_lt_def using True m_empty by(auto split:option.splits)
    qed
  next
    case False
     show ?thesis unfolding a2_map'_def ivl_restr_a2_map_def Mapping.lookup_update' upd_nested_lookup 
       using m_def apply(auto)
     proof -
       fix xs
       have "Mapping.lookup tstp_map' tp = Some nt" unfolding tstp_map'_def by transfer auto
       then show "case Mapping.lookup (upd_set' m new_tstp (max_tstp new_tstp) {b. (tp, b) \<in> tmp'}) xs of
          None \<Rightarrow> True | Some x \<Rightarrow> ts_tp_lt I nt tp x"
         unfolding upd_set'_lookup new_tstp_def ts_tp_lt_def tmp'_def 
         using False m_empty by auto
     qed
  qed
  moreover have "valid_tstp_map nt tp tstp_map'"
    unfolding tstp_map'_def valid_tstp_map_def Mapping.lookup_update' by auto
  ultimately have list_all': "list_all
     (\<lambda>(ts', tp').
         ivl_restr_a2_map I ts' tp' a2_map' \<and> valid_tstp_map ts' tp' tstp_map')
     (zip (linearize tss') [tp + 1 - (len + 1)..<tp + 1])" 
    unfolding lin_tss' tp_upt_Suc zip_dist using list_all_old' by auto
  have valid_table_restr: "\<forall>tp' \<in> Mapping.keys a2_map'. case Mapping.lookup a2_map' tp' of Some m \<Rightarrow> \<forall>xs\<in>Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables'). tstp = tstp' \<and> xs \<in> table"
  proof 
    fix tp'
    assume tp'_in: "tp' \<in> Mapping.keys a2_map'"
    then obtain m where m_def: "Mapping.lookup a2_map' tp' = Some m" by (meson Mapping_keys_dest)
    have "\<forall>xs\<in>Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables'). tstp = tstp' \<and> xs \<in> table"
    proof(cases "tp' = tp + 1")
      case True
      then have "m = Mapping.empty" using m_def unfolding a2_map'_def Mapping.lookup_update' by auto
      then show ?thesis by auto
    next
      case not_eq: False
      then show ?thesis 
      proof(cases "Mapping.lookup a2_map tp'")
        case None
        then show ?thesis 
        proof(cases "tp' \<in> fst ` tmp'")
          case True
          then have m_def: "m = upd_set' Mapping.empty new_tstp (max_tstp new_tstp) {b. (tp', b) \<in> tmp'}"
            using m_def not_eq None unfolding a2_map'_def Mapping.lookup_update' upd_nested_lookup by auto
          show ?thesis unfolding m_def upd_set'_lookup upd_set'_keys Mapping.lookup_empty tables'_def append_queue_rep new_tstp_def 
            by(simp) (meson image_snd)
        next
          case False
          then have "m = Mapping.empty" using m_def None not_eq unfolding a2_map'_def Mapping.lookup_update' upd_nested_lookup by auto
          then show ?thesis by auto
        qed
      next
        case (Some a)
        have "(\<forall>tp'\<in>Mapping.keys a2_map. case Mapping.lookup a2_map tp' of Some m \<Rightarrow> \<forall>xs\<in>Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables). tstp = tstp' \<and> xs \<in> table)"
          using valid_shift_aux by auto
        then have a_restr: "\<forall>xs \<in> Mapping.keys a. case Mapping.lookup a xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables). tstp = tstp' \<and> xs \<in> table"
            using Some tp'_in Mapping_keys_intro by fastforce
        have m_def: "m = upd_set' a new_tstp (max_tstp new_tstp) {b. (tp', b) \<in> tmp'}" using Some m_def not_eq unfolding a2_map'_def Mapping.lookup_update' upd_nested_lookup by auto
        show ?thesis
        proof 
          fix xs
          assume in_m: "xs \<in> Mapping.keys m"
          show "case Mapping.lookup m xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables'). tstp = tstp' \<and> xs \<in> table"
          proof (cases "xs \<in> {b. (tp', b) \<in> tmp'}")
            case True
            then show ?thesis
            proof(cases "Mapping.lookup a xs")
              case None
              then show ?thesis using True unfolding m_def upd_set'_lookup tables'_def append_queue_rep new_tstp_def by(cases "memL I 0"; simp; meson image_snd)
            next
              case (Some a')
              then have "xs \<in> Mapping.keys a" by transfer auto
              then have "\<exists>x\<in>set (linearize tables). case x of (tablea, tstp') \<Rightarrow> a' = tstp' \<and> xs \<in> tablea"
                using a_restr Some by fastforce
              then show ?thesis using Some True unfolding m_def upd_set'_lookup tables'_def append_queue_rep new_tstp_def 
                by(cases "memL I 0"; cases a'; simp; meson image_snd; linarith)
            qed
          next
            case False
            then have in_a: "xs \<in> Mapping.keys a" using in_m unfolding m_def upd_set'_keys False by auto
            then obtain tstp where tstp_def: "Mapping.lookup a xs = Some tstp" by (meson Mapping_keys_dest)
            then have "\<exists>x\<in>set (linearize tables). case x of (tablea, tstp') \<Rightarrow> tstp = tstp' \<and> xs \<in> tablea"
              using a_restr in_a by fastforce
            then show ?thesis using False tstp_def unfolding m_def upd_set'_lookup tables'_def append_queue_rep by(cases "memL I 0") simp+
          qed
        qed
      qed
    qed
    then show "case Mapping.lookup a2_map' tp' of Some m \<Rightarrow> \<forall>xs\<in>Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables'). tstp = tstp' \<and> xs \<in> table"
      using m_def by auto
  qed
  have "Mapping.lookup a2_map' (tp + 1) = Some Mapping.empty" 
    unfolding a2_map'_def using Mapping.lookup_update[of "tp + 1" Mapping.empty "upd_nested a2_map new_tstp (max_tstp new_tstp) tmp'"] by auto
  moreover have "(case Mapping.lookup a2_map' (tp - len) of None \<Rightarrow> False | Some m \<Rightarrow>
     result \<union> snd ` (Set.filter (\<lambda>(t, x). t = tp - len) tmp') = Mapping.keys m)"
  proof -
    have "(case Mapping.lookup a2_map (tp - len) of None \<Rightarrow> False | Some m \<Rightarrow> result = Mapping.keys m)"
      using valid_shift_aux
      by auto
    then show ?thesis
      by (force simp: a2_map'_def lookup_update' upd_nested_lookup upd_set'_keys split: option.splits)
  qed
  ultimately show ?thesis
    using valid_shift_aux len_lin_tss' sorted_lin_tss' set_lin_tss' tab_a1_map'_keys a2_map'_keys'
      len_upd_until sorted_upd_until lookup_a1_map_keys' rev_done' set_take_auxlist'
      lookup_a2_map'_keys list_all2' tstp_map'_keys list_all' new_table_restr1 new_table_restr2 sorted_upd_tables valid_table_restr
    unfolding valid_mmuaux_def add_new_mmuaux_eq valid_mmuaux'.simps
      I_def n_def L_def R_def pos_def by auto
qed

lemma list_all2_check_before: "list_all2 (\<lambda>x y. triple_eq_pair x y f g) xs (zip ys zs) \<Longrightarrow>
  (\<And>y. y \<in> set ys \<Longrightarrow> memR I (nt - y)) \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<not>check_before I nt x"
  by (auto simp: in_set_zip elim!: list_all2_in_setE triple_eq_pair.elims)

fun eval_mmuaux' :: "args \<Rightarrow> ts \<Rightarrow> event_data mmuaux \<Rightarrow> event_data table list \<times> event_data mmuaux" where
  "eval_mmuaux' args nt aux =
    (let (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done) =
    shift_mmuaux args nt aux in
    (rev done, (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, [])))"

lemma valid_eval_mmuaux':
  assumes "valid_mmuaux args cur aux auxlist" "nt \<ge> cur"
    "eval_mmuaux' args nt aux = (res, aux')" "eval_until (args_ivl args) nt auxlist = (res', auxlist')"
  shows "valid_mmuaux args cur aux' auxlist' \<and> res = map (eval_args_agg args) res'"
proof -
  define I where "I = args_ivl args"
  define pos where "pos = args_pos args"
  have valid_folded: "valid_mmuaux' args cur nt aux auxlist"
    using assms(1,2) valid_mmuaux'_mono unfolding valid_mmuaux_def by blast
  obtain tp len tss tables maskL maskR result a1_map a2_map tstp_map "done" where shift_aux_def:
    "shift_mmuaux args nt aux = (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done)"
    by (cases "shift_mmuaux args nt aux") auto
  have valid_shift_aux: "valid_mmuaux' args cur nt (tp, tss, tables, len, maskL, maskR,
    result, a1_map, a2_map, tstp_map, done) auxlist"
    "\<And>ts. ts \<in> set (linearize tss) \<Longrightarrow> memR (args_ivl args) (nt - ts)"
    using valid_shift_mmuaux'[OF assms(1)[unfolded valid_mmuaux_def] assms(2)]
    unfolding shift_aux_def by auto
  have len_done_auxlist: "length done \<le> length auxlist"
    using valid_shift_aux by auto
  have list_all: "\<And>x. x \<in> set (take (length done) auxlist) \<Longrightarrow> check_before I nt x"
    using valid_shift_aux unfolding I_def by auto
  have set_drop_auxlist: "\<And>x. x \<in> set (drop (length done) auxlist) \<Longrightarrow> \<not>check_before I nt x"
    using valid_shift_aux[unfolded valid_mmuaux'.simps]
      list_all2_check_before[OF _ valid_shift_aux(2)] unfolding I_def by fast
  have take_auxlist_takeWhile: "take (length done) auxlist = takeWhile (check_before I nt) auxlist"
    using len_done_auxlist list_all set_drop_auxlist
    by (rule take_takeWhile) assumption+
  have rev_done: "rev done = map (eval_args_agg args) (map proj_thd (take (length done) auxlist))"
    using valid_shift_aux by auto
  then have res'_def: "map (eval_args_agg args) res' = rev done"
    using eval_until_res[OF assms(4)] unfolding take_auxlist_takeWhile I_def by auto
  then have auxlist'_def: "auxlist' = drop (length done) auxlist"
    using eval_until_auxlist'[OF assms(4)] by (metis length_map length_rev)
  have eval_mmuaux_eq: "eval_mmuaux' args nt aux = (rev done, (tp, tss, tables, len, maskL, maskR,
    result, a1_map, a2_map, tstp_map, []))"
    using shift_aux_def by auto
  show ?thesis
    using assms(3) done_empty_valid_mmuaux'_intro[OF valid_shift_aux(1)]
    unfolding shift_aux_def eval_mmuaux_eq pos_def auxlist'_def res'_def valid_mmuaux_def by auto
qed

definition init_mmuaux :: "args \<Rightarrow> event_data mmuaux" where
  "init_mmuaux args = (0, empty_queue, empty_queue, 0,
  join_mask (args_n args) (args_L args), join_mask (args_n args) (args_R args),
  {}, Mapping.empty, Mapping.update 0 Mapping.empty Mapping.empty, Mapping.empty, [])"

lemma valid_init_mmuaux: "L \<subseteq> R \<Longrightarrow> valid_mmuaux (init_args I n L R b agg) 0
  (init_mmuaux (init_args I n L R b agg)) []"
  unfolding init_mmuaux_def valid_mmuaux_def
  by (auto simp add: init_args_def empty_queue_rep table_def)

fun length_mmuaux :: "args \<Rightarrow> event_data mmuaux \<Rightarrow> nat" where
  "length_mmuaux args (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done) =
    length done + len"

lemma valid_length_mmuaux:
  assumes "valid_mmuaux args cur aux auxlist"
  shows "length_mmuaux args aux = length auxlist"
  using assms by (cases aux) (auto simp add: valid_mmuaux_def dest: list_all2_lengthD)

interpretation default_muaux: muaux valid_mmuaux init_mmuaux add_new_mmuaux length_mmuaux eval_mmuaux'
  using valid_init_mmuaux valid_add_new_mmuaux valid_length_mmuaux valid_eval_mmuaux'
  by unfold_locales assumption+


(*<*)
end
(*>*)
