(*<*)
theory Monitor_Code
  imports Monitor
    SWA
    Event_Data
    "HOL-Library.Code_Target_Nat"
    Containers.Containers
begin
(*>*)



lemma [code_unfold del, symmetric, code_post del]: "card \<equiv> Cardinality.card'" by simp
declare [[code drop: card]] Set_Impl.card_code[code]

instantiation enat :: set_impl begin
definition set_impl_enat :: "(enat, set_impl) phantom" where
  "set_impl_enat = phantom set_RBT"

instance ..
end

derive ccompare Formula.trm
derive (eq) ceq Formula.trm
derive (rbt) set_impl Formula.trm
derive (eq) ceq Monitor.mregex
derive ccompare Monitor.mregex
derive (rbt) set_impl Monitor.mregex
derive (rbt) mapping_impl Monitor.mregex
derive (no) cenum Monitor.mregex
derive (rbt) set_impl event_data

type_synonym 'a msaux = "nat \<times> \<I> \<times> (ts \<times> 'a table) list"

type_synonym 'a queue = "'a list \<times> 'a list"

definition linearize :: "'a queue \<Rightarrow> 'a list" where
  "linearize q = (case q of (ls, fs) \<Rightarrow> ls @ rev fs)"

definition empty_queue :: "'a queue" where
  "empty_queue = ([], [])"

lemma empty_queue_rep: "linearize empty_queue = []"
  unfolding empty_queue_def by (simp add: linearize_def)

definition prepend_queue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "prepend_queue a q = (case q of (ls, fs) \<Rightarrow> (a # ls, fs))"

lemma prepend_queue_rep: "linearize (prepend_queue a q) = a # linearize q"
  by (auto simp add: linearize_def prepend_queue_def split: prod.splits)

definition append_queue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "append_queue a q = (case q of (ls, fs) \<Rightarrow> (ls, a # fs))"

lemma append_queue_rep: "linearize (append_queue a q) = linearize q @ [a]"
  by (auto simp add: linearize_def append_queue_def split: prod.splits)

fun safe_hd :: "'a queue \<Rightarrow> 'a option \<times> 'a queue" where
  "safe_hd ([], []) = (None, ([], []))"
| "safe_hd ([], fs) = (let ls = rev fs in (Some (hd ls), (ls, [])))"
| "safe_hd (a # as, fs) = (Some a, (a # as, fs))"

lemma safe_hd_rep: "safe_hd q = (\<alpha>, q') \<Longrightarrow> linearize q = linearize q' \<and>
  (case \<alpha> of None \<Rightarrow> linearize q = [] | Some a \<Rightarrow> linearize q \<noteq> [] \<and> a = hd (linearize q))"
  by (auto simp add: linearize_def Let_def split: prod.splits option.splits elim: safe_hd.elims)

lemma safe_hd_Cons: "xs \<noteq> [] \<Longrightarrow> safe_hd (xs, []) = (Some (hd xs), (xs, []))"
  by (cases xs) auto

lemma safe_hd_idem: "safe_hd q = (a, q') \<Longrightarrow> safe_hd q' = (a, q')"
  by (auto simp add: Let_def safe_hd_Cons elim: safe_hd.elims)

fun tl_queue :: "'a queue \<Rightarrow> 'a queue" where
  "tl_queue ([], fs) = (tl (rev fs), [])"
| "tl_queue (a # as, fs) = (as, fs)"

lemma tl_queue_rep: "linearize (tl_queue q) = tl (linearize q)"
  by (auto simp add: linearize_def split: prod.splits elim: tl_queue.elims)

lemma length_tl_queue_rep: "linearize q \<noteq> [] \<Longrightarrow>
  length (linearize (tl_queue q)) < length (linearize q)"
  unfolding tl_queue_rep by simp

lemma length_tl_queue_safe_hd:
  assumes "safe_hd q = (Some a, q')"
  shows "length (linearize (tl_queue q')) < length (linearize q)"
  using safe_hd_rep[OF assms] by (auto simp add: length_tl_queue_rep)

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
     (auto simp add: safe_hd_idem tl_queue_rep dropWhile_hd_tl
      split: prod.splits option.splits dest: safe_hd_rep)

function takeWhile_queue :: "('a \<Rightarrow> bool) \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "takeWhile_queue f q = (case safe_hd q of (None, q') \<Rightarrow> q'
  | (Some a, q') \<Rightarrow> if f a
    then prepend_queue a (takeWhile_queue f (tl_queue q'))
    else empty_queue)"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(f, q). length (linearize q))") (fastforce split: prod.splits)+

lemma takeWhile_hd_tl: "xs \<noteq> [] \<Longrightarrow>
  takeWhile P xs = (if P (hd xs) then hd xs # takeWhile P (tl xs) else [])"
  by (cases xs) auto

lemma takeWhile_queue_rep: "linearize (takeWhile_queue f q) = takeWhile f (linearize q)"
  by (induction f q rule: takeWhile_queue.induct)
     (auto simp add: prepend_queue_rep tl_queue_rep empty_queue_rep takeWhile_hd_tl
      split: prod.splits option.splits dest: safe_hd_rep)

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
  apply (induction f q rule: takedropWhile_queue.induct)
  by (auto split: prod.splits) (auto simp add: case_prod_unfold split: option.splits)

lemma takedropWhile_queue_snd: "snd (takedropWhile_queue f q) = takeWhile f (linearize q)"
  apply (induction f q rule: takedropWhile_queue.induct)
  by (auto split: prod.splits)
     (auto simp add: case_prod_unfold tl_queue_rep takeWhile_hd_tl
      split: option.splits dest: safe_hd_rep)

type_synonym 'a mmsaux = "ts \<times> \<I> \<times> bool list \<times> bool list \<times>
  (ts \<times> 'a table) queue \<times> (ts \<times> 'a table) queue \<times>
  (('a tuple, ts) mapping) \<times> (('a tuple, ts) mapping)"

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
    apply (rule ts_tuple_rel_intro)
    by auto
qed

lemma ts_tuple_rel_ext': "tas \<in> ts_tuple_rel (set ((nt, X) # tass)) \<Longrightarrow>
  tas \<in> ts_tuple_rel (set ((nt, X \<union> Y) # tass))"
proof -
  assume assm: "tas \<in> ts_tuple_rel (set ((nt, X) # tass))"
  then have "tas \<in> ts_tuple_rel {(nt, X)} \<union> ts_tuple_rel (set tass)"
    using ts_tuple_rel_Un by force
  then show "tas \<in> ts_tuple_rel (set ((nt, X \<union> Y) # tass))"
    apply (rule UnE)
    using ts_tuple_rel_ext Un_commute apply metis
    using ts_tuple_rel_ext_Cons' by fastforce
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

fun valid_mmsaux :: "Monitor.window \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> 'a mmsaux \<Rightarrow> 'a Monitor.msaux \<Rightarrow>
  bool" where
  "valid_mmsaux w n L R (nt, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) ys \<longleftrightarrow>
    L \<subseteq> R \<and> length maskL = n \<and> length maskR = n \<and>
    (\<forall>i < n. i \<in> L \<longleftrightarrow> maskL ! i) \<and> (\<forall>i < n. i \<in> R \<longleftrightarrow> maskR ! i) \<and>
    (\<forall>(t, X) \<in> set ys. table n R X) \<and>
    nt = current w \<and> I = ivl w \<and>
    ts_tuple_rel (set ys) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since tas} \<and>
    sorted (map fst (linearize data_prev)) \<and>
    (\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt \<and> nt - t < left I) \<and>
    sorted (map fst (linearize data_in)) \<and>
    (\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt \<and> nt - t \<ge> left I) \<and>
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

lemma valid_mmsaux_tuple_in_keys: "valid_mmsaux w n L R
  (nt, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) ys \<Longrightarrow>
  Mapping.keys tuple_in = snd ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
  valid_tuple tuple_since tas}"
  by (auto intro!: Mapping_keys_intro safe_max_Some_intro
      dest!: Mapping_keys_dest safe_max_Some_dest_in[OF finite_fst_ts_tuple_rel])+

definition init_mask :: "nat \<Rightarrow> nat set \<Rightarrow> bool list" where
  "init_mask n X = map (\<lambda>i. i \<in> X) [0..<n]"

fun init_mmsaux :: "\<I> \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> 'a mmsaux" where
  "init_mmsaux I n L R = (0, I, init_mask n L, init_mask n R,
  empty_queue, empty_queue, Mapping.empty, Mapping.empty)"

lemma valid_init_mmsaux: "L \<subseteq> R \<Longrightarrow> valid_mmsaux (init_window I) n L R (init_mmsaux I n L R) []"
  by (auto simp add: init_window_def empty_queue_rep ts_tuple_rel_def init_mask_def
      Mapping.lookup_empty safe_max_def)

abbreviation "filter_cond X' ts t' \<equiv> (\<lambda>as _. \<not> (as \<in> X' \<and> Mapping.lookup ts as = Some t'))"

lemma dropWhile_filter:
  "sorted (map fst xs) \<Longrightarrow> \<forall>t \<in> fst ` set xs. t \<le> nt \<Longrightarrow>
  dropWhile (\<lambda>(t, X). enat (nt - t) > c) xs = filter (\<lambda>(t, X). enat (nt - t) \<le> c) xs"
  apply (induction xs)
  using iffD1[OF filter_id_conv[symmetric], symmetric, of _ "\<lambda>(t, X). enat (nt - t) \<le> c"]
  dual_order.trans by auto fastforce

lemma dropWhile_filter':
  fixes nt :: nat
  shows "sorted (map fst xs) \<Longrightarrow> \<forall>t \<in> fst ` set xs. t \<le> nt \<Longrightarrow>
  dropWhile (\<lambda>(t, X). nt - t \<ge> c) xs = filter (\<lambda>(t, X). nt - t < c) xs"
  apply (induction xs)
  using iffD1[OF filter_id_conv[symmetric], symmetric, of _ "\<lambda>(t, X). nt - t < c"]
  dual_order.trans by auto fastforce

lemma takeWhile_filter:
  "sorted (map fst xs) \<Longrightarrow> \<forall>t \<in> fst ` set xs. t \<le> nt \<Longrightarrow>
  takeWhile (\<lambda>(t, X). enat (nt - t) > c) xs = filter (\<lambda>(t, X). enat (nt - t) > c) xs"
  apply (induction xs)
  using iffD1[OF filter_empty_conv[symmetric], symmetric, of _ "\<lambda>(t, X). enat (nt - t) > c"]
  less_enat_iff by auto fastforce

lemma takeWhile_filter':
  fixes nt :: nat
  shows "sorted (map fst xs) \<Longrightarrow> \<forall>t \<in> fst ` set xs. t \<le> nt \<Longrightarrow>
  takeWhile (\<lambda>(t, X). nt - t \<ge> c) xs = filter (\<lambda>(t, X). nt - t \<ge> c) xs"
  apply (induction xs)
  using iffD1[OF filter_empty_conv[symmetric], symmetric, of _ "\<lambda>(t, X). nt - t \<ge> c"]
  less_enat_iff by auto fastforce

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

fun filter_mmsaux :: "ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "filter_mmsaux nt (t, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (let data_prev' = dropWhile_queue (\<lambda>(t, X). enat (nt - t) > right I) data_prev;
    (data_in, discard) = takedropWhile_queue (\<lambda>(t, X). enat (nt - t) > right I) data_in;
    tuple_in = fold (\<lambda>(t, X) tuple_in. Mapping.filter
      (filter_cond X tuple_in t) tuple_in) discard tuple_in in
    (t, I, maskL, maskR, data_prev', data_in, tuple_in, tuple_since))"

lemma valid_filter_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux w n L R
    (ot, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and nt_mono: "nt \<ge> current w"
  and new_window: "w' = w\<lparr>earliest := if nt \<ge> right (ivl w)
    then the_enat (nt - right (ivl w)) else earliest w\<rparr>"
  shows "valid_mmsaux w' n L R (filter_mmsaux nt
    (ot, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))
    (filter (\<lambda>(t, rel). enat (nt - t) \<le> right (ivl w)) auxlist)"
proof -
  define data_in' where "data_in' \<equiv>
    fst (takedropWhile_queue (\<lambda>(t, X). enat (nt - t) > right I) data_in)"
  define data_prev' where "data_prev' \<equiv>
    dropWhile_queue (\<lambda>(t, X). enat (nt - t) > right I) data_prev"
  define discard where "discard \<equiv>
    snd (takedropWhile_queue (\<lambda>(t, X). enat (nt - t) > right I) data_in)"
  define tuple_in' where "tuple_in' \<equiv> fold (\<lambda>(t, X) tuple_in. Mapping.filter
    (\<lambda>as _. \<not>(as \<in> X \<and> Mapping.lookup tuple_in as = Some t)) tuple_in) discard tuple_in"
  have tuple_in_Some_None: "\<And>as t X. Mapping.lookup tuple_in as = Some t \<Longrightarrow>
    as \<in> X \<Longrightarrow> (t, X) \<in> set discard \<Longrightarrow> Mapping.lookup tuple_in' as = None"
    using fold_Mapping_filter_Some_None unfolding tuple_in'_def by fastforce
  have tuple_in_Some_Some: "\<And>as t. Mapping.lookup tuple_in as = Some t \<Longrightarrow>
    (\<And>X. (t, X) \<in> set discard \<Longrightarrow> as \<notin> X) \<Longrightarrow> Mapping.lookup tuple_in' as = Some t"
    using fold_Mapping_filter_Some_Some unfolding tuple_in'_def by fastforce
  have tuple_in_None_None: "\<And>as. Mapping.lookup tuple_in as = None \<Longrightarrow>
    Mapping.lookup tuple_in' as = None"
    using fold_Mapping_filter_None unfolding tuple_in'_def by fastforce
  have F1: "sorted (map fst (linearize data_in))" "\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt"
    using valid_before nt_mono by auto
  have F2: "sorted (map fst (linearize data_prev))" "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt"
    using valid_before nt_mono by auto
  have lin_data_in': "linearize data_in' =
    filter (\<lambda>(t, X). enat (nt - t) \<le> right I) (linearize data_in)"
    unfolding data_in'_def[unfolded takedropWhile_queue_fst] dropWhile_queue_rep
      dropWhile_filter[OF F1] ..
  then have set_lin_data_in': "set (linearize data_in') \<subseteq> set (linearize data_in)"
    by auto
  have "sorted (map fst (linearize data_in))"
    using valid_before by auto
  then have sorted_lin_data_in': "sorted (map fst (linearize data_in'))"
    unfolding lin_data_in' using sorted_filter by auto
  have discard_alt: "discard = filter (\<lambda>(t, X). enat (nt - t) > right I) (linearize data_in)"
    unfolding discard_def[unfolded takedropWhile_queue_snd] takeWhile_filter[OF F1] ..
  have lin_data_prev': "linearize data_prev' =
    filter (\<lambda>(t, X). enat (nt - t) \<le> right I) (linearize data_prev)"
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
        unfolding tuple_in_None_None[OF None] using iffD2[OF safe_max_empty, symmetric] by blast
    next
      case (Some t)
      show ?thesis
      proof (cases "\<exists>X. (t, X) \<in> set discard \<and> as \<in> X")
        case True
        then obtain X where X_def: "(t, X) \<in> set discard" "as \<in> X"
          by auto
        have "enat (nt - t) > right I"
          using X_def(1) unfolding discard_alt by simp
        moreover have "\<And>t'. (t', as) \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
          valid_tuple tuple_since (t', as) \<Longrightarrow> t' \<le> t"
          using valid_before Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff)
        ultimately have "{tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since tas \<and> as = snd tas} = {}"
          unfolding lin_data_in' using ts_tuple_rel_set_filter
          by (auto simp add: ts_tuple_rel_def)
             (meson diff_le_mono2 enat_ord_simps(2) leD le_less_trans)
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
  have "ts_tuple_rel (set auxlist) =
    {as \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since as}"
    using valid_before by auto
  then have "ts_tuple_rel (set (filter (\<lambda>(t, rel). enat (nt - t) \<le> right I) auxlist)) =
    {as \<in> ts_tuple_rel (set (linearize data_prev') \<union> set (linearize data_in')).
    valid_tuple tuple_since as}"
    unfolding lin_data_prev' lin_data_in' ts_tuple_rel_Un ts_tuple_rel_filter by auto
  then show ?thesis
    using data_prev'_def data_in'_def tuple_in'_def discard_def valid_before nt_mono new_window
      sorted_lin_data_prev' sorted_lin_data_in' lin_data_prev' lin_data_in' lookup_tuple_in'
    by (auto simp only: valid_mmsaux.simps filter_mmsaux.simps Let_def split: prod.splits) auto
      (* takes long *)
qed

lemma valid_filter_mmsaux: "valid_mmsaux w n L R aux auxlist \<Longrightarrow> nt \<ge> current w \<Longrightarrow>
  w' = w\<lparr>earliest := if nt \<ge> right (ivl w) then the_enat (nt - right (ivl w)) else earliest w\<rparr> \<Longrightarrow>
  valid_mmsaux w' n L R (filter_mmsaux nt aux)
  (filter (\<lambda>(t, rel). enat (nt - t) \<le> right (ivl w)) auxlist)"
  using valid_filter_mmsaux_unfolded by (cases aux) fast

fun proj_tuple :: "bool list \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple" where
  "proj_tuple [] [] = []"
| "proj_tuple (True # bs) (a # as) = a # proj_tuple bs as"
| "proj_tuple (False # bs) (a # as) = None # proj_tuple bs as"
| "proj_tuple (b # bs) [] = []"
| "proj_tuple [] (a # as) = []"

lemma proj_tuple_alt: "proj_tuple bs as = map2 (\<lambda>b a. if b then a else None) bs as"
  by (induction bs as rule: proj_tuple.induct) auto

lemma map_nth': "map f xs = map (\<lambda>i. f (xs ! i)) [0..<length xs]"
  by (subst map_nth[of "map f xs", unfolded length_map, symmetric]) simp

lemma proj_tuple_restrict:
  "(\<And>i. i < n \<Longrightarrow> i \<in> X \<longleftrightarrow> bs ! i) \<Longrightarrow> length bs = n \<Longrightarrow> length as = n \<Longrightarrow>
  proj_tuple bs as = restrict X as"
  by (auto simp add: restrict_def proj_tuple_alt map_nth'[of _ "zip bs as"])

definition proj_tuple_in_join :: "bool \<Rightarrow> bool list \<Rightarrow> 'a tuple \<Rightarrow> 'a table \<Rightarrow> bool" where
  "proj_tuple_in_join pos bs as t = (if pos then proj_tuple bs as \<in> t else proj_tuple bs as \<notin> t)"

lemma join_sub:
  assumes "L \<subseteq> R" "table n L t1" "table n R t2"
  and mask_length: "length bs = n"
  and mask_correct: "\<And>i. i < n \<Longrightarrow> i \<in> L \<longleftrightarrow> bs ! i"
  shows "join t2 pos t1 = {as \<in> t2. proj_tuple_in_join pos bs as t1}"
  using assms proj_tuple_restrict[OF mask_correct mask_length] join_restrict[of t2 n R t1 L pos]
    wf_tuple_length restrict_idle
  by (auto simp add: table_def proj_tuple_in_join_def sup.absorb1) fastforce+

fun join_mmsaux :: "bool \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "join_mmsaux pos X (t, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (let tuple_in = Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_in;
    tuple_since = Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_since in
    (t, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))"

lemma valid_join_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux w n L R
    (nt, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and table_left: "table n L X"
  shows "valid_mmsaux w n L R
    (join_mmsaux pos X (nt, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))
    (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist)"
proof -
  define tuple_in' where "tuple_in' \<equiv>
    Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_in"
  define tuple_since' where "tuple_since' \<equiv>
    Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_since"
  have tuple_in_None_None: "\<And>as. Mapping.lookup tuple_in as = None \<Longrightarrow>
    Mapping.lookup tuple_in' as = None"
    unfolding tuple_in'_def using Mapping_lookup_filter_not_None by fastforce
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
      using valid_before by auto
    have proj: "as \<in> Z" "proj_tuple_in_join pos maskL as X"
      using tas_def(2) join_sub[OF _ table_left table_Z, of maskL pos] valid_before by auto
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
      using valid_before by auto
    from tas_def(2) have "proj_tuple_in_join pos maskL as X"
      unfolding tuple_since'_def using Mapping_lookup_filter_Some_P
      by (fastforce simp add: valid_tuple_def split: option.splits)
    then have as_in_join: "as \<in> join Z pos X"
      using join_sub[OF _ table_left table_Z] Z_def(1) valid_before by auto
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
  have table_join': "\<And>t ys. (t, ys) \<in> set auxlist \<Longrightarrow> table (length maskL) R (join ys pos X)"
  proof -
    fix t ys
    assume "(t, ys) \<in> set auxlist"
    then have table_ys: "table n R ys"
      using valid_before by auto
    show "table (length maskL) R (join ys pos X)"
      using join_table[OF table_ys table_left, of pos R] valid_before by auto
  qed
  show ?thesis
    using valid_before ts_tuple_rel' lookup_tuple_in' tuple_in'_def tuple_since'_def table_join'
      Mapping_filter_keys[of tuple_since "\<lambda>as. case as of Some t \<Rightarrow> t \<le> nt"] by auto
qed

lemma valid_join_mmsaux: "valid_mmsaux w n L R aux auxlist \<Longrightarrow> table n L X \<Longrightarrow>
  valid_mmsaux w n L R (join_mmsaux pos X aux) (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist)"
  using valid_join_mmsaux_unfolded by (cases aux) fast

setup_lifting type_definition_mapping

lift_definition upd_set :: "('a, 'b) mapping \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>m f X a. if a \<in> X then Some (f a) else m a" .

lemma Mapping_lookup_upd_set: "Mapping.lookup (upd_set m f X) a =
  (if a \<in> X then Some (f a) else Mapping.lookup m a)"
  by (simp add: Mapping.lookup.rep_eq upd_set.rep_eq)

lemma Mapping_upd_set_keys: "Mapping.keys m \<subseteq> Mapping.keys (upd_set m f X)"
  by (metis (mono_tags, lifting) Mapping_lookup_upd_set domIff keys_dom_lookup
      option.simps(3) subsetI)

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
  apply (induction xs arbitrary: m)
  by auto (metis (no_types, lifting) Mapping_lookup_upd_set)

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

fun add_new_ts_mmsaux :: "ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_ts_mmsaux nt (t, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (let (data_prev, move) = takedropWhile_queue (\<lambda>(t, X). nt - t \<ge> left I) data_prev;
    data_in = fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in) move data_in;
    tuple_in = fold (\<lambda>(t, X) tuple_in. upd_set tuple_in (\<lambda>_. t)
      {as \<in> X. valid_tuple tuple_since (t, as)}) move tuple_in in
    (nt, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))"

lemma valid_add_new_ts_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux w n L R
    (ot, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and nt_mono: "nt \<ge> current w"
  and new_window: "w' = w\<lparr>latest := if nt \<ge> left (ivl w)
    then nt - left (ivl w) else latest w, current := nt\<rparr>"
  shows "valid_mmsaux w' n L R (add_new_ts_mmsaux nt
    (ot, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)) auxlist"
proof -
  define data_prev' where "data_prev' \<equiv> dropWhile_queue (\<lambda>(t, X). nt - t \<ge> left I) data_prev"
  define move where "move \<equiv> takeWhile (\<lambda>(t, X). nt - t \<ge> left I) (linearize data_prev)"
  define data_in' where "data_in' \<equiv> fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in)
    move data_in"
  define tuple_in' where "tuple_in' \<equiv> fold (\<lambda>(t, X) tuple_in. upd_set tuple_in (\<lambda>_. t)
      {as \<in> X. valid_tuple tuple_since (t, as)}) move tuple_in"
  have F1: "sorted (map fst (linearize data_in))" "\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt"
    "\<forall>t \<in> fst ` set (linearize data_in). t \<le> ot \<and> ot - t \<ge> left I"
    using valid_before nt_mono by auto
  have F2: "sorted (map fst (linearize data_prev))" "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt"
    "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> ot \<and> ot - t < left I"
    using valid_before nt_mono by auto
  have lin_data_prev': "linearize data_prev' =
    filter (\<lambda>(t, X). nt - t < left I) (linearize data_prev)"
    unfolding data_prev'_def dropWhile_queue_rep dropWhile_filter'[OF F2(1,2)] ..
  have move_filter: "move = filter (\<lambda>(t, X). nt - t \<ge> left I) (linearize data_prev)"
    unfolding move_def takeWhile_filter'[OF F2(1,2)] ..
  then have sorted_move: "sorted (map fst move)"
    using sorted_filter F2 by auto
  have "\<forall>t\<in>fst ` set move. t \<le> ot \<and> ot - t < left I"
    using move_filter F2(3) set_filter by auto
  then have fst_set_before: "\<forall>t\<in>fst ` set (linearize data_in). \<forall>t'\<in>fst ` set move. t \<le> t'"
    using F1(3) by fastforce
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
        unfolding split
        apply (rule Max_Un_absorb[OF finite_fst_ts_tuple_rel _ finite_fst_ts_tuple_rel, symmetric])
        using False fst_ts_tuple_rel_before by (fastforce simp add: ts_tuple_rel_def)+
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
  have data_prev'_move: "(data_prev', move) =
    takedropWhile_queue (\<lambda>(t, X). nt - t \<ge> left I) data_prev"
    using takedropWhile_queue_fst takedropWhile_queue_snd data_prev'_def move_def
    by (metis surjective_pairing)
  moreover have "valid_mmsaux w' n L R (nt, I, maskL, maskR, data_prev', data_in',
    tuple_in', tuple_since) auxlist"
    using lin_data_prev' sorted_lin_data_prev' lin_data_in' move_filter sorted_lin_data_in'
      nt_mono valid_before ts_tuple_rel' lookup' new_window
    by (auto simp only: valid_mmsaux.simps split: option.splits) auto
      (* takes long *)
  ultimately show ?thesis
    by (auto simp only: add_new_ts_mmsaux.simps Let_def data_in'_def tuple_in'_def
        split: prod.splits)
qed

lemma valid_add_new_ts_mmsaux: "valid_mmsaux w n L R aux auxlist \<Longrightarrow> nt \<ge> current w \<Longrightarrow>
  w' = w\<lparr>latest := if nt \<ge> left (ivl w) then nt - left (ivl w) else latest w, current := nt\<rparr> \<Longrightarrow>
  valid_mmsaux w' n L R (add_new_ts_mmsaux nt aux) auxlist"
  using valid_add_new_ts_mmsaux_unfolded by (cases aux) fast

fun add_new_table_mmsaux :: "'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_table_mmsaux X (t, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (let tuple_since = upd_set tuple_since (\<lambda>_. t) (X - Mapping.keys tuple_since) in
    (if 0 \<ge> left I then (t, I, maskL, maskR, data_prev, append_queue (t, X) data_in,
      upd_set tuple_in (\<lambda>_. t) X, tuple_since)
    else (t, I, maskL, maskR, append_queue (t, X) data_prev, data_in, tuple_in, tuple_since)))"

lemma valid_add_new_table_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux w n L R
    (nt, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and table_X: "table n R X"
  shows "valid_mmsaux w n L R (add_new_table_mmsaux X
    (nt, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))
    (case auxlist of
      [] => [(nt, X)]
    | ((t, y) # ts) \<Rightarrow> if t = nt then (t, y \<union> X) # ts else (nt, X) # auxlist)"
proof -
  define tuple_in' where "tuple_in' \<equiv> upd_set tuple_in (\<lambda>_. nt) X"
  define tuple_since' where "tuple_since' \<equiv> upd_set tuple_since (\<lambda>_. nt)
    (X - Mapping.keys tuple_since)"
  define data_prev' where "data_prev' \<equiv> append_queue (nt, X) data_prev"
  define data_in' where "data_in' \<equiv> append_queue (nt, X) data_in"
  define auxlist' where "auxlist' \<equiv> (case auxlist of
    [] => [(nt, X)]
    | ((t, y) # ts) \<Rightarrow> if t = nt then (t, y \<union> X) # ts else (nt, X) # auxlist)"
  have tuple_since'_keys: "Mapping.keys tuple_since \<subseteq> Mapping.keys tuple_since'"
    using Mapping_upd_set_keys by (fastforce simp add: tuple_since'_def)
  have lin_data_prev': "linearize data_prev' = linearize data_prev @ [(nt, X)]"
    unfolding data_prev'_def append_queue_rep ..
  have lin_data_in': "linearize data_in' = linearize data_in @ [(nt, X)]"
    unfolding data_in'_def append_queue_rep ..
  have table_auxlist': "\<forall>(t, X) \<in> set auxlist'. table n R X"
    using table_X table_Un valid_before
    by (auto simp add: auxlist'_def split: list.splits if_splits)
  have lookup_tuple_since': "\<forall>as \<in> Mapping.keys tuple_since'.
    case Mapping.lookup tuple_since' as of Some t \<Rightarrow> t \<le> nt"
    unfolding tuple_since'_def using valid_before Mapping_lookup_upd_set[of tuple_since]
    by (auto dest: Mapping_keys_dest intro!: Mapping_keys_intro split: if_splits option.splits)
  have ts_tuple_rel_auxlist': "ts_tuple_rel (set auxlist') =
    ts_tuple_rel (set auxlist) \<union> ts_tuple_rel {(nt, X)}"
    unfolding auxlist'_def
    using ts_tuple_rel_ext ts_tuple_rel_ext' ts_tuple_rel_ext_Cons ts_tuple_rel_ext_Cons'
    apply (auto simp only: split: list.splits if_splits)
         apply (auto simp add: ts_tuple_rel_def)[5]
    by fastforce
  have valid_tuple_nt_X: "\<And>tas. tas \<in> ts_tuple_rel {(nt, X)} \<Longrightarrow> valid_tuple tuple_since' tas"
    using valid_before by (auto simp add: ts_tuple_rel_def valid_tuple_def tuple_since'_def
        Mapping_lookup_upd_set dest: Mapping_keys_dest split: option.splits)
  have valid_tuple_mono: "\<And>tas. valid_tuple tuple_since tas \<Longrightarrow> valid_tuple tuple_since' tas"
    by (auto simp add: valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
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
        using assm valid_before by (auto simp add: ts_tuple_rel_Un tuple_since'_def
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
          using valid_tas tas_def by (auto simp add: valid_tuple_def tuple_since'_def
              Mapping_lookup_upd_set split: option.splits if_splits)
      next
        case False
        then have "t = nt" "as \<in> X"
          using valid_tas t_le_nt unfolding tas_def
          by (auto simp add: valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
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
  show ?thesis
  proof (cases "0 \<ge> left I")
    case True
    then have add_def: "add_new_table_mmsaux X (nt, I, maskL, maskR, data_prev, data_in,
      tuple_in, tuple_since) = (nt, I, maskL, maskR, data_prev, data_in',
      tuple_in', tuple_since')"
      using data_in'_def tuple_in'_def tuple_since'_def by auto
    have left_I: "left I = 0"
      using True by auto
    have "\<forall>t \<in> fst ` set (linearize data_in'). t \<le> nt \<and> nt - t \<ge> left I"
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
          using True valid_before by (auto simp add: valid_tuple_def tuple_since'_def
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
          using False by (fastforce simp add: lin_data_in' ts_tuple_rel_def valid_tuple_def
              tuple_since'_def Mapping_lookup_upd_set intro: Mapping_keys_intro
              split: option.splits if_splits)
        then show ?thesis
          using valid_before False by (auto simp add: tuple_in'_def Mapping_lookup_upd_set)
      qed
    qed
    ultimately show ?thesis
      using assms table_auxlist' sorted_append[of "map fst (linearize data_in)"]
        lookup_tuple_since' ts_tuple_rel_auxlist' unfolding add_def auxlist'_def[symmetric]
      by (auto simp only: valid_mmsaux.simps lin_data_in') auto
  next
    case False
    then have add_def: "add_new_table_mmsaux X (nt, I, maskL, maskR, data_prev, data_in,
      tuple_in, tuple_since) = (nt, I, maskL, maskR, data_prev', data_in,
      tuple_in, tuple_since')"
      using data_prev'_def tuple_since'_def by auto
    have left_I: "left I > 0"
      using False by auto
    have "\<forall>t \<in> fst ` set (linearize data_prev'). t \<le> nt \<and> nt - t < left I"
      using valid_before False by (auto simp add: lin_data_prev')
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
          using Z_def(3) valid_before left_I by auto
      qed (auto simp add: valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
           dest: Mapping_keys_dest split: option.splits)
    qed (auto simp add: Mapping_lookup_upd_set valid_tuple_def tuple_since'_def
         intro: Mapping_keys_intro split: option.splits)
    ultimately show ?thesis
      using assms table_auxlist' sorted_append[of "map fst (linearize data_prev)"]
        False lookup_tuple_since' ts_tuple_rel_auxlist' unfolding add_def auxlist'_def[symmetric]
      by (auto simp only: valid_mmsaux.simps lin_data_prev') auto
  qed
qed

fun add_new_mmsaux :: "nat \<times> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_mmsaux (nt, X) (t, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    add_new_table_mmsaux X (add_new_ts_mmsaux nt (t, I, maskL, maskR, data_prev, data_in,
    tuple_in, tuple_since))"

lemma valid_add_new_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux w n L R
    (t, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and nt_mono: "nt \<ge> current w"
  and new_window: "w' = w\<lparr>latest := if nt \<ge> left (ivl w) then nt - left (ivl w)
    else latest w, current := nt\<rparr>"
  and table_X: "table n R X"
  shows "valid_mmsaux w' n L R (add_new_mmsaux (nt, X)
    (t, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))
    (case auxlist of
      [] => [(nt, X)]
    | ((t, y) # ts) \<Rightarrow> if t = nt then (t, y \<union> X) # ts else (nt, X) # auxlist)"
  using valid_add_new_table_mmsaux_unfolded[OF _ table_X]
    valid_add_new_ts_mmsaux[OF valid_before nt_mono new_window]
  by (cases "add_new_ts_mmsaux nt (t, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)")
     (auto simp only: add_new_ts_mmsaux.simps add_new_table_mmsaux.simps add_new_mmsaux.simps
      Let_def split: prod.splits)

lemma valid_add_new_mmsaux: "valid_mmsaux w n L R aux auxlist \<Longrightarrow> nt \<ge> current w \<Longrightarrow>
  table n R X \<Longrightarrow> w' = w\<lparr>latest := if nt \<ge> left (ivl w) then nt - left (ivl w)
  else latest w, current := nt\<rparr> \<Longrightarrow> valid_mmsaux w' n L R (add_new_mmsaux (nt, X) aux)
  (case auxlist of
    [] => [(nt, X)]
  | ((t, y) # ts) \<Rightarrow> if t = nt then (t, y \<union> X) # ts else (nt, X) # auxlist)"
  using valid_add_new_mmsaux_unfolded by (cases aux) fast

lemma foldr_ts_tuple_rel:
  "as \<in> foldr (\<union>) (concat (map (\<lambda>(t, rel). if P t then [rel] else []) auxlist)) {} \<longleftrightarrow>
  (\<exists>t. (t, as) \<in> ts_tuple_rel (set auxlist) \<and> P t)"
proof (rule iffI)
  assume assm: "as \<in> foldr (\<union>) (concat (map (\<lambda>(t, rel). if P t then [rel] else []) auxlist)) {}"
  then obtain t X where tX_def: "P t" "as \<in> X" "(t, X) \<in> set auxlist"
    by (auto elim!: in_foldr_UnE)
  then show "\<exists>t. (t, as) \<in> ts_tuple_rel (set auxlist) \<and> P t"
    by (auto simp add: ts_tuple_rel_def)
next
  assume assm: "\<exists>t. (t, as) \<in> ts_tuple_rel (set auxlist) \<and> P t"
  then obtain t X where tX_def: "P t" "as \<in> X" "(t, X) \<in> set auxlist"
    by (auto simp add: ts_tuple_rel_def)
  show "as \<in> foldr (\<union>) (concat (map (\<lambda>(t, rel). if P t then [rel] else []) auxlist)) {}"
    using in_foldr_UnI[OF tX_def(2)] tX_def assm by (induction auxlist) force+
qed

lemma image_snd: "(a, b) \<in> X \<Longrightarrow> b \<in> snd ` X"
  by force

fun result_mmsaux :: "'a mmsaux \<Rightarrow> 'a table" where
  "result_mmsaux (nt, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
  Mapping.keys tuple_in"

lemma valid_result_mmsaux_unfolded:
  assumes "valid_mmsaux w n L R
    (t, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  shows "result_mmsaux (t, I, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
  foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, left (ivl w) \<le> current w - t] {}"
  using valid_mmsaux_tuple_in_keys[OF assms] assms
  apply (auto simp add: image_Un ts_tuple_rel_Un foldr_ts_tuple_rel image_snd)
   apply (fastforce intro!: ts_tuple_rel_intro dest!: ts_tuple_rel_dest)+
  done

lemma valid_result_mmsaux: "valid_mmsaux w n L R aux auxlist \<Longrightarrow>
  result_mmsaux aux = foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, left (ivl w) \<le> current w - t] {}"
  using valid_result_mmsaux_unfolded by (cases aux) fast

global_interpretation default: msaux valid_mmsaux init_mmsaux filter_mmsaux join_mmsaux
  add_new_mmsaux result_mmsaux
  using valid_init_mmsaux valid_filter_mmsaux valid_join_mmsaux
    valid_add_new_mmsaux valid_result_mmsaux by unfold_locales assumption+

(*
  defines minit0 = "msaux.minit0 (\<lambda>I. (0, I, [] :: (ts \<times> 'a table) list)) :: nat \<Rightarrow> 'a Formula.formula \<Rightarrow> ( 'a msaux, 'a) mformula"
  and minit = "msaux.minit (\<lambda>I. (0, I, [] :: (ts \<times> 'a table) list)):: 'a Formula.formula \<Rightarrow> ( 'a msaux, 'a) mstate"
  and minit_safe = "msaux.minit_safe (\<lambda>I. (0, I, [] :: (ts \<times> 'a table) list)) :: 'a Formula.formula \<Rightarrow> ( 'a msaux, 'a) mstate"
  and update_since = "msaux.update_since
    (\<lambda>nt (t, I, xs). (t, I, filter (\<lambda>(t, X). enat (nt - t) \<le> right I) xs))
    (\<lambda>pos rel1 (t, I, xs). (t, I, map (\<lambda>(t, X). (t, join X pos rel1)) xs))
    (\<lambda>(nt, X) (t, I, xs). (nt, I, case xs of [] \<Rightarrow> [(nt, X)]
    | (t, Y) # ts \<Rightarrow> if t = nt then (nt, Y \<union> X) # ts else (nt, X) # xs))
    (\<lambda>(nt, I, xs). foldr (\<union>) [rel. (t, rel) \<leftarrow> xs, nt - t \<ge> left I] {})"
  and meval = "msaux.meval
    (\<lambda>nt (t, I, xs). (t, I, filter (\<lambda>(t, X). enat (nt - t) \<le> right I) xs))
    (\<lambda>pos rel1 (t, I, xs). (t, I, map (\<lambda>(t, X). (t, join X pos rel1)) xs))
    (\<lambda>(nt, X) (t, I, xs). (nt, I, case xs of [] \<Rightarrow> [(nt, X)]
    | (t, Y) # ts \<Rightarrow> if t = nt then (nt, Y \<union> X) # ts else (nt, X) # xs))
    (\<lambda>(nt, I, xs). foldr (\<union>) [rel. (t, rel) \<leftarrow> xs, nt - t \<ge> left I] {})"
  and mstep = "msaux.mstep
    (\<lambda>nt (t, I, xs). (t, I, filter (\<lambda>(t, X). enat (nt - t) \<le> right I) xs))
    (\<lambda>pos rel1 (t, I, xs). (t, I, map (\<lambda>(t, X). (t, join X pos rel1)) xs))
    (\<lambda>(nt, X) (t, I, xs). (nt, I, case xs of [] \<Rightarrow> [(nt, X)]
    | (t, Y) # ts \<Rightarrow> if t = nt then (nt, Y \<union> X) # ts else (nt, X) # xs))
    (\<lambda>(nt, I, xs). foldr (\<union>) [rel. (t, rel) \<leftarrow> xs, nt - t \<ge> left I] {})"
  and msteps0_stateless = "msaux.msteps0_stateless
    (\<lambda>nt (t, I, xs). (t, I, filter (\<lambda>(t, X). enat (nt - t) \<le> right I) xs))
    (\<lambda>pos rel1 (t, I, xs). (t, I, map (\<lambda>(t, X). (t, join X pos rel1)) xs))
    (\<lambda>(nt, X) (t, I, xs). (nt, I, case xs of [] \<Rightarrow> [(nt, X)]
    | (t, Y) # ts \<Rightarrow> if t = nt then (nt, Y \<union> X) # ts else (nt, X) # xs))
    (\<lambda>(nt, I, xs). foldr (\<union>) [rel. (t, rel) \<leftarrow> xs, nt - t \<ge> left I] {})"
  and msteps_stateless = "msaux.msteps_stateless
    (\<lambda>nt (t, I, xs). (t, I, filter (\<lambda>(t, X). enat (nt - t) \<le> right I) xs))
    (\<lambda>pos rel1 (t, I, xs). (t, I, map (\<lambda>(t, X). (t, join X pos rel1)) xs))
    (\<lambda>(nt, X) (t, I, xs). (nt, I, case xs of [] \<Rightarrow> [(nt, X)]
    | (t, Y) # ts \<Rightarrow> if t = nt then (nt, Y \<union> X) # ts else (nt, X) # xs))
    (\<lambda>(nt, I, xs). foldr (\<union>) [rel. (t, rel) \<leftarrow> xs, nt - t \<ge> left I] {})"
  and monitor = "msaux.monitor (\<lambda>I. (0, I, []))
    (\<lambda>nt (t, I, xs). (t, I, filter (\<lambda>(t, X). enat (nt - t) \<le> right I) xs))
    (\<lambda>pos rel1 (t, I, xs). (t, I, map (\<lambda>(t, X). (t, join X pos rel1)) xs))
    (\<lambda>(nt, X) (t, I, xs). (nt, I, case xs of [] \<Rightarrow> [(nt, X)]
    | (t, Y) # ts \<Rightarrow> if t = nt then (nt, Y \<union> X) # ts else (nt, X) # xs))
    (\<lambda>(nt, I, xs). foldr (\<union>) [rel. (t, rel) \<leftarrow> xs, nt - t \<ge> left I] {})"
  *)

(*
definition update_since :: "\<I> \<Rightarrow> bool \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> ts \<Rightarrow>
  'a msaux \<Rightarrow> 'a table \<times> 'a msaux" where
  "update_since I pos rel1 rel2 nt aux =
    (let auxrest0 = [(t, join rel pos rel1). (t, rel) \<leftarrow> snd aux];
         auxrest0' = (case auxrest0 of
             [] \<Rightarrow> (nt, rel2) # map (\<lambda>i. (i, empty_table)) (rev [r (fst aux) ..< nt])
           | x # aux' \<Rightarrow> (if fst x = nt then (fst x, snd x \<union> rel2) # aux'
              else (nt, rel2) # map (\<lambda>i. (i, empty_table)) (rev [Suc (fst x) ..< nt]) @ (x # aux')));
         auxtree0 = map_tree (\<lambda>rel. join rel pos rel1) (fst aux);
         auxtree' =
           (if r auxtree0 = Suc nt then
              update_rightmost (\<lambda>rel. rel + rel2) auxtree0
            else if Suc nt - left I > 0 then
              (let window = (max 1 (the_enat (enat (Suc nt) - right I)), Suc nt - left I);
                   new_atoms = drop (left I) auxrest0'
               in slide' (rev (map snd new_atoms)) auxtree0 window)
            else auxtree0)
     in (if Suc nt - left I > 0 then the (val auxtree') else empty_table, (auxtree', take (left I) auxrest0')))"
*)

(*
  "wf_since_aux \<sigma> n R pos \<phi> I \<psi> aux ne \<longleftrightarrow>
    (\<exists>auxlist.
      l (fst aux) = (if ne = 0 then 0 else if Suc (\<tau> \<sigma> (ne-1)) - left I > 0 then max 1 (the_enat (enat (Suc (\<tau> \<sigma> (ne-1))) - right I)) else 0) \<and>
      r (fst aux) = (if ne = 0 then 0 else Suc (\<tau> \<sigma> (ne-1)) - left I) \<and>
      take (left I) auxlist = snd aux \<and>
      valid (replicate (l (fst aux) - 1) empty_table @ rev (map snd (drop (left I) auxlist))) (fst aux) \<and>
      sorted_wrt (\<lambda>x y. fst x > fst y) auxlist \<and>
      (\<forall>t X. (t, X) \<in> set auxlist \<longrightarrow> ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> \<tau> \<sigma> (ne-1) - t \<le> right I \<and>
        (if (\<exists>i. \<tau> \<sigma> i = t) then qtable n (MFOTL.fv \<psi>) (mem_restr R) (\<lambda>v. MFOTL.sat \<sigma> (map the v) (ne-1) (Sincep pos \<phi> (point (\<tau> \<sigma> (ne-1) - t)) \<psi>)) X else X = empty_table)) \<and>
      (\<forall>t. ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> \<tau> \<sigma> (ne-1) - t \<le> right I \<longrightarrow>
        (\<exists>X. (t, X) \<in> set auxlist)))"
*)
fun fill where
  "fill ((t, X) # (u, Y) # xs) = (t, X) # map (\<lambda>t. (t, empty_table)) [t + 1 ..< u] @ fill ((u, Y) # xs)"
| "fill xs = xs"

lemma join_empty_table[simp]: "join empty_table pos rel = empty_table"
  by (auto simp: Table.join_def empty_table_def)

lemma map_join_fill:
  "map (\<lambda>(t, X). (t, join X pos rel)) (fill xs) = fill (map (\<lambda>(t, X). (t, join X pos rel)) xs)"
  by (induct xs rule: fill.induct) (auto simp: drop_Cons' gr0_conv_Suc drop_map)

lemma map_join_take_fill:
  "map (\<lambda>(t, X). (t, join X pos rel)) (take n (fill xs)) = take n (fill (map (\<lambda>(t, X). (t, join X pos rel)) xs))"
  by (auto simp: take_map[symmetric] map_join_fill)

lemma map_join_drop_fill:
  "map (\<lambda>(t, X). (t, join X pos rel)) (drop n (fill xs)) = drop n (fill (map (\<lambda>(t, X). (t, join X pos rel)) xs))"
  by (auto simp: drop_map[symmetric] map_join_fill)

lemma join_distr: "join (A \<union> B) pos C = join A pos C \<union> join B pos C"
  by (cases pos) (auto simp: join_False_code join_True_code)

lemma map_snd_flip: "map f (map snd xs) = map snd (map (\<lambda>(a, b). (a, f b)) xs)"
  by (auto simp: list.map_comp fun_eq_iff)

global_interpretation swa: msaux
  "\<lambda>w (I, t, xs) ys.
     let auxlist = fill ys in
     ivl w = I \<and>
     current w = r t + length xs - Suc 0 \<and>
     take (left (ivl w)) auxlist = xs \<and>
     valid (replicate (l t - 1) empty_table @ rev (map snd (drop (left (ivl w)) auxlist))) t \<and>
     l t = (if t = Leaf then 0 else earliest w + Suc 0) \<and>
     r t = (if t = Leaf then 0 else latest w + Suc 0)"
  "\<lambda>I. (I, Leaf, [])"
  "undefined"
  "\<lambda>pos rel (I, t, xs). (I, map_tree (\<lambda>X. join X pos rel) t, map (\<lambda>(t, X). (t, join X pos rel)) xs)"
  "\<lambda>(nt, X) (I, t, xs).
    let xs' =
      (case xs of [] \<Rightarrow> (nt, X) # map (\<lambda>i. (i, empty_table)) (rev [r t ..< nt])
           | x # aux' \<Rightarrow> (if fst x = nt then (fst x, snd x \<union> X) # aux'
              else (nt, X) # map (\<lambda>i. (i, empty_table)) (rev [Suc (fst x) ..< nt])));
      t' = (if r t = Suc nt then
              update_rightmost (\<lambda>rel. rel + X) t
            else if Suc nt - left I > 0 then
              (let window = (max 1 (the_enat (enat (Suc nt) - right I)), Suc nt - left I);
                   new_atoms = drop (left I) xs'
               in slide' (rev (map snd new_atoms)) t window)
            else t)
    in (I, t', xs')"
  "\<lambda>(I, t, xs). case val t of None \<Rightarrow> empty_table | Some X \<Rightarrow> X"
  apply unfold_locales
  subgoal by (auto simp: valid_Leaf init_window_def)
  subgoal sorry
  subgoal for w msaux auxlist pos rel
    by (auto simp: valid_Leaf Let_def map_join_take_fill map_join_drop_fill map_join_fill[symmetric]
      join_distr plus_set_def rev_map[symmetric] map_snd_flip simp del: map_map
      dest!: valid_map_map_tree[where f="\<lambda>X. join X pos rel" and as = "replicate (earliest w) empty_table @ rev (map snd (drop (left (ivl w)) (fill auxlist)))", rotated])
  subgoal sorry
  subgoal for w msaux auxlist
    apply (auto split: option.splits if_splits simp: Let_def)
       apply (frule val_eq_Some_sum_if_valid_neq_Leaf)
        apply auto []
       apply (subst (asm) sum_alt)
         apply simp
        apply (unfold valid_def)
        apply (case_tac a)
         apply auto [2]
         apply (auto simp: rev_filter[symmetric] filter_map o_def nth_append empty_table_def plus_set_def zero_set_def split: if_split) []
       apply (simp add: foldr_conv_fold plus_set_def zero_set_def del: fold_simps)
       apply (erule arg_cong[where f="\<lambda>x. _ \<in> x", THEN iffD1, rotated])
       apply (rule arg_cong[where f="\<lambda>xs. fold (\<union>) (rev xs) {}"])
    apply (rule nth_equalityI)
        apply auto []
    find_theorems "concat (map _ _)"
    thm fold_plus_sum_list_rev
(*
    apply simp
      apply (auto dest!: val_eq_Some_sum_if_valid_neq_Leaf simp: nth_append
        rev_map[symmetric] foldr_conv_fold fold_plus_sum_list_rev split: if_splits)
*)
    find_theorems "fold (+)"
    sorry
  done

lemma image_these: "f ` Option.these X = Option.these (map_option f ` X)"
  by (force simp: in_these_eq Bex_def image_iff map_option_case split: option.splits)

lemma meval_MPred: "meval n t db (MPred e ts) = ([Option.these
  ((map_option (\<lambda>f. Table.tabulate f 0 n) o match ts) ` (\<Union>(e', x)\<in>db. if e = e' then {x} else {}))], MPred e ts)"
  unfolding default.meval.simps image_these image_image o_def ..

lemma meval_MPred': "meval n t db (MPred e ts) = ([Option.these
  (\<Union>(e', x)\<in>db. if e = e' then {map_option (\<lambda>f. Table.tabulate f 0 n) (match ts x)} else {})], MPred e ts)"
  unfolding meval_MPred image_UN split_beta if_distrib[of "image _"] image_insert image_empty o_apply
  ..

lemma these_UNION: "Option.these (\<Union>x \<in> A. B x) = (\<Union>x \<in> A. (Option.these o B) x)"
  by (auto simp: Option.these_def)

lemma meval_MPred'': "meval n t db (MPred e ts) = ([
  (\<Union>(e', x)\<in>db. if e = e' then set_option (map_option (\<lambda>f. Table.tabulate f 0 n) (match ts x)) else {})], MPred e ts)"
  unfolding meval_MPred' these_UNION o_def prod.case_distrib[of Option.these]
  by (auto simp: Option.these_def map_option_case image_iff split: if_splits option.splits)

lemmas meval_code[code] = default.meval.simps(1) meval_MPred'' default.meval.simps(3-13)

definition mk_db :: "(string \<times> event_data list) list \<Rightarrow> (string \<times> event_data list) set" where
  "mk_db = set"

definition rbt_verdict :: "_ \<Rightarrow> (nat \<times> event_data option list) list" where
  "rbt_verdict = RBT_Set2.keys"

lemma saturate_commute:
  assumes "\<And>s. r \<in> g s" "\<And>s. g (insert r s) = g s" "\<And>s. r \<in> s \<Longrightarrow> h s = g s"
  and terminates: "mono g" "\<And>X. X \<subseteq> C \<Longrightarrow> g X \<subseteq> C" "finite C"
shows "saturate g {} = saturate h {r}"
proof (cases "g {} = {r}")
  case True
  with assms have "g {r} = {r}" "h {r} = {r}" by auto
  with True show ?thesis
    by (subst (1 2) saturate_code; subst saturate_code) (simp add: Let_def)
next
  case False
  then show ?thesis
    unfolding saturate_def while_def
    using while_option_finite_subset_Some[OF terminates] assms(1-3)
    by (subst while_option_commute_invariant[of "\<lambda>S. S = {} \<or> r \<in> S" "\<lambda>S. g S \<noteq> S" g "\<lambda>S. h S \<noteq> S" "insert r" h "{}", symmetric])
      (auto 4 4 dest: while_option_stop[of "\<lambda>S. g S \<noteq> S" g "{}"])
qed

definition "RPDs_aux = saturate (\<lambda>S. S \<union> \<Union> (RPD ` S))"

lemma RPDs_aux_code[code]:
  "RPDs_aux S = (let S' = S \<union> Set.bind S RPD in if S' \<subseteq> S then S else RPDs_aux S')"
  unfolding RPDs_aux_def bind_UNION
  by (subst saturate_code) auto

declare RPDs_code[code del]
lemma RPDs_code[code]: "RPDs r = RPDs_aux {r}"
  unfolding RPDs_aux_def RPDs_code
  by (rule saturate_commute[where C="RPDs r"])
     (auto 0 3 simp: mono_def subset_singleton_iff RPDs_refl RPDs_trans finite_RPDs)

definition "LPDs_aux = saturate (\<lambda>S. S \<union> \<Union> (LPD ` S))"

lemma LPDs_aux_code[code]:
  "LPDs_aux S = (let S' = S \<union> Set.bind S LPD in if S' \<subseteq> S then S else LPDs_aux S')"
  unfolding LPDs_aux_def bind_UNION
  by (subst saturate_code) auto

declare LPDs_code[code del]
lemma LPDs_code[code]: "LPDs r = LPDs_aux {r}"
  unfolding LPDs_aux_def LPDs_code
  by (rule saturate_commute[where C="LPDs r"])
     (auto 0 3 simp: mono_def subset_singleton_iff LPDs_refl LPDs_trans finite_LPDs)

lemma is_empty_table_unfold [code_unfold]:
  "X = empty_table \<longleftrightarrow> Set.is_empty X"
  "empty_table = X \<longleftrightarrow> Set.is_empty X"
  "Cardinality.eq_set X empty_table \<longleftrightarrow> Set.is_empty X"
  "Cardinality.eq_set empty_table X \<longleftrightarrow> Set.is_empty X"
  "set_eq X empty_table \<longleftrightarrow> Set.is_empty X"
  "set_eq empty_table X \<longleftrightarrow> Set.is_empty X"
  unfolding set_eq_def empty_table_def Set.is_empty_def Cardinality.eq_set_def by auto

lemma tabulate_rbt_code[code]: "Monitor.mrtabulate (xs :: mregex list) f =
  (case ID CCOMPARE(mregex) of None \<Rightarrow> Code.abort (STR ''tabulate RBT_Mapping: ccompare = None'') (\<lambda>_. Monitor.mrtabulate (xs :: mregex list) f)
  | _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.bulkload (List.map_filter (\<lambda>k. let fk = f k in if fk = empty_table then None else Some (k, fk)) xs)))"
  unfolding mrtabulate.abs_eq RBT_Mapping_def
  by (auto split: option.splits)

lemma lexordp_eq_code[code]: "lexordp_eq xs ys \<longleftrightarrow> (case xs of [] \<Rightarrow> True
  | x # xs \<Rightarrow> (case ys of [] \<Rightarrow> False
    | y # ys \<Rightarrow> if x < y then True else if x > y then False else lexordp_eq xs ys))"
  by (subst lexordp_eq.simps) (auto split: list.split)

definition mmonitorable_exec_e :: "event_data Formula.formula \<Rightarrow> bool" where
  [code_unfold]: "mmonitorable_exec_e = mmonitorable_exec"

definition convert_multiway_e :: "event_data Formula.formula \<Rightarrow> event_data Formula.formula" where
  [code_unfold]: "convert_multiway_e = convert_multiway"

definition minit_safe_e :: "event_data Formula.formula \<Rightarrow> (event_data msaux, event_data) mstate" where
  [code_unfold]: "minit_safe_e = minit_safe"

definition mstep_e :: "event_data Formula.database \<times> ts \<Rightarrow> (event_data msaux, event_data) mstate \<Rightarrow>
  (nat \<times> event_data tuple) set \<times> (event_data msaux, event_data) mstate" where
  [code_unfold]: "mstep_e = mstep"

export_code convert_multiway_e minit_safe_e mstep_e mmonitorable_exec_e
  checking OCaml?

export_code
  (*basic types*)
  nat_of_integer integer_of_nat int_of_integer integer_of_int enat
  String.explode String.implode interval mk_db RBT_set rbt_verdict
  (*term, formula, and constructors*)
  Formula.Var Formula.Pred Regex.Skip Regex.Wild
  (*event data and aggregations*)
  EInt sum_agg count_agg average_agg min_agg max_agg median_agg
  (*main functions*)
  convert_multiway_e minit_safe_e mstep_e mmonitorable_exec_e
  in OCaml module_name Monitor file_prefix "verified"

(*<*)
end
(*>*)
