theory Optimized_Agg_Temporal
  imports Optimized_Agg
  Optimized_MTL
begin

type_synonym mmasaux = "event_data mmsaux \<times> aggaux option"

fun init_maggaux' where
  "init_maggaux' args = (let (v', aux') = init_maggaux args in
                        if v' then Some aux' else None)"

fun insert_maggaux' :: "aggargs \<Rightarrow> event_data option list set \<Rightarrow> aggaux option \<Rightarrow> aggaux option" where
  "insert_maggaux' args X None = None" |
  "insert_maggaux' args X (Some aux) = (let (v', aux') = insert_maggaux args X aux in
                                       if v' \<and> finite X then Some aux' else None)"

fun delete_maggaux' :: "aggargs \<Rightarrow> event_data option list set \<Rightarrow> aggaux option \<Rightarrow> aggaux option" where
  "delete_maggaux' args X None = None" |
  "delete_maggaux' args X (Some aux) = (let (v', aux') = delete_maggaux args X aux in
                                       if v' then Some aux' else None)"

fun valid_maggaux' :: "aggargs \<Rightarrow> aggaux option \<Rightarrow> event_data option list set \<Rightarrow> bool" where
  "valid_maggaux' args None X = True" |
  "valid_maggaux' args (Some aux) X = valid_maggaux args aux X"

fun valid_mmasaux :: "args \<Rightarrow> ts \<Rightarrow> mmasaux \<Rightarrow> event_data Monitor.msaux \<Rightarrow> bool" where
  "valid_mmasaux args cur ((nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux) ys =
    (case args_agg args of
      Some aggargs \<Rightarrow> (valid_mmsaux args cur (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) ys \<and> 
                      valid_maggaux' aggargs aggaux (Mapping.keys tuple_in)) |
      None \<Rightarrow> valid_mmsaux args cur (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) ys)"

fun init_mmasaux :: "args \<Rightarrow> mmasaux" where
  "init_mmasaux args =  (case args_agg args of
      Some aggargs \<Rightarrow> (init_mmsaux args, init_maggaux' aggargs) |
      None \<Rightarrow> (init_mmsaux args, None))"

fun add_new_table_mmasaux :: "args \<Rightarrow> event_data table \<Rightarrow> mmasaux \<Rightarrow> mmasaux" where
  "add_new_table_mmasaux args X ((nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux) = 
    (let msaux' = add_new_table_mmsaux args X (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) in
    (case args_agg args of 
      None \<Rightarrow> (msaux', aggaux) |
      Some aggargs \<Rightarrow> (msaux', if (memL (args_ivl args) 0) 
                                      then insert_maggaux' aggargs (X - Mapping.keys tuple_in) aggaux
                                      else aggaux)))" 

fun join_mmasaux :: "args \<Rightarrow> event_data table \<Rightarrow> mmasaux \<Rightarrow> mmasaux" where
  "join_mmasaux args X ((t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux) =
    (case args_agg args of 
      None \<Rightarrow> (join_mmsaux args X (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux) |
      Some aggargs \<Rightarrow>
    (let pos = args_pos args in
    (if maskL = maskR then
      (let tuple_in' = Mapping.filter (join_filter_cond pos X) tuple_in;
      tuple_since = Mapping.filter (join_filter_cond pos X) tuple_since in
      ((t, gc, maskL, maskR, data_prev, data_in, tuple_in', tuple_since), delete_maggaux' aggargs (Mapping.keys tuple_in - Mapping.keys tuple_in') aggaux))
    else if (\<forall>i \<in> set maskL. \<not>i) then
      (let nones = replicate (length maskL) None;
      take_all = (pos \<longleftrightarrow> nones \<in> X); 
      tuple_in' = (if take_all then tuple_in else Mapping.empty);
      aggaux' = (if take_all then aggaux else init_maggaux' aggargs);
      tuple_since = (if take_all then tuple_since else Mapping.empty) in
      ((t, gc, maskL, maskR, data_prev, data_in, tuple_in', tuple_since), aggaux'))
    else
      (let tuple_in' = Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_in;
      tuple_since = Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_since in
      ((t, gc, maskL, maskR, data_prev, data_in, tuple_in', tuple_since), delete_maggaux' aggargs (Mapping.keys tuple_in - Mapping.keys tuple_in') aggaux)))))"

fun gc_join_mmasaux :: "args \<Rightarrow> event_data table \<Rightarrow> mmasaux \<Rightarrow> mmasaux" where
  "gc_join_mmasaux args X ((t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aux) =
    (if \<not> memR (args_ivl args) (t - gc) then join_mmasaux args X ((gc_mmsaux (t, gc, maskL, maskR,
      data_prev, data_in, tuple_in, tuple_since), aux))
    else join_mmasaux args X ((t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aux))"

fun shift_end_mmasaux :: "args \<Rightarrow> ts \<Rightarrow> mmasaux \<Rightarrow> mmasaux" where
  "shift_end_mmasaux args nt ((t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux) =
    (case args_agg args of 
      None \<Rightarrow> (shift_end args nt (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux) |
      Some aggargs \<Rightarrow>
    (let I = args_ivl args;
    data_prev' = dropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_prev;
    (data_in, discard) = takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in;
    (tuple_in, aggaux) = fold (\<lambda>(t, X) (tuple_in, aux). let tuple_in' = Mapping.filter (filter_cond X tuple_in t) tuple_in in
    (tuple_in', delete_maggaux' aggargs (Mapping.keys tuple_in - Mapping.keys tuple_in') aux)) discard (tuple_in, aggaux) in
    ((t, gc, maskL, maskR, data_prev', data_in, tuple_in, tuple_since), aggaux)))"

fun add_new_ts_mmasaux' :: "args \<Rightarrow> ts \<Rightarrow> mmasaux \<Rightarrow> mmasaux" where
  "add_new_ts_mmasaux' args nt ((t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux) =
    (case args_agg args of 
      None \<Rightarrow> (add_new_ts_mmsaux' args nt (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux) |
      Some aggargs \<Rightarrow>
    (let I = args_ivl args; 
    (data_prev, move) = takedropWhile_queue (\<lambda>(t, X). memL I (nt - t)) data_prev;
    data_in = fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in) move data_in;
    (tuple_in, aggaux) = fold (\<lambda>(t, X) (tuple_in, aggaux). let new_set = {as \<in> X. valid_tuple tuple_since (t, as)} in 
      (upd_set tuple_in (\<lambda>_. t) new_set, insert_maggaux' aggargs (new_set - Mapping.keys tuple_in) aggaux)) move (tuple_in, aggaux) in
    ((nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux)))"

definition add_new_ts_mmasaux :: "args \<Rightarrow> ts \<Rightarrow> mmasaux \<Rightarrow> mmasaux" where
  "add_new_ts_mmasaux args nt aux = add_new_ts_mmasaux' args nt (shift_end_mmasaux args nt aux)"

fun result_mmasaux :: "args \<Rightarrow> mmasaux \<Rightarrow> event_data table" where
  "result_mmasaux args ((nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux) =
    (case (args_agg args, aggaux) of 
      (Some aggargs, Some aux) \<Rightarrow> result_maggaux aggargs aux |
      (Some aggargs, None) \<Rightarrow> eval_aggargs aggargs (Mapping.keys tuple_in) |
      (None, _) \<Rightarrow> Mapping.keys tuple_in)"

lemma valid_init_mmasaux: 
  assumes "L \<subseteq> R"
  and "valid_aggargs n R agg"
  shows "valid_mmasaux (init_args I n L R b agg) 0
  (init_mmasaux (init_args I n L R b agg)) []"
proof(cases agg)
  case None
  then show ?thesis using valid_init_mmsaux[OF assms(1), of I n b agg] by(simp only:init_args_def init_mmasaux.simps) simp
next
  case (Some aggargs)
  then have safe_aggargs: "safe_aggargs aggargs" using assms(2) by(simp add:valid_aggargs_def)
  show ?thesis using Some valid_init_mmsaux[OF assms(1), of I n b agg] 
     valid_init_maggaux[of aggargs] by(cases "type_restr aggargs {}") (auto simp: init_args_def) 
qed

lemma valid_add_new_table_mmasaux_unfolded:
  assumes "valid_mmasaux args cur ((nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux) auxlist"
  and "table (args_n args) (args_R args) rel2"
  shows "valid_mmasaux args cur (add_new_table_mmasaux args rel2 ((nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux))
    (case auxlist of [] => [(cur, rel2)] | 
    ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> rel2) # ts else (cur, rel2) # auxlist)"
proof -
  let ?msaux = "(nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)"
  let ?msaux' = "add_new_table_mmsaux args rel2 ?msaux"
  obtain nt' gc' maskL' maskR' data_prev' data_in' tuple_in' tuple_since'
    where split: "?msaux' = (nt', gc', maskL', maskR', data_prev', data_in', tuple_in', tuple_since')" by fastforce 
  have valid_msaux: "valid_mmsaux args cur ?msaux auxlist" using assms(1) by(auto split:option.splits) 
  note valid_msaux' = valid_add_new_table_mmsaux[OF valid_msaux assms(2)] 
  show ?thesis
  proof(cases "memL (args_ivl args) 0")
    case True
    then have tuple_in_eq: "Mapping.keys tuple_in' = Mapping.keys tuple_in \<union> (rel2 - Mapping.keys tuple_in)" 
      using split Mapping_upd_set_keys[of tuple_in] by auto
    then show ?thesis
    proof(cases "args_agg args")
      case None
      then show ?thesis using True valid_msaux' assms(1) by(auto simp del:valid_mmsaux.simps split:option.splits)
    next
      case (Some aggargs)
      then have some_aggargs: "args_agg args = Some aggargs" by auto
      then obtain msaux' aggaux' where new_def: "(msaux', aggaux') = add_new_table_mmasaux args rel2 (?msaux, aggaux)"
        by(auto split:prod.splits)
      show ?thesis
      proof(cases aggaux')
        case None
        then show ?thesis using Some new_def valid_msaux' by(auto simp del:valid_mmsaux.simps)
      next
        case (Some a)
        then obtain aux where [simp]: "aggaux = Some aux" using new_def some_aggargs by(cases aggaux) (auto split:if_splits) 
        then have valid_maggaux: "valid_maggaux aggargs aux (Mapping.keys tuple_in)" 
          using assms(1) some_aggargs by simp
        show ?thesis
        proof(cases "memL (args_ivl args) 0")
          case True
          then have finite: "finite (rel2 - Mapping.keys tuple_in)" 
            using new_def some_aggargs Some by(simp del:insert_maggaux.simps split:prod.splits if_splits) 
          then show ?thesis using True Some some_aggargs new_def valid_msaux' valid_insert_maggaux[OF valid_maggaux finite] split tuple_in_eq
            by(simp del:valid_mmsaux.simps split:prod.splits if_splits)
        next
          case False
          then show ?thesis using valid_maggaux some_aggargs valid_msaux' by simp
        qed
      qed
    qed
  next
    case False
    then have "Mapping.keys tuple_in' = Mapping.keys tuple_in" using split by auto
    then show ?thesis using False valid_msaux' assms(1) by(auto simp del:valid_mmsaux.simps split:option.splits)
  qed
qed

lemma valid_add_new_table_mmasaux:
  assumes valid_before: "valid_mmasaux args cur (mmsaux, aux) auxlist"
  and table_X: "table (args_n args) (args_R args) X"
  shows "valid_mmasaux args cur (add_new_table_mmasaux args X (mmsaux, aux))
    (case auxlist of
      [] => [(cur, X)]
    | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> X) # ts else (cur, X) # auxlist)"
  using valid_add_new_table_mmasaux_unfolded assms
  by (cases mmsaux) fast

lemma mapping_filter_keys_diff: "Mapping.keys (Mapping.filter p m) = Mapping.keys m - (Mapping.keys m - Mapping.keys (Mapping.filter p m))"
  by (simp add: double_diff keys_filter)

lemma valid_join_mmasaux_unfolded:
  assumes "valid_mmasaux args cur ((nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux) auxlist"
  and "table (args_n args) (args_L args) rel1"
  shows "valid_mmasaux args cur (join_mmasaux args rel1 ((nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux))
    (map (\<lambda>(t, rel). (t, join rel (args_pos args) rel1)) auxlist)"
proof -
  let ?msaux = "(nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)"
  let ?msaux' = "join_mmsaux args rel1 ?msaux"
  let ?p1 = "join_filter_cond (args_pos args) rel1"
  let ?p2 = "\<lambda>k _. proj_tuple_in_join (args_pos args) maskL k rel1"
  have valid_msaux: "valid_mmsaux args cur ?msaux auxlist" using assms(1) by(auto split:option.splits) 
  note valid_msaux' = valid_join_mmsaux[OF valid_msaux assms(2)]
  show ?thesis
  proof(cases "args_agg args")
    case None
    then show ?thesis using valid_msaux' by(auto simp del:valid_mmsaux.simps split:if_splits) 
  next
    case (Some aggargs)
    then have some_aggargs: "args_agg args = Some aggargs" by auto
    show ?thesis 
    proof(cases "maskL = maskR")
      case True
      then show ?thesis 
      proof(cases aggaux)
        case None
        then show ?thesis using Some valid_msaux' True by(simp del:valid_mmsaux.simps) 
      next
        case (Some a)
        then have valid_maggaux: "valid_maggaux aggargs a (Mapping.keys tuple_in)" using some_aggargs assms(1) by auto
        show ?thesis using True valid_msaux' some_aggargs mapping_filter_keys_diff[of _ tuple_in, symmetric] Some
          valid_delete_maggaux[OF valid_maggaux, of "Mapping.keys tuple_in - Mapping.keys (Mapping.filter ?p1 tuple_in)"]
          by(simp split:if_splits prod.splits) 
      qed
    next
      case False
      then have neq: "maskL \<noteq> maskR" by auto
      then show ?thesis 
      proof(cases "(\<forall>i \<in> set maskL. \<not>i)")
        case True
        let ?temp = "let nones = replicate (length maskL) None;
      take_all = (args_pos args \<longleftrightarrow> nones \<in> rel1); 
      tuple_in' = (if take_all then tuple_in else Mapping.empty);
      aggaux' = (if take_all then aggaux else init_maggaux' aggargs);
      tuple_since = (if take_all then tuple_since else Mapping.empty) in
      ((nt, gc, maskL, maskR, data_prev, data_in, tuple_in', tuple_since), aggaux')"
        have *: "join_mmasaux args rel1 ((nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux) = ?temp" 
          using False Some True by simp blast
        have "valid_mmasaux args cur ?temp (map (\<lambda>(t, rel). (t, join rel (args_pos args) rel1)) auxlist)"
          using valid_msaux' neq True valid_init_maggaux assms(1) some_aggargs sorry
          (*by(simp del:valid_mmsaux.simps split:if_splits option.splits) (smt (z3) case_prodD)+*)
        then show ?thesis using * by simp
      next
        case False
        let ?temp = "let tuple_in' = Mapping.filter (\<lambda>as _. proj_tuple_in_join (args_pos args) maskL as rel1) tuple_in;
      tuple_since = Mapping.filter (\<lambda>as _. proj_tuple_in_join (args_pos args) maskL as rel1) tuple_since in
      ((nt, gc, maskL, maskR, data_prev, data_in, tuple_in', tuple_since), delete_maggaux' aggargs (Mapping.keys tuple_in - Mapping.keys tuple_in') aggaux)"
        have *: "join_mmasaux args rel1 ((nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux) = ?temp" 
          using False neq some_aggargs by simp blast
        have "valid_mmasaux args cur ?temp (map (\<lambda>(t, rel). (t, join rel (args_pos args) rel1)) auxlist)" 
        proof(cases aggaux)
          case None
          then show ?thesis using some_aggargs valid_msaux' neq False by(simp del:valid_mmsaux.simps) 
        next
          case (Some a)
          then have valid_maggaux: "valid_maggaux aggargs a (Mapping.keys tuple_in)" using some_aggargs assms(1) by auto
          show ?thesis using valid_delete_maggaux[OF valid_maggaux, of "Mapping.keys tuple_in - Mapping.keys (Mapping.filter ?p2 tuple_in)"] 
            some_aggargs Some valid_msaux' neq False mapping_filter_keys_diff[of _ tuple_in, symmetric]
            by(simp del:delete_maggaux.simps valid_mmsaux.simps split:option.splits prod.splits if_splits)
        qed
        then show ?thesis using * by simp
      qed
    qed
  qed
qed

lemma valid_join_mmasaux: "valid_mmasaux args cur (mmsaux, aux) auxlist \<Longrightarrow>
  table (args_n args) (args_L args) X \<Longrightarrow> valid_mmasaux args cur
  (join_mmasaux args X (mmsaux, aux)) (map (\<lambda>(t, rel). (t, join rel (args_pos args) X)) auxlist)"
  using valid_join_mmasaux_unfolded by (cases mmsaux) fast

lemma gc_join_mmasaux_alt: "gc_join_mmasaux args rel1 (mmsaux, aux) = join_mmasaux args rel1 ((gc_mmsaux mmsaux), aux) \<or>
  gc_join_mmasaux args rel1 (mmsaux, aux) = join_mmasaux args rel1 (mmsaux, aux)"
  by(cases mmsaux) (auto simp only: gc_join_mmasaux.simps split: if_splits)

lemma valid_gc_mmasaux_unfolded:
  assumes valid_before: "valid_mmasaux args cur ((nt, gc, maskL, maskR, data_prev, data_in,
    tuple_in, tuple_since), aux) ys"
  shows "valid_mmasaux args cur (gc_mmsaux (nt, gc, maskL, maskR, data_prev, data_in,
    tuple_in, tuple_since), aux) ys"
proof -
  have valid_msaux: "valid_mmsaux args cur (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) ys" using valid_before
    by(simp del:valid_mmsaux.simps split:option.splits)
  note valid_msaux' = valid_gc_mmsaux_unfolded[OF valid_msaux]
  show ?thesis using valid_gc_mmsaux_unfolded[OF valid_msaux] valid_before
    by(simp split:option.splits prod.splits) 
qed

lemma valid_gc_mmasaux: "valid_mmasaux args cur (mmsaux, aux) ys \<Longrightarrow> valid_mmasaux args cur ((gc_mmsaux mmsaux), aux) ys"
  using valid_gc_mmasaux_unfolded by (cases mmsaux) fast

lemma valid_gc_join_mmasaux:
  assumes "valid_mmasaux args cur (mmsaux, aux) auxlist" "table (args_n args) (args_L args) rel1"
  shows "valid_mmasaux args cur (gc_join_mmasaux args rel1 (mmsaux, aux))
    (map (\<lambda>(t, rel). (t, join rel (args_pos args) rel1)) auxlist)"
  using gc_join_mmasaux_alt[of args rel1 mmsaux aux]
  valid_gc_mmasaux[OF assms(1)] valid_join_mmasaux using assms by presburger

lemma fold_pair_extract:
  assumes "(x', y') = fold (\<lambda>(t, X) (x, y). (f X x t, g X x t y)) Y (x, y)"
  shows "x' = fold (\<lambda>(t, X) x. f X x t) Y x"
  using assms by(induction Y arbitrary: x y) auto

lemma valid_shift_end_mmasaux_unfolded:
  assumes valid_before: "valid_mmasaux args cur
    ((ot, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux) auxlist"
  and nt_mono: "nt \<ge> cur"
  shows "valid_mmasaux args cur (shift_end_mmasaux args nt
    ((ot, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux))
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
proof -
  let ?msaux = "(ot, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)"
  obtain data_in' discard where takedrop_def: "(data_in', discard) = takedropWhile_queue (\<lambda>(t, X). \<not> memR (args_ivl args) (nt - t)) data_in"
    by (metis old.prod.exhaust)
  obtain msaux' aggaux' where updated_def: "shift_end_mmasaux args nt ((ot, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux) = (msaux', aggaux')"
    by fastforce
  then obtain ot' gc' maskL' maskR' data_prev' data_in' tuple_in' tuple_since' where split:
    "msaux' = (ot', gc', maskL', maskR', data_prev', data_in', tuple_in', tuple_since')" using gc_mmsaux.cases by blast
  have valid_msaux: "valid_mmsaux args cur ?msaux auxlist" using assms(1) by(auto split:option.splits) 
  show ?thesis
  proof(cases "args_agg args")
    case None
    then show ?thesis using valid_shift_end_mmsaux[OF valid_msaux assms(2)] takedrop_def
      by(auto simp del:valid_mmsaux.simps split:prod.splits) 
  next
    case (Some aggargs)
    let ?lambda = "\<lambda>(t, X) (x, y). (Mapping.filter (filter_cond X x t) x, delete_maggaux' aggargs (Mapping.keys x - Mapping.keys (Mapping.filter (filter_cond X x t) x)) y)"
    have valid_maggaux: "valid_maggaux' aggargs aggaux (Mapping.keys tuple_in)" using valid_before Some by auto
    have *: "(tuple_in', aggaux') = fold ?lambda discard (tuple_in, aggaux)"
      using split updated_def Some takedrop_def by(auto split:prod.splits) 
    then have "msaux' = shift_end args nt (ot, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)"
      using fold_pair_extract[OF *] valid_before Some split updated_def takedrop_def
      by(auto simp del: valid_mmsaux.simps dropWhile_queue.simps takedropWhile_queue.simps split:prod.splits)
    then have valid_msaux': "valid_mmsaux args cur msaux' (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
      using valid_shift_end_mmsaux[OF valid_msaux assms(2)] by simp
    have valid_maggaux': "valid_maggaux' aggargs aggaux' (Mapping.keys tuple_in')" using * valid_maggaux
    proof(induction discard arbitrary: tuple_in aggaux)
      case Nil
      then show ?case using Nil by auto
    next
      case (Cons a discard)
      then obtain X t where [simp]: "a = (t, X)" by fastforce
      have *: "(tuple_in', aggaux') = (let tuple_in'' = Mapping.filter (filter_cond X tuple_in t) tuple_in in
        fold ?lambda discard (tuple_in'', delete_maggaux' aggargs (Mapping.keys tuple_in - Mapping.keys tuple_in'') aggaux))"
        using Cons(2) by auto
      have subs: "Mapping.keys tuple_in - Mapping.keys (Mapping.filter (filter_cond X tuple_in t) tuple_in) \<subseteq> Mapping.keys tuple_in" by auto
      have valid': "valid_maggaux' aggargs (delete_maggaux' aggargs (Mapping.keys tuple_in - Mapping.keys (Mapping.filter (filter_cond X tuple_in t) tuple_in)) aggaux) (Mapping.keys (Mapping.filter (filter_cond X tuple_in t) tuple_in))" 
      proof(cases aggaux)
        case None
        then show ?thesis by auto
      next
        case (Some a)
        then have *: "valid_maggaux aggargs a (Mapping.keys tuple_in)" using Cons(3) by auto
        show ?thesis using valid_delete_maggaux[OF * subs] Some
          by(simp del:delete_maggaux.simps split:prod.splits if_splits)  (metis mapping_filter_keys_diff)
      qed
      then show ?case using Cons.IH[OF _ valid'] * by auto
    qed
    show ?thesis using valid_maggaux' valid_msaux' updated_def Some split by(auto simp del:shift_end_mmasaux.simps)
  qed
qed

lemma valid_shift_end_mmasaux: "valid_mmasaux args cur (mmsaux, aux) auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
  valid_mmasaux args cur (shift_end_mmasaux args nt (mmsaux, aux))
  (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
  using valid_shift_end_mmasaux_unfolded by (cases mmsaux) fast

lemma valid_add_new_ts_mmasaux'_unfolded:
  assumes valid_before: "valid_mmasaux args cur ((ot, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux) auxlist"
  and nt_mono: "nt \<ge> cur"
  shows "valid_mmasaux args nt (add_new_ts_mmasaux' args nt
    ((ot, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux)) auxlist"
proof -
  let ?msaux = "(ot, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)"
  obtain data_prev' move where takedrop_def: "(data_prev', move) = takedropWhile_queue (\<lambda>(t, X). memL (args_ivl args) (nt - t)) data_prev"
    by (metis old.prod.exhaust)
  obtain msaux' aggaux' where updated_def: "add_new_ts_mmasaux' args nt ((ot, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux) = (msaux', aggaux')"
    by fastforce
  then obtain ot' gc' maskL' maskR' data_prev' data_in' tuple_in' tuple_since' where split:
    "msaux' = (ot', gc', maskL', maskR', data_prev', data_in', tuple_in', tuple_since')" using gc_mmsaux.cases by blast
  have valid_msaux: "valid_mmsaux args cur ?msaux auxlist" using assms(1) by(auto split:option.splits) 
  show ?thesis
  proof(cases "args_agg args")
    case None
    show ?thesis using None valid_add_new_ts_mmsaux'[OF valid_msaux assms(2)] takedrop_def
      by(auto simp del:valid_mmsaux.simps split:prod.splits) 
  next
    case (Some aggargs)
    let ?lambda = "\<lambda>(t, X) (tuple_in, aux). (upd_set tuple_in (\<lambda>_. t) {as \<in> X. valid_tuple tuple_since (t, as)}, insert_maggaux' aggargs ({as \<in> X. valid_tuple tuple_since (t, as)} - Mapping.keys tuple_in) aux)"
    have *: "(tuple_in', aggaux') = fold ?lambda move (tuple_in, aggaux)"
      using split updated_def Some takedrop_def by(auto split:prod.splits)
    then have "msaux' = add_new_ts_mmsaux' args nt (ot, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)"
      using fold_pair_extract[OF *] valid_before Some split updated_def takedrop_def
      by(auto simp del: valid_mmsaux.simps dropWhile_queue.simps takedropWhile_queue.simps split:prod.splits)
    then have valid_msaux': "valid_mmsaux args nt msaux' auxlist"
      using valid_add_new_ts_mmsaux'[OF valid_msaux assms(2)] by simp
    have valid_maggaux: "valid_maggaux' aggargs aggaux (Mapping.keys tuple_in)" using valid_before Some by auto
    have valid_maggaux': "valid_maggaux' aggargs aggaux' (Mapping.keys tuple_in')" using * valid_maggaux
    proof(induction move arbitrary: tuple_in aggaux)
      case Nil
      then show ?case by auto
    next
      case (Cons a move)
      then obtain X t where [simp]: "a = (t, X)" by fastforce
      let ?new_set = "{as \<in> X. valid_tuple tuple_since (t, as)}"
      have *: "(tuple_in', aggaux') = fold ?lambda move (upd_set tuple_in (\<lambda>_. t) ?new_set, insert_maggaux' aggargs (?new_set - Mapping.keys tuple_in) aggaux)"
        using Cons(2) by auto
      have subs: "Mapping.keys tuple_in - Mapping.keys (Mapping.filter (filter_cond X tuple_in t) tuple_in) \<subseteq> Mapping.keys tuple_in" by auto
      have valid': "valid_maggaux' aggargs (insert_maggaux' aggargs ({as \<in> X. valid_tuple tuple_since (t, as)} - Mapping.keys tuple_in) aggaux) (Mapping.keys (upd_set tuple_in (\<lambda>_. t) ?new_set))" 
      proof(cases aggaux)
        case None
        then show ?thesis by auto
      next
        case (Some a)
        then have *: "valid_maggaux aggargs a (Mapping.keys tuple_in)" using Cons(3) by auto
        show ?thesis using valid_insert_maggaux[OF *] Some Mapping_upd_set_keys[of tuple_in]
          by(simp del:insert_maggaux.simps split:prod.splits if_splits) fastforce
      qed
      show ?case using Cons.IH[OF _ valid'] * by auto
    qed
    show ?thesis using valid_maggaux' valid_msaux' updated_def Some split by(auto simp del:shift_end_mmasaux.simps)
  qed
qed

lemma valid_add_new_ts_mmasaux': "valid_mmasaux args cur (mmsaux, aux) auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
  valid_mmasaux args nt (add_new_ts_mmasaux' args nt (mmsaux, aux)) auxlist"
  using valid_add_new_ts_mmasaux'_unfolded by (cases mmsaux) fast

lemma valid_add_new_ts_mmasaux:
  assumes "valid_mmasaux args cur (mmsaux, aux) auxlist" "nt \<ge> cur"
  shows "valid_mmasaux args nt (add_new_ts_mmasaux args nt (mmsaux, aux))
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
  using valid_add_new_ts_mmasaux' valid_shift_end_mmasaux[OF assms]
  unfolding add_new_ts_mmasaux_def by (smt (z3) assms(2) valid_mmasaux.elims(1))

lemma valid_result_mmasaux_unfolded:
  assumes "valid_mmasaux args cur ((nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux) auxlist"
  shows "result_mmasaux args ((nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux) = eval_args_agg args (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {})"
proof -
  let ?msaux = "(nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)"
  have valid_msaux: "valid_mmsaux args cur ?msaux auxlist" using assms by(auto split:option.splits) 
  have tuple_in_rel: "foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {} = Mapping.keys tuple_in"
    using valid_result_mmsaux[OF valid_msaux] by auto
  show ?thesis
  proof(cases "args_agg args")
    case None
    then show ?thesis using tuple_in_rel assms by(simp add: eval_args_agg_def split:option.splits) 
  next
    case (Some a)
    then show ?thesis using tuple_in_rel assms valid_result_maggaux 
      by(auto simp del: valid_mmsaux.simps simp add: eval_args_agg_def split:option.splits) 
  qed
qed

lemma valid_result_mmasaux: "valid_mmasaux args cur (mmsaux, aux) auxlist \<Longrightarrow>
  result_mmasaux args (mmsaux, aux) = eval_args_agg args (foldr (\<union>) (concat (map (\<lambda>(t, rel). if memL (args_ivl args) (cur - t) then [rel] else []) auxlist)) {})"
  using valid_result_mmasaux_unfolded by (cases mmsaux) fast

interpretation default_mmasaux: msaux valid_mmasaux init_mmasaux add_new_ts_mmasaux gc_join_mmasaux
  add_new_table_mmasaux result_mmasaux
  using valid_init_mmasaux valid_add_new_ts_mmasaux valid_gc_join_mmasaux valid_add_new_table_mmasaux
    valid_result_mmasaux
  by unfold_locales (auto split:prod.splits)

end