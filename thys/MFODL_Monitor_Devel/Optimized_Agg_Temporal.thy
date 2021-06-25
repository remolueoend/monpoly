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

fun result_maggaux' :: "aggargs \<Rightarrow> aggaux option \<Rightarrow> event_data option list set option" where
  "result_maggaux' args None = None" |
  "result_maggaux' args (Some aux) = Some (result_maggaux args aux)"

fun valid_maggaux' :: "aggargs \<Rightarrow> aggaux option \<Rightarrow> event_data option list set \<Rightarrow> bool" where
  "valid_maggaux' args None X = True" |
  "valid_maggaux' args (Some aux) X = valid_maggaux args aux X"

fun valid_mmasaux :: "args \<Rightarrow> ts \<Rightarrow> mmasaux \<Rightarrow> event_data Monitor.msaux \<Rightarrow> bool" where
  "valid_mmasaux args cur ((nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since), aggaux) ys =
   (valid_mmsaux args cur (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) ys \<and>
    (case args_agg args of
      Some aggargs \<Rightarrow> valid_maggaux' aggargs aggaux (Mapping.keys tuple_in) |
      None \<Rightarrow> True))"

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
      (let (tuple_in', to_del) = (Mapping.filter (join_filter_cond pos X) tuple_in, Mapping.keys tuple_in - Mapping.keys (Mapping.filter (join_filter_cond pos X) tuple_in));
      tuple_since = Mapping.filter (join_filter_cond pos X) tuple_since in
      ((t, gc, maskL, maskR, data_prev, data_in, tuple_in', tuple_since), delete_maggaux' aggargs to_del aggaux))
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
    (tuple_in, aggaux) = fold (\<lambda>(t, X) (tuple_in, aux). let (tuple_in', to_del) = (Mapping.filter (filter_cond X tuple_in t) tuple_in, Mapping.keys tuple_in - Mapping.keys (Mapping.filter (filter_cond X tuple_in t) tuple_in)) in
    (tuple_in', delete_maggaux' aggargs to_del aux)) discard (tuple_in, aggaux) in
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
  shows "valid_mmasaux (init_args I n L R b agg) 0
  (init_mmasaux (init_args I n L R b agg)) []"
proof(cases agg)
  case None
  then show ?thesis using valid_init_mmsaux[OF assms(1), of I n b agg] by(simp only:init_args_def init_mmasaux.simps) simp
next
  case (Some aggargs)
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
          using valid_msaux' neq True valid_init_maggaux assms(1) some_aggargs
          by(simp del:valid_mmsaux.simps split:if_splits option.splits) 
        then show ?thesis using * by presburger
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
        then show ?thesis using * by presburger
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
  by unfold_locales (auto simp del: valid_mmasaux.simps split:prod.splits)

type_synonym mmauaux = "event_data mmuaux \<times> aggaux option \<times> event_data table option list"

fun valid_aggaux_list :: "Monitor.args \<Rightarrow> event_data option list set list \<Rightarrow> event_data table option list \<Rightarrow> bool"where
  "valid_aggaux_list args [] [] = True" |
  "valid_aggaux_list args (x#xs) (y#ys) = (valid_aggaux_list args xs ys \<and>
                                          (case y of Some k \<Rightarrow> (k = eval_args_agg args x) |
                                                     None \<Rightarrow> True))" |
  "valid_aggaux_list _ _ _ = False"

fun valid_mmauaux' :: "args \<Rightarrow> ts \<Rightarrow> ts \<Rightarrow> mmauaux \<Rightarrow> event_data muaux \<Rightarrow> bool" where
  "valid_mmauaux' args cur dt ((tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length), aggaux, done_agg) auxlist 
 = (valid_mmuaux' args cur dt (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length) auxlist \<and>
  (case args_agg args of
      Some aggargs \<Rightarrow> (valid_maggaux' aggargs aggaux (Mapping.keys (the (Mapping.lookup a2_map tp))) \<and>
                      valid_aggaux_list args done done_agg) |
      None \<Rightarrow> True))"

definition valid_mmauaux :: "args \<Rightarrow> ts \<Rightarrow> mmauaux \<Rightarrow> event_data muaux \<Rightarrow> bool" where
  "valid_mmauaux args cur = valid_mmauaux' args cur cur"

fun init_mmauaux :: "args \<Rightarrow> mmauaux" where
  "init_mmauaux args = (init_mmuaux args, (case args_agg args of
    Some aggargs \<Rightarrow> init_maggaux' aggargs |
    None \<Rightarrow> None), [])"

fun lin_ts_mmauaux :: "mmauaux \<Rightarrow> ts list" where
  "lin_ts_mmauaux ((tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length), auxs, done_agg) =
    linearize tss"

fun eval_step_mmauaux :: "args \<Rightarrow> mmauaux \<Rightarrow> mmauaux" where
  "eval_step_mmauaux args ((tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length), aggaux, done_agg) = 
  (case safe_hd tss of 
  (Some ts, tss') \<Rightarrow>
    (case args_agg args of 
    None \<Rightarrow> (eval_step_mmuaux args (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length), aggaux, done_agg) |
    Some aggargs \<Rightarrow>
      (case Mapping.lookup a2_map (tp - len) of 
      Some m \<Rightarrow> 
        let T = Mapping.keys m;
        tss' = tl_queue tss';
        ts' = case safe_hd tss' of 
              (Some ts', tss'') \<Rightarrow> ts';
        m'' =  Mapping.filter (\<lambda> _ tstp. ts_tp_lt (args_ivl args) ts' (tp - len + 1) tstp) m;
        to_del = Mapping.keys m - Mapping.keys m'';
        to_ins = case Mapping.lookup a2_map (tp - len + 1) of Some m' \<Rightarrow> m';
        a2_map = Mapping.update (tp - len + 1)
          (Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') m'' to_ins) a2_map;
        a2_map = Mapping.delete (tp - len) a2_map;
        agg_result = result_maggaux' aggargs aggaux;
        aggaux = insert_maggaux' aggargs (Mapping.keys to_ins) (delete_maggaux' aggargs to_del aggaux) in
        ((tp, tss', len - 1, maskL, maskR, a1_map, a2_map,
        T # done, done_length + 1), aggaux, agg_result#done_agg))))"

fun shift_mmauaux :: "args \<Rightarrow> ts \<Rightarrow> mmauaux \<Rightarrow> mmauaux" where
  "shift_mmauaux args nt ((tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length), auxs, done_agg) =
    (let tss_list = linearize (takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss) in
    foldl (\<lambda>aux _. eval_step_mmauaux args aux) ((tp, tss, len, maskL, maskR,
      a1_map, a2_map, done, done_length), auxs, done_agg) tss_list)"

fun add_new_mmauaux :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> mmauaux \<Rightarrow> mmauaux" where
  "add_new_mmauaux args rel1 rel2 nt (mmuaux, aggaux, done_agg) =
    (case args_agg args of 
     None \<Rightarrow> (add_new_mmuaux args rel1 rel2 nt mmuaux, aggaux, done_agg) |
     Some aggargs \<Rightarrow>
    (let ((tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length), aggaux, done_agg) = shift_mmauaux args nt (mmuaux, aggaux, done_agg);
    I = args_ivl args; pos = args_pos args;
    new_tstp = (if memL I 0 then Inr tp else Inl nt);
    tmp = \<Union>((\<lambda>as. case Mapping.lookup a1_map (proj_tuple maskL as) of None \<Rightarrow>
      (if \<not>pos then {(tp - len, as)} else {})
      | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
      else {(max (tp - len) (tp' + 1), as)}) ` rel2) \<union> (if memL I 0 then {tp} \<times> rel2 else {});
    a2_map' = Mapping.update (tp + 1) Mapping.empty
      (upd_nested a2_map new_tstp (max_tstp new_tstp) tmp);
    a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
      (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
    tss = append_queue nt tss in
    ((tp + 1, tss, len + 1, maskL, maskR, a1_map, a2_map', done, done_length), aggaux, done_agg)))"

fun length_mmauaux :: "args \<Rightarrow> mmauaux \<Rightarrow> nat" where
  "length_mmauaux args ((tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length), auxs, done_agg) =
    len + done_length"

fun eval_mmauaux :: "args \<Rightarrow> ts \<Rightarrow> mmauaux \<Rightarrow> (event_data table list \<times> event_data table option list \<times> mmauaux)" where
  "eval_mmauaux args nt aux =
    (let ((tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length), auxs, done_agg) =
    shift_mmauaux args nt aux in
    (rev done, rev done_agg, ((tp, tss, len, maskL, maskR, a1_map, a2_map, [], 0), auxs, [])))"

fun combine_res where
  "combine_res args [] [] = []" |
  "combine_res args (x#xs) (y#ys) = (case y of Some k \<Rightarrow> k |
                                               None \<Rightarrow> eval_args_agg args x)#combine_res args xs ys"
          

definition "eval_mmauaux' args nt aux = (case eval_mmauaux args nt aux of (res, res_agg, aux') \<Rightarrow>
    (combine_res args res res_agg, aux'))"

lemma valid_length_mmauaux:
  assumes "valid_mmauaux args cur (mmaux, auxs, done_agg) auxlist"
  shows "length_mmauaux args (mmaux, auxs, done_agg) = length auxlist"
  using assms by (cases mmaux) (auto simp add: valid_mmauaux_def dest: list_all2_lengthD)

lemma valid_init_mmauaux:
  assumes "L \<subseteq> R" 
  shows "valid_mmauaux (init_args I n L R b agg) 0 (init_mmauaux (init_args I n L R b agg)) []"
proof -
  let ?map = "Mapping.update 0 Mapping.empty Mapping.empty"
  note valid_mmuaux = valid_init_mmuaux[OF assms, of I n b agg] 
  show ?thesis 
  proof (cases "agg")
    case None
    then show ?thesis using valid_mmuaux
      by(simp only:init_args_def init_mmauaux.simps) (simp add: init_mmuaux_def valid_mmauaux_def valid_mmuaux_def) 
  next
    case (Some a)
    then show ?thesis using valid_mmuaux Some valid_init_maggaux[of a]
      by(simp only:init_args_def init_mmauaux.simps) (auto simp add: Mapping.lookup_update[of 0 Mapping.empty Mapping.empty] simp del: valid_mmuaux'.simps simp add: init_mmuaux_def valid_mmauaux_def valid_mmuaux_def)
  qed
qed

lemma valid_eval_step_mmauaux_unfolded:
  assumes "valid_mmauaux' args cur dt ((tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length), auxs, done_agg) auxlist"
    "lin_ts_mmauaux ((tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length), auxs, done_agg) = ts # tss''" "\<not> memR (args_ivl args) (dt - ts)"
  shows "valid_mmauaux' args cur dt (eval_step_mmauaux args ((tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length), auxs, done_agg)) auxlist \<and>
    lin_ts_mmauaux (eval_step_mmauaux args ((tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length), auxs, done_agg)) = tss'' \<and>
    (case eval_step_mmauaux args ((tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length), auxs, done_agg) of
    (mmaux', auxs', done_agg') \<Rightarrow> mmaux' = eval_step_mmuaux args (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length))"
proof -
  let ?muaux = "(tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length)"
  obtain tss' where safe_hd_eq: "safe_hd tss = (Some ts, tss')" using assms(2) safe_hd_rep case_optionE by (cases "safe_hd tss") fastforce
  have a2_map_keys: "Mapping.keys a2_map = {tp - len..tp}"
    using assms(1) by auto
  have tp_minus_keys: "tp - len \<in> Mapping.keys a2_map"
    using a2_map_keys by auto
  have len_tp: "len \<le> tp"
    using assms(1) by auto
  have lin_tss_not_Nil: "linearize tss \<noteq> []"
    using safe_hd_rep[OF safe_hd_eq] by auto
  have len_pos: "len > 0"
    using lin_tss_not_Nil assms(1) by auto
  have tp_minus_keys': "tp - len + 1 \<in> Mapping.keys a2_map"
    using a2_map_keys len_pos len_tp by auto
  obtain m where m_def: "Mapping.lookup a2_map (tp - len) = Some m"
    using tp_minus_keys by (auto dest: Mapping_keys_dest)
  obtain m' where m'_def: "Mapping.lookup a2_map (tp - len + 1) = Some m'"
      using tp_minus_keys' by (auto dest: Mapping_keys_dest)
  obtain muaux' auxs' done_agg' where updated_def: "(muaux', auxs', done_agg') = eval_step_mmauaux args (?muaux, auxs, done_agg)" by (smt (z3) lin_ts_mmauaux.cases)
  then obtain tp' tss' len' maskL' maskR' a1_map' a2_map' done' done_length' where split:
    "muaux' = (tp', tss', len', maskL', maskR', a1_map', a2_map', done', done_length')" using lin_ts_mmuaux.cases by blast
  have muaux'_def: "muaux' = eval_step_mmuaux args ?muaux" using updated_def m_def safe_hd_eq m'_def by(auto split:option.splits) 
  have valid_muaux: "valid_mmuaux' args cur dt ?muaux auxlist" using assms(1) by auto
  have lin_ts_muaux: "lin_ts_mmuaux (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length) = ts # tss''" using assms(2) by(auto split:option.splits)
  have valid_old: "lin_ts_mmauaux (eval_step_mmauaux args ((tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length), auxs, done_agg)) = tss''"
                  "valid_mmuaux' args cur dt muaux' auxlist"
    using updated_def[symmetric] split valid_eval_step_mmuaux'[OF valid_muaux lin_ts_muaux assms(3)] muaux'_def[symmetric]
    by simp+
  show ?thesis
  proof(cases "args_agg args")
  case None
  then show ?thesis 
    using updated_def[symmetric] valid_old split
    using valid_old by (simp add: muaux'_def)
  next
    case aargs: (Some aggargs)
    then obtain agg_result where done_agg'_def: "done_agg' = agg_result # done_agg" using updated_def m_def safe_hd_eq m'_def by auto
    let ?m' = "Mapping.filter (\<lambda>_ tstp. ts_tp_lt (args_ivl args) ts (tp - len) tstp) m"
    have done'_def: "done' = (Mapping.keys ?m')#done" using updated_def split m_def safe_hd_eq aargs m'_def by auto
    let ?aggaux = "Mapping.lookup auxs (tp - len)"
    let ?aggaux' = "Mapping.lookup auxs (tp - len + 1)"
    have subs: "Mapping.keys m - Mapping.keys ?m' \<subseteq> Mapping.keys m" by auto
    have valid_agg: "valid_maggaux' aggargs ?aggaux (Mapping.keys m)"
      using assms(1) m_def aargs by(auto simp del: valid_mmuaux'.simps)
    then have valid_del: "valid_maggaux' aggargs (delete_maggaux' aggargs (Mapping.keys m - Mapping.keys ?m') ?aggaux) (Mapping.keys ?m')"
    proof(cases ?aggaux)
      case None
      then show ?thesis by auto
    next
      case (Some a)
      then have *: "valid_maggaux aggargs a (Mapping.keys m)" using valid_agg by auto
      then show ?thesis  
        using valid_delete_maggaux[OF * subs] Some by(auto simp del:delete_maggaux.simps split:prod.splits if_splits) (metis mapping_filter_keys_diff)
    qed
    have "agg_result = Some (eval_args_agg args (Mapping.keys ?m')) \<or> agg_result = None"
    proof(cases "delete_maggaux' aggargs (Mapping.keys m - Mapping.keys ?m') ?aggaux")
      case None
      then have "agg_result = None" using done_agg'_def updated_def safe_hd_eq m_def aargs m'_def by auto
      then show ?thesis by auto
    next
      case (Some a)
      then have *: "valid_maggaux aggargs a (Mapping.keys ?m')" using valid_del by auto
      have "agg_result = Some (eval_args_agg args (Mapping.keys ?m'))"
        unfolding eval_args_agg_def using valid_result_maggaux[OF *] aargs done_agg'_def updated_def safe_hd_eq m_def Some m'_def by auto
      then show ?thesis by auto
    qed
    then have valid1: "valid_aggaux_list args done' done_agg'" using done'_def done_agg'_def assms(1) aargs by auto
    have valid_agg': "valid_maggaux' aggargs ?aggaux' (Mapping.keys m')"
      using assms(1) m'_def aargs by(auto simp del: valid_mmuaux'.simps)
    then have *: "valid_maggaux' aggargs (insert_maggaux' aggargs (Mapping.keys ?m' - Mapping.keys m') ?aggaux') (Mapping.keys ?m' \<union> Mapping.keys m')"
    proof(cases ?aggaux')
      case None
      then show ?thesis by auto
    next
      case (Some a)
      then have *: "valid_maggaux aggargs a (Mapping.keys m')" using valid_agg' by auto
      then show ?thesis  
        using valid_insert_maggaux[OF *, of "Mapping.keys ?m' - Mapping.keys m'"] Some by(auto simp add: Un_commute simp del:insert_maggaux.simps split:prod.splits)
    qed
    then have valid_upd_lookup: "valid_maggaux' aggargs (insert_maggaux' aggargs (Mapping.keys ?m' - Mapping.keys m') (Mapping.lookup auxs (tp - len + 1))) (Mapping.keys (Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') ?m' m'))" by auto
    have "\<forall>k m. Mapping.lookup a2_map k = Some m \<longrightarrow> valid_maggaux' aggargs (Mapping.lookup auxs k) (Mapping.keys m)" using assms(1) aargs by auto
    then have "\<forall>k m. Mapping.lookup a2_map' k = Some m \<longrightarrow> valid_maggaux' aggargs (Mapping.lookup auxs' k) (Mapping.keys m)"
      using updated_def split aargs safe_hd_eq m_def m'_def assms(1) valid_upd_lookup by(auto simp add:  Mapping_lookup_delete Mapping_lookup_update simp del:valid_mmuaux'.simps insert_maggaux'.simps split:option.splits) 
    then show ?thesis using updated_def valid_old split aargs safe_hd_eq m_def m'_def valid1 by(auto simp del:valid_mmuaux'.simps)   
  qed
qed

lemma valid_eval_step_mmauaux':
  assumes "valid_mmauaux' args cur dt (mmaux, auxs, done_agg) auxlist"
    "lin_ts_mmauaux (mmaux, auxs, done_agg) = ts # tss''" "\<not> memR (args_ivl args) (dt - ts)"
  shows "valid_mmauaux' args cur dt (eval_step_mmauaux args (mmaux, auxs, done_agg)) auxlist \<and>
    lin_ts_mmauaux (eval_step_mmauaux args (mmaux, auxs, done_agg)) = tss'' \<and> 
    (case eval_step_mmauaux args (mmaux, auxs, done_agg) of (mmaux', auxs', done_agg') \<Rightarrow>
    mmaux' = eval_step_mmuaux args mmaux)"
proof -
  obtain tp tss len maskL maskR a1_map a2_map donea done_length where "mmaux = (tp, tss, len, maskL, maskR, a1_map, a2_map, donea, done_length)" 
    using lin_ts_mmuaux.cases by blast
  then show ?thesis using valid_eval_step_mmauaux_unfolded[of args cur dt tp tss len maskL maskR a1_map a2_map donea done_length auxs done_agg auxlist ts tss'']
    assms by auto
qed

lemma valid_foldl_eval_step_mmauaux':
  assumes valid_before: "valid_mmauaux' args cur dt aux auxlist"
    "lin_ts_mmauaux aux = tss @ tss'"
    "\<And>ts. ts \<in> set (take (length tss) (lin_ts_mmauaux aux)) \<Longrightarrow> \<not> memR (args_ivl args) (dt - ts)"
  shows "valid_mmauaux' args cur dt (foldl (\<lambda>aux _. eval_step_mmauaux args aux) aux tss) auxlist \<and>
    lin_ts_mmauaux (foldl (\<lambda>aux _. eval_step_mmauaux args aux) aux tss) = tss' \<and> (case (foldl (\<lambda>aux _. eval_step_mmauaux args aux) aux tss) of (mmaux', auxs', done_agg') \<Rightarrow>
     case aux of (mmaux, auxs, donw_agg) \<Rightarrow> mmaux' = foldl (\<lambda>aux _. eval_step_mmuaux args aux) mmaux tss)"
  using assms
proof (induction tss arbitrary: aux)
  case (Cons ts tss)
  have app_ass: "lin_ts_mmauaux aux = ts # (tss @ tss')"
    using Cons(3) by auto
  obtain mmaux auxs done_agg where split: "aux = (mmaux, auxs, done_agg)" using proj_thd.cases by blast
  have "\<not> memR (args_ivl args) (dt - ts)"
    using Cons by auto
  then have valid_step: "valid_mmauaux' args cur dt (eval_step_mmauaux args aux) auxlist"
    "lin_ts_mmauaux (eval_step_mmauaux args aux) = tss @ tss'" 
    "case eval_step_mmauaux args aux of (mmaux', auxs', done_agg') \<Rightarrow>
     mmaux' = eval_step_mmuaux args mmaux"
    using valid_eval_step_mmauaux' Cons(2) app_ass split by auto 
  have *: "\<And>ts. ts \<in> set (take (length tss) (lin_ts_mmauaux (eval_step_mmauaux args aux))) \<Longrightarrow>
         \<not> memR (args_ivl args) (dt - ts)" using app_ass Cons(4) apply(auto) using valid_step(2) by force
  have "(case foldl (\<lambda>aux _. eval_step_mmauaux args aux) (eval_step_mmauaux args aux) tss of (mmaux', auxs', done_agg') \<Rightarrow>
         case eval_step_mmauaux args aux of (mmaux, auxs, donw_agg) \<Rightarrow> 
         mmaux' = foldl (\<lambda>aux _. eval_step_mmuaux args aux) mmaux tss)"
    using Cons(1)[OF valid_step(1-2) *] by auto
  then have "(case foldl (\<lambda>aux _. eval_step_mmauaux args aux) aux (ts # tss) of (mmaux', auxs', done_agg') \<Rightarrow>
       case aux of (mmaux, auxs, donw_agg) \<Rightarrow> mmaux' = foldl (\<lambda>aux _. eval_step_mmuaux args aux) mmaux (ts # tss))" 
    using valid_step(3) split by(simp only:foldl.simps split:prod.splits) simp
  then show ?case
    using Cons(1)[OF valid_step(1-2)] valid_step Cons(4) app_ass by auto
qed auto

lemma valid_mmauaux'_mono:
  assumes "valid_mmauaux' args cur dt aux auxlist" "dt \<le> dt'"
  shows "valid_mmauaux' args cur dt' aux auxlist"
  using assms less_le_trans by (cases aux) (fastforce simp: memR_antimono)


lemma valid_shift_mmauaux':
  assumes "valid_mmauaux' args cur cur (mmaux, auxs, done_agg) auxlist" "nt \<ge> cur"
  shows "valid_mmauaux' args cur nt (shift_mmauaux args nt (mmaux, auxs, done_agg)) auxlist \<and>
    (\<forall>ts \<in> set (lin_ts_mmauaux (shift_mmauaux args nt (mmaux, auxs, done_agg))). memR (args_ivl args) (nt - ts)) \<and>
     (case shift_mmauaux args nt (mmaux, auxs, done_agg) of (mmaux', auxs', done_agg') \<Rightarrow> 
     mmaux' = shift_mmuaux args nt mmaux)"
proof -
  define I where "I = args_ivl args"
  define pos where "pos = args_pos args"
  let ?aux = "(mmaux, auxs, done_agg)"
  have valid_folded: "valid_mmauaux' args cur nt ?aux auxlist"
    using assms(1,2) valid_mmauaux'_mono by blast
  obtain tp len tss maskL maskR a1_map a2_map "done" done_length where aux_def:
    "mmaux = (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length)"
    by (cases mmaux) auto
  note valid_before = valid_folded[unfolded aux_def]
  define tss_list where "tss_list =
    linearize (takeWhile_queue (\<lambda>t. \<not> memR I (nt - t)) tss)"
  have tss_list_takeWhile: "tss_list = takeWhile (\<lambda>t. \<not> memR I (nt - t)) (linearize tss)"
    using tss_list_def unfolding takeWhile_queue_rep .
  then obtain tss_list' where tss_list'_def: "linearize tss = tss_list @ tss_list'"
    "tss_list' = dropWhile (\<lambda>t. \<not> memR I (nt - t)) (linearize tss)"
    by auto
  obtain tp' len' tss' maskL' maskR' a1_map' a2_map' "done'" done_length' where
    foldl_aux_def: "(tp', tss', len', maskL', maskR', a1_map', a2_map',
      done', done_length') = foldl (\<lambda>aux _. eval_step_mmuaux args aux) mmaux tss_list"
    by (cases "foldl (\<lambda>aux _. eval_step_mmuaux args aux) mmaux tss_list") auto
  have lin_tss_aux: "lin_ts_mmauaux (mmaux, auxs, done_agg) = linearize tss"
    unfolding aux_def by auto
  have "take (length tss_list) (lin_ts_mmauaux (mmaux, auxs, done_agg)) = tss_list"
    unfolding lin_tss_aux using tss_list'_def(1) by auto
  then have valid_foldl: "valid_mmauaux' args cur nt
    (foldl (\<lambda>aux _. eval_step_mmauaux args aux) (mmaux, auxs, done_agg) tss_list) auxlist"
    "lin_ts_mmauaux (foldl (\<lambda>aux _. eval_step_mmauaux args aux) (mmaux, auxs, done_agg) tss_list) = tss_list'"
    "case (foldl (\<lambda>aux _. eval_step_mmauaux args aux) (mmaux, auxs, done_agg) tss_list) of (mmaux', auxs', done_agg') \<Rightarrow>
     mmaux' = foldl (\<lambda>aux _. eval_step_mmuaux args aux) mmaux tss_list"
    using valid_foldl_eval_step_mmauaux'[OF valid_before[folded aux_def], unfolded lin_tss_aux,
      OF tss_list'_def(1)] tss_list_takeWhile set_takeWhileD
    unfolding lin_tss_aux I_def by fastforce+
  have shift_mmuaux_eq: "shift_mmauaux args nt (mmaux, auxs, done_agg) = foldl (\<lambda>aux _. eval_step_mmauaux args aux) (mmaux, auxs, done_agg) tss_list"
    using tss_list_def unfolding aux_def I_def by auto
  have aux: "(case shift_mmauaux args nt (mmaux, auxs, done_agg) of (mmaux', auxs', done_agg') \<Rightarrow> 
     mmaux' = shift_mmuaux args nt mmaux)" using valid_foldl(3) by(simp only:aux_def shift_mmauaux.simps Let_def tss_list_def shift_mmuaux.simps I_def) 
  have "\<And>ts. ts \<in> set tss_list' \<Longrightarrow> memR (args_ivl args) (nt - ts)"
    using sorted_dropWhile_filter tss_list'_def(2) valid_before unfolding I_def by auto
  then show ?thesis
    using valid_foldl(1)[unfolded shift_mmuaux_eq[symmetric]] aux
    unfolding valid_foldl(2)[unfolded shift_mmuaux_eq[symmetric]] by auto
qed

lemma upd_nested_agg_lookup: "Mapping.lookup (upd_nested_agg m args ma X) a =
  (case Mapping.lookup ma a of 
   Some m' \<Rightarrow> insert_maggaux' args ({b. (a, b) \<in> X} - Mapping.keys m') (Mapping.lookup m a) |
   None \<Rightarrow> if a \<in> fst ` X then insert_maggaux' args {b. (a, b) \<in> X} (init_maggaux' args) else None)"
  by (simp add: Mapping.lookup.abs_eq upd_nested_agg.abs_eq)

lemma valid_upd_nested_comb:
  assumes "\<forall>k m. Mapping.lookup a2_map k = Some m \<longrightarrow> valid_maggaux' aggargs (Mapping.lookup auxs k) (Mapping.keys m)"
  shows "\<forall>k m. Mapping.lookup (upd_nested a2_map d f X) k = Some m \<longrightarrow> valid_maggaux' aggargs (Mapping.lookup (upd_nested_agg auxs aggargs a2_map X) k) (Mapping.keys m)"
proof(rule allI, rule allI, rule impI)
  fix k m
  assume assm: "Mapping.lookup (upd_nested a2_map d f X) k = Some m"
  note lookup_map = upd_nested_lookup[of a2_map d f X k] 
  note lookup_agg = upd_nested_agg_lookup[of auxs aggargs a2_map X k] 
  show "valid_maggaux' aggargs (Mapping.lookup (upd_nested_agg auxs aggargs a2_map X) k) (Mapping.keys m)"
  proof(cases "Mapping.lookup a2_map k")
    case None
    then show ?thesis 
    proof(cases "k \<in> fst ` X")
      case True
      then have keys: "Mapping.keys m = {b. (k, b) \<in> X}" using assm None lookup_map upd_set'_keys[of _ d f "{b. (k, b) \<in> X}"] by auto
      have valid_init: "valid_maggaux' aggargs (init_maggaux' aggargs) {}" using valid_init_maggaux by auto
      have *: "{} \<inter> {b. (k, b) \<in> X} = {}" by simp
      have "valid_maggaux' aggargs (insert_maggaux' aggargs {b. (k, b) \<in> X} (init_maggaux' aggargs)) {b. (k, b) \<in> X}"
        using valid_insert_maggaux[OF _ _ *, of aggargs] by(auto simp del:insert_maggaux.simps init_maggaux.simps split:prod.splits) (metis Int_Un_eq(2) case_prodD inf_bot_left valid_init_maggaux)
      then show ?thesis using lookup_map lookup_agg keys None True
        by(auto simp del:insert_maggaux.simps init_maggaux'.simps split:option.splits) 
    next
      case False 
      then show ?thesis using assm None lookup_map by auto
    qed
  next
    case m_old: (Some m_old)
    then have keys: "Mapping.keys m = Mapping.keys m_old \<union> {b. (k, b) \<in> X}" using assm lookup_map upd_set'_keys[of m_old d f "{b. (k, b) \<in> X}"] by auto
    then show ?thesis 
    proof(cases "Mapping.lookup auxs k")
      case None
      then show ?thesis using lookup_agg m_old by auto
      next
        case (Some aux)
        have *: "Mapping.keys m_old \<inter> ({b. (k, b) \<in> X} - Mapping.keys m_old) = {}" by auto
        have **: "valid_maggaux aggargs aux (Mapping.keys m_old)" using assms m_old Some by force 
        have "valid_maggaux' aggargs (insert_maggaux' aggargs ({b. (k, b) \<in> X} - Mapping.keys m_old) (Some aux)) (Mapping.keys m)"
          using valid_insert_maggaux[OF ** _ *] keys[symmetric] by(auto split:prod.splits)
        then show ?thesis using m_old lookup_agg Some by auto
      qed
  qed
qed

lemma valid_add_new_mmauaux_unfolded:
  assumes valid_before: "valid_mmauaux args cur ((tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length), auxs, done_agg) auxlist"
    and tabs: "table (args_n args) (args_L args) rel1" "table (args_n args) (args_R args) rel2"
    and nt_mono: "nt \<ge> cur"
  shows "valid_mmauaux args nt (add_new_mmauaux args rel1 rel2 nt ((tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length), auxs, done_agg))
    (update_until args rel1 rel2 nt auxlist)"
proof - 
  let ?muaux = "(tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length)"
  have *: "valid_mmauaux' args cur cur (?muaux, auxs, done_agg) auxlist" using valid_before unfolding valid_mmauaux_def by auto
  obtain muaux' auxs' done_agg' where updated_def: "(muaux', auxs', done_agg') = add_new_mmauaux args rel1 rel2 nt (?muaux, auxs, done_agg)" by (smt (z3) lin_ts_mmauaux.cases)
  then obtain tp' tss' len' maskL' maskR' a1_map' a2_map' done' done_length' where split:
    "muaux' = (tp', tss', len', maskL', maskR', a1_map', a2_map', done', done_length')" using lin_ts_mmuaux.cases by blast
  obtain muaux_i auxs_i done_agg_i where inter_def: "(muaux_i, auxs_i, done_agg_i) = shift_mmauaux args nt (?muaux, auxs, done_agg)" by (smt (z3) lin_ts_mmauaux.cases)
  then obtain tp_i tss_i len_i maskL_i maskR_i a1_map_i a2_map_i done_i done_length_i where split_i:
    "muaux_i = (tp_i, tss_i, len_i, maskL_i, maskR_i, a1_map_i, a2_map_i, done_i, done_length_i)" using lin_ts_mmuaux.cases by blast
  define new_tstp where "new_tstp = (if memL (args_ivl args) 0 then Inr tp_i else Inl nt)"
  define tmp where "tmp = \<Union>((\<lambda>as. case Mapping.lookup a1_map_i (proj_tuple maskL_i as) of None \<Rightarrow>
      (if \<not>(args_pos args) then {(tp_i - len_i, as)} else {})
      | Some tp' \<Rightarrow> if (args_pos args) then {(max (tp_i - len_i) tp', as)}
      else {(max (tp_i - len_i) (tp' + 1), as)}) ` rel2) \<union> (if memL (args_ivl args) 0 then {tp_i} \<times> rel2 else {})"
  have shift_lemmas: "muaux_i = shift_mmuaux args nt ?muaux"
    "valid_mmauaux' args cur nt (muaux_i, auxs_i, done_agg_i) auxlist"
    using valid_shift_mmauaux'[OF * nt_mono] inter_def by auto
  have muaux'_def: "muaux' = add_new_mmuaux args rel1 rel2 nt ?muaux" 
    using updated_def inter_def[symmetric] split[symmetric] shift_lemmas(1) by(auto simp del:shift_mmauaux.simps shift_mmuaux.simps split:option.splits prod.splits)
  have valid_old: "valid_mmuaux args cur ?muaux auxlist" using assms(1) unfolding valid_mmauaux_def valid_mmuaux_def by auto
  have valid_muaux: "valid_mmuaux args nt muaux' (update_until args rel1 rel2 nt auxlist)" 
    using valid_add_new_mmuaux[OF valid_old tabs nt_mono] muaux'_def by simp
  show ?thesis
  proof(cases "args_agg args")
    case None
    then show ?thesis using valid_muaux unfolding updated_def[symmetric] valid_mmauaux_def split valid_mmauaux'.simps valid_mmuaux_def by auto
  next
    case (Some aggargs)
    have upd_defs: "a2_map' = Mapping.update (tp_i + 1) Mapping.empty (upd_nested a2_map_i new_tstp (max_tstp new_tstp) tmp)"
         "auxs' = (let auxs'' = upd_nested_agg auxs_i aggargs a2_map_i tmp in
          case init_maggaux' aggargs of None \<Rightarrow> auxs'' |
          Some aux \<Rightarrow> Mapping.update (tp_i + 1) aux auxs'')"
          "done' = done_i" "done_agg' = done_agg_i"
      using Some updated_def unfolding tmp_def new_tstp_def add_new_mmauaux.simps unfolding inter_def[symmetric] split_i split by(auto)
    have *: "\<forall>k m. Mapping.lookup a2_map_i k = Some m \<longrightarrow> valid_maggaux' aggargs (Mapping.lookup auxs_i k) (Mapping.keys m)"
            "valid_aggaux_list args done_i done_agg_i"
      using shift_lemmas(2) Some split_i by auto
    note inter_valid =  valid_upd_nested_comb[OF *(1), of new_tstp "max_tstp new_tstp" tmp]
    have "valid_maggaux' aggargs (init_maggaux' aggargs) {}" using valid_init_maggaux by auto
    then have "\<forall>k m. Mapping.lookup a2_map' k = Some m \<longrightarrow> valid_maggaux' aggargs (Mapping.lookup auxs' k) (Mapping.keys m)"
      using upd_defs inter_valid Mapping.lookup_update'[of "(Suc tp_i)" "Mapping.empty" "(upd_nested a2_map_i new_tstp (max_tstp new_tstp) tmp)"]
        Mapping.lookup_update'[of "(Suc tp_i)" _ "upd_nested_agg auxs_i aggargs a2_map_i tmp"]
      by(auto simp add:lookup_update  simp del:init_maggaux.simps split:prod.splits) simp
    then show ?thesis using valid_muaux *(2) unfolding updated_def[symmetric] valid_mmauaux_def split valid_mmauaux'.simps upd_defs(3-4) valid_mmuaux_def Some 
      by(simp del:valid_mmuaux'.simps) 
  qed
qed

lemma valid_add_new_mmauaux:
  assumes valid_before: "valid_mmauaux args cur (mmaux, auxs, done_agg) auxlist"
    and tabs: "table (args_n args) (args_L args) rel1" "table (args_n args) (args_R args) rel2"
    and nt_mono: "nt \<ge> cur"
  shows "valid_mmauaux args nt (add_new_mmauaux args rel1 rel2 nt (mmaux, auxs, done_agg))
    (update_until args rel1 rel2 nt auxlist)"
  using valid_add_new_mmauaux_unfolded[OF _ tabs nt_mono] valid_before by (cases mmaux) fast

lemma done_empty_valid_mmauaux'_intro:
  assumes "valid_mmauaux' args cur dt
    ((tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length), auxs, done_agg) auxlist"
  shows "valid_mmauaux' args cur dt'
    ((tp, tss, len, maskL, maskR, a1_map, a2_map, [], 0), auxs, [])
    (drop (length done) auxlist)"
  using assms sorted_drop by (auto simp add: drop_map[symmetric] split:option.splits)

lemma valid_agg_list_rev:
  assumes "valid_aggaux_list args done done_agg"
  shows "valid_aggaux_list args (rev done) (rev done_agg)"
  sorry

lemma valid_eval_mmauaux:
  assumes "valid_mmauaux args cur (mmaux, auxs, done_agg) auxlist" "nt \<ge> cur"
    "eval_mmauaux args nt (mmaux, auxs, done_agg) = (res, res_agg, aux')" "eval_until (args_ivl args) nt auxlist = (res', auxlist')"
  shows "res = res' \<and> valid_mmauaux args cur aux' auxlist' \<and> (case args_agg args of Some aggargs \<Rightarrow> valid_aggaux_list args res res_agg|
                                                                                    None \<Rightarrow> True)"
proof -
  define I where "I = args_ivl args"
  define pos where "pos = args_pos args"
  have valid_folded: "valid_mmauaux' args cur nt (mmaux, auxs, done_agg) auxlist"
    using assms(1,2) valid_mmauaux'_mono unfolding valid_mmauaux_def by blast
  obtain tp len tss maskL maskR a1_map a2_map "done" done_length auxs' done_agg' where shift_aux_def:
    "shift_mmauaux args nt (mmaux, auxs, done_agg) = ((tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length), auxs', done_agg')"
    by (cases "shift_mmauaux args nt (mmaux, auxs, done_agg)") auto
  have valid_shift_aux: "valid_mmauaux' args cur nt ((tp, tss, len, maskL, maskR,
    a1_map, a2_map, done, done_length), auxs', done_agg') auxlist"
    "\<And>ts. ts \<in> set (linearize tss) \<Longrightarrow> memR (args_ivl args) (nt - ts)"
    using valid_shift_mmauaux'[OF assms(1)[unfolded valid_mmauaux_def]  assms(2)]
    unfolding shift_aux_def by auto
  have len_done_auxlist: "length done \<le> length auxlist"
    using valid_shift_aux by auto
  have list_all: "\<And>x. x \<in> set (take (length done) auxlist) \<Longrightarrow> check_before I nt x"
    using valid_shift_aux unfolding I_def by auto
  have set_drop_auxlist: "\<And>x. x \<in> set (drop (length done) auxlist) \<Longrightarrow> \<not>check_before I nt x"
    using valid_shift_aux[unfolded valid_mmauaux'.simps valid_mmuaux'.simps]
      list_all2_check_before[OF _ valid_shift_aux(2)] unfolding I_def by fast
  have take_auxlist_takeWhile: "take (length done) auxlist = takeWhile (check_before I nt) auxlist"
    using len_done_auxlist list_all set_drop_auxlist
    by (rule take_takeWhile) assumption+
  have rev_done: "rev done = map proj_thd (take (length done) auxlist)"
    using valid_shift_aux by auto
  then have res'_def: "res' = rev done"
    using eval_until_res[OF assms(4)] unfolding take_auxlist_takeWhile I_def by auto
  then have auxlist'_def: "auxlist' = drop (length done) auxlist"
    using eval_until_auxlist'[OF assms(4)] by auto
  have eval_mmuaux_eq: "eval_mmauaux args nt (mmaux, auxs, done_agg)  = (rev done, rev done_agg', ((tp, tss, len, maskL, maskR,
    a1_map, a2_map, [], 0), auxs', []))"
    using shift_aux_def by auto
  have "case args_agg args of Some aggargs \<Rightarrow> valid_aggaux_list args done done_agg' |
                              None \<Rightarrow> True" using valid_shift_aux(1) unfolding valid_mmauaux'.simps
    by(auto split:option.splits)
  then have "case args_agg args of Some aggargs \<Rightarrow> valid_aggaux_list args (rev done) (rev done_agg') |
                              None \<Rightarrow> True"
    using valid_agg_list_rev[of args "done" done_agg'] by(auto split:option.splits)
  then show ?thesis
    using assms(3) done_empty_valid_mmauaux'_intro[OF valid_shift_aux(1)]
    unfolding shift_aux_def eval_mmuaux_eq pos_def auxlist'_def res'_def valid_mmauaux_def by (auto simp del:valid_mmuaux'.simps split:option.splits)
qed

lemma valid_eval_mmauaux':
  assumes "valid_mmauaux args cur (mmaux, auxs, done_agg) auxlist" "nt \<ge> cur"
    "eval_mmauaux' args nt (mmaux, auxs, done_agg) = (res,  aux')" "eval_until (args_ivl args) nt auxlist = (res', auxlist')"
  shows "valid_mmauaux args cur aux' auxlist' \<and> res = map (eval_args_agg args) res'"
  using assms(3) valid_eval_mmauaux[OF assms(1-2) _ assms(4)]
  sorry

interpretation default_mmauaux: muaux valid_mmauaux init_mmauaux add_new_mmauaux length_mmauaux eval_mmauaux'
  using valid_init_mmauaux valid_add_new_mmauaux valid_length_mmauaux valid_eval_mmauaux'
  by unfold_locales (auto split:prod.splits)

end