theory Optimized_Agg
  imports Monitor
begin
type_synonym 'a agg_map = "(event_data tuple, 'a) mapping"

datatype aggaux = CntAux "int agg_map" | SumAux "event_data table" | MinAux "event_data table"
                    | MaxAux "event_data table" | AvgAux "event_data table" | MedAux "event_data table"

fun valid_maggaux :: "aggargs \<Rightarrow> aggaux \<Rightarrow> event_data table \<Rightarrow> bool" where
  "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> aux data = 
  (let aggtype = fst \<omega> in case aux of 
      CntAux m \<Rightarrow>
        (aggtype = Formula.Agg_Cnt) \<and> (data = {} \<longleftrightarrow> Mapping.keys m = {}) \<and>
        (\<forall>k. k \<in> (drop b) ` data \<longleftrightarrow> k \<in> Mapping.keys m) \<and>
        (\<forall>k. k \<in> Mapping.keys m \<longrightarrow> Mapping.lookup m k = 
          (let group = Set.filter (\<lambda>x. drop b x = k) data;
           M = (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` meval_trm f ` group
          in Some (length (flatten_multiset M))))
    | SumAux t \<Rightarrow> (aggtype = Formula.Agg_Sum) \<and> t = data
    | MinAux t \<Rightarrow> (aggtype = Formula.Agg_Min) \<and> t = data
    | MaxAux t \<Rightarrow> (aggtype = Formula.Agg_Max) \<and> t = data
    | AvgAux t \<Rightarrow> (aggtype = Formula.Agg_Avg) \<and> t = data
    | MedAux t \<Rightarrow> (aggtype = Formula.Agg_Med) \<and> t = data)"

fun init_maggaux :: "aggargs \<Rightarrow> aggaux" where
  "init_maggaux args =
  (let aggtype = fst (aggargs_\<omega> args) in case aggtype of
      Formula.Agg_Cnt \<Rightarrow> CntAux Mapping.empty
    | Formula.Agg_Sum \<Rightarrow> SumAux {}
    | Formula.Agg_Min \<Rightarrow> MinAux {}
    | Formula.Agg_Max \<Rightarrow> MaxAux {}
    | Formula.Agg_Avg \<Rightarrow> AvgAux {}
    | Formula.Agg_Med \<Rightarrow> MedAux {})"

fun insert_maggaux :: "aggargs \<Rightarrow> event_data table \<Rightarrow> aggaux \<Rightarrow> aggaux" where
  "insert_maggaux  \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> data aux = (case aux of
    CntAux m \<Rightarrow> CntAux (foldl (\<lambda> m t. (let group = drop b t in case (Mapping.lookup m group) of
                                       Some i \<Rightarrow> Mapping.update group (i + 1) m
                                       | None \<Rightarrow> Mapping.update group 1 m) ) m (csorted_list_of_set data))
  | SumAux t \<Rightarrow> SumAux (t \<union> data)
  | MinAux t \<Rightarrow> MinAux (t \<union> data)
  | MaxAux t \<Rightarrow> MaxAux (t \<union> data)
  | AvgAux t \<Rightarrow> AvgAux (t \<union> data)
  | MedAux t \<Rightarrow> MedAux (t \<union> data))"

fun delete_maggaux :: "aggargs \<Rightarrow> event_data table \<Rightarrow> aggaux \<Rightarrow> aggaux" where
  "delete_maggaux  \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> data aux = (case aux of
    CntAux m \<Rightarrow> CntAux (foldl (\<lambda> m t. (let group = drop b t in case (Mapping.lookup m group) of
                                       Some i \<Rightarrow> (if i = 1 then Mapping.delete group m 
                                                  else Mapping.update group (i - 1) m)
                                       | None \<Rightarrow> m) ) m (csorted_list_of_set data))
  | SumAux t \<Rightarrow> SumAux (t - data)
  | MinAux t \<Rightarrow> MinAux (t - data)
  | MaxAux t \<Rightarrow> MaxAux (t - data)
  | AvgAux t \<Rightarrow> AvgAux (t - data)
  | MedAux t \<Rightarrow> MedAux (t - data))"

fun result_maggaux :: "aggargs \<Rightarrow> aggaux \<Rightarrow> event_data table" where
  "result_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> aux = (case aux of
    CntAux m \<Rightarrow> (if g0 \<and> Mapping.keys m = {} then singleton_table n y (eval_agg_op \<omega> {})
    else (\<lambda>k. let agg_val = (EInt (integer_of_int (Mapping.lookup_default 0 m k))) in
            k[y:=Some agg_val]) ` Mapping.keys m)
  | SumAux t \<Rightarrow> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> t
  | MinAux t \<Rightarrow> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> t
  | MaxAux t \<Rightarrow> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> t
  | AvgAux t \<Rightarrow> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> t
  | MedAux t \<Rightarrow> eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> t)"

lemma valid_init_maggaux_unfolded: "safe_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> \<Longrightarrow> valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (init_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr>) {}"
  apply(induction "fst \<omega>")
  by (auto)

lemma valid_init_maggaux: "safe_aggargs args \<Longrightarrow> valid_maggaux args (init_maggaux args) {}"
  using valid_init_maggaux_unfolded by (cases args) fast

lemma valid_result_maggaux_unfolded: "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> aux X
                                  \<Longrightarrow> result_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> aux
                                    = eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> X"
proof(induction aux)
  case(SumAux x)
  then show ?case by auto
next 
  case(MinAux x)
  then show ?case by auto
next
  case(MaxAux x)
  then show ?case by auto
next
  case(AvgAux x)
  then show ?case by auto
next  
  case(MedAux x)
  then show ?case by auto
next
  case(CntAux x)
  from this have valid_agg: "valid_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (CntAux x) X"  by auto
  then show ?case
  proof (cases "g0 \<and> X = {}")
    case(True)
    then have assm: "g0 \<and> X = {}" by auto
    have result_singleton: "result_maggaux \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> (CntAux x) = singleton_table n y (eval_agg_op \<omega> {})" 
      using assm valid_agg by auto
    have eval_singleton: "eval_aggargs \<lparr>aggargs_cols = cols, aggargs_n = n, aggargs_g0 = g0, aggargs_y = y, aggargs_\<omega> = \<omega>, aggargs_b = b, aggargs_f = f\<rparr> X = singleton_table n y (eval_agg_op \<omega> {})"
      using assm unfolding eval_aggargs_def eval_agg_def by auto
    show ?thesis using result_singleton eval_singleton by auto
    case(False)
    then have assm: "\<not>(g0 \<and> X = {})" by auto
    have eval_subs_result: "eval_aggargs args X \<subseteq> result_maggaux args (CntAux x)" 
    proof - {
      
    }

end