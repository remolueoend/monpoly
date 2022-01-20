(*<*)
theory Abstract_Monitor
  imports Trace Table
begin
(*>*)

section \<open>Abstract monitors and slicing\<close>

subsection \<open>First-order specifications\<close>

text \<open>
  We abstract from first-order trace specifications by referring only to their
  semantics. A first-order specification is described by a finite set of free
  variables and a satisfaction function that defines for every trace the pairs
  of valuations and time-points for which the specification is satisfied.
  The specification can be restricted to a set of traces to which it applies.
\<close>

locale fo_spec =
  fixes
    nfv :: nat and fv :: "nat set" and
    traces :: "'a trace set" and
    sat :: "'a trace \<Rightarrow> 'b list \<Rightarrow> nat \<Rightarrow> bool"
  assumes
    fv_less_nfv: "x \<in> fv \<Longrightarrow> x < nfv" and
    sat_fv_cong: "\<sigma> \<in> traces \<Longrightarrow> (\<And>x. x \<in> fv \<Longrightarrow> v!x = v'!x) \<Longrightarrow> sat \<sigma> v i = sat \<sigma> v' i"
begin

definition verdicts :: "'a trace \<Rightarrow> (nat \<times> 'b tuple) set" where
  "verdicts \<sigma> = {(i, v). wf_tuple nfv fv v \<and> sat \<sigma> (map the v) i}"

definition prefixes :: "'a prefix set" where
  "prefixes = {\<pi>. \<exists>\<sigma> \<in> traces. prefix_of \<pi> \<sigma>}"

lemma prefix_of_trace[simp, intro]: "\<sigma> \<in> traces \<Longrightarrow> prefix_of \<pi> \<sigma> \<Longrightarrow> \<pi> \<in> prefixes"
  by (auto simp: prefixes_def)

lemma prefixes_closed[simp, intro]: "\<pi>' \<in> prefixes \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow> \<pi> \<in> prefixes"
  using prefix_of_antimono by (auto simp: prefixes_def)

end

text \<open>
  We usually employ a monitor to find the \<^emph>\<open>violations\<close> of a specification.
  That is, the monitor should output the satisfactions of its negation.
  Moreover, all monitor implementations must work with finite prefixes.
  We are therefore interested in co-safety properties, which allow us to
  identify all satisfactions on finite prefixes.
\<close>

locale cosafety_fo_spec = fo_spec +
  assumes cosafety_lr: "\<sigma> \<in> traces \<Longrightarrow> sat \<sigma> v i \<Longrightarrow>
    \<exists>\<pi>. prefix_of \<pi> \<sigma> \<and> (\<forall>\<sigma>' \<in> traces. prefix_of \<pi> \<sigma>' \<longrightarrow> sat \<sigma>' v i)"
begin

lemma cosafety: "\<sigma> \<in> traces \<Longrightarrow>
  sat \<sigma> v i \<longleftrightarrow> (\<exists>\<pi>. prefix_of \<pi> \<sigma> \<and> (\<forall>\<sigma>' \<in> traces. prefix_of \<pi> \<sigma>' \<longrightarrow> sat \<sigma>' v i))"
  using cosafety_lr by blast

end

subsection \<open>Monitor function\<close>

text \<open>
  We model monitors abstractly as functions from prefixes to verdict sets.
  The following locale specifies a minimal set of properties that any
  reasonable monitor should have.
\<close>

locale monitor = fo_spec +
  fixes M :: "'a prefix \<Rightarrow> (nat \<times> 'b tuple) set"
  assumes
    mono_monitor: "\<pi>' \<in> prefixes \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow> M \<pi> \<subseteq> M \<pi>'" and
    wf_monitor: "\<pi> \<in> prefixes \<Longrightarrow> (i, v) \<in> M \<pi> \<Longrightarrow> wf_tuple nfv fv v" and
    sound_monitor: "\<sigma> \<in> traces \<Longrightarrow> (i, v) \<in> M \<pi> \<Longrightarrow> prefix_of \<pi> \<sigma> \<Longrightarrow> sat \<sigma> (map the v) i" and
    complete_monitor: "\<sigma> \<in> traces \<Longrightarrow> prefix_of \<pi> \<sigma> \<Longrightarrow> wf_tuple nfv fv v \<Longrightarrow>
      (\<And>\<sigma>'. \<sigma>' \<in> traces \<Longrightarrow> prefix_of \<pi> \<sigma>' \<Longrightarrow> sat \<sigma>' (map the v) i) \<Longrightarrow>
      \<exists>\<pi>'. prefix_of \<pi>' \<sigma> \<and> (i, v) \<in> M \<pi>'"

text \<open>
  A monitor for a co-safety specification computes precisely the set of all
  satisfactions in the limit:
\<close>

abbreviation (in monitor) "M_limit \<sigma> \<equiv> \<Union>{M \<pi> | \<pi>. prefix_of \<pi> \<sigma>}"

locale cosafety_monitor = cosafety_fo_spec + monitor
begin

lemma M_limit_eq:
  assumes "\<sigma> \<in> traces"
  shows "M_limit \<sigma> = verdicts \<sigma>"
proof
  show "\<Union>{M \<pi> | \<pi>. prefix_of \<pi> \<sigma>} \<subseteq> verdicts \<sigma>"
    using assms wf_monitor sound_monitor by (auto simp: verdicts_def)
next
  show "\<Union>{M \<pi> | \<pi>. prefix_of \<pi> \<sigma>} \<supseteq> verdicts \<sigma>"
    unfolding verdicts_def
  proof safe
    fix i v
    assume "wf_tuple nfv fv v" and "sat \<sigma> (map the v) i"
    then obtain \<pi> where "prefix_of \<pi> \<sigma> \<and> (\<forall>\<sigma>'\<in>traces. prefix_of \<pi> \<sigma>' \<longrightarrow> sat \<sigma>' (map the v) i)"
      using assms cosafety_lr by blast
    with \<open>wf_tuple nfv fv v\<close> obtain \<pi>' where "prefix_of \<pi>' \<sigma> \<and> (i, v) \<in> M \<pi>'"
      using assms complete_monitor by blast
    then show "(i, v) \<in> \<Union>{M \<pi> | \<pi>. prefix_of \<pi> \<sigma>}"
      by blast
  qed
qed

end

text \<open>
  The monitor function \<^term>\<open>M\<close> adds some information over \<^term>\<open>sat\<close>, namely
  when a verdict is output. One possible behavior is that the monitor outputs
  its verdicts for one time-point at a time, in increasing order of
  time-points. Then \<^term>\<open>M\<close> is uniquely defined by a progress function, which
  returns for every prefix the time-point up to which all verdicts are computed.
\<close>

locale progress = fo_spec _ _ _ sat for sat :: "'a trace \<Rightarrow> 'b list \<Rightarrow> nat \<Rightarrow> bool" +
  fixes progress :: "'a prefix \<Rightarrow> nat"
  assumes
    progress_mono: "\<pi>' \<in> prefixes \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow> progress \<pi> \<le> progress \<pi>'" and
    ex_progress_ge: "\<sigma> \<in> traces \<Longrightarrow> \<exists>\<pi>. prefix_of \<pi> \<sigma> \<and> x \<le> progress \<pi>" and
    progress_sat_cong: "\<sigma> \<in> traces \<Longrightarrow> prefix_of \<pi> \<sigma> \<Longrightarrow> prefix_of \<pi> \<sigma>' \<Longrightarrow> i < progress \<pi> \<Longrightarrow>
      sat \<sigma> v i \<longleftrightarrow> sat \<sigma>' v i"
    \<comment> \<open>The last condition is not necessary to obtain a proper monitor function.
      However, it corresponds to the intuitive understanding of monitor progress,
      and it results in a stronger characterisation. In particular, it implies that
      the specification is co-safety, as we will show below.\<close>
begin

definition M :: "'a prefix \<Rightarrow> (nat \<times> 'b tuple) set" where
  "M \<pi> = {(i, v). i < progress \<pi> \<and> wf_tuple nfv fv v \<and>
    (\<forall>\<sigma> \<in> traces. prefix_of \<pi> \<sigma> \<longrightarrow> sat \<sigma> (map the v) i)}"

definition Mt :: "'a prefix \<Rightarrow> (nat \<times> nat \<times> 'b tuple) set" where
  "Mt \<pi> = (\<lambda>(i, v). (i, pts \<pi> ! i, v)) ` M \<pi>"

lemma M_alt: "\<pi> \<in> prefixes \<Longrightarrow> M \<pi> = {(i, v). i < progress \<pi> \<and> wf_tuple nfv fv v \<and>
    (\<exists>\<sigma> \<in> traces. prefix_of \<pi> \<sigma> \<and> sat \<sigma> (map the v) i)}"
  using ex_prefix_of[of \<pi>]
  by (auto simp: prefixes_def M_def cong: progress_sat_cong)

end

sublocale progress \<subseteq> cosafety_monitor _ _ _ _ M
proof
  fix i v and \<sigma> :: "'a trace"
  assume "\<sigma> \<in> traces" and "sat \<sigma> v i"
  moreover obtain \<pi> where *: "prefix_of \<pi> \<sigma>" "i < progress \<pi>"
    using \<open>\<sigma> \<in> traces\<close> ex_progress_ge by (auto simp: less_eq_Suc_le)
  ultimately have "sat \<sigma>' v i" if "prefix_of \<pi> \<sigma>'" for \<sigma>'
    using \<open>\<sigma> \<in> traces\<close> that progress_sat_cong by blast
  with * show "\<exists>\<pi>. prefix_of \<pi> \<sigma> \<and> (\<forall>\<sigma>' \<in> traces. prefix_of \<pi> \<sigma>' \<longrightarrow> sat \<sigma>' v i)"
    by blast
next
  fix \<pi> \<pi>' :: "'a prefix"
  assume "\<pi>' \<in> prefixes" and "\<pi> \<le> \<pi>'"
  then show "M \<pi> \<subseteq> M \<pi>'"
    by (auto simp: M_def intro: progress_mono prefix_of_antimono
        elim: order.strict_trans2)
next
  fix i v \<pi>
  assume "\<pi> \<in> prefixes" and "(i, v) \<in> M \<pi>"
  then show "wf_tuple nfv fv v"
    by (simp add: M_def)
next
  fix i v \<pi> and \<sigma> :: "'a trace"
  assume "\<sigma> \<in> traces" and "(i, v) \<in> M \<pi>" and "prefix_of \<pi> \<sigma>"
  then show "sat \<sigma> (map the v) i"
    by (simp add: M_def)
next
  fix i v \<pi> and \<sigma> :: "'a trace"
  assume *: "\<sigma> \<in> traces" "prefix_of \<pi> \<sigma>" "wf_tuple nfv fv v"
    "\<And>\<sigma>'. \<sigma>' \<in> traces \<Longrightarrow> prefix_of \<pi> \<sigma>' \<Longrightarrow> sat \<sigma>' (map the v) i"
  show "\<exists>\<pi>'. prefix_of \<pi>' \<sigma> \<and> (i, v) \<in> M \<pi>'"
  proof (cases "i < progress \<pi>")
    case True
    with * show ?thesis by (auto simp: M_def)
  next
    case False
    obtain \<pi>' where **: "prefix_of \<pi>' \<sigma> \<and> i < progress \<pi>'"
      using \<open>\<sigma> \<in> traces\<close> ex_progress_ge by (auto simp: less_eq_Suc_le)
    then have "\<pi> \<le> \<pi>'"
      using \<open>\<sigma> \<in> traces\<close> \<open>prefix_of \<pi> \<sigma>\<close> prefix_of_imp_linear False progress_mono
      by (blast intro: order.strict_trans2)
    with * ** show ?thesis
      by (auto simp: M_def intro: prefix_of_antimono)
  qed
qed

subsection \<open>Slicing\<close>

text \<open>Sliceable specifications can be evaluated meaningfully on a subset of events.\<close>

locale abstract_slicer =
  fixes relevant_events :: "'b list set \<Rightarrow> 'a set"
begin

abbreviation slice :: "'b list set \<Rightarrow> 'a set trace \<Rightarrow> 'a set trace" where
  "slice S \<equiv> map_\<Gamma> (\<lambda>D. D \<inter> relevant_events S)"

abbreviation pslice :: "'b list set \<Rightarrow> 'a set prefix \<Rightarrow> 'a set prefix" where
  "pslice S \<equiv> pmap_\<Gamma> (\<lambda>D. D \<inter> relevant_events S)"

lemma prefix_of_psliceI: "prefix_of \<pi> \<sigma> \<Longrightarrow> prefix_of (pslice S \<pi>) (slice S \<sigma>)"
  by (transfer fixing: S) auto

lemma plen_pslice[simp]: "plen (pslice S \<pi>) = plen \<pi>"
  by (transfer fixing: S) simp

lemma pslice_pnil[simp]: "pslice S pnil = pnil"
  by (transfer fixing: S) simp

lemma last_ts_pslice[simp]: "last_ts (pslice S \<pi>) = last_ts \<pi>"
  by (transfer fixing: S) (simp add: last_map case_prod_beta split: list.split)

abbreviation verdict_filter :: "'b list set \<Rightarrow> (nat \<times> 'b tuple) set \<Rightarrow> (nat \<times> 'b tuple) set" where
  "verdict_filter S V \<equiv> {(i, v) \<in> V. mem_restr S v}"

end

locale sliceable_fo_spec = fo_spec _ _ _ sat + abstract_slicer relevant_events
  for relevant_events :: "'b list set \<Rightarrow> 'a set" and sat :: "'a set trace \<Rightarrow> 'b list \<Rightarrow> nat \<Rightarrow> bool" +
  assumes
    slice_closed[simp, intro]: "\<sigma> \<in> traces \<Longrightarrow> slice S \<sigma> \<in> traces" and
    sliceable: "\<sigma> \<in> traces \<Longrightarrow> v \<in> S \<Longrightarrow> sat (slice S \<sigma>) v i \<longleftrightarrow> sat \<sigma> v i"
begin

lemma pslice_closed[simp, intro]: "\<pi> \<in> prefixes \<Longrightarrow> pslice S \<pi> \<in> prefixes"
  using prefix_of_pmap_\<Gamma> by (fastforce simp: prefixes_def)

lemma union_verdicts_slice:
  assumes part: "\<Union>\<S> = UNIV"
    and trace: "\<sigma> \<in> traces"
  shows "\<Union>((\<lambda>S. verdict_filter S (verdicts (slice S \<sigma>))) ` \<S>) = verdicts \<sigma>"
proof safe
  fix S i and v :: "'b tuple"
  assume "(i, v) \<in> verdicts (slice S \<sigma>)"
  then have tuple: "wf_tuple nfv fv v" and "sat (slice S \<sigma>) (map the v) i"
    by (auto simp: verdicts_def)
  assume "mem_restr S v"
  then obtain v' where "v' \<in> S" and 1: "\<forall>i\<in>fv. v ! i = Some (v' ! i)"
    using tuple by (auto simp: fv_less_nfv elim: mem_restrE)
  then have "sat (slice S \<sigma>) v' i"
    using trace \<open>sat (slice S \<sigma>) (map the v) i\<close> tuple
    by (auto simp: wf_tuple_length fv_less_nfv cong: sat_fv_cong)
  then have "sat \<sigma> v' i"
    using sliceable[OF trace \<open>v' \<in> S\<close>] by simp
  then have "sat \<sigma> (map the v) i"
    using trace tuple 1
    by (auto simp: wf_tuple_length fv_less_nfv cong: sat_fv_cong)
  then show "(i, v) \<in> verdicts \<sigma>"
    using tuple by (simp add: verdicts_def)
next
  fix i and v :: "'b tuple"
  assume "(i, v) \<in> verdicts \<sigma>"
  then have tuple: "wf_tuple nfv fv v" and "sat \<sigma> (map the v) i"
    by (auto simp: verdicts_def)
  from part obtain S where "S \<in> \<S>" and "map the v \<in> S"
    by blast
  then have "mem_restr S v"
    using mem_restrI[of "map the v" S nfv fv] tuple
    by (auto simp: wf_tuple_def fv_less_nfv)
  moreover have "sat (slice S \<sigma>) (map the v) i"
    using \<open>sat \<sigma> (map the v) i\<close> sliceable[OF trace \<open>map the v \<in> S\<close>] by simp
  then have "(i, v) \<in> verdicts (slice S \<sigma>)"
    using tuple by (simp add: verdicts_def)
  ultimately show "(i, v) \<in> (\<Union>S\<in>\<S>. verdict_filter S (verdicts (slice S \<sigma>)))"
    using \<open>S \<in> \<S>\<close> by blast
qed

end

text \<open>
  We define a similar notion for monitors. It is potentially stronger because
  the time-point at which verdicts are output must not change.
\<close>

locale sliceable_monitor = monitor _ _ _ sat M + abstract_slicer relevant_events
  for relevant_events :: "'b list set \<Rightarrow> 'a set" and sat :: "'a set trace \<Rightarrow> 'b list \<Rightarrow> nat \<Rightarrow> bool" and M +
  assumes sliceable_M: "\<pi> \<in> prefixes \<Longrightarrow> mem_restr S v \<Longrightarrow> (i, v) \<in> M (pslice S \<pi>) \<longleftrightarrow> (i, v) \<in> M \<pi>"
begin

lemma union_M_pslice:
  assumes part: "\<Union>\<S> = UNIV"
    and prefix: "\<pi> \<in> prefixes"
  shows "\<Union>((\<lambda>S. verdict_filter S (M (pslice S \<pi>))) ` \<S>) = M \<pi>"
proof safe
  fix S i and v :: "'b tuple"
  assume "mem_restr S v" and "(i, v) \<in> M (pslice S \<pi>)"
  then show "(i, v) \<in> M \<pi>" using sliceable_M prefix by blast
next
  fix i and v :: "'b tuple"
  assume "(i, v) \<in> M \<pi>"
  then have tuple: "wf_tuple nfv fv v"
    using prefix wf_monitor by blast
  from part obtain S where "S \<in> \<S>" and "map the v \<in> S"
    by blast
  then have "mem_restr S v"
    using mem_restrI[of "map the v" S nfv fv] tuple
    by (auto simp: wf_tuple_def fv_less_nfv)
  then have "(i, v) \<in> M (pslice S \<pi>)"
    using \<open>(i, v) \<in> M \<pi>\<close> sliceable_M prefix by blast
  then show "(i, v) \<in> (\<Union>S\<in>\<S>. verdict_filter S (M (pslice S \<pi>)))"
    using \<open>S \<in> \<S>\<close> \<open>mem_restr S v\<close> by blast
qed

end

text \<open>
  If the specification is sliceable and the monitor's progress depends only on
  time-stamps, then also the monitor itself is sliceable.
\<close>

locale timed_progress = progress +
  assumes progress_time_conv: "\<pi> \<in> prefixes \<Longrightarrow> \<pi>' \<in> prefixes \<Longrightarrow>
    pts \<pi> = pts \<pi>' \<Longrightarrow> progress \<pi> = progress \<pi>'"

locale sliceable_timed_progress = sliceable_fo_spec + timed_progress
begin

lemma progress_pslice[simp]: "\<pi> \<in> prefixes \<Longrightarrow> progress (pslice S \<pi>) = progress \<pi>"
  by (simp cong: progress_time_conv)

end

sublocale sliceable_timed_progress \<subseteq> sliceable_monitor _ _ _ _ _ M
proof
  fix S :: "'b list set" and v i \<pi>
  assume *: "\<pi> \<in> prefixes" "mem_restr S v"
  show "(i, v) \<in> M (pslice S \<pi>) \<longleftrightarrow> (i, v) \<in> M \<pi>" (is "?L \<longleftrightarrow> ?R")
  proof
    assume ?L
    with * show ?R
      by (auto 0 4 simp: M_def wf_tuple_def elim!: mem_restrE
          box_equals[OF sliceable sat_fv_cong sat_fv_cong, THEN iffD1, rotated -1]
          intro: prefix_of_psliceI dest: fv_less_nfv spec[of _ "slice S _"]) (* SLOW *)
  next
    assume ?R
    with * show ?L
      by (auto 0 4 simp: M_alt wf_tuple_def elim!: mem_restrE
        box_equals[OF sliceable sat_fv_cong sat_fv_cong, THEN iffD2, rotated -1]
        intro: exI[of _ "slice S _"] prefix_of_psliceI dest: fv_less_nfv) (* SLOW *)
  qed
qed

(*<*)
end
(*>*)
