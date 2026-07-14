section \<open>Candidate-set extraction certificates\<close>

theory Extraction_Certificates
  imports EGraph_Explanations
begin

text \<open>
  This lightweight interchange checker validates an explicitly enumerated
  candidate set: the chosen term is convertible to the source and has minimum
  cost among the supplied candidates.  The stronger acyclic-e-graph development
  builds and verifies a dynamic-programming extractor over every term
  represented by a finite e-class DAG.
\<close>

fun term_cost :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) term \<Rightarrow> nat" where
  "term_cost w (Var x) = 1"
| "term_cost w (Fun f ts) = w f + sum_list (map (term_cost w) ts)"

record ('f, 'v) extraction =
  ex_source :: "('f, 'v) term"
  ex_chosen :: "('f, 'v) term"
  ex_candidates ::
    "(('f, 'v) term \<times> ('f, 'v) certificate_step list) list"

definition check_extraction ::
  "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) rule list \<Rightarrow>
    ('f, 'v) rule list \<Rightarrow> ('f, 'v) extraction \<Rightarrow> bool" where
  "check_extraction w R \<Gamma> E \<longleftrightarrow>
     (\<forall>p \<in> set (ex_candidates E).
        check_explanation R \<Gamma> (snd p) (ex_source E) (fst p)) \<and>
     ex_chosen E \<in> set (map fst (ex_candidates E)) \<and>
     (\<forall>v \<in> set (map fst (ex_candidates E)).
        term_cost w (ex_chosen E) \<le> term_cost w v)"

lemma check_extraction_candidate_sound:
  assumes merges: "\<forall>ab \<in> set \<Gamma>.
      (fst ab, snd ab) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    and check: "check_extraction w R \<Gamma> E"
    and candidate: "v \<in> set (map fst (ex_candidates E))"
  shows "(ex_source E, v) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  from candidate obtain p where
    p: "p \<in> set (ex_candidates E)" and v: "fst p = v"
    by force
  from check p have
    "check_explanation R \<Gamma> (snd p) (ex_source E) (fst p)"
    unfolding check_extraction_def by blast
  from check_explanation_sound[OF merges this] v show ?thesis by simp
qed

lemma check_extraction_chosen_sound:
  assumes "\<forall>ab \<in> set \<Gamma>.
      (fst ab, snd ab) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    and "check_extraction w R \<Gamma> E"
  shows "(ex_source E, ex_chosen E) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  from assms(2) have
    "ex_chosen E \<in> set (map fst (ex_candidates E))"
    unfolding check_extraction_def by simp
  from check_extraction_candidate_sound[OF assms this] show ?thesis .
qed

lemma check_extraction_minimal:
  assumes "check_extraction w R \<Gamma> E"
    and "v \<in> set (map fst (ex_candidates E))"
  shows "term_cost w (ex_chosen E) \<le> term_cost w v"
  using assms unfolding check_extraction_def by blast

theorem extraction_over_checked_log_correct:
  assumes log: "check_merge_log R mlog"
    and extraction:
      "check_extraction w R (recorded_merges mlog) E"
  shows "(ex_source E, ex_chosen E)
           \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    and "\<forall>v \<in> set (map fst (ex_candidates E)).
           term_cost w (ex_chosen E) \<le> term_cost w v"
proof -
  have merges: "\<forall>ab \<in> set (recorded_merges mlog).
      (fst ab, snd ab) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    using checked_merge_log_sound[OF log] by blast
  show "(ex_source E, ex_chosen E)
      \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*"
    by (rule check_extraction_chosen_sound[OF merges extraction])
  show "\<forall>v \<in> set (map fst (ex_candidates E)).
      term_cost w (ex_chosen E) \<le> term_cost w v"
    using extraction unfolding check_extraction_def by blast
qed

end
