section {* Refinement for Transition Systems *}

theory Transition_System_Refine
imports
  "Transition_System"
  "../Basic/Refine"
begin

  lemma path_param[param]: "(transition_system.path, transition_system.path) \<in>
    (T \<rightarrow> S \<rightarrow> S) \<rightarrow> (T \<rightarrow> S \<rightarrow> bool_rel) \<rightarrow> \<langle>T\<rangle> list_rel \<rightarrow> S \<rightarrow> bool_rel"
  proof (rule, rule)
    fix exa exb ena enb
    assume [param]: "(exa, exb) \<in> T \<rightarrow> S \<rightarrow> S" "(ena, enb) \<in> T \<rightarrow> S \<rightarrow> bool_rel"
    interpret A: transition_system exa ena by this
    interpret B: transition_system exb enb by this
    have [param]: "(A.path [] p, B.path [] q) \<in> bool_rel" for p q by auto
    have [param]: "(A.path (a # r) p, B.path (b # s) q) \<in> bool_rel"
      if "(ena a p, enb b q) \<in> bool_rel" "(A.path r (exa a p), B.path s (exb b q)) \<in> bool_rel"
      for a r p b s q
      using that by auto
    show "(A.path, B.path) \<in> \<langle>T\<rangle> list_rel \<rightarrow> S \<rightarrow> bool_rel"
    proof (intro fun_relI)
      show "(A.path r p, B.path s q) \<in> bool_rel" if "(r, s) \<in> \<langle>T\<rangle> list_rel" "(p, q) \<in> S" for r s p q
        using that by (induct arbitrary: p q) (parametricity+)
    qed
  qed
  lemma run_param[param]: "(transition_system.run, transition_system.run) \<in>
    (T \<rightarrow> S \<rightarrow> S) \<rightarrow> (T \<rightarrow> S \<rightarrow> bool_rel) \<rightarrow> \<langle>T\<rangle> stream_rel \<rightarrow> S \<rightarrow> bool_rel"
  proof (rule, rule)
    fix exa exb ena enb
    assume 1: "(exa, exb) \<in> T \<rightarrow> S \<rightarrow> S" "(ena, enb) \<in> T \<rightarrow> S \<rightarrow> bool_rel"
    interpret A: transition_system exa ena by this
    interpret B: transition_system exb enb by this
    show "(A.run, B.run) \<in> \<langle>T\<rangle> stream_rel \<rightarrow> S \<rightarrow> bool_rel"
    proof safe
      show "B.run s q" if "(r, s) \<in> \<langle>T\<rangle> stream_rel" "(p, q) \<in> S" "A.run r p" for r s p q
        using 1[param_fo] that by (coinduction arbitrary: r s p q) (blast elim: stream_rel_cases)
      show "A.run r p" if "(r, s) \<in> \<langle>T\<rangle> stream_rel" "(p, q) \<in> S" "B.run s q" for r s p q
        using 1[param_fo] that by (coinduction arbitrary: r s p q) (blast elim: stream_rel_cases)
    qed
  qed

end
