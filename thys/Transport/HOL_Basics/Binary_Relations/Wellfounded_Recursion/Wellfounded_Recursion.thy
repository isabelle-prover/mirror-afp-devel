\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Niklas Krofta"\<close>
section \<open>Well-Founded Recursion\<close>
theory Wellfounded_Recursion
  imports
    Binary_Relations_Transitive_Closure
    Wellfounded_Transitive_Recursion
begin

paragraph \<open>Summary\<close>
text \<open>We use @{term wftrec} to define well-founded recursion on non-transitive, well-founded
relations. The fact that the transitive closure of a well-founded relation is itself well-founded
can be used to remove the transitivity assumption of @{thm wftrec_eq_wfrec_stepI}.\<close>

lemma wellfounded_trans_closure_if_wellfounded:
  assumes "wellfounded R"
  shows "wellfounded (trans_closure R)"
proof (rule ccontr)
  assume "\<not>(wellfounded (trans_closure R))"
  then obtain P X where "P X" and no_minimal: "\<And>Y. P Y \<Longrightarrow> (\<exists>y. trans_closure R y Y \<and> P y)"
    unfolding wellfounded_rel_def by auto
  from assms have "\<not>(P Y) \<and> (\<forall>y. trans_closure R y Y \<longrightarrow> \<not>(P y))" for Y
  proof (induction Y rule: wellfounded_induct)
    case (step Y)
    show ?case
    proof (rule ccontr)
      assume "\<not>(\<not>(P Y) \<and> (\<forall>y. trans_closure R y Y \<longrightarrow> \<not>(P y)))"
      then consider "P Y" | y where "trans_closure R y Y" "P y" by blast
      then show "False"
      proof cases
        case 1
        then obtain y where "trans_closure R y Y" "P y" using no_minimal by blast
        then show "False" using step.IH trans_closure_cases by force
      next
        case 2
        then show "False" using step.IH trans_closure_cases by force
      qed
    qed
  qed
  then show "False" using \<open>P X\<close> by blast
qed

definition "wfrec R step = wftrec (trans_closure R) (\<lambda>f. wfrec_step R step (\<lambda>_. f))"

theorem wfrec_eq_wfrec_stepI:
  assumes "wellfounded R"
  shows "wfrec R step X = wfrec_step R step (\<lambda>_. wfrec R step) X"
proof -
  have fun_rel_restrict_eq:
    "fun_rel_restrict (fun_rel_restrict f (trans_closure R) X) R X x = fun_rel_restrict f R X x"
    for f x by (cases "R x X") (auto dest: trans_closure_if_rel)
  have "wfrec R step X = wfrec_step R step (fun_rel_restrict (wfrec R step) (trans_closure R)) X"
    using wellfounded_trans_closure_if_wellfounded[OF assms] transitive_trans_closure[of R]
    wftrec_eq_wfrec_stepI[where ?step="\<lambda>f. wfrec_step R step (\<lambda>_. f)"]
    by (simp add: wfrec_step_eq wfrec_def)
  then show ?thesis unfolding wfrec_step_eq fun_rel_restrict_eq by simp
qed


end