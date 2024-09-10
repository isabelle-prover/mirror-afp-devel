\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Niklas Krofta"\<close>
subsection \<open>Well-Founded Recursion\<close>
theory Wellfounded_Recursion
  imports
    Binary_Relations_Transitive_Closure
    Wellfounded_Transitive_Recursion
begin

paragraph \<open>Summary\<close>
text \<open>We use @{term wft_rec} to define well-founded recursion on non-transitive, well-founded
relations. The fact that the transitive closure of a well-founded relation is itself well-founded
can be used to remove the transitivity assumption of @{thm wft_rec_eq_wf_rec_stepI}.\<close>

lemma wellfounded_trans_closure_if_wellfounded:
  assumes "wellfounded R"
  shows "wellfounded (trans_closure R)"
proof (rule ccontr)
  assume "\<not>(wellfounded (trans_closure R))"
  then obtain P X where "P X" and no_minimal: "\<And>Y. P Y \<Longrightarrow> (\<exists>y. trans_closure R y Y \<and> P y)"
    unfolding wellfounded_eq_wellfounded_on wellfounded_on_pred_def by auto
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

consts wf_rec :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"

definition "wf_rec_rel R step = wft_rec (trans_closure R) (\<lambda>f. wf_rec_step R step (\<lambda>_. f))"
adhoc_overloading wf_rec wf_rec_rel

theorem wf_rec_eq_wf_rec_stepI:
  assumes "wellfounded R"
  shows "wf_rec R step X = wf_rec_step R step (\<lambda>_. wf_rec R step) X"
proof -
  have fun_rel_restrict_eq:
    "fun_rel_restrict (fun_rel_restrict f (trans_closure R) X) R X x = fun_rel_restrict f R X x"
    for f x by (cases "R x X") (auto dest: trans_closure_if_rel)
  have "wf_rec R step X = wf_rec_step R step (fun_rel_restrict (wf_rec R step) (trans_closure R)) X"
    using wellfounded_trans_closure_if_wellfounded[OF assms] transitive_trans_closure[of R]
    wft_rec_eq_wf_rec_stepI[where ?step="\<lambda>f. wf_rec_step R step (\<lambda>_. f)"]
    by (simp add: wf_rec_step_eq wf_rec_rel_def)
  then show ?thesis unfolding wf_rec_step_eq fun_rel_restrict_eq by simp
qed

consts wf_rec_on :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd"

definition wf_rec_on_pred :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
  "wf_rec_on_pred P R \<equiv> wf_rec R\<up>\<^bsub>P\<^esub>"
adhoc_overloading wf_rec_on wf_rec_on_pred

lemma wf_rec_on_eq_wf_rec_restrict: "wf_rec_on P R = wf_rec R\<up>\<^bsub>P\<^esub>"
  unfolding wf_rec_on_pred_def by simp

theorem wf_rec_on_eq_wf_rec_step_restrictI:
  assumes "wellfounded_on P R"
  shows "wf_rec_on P R step X = wf_rec_step R\<up>\<^bsub>P\<^esub> step (\<lambda>_. wf_rec_on P R step) X"
proof -
  from assms have "wellfounded R\<up>\<^bsub>P\<^esub>" using wellfounded_rel_restrict_if_wellfounded_on by blast
  with wf_rec_eq_wf_rec_stepI show ?thesis unfolding wf_rec_on_eq_wf_rec_restrict by fastforce
qed

lemma wf_rec_on_eq_app_fun_restrict_fun_rel_restrictI:
  fixes step
  assumes wf: "wellfounded_on P R"
  and "P x"
  defines "f \<equiv> wf_rec_on P R step"
  shows "f x = step (fun_restrict (fun_rel_restrict f R x) P) x"
proof -
  from wf have "f x = step (fun_rel_restrict f R\<up>\<^bsub>P\<^esub> x) x"
    unfolding f_def by (simp only: wf_rec_step_eq wf_rec_on_eq_wf_rec_step_restrictI)
  moreover have "fun_rel_restrict f R\<up>\<^bsub>P\<^esub> x = fun_restrict (fun_rel_restrict f R x) P"
    using \<open>P x\<close> fun_rel_restrict_rel_restrict_eq_fun_restrict_fun_rel_restrictI by simp
  ultimately show ?thesis by simp
qed


end