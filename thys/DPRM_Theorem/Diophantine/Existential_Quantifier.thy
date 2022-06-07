subsection \<open>Existential quantification is Diophantine\<close>

theory Existential_Quantifier
  imports Diophantine_Relations
begin

lemma exist_list_dioph[dioph]:
  fixes D
  assumes "is_dioph_rel D"
  shows "is_dioph_rel ([\<exists>n] D)"
proof (induction n)
  case 0
  then show ?case
    using assms unfolding is_dioph_rel_def by (auto simp: push_list_empty)
next
  case (Suc n)

  have h: "(\<lambda>i. if i = 0 then v 0 else v i) = v" for v::assignment
    by auto

  have "eval ([\<exists>Suc n] D) a = (\<exists>k::nat. eval ([\<exists>n] D) (push a k))" for a
    apply (simp add: push_list2)
    by (smt (z3) Zero_not_Suc add_Suc_right append_Nil2 length_Cons
                 length_append list.size(3) nat.inject rev_exhaust)
  moreover from Suc is_dioph_rel_def obtain P\<^sub>1 P\<^sub>2 where
    "\<forall>a. eval ([\<exists>n] D) a = (\<exists>v. ppeval P\<^sub>1 a v = ppeval P\<^sub>2 a v)"
    by auto
  ultimately have t1: "eval ([\<exists>Suc n] D) a = (\<exists>k::nat. (\<exists>v. ppeval P\<^sub>1 (push a k) v
                                                            = ppeval P\<^sub>2 (push a k) v))" for a
    by simp

  define f :: "ppolynomial \<Rightarrow> ppolynomial" where
    "f \<equiv> \<lambda>P. pull_param (push_var P 1) (Var 0)"
  have "ppeval P (push a k) v = ppeval (f P) a (push v k)" for P a k v
    apply (induction P, auto simp: push_def f_def)
    by (metis (no_types, lifting) Suc_pred ppeval.simps(2) pull_param.simps(2))
  then have t2: "eval ([\<exists>Suc n] D) a = (\<exists>k::nat. (\<exists>v. ppeval (f P\<^sub>1) a (push v k)
                                                      = ppeval (f P\<^sub>2) a (push v k)))" for a
    using t1 by auto
  moreover have "(\<exists>k::nat. \<exists>v. ppeval P a (push v k) = ppeval Q a (push v k))
                  \<longleftrightarrow> (\<exists>v. ppeval P a v = ppeval Q a v)" for P Q a
    unfolding push_def
    apply auto
    subgoal for v
      apply (rule exI[of _ "v 0"])
      apply (rule exI[of _ "\<lambda>i. v (i + 1)"])
      by (auto simp: h cong: if_cong)
    done
  ultimately have "eval ([\<exists>Suc n] D) a = (\<exists>v. ppeval (f P\<^sub>1) a v = ppeval (f P\<^sub>2) a v)" for a
    by auto

  thus ?case
    unfolding is_dioph_rel_def by auto
qed

lemma exist_dioph[dioph]:
  fixes D
  assumes "is_dioph_rel D"
  shows "is_dioph_rel ([\<exists>] D)"
  unfolding EXIST_def using assms by (auto simp: exist_list_dioph)

lemma exist_eval[defs]:
  shows "eval ([\<exists>] D) a = (\<exists>k. eval D (push a k))"
  unfolding EXIST_def apply (simp add: push_list_def)
  by (metis length_Suc_conv list.exhaust list.size(3) nat.simps(3) push_list_singleton)

end