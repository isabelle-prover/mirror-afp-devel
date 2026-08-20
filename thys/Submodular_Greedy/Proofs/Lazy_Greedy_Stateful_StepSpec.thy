theory Lazy_Greedy_Stateful_StepSpec
  imports "../Algorithms/Lazy_Greedy_Stateful"
begin

text \<open>
  Sequence-level lemmas for the verified stateful lazy run.

  This theory packages the per-iteration facts needed by the approximation
  proof, such as the membership and maximal-gain properties of the chosen
  lazy element at step \<open>i\<close>, together with the update equation for the next lazy set.

  It is not formalized by instantiating the stateless greedy step-oracle locale.
  Instead, it exposes the corresponding properties of the concrete verified run.
\<close>

context Cardinality_Constraint
begin

abbreviation st_i :: "nat \<Rightarrow> 'a lg_state" where
  "st_i i \<equiv> lazy_state i"

abbreviation S_i :: "nat \<Rightarrow> 'a set" where
  "S_i i \<equiv> lazy_set i"

abbreviation A_i :: "nat \<Rightarrow> 'a set" where
  "A_i i \<equiv> remaining (st_i i)"

lemma A_i_eq: "A_i i = V - S_i i"
  by (simp add: remaining_def lazy_set_def)

definition lazy_choice :: "nat \<Rightarrow> 'a" where
  "lazy_choice i = fst (lazy_select (S_i i) (A_i i) (ubg (st_i i)))"

lemma A_i_finite: "finite (A_i i)"
proof -
  have Ssub: "Sg (st_i i) \<subseteq> V"
    using lazy_state_subset_V[of i] .
  have Asub: "A_i i \<subseteq> V"
    by (simp add: A_i_eq lazy_set_def Ssub)
  show ?thesis
    using finite_subset[OF Asub finite_V] .
qed

lemma lazy_choice_mem:
  assumes ne: "A_i i \<noteq> {}"
  shows "lazy_choice i \<in> A_i i"
proof -
  have finA: "finite (A_i i)" by (rule A_i_finite)
  have eq: "lazy_choice i = lazy_argmax_gain (S_i i) (A_i i) (ubg (st_i i))"
    by (simp add: lazy_choice_def lazy_select_fst)
  show ?thesis
    unfolding eq
    using lazy_argmax_gain_mem[OF finA ne] .
qed

lemma lazy_choice_max:
  assumes ne: "A_i i \<noteq> {}"
  shows "\<forall>y\<in>A_i i. gain (S_i i) y \<le> gain (S_i i) (lazy_choice i)"
proof -
  have finA: "finite (A_i i)"
    by (rule A_i_finite)

  have ubv: "ub_valid (S_i i) (A_i i) (ubg (st_i i))"
  proof -
    have ubvR: "ub_valid (Sg (st_i i)) (remaining (st_i i)) (ubg (st_i i))"
      using lazy_state_ub_valid[of i] by simp
    show ?thesis
      using ubvR
      by (simp add: A_i_eq lazy_set_def remaining_def)
  qed

  have max_arg:
    "\<forall>y\<in>A_i i.
       gain (S_i i) y \<le> gain (S_i i) (lazy_argmax_gain (S_i i) (A_i i) (ubg (st_i i)))"
    using lazy_argmax_gain_max[OF finA ne ubv] .

  show ?thesis
    using max_arg
    by (simp add: lazy_choice_def lazy_select_fst)
qed

lemma lazy_set_Suc_insert:
  assumes ne: "A_i i \<noteq> {}"
  shows "S_i (Suc i) = insert (lazy_choice i) (S_i i)"
proof -
  have rem_ne: "remaining (st_i i) \<noteq> {}" using ne by simp
  have Sg_step:
    "Sg (lazy_step (st_i i)) =
      insert (fst (lazy_select (Sg (st_i i)) (remaining (st_i i)) (ubg (st_i i))))
             (Sg (st_i i))"
    using lazy_step_nonempty_Sg[OF rem_ne] .
  show ?thesis
    by (simp add: lazy_set_def lazy_choice_def Sg_step)
qed

lemma lazy_choice_in_V_minus_S:
  assumes "V - lazy_set i \<noteq> {}"
  shows "lazy_choice i \<in> V - lazy_set i"
  using lazy_choice_mem[of i] assms
  by (simp add: A_i_eq)

lemma lazy_choice_argmax_V_minus_S:
  assumes "V - lazy_set i \<noteq> {}"
  shows "\<forall>y\<in>V - lazy_set i. gain (lazy_set i) y \<le> gain (lazy_set i) (lazy_choice i)"
  using lazy_choice_max[of i] assms
  by (simp add: A_i_eq)

lemma lazy_set_Suc_insert_V_minus_S:
  assumes "V - lazy_set i \<noteq> {}"
  shows "lazy_set (Suc i) = insert (lazy_choice i) (lazy_set i)"
  using lazy_set_Suc_insert[of i] assms
  by (simp add: A_i_eq)

end
end