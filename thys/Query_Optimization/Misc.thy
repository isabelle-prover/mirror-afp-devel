theory Misc
  imports Main "Graph_Theory.Shortest_Path"
begin

text \<open>These are some utility lemmas which are not directly concerned with the graph library.\<close>

lemma Sup_in_set:
"\<lbrakk> finite (A::('a::complete_linorder) set); A \<noteq> {}; a = Sup A\<rbrakk>
  \<Longrightarrow> a \<in> A"
proof(induction A arbitrary: a rule: finite_induct)
  case (insert x F)
  show ?case
  proof(cases "F = {}")
    case False
    with insert.IH have "\<exists>y. Sup F = y \<and> y \<in> F" by simp
    then obtain y where y_def: "Sup F = y" and y_in_F: "y \<in> F" by blast

    have [simp]: "Sup (insert x F) = sup x (Sup F)"
      using insert.hyps(1)
      by (induction F rule: finite_induct) (auto)

    with insert show ?thesis
    proof(cases "y \<le> x")
      case True
      then have "Sup (insert x F) = x"
        by (simp add: sup.absorb_iff1 y_def)
      with insert.prems(2) show ?thesis by blast
    next
      case False
      with y_def have "Sup (insert x F) = y"
        by (simp add: sup.absorb2)
      with insert.prems(2) y_in_F show ?thesis by blast
    qed
  qed (simp add: insert.prems)
qed simp

text \<open>Analogous to the proof of @{thm Sup_in_set}.\<close>
lemma Inf_in_set:
"\<lbrakk> finite (A::('a::complete_linorder) set); A \<noteq> {}; a = Inf A\<rbrakk>
  \<Longrightarrow> a \<in> A"
proof(induction A arbitrary: a rule: finite_induct)
  case (insert x F)
  show ?case
  proof(cases "F = {}")
    case False
    with insert.IH have "\<exists>y. Inf F = y \<and> y \<in> F" by simp
    then obtain y where y_def: "Inf F = y" and y_in_F: "y \<in> F" by blast

    have [simp]: "Inf (insert x F) = inf x (Inf F)"
      using insert.hyps(1)
      by (induction F rule: finite_induct) (auto)

    with insert show ?thesis
    proof(cases "y \<ge> x")
      case True
      then have "Inf (insert x F) = x"
        by (simp add: inf.absorb_iff1 y_def)
      with insert.prems(2) show ?thesis by blast
    next
      case False
      with y_def have "Inf (insert x F) = y"
        by (simp add: inf.absorb2)
      with insert.prems(2) y_in_F show ?thesis by blast
    qed
  qed (simp add: insert.prems)
qed simp

lemma mem_card1_singleton: "\<lbrakk> u \<in> U; card U = 1 \<rbrakk> \<Longrightarrow> U = {u}"
  by (metis card_1_singletonE singletonD)

lemma finite_Union: "\<lbrakk> finite A; \<forall>x \<in> A. finite (a x) \<rbrakk> \<Longrightarrow> finite (\<Union>{a x|x. x \<in> A})"
  by (induction A rule: finite_induct) (auto)

end