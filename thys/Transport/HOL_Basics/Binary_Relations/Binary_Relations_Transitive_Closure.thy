\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Transitive Closure\<close>
theory Binary_Relations_Transitive_Closure
  imports
    Binary_Relations_Least
    Binary_Relations_Transitive
begin

consts trans_closure_on :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"

definition "trans_closure_on_pred (P :: 'a \<Rightarrow> bool) R x y \<equiv>
  \<forall>(R' :: 'a \<Rightarrow> 'a \<Rightarrow> bool) : transitive_on P. R \<le> R' \<longrightarrow> R' x y"
adhoc_overloading trans_closure_on trans_closure_on_pred

lemma trans_closure_on_if_all_trans_relI:
  assumes "\<And>R'. transitive_on P R' \<Longrightarrow> R \<le> R' \<Longrightarrow> R' x y"
  shows "trans_closure_on P R x y"
  using assms unfolding trans_closure_on_pred_def by auto

lemma all_rel_if_trans_closure_onE:
  assumes "trans_closure_on P R x y"
  obtains "\<And>R'. transitive_on P R' \<Longrightarrow> R \<le> R' \<Longrightarrow> R' x y"
  using assms unfolding trans_closure_on_pred_def by auto

lemma transitive_on_trans_closure_on: "transitive_on P (trans_closure_on P R)"
  by (intro transitive_onI trans_closure_on_if_all_trans_relI, elim all_rel_if_trans_closure_onE)
  (blast dest: transitive_onD)

lemma trans_closure_on_le_if_le_if_transitive_on:
  assumes "transitive_on P S"
  and "R \<le> S"
  shows "trans_closure_on P R \<le> S"
  using assms by (intro le_relI trans_closure_on_if_all_trans_relI) (elim all_rel_if_trans_closure_onE)

lemma trans_closure_on_if_rel: "R x y \<Longrightarrow> trans_closure_on P R x y"
  by (intro trans_closure_on_if_all_trans_relI) auto

corollary le_trans_closure_on: "R \<le> trans_closure_on P R"
  using trans_closure_on_if_rel by fast

corollary is_least_wrt_rel_trans_closure_on:
  "is_least_wrt_rel (\<le>) ((\<le>) R \<sqinter> transitive_on P) (trans_closure_on P R)"
  by (intro is_least_wrt_rel_if_antisymmetric_onI is_minimal_wrt_relI inf1I
    trans_closure_on_le_if_le_if_transitive_on le_trans_closure_on transitive_on_trans_closure_on)
  auto

corollary trans_closure_on_eq_least_wrt_rel:
  "trans_closure_on P R = least_wrt_rel (\<le>) ((\<le>) R \<sqinter> transitive_on P)"
  by (intro least_wrt_rel_eqI[symmetric] is_least_wrt_rel_trans_closure_on)

lemma trans_closure_on_le_sup:
  fixes P R defines "S \<equiv> R \<squnion> (\<lambda>x y. P x \<and> P y \<and> (\<exists>z : P. trans_closure_on P R x z \<and> R z y))"
  shows "trans_closure_on P R \<le> S"
proof (rule trans_closure_on_le_if_le_if_transitive_on)
  show "transitive_on P S"
  proof (intro transitive_onI)
    fix x y z assume Ps: "P x" "P y" "P z" and "S x y"
    then have txy: "trans_closure_on P R x y" unfolding S_def
      using transitive_on_trans_closure_on[of P R] by (elim sup2E conjE bexE)
      (blast dest: trans_closure_on_if_rel[of R] transitive_onD
        intro: trans_closure_on_if_all_trans_relI)+
    assume "S y z"
    then consider "R y z" | z' where "P z'" "trans_closure_on P R y z'" "R z' z"
      unfolding S_def by auto
    then show "S x z"
    proof cases
      case 1 with Ps txy show ?thesis unfolding S_def by fastforce
    next
      case 2 with Ps txy show ?thesis unfolding S_def
        using transitive_on_trans_closure_on[of P R] by (fastforce dest: transitive_onD)
    qed
  qed
  show "R \<le> S" unfolding S_def by fastforce
qed

lemma trans_closure_on_cases:
  assumes "trans_closure_on P R x y"
  obtains (rel) "R x y" | (step) z where "P x" "P z" "P y" "trans_closure_on P R x z" "R z y"
  using le_relD[OF trans_closure_on_le_sup assms] by auto

lemma trans_closure_on_eq_rel_sup_trans_closure_on:
  "trans_closure_on P R = R \<squnion> trans_closure_on P R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>P\<^esub>"
proof -
  have "R' x y" if "\<And>R'. transitive_on P R' \<Longrightarrow> R \<le> R' \<Longrightarrow> R' x y" "\<not>(R x y)" "transitive_on P R'"
    "R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>P\<^esub> \<le> R'" for R' x y
  proof -
    let ?R'plus = "R \<squnion> R'"
    from that(3-4) have "transitive_on P ?R'plus"
      by (intro transitive_onI sup2CI) (auto dest: transitive_onD)+
    with that show ?thesis by fastforce
  qed
  moreover have "R' x y" if "\<And>R'. transitive_on P R' \<Longrightarrow> R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>P\<^esub> \<le> R' \<Longrightarrow> R' x y" "transitive_on P R'"
    "R \<le> R'" for R' x y
    using that by blast
  ultimately show ?thesis
    by (intro ext iffI sup2CI; elim sup2E all_rel_if_trans_closure_onE )
    (blast intro!: trans_closure_on_if_all_trans_relI dest: transitive_onD)+
qed

consts trans_closure :: "'a \<Rightarrow> 'a"

definition "trans_closure_rel \<equiv> trans_closure_on \<top>"
adhoc_overloading trans_closure trans_closure_rel

lemma trans_closure_eq_trans_closure_on: "trans_closure = trans_closure_on \<top>"
  unfolding trans_closure_rel_def ..

lemma trans_closure_eq_trans_closure_on_uhint [uhint]:
  assumes "P \<equiv> \<top>"
  shows "trans_closure = trans_closure_on P"
  using assms trans_closure_eq_trans_closure_on by simp

lemma trans_closure_iff_trans_closure_on: "trans_closure R x y = trans_closure_on \<top> R x y"
  unfolding trans_closure_eq_trans_closure_on by simp

lemma all_rel_if_trans_closureE:
  assumes "trans_closure R x y"
  obtains "\<And>R'. transitive R' \<Longrightarrow> R \<le> R' \<Longrightarrow> R' x y"
  using assms by (urule (e) all_rel_if_trans_closure_onE)

lemma transitive_trans_closure: "transitive (trans_closure R)"
  by (urule transitive_on_trans_closure_on)

lemma trans_closure_le_if_le_if_transitive:
  assumes "transitive S"
  and "R \<le> S"
  shows "trans_closure R \<le> S"
  using assms by (urule trans_closure_on_le_if_le_if_transitive_on)

lemma trans_closure_if_rel: "R x y \<Longrightarrow> trans_closure R x y"
  by (urule trans_closure_on_if_rel)

corollary trans_closure_eq_least_wrt_rel: "trans_closure R = least_wrt_rel (\<le>) ((\<le>) R \<sqinter> transitive)"
  by (urule trans_closure_on_eq_least_wrt_rel)

lemma trans_closure_cases:
  assumes "trans_closure R x y"
  obtains (rel) "R x y" | (step) z where "trans_closure R x z" "R z y"
  using assms unfolding trans_closure_eq_trans_closure_on by (urule (e) trans_closure_on_cases)

end