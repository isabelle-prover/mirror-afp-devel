\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Extending Functions\<close>
theory Binary_Relations_Function_Extend
  imports
    Binary_Relations_Clean_Function
begin

lemma left_total_on_eq_sup_extend_if_left_total_on:
  assumes "left_total_on A R"
  shows "left_total_on ((=) x \<squnion> A) (extend x y R)"
  using assms by fastforce

lemma right_unique_on_eq_sup_extend_if_not_in_dom_if_right_unique_on:
  assumes "right_unique_on A R"
  and "\<not>(in_dom R x)"
  shows "right_unique_on ((=) x \<squnion> A) (extend x y R)"
  using assms by (intro right_unique_onI) (auto dest: right_unique_onD elim!: extendE)

lemma rel_dep_mono_wrt_eq_sup_if_extend_if_rel_dep_mono_wrt_predI:
  assumes "((x : A) \<rightarrow> B x) R"
  and "\<not>(in_dom R x)"
  shows "((x' : (=) x \<squnion> A) \<rightarrow> (if x' = x then (=) y else B x')) (extend x y R)"
  using assms by (intro rel_dep_mono_wrt_predI left_total_on_eq_sup_extend_if_left_total_on
    right_unique_on_eq_sup_extend_if_not_in_dom_if_right_unique_on dep_mono_wrt_predI)
  auto

lemma rel_dep_mono_wrt_eq_sup_extend_if_rel_dep_mono_wrt_predI:
  assumes "((x : A) \<rightarrow> B x) R"
  and "\<not>(in_dom R x)"
  and "B x y"
  shows "((x' : (=) x \<squnion> A) \<rightarrow> B x') (extend x y R)"
  by (urule rel_dep_mono_wrt_pred_covariant_codom,
    urule rel_dep_mono_wrt_eq_sup_if_extend_if_rel_dep_mono_wrt_predI)
  (use assms in \<open>force split: if_split_asm\<close>)+

lemma crel_dep_mono_wrt_eq_sup_if_extend_if_crel_dep_mono_wrt_predI:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  and "\<not>(in_dom R x)"
  shows "((x' : (=) x \<squnion> A) \<rightarrow>\<^sub>c (if x' = x then (=) y else B x')) (extend x y R)"
  using assms by (intro crel_dep_mono_wrt_predI
    rel_dep_mono_wrt_eq_sup_if_extend_if_rel_dep_mono_wrt_predI)
  fastforce+

lemma crel_dep_mono_wrt_eq_sup_extend_if_rel_dep_mono_wrt_predI:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  and "\<not>(in_dom R x)"
  and "B x y"
  shows "((x' : (=) x \<squnion> A) \<rightarrow>\<^sub>c B x') (extend x y R)"
  using assms
  by (intro crel_dep_mono_wrt_predI rel_dep_mono_wrt_eq_sup_extend_if_rel_dep_mono_wrt_predI)
  fastforce+

context
  fixes \<R> :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" and A :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" and D
  defines [simp]: "D \<equiv> in_codom_on \<R> A"
begin

lemma rel_dep_mono_wrt_pred_glue_if_right_unique_if_rel_dep_mono_wrt_pred:
  assumes funs: "\<And>R. \<R> R \<Longrightarrow> ((x : A R) \<rightarrow> B x) R"
  and runique: "right_unique_on D (glue \<R>)"
  shows "((x : D) \<rightarrow> B x) (glue \<R>)"
proof (intro rel_dep_mono_wrt_predI dep_mono_wrt_predI left_total_onI)
  fix x assume "D x"
  with funs obtain R where hyps: "\<R> R" "A R x" "((x : A R) \<rightarrow> B x) R" by auto
  then have "B x (R`x)" by (auto elim: rel_dep_mono_wrt_pred_relE)
  moreover have "(glue \<R>)`x = R`x"
  proof (intro glue_eval_eqI)
    show "\<R> R" by (fact hyps)
    then have "A R \<le> D" by fastforce
    with runique show "right_unique_on (A R) (glue \<R>)" using antimono_right_unique_on by blast
  qed (use hyps in \<open>auto elim: rel_dep_mono_wrt_pred_relE\<close>)
  ultimately show "B x (glue \<R>`x)" by simp
qed (use assms in \<open>fastforce+\<close>)

lemma crel_dep_mono_wrt_pred_glue_if_right_unique_if_crel_dep_mono_wrt_pred:
  assumes "\<And>R. \<R> R \<Longrightarrow> ((x : A R) \<rightarrow>\<^sub>c B x) R"
  and "right_unique_on D (glue \<R>)"
  shows "((x : D) \<rightarrow>\<^sub>c B x) (glue \<R>)"
  using assms
  by (intro crel_dep_mono_wrt_predI rel_dep_mono_wrt_pred_glue_if_right_unique_if_rel_dep_mono_wrt_pred)
  fastforce+

end

lemma right_unique_on_sup_if_rel_agree_on_sup_if_right_unique_on:
  assumes "right_unique_on P R" "right_unique_on P R'"
  and "rel_agree_on (P \<sqinter> in_dom R \<sqinter> in_dom R') ((=) R \<squnion> (=) R')"
  shows "right_unique_on P (R \<squnion> R')"
proof (intro right_unique_onI)
  fix x y y' assume "P x" "(R \<squnion> R') x y" "(R \<squnion> R') x y'"
  then obtain R1 R2 where rels: "R1 x y" "R2 x y'" and ors: "R1 = R \<or> R1 = R'" "R2 = R \<or> R2 = R'" by auto
  then consider (neq) "R1 \<noteq> R2" | "R1 = R2" by auto
  then show "y = y'"
  proof cases
    case neq
    with rels ors obtain z z' where "R x z" "R' x z'" and yors: "y = z \<or> y = z'" "y' = z \<or> y' = z'"
      by auto
    with \<open>P x\<close> have "R' x z" by (intro rel_agree_onD[where ?R=R and ?R'=R' and
      ?P="P \<sqinter> in_dom R \<sqinter> in_dom R'" and ?\<R>="(=) R \<squnion> (=) R'"] assms)
      auto
    with \<open>P x\<close> \<open>R' x z'\<close> assms have "z = z'" by (blast dest: right_unique_onD)
    with yors show "y = y'" by auto
  qed (use assms \<open>P x\<close> rels ors in \<open>auto dest: right_unique_onD\<close>)
qed

lemma crel_dep_mono_wrt_pred_sup_if_eval_eq_if_crel_dep_mono_wrt_pred:
  assumes dep_funs: "((x : A) \<rightarrow>\<^sub>c B x) R" "((x : A') \<rightarrow>\<^sub>c B x) R'"
  and "\<And>x. A x \<Longrightarrow> A' x \<Longrightarrow> R`x = R'`x"
  shows "((x : A \<squnion> A') \<rightarrow>\<^sub>c B x) (R \<squnion> R')"
proof -
  let ?A = "\<lambda>S. if S = R then A else A'"
  from dep_funs have "A = A'" if "R = R'" using that by (simp only: flip:
    in_dom_eq_if_crel_dep_mono_wrt_pred[OF dep_funs(1)] in_dom_eq_if_crel_dep_mono_wrt_pred[OF dep_funs(2)])
  then have [uhint]: "in_codom_on ((=) R \<squnion> (=) R') ?A = A \<squnion> A'"
    by (intro ext iffI) (fastforce split: if_splits)+
  show ?thesis by (urule (rr) crel_dep_mono_wrt_pred_glue_if_right_unique_if_crel_dep_mono_wrt_pred
    right_unique_on_sup_if_rel_agree_on_sup_if_right_unique_on
    rel_agree_on_if_eval_eq_if_rel_dep_mono_wrt_pred)
    (use assms in \<open>auto 7 0 intro: rel_dep_mono_wrt_pred_contravariant_dom dest: right_unique_onD\<close>)
qed

end
