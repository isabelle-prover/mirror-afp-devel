section \<open>Derived facts about classical registers\<close>

theory Classical_Extra
  imports Laws_Classical Misc
begin

lemma register_from_getter_setter_of_getter_setter[simp]: \<open>register_from_getter_setter (getter F) (setter F) = F\<close> if \<open>register F\<close>
  by (metis getter_of_register_from_getter_setter register_def setter_of_register_from_getter_setter that)

lemma valid_getter_setter_getter_setter[simp]: \<open>valid_getter_setter (getter F) (setter F)\<close> if \<open>register F\<close>
  by (metis getter_of_register_from_getter_setter register_def setter_of_register_from_getter_setter that)

lemma register_register_from_getter_setter[simp]: \<open>register (register_from_getter_setter g s)\<close> if \<open>valid_getter_setter g s\<close>
  using register_def that by blast

definition \<open>total_fun f = (\<forall>x. f x \<noteq> None)\<close>

lemma register_total:
  assumes \<open>register F\<close>
  assumes \<open>total_fun a\<close>
  shows \<open>total_fun (F a)\<close>
  using assms 
  by (auto simp: register_def total_fun_def register_from_getter_setter_def option.case_eq_if)

lemma register_apply:
  assumes \<open>register F\<close>
  shows \<open>Some o register_apply F a = F (Some o a)\<close>
proof -
  have \<open>total_fun (F (Some o a))\<close>
    using assms apply (rule register_total)
    by (auto simp: total_fun_def)
  then show ?thesis
    by (auto simp: register_apply_def dom_def total_fun_def)
qed

lemma register_empty:
  assumes \<open>preregister F\<close>
  shows \<open>F Map.empty = Map.empty\<close>
  using assms unfolding preregister_def by auto

lemma compatible_setter:
  fixes F :: \<open>('a,'c) preregister\<close> and G :: \<open>('b,'c) preregister\<close>
  assumes [simp]: \<open>register F\<close> \<open>register G\<close>
  shows \<open>compatible F G \<longleftrightarrow> (\<forall>a b. setter F a o setter G b = setter G b o setter F a)\<close>
proof (intro allI iffI)
  fix a b
  assume \<open>compatible F G\<close>
  then show \<open>setter F a o setter G b = setter G b o setter F a\<close>
    apply (rule_tac compatible_setter)
    unfolding compatible_def by auto
next
  assume commute[rule_format, THEN fun_cong, unfolded o_def]: \<open>\<forall>a b. setter F a \<circ> setter G b = setter G b \<circ> setter F a\<close>
  have \<open>valid_getter_setter (getter F) (setter F)\<close>
    by auto
  then have \<open>F a \<circ>\<^sub>m G b = G b \<circ>\<^sub>m F a\<close> for a b
    apply (subst (2) register_from_getter_setter_of_getter_setter[symmetric, of F], simp)
    apply (subst (1) register_from_getter_setter_of_getter_setter[symmetric, of F], simp)
    apply (subst (2) register_from_getter_setter_of_getter_setter[symmetric, of G], simp)
    apply (subst (1) register_from_getter_setter_of_getter_setter[symmetric, of G], simp)
    unfolding register_from_getter_setter_def valid_getter_setter_def
    apply (auto intro!: ext simp: option.case_eq_if map_comp_def) (* Sledgehammer: *)
          apply ((metis commute option.distinct option.simps)+)[4]
      apply (smt (verit, ccfv_threshold) assms(2) commute valid_getter_setter_def valid_getter_setter_getter_setter)
     apply (smt (verit, ccfv_threshold) assms(2) commute valid_getter_setter_def valid_getter_setter_getter_setter)
    by (smt (verit, del_insts) assms(2) commute option.inject valid_getter_setter_def valid_getter_setter_getter_setter)
  then show \<open>compatible F G\<close>
    unfolding compatible_def by auto
qed

lemma register_from_getter_setter_compatibleI[intro]:
  assumes [simp]: \<open>valid_getter_setter g s\<close> \<open>valid_getter_setter g' s'\<close>
  assumes \<open>\<And>x y m. s x (s' y m) = s' y (s x m)\<close>
  shows \<open>compatible (register_from_getter_setter g s) (register_from_getter_setter g' s')\<close>
  apply (subst compatible_setter)
  using assms by auto

lemma separating_update1:
  \<open>separating TYPE(_) {update1 x y | x y. True}\<close>
  by (smt (verit) mem_Collect_eq separating_def update1_extensionality)

definition "permutation_register (p::'b\<Rightarrow>'a) = register_from_getter_setter p (\<lambda>a _. inv p a)"

lemma permutation_register_register[simp]: 
  fixes p :: "'b \<Rightarrow> 'a"
  assumes [simp]: "bij p"
  shows "register (permutation_register p)"
  apply (auto intro!: register_register_from_getter_setter simp: permutation_register_def valid_getter_setter_def bij_inv_eq_iff)
  by (meson assms bij_inv_eq_iff)

lemma getter_permutation_register: \<open>bij p \<Longrightarrow> getter (permutation_register p) = p\<close>
  by (smt (verit, ccfv_threshold) bij_inv_eq_iff getter_of_register_from_getter_setter permutation_register_def valid_getter_setter_def)

lemma setter_permutation_register: \<open>bij p \<Longrightarrow> setter (permutation_register p) a m = inv p a\<close>
  by (metis bij_inv_eq_iff getter_permutation_register permutation_register_register valid_getter_setter_def valid_getter_setter_getter_setter)

definition empty_var :: \<open>'a::{CARD_1} update \<Rightarrow> 'b update\<close> where
  "empty_var = register_from_getter_setter (\<lambda>_. undefined) (\<lambda>_ m. m)"

lemma valid_empty_var[simp]: \<open>valid_getter_setter (\<lambda>_. (undefined::_::CARD_1)) (\<lambda>_ m. m)\<close>
  by (simp add: valid_getter_setter_def)

lemma register_empty_var[simp]: \<open>register empty_var\<close>
  using empty_var_def register_def valid_empty_var by blast

lemma getter_empty_var[simp]: \<open>getter empty_var m = undefined\<close>
  by (rule everything_the_same)

lemma setter_empty_var[simp]: \<open>setter empty_var a m = m\<close>
  by (simp add: empty_var_def setter_of_register_from_getter_setter)

lemma empty_var_compatible[simp]: \<open>compatible empty_var X\<close> if [simp]: \<open>register X\<close>
  apply (subst compatible_setter) by auto

lemma empty_var_compatible'[simp]: \<open>register X \<Longrightarrow> compatible X empty_var\<close>
  using compatible_sym empty_var_compatible by blast

paragraph \<open>Example\<close>

record memory = 
  x :: "int*int"
  y :: nat

definition "X = register_from_getter_setter x (\<lambda>a b. b\<lparr>x:=a\<rparr>)"
definition "Y = register_from_getter_setter y (\<lambda>a b. b\<lparr>y:=a\<rparr>)"

lemma validX[simp]: \<open>valid_getter_setter x (\<lambda>a b. b\<lparr>x:=a\<rparr>)\<close>
  unfolding valid_getter_setter_def by auto

lemma registerX[simp]: \<open>register X\<close>
  using X_def register_def validX by blast

lemma validY[simp]: \<open>valid_getter_setter y (\<lambda>a b. b\<lparr>y:=a\<rparr>)\<close>
  unfolding valid_getter_setter_def by auto

lemma registerY[simp]: \<open>register Y\<close>
  using Y_def register_def validY by blast

lemma compatibleXY[simp]: \<open>compatible X Y\<close>
  unfolding X_def Y_def by auto

end
