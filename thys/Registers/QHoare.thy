section \<open>Very simple Quantum Hoare logic\<close>

theory QHoare
  imports Quantum_Extra
begin

no_notation Order.top ("\<top>\<index>")

locale qhoare =
  fixes memory_type :: "'mem::finite itself"
begin

definition "apply U R = R U" for R :: \<open>'a update \<Rightarrow> 'mem update\<close>
definition "ifthen R x = R (butterket x x)" for R :: \<open>'a update \<Rightarrow> 'mem update\<close>
definition "program S = fold (o\<^sub>C\<^sub>L) S id_cblinfun" for S :: \<open>'mem update list\<close>


definition hoare :: \<open>'mem ell2 ccsubspace \<Rightarrow> ('mem ell2 \<Rightarrow>\<^sub>C\<^sub>L 'mem ell2) list \<Rightarrow> 'mem ell2 ccsubspace \<Rightarrow> bool\<close> where
  "hoare C p D \<longleftrightarrow> (\<forall>\<psi>\<in>space_as_set C. program p *\<^sub>V \<psi> \<in> space_as_set D)" for C p D

definition EQ :: "('a update \<Rightarrow> 'mem update) \<Rightarrow> 'a ell2 \<Rightarrow> 'mem ell2 ccsubspace" (infix "=\<^sub>q" 75) where
  "EQ R \<psi> = R (selfbutter \<psi>) *\<^sub>S \<top>"

lemma program_skip[simp]: "program [] = id_cblinfun"
  by (simp add: qhoare.program_def)

lemma program_seq: "program (p1@p2) = program p2 o\<^sub>C\<^sub>L program p1"
  apply (induction p2 rule:rev_induct)
   apply (simp_all add: program_def)
  by (meson cblinfun_assoc_left(1))

lemma hoare_seq[trans]: "hoare C p1 D \<Longrightarrow> hoare D p2 E \<Longrightarrow> hoare C (p1@p2) E"
  by (auto simp: program_seq hoare_def)

lemma hoare_weaken_left[trans]: \<open>A \<le> B \<Longrightarrow> hoare B p C \<Longrightarrow> hoare A p C\<close>
  unfolding hoare_def
  by (meson in_mono less_eq_ccsubspace.rep_eq) 

lemma hoare_weaken_right[trans]: \<open>hoare A p B \<Longrightarrow> B \<le> C \<Longrightarrow> hoare A p C\<close>
  unfolding hoare_def 
  by (meson in_mono less_eq_ccsubspace.rep_eq) 

lemma hoare_skip: "C \<le> D \<Longrightarrow> hoare C [] D"
  by (auto simp: program_def hoare_def in_mono less_eq_ccsubspace.rep_eq)

lemma hoare_apply: 
  assumes "R U *\<^sub>S pre \<le> post"
  shows "hoare pre [apply U R] post"
  using assms 
  apply (auto simp: hoare_def program_def apply_def)
  by (metis (no_types, lifting) cblinfun_image.rep_eq closure_subset imageI less_eq_ccsubspace.rep_eq subsetD)

lemma hoare_ifthen: 
  fixes R :: \<open>'a update \<Rightarrow> 'mem update\<close>
  assumes "R (selfbutter (ket x)) *\<^sub>S pre \<le> post"
  shows "hoare pre [ifthen R x] post"
  using assms 
  apply (auto simp: hoare_def program_def ifthen_def butterfly_def)
  by (metis (no_types, lifting) cblinfun_image.rep_eq closure_subset imageI less_eq_ccsubspace.rep_eq subsetD)

end

end
