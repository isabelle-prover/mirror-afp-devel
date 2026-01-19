\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Transport using Conditional Relation\<close>
theory Transport_Rel_If
  imports
    Transport_Base
begin

paragraph \<open>Summary\<close>
text \<open>Setup for Transport using conditional relations.\<close>

context fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

lemma reflexive_on_rel_if_if_reflexive_onI [intro]:
  assumes "B \<Longrightarrow> reflexive_on P R"
  shows "reflexive_on P (B \<longrightarrow>\<^sub>r R)"
  using assms by (intro reflexive_onI) blast

lemma transitive_on_rel_if_if_transitive_onI [intro]:
  assumes "B \<Longrightarrow> transitive_on P R"
  shows "transitive_on P (B \<longrightarrow>\<^sub>r R)"
  using assms by (intro transitive_onI) (blast dest: transitive_onD)

lemma preorder_on_rel_if_if_preorder_onI [intro]:
  assumes "B \<Longrightarrow> preorder_on P R"
  shows "preorder_on P (B \<longrightarrow>\<^sub>r R)"
  using assms by (intro preorder_onI) auto

lemma symmetric_on_rel_if_if_symmetric_onI [intro]:
  assumes "B \<Longrightarrow> symmetric_on P R"
  shows "symmetric_on P (B \<longrightarrow>\<^sub>r R)"
  using assms by (intro symmetric_onI) (blast dest: symmetric_onD)

lemma partial_equivalence_rel_on_rel_if_if_partial_equivalence_rel_onI [intro]:
  assumes "B \<Longrightarrow> partial_equivalence_rel_on P R"
  shows "partial_equivalence_rel_on P (B \<longrightarrow>\<^sub>r R)"
  using assms by (intro partial_equivalence_rel_onI)
  auto

lemma dep_mono_wrt_rel_if_rel_if_if_imp_if_dep_mono_wrt_rel:
  assumes "B \<Longrightarrow> B' \<Longrightarrow> ((x y \<Colon> R) \<Rightarrow> S x y) f"
  and "B' \<Longrightarrow> B"
  shows "((x y \<Colon> B \<longrightarrow>\<^sub>r R) \<Rightarrow> (B' \<longrightarrow>\<^sub>r S x y)) f"
  using assms by fastforce

end


locale transport_rel_if =
  fixes L :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and R :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  and l :: "'a \<Rightarrow> 'b"
  and r :: "'b \<Rightarrow> 'a"
  and B B' :: bool
begin

sublocale t : transport L R l r .
sublocale transport "B \<longrightarrow>\<^sub>r (\<le>\<^bsub>L\<^esub>)" "B' \<longrightarrow>\<^sub>r (\<le>\<^bsub>R\<^esub>)" l r .

lemma half_galois_prop_left_if_imp_if_half_galois_prop_left:
  assumes "B \<Longrightarrow> B' \<Longrightarrow> ((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "B' \<Longrightarrow> B"
  shows "((B \<longrightarrow>\<^sub>r (\<le>\<^bsub>L\<^esub>)) \<^sub>h\<unlhd> (B' \<longrightarrow>\<^sub>r (\<le>\<^bsub>R\<^esub>))) l r"
  using assms by (intro half_galois_prop_leftI rel_if_if_impI) fast

lemma half_galois_prop_right_if_imp_if_half_galois_prop_right:
  assumes "B \<Longrightarrow> B' \<Longrightarrow> ((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  and "B \<Longrightarrow> B'"
  shows "((B \<longrightarrow>\<^sub>r (\<le>\<^bsub>L\<^esub>)) \<unlhd>\<^sub>h (B' \<longrightarrow>\<^sub>r (\<le>\<^bsub>R\<^esub>))) l r"
  using assms by (intro half_galois_prop_rightI) fast

lemma galois_prop_if_iff_if_galois_prop:
  assumes "B \<Longrightarrow> B' \<Longrightarrow> ((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "B \<longleftrightarrow> B'"
  shows "((B \<longrightarrow>\<^sub>r (\<le>\<^bsub>L\<^esub>)) \<unlhd> (B' \<longrightarrow>\<^sub>r (\<le>\<^bsub>R\<^esub>))) l r"
  using assms by (intro galois_propI
    half_galois_prop_left_if_imp_if_half_galois_prop_left
    half_galois_prop_right_if_imp_if_half_galois_prop_right)
  auto

lemma galois_connection_if_iff_if_galois_connection:
  assumes "B \<Longrightarrow> B' \<Longrightarrow> ((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  and "B \<longleftrightarrow> B'"
  shows "((B \<longrightarrow>\<^sub>r (\<le>\<^bsub>L\<^esub>)) \<stileturn> (B' \<longrightarrow>\<^sub>r (\<le>\<^bsub>R\<^esub>))) l r"
  by (urule (rr) galois_connectionI galois_prop_if_iff_if_galois_prop
    dep_mono_wrt_rel_if_rel_if_if_imp_if_dep_mono_wrt_rel)
  (use assms in auto)

lemma galois_equivalence_if_iff_if_galois_equivalence:
  assumes "B \<Longrightarrow> B' \<Longrightarrow> ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  and "B \<longleftrightarrow> B'"
  shows "((B \<longrightarrow>\<^sub>r (\<le>\<^bsub>L\<^esub>)) \<equiv>\<^sub>G (B' \<longrightarrow>\<^sub>r (\<le>\<^bsub>R\<^esub>))) l r"
  using assms by (intro galois_equivalenceI
    galois_connection_if_iff_if_galois_connection
    transport_rel_if.galois_prop_if_iff_if_galois_prop)
  (auto elim: galois.galois_connectionE)

lemma preorder_equivalence_if_iff_if_preorder_equivalence:
  assumes "B \<Longrightarrow> B' \<Longrightarrow> ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  and "B \<longleftrightarrow> B'"
  shows "((B \<longrightarrow>\<^sub>r (\<le>\<^bsub>L\<^esub>)) \<equiv>\<^bsub>pre\<^esub> (B' \<longrightarrow>\<^sub>r (\<le>\<^bsub>R\<^esub>))) l r"
  using assms by (intro preorder_equivalence_if_galois_equivalenceI
    galois_equivalence_if_iff_if_galois_equivalence
    preorder_on_rel_if_if_preorder_onI)
  blast+

lemma partial_equivalence_rel_equivalence_if_iff_if_partial_equivalence_rel_equivalence:
  assumes "B \<Longrightarrow> B' \<Longrightarrow> ((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  and "B \<longleftrightarrow> B'"
  shows "((B \<longrightarrow>\<^sub>r (\<le>\<^bsub>L\<^esub>)) \<equiv>\<^bsub>PER\<^esub> (B' \<longrightarrow>\<^sub>r (\<le>\<^bsub>R\<^esub>))) l r"
  using assms by (intro
    partial_equivalence_rel_equivalence_if_galois_equivalenceI
    galois_equivalence_if_iff_if_galois_equivalence)
  fastforce+

end

end