\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Galois Connections\<close>
theory Galois_Connections
  imports
    Galois_Property
begin

context galois
begin

definition "galois_connection \<equiv>
  ((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l \<and> ((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r \<and> ((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"

notation galois.galois_connection (infix "\<stileturn>" 50)

lemma galois_connectionI [intro]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l" and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  unfolding galois_connection_def using assms by blast

lemma galois_connectionE [elim]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  obtains "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l" "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r" "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms unfolding galois_connection_def by blast

context
begin

interpretation g : galois S T f g for S T f g.

lemma rel_inv_galois_connection_eq_galois_connection_rel_inv [simp]:
  "((\<le>\<^bsub>R\<^esub>) \<stileturn> (\<le>\<^bsub>L\<^esub>))\<inverse> = ((\<ge>\<^bsub>L\<^esub>) \<stileturn> (\<ge>\<^bsub>R\<^esub>))"
  by (intro ext) blast

corollary galois_connection_rel_inv_iff_galois_connection [iff]:
  "((\<ge>\<^bsub>L\<^esub>) \<stileturn> (\<ge>\<^bsub>R\<^esub>)) l r \<longleftrightarrow> ((\<le>\<^bsub>R\<^esub>) \<stileturn> (\<le>\<^bsub>L\<^esub>)) r l"
  by (simp flip: rel_inv_galois_connection_eq_galois_connection_rel_inv)

lemma rel_unit_if_left_rel_if_galois_connection:
  assumes "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  and "x \<le>\<^bsub>L\<^esub> x'"
  shows "x \<le>\<^bsub>L\<^esub> \<eta> x'"
  using assms
  by (blast intro: rel_unit_if_left_rel_if_half_galois_prop_right_if_mono_wrt_rel)

end

lemma counit_rel_if_right_rel_if_galois_connection:
  assumes "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  and "y \<le>\<^bsub>R\<^esub> y'"
  shows "\<epsilon> y \<le>\<^bsub>R\<^esub> y'"
  using assms
  by (blast intro: counit_rel_if_right_rel_if_half_galois_prop_left_if_mono_wrt_rel)

lemma rel_unit_if_reflexive_on_if_galois_connection:
  assumes "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  and "reflexive_on P (\<le>\<^bsub>L\<^esub>)"
  and "P x"
  shows "x \<le>\<^bsub>L\<^esub> \<eta> x"
  using assms
  by (blast intro: rel_unit_if_reflexive_on_if_half_galois_prop_right_if_mono_wrt_rel)

lemma counit_rel_if_reflexive_on_if_galois_connection:
  assumes "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  and "reflexive_on P (\<le>\<^bsub>R\<^esub>)"
  and "P y"
  shows "\<epsilon> y \<le>\<^bsub>R\<^esub> y"
  using assms
  by (blast intro: counit_rel_if_reflexive_on_if_half_galois_prop_left_if_mono_wrt_rel)

lemma inflationary_on_unit_if_reflexive_on_if_galois_connection:
  fixes P :: "'a \<Rightarrow> bool"
  assumes "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  and "reflexive_on P (\<le>\<^bsub>L\<^esub>)"
  shows "inflationary_on P (\<le>\<^bsub>L\<^esub>) \<eta>"
  using assms
  by (blast intro: inflationary_on_unit_if_reflexive_on_if_half_galois_prop_rightI)

lemma deflationary_on_counit_if_reflexive_on_if_galois_connection:
  fixes P :: "'b \<Rightarrow> bool"
  assumes "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  and "reflexive_on P (\<le>\<^bsub>R\<^esub>)"
  shows "deflationary_on P (\<le>\<^bsub>R\<^esub>) \<epsilon>"
  using assms
  by (blast intro: deflationary_on_counit_if_reflexive_on_if_half_galois_prop_leftI)

end


end