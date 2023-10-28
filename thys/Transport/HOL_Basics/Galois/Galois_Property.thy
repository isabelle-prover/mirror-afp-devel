\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Galois Property\<close>
theory Galois_Property
  imports
    Half_Galois_Property
begin

context galois_prop
begin

definition "galois_prop \<equiv> ((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) \<sqinter> ((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>))"

notation galois_prop.galois_prop (infix "\<unlhd>" 50)

lemma galois_propI [intro]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  unfolding galois_prop_def using assms by auto

lemma galois_propI':
  assumes "\<And>x y. in_dom (\<le>\<^bsub>L\<^esub>) x \<Longrightarrow> in_codom (\<le>\<^bsub>R\<^esub>) y \<Longrightarrow> x \<le>\<^bsub>L\<^esub> r y \<longleftrightarrow> l x \<le>\<^bsub>R\<^esub> y"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by blast

lemma galois_propE [elim]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  obtains "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r" "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  using assms unfolding galois_prop_def by auto

interpretation g : galois_prop S T f g for S T f g.

lemma galois_prop_eq_half_galois_prop_left_rel_inf_half_galois_prop_right:
  "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) = ((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) \<sqinter> ((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>))"
  by (intro ext) auto

lemma galois_prop_left_rel_right_iff_left_right_rel:
  assumes "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "in_dom (\<le>\<^bsub>L\<^esub>) x" "in_codom (\<le>\<^bsub>R\<^esub>) y"
  shows "x \<le>\<^bsub>L\<^esub> r y \<longleftrightarrow> l x \<le>\<^bsub>R\<^esub> y"
  using assms by blast

lemma rel_inv_galois_prop_eq_galois_prop_rel_inv [simp]:
  "((\<le>\<^bsub>R\<^esub>) \<unlhd> (\<le>\<^bsub>L\<^esub>))\<inverse> = ((\<ge>\<^bsub>L\<^esub>) \<unlhd> (\<ge>\<^bsub>R\<^esub>))"
  by (intro ext) blast

corollary galois_prop_rel_inv_iff_galois_prop [iff]:
  "((\<ge>\<^bsub>L\<^esub>) \<unlhd> (\<ge>\<^bsub>R\<^esub>)) f g \<longleftrightarrow> ((\<le>\<^bsub>R\<^esub>) \<unlhd> (\<le>\<^bsub>L\<^esub>)) g f"
  by auto

end

context galois
begin

lemma galois_prop_left_right_if_transitive_if_deflationary_on_if_inflationary_on_if_mono_wrt_rel:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l" and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "inflationary_on (in_dom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  and "deflationary_on (in_codom (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>) \<epsilon>"
  and "transitive (\<le>\<^bsub>L\<^esub>)" "transitive (\<le>\<^bsub>R\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms
  by (intro galois_propI
    half_galois_prop_left_left_right_if_transitive_if_deflationary_on_if_mono_wrt_rel
    half_galois_prop_right_left_right_if_transitive_if_inflationary_on_if_mono_wrt_rel)

end


end