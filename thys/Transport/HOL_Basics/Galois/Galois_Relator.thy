\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Relator For Galois Connections\<close>
theory Galois_Relator
  imports
    Galois_Relator_Base
    Galois_Property
begin

context galois_prop
begin

interpretation flip_inv : galois_rel "(\<ge>\<^bsub>R\<^esub>)" "(\<ge>\<^bsub>L\<^esub>)" l .

lemma left_Galois_if_Galois_right_if_half_galois_prop_right:
  assumes "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  and "x \<lessapprox>\<^bsub>R\<^esub> y"
  shows "x \<^bsub>L\<^esub>\<lessapprox> y"
  using assms by (intro left_GaloisI) auto

lemma Galois_right_if_left_Galois_if_half_galois_prop_left:
  assumes "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "x \<^bsub>L\<^esub>\<lessapprox> y"
  shows "x \<lessapprox>\<^bsub>R\<^esub> y"
  using assms by blast

corollary Galois_right_iff_left_Galois_if_galois_prop [iff]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "x \<lessapprox>\<^bsub>R\<^esub> y \<longleftrightarrow> x \<^bsub>L\<^esub>\<lessapprox> y"
  using assms
    left_Galois_if_Galois_right_if_half_galois_prop_right
    Galois_right_if_left_Galois_if_half_galois_prop_left
  by blast

lemma rel_inv_Galois_eq_flip_Galois_rel_inv_if_galois_prop [simp]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "(\<greaterapprox>\<^bsub>L\<^esub>) = (\<^bsub>R\<^esub>\<greaterapprox>)"
  using assms by blast

corollary flip_Galois_rel_inv_iff_Galois_if_galois_prop [iff]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "y \<^bsub>R\<^esub>\<greaterapprox> x \<longleftrightarrow> x \<^bsub>L\<^esub>\<lessapprox> y"
  using assms by blast

corollary inv_flip_Galois_rel_inv_eq_Galois_if_galois_prop [simp]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "(\<lessapprox>\<^bsub>R\<^esub>) = (\<^bsub>L\<^esub>\<lessapprox>)" \<comment>\<open>Note that @{term "(\<lessapprox>\<^bsub>R\<^esub>) = (galois_rel.Galois (\<ge>\<^bsub>R\<^esub>) (\<ge>\<^bsub>L\<^esub>) l)\<inverse>"}\<close>
  using assms by (subst rel_inv_eq_iff_eq[symmetric]) simp

end

context galois
begin

interpretation flip_inv : galois "(\<ge>\<^bsub>R\<^esub>)" "(\<ge>\<^bsub>L\<^esub>)" r l .

context
begin

interpretation flip : galois R L r l .

lemma left_Galois_left_if_left_relI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  and "x \<le>\<^bsub>L\<^esub> x'"
  shows "x \<^bsub>L\<^esub>\<lessapprox> l x'"
  using assms
  by (intro left_Galois_if_Galois_right_if_half_galois_prop_right) auto

corollary left_Galois_left_if_reflexive_on_if_half_galois_prop_rightI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  and "reflexive_on P (\<le>\<^bsub>L\<^esub>)"
  and "P x"
  shows "x \<^bsub>L\<^esub>\<lessapprox> l x"
  using assms by (intro left_Galois_left_if_left_relI) auto

lemma left_Galois_left_if_in_codom_if_inflationary_onI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "inflationary_on P (\<le>\<^bsub>L\<^esub>) \<eta>"
  and "in_codom (\<le>\<^bsub>L\<^esub>) x"
  and "P x"
  shows "x \<^bsub>L\<^esub>\<lessapprox> l x"
  using assms by (intro left_GaloisI) (auto elim!: in_codomE)

lemma left_Galois_left_if_in_codom_if_inflationary_on_in_codomI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "inflationary_on (in_codom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  and "in_codom (\<le>\<^bsub>L\<^esub>) x"
  shows "x \<^bsub>L\<^esub>\<lessapprox> l x"
  using assms by (auto intro!: left_Galois_left_if_in_codom_if_inflationary_onI)

lemma left_Galois_left_if_left_rel_if_inflationary_on_in_fieldI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "inflationary_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  and "x \<le>\<^bsub>L\<^esub> x"
  shows "x \<^bsub>L\<^esub>\<lessapprox> l x"
  using assms by (auto intro!: left_Galois_left_if_in_codom_if_inflationary_onI)

lemma right_left_Galois_if_right_relI:
  assumes "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "y \<le>\<^bsub>R\<^esub> y'"
  shows "r y \<^bsub>L\<^esub>\<lessapprox> y'"
  using assms by (intro left_GaloisI) auto

corollary right_left_Galois_if_reflexive_onI:
  assumes "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "reflexive_on P (\<le>\<^bsub>R\<^esub>)"
  and "P y"
  shows "r y \<^bsub>L\<^esub>\<lessapprox> y"
  using assms by (intro right_left_Galois_if_right_relI) auto

lemma left_Galois_if_right_rel_if_left_GaloisI:
  assumes "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "transitive (\<le>\<^bsub>L\<^esub>)"
  and "x \<^bsub>L\<^esub>\<lessapprox> y"
  and "y \<le>\<^bsub>R\<^esub> z"
  shows "x \<^bsub>L\<^esub>\<lessapprox> z"
  using assms by (intro left_GaloisI) auto

lemma left_Galois_if_left_Galois_if_left_relI:
  assumes "transitive (\<le>\<^bsub>L\<^esub>)"
  and "x \<le>\<^bsub>L\<^esub> y"
  and "y \<^bsub>L\<^esub>\<lessapprox> z"
  shows "x \<^bsub>L\<^esub>\<lessapprox> z"
  using assms by (intro left_GaloisI) auto

lemma left_rel_if_right_Galois_if_left_GaloisI:
  assumes "((\<le>\<^bsub>R\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>L\<^esub>)) r l"
  and "transitive (\<le>\<^bsub>L\<^esub>)"
  and "x \<^bsub>L\<^esub>\<lessapprox> y"
  and "y \<^bsub>R\<^esub>\<lessapprox> z"
  shows "x \<le>\<^bsub>L\<^esub> z"
  using assms by auto

lemma Dep_Fun_Rel_left_Galois_right_Galois_if_mono_wrt_rel [intro]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  shows "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>R\<^esub>\<lessapprox>)) l r"
  using assms by auto

lemma left_ge_Galois_eq_left_Galois_if_in_codom_eq_in_dom_if_symmetric:
  assumes "symmetric (\<le>\<^bsub>L\<^esub>)"
  and "in_codom (\<le>\<^bsub>R\<^esub>) = in_dom (\<le>\<^bsub>R\<^esub>)"
  shows "(\<^bsub>L\<^esub>\<greaterapprox>) = (\<^bsub>L\<^esub>\<lessapprox>)" \<comment>\<open>Note that @{term "(\<^bsub>L\<^esub>\<greaterapprox>) = galois_rel.Galois (\<ge>\<^bsub>L\<^esub>) (\<ge>\<^bsub>R\<^esub>) r"}\<close>
  using assms by (intro ext iffI)
  (auto elim!: galois_rel.left_GaloisE intro!: galois_rel.left_GaloisI)

end

interpretation flip : galois R L r l .

lemma ge_Galois_right_eq_left_Galois_if_symmetric_if_in_codom_eq_in_dom_if_galois_prop:
  assumes "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  and "in_codom (\<le>\<^bsub>L\<^esub>) = in_dom (\<le>\<^bsub>L\<^esub>)"
  and "symmetric (\<le>\<^bsub>R\<^esub>)"
  shows "(\<greaterapprox>\<^bsub>R\<^esub>) = (\<^bsub>L\<^esub>\<lessapprox>)" \<comment>\<open>Note that @{term "(\<greaterapprox>\<^bsub>R\<^esub>) = (galois_rel.Galois (\<le>\<^bsub>R\<^esub>) (\<le>\<^bsub>L\<^esub>) l)\<inverse>"}\<close>
  using assms
  by (simp only: inv_flip_Galois_rel_inv_eq_Galois_if_galois_prop
    flip: flip.left_ge_Galois_eq_left_Galois_if_in_codom_eq_in_dom_if_symmetric)

interpretation gp : galois_prop "(\<^bsub>L\<^esub>\<lessapprox>)" "(\<^bsub>R\<^esub>\<lessapprox>)" l l .

lemma half_galois_prop_left_left_Galois_right_Galois_if_half_galois_prop_leftI [intro]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "((\<^bsub>L\<^esub>\<lessapprox>) \<^sub>h\<unlhd> (\<^bsub>R\<^esub>\<lessapprox>)) l l"
  using assms by fast

lemma half_galois_prop_right_left_Galois_right_Galois_if_half_galois_prop_rightI [intro]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "((\<^bsub>L\<^esub>\<lessapprox>) \<unlhd>\<^sub>h (\<^bsub>R\<^esub>\<lessapprox>)) l l"
  using assms by fast

corollary galois_prop_left_Galois_right_Galois_if_galois_prop [intro]:
  assumes "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "((\<^bsub>L\<^esub>\<lessapprox>) \<unlhd> (\<^bsub>R\<^esub>\<lessapprox>)) l l"
  using assms by blast

end


end