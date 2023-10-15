\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Reflexive Relator\<close>
theory Reflexive_Relator
  imports
    Galois_Equivalences
    Galois_Relator
begin

definition "Refl_Rel R x y \<equiv> R x x \<and> R y y \<and> R x y"

bundle Refl_Rel_syntax begin notation Refl_Rel ("(_\<^sup>\<oplus>)" [1000]) end
bundle no_Refl_Rel_syntax begin no_notation Refl_Rel ("(_\<^sup>\<oplus>)" [1000]) end
unbundle Refl_Rel_syntax

lemma Refl_RelI [intro]:
  assumes "R x x"
  and "R y y"
  and "R x y"
  shows "R\<^sup>\<oplus> x y"
  using assms unfolding Refl_Rel_def by blast

lemma Refl_Rel_selfI [intro]:
  assumes "R x x"
  shows "R\<^sup>\<oplus> x x"
  using assms by blast

lemma Refl_RelE [elim]:
  assumes "R\<^sup>\<oplus> x y"
  obtains "R x x" "R y y" "R x y"
  using assms unfolding Refl_Rel_def by blast

lemma Refl_Rel_reflexive_on_in_field [iff]:
  "reflexive_on (in_field R\<^sup>\<oplus>) R\<^sup>\<oplus>"
  by (rule reflexive_onI) auto

lemma Refl_Rel_le_self [iff]: "R\<^sup>\<oplus> \<le> R" by blast

lemma Refl_Rel_eq_self_if_reflexive_on [simp]:
  assumes "reflexive_on (in_field R) R"
  shows "R\<^sup>\<oplus> = R"
  using assms by blast

lemma reflexive_on_in_field_if_Refl_Rel_eq_self:
  assumes "R\<^sup>\<oplus> = R"
  shows "reflexive_on (in_field R) R"
  by (fact Refl_Rel_reflexive_on_in_field[of R, simplified assms])

corollary Refl_Rel_eq_self_iff_reflexive_on:
  "R\<^sup>\<oplus> = R \<longleftrightarrow> reflexive_on (in_field R) R"
  using Refl_Rel_eq_self_if_reflexive_on reflexive_on_in_field_if_Refl_Rel_eq_self
  by blast

lemma Refl_Rel_Refl_Rel_eq [simp]: "(R\<^sup>\<oplus>)\<^sup>\<oplus> = R\<^sup>\<oplus>"
  by (intro ext) auto

lemma rel_inv_Refl_Rel_eq [simp]: "(R\<^sup>\<oplus>)\<inverse> = (R\<inverse>)\<^sup>\<oplus>"
  by (intro ext iffI Refl_RelI rel_invI) auto

lemma Refl_Rel_transitive_onI [intro]:
  assumes "transitive_on (P :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> _)"
  shows "transitive_on P R\<^sup>\<oplus>"
  using assms by (intro transitive_onI) (blast dest: transitive_onD)

corollary Refl_Rel_transitiveI [intro]:
  assumes "transitive R"
  shows "transitive R\<^sup>\<oplus>"
  using assms by blast

corollary Refl_Rel_preorder_onI:
  assumes "transitive_on P R"
  and "P \<le> in_field R\<^sup>\<oplus>"
  shows "preorder_on P R\<^sup>\<oplus>"
  using assms by (intro preorder_onI
    reflexive_on_if_le_pred_if_reflexive_on[where ?P="in_field R\<^sup>\<oplus>" and ?P'=P])
  auto

corollary Refl_Rel_preorder_on_in_fieldI [intro]:
  assumes "transitive R"
  shows "preorder_on (in_field R\<^sup>\<oplus>) R\<^sup>\<oplus>"
  using assms by (intro Refl_Rel_preorder_onI) auto

lemma Refl_Rel_symmetric_onI [intro]:
  assumes "symmetric_on (P :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> _)"
  shows "symmetric_on P R\<^sup>\<oplus>"
  using assms by (intro symmetric_onI) (auto dest: symmetric_onD)

lemma Refl_Rel_symmetricI [intro]:
  assumes "symmetric R"
  shows "symmetric R\<^sup>\<oplus>"
  using assms by (fold symmetric_on_in_field_iff_symmetric)
  (blast intro: symmetric_on_if_le_pred_if_symmetric_on)

lemma Refl_Rel_partial_equivalence_rel_onI [intro]:
  assumes "partial_equivalence_rel_on (P :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> _)"
  shows "partial_equivalence_rel_on P R\<^sup>\<oplus>"
  using assms by (intro partial_equivalence_rel_onI Refl_Rel_transitive_onI
    Refl_Rel_symmetric_onI) auto

lemma Refl_Rel_partial_equivalence_relI [intro]:
  assumes "partial_equivalence_rel R"
  shows "partial_equivalence_rel R\<^sup>\<oplus>"
  using assms
  by (intro partial_equivalence_relI Refl_Rel_transitiveI Refl_Rel_symmetricI) auto

lemma Refl_Rel_app_leftI:
  assumes "R (f x) y"
  and "in_field S\<^sup>\<oplus> x"
  and "in_field R\<^sup>\<oplus> y"
  and "(S \<Rrightarrow>\<^sub>m R) f"
  shows "R\<^sup>\<oplus> (f x) y"
proof (rule Refl_RelI)
  from \<open>in_field R\<^sup>\<oplus> y\<close> show "R y y" by blast
  from \<open>in_field S\<^sup>\<oplus> x\<close> have "S x x" by blast
  with \<open>(S \<Rrightarrow>\<^sub>m R) f\<close> show "R (f x) (f x)" by blast
qed fact

corollary Refl_Rel_app_rightI:
  assumes "R x (f y)"
  and "in_field S\<^sup>\<oplus> y"
  and "in_field R\<^sup>\<oplus> x"
  and "(S \<Rrightarrow>\<^sub>m R) f"
  shows "R\<^sup>\<oplus> x (f y)"
proof -
  from assms have "(R\<inverse>)\<^sup>\<oplus> (f y) x" by (intro Refl_Rel_app_leftI[where ?S="S\<inverse>"])
    (auto simp flip: rel_inv_Refl_Rel_eq)
  then show ?thesis by blast
qed

lemma mono_wrt_rel_Refl_Rel_Refl_Rel_if_mono_wrt_rel [intro]:
  assumes "(R \<Rrightarrow>\<^sub>m S) f"
  shows "(R\<^sup>\<oplus> \<Rrightarrow>\<^sub>m S\<^sup>\<oplus>) f"
  using assms by (intro dep_mono_wrt_relI) auto

context galois
begin

interpretation gR : galois "(\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus>" "(\<le>\<^bsub>R\<^esub>)\<^sup>\<oplus>" l r .

lemma Galois_Refl_RelI:
  assumes "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "in_field (\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus> x"
  and "in_field (\<le>\<^bsub>R\<^esub>)\<^sup>\<oplus> y"
  and "in_codom (\<le>\<^bsub>R\<^esub>) y \<Longrightarrow> x \<^bsub>L\<^esub>\<lessapprox> y"
  shows "(galois_rel.Galois ((\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus>) ((\<le>\<^bsub>R\<^esub>)\<^sup>\<oplus>) r) x y"
  using assms by (intro gR.left_GaloisI in_codomI Refl_Rel_app_rightI[where ?f=r])
  auto

lemma half_galois_prop_left_Refl_Rel_left_rightI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "((\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus> \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)\<^sup>\<oplus>) l r"
  using assms by (intro gR.half_galois_prop_leftI Refl_RelI)
  (auto elim!: in_codomE gR.left_GaloisE Refl_RelE)

interpretation flip_inv : galois "(\<ge>\<^bsub>R\<^esub>)" "(\<ge>\<^bsub>L\<^esub>)" r l
  rewrites "((\<ge>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<ge>\<^bsub>L\<^esub>)) \<equiv> ((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>))"
  and "\<And>R. (R\<inverse>)\<^sup>\<oplus> \<equiv> (R\<^sup>\<oplus>)\<inverse>"
  and "\<And>R S f g. (R\<inverse> \<^sub>h\<unlhd> S\<inverse>) f g \<equiv> (S \<unlhd>\<^sub>h R) g f"
  by (simp_all add: galois_prop.half_galois_prop_left_rel_inv_iff_half_galois_prop_right)

lemma half_galois_prop_right_Refl_Rel_right_leftI:
  assumes "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  shows "((\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus> \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)\<^sup>\<oplus>) l r"
  using assms by (fact flip_inv.half_galois_prop_left_Refl_Rel_left_rightI)

corollary galois_prop_Refl_Rel_left_rightI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "((\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus> \<unlhd> (\<le>\<^bsub>R\<^esub>)\<^sup>\<oplus>) l r"
  using assms
  by (intro gR.galois_propI half_galois_prop_left_Refl_Rel_left_rightI
    half_galois_prop_right_Refl_Rel_right_leftI) auto

lemma galois_connection_Refl_Rel_left_rightI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  shows "((\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus> \<stileturn> (\<le>\<^bsub>R\<^esub>)\<^sup>\<oplus>) l r"
  using assms
  by (intro gR.galois_connectionI galois_prop_Refl_Rel_left_rightI) auto

lemma galois_equivalence_Refl_RelI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  shows "((\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus> \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)\<^sup>\<oplus>) l r"
proof -
  interpret flip : galois R L r l .
  show ?thesis using assms by (intro gR.galois_equivalenceI
    galois_connection_Refl_Rel_left_rightI flip.galois_prop_Refl_Rel_left_rightI)
  auto
qed

end

context order_functors
begin

lemma inflationary_on_in_field_Refl_Rel_left:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "inflationary_on (in_dom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  shows "inflationary_on (in_field (\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus>) (\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus> \<eta>"
  using assms
  by (intro inflationary_onI Refl_RelI) (auto elim!: in_fieldE Refl_RelE)

lemma inflationary_on_in_field_Refl_Rel_left':
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "inflationary_on (in_codom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  shows "inflationary_on (in_field (\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus>) (\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus> \<eta>"
  using assms
  by (intro inflationary_onI Refl_RelI) (auto elim!: in_fieldE Refl_RelE)

interpretation inv : galois "(\<ge>\<^bsub>L\<^esub>)" "(\<ge>\<^bsub>R\<^esub>)" l r
  rewrites "((\<ge>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<ge>\<^bsub>R\<^esub>)) \<equiv> ((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>))"
  and "((\<ge>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<ge>\<^bsub>L\<^esub>)) \<equiv> ((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>))"
  and "\<And>R. (R\<inverse>)\<^sup>\<oplus> \<equiv> (R\<^sup>\<oplus>)\<inverse>"
  and "\<And>R. in_dom R\<inverse> \<equiv> in_codom R"
  and "\<And>R. in_codom R\<inverse> \<equiv> in_dom R"
  and "\<And>R. in_field R\<inverse> \<equiv> in_field R"
  and "\<And>P R. inflationary_on P R\<inverse> \<equiv> deflationary_on P R"
  by simp_all

lemma deflationary_on_in_field_Refl_Rel_leftI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "deflationary_on (in_dom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  shows "deflationary_on (in_field (\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus>) (\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus> \<eta>"
  using assms by (fact inv.inflationary_on_in_field_Refl_Rel_left')

lemma deflationary_on_in_field_Refl_RelI_left':
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "deflationary_on (in_codom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  shows "deflationary_on (in_field (\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus>) (\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus> \<eta>"
  using assms by (fact inv.inflationary_on_in_field_Refl_Rel_left)

lemma rel_equivalence_on_in_field_Refl_Rel_leftI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "rel_equivalence_on (in_dom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  shows "rel_equivalence_on (in_field (\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus>) (\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus> \<eta>"
  using assms by (intro rel_equivalence_onI
    inflationary_on_in_field_Refl_Rel_left
    deflationary_on_in_field_Refl_Rel_leftI)
  auto

lemma rel_equivalence_on_in_field_Refl_Rel_leftI':
  assumes "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  and "((\<le>\<^bsub>R\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L\<^esub>)) r"
  and "rel_equivalence_on (in_codom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  shows "rel_equivalence_on (in_field (\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus>) (\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus> \<eta>"
  using assms by (intro rel_equivalence_onI
    inflationary_on_in_field_Refl_Rel_left'
    deflationary_on_in_field_Refl_RelI_left')
  auto

interpretation oR : order_functors "(\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus>" "(\<le>\<^bsub>R\<^esub>)\<^sup>\<oplus>" l r .

lemma order_equivalence_Refl_RelI:
  assumes "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  shows "((\<le>\<^bsub>L\<^esub>)\<^sup>\<oplus> \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)\<^sup>\<oplus>) l r"
proof -
  interpret flip : galois R L r l
    rewrites "flip.unit \<equiv> \<epsilon>"
    by (simp only: flip_unit_eq_counit)
  show ?thesis using assms by (intro oR.order_equivalenceI
    mono_wrt_rel_Refl_Rel_Refl_Rel_if_mono_wrt_rel
    rel_equivalence_on_in_field_Refl_Rel_leftI
    flip.rel_equivalence_on_in_field_Refl_Rel_leftI)
    (auto intro: rel_equivalence_on_if_le_pred_if_rel_equivalence_on
      in_field_if_in_dom)
qed

end


end