\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Order Equivalence\<close>
theory Transport_Compositions_Agree_Order_Equivalence
  imports
    Transport_Compositions_Agree_Monotone
begin

context transport_comp_agree
begin

subsubsection \<open>Unit\<close>
paragraph \<open>Inflationary\<close>

lemma inflationary_on_unitI:
  assumes mono_l1: "([P] \<Rrightarrow>\<^sub>m P') l1"
  and mono_r1: "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and inflationary_unit1: "inflationary_on P (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and trans_L1: "transitive (\<le>\<^bsub>L1\<^esub>)"
  and inflationary_unit2: "inflationary_on P' (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and L2_le_R1: "\<And>x. P x \<Longrightarrow> l1 x \<le>\<^bsub>L2\<^esub> r2 (l x) \<Longrightarrow> l1 x \<le>\<^bsub>R1\<^esub> r2 (l x)"
  shows "inflationary_on P (\<le>\<^bsub>L\<^esub>) \<eta>"
proof (rule inflationary_onI)
  fix x assume "P x"
  with mono_l1 have "P' (l1 x)" by blast
  with inflationary_unit2 have "l1 x \<le>\<^bsub>L2\<^esub> r2 (l x)" by auto
  with L2_le_R1 \<open>P x\<close> have "l1 x \<le>\<^bsub>R1\<^esub> r2 (l x)" by blast
  with mono_r1 have "\<eta>\<^sub>1 x \<le>\<^bsub>L1\<^esub> \<eta> x" by auto
  moreover from inflationary_unit1 \<open>P x\<close> have "x \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x" by auto
  ultimately show "x \<le>\<^bsub>L\<^esub> \<eta> x" using trans_L1 by blast
qed

corollary inflationary_on_in_field_unitI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) l1"
  and "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "inflationary_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and "transitive (\<le>\<^bsub>L1\<^esub>)"
  and "inflationary_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and "\<And>x. in_field (\<le>\<^bsub>L1\<^esub>) x \<Longrightarrow> l1 x \<le>\<^bsub>L2\<^esub> r2 (l x) \<Longrightarrow> l1 x \<le>\<^bsub>R1\<^esub> r2 (l x)"
  shows "inflationary_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  using assms by (intro inflationary_on_unitI dep_mono_wrt_predI) auto


paragraph \<open>Deflationary\<close>

context
begin

interpretation inv :
  transport_comp_agree "(\<ge>\<^bsub>L1\<^esub>)" "(\<ge>\<^bsub>R1\<^esub>)" l1 r1 "(\<ge>\<^bsub>L2\<^esub>)" "(\<ge>\<^bsub>R2\<^esub>)" l2 r2
  rewrites "\<And>R S. (R\<inverse> \<Rrightarrow>\<^sub>m S\<inverse>) \<equiv> (R \<Rrightarrow>\<^sub>m S)"
  and "\<And>R. inflationary_on P R\<inverse> \<equiv> deflationary_on P R"
  and "\<And>R. transitive R\<inverse> \<equiv> transitive R"
  and "\<And>R. in_field R\<inverse> \<equiv> in_field R"
  by simp_all

lemma deflationary_on_in_field_unitI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) l1"
  and "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "deflationary_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and "transitive (\<le>\<^bsub>L1\<^esub>)"
  and "deflationary_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and "\<And>x. in_field (\<le>\<^bsub>L1\<^esub>) x \<Longrightarrow> r2 (l x) \<le>\<^bsub>L2\<^esub> l1 x \<Longrightarrow> r2 (l x) \<le>\<^bsub>R1\<^esub> l1 x"
  shows "deflationary_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  using assms by (intro inv.inflationary_on_in_field_unitI[simplified rel_inv_iff_rel])
  auto

end


text \<open>Relational Equivalence\<close>

corollary rel_equivalence_on_in_field_unitI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L2\<^esub>)) l1"
  and "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "rel_equivalence_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>) \<eta>\<^sub>1"
  and "transitive (\<le>\<^bsub>L1\<^esub>)"
  and "rel_equivalence_on (in_field (\<le>\<^bsub>L2\<^esub>)) (\<le>\<^bsub>L2\<^esub>) \<eta>\<^sub>2"
  and "\<And>x. in_field (\<le>\<^bsub>L1\<^esub>) x \<Longrightarrow> l1 x \<le>\<^bsub>L2\<^esub> r2 (l x) \<Longrightarrow> l1 x \<le>\<^bsub>R1\<^esub> r2 (l x)"
  and "\<And>x. in_field (\<le>\<^bsub>L1\<^esub>) x \<Longrightarrow> r2 (l x) \<le>\<^bsub>L2\<^esub> l1 x \<Longrightarrow> r2 (l x) \<le>\<^bsub>R1\<^esub> l1 x"
  shows "rel_equivalence_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  using assms by (intro rel_equivalence_onI
    inflationary_on_in_field_unitI deflationary_on_in_field_unitI)
  auto


subsubsection \<open>Counit\<close>

text \<open>Corresponding lemmas for the counit can be obtained by flipping the
interpretation of the locale.\<close>


subsubsection \<open>Order Equivalence\<close>

interpretation flip : transport_comp_agree R2 L2 r2 l2 R1 L1 r1 l1
  rewrites "flip.g1.unit \<equiv> \<epsilon>\<^sub>2" and "flip.g2.unit \<equiv> \<epsilon>\<^sub>1" and "flip.unit \<equiv> \<epsilon>"
  by (simp_all only: g1.flip_unit_eq_counit g2.flip_unit_eq_counit flip_unit_eq_counit)

lemma order_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "transitive (\<le>\<^bsub>L1\<^esub>)"
  and "((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "transitive (\<le>\<^bsub>R2\<^esub>)"
  and "\<And>x y. x \<le>\<^bsub>L1\<^esub> y \<Longrightarrow> l1 x \<le>\<^bsub>R1\<^esub> l1 y \<Longrightarrow> l1 x \<le>\<^bsub>L2\<^esub> l1 y"
  and "\<And>x y. x \<le>\<^bsub>R2\<^esub> y \<Longrightarrow> r2 x \<le>\<^bsub>L2\<^esub> r2 y \<Longrightarrow> r2 x \<le>\<^bsub>R1\<^esub> r2 y"
  and "\<And>x. in_field (\<le>\<^bsub>L1\<^esub>) x \<Longrightarrow> l1 x \<le>\<^bsub>L2\<^esub> r2 (l x) \<Longrightarrow> l1 x \<le>\<^bsub>R1\<^esub> r2 (l x)"
  and "\<And>x. in_field (\<le>\<^bsub>L1\<^esub>) x \<Longrightarrow> r2 (l x) \<le>\<^bsub>L2\<^esub> l1 x \<Longrightarrow> r2 (l x) \<le>\<^bsub>R1\<^esub> l1 x"
  and "\<And>x. in_field (\<le>\<^bsub>R2\<^esub>) x \<Longrightarrow> r2 x \<le>\<^bsub>R1\<^esub> l1 (r x) \<Longrightarrow> r2 x \<le>\<^bsub>L2\<^esub> l1 (r x)"
  and "\<And>x. in_field (\<le>\<^bsub>R2\<^esub>) x \<Longrightarrow> l1 (r x) \<le>\<^bsub>R1\<^esub> r2 x \<Longrightarrow> l1 (r x) \<le>\<^bsub>L2\<^esub> r2 x"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro order_equivalenceI rel_equivalence_on_in_field_unitI
    flip.rel_equivalence_on_in_field_unitI
    mono_wrt_rel_leftI flip.mono_wrt_rel_leftI dep_mono_wrt_relI)
  (auto elim!: g1.order_equivalenceE g2.order_equivalenceE)

end

context transport_comp_same
begin

lemma order_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "transitive (\<le>\<^bsub>L1\<^esub>)"
  and "((\<le>\<^bsub>R1\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "transitive (\<le>\<^bsub>R2\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (rule order_equivalenceI) auto

end


end