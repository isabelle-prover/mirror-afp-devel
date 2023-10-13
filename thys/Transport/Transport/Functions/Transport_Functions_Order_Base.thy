\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Basic Order Properties\<close>
theory Transport_Functions_Order_Base
  imports
    Transport_Functions_Base
begin

paragraph \<open>Dependent Function Relator\<close>

context hom_Dep_Fun_Rel_orders
begin

lemma reflexive_on_in_domI:
  assumes refl_L: "reflexive_on (in_codom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  and R_le_R_if_L: "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>R x2 x2\<^esub>) \<le> (\<le>\<^bsub>R x1 x2\<^esub>)"
  and pequiv_R: "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> partial_equivalence_rel (\<le>\<^bsub>R x1 x2\<^esub>)"
  shows "reflexive_on (in_dom DFR) DFR"
proof (intro reflexive_onI Dep_Fun_Rel_relI)
  fix f x1 x2
  assume "in_dom DFR f"
  then obtain g where "DFR f g" by auto
  moreover assume "x1 \<le>\<^bsub>L\<^esub> x2"
  moreover with refl_L have "x2 \<le>\<^bsub>L\<^esub> x2" by blast
  ultimately have "f x1 \<le>\<^bsub>R x1 x2\<^esub> g x2" "f x2 \<le>\<^bsub>R x1 x2\<^esub> g x2"
    using R_le_R_if_L by auto
  moreover with pequiv_R \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close>  have "g x2 \<le>\<^bsub>R x1 x2\<^esub> f x2"
    by (blast dest: symmetricD)
  ultimately show "f x1 \<le>\<^bsub>R x1 x2\<^esub> f x2" using pequiv_R \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close> by blast
qed

lemma reflexive_on_in_codomI:
  assumes refl_L: "reflexive_on (in_dom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  and R_le_R_if_L: "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>R x1 x1\<^esub>) \<le> (\<le>\<^bsub>R x1 x2\<^esub>)"
  and pequiv_R: "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> partial_equivalence_rel (\<le>\<^bsub>R x1 x2\<^esub>)"
  shows "reflexive_on (in_codom DFR) DFR"
proof (intro reflexive_onI Dep_Fun_Rel_relI)
  fix f x1 x2
  assume "in_codom DFR f"
  then obtain g where "DFR g f" by auto
  moreover assume "x1 \<le>\<^bsub>L\<^esub> x2"
  moreover with refl_L have "x1 \<le>\<^bsub>L\<^esub> x1" by blast
  ultimately have "g x1 \<le>\<^bsub>R x1 x2\<^esub> f x2" "g x1 \<le>\<^bsub>R x1 x2\<^esub> f x1"
    using R_le_R_if_L by auto
  moreover with pequiv_R \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close>  have "f x1 \<le>\<^bsub>R x1 x2\<^esub> g x1"
    by (blast dest: symmetricD)
  ultimately show "f x1 \<le>\<^bsub>R x1 x2\<^esub> f x2" using pequiv_R \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close> by blast
qed

corollary reflexive_on_in_fieldI:
  assumes "reflexive_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>R x2 x2\<^esub>) \<le> (\<le>\<^bsub>R x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>R x1 x1\<^esub>) \<le> (\<le>\<^bsub>R x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> partial_equivalence_rel (\<le>\<^bsub>R x1 x2\<^esub>)"
  shows "reflexive_on (in_field DFR) DFR"
proof -
  from assms have "reflexive_on (in_dom DFR) DFR"
    by (intro reflexive_on_in_domI)
    (auto intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_codom)
  moreover from assms have "reflexive_on (in_codom DFR) DFR"
    by (intro reflexive_on_in_codomI)
    (auto intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_dom)
  ultimately show ?thesis by (auto iff: in_field_iff_in_dom_or_in_codom)
qed

lemma transitiveI:
  assumes refl_L: "reflexive_on (in_dom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  and R_le_R_if_L: "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>R x1 x1\<^esub>) \<le> (\<le>\<^bsub>R x1 x2\<^esub>)"
  and trans: "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>R x1 x2\<^esub>)"
  shows "transitive DFR"
proof (intro transitiveI Dep_Fun_Rel_relI)
  fix f1 f2 f3 x1 x2 assume "x1 \<le>\<^bsub>L\<^esub> x2"
  with refl_L have "x1 \<le>\<^bsub>L\<^esub> x1" by blast
  moreover assume "DFR f1 f2"
  ultimately have "f1 x1 \<le>\<^bsub>R x1 x1\<^esub> f2 x1" by blast
  with R_le_R_if_L have "f1 x1 \<le>\<^bsub>R x1 x2\<^esub> f2 x1" using \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close> by blast
  assume "DFR f2 f3"
  with \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close> have "f2 x1 \<le>\<^bsub>R x1 x2\<^esub> f3 x2" by blast
  with \<open>f1 x1 \<le>\<^bsub>R x1 x2\<^esub> f2 x1\<close> show "f1 x1 \<le>\<^bsub>R x1 x2\<^esub>  f3 x2"
    using trans \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close> by blast
qed

lemma transitiveI':
  assumes refl_L: "reflexive_on (in_codom (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  and R_le_R_if_L: "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>R x2 x2\<^esub>) \<le> (\<le>\<^bsub>R x1 x2\<^esub>)"
  and trans: "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>R x1 x2\<^esub>)"
  shows "transitive DFR"
proof (intro Binary_Relations_Transitive.transitiveI Dep_Fun_Rel_relI)
  fix f1 f2 f3 x1 x2 assume "DFR f1 f2" "x1 \<le>\<^bsub>L\<^esub> x2"
  then have "f1 x1 \<le>\<^bsub>R x1 x2\<^esub> f2 x2" by blast
  from \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close> refl_L have "x2 \<le>\<^bsub>L\<^esub> x2" by blast
  moreover assume "DFR f2 f3"
  ultimately have "f2 x2 \<le>\<^bsub>R x2 x2\<^esub> f3 x2" by blast
  with R_le_R_if_L have "f2 x2 \<le>\<^bsub>R x1 x2\<^esub> f3 x2" using \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close> by blast
  with \<open>f1 x1 \<le>\<^bsub>R x1 x2\<^esub> f2 x2\<close> show "f1 x1 \<le>\<^bsub>R x1 x2\<^esub> f3 x2"
    using trans \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close> by blast
qed

lemma preorder_on_in_fieldI:
  assumes "reflexive_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>R x2 x2\<^esub>) \<le> (\<le>\<^bsub>R x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>R x1 x1\<^esub>) \<le> (\<le>\<^bsub>R x1 x2\<^esub>)"
  and pequiv_R: "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> partial_equivalence_rel (\<le>\<^bsub>R x1 x2\<^esub>)"
  shows "preorder_on (in_field DFR) DFR"
  using assms by (intro preorder_onI reflexive_on_in_fieldI)
  (auto intro!: transitiveI dest: pequiv_R elim!: partial_equivalence_relE)

lemma symmetricI:
  assumes sym_L: "symmetric (\<le>\<^bsub>L\<^esub>)"
  and R_le_R_if_L: "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>R x1 x2\<^esub>) \<le> (\<le>\<^bsub>R x2 x1\<^esub>)"
  and sym_R: "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> symmetric (\<le>\<^bsub>R x1 x2\<^esub>)"
  shows "symmetric DFR"
proof (intro symmetricI Dep_Fun_Rel_relI)
  fix f g x y assume "x \<le>\<^bsub>L\<^esub> y"
  with sym_L have "y \<le>\<^bsub>L\<^esub> x" by (rule symmetricD)
  moreover assume "DFR f g"
  ultimately have "f y \<le>\<^bsub>R y x\<^esub> g x" by blast
  with sym_R \<open>y \<le>\<^bsub>L\<^esub> x\<close> have "g x \<le>\<^bsub>R y x\<^esub> f y" by (blast dest: symmetricD)
  with R_le_R_if_L \<open>y \<le>\<^bsub>L\<^esub> x\<close> show "g x \<le>\<^bsub>R x y\<^esub> f y" by blast
qed

corollary partial_equivalence_relI:
  assumes "reflexive_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  and sym_L: "symmetric (\<le>\<^bsub>L\<^esub>)"
  and mono_R: "([x1 x2 \<Colon> (\<le>\<^bsub>L\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L\<^esub>) | x1 \<le>\<^bsub>L\<^esub> x3] \<Rrightarrow> (\<le>)) R"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L\<^esub> x2 \<Longrightarrow> partial_equivalence_rel (\<le>\<^bsub>R x1 x2\<^esub>)"
  shows "partial_equivalence_rel DFR"
proof -
  have "(\<le>\<^bsub>R x1 x2\<^esub>) \<le> (\<le>\<^bsub>R x2 x1\<^esub>)" if "x1 \<le>\<^bsub>L\<^esub> x2" for x1 x2
  proof -
    from sym_L \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close> have "x2 \<le>\<^bsub>L\<^esub> x1" by (rule symmetricD)
    with mono_R \<open>x1 \<le>\<^bsub>L\<^esub> x2\<close> show ?thesis by blast
  qed
  with assms show ?thesis
    by (intro partial_equivalence_relI transitiveI symmetricI)
    (auto elim: partial_equivalence_relE[OF assms(4)])
qed

end

context transport_Dep_Fun_Rel
begin

lemmas reflexive_on_in_field_leftI = dfro1.reflexive_on_in_fieldI
  [folded left_rel_eq_Dep_Fun_Rel]
lemmas transitive_leftI = dfro1.transitiveI[folded left_rel_eq_Dep_Fun_Rel]
lemmas transitive_leftI' = dfro1.transitiveI'[folded left_rel_eq_Dep_Fun_Rel]
lemmas preorder_on_in_field_leftI = dfro1.preorder_on_in_fieldI
  [folded left_rel_eq_Dep_Fun_Rel]
lemmas symmetric_leftI = dfro1.symmetricI[folded left_rel_eq_Dep_Fun_Rel]
lemmas partial_equivalence_rel_leftI = dfro1.partial_equivalence_relI
  [folded left_rel_eq_Dep_Fun_Rel]


subparagraph \<open>Introduction Rules for Assumptions\<close>

lemma transitive_left2_if_transitive_left2_if_left_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and L2_eq: "(\<le>\<^bsub>L2 x1 x2\<^esub>) = (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> transitive (\<le>\<^bsub>L2 x (r1 x')\<^esub>)"
  and "x1 \<le>\<^bsub>L1\<^esub> x2"
  shows "transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  by (subst L2_eq) (auto intro!: assms t1.left_Galois_left_if_left_relI)

lemma symmetric_left2_if_symmetric_left2_if_left_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and L2_eq: "(\<le>\<^bsub>L2 x1 x2\<^esub>) = (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> symmetric (\<le>\<^bsub>L2 x (r1 x')\<^esub>)"
  and "x1 \<le>\<^bsub>L1\<^esub> x2"
  shows "symmetric (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  by (subst L2_eq) (auto intro!: assms t1.left_Galois_left_if_left_relI)

lemma partial_equivalence_rel_left2_if_partial_equivalence_rel_left2_if_left_GaloisI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L1\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and L2_eq: "(\<le>\<^bsub>L2 x1 x2\<^esub>) = (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> partial_equivalence_rel (\<le>\<^bsub>L2 x (r1 x')\<^esub>)"
  and "x1 \<le>\<^bsub>L1\<^esub> x2"
  shows "partial_equivalence_rel (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  by (subst L2_eq) (auto intro!: assms t1.left_Galois_left_if_left_relI)

context
  assumes galois_prop: "((\<le>\<^bsub>L1\<^esub>) \<unlhd> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
begin

interpretation flip_inv :
  transport_Dep_Fun_Rel "(\<ge>\<^bsub>R1\<^esub>)" "(\<ge>\<^bsub>L1\<^esub>)" r1 l1 "flip2 R2" "flip2 L2" r2 l2
  rewrites "flip_inv.t1.unit \<equiv> \<epsilon>\<^sub>1"
  and "\<And>R x y. (flip2 R x y) \<equiv> (R y x)\<inverse>"
  and "\<And>R S. R\<inverse> = S\<inverse> \<equiv> R = S"
  and "\<And>R S. (R\<inverse> \<Rrightarrow>\<^sub>m S\<inverse>) \<equiv> (R \<Rrightarrow>\<^sub>m S)"
  and "\<And>x x'. x' \<^bsub>R1\<^esub>\<greaterapprox> x \<equiv> x \<^bsub>L1\<^esub>\<lessapprox> x'"
  and "((\<ge>\<^bsub>R1\<^esub>) \<unlhd>\<^sub>h (\<ge>\<^bsub>L1\<^esub>)) r1 l1 \<equiv> True"
  and "\<And>R. transitive R\<inverse> \<equiv> transitive R"
  and "\<And>R. symmetric R\<inverse> \<equiv> symmetric R"
  and "\<And>R. partial_equivalence_rel R\<inverse> \<equiv> partial_equivalence_rel R"
  and "\<And>P. (True \<Longrightarrow> P) \<equiv> Trueprop P"
  and "\<And>P Q. (True \<Longrightarrow> PROP P \<Longrightarrow> PROP Q) \<equiv> (PROP P \<Longrightarrow> True \<Longrightarrow> PROP Q)"
  using galois_prop
  by (auto intro!: Eq_TrueI simp add: t1.flip_unit_eq_counit
    galois_prop.half_galois_prop_right_rel_inv_iff_half_galois_prop_left
    simp del: rel_inv_iff_rel)

lemma transitive_right2_if_transitive_right2_if_left_GaloisI:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "(\<le>\<^bsub>R2 x1 x2\<^esub>) = (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1) x2\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> transitive (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)"
  and "x1 \<le>\<^bsub>R1\<^esub> x2"
  shows "transitive (\<le>\<^bsub>R2 x1 x2\<^esub>)"
  using galois_prop assms
  by (intro flip_inv.transitive_left2_if_transitive_left2_if_left_GaloisI
    [simplified rel_inv_iff_rel, of x1])
  auto

lemma symmetric_right2_if_symmetric_right2_if_left_GaloisI:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "(\<le>\<^bsub>R2 x1 x2\<^esub>) = (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1) x2\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> symmetric (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)"
  and "x1 \<le>\<^bsub>R1\<^esub> x2"
  shows "symmetric (\<le>\<^bsub>R2 x1 x2\<^esub>)"
  using galois_prop assms
  by (intro flip_inv.symmetric_left2_if_symmetric_left2_if_left_GaloisI
    [simplified rel_inv_iff_rel, of x1])
  auto

lemma partial_equivalence_rel_right2_if_partial_equivalence_rel_right2_if_left_GaloisI:
  assumes "((\<le>\<^bsub>R1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>L1\<^esub>)) r1"
  and "(\<le>\<^bsub>R2 x1 x2\<^esub>) = (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1) x2\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> partial_equivalence_rel (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)"
  and "x1 \<le>\<^bsub>R1\<^esub> x2"
  shows "partial_equivalence_rel (\<le>\<^bsub>R2 x1 x2\<^esub>)"
  using galois_prop assms
  by (intro flip_inv.partial_equivalence_rel_left2_if_partial_equivalence_rel_left2_if_left_GaloisI
    [simplified rel_inv_iff_rel, of x1])
  auto

end

lemma transitive_left2_if_preorder_equivalenceI:
  assumes pre_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "x1 \<le>\<^bsub>L1\<^esub> x2"
  shows "transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
proof -
  from \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> pre_equiv1 have "x2 \<equiv>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2"
    by (blast elim: t1.preorder_equivalence_order_equivalenceE
      intro: bi_related_if_rel_equivalence_on)
  with assms have "(\<le>\<^bsub>L2 x1 x2\<^esub>) = (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>)"
    by (intro left2_eq_if_bi_related_if_monoI) blast+
  with assms show ?thesis
    by (intro transitive_left2_if_transitive_left2_if_left_GaloisI[of x1]) blast+
qed

lemma symmetric_left2_if_partial_equivalence_rel_equivalenceI:
  assumes PER_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "x1 \<le>\<^bsub>L1\<^esub> x2"
  shows "symmetric (\<le>\<^bsub>L2 x1 x2\<^esub>)"
proof -
  from \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> PER_equiv1 have "x2 \<equiv>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2"
    by (blast elim: t1.preorder_equivalence_order_equivalenceE
      intro: bi_related_if_rel_equivalence_on)
  with assms have "(\<le>\<^bsub>L2 x1 x2\<^esub>) = (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>)"
    by (intro left2_eq_if_bi_related_if_monoI) blast+
  with assms show ?thesis
    by (intro symmetric_left2_if_symmetric_left2_if_left_GaloisI[of x1]) blast+
qed

lemma partial_equivalence_rel_left2_if_partial_equivalence_rel_equivalenceI:
  assumes PER_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "x1 \<le>\<^bsub>L1\<^esub> x2"
  shows "partial_equivalence_rel (\<le>\<^bsub>L2 x1 x2\<^esub>)"
proof -
  from \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> PER_equiv1 have "x2 \<equiv>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x2"
    by (blast elim: t1.preorder_equivalence_order_equivalenceE
      intro: bi_related_if_rel_equivalence_on)
  with assms have "(\<le>\<^bsub>L2 x1 x2\<^esub>) = (\<le>\<^bsub>L2 x1 (\<eta>\<^sub>1 x2)\<^esub>)"
    by (intro left2_eq_if_bi_related_if_monoI) blast+
  with assms show ?thesis
    by (intro partial_equivalence_rel_left2_if_partial_equivalence_rel_left2_if_left_GaloisI[of x1])
    blast+
qed

interpretation flip : transport_Dep_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2
  rewrites "flip.t1.counit \<equiv> \<eta>\<^sub>1" and "flip.t1.unit \<equiv> \<epsilon>\<^sub>1"
  by (simp_all only: t1.flip_counit_eq_unit t1.flip_unit_eq_counit)

lemma transitive_right2_if_preorder_equivalenceI:
  assumes pre_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "([x1' x2' \<Colon> (\<ge>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x1' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "x1' \<le>\<^bsub>R1\<^esub> x2'"
  shows "transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
proof -
  from \<open>x1' \<le>\<^bsub>R1\<^esub> x2'\<close> pre_equiv1 have "x1' \<equiv>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x1'"
    by (blast elim: t1.preorder_equivalence_order_equivalenceE
      intro: bi_related_if_rel_equivalence_on)
  with assms have "(\<le>\<^bsub>R2 x1' x2'\<^esub>) = (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>)"
    by (intro flip.left2_eq_if_bi_related_if_monoI) blast+
  with assms show ?thesis
    by (intro transitive_right2_if_transitive_right2_if_left_GaloisI[of x1']) blast+
qed

lemma symmetric_right2_if_partial_equivalence_rel_equivalenceI:
  assumes PER_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "([x1' x2' \<Colon> (\<ge>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x1' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "x1' \<le>\<^bsub>R1\<^esub> x2'"
  shows "symmetric (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
proof -
  from \<open>x1' \<le>\<^bsub>R1\<^esub> x2'\<close> PER_equiv1 have "x1' \<equiv>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x1'"
    by (blast elim: t1.preorder_equivalence_order_equivalenceE
      intro: bi_related_if_rel_equivalence_on)
  with assms have "(\<le>\<^bsub>R2 x1' x2'\<^esub>) = (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>)"
    by (intro flip.left2_eq_if_bi_related_if_monoI) blast+
  with assms show ?thesis
    by (intro symmetric_right2_if_symmetric_right2_if_left_GaloisI[of x1']) blast+
qed

lemma partial_equivalence_rel_right2_if_partial_equivalence_rel_equivalenceI:
  assumes PER_equiv1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "([x1' x2' \<Colon> (\<ge>\<^bsub>R1\<^esub>)] \<Rrightarrow>\<^sub>m [x3' x4' \<Colon> (\<le>\<^bsub>R1\<^esub>) | x1' \<le>\<^bsub>R1\<^esub> x3'] \<Rrightarrow> (\<le>)) R2"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) (l2\<^bsub>x' x\<^esub>) (r2\<^bsub>x x'\<^esub>)"
  and "x1' \<le>\<^bsub>R1\<^esub> x2'"
  shows "partial_equivalence_rel (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
proof -
  from \<open>x1' \<le>\<^bsub>R1\<^esub> x2'\<close> PER_equiv1 have "x1' \<equiv>\<^bsub>R1\<^esub> \<epsilon>\<^sub>1 x1'"
    by (blast elim: t1.preorder_equivalence_order_equivalenceE
      intro: bi_related_if_rel_equivalence_on)
  with assms have "(\<le>\<^bsub>R2 x1' x2'\<^esub>) = (\<le>\<^bsub>R2 (\<epsilon>\<^sub>1 x1') x2'\<^esub>)"
    by (intro flip.left2_eq_if_bi_related_if_monoI) blast+
  with assms show ?thesis
    by (intro partial_equivalence_rel_right2_if_partial_equivalence_rel_right2_if_left_GaloisI[of x1'])
    blast+
qed

end

paragraph \<open>Function Relator\<close>

context transport_Fun_Rel
begin

lemma reflexive_on_in_field_leftI:
  assumes "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "partial_equivalence_rel (\<le>\<^bsub>L2\<^esub>)"
  shows "reflexive_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  using assms by (intro tdfr.reflexive_on_in_field_leftI) simp_all

lemma transitive_leftI:
  assumes "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  shows "transitive (\<le>\<^bsub>L\<^esub>)"
  using assms by (intro tdfr.transitive_leftI) simp_all

lemma transitive_leftI':
  assumes "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "transitive (\<le>\<^bsub>L2\<^esub>)"
  shows "transitive (\<le>\<^bsub>L\<^esub>)"
  using assms by (intro tdfr.transitive_leftI') simp_all

lemma preorder_on_in_field_leftI:
  assumes "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "partial_equivalence_rel (\<le>\<^bsub>L2\<^esub>)"
  shows "preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  using assms by (intro tdfr.preorder_on_in_field_leftI) simp_all

lemma symmetric_leftI:
  assumes "symmetric (\<le>\<^bsub>L1\<^esub>)"
  and "symmetric (\<le>\<^bsub>L2\<^esub>)"
  shows "symmetric (\<le>\<^bsub>L\<^esub>)"
  using assms by (intro tdfr.symmetric_leftI) simp_all

corollary partial_equivalence_rel_leftI:
  assumes "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "symmetric (\<le>\<^bsub>L1\<^esub>)"
  and "partial_equivalence_rel (\<le>\<^bsub>L2\<^esub>)"
  shows "partial_equivalence_rel (\<le>\<^bsub>L\<^esub>)"
  using assms by (intro tdfr.partial_equivalence_rel_leftI) auto

end

paragraph \<open>Monotone Dependent Function Relator\<close>

context transport_Mono_Dep_Fun_Rel
begin

lemmas reflexive_on_in_field_leftI = Refl_Rel_reflexive_on_in_field[of tdfr.L,
  folded left_rel_eq_tdfr_left_Refl_Rel]
lemmas transitive_leftI = Refl_Rel_transitiveI
  [of tdfr.L, folded left_rel_eq_tdfr_left_Refl_Rel]
lemmas preorder_on_in_field_leftI = Refl_Rel_preorder_on_in_fieldI[of tdfr.L,
  folded left_rel_eq_tdfr_left_Refl_Rel]
lemmas symmetric_leftI = Refl_Rel_symmetricI[of tdfr.L,
  OF tdfr.symmetric_leftI, folded left_rel_eq_tdfr_left_Refl_Rel]
lemmas partial_equivalence_rel_leftI = Refl_Rel_partial_equivalence_relI[of tdfr.L,
  OF tdfr.partial_equivalence_rel_leftI, folded left_rel_eq_tdfr_left_Refl_Rel]

end


paragraph \<open>Monotone Function Relator\<close>

context transport_Mono_Fun_Rel
begin

lemma symmetric_leftI:
  assumes "symmetric (\<le>\<^bsub>L1\<^esub>)"
  and "symmetric (\<le>\<^bsub>L2\<^esub>)"
  shows "symmetric (\<le>\<^bsub>L\<^esub>)"
  using assms by (intro tpdfr.symmetric_leftI) auto

lemma partial_equivalence_rel_leftI:
  assumes "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "symmetric (\<le>\<^bsub>L1\<^esub>)"
  and "partial_equivalence_rel (\<le>\<^bsub>L2\<^esub>)"
  shows "partial_equivalence_rel (\<le>\<^bsub>L\<^esub>)"
  using assms by (intro tpdfr.partial_equivalence_rel_leftI) auto

end


end