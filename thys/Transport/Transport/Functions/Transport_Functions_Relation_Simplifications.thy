\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Simplification of Left and Right Relations\<close>
theory Transport_Functions_Relation_Simplifications
  imports
    Transport_Functions_Order_Base
    Transport_Functions_Galois_Equivalence
begin

paragraph \<open>Dependent Function Relator\<close>

context transport_Dep_Fun_Rel
begin

text \<open>Due to
@{thm "transport_Mono_Dep_Fun_Rel.left_rel_eq_tdfr_left_rel_if_reflexive_on"},
we can apply all results from @{locale "transport_Mono_Dep_Fun_Rel"} to
@{locale "transport_Dep_Fun_Rel"} whenever @{term "(\<le>\<^bsub>L\<^esub>)"} and @{term "(\<le>\<^bsub>R\<^esub>)"} are
reflexive.\<close>

lemma reflexive_on_in_field_left_rel2_le_assmI:
  assumes refl_L1: "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and mono_L2: "([x1 \<Colon> \<top>] \<Rrightarrow>\<^sub>m [x2 x3 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x2] \<Rrightarrow>\<^sub>m (\<le>)) L2"
  and "x1 \<le>\<^bsub>L1\<^esub> x2"
  shows "(\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
proof -
  from refl_L1 \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close> have "x1 \<le>\<^bsub>L1\<^esub> x1" by blast
  with dep_mono_wrt_relD[OF dep_mono_wrt_predD[OF mono_L2] \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close>]
    show "(\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)" by auto
qed

lemma reflexive_on_in_field_mono_assm_left2I:
  assumes mono_L2: "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and refl_L1: "reflexive_on (in_dom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  shows "([x1 \<Colon> \<top>] \<Rrightarrow>\<^sub>m [x2 x3 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x2] \<Rrightarrow>\<^sub>m (\<le>)) L2"
proof (intro dep_mono_wrt_predI dep_mono_wrt_relI rel_if_if_impI)
  fix x1 x2 x3 assume "x1 \<le>\<^bsub>L1\<^esub> x2" "x2 \<le>\<^bsub>L1\<^esub> x3"
  with refl_L1 have "x1 \<ge>\<^bsub>L1\<^esub> x1" by blast
  from Dep_Fun_Rel_relD[OF dep_mono_wrt_relD[OF mono_L2 \<open>x1 \<ge>\<^bsub>L1\<^esub> x1\<close>]
    \<open>x2 \<le>\<^bsub>L1\<^esub> x3\<close>] \<open>x1 \<le>\<^bsub>L1\<^esub> x2\<close>
    show "(\<le>\<^bsub>L2 x1 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x3\<^esub>)" by blast
qed

lemma reflexive_on_in_field_left_if_equivalencesI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "preorder_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> partial_equivalence_rel (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  shows "reflexive_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  using assms
  by (intro reflexive_on_in_field_leftI
    left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_leftI
    galois_equivalence_if_mono_if_galois_equivalence_mono_assms_leftI
    reflexive_on_in_field_left_rel2_le_assmI
    reflexive_on_in_field_mono_assm_left2I)
  (auto intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_dom)

end


paragraph \<open>Monotone Dependent Function Relator\<close>

context transport_Mono_Dep_Fun_Rel
begin

lemma left_rel_eq_tdfr_leftI:
  assumes "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x2 x2\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> (\<le>\<^bsub>L2 x1 x1\<^esub>) \<le> (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> partial_equivalence_rel (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  shows "(\<le>\<^bsub>L\<^esub>) = tdfr.L"
  using assms by (intro left_rel_eq_tdfr_left_rel_if_reflexive_on
    tdfr.reflexive_on_in_field_leftI)
  auto

lemma left_rel_eq_tdfr_leftI_if_equivalencesI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "preorder_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "([x1 x2 \<Colon> (\<ge>\<^bsub>L1\<^esub>)] \<Rrightarrow>\<^sub>m [x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x1 \<le>\<^bsub>L1\<^esub> x3] \<Rrightarrow> (\<le>)) L2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> partial_equivalence_rel (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  shows "(\<le>\<^bsub>L\<^esub>) = tdfr.L"
  using assms by (intro left_rel_eq_tdfr_left_rel_if_reflexive_on
    tdfr.reflexive_on_in_field_left_if_equivalencesI)
  auto

end


paragraph \<open>Monotone Function Relator\<close>

context transport_Mono_Fun_Rel
begin

lemma left_rel_eq_tfr_leftI:
  assumes "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "partial_equivalence_rel (\<le>\<^bsub>L2\<^esub>)"
  shows "(\<le>\<^bsub>L\<^esub>) = tfr.tdfr.L"
  using assms by (intro tpdfr.left_rel_eq_tdfr_leftI) auto

end


end