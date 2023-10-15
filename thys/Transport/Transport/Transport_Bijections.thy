\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Transport using Bijections\<close>
theory Transport_Bijections
  imports
    Functions_Bijection
    Transport_Base
begin

paragraph \<open>Summary\<close>
text \<open>Setup for Transport using bijective transport functions.\<close>

locale transport_bijection =
  fixes L :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and R :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  and l :: "'a \<Rightarrow> 'b"
  and r :: "'b \<Rightarrow> 'a"
  assumes mono_wrt_rel_left: "(L \<Rrightarrow>\<^sub>m R) l"
  and mono_wrt_rel_right: "(R \<Rrightarrow>\<^sub>m L) r"
  and inverse_left_right: "inverse_on (in_field L) l r"
  and inverse_right_left: "inverse_on (in_field R) r l"
begin

interpretation transport L R l r .
interpretation g_flip_inv : galois "(\<ge>\<^bsub>R\<^esub>)" "(\<ge>\<^bsub>L\<^esub>)" r l .

lemma bijection_on_in_field: "bijection_on (in_field (\<le>\<^bsub>L\<^esub>)) (in_field (\<le>\<^bsub>R\<^esub>)) l r"
  using mono_wrt_rel_left mono_wrt_rel_right inverse_left_right inverse_right_left
  by (intro bijection_onI in_field_if_in_field_if_mono_wrt_rel)
  auto

lemma half_galois_prop_left: "((\<le>\<^bsub>L\<^esub>) \<^sub>h\<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  using mono_wrt_rel_left inverse_right_left
  by (intro half_galois_prop_leftI)
  (auto dest!: in_field_if_in_codom inverse_onD)

lemma half_galois_prop_right: "((\<le>\<^bsub>L\<^esub>) \<unlhd>\<^sub>h (\<le>\<^bsub>R\<^esub>)) l r"
  using mono_wrt_rel_right inverse_left_right
  by (intro half_galois_prop_rightI)
  (force dest: in_field_if_in_dom inverse_onD)

lemma galois_prop: "((\<le>\<^bsub>L\<^esub>) \<unlhd> (\<le>\<^bsub>R\<^esub>)) l r"
  using half_galois_prop_left half_galois_prop_right
  by (intro galois_propI)

lemma galois_connection: "((\<le>\<^bsub>L\<^esub>) \<stileturn> (\<le>\<^bsub>R\<^esub>)) l r"
  using mono_wrt_rel_left mono_wrt_rel_right galois_prop
  by (intro galois_connectionI)

lemma rel_equivalence_on_unitI:
  assumes "reflexive_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  shows "rel_equivalence_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>) \<eta>"
  using assms inverse_left_right
  by (subst rel_equivalence_on_unit_iff_reflexive_on_if_inverse_on)

interpretation flip : transport_bijection R L r l
  rewrites "order_functors.unit r l \<equiv> \<epsilon>"
  using mono_wrt_rel_left mono_wrt_rel_right inverse_left_right inverse_right_left
  by unfold_locales (simp_all only: flip_unit_eq_counit)

lemma galois_equivalence: "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R\<^esub>)) l r"
  using galois_connection flip.galois_prop by (intro galois_equivalenceI)

lemmas rel_equivalence_on_counitI = flip.rel_equivalence_on_unitI

lemma order_equivalenceI:
  assumes "reflexive_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^sub>o (\<le>\<^bsub>R\<^esub>)) l r"
  using assms mono_wrt_rel_left mono_wrt_rel_right rel_equivalence_on_unitI
    rel_equivalence_on_counitI
  by (intro order_equivalenceI)

lemma preorder_equivalenceI:
  assumes "preorder_on (in_field (\<le>\<^bsub>L\<^esub>)) (\<le>\<^bsub>L\<^esub>)"
  and "preorder_on (in_field (\<le>\<^bsub>R\<^esub>)) (\<le>\<^bsub>R\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro preorder_equivalence_if_galois_equivalenceI
    galois_equivalence)
  simp_all

lemma partial_equivalence_rel_equivalenceI:
  assumes "partial_equivalence_rel (\<le>\<^bsub>L\<^esub>)"
  and "partial_equivalence_rel (\<le>\<^bsub>R\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro partial_equivalence_rel_equivalence_if_galois_equivalenceI
    galois_equivalence)
  simp_all

end

locale transport_reflexive_on_in_field_bijection =
  fixes L :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and R :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  and l :: "'a \<Rightarrow> 'b"
  and r :: "'b \<Rightarrow> 'a"
  assumes reflexive_on_in_field_left: "reflexive_on (in_field L) L"
  and reflexive_on_in_field_right: "reflexive_on (in_field R) R"
  and transport_bijection: "transport_bijection L R l r"
begin

sublocale tbij? : transport_bijection L R l r
  rewrites "reflexive_on (in_field L) L \<equiv> True"
  and "reflexive_on (in_field R) R \<equiv> True"
  and "\<And>P. (True \<Longrightarrow> P) \<equiv> Trueprop P"
  using transport_bijection reflexive_on_in_field_left reflexive_on_in_field_right
  by auto

lemmas rel_equivalence_on_unit = rel_equivalence_on_unitI
lemmas rel_equivalence_on_counit = rel_equivalence_on_counitI
lemmas order_equivalence = order_equivalenceI

end

locale transport_preorder_on_in_field_bijection =
  fixes L :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and R :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  and l :: "'a \<Rightarrow> 'b"
  and r :: "'b \<Rightarrow> 'a"
  assumes preorder_on_in_field_left: "preorder_on (in_field L) L"
  and preorder_on_in_field_right: "preorder_on (in_field R) R"
  and transport_bijection: "transport_bijection L R l r"
begin

sublocale trefl_bij? : transport_reflexive_on_in_field_bijection L R l r
  rewrites "preorder_on (in_field L) L \<equiv> True"
  and "preorder_on (in_field R) R \<equiv> True"
  and "\<And>P. (True \<Longrightarrow> P) \<equiv> Trueprop P"
  using transport_bijection
  by (intro transport_reflexive_on_in_field_bijection.intro)
  (insert preorder_on_in_field_left preorder_on_in_field_right, auto)

lemmas preorder_equivalence = preorder_equivalenceI

end

locale transport_partial_equivalence_rel_bijection =
  fixes L :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and R :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  and l :: "'a \<Rightarrow> 'b"
  and r :: "'b \<Rightarrow> 'a"
  assumes partial_equivalence_rel_left: "partial_equivalence_rel L"
  and partial_equivalence_rel_right: "partial_equivalence_rel R"
  and transport_bijection: "transport_bijection L R l r"
begin

sublocale tpre_bij? : transport_preorder_on_in_field_bijection L R l r
  rewrites "partial_equivalence_rel L \<equiv> True"
  and "partial_equivalence_rel R \<equiv> True"
  and "\<And>P. (True \<Longrightarrow> P) \<equiv> Trueprop P"
  using transport_bijection
  by (intro transport_preorder_on_in_field_bijection.intro)
  (insert partial_equivalence_rel_left partial_equivalence_rel_right, auto)

lemmas partial_equivalence_rel_equivalence = partial_equivalence_rel_equivalenceI

end

locale transport_eq_restrict_bijection =
  fixes P :: "'a \<Rightarrow> bool"
  and Q :: "'b \<Rightarrow> bool"
  and l :: "'a \<Rightarrow> 'b"
  and r :: "'b \<Rightarrow> 'a"
  assumes bijection_on_in_field:
    "bijection_on (in_field ((=\<^bsub>P\<^esub>) :: 'a \<Rightarrow> _)) (in_field ((=\<^bsub>Q\<^esub>) :: 'b \<Rightarrow> _)) l r"
begin

interpretation transport "(=\<^bsub>P\<^esub>)" "(=\<^bsub>Q\<^esub>)" l r .

sublocale tper_bij? : transport_partial_equivalence_rel_bijection "(=\<^bsub>P\<^esub>)" "(=\<^bsub>Q\<^esub>)" l r
  using bijection_on_in_field partial_equivalence_rel_eq_restrict
    eq_restrict_le_eq
  by unfold_locales
  (auto elim: bijection_onE intro!:
    mono_wrt_rel_left_if_reflexive_on_if_le_eq_if_mono_wrt_in_field
      [of "in_field (=\<^bsub>Q\<^esub>)"]
    flip_of.mono_wrt_rel_left_if_reflexive_on_if_le_eq_if_mono_wrt_in_field
      [of "in_field (=\<^bsub>P\<^esub>)"])

lemma left_Galois_eq_Galois_eq_eq_restrict: "(\<^bsub>L\<^esub>\<lessapprox>) = (galois_rel.Galois (=) (=) r)\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub>"
  by (subst galois_rel.left_Galois_restrict_left_eq_left_Galois_left_restrict_left
    galois_rel.left_Galois_restrict_right_eq_left_Galois_right_restrict_right
    restrict_right_eq rel_inv_eq_self_if_symmetric)+
  (auto simp: eq_restrict_eq_eq_restrict_left)

end

locale transport_eq_bijection =
  fixes l :: "'a \<Rightarrow> 'b"
  and r :: "'b \<Rightarrow> 'a"
  assumes bijection_on_in_field:
    "bijection_on (in_field ((=) :: 'a \<Rightarrow> _)) (in_field ((=) :: 'b \<Rightarrow> _)) l r"
begin

sublocale teq_restr_bij? : transport_eq_restrict_bijection \<top> \<top> l r
  rewrites "(=\<^bsub>\<top> :: 'a \<Rightarrow> bool\<^esub>) = ((=) :: 'a \<Rightarrow> _)"
  and "(=\<^bsub>\<top> :: 'b \<Rightarrow> bool\<^esub>) = ((=) :: 'b \<Rightarrow> _)"
  using bijection_on_in_field by unfold_locales simp_all

end


end