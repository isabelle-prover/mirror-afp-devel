\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Transport using Identity\<close>
theory Transport_Identity
  imports
    Transport_Bijections
begin

paragraph \<open>Summary\<close>
text \<open>Setup for Transport using the identity transport function.\<close>


locale transport_id =
  fixes L :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

sublocale tbij? : transport_bijection L L id id
  by (intro transport_bijection.intro) auto

interpretation transport L L id id .

lemma left_Galois_eq_left: "(\<^bsub>L\<^esub>\<lessapprox>) = (\<le>\<^bsub>L\<^esub>)"
  by (intro ext iffI) auto

end

locale transport_reflexive_on_in_field_id =
  fixes L :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes reflexive_on_in_field: "reflexive_on (in_field L) L"
begin

sublocale trefl_bij? : transport_reflexive_on_in_field_bijection L L id id
  using reflexive_on_in_field by unfold_locales auto

end

locale transport_preorder_on_in_field_id =
  fixes L :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes preorder_on_in_field: "preorder_on (in_field L) L"
begin

sublocale tpre_bij? : transport_preorder_on_in_field_bijection L L id id
  using preorder_on_in_field by unfold_locales auto

end

locale transport_partial_equivalence_rel_id =
  fixes L :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes partial_equivalence_rel: "partial_equivalence_rel L"
begin

sublocale tper_bij? : transport_partial_equivalence_rel_bijection L L id id
  using partial_equivalence_rel by unfold_locales auto

end

interpretation transport_eq_restrict_id :
  transport_eq_restrict_bijection P P id id for  P :: "'a \<Rightarrow> bool"
  using bijection_on_self_id by (unfold_locales) auto

interpretation transport_eq_id : transport_eq_bijection id id
  using bijection_on_self_id by (unfold_locales) auto


end
