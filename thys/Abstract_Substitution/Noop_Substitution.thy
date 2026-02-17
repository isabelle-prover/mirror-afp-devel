theory Noop_Substitution \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close> 
  imports Based_Substitution
begin

definition noop_comp_subst where
  "noop_comp_subst \<sigma> _ = \<sigma>"

definition noop_id_subst where
  "noop_id_subst = ()"

global_interpretation unit: abstract_substitution_monoid where
  comp_subst = noop_comp_subst and id_subst = noop_id_subst
  by unfold_locales auto

locale properties =
  base_substitution +
  all_subst_ident_iff_ground +
  exists_non_ident_subst +
  subst_update +
  grounding +
  finite_variables +
  renaming_variables +
  exists_ground +
  range_vars_subset_if_is_imgu +
  exists_imgu +
  create_renaming where base_subst = subst and base_vars = vars and base_is_ground = is_ground

definition noop_apply_subst where
  "noop_apply_subst _ _ \<equiv> SOME expr. True"

definition noop_subst where
  "noop_subst expr _ \<equiv> expr"

definition noop_vars where
  "noop_vars _ \<equiv> {}"

definition noop_is_ground where
  "noop_is_ground _ \<longleftrightarrow> True"

definition noop_subst_update where
  "noop_subst_update \<sigma> _ _ \<equiv> \<sigma>"


context abstract_substitution_monoid
begin

sublocale noop: base_substitution where 
  vars = noop_vars and apply_subst = noop_apply_subst and is_ground = noop_is_ground and
  subst = noop_subst
  by 
    unfold_locales 
    (auto simp: noop_vars_def noop_subst_update_def noop_apply_subst_def noop_subst_def
      noop_is_ground_def)

sublocale noop: properties where 
  vars = noop_vars and subst_update = noop_subst_update and apply_subst = noop_apply_subst and
  subst = noop_subst and to_ground = id and from_ground = id and is_ground = noop_is_ground
  by 
    unfold_locales 
    (auto simp: noop_vars_def noop.range_vars_def noop.subst_domain_def noop_is_ground_def
      noop_subst_update_def)

(* TODO: *)
lemma noop_subst [simp]: "noop_subst expr \<sigma> = expr"
  by (simp add: noop_subst_def)

lemma noop_is_ground [simp]: "noop_is_ground expr"
  using noop_is_ground_def
  by fast

lemma noop_vars [simp]: "noop_vars expr = {}"
  unfolding noop_vars_def
  by blast

end

end
