theory Nonground_Inference
  imports
    Nonground_Clause_Generic
    Inference_Functor
begin

context nonground_clause_generic
begin

sublocale inference: term_based_lifting where
  sub_subst = clause.subst and sub_vars = clause.vars and sub_is_ground = clause.is_ground and
  map = map_inference and to_set = set_inference and sub_to_ground = clause.to_ground and
  sub_from_ground = clause.from_ground and to_ground_map = map_inference and
  from_ground_map = map_inference and ground_map = map_inference and to_set_ground = set_inference
  by unfold_locales

notation inference.subst (infixl "\<cdot>\<iota>" 67)

lemma vars_inference [simp]:
  "inference.vars (Infer Ps C) = \<Union> (clause.vars ` set Ps) \<union> clause.vars C"
  unfolding inference.vars_def
  by auto

lemma subst_inference [simp]:
  "Infer Ps C \<cdot>\<iota> \<sigma> = Infer (map (\<lambda>P. P \<cdot> \<sigma>) Ps) (C \<cdot> \<sigma>)"
  unfolding inference.subst_def
  by simp_all

lemma inference_from_ground_clause_from_ground [simp]:
  "inference.from_ground (Infer Ps C) = Infer (map clause.from_ground Ps) (clause.from_ground C)"
  by (simp add: inference.from_ground_def)

lemma inference_to_ground_clause_to_ground [simp]:
  "inference.to_ground (Infer Ps C) = Infer (map clause.to_ground Ps) (clause.to_ground C)"
  by (simp add: inference.to_ground_def)

lemma inference_is_ground_clause_is_ground [simp]:
  "inference.is_ground (Infer Ps C) \<longleftrightarrow> list_all clause.is_ground Ps \<and> clause.is_ground C"
  using Ball_set inference.is_ground_def
  by auto

end

end
