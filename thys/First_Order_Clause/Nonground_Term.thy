theory Nonground_Term
  imports Abstract_Substitution.Based_Substitution_Lifting
begin

locale vars_def =
  fixes vars_def :: "'expr \<Rightarrow> 'var"
begin

abbreviation "vars \<equiv> vars_def"

end

locale grounding_def =
  fixes
    to_ground_def :: "'expr \<Rightarrow> 'expr\<^sub>G" and
    from_ground_def :: "'expr\<^sub>G \<Rightarrow> 'expr"
begin

abbreviation "to_ground \<equiv> to_ground_def"

abbreviation "from_ground \<equiv> from_ground_def"

end

locale base_properties =
  base_substitution +
  all_subst_ident_iff_ground +
  exists_non_ident_subst +
  grounding +
  finite_variables +
  renaming_variables +
  variables_in_base_imgu where
  base_vars = vars and base_subst = subst +
  base_exists_ground_subst

locale nonground_term =
  base_properties where
  subst = term_subst and vars = term_vars and to_ground = term_to_ground and
  from_ground = term_from_ground
for
  term_subst :: "'t \<Rightarrow> 'subst \<Rightarrow> 't" and
  term_vars :: "'t \<Rightarrow> 'v set" and
  term_to_ground :: "'t \<Rightarrow> 't\<^sub>G" and
  term_from_ground :: "'t\<^sub>G \<Rightarrow> 't"
begin

abbreviation Var where
  "Var x \<equiv> x \<cdot>v id_subst"

notation term_subst (infixl "\<cdot>t" 67)

sublocale vars_def where vars_def = term_vars .

sublocale grounding_def where
  to_ground_def = term_to_ground and from_ground_def = term_from_ground .

abbreviation is_Var where
 "is_Var t \<equiv> \<exists>x. t = Var x"

end

locale lifting =
  based_substitution_lifting +
  all_subst_ident_iff_ground_lifting +
  grounding_lifting +
  renaming_variables_lifting +
  variables_in_base_imgu_lifting +
  exists_ground_subst_lifting

locale term_based_lifting =
  "term": nonground_term +
  lifting where base_subst = term_subst and base_vars = term_vars

end
