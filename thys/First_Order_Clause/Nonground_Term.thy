theory Nonground_Term
  imports 
    Abstract_Substitution.Functional_Substitution_Lifting
    Ground_Term_Extra (* TODO: Also just specify ground term *)
begin

type_synonym 'f ground_term = "'f gterm"

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
  base_functional_substitution +
  all_subst_ident_iff_ground +
  grounding +
  finite_variables +
  renaming_variables +
  variables_in_base_imgu where base_vars = vars and base_subst = subst

locale nonground_term =
  base_properties where
  id_subst = Var and subst = term_subst and vars = term_vars and to_ground = term_to_ground and
  from_ground = term_from_ground
for 
  Var :: "'v \<Rightarrow> 't" and
  term_subst term_vars and
  term_to_ground :: "'t \<Rightarrow> 'f ground_term" and
  term_from_ground :: "'f ground_term \<Rightarrow> 't"
begin

notation term_subst (infixl "\<cdot>t" 67)

sublocale vars_def where vars_def = term_vars .

sublocale grounding_def where
  to_ground_def = term_to_ground and from_ground_def = term_from_ground .

abbreviation is_Var where
 "is_Var t \<equiv> \<exists>x. t = Var x"

end

locale lifting =
  based_functional_substitution_lifting +
  all_subst_ident_iff_ground_lifting +
  grounding_lifting +
  renaming_variables_lifting +
  variables_in_base_imgu_lifting

locale term_based_lifting =
  "term": nonground_term +
  lifting where id_subst = Var and base_subst = term_subst and base_vars = term_vars

end
