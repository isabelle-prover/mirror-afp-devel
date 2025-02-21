theory Functional_Substitution_Typing
  imports Typed_Functional_Substitution
begin

locale subst_is_typed_abbreviations =
  is_typed: typed_functional_substitution where
  base_typed = base_typed and is_typed = expr_is_typed +
  is_welltyped: typed_functional_substitution where
  base_typed = base_welltyped and is_typed = expr_is_welltyped
for
  base_typed base_welltyped :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" and
  expr_is_typed expr_is_welltyped :: "('var, 'ty) var_types \<Rightarrow> 'expr \<Rightarrow> bool"
begin

abbreviation is_typed_on where
  "is_typed_on \<equiv> is_typed.base.is_typed_on"

abbreviation is_welltyped_on where
  "is_welltyped_on \<equiv> is_welltyped.base.is_typed_on"

abbreviation is_typed where
  "is_typed \<equiv> is_typed.base.is_typed_on UNIV"

abbreviation is_welltyped where
  "is_welltyped \<equiv> is_welltyped.base.is_typed_on UNIV"

end

locale functional_substitution_typing =
  is_typed: typed_functional_substitution where
  base_typed = base_typed and is_typed = is_typed +
  is_welltyped: typed_functional_substitution where
  base_typed = base_welltyped and is_typed = is_welltyped
for
  base_typed base_welltyped :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" and
  is_typed is_welltyped :: "('var, 'ty) var_types \<Rightarrow> 'expr \<Rightarrow> bool" +
assumes typing: "\<And>\<V>. typing (is_typed \<V>) (is_welltyped \<V>)"
begin

sublocale base: typing "is_typed \<V>" "is_welltyped \<V>"
  by (rule typing)


sublocale subst: subst_is_typed_abbreviations
  where expr_is_typed = is_typed and expr_is_welltyped = is_welltyped
  by unfold_locales

end

locale base_functional_substitution_typing =
  typed: explicitly_typed_functional_substitution where typed = typed +
  welltyped: explicitly_typed_functional_substitution where typed = welltyped
for
  welltyped typed :: "('var, 'ty) var_types \<Rightarrow> 'expr \<Rightarrow> 'ty \<Rightarrow> bool" +
assumes
   explicit_typing: "\<And>\<V>. explicit_typing (typed \<V>) (welltyped \<V>)"
begin

sublocale base: explicit_typing "typed \<V>" "welltyped \<V>"
  using explicit_typing .

lemmas typed_id_subst = typed.typed_id_subst

lemmas welltyped_id_subst = welltyped.typed_id_subst

lemmas is_typed_id_subst = typed.is_typed_id_subst

lemmas is_welltyped_id_subst = welltyped.is_typed_id_subst

lemmas is_typed_on_subset = typed.is_typed_on_subset

lemmas is_welltyped_on_subset = welltyped.is_typed_on_subset

sublocale functional_substitution_typing where
  is_typed = base.is_typed and is_welltyped = base.is_welltyped and base_typed = typed and
  base_welltyped = welltyped and base_vars = vars and base_subst = subst
  by unfold_locales

sublocale subst: typing "subst.is_typed_on X \<V>" "subst.is_welltyped_on X \<V>"
  using base.typed_if_welltyped
  by unfold_locales blast

end

end
