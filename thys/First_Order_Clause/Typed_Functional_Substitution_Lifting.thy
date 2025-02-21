theory Typed_Functional_Substitution_Lifting
  imports
    Typed_Functional_Substitution
    Abstract_Substitution.Functional_Substitution_Lifting
begin

(* TODO: *)
lemma ext_equiv: "(\<And>x. f x \<equiv> g x) \<Longrightarrow> f \<equiv> g"
  by presburger

locale typed_functional_substitution_lifting =
  sub: typed_functional_substitution where
  vars = sub_vars and subst = sub_subst and is_typed = sub_is_typed and
  base_vars = base_vars +
  based_functional_substitution_lifting where to_set = to_set and base_vars = base_vars
for
  sub_is_typed :: "('var, 'ty) var_types \<Rightarrow> 'sub \<Rightarrow> bool" and
  to_set :: "'expr \<Rightarrow> 'sub set" and
  base_vars :: "'base \<Rightarrow> 'var set"
begin

abbreviation (input) lifted_is_typed where
  "lifted_is_typed \<V> \<equiv> is_typed_lifting to_set (sub_is_typed \<V>)"

lemmas lifted_is_typed_def = is_typed_lifting_def[of to_set, THEN ext_equiv, of sub_is_typed]

sublocale typed_functional_substitution where
  vars = vars and subst = subst and is_typed = lifted_is_typed
  by unfold_locales

end

locale uniform_typed_functional_substitution_lifting =
  base: explicitly_typed_functional_substitution where
  vars = base_vars and subst = base_subst and typed = base_typed +
  based_functional_substitution_lifting where
  to_set = to_set and sub_subst = base_subst and sub_vars = base_vars
for
  base_typed :: "('var, 'ty) var_types \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" and
  to_set :: "'expr \<Rightarrow> 'base set"
begin

abbreviation (input) lifted_is_typed where
  "lifted_is_typed \<V> \<equiv> uniform_typed_lifting to_set (base_typed \<V>)"

lemmas lifted_is_typed_def = uniform_typed_lifting_def[of to_set, THEN ext_equiv, of base_typed]

sublocale typed_functional_substitution where
  vars = vars and subst = subst and is_typed = lifted_is_typed
  by unfold_locales

end

locale uniform_typed_grounding_functional_substitution_lifting =
  uniform_typed_functional_substitution_lifting +
  grounding_lifting where sub_subst = base_subst and sub_vars = base_vars +
  base: explicitly_typed_grounding_functional_substitution where
  vars = base_vars and subst = base_subst and typed = base_typed and
  to_ground = sub_to_ground and from_ground = sub_from_ground
begin

sublocale typed_grounding_functional_substitution where
  vars = vars and subst = subst and is_typed = lifted_is_typed and to_ground = to_ground and
  from_ground = from_ground
  by unfold_locales

end

locale typed_grounding_functional_substitution_lifting =
  typed_functional_substitution_lifting +
  grounding_lifting +
  sub: typed_grounding_functional_substitution where
  vars = sub_vars and subst = sub_subst and is_typed = sub_is_typed and
  to_ground = sub_to_ground and from_ground = sub_from_ground
begin

sublocale typed_grounding_functional_substitution where
  vars = vars and subst = subst and is_typed = lifted_is_typed and to_ground = to_ground and
  from_ground = from_ground
  by unfold_locales

end

locale uniform_inhabited_typed_functional_substitution_lifting =
  uniform_typed_functional_substitution_lifting +
  base: inhabited_explicitly_typed_functional_substitution where
  vars = base_vars and subst = base_subst and typed = base_typed
begin

sublocale inhabited_typed_functional_substitution where
  vars = vars and subst = subst and is_typed = lifted_is_typed
  by unfold_locales

end

locale inhabited_typed_functional_substitution_lifting =
  typed_functional_substitution_lifting +
  sub: inhabited_typed_functional_substitution where
  vars = sub_vars and subst = sub_subst and is_typed = sub_is_typed
begin

sublocale inhabited_typed_functional_substitution where
  vars = vars and subst = subst and is_typed = lifted_is_typed
  by unfold_locales

end

locale typed_subst_stability_lifting =
  typed_functional_substitution_lifting +
  sub: typed_subst_stability where is_typed = sub_is_typed and vars = sub_vars and subst = sub_subst
begin

sublocale typed_subst_stability where
  is_typed = lifted_is_typed and subst = subst and vars = vars
proof unfold_locales
  fix expr \<V> \<sigma>
  assume "sub.base.is_typed_on (vars expr) \<V> \<sigma>"

  then show "lifted_is_typed \<V> (expr \<cdot> \<sigma>) \<longleftrightarrow> lifted_is_typed \<V> expr"
    unfolding vars_def is_typed_lifting_def
    using sub.subst_stability to_set_image
    by fastforce

qed

end

locale uniform_typed_subst_stability_lifting =
  uniform_typed_functional_substitution_lifting +
  base: explicitly_typed_subst_stability where
  typed = base_typed and vars = base_vars and subst = base_subst
begin

sublocale typed_subst_stability where
  is_typed = lifted_is_typed and subst = subst and vars = vars
proof unfold_locales
  fix expr \<V> \<sigma>
  assume "base.is_typed_on (vars expr) \<V> \<sigma>"

  then show "lifted_is_typed \<V> (subst expr \<sigma>) \<longleftrightarrow> lifted_is_typed \<V> expr"
    unfolding vars_def uniform_typed_lifting_def
    using base.subst_stability to_set_image
    by force
qed

end

locale replaceable_\<V>_lifting =
  typed_functional_substitution_lifting +
  sub: replaceable_\<V> where
  subst = sub_subst and vars = sub_vars and is_typed = sub_is_typed
begin

sublocale replaceable_\<V> where
  subst = subst and vars = vars and is_typed = lifted_is_typed
  by unfold_locales (auto simp: sub.replace_\<V> vars_def is_typed_lifting_def)

end

locale uniform_replaceable_\<V>_lifting =
  uniform_typed_functional_substitution_lifting +
  sub: explicitly_replaceable_\<V> where
  typed = base_typed and vars = base_vars and subst = base_subst
begin

sublocale replaceable_\<V> where
  is_typed = lifted_is_typed and subst = subst and vars = vars
  by
    unfold_locales
    (auto 4 4 simp: vars_def uniform_typed_lifting_def intro: sub.explicit_replace_\<V>)

end

locale based_typed_renaming_lifting =
  based_functional_substitution_lifting +
  renaming_variables_lifting +
  based_typed_renaming where subst = sub_subst and vars = sub_vars
begin

sublocale based_typed_renaming where subst = subst and vars = vars
  by unfold_locales

end

locale typed_renaming_lifting =
  typed_functional_substitution_lifting where
  base_typed = "base_typed :: ('v \<Rightarrow> 'ty) \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool" +
  based_typed_renaming_lifting where typed = base_typed +
  sub: typed_renaming where
  subst = sub_subst and vars = sub_vars and is_typed = sub_is_typed
begin

sublocale typed_renaming where
  subst = subst and vars = vars and is_typed = lifted_is_typed
proof unfold_locales
  fix \<rho> expr and \<V> \<V>' :: "'v \<Rightarrow> 'ty"
  assume "sub.base.is_renaming \<rho>" "\<forall>x\<in>vars expr. \<V> x = \<V>' (rename \<rho> x)"

  then show "lifted_is_typed \<V>' (expr \<cdot> \<rho>) = lifted_is_typed \<V> expr"
    using sub.typed_renaming
    unfolding vars_def subst_def is_typed_lifting_def
    by force
qed

end

locale uniform_typed_renaming_lifting =
  uniform_typed_functional_substitution_lifting where base_typed = base_typed +
  based_typed_renaming_lifting where
  typed = base_typed and sub_vars = base_vars and sub_subst = base_subst
for base_typed :: "('v \<Rightarrow> 'ty) \<Rightarrow> 'base \<Rightarrow> 'ty \<Rightarrow> bool"
begin

sublocale typed_renaming where
  is_typed = lifted_is_typed and subst = subst and vars = vars
proof unfold_locales
  fix \<rho> expr and \<V> \<V>' :: "'v \<Rightarrow> 'ty"
  assume "base.is_renaming \<rho>" "\<forall>x\<in>vars expr. \<V> x = \<V>' (rename \<rho> x)"

  then show "lifted_is_typed \<V>' (subst expr \<rho>) = lifted_is_typed \<V> expr"
    using base.typed_renaming
    unfolding vars_def subst_def uniform_typed_lifting_def
    by force
qed

end

end
