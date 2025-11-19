theory Literal_Functor
  imports
    Abstract_Substitution.Natural_Functor
    Saturation_Framework_Extensions.Clausal_Calculus
begin

lemma literal_cases: "\<lbrakk>\<P> \<in> {Pos, Neg}; \<P> = Pos \<Longrightarrow> P; \<P> = Neg \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by blast

lemma map_literal_inverse:
  "(\<And>x. f (g x) = x) \<Longrightarrow> (\<And>l. map_literal f (map_literal g l) = l)"
  by (simp add: literal.map_comp literal.map_ident_strong)

lemma map_literal_comp:
  "map_literal f (map_literal g l) = map_literal (\<lambda>a. f (g a)) l"
  using literal.map_comp
  unfolding comp_def.

lemma literals_distinct [simp]: "Pos \<noteq> Neg" "Neg \<noteq> Pos"
  by (metis literal.distinct(1))+

lemma set_literal_not_empty [iff]: "set_literal l \<noteq> {}"
  by (cases l) simp_all

lemma finite_set_literal [intro]: "finite (set_literal l)"
  unfolding set_literal_atm_of
  by simp

global_interpretation literal_functor: finite_natural_functor where
  map = map_literal and to_set = set_literal
  by
    unfold_locales
    (auto simp: literal.map_comp literal.map_ident literal.set_map intro: literal.map_cong)

global_interpretation literal_functor: natural_functor_conversion where
  map = map_literal and to_set = set_literal and map_to = map_literal and map_from = map_literal and
  map' = map_literal and to_set' = set_literal
  by unfold_locales
    (auto simp: literal.set_map literal.map_comp)

end
