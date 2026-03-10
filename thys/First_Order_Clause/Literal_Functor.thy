theory Literal_Functor
  imports
    Abstract_Substitution.Natural_Functor
    Saturation_Framework_Extensions.Clausal_Calculus
begin

setup natural_functor_setups

lemma literal_cases: "\<lbrakk>\<P> \<in> {Pos, Neg}; \<P> = Pos \<Longrightarrow> P; \<P> = Neg \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by blast

lemma literals_distinct [simp]: "Pos \<noteq> Neg" "Neg \<noteq> Pos"
  by (metis literal.distinct(1))+

lemma set_literal_not_empty [iff]: "set_literal l \<noteq> {}"
  by (cases l) simp_all

global_interpretation literal_functor: natural_functor_conversion where
  map = map_literal and to_set = set_literal and map_to = map_literal and map_from = map_literal and
  map' = map_literal and to_set' = set_literal
  by unfold_locales (auto simp: literal.set_map literal.map_comp)

end
