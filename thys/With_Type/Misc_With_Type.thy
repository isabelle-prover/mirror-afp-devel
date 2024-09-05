section \<open>\<open>Misc_With_Type\<close> -- Some auxiliary definitions and lemmas\<close>

theory Misc_With_Type
  imports Main
begin

lemma type_definition_bij_betw_iff: \<open>type_definition rep (inv rep) S \<longleftrightarrow> bij_betw rep UNIV S\<close>
  by (smt (verit, best) UNIV_I bij_betw_def bij_betw_iff_bijections inj_on_def inv_f_eq type_definition.Rep_inject type_definition.Rep_range type_definition.intro)

inductive rel_unit_itself :: \<open>unit \<Rightarrow> 'a itself \<Rightarrow> bool\<close> where
\<comment> \<open>A canonical relation between \<^typ>\<open>unit\<close> and \<^typ>\<open>'a itself\<close>.
  Note that while the latter may not be a singleton type, in many situations we treat it as 
  one by only using the element \<^term>\<open>TYPE('a)\<close>.\<close>
  \<open>rel_unit_itself () TYPE('a)\<close>

lemma Domain_rel_unit_itself[simp]: \<open>Domainp rel_unit_itself x\<close>
  by (simp add: Domainp_iff rel_unit_itself.simps)
lemma rel_unit_itself_iff[simp]: \<open>rel_unit_itself x y \<longleftrightarrow> (y = TYPE('a))\<close>
  by (simp add: rel_unit_itself.simps)

end
