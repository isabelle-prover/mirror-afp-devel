section \<open>Countable Sets\<close>

theory Countable
  imports Nats Axiom_Of_Choice Nat_Parity Cardinality
begin

text \<open>The definition below corresponds to Definition 2.6.9 in Halvorson.\<close>
definition epi_countable :: "cset \<Rightarrow> bool" where
  "epi_countable X \<longleftrightarrow> (\<exists> f. f : \<nat>\<^sub>c \<rightarrow> X \<and> epimorphism f)"

lemma emptyset_is_not_epi_countable:
  "\<not> epi_countable \<emptyset>"
  using comp_type emptyset_is_empty epi_countable_def zero_type by blast

text \<open>The fact that the empty set is not countable according to the definition from Halvorson
  (@{thm epi_countable_def}) motivated the following definition.\<close>
definition countable :: "cset \<Rightarrow> bool" where
  "countable X \<longleftrightarrow> (\<exists> f. f : X \<rightarrow> \<nat>\<^sub>c \<and> monomorphism f)"

lemma epi_countable_is_countable: 
  assumes "epi_countable X"
  shows "countable X"
  using assms countable_def epi_countable_def epis_give_monos by blast

lemma emptyset_is_countable:
  "countable \<emptyset>"
  using countable_def empty_subset subobject_of_def2 by blast

lemma natural_numbers_are_countably_infinite:
  "countable \<nat>\<^sub>c \<and> is_infinite \<nat>\<^sub>c"
  by (meson CollectI Peano's_Axioms countable_def injective_imp_monomorphism is_infinite_def successor_type)

lemma iso_to_N_is_countably_infinite:
  assumes "X \<cong> \<nat>\<^sub>c"
  shows "countable X \<and> is_infinite X"
  by (meson assms countable_def is_isomorphic_def is_smaller_than_def iso_imp_epi_and_monic isomorphic_is_symmetric larger_than_infinite_is_infinite natural_numbers_are_countably_infinite)

lemma smaller_than_countable_is_countable:
  assumes "X \<le>\<^sub>c Y" "countable Y"
  shows "countable X"
  by (smt assms cfunc_type_def comp_type composition_of_monic_pair_is_monic countable_def is_smaller_than_def)

lemma iso_pres_countable:
  assumes "X \<cong> Y" "countable Y"
  shows "countable X"
  using assms is_isomorphic_def is_smaller_than_def iso_imp_epi_and_monic smaller_than_countable_is_countable by blast

lemma NuN_is_countable:
  "countable(\<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c)"
  using countable_def epis_give_monos halve_with_parity_iso halve_with_parity_type iso_imp_epi_and_monic by smt

text \<open>The lemma below corresponds to Exercise 2.6.11 in Halvorson.\<close>
lemma coproduct_of_countables_is_countable:
  assumes "countable X" "countable Y"
  shows "countable(X \<Coprod> Y)"
  unfolding countable_def
proof-
  obtain x where x_def:  "x : X  \<rightarrow> \<nat>\<^sub>c \<and> monomorphism x"
    using assms(1) countable_def by blast
  obtain y where y_def:  "y : Y  \<rightarrow> \<nat>\<^sub>c \<and> monomorphism y"
    using assms(2) countable_def by blast
  obtain n where n_def: " n : \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c \<rightarrow> \<nat>\<^sub>c \<and> monomorphism n"
    using NuN_is_countable countable_def by blast
  have xy_type: "x \<bowtie>\<^sub>f y : X \<Coprod> Y \<rightarrow> \<nat>\<^sub>c \<Coprod> \<nat>\<^sub>c"
    using x_def y_def by (typecheck_cfuncs, auto)
  then have nxy_type: "n \<circ>\<^sub>c (x \<bowtie>\<^sub>f y) : X \<Coprod> Y \<rightarrow> \<nat>\<^sub>c"
    using comp_type n_def by blast
  have "injective(x \<bowtie>\<^sub>f y)"
    using cfunc_bowtieprod_inj monomorphism_imp_injective x_def y_def by blast
  then have "monomorphism(x \<bowtie>\<^sub>f y)"
    using injective_imp_monomorphism by auto
  then have "monomorphism(n \<circ>\<^sub>c (x \<bowtie>\<^sub>f y))"
    using cfunc_type_def composition_of_monic_pair_is_monic n_def xy_type by auto
  then show "\<exists>f. f : X \<Coprod> Y \<rightarrow> \<nat>\<^sub>c \<and> monomorphism f"
    using nxy_type by blast
qed

end