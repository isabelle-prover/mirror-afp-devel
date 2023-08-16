(*
Title: Multimonoids
Author: Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Multimonoids\<close>

theory Multimonoid
  imports Catoid

begin

context multimagma
begin

subsection \<open>Unital multimagmas\<close>

text \<open>This component presents an alternative approach to catoids, as multisemigroups with many units.
This is more akin to the formalisation of single-set categories in Chapter I of Mac Lane's book, but
in fact this approach to axiomatising categories goes back to the middle of the twentieth century.\<close>

text \<open>Units can already be defined in multimagmas.\<close>

definition "munitl e = ((\<exists>x. x \<in> e \<odot> x) \<and> (\<forall>x y. y \<in> e \<odot> x \<longrightarrow> y = x))"

definition "munitr e = ((\<exists>x. x \<in> x \<odot> e) \<and> (\<forall>x y. y \<in> x \<odot> e \<longrightarrow> y = x))"

abbreviation "munit e \<equiv> (munitl e \<or> munitr e)"

end

text \<open>A multimagma is unital if every element has a left and a right unit.\<close>

class unital_multimagma_var = multimagma +
  assumes munitl_ex: "\<forall>x.\<exists>e. munitl e \<and> \<Delta> e x"
  assumes munitr_ex: "\<forall>x.\<exists>e. munitr e \<and> \<Delta> x e"

begin

lemma munitl_ex_var: "\<forall>x.\<exists>e. munitl e \<and> x \<in> e \<odot> x"
  by (metis equals0I local.munitl_def local.munitl_ex)

lemma unitl: "\<Union>{e \<odot> x |e. munitl e} = {x}"
  apply safe
  apply (simp add: multimagma.munitl_def)
  by (simp, metis munitl_ex_var)

lemma munitr_ex_var: "\<forall>x.\<exists>e. munitr e \<and> x \<in> x \<odot> e"
  by (metis equals0I local.munitr_def local.munitr_ex)

lemma unitr: "\<Union>{x \<odot> e |e. munitr e} = {x}"
  apply safe
   apply (simp add: multimagma.munitr_def)
  by (simp, metis munitr_ex_var)

end

text \<open>Here is an alternative definition.\<close>

class unital_multimagma = multimagma +
  fixes E :: "'a set"
  assumes El: "\<Union>{e \<odot> x |e. e \<in> E} = {x}"
  and Er: "\<Union>{x \<odot> e |e. e \<in> E} = {x}"

begin

lemma E1: "\<forall>e \<in> E. (\<forall>x y. y \<in> e \<odot> x \<longrightarrow> y = x)"
  using local.El by fastforce

lemma E2: "\<forall>e \<in> E. (\<forall>x y. y \<in> x \<odot> e \<longrightarrow> y = x)"
  using local.Er by fastforce

lemma El11: "\<forall>x.\<exists>e \<in> E. x \<in> e \<odot> x"
  using local.El by fastforce

lemma El12: "\<forall>x.\<exists>e \<in> E. e \<odot> x = {x}"
  using E1 El11 by fastforce

lemma Er11: "\<forall>x.\<exists>e \<in> E. x \<in> x \<odot> e"
  using local.Er by fastforce

lemma Er12: "\<forall>x.\<exists>e \<in> E. x \<odot> e = {x}"
  using Er Er11 by fastforce

text \<open>Units are "orthogonal" idempotents.\<close>

lemma unit_id: "\<forall>e \<in> E. e \<in> e \<odot> e"
  using E1 local.Er by fastforce

lemma unit_id_eq: "\<forall>e \<in> E. e \<odot> e = {e}"
  by (simp add: E1 equalityI subsetI unit_id)

lemma unit_comp:
  assumes "e\<^sub>1 \<in> E"
and "e\<^sub>2 \<in> E"
and "\<Delta> e\<^sub>1 e\<^sub>2"
shows "e\<^sub>1 = e\<^sub>2"
proof-
  obtain x where a: "x \<in> e\<^sub>1 \<odot> e\<^sub>2"
    using assms(3) by auto
  hence b: "x = e\<^sub>1"
    using E2 assms(2) by blast
  hence "x = e\<^sub>2"
    using E1 a assms(1) by blast
  thus "e\<^sub>1 = e\<^sub>2"
    by (simp add: b)
qed

lemma unit_comp_iff: "e\<^sub>1 \<in> E \<Longrightarrow> e\<^sub>2 \<in> E \<Longrightarrow> (\<Delta> e\<^sub>1 e\<^sub>2 = (e\<^sub>1 = e\<^sub>2))"
  using unit_comp unit_id by fastforce

lemma "\<forall>e \<in> E.\<exists>x. x \<in> e \<odot> x"
  using unit_id by force

lemma "\<forall>e \<in> E.\<exists>x. x \<in> x \<odot> e"
  using unit_id by force

sublocale unital_multimagma_var
  apply unfold_locales
  apply (metis E1 El12 empty_not_insert insertI1 local.munitl_def)
  by (metis E2 Er12 empty_not_insert insertI1 local.munitr_def)

text \<open>Now it is clear that the two definitions are equivalent.\<close>

text \<open>The next two lemmas show that the set of units is a left and right unit of composition at powerset level.\<close>

lemma conv_unl: "E \<star> X = X"
  unfolding conv_def
  apply safe
  using E1 apply blast
  using El12 by fastforce

lemma conv_unr: "X \<star> E = X"
  unfolding conv_def
  apply safe
  using E2 apply blast
  using Er12 by fastforce

end


subsection \<open>Multimonoids\<close>

text \<open>A multimonoid is a unital multisemigroup.\<close>

class multimonoid = multisemigroup + unital_multimagma

begin

text \<open>In a multimonoid, left and right units are unique for each element.\<close>

lemma munits_uniquel: "\<forall>x.\<exists>!e. e \<in> E \<and> e \<odot> x = {x}"
proof-
  {fix x
  obtain e where a: "e \<in> E \<and> e \<odot> x = {x}"
    using local.El12 by blast
  {fix e'
  assume b: "e' \<in> E \<and> e' \<odot> x = {x}"
  hence "{e} \<star> (e' \<odot> x) = {x}"
    by (simp add: a multimagma.conv_atom)
  hence "(e \<odot> e') \<star> {x}  = {x}"
    by (simp add: local.assoc_var)
  hence "\<Delta> e e'"
    using local.conv_exp2 by auto
  hence "e = e'"
    by (simp add: a b local.unit_comp_iff)}
  hence "\<exists>e \<in> E. e \<odot> x = {x} \<and> (\<forall>e' \<in> E. e' \<odot> x = {x} \<longrightarrow> e = e)"
    using a by blast}
  thus ?thesis
    by (metis emptyE local.assoc_exp local.unit_comp singletonI)
qed

lemma munits_uniquer: "\<forall>x.\<exists>!e. e \<in> E \<and> x \<odot> e = {x}"
  apply safe
   apply (meson local.Er12)
  by (metis insertI1 local.E1 local.E2 local.assoc_var local.conv_exp2)

text \<open>In a monoid, there is of course one single unit, and my definition of many units reduces to this one.\<close>

lemma units_unique: "(\<forall>x y. \<Delta> x y) \<Longrightarrow> \<exists>!e. e \<in> E"
  apply safe
  using local.El11 apply blast
  using local.unit_comp_iff by presburger

lemma units_rm2l: "e\<^sub>1 \<in> E \<Longrightarrow> e\<^sub>2 \<in> E \<Longrightarrow> \<Delta> e\<^sub>1 x \<Longrightarrow> \<Delta> e\<^sub>2 x \<Longrightarrow> e\<^sub>1 = e\<^sub>2"
  by (smt (verit, del_insts) ex_in_conv local.E1 local.assoc_exp local.unit_comp)

lemma units_rm2r: "e\<^sub>1 \<in> E \<Longrightarrow> e\<^sub>2 \<in> E \<Longrightarrow> \<Delta> x e\<^sub>1 \<Longrightarrow> \<Delta> x e\<^sub>2 \<Longrightarrow> e\<^sub>1 = e\<^sub>2"
  by (metis (full_types) ex_in_conv local.E2 local.assoc_exp local.unit_comp)

text \<open>One can therefore express the functional relationship between elements and their units in terms of
explict (source and target) maps -- as in catoids.\<close>

definition so :: "'a \<Rightarrow> 'a" where
  "so x = (THE e. e \<in> E \<and> e \<odot> x = {x})"

definition ta :: "'a \<Rightarrow> 'a"  where
  "ta x = (THE e. e \<in> E \<and> x \<odot> e = {x})"

abbreviation So :: "'a set \<Rightarrow> 'a set" where
 "So X \<equiv> image so X"

abbreviation Ta :: "'a set \<Rightarrow> 'a set" where
 "Ta X \<equiv> image ta X"

end

subsection \<open>Multimonoids and catoids\<close>

text \<open>It is now easy to show that every catoid is a multimonoid and vice versa.\<close>

(*sublocale catoid \<subseteq> lrmon: multimonoid "(\<odot>)" sfix
  apply unfold_locales
  using local.sfix_absorb_var apply presburger
  using local.stfix_set local.tfix_absorb_var by presburger*)

text \<open>One cannot have both sublocale statements at the same time.\<close>

text \<open>The converse direction requires some preparation.\<close>

lemma (in multimonoid) so_unit: "so x \<in> E"
  unfolding so_def by (metis (mono_tags, lifting) local.munits_uniquel theI')

lemma (in multimonoid) ta_unit: "ta x \<in> E"
  unfolding ta_def by (metis (mono_tags, lifting) local.munits_uniquer theI')

lemma (in multimonoid) so_absorbl: "so x \<odot> x = {x}"
  unfolding so_def by (metis (mono_tags, lifting) local.munits_uniquel the_equality)

lemma (in multimonoid) ta_absorbr: "x \<odot> ta x = {x}"
  unfolding ta_def by (metis (mono_tags, lifting) local.munits_uniquer the_equality)

lemma (in multimonoid) semi_locality: "\<Delta> x y \<Longrightarrow> ta x = so y"
  by (smt (verit, best) local.assoc_var local.conv_atom local.so_absorbl local.so_unit local.ta_absorbr local.ta_unit local.units_rm2l local.units_rm2r)

sublocale multimonoid \<subseteq> monlr: catoid "(\<odot>)" "so" "ta"
  by (unfold_locales, simp_all add: local.semi_locality local.so_absorbl local.ta_absorbr)


subsection\<open>From multimonoids to categories\<close>

text\<open>Single-set categories are precisely local partial monoids, that is, object-free categories
as in Chapter I of Mac Lane's book.\<close>

class local_multimagma = multimagma +
  assumes locality: "v \<in> x \<odot> y \<Longrightarrow> \<Delta> y z  \<Longrightarrow> \<Delta> v z"

class local_multisemigroup = multisemigroup + local_multimagma

text \<open>In this context, a semicategory is an object-free category without identity arrows\<close>

class of_semicategory = local_multisemigroup + functional_semigroup

begin

lemma part_locality: "\<Delta> x y  \<Longrightarrow> \<Delta> y z  \<Longrightarrow> \<Delta> (x \<otimes> y) z"
  by (meson local.locality local.pcomp_def_var2)

lemma part_locality_var: "\<Delta> x y  \<Longrightarrow> \<Delta> y z  \<Longrightarrow> (x \<odot> y) \<star> {z} \<noteq> {}"
  by (smt (z3) ex_in_conv local.locality multimagma.conv_exp2 singleton_iff)

lemma locality_iff: "(\<Delta> x y \<and> \<Delta> y z) = (\<Delta> x y \<and> \<Delta> (x \<otimes> y) z)"
  by (meson local.pcomp_assoc_defined part_locality)

lemma locality_iff_var: "(\<Delta> x y \<and> \<Delta> y z) = (\<Delta> x y \<and> (x \<odot> y) \<star> {z} \<noteq> {})"
  by (metis ex_in_conv local.assoc_var local.conv_exp2 part_locality_var)

end

class partial_monoid = multimonoid + functional_magma

class local_multimonoid = multimonoid + local_multimagma

begin

lemma sota_locality: "ta x = so y \<Longrightarrow> \<Delta> x y"
  using local.locality monlr.st_local_iff by blast

lemma So_local: "So (x \<odot> so y) = So (x \<odot> y)"
  using local.locality monlr.st_local_iff monlr.st_locality_locality by presburger

lemma Ta_local: "Ta (ta x \<odot> y) = Ta (x \<odot> y)"
  using local.locality monlr.st_local_iff monlr.st_locality_locality by presburger

sublocale locmm: local_catoid "(\<odot>)" so ta
  by (unfold_locales, simp_all add: So_local Ta_local)

text \<open>The following statements formalise compatibility properties.\<close>

lemma local_conv: "v \<in> x \<odot> y \<Longrightarrow> (\<Delta> v z = \<Delta> y z)"
  by (metis ex_in_conv local.assoc_exp local.locality)

lemma local_alt: "e \<in> E \<Longrightarrow> x \<in> x \<odot> e \<Longrightarrow> y \<in> e \<odot> y \<Longrightarrow> \<Delta> x y"
  using local_conv by blast

lemma local_iff: "\<Delta> x y = (\<exists>e \<in> E. \<Delta> x e \<and> \<Delta> e y)"
  by (smt (verit, best) local.Er11 local.units_rm2l local_alt local_conv)

lemma local_iff2: "(ta x = so y) = \<Delta> x y"
  by (simp add: locmm.st_local)

end

text \<open>Finally I formalise object-free categories. The axioms are essentially Mac Lane's,
but a multioperation is used for arrow composition, to capture partiality.\<close>

class of_category = of_semicategory + partial_monoid

text \<open>The next statements show that single-set categories based on catoids and object-free categories
based on multimonoids are the same (we can only have one direction as a sublocale statement). It then
follows from results about catoids and single-set categories that object-free categories are indeed categories.
These results can be found in the catoid component. I do not present explicit proofs for object-free categories
here.\<close>

sublocale of_category \<subseteq> ofss_cat: single_set_category _ so ta
  apply unfold_locales
  using local.locality monlr.st_local_iff monlr.st_locality_locality apply auto[1]
  using local.locality monlr.st_local_iff monlr.st_locality_locality monlr.tgt_weak_local by presburger

(*
sublocale single_set_category \<subseteq> of_category _ sfix
  apply unfold_locales
  using local.st_local local.st_local_iff apply auto[1]
  using local.sfix_absorb_var apply presburger
  using local.stfix_set local.tfix_absorb_var by presburger
*)

subsection \<open>Multimonoids and relational monoids\<close>

text \<open>Relational monoids are monoids in the category Rel. They have been used previously to construct
convolution algebras in another AFP entry. Here I show that relational monoids are isomorphic to multimonoids,
but I do not integrate the AFP entry with relational monoids because it uses a historic quantale component,
which is different from the quantale component in the AFP. Instead, I simply copy in the definitions
leading to relational monoids and leave the consolidation of Isabelle theories to the future.\<close>

class rel_magma =
  fixes \<rho> :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"

class rel_semigroup = rel_magma +
  assumes rel_assoc: "(\<exists>y. \<rho> y u v \<and> \<rho> x y w) = (\<exists>z. \<rho> z v w \<and> \<rho> x u z)"

class rel_monoid = rel_semigroup +
  fixes \<xi> :: "'a set"
  assumes unitl_ex: "\<exists>e \<in> \<xi>. \<rho> x e x"
  and unitr_ex: "\<exists>e \<in> \<xi>. \<rho> x x e"
  and unitl_eq: "e \<in> \<xi> \<Longrightarrow> \<rho> x e y \<Longrightarrow> x = y"
  and unitr_eq: "e \<in> \<xi> \<Longrightarrow> \<rho> x y e \<Longrightarrow> x = y"

text \<open>Once again, only one of the two sublocale statements compiles.\<close>

(*sublocale rel_monoid \<subseteq> multimonoid "\<lambda>x y. {z. \<rho> z x y}" \<xi>
  apply unfold_locales
    apply safe
       apply simp_all
       apply (metis CollectI local.rel_assoc)
      apply (metis CollectI local.rel_assoc)
     apply (simp add: local.unitl_eq)
    apply (metis CollectI local.unitl_ex)
  apply (simp add: local.unitr_eq)
  by (metis local.unitr_ex mem_Collect_eq)*)

sublocale multimonoid \<subseteq> rel_monoid "\<lambda>x y z. x \<in> y \<odot> z" E
  apply unfold_locales
  using local.assoc_exp apply blast
  using local.El11 apply blast
    apply (simp add: local.Er11)
  using local.E1 apply blast
  by (simp add: local.E2)

end



