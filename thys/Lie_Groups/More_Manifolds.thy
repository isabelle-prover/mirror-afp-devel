(*  Title:       More_Manifolds
    Author:      Richard Schmoetten <richard.schmoetten@ed.ac.uk>, 2024
    Maintainer:  Richard Schmoetten <richard.schmoetten@ed.ac.uk>
*)

section \<open>Results about Manifolds and Analysis.\<close>
theory More_Manifolds
imports
  Types_To_Sets_Extension.VS_Modules
  Smooth_Manifolds.Tangent_Space
  Smooth_Manifolds.Product_Manifold
  Groups_On_With
begin

text \<open>Contains results not just about manifolds, but also supporting results about other parts of
  the standard Isabelle distribution/AFP.\<close>

subsection \<open>General and Miscellaneous\<close>

lemma bij_betw_if_inverse:
  assumes "bij_betw f A B"
    and "\<And>x. x\<in>A \<Longrightarrow> f' (f x) = x"
    and "\<And>y. y\<in>B \<Longrightarrow> f (f' y) = y"
  shows "bij_betw f' B A"
  by (smt (verit, ccfv_SIG) assms bij_betwE bij_betw_cong bij_betw_the_inv_into f_the_inv_into_f_bij_betw)

\<comment> \<open>Complements @{thm f_the_inv_into_f_bij_betw}.\<close>
lemma the_inv_into_f_f_bij_betw:
  "bij_betw f A B \<Longrightarrow> (bij_betw f A B \<Longrightarrow> x \<in> A) \<Longrightarrow> the_inv_into A f (f x) = x"
  unfolding bij_betw_def by (blast intro: the_inv_into_f_f)

lemma has_derivativeD:
  assumes "(f has_derivative f') (at x within s)"
  shows "bounded_linear f'"
    and "((\<lambda>y. ((f y - f x) - f' (y - x)) /\<^sub>R norm (y - x)) \<longlongrightarrow> 0) (at x within s)"
    using assms has_derivative_at_within by auto

lemma homeomorphism_imp_open_map':
  assumes hom: "homeomorphism S T f g"
    and U: "open U" "U \<subseteq> S"
    and T: "open T"
  shows "open (f ` U)"
proof -
  have "openin (top_of_set T) (f`U)" by (simp add: open_subset homeomorphism_imp_open_map[OF hom] U)
  thus ?thesis by (simp add: T openin_open_eq)
qed

lemma homeo_imp_bij: assumes "homeomorphism a b f f'" shows "bij_betw f a b"
  by (metis assms bij_betw_def homeomorphism_apply1 homeomorphism_image1 inj_onI)

lemma smooth_on_cong':
  assumes "k-smooth_on T f" "S=T"
  shows "k-smooth_on S f"
  by (simp add: assms)

lemma ran_the_im_dom: "ran f = the ` (f ` dom f)"
  unfolding ran_def dom_def image_def by force

lemma map_comp_assoc: "(h\<circ>\<^sub>mg)\<circ>\<^sub>mf = h\<circ>\<^sub>m(g\<circ>\<^sub>mf)" for f g h
proof
  fix x
  consider (x_in)"x\<in>dom f"|(x_out)"x\<notin>dom f" by blast
  then show "(h \<circ>\<^sub>m g \<circ>\<^sub>m f) x = (h \<circ>\<^sub>m (g \<circ>\<^sub>m f)) x"
    by (cases, smt (verit, ccfv_threshold) map_comp_simps option.exhaust, simp add: domIff)
qed

lemma map_comp_dom: "dom (g\<circ>\<^sub>mf) = dom f" if "ran f \<subseteq> dom g" for f and g
  using ranI subset_iff' that by fastforce

text \<open>It would be much nicer if instead of \<^term>\<open>f \<in> manifold_eucl.diff_fun_space k\<close>, we could
  just state that \<^term>\<open>f\<close> is differentiable at \<^term>\<open>p\<close>. However, (one of) the difference between
  \<^term>\<open>directional_derivative\<close> and \<^term>\<open>frechet_derivative\<close> is that the former returns 0
  whenever the argument function is non-zero anywhere outside the carrier. It is therefore not a
  local operation: two functions that differ only at a point far away may still have different
  \<^term>\<open>directional_derivative\<close>s.\<close>
lemma directional_derivative_cong:
  assumes "open U" "p\<in>U" "\<forall>x\<in>U. f x = g x" "k\<noteq>0" "f \<in> manifold_eucl.diff_fun_space k" "g \<in> manifold_eucl.diff_fun_space k"
  shows "directional_derivative k p v f = directional_derivative k p v g"
  using assms(5,6) apply (simp add: directional_derivative_def)
  apply (intro frechet_derivative_transform_within_open_ext[OF _ assms(1,2)])
  using differentiable_onD assms(3-6) Smooth.smooth_on_imp_differentiable_on by blast+


lemma inverse_bij_betw:
  assumes f: "bij_betw f A B" and g: "\<forall>x\<in>A. g (f x) = x" "\<forall>y\<in>B. f (g y) = y"
  shows "bij_betw g B A"
  unfolding bij_betw_def inj_on_def apply (intro conjI)
   apply (metis g(2))
  using f g(1) by (simp add: bij_betw_if_inverse bij_betw_imp_surj_on g(2))

lemma linear_on_inv:
  assumes lin: "linear_on A B scaleA scaleB a"
    and bij: "bij_betw a A B"
    and inv: "(\<forall>x \<in> A. a x \<in> B \<and> b(a x) = x)" "(\<forall>y \<in> B. b y \<in> A \<and> a(b y) = y)"
  shows "linear_on B A scaleB scaleA b"
proof -
  interpret l: linear_on A B scaleA scaleB a
    using lin .
  show "linear_on B A scaleB scaleA b"
    apply unfold_locales using bij inv l.add l.m1.mem_add l.m1.mem_scale l.scale by metis+
qed

lemma linear_on_the_inv_into:
  assumes "linear_on A B scaleA scaleB a"
    and "bij_betw a A B"
  shows "linear_on B A scaleB scaleA (the_inv_into A a)"
  using linear_on_inv assms f_the_inv_into_f_bij_betw the_inv_into_f_eq
      the_inv_into_onto bij_betw_iff_bijections bij_betw_the_inv_into
  by (smt (verit, best))

lemma linear_on_image:
  assumes "linear_on A B scaleA scaleB a"
    and "a`A\<subseteq>B"
  shows "linear_on A (a`A) scaleA scaleB a"
proof -
  interpret l: linear_on A B scaleA scaleB a using assms(1) .
  show ?thesis apply unfold_locales
    subgoal by (meson assms(2) in_mono l.m2.scale_right_distrib_on)
    using assms(2) l.m2.scale_left_distrib_on apply auto[3]
    subgoal using l.add l.m1.mem_add by force
    subgoal using l.add l.m1.mem_zero by force
    subgoal by (metis (no_types, lifting) image_iff l.m1.mem_scale l.scale)
    subgoal by (simp add: l.add)
    subgoal by (simp add: l.scale)
  done
qed

lemma linear_on_the_inv_into':
  assumes "linear_on A B scaleA scaleB a"
    and "inj_on a A" "a`A\<subseteq>B"
  shows "linear_on (a`A) A scaleB scaleA (the_inv_into A a)"
  using linear_on_the_inv_into[OF linear_on_image[OF assms(1,3)]] assms(2) by (simp add: bij_betw_def)

lemma module_hom_on_compose:
  assumes "module_hom_on S1 S2 s1 s2 f" "module_hom_on S2 S3 s2 s3 g" "f ` S1 \<subseteq> S2"
  shows "module_hom_on S1 S3 s1 s3 (g o f)"
proof -
  interpret f: module_hom_on S1 S2 s1 s2 f using assms(1) .
  interpret g: module_hom_on S2 S3 s2 s3 g using assms(2) .
  show "module_hom_on S1 S3 s1 s3 (g o f)"
    apply unfold_locales
      subgoal using f.add g.add assms(3) by fastforce
      subgoal using f.scale g.scale assms(3) by fastforce
    done
qed

lemma linear_on_compose:
  assumes "linear_on S1 S2 s1 s2 f" "linear_on S2 S3 s2 s3 g" "f ` S1 \<subseteq> S2"
  shows "linear_on S1 S3 s1 s3 (g o f)"
  using module_hom_on_compose assms by (simp add: linear_on_def)

lemma bij_betw_restrict0:
  assumes "bij_betw f A B"
  shows "bij_betw (restrict0 A f) A B"
  unfolding restrict0_def by (simp add: assms bij_betw_cong)

lemma linear_on_restrict0:
  assumes "linear_on S1 S2 s1 s2 f"
  shows "linear_on S1 S2 s1 s2 (restrict0 S1 f)"
proof -
  interpret f: linear_on S1 S2 s1 s2 f using assms .
  show ?thesis
    by unfold_locales (simp_all add: restrict0_def f.m1.mem_scale f.scale f.add f.m1.mem_add)
qed

lemma extensional0_subset:
  assumes "extensional0 B f" "B\<subseteq>A"
  shows "extensional0 A f"
  using assms unfolding extensional0_def by auto

lemma restrict0_subset: "B\<subseteq>A \<Longrightarrow> restrict0 A (restrict0 B f) = restrict0 B f"
  unfolding restrict0_def by force

lemma restrict0_subset': "B\<subseteq>A \<Longrightarrow> extensional0 B f \<Longrightarrow> restrict0 A f = f"
  unfolding restrict0_def extensional0_def by force

lemma (in linear_on) vector_space_pair_on: "vector_space_pair_on S1 S2 s1 s2"
  by unfold_locales

lemma (in linear_on) linear_0: "f 0 = 0"
  using add m1.mem_zero by fastforce

lemma (in linear_on) linear_sum: "sum (f \<circ> g) A = f (sum g A)"
  if "g`A\<subseteq>S1" "f`S1\<subseteq>S2" for g and A using that
  by (auto intro!: vector_space_pair_on.linear_sum'[OF _ _ _ linear_on_axioms, symmetric])
    (unfold_locales)

lemma (in linear_on) independent:
  assumes "\<not> m1.dependent T" "T \<subseteq> S1" "inj_on f S1" "f ` S1 \<subseteq> S2"
  shows "\<not> m2.dependent (f`T)"
  apply (intro vector_space_pair_on.linear_independent_injective_image[OF vector_space_pair_on _ _ linear_on_axioms])
  using assms(1,2,4) inj_on_subset[OF assms(3)] m1.span_minimal m1.subspace_UNIV by auto

lemma (in linear_on) span:
  assumes "T \<subseteq> S1" "f ` S1 \<subseteq> S2"
  shows "m2.span (f`T) = f`(m1.span T)"
  apply (intro vector_space_pair_on.linear_span_image[OF vector_space_pair_on _ _ linear_on_axioms])
  using assms by auto

lemma (in linear_on) spanning:
  assumes "m1.span T = S1" "T \<subseteq> S1" "f`S1 = S2"
  shows "m2.span (f`T) = S2"
proof -
  have "S2 \<subseteq> m2.span (f ` T)"
    apply (intro vector_space_pair_on.linear_spanning_surjective_image[OF vector_space_pair_on _ _ linear_on_axioms])
    using assms(3) by (auto simp add: assms(1,2))
  thus "m2.span (f`T) = S2"
    by (metis assms(2) assms(3) image_mono m2.span_minimal m2.subspace_UNIV set_eq_subset)
qed

lemma (in linear_on) linear_on_cong:
  assumes "\<And>x. x\<in>S1 \<Longrightarrow> g x = f x"
  shows "linear_on S1 S2 s1 s2 g"
  using assms by (unfold_locales, simp_all add: add m1.mem_add m1.mem_scale scale)

\<comment> \<open>Compare to @{thm directional_derivative_linear_on_diff_fun_space}.\<close>
lemma frechet_derivative_linear_on_diff_fun_space:
  "k \<noteq> 0 \<Longrightarrow> manifold_eucl.linear_diff_fun k (\<lambda>f. frechet_derivative f (at a) x)"
  using directional_derivative_eq_frechet_derivative directional_derivative_linear_on_diff_fun_space
  by (metis (no_types, lifting) linear_on.linear_on_cong manifold_eucl.manifold_eucl_diff_fun_space_iff)

lemma real_vector_space_onI:
  assumes "vector_space_on S scaleR"
  shows "real_vector_space_on S"
proof
  interpret v: vector_space_on S scaleR using assms .
  show "subspace S"
    unfolding subspace_def by (auto simp add: v.mem_zero v.mem_add v.mem_scale)
qed

lemma finite_dimensional_real_vector_space_onI:
  assumes "finite_dimensional_vector_space_on S scaleR B"
  shows "finite_dimensional_real_vector_space_on S B"
proof
  interpret v: finite_dimensional_vector_space_on S scaleR B using assms .
  show "subspace S"
    unfolding subspace_def by (auto simp add: v.mem_zero v.mem_add v.mem_scale)
  show "finite B"
    by (simp add: v.finite_Basis)
  show "independent B"
    by (simp add: dependent_with v.implicit_dependent_with v.independent_Basis)
  show "B \<subseteq> S"
    by (simp add: v.basis_subset)
  show "span B = S"
    by (metis \<open>subspace S\<close> span_minimal span_subspace span_superset subspace_def subspace_span
        v.basis_subset v.span_Basis v.span_minimal v.subspace_on_def)
qed

lemma (in finite_dimensional_real_vector_space_on) basis_transfer:
  assumes "linear_on S T scaleR scaleR f" "bij_betw f S T"
  shows "finite_dimensional_real_vector_space_on T (f`basis)"
proof (intro finite_dimensional_real_vector_space_onI)
  interpret f: linear_on S T scaleR scaleR f using assms(1) .
  show "finite_dimensional_vector_space_on T scaleR (f ` basis)"
  proof (unfold_locales)
    show "finite (f ` basis)"
      by (simp add: finite_Basis)
    show "f ` basis \<subseteq> T"
      using assms(2) basis_subset by (auto simp: bij_betw_def)
    show "\<not> f.m2.dependent (f ` basis)"
      by (intro f.independent, simp_all add: independent_Basis basis_subset assms(2)[unfolded bij_betw_def])
    show "f.m2.span (f ` basis) = T"
      by (intro f.spanning, simp_all add: span_Basis basis_subset assms(2)[unfolded bij_betw_def])
  qed
qed

lemma euclidean_components_eq_iff:
  shows "(\<Sum>i\<in>Basis. f i *\<^sub>R i) = (\<Sum>i\<in>Basis. g i *\<^sub>R i) \<longleftrightarrow> (\<forall>i\<in>Basis. f i = g i)"
  by (auto, metis inner_sum_left_Basis)

lemma (in finite_dimensional_vector_space_on) VS_module_on: "VS_Modules.module_on S scale"
  apply unfold_locales
  by (simp_all add: scale_right_distrib_on scale_left_distrib_on mem_add mem_zero mem_scale)

\<comment> \<open>We bring in a result from the extended-Types-to-Sets development,
  @{thm VS_Modules.module_on.unique_representation}.\<close>
lemma (in finite_dimensional_vector_space_on) unique_representation_basis':
  assumes "B \<subseteq> basis"
    and "\<And>v. \<lbrakk>v \<in> S; f v \<noteq> 0\<rbrakk> \<Longrightarrow> v \<in> B"
    and "\<And>v. \<lbrakk>v \<in> S; g v \<noteq> 0\<rbrakk> \<Longrightarrow> v \<in> B"
    and "(\<Sum>v\<in>{x\<in>S. f x \<noteq> 0}. scale (f v) v) = (\<Sum>v\<in>{x\<in>S. g x \<noteq> 0}. scale (g v) v)"
  shows "\<forall>x\<in>S. f x = g x"
proof -
  interpret ETTS_mod: VS_Modules.module_on S scale using VS_module_on .
  have "\<not> ETTS_mod.dependent basis"
    using ETTS_mod.dependent_explicit basis_subset dependent_explicit independent_Basis by fastforce
  hence 1: "\<not> ETTS_mod.dependent B"
    using ETTS_mod.dependent_mono assms(1) basis_subset by blast
  have 2: "finite {x \<in> S. f x \<noteq> 0}" "finite {x \<in> S. g x \<noteq> 0}"
    using finite_Basis assms(1,2,3) by (auto intro: finite_subset)
  show ?thesis apply (rule ETTS_mod.unique_representation[of B])
    using assms basis_subset 1 2 by auto
qed

lemma (in finite_dimensional_vector_space_on) unique_representation_basis:
  assumes "\<And>v. \<lbrakk>v \<in> S; f v \<noteq> 0\<rbrakk> \<Longrightarrow> v \<in> basis"
    and "\<And>v. \<lbrakk>v \<in> S; g v \<noteq> 0\<rbrakk> \<Longrightarrow> v \<in> basis"
    and "(\<Sum>v\<in>{x\<in>S. f x \<noteq> 0}. scale (f v) v) = (\<Sum>v\<in>{x\<in>S. g x \<noteq> 0}. scale (g v) v)"
  shows "\<forall>x\<in>S. f x = g x"
  using unique_representation_basis' assms by auto

lemma (in finite_dimensional_vector_space_on) components_eq_iff:
  assumes "\<And>v. v \<in> S \<and> f v \<noteq> 0 \<longleftrightarrow> v \<in> basis"
    and "\<And>v. v \<in> S \<and> g v \<noteq> 0 \<longleftrightarrow> v \<in> basis"
  shows "(\<Sum>i\<in>basis. scale (f i) i) = (\<Sum>i\<in>basis. scale (g i) i) \<longleftrightarrow> (\<forall>i\<in>basis. f i = g i)"
proof -
  have "\<forall>i\<in>S. f i = g i" if "(\<Sum>i\<in>basis. scale (f i) i) = (\<Sum>i\<in>basis. scale (g i) i)"
    apply (rule unique_representation_basis)
    using assms that by auto
  from this show ?thesis using basis_subset by auto
qed

lemma linear_on_subset:
  assumes "linear_on C B scaleR scaleR f"
    and closed_A: "A\<subseteq>C" "A\<noteq>{}" "\<And>x r. x\<in>A \<Longrightarrow> scaleR r x \<in> A" "\<And>x y. \<lbrakk>x\<in>A; y\<in>A\<rbrakk> \<Longrightarrow> x+y \<in> A"
  shows "linear_on A B scaleR scaleR f"
proof -
  interpret linear_on C B scaleR scaleR f by fact
  show ?thesis
    using closed_A apply unfold_locales
    by (auto simp: algebra_simps add scale subset_iff) (metis m1.scale_zero_left)
qed


lemma
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "linear f"
  shows linear_imp_higher_differentiable_on: "higher_differentiable_on S f n"
    and linear_imp_smooth_on: "smooth_on S f"
  using bounded_linear.higher_differentiable_on bounded_linear.smooth_on assms
  by (auto simp: linear_conv_bounded_linear[of f])


lemma differentiable_transform_within:
  assumes "f differentiable (at x within s)"
    and "0 < d"
    and "x \<in> s"
    and "\<And>x'. \<lbrakk>x' \<in> s; dist x' x < d\<rbrakk> \<Longrightarrow> f x' = g x'"
  shows "g differentiable (at x within s)"
  using assms has_derivative_transform_within unfolding differentiable_def by blast

lemma differentiable_transform_within_open:
  assumes "f differentiable (at x within t)"
    and "open s"
    and "x \<in> s"
    and "\<And>x. x\<in>s \<Longrightarrow> f x = g x"
  shows "g differentiable (at x within t)"
  using assms has_derivative_transform_within_open unfolding differentiable_def by blast

lemma differentiable_transform:
  assumes "x \<in> s" "\<And>x. x \<in> s \<Longrightarrow> g x = f x"
  assumes "f differentiable (at x within s)"
  shows "g differentiable (at x within s)"
  using assms has_derivative_transform unfolding differentiable_def by blast


lemma derivative_is_smooth2': "smooth_on S (\<lambda>v. frechet_derivative f (at x) v)"
  if "f differentiable_on S" "x\<in>S" "open S"
  for S x and f :: "'i::euclidean_space \<Rightarrow> 'o::real_normed_vector"
proof -
  have linear_deriv: "linear (frechet_derivative f (at x within S))"
    using that(1,2) by (auto intro: linear_frechet_derivative simp: differentiable_on_def)
  show ?thesis
    using linear_imp_smooth_on[OF linear_deriv] at_within_open[OF that(2,3)] by force
qed

lemma derivative_is_smooth2: "smooth_on S (\<lambda>v. frechet_derivative f (at x) v)"
  if "smooth_on S f" "x\<in>S" "open S"
  for S x and f :: "'i::euclidean_space \<Rightarrow> 'o::real_normed_vector"
  using derivative_is_smooth2'[OF smooth_on_imp_differentiable_on[OF that(1)] that(2,3)] by simp


lemma (in c_manifold) diff_fun_on_open:
  assumes "open A"
  shows "diff_fun_on A f \<longleftrightarrow> A \<subseteq> carrier \<and> diff_fun k (charts_submanifold A) f"
proof (intro iffI conjI)
  assume diff_A_f: "diff_fun_on A f"
  thus "diff_fun k (charts_submanifold A) f"
  proof -
    {
      fix W f'
      assume asm: "open W" "A\<subseteq>W" "W \<subseteq> carrier" "\<forall>x\<in>A. f x = f' x" "diff_fun k (charts_submanifold W) f'"
      interpret W: manifold "restrict_chart W ` charts" .
      have 1: "manifold.charts_submanifold (charts_submanifold W) A = charts_submanifold A"
        apply (simp add: charts_submanifold_def W.charts_submanifold_def)
        using restrict_chart_restrict_chart asm(1-2) assms
        by (smt (verit, best) image_cong image_image inf.absorb_iff1)
      then interpret f': diff_fun k "charts_submanifold A" f'
        unfolding diff_fun_def
        using diff.diff_submanifold[OF asm(5)[unfolded diff_fun_def] assms] by simp
      have "diff_fun k (charts_submanifold A) f"
        apply (rule f'.diff_fun_cong)
        using assms asm(4) by (metis (no_types, lifting) Int_iff domain_restrict_chart
          f'.src.carrierE image_iff manifold.charts_submanifold_def)
    }
    then show ?thesis
      using diff_A_f by (metis diff_fun_onE)
    qed
  show "A \<subseteq> carrier"
    using diff_A_f unfolding diff_fun_on_def by auto
next
  assume asm: "A\<subseteq>carrier \<and> diff_fun k (charts_submanifold A) f"
  show "diff_fun_on A f"
    using asm assms by (auto intro: exI[of _ A] simp: diff_fun_on_def)
qed


lemma (in c_manifold) diff_fun_differentiable_at: "(f \<circ> (inv_chart c)) differentiable at (c p)"
  if "diff_fun k charts f" "c \<in> atlas" "p \<in> domain c" "k>0"
    using diff_fun.diff_fun_between_chartsD[OF that(1-3)] higher_differentiable_on.simps(2) that(3,4)
    unfolding smooth_on_def diff_fun_def diff_def diff_axioms_def
    by (metis Suc_ile_eq chart_in_codomain enat_0_iff(2))

lemma (in submanifold) sub_diff_fun_differentiable_at: "(f \<circ> (inv_chart c)) differentiable at (c p)"
  if "diff_fun k (charts_submanifold S) f" "c \<in> sub.atlas" "p \<in> domain c" "k>0"
  using sub.diff_fun_differentiable_at that by blast

lemma (in c_manifold) diff_fun_on_differentiable_at: "(f \<circ> (inv_chart c)) differentiable at (c p)"
  if "diff_fun_on S f" "c \<in> atlas" "p \<in> S" "S \<subseteq> domain c" "k>0" "open S"
proof -
  interpret S: submanifold charts k S by (unfold_locales, fact)
  show ?thesis
    apply (rule S.sub_diff_fun_differentiable_at[of f "restrict_chart S c" p, simplified])
    using diff_fun_on_open[OF that(6)] that S.submanifold_atlasI by auto
qed



subsection \<open>Products\<close>

subsubsection \<open>\<^term>\<open>map_prod\<close> and \<^term>\<open>swap\<close> (no manifolds required)\<close>

lemma continuous_on_swap2[continuous_intros]:
  "continuous_on (s \<times> t) f \<Longrightarrow> continuous_on (t \<times> s) (f \<circ> prod.swap)"
  using continuous_on_compose by (metis continuous_on_swap product_swap)

lemma homeomorphism_prod_swap:
  "homeomorphism (b \<times> a) (c \<times> d) (\<lambda>(y, x). (f x, g y)) (\<lambda>(x, y). (g' y, f' x))"
  if "homeomorphism a c f f'" "homeomorphism b d g g'"
proof -
  { 
    fix x y assume asm: "x\<in>a" "y\<in>b"
    have "(f x, g y) \<in> (\<lambda>x. (f (snd x), g (fst x))) ` (b \<times> a)"
      and "(y, x) \<in> (\<lambda>x. (g' (snd x), f' (fst x))) ` (f ` a \<times> g ` b)"
      using asm that unfolding homeomorphism_def using image_iff by fastforce+
  }
  thus ?thesis
    using that unfolding homeomorphism_def
    by (auto
        simp: split_beta image_prod
        intro!: continuous_intros
        elim: continuous_on_compose2)
qed

lemma continuous_on_map_prod:
  assumes "continuous_on A f" "continuous_on B g"
  shows "continuous_on (A\<times>B) (map_prod f g)"
proof -
  have "continuous_on (A \<times> B) (f \<circ> fst)"
    apply (rule continuous_on_compose[OF continuous_on_fst[OF continuous_on_id]])
    by (simp add: assms(1))
  moreover have "continuous_on (A \<times> B) (g \<circ> snd)"
    apply (rule continuous_on_compose[OF continuous_on_snd[OF continuous_on_id]])
    by (simp add: assms(2))
  ultimately show ?thesis
    using continuous_on_Pair[of "A\<times>B" "f\<circ>fst" "g\<circ>snd"] by (simp add: map_prod_def case_prod_beta)
qed

lemma continuous_on_map_proj:
  assumes "continuous_on (A\<times>B) (map_prod f g)"
  shows "continuous_on (A\<times>B) (f\<circ>fst)" "continuous_on (A\<times>B) (g\<circ>snd)"
  using assms continuous_on_fst continuous_on_snd by fastforce+

lemma homeomorphism_swap:
  fixes a :: "'a::topological_space set" and b :: "'b::topological_space set"
    and c :: "'c::topological_space set" and d :: "'d::topological_space set"
  assumes "homeomorphism S T F G"
  shows "homeomorphism (prod.swap`S) T (F\<circ>prod.swap) (prod.swap\<circ>G)"
  (is "homeomorphism ?S' T ?F' ?G'")
proof
  have "continuous_on S F"
    using assms by (simp add: homeomorphism_cont1)
  thus "continuous_on ?S' ?F'"
    using continuous_on_compose[OF continuous_on_swap, of "?S'" "F"] by (simp add: image_comp)
  have "continuous_on T G"
    using assms by (simp add: homeomorphism_cont2)
  from continuous_on_compose[OF this continuous_on_swap] show "continuous_on T ?G'"
    by (simp add: case_prod_unfold)
  show "?F' ` ?S' \<subseteq> T"
    using homeomorphism_image1[OF assms] by auto
  show "?G' ` T \<subseteq> ?S'"
    using homeomorphism_image2[OF assms] by auto
  show "\<And>y. y\<in>T \<Longrightarrow> (?F'(?G' y) = y)"
    using homeomorphism_apply2[OF assms] by auto
  show "\<And>x. x\<in>?S' \<Longrightarrow> (?G'(?F' x) = x)"
    using homeomorphism_apply1[OF assms] by auto
qed

lemma homeomorphism_swap':
  fixes a :: "'a::topological_space set" and b :: "'b::topological_space set"
    and c :: "'c::topological_space set" and d :: "'d::topological_space set"
  assumes "homeomorphism (a \<times> b) (c \<times> d) (\<lambda>(x, y). (f x, g y)) (\<lambda>(x, y). (f' x, g' y))"
  shows "homeomorphism (b \<times> a) (c \<times> d) (\<lambda>(y, x). (f x, g y)) (\<lambda>(x, y). (g' y, f' x))"
  apply (rule homeomorphism_cong[OF homeomorphism_swap[OF assms]])
  by (simp_all add: product_swap case_prod_unfold)


lemma open_swap: "open a \<Longrightarrow> open (prod.swap ` a)"
  by (smt (verit) imageE image_mono open_prod_def prod.swap_def product_swap swap_simp)


lemma bounded_linear_swap:
  assumes f: "bounded_linear f"
  shows "bounded_linear (f \<circ> prod.swap)"
proof
  interpret f: bounded_linear f by fact
  fix x::"'b\<times>'a" and y::"'b\<times>'a" and r :: real
  show "(f \<circ> prod.swap) (x + y) = (f \<circ> prod.swap) x + (f \<circ> prod.swap) y"
    using f.add by (auto simp add: prod.swap_def)
  show "(f \<circ> prod.swap) (r *\<^sub>R x) = r *\<^sub>R (f \<circ> prod.swap) x"
    using f.scale by (auto simp: prod.swap_def)
  obtain Kf where "0 < Kf" and norm_f: "\<And>x. norm (f x) \<le> norm x * Kf"
    using f.pos_bounded by fast
  have "\<forall>x. norm ((f \<circ> prod.swap) x) \<le> norm x * Kf"
    by (simp add: prod.swap_def, metis norm_commute norm_f)
  then show "\<exists>K. \<forall>x. norm ((f \<circ> prod.swap) x) \<le> norm x * K" ..
qed

lemma norm_swap: "norm x = norm (prod.swap x)"
    using norm_commute apply (simp add: prod.swap_def)
    by (smt (verit, ccfv_threshold) norm_commute prod.exhaust_sel)



subsubsection \<open>Pair is a smooth map (just like fst and snd)\<close>
context c_manifold_prod begin

sublocale prod_manifold: c_manifold prod_charts k
  using c_manifold_atlas_product by auto

lemma prod_carrier: "prod_manifold.carrier = m1.carrier \<times> m2.carrier"
proof -
  have "domain ` prod_charts = {domain (prod_chart c1 c2) |c1 c2. c1 \<in> charts1 \<and> c2 \<in> charts2}"
    unfolding prod_charts_def by blast
  also have "\<dots> = {domain c1 \<times> domain c2 |c1 c2. c1 \<in> charts1 \<and> c2 \<in> charts2}"
    by auto
  finally show ?thesis
    unfolding manifold.carrier_def by auto
qed

(* is this a good name? overlap with manifold.carrier not a problem? *)
abbreviation (in c_manifold_prod) "carrier \<equiv> manifold.carrier prod_charts"

lemma diff_fst:
  shows "diff k prod_charts charts1 fst"
proof
  let ?prod_atl = "c_manifold.atlas prod_charts k"
  fix x
  assume "x \<in> manifold.carrier prod_charts"
  then obtain c where c: "x \<in> domain c" "c \<in> prod_charts"
    by (meson manifold.carrierE)
  then obtain c1 c2 where c12: "c1 \<in> charts1" "c2 \<in> charts2" "c = prod_chart c1 c2"
    using prod_charts_def by force
  show "\<exists>c1 \<in> ?prod_atl. \<exists>c2 \<in> m1.atlas.
    x \<in> domain c1 \<and>
    fst ` domain c1 \<subseteq> domain c2 \<and>
    k-smooth_on (codomain c1) (apply_chart c2 \<circ> fst \<circ> inv_chart c1)"
  proof (intro bexI conjI)
    show "x \<in> domain c" "c \<in> ?prod_atl" "c1 \<in> m1.atlas"
      by (simp add: c c_manifold.in_charts_in_atlas c_manifold_atlas_product c12(1) m1.in_charts_in_atlas)+
    show "fst ` domain c \<subseteq> domain c1"
      using domain_prod_chart c12(3) by auto
    let ?f = "apply_chart c1 \<circ> fst \<circ> inv_chart c"
    let ?g = "\<lambda>(x,y). (inv_chart c1 x, inv_chart c2 y)"
    have 1: "codomain c = codomain c1 \<times> codomain c2" by (simp add: c12(3))
    then have 2: "\<And>x. x \<in> codomain c \<Longrightarrow> ?f x = fst x" using c12(3) by fastforce
    \<comment> \<open>This next step is actually stronger than what we need!
      However, since we can only obtain k-compatible charts when in a k-smooth manifold,
      the overall degree of differentiability obtainable is limited.\<close>
    have "smooth_on (codomain c1 \<times> codomain c2) ?f"
      by (auto intro!: smooth_on_cong[OF _ _ 2] smooth_on_fst simp only: 1[symmetric])
    then show "k-smooth_on (codomain c) ?f" using 1 smooth_on_le by force
  qed
qed

lemma diff_snd:
  shows "diff k prod_charts charts2 snd" 
proof
  let ?prod_atl = "c_manifold.atlas prod_charts k"
  fix x
  assume "x \<in> manifold.carrier prod_charts"
  then obtain c where "x \<in> domain c" "c \<in> prod_charts"
    by (meson manifold.carrierE)
  then obtain c1 c2 where "c = prod_chart c1 c2" "c1 \<in> charts1" "c2 \<in> charts2"
    using prod_charts_def by force
  show "\<exists>c1 \<in> ?prod_atl. \<exists>c2 \<in> m2.atlas. x \<in> domain c1 \<and> snd ` domain c1 \<subseteq> domain c2 \<and>
    k-smooth_on (codomain c1) (apply_chart c2 \<circ> snd \<circ> inv_chart c1)"
  proof (intro bexI, intro conjI)
    show "x \<in> domain c" by (simp add: \<open>x \<in> domain c\<close>)
    show "c2 \<in> m2.atlas" by (simp add: \<open>c2 \<in> charts2\<close> m2.in_charts_in_atlas)
    show "snd ` domain c \<subseteq> domain c2" using \<open>c = prod_chart c1 c2\<close> by simp
    show "c \<in> ?prod_atl"
      by (simp add: \<open>c \<in> prod_charts\<close> c_manifold.in_charts_in_atlas c_manifold_atlas_product)
    let ?f = "apply_chart c2 \<circ> snd \<circ> inv_chart c"
    have 1: "codomain c = codomain c1 \<times> codomain c2" by (simp add: \<open>c = prod_chart c1 c2\<close>)
    have 2: "\<And>x. x \<in> codomain c \<Longrightarrow> ?f x = snd x" using 1 \<open>c = prod_chart c1 c2\<close> by fastforce
    have "smooth_on (codomain c1 \<times> codomain c2) ?f"
      using 1 2 smooth_on_snd smooth_on_id open_codomain smooth_on_cong
      by (smt (verit, ccfv_threshold))
    then show "k-smooth_on (codomain c) ?f" using 1 smooth_on_le by force
  qed
qed

lemma prod_chartsI:
  assumes "c1 \<in> charts1" "c2 \<in> charts2"
  shows "prod_chart c1 c2 \<in> prod_charts"
  unfolding prod_charts_def using assms by auto

lemma prod_chart_in_atlas:
  assumes "c1 \<in> charts1" "c2 \<in> charts2"
  shows "prod_chart c1 c2 \<in> prod_manifold.atlas"
  using prod_chartsI prod_manifold.in_charts_in_atlas assms by simp

text \<open>This next lemma is in \<^locale>\<open>c_manifolds\<close>, rather than \<^locale>\<open>c_manifold_prod\<close>, so that we
  can pick and choose the charts it applies to later.\<close>
lemma (in c_manifolds) diff_const: "diff k charts1 charts2 (\<lambda>z. x)" if "x \<in> dest.carrier"
  apply (unfold_locales, auto)
  by (metis dest.atlasE image_subsetI smooth_on_const src.atlasE that)


lemma diff_Pair:
  assumes m3: "c_manifold charts3 k"
    and diff_f: "diff k charts3 charts1 f"
    and diff_g: "diff k charts3 charts2 g"
  shows "diff k charts3 prod_charts (\<lambda>x. (f x, g x))"
proof (unfold_locales)
  show "c1 \<in> charts3 \<Longrightarrow> c2 \<in> charts3 \<Longrightarrow> k-smooth_compat c1 c2" for c1 c2
    using c_manifold.pairwise_compat[OF m3] .
  let ?prod_atl = "prod_manifold.atlas"
  let ?atl3 = "c_manifold.atlas charts3 k"
  let ?m3 = "manifold.carrier charts3"
  fix x assume x[simp]: "x \<in> ?m3"
  obtain c1 c2
    where c1[simp]: "c1 \<in> charts1" "f x \<in> domain c1"
      and c2[simp]: "c2 \<in> charts2" "g x \<in> domain c2"
    using manifold.carrierE x diff.defined diff_f diff_g by (metis image_subset_iff)
  obtain c3' where c3': "c3' \<in> charts3" "x \<in> domain c3'"
    using x manifold.carrierE m3 by blast
  have open_int_f_g: "open ((f -` domain c1) \<inter> (g -` domain c2) \<inter> ?m3)"
    using diff_f diff.continuous_on diff_g open_domain manifold.open_carrier open_continuous_vimage
    by (metis (no_types, lifting) Int_lower2 inf.absorb_iff2 inf_assoc open_Int)
  then obtain c3
    where c3: "c3 \<in> ?atl3" "x \<in> domain c3"
                    "c3 = restrict_chart ((f -` domain c1) \<inter> (g -` domain c2) \<inter> ?m3) c3'"
    by (simp add: c3' c_manifold.in_charts_in_atlas c_manifold.restrict_chart_in_atlas m3)
  have c3_simps [simp]:
    "domain c3 = (f -` domain c1) \<inter> (g -` domain c2) \<inter> ?m3 \<inter> domain c3'"
    "codomain c3 = codomain c3' \<inter> inv_chart c3' -` ((f -` domain c1) \<inter> (g -` domain c2) \<inter> ?m3 \<inter> domain c3')"
    "apply_chart c3 = c3'" "inv_chart c3 = inv_chart c3'"
    using open_int_f_g c3 by auto
  let ?c = "prod_chart c1 c2"
  show "\<exists>c3 \<in> ?atl3. \<exists>c \<in> ?prod_atl.
    x \<in> domain c3 \<and> (\<lambda>x. (f x, g x)) ` domain c3 \<subseteq> domain c \<and>
    k-smooth_on (codomain c3) (c \<circ> (\<lambda>x. (f x, g x)) \<circ> inv_chart c3)"
  proof (intro bexI, intro conjI)
    show "?c \<in> ?prod_atl"
      using prod_chart_in_atlas by simp
    show "c3 \<in> ?atl3" "x \<in> domain c3"
      using c3(1,2) .
    show "(\<lambda>x. (f x, g x)) ` domain c3 \<subseteq> domain (prod_chart c1 c2)"
      by (auto simp: open_int_f_g)
    let ?f = "apply_chart ?c \<circ> (\<lambda>x. (f x, g x)) \<circ> inv_chart c3"

    have unfold_f: "\<And>y. y \<in> codomain c3 \<Longrightarrow> ?f y = (c1 (f (inv_chart c3 y)), c2 (g (inv_chart c3 y)))"
      by fastforce

    have comp_cong[simp]: "(c1 \<circ> f \<circ> inv_chart c3) z = (\<lambda>y. c1 (f (inv_chart c3 y))) z"
        "(c2 \<circ> g \<circ> inv_chart c3) z = (\<lambda>y. c2 (g (inv_chart c3 y))) z"
      if "z \<in> codomain c3" for z
      by auto

    have open_c3: "open (codomain c3)" by (simp add: c3)
    moreover have "k-smooth_on (codomain c3) (\<lambda>y. apply_chart c1 (f (inv_chart c3 y)))"
      apply (rule smooth_on_cong(1)[OF _ open_c3 comp_cong(1)[symmetric]])
      apply (rule smooth_on_cong'[OF diff.diff_chartsD[OF diff_f c3(1) m1.in_charts_in_atlas[OF c1(1)]]])
      by auto
    moreover have "k-smooth_on (codomain c3) (\<lambda>y. apply_chart c2 (g (inv_chart c3 y)))"
      apply (rule smooth_on_cong(1)[OF _ open_c3 comp_cong(2)[symmetric]])
      apply (rule smooth_on_cong'[OF diff.diff_chartsD[OF diff_g c3(1) m2.in_charts_in_atlas[OF c2(1)]]])
      by auto
    ultimately show "k-smooth_on (codomain c3) ?f"
      using smooth_on_Pair smooth_on_cong unfold_f by blast
  qed
qed

lemma diff_Pair':
  assumes m3: "c_manifold charts3 k"
    and diff_f: "diff k charts3 charts1 (fst\<circ>f)"
    and diff_g: "diff k charts3 charts2 (snd\<circ>f)"
  shows "diff k charts3 prod_charts f"
  using diff_Pair[OF assms] by simp

lemma diff_left_Pair: "diff k charts2 prod_charts (\<lambda>y. (x,y))" if "x \<in> m1.carrier"
  using diff_Pair[of charts2 "\<lambda>z. x" id]
  using c_manifold_prod_axioms unfolding c_manifold_prod_def
  using c_manifolds.diff_const[of k charts2 charts1 x] unfolding c_manifolds_def
  using m2.diff_id
  by (simp add: diff.diff_cong that)

lemma diff_right_Pair: "diff k charts1 prod_charts (\<lambda>x. (x,y))" if "y \<in> m2.carrier"
  using diff_Pair[of charts1 id "\<lambda>z. y"]
  using c_manifold_prod_axioms unfolding c_manifold_prod_def
  using c_manifolds.diff_const[of k charts1 charts2 y] unfolding c_manifolds_def
  using m1.diff_id
  by (simp add: diff.diff_cong that)

lemma (in c_manifold) diff_on_sqr_Pair:
  "diff k charts (c_manifold_prod.prod_charts charts charts) (\<lambda>x. (f x, g x))"
  if "diff k charts charts f" "diff k charts charts g"
  using c_manifold_prod.diff_Pair[OF _ _ that]
  by (simp add: c_manifold_axioms c_manifold_prod.intro)

end (* context c_manifold_prod *)


lemma smooth_on_Pair':
  "k-smooth_on S f"
  if "open S" "k-smooth_on S (fst\<circ>f)" "k-smooth_on S (snd\<circ>f)"
  for f::"_::euclidean_space\<Rightarrow>_" and g::"_::euclidean_space\<Rightarrow>_"
  using smooth_on_Pair[OF that] by simp



subsubsection \<open>Some results about Euclidean manifolds and their products.\<close>

abbreviation prod_chart_eucl::"('a\<times>'a,'a\<times>'a::euclidean_space)chart"
  where "prod_chart_eucl \<equiv> c_manifold_prod.prod_chart chart_eucl chart_eucl"

abbreviation prod_charts_eucl
  where "prod_charts_eucl \<equiv> c_manifold_prod.prod_charts charts_eucl charts_eucl"

lemma eucl_makes_product_manifold: "c_manifold_prod \<infinity> charts_eucl charts_eucl"
  by (simp add: c_manifold_prod.intro manifold_eucl.c_manifold_axioms)

lemma prod_chart_in_prod_charts: "prod_chart_eucl \<in> prod_charts_eucl"
  using c_manifold_prod.prod_chartsI eucl_makes_product_manifold
  by blast

lemma chart_eucl_id: "apply_chart chart_eucl = (\<lambda>x. x)"
  by simp

lemma inv_prod_chart_eucl_id: "inv_chart prod_chart_eucl = (\<lambda>(x,y). (x,y))"
  using c_manifold_prod.inv_chart_prod_chart [OF eucl_makes_product_manifold]
  by (simp add: \<open>\<And>c2 c1. inv_chart (c_manifold_prod.prod_chart c1 c2)
    = (\<lambda>(x, y). (inv_chart c1 x, inv_chart c2 y))\<close>)

lemma map_fun_eucl_prod_id_f: "apply_chart chart_eucl \<circ> f \<circ> inv_chart (prod_chart_eucl) = f"
proof -
  have "apply_chart chart_eucl \<circ> f = f"
    using chart_eucl_id by auto
  thus "apply_chart chart_eucl \<circ> f \<circ> inv_chart (prod_chart_eucl) = f"
    using inv_prod_chart_eucl_id
    by (metis case_prod_Pair comp_id)
qed

lemma map_fun_eucl_id_f: "apply_chart chart_eucl \<circ> f \<circ> inv_chart (chart_eucl) = f"
  by auto

lemma map_fun_eucl_prod_id: "map_fun (inv_chart (prod_chart_eucl)) (apply_chart chart_eucl) = id"
  unfolding map_fun_def
  using map_fun_eucl_prod_id_f eq_id_iff
  by auto

text \<open>Maps that are at least \<^term>\<open>diff 1\<close> between Euclidean spaces in the manifold-sense,
  are differentiable in the usual real analysis sense.\<close>
lemma diff_eucl_differentiable:
  fixes charts_eucl1 :: "('a::euclidean_space, 'a) chart set"
    and charts_eucl2 :: "('b::euclidean_space, 'b) chart set"
  defines "charts_eucl1 \<equiv> charts_eucl"
    and "charts_eucl2 \<equiv> charts_eucl"
  assumes "diff 1 charts_eucl1 charts_eucl2 f" "x \<in> manifold.carrier charts_eucl1"
  shows "f differentiable at x"
proof -
  interpret eucl1: c_manifold charts_eucl1 1 using charts_eucl1_def c1_manifold_atlas_eucl by auto
  interpret eucl2: c_manifold charts_eucl2 1 using charts_eucl2_def c1_manifold_atlas_eucl by auto

  text \<open>First, obtain some charts in which we know f is differentiable in the real analysis sense.\<close>
  obtain c1' c2'
    where c1': "c1' \<in> eucl1.atlas" "x \<in> domain c1'"
      and c2': "c2' \<in> eucl2.atlas" "f ` domain c1' \<subseteq> domain c2'"
      and f': "1-smooth_on (codomain c1') (c2' \<circ> f \<circ> inv_chart c1')"
    using assms unfolding diff_def diff_axioms_def by blast

  text \<open>Then show that smooth compatibility preserves this property in the \<^term>\<open>charts_eucl\<close> (the identity).\<close>
  obtain c1 c2 where c_eucl: "c1 = chart_eucl" "c1 \<in> charts_eucl1" "c2 = chart_eucl" "c2 \<in> charts_eucl2"
    by (simp add: charts_eucl1_def charts_eucl2_def)
  have c1: "c1 \<in> eucl1.atlas" "x \<in> domain c1"
    and c2: "c2 \<in> eucl2.atlas" "f ` domain c1 \<subseteq> domain c2"
    by (simp_all add: c_eucl(1,3) charts_eucl1_def charts_eucl2_def)
  have f: "1-smooth_on (domain c1') (c2 \<circ> f \<circ> inv_chart c1)"
  proof -
    have 1: "1-smooth_on (codomain c1') (c2 \<circ> inv_chart c2' \<circ> (c2' \<circ> f \<circ> inv_chart c1'))"
      apply (rule smooth_on_compose[OF smooth_compat_D1[of 1 c2' c2] f'])
      using c2' c2(1) by (auto simp: c_eucl(3) eucl2.atlas_is_atlas open_Int)
    have 2: "1-smooth_on (c1 ` (domain c1 \<inter> domain c1'))
        ((c2 \<circ> inv_chart c2' \<circ> (c2' \<circ> f \<circ> inv_chart c1')) \<circ> (c1' \<circ> inv_chart c1))"
      apply (rule smooth_on_compose[OF 1 smooth_compat_D1[of 1 c1 c1']])
      using c1'(1) c1(1) by (auto simp: open_Int eucl1.atlas_is_atlas c_eucl(1) image_subsetI)
    have "1-smooth_on (c1 ` (domain c1 \<inter> domain c1')) (c2 \<circ> f \<circ> inv_chart c1)"
      apply (rule smooth_on_cong[OF 2])
      using c2'(2) inv_chart_inverse by (auto simp: open_Int)
    thus ?thesis using c_eucl(1) by auto
  qed
  hence "higher_differentiable_on (domain c1') (c2 \<circ> f \<circ> inv_chart c1) 1"
    unfolding smooth_on_def by (simp add: one_enat_def)

  text \<open>Finally, put it all together: \<^term>\<open>f\<close> sandwiched between two identity maps is differentiable
    on a domain containing \<^term>\<open>x\<close>, thus \<^term>\<open>f differentiable at x\<close> in the real analysis sense.\<close>
  thus ?thesis
    using higher_differentiable_on_imp_differentiable_on differentiable_onD
    by (metis at_within_domain c1'(2) c_eucl(1,3) map_fun_eucl_id_f less_one)
qed

\<comment> \<open>A more specific version of @{thm c_manifold_prod.diff_fst} for Euclidean spaces.\<close>
lemma smooth_on_proj:
    "smooth_on (manifold.carrier prod_charts_eucl) fst"
    "smooth_on (manifold.carrier prod_charts_eucl) snd"
  using smooth_on_fst [OF smooth_on_id manifold.open_carrier]
  using smooth_on_snd [OF smooth_on_id manifold.open_carrier] by blast+

lemma eucl_add_smooth: "smooth_on (manifold.carrier prod_charts_eucl) (\<lambda>(x,y). x+y)"
  using smooth_on_add [OF smooth_on_proj manifold.open_carrier]
  by (simp add: case_prod_beta')

lemma eucl_um_smooth: "smooth_on manifold_eucl.carrier uminus"
  using smooth_on_uminus [OF smooth_on_id manifold.open_carrier]
  by blast


subsection \<open>Swapping a product manifold.\<close>
context c_manifold_prod begin

lift_definition swap_chart :: "('a \<times> 'c, 'b \<times> 'd) chart \<Rightarrow> ('c \<times> 'a, 'b \<times> 'd) chart"
  is "\<lambda>(d::('a\<times>'c) set, d'::('b\<times>'d) set, f::('a\<times>'c)\<Rightarrow>('b\<times>'d), f'::('b\<times>'d)\<Rightarrow>('a\<times>'c)).
    (prod.swap ` d, d', f \<circ> prod.swap, prod.swap \<circ> f')"
  by (auto intro: open_Times simp: open_swap homeomorphism_swap)

lemma domain_swap_chart[simp]: "domain (swap_chart c) = prod.swap ` (domain c)"
  and codomain_swap_chart[simp]: "codomain (swap_chart c) = codomain c"
  and apply_swap_chart[simp]: "apply_chart (swap_chart c) = c \<circ> prod.swap"
  and inv_chart_swap_chart[simp]: "inv_chart (swap_chart c) = prod.swap \<circ> (inv_chart c)"
  by (transfer, auto)+

lemma domain_swap_prod_chart[simp]: "domain (swap_chart (prod_chart c1 c2)) = domain c2 \<times> domain c1"
  and codomain_swap_prod_chart[simp]: "codomain (swap_chart (prod_chart c1 c2)) = codomain c1 \<times> codomain c2"
  and apply_swap_prod_chart[simp]: "apply_chart (swap_chart (prod_chart c1 c2)) = (\<lambda>(y,x). (c1 x, c2 y))"
  and inv_chart_swap_prod_chart[simp]: "inv_chart (swap_chart (prod_chart c1 c2)) = (\<lambda>(x,y). (inv_chart c2 y, inv_chart c1 x))"
  by auto

end (* context c_manifold_prod *)



subsection \<open>The diffeomorphism group of a manifold.\<close>

lemma (in diffeomorphism) diffeo_f': "diffeomorphism k charts2 charts1 f' f"
  apply unfold_locales by auto

lemma (in diffeomorphism) is_homeomorphism: "homeomorphism src.carrier dest.carrier f f'"
  by (simp add: defined homeomorphismI inv.continuous_on inv.defined local.continuous_on)

context c_manifold begin

lemma id_diffeomorphism: "diffeomorphism k charts charts id id"
proof
  fix x
  assume "x\<in>carrier"
  then obtain c where c: "c\<in>atlas" "x \<in> domain c"
    using atlasE by blast
  show "\<exists>c1\<in>atlas. \<exists>c2\<in>atlas. x \<in> domain c1 \<and> id ` domain c1 \<subseteq> domain c2 \<and>
    k-smooth_on (codomain c1) (apply_chart c2 \<circ> id \<circ> inv_chart c1)"
  proof -
    have "id ` domain c \<subseteq> domain c" "k-smooth_on (codomain c) (apply_chart c \<circ> id \<circ> inv_chart c)"
      by (simp, metis Int_absorb comp_id image_domain_eq smooth_compat_D2 smooth_compat_refl)
    thus ?thesis using c by blast
  qed
qed (simp)

lemma diffeomorphism_compose: "diffeomorphism k M1 M3 (g \<circ> f) (f' \<circ> g')"
  if "diffeomorphism k M1 M2 f f'" "diffeomorphism k M2 M3 g g'"
proof (intro diffeomorphism.intro diffeomorphism_axioms.intro conjI allI impI)
  let ?M1 = "manifold.carrier M1"
    and ?M2 = "manifold.carrier M2"
    and ?M3 = "manifold.carrier M3"
  { fix x assume x: "x\<in>?M1"
    have "f x \<in> ?M2"
      using that(1) x diff.defined[of k M1 M2 f] by (simp add: image_subset_iff diffeomorphism_def)
    thus "(f' \<circ> g') ((g \<circ> f) x) = x"
      using that by (simp add: diffeomorphism.f_inv x) }
  { fix y assume y: "y \<in> ?M3"
    have "g' y \<in> ?M2"
      using that(2) y diff.defined[of k M3 M2 g'] by (simp add: image_subset_iff diffeomorphism_def)
    thus "(g \<circ> f) ((f' \<circ> g') y) = y"
      using that by (simp add: diffeomorphism.f'_inv y) }
  show "diff k M1 M3 (g \<circ> f)" "diff k M3 M1 (f' \<circ> g')"
    using diff_compose that unfolding diffeomorphism_def by blast+
qed

end (* context c_manifold *)


lemma (in diffeomorphism) is_bij_betw: "bij_betw f src.carrier dest.carrier"
  using defined
  apply (simp add: bij_betw_def, intro conjI inj_onI)
   using f_inv f'_inv apply metis
  using f_inv f'_inv by (meson homeomorphism_image1 is_homeomorphism)

locale c_automorphism = diffeomorphism k charts charts f f'
  for k charts f f'
begin

abbreviation "carrier \<equiv> src.carrier"

lemma in_dest: "f x \<in> carrier" if "x \<in> carrier"
  using defined that by blast

lemma inverse_automorphism: "c_automorphism k charts f' f"
  by (unfold_locales, simp_all)

lemma automorphism_compose:
  assumes "c_automorphism k charts g g'"
  shows "c_automorphism k charts (g\<circ>f) (f'\<circ>g')"
proof (intro c_automorphism.intro diffeomorphism.intro diffeomorphism_axioms.intro)
  show "diff k charts charts (g \<circ> f)" "diff k charts charts (f' \<circ> g')"
    using c_automorphism_axioms assms diff_compose
    unfolding c_automorphism_def diffeomorphism_def by blast+
  fix x assume "x\<in>carrier"
  show "(f' \<circ> g') ((g \<circ> f) x) = x"
    using \<open>x \<in> carrier\<close> assms c_automorphism.axioms diffeomorphism.f_inv in_dest by fastforce
  show "(g \<circ> f) ((f' \<circ> g') x) = x"
    by (meson \<open>x \<in> carrier\<close> assms c_automorphism_def diffeomorphism.f'_inv diffeomorphism_axioms manifold_eucl.diffeomorphism_compose)
qed

lemma c_automorphism_cong:
  assumes "\<And>x. x\<in>carrier \<Longrightarrow> f x = g x"
  shows "c_automorphism k charts g f'"
proof (intro c_automorphism.intro diffeomorphism.intro diffeomorphism_axioms.intro)
  show "diff k charts charts g" "diff k charts charts f'"
    using c_automorphism_axioms assms diff_cong
    unfolding c_automorphism_def diffeomorphism_def by blast+
  fix x assume "x\<in>carrier"
  show "f' (g x) = x"
    using \<open>x \<in> carrier\<close> assms f_inv by presburger
  show "g (f' x) = x"
    by (metis \<open>x \<in> carrier\<close> assms f'_inv image_subset_iff inv.defined)
qed

lemma automorphism_cong':
  assumes "\<And>x. x\<in>carrier \<Longrightarrow> f' x = g x"
  shows "c_automorphism k charts f g"
proof (intro c_automorphism.intro diffeomorphism.intro diffeomorphism_axioms.intro)
  show "diff k charts charts g" "diff k charts charts f"
    using c_automorphism_axioms assms
    unfolding c_automorphism_def diffeomorphism_def by (simp add: inv.diff_cong)+
  fix x assume "x\<in>carrier"
  show "f (g x) = x"
    using \<open>x \<in> carrier\<close> assms f'_inv by presburger
  show "g (f x) = x"
    by (metis \<open>x \<in> carrier\<close> assms f_inv image_subset_iff defined)
qed

end (* c_automorphism *)


text \<open>Now define an automorphism (of a \<^locale>\<open>c_manifold\<close>) as a partial function
  (whose domain is the carrier set) which is also a \<^locale>\<open>c_automorphism\<close>.\<close>
context c_manifold begin

definition automorphism :: "('a\<rightharpoonup>'a) \<Rightarrow> bool"
  where "automorphism f \<equiv> (\<exists>f'. c_automorphism k charts (\<lambda>x. the (f x)) f') \<and> dom f = carrier"

lemma automorphismD [dest]:
  assumes "automorphism f"
  shows "\<exists>f'. c_automorphism k charts (\<lambda>x. the (f x)) f'"
    and "dom f = carrier"
  using assms by (auto simp: automorphism_def)

lemma automorphismD2:
  assumes "automorphism f"
  obtains f' where "c_automorphism k charts (\<lambda>x. the (f x)) f'"
  using automorphismD(1)[OF assms] by blast

lemma automorphismI [intro]:
  assumes "\<exists>f'. c_automorphism k charts (\<lambda>x. the (f x)) f'"
    and "dom f = carrier"
  shows "automorphism f"
  using assms by (auto simp: automorphism_def)

lemma automorphism_partial_id: "automorphism (\<lambda>x. if x \<in> carrier then Some x else None)"
  (is "automorphism ?part_id")
proof (intro automorphismI exI c_automorphism.intro)
  have part_id_on_carrier: "(\<lambda>x. the (?part_id x)) y = id y" if "y\<in>carrier" for y
    by (simp add: that)
  show "diffeomorphism k charts charts (\<lambda>x. the (?part_id x)) id"
    apply (intro diffeomorphism.intro diffeomorphism_axioms.intro)
    subgoal using diff_id diff.diff_cong[of k charts charts] part_id_on_carrier by force
    subgoal using diff_id eq_id_iff by metis
    by simp+
  show "dom ?part_id = carrier" using domIff by fastforce
qed

lemma automorphism_openin:
  assumes "automorphism f" "openin (top_of_set carrier) S"
  shows "openin (top_of_set carrier) (the ` f ` S)"
  using assms diffeomorphism.is_homeomorphism homeomorphism_imp_open_map
  unfolding automorphism_def c_automorphism_def
  by (metis (no_types, lifting) image_cong image_image)

lemma obtain_inverse_aut:
  assumes "automorphism f"
  obtains f' where "automorphism f'"
    and "\<And>x. x \<in> carrier \<Longrightarrow> the (f' (the (f x))) = x"
    and "\<And>x. x \<in> carrier \<Longrightarrow> the (f (the (f' x))) = x"
proof -
  let ?g = "\<lambda>x. the (f x)"
  obtain g' where g': "c_automorphism k charts ?g g'" and dom_f: "dom f = carrier"
    using assms automorphismD by auto
  let ?f' = "\<lambda>y::'a. if y\<in>carrier then Some (g' y) else None"
  have dom_f': "dom ?f' = carrier" using subset_iff by fastforce
  have unwrap_the: "(\<lambda>x. the (?f' x)) y = g' y" if "y \<in> carrier" for y using that by auto
  {
    fix x assume "x \<in> carrier"
    have "automorphism ?f'" "the (?f' (the (f x))) = x" "the (f (the (?f' x))) = x"
    proof -
      have diff_f': "diff k charts charts (\<lambda>x. the (?f' x))"
        using c_automorphism.inverse_automorphism[OF g'] diff.diff_cong
        unfolding c_automorphism_def diffeomorphism_def
        by fastforce

      text \<open>Finding an inverse diffeomorphism is the main part of this proof.\<close>
      have diffeo_f': "diffeomorphism k charts charts (\<lambda>x. the (?f' x)) (\<lambda>x. the (f x))"
        apply (intro diffeomorphism.intro diffeomorphism_axioms.intro conjI)
        subgoal using diff_f' .
        subgoal using assms unfolding automorphism_def c_automorphism_def diffeomorphism_def by simp
        subgoal by (simp, metis c_automorphism.axioms(1) diffeomorphism.f'_inv g')
        subgoal using c_automorphism.in_dest diffeomorphism.f_inv g' by (simp add: c_automorphism_def, blast)
        done

      show "automorphism ?f'"
        apply (intro automorphismI exI[of _ "\<lambda>x. the (f x)"])
        by (auto intro: c_automorphism.intro simp: dom_f' diffeo_f')
      show "the (?f' (the (f x))) = x"
        using \<open>x \<in> carrier\<close> diffeo_f' diffeomorphism.f'_inv by blast
      show "the (f (the (?f' x))) = x"
        using \<open>x \<in> carrier\<close> diffeo_f' diffeomorphism.f_inv by blast
    qed }
  thus ?thesis using that assms by blast
qed

lemma aut_cong:
  assumes "automorphism f"
    and "\<And>x. x\<in>carrier \<Longrightarrow> f x = g x" "dom g = carrier"
  shows "automorphism g"
  apply (intro automorphismI)
  using c_automorphism.c_automorphism_cong by (metis assms(1,2) automorphism_def, simp add: assms(3))

lemma aut_comp_simps [simp]: "(g \<circ>\<^sub>m f) x = (g (the (f x)))"
    "automorphism g \<Longrightarrow> \<exists>z\<in>carrier. Some z = (g \<circ>\<^sub>m f) x"
  if "x \<in> carrier" "automorphism f" for x
  subgoal by (metis automorphismD(2) domIff map_comp_simps(2) option.exhaust_sel that)
  subgoal using that automorphismD domIff map_comp_simps
    by (smt (verit, del_insts) c_automorphism.in_dest option.exhaust_sel)
  done

lemma aut_to [simp]: "the (f x) \<in> carrier" if "automorphism f" "x \<in> carrier"
  by (metis (mono_tags, lifting) c_manifold.aut_comp_simps c_manifold.automorphismD(2) c_manifold_axioms domI that)

lemma automorphism_ran: "ran f = carrier" if "automorphism f"
  unfolding ran_def apply (intro subset_antisym subsetI)
  using automorphismD(2) aut_to mem_Collect_eq option.sel that
  by (smt (verit) domIff domD option.distinct(1) obtain_inverse_aut)+

lemma aut_comp:
  assumes "automorphism f" "automorphism g"
  shows "automorphism (g \<circ>\<^sub>m f)"
proof (intro automorphismI)

  obtain f' where f': "c_automorphism k charts (\<lambda>x. the (f x)) f'" and domf: "dom f = carrier"
    using automorphismD[OF assms(1)] by blast
  obtain g' where g': "c_automorphism k charts (\<lambda>x. the (g x)) g'" and domg: "dom g = carrier"
    using automorphismD[OF assms(2)] by blast

  show dom_comp: "dom (g \<circ>\<^sub>m f) = carrier"
    using map_comp_dom automorphism_ran by (metis assms(1) domf domg subsetI)

  have "c_automorphism k charts (\<lambda>x. the (g (the (f x)))) (f' \<circ> g')"
    using c_automorphism.automorphism_compose[OF f' g'] c_automorphism.c_automorphism_cong
    by fastforce
  thus "\<exists>f'. c_automorphism k charts (\<lambda>x. the ((g \<circ>\<^sub>m f) x)) f'"
    by (auto intro: exI[of _ "f' \<circ> g'"] simp: assms(1) c_automorphism.c_automorphism_cong)
qed

definition "Diff \<equiv> {f. automorphism f}"

lemma DiffD [dest]: "f \<in> Diff \<Longrightarrow> automorphism f" by (simp add: Diff_def)
lemma DiffI [intro]: "automorphism f \<Longrightarrow> f \<in> Diff" by (simp add: Diff_def)

abbreviation (input) Diff_comp::"('a\<rightharpoonup>'a) \<Rightarrow> ('a\<rightharpoonup>'a) \<Rightarrow> ('a\<rightharpoonup>'a)" where "Diff_comp \<equiv> map_comp"
abbreviation (*input*) "Diff_id x \<equiv> if x\<in>carrier then Some x else None"
(* abbreviation (input) "Diff_inv x \<equiv> res (SOME y. )" *)

lemma Diff_grp: "grp_on Diff Diff_comp Diff_id"
proof (unfold_locales)

  show assoc: "Diff_comp (Diff_comp a b) c = Diff_comp a (Diff_comp b c)"
    if asms: "a \<in> Diff" "b \<in> Diff" "c \<in> Diff" for a b c
    using map_comp_assoc by blast

  show id_comp: "Diff_comp Diff_id a = a \<and> Diff_comp a Diff_id = a" if "a \<in> Diff" for a
    apply (standard; standard)
    subgoal
      using automorphismD[OF DiffD[OF that]] c_automorphism.in_dest
      by (smt (verit, del_insts) domIff map_comp_simps(1) map_comp_simps(2) option.collapse)
    subgoal
      using automorphismD[OF DiffD[OF that]] c_automorphism.in_dest
      by (smt (verit, ccfv_threshold) domIff map_comp_simps(1) map_comp_simps(2))
    done

  show id_mem: "Diff_id \<in> Diff"
    by (auto simp: automorphism_partial_id)

  { fix x y assume x: "x\<in>Diff" and y: "y\<in>Diff"
    show "Diff_comp x y \<in> Diff"
      using aut_comp DiffD x y by auto }

  { fix f assume f: "f\<in>Diff"
    obtain g where g: "g\<in>Diff" "\<forall>x \<in> carrier. the (g (the (f x))) = x" "\<forall>x \<in> carrier. the (f (the (g x))) = x"
      using obtain_inverse_aut[OF DiffD[OF f]] by (metis DiffI)
    have "\<exists>g\<in>Diff. Diff_comp f g = Diff_id \<and> Diff_comp g f = Diff_id"
      apply (intro bexI[OF _ g(1)])
      using g aut_comp_simps(1) aut_to
      by (metis (opaque_lifting) DiffD automorphismD(2) domIff f map_comp_simps(1) option.collapse) }
  thus "\<forall>x\<in>Diff. \<exists>y\<in>Diff. Diff_comp x y = Diff_id \<and> Diff_comp y x = Diff_id" by blast
qed

sublocale Diff_grp: grp_on Diff Diff_comp Diff_id
  by (rule Diff_grp)

abbreviation "Diff_inv \<equiv> Diff_grp.invs"
abbreviation "Diff_comp_inv \<equiv> Diff_grp.mns"

end



section \<open>Coordinates and isomorphisms of tangent spaces\<close>

text \<open>To work with local coordinates, we fix an atlas chart on a manifold.\<close>
locale c_manifold_local = c_manifold +
  fixes \<psi> assumes \<psi> [simp]: "\<psi> \<in> atlas"
begin

sublocale sub_\<psi>: submanifold charts k "domain \<psi>"
  by (unfold_locales, simp)

lemma sub_\<psi>_carrier: "sub_\<psi>.sub.carrier = domain \<psi>"
  unfolding sub_\<psi>.sub.carrier_def charts_submanifold_def manifold.carrier_def by (auto, meson \<psi> carrierE in_carrier_atlasI)

lemma sub_\<psi>: "\<psi> \<in> sub_\<psi>.sub.atlas"
  by (metis \<psi> atlas_is_atlas c_manifold.maximal_atlas equalityE sub_\<psi>.sub.c_manifold_axioms sub_\<psi>.submanifold_atlasE sub_\<psi>_carrier)

text \<open>Although the inclusion is not a diffeomorphism, the push-forward still defines a vector
  isomorphism. Therefore, it has an inverse.\<close>
notation sub_\<psi>.inclusion.push_forward (\<open>d\<iota>\<close>)

lemma (in c_manifold) diffeomorphism_chart:
  assumes c: "c \<in> atlas"
  shows "diffeomorphism k (charts_submanifold (domain c)) (manifold_eucl.charts_submanifold (codomain c)) (apply_chart c) (inv_chart c)"
proof -
  have sub_c_carrier: "manifold.carrier (charts_submanifold (domain c)) = domain c"
    using c c_manifold_axioms c_manifold_local.sub_\<psi>_carrier c_manifold_local_axioms.intro c_manifold_local_def by blast
  interpret diff_c: diff k "charts_submanifold (domain c)" charts_eucl c
    using diff_apply_chart[OF c] .
  interpret diff_c_inv: diff k "manifold_eucl.charts_submanifold (codomain c)" charts "inv_chart c"
    using diff_inv_chart[OF c] .
  have diff_c_inv_carrier [simp]: "diff_c_inv.src.carrier = codomain c"
    unfolding diff_c_inv.src.carrier_def manifold_eucl.dest.charts_submanifold_def manifold.carrier_def by auto
  show "diffeomorphism k (charts_submanifold (domain c)) (manifold_eucl.charts_submanifold (codomain c)) c (inv_chart c)"
    apply (unfold diffeomorphism_def, intro conjI)
    subgoal by (auto intro: diff_c.diff_submanifold2 simp: sub_c_carrier)
    subgoal by (auto intro: diff_c_inv.diff_submanifold2)
  by (unfold_locales, simp_all add: sub_c_carrier)
qed

sublocale diffeo_\<psi>: diffeomorphism k "charts_submanifold (domain \<psi>)" "manifold_eucl.charts_submanifold (codomain \<psi>)" \<psi> "inv_chart \<psi>"
  using diffeomorphism_chart by auto

lemma diffeo_\<psi>_inv: "diffeomorphism k (manifold_eucl.charts_submanifold (codomain \<psi>)) (charts_submanifold (domain \<psi>)) (inv_chart \<psi>) \<psi>"
  using diffeo_\<psi>.diffeo_f' .

abbreviation differential_apply_chart :: "(('a\<Rightarrow>real)\<Rightarrow>real) \<Rightarrow> (('b\<Rightarrow>real)\<Rightarrow>real)" (\<open>d\<psi>\<close>)
  where (*[simp]:*) "differential_apply_chart \<equiv> diffeo_\<psi>.push_forward"

abbreviation differential_inv_chart :: "(('b\<Rightarrow>real)\<Rightarrow>real) \<Rightarrow> (('a\<Rightarrow>real)\<Rightarrow>real)" (\<open>d\<psi>\<inverse>\<close>)
  where (*[simp]:*) "differential_inv_chart \<equiv> diffeo_\<psi>.inv.push_forward"

sublocale diff_fun_\<psi>: diff_fun k "charts_submanifold (domain \<psi>)" \<psi>
  using diff_apply_chart[OF \<psi>] by (simp add: diff_fun.intro)

sublocale sub_eucl: submanifold charts_eucl k "codomain \<psi>"
  apply unfold_locales by simp

notation sub_eucl.inclusion.push_forward (\<open>d\<kappa>\<close>)

text \<open>Inverses for the pushforward under the inclusion.
  If we are to ``glue together'' coordinate charts on multiple domains, these pushforwards need
  to coordinatise tangent spaces over a small neighbourhood on the manifold (a thin bundle).\<close>

abbreviation differential_inclusion_inv_at (\<open>d\<iota>\<inverse>\<close>)
  where "d\<iota>\<inverse> p \<equiv> restrict0 (tangent_space p) (the_inv_into (sub_\<psi>.sub.tangent_space p) d\<iota>)"

abbreviation differential_inclusion_eucl_inv_at (\<open>d\<kappa>\<inverse>\<close>)
  where "d\<kappa>\<inverse> p \<equiv> restrict0 (manifold_eucl.tangent_space k (\<psi> p)) (the_inv_into (diffeo_\<psi>.dest.tangent_space (\<psi> p)) d\<kappa>)"

end


locale c_manifold_point = c_manifold_local +
  fixes p assumes p [simp]: "p\<in>domain \<psi>"
begin

text \<open>Given local coordinates from a chart \<^term>\<open>\<psi>\<close> on a manifold,
  we can coordinatize the tangent space at any point \<^term>\<open>p\<close> contained in the \<^term>\<open>domain \<psi>\<close>.\<close>
abbreviation "T\<^sub>pM \<equiv> tangent_space p"
abbreviation "T\<^sub>pU \<equiv> sub_\<psi>.sub.tangent_space p"
abbreviation "T\<^sub>\<psi>\<^sub>pE \<equiv> manifold_eucl.tangent_space k (\<psi> p)"
abbreviation "T\<^sub>\<psi>\<^sub>p\<psi>U \<equiv> diffeo_\<psi>.dest.tangent_space (\<psi> p)"
abbreviation dRestr (\<open>d\<kappa>\<inverse>\<close>) where "dRestr \<equiv> differential_inclusion_eucl_inv_at p"
abbreviation dRestr2 (\<open>d\<iota>\<inverse>\<close>) where "dRestr2 \<equiv> differential_inclusion_inv_at p"

lemma \<psi>p_in [simp]: "\<psi> p \<in> diffeo_\<psi>.dest.carrier"
  using diffeo_\<psi>.defined sub_\<psi>_carrier by force

lemma bij_betw_directional_derivative: "bij_betw (directional_derivative k (\<psi> p)) UNIV T\<^sub>\<psi>\<^sub>pE" if "k=\<infinity>"
  unfolding bij_betw_def using that
  by (simp add: inj_on_directional_derivative surj_directional_derivative)

end


lemma (in c_manifold) c_manifold_point:
  assumes "c \<in> atlas" "p \<in> domain c"
  shows "c_manifold_point charts k c p"
  using assms by unfold_locales (simp_all)


subsection \<open>Results extracted from \<^theory>\<open>Smooth_Manifolds.Tangent_Space\<close>.\<close>
text \<open>Some of the proofs in the above theory are quite long, and contain statements that
  may be useful outside that proof.
  Some proofs in this subsection are due to Immler \& Zhan \cite{Smooth_Manifolds-AFP}.\<close>

definition (in c_manifold_point) coord_fun where "coord_fun X i = X (\<lambda>x. (x - (\<psi> p)) \<bullet> i)"

lemma (in c_manifold_point) euclidean_tangent_space_coordinatesE:
  fixes X
  defines "v \<equiv> coord_fun X"
  assumes "X \<in> manifold_eucl.tangent_space k (\<psi> p)" "k=\<infinity>"
  shows "X = directional_derivative k (\<psi> p) (\<Sum>i\<in>Basis. v i *\<^sub>R i)"
\<comment> \<open>Extracted from Immler and Zhan's @{thm surj_directional_derivative}.\<close>
proof -
  have linear_X: "manifold_eucl.linear_diff_fun k X"
    by (rule manifold_eucl.tangent_space_linear_on) fact
  note X_sum = manifold_eucl.diff_fun_space.linear_sum'[OF _ _ linear_X]
  note X_add = manifold_eucl.diff_fun_space.linear_add[OF _ _ _ linear_X]
  note X_scale = manifold_eucl.diff_fun_space.linear_scale[OF _ _ linear_X]
  have X_is_derivative: "X f = directional_derivative k (apply_chart \<psi> p) (\<Sum>i\<in>Basis. v i *\<^sub>R i) f"
    if f: "f \<in> manifold_eucl.dest.diff_fun_space" for f
  proof -
    (* fix f::"'b \<Rightarrow> real"
    assume f: "f \<in> manifold_eucl.dest.diff_fun_space" *)
    have "smooth_on UNIV f" using \<open>k = \<infinity>\<close> f
      by simp
    from smooth_on_Taylor2E[OF this, of "\<psi> p"]
    obtain g where f_exp:
      "\<And>x. f x = f (\<psi> p) + frechet_derivative f (at (\<psi> p)) (x - (\<psi> p)) +
        (\<Sum>i\<in>Basis. \<Sum>j\<in>Basis. (x - (\<psi> p)) \<bullet> j * ((x - (\<psi> p)) \<bullet> i) * g i j x)"
      and g: "\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> smooth_on UNIV (g i j)"
      by auto
    note [simp] = assms(3)
    have *: "X (\<lambda>x. \<Sum>i\<in>Basis. \<Sum>j\<in>Basis. (x - (\<psi> p)) \<bullet> j * ((x - (\<psi> p)) \<bullet> i) * g i j x) = 0"
      apply (subst X_sum[unfolded sum_fun_def], safe)
      subgoal by auto
      subgoal by (auto intro!: smooth_on_sum smooth_on_mult smooth_on_inner smooth_on_minus simp: g)
      apply (intro sum.neutral ballI)
      apply (subst X_sum[unfolded sum_fun_def])
      subgoal by (auto intro!: smooth_on_mult smooth_on_inner smooth_on_minus g)
      subgoal by (auto intro!: smooth_on_mult smooth_on_inner smooth_on_minus g)
    proof (intro sum.neutral ballI)
      fix i j::'b
      assume ij: "i \<in> Basis" "j \<in> Basis"
      have "X (\<lambda>xb. (xb - (\<psi> p)) \<bullet> j * ((xb - (\<psi> p)) \<bullet> i) * g i j xb) =
        X ((\<lambda>xb. (xb - (\<psi> p)) \<bullet> j) * (\<lambda>xb. ((xb - (\<psi> p)) \<bullet> i) * g i j xb))"
        by (auto simp: times_fun_def ac_simps)
      also have "\<dots> = 0"
        apply (rule manifold_eucl.derivation_times_eq_zeroI)
            apply fact
        subgoal
          by (auto intro!: smooth_on_sum smooth_on_mult smooth_on_inner smooth_on_minus)
        subgoal
          by (auto intro!: smooth_on_mult smooth_on_inner smooth_on_minus g ij)
         apply auto
        done
      finally
      show "X (\<lambda>xb. (xb - (\<psi> p)) \<bullet> j * ((xb - (\<psi> p)) \<bullet> i) * g i j xb) = 0"
        by simp
    qed
    from f have "smooth_on UNIV f"
      by (auto )
    have "f differentiable at (\<psi> p)"
      apply (rule differentiable_onD)
       apply (rule smooth_on_imp_differentiable_on)
        apply fact
      by auto
    interpret Df: linear "frechet_derivative f (at (\<psi> p))"
      apply (rule linear_frechet_derivative)
      by fact
    have X_mult_right: "k-smooth_on UNIV xx \<Longrightarrow> X (\<lambda>x. xx x * cc) = X xx * cc" for xx cc
      using X_scale[unfolded scaleR_fun_def, simplified, of xx cc]
      by (auto simp: ac_simps)
    have blf: "bounded_linear (frechet_derivative f (at (\<psi> p)))"
      apply (rule has_derivative_bounded_linear)
      apply (rule frechet_derivative_worksI)
      apply fact
      done
    note smooth_on_frechet = smooth_on_compose[OF bounded_linear.smooth_on[OF blf], unfolded o_def, OF _ _ open_UNIV subset_UNIV]
    have **: "X (\<lambda>x. frechet_derivative f (at (\<psi> p)) (x - (\<psi> p))) = frechet_derivative f (at (\<psi> p)) (\<Sum>i\<in>Basis. v i *\<^sub>R i)"
      unfolding assms(1) coord_fun_def
      apply (subst frechet_derivative_componentwise)
      subgoal by fact
      apply (subst X_sum[unfolded sum_fun_def])
      subgoal by (auto intro!: smooth_on_sum smooth_on_mult smooth_on_inner smooth_on_minus)
      subgoal by (auto intro!: smooth_on_frechet smooth_on_minus smooth_on_mult smooth_on_inner)
      apply (subst X_mult_right)
      subgoal by (auto intro!: smooth_on_sum smooth_on_mult smooth_on_inner smooth_on_minus)
      apply (subst Df.sum)
      apply (rule sum.cong, rule refl)
      apply (subst Df.scaleR)
      apply auto
      done

    show "X f = directional_derivative k (\<psi> p) (\<Sum>i\<in>Basis. v i *\<^sub>R i) f"
      apply (subst f_exp[abs_def])
      apply (subst X_add[unfolded plus_fun_def])
      subgoal by simp
      subgoal by (auto intro!: smooth_on_add smooth_on_frechet smooth_on_minus)
      subgoal
        by (auto intro!: smooth_on_add smooth_on_sum smooth_on_mult smooth_on_inner g smooth_on_minus)
      apply (subst X_add[unfolded plus_fun_def])
      subgoal by auto
      subgoal by (auto intro!: smooth_on_add smooth_on_frechet smooth_on_minus)
      subgoal by (auto intro!: smooth_on_frechet smooth_on_minus)
      apply (subst manifold_eucl.derivation_const_eq_zero[where c="f (\<psi> p)" and X=X, simplified], fact)
      apply (subst *)
      apply simp
      using f
      by (simp add: directional_derivative_def **)
  qed

  show "X = directional_derivative k (\<psi> p) (\<Sum>i\<in>Basis. v i *\<^sub>R i)"
    apply (rule ext_extensional0)
    using assms(2)
      apply (rule manifold_eucl.tangent_space_restrict)
     apply (rule extensional0_directional_derivative)
    apply (rule X_is_derivative) .
qed

text \<open>Applying a tangent vector (in $T_{\psi(p)}\mathbb R^n$) to the coordinate functions of the
  Euclidean space yields components of the tangent vector in the basis of the directional derivatives.\<close>
lemma (in c_manifold_point) directional_derivative_inverse:
  defines "D \<equiv> directional_derivative k (\<psi> p)"
    and "Di \<equiv> \<lambda>X :: ('b \<Rightarrow> real) \<Rightarrow> real. (\<Sum>i\<in>Basis. coord_fun X i *\<^sub>R i)"
  assumes k: "k=\<infinity>"
  shows "\<And>X. X \<in> T\<^sub>\<psi>\<^sub>pE \<Longrightarrow> D (Di X) = X"
    and "\<And>v. Di (D v) = v"
    and "bij_betw Di T\<^sub>\<psi>\<^sub>pE UNIV"
proof -
  show 1: "\<And>X. X \<in> T\<^sub>\<psi>\<^sub>pE \<Longrightarrow> D (Di X) = X"
    using assms euclidean_tangent_space_coordinatesE by simp

  { fix v
    have "(directional_derivative k (\<psi> p) v (\<lambda>x. (x - \<psi> p) \<bullet> i)) =
        frechet_derivative (\<lambda>x. (x - \<psi> p) \<bullet> i) (at (\<psi> p)) v" for i :: 'b
      apply (intro directional_derivative_eq_frechet_derivative)
      by (auto intro!: smooth_on_inner smooth_on_minus simp: smooth_on_const smooth_on_id)
    moreover have "((\<lambda>x. (x - \<psi> p) \<bullet> i) has_derivative (\<lambda>h. h \<bullet> i)) (at (\<psi> p))" for i :: 'b
      apply (rule has_derivative_eq_rhs)
      apply (rule has_derivative_inner)
      apply (rule has_derivative_diff)
      apply (rule has_derivative_ident)
      apply (rule has_derivative_const)+
      by simp
    ultimately have "(\<Sum>i\<in>Basis. directional_derivative k (\<psi> p) v (\<lambda>x. (x - \<psi> p) \<bullet> i) *\<^sub>R i) = (\<Sum>i\<in>Basis. (v \<bullet> i) *\<^sub>R i)"
      by (metis (no_types, lifting) frechet_derivative_at)
    then show "Di (D v) = v"
      unfolding assms(1,2) coord_fun_def by (simp add: euclidean_representation)
  } note 2 = this

  show "bij_betw Di T\<^sub>\<psi>\<^sub>pE UNIV"
    apply (rule bij_betw_if_inverse)
    using bij_betw_directional_derivative[OF k] 1 2 D_def by auto
qed



subsection \<open>\<^term>\<open>d\<psi>\<close> is an isomorphism \<^term>\<open>T\<^sub>pM\<rightarrow>T\<^sub>\<psi>\<^sub>pE\<close>.\<close>

context c_manifold_point begin

text \<open>The map \<^term>\<open>d\<psi>\<close> is \<^term>\<open>linear\<close> (i.e. linear on the type universe) because functions
  add and scale. However, because there are many smooth functions on $M$ that are not equal on $M$,
  but are equal on a strict submanifold $U$, it is not bijective (isomorphic) between universes, but only
  between the tangent spaces (i.e. \<^term>\<open>extensional0\<close> functions) it is actually meant to act on.\<close>

lemma linear_on_d\<psi>: "linear_on T\<^sub>pM T\<^sub>\<psi>\<^sub>pE scaleR scaleR d\<psi>"
  apply (intro linear_imp_linear_on)
  using diffeo_\<psi>.linear_push_forward subspace_tangent_space manifold_eucl.subspace_tangent_space .

lemma linear_on_d\<psi>': "linear_on T\<^sub>pU T\<^sub>\<psi>\<^sub>p\<psi>U scaleR scaleR d\<psi>"
  by (unfold_locales, simp_all add: diffeo_\<psi>.linear_push_forward linear_add linear_cmul)

lemma linear_on_d\<psi>_inv: "linear_on T\<^sub>\<psi>\<^sub>pE T\<^sub>pM scaleR scaleR d\<psi>\<inverse>"
  by (unfold_locales, simp_all add: diffeo_\<psi>.inv.linear_push_forward linear_add linear_cmul)

lemma linear_on_d\<psi>_inv': "linear_on T\<^sub>\<psi>\<^sub>p\<psi>U T\<^sub>pU scaleR scaleR d\<psi>\<inverse>"
  by (unfold_locales, simp_all add: diffeo_\<psi>.inv.linear_push_forward linear_add linear_cmul)

lemma bij_betw_d\<psi>: "bij_betw d\<psi> (sub_\<psi>.sub.tangent_space p) (diffeo_\<psi>.dest.tangent_space (\<psi> p))"
  using diffeo_\<psi>.bij_betw_push_forward sub_\<psi>_carrier p by blast

lemma bij_betw_d\<psi>_inv: "bij_betw d\<psi>\<inverse> (diffeo_\<psi>.dest.tangent_space (\<psi> p)) (sub_\<psi>.sub.tangent_space p)"
  using diffeomorphism.bij_betw_push_forward[OF diffeo_\<psi>.diffeo_f', of "\<psi> p", simplified]
    diffeo_\<psi>.defined p sub_\<psi>_carrier by blast

lemma inverse_d\<psi>:
  shows "v \<in> (sub_\<psi>.sub.tangent_space p) \<Longrightarrow> d\<psi>\<inverse> (d\<psi> v) = v"
        "u \<in> (diffeo_\<psi>.dest.tangent_space (\<psi> p)) \<Longrightarrow> d\<psi> (d\<psi>\<inverse> u) = u"
  using diffeo_\<psi>.push_forward_inverse diffeo_\<psi>.inv_push_forward_inverse diffeo_\<psi>.defined p sub_\<psi>_carrier by blast+

end (* c_manifold_point *)



context c_manifold_local begin

text \<open>The map \<^term>\<open>d\<psi>\<close> is \<^term>\<open>linear\<close> (i.e. linear on the type universe) because functions
  add and scale. However, because there are many smooth functions on $M$ that are not equal on $M$,
  but are equal on a strict submanifold $U$, it is not bijective (isomorphic) between universes, but only
  between the tangent spaces (i.e. \<^term>\<open>extensional0\<close> functions) it is actually meant to act on.\<close>

lemma linear_on_d\<psi>: "linear_on (tangent_space p) (diffeo_\<psi>.dest.tangent_space (\<psi> p)) scaleR scaleR d\<psi>"
  by (unfold_locales, simp_all add: diffeo_\<psi>.linear_push_forward linear_add linear_cmul)

lemma bij_betw_d\<psi>: "bij_betw d\<psi> (sub_\<psi>.sub.tangent_space p) (diffeo_\<psi>.dest.tangent_space (\<psi> p))"
  if "p\<in>domain \<psi>" for p
  using diffeo_\<psi>.bij_betw_push_forward sub_\<psi>_carrier that by blast

lemma bij_betw_d\<psi>_inv: "bij_betw d\<psi>\<inverse> (diffeo_\<psi>.dest.tangent_space (\<psi> p)) (sub_\<psi>.sub.tangent_space p)"
  if "p\<in>domain \<psi>" for p
  using diffeomorphism.bij_betw_push_forward[OF diffeo_\<psi>.diffeo_f', of "\<psi> p"]
    diffeo_\<psi>.defined that sub_\<psi>_carrier by simp

lemma inverse_d\<psi>:
  assumes "p\<in>domain \<psi>"
  shows "v \<in> (sub_\<psi>.sub.tangent_space p) \<Longrightarrow> d\<psi>\<inverse> (d\<psi> v) = v"
        "u \<in> (diffeo_\<psi>.dest.tangent_space (\<psi> p)) \<Longrightarrow> d\<psi> (d\<psi>\<inverse> u) = u"
  using diffeo_\<psi>.push_forward_inverse diffeo_\<psi>.inv_push_forward_inverse diffeo_\<psi>.defined assms sub_\<psi>_carrier by blast+

end (* c_manifold_local *)


subsection \<open>\<^term>\<open>d\<iota>\<close> is an isomorphism \<^term>\<open>T\<^sub>pU\<rightarrow>T\<^sub>pM\<close>\<close>

context submanifold begin

lemma tangent_submanifold_isomorphism:
  assumes "p\<in>sub.carrier"
  shows bij_betw_d\<iota>: "bij_betw inclusion.push_forward (sub.tangent_space p) (tangent_space p)"
    and linear_on_d\<iota>: "linear_on (sub.tangent_space p) (tangent_space p) scaleR scaleR inclusion.push_forward"
  using inj_on_push_forward_inclusion[OF assms] inclusion.push_forward_in_tangent_space[OF assms] surj_on_push_forward_inclusion[OF assms]
  apply (auto simp: bij_betw_def)[1] by (rule linear_on_push_forward_inclusion)

lemma bij_betw_d\<iota>_inv:
  fixes p and d\<iota>_inv
  defines "d\<iota>_inv \<equiv> restrict0 (tangent_space p) (the_inv_into (sub.tangent_space p) inclusion.push_forward)"
  assumes "p\<in>sub.carrier"
  shows "bij_betw d\<iota>_inv (tangent_space p) (sub.tangent_space p)"
  using bij_betw_the_inv_into[OF tangent_submanifold_isomorphism(1)] assms by (simp add: bij_betw_restrict0)

lemma linear_on_d\<iota>_inv:
  fixes p and d\<iota>_inv
  defines "d\<iota>_inv \<equiv> restrict0 (tangent_space p) (the_inv_into (sub.tangent_space p) inclusion.push_forward)"
  assumes "p\<in>sub.carrier"
  shows "linear_on (tangent_space p) (sub.tangent_space p) scaleR scaleR d\<iota>_inv"
  using linear_on_the_inv_into[OF linear_on_push_forward_inclusion tangent_submanifold_isomorphism(1)] assms
  by (simp add: linear_on_restrict0)

end


context c_manifold_point begin

lemma tangent_submanifold_isomorphism:
  shows bij_betw_d\<iota>: "bij_betw d\<iota> T\<^sub>pU T\<^sub>pM"
    and linear_on_d\<iota>: "linear_on T\<^sub>pU T\<^sub>pM scaleR scaleR d\<iota>"
  using sub_\<psi>_carrier p apply (simp only: bij_betw_def, intro conjI)
  subgoal using sub_\<psi>.inj_on_push_forward_inclusion by blast
  subgoal using sub_\<psi>.inclusion.push_forward_in_tangent_space sub_\<psi>.surj_on_push_forward_inclusion
    by (simp add: subset_antisym)
  subgoal by (rule sub_\<psi>.linear_on_push_forward_inclusion)
  done

lemma bij_betw_d\<iota>_inv: "bij_betw d\<iota>\<inverse> T\<^sub>pM T\<^sub>pU"
  using bij_betw_the_inv_into[OF tangent_submanifold_isomorphism(1)] by (simp add: bij_betw_restrict0)

lemma linear_on_d\<iota>_inv: "linear_on T\<^sub>pM T\<^sub>pU scaleR scaleR d\<iota>\<inverse>"
  using linear_on_the_inv_into[OF sub_\<psi>.linear_on_push_forward_inclusion tangent_submanifold_isomorphism(1)]
  by (simp add: linear_on_restrict0)


subsection \<open>\<^term>\<open>d\<kappa>\<close> is an isomorphism \<^term>\<open>T\<^sub>\<psi>\<^sub>p\<psi>U\<rightarrow>T\<^sub>\<psi>\<^sub>pE\<close>\<close>

lemma eq_T\<^sub>\<psi>\<^sub>pE_range_inclusion: "T\<^sub>\<psi>\<^sub>pE = d\<kappa> ` T\<^sub>\<psi>\<^sub>p\<psi>U"
  using sub_eucl.surj_on_push_forward_inclusion[of "\<psi> p"] sub_eucl.inclusion.push_forward_in_tangent_space[of "\<psi> p"]
  by auto

lemma eq_T\<^sub>\<psi>\<^sub>pE_range_inclusion2: "range (directional_derivative k (\<psi> p)) = d\<kappa> ` T\<^sub>\<psi>\<^sub>p\<psi>U" if "k=\<infinity>"
  apply (subst surj_directional_derivative[OF that]) using eq_T\<^sub>\<psi>\<^sub>pE_range_inclusion .

lemma bij_betw_d\<kappa>: "bij_betw d\<kappa> T\<^sub>\<psi>\<^sub>p\<psi>U T\<^sub>\<psi>\<^sub>pE"
  unfolding bij_betw_def using sub_eucl.surj_on_push_forward_inclusion[of "\<psi> p"]
    sub_eucl.inj_on_push_forward_inclusion sub_eucl.inclusion.push_forward_in_tangent_space[of "\<psi> p"]
  by simp

lemma bij_betw_d\<kappa>_inv: "bij_betw d\<kappa>\<inverse> T\<^sub>\<psi>\<^sub>pE T\<^sub>\<psi>\<^sub>p\<psi>U"
  using bij_betw_the_inv_into[OF bij_betw_d\<kappa>] by (simp add: bij_betw_restrict0)

lemma linear_on_d\<kappa>_inv: "linear_on T\<^sub>\<psi>\<^sub>pE T\<^sub>\<psi>\<^sub>p\<psi>U scaleR scaleR d\<kappa>\<inverse>"
  using linear_on_the_inv_into[OF sub_eucl.linear_on_push_forward_inclusion bij_betw_d\<kappa>]
  by (simp add: linear_on_restrict0)



subsection \<open>The coordinate basis of a tangent space\<close>

lemma (in submanifold) vector_apply_sub_eq_localI:
  fixes p and d\<iota> and d\<iota>_inv
  defines d\<iota>: "d\<iota> \<equiv> inclusion.push_forward"
    and d\<iota>_inv: "d\<iota>_inv \<equiv> the_inv_into (sub.tangent_space p) d\<iota>"
  assumes p: "p\<in>N" and S: "S \<subseteq> carrier" and N: "open N" "N \<subseteq> S"
    and f: "f \<in> diff_fun_space" "f' \<in> sub.diff_fun_space" "\<And>x. x \<in> N \<Longrightarrow> f x = f' x"
  shows "\<And>v. v\<in>(sub.tangent_space p) \<Longrightarrow> v f' = (d\<iota> v) f" "\<And>v. v\<in>(tangent_space p) \<Longrightarrow> (d\<iota>_inv v) f' = v f"
proof -
  have 1: "restrict0 (S\<inter>carrier) f \<in> sub.diff_fun_space"
    apply (rule sub.restrict0_in_fun_space[simplified])
    apply (rule diff_fun.diff_fun_submanifold[OF diff_fun_spaceD[OF f(1)]])
    by (simp add: open_submanifold)
  have p_sub: "p\<in>sub.carrier"
    using p S N(2) by auto

  { fix v assume v: "v\<in>(sub.tangent_space p)"
    show "v f' = (d\<iota> v) f"
      apply (simp add: f(1) assms(1) inclusion.push_forward_def comp_id[unfolded id_def])
      apply (rule sub.derivation_eq_localI[OF N(1) p _ v f(2) 1])
      using N(2) S by simp_all (metis f(3) inf.orderE restrict0_def subsetD)
  } moreover {
    fix v assume v_in: "v\<in>(tangent_space p)"
    then have "(d\<iota>_inv v) \<in> (sub.tangent_space p)"
      using bij_betwE[OF bij_betw_d\<iota>_inv[OF p_sub]] unfolding assms(1,2) by simp
    from calculation[OF this] f_the_inv_into_f tangent_submanifold_isomorphism(1) v_in p_sub
    show "(d\<iota>_inv v) f' = v f" unfolding assms(1,2) bij_betw_def by fastforce }
qed


lemma vector_apply_eq_localI:
  defines d\<iota>_inv: "d\<iota>_inv \<equiv> the_inv_into T\<^sub>pU d\<iota>"
  assumes N: "p\<in>N" "open N" "N \<subseteq> sub_\<psi>.sub.carrier"
    and f: "f \<in> diff_fun_space" "f' \<in> sub_\<psi>.sub.diff_fun_space" "\<And>x. x \<in> N \<Longrightarrow> f x = f' x"
  shows "\<And>v. v\<in>T\<^sub>pU \<Longrightarrow> v f' = (d\<iota> v) f" "\<And>v. v\<in>T\<^sub>pM \<Longrightarrow> (d\<iota>_inv v) f' = v f"
proof -
  have 1: "restrict0 (domain \<psi> \<inter> carrier) f \<in> sub_\<psi>.sub.diff_fun_space"
    unfolding sub_\<psi>.sub.diff_fun_space_def
    by auto (metis diff_fun.diff_fun_submanifold diff_fun_spaceD f(1) open_domain
        sub_\<psi>.carrier_submanifold sub_\<psi>.sub.diff_fun_spaceD sub_\<psi>.sub.restrict0_in_fun_space)
  { fix v assume v: "v\<in>T\<^sub>pU"
    show "v f' = (d\<iota> v) f"
      apply (simp add: f(1) sub_\<psi>.inclusion.push_forward_def comp_id[unfolded id_def])
      apply (rule sub_\<psi>.sub.derivation_eq_localI[OF N(2,1) _ v f(2)])
      using N(3) 1 apply auto[2]
      by (metis N(3) f(3) in_mono restrict0_apply_in sub_\<psi>.carrier_submanifold)
  } moreover {
    fix v assume v_in: "v\<in>T\<^sub>pM"
    then have "(d\<iota>_inv v) \<in> T\<^sub>pU"
      using tangent_submanifold_isomorphism(1) the_inv_into_into
      unfolding d\<iota>_inv bij_betw_def by fastforce
    from calculation[OF this] f_the_inv_into_f tangent_submanifold_isomorphism(1) v_in
    show "(d\<iota>_inv v) f' = v f" unfolding d\<iota>_inv bij_betw_def by fastforce }
qed 

\<comment> \<open>This next lemma is another function extension lemma, to deal with the carrier-dependency
  of the differentiable function space tangent vectors act on. See also:
  @{thm sub_\<psi>.extension_lemma_submanifoldE},
  @{thm extension_lemmaE}, and even
  @{thm smooth_bump_functionE}.\<close>
lemma extension_lemma_localE:
  fixes f::"'a\<Rightarrow>real"
  defines d\<iota>_inv: "d\<iota>_inv \<equiv> the_inv_into T\<^sub>pU d\<iota>"
  assumes f: "f \<in> sub_\<psi>.sub.diff_fun_space"
  obtains N f' where
    "p\<in>N" "open N" "compact (closure N)" "closure N \<subseteq> sub_\<psi>.sub.carrier"
    "f' \<in> diff_fun_space" "f' \<in> sub_\<psi>.sub.diff_fun_space" "\<And>x. x \<in> closure N \<Longrightarrow> f' x = f x"
    "\<And>v. v\<in>T\<^sub>pU \<Longrightarrow> v f = v f'" "\<And>v. v\<in>T\<^sub>pU \<Longrightarrow> v f' = (d\<iota> v) f'" "\<And>v. v\<in>(tangent_space p) \<Longrightarrow> (d\<iota>_inv v) f = v f'"
proof -
  obtain N where N: "p\<in>N" "open N" "compact (closure N)" "closure N \<subseteq> sub_\<psi>.sub.carrier"
    using sub_\<psi>.sub.precompact_neighborhoodE p sub_\<psi>_carrier by metis
  obtain f' where  f': "diff_fun k charts f'" "\<And>x. x \<in> closure N \<Longrightarrow> f' x = f x" "csupport_on carrier f' \<inter> carrier \<subseteq> sub_\<psi>.sub.carrier"
    using sub_\<psi>.extension_lemma_submanifoldE[OF sub_\<psi>.sub.diff_fun_spaceD[OF f] closed_closure N(4)] by blast
  let ?f1 = "restrict0 carrier f'"

  have f1: "?f1 \<in> diff_fun_space" "\<And>x. x \<in> closure N \<Longrightarrow> ?f1 x = f x" "extensional0 sub_\<psi>.sub.carrier ?f1"
    using restrict0_in_fun_space[OF f'(1)] apply force
    using N(4) restrict0_apply_in[of _ carrier f'] f'(2) apply force
    unfolding extensional0_def restrict0_def using f'(3) not_in_csupportD by fastforce
  have f1_sub: "?f1 \<in> sub_\<psi>.sub.diff_fun_space"
    using f1(1,3) diff_fun.diff_fun_submanifold[of k charts _ "domain \<psi>"]
    by (auto simp: sub_\<psi>.sub.diff_fun_space_def diff_fun_space_def)

  { fix v assume v: "v\<in>T\<^sub>pU"
    have "v ?f1 = (d\<iota> v) ?f1"
      apply (simp add: f1(1) sub_\<psi>.inclusion.push_forward_def)
      using f1(3) by (metis (mono_tags, lifting) comp_apply ext_extensional0 restrict0_apply_in extensional0_restrict0 sub_\<psi>.carrier_submanifold)
  } moreover {
    fix v assume v: "v\<in>T\<^sub>pU"
    have "v f = v ?f1"
      apply (rule sub_\<psi>.sub.derivation_eq_localI[OF N(2,1) _ v f f1_sub])
      using N(4) f'(2) by auto
  } moreover {
    fix v assume v_in: "v\<in>T\<^sub>pM"
    have "(d\<iota>_inv v) f = v ?f1"
      unfolding assms(1) apply (rule vector_apply_eq_localI(2)[OF N(1,2) _ f1(1) f _ v_in])
      using N(4) f1(2) by auto
  } ultimately show ?thesis using N f1_sub f1 that by presburger
qed

lemma extension_lemma_localE2:
  fixes f::"'b\<Rightarrow>real"
  assumes f: "f \<in> diffeo_\<psi>.dest.diff_fun_space"
  obtains N f' where
    "\<psi> p \<in> N" "open N" "compact (closure N)" "closure N \<subseteq> diffeo_\<psi>.dest.carrier"
    "f' \<in> manifold_eucl.diff_fun_space k" "f' \<in> diffeo_\<psi>.dest.diff_fun_space" "\<And>x. x \<in> closure N \<Longrightarrow> f' x = f x"
    "\<And>v. v\<in>T\<^sub>\<psi>\<^sub>p\<psi>U \<Longrightarrow> v f = v f'" "\<And>v. v\<in>T\<^sub>\<psi>\<^sub>p\<psi>U \<Longrightarrow> v f' = (d\<kappa> v) f'" "\<And>v. v\<in>T\<^sub>\<psi>\<^sub>pE \<Longrightarrow> (d\<kappa>\<inverse> v) f = v f'"
proof -
  interpret local_eucl: c_manifold_point charts_eucl k "restrict_chart (codomain \<psi>) chart_eucl" "\<psi> p"
    by unfold_locales (simp_all add: manifold_eucl.dest.restrict_chart_in_atlas)
  show ?thesis using that local_eucl.extension_lemma_localE f by auto
qed

text \<open>In order to get not just a linear map, but an isomorphism, we have to wrap the differential
  of the chart \<^term>\<open>\<psi>\<close> with the correct (inclusion) maps. This is because the tangent spaces at \<open>p\<close>
  considered on a manifold vs a submanifold contain fundamentally different functions,
  being zero outside the differentiable function sets on the respective carriers.
  The linearity of e.g. \<^term>\<open>d\<psi>\<inverse>\<close>, @{thm linear_on_d\<psi>_inv}, is due to the zero function agreeing with
  the vector space operations, and is not a ``truly'' geometric statement.\<close>

text \<open>The basis of \<^term>\<open>directional_derivative\<close>s for the tangent space \<^term>\<open>T\<^sub>\<psi>\<^sub>pE\<close> at \<^term>\<open>\<psi> p\<close> of a
  \<^typ>\<open>'b::euclidean_space\<close> can be pulled back through the chart \<^term>\<open>\<psi> :: ('a,'b)chart\<close> into a basis
  for the tangent space \<^term>\<open>T\<^sub>pM\<close> at \<^term>\<open>p\<close>.\<close>

definition coordinate_vector :: "'b \<Rightarrow> (('a \<Rightarrow> real) \<Rightarrow> real)"
  where "coordinate_vector = d\<iota> \<circ> d\<psi>\<inverse> \<circ> d\<kappa>\<inverse> \<circ> (directional_derivative k (\<psi> p))"

lemma coordinate_vector_apply:
  "coordinate_vector v \<equiv> d\<iota> (d\<psi>\<inverse> (dRestr (directional_derivative k (\<psi> p) v)))"
  unfolding coordinate_vector_def by auto

lemma coordinate_vector_bij: "bij_betw coordinate_vector UNIV T\<^sub>pM" if "k=\<infinity>"
  using bij_betw_directional_derivative[OF that] bij_betw_d\<kappa>_inv bij_betw_d\<psi>_inv tangent_submanifold_isomorphism(1)
  by (auto intro: bij_betw_trans simp: coordinate_vector_def)

lemma coordinate_vector_linear_on: "linear_on UNIV T\<^sub>pM scaleR scaleR coordinate_vector"
  if "k=\<infinity>"
proof -
  have k: "k\<noteq>0" using that by simp
  have *: "linear_on UNIV T\<^sub>\<psi>\<^sub>pE scaleR scaleR (directional_derivative k (apply_chart \<psi> p))"
    using linear_directional_derivative[OF k] manifold_eucl.subspace_tangent_space
    by (auto intro!: linear_imp_linear_on)
  show ?thesis
    apply (simp add: coordinate_vector_def)
    apply (intro linear_on_compose)
    using * linear_on_d\<kappa>_inv linear_on_d\<psi>_inv' tangent_submanifold_isomorphism(2) apply auto[4]
    apply (metis \<psi>p_in diffeo_\<psi>.inv.push_forward_in_tangent_space inv_chart_inverse p)
    apply (simp add: eq_T\<^sub>\<psi>\<^sub>pE_range_inclusion sub_eucl.submanifold_axioms submanifold.inj_on_push_forward_inclusion)
    by (simp add: that surj_directional_derivative)
qed

lemma coordinate_vector_isomorphismE:
  assumes "k=\<infinity>"
  shows coordinate_vector_linear: "linear coordinate_vector"
    and coordinate_vector_inj: "inj coordinate_vector"
    and coordinate_vector_surj: "range coordinate_vector = T\<^sub>pM"
proof -
  show coordinate_vector_inj: "inj coordinate_vector"
    and coordinate_vector_surj: "range coordinate_vector = T\<^sub>pM"
    using coordinate_vector_bij[OF assms] unfolding bij_betw_def by auto
  have k': "k \<noteq> 0" using assms by simp
  have *: "linear_on UNIV T\<^sub>\<psi>\<^sub>pE scaleR scaleR (directional_derivative k (apply_chart \<psi> p))"
    using linear_directional_derivative[OF k'] manifold_eucl.subspace_tangent_space
    by (auto intro!: linear_imp_linear_on)
  interpret f: linear_on UNIV T\<^sub>pM scaleR scaleR coordinate_vector
    using coordinate_vector_linear_on[OF assms] .
  show "linear coordinate_vector"
    using f.add f.scale by unfold_locales (auto)
qed

lemma coordinate_vector_i_linear_on: "linear_on diff_fun_space UNIV scaleR scaleR (coordinate_vector i)"
  if k: "k=\<infinity>"
  using coordinate_vector_isomorphismE(3)[OF k] mem_tangent_space[of "coordinate_vector i" p]
  by (auto intro: is_derivation_linear_on)

lemma coordinate_basis: "finite_dimensional_real_vector_space_on T\<^sub>pM (coordinate_vector ` Basis)"
  if k: "k=\<infinity>"
proof -
  interpret E: finite_dimensional_real_vector_space_on UNIV "Basis :: 'b set"
    by unfold_locales (auto simp: independent_Basis)
  show ?thesis
    by (intro E.basis_transfer coordinate_vector_linear_on coordinate_vector_bij) (fact that)+
qed

lemma coordinate_vector_apply_in:
  assumes k: "k=\<infinity>"
    and f: "f\<in>diff_fun_space"
  shows "(coordinate_vector b) f = (frechet_derivative (f \<circ> inv_chart \<psi>) (at (\<psi> p)) b)"
proof (unfold coordinate_vector_apply)
  define D where D[simp]: "D \<equiv> directional_derivative k (\<psi> p) b"
  have k': "k\<noteq>0" using k by simp

  let ?y = "THE y. y \<in> T\<^sub>\<psi>\<^sub>p\<psi>U \<and> d\<kappa> y = D"
  have y_eq: "?y = d\<kappa>\<inverse> D" "?y = (the_inv_into T\<^sub>\<psi>\<^sub>p\<psi>U d\<kappa>) D"
    unfolding the_inv_into_def using directional_derivative_in_tangent_space[OF k', of "\<psi> p"] by simp_all
  have y: "?y \<in> T\<^sub>\<psi>\<^sub>p\<psi>U" "d\<kappa> ?y = D"
    apply (simp_all only: y_eq(2))
    subgoal apply (intro the_inv_into_into[of d\<kappa> T\<^sub>\<psi>\<^sub>p\<psi>U D])
      using bij_betw_d\<kappa> directional_derivative_in_tangent_space[OF k', of "\<psi> p"] by (auto simp: bij_betw_def)
    subgoal apply (intro f_the_inv_into_f[of d\<kappa> T\<^sub>\<psi>\<^sub>p\<psi>U D])
      using bij_betw_d\<kappa> directional_derivative_in_tangent_space[OF k', of "\<psi> p"] by (auto simp: bij_betw_def)
    done

  have 1[simp]: "domain \<psi> \<inter> carrier = domain \<psi>"
    using domain_atlas_subset_carrier[OF \<psi>] by auto
  have 2: "restrict0 sub_\<psi>.sub.carrier f \<in> sub_\<psi>.sub.diff_fun_space"
    using f[unfolded diff_fun_space_def] by (auto
        simp: sub_\<psi>.sub.diff_fun_space_def
        intro!: diff_fun.diff_fun_cong[where f=f and g="restrict0 (domain \<psi>) f"]
        intro: diff_fun.diff_fun_submanifold)

  let ?f = "(restrict0 diffeo_\<psi>.dest.carrier (restrict0 sub_\<psi>.sub.carrier f \<circ> inv_chart \<psi>))"
  have f2: "?f \<in> diffeo_\<psi>.dest.diff_fun_space"
    apply (simp add: diffeo_\<psi>.dest.diff_fun_space_def)
    apply (rule diff_fun.diff_fun_cong[where f="f \<circ> inv_chart \<psi>"])
    apply (rule diff_fun_compose[of _ _ "charts_submanifold (domain \<psi>)"])
    by (simp_all add: diffeo_\<psi>.inv.diff_axioms diff_fun.diff_fun_submanifold diff_fun_spaceD f)

  obtain Ng g \<comment> \<open>g is the differentiable extension of \<^term>\<open>?f\<close> to the whole Euclidean space.\<close>
    where Ng: "\<psi> p \<in> Ng" "open Ng" "compact (closure Ng)" "closure Ng \<subseteq> diffeo_\<psi>.dest.carrier"
    and g: "g \<in> manifold_eucl.dest.diff_fun_space" "g \<in> diffeo_\<psi>.dest.diff_fun_space" "\<And>x. x \<in> closure Ng \<Longrightarrow> g x = ?f x"
    and vg: "\<And>v. v \<in> T\<^sub>\<psi>\<^sub>p\<psi>U \<Longrightarrow> v ?f = v g" "\<And>v. v \<in> T\<^sub>\<psi>\<^sub>p\<psi>U \<Longrightarrow> v g = d\<kappa> v g" "\<And>v. v \<in> T\<^sub>\<psi>\<^sub>pE \<Longrightarrow> d\<kappa>\<inverse> v ?f = v g"
    using extension_lemma_localE2[OF f2] by blast

  have "d\<iota> (d\<psi>\<inverse> (d\<kappa>\<inverse> D)) f =  d\<psi>\<inverse> (d\<kappa>\<inverse> D) (restrict0 sub_\<psi>.sub.carrier (f))"
    unfolding sub_\<psi>.inclusion.push_forward_def by (auto simp: restrict0_apply_in[OF f] comp_def)
  also have "\<dots> =  (d\<kappa>\<inverse> D) (restrict0 diffeo_\<psi>.dest.carrier ((restrict0 sub_\<psi>.sub.carrier f) \<circ> inv_chart \<psi>))"
    unfolding diffeo_\<psi>.inv.push_forward_def using restrict0_apply_in 2 by simp
  also have "\<dots> = ?y ?f"
    unfolding the_inv_into_def using directional_derivative_in_tangent_space[OF k', of "\<psi> p"] by (simp add: k)
  also have "?y ?f = D g"
    using vg(1,2)[OF y(1)] y(2) by simp
  also have "D g = frechet_derivative g (at (\<psi> p)) b"
    unfolding D directional_derivative_def using restrict0_apply_in[OF g(1)] by auto
  also have "\<dots> = frechet_derivative (f \<circ> inv_chart \<psi>) (at (\<psi> p)) b"
    apply (rule frechet_derivative_transform_within_open_ext[where X=Ng])
    using g(3) Ng(1,2,4) g(1) k by (auto simp: differentiable_onD)
  finally show "d\<iota> (d\<psi>\<inverse> (d\<kappa>\<inverse> (directional_derivative k (apply_chart \<psi> p) b))) f =
                frechet_derivative (f \<circ> inv_chart \<psi>) (at (\<psi> p)) b"
    by auto
qed

lemma coordinate_vector_apply_out:
  assumes k: "k=\<infinity>"
    and f: "f \<notin> diff_fun_space"
  shows "(coordinate_vector b) f = 0"
  using bij_betwE[OF coordinate_vector_bij[OF k]] f extensional0_outside
  unfolding tangent_space_def by fastforce

text \<open>Just the same as @{thm coordinate_vector_apply_in}, but with unfolded definition. For display.\<close>
lemma coordinate_vector_apply_in':
  assumes k: "k=\<infinity>"
    and f: "f\<in>diff_fun_space"
  shows "(d\<iota> \<circ> d\<psi>\<inverse> \<circ> d\<kappa>\<inverse> \<circ> directional_derivative \<infinity> (\<psi> p)) b f = frechet_derivative (f \<circ> inv_chart \<psi>) (at (\<psi> p)) b"
  using coordinate_vector_apply_in[OF assms] unfolding coordinate_vector_def k[symmetric] .


definition component_function :: "(('a \<Rightarrow> real) \<Rightarrow> real) \<Rightarrow> 'b \<Rightarrow> real"
  where "component_function \<equiv> coord_fun \<circ> d\<kappa> \<circ> d\<psi> \<circ> d\<iota>\<inverse>"

definition tangent_chart_fun :: "(('a \<Rightarrow> real) \<Rightarrow> real) \<Rightarrow> 'b"
  where "tangent_chart_fun v \<equiv> \<Sum>i\<in>Basis. component_function v i *\<^sub>R i"

lemma component_function_T\<^sub>pU: "component_function (d\<iota> v) = coord_fun (d\<kappa> (d\<psi> v))" if "v \<in> T\<^sub>pU" for v
  using tangent_submanifold_isomorphism(1) that
  by (auto simp: bij_betwE the_inv_into_f_f[OF bij_betw_imp_inj_on] component_function_def)

lemma component_function_apply_in_T\<^sub>pU: "component_function (d\<iota> v) i = v (restrict0 (domain \<psi>) (\<lambda>x. (\<psi> x - \<psi> p) \<bullet> i))" if "v \<in> T\<^sub>pU" for v i
proof -
  from that have assms: "d\<iota> v \<in> T\<^sub>pM" "v\<in>T\<^sub>pU"
    using tangent_submanifold_isomorphism(1) by (auto simp: bij_betwE)

  have 1: "(\<lambda>x. (x - \<psi> p) \<bullet> i) \<in> manifold_eucl.dest.diff_fun_space"
    by (auto intro!: smooth_on_inner smooth_on_minus)
  have 2: "(restrict0 diffeo_\<psi>.dest.carrier ((\<lambda>x. (x - \<psi> p) \<bullet> i) \<circ> (\<lambda>x. x))) \<in> diffeo_\<psi>.dest.diff_fun_space"
    apply (simp add: diffeo_\<psi>.dest.diff_fun_space_def)
    apply (rule diff_fun.diff_fun_cong[of k _ "(\<lambda>x. (x - \<psi> p) \<bullet> i)"])
    apply (rule diff_fun.diff_fun_submanifold)
    using 1 by (auto intro: diff_fun_charts_euclI)

  let ?g = "restrict0 diffeo_\<psi>.dest.carrier (\<lambda>x. (x - \<psi> p) \<bullet> i)"
  let ?f = "restrict0 sub_\<psi>.sub.carrier (?g \<circ> \<psi>)"
  have f: "?f \<in> sub_\<psi>.sub.diff_fun_space"
    apply (simp add: sub_\<psi>.sub.diff_fun_space_def)
    apply (rule diff_fun.diff_fun_cong[of k _ "(\<lambda>x. (x - \<psi> p) \<bullet> i) \<circ> \<psi>"])
     apply (rule diff_fun_compose[of k _ "manifold_eucl.charts_submanifold (codomain \<psi>)"])
    using 1 by (auto intro: diff_fun_charts_euclI diffeo_\<psi>.diff_axioms diff_fun.diff_fun_submanifold)

  have "component_function (d\<iota> v) i = (coord_fun (d\<kappa> (d\<psi> v))) i"
    using component_function_T\<^sub>pU[OF assms(2)] by simp
  also have "\<dots> = (\<lambda>g. d\<psi> v (restrict0 diffeo_\<psi>.dest.carrier (g \<circ> (\<lambda>x. x)))) (\<lambda>x. (x - \<psi> p) \<bullet> i)"
    by (simp only: restrict0_apply_in[OF 1] coord_fun_def sub_eucl.inclusion.push_forward_def)
  also have "\<dots> = v (restrict0 sub_\<psi>.sub.carrier (?g \<circ> \<psi>))"
    apply (simp only: diffeo_\<psi>.push_forward_def restrict0_apply_in[OF 2])
    by (simp only: o_id[unfolded id_def])
  also have "v ?f = v (restrict0 (domain \<psi>) (\<lambda>x. (\<psi> x - \<psi> p) \<bullet> i))"
    apply (rule sub_\<psi>.sub.derivation_eq_localI[of "domain \<psi>" p v])
    prefer 6 subgoal
      apply (simp add: sub_\<psi>.sub.diff_fun_space_def, intro conjI)
      apply (rule diff_fun.diff_fun_cong[of _ _ "(\<lambda>x. (x - \<psi> p) \<bullet> i) \<circ> \<psi>"])
      apply (rule diff_fun_compose[of k _ "manifold_eucl.charts_submanifold (codomain \<psi>)"])
      using 1 sub_\<psi>_carrier by (auto simp: diffeo_\<psi>.diff_axioms manifold_eucl.dest.diff_fun_spaceD diff_fun.diff_fun_submanifold)
    using domain_atlas_subset_carrier assms(2) f sub_\<psi>_carrier by auto
  finally show "component_function (d\<iota> v) i = v (restrict0 (domain \<psi>) (\<lambda>x. (\<psi> x - \<psi> p) \<bullet> i))" .
qed

lemma component_function_apply_in_T\<^sub>pM: "component_function v i = (d\<iota>\<inverse> v) (restrict0 (domain \<psi>) (\<lambda>x. (\<psi> x - \<psi> p) \<bullet> i))" if "v \<in> T\<^sub>pM" for v i
proof -
  let ?u = "d\<iota>\<inverse> v"
  have 1: "?u \<in> T\<^sub>pU"
    using bij_betwE[OF bij_betw_d\<iota>_inv] that by auto
  have "v = d\<iota> ?u"
    using that tangent_submanifold_isomorphism(1)
    by (auto simp: f_the_inv_into_f bij_betw_imp_inj_on bij_betw_imp_surj_on)
  thus ?thesis
    using component_function_apply_in_T\<^sub>pU[OF 1] by simp
qed


\<comment> \<open>This lemma is most useful on the Euclidean manifold.
  On any other manifold, or on local submanifolds (in a single chart),
  it can be equally useful and confusing! Use with care.\<close>
lemma component_function_apply_in:
  assumes "v \<in> T\<^sub>pM" "domain \<psi> = carrier"
  shows "component_function v i = v (restrict0 carrier (\<lambda>x. (\<psi> x - \<psi> p) \<bullet> i))"
  using component_function_apply_in_T\<^sub>pU assms p push_forward_id by force

lemma component_function_apply_out: "component_function v i = 0" if "\<not> v \<in> T\<^sub>pM" for v i
  unfolding component_function_def
  apply (simp add: restrict0_apply_out[OF that, of "the_inv_into (sub_\<psi>.sub.tangent_space p) d\<iota>"])
  apply (simp add: linear_on.linear_0[OF linear_on_d\<psi>])
  apply (simp add: linear_on.linear_0[OF sub_eucl.linear_on_push_forward_inclusion[of "\<psi> p"]])
  by (simp add: coord_fun_def)

lemma coordinate_vector_inverse:
  assumes k: "k=\<infinity>"
  shows "v \<in> T\<^sub>pM \<Longrightarrow> v = coordinate_vector (\<Sum>i\<in>Basis. component_function v i *\<^sub>R i)"
    and "x = (\<Sum>i\<in>Basis. component_function (coordinate_vector x) i *\<^sub>R i)"
proof -
  fix v assume "v\<in>T\<^sub>pM"
  hence v: "v \<in> T\<^sub>pM" "d\<iota>\<inverse> v \<in> T\<^sub>pU" "d\<psi> (d\<iota>\<inverse> v) \<in> T\<^sub>\<psi>\<^sub>p\<psi>U" "d\<kappa> (d\<psi> (d\<iota>\<inverse> v)) \<in> T\<^sub>\<psi>\<^sub>pE"
    using bij_betw_d\<iota>_inv bij_betw_d\<psi> bij_betw_d\<kappa> by (simp_all only: bij_betwE)

  have "v = d\<iota> (d\<psi>\<inverse> (d\<kappa>\<inverse> (d\<kappa> (d\<psi> (d\<iota>\<inverse> v)))))"
    apply (simp add: the_inv_into_f_f_bij_betw[OF bij_betw_d\<kappa>] v(3,4))
    apply (simp add: inverse_d\<psi>(1) v(2))
    by (simp add: f_the_inv_into_f_bij_betw[OF bij_betw_d\<iota>] v(1))
  then show "v = coordinate_vector (\<Sum>i\<in>Basis. component_function v i *\<^sub>R i)"
    using euclidean_tangent_space_coordinatesE[OF v(4) k] by (simp_all add: coordinate_vector_apply component_function_def)
next
  fix x :: 'b
  define D where "D \<equiv> directional_derivative k (\<psi> p)"
  define D_inv (\<open>D\<inverse>\<close>) where "D\<inverse> \<equiv> \<lambda>X. \<Sum>i\<in>Basis. coord_fun X i *\<^sub>R i"
  have D_inv: "x = D\<inverse> (D x)" "bij_betw D\<inverse> T\<^sub>\<psi>\<^sub>pE UNIV" for x
    using directional_derivative_inverse(2,3)[OF k] by (simp_all add: D_def D_inv_def)
  have x: "D x \<in> T\<^sub>\<psi>\<^sub>pE" "d\<kappa>\<inverse> (D x) \<in> T\<^sub>\<psi>\<^sub>p\<psi>U" "d\<psi>\<inverse> (d\<kappa>\<inverse> (D x)) \<in> T\<^sub>pU" "d\<iota> (d\<psi>\<inverse> (d\<kappa>\<inverse> (D x))) \<in> T\<^sub>pM"
    using bij_betw_directional_derivative[OF k] bij_betw_d\<kappa>_inv bij_betw_d\<psi>_inv bij_betw_d\<iota> by (simp_all only: bij_betwE D_def UNIV_I)

  have "x = D\<inverse> (d\<kappa> (d\<psi> (d\<iota>\<inverse> (d\<iota> (d\<psi>\<inverse> (d\<kappa>\<inverse> (D x)))))))"
    apply (simp add: the_inv_into_f_f_bij_betw[OF bij_betw_d\<iota>] x(3,4))
    apply (simp add: inverse_d\<psi>(2) x(2))
    by (simp add: f_the_inv_into_f_bij_betw[OF bij_betw_d\<kappa>] x(1) D_inv(1))
  then show "x = (\<Sum>i\<in>Basis. component_function (coordinate_vector x) i *\<^sub>R i)"
    by (simp add: coordinate_vector_apply[folded D_def] component_function_def D_inv_def)
qed


\<comment> \<open>Just a rewriting of @{thm coordinate_vector_inverse} using the \<^term>\<open>tangent_chart_fun\<close>.\<close>
lemma tangent_chart_fun_inverse:
  assumes k: "k=\<infinity>"
  shows "v \<in> T\<^sub>pM \<Longrightarrow> v = coordinate_vector (tangent_chart_fun v)"
    and "x = tangent_chart_fun (coordinate_vector x)"
  unfolding tangent_chart_fun_def using coordinate_vector_inverse[OF assms] by auto


lemma tangent_chart_fun_bij: "bij_betw tangent_chart_fun T\<^sub>pM UNIV" if "k=\<infinity>"
  using coordinate_vector_bij[OF that] coordinate_vector_inverse[OF that]
  by (auto intro: inverse_bij_betw simp: tangent_chart_fun_def)


lemma tangent_chart_fun_linear_on: "linear_on T\<^sub>pM UNIV scaleR scaleR tangent_chart_fun" if "k=\<infinity>"
  apply (rule linear_on_inv)
  using coordinate_vector_bij[OF that] coordinate_vector_inverse[OF that] coordinate_vector_linear_on[OF that]
  by (auto simp: bij_betw_def tangent_chart_fun_def)


lemma coordinate_vector_representation:
  assumes v: "v \<in> T\<^sub>pM" and k: "k=\<infinity>"
  shows "v = (\<Sum>i\<in>Basis. (component_function v i) *\<^sub>R (coordinate_vector i))"
  (is \<open>v = (\<Sum>b\<in>Basis. (?f\<^sub>v b) *\<^sub>R (?c b))\<close>)
proof -
  have v: "v \<in> T\<^sub>pM" "d\<iota>\<inverse> v \<in> T\<^sub>pU" "d\<psi> (d\<iota>\<inverse> v) \<in> T\<^sub>\<psi>\<^sub>p\<psi>U" "d\<kappa> (d\<psi> (d\<iota>\<inverse> v)) \<in> T\<^sub>\<psi>\<^sub>pE"
    using bij_betw_d\<iota>_inv bij_betw_d\<psi> bij_betw_d\<kappa> v by (simp_all only: bij_betwE)

  have "v = ?c (\<Sum>i\<in>Basis. ?f\<^sub>v i *\<^sub>R i)"
    using coordinate_vector_inverse(1)[OF k v(1)] .
  also have "\<dots> = (\<Sum>b\<in>Basis. ?c ((?f\<^sub>v b) *\<^sub>R b))"
    by (rule linear_sum) (fact coordinate_vector_linear[OF k])
  also have "\<dots> = (\<Sum>b\<in>Basis. (?f\<^sub>v b) *\<^sub>R (?c b))"
    using linear_cmul coordinate_vector_linear k by (auto intro: sum.cong)
  finally show "v = (\<Sum>b\<in>Basis. (?f\<^sub>v b) *\<^sub>R (?c b))" .
qed

lemma coordinate_vector_representation_apply_in:
  assumes v: "v \<in> T\<^sub>pM" and k: "k=\<infinity>" and f: "f \<in> diff_fun_space"
  shows "v f = (\<Sum>i\<in>Basis. (component_function v i) *\<^sub>R (coordinate_vector i f))"
  using coordinate_vector_representation[OF assms(1,2)]
  by (auto simp: scaleR_fun_def sum_fun_def) (metis)

\<comment> \<open>A stronger version of @{thm derivation_eq_localI} for the case where \<^term>\<open>k=\<infinity>\<close>, i.e. we know
  all derivations can be represented as directional derivatives.\<close>
lemma (in c_manifold) derivation_eq_localI': "X f = X g"
  if "k=\<infinity>" "p \<in> U" "U \<subseteq> domain c" "c \<in> atlas"
    "X \<in> tangent_space p"
    "f \<in> diff_fun_space"
    "g \<in> diff_fun_space"
    "\<And>x. x \<in> U \<Longrightarrow> frechet_derivative (f \<circ> inv_chart c) (at (c x)) =  frechet_derivative (g \<circ> inv_chart c) (at (c x))"
proof -
  interpret p: c_manifold_point charts k c p using that(2-4) by unfold_locales auto
  show ?thesis
    apply (simp only: p.coordinate_vector_representation_apply_in[OF that(5,1)] p.coordinate_vector_apply_in[OF that(1)] that(6,7))
    using that(2,8) by presburger
qed

lemma coordinate_vector_restrict_chart:
  assumes "p \<in> S" "open S" and k: "k=\<infinity>"
  shows "coordinate_vector i = (c_manifold_point.coordinate_vector charts \<infinity> (restrict_chart S \<psi>) p) i"
    (is \<open>_ = ?coordinate_restrict i\<close>)
proof
  fix f :: "'a \<Rightarrow> real"
  interpret S: c_manifold_point charts \<infinity> "restrict_chart S \<psi>" p
    using \<psi> assms c_manifold_point restrict_chart_in_atlas by auto
  have 1: "coordinate_vector i \<in> T\<^sub>pM"
    using bij_betwE coordinate_vector_bij k by blast
  have 2: "?coordinate_restrict i \<in> T\<^sub>pM"
    using bij_betwE S.coordinate_vector_bij k by blast
  show "coordinate_vector i f = ?coordinate_restrict i f"
  proof (cases "f \<in> diff_fun_space")
    case True thus ?thesis
      using coordinate_vector_apply_in[OF k] by (simp add: S.coordinate_vector_apply_in k)
  next
    case False thus ?thesis
      using coordinate_vector_apply_out by (simp add: S.coordinate_vector_apply_out k)
  qed
qed


lemma inj_coordinate_vector:
  assumes k: "k=\<infinity>"
  shows "inj_on coordinate_vector S"
    using bij_betw_imp_inj_on[OF coordinate_vector_bij[OF k]] by (simp add: inj_def inj_onI)


lemma (in finite_dimensional_vector_space_on) mem_scaled_basis_sum:
  shows "(\<Sum>i\<in>basis. scale (f i) i) \<in> S"
  using finite_Basis span_Basis span_on_def by auto

\<comment> \<open>Same as @{thm euclidean_components_eq_iff}, but for the basis of coordinate vectors.\<close>
lemma euclidean_coordinates_eq_iff:
  assumes k: "k=\<infinity>"
  shows "((\<Sum>i\<in>Basis. f i *\<^sub>R coordinate_vector i) = (\<Sum>i\<in>Basis. g i *\<^sub>R coordinate_vector i)) \<longleftrightarrow> (\<forall>i\<in>Basis. f i = g i)"
proof -
  let ?B = "coordinate_vector ` Basis"
  interpret coordinate_basis: finite_dimensional_real_vector_space_on T\<^sub>pM ?B
    using coordinate_basis[OF k] .

  have "((\<Sum>i\<in>Basis. f i *\<^sub>R coordinate_vector i) = (\<Sum>i\<in>Basis. g i *\<^sub>R coordinate_vector i)) \<longleftrightarrow>
              (\<Sum>i\<in>Basis. f i *\<^sub>R i) = (\<Sum>i\<in>Basis. g i *\<^sub>R i)"
      (is \<open>?LHS1 = ?LHS2 \<longleftrightarrow> ?RHS\<close>)
  proof -
    have tan_eq_simp: "l = r \<longleftrightarrow> tangent_chart_fun l = tangent_chart_fun r"
        if "l\<in>T\<^sub>pM" "r\<in>T\<^sub>pM" for l r
      using tangent_chart_fun_bij[OF k] that by (auto simp: bij_betw_def inj_onD)

    have tan_sum_simp: "tangent_chart_fun (\<Sum>i\<in>Basis. f i *\<^sub>R coordinate_vector i) = (\<Sum>i\<in>Basis. f i *\<^sub>R i)"
      for f :: "'b \<Rightarrow> real"
    proof-
      have "tangent_chart_fun (\<Sum>i\<in>Basis. f i *\<^sub>R coordinate_vector i) =
            sum (tangent_chart_fun \<circ> (\<lambda>i. f i *\<^sub>R coordinate_vector i)) Basis"
        apply (rule linear_on.linear_sum[symmetric])
        apply (rule tangent_chart_fun_linear_on[OF k])
        using coordinate_vector_surj k tangent_space.mem_scale by (blast, simp)
      also have "\<dots> = (\<Sum>i\<in>Basis. f i *\<^sub>R tangent_chart_fun (coordinate_vector i))"
      proof -
        have "tangent_chart_fun (f i *\<^sub>R coordinate_vector i) =
              f i *\<^sub>R tangent_chart_fun (coordinate_vector i)"
            if "i\<in>Basis" for i::'b
          apply (rule vector_space_pair_on.linear_scale[OF _ _ _ tangent_chart_fun_linear_on[OF k]])
          by unfold_locales
            (simp_all add: scaleR_right_distrib scaleR_left_distrib bij_betwE[OF coordinate_vector_bij[OF k]])
        thus ?thesis by simp
      qed
      finally show ?thesis
        using coordinate_vector_inverse(2)[OF k] by (simp add: tangent_chart_fun_def)
    qed

    have "?LHS1 = ?LHS2 \<longleftrightarrow> tangent_chart_fun ?LHS1 = tangent_chart_fun ?LHS2"
    proof -
      have "f i *\<^sub>R coordinate_vector i \<in> T\<^sub>pM" if "i\<in>Basis" for i f
          using coordinate_basis.basis_subset that by (auto simp add: tangent_space.mem_scale)
      hence 1: "(\<Sum>i\<in>Basis. f i *\<^sub>R coordinate_vector i) \<in> T\<^sub>pM" for f
        by (metis (no_types, lifting) coordinate_basis.finite_dimensional_basis(3) span_sum)
      then show ?thesis
        by (auto intro!: tan_eq_simp)
    qed
    then show ?thesis using tan_sum_simp by presburger
  qed

  thus ?thesis using euclidean_components_eq_iff by auto
qed


\<comment>\<open> TODO obsolete with @{thm euclidean_coordinates_eq_iff} subsuming it?
    Somewhat different proof origin though. \<close>
lemma coordinate_sum_eq_imp_components_eq':
  assumes "\<forall>v. f v \<noteq> 0 \<longrightarrow> v \<in> Basis" "\<forall>v. g v \<noteq> 0 \<longrightarrow> v \<in> Basis"
    and k: "k=\<infinity>"
    and "(\<Sum>i\<in>{v. f v \<noteq> 0}. (f i) *\<^sub>R coordinate_vector i) = (\<Sum>i\<in>{v. g v \<noteq> 0}. (g i) *\<^sub>R coordinate_vector i)"
  shows "\<forall>i. f i = g i"
proof -

  text \<open>This proof is mostly about massaging \<open>\<Sum>\<close> expressions. We know coordinate vectors form a
    basis, and we know a basis is linearly independent. The rest is about getting from an expression
    entirely in the vector space of @{thm coordinate_basis} to an expression that uses linear
    independence in the tangent space, while talking about the \<^term>\<open>Basis\<close> of the corresponding
    \<^typ>\<open>'b::euclidean_space\<close>.\<close>

  let ?B = "coordinate_vector ` Basis"
  interpret VS: finite_dimensional_real_vector_space_on T\<^sub>pM ?B
    using coordinate_basis[OF k] .

  have 1: "v \<in> ?B" if "v \<in> T\<^sub>pM" "f (tangent_chart_fun v) \<noteq> 0 \<or> g (tangent_chart_fun v) \<noteq> 0" for v
    using that(2) unfolding tangent_chart_fun_def
    using VS.basis_subset coordinate_vector_inverse(1)[OF k that(1)] assms(1,2) by auto
  have f_eq_g: "\<forall>x\<in>T\<^sub>pM. f (tangent_chart_fun x) = g (tangent_chart_fun x)"
  proof (rule VS.unique_representation_basis)
    have set_simps: "{x \<in> T\<^sub>pM. f (tangent_chart_fun x) \<noteq> 0} = coordinate_vector ` {v. f v \<noteq> 0}"
                    "{x \<in> T\<^sub>pM. g (tangent_chart_fun x) \<noteq> 0} = coordinate_vector ` {v. g v \<noteq> 0}"
      using coordinate_vector_inverse[OF k] unfolding tangent_chart_fun_def
      using assms(1,2) component_function_apply_out by auto
        (metis (no_types, lifting) Basis_zero scaleR_eq_0_iff sum.not_neutral_contains_not_neutral)+
    have "(\<Sum>v\<in>{x \<in> T\<^sub>pM. f (tangent_chart_fun x) \<noteq> 0}. f (tangent_chart_fun v) *\<^sub>R v) = (\<Sum>i\<in>{v. f v \<noteq> 0}. f i *\<^sub>R coordinate_vector i)"
      apply (simp add: set_simps)
      using coordinate_vector_inverse(2)[OF k] by (simp add: tangent_chart_fun_def sum.reindex[OF inj_coordinate_vector[OF k]])
    also have "\<dots> = (\<Sum>i\<in>{v. g v \<noteq> 0}. (g i) *\<^sub>R coordinate_vector i)"
      using assms(4) .
    finally show "(\<Sum>v\<in>{x \<in> T\<^sub>pM. f (tangent_chart_fun x) \<noteq> 0}. f (tangent_chart_fun v) *\<^sub>R v) =
          (\<Sum>v\<in>{x \<in> T\<^sub>pM. g (tangent_chart_fun x) \<noteq> 0}. g (tangent_chart_fun v) *\<^sub>R v)"
      apply (simp add: set_simps)
      using coordinate_vector_inverse[OF k]
      by (simp add: tangent_chart_fun_def sum.reindex[OF inj_coordinate_vector[OF k]])
  qed (simp_all add: 1)

  show ?thesis
    using coordinate_vector_inverse[unfolded tangent_chart_fun_def[symmetric]]
    using tangent_chart_fun_bij coordinate_vector_bij f_eq_g by (metis coordinate_vector_surj k rangeI)
qed


lemma coordinate_sum_eq_imp_components_eq:
  assumes k: "k=\<infinity>"
    and "(\<Sum>i\<in>Basis. (f i) *\<^sub>R coordinate_vector i) = (\<Sum>i\<in>Basis. (g i) *\<^sub>R coordinate_vector i)"
  shows "\<forall>i\<in>Basis. f i = g i"
  using euclidean_coordinates_eq_iff[OF k] assms(2) by blast


\<comment> \<open>TODO Same as above: obsolete?\<close>
lemma coordinate_sum_eq_iff:
  assumes "\<And>v. f v \<noteq> 0 \<longleftrightarrow> v \<in> Basis"
    and "\<And>v. g v \<noteq> 0 \<longleftrightarrow> v \<in> Basis"
    and k: "k=\<infinity>"
  shows "(\<Sum>i\<in>Basis. (f i) *\<^sub>R coordinate_vector i) = (\<Sum>i\<in>Basis. (g i) *\<^sub>R coordinate_vector i) \<longleftrightarrow> (\<forall>i\<in>Basis. f i = g i)"
  using coordinate_sum_eq_imp_components_eq assms by auto


lemma component_function_restrict_chart:
  assumes S: "p \<in> S" "open S"
    and v: "v \<in> T\<^sub>pM" and i: "i \<in> Basis" and k: "k=\<infinity>"
  shows "component_function v i = (c_manifold_point.component_function charts \<infinity> (restrict_chart S \<psi>) p) v i"
proof -
  interpret p2: c_manifold_point charts \<infinity> "restrict_chart S \<psi>" p
    using \<psi> S k c_manifold_point restrict_chart_in_atlas by force
  have coord_vec_eq: "coordinate_vector i = p2.coordinate_vector i" for i
    using coordinate_vector_restrict_chart[OF S k] .
  let ?c = "restrict0 Basis (component_function v)" and ?c2 = "restrict0 Basis (p2.component_function v)"
  have "(\<Sum>i\<in>Basis. ?c i *\<^sub>R coordinate_vector i) = (\<Sum>i\<in>Basis. ?c2 i *\<^sub>R coordinate_vector i)"
    using coordinate_vector_representation p2.coordinate_vector_representation coord_vec_eq k v
    by simp
  thus ?thesis using euclidean_coordinates_eq_iff[OF k] i restrict0_apply_in by auto
qed


lemma coordinate_vector_uminus: "coordinate_vector i (- f) = - coordinate_vector i f"
  if k: "k=\<infinity>" and f: "f \<in> diff_fun_space"
proof -
  interpret l: linear_on diff_fun_space UNIV scaleR scaleR "coordinate_vector i"
    using coordinate_vector_i_linear_on[OF k] .
  show ?thesis using diff_fun_space.m1.mem_uminus l.add l.linear_0 f by fastforce
qed


\<comment> \<open>An intro lemma: a coordinate vector has the same result when applied to two functions
  with equal local derivative (in the correct function space). See @{thm derivation_eq_localI'}.\<close>
lemma coordinate_vector_cong': "coordinate_vector i g = coordinate_vector i f"
  if k: "k=\<infinity>" and g: "g \<in> diff_fun_space" and f: "f \<in> diff_fun_space"
    and gf: "frechet_derivative (g \<circ> inv_chart \<psi>) (at (\<psi> p)) = frechet_derivative (f \<circ> inv_chart \<psi>) (at (\<psi> p))"
  using coordinate_vector_apply_in[OF k, of _ i] g f gf by presburger


lemma coordinate_vector_cong: "coordinate_vector i g = coordinate_vector i f"
  if k: "k=\<infinity>" and g: "g \<in> diff_fun_space" and f: "f \<in> diff_fun_space"
    and gf: "\<And>x. x\<in>(domain \<psi>) \<Longrightarrow> g x = f x"
proof -
  have "frechet_derivative (g \<circ> inv_chart \<psi>) (at (\<psi> p)) = frechet_derivative (f \<circ> inv_chart \<psi>) (at (\<psi> p))"
    apply (rule frechet_derivative_transform_within_open)
    using diff_fun_differentiable_at g[unfolded diff_fun_space_def] \<psi> k p apply (simp, blast)
    using gf by (auto simp: o_def)
  from coordinate_vector_cong'[OF that(1-3) this] show ?thesis .
qed

end (*context c_manifold_point*)


lemma (in c_manifold) diff_fun_components_iff:
  fixes f :: "'b::euclidean_space \<Rightarrow> 'a::{second_countable_topology,t2_space} \<Rightarrow> real"
  shows "diff_fun k charts (\<lambda>x. \<Sum>i\<in>Basis. (f i x) *\<^sub>R i) \<longleftrightarrow> (\<forall>i\<in>Basis. diff_fun k charts (f i))"
    (is \<open>?diff_sum \<longleftrightarrow> ?diff_cpt\<close>)
proof
  assume asm: "?diff_sum"
  have f_eq_inner_sum_cpt: "(\<Sum>j\<in>Basis. (f j x) *\<^sub>R j) \<bullet> i = f i x" if "i\<in>Basis" for i::'b and x
    using that by force
  show "?diff_cpt"
  proof
    fix i::'b assume i: "i\<in>Basis"
    hence 1: "((\<lambda>x. x \<bullet> i) \<circ> (\<lambda>x. \<Sum>j\<in>Basis. f j x *\<^sub>R j)) x = f i x" for x
      using f_eq_inner_sum_cpt by (simp add: comp_def)
    show "diff_fun k charts (f i)"
      apply (rule diff_fun.diff_fun_cong[OF _ 1])
      apply (rule diff_fun_compose[of _ _ charts_eucl])
      using asm[unfolded diff_fun_def] by (auto intro: diff_fun_charts_euclI smooth_on_inner)
  qed
next
  assume "?diff_cpt"
  then show "?diff_sum"
    by (auto intro!: diff_fun_sum diff_fun_scaleR simp: diff_fun_const)
qed

end