section \<open>$C^*$-algebras\<close>

theory Cstar_Algebra_On
  imports
    Lie_Groups.Algebra_On
    Types_To_Sets_Extension.SML_Topological_Space
    Complex_Bounded_Operators.Complex_Vector_Spaces
    "HOL-Analysis.Abstract_Metric_Spaces"
begin

bundle scaleC_syntax begin
  notation Complex_Vector_Spaces0.scaleC_class.scaleC (infixr \<open>*\<^sub>C\<close> 75)
end

unbundle no scaleC_syntax


subsection \<open>Additional lemmas for \<^theory>\<open>Lie_Groups.Algebra_On\<close>\<close>

lemma (in algebra_on)
  shows distR': "\<lbrakk>x\<in>S; y\<in>S; z\<in>S\<rbrakk> \<Longrightarrow> (x-y) \<Zspot> z = x \<Zspot> z - y \<Zspot> z"
    and distL': "\<lbrakk>x\<in>S; y\<in>S; z\<in>S\<rbrakk> \<Longrightarrow> z \<Zspot> (x-y) = z \<Zspot> x - z \<Zspot> y"
  using distR m1.mem_uminus apply fastforce
  using distL m1.mem_uminus by fastforce


subsection \<open>Involutive rings and algebras\<close>

locale involutive_semigroup = semigroup_add_on_with +
  fixes involution :: "'a\<Rightarrow>'a" (\<open>_\<^sup>\<dagger>\<close> [99] 100)
  assumes involution[simp]: "x\<in>S \<Longrightarrow> (x\<^sup>\<dagger>)\<^sup>\<dagger> = x"
    and antiautomorphism: "\<lbrakk>x\<in>S; y\<in>S\<rbrakk> \<Longrightarrow> (pls x y)\<^sup>\<dagger> = pls (y\<^sup>\<dagger>) (x\<^sup>\<dagger>)"
    and involution_mem[simp]: "x\<in>S \<Longrightarrow> x\<^sup>\<dagger> \<in> S"


\<comment> \<open>Bundle for class constant notation (e.g. for \<^const>\<open>plus\<close>):
  disable inside Ballarin's set-based locale for rings,
  re-enable once we involve type classes for e.g. base fields of algebras.\<close>
bundle class_ring_notation begin
  notation plus (infixl "+" 65)
  notation minus (infixl \<open>-\<close> 65)
  notation uminus (\<open>(\<open>open_block notation=\<open>prefix -\<close>\<close>- _)\<close> [81] 80)
end

unbundle no class_ring_notation
locale involutive_ring =
    Ring_Theory.ring R addition multiplication zero unit +
    involutive_semigroup R multiplication involution
  for R :: "'a set" and addition :: "'a\<Rightarrow>'a\<Rightarrow>'a" (infixl "+" 65)
    and multiplication (infixl "\<cdot>" 70) and zero ("\<zero>") and unit ("\<one>")
    and involution :: "'a\<Rightarrow>'a" (\<open>_\<^sup>\<dagger>\<close> [99] 100) +
  assumes ivl_ring: "\<lbrakk>x\<in>R; y\<in>R\<rbrakk> \<Longrightarrow> (x+y)\<^sup>\<dagger> = x\<^sup>\<dagger> + y\<^sup>\<dagger>"
begin

  lemma unit_self_adjoint: "\<one>\<^sup>\<dagger> = \<one>"
    using antiautomorphism[of _ \<one>] involution involution_mem
    by (metis multiplicative.right_unit multiplicative.unit_closed)

  lemma ivl_uminus: "x\<in>R \<Longrightarrow> involution (-x) = - involution x"
    by (metis (no_types, lifting) additive.inverse_equality additive.invertible additive.invertibleE
        additive.invertible_left_inverse2 additive.unit_closed involution_mem ivl_ring)

  lemma ivl_minus: "\<lbrakk>x\<in>R; y\<in>R\<rbrakk> \<Longrightarrow> involution (x-y) = involution x - involution y"
    by (simp add: ivl_ring ivl_uminus)

end
unbundle class_ring_notation

text \<open>A general definition of $^*$-algebra might look as follows.

\begin{definition}[$^*$-algebra]
Let $A$ be a ring with involution $^*$, and $R$ any commutative ring with involution $'$.
$A$ is a $^*$-algebra if it is an associative algebra over $R$, such that:
\[
\forall r \in R. \forall a \in A. (r a)^* = r' a^*
\]
A \emph{$^*$-homomorphism} $f\colon A \to B$ is an algebra homomorphism that respects involution:
\[ \forall a \in A. f(a)^{*_B} = f(a^{*_A}) \]
\end{definition}

Since nearly all formalisation seems to use classes for the vector addition and base field,
and some texts (e.g. \cite{fewster2019}) define $^*$-algebras using the complex numbers as
a base ring directly, we do so as well, without worrying about the involution of the base ring
being specified only implicitly, on a type-level. Even category theory is, most of the time,
only interested in categories of spaces over a shared base field/ring.
Note also our involutive complex algebras are unital (and associative).\<close>


locale involutive_complex_algebra =
  assoc_algebra_1_on S scale multiplication unit +
  involutive_ring S "(+)" multiplication 0 unit involution
  for S :: "'a::ab_group_add set"
    and scale :: "complex \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr \<open>*\<^sub>C\<close> 75)
    and multiplication :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr \<open>\<Zspot>\<close> 74)
    and unit :: "'a" (\<open>\<one>\<close>)
    and involution :: "'a\<Rightarrow>'a" (\<open>_\<^sup>\<dagger>\<close> [99] 100) +
  assumes ivl_scale: "s\<in>S \<Longrightarrow> (c *\<^sub>C s)\<^sup>\<dagger> = cnj c *\<^sub>C s\<^sup>\<dagger>"


lemma involutive_complex_algebraI:
  fixes S :: "'a::ab_group_add set"
    and scl :: "complex \<Rightarrow> 'a \<Rightarrow> 'a"
    and mlt :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and e :: "'a"
    and involution :: "'a\<Rightarrow>'a"
  assumes "assoc_algebra_1_on S scl mlt e"
    and involution: "\<forall>x. x\<in>S \<longrightarrow> involution (involution x) = x"
    and antiautomorphism: "\<forall>x y. x\<in>S \<longrightarrow> y\<in>S \<longrightarrow> involution (mlt x y) = mlt (involution y) (involution x)"
    and ivl_mem: "\<forall>x. x\<in>S \<longrightarrow> involution x \<in> S"
    and ivl_ring: "\<forall>x y. x\<in>S\<longrightarrow> y\<in>S \<longrightarrow> involution (x+y) = (involution x) + (involution y)"
    and ivl_scale: "\<forall>x c. x\<in>S \<longrightarrow> involution (scl c x) = scl (cnj c) (involution x)"
  shows "involutive_complex_algebra S scl mlt e involution"
proof -
  interpret alg: assoc_algebra_1_on S scl mlt e using assms(1).
  interpret mon: Group_Theory.monoid S "(+)" 0
    by (unfold_locales, simp_all add: group_cancel.add1 alg.m1.mem_add alg.m1.mem_zero)
  have "mon.invertible u" if "u \<in> S" for u
    by (meson ab_left_minus alg.m1.mem_uminus mon.invertibleI neg_eq_iff_add_eq_0 that)
  then show "involutive_complex_algebra S scl mlt e involution"
    by (unfold_locales, simp_all add: alg.m1.subspace_UNIV alg.m1.subspace_add add.commute
        add.left_commute alg.amult_assoc alg.distL alg.distR assms(2-))
qed

lemma (in module_on) sub_module:
  assumes "subspace A" "A\<subseteq>S"
  shows "module_on A scale"
  using assms module_on.intro module_on.subspace_def module_on_axioms scale_left_distrib_on
    scale_one_on scale_right_distrib_on scale_scale_on subset_eq by (smt (verit, ccfv_threshold))

locale involutive_subalgebra =
  subalg: involutive_complex_algebra A + involutive_complex_algebra B for A B +
  assumes "A \<subseteq> B"

lemma (in involutive_complex_algebra) subalgebraI:
  fixes A
    assumes unital_subspace: "m1.subspace A" "A \<subseteq> S" "\<one> \<in> A"
      and mult_closed: "\<forall>x y. x \<in> A \<longrightarrow> y \<in> A \<longrightarrow> x \<Zspot> y \<in> A"
      and involution_closed: "\<forall>x. x \<in> A \<longrightarrow> involution x \<in> A"
  shows "involutive_subalgebra (*\<^sub>C) (\<Zspot>) \<one> involution A S"
proof -
  interpret vector_space_on A
    using m1.sub_module unital_subspace(1,2) vector_space_on.intro by blast
  
  interpret subalg: assoc_algebra_1_on A "(*\<^sub>C)" "(\<Zspot>)" \<one>
    apply unfold_locales
             apply (meson in_mono linearL'(2) unital_subspace(2))
            apply (meson unital_subspace(2) in_mono linearL'(1))
           apply (meson distributive(1) in_mono unital_subspace(2))
          apply (meson unital_subspace(2) linearR'(1) subsetD)
         using assms(4) apply blast
        using unital_subspace(2) apply blast
       apply (simp add: unital_subspace(3))
      using unital_subspace(2) apply blast
     using unital_subspace(2) apply blast
    by simp

  interpret ivl_subalg: involutive_complex_algebra A
    apply (intro involutive_complex_algebraI)
    subgoal by unfold_locales
    using involution unital_subspace(2) apply blast
    apply (meson antiautomorphism in_mono unital_subspace(2))
    using involution_closed apply blast
    apply (meson ivl_ring subset_eq unital_subspace(2))
    using assms(2) ivl_scale by blast

  show ?thesis
    by (unfold_locales, simp add: assms(2))
qed
    


subsection \<open>Preliminaries and experiments\<close>

context Metric_space begin

sublocale topological_space_ow M mopen
  apply unfold_locales
  subgoal by (simp add: gt_ex mball_subset_mspace mopen_def)
  subgoal by (metis mopen_def openin_Int openin_mtopology)
  subgoal using openin_Union[of _ mtopology] by (simp add: mtopology_def)
  done

end


subsection \<open>Subfields of a \<^class>\<open>field\<close> on a type universe\<close>
text \<open>Compare to \<^term>\<open>subspace\<close> in \<^theory>\<open>HOL-Types_To_Sets.Linear_Algebra_On\<close>.\<close>

abbreviation "closed_under_un K op \<equiv> \<forall>x\<in>K. op x \<in> K"
abbreviation "closed_under_bin K op \<equiv> \<forall>x\<in>K. \<forall>y\<in>K. op x y \<in> K"

locale subfield =
  fixes K :: "'a::field set"
  assumes subfield_1[simp]: "1 \<in> K"
  and subfield_closed[simp]:
    "x\<in>K \<Longrightarrow> - x \<in> K"
    "x\<in>K \<Longrightarrow> inverse x \<in> K"
    "\<lbrakk>x\<in>K; y\<in>K\<rbrakk> \<Longrightarrow> x + y \<in> K"
    "\<lbrakk>x\<in>K; y\<in>K\<rbrakk> \<Longrightarrow> x * y \<in> K"
begin

\<comment> \<open>The zero element of a field coincides with the zero element of any of its subfields. Since
  \<^term>\<open>0\<close> is a class constant, it is always the zero element of the field on the type universe.\<close>
lemma subfield_0 [simp]: "0 \<in> K"
  by (metis add.right_inverse subfield_1 subfield_closed(1,3))

end


\<comment> \<open>Any field is a subfield of itself.\<close>
lemma subfield_UNIV: "subfield UNIV"
  unfolding subfield_def by simp

\<comment> \<open>The real numbers are a subfield of the complex numbers.\<close>
lemma real_subfield_complex: "subfield {c. Im c = 0}"
  unfolding subfield_def by auto


subsubsection \<open>... as a transfer relation?\<close>
text \<open>The price of being able to talk about a subfield of a different type is representational
  definiteness. The subfield of type 'a is only a subfield ``up to isomorphism". Quite categorical
  in flavour, this should make no practical difference. See also skeletal categories:
  https://ncatlab.org/nlab/show/skeleton\<close>
context includes lifting_syntax begin

definition "subfield_rel (R :: 'a::field \<Rightarrow> 'b::field \<Rightarrow> bool) \<equiv>
    left_total R \<and> bi_unique R \<and>    \<^cancel>\<open>inj_on R (UNIV::'a set)\<close>
    R 1 1 \<and>
    (R ===> R ===> R) (+) (+) \<and>
    (R ===> R ===> R) (*) (*) \<and>
    (R ===> R) uminus uminus \<and>
    (R ===> R) inverse inverse"
    (* ... etc for all operations ...*)

lemma subfield_rel_0: "R 0 0" if "subfield_rel R"
  using add.right_inverse by (metis rel_funD that[unfolded subfield_rel_def])

lemma subfield_rel_UNIV: "subfield_rel (=)"
  by (simp add: bi_unique_eq left_total_eq rel_fun_eq subfield_rel_def)

lemma real_subfield_rel_complex: "subfield_rel (\<lambda>r c. complex_of_real r = c)"
  using of_real_add of_real_mult by (simp add: left_total_def bi_unique_def subfield_rel_def rel_fun_def)

end (* lifting_syntax *)


subsection \<open>Topological Fields and Vector Spaces\<close>
text \<open>
  The topology will be defined, as usual for locales, on a carrier set only.
  Here, that carrier is implicit as the union of all open sets, like for manifolds.
  This means e.g. addition is defined on the type universe, but is continuous only on the
  subset of that universe covered by the topology.
\<close>

abbreviation "continuous_binary_op t f \<equiv> continuous_map (prod_topology t t) t (\<lambda>(a,b). f a b)"
locale topological_field_ow = topological_space_ow F \<tau>
  for F :: "'at::field set"
    and \<tau> :: "'at set \<Rightarrow> bool" +
  assumes continuous_plus: "continuous_binary_op (topology \<tau>) (+)"
    and continuous_times: "continuous_binary_op (topology \<tau>) (*)"
    and continuous_uminus: "continuous_map (topology \<tau>) (topology \<tau>) uminus"
    and continuous_inverse: "continuous_map (topology \<tau>) (topology \<tau>) inverse"
begin
text \<open>
  A somewhat Frankensteinian construction.
  The locale \<^locale>\<open>topological_space_ow\<close> is taken from the ETTS-powered
  \<^theory>\<open>Types_To_Sets_Extension.SML_Topological_Space\<close>, and transferred from
  \<^class>\<open>Topological_Spaces.topological_space\<close>. By contrast, \<^term>\<open>continuous_map\<close> stems from
  \<^theory>\<open>HOL-Analysis.Abstract_Topology\<close>. The field operations are still class constants,
  similarly to \<^locale>\<open>vector_space_on\<close>, with topological properties on the carrier \<^term>\<open>F\<close> only.
\<close>
end

locale topological_vector_space_on =
    vector_space_on V scale +
    topological_space_ow V \<tau>\<^sub>V +
    top_F: topological_field_ow F \<tau>\<^sub>F
  for F :: "'a::field set" and \<tau>\<^sub>F :: "'a set \<Rightarrow> bool"
    and V :: "'b::ab_group_add set"
    and scale :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" (infixr "*s" 75)
    and \<tau>\<^sub>V :: "'b set \<Rightarrow> bool" +
  assumes continuous_add: "continuous_binary_op (topology \<tau>\<^sub>V) (+)"
    and continuous_scale: "continuous_map (prod_topology (topology \<tau>\<^sub>F) (topology \<tau>\<^sub>V)) (topology \<tau>\<^sub>V) (\<lambda>(a,v). scale a v)"


subsection \<open>Normed Fields and Vector Spaces\<close>

\<comment> \<open>We can equip a (sub)field with a norm on its carrier set.\<close>
locale normed_field = subfield F for F :: "'a::field set" +
  fixes norm :: "'a\<Rightarrow>real" ("\<Parallel>_\<Parallel>" 100)
  assumes normed_field: "x\<in>F \<Longrightarrow> \<Parallel>x\<Parallel> \<ge> 0"
    "x\<in>F \<Longrightarrow> \<Parallel>x\<Parallel> = 0 \<longleftrightarrow> x = 0"
    "x\<in>F \<Longrightarrow> \<Parallel>-x\<Parallel> = \<Parallel>x\<Parallel>"
    "\<lbrakk>x\<in>F; y\<in>F\<rbrakk> \<Longrightarrow> \<Parallel>x+y\<Parallel> \<le> \<Parallel>x\<Parallel>+\<Parallel>y\<Parallel>"
    "\<lbrakk>x\<in>F; y\<in>F\<rbrakk> \<Longrightarrow> \<Parallel>x*y\<Parallel> \<le> \<Parallel>x\<Parallel>*\<Parallel>y\<Parallel>"


locale valued_field = normed_field +
  assumes multiplicative_norm: "\<lbrakk>x\<in>F; y\<in>F\<rbrakk> \<Longrightarrow> \<Parallel>x*y\<Parallel> = \<Parallel>x\<Parallel>*\<Parallel>y\<Parallel>"
begin

lemma norm_1 [simp]: "\<Parallel>1\<Parallel> = 1"
  by (metis mult_cancel_right1 multiplicative_norm normed_field(2) subfield_1 zero_neq_one)

end

locale seminormed_vector_space_on =
    vector_space_on V scale +
    F: valued_field F field_abs
  for F :: "'f::field set" and field_abs :: "'f\<Rightarrow>real" ("\<parallel>_\<parallel>" [80])
    and V :: "'v::ab_group_add set" and scale :: "'f\<Rightarrow>'v\<Rightarrow>'v" +
  fixes vector_norm :: "'v::ab_group_add \<Rightarrow> real" ("\<Parallel>_\<Parallel>" [65]) \<comment> \<open>At priority 65, you can write sums inside the norm.\<close>
  assumes triangle_add: "\<lbrakk>x\<in>V; y\<in>V\<rbrakk> \<Longrightarrow>
      vector_norm (x+y) \<le> vector_norm x + vector_norm y"
    and absolute_homogeneous: "\<lbrakk>a\<in>F; x\<in>V\<rbrakk> \<Longrightarrow>
      vector_norm (scale a x) = (field_abs a) * (vector_norm x)"
begin

lemma norm_0: "vector_norm 0 = 0"
  using absolute_homogeneous[of 0 0] F.normed_field(2) scale_zero_left mem_zero F.subfield_0
  by fastforce

lemma norm_uminus: "\<Parallel>-x\<Parallel> = \<Parallel>x\<Parallel>" if x: "x \<in> V"
proof -
  have "\<Parallel>-x\<Parallel> = \<parallel>-1\<parallel> * \<Parallel>x\<Parallel>"
    using absolute_homogeneous[OF _ x, of "-1"] by (simp add: scale_minus_left_on x)
  then show "\<Parallel>-x\<Parallel> = \<Parallel>x\<Parallel>"
    using F.normed_field(3)[OF F.subfield_1] absolute_homogeneous x by simp
qed

lemma norm_nonneg [simp]: "x\<in>V \<Longrightarrow> \<Parallel>x\<Parallel> \<ge> 0"
  using mem_uminus norm_0 norm_uminus triangle_add
  by fastforce

end


locale normed_vector_space_on = seminormed_vector_space_on +
  assumes positive_definite: "\<lbrakk>x\<in>V; vector_norm x = 0\<rbrakk> \<Longrightarrow> x = 0"
begin

lemma norm_0_iff: "vector_norm x = 0 \<longleftrightarrow> x = 0" if "x\<in>V"
  using positive_definite norm_0 that by blast

abbreviation (input) induced_metric
  where "induced_metric x y \<equiv> \<Parallel>y-x\<Parallel>"

text \<open>The locale \<^locale>\<open>Metric_space\<close>, which we would like to instantiate, requires things like
  \<^term>\<open>induced_metric x y \<ge> 0\<close>. This is not true in general: @{thm norm_nonneg} only guarantees
  this behaviour inside the carrier set. Thus we have to ``totalise'' the induced metric for use
  in the existing \<^locale>\<open>Metric_space\<close>, by defining behaviour outside the carrier set to satisfy
  the axioms of the locale.\<close>

definition totalized_induced_metric ("\<d>")
(* TODO move defn to seminormed_space - it induces a topology which is Hausdorff iff d is a norm:
    https://en.wikipedia.org/wiki/Seminorm#Pseudometrics_and_the_induced_topology *)
  where "\<d> x y \<equiv> if x\<in>V \<and> y\<in>V then induced_metric x y else 0"

lemma induced_metric_simps [simp]:
  "\<lbrakk>x\<in>V; y\<in>V\<rbrakk> \<Longrightarrow> \<d> x y = induced_metric x y"
  "x\<notin>V \<Longrightarrow> \<d> x y = 0"
  "y\<notin>V \<Longrightarrow> \<d> x y = 0"
  by (simp_all add: totalized_induced_metric_def)

lemma metric_translation_invariant: "\<lbrakk>x\<in>V; y\<in>V; z\<in>V\<rbrakk> \<Longrightarrow> \<d> x y = \<d> (x+z) (y+z)"
  by (simp add: mem_add)
lemma metric_translation_invariant': "\<lbrakk>x\<in>V; y\<in>V\<rbrakk> \<Longrightarrow> \<d> x y = \<d> (x-y) 0"
  using mem_add mem_uminus mem_zero by fastforce

sublocale Metric_space V \<d>
proof
  fix x y z
  show "0 \<le> \<d> x y"
    using mem_add mem_uminus norm_nonneg
    by (metis ab_group_add_class.ab_diff_conv_add_uminus induced_metric_simps le_numeral_extra(3))
  show "\<d> x y = \<d> y x"
    by (metis mem_add mem_uminus minus_diff_eq norm_uminus totalized_induced_metric_def uminus_add_conv_diff)
  assume x: "x\<in>V" and y: "y\<in>V"
  thus "\<d> x y = 0 \<longleftrightarrow> x = y"
    by simp (metis diff_conv_add_uminus eq_iff_diff_eq_0 mem_add mem_uminus norm_0_iff)
  assume z: "z\<in>V"
  have "\<Parallel>z - x\<Parallel> = \<Parallel>(z-y) + (y-x)\<Parallel>" by simp
  also have "\<dots> \<le> \<Parallel>z - y\<Parallel> + \<Parallel>y - x\<Parallel>" (* TODO move to seminorm? *)
    using triangle_add[of "z-y" "y-x"] by (metis diff_conv_add_uminus mem_add mem_uminus x y z)
  finally show "\<d> x z \<le> \<d> x y + \<d> y z"
    using x y z by simp
qed

end


lemma totalized_induced_metric_eq_dist:
  "normed_vector_space_on.totalized_induced_metric UNIV norm = dist"
proof -
  interpret normed_vector_space_on UNIV abs "UNIV :: 'a set" scaleR norm
    apply unfold_locales apply simp_all
    using scaleR_right.add apply blast
    using module.scale_left_distrib module_axioms apply blast
    apply (simp add: abs_mult)
    using abs_mult apply blast
    using norm_triangle_ineq by blast
  show "totalized_induced_metric = dist"
    unfolding totalized_induced_metric_def
    by (auto simp add: Met_TC.commute simp flip: dist_norm)
qed


term \<open>x::'a::real_normed_vector\<close>

locale banach_space_on = normed_vector_space_on +
  assumes "mcomplete"

thm class.cbanach_def
lemma cbanach_is_banach_space_on:
  shows "banach_space_on UNIV cmod (UNIV::'cb::cbanach set) scaleC norm"
  apply unfold_locales apply simp_all
  subgoal using complex_vector.vector_space_assms(1) by blast
  subgoal using complex_vector.vector_space_assms(2) by blast
  subgoal using norm_triangle_ineq by blast
  subgoal using norm_mult_ineq by blast
  subgoal using norm_mult by blast
  subgoal by (simp add: norm_triangle_ineq)
  subgoal
    unfolding totalized_induced_metric_eq_dist mcomplete_iff_complete
    by (simp add: complete_UNIV)
  done


subsection \<open>C* algebras\<close>

(* TODO decompose into normed algebra, Banach, B*, etc *)
locale Cstar_algebra =
    banach_space_on F cmod V scale vector_norm +
(* TODO only complex: should at least be any subfield of the complex numbers, but could probably be more general *)
    involutive_complex_algebra V scale multiplication unit involution
  for F :: "complex set"
    and V :: "'v::ab_group_add set"
    and scale :: "complex \<Rightarrow> 'v \<Rightarrow> 'v"  (infixr \<open>*\<^sub>C\<close> 75)
    and multiplication :: "'v \<Rightarrow> 'v \<Rightarrow> 'v"  (infixr \<open>\<Zspot>\<close> 74)
    and vector_norm :: "'v \<Rightarrow> real"  (\<open>\<Parallel>_\<Parallel>\<close> [65])
    and unit :: "'v" (\<open>\<one>\<close>)
    and involution :: "'v\<Rightarrow>'v" (\<open>_\<^sup>\<dagger>\<close> [99] 100) +
  assumes normed_algebra : "\<And>A B. \<lbrakk>A\<in>V; B\<in>V\<rbrakk> \<Longrightarrow> \<Parallel>A\<Zspot>B\<Parallel> \<le> \<Parallel>A\<Parallel> * \<Parallel>B\<Parallel>"
  assumes normed_unital: "\<Parallel>\<one>\<Parallel> = 1"
  assumes involution_isometric: "\<And>A. A\<in>V \<Longrightarrow> \<Parallel>A\<^sup>\<dagger>\<Parallel> = \<Parallel>A\<Parallel>"
  assumes Cstar: "\<And>A. A\<in>V \<Longrightarrow> \<Parallel>(A\<^sup>\<dagger>) \<Zspot> A\<Parallel> = \<Parallel>A\<^sup>\<dagger>\<Parallel> * \<Parallel>A\<Parallel>"
begin

lemma Bstar: "\<Parallel>(A\<^sup>\<dagger>) \<Zspot> A\<Parallel> = \<Parallel>A\<Parallel>\<^sup>2" if "A\<in>V" for A
  using Cstar[OF that]
  unfolding involution_isometric[OF that] power2_eq_square .

end


lemma Bstar_implies_isometric:
  assumes "seminormed_vector_space_on F cmod V scale vector_norm"
    "involutive_complex_algebra V scale multiplication unit involution"
    and "\<And>A B. \<lbrakk>A\<in>V; B\<in>V\<rbrakk> \<Longrightarrow> vector_norm (multiplication A B) \<le> vector_norm A * vector_norm B" "vector_norm unit = 1"
    and "\<And>A. A\<in>V \<Longrightarrow> vector_norm (multiplication (involution A) A) = (vector_norm A)\<^sup>2"
    and "A\<in>V"
  shows "vector_norm (involution A) = vector_norm A"
proof -
  interpret seminormed_vector_space_on F cmod V scale vector_norm
    using assms(1) .
  interpret involutive_complex_algebra V scale multiplication unit involution
    using assms(2) .
  from assms(3)[of "involution A" A]
  have "(vector_norm A)\<^sup>2 \<le> vector_norm (involution A) * vector_norm A"
    by (simp add: assms(5,6))
  hence ineq_1: "(vector_norm A) \<le> vector_norm (involution A)"
    unfolding power2_eq_square 
    using norm_nonneg[OF involution_mem[OF assms(6)]]
    using nle_le
    by (smt (verit, ccfv_SIG) mult_mono vector_space_over_itself.scale_cancel_right)
  from assms(3)[of A "involution A"]
  have "(vector_norm (involution A))\<^sup>2 \<le> vector_norm A * vector_norm (involution A)"
    by (metis assms(5,6) involution involution_mem)
  hence ineq_2: "(vector_norm (involution A)) \<le> vector_norm A"
    unfolding power2_eq_square 
    using norm_nonneg[OF assms(6)]
    using linorder_not_le by fastforce
  from ineq_1 ineq_2 show ?thesis by force
qed




locale Cstar_subalgebra =
  subalg: Cstar_algebra _ A + Cstar_algebra _ B for A B +
assumes "A \<subseteq> B"
  

lemma (in banach_space_on) closed_iff_complete:
  assumes "A \<subseteq> V"
  shows "closedin mtopology A \<longleftrightarrow> Metric_space.mcomplete A \<d>"
proof -
  interpret sub_A: Submetric V \<d> A
    using assms by unfold_locales
  show ?thesis
    using sub_A.closedin_eq_mcomplete assms banach_space_on_axioms
    by (simp add: banach_space_on_def banach_space_on_axioms_def)
qed

lemma (in normed_vector_space_on) from_subspace:
  assumes "subspace A" "A\<subseteq>V"
  shows "normed_vector_space_on F field_abs A scale vector_norm"
proof -
  interpret VS: vector_space_on A scale
    by (simp add: assms sub_module vector_space_on_alt_def)
  show ?thesis
    apply unfold_locales
    using absolute_homogeneous assms(2) positive_definite triangle_add by (auto simp: in_mono)
qed

text \<open>Not particularly elegantly or generally written: it doesn't matter which (induced) metric we use,
  because all cases outside of the subspace carrier A don't matter. Used for C*-subalgebra intro lemma.\<close>
lemma (in normed_vector_space_on) mcomplete_submetric_equal:
  assumes "A \<subseteq> V" "subspace A"
  shows "Metric_space.mcomplete A (normed_vector_space_on.totalized_induced_metric A vector_norm) = Metric_space.mcomplete A \<d>"
proof -
  interpret VS_A: normed_vector_space_on _ _ A
    using from_subspace[OF assms(2,1)] .
  interpret met_A: Metric_space A \<d>
    apply unfold_locales
    using nonneg commute assms(1) zero triangle subset_iff by (auto simp: in_mono)
  have tot_met_simp: "VS_A.totalized_induced_metric x y = totalized_induced_metric x y" if "x\<in>A" "y\<in>A" for x y
    using assms(1) that totalized_induced_metric_def by auto
  have mball_local_simp: "VS_A.mball x r = met_A.mball x r" for x r
    using tot_met_simp by auto
  show ?thesis
    unfolding VS_A.mcomplete_def met_A.mcomplete_def
    unfolding VS_A.MCauchy_def met_A.MCauchy_def
    unfolding VS_A.mtopology_def met_A.mtopology_def
    unfolding VS_A.mopen_def met_A.mopen_def
    apply (subst mball_local_simp)
    using tot_met_simp by (auto simp: range_subsetD)
qed

lemma (in banach_space_on) closed_iff_complete':
  defines "complete_in_induced_submetric \<equiv>
      \<lambda>A n. Metric_space.mcomplete A (normed_vector_space_on.totalized_induced_metric A n)"
  assumes "A \<subseteq> V" "subspace A"
  shows "closedin mtopology A \<longleftrightarrow> complete_in_induced_submetric A vector_norm"
  using closed_iff_complete mcomplete_submetric_equal assms by simp

lemma (in Cstar_algebra) subalgebraI:
  fixes A
    assumes unital_subalgebra: "subspace A" "A \<subseteq> V" "\<one> \<in> A"
      and mult_closed: "\<forall>x y. x \<in> A \<longrightarrow> y \<in> A \<longrightarrow> x \<Zspot> y \<in> A"
      and involution_closed: "\<forall>x. x \<in> A \<longrightarrow> involution x \<in> A"
      and closed_subset: "closedin mtopology A"
    shows "Cstar_subalgebra F scale (\<Zspot>) vector_norm \<one> involution A V"
proof -
  interpret involutive_subalgebra _ _ _ _ A V
    using subalgebraI[OF assms(1-5)] .
  show ?thesis
    apply unfold_locales
    using triangle_add unital_subalgebra(2) apply blast
    using absolute_homogeneous unital_subalgebra(2) apply blast
    using assms(2) positive_definite apply blast
    using closed_iff_complete'[OF assms(2,1)] closed_subset apply blast
    apply (meson assms(2) normed_algebra subset_iff)
    using normed_unital assms(2) involution_isometric Cstar by blast+
qed

lemma (in Cstar_algebra) subalgebraI':
  fixes A
    assumes unital_subalgebra: "subspace A" "A \<subseteq> V" "\<one> \<in> A"
      and mult_closed: "\<forall>x y. x \<in> A \<longrightarrow> y \<in> A \<longrightarrow> x \<Zspot> y \<in> A"
      and involution_closed: "\<forall>x. x \<in> A \<longrightarrow> involution x \<in> A"
      and complete_subset: "Metric_space.mcomplete A \<d>"
    shows "Cstar_subalgebra F scale (\<Zspot>) vector_norm \<one> involution A V"
  using subalgebraI[OF assms(1-5)] assms(2,6) closed_iff_complete by blast


subsection \<open>Cauchy-Schwarz Inequality for functionals on involutive algebras\<close>
context involutive_complex_algebra begin

text \<open>
  Disable the notation from \<^session>\<open>Jacobson_Basic_Algebra\<close> that conflicts with underlying
  class constants used for our algebras.
\<close>
no_notation additive.inverse ("- _" [66] 65)  \<comment> \<open>conflicts with \<^term>\<open>uminus_class.uminus\<close>\<close>
no_notation subtraction (infixl "-" 65)       \<comment> \<open>conflicts with \<^term>\<open>minus_class.minus\<close>\<close>

lemma additive_inverse_uminus[simp]:
  "additive.inverse A = - A" if "A\<in>S"
  by (simp add: additive.inverse_equality m1.mem_uminus that)

lemma subtraction_minus[simp]:
  "subtraction A B = A - B" if "A\<in>S" "B\<in>S"
  by (simp add: that(2))


declare ivl_uminus [[simp del]]
lemma involution_uminus'[simp]: "involution (- B) = - (involution B)" if "B\<in>S" for B
  using ivl_uminus by (simp add: that)

declare ivl_minus [[simp del]]
lemma ivl_minus'[simp]: "involution (A - B) = involution A - (involution B)"
  if "A\<in>S" "B\<in>S" for B
  using ivl_minus[OF that] by (simp add: that)

end


text \<open>The nomenclature of ``functional'' is taken from operator algebras, where operators are often functions.
  Here ``positive'' is not strict: the corresponding axiom is named after non-negativity.\<close>
locale positive_normalised_linear_functional =
    involutive_complex_algebra S scale multiplication unit involution +
    linear_on S UNIV scale "(*)" \<omega>
  for S :: "'a::ab_group_add set"
    and scale :: "complex \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr \<open>*\<^sub>C\<close> 75)
    and multiplication :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr \<open>\<Zspot>\<close> 74)
    and unit :: "'a" (\<open>\<one>\<close>)
    and involution :: "'a\<Rightarrow>'a" (\<open>_\<^sup>\<dagger>\<close> 73)
    and \<omega> :: "'a\<Rightarrow>complex" +
  assumes nonneg: "A\<in>S \<Longrightarrow> \<omega> ((A\<^sup>\<dagger>) \<Zspot> A) \<ge> 0"
    and one [simp]: "\<omega> \<one> = 1"
begin

(* TODO this should go in involutive_complex_algebra *)
notation cmod ("\<parallel>_\<parallel>") \<comment> \<open>\<^term>\<open>abs\<close> has omitted priority\<close>

lemma nonneg':
  assumes "A \<in> S"
  shows "Re (\<omega> (involution A \<Zspot> A)) \<ge> 0" "Re (\<omega> (A \<Zspot> involution A)) \<ge> 0" "Im (\<omega> (A \<Zspot> involution A)) = 0" "Im (\<omega> (involution A \<Zspot> A)) = 0"
  using nonneg assms involution involution_mem
  by (metis zero_complex.simps(1) Re_mono,
      metis zero_complex.simps(1) Re_mono,
      (metis comp_Im_same zero_complex.simps(2))+)

lemma involution_conjugate: "\<omega> (involution A) = cnj (\<omega> A)" if "A \<in> S"
proof -
  have is_Real: "Im (\<alpha> * \<omega> A + cnj \<alpha> * \<omega> (involution A)) = 0" if "A \<in> S" for \<alpha>::complex and A
  proof -
    let ?s = "\<one> + \<alpha> *\<^sub>C A" \<comment> \<open>This is the crucial starting ``guess''.\<close>
    note [simp] = m1.mem_scale
    have inS [simp]: "A \<in> S" "involution A \<in> S" "?s \<in> S"
      by (simp_all add: that)
    have "?s \<Zspot> involution ?s = \<one> \<Zspot> involution (\<one> + \<alpha> *\<^sub>C A) + \<alpha> *\<^sub>C A \<Zspot> involution (\<one> + \<alpha> *\<^sub>C A)"
      by (simp add: distR[of \<one> "\<alpha> *\<^sub>C A" "involution ?s"])
    also have "\<dots> = \<one> + involution (\<alpha> *\<^sub>C A) + \<alpha> *\<^sub>C A + \<alpha> *\<^sub>C A \<Zspot> involution (\<alpha> *\<^sub>C A)"
      by (simp add: ivl_ring unit_self_adjoint algebra_simps distL)
    finally have "?s \<Zspot> involution ?s = \<one> + \<bar>\<alpha>\<bar>\<^sup>2 *\<^sub>C A\<Zspot>(involution A) + \<alpha> *\<^sub>C A + involution (\<alpha> *\<^sub>C A)"
      using ivl_scale using complex_norm_square[of \<alpha>] by (simp add: abs_complex_def mult.commute)
    then have "Im (\<alpha> * \<omega> A + cnj \<alpha> * \<omega> (involution A)) = Im (\<omega> (?s \<Zspot> involution ?s))"
      by (simp add: abs_complex_def add scale ivl_scale nonneg'(3))
    then show ?thesis
      by (simp add: nonneg'(3))
  qed
  have re_im_decompose: "0 = Re a * (Im (\<omega> A) + Im (\<omega> (involution A))) + Im a * (Re (\<omega> A) - Re (\<omega> (involution A)))"
    for a::complex
    using is_Real[OF that, of a]
    by (simp add: vector_space_over_itself.scale_right_diff_distrib vector_space_over_itself.scale_right_distrib)
  have "Im (\<omega> A) + Im (\<omega> (involution A)) = 0" "Re (\<omega> A) - Re (\<omega> (involution A)) = 0"
    using re_im_decompose[of 1] re_im_decompose[of \<i>] by simp_all
  thus ?thesis by (simp add: complex_eq_iff)
qed

lemma cnj_ivl: "cnj (\<omega> (involution A)) = \<omega> (A)" if "A \<in> S"
  using involution_conjugate that by simp

text \<open>
  Any such functional can be used to define a sesquilinear form that acts as a generalised inner
  product. This interpretation is justified below by providing a Cauchy-Schwarz inequality.
\<close> (* TODO define/instantiate a locale for sesquilinear? *)
definition functional_inner :: "'a \<Rightarrow> 'a \<Rightarrow> complex" ("\<langle>_|_\<rangle>" 76)
  where "functional_inner A B \<equiv> \<omega> ((A\<^sup>\<dagger>) \<Zspot> B)"

named_theorems finner_simps

(* TODO good for simp? better to have geq_real_def and \<open>\<omega> (A \<Zspot> involution A) \<ge>\<^sub>R 0\<close> as simp rules instead? *)
lemma finner_nonneg [finner_simps]:
  assumes "A \<in> S"
  shows "\<langle>A|A\<rangle> \<ge> 0"
  using nonneg by (simp add: assms functional_inner_def)

lemma finner_scale [finner_simps]:
    "\<langle>c *\<^sub>C A|B\<rangle> = (cnj c) * \<langle>A|B\<rangle>"
    "\<langle>A|c *\<^sub>C B\<rangle> = c * \<langle>A|B\<rangle>"
  if "A\<in>S" "B\<in>S" for c and A B
  unfolding functional_inner_def
  subgoal using involution_mem that scale ivl_scale linearL'(1) multiplicative.composition_closed by presburger
  subgoal using involution_mem that multiplicative.composition_closed scalar_compat'(2) scale by presburger
  done

lemma finner_plus [finner_simps]: "\<langle>A+B|C\<rangle> = \<langle>A|C\<rangle> + \<langle>B|C\<rangle>" "\<langle>A|B+C\<rangle> = \<langle>A|B\<rangle> + \<langle>A|C\<rangle>"
  if "A\<in>S" "B\<in>S" "C\<in>S" for A B C
  unfolding functional_inner_def
  subgoal using involution_mem that add amult_closed distR ivl_ring by presburger
  subgoal using involution_mem that add amult_closed distL by presburger
  done

lemma finner_uminus [finner_simps]: "\<langle>uminus A|B\<rangle> = uminus (\<langle>A|B\<rangle>)" "\<langle>A|uminus B\<rangle> = uminus (\<langle>A|B\<rangle>)"
      if "A\<in>S" "B\<in>S" for c and A B
  using ivl_uminus mapsto_uminus by (simp_all add: that functional_inner_def)

lemma finner_minus [finner_simps]: "\<langle>A-B|C\<rangle> = \<langle>A|C\<rangle> - \<langle>B|C\<rangle>" "\<langle>A|B-C\<rangle> = \<langle>A|B\<rangle> - \<langle>A|C\<rangle>"
  if "A\<in>S" "B\<in>S" "C\<in>S" for c and A B C
  subgoal using finner_plus[OF _ m1.mem_uminus] finner_uminus(1) that by force
  subgoal using finner_plus[OF _ _ m1.mem_uminus] finner_uminus(2) that by force
  done

lemma finner_cnj:"\<langle>A|B\<rangle> = cnj (\<langle>B|A\<rangle>)"
  if "A\<in>S" "B\<in>S" for A B
  unfolding functional_inner_def
  using involution_conjugate[of "involution A \<Zspot> B"] antiautomorphism[of "involution A" B] involution[OF that(1)]
  by (simp add: that)

lemma finner_real_commute:
  assumes "A\<in>S" "B\<in>S" "\<langle>A|B\<rangle> \<in> \<real>"
  shows "\<langle>A|B\<rangle> = \<langle>B|A\<rangle>"
  using cnj_ivl[of "involution B \<Zspot> A"] antiautomorphism[of "involution B" A] involution[of B] assms(3)[unfolded Reals_cnj_iff]
  by (simp add: assms(1,2) functional_inner_def)

lemma finner_zero_commute:
  assumes "A\<in>S" "B\<in>S" "\<langle>A|B\<rangle> = 0"
  shows "\<langle>B|A\<rangle> = 0"
  using finner_real_commute assms Reals_0 by metis

lemma finner_self_0_if: "\<langle>A|A\<rangle> = 0" if "A = 0"
  by (simp add: functional_inner_def mapsto_zero that)

lemma pythagorean_theorem:
  assumes "A\<in>S" "B\<in>S" "\<langle>A|B\<rangle> = 0"
  shows "\<langle>A+B|A+B\<rangle> = \<langle>A|A\<rangle> + \<langle>B|B\<rangle>"
proof (unfold functional_inner_def)
  have inS: "involution A \<in> S" "involution B \<in> S" "involution A \<Zspot> B \<in> S" "involution B \<Zspot> A \<in> S"
    by (simp_all add: assms)
  have BA_0: "\<omega> (involution B \<Zspot> A) = 0"
    using involution antiautomorphism complex_cnj_zero cnj_ivl[symmetric]
    by (simp only: assms(1,2,3)[unfolded functional_inner_def] inS)
  have "\<omega> ((involution (A + B)) \<Zspot> (A + B)) = \<omega> ((involution A \<Zspot> A) + involution A \<Zspot> B + involution B \<Zspot> A + involution B \<Zspot> B)"
    by (simp add: add.commute add.left_commute assms(1,2) distributive inS(1,2) ivl_ring)
  thus "\<omega> (involution (A + B) \<Zspot> (A + B)) = \<omega> (involution A \<Zspot> A) + \<omega> (involution B \<Zspot> B)"
    using add BA_0 finner_zero_commute[OF assms]
    using assms(1,2,3) functional_inner_def by fastforce
qed

lemma finner_csqrt_nonneg: "csqrt (\<langle>X|X\<rangle>) \<ge> 0" if "X\<in>S"
  unfolding less_eq_complex_def
  using finner_nonneg Re_csqrt apply simp
  using cmod_Re that by blast+

lemma finner_cmod_eq: " \<parallel>\<langle>B|B\<rangle>\<parallel> = \<langle>B|B\<rangle>" if "B\<in>S"
  using cmod_Re finner_nonneg nonnegative_complex_is_real of_real_Re that by presburger

definition functional_norm :: "'a \<Rightarrow> real" ("\<Parallel>_\<Parallel>\<^sub>\<omega>")
  where "functional_norm X \<equiv> Re (csqrt (\<langle>X|X\<rangle>))"

lemma fnorm_finner_squared: "\<langle>B|B\<rangle> = \<Parallel>B\<Parallel>\<^sub>\<omega>\<^sup>2" "\<parallel>\<langle>B|B\<rangle>\<parallel> = \<Parallel>B\<Parallel>\<^sub>\<omega>\<^sup>2" if "B\<in>S"
  unfolding functional_norm_def
  apply (metis Re_power_real complex_is_Real_iff complex_is_real_iff_compare0 finner_csqrt_nonneg functional_inner_def nonneg'(4) of_real_Re power2_csqrt that)
  by (metis cmod_Re finner_csqrt_nonneg norm_power power2_csqrt that)

lemma fnorm_nonneg: "\<Parallel>X\<Parallel>\<^sub>\<omega> \<ge> 0"
  using Re_csqrt functional_norm_def by presburger

lemma finner_lindep:
  fixes c::complex
  assumes "B\<in>S"
  shows "\<parallel>\<langle>c *\<^sub>C B|B\<rangle>\<parallel> = \<parallel>c\<parallel> * \<Parallel>B\<Parallel>\<^sub>\<omega>\<^sup>2"
    using finner_scale(1)[OF assms assms] fnorm_finner_squared(2)[OF assms]
    by (simp add: norm_mult)

lemma fnorm_scale: "\<Parallel>c *\<^sub>C X\<Parallel>\<^sub>\<omega> = \<parallel>c\<parallel> * \<Parallel>X\<Parallel>\<^sub>\<omega>" if "X\<in>S" for c::complex
proof (unfold functional_norm_def)
  have 2: "\<langle>c *\<^sub>C X|c *\<^sub>C X\<rangle> = c * cnj c * \<langle>X|X\<rangle>"
    using finner_scale(1) finner_scale(2)[OF m1.mem_scale] by (simp add: that)
  have "\<parallel>\<langle>c *\<^sub>C X|c *\<^sub>C X\<rangle>\<parallel> = Re (\<langle>c *\<^sub>C X|c *\<^sub>C X\<rangle>)" "\<parallel>\<langle>X|X\<rangle>\<parallel> = Re (\<langle>X|X\<rangle>)"
    using cmod_Re finner_nonneg(1)
    by (simp add: functional_inner_def less_eq_complexI m1.mem_scale nonneg'(3) that
        del: involution_mem)+
  thus "Re (csqrt (\<langle>c *\<^sub>C X|c *\<^sub>C X\<rangle>)) = \<parallel>c\<parallel> * Re (csqrt (\<langle>X|X\<rangle>))"
    apply simp
    using 2 cmod_Re complex_mod_sqrt_Re_mult_cnj real_sqrt_mult
    by (metis (no_types, lifting) cnj_x_x_geq0 mult.commute norm_mult)
qed

lemma finner_lindep_cong:
  assumes "B\<in>S" "A = c *\<^sub>C B"
  shows "\<parallel>\<langle>A|B\<rangle>\<parallel> = \<Parallel>A\<Parallel>\<^sub>\<omega> * \<Parallel>B\<Parallel>\<^sub>\<omega>"
  using finner_lindep fnorm_scale
  by (simp add: assms power2_eq_square)


context \<comment> \<open>Controlling notation for partitions/division.\<close> begin
no_notation equivalence.Partition (infixl \<open>'/\<close> 75)

\<comment> \<open>Stolen from \<open>Polygonal_Number_Theorem.Polygonal_Number_Theorem_Lemmas.qua_disc\<close>
  on the AFP. The import brought in too many dependencies to be worth it.\<close>
lemma qua_disc:
  fixes a b c :: real
  assumes "a>0"
  assumes "\<forall>x::real. a*x^2+b*x + c \<ge> 0"
  shows "b^2 - 4 * a * c \<le> 0"
proof -
  from assms have 0:"\<forall>x::real. (a*x^2 + b*x + c)/a \<ge>0" by simp
  from assms have 1:"\<forall>x::real.(b*x + c)/a = b/a*x + c/a" by (simp add: add_divide_distrib)
  from assms have "\<forall>x::real.(a*x^2 + b*x + c)/a = x^2 + (b*x + c)/a"
    by (simp add: add_divide_eq_if_simps(1))
  from 1 this have "\<forall>x::real.(a*x^2 + b*x  +  c)/a = x^2 + b/a*x + c/a" by simp
  hence atleastzero:"\<forall>x::real. x^2 + b/a*x + c/a \<ge>0" using 0 by simp

  from assms have 2:"\<forall>x::real. x^2 + b/a*x + c/a = x^2 + 2*b/(2*a)*x + c/a + b^2/(4*a^2)-b^2/(4*a^2)" by simp
  have simp1:"\<forall>x::real.(x + b/(2*a))^2 = x^2 + 2*b/(2*a)*x + (b/(2*a))^2" by (simp add: power2_sum)
  have "(b/(2*a))^2 = b^2/(4*a^2)" by (metis four_x_squared power_divide)
  hence "\<forall>x::real. x^2 + b/a*x + c/a = (x + b/(2*a))^2 + c/a-b^2/(4*a^2)" using 2 simp1 by auto
  hence "\<forall>x::real. (x + b/(2*a))^2 + c/a-b^2/(4*a^2) \<ge>0" using atleastzero by presburger
  hence 3:"\<forall>x::real. b^2/(4*a^2)-c/a\<le>(x + b/(2*a))^2" by (smt (verit, del_insts))
  have "\<exists>x::real. (x + b/(2*a))^2=0" by (metis diff_add_cancel power_zero_numeral)
  hence "b^2/(4*a^2)-c/a\<le>0" using 3 by metis
  hence 4:"4*a^2*(b^2/(4*a^2)-c/a)\<le>0" using assms by (simp add: mult_nonneg_nonpos)
  have 5:"4*a^2*b^2/(4*a^2) = b^2" using assms by simp
  have 6:"4*a^2 * c/a = 4*a * c" using assms by (simp add: power2_eq_square)
  show ?thesis using 4 5 6 assms by (simp add: Rings.ring_distribs(4))
qed

lemma sign_of_discriminant:
  fixes a b c :: real
  assumes "\<forall>x::real. a*x^2 + b*x + c \<ge>0"
  shows "a \<ge> 0 \<Longrightarrow> b^2 - 4 * a * c \<le> 0" "a < 0 \<Longrightarrow> b^2 - 4 * a * c \<ge> 0"
  subgoal apply (cases "a=0")
    subgoal by (metis Groups.add_ac(2) assms diff_add_cancel diff_zero mult_zero_left mult_zero_right
      nonzero_mult_div_cancel_left real_sqrt_pow2 sum_power2_le_zero_iff times_divide_eq_right zero_eq_power2)
    subgoal using qua_disc assms by simp
    done
  subgoal using assms by (smt (verit, ccfv_threshold) zero_compare_simps(8,12))
  done

end


lemma cauchy_schwarz_square:
  assumes "A\<in>S" "B\<in>S"
  shows "\<bar>\<langle>A|B\<rangle>\<bar>\<^sup>2 \<le> \<langle>A|A\<rangle> * \<langle>B|B\<rangle>"
proof -
  consider (some_zero) "A=0 \<or> B=0" | (nonzero) "A\<noteq>0 \<and> B\<noteq>0" by fastforce
  then show ?thesis
  proof (cases)
    case some_zero
    then show ?thesis
      using finner_plus(1) finner_zero_commute
      by (metis assms cnj_x_x cnj_x_x_geq0 eq_add_iff mult_eq_0_iff)
  next
    case nonzero \<comment> \<open>Mostly revolves around the discriminant of a quadratic,
        and the inequality @{thm qua_disc} (cribbed from \<open>Polygonal_Number_Theorem\<close>).\<close>

    let ?c = "\<bar>\<langle>B|A\<rangle>\<bar> / \<langle>B|A\<rangle>"
    have c_witness: "\<parallel>?c\<parallel> = 1" "?c * \<langle>B|A\<rangle> = \<bar>\<langle>B|A\<rangle>\<bar>" if "\<langle>B|A\<rangle> \<noteq> 0"
      using Real_Vector_Spaces.norm_divide[of "\<parallel>\<langle>B|A\<rangle>\<parallel>" "\<langle>B|A\<rangle>"] that
      by (simp_all add: abs_complex_def)
    have "\<exists>c::complex. cmod c = 1 \<and> c * \<langle>B|A\<rangle> = \<bar>\<langle>B|A\<rangle>\<bar>"
      apply (cases "\<langle>B|A\<rangle>=0")
      subgoal using norm_one by fastforce
      using c_witness by blast
    then
    obtain c :: complex
      where c: "cmod c = 1" "c * \<langle>B|A\<rangle> = \<bar>\<langle>B|A\<rangle>\<bar>"
      by blast
    { fix x :: complex assume x: "x\<in>\<real>"
      have "\<langle>(x * c) *\<^sub>C A + B|(x * c) *\<^sub>C A + B\<rangle> =
          \<langle>(x * c) *\<^sub>C A|(x * c) *\<^sub>C A\<rangle> +
          \<langle>(x * c) *\<^sub>C A|B\<rangle> + \<langle>B|(x * c) *\<^sub>C A\<rangle> + \<langle>B|B\<rangle>"
        using m1.mem_scale finner_plus by (simp add: assms finner_plus(1))+
      also have "\<dots> = (cmod (x * c))\<^sup>2 * \<langle>A|A\<rangle> + \<langle>(x * c) *\<^sub>C A|B\<rangle> + \<langle>B|(x * c) *\<^sub>C A\<rangle> + \<langle>B|B\<rangle>"
        apply (simp add: complex_mod_mult_cnj del: Real_Vector_Spaces.of_real_power)
        using finner_scale[OF assms(1), of _ "x * c"] m1.mem_scale[OF assms(2)]
        using assms(1) complex_norm_square m1.mem_scale by auto
      also have "\<dots> = (cmod (x * c))\<^sup>2 * \<langle>A|A\<rangle> + cnj (x * c) * \<langle>A|B\<rangle> + (x * c) * \<langle>B|A\<rangle> + \<langle>B|B\<rangle>"
        using finner_scale m1.mem_scale assms by simp
      also have "\<dots> = \<parallel>x * c\<parallel>\<^sup>2 * \<langle>A|A\<rangle> +
          cnj (x * c * \<langle>B|A\<rangle>) + ((x * c) * \<langle>B|A\<rangle>) + \<langle>B|B\<rangle>"
        by (metis assms complex_cnj_mult finner_cnj)
      also have "\<dots> = \<bar>x * c\<bar>\<^sup>2 * \<langle>A|A\<rangle> + cnj (x*\<bar>\<langle>B|A\<rangle>\<bar>) + (x*\<bar>\<langle>B|A\<rangle>\<bar>) + \<langle>B|B\<rangle>"
        apply (simp add: complex_of_real_cmod)
        using c(2) by (metis Extra_Ordered_Fields.sign_simps(4) complex_cnj_mult)
      also have "\<dots> = \<parallel>\<langle>A|A\<rangle>\<parallel> * x\<^sup>2 + (2*\<parallel>\<langle>B|A\<rangle>\<parallel>)*x + \<parallel>\<langle>B|B\<rangle>\<parallel>"
        unfolding fnorm_finner_squared(2)[OF assms(1)] fnorm_finner_squared(2)[OF assms(2)]
        apply (simp add: complex_of_real_cmod)
        using c(1) Reals_cnj_iff x assms abs_complex_real complex_norm_square complex_of_real_cmod
          fnorm_finner_squared(1) norm_mult norm_one
        by (smt (verit) sign_simps(3,5) more_arith_simps(6) of_real_power power2_eq_square)
      finally
      have "\<Parallel>A\<Parallel>\<^sub>\<omega>\<^sup>2 * x\<^sup>2 + (2*\<parallel>\<langle>B|A\<rangle>\<parallel>)*x + \<Parallel>B\<Parallel>\<^sub>\<omega>\<^sup>2 \<ge> 0"
        unfolding fnorm_finner_squared(2)[OF assms(1)] fnorm_finner_squared(2)[OF assms(2)]
        by (metis assms finner_nonneg m1.mem_add m1.mem_scale) }
    note quadratic_nonnegative = this
    have "0 \<le> \<parallel>\<langle>A|A\<rangle>\<parallel> * x\<^sup>2 + 2 * \<parallel>\<langle>B|A\<rangle>\<parallel> * x + \<parallel>\<langle>B|B\<rangle>\<parallel>" for x::real
      using quadratic_nonnegative[of x, simplified]
      unfolding functional_norm_def
      using assms(1,2) fnorm_finner_squared(1) quadratic_nonnegative
      by (smt (verit, ccfv_threshold) Re_complex_of_real Reals_of_real cmod_Re finner_nonneg less_eq_complex_def
          of_real_0 of_real_mult of_real_power plus_complex.sel(1))
    hence "(2*\<parallel>\<langle>B|A\<rangle>\<parallel>)\<^sup>2 - 4*\<parallel>\<langle>A|A\<rangle>\<parallel>*\<parallel>\<langle>B|B\<rangle>\<parallel> \<le> 0"
      using sign_of_discriminant(1) zero_le_power norm_ge_zero
      by blast
    then show ?thesis
      apply (simp add: abs_complex_def)
      apply (subst of_real_power[of "\<parallel>\<langle>A|B\<rangle>\<parallel>" 2, symmetric])
      using norm_of_real of_real_0 of_real_mult
      by (smt (verit, del_insts) Im_complex_of_real Re_complex_of_real assms(1,2) cnj_x_x complex_norm_square
          finner_cnj finner_nonneg fnorm_finner_squared(1) less_eq_complex_def
          x_cnj_x)
  qed
qed

lemma cauchy_schwarz:
  assumes "A\<in>S" "B\<in>S"
  shows "\<parallel>\<langle>A|B\<rangle>\<parallel> \<le> \<Parallel>A\<Parallel>\<^sub>\<omega> * \<Parallel>B\<Parallel>\<^sub>\<omega>"
proof -
  from cauchy_schwarz_square[OF assms]
  have "\<parallel>\<langle>A|B\<rangle>\<parallel>\<^sup>2 \<le> \<Parallel>A\<Parallel>\<^sub>\<omega>\<^sup>2 * \<Parallel>B\<Parallel>\<^sub>\<omega>\<^sup>2" (* . ChatGPT fails *)
    (* by (smt (verit, ccfv_SIG) Re_complex_of_real assms complex_of_real_cmod fnorm_finner_squared(1)
        less_eq_complex_def of_real_mult of_real_power) (* sledgehammer succeeds *) *)
    unfolding abs_complex_def by (simp add: assms fnorm_finner_squared(1) less_eq_complex_def)
  hence "\<parallel>\<langle>A|B\<rangle>\<parallel> \<le> sqrt (\<Parallel>A\<Parallel>\<^sub>\<omega>\<^sup>2 * \<Parallel>B\<Parallel>\<^sub>\<omega>\<^sup>2)"
    (* by (simp add: real_le_lsqrt) ChatGPT fails *)
    using real_le_rsqrt by blast (* sledgehammer succeeds *)
  also have "sqrt (\<Parallel>A\<Parallel>\<^sub>\<omega>\<^sup>2 * \<Parallel>B\<Parallel>\<^sub>\<omega>\<^sup>2) = \<Parallel>A\<Parallel>\<^sub>\<omega> * \<Parallel>B\<Parallel>\<^sub>\<omega>"
    (* by (simp add: real_sqrt_mult) ChatGPT fails *)
    by (simp add: fnorm_nonneg real_sqrt_mult) (* sledgehammer succeeds *)
  finally show ?thesis .
qed


subsection \<open>Identities for states on unital $C^*$-algebras\<close>
text\<open>For now, see \cite[page 49, Prop.~2.3.11]{bratteli1979}.
  We already have @{thm involution_conjugate}.\<close>

lemma state_norm_leq_inner: "\<parallel>\<omega> A\<parallel>\<^sup>2 \<le> \<langle>A|A\<rangle>" if "A\<in>S"
  using cauchy_schwarz_square[OF that, of \<one>]
  unfolding functional_inner_def
  by (metis amult_id(3) antiautomorphism cnj_ivl cnj_x_x complex_norm_square involution_conjugate
      local.one more_arith_simps(6) multiplicative.unit_closed that unit_self_adjoint)

lemma state_zero_if_inner_zero: "\<omega> A = 0" if "\<omega> (involution A \<Zspot> A) = 0" "A\<in>S"
proof-
  have "(norm (\<omega> A))\<^sup>2 = 0"
    using state_norm_leq_inner apply (simp add: functional_inner_def)
    by (metis complex_of_real_mono_iff norm_le_zero_iff
        norm_power of_real_eq_0_iff of_real_power that zero_eq_power2)
  thus ?thesis by simp
qed

end (* positive_normalised_linear_functional *)


locale Cstar_state =
    Cstar_algebra F S scale multiplication vector_norm unit involution +
    positive_normalised_linear_functional S scale multiplication unit involution \<omega>
  for F :: "complex set"
    and S :: "'a::ab_group_add set"
    and scale :: "complex \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr \<open>*\<^sub>C\<close> 75)
    and multiplication :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr \<open>\<Zspot>\<close> 74)
    and vector_norm :: "'a \<Rightarrow> real"  (\<open>\<Parallel>_\<Parallel>\<close> [65])
    and unit :: "'a" (\<open>\<one>\<close>)
    and involution :: "'a\<Rightarrow>'a" ("_\<^sup>\<dagger>" [99] 100)
    and \<omega> :: "'a\<Rightarrow>complex"
begin

(* TODO name *)
lemma mult_inner_norm_bound:
  assumes "\<And>A B. \<lbrakk>A\<in>S; B\<in>S\<rbrakk> \<Longrightarrow> \<langle>B \<Zspot> A|B \<Zspot> A\<rangle> \<le> \<Parallel>B\<Parallel>\<^sup>2 * \<omega> (A\<^sup>\<dagger> \<Zspot> A)"
    \<comment> \<open>This assumption is, in fact, a theorem. It can be proven using spectral theory,
    by defining positive operators to enable the following ordering relation:
    $$A^\dagger B^\dagger B A \leq \|B\|^2 A^\dagger A$$
    See Bratteli and Robinson's textbook, p.~51 for proof of the lemma,
    and p.~36 for ordering on positive operators \cite{bratteli1979}.
    The definition of an operator as positive depends on the operator's spectrum
    (i.e.~it is in the positive half-line, p.~32).
    Spectral theory is, for now, out of scope for this development.\<close>
    and "A\<in>S" "B\<in>S"
  shows "\<bar>\<langle>B \<Zspot> A|A\<rangle>\<bar> \<le> \<langle>A|A\<rangle> * \<Parallel>B\<Parallel>"
proof-
  have "\<bar>\<langle>B \<Zspot> A|A\<rangle>\<bar>\<^sup>2 \<le> \<langle>B \<Zspot> A|B \<Zspot> A\<rangle> * \<langle>A|A\<rangle>"
    using cauchy_schwarz_square[of \<open>B\<Zspot>A\<close> \<open>A\<close>]
    by (auto simp: assms(2,3))
  also have "\<dots> \<le> (\<Parallel>B\<Parallel>\<^sup>2) * \<omega> (involution A \<Zspot> A) * \<langle>A|A\<rangle>"
    using assms(1)[OF assms(2,3)] finner_nonneg[OF assms(2)] mult_right_mono by blast
  finally have "\<bar>\<langle>B \<Zspot> A|A\<rangle>\<bar>\<^sup>2 \<le> \<langle>A|A\<rangle> * (\<Parallel>B\<Parallel>\<^sup>2) * \<langle>A|A\<rangle>"
    by (metis Extra_Ordered_Fields.sign_simps(5) functional_inner_def)
  then have "\<bar>\<langle>B \<Zspot> A|A\<rangle>\<bar>\<^sup>2 \<le> (\<langle>A|A\<rangle> * \<Parallel>B\<Parallel>)\<^sup>2"
    by (smt (verit) of_real_power ordered_field_class.sign_simps(23,4,5) power2_eq_square)
  moreover have "\<bar>0\<bar> \<le> \<bar>\<langle>B \<Zspot> A|A\<rangle>\<bar>" by (simp add: abs_nn)
  ultimately have "\<parallel>\<langle>B \<Zspot> A|A\<rangle>\<parallel> \<le> Re(\<langle>A|A\<rangle>) * \<Parallel>B\<Parallel>"
    apply (intro power2_le_imp_le[of "\<parallel>\<langle>B \<Zspot> A|A\<rangle>\<parallel>" "Re (\<langle>A|A\<rangle>) * \<Parallel>B\<Parallel>"])
    subgoal using finner_cmod_eq x_cnj_x
      by (smt (verit, best) Re_complex_of_real complex_norm_square
          less_eq_complex_def of_real_mult of_real_power assms(2))
    subgoal by (simp add: assms(2,3) functional_inner_def nonneg'(1))
    done
  thus ?thesis
    by (metis Re_complex_of_real Reals_cnj_iff assms(2) of_real_mult
        complex_cnj_complex_of_real complex_is_Real_iff
        complex_of_real_cmod finner_cmod_eq less_eq_complexI)
qed

end (* Cstar_state *)


subsection \<open>Morphisms\<close>

locale involutive_complex_algebras =
  A1: involutive_complex_algebra S1 scale1 multiplication1 unit1 involution1 +
  A2: involutive_complex_algebra S2 scale2 multiplication2 unit2 involution2
  for S1 :: "'a::ab_group_add set"
    and scale1 :: "complex \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr \<open>*\<^sub>C\<^sub>1\<close> 75)
    and multiplication1 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr \<open>\<Zspot>\<^sub>1\<close> 74)
    and unit1 :: "'a" (\<open>\<one>\<^sub>1\<close>)
    and involution1 :: "'a\<Rightarrow>'a"
    and S2 :: "'b::ab_group_add set"
    and scale2 :: "complex \<Rightarrow> 'b \<Rightarrow> 'b"  (infixr \<open>*\<^sub>C\<^sub>2\<close> 75)
    and multiplication2 :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"  (infixr \<open>\<Zspot>\<^sub>2\<close> 74)
    and unit2 :: "'b" (\<open>\<one>\<^sub>2\<close>)
    and involution2 :: "'b\<Rightarrow>'b"


text \<open>We define *-homomorphisms to be unital always. I believe a minority
  of authors consider non-unital homomorphisms of rings, but then you need
  to consider degenerate cases (e.g. \<^term>\<open>\<lambda>x. 0\<close>). For some discussion, see e.g.
  \href{mathoverflow}{
    https://mathoverflow.net/questions/34332/consequences-of-not-requiring-ring-homomorphisms-to-be-unital
  }.\<close>
locale involutive_complex_homomorphism = involutive_complex_algebras +
  fixes f :: "'a\<Rightarrow>'b"
  assumes f_codomain: "f`S1 \<subseteq> S2"
    and f_unit: "f \<one>\<^sub>1 = \<one>\<^sub>2"
    and f_scale: "\<And>r x. \<lbrakk>x\<in>S1\<rbrakk> \<Longrightarrow> f (r *\<^sub>C\<^sub>1 x) = r *\<^sub>C\<^sub>2 (f x)"
    and f_plus: "\<And>x y. \<lbrakk>x\<in>S1; y\<in>S1\<rbrakk> \<Longrightarrow> f (x + y) = (f x) + (f y)"
    and f_multiplication: "\<And>x y. \<lbrakk>x\<in>S1; y\<in>S1\<rbrakk> \<Longrightarrow>
      f (x \<Zspot>\<^sub>1 y) = (f x) \<Zspot>\<^sub>2 (f y)"
    and f_involution: "\<And>x. \<lbrakk>x\<in>S1\<rbrakk> \<Longrightarrow>
      f (involution1 x) = involution2 (f x)"
begin

lemma linear_f: "linear_on S1 S2 scale1 scale2 f"
  apply unfold_locales
  using f_plus f_scale by auto

interpretation linear_f: linear_on S1 S2 scale1 scale2 f
  using linear_f .

end (* involutive_complex_homomorphism *)

abbreviation (in involutive_complex_algebras) homomorphism
  where "homomorphism f \<equiv> involutive_complex_homomorphism
    S1 scale1 multiplication1 unit1 involution1
    S2 scale2 multiplication2 unit2 involution2
    f"

locale involutive_complex_isomorphism = involutive_complex_homomorphism +
  assumes bij_f: "bij_betw f S1 S2"

abbreviation (in involutive_complex_algebras) isomorphism
  where "isomorphism f \<equiv> involutive_complex_isomorphism
    S1 scale1 multiplication1 unit1 involution1
    S2 scale2 multiplication2 unit2 involution2
    f"

locale involutive_complex_automorphism =
    involutive_complex_isomorphism S scale multiplication unit involution
                                   S scale multiplication unit involution f
  for S scale multiplication unit involution f

abbreviation (in involutive_complex_algebra) automorphism
  where "automorphism f \<equiv> involutive_complex_automorphism S scale multiplication unit involution f"




locale Cstar_algebras =
  A1: Cstar_algebra F1 S1 scale1 multiplication1 vnorm1 unit1 involution1 +
  A2: Cstar_algebra F2 S2 scale2 multiplication2 vnorm2 unit2 involution2
  for F1 :: "complex set"
    and S1 :: "'a::ab_group_add set"
    and scale1 :: "complex \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr \<open>*\<^sub>C\<^sub>1\<close> 75)
    and multiplication1 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr \<open>\<Zspot>\<^sub>1\<close> 74)
    and vnorm1 :: "'a \<Rightarrow> real"  (\<open>\<Parallel>_\<Parallel>\<^sub>1\<close> [65])
    and unit1 :: "'a" (\<open>\<one>\<^sub>1\<close>)
    and involution1 :: "'a\<Rightarrow>'a"
    and F2 :: "complex set"
    and S2 :: "'b::ab_group_add set"
    and scale2 :: "complex \<Rightarrow> 'b \<Rightarrow> 'b"  (infixr \<open>*\<^sub>C\<^sub>2\<close> 75)
    and multiplication2 :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"  (infixr \<open>\<Zspot>\<^sub>2\<close> 74)
    and vnorm2 :: "'b \<Rightarrow> real"  (\<open>\<Parallel>_\<Parallel>\<^sub>2\<close> [65])
    and unit2 :: "'b" (\<open>\<one>\<^sub>2\<close>)
    and involution2 :: "'b\<Rightarrow>'b"
begin

sublocale involutive_complex_algebras
  by unfold_locales

end

text \<open>A $C^*$-homomorphism is a homomorphism of $\phantom{}^*$-algebras between $C^*$-algebras.\<close>
locale Cstar_homomorphism = Cstar_algebras + involutive_complex_homomorphism


lemma (in Cstar_algebras) homomorphismI:
  assumes "homomorphism f"
  shows "Cstar_homomorphism F1 S1 scale1 multiplication1 vnorm1 unit1 involution1
                            F2 S2 scale2 multiplication2 vnorm2 unit2 involution2 f"
  by (simp add: assms Cstar_algebras_axioms Cstar_homomorphism.intro)


locale Cstar_isomorphism = Cstar_algebras + involutive_complex_isomorphism


locale Cstar_automorphism =
    Cstar_isomorphism F V scale multiplication vector_norm unit involution
                       F V scale multiplication vector_norm unit involution f
  for F :: "complex set"
    and V :: "'v::ab_group_add set"
    and scale :: "complex \<Rightarrow> 'v \<Rightarrow> 'v"  (infixr \<open>*\<^sub>C\<close> 75)
    and multiplication :: "'v \<Rightarrow> 'v \<Rightarrow> 'v"  (infixr \<open>\<Zspot>\<close> 74)
    and vector_norm :: "'v \<Rightarrow> real"  (\<open>\<Parallel>_\<Parallel>\<close> [65])
    and unit :: "'v" (\<open>\<one>\<close>)
    and involution :: "'v\<Rightarrow>'v" (\<open>_\<^sup>\<dagger>\<close> 73)
    and f
begin

lemma is_star_aut: "involutive_complex_automorphism V (*\<^sub>C) (\<Zspot>) \<one> involution f"
  using involutive_complex_isomorphism_axioms by (simp only: involutive_complex_automorphism_def)

sublocale as_star_aut: involutive_complex_automorphism V
  using is_star_aut .

end


lemma (in Cstar_algebra) automorphismI:
  assumes "automorphism f"
  shows "Cstar_automorphism F V scale multiplication vector_norm unit involution f"
  using involutive_complex_isomorphism.axioms[OF assms[unfolded involutive_complex_automorphism_def]]
  unfolding involutive_complex_isomorphism_axioms_def
  unfolding involutive_complex_homomorphism_def involutive_complex_homomorphism_axioms_def
  by unfold_locales presburger+

end