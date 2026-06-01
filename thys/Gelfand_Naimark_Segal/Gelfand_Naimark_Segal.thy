section \<open>The Gelfand-Naimark-Segal Construction\<close>

theory Gelfand_Naimark_Segal
imports
  Inner_Completion
  Cstar_Algebra_On
  Complex_Bounded_Operators.Complex_Bounded_Linear_Function
  Smooth_Manifolds.Analysis_More
begin

unbundle lifting_syntax

subsection \<open>Strengthen lifting lemmas\<close>

subsubsection \<open>Lifting to the metric completion\<close>

lemma inj_to_metric_completion: "inj to_metric_completion"
  using isometry_on_injective to_metric_completion_isometry by blast

definition "from_metric_completion \<equiv> the_inv to_metric_completion"

lemma lift_to_metric_completion2:
  fixes f::"('a::metric_space) \<Rightarrow> ('b::complete_space)"
  assumes "uniformly_continuous_on UNIV f"
  shows "\<exists>g. (uniformly_continuous_on UNIV g)
            \<and> (f = g o to_metric_completion)
            \<and> (\<forall>x \<in> range to_metric_completion. g x = f (from_metric_completion x))"
  unfolding from_metric_completion_def
  using lift_to_metric_completion[OF assms]
  by (simp add: inj_to_metric_completion the_inv_f_f)

lemma lift_to_metric_completion_isometry2:
  fixes f::"('a::metric_space) \<Rightarrow> ('b::complete_space)"
  assumes "isometry_on UNIV f"
  shows "\<exists>g. isometry_on UNIV g
          \<and> range g = closure(range f)
          \<and> f = g o to_metric_completion
          \<and> (\<forall>x \<in> range to_metric_completion. g x = f (from_metric_completion x))"
  unfolding from_metric_completion_def
  using lift_to_metric_completion_isometry[OF assms]
  by (simp add: inj_to_metric_completion the_inv_f_f)

lemma dense_imp_conv_seq:
  assumes "closure S = U" "x\<in>U"
  shows "\<exists>s. (s n) \<in> S \<and> s \<longlonglongrightarrow> x"
  using LIMSEQ_if_less
  by (metis (full_types, lifting) ext all_not_in_conv
      assms closed_empty closure_closed order.strict_iff_order)

lemma to_metric_completion_sequence_ex:
  shows "\<exists>s. (to_metric_completion o s) \<longlonglongrightarrow> x"
  using dense_imp_conv_seq[of "range to_metric_completion" UNIV]
  by (smt (verit, best) UNIV_I closure_sequential function_factors_right image_iff
      to_metric_completion_dense')

lemma cinner_extensionality_dense:
  assumes dense_S: "closure S = UNIV"
    and inner_on_S: "\<forall>z\<in>S. cinner z x = cinner z y"
  shows "x = y"
proof (rule cinner_extensionality)
  fix z :: "'a::complex_inner"
  obtain s where s: "s \<longlonglongrightarrow> z" "\<And>n::nat. (s n) \<bullet>\<^sub>C x = (s n) \<bullet>\<^sub>C y"
    by (metis UNIV_I closure_sequential dense_S inner_on_S)
  \<comment> \<open>We could obtain \<^term>\<open>\<forall>n. s n \<in> S\<close> at the same time,
      but this is not needed here.\<close>
  have "(\<lambda>n. s n \<bullet>\<^sub>C x) \<longlonglongrightarrow> z \<bullet>\<^sub>C x"
    and"(\<lambda>n. s n \<bullet>\<^sub>C x) \<longlonglongrightarrow> z \<bullet>\<^sub>C y"
    apply (simp add: s(1) tendsto_cinner)
    unfolding s(2) by (simp add: s(1) tendsto_cinner)
  thus "z \<bullet>\<^sub>C x = z \<bullet>\<^sub>C y"
    using LIMSEQ_unique by blast
qed

lemma cinner_extensionality_metric_completion:
  assumes "\<forall>z. cinner (to_metric_completion z) x = cinner (to_metric_completion z) y"
  shows "x = y"
  using cinner_extensionality_dense[OF to_metric_completion_dense'] assms
  by blast

lemma completion_ext_simp1:
  fixes f::"('m::metric_space) \<Rightarrow> ('c::complete_space)" and g
  defines "D \<equiv> range to_metric_completion"
  shows "(f = g o to_metric_completion) \<longleftrightarrow>
      (\<forall>x \<in> D. g x = f (from_metric_completion x))"
  unfolding assms o_def from_metric_completion_def
  using f_the_inv_into_f the_inv_f_f inj_to_metric_completion
  by (metis rangeI)

lemma lift_to_metric_completion4:
  fixes f::"('m::metric_space) \<Rightarrow> ('c::complete_space)"
  assumes "uniformly_continuous_on UNIV f"
  shows "\<exists>!g. (uniformly_continuous_on UNIV g)
            \<and> (f = g \<circ> to_metric_completion)"
proof -
  { fix x y and v :: "'m metric_completion"
    assume x: "isUCont x" "f = x \<circ> to_metric_completion"
      and y: "isUCont y" "f = y \<circ> to_metric_completion"
    have x3: "\<forall>b\<in>range to_metric_completion. x b = f (from_metric_completion b)"
      and y3: "\<forall>b\<in>range to_metric_completion. y b = f (from_metric_completion b)"
      using completion_ext_simp1 x(2) y(2) by blast+
    have "\<exists>s. (to_metric_completion o s) \<longlonglongrightarrow> v"
      using to_metric_completion_sequence_ex .
    then obtain s :: "nat\<Rightarrow>'m" where s: "(to_metric_completion \<circ> s) \<longlonglongrightarrow> v"
      by blast
    let ?s = "to_metric_completion o s"
    have x_to_x: "(x \<circ> ?s) \<longlonglongrightarrow> x v"
      and y_to_y: "(y \<circ> ?s) \<longlonglongrightarrow> y v"
      using continuous_at_sequentially isUCont_isCont s x(1) y(1) by blast+
    moreover have "\<forall>b\<in>range to_metric_completion. x b = y b"
      using x3 y3 by presburger
    ultimately have x_to_y: "(x \<circ> ?s) \<longlonglongrightarrow> y v"
      by (metis fun.map_comp x(2) y(2))
    have "x v = y v"
      using LIMSEQ_unique x_to_x x_to_y by blast
  } note 1 = this
  have "\<exists>!x. isUCont x \<and>
       f = x \<circ> to_metric_completion \<and>
       (\<forall>xa\<in>range to_metric_completion.
           x xa = f (from_metric_completion xa))"
    by (metis (no_types, lifting) ext "1" assms lift_to_metric_completion2)
  thus ?thesis
    using completion_ext_simp1
    by (metis (no_types, lifting))
qed


lemma lift_to_metric_completion3:
  fixes f::"('m::metric_space) \<Rightarrow> ('c::complete_space)"
  assumes "uniformly_continuous_on UNIV f"
  shows "\<exists>!g. (uniformly_continuous_on UNIV g)
            \<and> (f = g o to_metric_completion)
            \<and> (\<forall>x \<in> range to_metric_completion. g x = f (from_metric_completion x))"
  by (metis assms lift_to_metric_completion2 lift_to_metric_completion4)


subsubsection \<open>Lifting a bounded operator from an inner product space to a Hilbert space\<close>

lemma to_metric_completion_cblinfun_exists:
  fixes f :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::cbanach\<close>
  assumes f_add: \<open>\<And>x y. f (x + y) = f x + f y\<close>
  assumes f_scale: \<open>\<And>c x y. f (c *\<^sub>C x) = c *\<^sub>C f x\<close>
  assumes bounded: \<open>\<And>x. norm (f x) \<le> B * norm x\<close>
  shows "cblinfun_extension_exists (range to_metric_completion)
      (map_fun (from_metric_completion) id f)"
    (is \<open>cblinfun_extension_exists ?D ?f\<close>)
proof -
  interpret f: bounded_clinear f
    by unfold_locales (use f_add f_scale bounded in \<open>auto simp: mult.commute\<close>)
  obtain K where K: "\<And>x. norm (f x) \<le> norm x * K"
    using f.real.bounded by blast
  interpret m: bounded_clinear to_metric_completion
    using to_metric_completion_bounded_clinear .

  show ?thesis
  proof (rule cblinfun_extension_exists_bounded_dense)
    fix c x y 
    assume x: "x \<in> ?D"
    show "?f (c *\<^sub>C x) = c *\<^sub>C ?f x"
      unfolding map_fun_def from_metric_completion_def apply simp
      using the_inv_f_f[OF inj_to_metric_completion]
      by (metis x assms(2) m.scale rangeE)
     show "norm (?f x) \<le> K * norm x"
      unfolding map_fun_def from_metric_completion_def apply simp
      using the_inv_f_f[OF inj_to_metric_completion]
      using to_metric_completion_norm
      by (metis Extra_Ordered_Fields.sign_simps(5) K rangeE x)
    assume y: "y \<in> ?D"
    show "?f (x + y) = ?f x + ?f y"
      unfolding map_fun_def from_metric_completion_def apply simp
      using the_inv_f_f[OF inj_to_metric_completion] f_the_inv_into_f[OF inj_to_metric_completion]
      using m.add f.add
      by (metis (no_types, lifting) x y)
  qed (use range_is_csubspace to_metric_completion_clinear in blast,
    use to_metric_completion_dense' in blast)
qed

lemma to_metric_completion_cblinfun_exists':
  fixes f :: \<open>('a::complex_normed_vector, 'b::cbanach) cblinfun\<close>
  shows "cblinfun_extension_exists (range to_metric_completion)
      (map_fun (from_metric_completion) id f)"
  using to_metric_completion_cblinfun_exists
        cblinfun.add_right cblinfun.scaleC_right norm_cblinfun
  by meson


subsection \<open>The $C^*$-algebra of bounded operators on a Hilbert space\<close>

text \<open>The assumption on the next lemma is a nondegeneracy condition found as the defining
  assumption of \<^locale>\<open>assoc_algebra_1_on\<close>. It's similar also to the class \<^class>\<open>zero_neq_one\<close>,
  which enters for example into \<^class>\<open>ring_1\<close>, \<^class>\<open>field\<close>, and \<^class>\<open>one_dim\<close>.\<close>

lemma Cstar_cblinfun:
  includes cblinfun_syntax
  assumes "(id_cblinfun :: ('b \<Rightarrow>\<^sub>C\<^sub>L ('b::chilbert_space))) \<noteq> 0"
  shows "Cstar_algebra UNIV (UNIV :: ('b \<Rightarrow>\<^sub>C\<^sub>L ('b::chilbert_space)) set) (*\<^sub>C) (o\<^sub>C\<^sub>L) norm id_cblinfun adj"
  (is "Cstar_algebra ?C ?B _ _ _ _ _")
proof -
  interpret normed_vector_space_on ?C cmod ?B "(*\<^sub>C)" norm
    by (unfold_locales,
      auto simp: norm_triangle_ineq norm_mult_ineq norm_mult complex_vector.vector_space_assms(1,2))

  interpret Group_Theory.monoid ?B "(+)" 0
    by unfold_locales auto
  interpret involutive_complex_algebra ?B "(*\<^sub>C)" "(o\<^sub>C\<^sub>L)" id_cblinfun adj
    by (unfold_locales,
      auto simp: assms cblinfun_compose_add_left cblinfun_compose_add_right lift_cblinfun_comp(2)
        add_eq_0_iff adj_plus)

  have "complete ?B"
    by (simp add: complete_UNIV)
  then have "mcomplete"
    unfolding mcomplete_iff_complete[symmetric] dist_cblinfun_def totalized_induced_metric_def
    by (simp add: norm_minus_commute)
  show ?thesis
    apply unfold_locales
    using \<open>mcomplete\<close> by (auto simp:
        norm_is_Proj_nonzero norm_cblinfun_compose power2_eq_square)
qed
text \<open>The above can be used e.g. as
  @{thm Cstar_cblinfun[OF id_cblinfun_not_0]}, or using \<^class>\<open>zero_neq_one\<close>.\<close>


subsection \<open>Type class of $C^*$-algebras\<close>

text \<open>Make a bundle to (de)activate dagger notation for adjoints of functions
  between types in the class of complex inner product spaces.\<close>
bundle cadjoint_syntax begin
  notation Complex_Inner_Product.cadjoint ("_\<^sup>\<dagger>" [99] 100)
end
unbundle no cadjoint_syntax


class cstar = complex_normed_algebra_1 + cbanach +
  fixes involution::"'a\<Rightarrow>'a" ("_\<^sup>\<dagger>" [99] 100)
  assumes ivl_scaleC: "(c *\<^sub>C s)\<^sup>\<dagger> = cnj c *\<^sub>C s\<^sup>\<dagger>" \<comment> \<open>@{thm involutive_complex_algebra.ivl_scale}\<close>
    and ivl_plus [simp]: "(x+y)\<^sup>\<dagger> = x\<^sup>\<dagger> + y\<^sup>\<dagger>" \<comment> \<open>@{thm involutive_ring.ivl_ring}\<close>
    and involution[simp]: "(x\<^sup>\<dagger>)\<^sup>\<dagger> = x" \<comment> \<open>@{thm involutive_semigroup.involution}\<close>
    and ivl_times [simp]: "(x * y)\<^sup>\<dagger> = y\<^sup>\<dagger> * x\<^sup>\<dagger>" \<comment> \<open>@{thm involutive_semigroup.antiautomorphism}\<close>
    and ivl_isometric: "norm (A\<^sup>\<dagger>) = norm A" \<comment> \<open>@{thm Cstar_algebra.involution_isometric}\<close>
    and Cstar: "norm (A\<^sup>\<dagger> * A) = (norm (A\<^sup>\<dagger>)) * (norm A)" \<comment> \<open>@{thm Cstar_algebra.Cstar}\<close>
begin

text \<open>
A class analogue of \<^locale>\<open>Cstar_algebra\<close>,
reproducing the axioms @{thm Cstar_algebra_axioms_def} one-by-one.
Some assumptions of \<^locale>\<open>Cstar_algebra\<close> are in \<^class>\<open>real_normed_algebra\<close>, compare:
\begin{itemize}
  \item @{thm Cstar_algebra.normed_algebra} with @{thm norm_mult_ineq},
  \item @{thm Cstar_algebra.normed_unital} with @{thm norm_one}.
\end{itemize}
\<close>

end

bundle cstar_syntax begin
  notation involution ("_\<^sup>\<dagger>" [99] 100)
end

unbundle cstar_syntax


lemma cstar_locale: "Cstar_algebra UNIV (UNIV::'a::cstar set)
    scaleC times norm 1 involution"
proof -
  have 0: "Metric_space.mcomplete (UNIV::'a set)
      (normed_vector_space_on.totalized_induced_metric UNIV norm)"
    by (simp add: complete_UNIV totalized_induced_metric_eq_dist)
  have 1: "monoid.invertible UNIV (+) 0 u"
    for u :: 'a
  proof -
    interpret Group_Theory.monoid UNIV "(+)" "0::'a"
      by unfold_locales simp_all
    show ?thesis
      unfolding invertible_def[simplified]
      by (intro exI[of _ "-u"]) simp
  qed
  have 2: "involution u * involution (of_complex c) =
      of_complex (cnj c) * involution u"
    for u :: 'a and c::complex
    using ivl_scaleC by auto
  have 3: "norm (of_complex c * u) = cmod c * norm u"
    for u :: 'a and c::complex
    by (metis norm_scaleC scaleC_conv_of_complex)
  have 4: "v * (of_complex c * u) = of_complex c * (v * u)"
    for u v :: 'a and c::complex
    by (metis mult_scaleC_right scaleC_conv_of_complex)
  show ?thesis
    apply unfold_locales
    apply (simp_all add: ivl_isometric Cstar
        norm_triangle_ineq norm_mult Groups.mult_ac(1)
        nat_distrib(2) cross3_simps(23) norm_mult_ineq)
    using 0 1 2 3 4 by simp_all
qed

text \<open>We \emph{have to} interpret \<^class>\<open>cstar\<close> as a \<^locale>\<open>Cstar_algebra\<close>
  in stages, and name the interpretation of the \<^locale>\<open>involutive_complex_algebra\<close>,
  otherwise there is a naming conflict between
  @{thm algebra_on.lie_algebraI} and @{thm vector_space_on.lie_algebraI}.\<close>
interpretation cstar1: involutive_complex_algebra
    "UNIV::'a::cstar set" scaleC times 1 involution
  using cstar_locale unfolding Cstar_algebra_def by blast

interpretation Cstar_algebra
    UNIV "UNIV::'a::cstar set" scaleC times norm 1 involution
  using cstar_locale .

text \<open>Some simp set adjustments.\<close>
declare cstar1.involution_uminus'[simp del]
declare cstar1.ivl_minus'[simp del]

context cstar begin
named_theorems cstar_simps
lemmas cross3_simps(10,11,23,24,27,28)[cstar_simps]
lemmas
  cstar1.involution_uminus'[OF UNIV_I, cstar_simps]
  cstar1.ivl_minus'[OF UNIV_I UNIV_I, cstar_simps]
end


subsection \<open>GNS construction\<close>

context
  fixes \<omega> :: "'a::cstar \<Rightarrow> complex"
  assumes omega_nonneg: "\<And>A::'a. \<omega> (A\<^sup>\<dagger> * A) \<ge> 0"
    and one [simp]: "\<omega> 1 = 1"
    and "clinear \<omega>"
begin

subsubsection \<open>Interpretation of existing locales\<close>

thm linear_def clinear_def linear_on_def

interpretation \<omega>: clinear \<omega>
  using \<open>clinear \<omega>\<close> .

lemma cstar_state: "Cstar_state UNIV UNIV scaleC times norm 1 involution \<omega>"
  apply unfold_locales
  using \<omega>.add \<omega>.scaleC omega_nonneg
  by (simp_all add: nat_distrib(2) cross3_simps(52))

interpretation Cstar_state UNIV UNIV scaleC times norm 1 involution \<omega>
  using cstar_state .

subsubsection \<open>Some identities for \<^class>\<open>cstar\<close> and its left ideal.\<close>

text \<open>Show the kernel of our intended inner product is a (left) ideal.\<close>
definition zero_inner_set: "\<II> = {A::'a. \<omega> (A\<^sup>\<dagger> * A) = 0}"

lemma is_zero_inner: "\<omega> (A\<^sup>\<dagger> * A) = 0" if "A\<in>\<II>"
  using that unfolding zero_inner_set by simp

lemma zero_inner_zero: "\<omega> i = 0" if "i\<in>\<II>"
  using state_zero_if_inner_zero that unfolding zero_inner_set
  by blast

lemma zero_inner_times: "a*i \<in> \<II>" if "i\<in>\<II>" for a i :: 'a
proof -
  let ?b = "a\<^sup>\<dagger>*a*i"
  from cauchy_schwarz_square[of ?b i]
  have "\<bar>\<omega> ((a*i)\<^sup>\<dagger> * (a*i))\<bar>\<^sup>2 \<le> \<omega> (?b\<^sup>\<dagger> * ?b) * \<omega> (i\<^sup>\<dagger> * i)"
    by (simp add: cstar_simps functional_inner_def)
  then show ?thesis
    unfolding is_zero_inner[OF that] zero_inner_set apply simp
    using cnj_x_x_geq0 cnj_x_x
    by (metis abs_eq_0_iff le_less less_le_not_le zero_eq_power2)
qed

lemma zero_inner_zero2: "\<omega> (a*i) = 0" if "i\<in>\<II>"
  apply (rule zero_inner_zero)
  apply (rule zero_inner_times)
  using that .

end


class cstar_state = cstar +
  fixes state :: "'a \<Rightarrow> complex" (\<open>\<omega>\<close>)
  assumes omega_nonneg: "\<And>A::'a. \<omega> (A\<^sup>\<dagger> * A) \<ge> 0"
    and omega_one [simp]: "\<omega> 1 = 1"
    and omega_linear[simp]: "\<omega> (u + v) = \<omega> u + \<omega> v"
      "\<omega> (c *\<^sub>C u) = c * \<omega> u"
    and extra_assm[no_atp]:
      \<open>\<omega> ((B*A)\<^sup>\<dagger> * B*A) \<le> (norm B)\<^sup>2 * \<omega> (A\<^sup>\<dagger> * A)\<close>


lemma omega_clinear: "clinear \<omega>"
  apply unfold_locales using omega_linear by auto

interpretation omega_linear: Vector_Spaces.linear scaleC times \<omega>
  apply unfold_locales using omega_linear(2)
  by auto

\<comment> \<open>Top-level interpretation of \<^locale>\<open>Cstar_state\<close> for any type in \<^class>\<open>cstar_state\<close>.\<close>
interpretation cstar_state: Cstar_state UNIV UNIV scaleC times norm 1 involution \<omega>
proof -
  interpret Cstar_algebra UNIV UNIV scaleC times norm 1 involution
    using cstar_locale .
  show "Cstar_state UNIV UNIV (*\<^sub>C) (*) norm 1 involution \<omega>"
    apply unfold_locales
    using omega_linear(2) omega_nonneg by (auto simp: cstar_simps)
qed


lemma zero_inner_zero': "\<omega> A = 0" if "\<omega> (A\<^sup>\<dagger> * A) = 0"
  using zero_inner_zero zero_inner_set that
  using omega_nonneg omega_one omega_clinear
  by (metis (full_types,lifting) ctr_simps_mem_Collect_eq)

lemma zero_inner_zero2': "\<omega> (B*A) = 0" if "\<omega> (A\<^sup>\<dagger> * A) = 0"
  using zero_inner_zero2 zero_inner_set that
  using omega_nonneg omega_one omega_clinear
  by (metis (full_types,lifting) ctr_simps_mem_Collect_eq)


text \<open>Some identities, restated for \<^class>\<open>cstar_state\<close>.\<close>
lemma state_ivl_cnj: "\<omega> (A\<^sup>\<dagger>) = cnj (\<omega> A)"
  using positive_normalised_linear_functional.involution_conjugate
  using cstar_state[of \<omega>, OF omega_nonneg omega_one omega_clinear]
  unfolding Cstar_state_def by blast

lemma state_cnj_ivl [cstar_simps]: "cnj (\<omega> (A\<^sup>\<dagger>)) = \<omega> A"
  using positive_normalised_linear_functional.cnj_ivl
  using cstar_state[of \<omega>, OF omega_nonneg omega_one omega_clinear]
  unfolding Cstar_state_def by blast

lemma state_norm_leq_inner: "\<bar>\<omega> A\<bar>\<^sup>2 \<le> \<omega> (A\<^sup>\<dagger> * A)"
  using positive_normalised_linear_functional.state_norm_leq_inner
  using cstar_state[of \<omega>, OF omega_nonneg omega_one omega_clinear]
  unfolding Cstar_state_def
  by (metis UNIV_I complex_of_real_cmod of_real_power
      positive_normalised_linear_functional.functional_inner_def)


lemma zero_inner_equivp: "equivp (\<lambda>u v. \<exists>A. \<omega> (A\<^sup>\<dagger> * A) = 0 \<and> u = v + A)"
proof -
  have 1: "\<exists>B. \<omega> (B\<^sup>\<dagger> * B) = 0 \<and> A + B = 0"
      if "\<omega> (A\<^sup>\<dagger> * A) = 0" for A :: 'a
    apply (intro exI[of _ "-A"])
    by (simp add: cstar1.involution_uminus' that)
  have 2: "\<omega> ((B\<^sup>\<dagger> + A\<^sup>\<dagger>) * (B + A)) = 0"
    if "\<omega> (A\<^sup>\<dagger> * A) = 0" "\<omega> (B\<^sup>\<dagger> * B) = 0"
    for A B :: 'a
    by (simp add: ordered_field_class.sign_simps(18) that zero_inner_zero2')
  show ?thesis
    apply (intro equivpI reflpI sympI transpI)
    by (auto simp: 1 2)
qed


subsubsection \<open>Quotient construction for the inner product\<close>

quotient_type (overloaded) 'a gns_precomplete =
  "'a::cstar_state" / "\<lambda>u v. \<exists>A. (\<omega> (A\<^sup>\<dagger> * A) = 0 \<and> u = v + A)"
  using zero_inner_equivp .

instantiation gns_precomplete :: (cstar_state) scaleC
begin

lift_definition scaleC_gns_precomplete ::
    "complex \<Rightarrow> 'a gns_precomplete \<Rightarrow> 'a gns_precomplete"
  is scaleC
  apply (simp add: cstar_simps)
  by (metis cross3_simps(10) nat_distrib(2) zero_inner_zero2')

lift_definition scaleR_gns_precomplete ::
    "real \<Rightarrow> 'a gns_precomplete \<Rightarrow> 'a gns_precomplete"
  is scaleR
proof -
  { fix r :: real and u i :: 'a
    assume asm: "\<omega> (i\<^sup>\<dagger> * i) = 0"
    have "\<exists>i'. \<omega> (i'\<^sup>\<dagger> * i') = 0 \<and> r *\<^sub>R (u + i) = r *\<^sub>R u + i'"
      apply (rule exI[of _ "scaleR r i"], intro conjI)
      apply (metis scaleC_gns_precomplete.abs_eq asm arithmetic_simps(49)
          gns_precomplete.abs_eq_iff pth_4(2) scaleR_scaleC)
      using cross3_simps(30) by blast }
  thus "\<exists>A. \<omega> (A\<^sup>\<dagger> * A) = 0 \<and> r *\<^sub>R a1 = r *\<^sub>R a2 + A"
    if "\<exists>A. \<omega> (A\<^sup>\<dagger> * A) = 0 \<and> a1 = a2 + A"
    for r and a1 a2 :: 'a
    using that by blast
qed

instance
  by (intro_classes) (simp add: scaleC_gns_precomplete_def
      scaleR_gns_precomplete_def scaleR_scaleC)

end


text \<open>The lifting of the vector space structure is almost entirely a
  transfer+sledgehammer affair: identities proven earlier are enough
  to let sledgehammer find respectfulness proofs.\<close>

instantiation gns_precomplete :: (cstar_state) complex_vector
begin

lift_definition zero_gns_precomplete :: "'a gns_precomplete"
  is 0 .

lemma "(a+b)* c = a* c + b* (c::'a)"
  using cross3_simps(23) by blast

lift_definition minus_gns_precomplete ::
    "'a gns_precomplete \<Rightarrow> 'a gns_precomplete \<Rightarrow> 'a gns_precomplete"
  is minus
proof -
  { fix u v :: 'a
    assume u: "\<omega> (u\<^sup>\<dagger> * u) = 0" and v: "\<omega> (v\<^sup>\<dagger> * v) = 0"
    have "\<omega> ((u\<^sup>\<dagger> - v\<^sup>\<dagger>) * (u - v)) = \<omega> (u\<^sup>\<dagger> * u) - \<omega> (v\<^sup>\<dagger> * u) - \<omega> (u\<^sup>\<dagger> * v) + \<omega> (v\<^sup>\<dagger> * v)"
      by (simp add: omega_linear.diff cstar_simps)
    also have "\<dots> = 0"
      using zero_inner_zero2'[OF u] zero_inner_zero2'[OF v] by simp
    finally have "\<omega> ((u\<^sup>\<dagger> - v\<^sup>\<dagger>) * (u - v)) = 0" . }
  thus "\<And>a1 a2 a3 a4.
      \<exists>A. \<omega> (A\<^sup>\<dagger> * A) = 0 \<and> a1 = a2 + A \<Longrightarrow>
      \<exists>A. \<omega> (A\<^sup>\<dagger> * A) = 0 \<and> a3 = a4 + A \<Longrightarrow>
      \<exists>A. \<omega> (A\<^sup>\<dagger> * A) = 0 \<and> a1 - a3 = a2 - a4 + A"
    apply (auto simp add: cstar1.involution_uminus' cstar1.ivl_minus')
    apply (metis arith_simps(57) cross3_simps(27) omega_linear.diff zero_inner_zero2')
    done
qed

lift_definition uminus_gns_precomplete ::
    "'a gns_precomplete \<Rightarrow> 'a gns_precomplete"
  is uminus by (auto simp: cstar_simps)

lift_definition plus_gns_precomplete ::
    "'a gns_precomplete \<Rightarrow> 'a gns_precomplete \<Rightarrow> 'a gns_precomplete"
  is plus
  by (auto simp: cstar_simps) (metis add_0_iff zero_inner_zero2')

instance
  apply (intro_classes; transfer)
  by (auto simp add: cstar_simps)

end


instantiation gns_precomplete :: (cstar_state) complex_inner
begin

text \<open>The interesting definition is for the inner product,
  which implies that of the norm.\<close>

lift_definition cinner_gns_precomplete ::
    "'a gns_precomplete \<Rightarrow> 'a gns_precomplete \<Rightarrow> complex"
  is "\<lambda>u v. \<omega> (u\<^sup>\<dagger> * v)"
proof clarify
  fix u v i1 i2 :: 'a
  assume i_in_ideal: "\<omega> (i1\<^sup>\<dagger> * i1) = 0" "\<omega> (i2\<^sup>\<dagger> * i2) = 0"
  have 1: "\<omega> ((v+i2)\<^sup>\<dagger> * (u+i1)) =
      \<omega> (v\<^sup>\<dagger>*u) + \<omega> (v\<^sup>\<dagger>*i1) + cnj (\<omega> (u\<^sup>\<dagger>*i2)) + \<omega> (i2\<^sup>\<dagger>*i1)"
    apply (simp add: ring_distribs)
    using involution ivl_times omega_clinear omega_nonneg omega_one
    by (metis (no_types, lifting) Cstar_state_def UNIV_I cstar_state
        positive_normalised_linear_functional.involution_conjugate)
  also have "\<dots> = \<omega> (v\<^sup>\<dagger>*u)"
    using i_in_ideal by (simp add: cstar_simps zero_inner_zero2')
  finally show "\<omega> ((v + i2)\<^sup>\<dagger> * (u + i1)) = \<omega> (v\<^sup>\<dagger> * u)"
    by (simp add: cstar_simps)
qed

\<comment> \<open>This could be defined in terms of \<^term>\<open>\<lambda>u. cinner u u\<close>, which
  will be a proof obligation later on anyway, but I think this
  is easier (since we can leverage identities to prove the necessary
  anyway) in the long term: we keep a concrete construction.\<close>
lift_definition norm_gns_precomplete :: "'a gns_precomplete \<Rightarrow> real"
  is "\<lambda>u. Re (csqrt (\<omega> (u\<^sup>\<dagger> * u)))"
  by clarsimp (metis (no_types, lifting) cinner_gns_precomplete.abs_eq
      gns_precomplete.abs_eq_iff ivl_plus)


text \<open>The distance is given by the norm (and vector subtraction),
  as is standard.\<close>

definition dist_gns_precomplete ::
    "'a gns_precomplete \<Rightarrow> 'a gns_precomplete \<Rightarrow> real"
    where "dist_gns_precomplete x y = norm (y-x)"


text \<open>The uniform and topological structures are prescribed,
  in turn, by the metric structure.\<close>

definition uniformity_gns_precomplete::"(('a gns_precomplete) \<times> ('a gns_precomplete)) filter"
  where "uniformity_gns_precomplete = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition open_gns_precomplete :: "'a gns_precomplete set \<Rightarrow> bool"
  where "open_gns_precomplete U = (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"

definition sgn_gns_precomplete ::
    "'a gns_precomplete \<Rightarrow> 'a gns_precomplete"
  where "sgn_gns_precomplete x \<equiv> x /\<^sub>R norm x"

lemma norm_sym_gns_precomplete:
  fixes x y :: "'a gns_precomplete"
  shows "norm (y - x) = norm (x - y)"
proof transfer
  fix x y :: 'a
  have "\<omega> ((y - x)\<^sup>\<dagger> * (y - x)) = \<omega> ((x - y)\<^sup>\<dagger> * (x - y))"
    by (simp add: cstar_simps omega_linear.diff)
  thus "Re (csqrt (\<omega> ((y-x)\<^sup>\<dagger> * (y-x)))) = Re (csqrt (\<omega> ((x-y)\<^sup>\<dagger> * (x-y))))"
    by simp
qed

instance
  apply intro_classes
  subgoal unfolding dist_gns_precomplete_def using norm_sym_gns_precomplete .
  subgoal unfolding sgn_gns_precomplete_def by blast
  subgoal unfolding uniformity_gns_precomplete_def by blast
  subgoal unfolding open_gns_precomplete_def by blast
  subgoal apply transfer
    using state_ivl_cnj by (metis involution ivl_times)
  subgoal apply transfer
    by (simp add: cstar_simps)
  subgoal by transfer (simp only: ivl_scaleC mult_scaleC_left omega_linear.scale)
  subgoal by transfer (simp add: omega_nonneg)
  subgoal by transfer simp
  subgoal by transfer (simp add: cmod_Re omega_nonneg)
  done

end


type_synonym ('a) gns = "'a gns_precomplete metric_completion"


subsubsection \<open>Representation of \<^typ>\<open>'a\<close> on the Hilbert space \<^typ>\<open>'a gns\<close>.\<close>

text \<open>The action on the dense subspace \<^term>\<open>to_gns ` UNIV\<close> is given
  by lifted multiplication. Notice this isn't quite the dense
  subspace -- this is the action on the precomplete quotient,
  a type, not a set on \<^typ>\<open>'a gns\<close>.\<close>
lift_definition action_gns_precomplete ::
    "'a::cstar_state \<Rightarrow> 'a gns_precomplete \<Rightarrow> 'a gns_precomplete"
  is "(*)"
  by (metis Extra_Ordered_Fields.sign_simps(4) nat_distrib(2) zero_inner_zero2')

lemma action_gns_precomplete_alt: "action_gns_precomplete u \<equiv>
    \<lambda>v. abs_gns_precomplete (u * (rep_gns_precomplete v))"
  unfolding action_gns_precomplete_def map_fun_def o_def id_def .


\<comment> \<open>We can't use lift-definition for the action on the completion,
  because \<open>from_gns\<close> (below) isn't total (since \<^term>\<open>from_metric_completion\<close> isn't).\<close>

definition to_gns :: "'a::cstar_state \<Rightarrow> 'a gns"
  where "to_gns \<equiv> to_metric_completion \<circ> abs_gns_precomplete"

definition from_gns :: "'a::cstar_state gns \<Rightarrow> 'a"
  where "from_gns \<equiv> rep_gns_precomplete \<circ> from_metric_completion"

definition action_gns_precomplete' ::
    "'a::cstar_state \<Rightarrow> 'a gns_precomplete \<Rightarrow> 'a gns"
  where "action_gns_precomplete' u \<equiv>
    to_metric_completion \<circ> (action_gns_precomplete u)"

lemma action_gns_precomplete'_alt: "action_gns_precomplete' \<equiv>
    (id ---> id ---> to_metric_completion) action_gns_precomplete"
  unfolding action_gns_precomplete'_def map_fun_def o_def by simp

lemma action_gns_precomplete'_alt2: "action_gns_precomplete' \<equiv>
    (id ---> rep_gns_precomplete ---> (to_gns)) (*)"
  unfolding action_gns_precomplete'_def action_gns_precomplete_def
    to_gns_def map_fun_def o_def id_def by argo


subsubsection \<open>The action is bounded.\<close>
text \<open>This is where @{thm extra_assm} is first used.\<close> 

lemma state_norm_sandwich_leq: \<open>\<bar>\<omega> (A\<^sup>\<dagger> * B * A)\<bar> \<le> \<omega> (A\<^sup>\<dagger> * A) * norm B\<close>
proof-
  from cstar_state.mult_inner_norm_bound extra_assm
  show ?thesis
    unfolding cstar_state.functional_inner_def
    by (metis (no_types, lifting) UNIV_I involution ivl_isometric ivl_times mult.assoc)
qed

lemma action_gns_bounded_norm_square:
  "(norm ((action_gns_precomplete u) v))\<^sup>2 \<le> (norm u)\<^sup>2 * (norm v)\<^sup>2"
proof -
  { fix u v :: 'a
    have "\<bar>\<omega> (v\<^sup>\<dagger> * u\<^sup>\<dagger> * u * v)\<bar> \<le> \<omega> (v\<^sup>\<dagger> * v) * (norm (u\<^sup>\<dagger> * u))"
      using state_norm_sandwich_leq[of v "u\<^sup>\<dagger> * u"] by (simp add: cstar_simps)
    then have "\<parallel>\<omega> ((u * v)\<^sup>\<dagger> * (u * v))\<parallel> \<le> (norm u)\<^sup>2 * \<parallel>\<omega> (v\<^sup>\<dagger> * v)\<parallel>"
      apply (simp add: cstar_simps)
      using Bstar[simplified]
      by (smt (verit) Extra_Ordered_Fields.sign_simps(5) UNIV_I complex_of_real_cmod
          complex_of_real_mono_iff cstar_state.finner_cmod_eq cstar_state.functional_inner_def
          of_real_mult) }
  thus ?thesis
    unfolding norm_eq_sqrt_cinner[of "(action_gns_precomplete u) v"]
    unfolding norm_eq_sqrt_cinner[of v]
    apply transfer
    by (simp only: abs_norm_cancel real_sqrt_power[of _ 2, symmetric, unfolded real_sqrt_abs])
qed

lemma action_gns_bounded_norm_square':
  shows "(norm ((action_gns_precomplete' u) v))\<^sup>2 \<le> (norm u)\<^sup>2 * (norm v)\<^sup>2"
  using to_metric_completion_norm[of "action_gns_precomplete u v"]
  by (simp add: action_gns_precomplete'_def action_gns_bounded_norm_square)

lemma action_gns_bounded_norm:
  shows "(norm ((action_gns_precomplete u) v)) \<le> (norm u) * (norm v)"
  using action_gns_bounded_norm_square norm_ge_zero
  by (metis power2_le_imp_le power_mult_distrib zero_compare_simps(4))

lemma action_gns_bounded_norm':
  shows "(norm ((action_gns_precomplete' u) v)) \<le> (norm u) * (norm v)"
  using to_metric_completion_norm[of "action_gns_precomplete u v"]
  by (simp add: action_gns_precomplete'_def action_gns_bounded_norm)

lemma action_gns_blin: "bounded_linear (action_gns_precomplete u)"
proof -
  interpret linear "action_gns_precomplete u"
    by unfold_locales (transfer, simp add: cstar_simps)+
  have "\<forall>x. norm (action_gns_precomplete u x) \<le> norm x * norm u"
    by (simp add: action_gns_bounded_norm[of u] cstar_simps) 
  then show ?thesis
    by unfold_locales blast
qed

lemma action_gns_blin': "bounded_linear (action_gns_precomplete' u)"
  unfolding action_gns_precomplete'_def o_def
  apply (rule bounded_linear_compose[OF _ action_gns_blin])
  using to_metric_completion_linear to_metric_completion_norm
  by (metis Groups.mult_ac(2) bounded_linear.intro
      bounded_linear_axioms_def more_arith_simps(5) order.refl)


lemma action_gns_unif_cts': "uniformly_continuous_on UNIV (action_gns_precomplete' u)"
  using bounded_linear.isUCont[OF action_gns_blin'] .



\<comment> \<open>Never unfold this. Use the lemma below instead.\<close>
definition action_gns_closure:: "'a::cstar_state \<Rightarrow> 'a gns\<Rightarrow>'a gns"
  where "action_gns_closure u \<equiv> THE g.
    (uniformly_continuous_on UNIV g) \<and>
    (action_gns_precomplete' u = g \<circ> to_metric_completion)"

lemma action_gns_closure:
  "uniformly_continuous_on UNIV (action_gns_closure u)"
  "action_gns_precomplete' u =
    (action_gns_closure u) \<circ> to_metric_completion"
  "\<And>x. x\<in>range to_metric_completion \<Longrightarrow>
    (action_gns_closure u) x = action_gns_precomplete' u (from_metric_completion x)"
  using theI'[OF lift_to_metric_completion3[OF action_gns_unif_cts'], of u]
  by (auto simp add: completion_ext_simp1 from_metric_completion_def action_gns_closure_def)


lemma action_gns_cblin: "bounded_clinear (action_gns_precomplete u)"
proof -
  interpret clinear "action_gns_precomplete u"
    apply unfold_locales 
    apply transfer
     apply (simp add: cstar_simps; fail)
    apply transfer
    using mult_scaleC_right mult_zero_right omega_linear.zero (* TODO simp set? *)
    by (metis nat_arith.rule0)
  have "\<forall>x. norm (action_gns_precomplete u x) \<le> norm x * norm u"
    by (simp add: action_gns_bounded_norm[of u] cstar_simps) 
  then show ?thesis
    by unfold_locales blast
qed

lemma action_gns_cblin': "bounded_clinear (action_gns_precomplete' u)"
  unfolding action_gns_precomplete'_def o_def
  apply (rule bounded_clinear_compose[OF _ action_gns_cblin])
  using to_metric_completion_clinear to_metric_completion_norm
  by (metis Groups.mult_ac(2) bounded_clinear.intro
      bounded_clinear_axioms_def more_arith_simps(5) order.refl)

\<comment> \<open>See \url{https://proofwiki.org/wiki/Bounded_Linear_Transformation_to_Banach_Space_has_Unique_Extension_to_Closure_of_Domain}
and \url{https://en.wikipedia.org/wiki/Continuous_linear_extension}\<close>
lemma linear_continuous_imp_bounded:
  assumes "linear f" "continuous_on UNIV f"
  shows "bounded_linear f"
proof -
  interpret linear f using assms(1) .
  find_theorems name: continuous_on norm
  thm continuous_on_closure_norm_le continuous_on_compact_bound
  thm assms(2)[unfolded continuous_on_def tendsto_def]
  have "continuous (at 0) f"
    using assms(2) by (simp add: continuous_on_interior)
  then obtain d where "d>0" "\<forall>x. norm (x-0) < d \<longrightarrow> norm (f x - f 0) < 1"
    unfolding dist_norm[symmetric]
    using continuous_at_eps_delta rel_simps(68) by blast
  hence d: "d>0" "\<And>x. norm (x) < d \<Longrightarrow> norm (f x) < 1"
    by auto
  { fix x :: 'a
    let ?dx = "d /\<^sub>R (2 * norm x)"
    let ?y = "?dx *\<^sub>R x"
    have 1: "norm ?y < d"
    proof -
      have "norm x * inverse (norm x) < 2 \<and> 0 \<le> d"
        by (metis d(1) less_le linorder_not_le mult_zero_left
            numeral_One numeral_less_iff right_inverse semiring_norm(83)
            verit_comp_simplify(21) zero_less_numeral)
      thus ?thesis
        by (simp add: Groups.mult_ac(2) d(1))
    qed
    have 2: "norm (f ?y) = ?dx * norm (f x)"
      using d(1) scaleR by fastforce
    then have 3: "?dx * norm (f x) < 1"
      using d(2)[OF 1] by presburger
    then have "norm (f x) \<le> (2 / d) * norm x"
      using norm_ge_zero zero_less_norm_iff d(1)
    proof -
      have "\<forall>r::real. 1 * r = r"
        by simp
      moreover have "\<forall>r ra. (r::real) * (1 / ra) = r / ra"
        by auto
      moreover have "norm (f x) < 1 / (d / (norm x * 2)) \<or> \<not> 0 < d / (norm x * 2)"
        by (metis Extra_Ordered_Fields.sign_simps(5) 3 divide_inverse linordered_field_class.pos_less_divide_eq real_scaleR_def)
      ultimately have "norm (f x) \<le> norm x * (2 / d)"
        by (metis (no_types) arith_extra_simps(18) d(1) divide_divide_eq_right less_le
            linordered_field_class.pos_less_divide_eq local.zero norm_ge_zero zero_less_norm_iff zero_less_numeral)
      then show ?thesis
        by (simp add: Extra_Ordered_Fields.sign_simps(5))
    qed
  } then
  show ?thesis
    by unfold_locales (metis Extra_Ordered_Fields.sign_simps(5))
qed

lemma linear_continuous_iff_bounded:
  assumes "linear f"
  shows "continuous_on UNIV f \<longleftrightarrow> bounded_linear f"
  using assms linear_continuous_imp_bounded linear_continuous_on
  by blast

lemma clinear_continuous_iff_bounded:
  assumes "clinear f"
  shows "continuous_on UNIV f \<longleftrightarrow> bounded_clinear f"
  using assms linear_continuous_iff_bounded
  by (metis bounded_clinear.bounded_linear
      bounded_linear_bounded_clinear clinear.linear clinear.scaleC)

lemma linear_UCont_iff_bounded:
  assumes "linear f"
  shows "uniformly_continuous_on UNIV f \<longleftrightarrow> bounded_linear f"
  using linear_continuous_iff_bounded[OF assms]
  using bounded_linear.isUCont uniformly_continuous_imp_continuous by blast

lemma clinear_UCont_iff_bounded:
  assumes "clinear f"
  shows "uniformly_continuous_on UNIV f \<longleftrightarrow> bounded_clinear f"
  using clinear_continuous_iff_bounded[OF assms]
    bounded_linear.isUCont[OF bounded_clinear.bounded_linear]
    uniformly_continuous_imp_continuous by blast

definition action_cblinfun ::
    "'a::cstar_state \<Rightarrow> ('a gns, 'a gns) cblinfun" (\<open>\<pi>\<^sub>\<omega>\<close>)
  where "action_cblinfun u \<equiv> cblinfun_extension
    (range to_metric_completion)
    (map_fun from_metric_completion id (action_gns_precomplete' u))"
                                         
lemma action_cblinfun: "cblinfun_extension_exists
    (range to_metric_completion)
    (map_fun from_metric_completion id (action_gns_precomplete' u))"
  for u :: "'a::cstar_state"
proof -
  interpret bounded_clinear "action_gns_precomplete' u"
    using action_gns_cblin' .
  obtain K where K: "\<And>x. norm (action_gns_precomplete' u x) \<le> norm x * K"
    using real.bounded by blast
  show ?thesis
    by (meson action_gns_bounded_norm' real.add scaleC to_metric_completion_cblinfun_exists)
qed

lemma action_cblinfun_apply:
  shows "action_cblinfun u (to_metric_completion x) = action_gns_precomplete' u x"
  using cblinfun_extension_apply[OF action_cblinfun]
  using the_inv_f_f[OF inj_to_metric_completion]
  unfolding action_cblinfun_def from_metric_completion_def
  by (smt (verit) eq_id_iff map_fun_apply rangeI)

lemma action_cblinfun_cong:
  assumes "cspan (range to_metric_completion) = cspan (to_metric_completion ` B')"
    "\<And>x. x \<in> B' \<Longrightarrow> action_cblinfun u (to_metric_completion x) = g (to_metric_completion x)"
  shows "cblinfun_extension (to_metric_completion ` B') g = action_cblinfun u"
  using assms
  using cblinfun_extension_cong[OF _ _ _ action_cblinfun]
  using the_inv_f_f[OF inj_to_metric_completion]
  by (smt (verit, ccfv_threshold) action_cblinfun_apply action_cblinfun_def eq_id_iff
      from_metric_completion_def image_iff image_mono map_fun_apply subset_UNIV)

lemmas action_cblinfun_apply' = cblinfun_extension_apply[OF action_cblinfun, folded action_cblinfun_def]
  and action_cblinfun_cong' = cblinfun_extension_cong[OF _ _ _ action_cblinfun, folded action_cblinfun_def]
  and action_cblinfun_restrict' = cblinfun_extension_exists_restrict[OF _ _ action_cblinfun, folded action_cblinfun_def]

lemma action_UCont: "isUCont (action_cblinfun u)"
  using clinear_UCont_iff_bounded bounded_cbilinear_apply_bounded_clinear
    bounded_cbilinear_cblinfun_apply cblinfun_apply_clinear by blast

lemma action_closure_cblinfun:
    "action_gns_closure u = (action_cblinfun u)"
proof-
  have action_cblinfun_to_completion:
    "action_gns_precomplete' u = action_cblinfun u \<circ> to_metric_completion"
    "x \<in> range to_metric_completion \<Longrightarrow>
      action_cblinfun u x = action_gns_precomplete' u (from_metric_completion x)" for x
    by (simp_all add: action_cblinfun_apply' action_cblinfun_apply o_def)
  show ?thesis
    using action_UCont action_cblinfun_to_completion(1) action_gns_closure(1,2) action_gns_unif_cts'
      lift_to_metric_completion4 by blast
qed


text \<open>The cyclic vector is the abstraction of the unit\<close>
definition gns_1 (\<open>\<Omega>\<close>)
  where "gns_1 \<equiv> to_gns 1"

lemma gns_1': "\<Omega> \<bullet>\<^sub>C (action_gns_closure u \<Omega>) = \<omega> u"
proof -
  have "(abs_gns_precomplete 1) \<bullet>\<^sub>C action_gns_precomplete u (abs_gns_precomplete 1) = \<omega> u"
    by transfer (simp add: cstar1.unit_self_adjoint)
  then have "to_metric_completion (abs_gns_precomplete 1) \<bullet>\<^sub>C
      action_gns_precomplete' u (abs_gns_precomplete 1) =
      \<omega> u"
    unfolding action_gns_precomplete'_def
    by (simp add: to_metric_completion_cinner)
  thus ?thesis
    using action_gns_closure(2) by (metis comp_def gns_1_def to_gns_def)
qed
 
\<comment> \<open>Basically an Isabelle phrasing of Bratteli and Robinson's
  last sentence on page 55 \cite{bratteli1979}.\<close>
lemma cyclic_set:
  shows "{\<pi>\<^sub>\<omega> u \<Omega> | u. True} = {to_gns u | u. True}"
    and "{action_gns_closure u \<Omega> | u. True} = {to_gns u | u. True}"
proof -
  have "\<exists>u. action_gns_closure v \<Omega> = to_gns u" for v :: "'c::cstar_state"
    unfolding gns_1_def to_gns_def
    by (metis action_gns_closure(2) action_gns_precomplete'_def action_gns_precomplete_alt o_def)
  moreover have "\<exists>v. to_gns u = action_gns_closure v \<Omega>" for u :: "'c::cstar_state"
    unfolding gns_1_def to_gns_def
    by (metis UNIV_I action_gns_closure(2) action_gns_precomplete'_def
        action_gns_precomplete.abs_eq comp_eq_dest_lhs cstar1.multiplicative.right_unit)
  ultimately show "{action_gns_closure u \<Omega> | u. True} = {to_gns u | u. True}"
    by (auto simp add: gns_1_def to_gns_def)
  thus "{\<pi>\<^sub>\<omega> u \<Omega> | u. True} = {to_gns u | u. True}"
    by (simp add: action_closure_cblinfun)
qed

lemma gns_cyclic': "Elementary_Topology.closure {action_gns_closure u \<Omega> | u :: 'a::cstar_state. True} = UNIV"
proof -
  have "\<exists>u. to_metric_completion x = to_metric_completion (abs_gns_precomplete u)"
    for x :: "'b::cstar_state gns_precomplete"
    by (metis add.inverse_inverse map_fun_apply uminus_gns_precomplete_def)
  hence "{to_gns u | u. True} = range to_metric_completion"
    by (auto simp add: to_gns_def)
  thus ?thesis
    using cyclic_set(2) to_metric_completion_dense'
    by (metis (lifting) ext)
qed


subsubsection \<open>The action is a homomorphism\<close>

hide_const (open) closure

text \<open>Following \<^theory>\<open>Smooth_Manifolds.Analysis_More\<close>
  to instantiate the vector space on functions.\<close>
instantiation "fun" :: (type,scaleC) scaleC
begin
definition scaleC_fun :: "complex \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  where "scaleC_fun r f = (\<lambda>x. r *\<^sub>C f x)"
instance
  apply intro_classes unfolding scaleC_fun_def scaleR_fun_def
  by (simp add: scaleR_scaleC)
end

instance "fun" :: (type, complex_vector) complex_vector
  by standard (auto simp: scaleC_fun_def algebra_simps)


\<comment> \<open>The action is (by design) not injective.
  The norm is defined through the inner product, not as a lifting
  of the norm -- it may not be preserved exactly.\<close>
lemma action_injective_on_quotient: "\<exists>I. \<omega> (I\<^sup>\<dagger> * I) = 0 \<and> a = b + I"
  if "\<forall>x. action_gns_precomplete a x = action_gns_precomplete b x"
  for a b :: "'a::cstar_state" and x :: "'a gns_precomplete"
    using that apply transfer
    by (metis verit_prod_simplify(2))

\<comment> \<open>We already know this action outputs \<^term>\<open>bounded_clinear\<close> maps.
  We don't yet know it is linear itself.\<close>
lemma action_precomplete_morphism:
  shows "action_gns_precomplete (a+b) = action_gns_precomplete a + action_gns_precomplete b"
    and "action_gns_precomplete (a*b) = action_gns_precomplete a \<circ> action_gns_precomplete b"
    and "action_gns_precomplete (c*\<^sub>Ca) = c *\<^sub>C (action_gns_precomplete a)"
    and "action_gns_precomplete 1 = id"
    and "action_gns_precomplete (involution a) = cadjoint (action_gns_precomplete a)"
proof -
  let ?pi = action_gns_precomplete
  show "?pi (a+b) = ?pi a + ?pi b"
    unfolding plus_fun_def apply (intro ext) apply transfer
    by (simp add: cross3_simps(23))
  show "?pi (a*b) = ?pi a \<circ> ?pi b"
    unfolding o_def apply (intro ext) apply transfer
    by (simp add: ordered_field_class.sign_simps(4))
  show "?pi (c*\<^sub>Ca) = c *\<^sub>C (?pi a)"
    unfolding o_def scaleC_fun_def apply (intro ext) apply transfer
    by (metis arith_simps(50) mult_scaleC_left mult_zero_right omega_linear.zero)
  show "?pi 1 = id"
    unfolding id_def apply (intro ext)
    by transfer fastforce
  show "?pi (a\<^sup>\<dagger>) = cadjoint (?pi a)"
  proof -
    have "(?pi (a\<^sup>\<dagger>) x) \<bullet>\<^sub>C y = x \<bullet>\<^sub>C (?pi a y)" for x y
      apply transfer by (simp add: Groups.mult_ac(1))
    thus ?thesis
      by (metis cadjoint_eqI)
  qed
qed

lemma action_precomplete_morphism':
  shows "action_gns_precomplete' (a+b) = action_gns_precomplete' a + action_gns_precomplete' b"
    and "action_gns_precomplete' (c*\<^sub>Ca) = c *\<^sub>C (action_gns_precomplete' a)"
    and "action_gns_precomplete' 1 = to_metric_completion"
    and "action_gns_precomplete' (a*b) = action_gns_precomplete' a \<circ>
        from_metric_completion \<circ> action_gns_precomplete' b"
    and "action_gns_precomplete' (a\<^sup>\<dagger>) = to_metric_completion \<circ>
      cadjoint (from_metric_completion \<circ> action_gns_precomplete' a)"
proof -
  let ?pi = action_gns_precomplete'
  show "?pi 1 = to_metric_completion"
    unfolding action_gns_precomplete'_def o_def
    by (simp add: action_precomplete_morphism(4))

  interpret clinear to_metric_completion
    using to_metric_completion_clinear .
  show "?pi (a+b) = ?pi a + ?pi b"
    unfolding action_gns_precomplete'_def o_def
    by (auto simp add: action_precomplete_morphism(1) add)
  show "?pi (c*\<^sub>Ca) = c *\<^sub>C (?pi a)"
    unfolding action_gns_precomplete'_def o_def
    by (simp only: action_precomplete_morphism(3) scaleC_fun_def scaleC)
  show "?pi (a*b) = (?pi a) \<circ> from_metric_completion \<circ> (?pi b)"
    unfolding action_gns_precomplete'_def
    by (metis (mono_tags) action_precomplete_morphism(2) completion_ext_simp1 o_apply)
  show "?pi (a\<^sup>\<dagger>) = to_metric_completion \<circ> (cadjoint (from_metric_completion \<circ> action_gns_precomplete' a))"
    unfolding action_gns_precomplete'_def action_precomplete_morphism(5) o_def
    by (simp add: from_metric_completion_def inj_to_metric_completion the_inv_f_f)
qed

method action_uniq_eqI =
  (unfold action_gns_closure_def,
    intro the1_equality[OF lift_to_metric_completion4[OF action_gns_unif_cts']] conjI,
    fold action_gns_closure_def)

lemma
  shows action_closure_morphism:
    "action_gns_closure (a+b) = action_gns_closure a + action_gns_closure b"
    "action_gns_closure (a*b) = comp (action_gns_closure a) (action_gns_closure b)"
    "action_gns_closure (c*\<^sub>Ca) = c *\<^sub>C (action_gns_closure a)"
    "action_gns_closure 1 = id_cblinfun"
    "action_gns_closure (involution a) = cadjoint (action_gns_closure a)"
  and action_cblinfun_morphism:
    "\<pi>\<^sub>\<omega> (a+b) = \<pi>\<^sub>\<omega> a + \<pi>\<^sub>\<omega> b"
    "\<pi>\<^sub>\<omega> (a*b) = cblinfun_compose (\<pi>\<^sub>\<omega> a) (\<pi>\<^sub>\<omega> b)"
    "\<pi>\<^sub>\<omega> (c*\<^sub>Ca) = c *\<^sub>C (\<pi>\<^sub>\<omega> a)"
    "\<pi>\<^sub>\<omega> 1 = id_cblinfun"
    "\<pi>\<^sub>\<omega> (involution a) = adj (\<pi>\<^sub>\<omega> a)"
proof -
  show "action_gns_closure (a+b) = action_gns_closure a + action_gns_closure b"
  proof action_uniq_eqI
    show "isUCont (action_gns_closure a + action_gns_closure b)"
      unfolding plus_fun_def
      using action_gns_closure(1) uniformly_continuous_on_add by blast
    show "action_gns_precomplete' (a + b) =
        (action_gns_closure a + action_gns_closure b) \<circ> to_metric_completion"
      unfolding plus_compose
      using action_gns_closure(2) action_precomplete_morphism'(1)
      by metis
  qed
  thus "\<pi>\<^sub>\<omega> (a+b) = \<pi>\<^sub>\<omega> a + \<pi>\<^sub>\<omega> b"
    unfolding action_closure_cblinfun
    by (intro cblinfun_eqI) (simp add: cblinfun.add_left)

  show "action_gns_closure (a*b) = action_gns_closure a \<circ> action_gns_closure b"
  proof action_uniq_eqI
    show "isUCont (action_gns_closure a \<circ> action_gns_closure b)"
      unfolding action_closure_cblinfun o_def
      apply (rule bounded_linear.isUCont)
      apply (rule bounded_linear_compose[of "cblinfun_apply (\<pi>\<^sub>\<omega> a)"])
      by (simp_all add: cblinfun.real.bounded_linear_right)
    show "action_gns_precomplete' (a * b) =
        (action_gns_closure a \<circ> action_gns_closure b) \<circ> to_metric_completion"
      using action_gns_closure(2) action_precomplete_morphism(2)
      by (metis (no_types, lifting) action_gns_precomplete'_def fun.map_comp)
  qed
  thus "\<pi>\<^sub>\<omega> (a*b) = cblinfun_compose (\<pi>\<^sub>\<omega> a) (\<pi>\<^sub>\<omega> b)"
    unfolding action_closure_cblinfun
    by (intro cblinfun_eqI) (simp)

  show "action_gns_closure (c*\<^sub>Ca) = c *\<^sub>C (action_gns_closure a)"
  proof action_uniq_eqI
    show "isUCont (c *\<^sub>C (action_gns_closure a))"
      unfolding action_closure_cblinfun scaleC_fun_def
      by (auto intro: bounded_linear.isUCont simp add: bounded_clinear.bounded_linear 
          bounded_clinear_scaleC_right bounded_linear_compose cblinfun.real.bounded_linear_right)
    show "action_gns_precomplete' (c*\<^sub>Ca) =
        (c *\<^sub>C (action_gns_closure a)) \<circ> to_metric_completion"
      using action_gns_closure(2) action_precomplete_morphism'(2)
      unfolding o_def scaleC_fun_def by metis
  qed
  thus "\<pi>\<^sub>\<omega> (c*\<^sub>Ca) = c *\<^sub>C (\<pi>\<^sub>\<omega> a)"
    unfolding action_closure_cblinfun
    by (intro cblinfun_eqI) (simp add: scaleC_fun_def)

  show "action_gns_closure 1 = id_cblinfun"
    by (metis action_gns_closure(1,2) action_gns_unif_cts' action_precomplete_morphism'(3) apply_id_cblinfun
        bounded_linear.isUCont cblinfun.real.bounded_linear_right fun.map_id lift_to_metric_completion4)
  thus "\<pi>\<^sub>\<omega> 1 = id_cblinfun"
    by (smt (verit, best) action_closure_cblinfun cblinfun_eqI)

  show "action_gns_closure (a\<^sup>\<dagger>) = cadjoint (action_gns_closure a)"
  proof action_uniq_eqI
    have cblin_action: "bounded_clinear (action_gns_closure a)"
      unfolding action_closure_cblinfun
      by (metis (no_types) bounded_clinear_intro cblinfun.add_right
          cblinfun.scaleC_right norm_cblinfun ordered_field_class.sign_simps(5))

    show "isUCont (cadjoint (action_gns_closure a))"
      by (auto intro!: bounded_linear.isUCont bounded_clinear.bounded_linear 
               simp add: cblin_action cadjoint_bounded_clinear)
    have to_metric_completion_cadjoint:
        "cadjoint (action_gns_closure a) (to_metric_completion x) \<bullet>\<^sub>C
          (to_metric_completion y) =
        cadjoint (action_gns_precomplete a) x \<bullet>\<^sub>C y"
      for x y :: "'a gns_precomplete"
    proof -
      let ?x = "to_metric_completion x"
      let ?y = "to_metric_completion y"
      have "cadjoint (action_gns_closure a) ?x \<bullet>\<^sub>C ?y = ?x \<bullet>\<^sub>C ((action_gns_closure a) ?y)"
        using cadjoint_univ_prop[OF cblin_action] by presburger
      also have "\<dots> = ?x \<bullet>\<^sub>C (to_metric_completion ((action_gns_precomplete a) y))"
        using action_gns_closure(2)[unfolded action_gns_precomplete'_def o_def]
        by metis
      also have "\<dots> = x \<bullet>\<^sub>C ((action_gns_precomplete a) y)"
        by (rule to_metric_completion_cinner)
      also have "\<dots> = (cadjoint (action_gns_precomplete a) x) \<bullet>\<^sub>C y"
        using cadjoint_univ_prop[OF cblin_action]
        by (metis (no_types, lifting) Groups.mult_ac(1) action_gns_precomplete'_def action_gns_precomplete_alt
            action_precomplete_morphism'(3) action_precomplete_morphism(5) cinner_gns_precomplete.abs_eq involution
            ivl_times more_arith_simps(5) o_def to_metric_completion_cinner)
      finally show "cadjoint (action_gns_closure a) ?x \<bullet>\<^sub>C ?y =
          cadjoint (action_gns_precomplete a) x \<bullet>\<^sub>C y"
        by -
    qed

    show "action_gns_precomplete' (a\<^sup>\<dagger>) =
        cadjoint (action_gns_closure a) \<circ> to_metric_completion"
      unfolding action_gns_closure(2)
      unfolding o_def apply (intro ext)
      apply (intro cinner_extensionality_metric_completion allI)
      by (metis (mono_tags, opaque_lifting) action_cblinfun_apply action_closure_cblinfun action_gns_precomplete'_def
          action_precomplete_morphism(5) cinner_eq_flip o_def to_metric_completion_cadjoint
          to_metric_completion_cinner)
  qed
  thus "\<pi>\<^sub>\<omega> (involution a) = adj (\<pi>\<^sub>\<omega> a)"
    unfolding action_closure_cblinfun
    by (intro cblinfun_eqI) (simp add: adj.rep_eq)
qed


subsection \<open>GNS theorem for \<^term>\<open>\<pi>\<^sub>\<omega>\<close>\<close>
text \<open>It's a little sparser than in textbooks: the existence of the
  Hilbert space and a representation in terms of bounded operators
  is implicit in the construction of \<^typ>\<open>'a::cstar_state gns\<close>
  and \<^term>\<open>\<pi>\<^sub>\<omega>\<close>.\<close>

\<comment> \<open>Uniqueness up to unitary equivalence is missing as of yet.\<close>
theorem GNS_construction:
  shows gns_1: "\<forall>u. \<Omega> \<bullet>\<^sub>C (\<pi>\<^sub>\<omega> u \<Omega>) = \<omega> u"
    and gns_cyclic: "closure {\<pi>\<^sub>\<omega> u \<Omega> | u. True} = UNIV"
    and gns_hom: "\<pi>\<^sub>\<omega> (a+b) = \<pi>\<^sub>\<omega> a + \<pi>\<^sub>\<omega> b"
      "\<pi>\<^sub>\<omega> (a*b) = cblinfun_compose (\<pi>\<^sub>\<omega> a) (\<pi>\<^sub>\<omega> b)"
      "\<pi>\<^sub>\<omega> (c*\<^sub>Ca) = c *\<^sub>C (\<pi>\<^sub>\<omega> a)"
      "\<pi>\<^sub>\<omega> 1 = id_cblinfun"
      "\<pi>\<^sub>\<omega> (involution a) = adj (\<pi>\<^sub>\<omega> a)"
proof -
  show "\<forall>u. \<Omega> \<bullet>\<^sub>C cblinfun_apply (\<pi>\<^sub>\<omega> u) \<Omega> = \<omega> u"
    using gns_1'[unfolded action_closure_cblinfun] by blast
  show "closure {cblinfun_apply (\<pi>\<^sub>\<omega> u) \<Omega> |u. True} = UNIV"
    using gns_cyclic'[unfolded action_closure_cblinfun] .
qed (use action_cblinfun_morphism in simp_all)


unbundle cblinfun_syntax
no_notation gns_1 (\<open>\<Omega>\<close>)
no_notation action_cblinfun (\<open>\<pi>\<^sub>\<omega>\<close>)
text \<open>For presentation only, we give the existential form of the GNS construction.
  There's no disadvantage to using explicit constructions and @{thm GNS_construction}.\<close>
theorem GNS_construction':
  obtains \<pi>\<^sub>\<omega> :: "'a::cstar_state \<Rightarrow> ('a gns \<Rightarrow>\<^sub>C\<^sub>L 'a gns)"
    and \<Omega> :: "'a gns"
  where \<comment> \<open>properties of \<open>\<Omega>\<close>\<close>
        "\<forall>u. \<Omega> \<bullet>\<^sub>C (\<pi>\<^sub>\<omega> u \<Omega>) = \<omega> u"
    and "closure {\<pi>\<^sub>\<omega> u \<Omega> | u. True} = UNIV"
        \<comment> \<open>\<open>\<pi>\<close> is a $^*$-homomorphism\<close>
    and "\<pi>\<^sub>\<omega> (a+b) = \<pi>\<^sub>\<omega> a + \<pi>\<^sub>\<omega> b"
    and "\<pi>\<^sub>\<omega> (a*b) = cblinfun_compose (\<pi>\<^sub>\<omega> a) (\<pi>\<^sub>\<omega> b)"
    and "\<pi>\<^sub>\<omega> (c*\<^sub>Ca) = c *\<^sub>C (\<pi>\<^sub>\<omega> a)"
    and "\<pi>\<^sub>\<omega> 1 = id_cblinfun"
    and "\<pi>\<^sub>\<omega> (involution a) = adj (\<pi>\<^sub>\<omega> a)"
  using GNS_construction by blast
unbundle no cblinfun_syntax
notation gns_1 (\<open>\<Omega>\<close>)
notation action_cblinfun (\<open>\<pi>\<^sub>\<omega>\<close>)

unbundle no lifting_syntax
unbundle no cstar_syntax
unbundle scaleC_syntax (* to undo changes from this entry *)

end
