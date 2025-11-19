section \<open>Elliptic Functions\<close>
theory Elliptic_Functions
  imports Complex_Lattices
begin

subsection \<open>Definition\<close>

text \<open>
  In the context of a complex lattice $\Lambda$, a function is called \<^emph>\<open>elliptic\<close> if it is
  meromorphic and periodic w.r.t.\ the lattice.
\<close>
locale elliptic_function = complex_lattice_periodic \<omega>1 \<omega>2 f
  for \<omega>1 \<omega>2 :: complex and f :: "complex \<Rightarrow> complex" +
  assumes meromorphic: "f meromorphic_on UNIV"

text \<open>
  We call a function \<^emph>\<open>nicely elliptic\<close> if it additionally is nicely meromorphic, i.e.\ it has
  no removable singularities and returns 0 at each pole. It is easy to convert elliptic functions
  into nicely elliptic ones using the \<^const>\<open>remove_sings\<close> operator and lift results from the
  nicely elliptic setting to the ``regular'' elliptic one.
\<close>
locale nicely_elliptic_function = complex_lattice_periodic \<omega>1 \<omega>2 f
  for \<omega>1 \<omega>2 :: complex and f :: "complex \<Rightarrow> complex" +
  assumes nicely_meromorphic: "f nicely_meromorphic_on UNIV"

locale elliptic_function_remove_sings = elliptic_function
begin

sublocale remove_sings: nicely_elliptic_function \<omega>1 \<omega>2 "remove_sings f"
proof
  show "remove_sings f nicely_meromorphic_on UNIV"
    using meromorphic by (rule remove_sings_nicely_meromorphic)
  have *: "remove_sings f (z + \<omega>) = remove_sings f z" if \<omega>: "\<omega> \<in> \<Lambda>" for z \<omega>
  proof -
    have "remove_sings f (z + \<omega>) = remove_sings (\<lambda>w. f (w + \<omega>)) z"
      by (simp add: remove_sings_shift_0' add_ac)
    also have "(\<lambda>w. f (w + \<omega>)) = f"
      by (intro ext lattice_cong) (auto simp: rel_def \<omega>)
    finally show ?thesis .
  qed
  show "remove_sings f (z + \<omega>1) = remove_sings f z" 
       "remove_sings f (z + \<omega>2) = remove_sings f z" for z
    by (rule *; simp; fail)+
qed

end


context elliptic_function
begin

interpretation elliptic_function_remove_sings ..

lemma isolated_singularity [simp, singularity_intros]: "isolated_singularity_at f z"
  using meromorphic by (simp add: meromorphic_on_altdef)

lemma not_essential [simp, singularity_intros]: "not_essential f z"
  using meromorphic by (simp add: meromorphic_on_altdef)

lemma meromorphic' [meromorphic_intros]: "f meromorphic_on A"
  by (rule meromorphic_on_subset[OF meromorphic]) auto

lemma meromorphic'' [meromorphic_intros]:
  assumes "g analytic_on A"
  shows   "(\<lambda>x. f (g x)) meromorphic_on A"
  by (rule meromorphic_on_compose[OF meromorphic assms]) auto  

text \<open>
  Due to the lattice-periodicity of \<open>f\<close>, its derivative, zeros, poles, multiplicities, and 
  residues are also all lattice-periodic.
\<close>
sublocale zeros: complex_lattice_periodic \<omega>1 \<omega>2 "isolated_zero f"
proof
  fix z :: complex
  have *: "isolated_zero f (z + c) \<longleftrightarrow> isolated_zero (\<lambda>z. f (z + c)) z" for c
    by (simp add: isolated_zero_shift' add_ac)
  from this show "isolated_zero f (z + \<omega>1) \<longleftrightarrow> isolated_zero f z" 
                 "isolated_zero f (z + \<omega>2) \<longleftrightarrow> isolated_zero f z"
    by (simp_all add: f_periodic)
qed

sublocale poles: complex_lattice_periodic \<omega>1 \<omega>2 "is_pole f"
proof
  fix z :: complex
  have *: "is_pole f (z + c) \<longleftrightarrow> is_pole (\<lambda>z. f (z + c)) z" for c
    by (simp add: is_pole_shift_0' add_ac)
  from this show "is_pole f (z + \<omega>1) \<longleftrightarrow> is_pole f z" "is_pole f (z + \<omega>2) \<longleftrightarrow> is_pole f z"
    by (simp_all add: f_periodic)
qed

sublocale zorder: complex_lattice_periodic \<omega>1 \<omega>2 "zorder f"
proof
  fix z :: complex
  have *: "zorder f (z + c) = zorder (\<lambda>z. f (z + c)) z" for c
    by (simp add: zorder_shift' add_ac) 
  from this show "zorder f (z + \<omega>1) = zorder f z" "zorder f (z + \<omega>2) = zorder f z"
    by (simp_all add: f_periodic)
qed

sublocale deriv: complex_lattice_periodic \<omega>1 \<omega>2 "deriv f"
proof
  fix z :: complex
  have *: "deriv f (z + c) = deriv (\<lambda>z. f (z + c)) z" for c
    by (simp add: deriv_shift_0' add_ac o_def) 
  from this show "deriv f (z + \<omega>1) = deriv f z" "deriv f (z + \<omega>2) = deriv f z"
    by (simp_all add: f_periodic)
qed

sublocale higher_deriv: complex_lattice_periodic \<omega>1 \<omega>2 "(deriv ^^ n) f"
proof
  fix z :: complex
  have *: "(deriv ^^ n) f (z + c) = (deriv ^^ n) (\<lambda>z. f (z + c)) z" for c
    by (simp add: higher_deriv_shift_0' add_ac o_def) 
  from this show "(deriv ^^ n) f (z + \<omega>1) = (deriv ^^ n) f z" 
                 "(deriv ^^ n) f (z + \<omega>2) = (deriv ^^ n) f z"
    by (simp_all add: f_periodic)
qed

sublocale residue: complex_lattice_periodic \<omega>1 \<omega>2 "residue f"
proof
  fix z :: complex
  have *: "residue f (z + c) = residue (\<lambda>z. f (z + c)) z" for c
    by (simp add: residue_shift_0' add_ac o_def) 
  from this show "residue f (z + \<omega>1) = residue f z" "residue f (z + \<omega>2) = residue f z"
    by (simp_all add: f_periodic)
qed

lemma eventually_remove_sings_eq: "eventually (\<lambda>w. remove_sings f w = f w) (cosparse UNIV)"
  by (simp add: eventually_remove_sings_eq meromorphic)

lemma eventually_remove_sings_eq': "eventually (\<lambda>w. remove_sings f w = f w) (at z)"
  using eventually_remove_sings_eq by (simp add: eventually_cosparse_open_eq)

lemma isolated_zero_analytic_iff: 
  assumes "f analytic_on {z}" "\<not>(\<forall>\<^sub>\<approx>z\<in>UNIV. f z = 0)"
  shows   "isolated_zero f z \<longleftrightarrow> f z = 0"
proof
  assume "isolated_zero f z"
  thus "f z = 0"
    using assms(1) zero_isolated_zero_analytic by blast
next
  assume "f z = 0"
  hence "f \<midarrow>z\<rightarrow> 0"
    using assms(1) by (metis analytic_at_imp_isCont continuous_at)

  have "eventually (\<lambda>z. remove_sings f z \<noteq> 0) (at z)"
  proof (rule ccontr)
    assume "\<not>eventually (\<lambda>z. remove_sings f z \<noteq> 0) (at z)"
    hence "frequently (\<lambda>z. remove_sings f z = 0) (at z)"
      by (auto simp: frequently_def)
    hence "remove_sings f z = 0" for z
      using remove_sings.nicely_meromorphic by (rule frequently_eq_meromorphic_imp_constant) auto
    with eventually_remove_sings_eq show False
      using assms(2) by simp
  qed
  hence "eventually (\<lambda>z. f z \<noteq> 0) (at z)"
    using eventually_remove_sings_eq'[of z] by eventually_elim auto
  with \<open>f \<midarrow>z\<rightarrow> 0\<close> show "isolated_zero f z"
    by (auto simp: isolated_zero_def)
qed

end


context nicely_elliptic_function
begin

lemma nicely_meromorphic' [meromorphic_intros]: "f nicely_meromorphic_on A"
  by (rule nicely_meromorphic_on_subset[OF nicely_meromorphic]) auto

lemma analytic:
  assumes "\<And>z. z \<in> A \<Longrightarrow> \<not>is_pole f z"
  shows   "f analytic_on A"
  using nicely_meromorphic_on_subset[OF nicely_meromorphic]
  by (rule nicely_meromorphic_without_singularities) (use assms in auto)

lemma holomorphic:
  assumes "\<And>z. z \<in> A \<Longrightarrow> \<not>is_pole f z"
  shows   "f holomorphic_on A"
  using analytic by (rule analytic_imp_holomorphic) (use assms in blast)

lemma continuous_on:
  assumes "\<And>z. z \<in> A \<Longrightarrow> \<not>is_pole f z"
  shows   "continuous_on A f"
  using holomorphic by (rule holomorphic_on_imp_continuous_on) (use assms in blast)

sublocale elliptic_function \<omega>1 \<omega>2 f
proof
  show "f meromorphic_on UNIV"
    using nicely_meromorphic unfolding nicely_meromorphic_on_def by blast
qed

lemma analytic_at_iff_not_pole: "f analytic_on {z} \<longleftrightarrow> \<not>is_pole f z"
  using analytic analytic_at_imp_no_pole by blast

lemma constant_or_avoid: "f = (\<lambda>_. c) \<or> (\<forall>\<^sub>\<approx>z\<in>UNIV. f z \<noteq> c)"
  using nicely_meromorphic_imp_constant_or_avoid[OF nicely_meromorphic, of c] by auto

lemma isolated_zero_iff:
  assumes "f \<noteq> (\<lambda>_. 0)"
  shows   "isolated_zero f z \<longleftrightarrow> \<not>is_pole f z \<and> f z = 0"
proof (cases "is_pole f z")
  case True
  thus ?thesis using pole_is_not_zero[of f z]
    by auto
next
  case False
  have "\<not>(\<forall>\<^sub>\<approx>z\<in>UNIV. f z = 0)"
  proof
    assume "\<forall>\<^sub>\<approx>z\<in>UNIV. f z = 0"
    moreover have "\<forall>\<^sub>\<approx>z\<in>UNIV. f z \<noteq> 0"
      using constant_or_avoid[of 0] assms by auto
    ultimately have "\<forall>\<^sub>\<approx>z\<in>(UNIV :: complex set). False"
      by eventually_elim auto
    thus False
      by simp
  qed
  moreover have "f analytic_on {z}"
    using False by (subst analytic_at_iff_not_pole)
  ultimately have "isolated_zero f z \<longleftrightarrow> f z = 0"
    by (subst isolated_zero_analytic_iff) auto
  thus ?thesis
    using False by simp
qed

end


subsection \<open>Basic results about zeros and poles\<close>

text \<open>
  In this section we will show that an elliptic function has the same number of poles
  in any period parallelogram. This number is called its \<^emph>\<open>order\<close>. Then we will show that
  the number of zeros in a period parallelogram is also equal to its order, and that there are
  no elliptic functions with order \<open>1\<close> and no non-constant elliptic functions with order \<open>0\<close>.
\<close>

context elliptic_function
begin

text \<open>
  Due to its meromorphicity and the fact that the period parallelograms are bounded, an 
  elliptic function can only have a finite number of poles and zeros in a period parallelogram.
\<close>
lemma finite_poles_in_parallelogram: "finite {z\<in>period_parallelogram orig. is_pole f z}"
proof (rule finite_subset)
  show "finite (closure (period_parallelogram orig) \<inter> {z. is_pole f z})"
  proof (rule finite_not_islimpt_in_compact)
    show "\<not>z islimpt {z. is_pole f z}" for z
      by (meson UNIV_I meromorphic meromorphic_on_isolated_singularity
          meromorphic_on_subset not_islimpt_poles subsetI)
  qed auto
qed (use closure_subset in auto)

lemma finite_zeros_in_parallelogram: "finite {z\<in>period_parallelogram orig. isolated_zero f z}"
proof (rule finite_subset)
  show "finite (closure (period_parallelogram orig) \<inter> {z. isolated_zero f z})"
  proof (rule finite_not_islimpt_in_compact)
    show "\<not>z islimpt {z. isolated_zero f z}" for z
      using meromorphic_on_imp_not_zero_cosparse[OF meromorphic]
      by (auto simp: eventually_cosparse_open_eq islimpt_iff_eventually)
  qed auto
qed (use closure_subset in auto)


text \<open>
  The \<^emph>\<open>order\<close> of an elliptic function is the number of its poles inside a period parallelogram,
  with multiplicity taken into account. We will later show that this is also the number of zeros.
\<close>
definition (in complex_lattice) elliptic_order :: "(complex \<Rightarrow> complex) \<Rightarrow> nat" where
  "elliptic_order f = (\<Sum>z | z \<in> period_parallelogram 0 \<and> is_pole f z. nat (-zorder f z))"

lemma elliptic_order_const [simp]: "elliptic_order (\<lambda>x. c) = 0"
  by (simp add: elliptic_order_def) 

lemma poles_eq_elliptic_order:
  "(\<Sum>z | z \<in> period_parallelogram orig \<and> is_pole f z. nat (-zorder f z)) = elliptic_order f"
proof -
  define h where "h = to_fund_parallelogram"
  define P where "P = period_parallelogram"
  have "(\<Sum>z \<in> {z\<in>P orig. is_pole f z}. nat (-zorder f (h z))) =
        (\<Sum>z \<in> {z\<in>P 0. is_pole f z}. nat (-zorder f z))"
  proof (rule sum.reindex_bij_betw)
    show "bij_betw h {z \<in> P orig. is_pole f z} {z \<in> P 0. is_pole f z}"
    proof (rule bij_betw_Collect)
      show "bij_betw h (P orig) (P 0)"
        unfolding h_def P_def by (rule bij_betw_to_fund_parallelogram)
    next
      fix z
      show "is_pole f (h z) \<longleftrightarrow> is_pole f z"
        unfolding h_def by (simp add: poles.lattice_cong)
    qed
  qed
  also have "(\<Sum>z \<in> {z\<in>P orig. is_pole f z}. nat (-zorder f (h z))) =
             (\<Sum>z \<in> {z\<in>P orig. is_pole f z}. nat (-zorder f z))"
    using zorder.lattice_cong[of "h z" z for z] by (simp add: h_def)
  finally show ?thesis
    by (simp add: elliptic_order_def P_def)
qed

end


context nicely_elliptic_function
begin

text \<open>
  The order of a (nicely) elliptic function is zero iff it is constant.
  We will later lift this to non-nicely elliptic functions, where we get that the order is zero
  iff the function is \<^emph>\<open>mostly\<close> constant (i.e.\ constant except for a sparse set).

  In combination with our other results relating \<^const>\<open>elliptic_order\<close> to the number of zeros
  and poles inside period parallelograms, this corresponds to Theorems~1.4 and 1.5 in Apostol's
  book.
\<close>
lemma elliptic_order_eq_0_iff: "elliptic_order f = 0 \<longleftrightarrow> f constant_on UNIV"
proof
  assume "f constant_on UNIV"
  then obtain c where f_eq: "f = (\<lambda>_. c)"
    by (auto simp: constant_on_def)
  have [simp]: "\<not>is_pole f z" for z
    unfolding f_eq by auto
  show "elliptic_order f = 0"
    by (simp add: elliptic_order_def)
next
  assume "elliptic_order f = 0"
  define P where "P = period_parallelogram 0"
  have "eventually (\<lambda>z. \<not>is_pole f z) (cosparse UNIV)"
    using meromorphic by (rule meromorphic_on_imp_not_pole_cosparse)
  hence "{z. is_pole f z} sparse_in UNIV"
    by (simp add: eventually_cosparse)
  hence fin: "finite (closure P \<inter> {z. is_pole f z})"
    by (intro sparse_in_compact_finite) (use sparse_in_subset in \<open>auto simp: P_def\<close>)
  
  from \<open>elliptic_order f = 0\<close> have "\<forall>z\<in>{z\<in>P. is_pole f z}. zorder f z \<ge> 0"
    unfolding elliptic_order_def
  proof (subst (asm) sum_nonneg_eq_0_iff)
    show "finite {z \<in> period_parallelogram 0. is_pole f z}"
      by (rule finite_subset[OF _ fin]) (use closure_subset in \<open>auto simp: P_def\<close>)
  qed (auto simp: P_def)
  moreover have "\<forall>z\<in>{z\<in>P. is_pole f z}. zorder f z < 0"
  proof safe
    fix z assume "is_pole f z"
    have "isolated_singularity_at f z"
      using meromorphic by (simp add: meromorphic_on_altdef)
    with \<open>is_pole f z\<close> show "zorder f z < 0"
      using isolated_pole_imp_neg_zorder by blast
  qed
  ultimately have no_poles_P: "\<not>is_pole f z" if "z \<in> P" for z
    using that by force

  have no_poles [simp]: "\<not>is_pole f z" for z
  proof -
    have "\<not>is_pole f (to_fund_parallelogram z)"
      by (intro no_poles_P) (auto simp: P_def)
    also have "is_pole f (to_fund_parallelogram z) \<longleftrightarrow> is_pole f z"
      using poles.lattice_cong rel_to_fund_parallelogram_left by blast
    finally show ?thesis .
  qed

  have ana: "f analytic_on UNIV"
    using nicely_meromorphic by (rule nicely_meromorphic_without_singularities) auto
  have "continuous_on A f" for A
    by (intro analytic_imp_holomorphic holomorphic_on_imp_continuous_on analytic_on_subset[OF ana]) 
       auto
  hence "compact (f ` closure P)"
    by (rule compact_continuous_image) (auto simp: P_def)
  hence "bounded (f ` closure P)"
    by (rule compact_imp_bounded)
  hence "bounded (f ` P)"
    by (rule bounded_subset) (use closure_subset in auto)
  also have "f ` P = f ` UNIV"
  proof safe
    fix z show "f z \<in> f ` P"
      by (rule image_eqI[of _ _ "to_fund_parallelogram z"]) (auto simp: P_def lattice_cong)
  qed auto
  finally show "f constant_on UNIV"
    by (intro Liouville_theorem) (auto intro!: analytic_imp_holomorphic ana)
qed

lemma order_pos_iff: "elliptic_order f > 0 \<longleftrightarrow> \<not>f constant_on UNIV"
  using elliptic_order_eq_0_iff by linarith


text \<open>
  The following lemma allows us to evaluate an integral of the form
  $\int_P h(w) f'(w)/f(w)\,\text{d}w$ more easily, where $P$ is the path along the border of
  a period parallelogram.

  Note that this only works if there are no zeros or pole on the border of the parallelogram.
\<close>
lemma argument_principle_f_gen:
  fixes orig :: complex
  defines "\<gamma> \<equiv> parallelogram_path orig \<omega>1 \<omega>2"
  assumes h: "h holomorphic_on UNIV"
  assumes nz: "\<And>z. z \<in> path_image \<gamma> \<Longrightarrow> f z \<noteq> 0 \<and> \<not>is_pole f z"
  shows "contour_integral \<gamma> (\<lambda>x. h x * deriv f x / f x) =
           contour_integral (linepath orig (orig + \<omega>1)) 
             (\<lambda>z. (h z - h (z + \<omega>2)) * deriv f z / f z) -
           contour_integral (linepath orig (orig + \<omega>2))
             (\<lambda>z. (h z - h (z + \<omega>1)) * deriv f z / f z)"
proof -
  define h' where "h' = (\<lambda>x. h (x + orig) * deriv f (x + orig) / f (x + orig))"
  have [analytic_intros]: "h analytic_on A" for A
    using h analytic_on_holomorphic by blast
  have f_analytic: "f analytic_on A" if "\<And>z. z \<in> A \<Longrightarrow> \<not>is_pole f z" for A
    by (rule nicely_meromorphic_without_singularities)
       (use that in \<open>auto intro!: nicely_meromorphic_on_subset[OF nicely_meromorphic]\<close>)

  have "contour_integral \<gamma> (\<lambda>x. h x * deriv f x / f x) = 
          contour_integral (linepath 0 \<omega>1) (\<lambda>x. h' x - h' (x + \<omega>2)) -
          contour_integral (linepath 0 \<omega>2) (\<lambda>x. h' x - h' (x + \<omega>1))" (is "_ = ?rhs")
    unfolding \<gamma>_def
  proof (subst contour_integral_parallelogram_path'; (fold \<gamma>_def)?)
    have "(\<lambda>x. h x * deriv f x / f x) analytic_on {z. f z \<noteq> 0 \<and> \<not>is_pole f z}"
      by (auto intro!: analytic_intros f_analytic)
    hence "(\<lambda>x. h x * deriv f x / f x) analytic_on path_image \<gamma>"
      by (rule analytic_on_subset) (use nz in auto)
    thus "continuous_on (path_image \<gamma>) (\<lambda>x. h x * deriv f x / f x)" using nz
      by (intro continuous_intros holomorphic_on_imp_continuous_on analytic_imp_holomorphic)
  next
    have 1: "linepath orig (orig + \<omega>1) = (+) orig \<circ> linepath 0 \<omega>1"
     and 2: "linepath orig (orig + \<omega>2) = (+) orig \<circ> linepath 0 \<omega>2"
      by (auto simp: linepath_translate add_ac)
    show "contour_integral (linepath orig (orig + \<omega>1))
            (\<lambda>x. h x * deriv f x / f x - h (x + \<omega>2) * deriv f (x + \<omega>2) / f (x + \<omega>2)) -
          contour_integral (linepath orig (orig + \<omega>2)) 
            (\<lambda>x. h x * deriv f x / f x - h (x + \<omega>1) * deriv f (x + \<omega>1) / f (x + \<omega>1)) = ?rhs"
      unfolding 1 2 contour_integral_translate h'_def by (simp add: algebra_simps)
  qed

  also have "(\<lambda>z. h' z - h' (z + \<omega>1)) = 
             (\<lambda>z. (h (z + orig) - h (z + orig + \<omega>1)) * deriv f (z + orig) / f (z + orig))" 
    (is "?lhs = ?rhs")
  proof
    fix z :: complex
    have "h' z - h' (z + \<omega>1) = 
            h (z + orig) * deriv f (z + orig) / f (z + orig) -
            h (z + orig + \<omega>1) * deriv f (z + orig + \<omega>1) / f (z + orig + \<omega>1)"
      by (simp add: h'_def add_ac)
    also have "\<dots> = (h (z + orig) - h (z + orig + \<omega>1)) * deriv f (z + orig) / f (z + orig)"
      unfolding f_periodic deriv.f_periodic by (simp add: diff_divide_distrib ring_distribs)
    finally show "?lhs z = ?rhs z" .
  qed
  also have "contour_integral (linepath 0 \<omega>2) \<dots> =
             contour_integral ((+) orig \<circ> linepath 0 \<omega>2) (\<lambda>z. (h z - h (z + \<omega>1)) * deriv f z / f z)"
    by (rule contour_integral_translate [symmetric])
  also have "(+) orig \<circ> linepath 0 \<omega>2 = linepath orig (orig + \<omega>2)"
    by (subst linepath_translate) (simp_all add: add_ac)

  also have "contour_integral (linepath 0 \<omega>1) (\<lambda>z. h' z - h' (z + \<omega>2)) =
             contour_integral (linepath 0 \<omega>1) 
               (\<lambda>z. (h (z + orig) - h (z + orig + \<omega>2)) * deriv f (z + orig) / f (z + orig))"
    (is "contour_integral _ ?lhs = contour_integral _ ?rhs")
  proof (rule contour_integral_cong)
    fix z :: complex
    assume z: "z \<in> path_image (linepath 0 \<omega>1)"
    hence "orig + z \<in> path_image ((+) orig \<circ> linepath 0 \<omega>1)"
      by (subst path_image_compose) auto
    also have "(+) orig \<circ> linepath 0 \<omega>1 = linepath orig (orig + \<omega>1)"
      by (subst linepath_translate) (auto simp: add_ac)
    finally have "orig + z \<in> path_image \<gamma>"
      unfolding \<gamma>_def parallelogram_path_def by (auto simp: path_image_join)
    hence nz': "f (orig + z) \<noteq> 0"
      using nz by blast

    have "h' z - h' (z + \<omega>2) = 
            h (z + orig) * deriv f (z + orig) / f (z + orig) -
            h (z + orig + \<omega>2) * (deriv f (z + orig + \<omega>2) / f (z + orig + \<omega>2))"
      by (simp add: h'_def add_ac)
    also have "deriv f (z + orig + \<omega>2) / f (z + orig + \<omega>2) = 
               deriv f (z + orig) / f (z + orig)"
      unfolding f_periodic deriv.f_periodic using nz'
      by (auto simp: divide_simps add_ac)
    also have "h (z + orig) * deriv f (z + orig) / f (z + orig) - h (z + orig + \<omega>2) * \<dots> = ?rhs z"
      by (simp add: ring_distribs diff_divide_distrib)
    finally show "?lhs z = ?rhs z" .
  qed auto
  also have "\<dots> = contour_integral ((+) orig \<circ> linepath 0 \<omega>1) 
                    (\<lambda>z. (h z - h (z + \<omega>2)) * deriv f z / f z)"
    unfolding contour_integral_translate by (simp add: add_ac)
  also have "(+) orig \<circ> linepath 0 \<omega>1 = linepath orig (orig + \<omega>1)"
    by (subst linepath_translate) (simp_all add: add_ac)

  finally show ?thesis .
qed

text \<open>
  Using our lemma with $h(z) = 1$, we immediately get the fact that the integral over $f'(z)/f(z)$
  vanishes.
\<close>
lemma argument_principle_f_1:
  fixes orig :: complex
  defines "\<gamma> \<equiv> parallelogram_path orig \<omega>1 \<omega>2"
  assumes nz: "\<And>z. z \<in> path_image \<gamma> \<Longrightarrow> f z \<noteq> 0 \<and> \<not>is_pole f z"
  shows "contour_integral (parallelogram_path orig \<omega>1 \<omega>2) (\<lambda>x. deriv f x / f x) = 0"
  using argument_principle_f_gen[of "\<lambda>_. 1" orig] nz by (simp add: \<gamma>_def)

text \<open>
  Using our lemma with $h(z) = z$, we see that the integral over $z f'(z)/f(z)$ does not vanish,
  but it is of the form $2\pi i \omega$, where $\omega\in\Lambda$.
\<close>
lemma argument_principle_f_z:
  fixes orig :: complex
  defines "\<gamma> \<equiv> parallelogram_path orig \<omega>1 \<omega>2"
  assumes wf: "\<And>z. z \<in> path_image \<gamma> \<Longrightarrow> f z \<noteq> 0 \<and> \<not>is_pole f z"
  shows "contour_integral \<gamma> (\<lambda>z. z * deriv f z / f z) / (2*pi*\<i>) \<in> \<Lambda>"
proof -
  note [holomorphic_intros del] = holomorphic_deriv
  note [holomorphic_intros] = holomorphic holomorphic_on_subset[OF holomorphic_deriv[of _ UNIV]]
  define \<gamma>1 where "\<gamma>1 = linepath orig (orig + \<omega>1)"
  define \<gamma>2 where "\<gamma>2 = linepath orig (orig + \<omega>2)"
  define \<gamma>1' where "\<gamma>1' = f \<circ> \<gamma>1"
  define \<gamma>2' where "\<gamma>2' = f \<circ> \<gamma>2"
  have path_image_subset: "path_image \<gamma>1 \<subseteq> path_image \<gamma>" "path_image \<gamma>2 \<subseteq> path_image \<gamma>"
    by (auto simp: \<gamma>_def \<gamma>1_def \<gamma>2_def path_image_join closed_segment_commute parallelogram_path_def)

  have "pathstart \<gamma> \<in> path_image \<gamma>"
    by blast
  from wf[OF this] have [simp]: "f orig \<noteq> 0"
    by (simp add: \<gamma>_def)
  have [simp, intro]: "valid_path \<gamma>1" "valid_path \<gamma>2"
    by (simp_all add: \<gamma>1_def \<gamma>2_def)
  have [simp, intro]: "valid_path \<gamma>1'" "valid_path \<gamma>2'" 
    unfolding \<gamma>1'_def \<gamma>2'_def using wf path_image_subset
    by (auto intro!: valid_path_compose_analytic[of _ _ "path_image \<gamma>"] analytic)
  have [simp]: "pathstart \<gamma>1' = f orig" "pathfinish \<gamma>1' = f (orig + \<omega>1)"
               "pathstart \<gamma>2' = f orig" "pathfinish \<gamma>2' = f (orig + \<omega>2)"
    by (simp_all add: \<gamma>1'_def \<gamma>1_def \<gamma>2'_def \<gamma>2_def pathstart_compose pathfinish_compose)

  have wf': "f z \<noteq> 0 \<and> \<not>is_pole f z" if "z \<in> path_image \<gamma>1 \<union> path_image \<gamma>2" for z
  proof -
    note \<open>z \<in> path_image \<gamma>1 \<union> path_image \<gamma>2\<close>
    also have "path_image \<gamma>1 \<union> path_image \<gamma>2 \<subseteq> path_image \<gamma>"
      using path_image_subset by blast
    finally show ?thesis
      using wf[of z] by blast
  qed
  have [simp]: "0 \<notin> path_image \<gamma>1'" "0 \<notin> path_image \<gamma>2'"
    using wf' by (auto simp: \<gamma>1'_def \<gamma>2'_def path_image_compose)


  text \<open>The actual proof starts here.\<close>
  define I1 where "I1 = contour_integral \<gamma>1"
  define I2 where "I2 = contour_integral \<gamma>2"

  have "winding_number \<gamma>1' 0 \<in> \<int>"
    by (rule integer_winding_number) (auto intro!: valid_path_imp_path simp: f_periodic)
  then obtain m where m: "winding_number \<gamma>1' 0 = of_int m"
    by (elim Ints_cases)

  have "winding_number \<gamma>2' 0 \<in> \<int>"
    by (rule integer_winding_number) (auto intro!: valid_path_imp_path simp: f_periodic)
  then obtain n where n: "winding_number \<gamma>2' 0 = of_int n"
    by (elim Ints_cases)

  have "contour_integral \<gamma> (\<lambda>z. z * deriv f z / f z) / (2*pi*\<i>) =
          (I1 (\<lambda>z. (-\<omega>2) * (deriv f z / f z)) - I2 (\<lambda>z. (-\<omega>1) * (deriv f z / f z))) / (2*pi*\<i>)"
    unfolding \<gamma>_def I1_def I2_def \<gamma>1_def \<gamma>2_def using wf
    by (subst argument_principle_f_gen) (auto simp: diff_divide_distrib \<gamma>_def)
  also have "I1 (\<lambda>z. (-\<omega>2) * (deriv f z / f z)) - I2 (\<lambda>z. (-\<omega>1) * (deriv f z / f z)) = 
             (-\<omega>2) * I1 (\<lambda>z. deriv f z / f z) - (-\<omega>1) * I2 (\<lambda>z. deriv f z / f z)"
    using wf' unfolding I1_def I2_def \<gamma>1_def \<gamma>2_def
    by (subst (1 2) contour_integral_lmul)
       (auto intro!: contour_integrable_continuous_linepath holomorphic_on_imp_continuous_on
                     analytic_imp_holomorphic analytic_intros analytic)
  also have "\<dots> = \<omega>1 * contour_integral \<gamma>2' (\<lambda>z. 1 / z) - 
                  \<omega>2 * contour_integral \<gamma>1' (\<lambda>z. 1 / z)"
    unfolding I1_def I2_def \<gamma>1'_def \<gamma>2'_def using wf'
    by (subst (1 2) contour_integral_comp_analyticW[OF analytic[of "path_image \<gamma>1 \<union> path_image \<gamma>2"]])
       (auto simp: \<gamma>1_def)
  also have "\<dots> / (2 * pi * \<i>) = \<omega>1 * winding_number \<gamma>2' 0 - \<omega>2 * winding_number \<gamma>1' 0"
    by (subst (1 2) winding_number_valid_path)
       (auto intro!: valid_path_compose_analytic analytic simp: diff_divide_distrib)
  also have "\<dots> = of_int n * \<omega>1 - of_int m * \<omega>2"
    by (auto simp: m n)
  also have "\<dots> \<in> \<Lambda>"
    by (auto intro!: lattice_intros)
  finally show ?thesis .
qed

text \<open>
  By using the fact that the integral $f'(z)/f(z)$ along the border of a period parallelogram
  vanishes, we get the following fact: The number of zeros in the period parallelogram equals the
  number of poles, i.e.\ the order.

  The only difficulty left here is to show that 1.\ the number of zeros is invariant under
  which period parallelogram we choose, and 2.\ there is a period parallelogram whose borders
  do not contain any zeros or poles.

  This is essentially Theorem~1.8 in Apostol's book.
\<close>
lemma zeros_eq_elliptic_order_aux:
  "(\<Sum>z | z \<in> period_parallelogram orig \<and> isolated_zero f z. nat (zorder f z)) = elliptic_order f"
proof (cases "f = (\<lambda>_. 0)")
  case True
  hence "elliptic_order f = 0"
    by (subst elliptic_order_eq_0_iff) (auto simp: constant_on_def)
  moreover have "\<not>isolated_zero f z" for z
    by (simp add: isolated_zero_def True)
  ultimately show ?thesis
    by simp
next
  case False
  define s where "s = complex_of_real (sgn (Im (\<omega>2 / \<omega>1)))"
  have [simp]: "s \<noteq> 0"
    using fundpair by (auto simp: s_def sgn_if fundpair_def complex_is_Real_iff)

  have ev_nonzero: "eventually (\<lambda>z. f z \<noteq> 0) (cosparse UNIV)"
    using nicely_meromorphic False nicely_meromorphic_imp_constant_or_avoid[of f UNIV 0]
    by auto
  have isolated_zero_iff: "isolated_zero f z \<longleftrightarrow> \<not>is_pole f z \<and> f z = 0" for z
    using isolated_zero_iff[OF False] by blast

  define P where "P = period_parallelogram"
  define avoid where "avoid = {z. isolated_zero f z \<or> is_pole f z}"
  have sparse_avoid: "\<not>z islimpt avoid" for z
  proof -
    have "\<forall>\<^sub>\<approx>z\<in>UNIV. \<not>isolated_zero f z \<and> \<not>is_pole f z" using meromorphic 
      by (intro meromorphic_on_imp_not_zero_cosparse 
                meromorphic_on_imp_not_pole_cosparse eventually_conj)
    hence "\<forall>\<^sub>\<approx>z\<in>UNIV. z \<notin> avoid"
      by eventually_elim (auto simp: avoid_def)
    thus ?thesis
      by (auto simp: eventually_cosparse_open_eq islimpt_iff_eventually)
  qed
  thus ?thesis
    unfolding P_def [symmetric]
  proof (induction orig rule: shifted_period_parallelogram_avoid_wlog)
    case (shift orig d)
    obtain h where h: "bij_betw h (P (orig + d)) (P orig)" "\<And>z. rel (h z) z"
      using bij_betw_period_parallelograms unfolding P_def by blast
    have "(\<Sum>z | z \<in> P (orig + d) \<and> isolated_zero f z. nat (zorder f (h z))) =
          (\<Sum>z | z \<in> P orig \<and> isolated_zero f z. nat (zorder f z))"
      by (rule sum.reindex_bij_betw, rule bij_betw_Collect[OF h(1)])
         (auto simp: zeros.lattice_cong[OF h(2)])
    also have "(\<Sum>z | z \<in> P (orig + d) \<and> isolated_zero f z. nat (zorder f (h z))) = 
               (\<Sum>z | z \<in> P (orig + d) \<and> isolated_zero f z. nat (zorder f z))"
      by (simp add: zorder.lattice_cong[OF h(2)])
    finally show ?case
      using shift by simp
  next
    case (avoid orig)
    define \<gamma> where "\<gamma> = parallelogram_path orig \<omega>1 \<omega>2"
    define zeros where "zeros = {z\<in>P orig. isolated_zero f z}"
    define poles where "poles = {z\<in>P orig. is_pole f z}"
    have \<gamma>: "\<not>isolated_zero f z \<and> \<not>is_pole f z" if "z \<in> path_image \<gamma>" for z
      using avoid that by (auto simp: avoid_def \<gamma>_def)
    have "compact (closure (P orig))"
      unfolding P_def by auto
    then obtain R where R: "closure (P orig) \<subseteq> ball 0 R"
      using compact_imp_bounded bounded_subset_ballD by blast
    define A :: "complex set" where "A = ball 0 R"
    have A: "closure (P orig) \<subseteq> A"
      using R by (simp add: A_def)

    have fin: "finite {w \<in> A. f w = 0 \<or> w \<in> {z. is_pole f z}}"
    proof (rule finite_subset)
      show "finite (cball 0 R \<inter> avoid)"
        by (rule finite_not_islimpt_in_compact) (use sparse_avoid in auto)
    next
      show "{w \<in> A. f w = 0 \<or> w \<in> {z. is_pole f z}} \<subseteq> cball 0 R \<inter> avoid"
        by (auto simp: avoid_def A_def isolated_zero_iff)
    qed

    have "contour_integral \<gamma> (\<lambda>x. deriv f x * 1 / f x) = 
            of_real (2 * pi) * \<i> * (\<Sum>p\<in>{w\<in>A. f w = 0 \<or> w \<in> {z. is_pole f z}}. 
              winding_number \<gamma> p * 1 * of_int (zorder f p))"
    proof (rule argument_principle)
      show "open A" "connected A"
        by (auto simp: A_def)
    next
      have "f analytic_on A - {z. is_pole f z}"
        using nicely_meromorphic_on_subset[OF nicely_meromorphic]
        by (rule nicely_meromorphic_without_singularities) auto
      thus "f holomorphic_on A - {z. is_pole f z}"
        by (rule analytic_imp_holomorphic)
    next
      show "path_image \<gamma> \<subseteq> A - {w \<in> A. f w = 0 \<or> w \<in> {z. is_pole f z}}"
        using A \<gamma> path_image_parallelogram_subset_closure[of orig] 
        by (auto simp: \<gamma>_def P_def isolated_zero_iff)
    next
      show "finite {w \<in> A. f w = 0 \<or> w \<in> {z. is_pole f z}}"
        by (rule finite_subset[OF _ fin]) auto
    next
      show "\<forall>z. z \<notin> A \<longrightarrow> winding_number \<gamma> z = 0"
        using A unfolding \<gamma>_def P_def by (auto intro!: winding_number_parallelogram_outside)
    qed (auto simp: \<gamma>_def)
    also have "contour_integral \<gamma> (\<lambda>x. deriv f x * 1 / f x) = 0"
      using argument_principle_f_1[of orig] \<gamma> by (auto simp: \<gamma>_def isolated_zero_iff)
    finally have "(\<Sum>z\<in>{z\<in>A. f z = 0 \<or> is_pole f z}. winding_number \<gamma> z * of_int (zorder f z)) = 0"
      by simp

    also have "(\<Sum>z\<in>{z\<in>A. f z = 0 \<or> is_pole f z}. winding_number \<gamma> z * of_int (zorder f z)) = 
               (\<Sum>z\<in>{z\<in>P orig. f z = 0 \<or> is_pole f z}. s * of_int (zorder f z))"
    proof (intro sum.mono_neutral_cong_right ballI, goal_cases)
      case (3 z)
      hence "z \<notin> P orig \<union> frontier (P orig)"
        using \<gamma>[of z] by (auto simp: isolated_zero_iff P_def \<gamma>_def path_image_parallelogram_path)
      also have "P orig \<union> frontier (P orig) = closure (P orig)"
        using closure_Un_frontier by blast
      finally have "winding_number \<gamma> z = 0"
        unfolding \<gamma>_def P_def using winding_number_parallelogram_outside by blast
      thus ?case
        by simp
    next
      case (4 z)
      hence "z \<in> P orig - frontier (P orig)"
        using \<gamma>[of z] by (auto simp: isolated_zero_iff P_def \<gamma>_def path_image_parallelogram_path)
      also have "P orig - frontier (P orig) = interior (P orig)"
        using interior_subset closure_subset by (auto simp: frontier_def)
      finally have "winding_number \<gamma> z = s"
        unfolding s_def \<gamma>_def P_def by (rule winding_number_parallelogram_inside)
      thus ?case
        by simp
    qed (use A fin closure_subset in auto)
    also have "{z\<in>P orig. f z = 0 \<or> is_pole f z} = zeros \<union> poles"
      by (auto simp: zeros_def poles_def isolated_zero_iff)
    also have "(\<Sum>z\<in>zeros \<union> poles. s * complex_of_int (zorder f z)) =
                 s * of_int (\<Sum>z\<in>zeros \<union> poles. zorder f z)"
      by (simp add: sum_distrib_left)
    finally have "(\<Sum>z\<in>zeros \<union> poles. zorder f z) = 0"
      by (simp del: of_int_sum)

    also have "(\<Sum>z\<in>zeros \<union> poles. zorder f z) = (\<Sum>z\<in>zeros. zorder f z) + (\<Sum>z\<in>poles. zorder f z)"
      by (subst sum.union_disjoint)
         (use A closure_subset
           in \<open>auto simp: zeros_def poles_def isolated_zero_iff intro!: finite_subset[OF _ fin]\<close>)
    also have "(\<Sum>z\<in>zeros. zorder f z) = (\<Sum>z\<in>zeros. int (nat (zorder f z)))"
    proof (intro sum.cong)
      fix z assume z: "z \<in> zeros"
      hence "\<not>is_pole f z"
        by (auto simp: zeros_def isolated_zero_iff)
      hence "f analytic_on {z}"
        using nicely_meromorphic nicely_meromorphic_on_imp_analytic_at by blast
      hence "zorder f z > 0"
        using z by (intro zorder_isolated_zero_pos) (auto simp: zeros_def)
      thus "zorder f z = int (nat (zorder f z))"
        by simp
    qed auto
    also have "\<dots> = int (\<Sum>z\<in>zeros. nat (zorder f z))"
      by simp

    also have "(\<Sum>z\<in>poles. zorder f z) = (\<Sum>z\<in>poles. -int (nat (-zorder f z)))"
    proof (intro sum.cong)
      fix z assume "z \<in> poles"
      hence "zorder f z < 0" using meromorphic 
        by (auto intro!: isolated_pole_imp_neg_zorder simp: poles_def meromorphic_on_altdef)
      thus "zorder f z = - int (nat (- zorder f z))"
        by simp
    qed auto
    also have "\<dots> = -int (\<Sum>z\<in>poles. nat (-zorder f z))"
      by (simp add: sum_negf)

    also have "(\<Sum>z\<in>poles. nat (-zorder f z)) = elliptic_order f"
      using poles_eq_elliptic_order[of orig] by (simp add: poles_def P_def)
    finally have "(\<Sum>z\<in>zeros. nat (zorder f z)) = elliptic_order f"
      by linarith
    thus ?case
      by (simp add: zeros_def)
  qed
qed

text \<open>
  In the same vein, we get the following from our earlier result about the integral over
  $z f'(z)/f(z)$: The sum over all zeros and poles (counted with multiplicity, where poles have
  negative multiplicity) in a period parallelogram is a lattice point.

  This is Exercise~1.2 in Apostol's book.
\<close>
lemma sum_zeros_poles_in_lattice_aux:
  defines "Z \<equiv> (\<lambda>orig. {z\<in>period_parallelogram orig. isolated_zero f z \<or> is_pole f z})"
  defines "S \<equiv> (\<lambda>orig. \<Sum>z\<in>Z orig. of_int (zorder f z) * z)"
  shows   "S orig \<in> \<Lambda>"
proof (cases "f = (\<lambda>_. 0)")
  case True
  hence "elliptic_order f = 0"
    by (subst elliptic_order_eq_0_iff) (auto simp: constant_on_def)
  moreover have "\<not>isolated_zero f z" "\<not>is_pole f z" for z
    by (auto simp: isolated_zero_def True)
  ultimately show ?thesis
    by (simp add: S_def Z_def)
next
  case False
  define s where "s = complex_of_real (sgn (Im (\<omega>2 / \<omega>1)))"
  have s: "s \<in> {-1, 1}"
    using fundpair by (auto simp: s_def sgn_if fundpair_def complex_is_Real_iff)

  have ev_nonzero: "eventually (\<lambda>z. f z \<noteq> 0) (cosparse UNIV)"
    using nicely_meromorphic False nicely_meromorphic_imp_constant_or_avoid[of f UNIV 0]
    by auto

  have isolated_zero_iff: "isolated_zero f z \<longleftrightarrow> \<not>is_pole f z \<and> f z = 0" for z
  proof
    assume z: "\<not>is_pole f z \<and> f z = 0"
    hence "f analytic_on {z}"
      using nicely_meromorphic by (simp add: nicely_meromorphic_on_imp_analytic_at)
    with z have "f \<midarrow>z\<rightarrow> 0"
      by (metis analytic_at_imp_isCont continuous_within)     
    moreover have "eventually (\<lambda>z. f z \<noteq> 0) (at z)"
      using ev_nonzero by (subst (asm) eventually_cosparse_open_eq) auto
    ultimately show "isolated_zero f z"
      unfolding isolated_zero_def by blast
  next
    assume "isolated_zero f z"
    thus "\<not>is_pole f z \<and> f z = 0"
      by (meson iso_tuple_UNIV_I nicely_meromorphic
          nicely_meromorphic_on_imp_analytic_at pole_is_not_zero
          zero_isolated_zero_analytic)
  qed

  define P where "P = period_parallelogram"
  define avoid where "avoid = {z. isolated_zero f z \<or> is_pole f z}"
  have sparse_avoid: "\<not>z islimpt avoid" for z
  proof -
    have "\<forall>\<^sub>\<approx>z\<in>UNIV. \<not>isolated_zero f z \<and> \<not>is_pole f z" using meromorphic 
      by (intro meromorphic_on_imp_not_zero_cosparse 
                meromorphic_on_imp_not_pole_cosparse eventually_conj)
    hence "\<forall>\<^sub>\<approx>z\<in>UNIV. z \<notin> avoid"
      by eventually_elim (auto simp: avoid_def)
    thus ?thesis
      by (auto simp: eventually_cosparse_open_eq islimpt_iff_eventually)
  qed
  thus ?thesis
    unfolding P_def [symmetric]
  proof (induction orig rule: shifted_period_parallelogram_avoid_wlog)
    case (shift orig d)
    obtain h where h: "bij_betw h (P (orig + d)) (P orig)" "\<And>z. rel (h z) z"
      using bij_betw_period_parallelograms unfolding P_def by blast
    have h': "bij_betw h (Z (orig + d)) (Z orig)"
      unfolding Z_def
      by (rule bij_betw_Collect)
         (use h(1) zeros.lattice_cong[OF h(2)] poles.lattice_cong[OF h(2)] in \<open>auto simp: P_def\<close>)

    have "S (orig + d) = (\<Sum>z\<in>Z (orig + d). of_int (zorder f z) * z)"
      by (simp add: S_def)
    also have "rel (\<Sum>z\<in>Z (orig + d). of_int (zorder f z) * z)
                   (\<Sum>z\<in>Z (orig + d). of_int (zorder f z) * h z)"
      by (intro lattice_intros) (use h(2) in \<open>auto simp: rel_sym\<close>)
    also have "\<dots> = (\<Sum>z\<in>Z (orig + d). of_int (zorder f (h z)) * h z)"
      by (simp add: zorder.lattice_cong[OF h(2)])
    also have "\<dots> = (\<Sum>z\<in>Z orig. of_int (zorder f z) * z)"
      using h' by (rule sum.reindex_bij_betw)
    also have "\<dots> = S orig"
      by (simp add: S_def)
    also have "S orig \<in> \<Lambda>"
      by fact
    finally show ?case .
  next
    case (avoid orig)
    define \<gamma> where "\<gamma> = parallelogram_path orig \<omega>1 \<omega>2"
    define zeros where "zeros = {z\<in>P orig. isolated_zero f z}"
    define poles where "poles = {z\<in>P orig. is_pole f z}"
    have \<gamma>: "\<not>isolated_zero f z \<and> \<not>is_pole f z" if "z \<in> path_image \<gamma>" for z
      using avoid that by (auto simp: avoid_def \<gamma>_def)
    have "compact (closure (P orig))"
      unfolding P_def by auto
    then obtain R where R: "closure (P orig) \<subseteq> ball 0 R"
      using compact_imp_bounded bounded_subset_ballD by blast
    define A :: "complex set" where "A = ball 0 R"
    have A: "closure (P orig) \<subseteq> A"
      using R by (simp add: A_def)

    have fin: "finite {w \<in> A. f w = 0 \<or> w \<in> {z. is_pole f z}}"
    proof (rule finite_subset)
      show "finite (cball 0 R \<inter> avoid)"
        by (rule finite_not_islimpt_in_compact) (use sparse_avoid in auto)
    next
      show "{w \<in> A. f w = 0 \<or> w \<in> {z. is_pole f z}} \<subseteq> cball 0 R \<inter> avoid"
        by (auto simp: avoid_def A_def isolated_zero_iff)
    qed

    have "contour_integral \<gamma> (\<lambda>x. deriv f x * x / f x) = 
            of_real (2 * pi) * \<i> * (\<Sum>p\<in>{w\<in>A. f w = 0 \<or> w \<in> {z. is_pole f z}}. 
              winding_number \<gamma> p * p * of_int (zorder f p))"
    proof (rule argument_principle)
      show "open A" "connected A"
        by (auto simp: A_def)
    next
      have "f analytic_on A - {z. is_pole f z}"
        using nicely_meromorphic_on_subset[OF nicely_meromorphic]
        by (rule nicely_meromorphic_without_singularities) auto
      thus "f holomorphic_on A - {z. is_pole f z}"
        by (rule analytic_imp_holomorphic)
    next
      show "path_image \<gamma> \<subseteq> A - {w \<in> A. f w = 0 \<or> w \<in> {z. is_pole f z}}"
        using A \<gamma> path_image_parallelogram_subset_closure[of orig] 
        by (auto simp: \<gamma>_def P_def isolated_zero_iff)
    next
      show "finite {w \<in> A. f w = 0 \<or> w \<in> {z. is_pole f z}}"
        by (rule finite_subset[OF _ fin]) auto
    next
      show "\<forall>z. z \<notin> A \<longrightarrow> winding_number \<gamma> z = 0"
        using A unfolding \<gamma>_def P_def by (auto intro!: winding_number_parallelogram_outside)
    qed (auto simp: \<gamma>_def)
    hence "(\<Sum>p\<in>{w\<in>A. f w = 0 \<or> is_pole f w}. winding_number \<gamma> p * p * of_int (zorder f p)) =
           contour_integral \<gamma> (\<lambda>x. x * deriv f x / f x) / (2 * pi * \<i>)"
      by (simp add: field_simps)
    also have "\<dots> \<in> \<Lambda>"
      unfolding \<gamma>_def by (rule argument_principle_f_z) (use \<gamma> in \<open>auto simp: \<gamma>_def isolated_zero_iff\<close>)

    also have "(\<Sum>z\<in>{z\<in>A. f z = 0 \<or> is_pole f z}. winding_number \<gamma> z * z * of_int (zorder f z)) = 
               (\<Sum>z\<in>Z orig. s * of_int (zorder f z) * z)"
    proof (intro sum.mono_neutral_cong_right ballI, goal_cases)
      case (3 z)
      hence "z \<notin> P orig \<union> frontier (P orig)"
        using \<gamma>[of z] by (auto simp: Z_def isolated_zero_iff P_def \<gamma>_def path_image_parallelogram_path)
      also have "P orig \<union> frontier (P orig) = closure (P orig)"
        using closure_Un_frontier by blast
      finally have "winding_number \<gamma> z = 0"
        unfolding \<gamma>_def P_def using winding_number_parallelogram_outside by blast
      thus ?case
        by simp
    next
      case (4 z)
      hence "z \<in> P orig - frontier (P orig)"
        using \<gamma>[of z] by (auto simp: Z_def isolated_zero_iff P_def \<gamma>_def path_image_parallelogram_path)
      also have "P orig - frontier (P orig) = interior (P orig)"
        using interior_subset closure_subset by (auto simp: frontier_def)
      finally have "winding_number \<gamma> z = s"
        unfolding s_def \<gamma>_def P_def by (rule winding_number_parallelogram_inside)
      thus ?case
        by simp
    qed (use A fin closure_subset in \<open>auto simp: Z_def P_def isolated_zero_iff\<close>)
    also have "(\<Sum>z\<in>Z orig. s * of_int (zorder f z) * z) = s * S orig"
      by (simp add: S_def sum_distrib_left mult.assoc)
    finally show "S orig \<in> \<Lambda>"
      using s by (auto simp: uminus_in_lattice_iff)
  qed
qed

text \<open>
  Again, similarly: The residues in a period parallelogram sum to 0.
\<close>
lemma sum_residues_eq_0_aux:
  defines "Q \<equiv> (\<lambda>orig. {z\<in>period_parallelogram orig. is_pole f z})"
  defines "S \<equiv> (\<lambda>orig. \<Sum>z\<in>Q orig. residue f z)"
  shows   "S orig \<in> \<Lambda>"
proof (cases "f = (\<lambda>_. 0)")
  case True
  hence "elliptic_order f = 0"
    by (subst elliptic_order_eq_0_iff) (auto simp: constant_on_def)
  moreover have "\<not>is_pole f z" for z
    by (auto simp: isolated_zero_def True)
  ultimately show ?thesis
    by (simp add: S_def Q_def)
next
  case False
  define s where "s = complex_of_real (sgn (Im (\<omega>2 / \<omega>1)))"
  have s: "s \<in> {-1, 1}"
    using fundpair by (auto simp: s_def sgn_if fundpair_def complex_is_Real_iff)

  have ev_nonzero: "eventually (\<lambda>z. f z \<noteq> 0) (cosparse UNIV)"
    using nicely_meromorphic False nicely_meromorphic_imp_constant_or_avoid[of f UNIV 0]
    by auto

  define P where "P = period_parallelogram"
  define avoid where "avoid = {z. is_pole f z}"
  have sparse_avoid: "\<not>z islimpt avoid" for z
    unfolding avoid_def
    by (meson UNIV_I meromorphic meromorphic_on_isolated_singularity
              meromorphic_on_subset not_islimpt_poles subsetI)
  thus ?thesis
    unfolding P_def [symmetric]
  proof (induction orig rule: shifted_period_parallelogram_avoid_wlog)
    case (shift orig d)
    obtain h where h: "bij_betw h (P (orig + d)) (P orig)" "\<And>z. rel (h z) z"
      using bij_betw_period_parallelograms unfolding P_def by blast
    have h': "bij_betw h (Q (orig + d)) (Q orig)"
      unfolding Q_def
      by (rule bij_betw_Collect)
         (use h(1) poles.lattice_cong[OF h(2)] in \<open>auto simp: P_def\<close>)

    have "S (orig + d) = (\<Sum>z\<in>Q (orig + d). residue f z)"
      by (simp add: S_def)
    also have "\<dots> = (\<Sum>z\<in>Q (orig + d). residue f (h z))"
      by (simp add: rel_sym residue.lattice_cong[OF h(2)])
    also have "\<dots> = (\<Sum>z\<in>Q orig. residue f z)"
      using h' by (rule sum.reindex_bij_betw)
    also have "\<dots> = S orig"
      by (simp add: S_def)
    also have "S orig \<in> \<Lambda>"
      by fact
    finally show ?case .
  next
    case (avoid orig)
    define \<gamma> where "\<gamma> = parallelogram_path orig \<omega>1 \<omega>2"
    have \<gamma>: "\<not>is_pole f z" if "z \<in> path_image \<gamma>" for z
      using avoid that by (auto simp: avoid_def \<gamma>_def)
    have "compact (closure (P orig))"
      unfolding P_def by auto
    then obtain R where R: "closure (P orig) \<subseteq> ball 0 R"
      using compact_imp_bounded bounded_subset_ballD by blast
    define A :: "complex set" where "A = ball 0 R"
    have A: "closure (P orig) \<subseteq> A"
      using R by (simp add: A_def)

    have fin: "finite {w \<in> A. is_pole f w}"
    proof (rule finite_subset)
      show "finite (cball 0 R \<inter> avoid)"
        by (rule finite_not_islimpt_in_compact) (use sparse_avoid in auto)
    next
      show "{z \<in> A. is_pole f z} \<subseteq> cball 0 R \<inter> avoid"
        by (auto simp: avoid_def A_def)
    qed

    have "contour_integral \<gamma> f = 
            of_real (2 * pi) * \<i> * (\<Sum>p\<in>{z\<in>A. is_pole f z}. winding_number \<gamma> p * residue f p)"
    proof (rule Residue_theorem)
      show "open A" "connected A"
        by (auto simp: A_def)
    next
      have "f analytic_on A - {z\<in>A. is_pole f z}"
        using nicely_meromorphic_on_subset[OF nicely_meromorphic]
        by (rule nicely_meromorphic_without_singularities) auto
      thus "f holomorphic_on A - {z\<in>A. is_pole f z}"
        by (rule analytic_imp_holomorphic)
    next
      show "path_image \<gamma> \<subseteq> A - {z \<in> A. is_pole f z}"
        using A \<gamma> path_image_parallelogram_subset_closure[of orig] 
        by (auto simp: \<gamma>_def P_def)
    next
      show "finite {z \<in> A. is_pole f z}"
        using fin by simp
    next
      show "\<forall>z. z \<notin> A \<longrightarrow> winding_number \<gamma> z = 0"
        using A unfolding \<gamma>_def P_def by (auto intro!: winding_number_parallelogram_outside)
    qed (auto simp: \<gamma>_def)
    also have "(\<Sum>p\<in>{z\<in>A. is_pole f z}. winding_number \<gamma> p * residue f p) =
               (\<Sum>p\<in>Q orig. s * residue f p)"
    proof (intro sum.mono_neutral_cong_right ballI, goal_cases)
      case (3 z)
      hence "z \<notin> P orig \<union> frontier (P orig)"
        using \<gamma>[of z] by (auto simp: Q_def P_def \<gamma>_def path_image_parallelogram_path)
      also have "P orig \<union> frontier (P orig) = closure (P orig)"
        using closure_Un_frontier by blast
      finally have "winding_number \<gamma> z = 0"
        unfolding \<gamma>_def P_def using winding_number_parallelogram_outside by blast
      thus ?case
        by simp
    next
      case (4 z)
      hence "z \<in> P orig - frontier (P orig)"
        using \<gamma>[of z] by (auto simp: Q_def P_def \<gamma>_def path_image_parallelogram_path)
      also have "P orig - frontier (P orig) = interior (P orig)"
        using interior_subset closure_subset by (auto simp: frontier_def)
      finally have "winding_number \<gamma> z = s"
        unfolding s_def \<gamma>_def P_def by (rule winding_number_parallelogram_inside)
      thus ?case
        by simp
    qed (use A fin closure_subset in \<open>auto simp: Q_def P_def\<close>)
    also have "\<dots> = s * (\<Sum>z\<in>Q orig. residue f z)"
      by (simp add: sum_distrib_left)
    also have "contour_integral \<gamma> f = 0"
      using \<gamma> unfolding \<gamma>_def
      by (subst contour_integral_parallelogram_path')
         (auto simp: f_periodic intro!: continuous_on)
    finally show ?case
      using s by (auto simp: S_def)
  qed
qed

end


text \<open>
  We now lift everything we have done to non-nice elliptic functions.
\<close>

context elliptic_function
begin

lemma elliptic_order_remove_sings [simp]: "elliptic_order (remove_sings f) = elliptic_order f"
  unfolding elliptic_order_def by simp

interpretation elliptic_function_remove_sings ..

theorem zeros_eq_elliptic_order:
  "(\<Sum>z | z \<in> period_parallelogram orig \<and> isolated_zero f z. nat (zorder f z)) = elliptic_order f"
  using remove_sings.zeros_eq_elliptic_order_aux by simp

lemma card_poles_le_order: "card {z\<in>period_parallelogram orig. is_pole f z} \<le> elliptic_order f"
proof -
  have "zorder f z < 0" if "is_pole f z" for z
    using that by (simp add: isolated_pole_imp_neg_zorder)
  hence "(\<Sum>z | z \<in> period_parallelogram orig \<and> is_pole f z. 1) \<le>
         (\<Sum>z | z \<in> period_parallelogram orig \<and> is_pole f z. nat (-zorder f z))"
    by (intro sum_mono) force+
  thus ?thesis
    by (simp add: poles_eq_elliptic_order)
qed

lemma card_zeros_le_order: "card {z\<in>period_parallelogram orig. isolated_zero f z} \<le> elliptic_order f"
proof -
  have "zorder f z > 0" if "isolated_zero f z" for z
    using that by (intro zorder_isolated_zero_pos') auto
  hence "(\<Sum>z | z \<in> period_parallelogram orig \<and> isolated_zero f z. 1) \<le>
         (\<Sum>z | z \<in> period_parallelogram orig \<and> isolated_zero f z. nat (zorder f z))"
    by (intro sum_mono) force+
  thus ?thesis
    by (simp add: zeros_eq_elliptic_order)
qed

corollary elliptic_order_eq_0_iff_no_poles: "elliptic_order f = 0 \<longleftrightarrow> (\<forall>z. \<not>is_pole f z)"
proof
  assume "elliptic_order f = 0"
  hence "card {z\<in>period_parallelogram 0. is_pole f z} \<le> 0"
    using card_poles_le_order[of 0] by simp
  hence "{z\<in>period_parallelogram 0. is_pole f z} = {}"
    using finite_poles_in_parallelogram[of 0] by simp
  hence *: "\<not>is_pole f z" if "z \<in> period_parallelogram 0" for z
    using that by blast
  hence "\<not>is_pole f z" for z
    using *[of "to_fund_parallelogram z"] poles.lattice_cong[of z "to_fund_parallelogram z"]
    by (auto simp: to_fund_parallelogram_in_parallelogram)
  thus "\<forall>z. \<not>is_pole f z"
    by blast
qed (simp_all add: elliptic_order_def)

corollary elliptic_order_eq_0_iff_no_zeros: "elliptic_order f = 0 \<longleftrightarrow> (\<forall>z. \<not>isolated_zero f z)"
proof
  assume "elliptic_order f = 0"
  hence "card {z\<in>period_parallelogram 0. isolated_zero f z} \<le> 0"
    using card_zeros_le_order[of 0] by simp
  hence "{z\<in>period_parallelogram 0. isolated_zero f z} = {}"
    using finite_zeros_in_parallelogram[of 0] by simp
  hence *: "\<not>isolated_zero f z" if "z \<in> period_parallelogram 0" for z
    using that by blast
  hence "\<not>isolated_zero f z" for z
    using *[of "to_fund_parallelogram z"] zeros.lattice_cong[of z "to_fund_parallelogram z"]
    by (auto simp: to_fund_parallelogram_in_parallelogram)
  thus "\<forall>z. \<not>isolated_zero f z"
    by blast
qed (simp_all flip: zeros_eq_elliptic_order[of 0])

lemma elliptic_order_eq_0_iff_const_cosparse:
  "elliptic_order f = 0 \<longleftrightarrow> (\<exists>c. \<forall>\<^sub>\<approx>x\<in>UNIV. f x = c)"
proof -
  have "elliptic_order f = 0 \<longleftrightarrow> elliptic_order (remove_sings f) = 0"
    by simp
  also have "\<dots> \<longleftrightarrow> remove_sings f constant_on UNIV"
    by (subst remove_sings.elliptic_order_eq_0_iff) auto
  also have "\<dots> \<longleftrightarrow> (\<exists>c. \<forall>\<^sub>\<approx>x\<in>UNIV. f x = c)"
    by (subst remove_sings_constant_on_open_iff) (auto intro: meromorphic)
  finally show ?thesis .
qed

lemma cosparse_eq_or_avoid: "(\<forall>\<^sub>\<approx>z\<in>UNIV. f z = c) \<or> (\<forall>\<^sub>\<approx>z\<in>UNIV. f z \<noteq> c)"
  by (simp add: Convex.connected_UNIV meromorphic meromorphic_imp_constant_or_avoid)

lemma frequently_eq_imp_almost_everywhere_eq:
  assumes "frequently (\<lambda>z. f z = c) (at z)"
  shows   "eventually (\<lambda>z. f z = c) (cosparse UNIV)"
proof -
  have "\<not>eventually (\<lambda>z. f z \<noteq> c) (cosparse UNIV)"
    using assms by (auto simp: eventually_cosparse_open_eq frequently_def)
  thus ?thesis
    using cosparse_eq_or_avoid[of c] by auto
qed

lemma eventually_eq_imp_almost_everywhere_eq:
  assumes "eventually (\<lambda>z. f z = c) (at z)"
  shows   "eventually (\<lambda>z. f z = c) (cosparse UNIV)"
  using assms frequently_eq_imp_almost_everywhere_eq eventually_frequently at_neq_bot by blast

lemma avoid: "elliptic_order f > 0 \<Longrightarrow> \<forall>\<^sub>\<approx>z\<in>UNIV. f z \<noteq> c"
  using cosparse_eq_or_avoid elliptic_order_eq_0_iff_const_cosparse by auto

lemma avoid': "elliptic_order f > 0 \<Longrightarrow> eventually (\<lambda>z. f z \<noteq> c) (at z)"
  using avoid eventually_cosparse_imp_eventually_at by blast

theorem sum_zeros_poles_in_lattice:
  fixes orig :: complex
  defines "Z \<equiv> {z\<in>period_parallelogram orig. isolated_zero f z \<or> is_pole f z}"
  shows   "(\<Sum>z\<in>Z. of_int (zorder f z) * z) \<in> \<Lambda>"
  using remove_sings.sum_zeros_poles_in_lattice_aux[of orig]
  by (simp add: Z_def)  

theorem sum_residues_eq_0:
  fixes orig :: complex
  defines "Q \<equiv> {z\<in>period_parallelogram orig. is_pole f z}"
  shows   "(\<Sum>z\<in>Q. residue f z) \<in> \<Lambda>"
  using remove_sings.sum_residues_eq_0_aux[of orig] by (simp add: Q_def)

text \<open>
  An obvious fact that we use at one point: if $\sum_{x\in A} f(x) = 1$ for 
  $f(x)$ in the positive integers, then $A = \{x\}$ for some $x$ and $f(x) = 1$.
\<close>
lemma (in -) sum_nat_eq_1E:
  fixes f :: "'a \<Rightarrow> nat"
  assumes sum_eq: "(\<Sum>x\<in>A. f x) = 1"
  assumes pos: "\<And>x. x \<in> A \<Longrightarrow> f x > 0"
  obtains x where "A = {x}" "f x = 1"
proof -
  have [simp, intro]: "finite A"
    by (rule ccontr) (use sum_eq in auto)
  have "A \<noteq> {}"
    using sum_eq by auto
  then obtain x where x: "x \<in> A"
    by auto
  have "(\<Sum>x\<in>A. f x) = f x + (\<Sum>x\<in>A-{x}. f x)"
    by (meson \<open>finite A\<close> \<open>x \<in> A\<close> sum.remove)
  hence "f x + (\<Sum>x\<in>A-{x}. f x) = 1"
    using sum_eq by simp
  with pos[OF x] have "f x = 1" "(\<Sum>x\<in>A-{x}. f x) = 0"
    by linarith+
  from this have "\<forall>y\<in> A - {x}. f y = 0"
    by (subst (asm) sum_eq_0_iff) auto
  with pos have "A - {x} = {}"
    by force
  with x have "A = {x}"
    by auto
  with \<open>f x = 1\<close> show ?thesis
    using that[of x] by blast
qed

text \<open>
  A simple consequence of our result about the sums of poles and zeros being a lattice point
  is that there are no elliptic functions of order 1.

  If there were such a function, it would have only one zero and one pole (both simple) in the
  fundamental parallelogram. Since their sum would be a lattice point, they would be equivalent 
  modulo the lattice and thus identical. But a point cannot be both a zero and a pole.
\<close>
theorem elliptic_order_neq_1: "elliptic_order f \<noteq> 1"
proof
  assume "elliptic_order f = 1"
  define P where "P = period_parallelogram 0"

  from \<open>elliptic_order f = 1\<close> have *: "(\<Sum>z | z \<in> P \<and> is_pole f z. nat (- zorder f z)) = 1"
    by (simp add: elliptic_order_def P_def)
  moreover have "zorder f z < 0" if "is_pole f z" for z using that meromorphic
    by (meson isolated_pole_imp_neg_zorder meromorphic_at_iff meromorphic_on_subset top_greatest)
  ultimately obtain pole where pole: "{z. z \<in> P \<and> is_pole f z} = {pole}" "zorder f pole = -1"
    by (elim sum_nat_eq_1E) auto

  from \<open>elliptic_order f = 1\<close> have *: "(\<Sum>z | z \<in> P \<and> isolated_zero f z. nat (zorder f z)) = 1"
    using zeros_eq_elliptic_order[of 0] by (simp add: P_def)
  moreover have "zorder f z > 0" if "isolated_zero f z" for z using that
    by (simp add: zorder_isolated_zero_pos')
  ultimately obtain zero where zero: "{z. z \<in> P \<and> isolated_zero f z} = {zero}" "zorder f zero = 1"
    by (elim sum_nat_eq_1E) auto

  have zero': "isolated_zero f zero" and pole': "is_pole f pole"
    using zero pole by blast+
  have "zero \<noteq> pole"
    using zero' pole' pole_is_not_zero by blast    

  have "(\<Sum>z | z \<in> P \<and> (isolated_zero f z \<or> is_pole f z). of_int (zorder f z) * z) \<in> \<Lambda>"
    unfolding P_def by (rule sum_zeros_poles_in_lattice)
  also have "{z. z \<in> P \<and> (isolated_zero f z \<or> is_pole f z)} = {zero, pole}"
    using zero pole by auto
  finally have "zero - pole \<in> \<Lambda>"
    using \<open>zero \<noteq> pole\<close> zero pole by simp
  hence "rel zero pole"
    by (simp add: rel_def)
  thus False
    using zero' pole' pole_is_not_zero poles.lattice_cong by blast
qed

end


locale nonconst_nicely_elliptic_function = nicely_elliptic_function +
  assumes order_pos: "elliptic_order f > 0"
begin

lemma isolated_zero_iff': "isolated_zero f z \<longleftrightarrow> \<not>is_pole f z \<and> f z = 0"
proof -
  have "f \<noteq> (\<lambda>_. 0)"
    using order_pos by auto
  thus ?thesis
    using isolated_zero_iff[of z] by simp
qed

end


subsection \<open>Even elliptic functions\<close>

text \<open>
  If an elliptic function is even, i.e.\ $f(-z) = f(z)$, it is invariant not only under the
  group generated by $z \mapsto z + \omega_1$ and $z\mapsto z + \omega_2$, but also the
  additional generator $z \mapsto -z$.

  Since our prototypical example of an elliptic function -- the Weierstra\ss\ \<open>\<wp>\<close> function --
  is even, we will examine these a bit more closely here.
\<close>
locale even_elliptic_function = elliptic_function +
  assumes even: "f (-z) = f z"
begin

text \<open>
  The Laurent series expansion of an even elliptic function at lattice points and half-lattice 
  points only has even-index coefficients. This also means that, at lattice and half-lattice points,
  an even elliptic function can only have zeros and poles of even order.
\<close>
lemma
  assumes z: "2 * z \<in> \<Lambda>" and "\<not>(\<forall>\<^sub>\<approx>z. f z = 0)"
  shows   odd_laurent_coeffs_eq_0: "odd n \<Longrightarrow> fls_nth (laurent_expansion f z) n = 0"
    and   even_zorder: "even (zorder f z)"
proof -
  define F where "F = laurent_expansion f z"
  have F: "(\<lambda>w. f (z + w)) has_laurent_expansion F"
    unfolding F_def  by (simp add: not_essential_has_laurent_expansion)
  have "F \<noteq> 0"
  proof
    assume "F = 0"
    with F have "eventually (\<lambda>w. f w = 0) (at z)"
      using has_laurent_expansion_eventually_zero_iff by blast
    thus False
      using assms(2) eventually_eq_imp_almost_everywhere_eq by blast
  qed

  have "((\<lambda>w. f (z + w)) \<circ> uminus) has_laurent_expansion (fls_compose_fps F (-fps_X))"
    by (intro laurent_expansion_intros F has_laurent_expansion_fps fps_expansion_intros) auto
  also have "((\<lambda>w. f (z + w)) \<circ> uminus) = (\<lambda>w. f (z + w))" (is "?lhs = ?rhs")
  proof
    fix w :: complex
    have "?lhs w = f (z - w)"
      by simp
    also have "\<dots> = f (-(z + w))"
      by (rule lattice_cong) (use assms z in \<open>auto simp: rel_def\<close>)
    also have "\<dots> = f (z + w)"
      by (rule even)
    finally show "?lhs w = ?rhs w" .
  qed
  finally have "(\<lambda>w. f (z + w)) has_laurent_expansion fls_compose_fps F (- fps_X)" .
  with F have "F = fls_compose_fps F (- fps_X)"
    using has_laurent_expansion_unique by blast
  thus even': "fls_nth F n = 0" if "odd n" for n
    using that fls_nth_fls_compose_fps_linear[of "-1" F n]
    by (auto simp: fls_eq_iff power_int_minus_left simp flip: fps_const_neg)

  have "fls_nth F (fls_subdegree F) \<noteq> 0"
    using \<open>F \<noteq> 0\<close> by auto
  with even' have "even (fls_subdegree F)"
    by blast
  also have "fls_subdegree F = zorder f z"
    using F \<open>F \<noteq> 0\<close> by (metis has_laurent_expansion_zorder)
  finally show "even (zorder f z)" .
qed

lemma lattice_cong': "rel w z \<or> rel w (-z) \<Longrightarrow> f w = f z"
  using even lattice_cong by metis

lemma eval_to_half_fund_parallelogram: "f (to_half_fund_parallelogram z) = f z"
  using rel_to_half_fund_parallelogram[of z] even lattice_cong by metis

lemma zorder_to_half_fund_parallelogram: "zorder f (to_half_fund_parallelogram z) = zorder f z"
proof -
  define z' where "z' = to_half_fund_parallelogram z"
  have "rel z z' \<or> rel z (-z')"
    unfolding z'_def by (rule rel_to_half_fund_parallelogram)
  hence "zorder f z = zorder f z'"
  proof
    assume "rel z z'"
    thus "zorder f z = zorder f z'"
      by (rule zorder.lattice_cong)
  next
    assume "rel z (-z')"
    hence "zorder f z = zorder f (-z')"
      by (rule zorder.lattice_cong)
    also have "\<dots> = zorder (\<lambda>z. f (-z)) z'"
      by (rule zorder_uminus [symmetric]) (auto intro!: meromorphic')
    also have "\<dots> = zorder f z'"
      by (simp add: even)
    finally show "zorder f z = zorder f z'" .
  qed
  thus ?thesis
    by (simp add: z'_def)
qed

lemma zorder_uminus: "zorder f (-z) = zorder f z"
  by (metis rel_refl to_half_fund_parallelogram_eq_iff zorder_to_half_fund_parallelogram)

end



subsection \<open>Closure properties of the class of elliptic functions\<close>

text \<open>
  Elliptic functions are closed under all basic arithmetic operations (addition, subtraction,
  multiplication, division). Additionally, they are closed under derivative, translation
  ($f(z) \rightsquigarrow f(z + c)$) and scaling with an integer ($f(z) \rightsquigarrow f(nz)$).

  Furthermore, constant functions are elliptic.
\<close>

lemma elliptic_function_unop:
  assumes "elliptic_function \<omega>1 \<omega>2 f"
  assumes "f meromorphic_on UNIV \<Longrightarrow> (\<lambda>z. h (f z)) meromorphic_on UNIV"
  shows   "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. h (f z))"
proof -
  interpret elliptic_function \<omega>1 \<omega>2 f by fact
  interpret complex_lattice_periodic_compose \<omega>1 \<omega>2 f h ..
  show ?thesis
    by standard (use assms(2) meromorphic in auto)
qed

lemma elliptic_function_binop:
  assumes "elliptic_function \<omega>1 \<omega>2 f" "elliptic_function \<omega>1 \<omega>2 g"
  assumes "f meromorphic_on UNIV \<Longrightarrow> g meromorphic_on UNIV \<Longrightarrow> (\<lambda>z. h (f z) (g z)) meromorphic_on UNIV"
  shows   "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. h (f z) (g z))"
proof -
  interpret f: elliptic_function \<omega>1 \<omega>2 f by fact
  interpret g: elliptic_function \<omega>1 \<omega>2 g by fact
  interpret complex_lattice_periodic \<omega>1 \<omega>2 "\<lambda>z. h (f z) (g z)"
    by standard (auto intro!: arg_cong2[of _ _ _ _ h] f.lattice_cong g.lattice_cong simp: f.rel_def)
  show ?thesis
    by standard (use assms(3) f.meromorphic g.meromorphic in auto)
qed


context complex_lattice
begin

named_theorems elliptic_function_intros

lemmas (in elliptic_function) [elliptic_function_intros] = elliptic_function_axioms

lemma elliptic_function_const [elliptic_function_intros]:
  "elliptic_function \<omega>1 \<omega>2 (\<lambda>_. c)"
  by standard auto

lemma [elliptic_function_intros]:
  assumes "elliptic_function \<omega>1 \<omega>2 f"
  shows   elliptic_function_cmult_left: "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. c * f z)"
    and   elliptic_function_cmult_right: "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. f z * c)"
    and   elliptic_function_scaleR: "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. c' *\<^sub>R f z)"
    and   elliptic_function_uminus: "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. -f z)"
    and   elliptic_function_inverse: "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. inverse (f z))"
    and   elliptic_function_power: "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. f z ^ m)"
    and   elliptic_function_power_int: "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. f z powi n)"
  by (rule elliptic_function_unop[OF assms(1)]; force intro!: meromorphic_intros)+

lemma [elliptic_function_intros]:
  assumes "elliptic_function \<omega>1 \<omega>2 f" "elliptic_function \<omega>1 \<omega>2 g"
  shows   elliptic_function_cmult_add: "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. f z + g z)"
    and   elliptic_function_cmult_diff: "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. f z - g z)"
    and   elliptic_function_cmult_mult: "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. f z * g z)"
    and   elliptic_function_cmult_divide: "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. f z / g z)"
  by (rule elliptic_function_binop[OF assms(1,2)]; force intro!: meromorphic_intros)+


lemma elliptic_function_compose_mult_of_int_left:
  assumes "elliptic_function \<omega>1 \<omega>2 f"
  shows   "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. f (of_int n * z))"
proof -
  interpret elliptic_function \<omega>1 \<omega>2 f
    by fact
  show ?thesis
    by unfold_locales
       (auto intro!: meromorphic_intros analytic_intros lattice_cong lattice_intros
             simp: rel_def uminus_in_lattice_iff ring_distribs)
qed

lemma elliptic_function_compose_mult_of_nat_left:
  assumes "elliptic_function \<omega>1 \<omega>2 f"
  shows   "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. f (of_nat n * z))"
  using elliptic_function_compose_mult_of_int_left[OF assms, of "int n"] by simp

lemma elliptic_function_compose_mult_numeral_left:
  assumes "elliptic_function \<omega>1 \<omega>2 f"
  shows   "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. f (numeral n * z))"
  using elliptic_function_compose_mult_of_int_left[OF assms, of "numeral n"] by simp

lemma
  assumes "elliptic_function \<omega>1 \<omega>2 f"
  shows   elliptic_function_compose_mult_of_int_right: "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. f (z * of_int n))"
    and   elliptic_function_compose_mult_of_nat_right: "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. f (z * of_nat m))"
    and   elliptic_function_compose_mult_numeral_right: "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. f (z * numeral num))"
  by (subst mult.commute, 
      rule elliptic_function_compose_mult_of_int_left 
           elliptic_function_compose_mult_of_nat_left 
           elliptic_function_compose_mult_numeral_left,
      rule assms)+

lemma elliptic_function_compose_uminus:
  assumes "elliptic_function \<omega>1 \<omega>2 f"
  shows   "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. f (-z))"
  using elliptic_function_compose_mult_of_int_left[OF assms, of "-1"] by simp

(* TODO: more lemmas? *)
lemma elliptic_function_shift:
  assumes "elliptic_function \<omega>1 \<omega>2 f"
  shows   "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. f (z + w))"
proof -
  interpret elliptic_function \<omega>1 \<omega>2 f by fact
  show ?thesis 
  proof
    show "(\<lambda>z. f (z + w)) meromorphic_on UNIV"
      using meromorphic by (rule meromorphic_on_compose) (auto intro!: analytic_intros)
  qed (auto intro!: lattice_cong simp: rel_def)    
qed

definition shift_fun :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a :: plus" where
  "shift_fun w f = (\<lambda>z. f (z + w))"

lemma elliptic_function_shift' [elliptic_function_intros]:
  assumes "elliptic_function \<omega>1 \<omega>2 f"
  shows   "elliptic_function \<omega>1 \<omega>2 (shift_fun w f)"
  unfolding shift_fun_def using assms by (rule elliptic_function_shift)


lemma nicely_elliptic_function_remove_sings [elliptic_function_intros]:
  assumes "elliptic_function \<omega>1 \<omega>2 f"
  shows   "nicely_elliptic_function \<omega>1 \<omega>2 (remove_sings f)"
proof -
  interpret elliptic_function \<omega>1 \<omega>2 f by fact
  interpret elliptic_function_remove_sings \<omega>1 \<omega>2 f ..
  show ?thesis ..
qed

lemma elliptic_function_remove_sings [elliptic_function_intros]:
  assumes "elliptic_function \<omega>1 \<omega>2 f"
  shows   "elliptic_function \<omega>1 \<omega>2 (remove_sings f)"
proof -
  interpret elliptic_function \<omega>1 \<omega>2 f by fact
  interpret elliptic_function_remove_sings \<omega>1 \<omega>2 f ..
  show ?thesis ..
qed

lemma elliptic_function_deriv [elliptic_function_intros]:
  assumes "elliptic_function \<omega>1 \<omega>2 f"
  shows   "elliptic_function \<omega>1 \<omega>2 (deriv f)"
proof -
  interpret elliptic_function \<omega>1 \<omega>2 f by fact
  show ?thesis by standard (auto intro!: meromorphic_intros meromorphic)
qed

lemma elliptic_function_higher_deriv [elliptic_function_intros]:
  assumes "elliptic_function \<omega>1 \<omega>2 f"
  shows   "elliptic_function \<omega>1 \<omega>2 ((deriv ^^ n) f)"
  using assms by (induction n) (auto intro!: elliptic_function_intros)

lemma elliptic_function_sum [elliptic_function_intros]:
  assumes "\<And>x. x \<in> X \<Longrightarrow> elliptic_function \<omega>1 \<omega>2 (f x)"
  shows   "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. \<Sum>x\<in>X. f x z)"
  using assms
  by (induction X rule: infinite_finite_induct) (auto intro!: elliptic_function_intros)

lemma elliptic_function_prod [elliptic_function_intros]:
  assumes "\<And>x. x \<in> X \<Longrightarrow> elliptic_function \<omega>1 \<omega>2 (f x)"
  shows   "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. \<Prod>x\<in>X. f x z)"
  using assms
  by (induction X rule: infinite_finite_induct) (auto intro!: elliptic_function_intros)

lemma elliptic_function_sum_list [elliptic_function_intros]:
  assumes "\<And>f. f \<in> set fs \<Longrightarrow> elliptic_function \<omega>1 \<omega>2 f"
  shows   "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. \<Sum>f\<leftarrow>fs. f z)"
  using assms by (induction fs) (auto intro!: elliptic_function_intros)

lemma elliptic_function_prod_list [elliptic_function_intros]:
  assumes "\<And>f. f \<in> set fs \<Longrightarrow> elliptic_function \<omega>1 \<omega>2 f"
  shows   "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. \<Prod>f\<leftarrow>fs. f z)"
  using assms by (induction fs) (auto intro!: elliptic_function_intros)

lemma elliptic_function_sum_mset [elliptic_function_intros]:
  assumes "\<And>f. f \<in># F \<Longrightarrow> elliptic_function \<omega>1 \<omega>2 f"
  shows   "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. \<Sum>f\<in>#F. f z)"
  using assms by (induction F) (auto intro!: elliptic_function_intros)

lemma elliptic_function_prod_mset [elliptic_function_intros]:
  assumes "\<And>f. f \<in># F \<Longrightarrow> elliptic_function \<omega>1 \<omega>2 f"
  shows   "elliptic_function \<omega>1 \<omega>2 (\<lambda>z. \<Prod>f\<in>#F. f z)"
  using assms by (induction F) (auto intro!: elliptic_function_intros)

end



subsection \<open>Affine transformations and surjectivity\<close>

text \<open>
  In the following we look at the properties of the elliptic function $a f(z) + b$, where
  $a\neq 0$. Obviously this function inherits many properties from $f(z)$.
\<close>

locale elliptic_function_affine = elliptic_function +
  fixes a b :: complex and g :: "complex \<Rightarrow> complex"
  defines "g \<equiv> \<lambda>z. a * f z + b"
  assumes nonzero_const: "a \<noteq> 0"
begin

sublocale affine: elliptic_function \<omega>1 \<omega>2 g
  unfolding g_def by (intro elliptic_function_intros elliptic_function_axioms)

lemma is_pole_affine_iff: "is_pole g z \<longleftrightarrow> is_pole f z"
  using nonzero_const by (simp add: g_def flip: is_pole_plus_const_iff)

lemma zorder_pole_affine:
  assumes "is_pole f z"
  shows   "zorder g z = zorder f z"
proof -
  note [simp] = nonzero_const
  have "zorder (\<lambda>z. a * f z + b) z = zorder (\<lambda>z. a * f z) z"
  proof (cases "b = 0")
    case [simp]: False
    show ?thesis
    proof (intro zorder_add1)
      from assms have "zorder (\<lambda>z. a * f z) z < 0"
        by (intro isolated_pole_imp_neg_zorder) (auto intro!: singularity_intros)
      thus "zorder (\<lambda>z. a * f z) z < zorder (\<lambda>z. b) z"
        by simp
    next
      have "elliptic_order f > 0"
        using assms elliptic_order_eq_0_iff_no_poles by blast
      hence "\<forall>\<^sub>F z in at z. a * f z \<noteq> 0"
        using avoid'[of 0 z] by auto
      thus "\<exists>\<^sub>F z in at z. a * f z \<noteq> 0"
        using at_neq_bot eventually_frequently by blast
    qed (use nonzero_const in \<open>auto intro!: meromorphic_intros meromorphic\<close>)
  qed auto
  also have "\<dots> = zorder f z"
    by (rule zorder_cmult) auto
  finally show ?thesis by (simp only: g_def)
qed

lemma order_affine_eq: "elliptic_order g = elliptic_order f"
  unfolding elliptic_order_def using nonzero_const
  by (intro sum.cong Collect_cong conj_cong refl)
     (auto simp flip: is_pole_plus_const_iff simp: zorder_pole_affine is_pole_affine_iff)

end


text \<open>
  One consequence of the above is that a non-constant elliptic function takes on each value in
  $\mathbb{C}$ ``equally often''. In particular, this means that any non-constant elliptic function 
  is surjective, i.e.\ for every $c\in\mathbb{C}$ there exists a preimage $z$ with $f(z)=c$ in
  every period parallelogram.
\<close>
context nonconst_nicely_elliptic_function
begin

theorem surj:
  fixes c :: complex
  obtains z where "\<not>is_pole f z" "z \<in> period_parallelogram w" "f z = c"
proof -
  define g where "g = (\<lambda>z. f z - c)"
  interpret elliptic_function_affine \<omega>1 \<omega>2 f 1 "-c" g
    by unfold_locales (auto simp: g_def)

  have "elliptic_order g > 0"
    using order_affine_eq order_pos by simp
  then obtain z where z: "isolated_zero g z"
    using affine.elliptic_order_eq_0_iff_no_zeros by auto
  moreover have "\<not>is_pole f z"
    using z pole_is_not_zero is_pole_affine_iff by blast
  hence "f analytic_on {z}"
    by (simp add: analytic_at_iff_not_pole)
  hence "g analytic_on {z}"
    by (auto simp: g_def intro!: analytic_intros)
  ultimately have g: "g z = 0"
    using zero_isolated_zero_analytic by auto

  obtain h where h: "bij_betw h (period_parallelogram z) (period_parallelogram w)" "\<And>z. rel (h z) z"
    by (rule bij_betw_period_parallelograms[of z w]) blast

  show ?thesis
  proof (rule that[of "h z"])
    show "\<not>is_pole f (h z)"
      using \<open>\<not>is_pole f z\<close> h(2)[of z] poles.lattice_cong by blast
  next
    show "h z \<in> period_parallelogram w"
      using h(1) by (auto simp: bij_betw_def)
  next
    show "f (h z) = c"
      using g h(2)[of z] unfolding g_def by (simp add: lattice_cong)
  qed
qed

end

end