(*<*)
section \<open>Auxiliary material\<close>
theory Modular_Forms_Library
imports
  "HOL-Complex_Analysis.Complex_Analysis"
  "Algebraic_Numbers.Bivariate_Polynomials"
  "Dirichlet_Series.Dirichlet_Series_Analysis"
  "Path_Automation.Path_Automation_Library"
begin

(* TODO: Move? *)
lemma continuous_within_poly2:
  fixes f g :: "'a :: t2_space \<Rightarrow> 'b :: {real_normed_field}"
  assumes [continuous_intros]: "continuous (at F within A) f" "continuous (at F within A) g"
  shows "continuous (at F within A) (\<lambda>x. poly2 p (f x) (g x))"
  by (induction p) (auto intro!: continuous_intros continuous_within_poly)

lemma map_poly2_0 [simp]: "map_poly2 f 0 = 0"
  by (simp add: map_poly2_def)

lemma map_poly2_pCons [simp]:
  "p \<noteq> 0 \<or> q \<noteq> 0 \<Longrightarrow> map_poly2 f (pCons p q) = pCons (map_poly f p) (map_poly2 f q)"
  by (simp add: map_poly2_def)

lemma map_poly2_compose: "f 0 = 0 \<Longrightarrow> map_poly2 (f \<circ> g) p = map_poly2 f (map_poly2 g p)"
  by (rule poly_eqI) (auto simp: map_poly2_def coeff_map_poly map_poly_map_poly)
(* END TODO *)


(* TODO: Move *)
lemma has_fps_expansion_poly [fps_expansion_intros]:
  fixes F :: "'a :: {banach, real_normed_div_algebra, comm_ring_1} fps"
  assumes "f has_fps_expansion F"
  shows   "(\<lambda>x. poly p (f x)) has_fps_expansion (poly (map_poly fps_const p) F)"
  by (induction p) (auto intro!: fps_expansion_intros assms)

(* TODO Move *)
lemma has_fps_expansion_poly2 [fps_expansion_intros]:
  fixes F G :: "'a :: {banach, real_normed_div_algebra, comm_ring_1} fps"
  assumes "f has_fps_expansion F" "g has_fps_expansion G"
  shows   "(\<lambda>x. poly2 p (f x) (g x)) has_fps_expansion (poly2 (map_poly2 fps_const p) F G)"
  by (induction p) (auto intro!: fps_expansion_intros assms simp: )

(* TODO Move *)
lemma fps_nth_numeral_pos [simp]: "n > 0 \<Longrightarrow> fps_nth (numeral m) n = 0"
  by (subst fps_numeral_nth) auto

(* TODO Move *)
lemma divisor_sigma_of_real: 
  "divisor_sigma (of_real s :: 'a :: nat_power_normed_field) n = of_real (divisor_sigma s n)"
  by (simp add: divisor_sigma_def)

(* TODO Move *)
lemma
  assumes "c \<in> \<real>"
  shows   Re_divisor_sigma_Reals [simp]: "Re (divisor_sigma c n) = divisor_sigma (Re c) n"
    and   Im_divisor_sigma_Reals [simp]: "Im (divisor_sigma c n) = 0"
  using assms by (auto elim!: Reals_cases simp: divisor_sigma_of_real)

(* TODO: Move *)
lemma has_laurent_expansion_imp_sums_complex:
  assumes f: "f analytic_on eball 0 r - {0}" "f has_laurent_expansion F"
  assumes z: "z \<in> eball 0 r - {0}"
  defines "n \<equiv> fls_subdegree F"
  shows   "(\<lambda>k. fls_nth F (int k + n) * z powi (int k + n)) sums f z"
proof -
  define F' where "F' = fls_base_factor_to_fps F"
  define f' where "f' = (\<lambda>z. if z = 0 then fps_nth F' 0 else f z * z powi - n)"
  have f': "f' has_fps_expansion F'"
    using has_fps_expansion_fls_base_factor_to_fps[OF f(2)] 
    by (simp add: F'_def n_def f'_def cong: if_cong)

  have ana: "f' analytic_on eball 0 r"
  proof -
    from f have "(\<lambda>z. f z * z powi -n) analytic_on eball 0 r - {0}"
      by (intro analytic_intros) auto
    hence "(\<lambda>z. f z * z powi -n) holomorphic_on eball 0 r - {0}"
      by (subst (asm) analytic_on_open) auto
    also have "?this \<longleftrightarrow> f' holomorphic_on eball 0 r - {0}"
      by (intro holomorphic_cong) (auto simp: f'_def)
    finally have "f' analytic_on eball 0 r - {0}"
      by (subst analytic_on_open) auto
    moreover have "f' analytic_on {0}"
      using f' by (simp add: has_fps_expansion_imp_analytic_0)
    ultimately have "f' analytic_on (eball 0 r - {0} \<union> {0})"
      by (subst analytic_on_Un) auto
    moreover have "eball 0 r \<subseteq> eball 0 r - {0} \<union> {0}"
      by blast
    ultimately show ?thesis
      using analytic_on_subset by blast
  qed

  have "(\<lambda>n. fps_nth F' n * z ^ n) sums f' z"
    by (rule has_fps_expansion_imp_sums_complex[where r = r])
       (use f' ana z in \<open>auto dest: analytic_imp_holomorphic\<close>)
  hence "(\<lambda>k. z powi n * (fps_nth F' k * z ^ k)) sums (z powi n * f' z)"
    by (intro sums_mult)
  also have "z powi n * f' z = f z"
    using z by (auto simp: f'_def power_int_minus)
  also have "(\<lambda>k. z powi n * (fps_nth F' k * z ^ k)) =
             (\<lambda>k. fls_nth F (int k + n) * z powi (int k + n))"
    using z by (simp add: F'_def n_def mult_ac power_int_add)
  finally show ?thesis .
qed

(* TODO Move *)
lemma is_pole_plus_analytic_iff1:
  assumes "g analytic_on {x}"
  shows   "is_pole (\<lambda>x. f x + g x) x \<longleftrightarrow> is_pole f x"
proof -
  have 1: "is_pole (\<lambda>x. f x + g x) x" if "is_pole f x" "g analytic_on {x}" for f g
    unfolding is_pole_def
  proof (rule tendsto_add_filterlim_at_infinity')
    show "g \<midarrow>x\<rightarrow> g x"
      by (intro isContD analytic_at_imp_isCont that(2))
  qed (use that(1) in \<open>simp add: is_pole_def\<close>)
  show ?thesis
  proof
    assume 2: "is_pole (\<lambda>x. f x + g x) x"
    have "is_pole (\<lambda>x. f x + g x + (-g x)) x"
      using 2 by (rule 1) (auto intro!: analytic_intros assms)
    thus "is_pole f x"
      by simp
  qed (auto intro!: 1 assms)
qed

lemma is_pole_plus_analytic_iff2:
  assumes "f analytic_on {x}"
  shows   "is_pole (\<lambda>x. f x + g x) x \<longleftrightarrow> is_pole g x"
  by (subst add.commute, rule is_pole_plus_analytic_iff1) fact


lemma meromorphic_on_imp_has_laurent_expansion0:
  assumes "f meromorphic_on A" "0 \<in> A"
  shows   "f has_laurent_expansion laurent_expansion f 0"
  using meromorphic_on_imp_has_laurent_expansion[OF assms] by simp

lemma filterlim_at_infinity_iff_eventually_norm_ge:
  "filterlim f at_infinity F \<longleftrightarrow> (\<forall>c. eventually (\<lambda>x. norm (f x) \<ge> c) F)"
  unfolding at_infinity_altdef going_to_within_def 
  by (simp add: filterlim_filtercomap_iff o_def filterlim_at_top)

lemma filterlim_at_infinity_iff_eventually_norm_gt:
  "filterlim f at_infinity F \<longleftrightarrow> (\<forall>c. eventually (\<lambda>x. norm (f x) > c) F)"
  unfolding at_infinity_altdef going_to_within_def 
  by (simp add: filterlim_filtercomap_iff o_def filterlim_at_top_dense)

lemma is_pole_power_iff:
  assumes "f meromorphic_on {z}"
  shows   "is_pole (\<lambda>z. f z ^ n) z \<longleftrightarrow> is_pole f z \<and> n > 0"
proof -
  from assms obtain F where F: "(\<lambda>w. f (z + w)) has_laurent_expansion F"
    by (auto simp: meromorphic_on_def)
  have "(\<lambda>w. f (z + w) ^ n) has_laurent_expansion F ^ n"
    by (intro laurent_expansion_intros F)
  hence "is_pole (\<lambda>z. f z ^ n) z \<longleftrightarrow> fls_subdegree (F ^ n) < 0"
    using is_pole_fls_subdegree_iff by simp
  also have "fls_subdegree (F ^ n) = n * fls_subdegree F"
    by (cases "F = 0") (auto simp: power_0_left fls_subdegree_pow)
  also have "int n * fls_subdegree F < 0 \<longleftrightarrow> fls_subdegree F < 0 \<and> n > 0"
    by (metis mult_less_0_iff of_nat_0_less_iff of_nat_less_0_iff)
  also have "fls_subdegree F < 0 \<longleftrightarrow> is_pole f z"
    using F is_pole_fls_subdegree_iff by simp
  finally show ?thesis .
qed

lemma (in field_hom) power_int_distrib [hom_distribs]: "hom (x powi n) = hom x powi n"
  by (auto simp: power_int_def hom_distribs)

lemma is_pole_deriv_iff:
  assumes "isolated_singularity_at f x" "not_essential f x"
  shows   "is_pole (deriv f) x \<longleftrightarrow> is_pole f x"
  using assms
  by (meson is_pole_def is_pole_deriv not_essential_def not_tendsto_and_filterlim_at_infinity 
        removable_singularity_deriv trivial_limit_at)

(* TODO: Move? *)
lemma (in -) filtermap_power_nhds_complex:
  assumes k: "k > 0"
  shows   "filtermap (\<lambda>q. q ^ k) (nhds x) = nhds (x ^ k :: complex)"
proof (rule filtermap_nhds_open_map)
  show "isCont (\<lambda>q. q ^ k :: complex) x"
    by (intro continuous_intros)
next
  show "open ((\<lambda>q. q ^ k) ` S :: complex set)" if "open S" for S
  proof (rule open_mapping_thm)
    show "(\<lambda>q. q ^ k) holomorphic_on UNIV"
      by (rule holomorphic_intros) auto
    show "\<not>(\<lambda>q. q ^ k :: complex) constant_on UNIV"
    proof
      assume "(\<lambda>q. q ^ k :: complex) constant_on UNIV"
      then obtain c where c: "\<And>q. q ^ k = (c::complex)"
        by (auto simp: constant_on_def)
      from c[of 0] c[of 1] show False
        using k by (simp add: zero_power)
    qed
  qed (use \<open>open S\<close> in auto)
qed

(* TODO: Move? *)
lemma (in -) filtermap_power_at_0_complex:
  assumes k: "k > 0"
  shows   "filtermap (\<lambda>q. q ^ k) (at 0) = at (0 :: complex)"
proof -
  have "filtermap (\<lambda>q. q ^ k) (at 0) = at (0 ^ k :: complex)"
  proof (rule filtermap_nhds_eq_imp_filtermap_at_eq)
    show "filtermap (\<lambda>q. q ^ k) (nhds 0) = nhds (0 ^ k :: complex)"
      using filtermap_power_nhds_complex[of k 0] k by (simp add: zero_power)
  next
    show "\<forall>\<^sub>F x in at 0. x ^ k = 0 ^ k \<longrightarrow> x = (0::complex)"
      using k by (auto simp: zero_power)
  qed
  thus ?thesis
    using k by (simp add: zero_power)
qed

lemma meromorphic_at_cong:
  assumes "\<forall>\<^sub>F w in at z. f w = g w" "z = z'"
  shows   "(f meromorphic_on {z}) = (g meromorphic_on {z'})"
  by (rule meromorphic_on_cong) (use assms in auto)

(* TODO Move *)
lemma not_isolated_zero_const [simp]: "\<not>isolated_zero (\<lambda>_::'a::real_normed_field. c) z"
  unfolding isolated_zero_def by (cases "c = 0") (auto simp: tendsto_const_iff)

(* TODO Move *)
lemma has_laurent_expansion_imp_bigtheta:
  assumes F: "f has_laurent_expansion F" "F \<noteq> 0"
  defines "n \<equiv> fls_subdegree F"
  shows   "f \<in> \<Theta>[at 0](\<lambda>z. z powi n)"
proof -
  have "f \<sim>[at 0] (\<lambda>z. fls_nth F n * z powi n)"
    unfolding n_def by (rule has_laurent_expansion_imp_asymp_equiv_0) fact+
  hence "f \<in> \<Theta>[at 0](\<lambda>z. fls_nth F n * z powi n)"
    by (rule asymp_equiv_imp_bigtheta)
  also have "(\<lambda>z. fls_nth F n * z powi n) \<in> \<Theta>[at 0](\<lambda>z. z powi n)"
    using \<open>F \<noteq> 0\<close> by (auto simp: n_def)
  finally show ?thesis .
qed

lemma ln_less_iff: "x > 0 \<Longrightarrow> ln x < (y :: real) \<longleftrightarrow> x < exp y"
  by (metis exp_less_cancel_iff exp_ln)

lemma zorder_0_eq': "zorder (\<lambda>_. 0) x = zorder (\<lambda>_. 0) 0"
  by (rule zorder_shift)

lemma moebius_meromorphic [meromorphic_intros]:
  assumes "f meromorphic_on A" "a meromorphic_on A" "b meromorphic_on A" 
          "c meromorphic_on A" "d meromorphic_on A"
  shows   "(\<lambda>z. moebius (a z) (b z) (c z) (d z) (f z)) meromorphic_on A"
  unfolding moebius_def
  by (intro meromorphic_intros assms )    


(* TODO Move *)
lemma ln_cis: "x \<in> {-pi<..pi} \<Longrightarrow> ln (cis x) = \<i> * x"
  by (simp add: Ln_Arg Arg_cis)

(* TODO Move *)
lemma tendsto_arcsin [tendsto_intros]:
  assumes "(f \<longlongrightarrow> L) F" "L \<in> {-1..1}" "L \<in> {-1<..<1} \<or> (\<forall>\<^sub>F x in F. f x \<in> {- 1..1})"
  shows   "((\<lambda>x. arcsin (f x)) \<longlongrightarrow> arcsin L) F"
proof -
  have *: "\<forall>\<^sub>F x in F. f x \<in> {-1..1}"
    using assms(3)
  proof
    assume "L \<in> {-1<..<1}"
    hence "eventually (\<lambda>x. x \<in> {-1<..<1}) (nhds L)"
      by (intro eventually_nhds_in_open) auto
    moreover have "nhds L \<ge> filtermap f F"
      using assms(1) by (simp add: filterlim_def)
    ultimately have "eventually (\<lambda>x. x \<in> {-1<..<1}) (filtermap f F)"
      using filter_leD by blast
    thus "eventually (\<lambda>x. f x \<in> {-1..1}) F"
      unfolding eventually_filtermap by eventually_elim auto
  qed     
  show ?thesis
    using continuous_on_tendsto_compose [OF continuous_on_arcsin' assms(1,2) *] .
qed  

(* TODO Move *)
lemma tendsto_arccos [tendsto_intros]:
  assumes "(f \<longlongrightarrow> L) F" "L \<in> {-1..1}" "L \<in> {-1<..<1} \<or> (\<forall>\<^sub>F x in F. f x \<in> {- 1..1})"
  shows   "((\<lambda>x. arccos (f x)) \<longlongrightarrow> arccos L) F"
proof -
  have *: "\<forall>\<^sub>F x in F. f x \<in> {-1..1}"
    using assms(3)
  proof
    assume "L \<in> {-1<..<1}"
    hence "eventually (\<lambda>x. x \<in> {-1<..<1}) (nhds L)"
      by (intro eventually_nhds_in_open) auto
    moreover have "nhds L \<ge> filtermap f F"
      using assms(1) by (simp add: filterlim_def)
    ultimately have "eventually (\<lambda>x. x \<in> {-1<..<1}) (filtermap f F)"
      using filter_leD by blast
    thus "eventually (\<lambda>x. f x \<in> {-1..1}) F"
      unfolding eventually_filtermap by eventually_elim auto
  qed     
  show ?thesis
    using continuous_on_tendsto_compose [OF continuous_on_arccos' assms(1,2) *] .
qed

lemma minus_part_circlepath:
  "-part_circlepath x r a b t = part_circlepath (-x) r (a + pi) (b + pi) t"
  by (simp add: part_circlepath_altdef rcis_def add.commute[of _ pi]
           flip: linepath_translate cis_mult)



(* TODO: move? *)
lemma convex_real_less: "convex {(x,y::real). x < y}"
proof -
  have "(1 - u) * a + u * aa < (1 - u) * b + u * ba" if "a < b" "aa < ba" "0 \<le> u" "u \<le> 1"
    for a b aa ba u :: real
  proof -
    have "0 < (1 - u) * (b - a) + u * (ba - aa)"
    proof (cases "u = 1")
      case False
      thus ?thesis
        using that by (intro add_pos_nonneg mult_pos_pos mult_nonneg_nonneg) auto
    next
      case True
      thus ?thesis
        using that by (intro add_nonneg_pos mult_pos_pos mult_nonneg_nonneg) auto
    qed
    thus ?thesis
      by (simp add: algebra_simps)
  qed
  thus ?thesis
    by (auto simp: convex_alt)
qed

(* TODO move *)
text \<open>
  The following lemma is intuitively obvious, but can be a bit painful to prove: if a 
  real function is continuous and injective, then it is either strictly increasing or
  strictly decreasing.

  We follow a very simple argument by Michael Hoppe from the Math StackExchange website:
  \<^url>\<open>https://math.stackexchange.com/q/1237172\<close>

  If \<open>f : A \<rightarrow> \<real>\<close> is our continuous injective function, we define \<open>g(x,y) = g(x) - g(y)\<close> on the 
  domain \<open>S = {(x,y) | x < y} \<inter> A\<times>A\<close>. Clearly, \<open>g\<close> is continuous on \<open>S\<close> and \<open>S\<close> is convex and
  thus also connected. Then \<open>g(S)\<close> is also connected. Moreover \<open>g(s)\<close> does not include 0.
  Thus all values of \<open>g(s)\<close> are positive or all of them are negative.
\<close>

lemma continuous_inj_on_real_imp_strict_mono_on:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "continuous_on A f" "inj_on f A" and "convex A"
  shows   "strict_mono_on A f \<or> strict_mono_on A (\<lambda>x. -f x)"
proof -
  note [continuous_intros] = continuous_on_compose2[OF f(1)]
  define S where "S = A \<times> A \<inter> {(x,y). x < y}"
  define g where "g = (\<lambda>(x,y). f x - f y)"
  have g: "continuous_on S g"
    unfolding g_def S_def case_prod_unfold by (intro continuous_intros) auto
  hence "convex S"
    unfolding S_def by (intro convex_Int convex_Times assms convex_real_less)
  hence "connected S"
    by (rule convex_connected)
  hence "connected (g ` S)"
    by (intro connected_continuous_image g)
  hence "is_interval (g ` S)"
    using is_interval_connected_1 by blast
  moreover have "0 \<notin> g ` S"
    using assms by (force simp: S_def g_def inj_on_def)
  ultimately have "(\<forall>x\<in>g`S. x < 0) \<or> (\<forall>x\<in>g`S. x > 0)"
    unfolding is_interval_1 by (meson not_le)
  thus ?thesis
    by (auto simp: strict_mono_on_def g_def S_def split: prod.splits)
qed

(* TODO move *)
lemma continuous_inj_on_real_imp_strict_mono:
  fixes f :: "real \<Rightarrow> real"
  assumes f: "continuous_on UNIV f" "inj f"
  shows   "strict_mono f \<or> strict_mono (\<lambda>x. -f x)"
  by (simp add: assms continuous_inj_on_real_imp_strict_mono_on)

end
(*>*)