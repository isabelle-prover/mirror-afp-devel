section \<open>Eisenstein series and the differential equations of \<open>\<wp>\<close>\<close>
theory Eisenstein_Series
imports
  Weierstrass_Elliptic
  Z_Plane_Q_Disc
  "Polynomial_Factorization.Fundamental_Theorem_Algebra_Factorized"
  "Zeta_Function.Zeta_Function"
  "Polylog.Polylog"
  "Lambert_Series.Lambert_Series"
  "Cotangent_PFD_Formula.Cotangent_PFD_Formula"
  "Algebraic_Numbers.Bivariate_Polynomials"
begin


(* TODO Move. Or rather, fix whatever causes these problems. *)
lemmas [simp del] = div_mult_self1 div_mult_self2 div_mult_self3 div_mult_self4


text \<open>
  We define the Eisenstein series $G_n$, which is the sequence of coefficients of the
  Laurent series expansion of \<open>\<wp>\<close>. Both \<open>\<wp>\<close> and $G_n$ (for $n\geq 3$) are invariants of the 
  lattice, i.e.\ they are independent from the choice of generators.
\<close>

subsection \<open>Definition\<close>

text \<open>
  For $n\geq 3$, the Eisenstein series $G_n$ is defined simply as the absolutely convergent sum
  $\sum_{\omega\in\Lambda^*} \omega^{-n}$. However, we want to stay as general as possible here
  and therefore define it in such a way that the definition also works for $n = 2$, where the
  sum is only conditionally convergent and much less well-behaved.

  Note that all the Eisenstein series with odd $n \geq 3$ vanish due to the symmetry in the
  sum. As for $n < 3$, we define $G_1 = 0$ in agreement with the the values for other odd $n$
  and $G_0 = 1$ since this makes some later theorem statements regarding modular forms more 
  elegant.
\<close>

context complex_lattice
begin

definition eisenstein_series :: "nat \<Rightarrow> complex" where
  "eisenstein_series k = (if k = 0 then 1 else if odd k then 0 else
      2 / \<omega>1 ^ k * zeta (of_nat k) + (\<Sum>\<^sub>\<infinity>n\<in>-{0}. \<Sum>\<^sub>\<infinity>m. 1 / of_\<omega>12_coords (of_int m, of_int n) ^ k))"

notation eisenstein_series ("G")

lemma eisenstein_series_0 [simp]: "eisenstein_series 0 = 1"
  by (auto simp: eisenstein_series_def)

lemma eisenstein_series_odd_eq_0 [simp]: "odd k \<Longrightarrow> eisenstein_series k = 0"
  by (auto simp: eisenstein_series_def elim!: oddE)

lemma eisenstein_series_Suc_0 [simp]: "eisenstein_series (Suc 0) = 0"
  by (rule eisenstein_series_odd_eq_0) auto

lemma eisenstein_series_norm_summable:
  assumes "n \<ge> 3"
  shows   "(\<lambda>\<omega>. 1 / norm \<omega> ^ n) summable_on \<Lambda>\<^sup>*"
  using converges_absolutely_iff[of "of_nat n"] assms by (simp add: powr_realpow')

lemma eisenstein_series_summable:
  assumes "n \<ge> 3"
  shows   "(\<lambda>\<omega>. 1 / \<omega> ^ n) summable_on \<Lambda>\<^sup>*"
  by (rule abs_summable_summable)
     (use eisenstein_series_norm_summable[OF assms] in \<open>simp add: norm_divide norm_power\<close>)

lemma eisenstein_series_has_sum:
  assumes "k \<ge> 3"
  shows   "((\<lambda>\<omega>. 1 / \<omega> ^ k) has_sum eisenstein_series k) \<Lambda>\<^sup>*"
proof (cases "even k")
  case odd: False
  define S where "S = (\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>\<^sup>*. 1 / \<omega> ^ k)"
  have sum1: "((\<lambda>\<omega>. 1 / \<omega> ^ k) has_sum S) \<Lambda>\<^sup>*"
    using eisenstein_series_summable[OF assms] has_sum_infsum unfolding S_def by blast
  also have "?this \<longleftrightarrow> ((\<lambda>\<omega>. -(1 / \<omega> ^ k)) has_sum S) \<Lambda>\<^sup>*"
    using assms odd
    by (intro has_sum_reindex_bij_witness[of _ uminus uminus]) (auto simp: uminus_in_lattice0_iff)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>\<omega>. 1 / \<omega> ^ k) has_sum (-S)) \<Lambda>\<^sup>*"
    by (rule has_sum_uminus)
  finally have "-S = S"
    using sum1 has_sum_unique by blast
  hence "S = 0"
    by simp
  thus ?thesis
    using sum1 odd assms by simp
next
  case even: True
  define f where "f = (\<lambda>(m,n). 1 / of_\<omega>12_coords (of_int m, of_int n) ^ k)"

  note k = \<open>k \<ge> 3\<close> even
  have "((\<lambda>m. 1 / of_int m ^ k) has_sum (2 * zeta (of_nat k))) (-{0})"
    by (rule has_sum_zeta_symmetric) (use k in auto)
  hence "((\<lambda>m. (1 / \<omega>1 ^ k) * (1 / of_int m ^ k)) 
           has_sum ((1 / \<omega>1 ^ k) * (2 * zeta (of_nat k)))) (-{0})"
    by (rule has_sum_cmult_right)
  hence "((\<lambda>m. 1 / (of_int m * \<omega>1) ^ k) has_sum (2 / \<omega>1 ^ k * zeta (of_nat k))) (-{0})"
    by (simp add: field_simps)
  also have "?this \<longleftrightarrow> (f has_sum (2 / \<omega>1 ^ k * zeta (of_nat k))) ((-{0}) \<times> {0})"
    by (rule has_sum_reindex_bij_witness[of _ fst "\<lambda>m. (m, 0)"]) (auto simp: f_def)
  finally have sum1: "(f has_sum (2 / \<omega>1 ^ k * zeta (of_nat k))) ((-{0}) \<times> {0})" .

  define S where "S = (\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>\<^sup>*. 1 / \<omega> ^ k)"
  define T where "T = (\<lambda>n. \<Sum>\<^sub>\<infinity>m. 1 / of_\<omega>12_coords (of_int m, of_int n) ^ k)"

  have sum2: "((\<lambda>\<omega>. 1 / \<omega> ^ k) has_sum S) \<Lambda>\<^sup>*"
    unfolding S_def using eisenstein_series_summable by (rule has_sum_infsum) (use k in auto)
  also have "?this \<longleftrightarrow> (f has_sum S) (-{(0,0)})"
    by (subst has_sum_reindex_bij_betw[OF bij_betw_lattice0', symmetric])
       (simp_all add: case_prod_unfold map_prod_def f_def)
  finally have "(f has_sum S) (- {(0, 0)})" .
  hence "(f has_sum (S - 2 / \<omega>1 ^ k * zeta (of_nat k))) (-{(0, 0)} - ((-{0}) \<times> {0}))"
    by (intro has_sum_Diff sum1) auto
  also have "-{(0, 0)} - ((-{0}) \<times> {0}) = (UNIV \<times> (-{0}) :: (int \<times> int) set)"
    by auto
  finally have "(f has_sum S - 2 / \<omega>1 ^ k * zeta (of_nat k)) (UNIV \<times> (-{0}))" .
  also have "?this \<longleftrightarrow> ((\<lambda>(n,m). f (m,n)) has_sum S - 2 / \<omega>1 ^ k * zeta (of_nat k)) ((-{0}) \<times> UNIV)"
    by (rule has_sum_reindex_bij_witness[of _ prod.swap prod.swap]) auto
  finally have sum3: "((\<lambda>(n,m). f (m,n)) has_sum S - 2 / \<omega>1 ^ k * zeta (of_nat k)) ((-{0}) \<times> UNIV)" .

  have "(T has_sum S - 2 / \<omega>1 ^ k * zeta (complex_of_nat k)) (-{0})"
    using sum3
  proof (rule has_sum_SigmaD, unfold prod.case)
    fix n :: int assume n: "n \<in> -{0}"
    have "(\<lambda>m. f (m, n)) summable_on UNIV"
      using summable_on_SigmaD1[OF has_sum_imp_summable[OF sum3, unfolded f_def], OF n]
      by (simp add: f_def)
    thus "((\<lambda>m. f (m, n)) has_sum T n) UNIV"
      unfolding T_def f_def prod.case by (rule has_sum_infsum)
  qed
  hence "S = 2 / \<omega>1 ^ k * zeta (of_nat k) + (\<Sum>\<^sub>\<infinity>m\<in>-{0}. T m)"
    by (simp add: has_sum_iff)
  also have "\<dots> = eisenstein_series k"
    using k by (simp add: eisenstein_series_def T_def)
  finally show ?thesis
    using sum2 by simp
qed

lemma eisenstein_series_altdef:
  assumes "k \<ge> 3"
  shows   "eisenstein_series k = (\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>\<^sup>*. 1 / \<omega> ^ k)"
  using eisenstein_series_has_sum[OF assms] by (simp add: has_sum_iff)

lemma eisenstein_fun_aux_0 [simp]:
  assumes "n \<noteq> 2"
  shows   "eisenstein_fun_aux n 0 = eisenstein_series n"
proof (cases "n \<ge> 3")
  case gt3: True
  show ?thesis
  proof (cases "even n")
    case True
    show ?thesis
      using True gt3 by (auto simp: eisenstein_fun_aux_def eisenstein_series_altdef)
  next
    case False
    have "eisenstein_fun_aux n 0 = -(\<Sum>\<^sub>\<infinity>\<omega>\<in>\<Lambda>\<^sup>*. 1 / \<omega> ^ n)"
      using False gt3
      by (auto simp: eisenstein_fun_aux_def eisenstein_series_def infsum_uminus)
    also have "\<dots> = -eisenstein_series n"
      using gt3 by (simp add: eisenstein_series_altdef)
    finally show ?thesis
      using False by (simp add: eisenstein_series_odd_eq_0)
  qed
next
  case False
  hence "n \<in> {0,1,2}"
    by auto
  thus ?thesis using assms
    by (auto simp: eisenstein_fun_aux_def)
qed


subsection \<open>The Laurent series expansion of \<open>\<wp>\<close> at the origin\<close>

lemma higher_deriv_weierstrass_fun_aux_0:
  assumes "m > 0"
  shows   "(deriv ^^ m) weierstrass_fun_aux 0 = (- 1) ^ m * fact (Suc m) * G (m + 2)"
proof -
  define n where "n = m - 1"
  have "(deriv ^^ Suc n) weierstrass_fun_aux 0 = (deriv ^^ n) (\<lambda>w. -2 * eisenstein_fun_aux 3 w) 0"
    unfolding funpow_Suc_right o_def
  proof (rule higher_deriv_cong_ev)
    have "eventually (\<lambda>z. z \<in> -\<Lambda>\<^sup>*) (nhds 0)"
      using closed_lattice0 by (intro eventually_nhds_in_open) auto
    thus "\<forall>\<^sub>F x in nhds 0. deriv weierstrass_fun_aux x = -2 * eisenstein_fun_aux 3 x"
      by eventually_elim (simp add: deriv_weierstrass_fun_aux)
  qed auto
  also have "\<dots> = -2 * (deriv ^^ n) (eisenstein_fun_aux 3) 0"
    using closed_lattice0  
    by (intro higher_deriv_cmult[where A = "-\<Lambda>\<^sup>*"]) (auto intro!: holomorphic_intros)
  also have "\<dots> = (- 1) ^ Suc n * fact (n + 2) * G (n + 3)"
    by (subst higher_deriv_eisenstein_fun_aux)
       (auto simp: algebra_simps pochhammer_rec pochhammer_fact)
  finally show ?thesis
    using assms by (simp add: n_def)
qed


(* Theorem 1.11 *)
text \<open>
  We now show that the Laurent series expansion of $\wp(z)$ at $z = 0$ has the form
  \[z^{-2} + \sum_{n\geq 1} (n+1) G_{n+2} z^n\ .\] 

  We choose a different approach to prove this than Apostol: Apostol converts the
  sum in question into a double sum and then interchanges the order of summation, claiming the
  double sum to be absolutely convergent. Since we were unable to see why that sum should be
  absolutely convergent, we were unable to replicate his argument. In any case, arguing about
  absolute convergence of double sums is always messy.

  Our approach instead simply uses the fact that \<^const>\<open>weierstrass_fun_aux\<close> (the Weierstrass
  function with its double pole removed) is analytic at 0 and thus has a power series expansion
  that is valid within any ball around 0 that does not contain any lattice points.

  The coefficients of this power series expansion can be determined simply by taking the \<open>n\<close>-th
  derivative of \<^const>\<open>weierstrass_fun_aux\<close> at 0, which is easy to do.

  Note that this series converges absolutely in this domain, since it is a power series, but
  we do not show this here.
\<close>
definition fps_weierstrass :: "complex fps"
  where "fps_weierstrass = Abs_fps (\<lambda>n. if n = 0 then 0 else of_nat (Suc n) * G (n + 2))"

lemma weierstrass_fun_aux_fps_expansion: "weierstrass_fun_aux has_fps_expansion fps_weierstrass"
proof -
  define c where "c = (\<lambda>n. if n = 0 then 0 else of_nat (Suc n) * G (n + 2))"
  have "(\<lambda>n. (deriv ^^ n) weierstrass_fun_aux 0 / fact n) = c"
          (is "?lhs = ?rhs")
  proof
    fix n :: nat
    show "?lhs n = ?rhs n" unfolding c_def
      by (cases "even n") (auto simp: higher_deriv_weierstrass_fun_aux_0 eisenstein_series_odd_eq_0)
  qed
  hence "fps_weierstrass = fps_expansion weierstrass_fun_aux 0"
    by (intro fps_ext) (auto simp: fps_expansion_def fps_weierstrass_def c_def fun_eq_iff)
  also have "weierstrass_fun_aux has_fps_expansion \<dots>"
    using closed_lattice0
    by (intro has_fps_expansion_fps_expansion[of "-\<Lambda>\<^sup>*"] holomorphic_intros) auto
  finally show ?thesis .
qed


definition fls_weierstrass :: "complex fls"
  where "fls_weierstrass = fls_X_intpow (-2) + fps_to_fls fps_weierstrass"

lemma fls_subdegree_weierstrass: "fls_subdegree fls_weierstrass = -2"
  by (intro fls_subdegree_eqI) (auto simp: fls_weierstrass_def)

lemma fls_weierstrass_nz [simp]: "fls_weierstrass \<noteq> 0"
  using fls_subdegree_weierstrass by auto

text \<open>
  The following corresponds to Theorem~1.11 in Apostol's book.
\<close>
theorem fls_weierstrass_laurent_expansion [laurent_expansion_intros]:
  "\<wp> has_laurent_expansion fls_weierstrass"
proof -
  have "(\<lambda>z. z powi (-2) + weierstrass_fun_aux z) has_laurent_expansion fls_weierstrass"
    unfolding fls_weierstrass_def
    by (intro laurent_expansion_intros has_laurent_expansion_fps[OF weierstrass_fun_aux_fps_expansion])
  also have "?this \<longleftrightarrow> ?thesis"
  proof (intro has_laurent_expansion_cong refl)
    have "eventually (\<lambda>z. z \<in> -\<Lambda>\<^sup>* - {0}) (at 0)"
      using closed_lattice0 by (intro eventually_at_in_open) auto
    thus "\<forall>\<^sub>F x in at 0. x powi - 2 + weierstrass_fun_aux x = \<wp> x"
      by eventually_elim
         (auto simp: weierstrass_fun_def power_int_minus field_simps lattice_lattice0)
  qed
  finally show ?thesis .
qed

corollary fls_weierstrass_deriv_laurent_expansion [laurent_expansion_intros]:
  "\<wp>' has_laurent_expansion fls_deriv fls_weierstrass"
  by (rule has_laurent_expansion_deriv'[where A = "-\<Lambda>\<^sup>*", OF fls_weierstrass_laurent_expansion])
     (use closed_lattice0 in \<open>auto intro!: derivative_eq_intros simp: lattice_lattice0\<close>)

lemma fls_nth_weierstrass:
  "fls_nth fls_weierstrass n =
     (if n = -2 then 1 else if n > 0 then of_int (n + 1) * G (nat n + 2) else 0)"
  unfolding fls_weierstrass_def fps_weierstrass_def by (auto simp: not_less)


subsection \<open>Differential equations for \<open>\<wp>\<close>\<close>

(* Apostol's Theorem 1.12 *)
text \<open>
  Using our results on elliptic functions, we can prove the important result that \<open>\<wp>\<close> satisfies
  the ordinary differential equation \[\wp'^2 = 4 \wp^3 - 60 G_4 \wp - 140 G_6\ .\]
  The proof works by simply subtracting the two sides and then looking at the Laurent series 
  expansion, noting that the poles all cancel out. This means that what remains is an elliptic
  functions without poles and therefore constant.

  The constant can then easily be determined, since it is the $0$-th coefficient of said Laurent
  series.

  This is Theorem~1.12 in Apostol's book.
\<close>
theorem weierstrass_fun_ODE1:
  assumes "z \<notin> \<Lambda>"
  shows   "\<wp>' z ^ 2 = 4 * \<wp> z ^ 3 - 60 * G 4 * \<wp> z - 140 * G 6"
proof -
  note [simp] = fls_subdegree_deriv fls_subdegree_weierstrass
  define f where "f = (\<lambda>z. \<wp>' z ^ 2 - 4 * \<wp> z ^ 3 + 60 * G 4 * \<wp> z)"
  interpret f: elliptic_function \<omega>1 \<omega>2 f
    unfolding f_def by (intro elliptic_function_intros)
  let ?P = fls_weierstrass
  define F :: "complex fls" where "F = fls_deriv ?P ^ 2 - 4 * ?P ^ 3 + fls_const (60 * G 4) * ?P"

  (* TODO: use remove_sings instead *)
  define g where "g = (\<lambda>z. if z \<in> \<Lambda> then -140 * G 6 else f z)"

  (* FIXME: Somewhat tedious computation. Could be automated – Manuel *)
  have unwind: "{m..n::int} = insert m {m+1..n}" if "m \<le> n" for m n
    using that by auto
  define fls_terms :: "complex fls \<Rightarrow> complex list"
    where "fls_terms = (\<lambda>F. map (\<lambda>k. fls_nth F k) [-6,-5,-4,-3,-2,-1,0])"
  have coeffs: "map (\<lambda>k. fls_nth F k) [-6,-5,-4,-3,-2,-1,0] = [0, 0, 0, 0, 0, 0, - (140 * G 6)]"
    by (simp add: power2_eq_square power3_eq_cube unwind fls_terms_def fls_times_nth(1) 
                  fls_nth_weierstrass F_def eisenstein_series_odd_eq_0 flip: One_nat_def)

  have F: "f has_laurent_expansion F"
    unfolding f_def F_def by (intro laurent_expansion_intros)

  have "fls_subdegree F \<ge> 0"
  proof (cases "F = 0")
    case False
    thus ?thesis
    proof (rule fls_subdegree_geI)
      show "fls_nth F k = 0" if "k < 0" for k
      proof (cases "k < -6")
        case True
        thus ?thesis
          by (simp add: power2_eq_square power3_eq_cube fls_times_nth(1) F_def)
      next
        case False
        with \<open>k < 0\<close> have "k \<in> {-6, -5, -4, -3, -2, -1}"
          by auto
        thus ?thesis using \<open>k < 0\<close>
          using coeffs by auto
      qed
    qed
  qed auto

  interpret g: complex_lattice_periodic \<omega>1 \<omega>2 g
    by standard (auto simp: g_def f.lattice_cong rel_def)

  have "f holomorphic_on -\<Lambda>\<^sup>* - {0}"
    unfolding f_def by (intro holomorphic_intros) (auto simp: lattice_lattice0)
  moreover have "open (-\<Lambda>\<^sup>*)"
    using closed_lattice0 by auto
  moreover have "f \<midarrow>0\<rightarrow> fls_nth F 0"
    using F \<open>fls_subdegree F \<ge> 0\<close> by (meson has_laurent_expansion_imp_tendsto_0)
  hence "f \<midarrow>0\<rightarrow> -140 * G 6"
    using coeffs by simp
  ultimately have "(\<lambda>z. if z = 0 then -140 * G 6 else f z) holomorphic_on -\<Lambda>\<^sup>*"
    unfolding g_def by (rule removable_singularity)
  hence "(\<lambda>z. if z = 0 then -140 * G 6 else f z) analytic_on {0}"
    using closed_lattice0 unfolding analytic_on_holomorphic by blast
  also have "?this \<longleftrightarrow> g analytic_on {0}"
    using closed_lattice0
    by (intro analytic_at_cong refl eventually_mono[OF eventually_nhds_in_open[of "-\<Lambda>\<^sup>*"]])
       (auto simp: g_def f_def lattice_lattice0)
  finally have "g analytic_on {0}" .

  have "g analytic_on (-\<Lambda> \<union> (\<Union>\<omega>\<in>\<Lambda>. {\<omega>}))"
    unfolding analytic_on_Un analytic_on_UN
  proof safe
    fix \<omega> :: complex
    assume \<omega>: "\<omega> \<in> \<Lambda>"
    have "g \<circ> (\<lambda>z. z - \<omega>) analytic_on {\<omega>}"
      using \<open>g analytic_on {0}\<close>
      by (intro analytic_on_compose) (auto intro!: analytic_intros)
    also have "g \<circ> (\<lambda>z. z - \<omega>) = g"
      by (auto simp: fun_eq_iff rel_def uminus_in_lattice_iff \<omega> intro!: g.lattice_cong)
    finally show "g analytic_on {\<omega>}" .
  next
    have "f holomorphic_on (-\<Lambda>)"
      unfolding f_def by (auto intro!: holomorphic_intros)
    also have "?this \<longleftrightarrow> g holomorphic_on (-\<Lambda>)"
      by (intro holomorphic_cong refl) (auto simp: g_def)
    finally show "g analytic_on (-\<Lambda>)"
      using closed_lattice by (subst analytic_on_open) auto
  qed
  also have "\<dots> = UNIV"
    by blast
  finally have g_ana: "g analytic_on UNIV" .

  interpret g: nicely_elliptic_function \<omega>1 \<omega>2 g
    by standard (auto intro!: analytic_on_imp_nicely_meromorphic_on g_ana)
  have "elliptic_order g = 0"
  proof (subst g.elliptic_order_eq_0_iff_no_poles, rule allI)
    show "\<not>is_pole g z" for z
      by (rule analytic_at_imp_no_pole) (auto intro: analytic_on_subset[OF g_ana])
  qed
  hence "g constant_on UNIV"
    by (simp add: g.elliptic_order_eq_0_iff)

  then obtain c where c: "g z = c" for z
    unfolding constant_on_def by blast
  from c[of 0] have "c = -140 * G 6"
    by (simp add: g_def)
  with c[of z] and assms show ?thesis
    by (simp add: g_def f_def algebra_simps)
qed

text \<open>
  The above ODE of the meromorphic function \<open>\<wp>\<close> can now easily be lifted to a formal ODE on
  the corresponding Laurent series.
\<close>
lemma fls_weierstrass_ODE1:
  defines "P \<equiv> fls_weierstrass"
  shows   "fls_deriv P ^ 2 = 4 * P ^ 3 - fls_const (60 * G 4) * P - fls_const (140 * G 6)"
  (is "?lhs = ?rhs")
proof -
  have ev: "eventually (\<lambda>z. z \<in> -\<Lambda>\<^sup>* - {0}) (at 0)"
    using closed_lattice0 by (intro eventually_at_in_open) auto
  have "(\<lambda>z. \<wp>' z ^ 2) has_laurent_expansion ?lhs"
    unfolding P_def by (intro laurent_expansion_intros)
  also have "?this \<longleftrightarrow> (\<lambda>z. 4 * \<wp> z ^ 3 - 60 * G 4 * \<wp> z - 140 * G 6) has_laurent_expansion ?lhs"
    by (intro has_laurent_expansion_cong refl eventually_mono[OF ev] weierstrass_fun_ODE1)
       (auto simp: lattice_lattice0)
  finally have \<dots> .
  moreover have "(\<lambda>z. 4 * \<wp> z ^ 3 - 60 * G 4 * \<wp> z - 140 * G 6) has_laurent_expansion ?rhs"
    unfolding P_def by (intro laurent_expansion_intros)
  ultimately show ?thesis
    using has_laurent_expansion_unique by blast
qed

lemma fls_weierstrass_ODE2:
  defines "P \<equiv> fls_weierstrass"
  shows   "fls_deriv (fls_deriv P) = 6 * P ^ 2 - fls_const (30 * G 4)"
proof -
  define d where "d = fls_deriv P"
  have "fls_subdegree d = -3"
    using fls_subdegree_weierstrass unfolding d_def
    by (subst fls_subdegree_deriv) (auto simp: P_def)
  hence nz: "d \<noteq> 0" by auto

  have "2 * d * fls_deriv d = 2 * d * (6 * P\<^sup>2  - 30 * fls_const (G 4))"
    using arg_cong[OF fls_weierstrass_ODE1, of fls_deriv]
    unfolding P_def [symmetric] fls_const_mult_const [symmetric] d_def
    by (simp add: fls_deriv_power algebra_simps)
  then have "fls_deriv d = 6 * P\<^sup>2 - 30 * fls_const (G 4)"
    using nz by simp
  then show ?thesis unfolding d_def
    by (metis fls_const_mult_const fls_const_numeral)
qed

theorem weierstrass_fun_ODE2:
  assumes "z \<notin> \<Lambda>"
  shows   "deriv \<wp>' z = 6 * \<wp> z ^ 2 - 30 * G 4"
proof -
  define P where "P = fls_weierstrass"
  have "(\<lambda>z. deriv \<wp>' z - 6 * \<wp> z ^ 2 + 30 * G 4) has_laurent_expansion
         (fls_deriv (fls_deriv P) - 6 * P ^ 2 +fls_const (30 * G 4))"
    unfolding P_def by (intro laurent_expansion_intros)
  also have "\<dots> = 0"
    by (simp add: fls_weierstrass_ODE2 P_def)
  finally have "deriv \<wp>' z - 6 * (\<wp> z)\<^sup>2 + 30 * G 4 = 0"
  proof (rule has_laurent_expansion_0_analytic_continuation)
    show "(\<lambda>z. deriv \<wp>' z - 6 * (\<wp> z)\<^sup>2 + 30 * G 4) holomorphic_on ((UNIV - (\<Lambda>-{0})) - {0})"
      by (auto intro!: holomorphic_intros intro: closed_subset_lattice)
    show "open (UNIV - (\<Lambda>-{0}))"
      by (intro open_Diff closed_subset_lattice) auto
    show "connected (UNIV - (\<Lambda>-{0}))"
      by (intro sparse_imp_connected sparse_in_subset2[OF lattice_sparse]) auto     
  qed (use assms in auto)
  thus ?thesis
    by (simp add: algebra_simps)
qed

lemma has_field_derivative_weierstrass_fun_deriv [derivative_intros]:
  assumes "(f has_field_derivative f') (at z within A)" "f z \<notin> \<Lambda>"
  shows   "((\<lambda>z. \<wp>' (f z)) has_field_derivative ((6 * \<wp> (f z) ^ 2 - 30 * G 4) * f')) (at z within A)"
proof (rule DERIV_chain' [OF assms(1)])
  have "(\<wp>' has_field_derivative (deriv \<wp>' (f z))) (at (f z))"
    by (rule analytic_derivI) (use assms(2) in \<open>auto intro!: analytic_intros\<close>)
  thus "(\<wp>' has_field_derivative 6 * (\<wp> (f z))\<^sup>2 - 30 * G 4) (at (f z))"
    using weierstrass_fun_ODE2[OF assms(2)] by simp
qed


subsection \<open>Lattice invariants and a recurrence for the Eisenstein series\<close>

 (* Definitions from Apostol, \S 1.9 *)
text \<open>
  We will see that $G_n$ can always be expressed in terms of $G_4$ and $G_6$. These values,
  up to a constant factor, are referred to as $g_2$ and $g_3$.
\<close>
definition invariant_g2:: "complex" ("\<g>\<^sub>2") where
  "\<g>\<^sub>2 \<equiv> 60 * eisenstein_series 4"

definition invariant_g3:: "complex" ("\<g>\<^sub>3") where
  "\<g>\<^sub>3 \<equiv> 140 * eisenstein_series 6"

lemma weierstrass_fun_ODE1':
  assumes "z \<notin> \<Lambda>"
  shows   "\<wp>' z ^ 2 = 4 * \<wp> z ^ 3 - \<g>\<^sub>2 * \<wp> z - \<g>\<^sub>3"
  using weierstrass_fun_ODE1[OF assms] by (simp add: invariant_g2_def invariant_g3_def)

text \<open>
  This is the ODE obtained by differentiating the first ODE.
\<close>
theorem weierstrass_fun_ODE2':
  assumes "z \<notin> \<Lambda>"
  shows   "deriv \<wp>' z = 6 * \<wp> z ^ 2 - \<g>\<^sub>2 / 2"
proof -
  define P where "P = fls_weierstrass"
  have "(\<lambda>z. deriv \<wp>' z - 6 * \<wp> z ^ 2 + \<g>\<^sub>2 / 2) has_laurent_expansion
        fls_deriv (fls_deriv P) - 6 * P ^ 2 + fls_const (\<g>\<^sub>2 / 2)" (is "?f has_laurent_expansion _")
    unfolding P_def by (intro laurent_expansion_intros)
  also have "\<dots> = 0"
    by (simp add: fls_weierstrass_ODE2 P_def invariant_g2_def)
  finally have "?f has_laurent_expansion 0" .
  hence "?f z = 0"
  proof (rule has_laurent_expansion_0_analytic_continuation)
    show "?f holomorphic_on UNIV - \<Lambda>\<^sup>* - {0}"
      using closed_lattice0
      by (intro holomorphic_intros) (auto simp: lattice_lattice0)
    show "connected (UNIV - \<Lambda>\<^sup>*)"
      by (intro connected_open_diff_countable countable_subset[OF _ countable_lattice])
         (auto simp: lattice_lattice0)        
  qed (use assms closed_lattice0 in \<open>auto simp: lattice_lattice0\<close>)
  thus ?thesis by (simp add: algebra_simps)
qed

lemma half_period_weierstrass_fun_is_root:
  assumes "\<omega> \<in> \<Lambda>" "\<omega> / 2 \<notin> \<Lambda>"
  defines "z \<equiv> \<wp> (\<omega> / 2)"
  shows   "4 * z ^ 3 - \<g>\<^sub>2 * z - \<g>\<^sub>3 = 0"
proof -
  have "\<wp>' (\<omega> / 2) = 0"
    using weierstrass_fun_deriv.lattice_cong[of "-\<omega>/2" "\<omega>/2"] \<open>\<omega> \<in> \<Lambda>\<close>
    by (auto simp: rel_def uminus_in_lattice_iff)
  hence "0 = \<wp>' (\<omega> / 2) ^ 2"
    by simp
  also have "\<dots> = 4 * \<wp> (\<omega> / 2) ^ 3 - \<g>\<^sub>2 * \<wp> (\<omega> / 2) - \<g>\<^sub>3"
    using assms by (subst weierstrass_fun_ODE1') auto
  finally show ?thesis
    by (simp add: z_def)
qed

text \<open>
  The discriminant of the depressed cubic polynomial $p(x) = cX^3 + aX + b$ is
  $-4a^3 - 27cb^2$. This is useful since it gives us an algebraic condition for whether $p$
  has distinct roots. 
\<close>
lemma (in -) depressed_cubic_discriminant:
  fixes a b :: "'a :: idom"
  assumes "[:b, a, 0, c:] = Polynomial.smult c ([:-x1, 1:] * [:-x2, 1:] * [:-x3, 1:])"
  shows   "c ^ 3 * (x1 - x2)\<^sup>2 * (x1 - x3)\<^sup>2 * (x2 - x3)\<^sup>2 = -4 * a ^ 3 - 27 * c * b ^ 2"
  using assms by (simp add: algebra_simps) Groebner_Basis.algebra


(* Theorem 1.14 *)

text \<open>
  The numbers \<open>\<e>\<^sub>1\<close>, \<open>\<e>\<^sub>2\<close>, \<open>\<e>\<^sub>3\<close> are all distinct and hence the discriminant
  $\Delta = g_2^3 - 27 g_3^2$ does not vanish. This is the first part of Apostol's Theorem~1.14.
\<close>
theorem distinct_e123: "distinct [\<e>\<^sub>1, \<e>\<^sub>2, \<e>\<^sub>3]"
proof -
  define X where "X = {\<omega>1 / 2, \<omega>2 / 2, (\<omega>1 + \<omega>2) / 2}"
  have empty: "X \<inter> \<Lambda> = {}"
    by (auto simp: X_def)
  have roots: "\<forall>x\<in>X. \<wp>' x = 0"
    using weierstass_fun_deriv_half_root_eq_0 unfolding X_def by blast
  have X_subset: "X \<subseteq> period_parallelogram 0"
    unfolding period_parallelogram_altdef of_\<omega>12_coords_image_eq
    by (auto simp: X_def \<omega>12_coords.add)

  have *: "\<wp> w1 \<noteq> \<wp> w2" if w12: "{w1, w2} \<subseteq> X" and neq: "w1 \<noteq> w2" for w1 w2
  proof
    assume eq: "\<wp> w1 = \<wp> w2"
    have not_in_lattice [simp]: "w1 \<notin> \<Lambda>" "w2 \<notin> \<Lambda>"
      using empty that(1) by blast+

    define f where "f = (\<lambda>z. \<wp> z - \<wp> w1)"

    have deriv_eq: "deriv f w = \<wp>' w" if "w \<notin> \<Lambda>" for w
      unfolding f_def using that 
      by (auto intro!: derivative_eq_intros DERIV_imp_deriv)
    have "deriv f w1 = 0" "deriv f w2 = 0"
      using w12 roots not_in_lattice deriv_eq by (metis insert_subset)+
    moreover have [simp]: "f w1 = 0" "f w2 = 0"
      using eq by (simp_all add: f_def)

    have "f has_laurent_expansion fls_weierstrass - fls_const (\<wp> w1)"
      unfolding f_def by (intro laurent_expansion_intros)
    moreover have "fls_subdegree (fls_weierstrass - fls_const (\<wp> w1)) = -2"
      by (simp add: fls_subdegree_weierstrass fls_subdegree_diff_eq1)
    ultimately have [simp]: "is_pole f 0" "zorder f 0 = -2"
      by (auto dest: has_laurent_expansion_imp_is_pole_0 has_laurent_expansion_zorder_0)
    have [simp]: "\<not>f constant_on UNIV"
      using pole_imp_not_constant[OF \<open>is_pole f 0\<close>, of UNIV UNIV] by auto

    have "\<not>(\<forall>x\<in>-\<Lambda>. f x = 0)"
    proof
      assume *: "\<forall>x\<in>-\<Lambda>. f x = 0"
      have "eventually (\<lambda>x. x \<in> -\<Lambda>\<^sup>* - {0}) (at 0)"
        using closed_lattice0 by (intro eventually_at_in_open) auto
      hence "eventually (\<lambda>x. f x = 0) (at 0)"
        by eventually_elim (use * in \<open>auto simp: lattice_lattice0\<close>)
      hence "f \<midarrow>0\<rightarrow> 0"
        by (simp add: tendsto_eventually)
      with \<open>is_pole f 0\<close> show False
        unfolding is_pole_def using not_tendsto_and_filterlim_at_infinity[of "at 0" f 0] by auto
    qed
    then obtain z0 where z0: "z0 \<notin> \<Lambda>" "f z0 \<noteq> 0"
      by auto
    then have nconst:"\<not> f constant_on (UNIV-\<Lambda>)"
      by (metis (mono_tags, lifting) Diff_iff UNIV_I \<open>f w1 = 0\<close>
          constant_on_def not_in_lattice(1))

    have zorder_ge: "zorder f w \<ge> int 2" if "w \<in> {w1, w2}" for w
    proof (rule zorder_geI)
      show "f analytic_on {w}" "f holomorphic_on UNIV - \<Lambda>"
        unfolding f_def using that w12 empty
        by (auto intro!: analytic_intros holomorphic_intros)
      show "connected (UNIV - \<Lambda>)"
        using countable_lattice by (intro connected_open_diff_countable) auto
      show "z0 \<in> UNIV - \<Lambda>" "f z0 \<noteq> 0"
        using z0 by auto
    next
      fix k :: nat
      assume "k < 2"
      hence "k = 0 \<or> k = 1"
        by auto
      thus "(deriv ^^ k) f w = 0"
        using that w12 empty deriv_eq[of w] roots by auto
    qed (use closed_lattice that w12 empty in auto)

    have not_pole: "\<not>is_pole f w" if "w \<in> {w1, w2}" for w
    proof -
      have "f holomorphic_on -\<Lambda>"
        unfolding f_def by (intro holomorphic_intros) auto
      moreover have "open (-\<Lambda>)" "w \<in> -\<Lambda>"
        using that empty w12 closed_lattice by auto
      ultimately show ?thesis
        using not_is_pole_holomorphic by blast
    qed

    have no_further_poles: "\<not>is_pole f z" if "z \<in> period_parallelogram 0 - {0}" for z
    proof -
      have "f holomorphic_on -\<Lambda>"
        unfolding f_def by (intro holomorphic_intros) auto
      moreover have "z \<notin> \<Lambda>"
      proof
        assume "z \<in> \<Lambda>"
        then obtain m n where z_eq: "z = of_\<omega>12_coords (of_int m, of_int n)"
          by (elim latticeE)
        from that have "m = 0" "n = 0"
          unfolding period_parallelogram_altdef of_\<omega>12_coords_image_eq
          by (auto simp: z_eq)
        with that show False
          by (auto simp: z_eq)
      qed
      ultimately show "\<not>is_pole f z"
        using closed_lattice not_is_pole_holomorphic[of "-\<Lambda>" z f] by auto
    qed

    interpret f: elliptic_function \<omega>1 \<omega>2 f
      unfolding f_def by (intro elliptic_function_intros)

    have [intro]: "isolated_zero f w" if "w \<in> {w1, w2}" for w
    proof (subst f.isolated_zero_analytic_iff)
      show "f analytic_on {w}"
        unfolding f_def by (intro analytic_intros) (use that in auto)
      show "f w = 0"
        using that by auto
      have "elliptic_order f \<noteq> 0"
        using \<open>is_pole f 0\<close> f.elliptic_order_eq_0_iff_no_poles by blast
      thus "\<not>(\<forall>\<^sub>\<approx>z\<in>UNIV. f z = 0)"
        unfolding f.elliptic_order_eq_0_iff_const_cosparse by metis
    qed

    have "4 = (\<Sum>z\<in>{w1, w2}. 2 :: nat)"
      using neq by simp
    also have "\<dots> \<le> (\<Sum>z\<in>{w1, w2}. nat (zorder f z))"
      using zorder_ge[of w1] zorder_ge[of w2] by (intro sum_mono) auto
    also have "{w1, w2} \<subseteq> {z \<in> period_parallelogram 0. isolated_zero f z}"
      using w12 X_subset by auto
    hence "(\<Sum>z\<in>{w1, w2}. nat (zorder f z)) \<le> (\<Sum>z\<in>\<dots>. nat (zorder f z))"
      using f.finite_zeros_in_parallelogram[of 0] by (intro sum_mono2) auto
    also have "\<dots> = elliptic_order f"
      by (rule f.zeros_eq_elliptic_order)
    also have "elliptic_order f = (\<Sum>z | z \<in> period_parallelogram 0 \<and> is_pole f z. nat (-zorder f z))"
      by (rule f.poles_eq_elliptic_order [symmetric])
    also have "\<dots> \<le> (\<Sum>z\<in>{0}. nat (-zorder f z))" 
    proof (rule sum_mono2)
      have "\<not>is_pole f w"  if "w \<in> period_parallelogram 0 - {0}" for w
        using no_further_poles[OF that] is_pole_cong by blast
      then show "{z \<in> period_parallelogram 0. is_pole f z} \<subseteq> {0}"
        unfolding period_parallelogram_def by auto
    qed simp_all
    also have "\<dots> = 2" by simp
    finally show False by simp
  qed
  show ?thesis
    by (simp add: number_e1_def number_e2_def number_e3_def; intro conjI *) (auto simp: X_def)
qed


text \<open>
  The above implies that the polynomial
  \[4(X-e_1)(X-e_2)(X-e_3) = 4X^3 - g_2 X - g_3\]
  has three distinct roots and therefore its discriminant
  \[\Delta = g_2^3 - 27g_3^2\]
  is non-zero. This is the second part of Apostol's Theorem~1.14.

  From now on, we will refer to $\Delta$ as the discriminant of our lattice $\Lambda$. We also
  introduce the related invariant $j = \tfrac{g_2^3}{\Delta}$.
\<close>

definition discr :: complex where
  "discr = \<g>\<^sub>2 ^ 3 - 27 * \<g>\<^sub>3 ^ 2"

definition invariant_j :: complex where
  "invariant_j = \<g>\<^sub>2 ^ 3 / discr"

theorem
  fixes z:: "complex"
  defines "P \<equiv> [:-\<g>\<^sub>3, -\<g>\<^sub>2, 0, 4:]"
  shows discr_nonzero_aux1: "P = 4 * [:-\<e>\<^sub>1, 1:] * [:-\<e>\<^sub>2, 1:] * [:-\<e>\<^sub>3, 1:]"
  and   discr_nonzero_aux2: "4 * (\<wp> z)^3 - \<g>\<^sub>2 * (\<wp> z) - \<g>\<^sub>3 = 4 * (\<wp> z - \<e>\<^sub>1) * (\<wp> z - \<e>\<^sub>2) * (\<wp> z - \<e>\<^sub>3)" 
  and   discr_nonzero: "discr \<noteq> 0"
proof -
  have zeroI: "poly P (\<wp> (\<omega> / 2)) = 0" if "\<omega> \<in> \<Lambda>" "\<omega> / 2 \<notin> \<Lambda>" for \<omega>
    using half_period_weierstrass_fun_is_root[OF that]
    by (simp add: P_def power3_eq_cube algebra_simps)

  obtain xs where "length xs = 3" and "Polynomial.smult 4 (\<Prod>x\<leftarrow>xs. [:-x, 1:]) = P"
    using fundamental_theorem_algebra_factorized[of P] 
    by (auto simp: P_def numeral_3_eq_3)
  hence P_eq: "P = Polynomial.smult 4 (\<Prod>x\<leftarrow>xs. [:-x, 1:])"
    by simp
  from \<open>length xs = 3\<close> obtain x1 x2 x3 where xs: "xs = [x1, x2, x3]"
    by (auto simp: numeral_3_eq_3 length_Suc_conv)
  have poly_P_eq: "poly P x = 4 * (x - x1) * (x - x2) * (x - x3)" for x
    by (simp add: algebra_simps P_eq xs)

  have "\<forall>x\<in>{\<e>\<^sub>1, \<e>\<^sub>2, \<e>\<^sub>3}. poly P x = 0"
    by (auto simp: number_e1_def number_e2_def number_e3_def intro!: zeroI intro: lattice_intros)
  hence set_xs: "set xs = {\<e>\<^sub>1, \<e>\<^sub>2, \<e>\<^sub>3}" and distinct: "distinct xs"
    using distinct_e123 by (auto simp: poly_P_eq xs)
  have "P = Polynomial.smult 4 (\<Prod>x\<in>set xs. [:-x, 1:])"
    using distinct P_eq by (subst prod.distinct_set_conv_list) auto
  thus P_eq': "P = 4 * [:-\<e>\<^sub>1, 1:] * [:-\<e>\<^sub>2, 1:] * [:-\<e>\<^sub>3, 1:]"
    unfolding set_xs using distinct_e123  by (simp add: xs numeral_poly algebra_simps)

  from arg_cong[OF this, of "\<lambda>P. poly P (\<wp> z)"]
    show "4 * (\<wp> z)^3 - \<g>\<^sub>2 * (\<wp> z) - \<g>\<^sub>3 = 4 * (\<wp> z - \<e>\<^sub>1) * (\<wp> z - \<e>\<^sub>2) * (\<wp> z - \<e>\<^sub>3)" 
    by (simp add: P_def numeral_poly algebra_simps power3_eq_cube)

  have "-4 * (-\<g>\<^sub>2) ^ 3 - 27 * 4 * (-\<g>\<^sub>3) ^ 2 = 4 ^ 3 * (\<e>\<^sub>1 - \<e>\<^sub>2)\<^sup>2 * (\<e>\<^sub>1 - \<e>\<^sub>3)\<^sup>2 * (\<e>\<^sub>2 - \<e>\<^sub>3)\<^sup>2"
    by (rule sym, rule depressed_cubic_discriminant, fold P_def) (simp add: P_eq' numeral_poly)
  also have "\<dots> \<noteq> 0"
    using distinct_e123 by simp
  finally show "discr \<noteq> 0"
    by (simp add: discr_def)
qed

end


context std_complex_lattice
begin

lemma eisenstein_series_norm_summable':
  "k \<ge> 3 \<Longrightarrow> (\<lambda>(m,n). norm (1 / (of_int m + of_int n * \<tau>) ^ k)) summable_on (-{(0,0)})"
  using eisenstein_series_norm_summable[of k]
        summable_on_reindex_bij_betw[OF bij_betw_lattice0', where f = "\<lambda>\<omega>. norm (1 / \<omega> ^ k)"]
  by (auto simp: eisenstein_series_def map_prod_def of_\<omega>12_coords_def
                 case_prod_unfold norm_divide norm_power)

lemma eisenstein_series_2_altdef:
  "eisenstein_series 2 = 2 * zeta 2 + (\<Sum>\<^sub>\<infinity>n\<in>-{0}. \<Sum>\<^sub>\<infinity>m. 1 / (of_int m + of_int n * \<tau>) ^ 2)"
  by (simp add: eisenstein_series_def of_\<omega>12_coords_def)  

lemma eisenstein_series_altdef':
  "k \<ge> 3 \<Longrightarrow> eisenstein_series k = (\<Sum>\<^sub>\<infinity>(m,n)\<in>-{(0,0)}. 1 / (of_int m + of_int n * \<tau>) ^ k)"
  using infsum_reindex_bij_betw[OF bij_betw_lattice0', where f = "\<lambda>\<omega>. 1 / \<omega> ^ k"]
  by (auto simp: eisenstein_series_altdef map_prod_def of_\<omega>12_coords_def case_prod_unfold)

end


subsection \<open>Fourier expansion\<close>

text \<open>
  In this section we derive the Fourier expansion of the Eisenstein series, following
  Apostol's Theorem~1.18, but with some alterations. For example, we directly generalise the
  result in the spirit of Apostol's Exercise~1.11, and we make use of the existing formalisation
  of Lambert series.

  We first define an auxiliary function
  \[f_n(z) = \sum_{m\in\mathbb{Z}} (z + m)^{-n} =
      \frac{1}{(n-1)!} \psi^{(n-1)}(1+z) + \psi^{(n-1)}(1-z) + \frac{1}{z^n}\]
  where $\psi^{(n)}$ denotes the Polygamma function.
  This is well-defined for $n \geq 2$ and $z\in\mathbb{C}\setminus\mathbb{Z}$.

  We then prove the Fourier expansion
  \[f_{n+1}(z) = \frac{(2i\pi)^{n+1}}{n!} \mathrm{Li}_{-n}(q)\]
  where $q = e^{2i\pi z}$ and $\mathrm{Li}_{-n}$ denotes the Polylogarithm function.
\<close>
definition eisenstein_fourier_aux :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
  "eisenstein_fourier_aux n z =
     (Polygamma (n-1) (1 + z) + Polygamma (n-1) (1 - z)) / fact (n - 1) + 1 / z ^ n"

lemma abs_summable_one_over_const_plus_nat_power:
  assumes "n \<ge> 2"
  shows   "summable (\<lambda>k. norm (1 / (z + of_nat k :: complex) ^ n))"
proof (rule summable_comparison_test_ev)
  have "eventually (\<lambda>k. real k > norm z) at_top"
    by real_asymp
  thus "eventually (\<lambda>k. norm (norm (1 / (z + of_nat k) ^ n)) \<le> 1 / (real k - norm z) ^ n) at_top"
  proof eventually_elim
    case (elim k)
    have "real k - norm z \<le> norm (z + of_nat k)"
      by (metis add.commute norm_diff_ineq norm_of_nat)
    hence "1 / norm (z + of_nat k) ^ n \<le> 1 / norm (real k - norm z) ^ n"
      using elim
      by (intro power_mono divide_left_mono Rings.mult_pos_pos zero_less_power) auto
    thus ?case using elim
      by (simp add: norm_divide norm_power)
  qed
next
  show "summable (\<lambda>k. 1 / (real k - norm z) ^ n)"
  proof (rule summable_comparison_test_bigo)
    show "summable (\<lambda>k. norm (1 / real k ^ n))"
      using inverse_power_summable[of n] assms
      by (simp add: norm_power norm_divide field_simps)
  next
    show "(\<lambda>k. 1 / (real k - norm z) ^ n) \<in> O(\<lambda>k. 1 / real k ^ n)"
      by real_asymp
  qed
qed

lemma abs_summable_one_over_const_minus_nat_power:
  assumes "n \<ge> 2"
  shows   "summable (\<lambda>k. norm (1 / (z - of_nat k :: complex) ^ n))"
proof -
  have "summable (\<lambda>k. norm (1 / ((-z) + of_nat k :: complex) ^ n))"
    using assms by (rule abs_summable_one_over_const_plus_nat_power)
  also have "(\<lambda>k. norm (1 / ((-z) + of_nat k :: complex) ^ n)) =
            (\<lambda>k. norm (1 / (z - of_nat k :: complex) ^ n))"
    by (simp add: norm_divide norm_power norm_minus_commute)
  finally show ?thesis .
qed

lemma has_sum_eisenstein_fourier_aux:
  assumes "n \<ge> 2" and "even n" and "Im z > 0"
  shows   "((\<lambda>m. 1 / (z + of_int m) ^ n) has_sum eisenstein_fourier_aux n z) UNIV"
proof -
  define f where "f = (\<lambda>k. 1 / (z + of_int k) ^ n)"

  from assms have "1 + z \<noteq> 0"
    by (subst add_eq_0_iff) auto
  have "(\<lambda>k. 1 / (((1 + z) + of_nat k) ^ n)) sums (Polygamma (n-1) (1+z) / fact (n-1))"
    using assms Polygamma_LIMSEQ[of "1 + z" "n - 1"] \<open>1 + z \<noteq> 0\<close> by (simp add: field_simps)
  moreover have "summable (\<lambda>k. cmod (1 / (z + (Suc k)) ^ n))"
    by (subst summable_Suc_iff) (rule abs_summable_one_over_const_plus_nat_power, fact)
  ultimately have "((\<lambda>k. 1 / (z + of_nat (Suc k)) ^ n) has_sum (Polygamma (n-1) (1+z) / fact (n-1))) UNIV"
    by (intro norm_summable_imp_has_sum) (simp_all add: algebra_simps)
  also have "?this \<longleftrightarrow> (f has_sum (Polygamma (n-1) (1+z) / fact (n-1))) {1..}" unfolding f_def
    by (rule has_sum_reindex_bij_witness[of _ "\<lambda>k. nat (k - 1)" "\<lambda>k. of_int (Suc k)"]) auto
  finally have sum1: "(f has_sum (Polygamma (n-1) (1+z) / fact (n-1))) {1..}" .

  have "1 - z \<noteq> 0"
    using assms by auto
  have "(\<lambda>k. 1 / (((1 - z) + of_nat k) ^ n)) sums (Polygamma (n-1) (1-z) / fact (n-1))"
    using assms Polygamma_LIMSEQ[of "1 - z" "n - 1"] \<open>1 - z \<noteq> 0\<close>
    by (simp add: field_simps)
  also have "(\<lambda>k. ((1 - z) + of_nat k) ^ n) = (\<lambda>k. (z - of_nat (Suc k)) ^ n)"
    using assms by (subst even_power_diff_commute) (auto simp: algebra_simps)
  finally have "(\<lambda>k. 1 / (z - of_nat (Suc k)) ^ n) sums (Polygamma (n-1) (1-z) / fact (n-1))" .
  moreover have "summable (\<lambda>k. cmod (1 / (z - (Suc k)) ^ n))"
    by (subst summable_Suc_iff) (rule abs_summable_one_over_const_minus_nat_power, fact)
  ultimately have "((\<lambda>k. 1 / (z - of_nat (Suc k)) ^ n) has_sum (Polygamma (n-1) (1-z) / fact (n-1))) UNIV"
    by (intro norm_summable_imp_has_sum)
  also have "?this \<longleftrightarrow> (f has_sum (Polygamma (n-1) (1-z) / fact (n-1))) {..-1}" unfolding f_def
    by (rule has_sum_reindex_bij_witness[of _ "\<lambda>k. nat (-k-1)" "\<lambda>k. -of_int (Suc k)"])
       (auto simp: algebra_simps)
  finally have sum2: "(f has_sum (Polygamma (n-1) (1-z) / fact (n-1))) {..-1}" .

  have "(f has_sum (Polygamma (n-1) (1+z) / fact (n-1)) + Polygamma (n-1) (1-z) / fact (n-1))
          ({1..} \<union> {..-1})"
    by (intro has_sum_Un_disjoint sum1 sum2) auto
  also have "({1..} \<union> {..-1}) = -{0::int}"
    by auto
  finally have "(f has_sum ((Polygamma (n-1) (1+z) + Polygamma (n-1) (1-z)) / fact (n-1))) (-{0})"
    by (simp add: add_divide_distrib)
  hence "(f has_sum (f 0 + (Polygamma (n-1) (1+z) + Polygamma (n-1) (1-z)) / fact (n-1))) (insert 0 (-{0}))"
    by (intro has_sum_insert) auto
  also have "insert 0 (-{0}) = (UNIV :: int set)"
    by auto
  finally show ?thesis
    by (simp add: eisenstein_fourier_aux_def f_def algebra_simps)
qed

lemma eisenstein_fourier_aux_expansion:
  assumes n: "odd n" and z: "Im z > 0"
  shows   "eisenstein_fourier_aux (n + 1) z =
             (2 * \<i> * pi) ^ Suc n / fact n * polylog (-int n) (to_q 1 z)"
proof -
  have eq0: "1 / z + cot_pfd z = -\<i> * pi * (2 * polylog 0 (to_q 1 z) + 1)"
    if z: "Im z > 0" for z :: complex
  proof -
    define x where "x = exp (2 * pi * \<i> * z)"
    have *: "exp (2 * pi * \<i> * z) = exp (pi * \<i> * z) ^ 2"
      by (subst exp_double [symmetric]) (simp add: algebra_simps)
    have "norm x < 1"
      using z by (auto simp: x_def)
    hence "x \<noteq> 1"
      by auto

    have "1 / z + cot_pfd z = pi * cot (pi * z)"
      using z by (intro cot_pfd_formula_complex [symmetric]) (auto elim: Ints_cases)
    also have "pi * cos (pi * z) * (x - 1) = pi * \<i> * sin (pi * z) * (x + 1)"
      using z * 
      by (simp add: sin_exp_eq cos_exp_eq x_def exp_minus field_simps power2_eq_square
               del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
    hence "pi * cot (pi * z) = \<i> * pi * (x + 1) / (x - 1)"
      unfolding cot_def using z by (auto simp: divide_simps sin_eq_0)
    also have "\<dots> = -\<i> * pi * (-(x + 1) / (x - 1))"
      by (simp add: field_simps)
    also have "-(x + 1) / (x - 1) = 1 + 2 * x / (1 - x)"
      using \<open>x \<noteq> 1\<close> by (simp add: field_simps)
    also have "\<dots> = 2 * polylog 0 x + 1"
      using \<open>norm x < 1\<close> and \<open>x \<noteq> 1\<close> by (simp add: polylog_0_left field_simps)
    finally show ?thesis by (simp only: x_def to_q_def) simp
  qed

  define f :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
    "f = (\<lambda>n z. if n = 0 then 1 / z + cot_pfd z
                else (-1) ^ n * Polygamma n (1 - z) - Polygamma n (1 + z) +
                     (-1) ^ n * fact n / z ^ (Suc n))"

  have f_odd_eq: "f n z = -fact n * eisenstein_fourier_aux (n+1) z" if "odd n" for n z
    using that by (auto simp add: f_def eisenstein_fourier_aux_def field_simps)

  have DERIV_f: "(f n has_field_derivative f (Suc n) z) (at z)" if "z \<notin> \<int>" for n z
  proof (cases "n = 0")
    case [simp]: True
    have "((\<lambda>z. 1 / z + cot_pfd z) has_field_derivative f 1 z) (at z)"
      unfolding f_def by (rule derivative_eq_intros refl | use that in force)+
    thus ?thesis by (simp add: f_def)
  next
    case False
    have 1: "1 - z \<notin> \<int>\<^sub>\<le>\<^sub>0" "1 + z \<notin> \<int>\<^sub>\<le>\<^sub>0"
      using that by (metis Ints_1 Ints_diff add_diff_cancel_left' diff_diff_eq2 nonpos_Ints_Int)+
    have 2: "z \<noteq> 0"
      using that by auto

    have "((\<lambda>z. (-1) ^ n * Polygamma n (1 - z) - Polygamma n (1 + z) + (-1) ^ n * fact n / z ^ (Suc n))
           has_field_derivative (-1) ^ Suc n * Polygamma (Suc n) (1 - z) -
             Polygamma (Suc n) (1 + z) + (-1) ^ Suc n * fact (Suc n) / z ^ (Suc (Suc n))) (at z)"
      by (rule derivative_eq_intros refl | use that 1 2 in force)+
    thus ?thesis
      using that False by (simp add: f_def)
  qed

  define g :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
    "g = (\<lambda>n z. -pi * \<i> * (2 * \<i> * pi) ^ n * (2 * polylog (-n) (to_q 1 z) + (if n = 0 then 1 else 0)))"

  have g_eq: "g n z = -((2 * \<i> * pi) ^ Suc n) * polylog (-n) (to_q 1 z)" if "n > 0" for n z
    using that unfolding g_def by simp

  note [derivative_intros del] = DERIV_sum
  have DERIV_g: "(g n has_field_derivative g (Suc n) z) (at z)" if z: "Im z > 0" for z n
  proof -
    have "norm (to_q 1 z) = exp (- (2 * pi * Im z))"
      by simp
    also have "\<dots> < exp 0"
      using that by (subst exp_less_cancel_iff) auto
    finally have "norm (to_q (Suc 0) z) \<noteq> 1"
      by auto
    moreover have "norm (1 :: complex) = 1"
      by simp
    ultimately have [simp]: "to_q (Suc 0) z \<noteq> 1"
      by metis
    show ?thesis unfolding g_def
      by (rule derivative_eq_intros refl | (use z in simp; fail))+
         (auto simp: algebra_simps minus_diff_commute)
  qed

  have eq: "f n z = g n z" if "Im z > 0" for z n
    using that
  proof (induction n arbitrary: z)
    case (0 z)
    have "norm (to_q 1 z) < 1"
      unfolding to_q_def using 0 by simp
    hence "polylog 0 (to_q 1 z) = to_q 1 z / (1 - to_q 1 z)"
      by (subst polylog_0_left) auto
    thus ?case
      using eq0[of z] 0 by (auto simp: complex_is_Int_iff f_def g_def)
  next
    case (Suc n z)
    have "(f n has_field_derivative f (Suc n) z) (at z)"
      by (rule DERIV_f) (use Suc.prems in \<open>auto simp: complex_is_Int_iff\<close>)
    also have "?this \<longleftrightarrow> (g n has_field_derivative f (Suc n) z) (at z)"
    proof (rule DERIV_cong_ev)
      have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (nhds z)"
        using Suc.prems by (intro eventually_nhds_in_open) (auto simp: open_halfspace_Im_gt)
      thus "eventually (\<lambda>z. f n z = g n z) (nhds z)"
        by eventually_elim (use Suc.IH in auto)
    qed auto
    finally have "(g n has_field_derivative f (Suc n) z) (at z)" .
    moreover have "(g n has_field_derivative g (Suc n) z) (at z)"
      by (rule DERIV_g) fact
    ultimately show "f (Suc n) z = g (Suc n) z"
      using DERIV_unique by blast
  qed

  from z have "f n z = g n z"
    by (intro eq) auto
  also have "f n z = -fact n * eisenstein_fourier_aux (n+1) z"
    using n by (subst f_odd_eq) auto
  also have "g n z = - ((2 * \<i> * pi) ^ Suc n) * polylog (-n) (to_q 1 z)"
    using n by (subst g_eq) (auto elim: oddE)
  finally show ?thesis
    by (simp add: to_q_def field_simps)
qed

text \<open>
  With this, we can now express the Fourier expansion of the Eisenstein series of the lattice
  $\Lambda(1, \tau)$ with $\mathrm{Im}(\tau) > 0$ in terms of a Lambert series:
  \[G_k = 2 (\zeta(k) + \frac{(2 i \pi)^k}{(k-1)!} L(n^{k-1}, q)) \]
  Here, as usual, $q = e^{2i\pi\tau}$ and
  \[L(n^{k-1}, q) =
     \sum_{n\geq 1} n^{k-1} \frac{q^n}{1 - q^n} = 
     \sum_{n\geq 1} \sigma_{k-1}(n) q^n \]
\<close>
lemma (in std_complex_lattice) eisenstein_series_conv_lambert:
  assumes k: "k \<ge> 2" "even k"
  defines "x \<equiv> to_q 1 \<tau>"
  shows "eisenstein_series k =
           2 * (zeta k + (2 * \<i> * pi) ^ k / fact (k - 1) * lambert (\<lambda>n. of_nat n ^ (k-1)) x)"
proof -
  have x: "norm x < 1"
    using Im_\<tau>_pos by (simp add: x_def to_q_def)

  define g where "g = (\<lambda>(n,m). 1 / (of_int m + of_int n * \<tau>) ^ k)"
  define C where "C = (2 * \<i> * pi) ^ k / fact (k-1)"
  define S where "S = lambert (\<lambda>n. of_nat n ^ (k-1)) x"

  have sum1: "((\<lambda>m. g (int n, m)) has_sum C * polylog (1 - int k) (x ^ n)) UNIV" if n: "n > 0" for n
  proof -
    have "((\<lambda>m. g (int n, m)) has_sum eisenstein_fourier_aux k (of_nat n * \<tau>)) UNIV"
      using has_sum_eisenstein_fourier_aux[of k "of_nat n * \<tau>"] n k Im_\<tau>_pos
      by (simp add: g_def add_ac)
    also have "eisenstein_fourier_aux k (of_nat n * \<tau>) =
                 C * polylog (1 - int k) (to_q 1 (of_nat n * \<tau>))"
      using eisenstein_fourier_aux_expansion[of "k-1" "of_nat n * \<tau>"] Im_\<tau>_pos n k
      by (simp add: C_def)
    also have "to_q 1 (of_nat n * \<tau>) = x ^ n"
      by (simp add: x_def to_q_power)
    finally show ?thesis .
  qed

  have "((\<lambda>n. polylog (1 - int k) (x ^ n)) has_sum S) {1..}"
    using lambert_power_int_has_sum_polylog_gen[of x 1 "int k - 1"] x k 
    by (simp add: power_int_def nat_diff_distrib S_def)
  hence "((\<lambda>n. C * polylog (1 - int k) (x ^ n)) has_sum (C * S)) {1..}"
    by (rule has_sum_cmult_right)
  also have "?this \<longleftrightarrow> ((\<lambda>n. (\<Sum>\<^sub>\<infinity>m. g (int n, m))) has_sum (C * S)) {1..}"
    by (rule has_sum_cong) (use sum1 in \<open>auto simp: has_sum_iff\<close>)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>n. (\<Sum>\<^sub>\<infinity>m. g (n, m))) has_sum (C * S)) {1..}"
    by (rule has_sum_reindex_bij_witness[of _ nat int]) auto
  finally have sum2: "((\<lambda>n. (\<Sum>\<^sub>\<infinity>m. g (n, m))) has_sum (C * S)) {1..}" .

  also have "?this \<longleftrightarrow> ((\<lambda>n. (\<Sum>\<^sub>\<infinity>m. g (-n, m))) has_sum (C * S)) {..-1}"
    by (rule has_sum_reindex_bij_witness[of _ uminus uminus]) (auto simp: g_def)
  also have "(\<lambda>n. \<Sum>\<^sub>\<infinity>m. g (-n, m)) = (\<lambda>n. \<Sum>\<^sub>\<infinity>m. g (n, m))"
  proof
    fix n :: int
    show "(\<Sum>\<^sub>\<infinity>m. g (-n, m)) = (\<Sum>\<^sub>\<infinity>m. g (n, m))"
      by (rule infsum_reindex_bij_witness[of _ uminus uminus])
         (use k in \<open>auto simp: g_def even_power_diff_commute\<close>)
  qed
  finally have "((\<lambda>n. \<Sum>\<^sub>\<infinity>m. g (n, m)) has_sum C * S) {..-1}" .
  hence "((\<lambda>n. \<Sum>\<^sub>\<infinity>m. g (n, m)) has_sum (C * S + C * S)) ({..-1} \<union> {1..})"
    by (intro has_sum_Un_disjoint sum2) auto
  also have "C * S + C * S = 2 * C * S"
    by simp
  also have "{..-1} \<union> {1..} = -{0::int}"
    by auto
  finally have sum3: "((\<lambda>n. \<Sum>\<^sub>\<infinity>m. g (n, m)) has_sum 2 * C * S) (-{0})" .

  have "eisenstein_series k = 2 * zeta (of_nat k) + (\<Sum>\<^sub>\<infinity>n\<in>-{0}. \<Sum>\<^sub>\<infinity>m. g (n, m))"
    using k by (simp add: eisenstein_series_def g_def of_\<omega>12_coords_def)
  also have "(\<Sum>\<^sub>\<infinity>n\<in>-{0}. \<Sum>\<^sub>\<infinity>m. g (n, m)) = 2 * C * S"
    using sum3 by (simp add: has_sum_iff)
  finally show ?thesis
    by (simp add: C_def S_def)
qed



subsection \<open>Behaviour under lattice transformations\<close>

text \<open>
  In this section, we will show how the Eisenstein series and related lattice properties
  behave under various lattice operations such as unimodular transformations and stretching.

  In particular, we will see that the invariant $j$ is actually invariant under unimodular
  transformations and stretching. This is Apostol's Theorem~1.16.
\<close>

context complex_lattice_swap
begin

lemma eisenstein_series_swap [simp]:
  assumes "k \<noteq> 2"
  shows   "swap.eisenstein_series k = eisenstein_series k"
proof (cases "k \<ge> 3")
  case True
  thus ?thesis
    unfolding eisenstein_series_altdef[OF True] swap.eisenstein_series_altdef[OF True] by simp
next
  case False
  with assms have "k = 0 \<or> k = 1"
    by auto
  thus ?thesis
    by auto
qed

lemma eisenstein_fun_aux_swap [simp]: "swap.eisenstein_fun_aux = eisenstein_fun_aux"
  unfolding eisenstein_fun_aux_def [abs_def] swap.eisenstein_fun_aux_def [abs_def] by (auto cong: if_cong)

lemma invariant_g2_swap [simp]: "swap.invariant_g2 = invariant_g2"
  and invariant_g3_swap [simp]: "swap.invariant_g3 = invariant_g3"
  unfolding invariant_g2_def [abs_def] swap.invariant_g2_def [abs_def]
            invariant_g3_def [abs_def] swap.invariant_g3_def [abs_def] by auto

lemma discr_swap [simp]: "swap.discr = discr"
  by (simp add: discr_def swap.discr_def)

lemma invariant_j_swap [simp]: "swap.invariant_j = invariant_j"
  by (simp add: invariant_j_def swap.invariant_j_def)

end


context complex_lattice_cnj
begin

lemma eisenstein_series_cnj [simp]: "cnj.eisenstein_series n = cnj (eisenstein_series n)"
  unfolding eisenstein_series_def cnj.eisenstein_series_def
  by (simp flip: zeta_cnj infsum_cnj add: of_\<omega>12_coords_def cnj.of_\<omega>12_coords_def)

lemma invariant_g2_cnj [simp]: "cnj.invariant_g2 = cnj invariant_g2"
  and invariant_g3_cnj [simp]: "cnj.invariant_g3 = cnj invariant_g3"
  by (simp_all add: cnj.invariant_g2_def invariant_g2_def cnj.invariant_g3_def invariant_g3_def)

lemma discr_cnj [simp]: "cnj.discr = cnj discr"
  by (simp add: discr_def cnj.discr_def)

lemma invariant_j_cnj [simp]: "cnj.invariant_j = cnj invariant_j"
  by (simp add: invariant_j_def cnj.invariant_j_def)

end


context complex_lattice_stretch
begin

lemma eisenstein_series_stretch:
  "stretched.eisenstein_series n = c powi (-n) * eisenstein_series n"
proof (cases "n \<ge> 3")
  case True
  have "stretched.eisenstein_series n = (\<Sum>\<^sub>\<infinity>x\<in>\<Lambda>\<^sup>*. c powi (-n) * (1 / x ^ n))"
    using infsum_reindex_bij_betw[OF bij_betw_stretch_lattice0, where f = "\<lambda>\<omega>. 1 / \<omega> ^ n"] True
    unfolding stretched.eisenstein_series_altdef[OF True] by (simp add: power_int_minus field_simps)
  also have "\<dots> = c powi (-n) * eisenstein_series n"
    using True by (subst infsum_cmult_right') (auto simp: eisenstein_series_altdef)
  finally show ?thesis .
next
  case False
  hence "n = 0 \<or> n = 1 \<or> n = 2"
    by auto
  thus ?thesis
  proof (elim disjE)
    assume [simp]: "n = 2"
    show "stretched.eisenstein_series n = c powi -int n * G n"
      unfolding eisenstein_series_def stretched.eisenstein_series_def stretched_of_\<omega>12_coords
      apply (simp add: ring_distribs flip: infsum_cmult_right')
      apply (simp add: power_int_minus field_simps)?
      done
  qed auto
qed

lemma invariant_g2_stretch [simp]: "stretched.invariant_g2 = invariant_g2 / c ^ 4"
  and invariant_g3_stretch [simp]: "stretched.invariant_g3 = invariant_g3 / c ^ 6"
  unfolding invariant_g2_def stretched.invariant_g2_def 
            invariant_g3_def stretched.invariant_g3_def eisenstein_series_stretch
  by (simp_all add: power_int_minus field_simps)

lemma discr_stretch [simp]: "stretched.discr = discr / c ^ 12"
  unfolding stretched.discr_def discr_def invariant_g2_stretch invariant_g3_stretch
  by (simp add: field_simps stretch_nonzero)

lemma invariant_j_stretch [simp]: "stretched.invariant_j = invariant_j"
  unfolding stretched.invariant_j_def invariant_j_def invariant_g2_stretch discr_stretch
  by (simp add: field_simps stretch_nonzero)

end


context unimodular_moebius_transform_lattice
begin

lemma eisenstein_series_transformed [simp]:
  assumes "k \<noteq> 2"
  shows   "transformed.eisenstein_series k = eisenstein_series k"
proof (cases "k \<ge> 3")
  case True
  thus ?thesis
    by (simp add: transformed.eisenstein_series_altdef eisenstein_series_altdef transformed_lattice0_eq)
next
  case False
  with assms have "k = 0 \<or> k = 1"
    by auto
  thus ?thesis
    by auto
qed

lemma invariant_g2_transformed [simp]: "transformed.invariant_g2 = invariant_g2"
  and invariant_g3_transformed [simp]: "transformed.invariant_g3 = invariant_g3"
     by ((intro ext)?, unfold invariant_g2_def invariant_g3_def number_e1_def
          transformed.invariant_g2_def transformed.invariant_g3_def transformed_lattice0_eq) simp_all

lemma discr_transformed [simp]: "transformed.discr = discr"
  by (simp add: transformed.discr_def discr_def)

lemma invariant_j_transformed [simp]: "transformed.invariant_j = invariant_j"
  by (simp add: transformed.invariant_j_def invariant_j_def)

end


subsection \<open>Recurrence relation\<close>

context complex_lattice
begin

(* Theorem 1.13 *)
text \<open>
  Using our formal ODE from above, we find the following recurrence for $G_n$.
  By unfolding this repeatedly, we can write any $G_n$ as a polynomial in $G_4$ and $G_6$ --
  or, equivalently, in $g_2$ and $g_3$.

  This is Theorem~1.13 in Apostol's book.
\<close>
lemma eisenstein_series_recurrence_aux:
  defines "b \<equiv> \<lambda>n. (2*n + 1) * (G (2*n + 2))"
  shows "b 1 = \<g>\<^sub>2 / 20"
    and "b 2 = \<g>\<^sub>3 / 28"
    and "\<And>n. n \<ge> 3 \<Longrightarrow> (2 * of_nat n + 3) * (of_nat n - 2) * b n = 3 * (\<Sum>i=1..n-2. b i * b (n - i - 1))"
proof -
  show "b 1 = \<g>\<^sub>2 / 20" "b 2 = \<g>\<^sub>3 / 28"
    by (simp_all add: b_def invariant_g2_def invariant_g3_def)
next
  fix n :: nat assume n: "n \<ge> 3"

  define c where "c = fls_nth fls_weierstrass"
  have b_c: "b n = c (2 * n)" if "n > 0" for n
    using that by (simp add: c_def fls_nth_weierstrass nat_add_distrib b_def nat_mult_distrib)

  have "(2 * of_nat n) * (2 * of_nat n - 1) * b n =
        6 * fls_nth (fls_weierstrass\<^sup>2) (2 * int n - 2)"
    using arg_cong[OF fls_weierstrass_ODE2, of "\<lambda>F. fls_nth F (2 * (n - 1))"] n
    by (simp add: algebra_simps of_nat_diff nat_mult_distrib b_c c_def)
  also have "fls_nth (fls_weierstrass\<^sup>2) (2 * int n - 2) =
             (\<Sum>i=-2..2 * int n. c i * c (2 * int n - 2 - i))"
    by (simp add: power2_eq_square fls_times_nth(2) fls_subdegree_weierstrass flip: c_def)
  also have "\<dots> = (\<Sum>i\<in>{-2..2 * int n}-{n. odd n}. c i * c (2 * int n - 2 - i))"
    by (intro sum.mono_neutral_right)
       (auto simp: c_def fls_nth_weierstrass eisenstein_series_odd_eq_0 even_nat_iff)
  also have "\<dots> = (\<Sum>i\<in>{-1, int n} \<union> {0..<int n}. c (2 * i) * c (2 * (int n - i - 1)))"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>k. 2 * k" "\<lambda>k. k div 2"]) (auto simp: algebra_simps)
  also have "\<dots> = 2 * b n + (\<Sum>i=0..<int n. c (2 * i) * c (2 * (int n - i - 1)))"
    using n by (subst sum.union_disjoint) (auto simp: c_def fls_nth_weierstrass b_c)
  also have "(\<Sum>i=0..<int n. c (2 * i) * c (2 * (int n - i - 1))) =
             (\<Sum>i=0..<n. c (2 * int i) * c (2 * (int n - int i - 1)))"
    by (intro sum.reindex_bij_witness[of _ int nat]) (auto simp: of_nat_diff)
  also have "\<dots> = (\<Sum>i=1..n-2. c (2 * int i) * c (2 * (int n - int i - 1)))"
    by (intro sum.mono_neutral_right) (auto simp: c_def fls_nth_weierstrass)
  also have "\<dots> = (\<Sum>i=1..n-2. b i * b (n - i - 1))"
    using n by (intro sum.cong) (auto simp: b_c of_nat_diff algebra_simps)
  finally show "(2 * of_nat n + 3) * (of_nat n - 2) * b n 
      = 3 * (\<Sum>i=1..n-2. b i * b (n - i - 1))"
    by Groebner_Basis.algebra
qed

theorem eisenstein_series_recurrence:
  assumes "n \<ge> 2"
  shows "G (2*n+4) = 3 / of_nat ((2*n+5) * (n-1) * (2*n+3)) *
           (\<Sum>i\<le>n-2. of_nat ((2*i+3) * (2*(n-i)-1)) * G (2*i+4) * G (2*(n-2-i)+4))"
proof -
  define c :: nat where "c = (2*(n+1)+3) * ((n+1)-2) * (2*(n+1)+1)"
  have c_altdef: "c = (2*n+5) * (n-1) * (2*n+3)"
    using assms unfolding c_def by (intro arg_cong2[of _ _ _ _ "(*)"]) auto
  define S where "S = (\<Sum>i\<le>n-2. of_nat ((2*i+3) * (2*(n-i)-1)) * G (2*i+4) * G (2*(n-2-i)+4))"
  have [simp]: "c \<noteq> 0"
    using assms unfolding c_def mult_eq_0_iff by auto
  have *: "n + 1 \<ge> 3"
    using assms by linarith
  have "of_nat c * G (2 * (n+1) + 2) = 
          3 * (\<Sum>i=1..(n+1) - 2. (2 * i + 1) * (2 * ((n+1) - i - 1) + 1) * G (2 * i + 2) * G (2 * ((n+1) - i - 1) + 2))"
    using eisenstein_series_recurrence_aux(3)[OF *] assms unfolding c_def
    apply simp
    apply (simp add: algebra_simps)
    done
  also have "2 * (n+1) + 2 = 2 * n + 4"
    using assms by simp
  also have "(\<Sum>i=1..(n+1) - 2. (2 * i + 1) * (2 * ((n+1) - i - 1) + 1) * G (2 * i + 2) * G (2 * ((n+1) - i - 1) + 2)) =
             (\<Sum>i\<le>(n+1) - 3. (2 * (i+1) + 1) * (2 * ((n+1) - (i+1) - 1) + 1) * G (2 * (i+1) + 2) * G (2 * ((n+1) - (i+1) - 1) + 2))"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>i. i+1" "\<lambda>i. i-1"]) (use assms in auto)
  also have "(n+1) - 3 = n - 2"
    using assms by linarith
  also have "(\<Sum>i\<le>n-2. (2 * (i+1) + 1) * (2 * ((n+1) - (i+1) - 1) + 1) * G (2 * (i+1) + 2) * G (2 * ((n+1) - (i+1) - 1) + 2)) = S"
    using assms unfolding S_def
    apply (intro sum.cong refl arg_cong2[of _ _ _ _ "(*)"] arg_cong[of _ _ of_nat] arg_cong[of _ _ G])
       apply (auto simp: algebra_simps Suc_diff_Suc)
    done
  finally have "G (2 * n + 4) = 3 / of_nat c * S"
    by (simp add: field_simps)
  thus ?thesis
    unfolding S_def c_altdef .
qed

end


text \<open>
  With this we can now write some code to compute representations of $G_n$ in terms of
  $G_4$ and $G_6$. Our code returns a bivariate polynomial with rational coefficients.
\<close>

fun eisenstein_series_poly :: "nat \<Rightarrow> rat poly poly" where
  "eisenstein_series_poly n =
     (if n = 0 then [: [:0, 1:] :]
      else if n = 1 then [:0, 1:]
      else
        Polynomial.smult [:3 / of_nat ((2*n+5) * (n-1) * (2*n+3)):]
          (\<Sum>i\<le>n-2. Polynomial.smult (of_nat ((2*i+3)*(2*(n-i)-1))) 
            (eisenstein_series_poly i * eisenstein_series_poly (n-2-i))))"

lemmas [simp del] = eisenstein_series_poly.simps

lemma eisenstein_series_poly_0 [simp]: "eisenstein_series_poly 0 = [: [:0, 1:] :]"
  and eisenstein_series_poly_1 [simp]: "eisenstein_series_poly (Suc 0) = [:0, 1:]"
  and eisenstein_series_poly_rec:
        "n \<ge> 2 \<Longrightarrow> eisenstein_series_poly n = 
           Polynomial.smult [:3 / of_nat ((2*n+5) * (n-1) * (2*n+3)):]
             (\<Sum>i\<le>n-2. Polynomial.smult (of_nat ((2*i+3)*(2*(n-i)-1))) 
               (eisenstein_series_poly i * eisenstein_series_poly (n-2-i)))"
  by (subst eisenstein_series_poly.simps; simp; fail)+

lemma coeff_0_0_eisenstein_series_poly [simp]:
  "poly.coeff (poly.coeff (eisenstein_series_poly n) 0) 0 = 0"
  by (induction n rule: eisenstein_series_poly.induct; subst eisenstein_series_poly.simps)
     (auto simp: coeff_sum coeff_mult_0)

context complex_lattice
begin

lemma eisenstein_series_poly_correct:
  "poly2 (map_poly2 of_rat (eisenstein_series_poly n)) (G 4) (G 6) = G (2 * n + 4)"
proof (induction n rule: eisenstein_series_poly.induct)
  case (1 n)
  interpret map1: map_poly_comm_ring_hom "of_rat :: rat \<Rightarrow> complex"
    by standard auto
  interpret map2: map_poly_comm_ring_hom "map_poly (of_rat :: rat \<Rightarrow> complex)"
    by standard auto
  consider "n = 0" | "n = 1" | "n \<ge> 2"
    by linarith
  thus ?case
  proof cases
    case 3
    define c where "c = 3 / complex_of_nat ((2 * n + 5) * (n - 1) * (2 * n + 3))"
    have "poly2 (map_poly2 of_rat (eisenstein_series_poly n)) (G 4) (G 6) =
           c * (\<Sum>i\<le>n-2. (of_nat ((2 * i + 3) * (2 * (n - i) - 1)) *
                         G (2 * i + 4) * G (2 * (n - 2 - i) + 4)))"
      using 3 1
      apply (simp add: eisenstein_series_poly_rec map_poly2_def hom_distribs c_def sum_distrib_left)
      apply (simp add: algebra_simps)?
      done
    also have "\<dots> = G (2 * n + 4)"
      unfolding c_def by (rule eisenstein_series_recurrence[OF \<open>n \<ge> 2\<close>, symmetric])
    finally show ?thesis .
  qed (auto simp: map_poly_pCons map_poly2_def)
qed

end


text \<open>
  We employ memoisation for better performance:
\<close>
definition eisenstein_polys_step :: "rat poly poly list \<Rightarrow> rat poly poly list" where
  "eisenstein_polys_step ps =
     (let n = length ps
      in  ps @ [Polynomial.smult [:3 / of_nat ((2*n+5) * (n-1) * (2*n+3)):]
             (\<Sum>i\<le>n-2. Polynomial.smult (of_nat ((2*i+3)*(2*(n-i)-1))) 
               (ps ! i * ps ! (n-2-i)))])"

definition eisenstein_series_polys :: "nat \<Rightarrow> rat poly poly list" where
  "eisenstein_series_polys n = (eisenstein_polys_step ^^ (n - 2)) [[: [:0, 1:] :], [:0, 1:]]"

lemma eisenstein_polys_step_correct:
  assumes n: "n \<ge> 2" and ps_eq: "ps = map eisenstein_series_poly [0..<n]"
  shows   "eisenstein_polys_step ps = map eisenstein_series_poly [0..<Suc n]"
proof (rule nth_equalityI)
  fix i assume "i < length (eisenstein_polys_step ps)"
  have length: "length ps = n"
    by (simp add: ps_eq)
  define p where "p = Polynomial.smult [:3 / of_nat ((2*n+5) * (n-1) * (2*n+3)):]
             (\<Sum>i\<le>n-2. Polynomial.smult (of_nat ((2*i+3)*(2*(n-i)-1))) 
               (ps ! i * ps ! (n-2-i)))"
  have step: "eisenstein_polys_step ps = ps @ [p]"
    by (simp add: eisenstein_polys_step_def p_def length Let_def)
  have i: "i \<le> n"
    using \<open>i < _\<close> unfolding ps_eq length eisenstein_polys_step_def by simp
  show "eisenstein_polys_step ps ! i = map eisenstein_series_poly [0..<Suc n] ! i"
  proof (cases "i = n")
    case False
    thus ?thesis
      using i unfolding step by (auto simp: ps_eq nth_append simp del: upt_Suc)
  next
    case [simp]: True
    have "eisenstein_polys_step ps ! i = p"
      by (auto simp: step nth_append length)
    also have "p = eisenstein_series_poly n"
      unfolding eisenstein_series_poly_rec[OF n] p_def ps_eq
      by (intro arg_cong2[of _ _ _ _ Polynomial.smult] refl sum.cong) (use n in auto)
    also have "\<dots> = map eisenstein_series_poly [0..<Suc n] ! i"
      by (simp del: upt_Suc)
    finally show ?thesis .
  qed
qed (auto simp: eisenstein_polys_step_def ps_eq)

lemma eisenstein_series_polys_correct:
  "eisenstein_series_polys n = map eisenstein_series_poly [0..<max 2 n]"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n \<ge> 3")
    case False
    thus ?thesis
      by (auto simp: eisenstein_series_polys_def upt_rec)
  next
    case True
    define m where "m = n - 3"
    have n_eq: "n = Suc (Suc (Suc m))"
      using True unfolding m_def by simp
    have "eisenstein_polys_step (eisenstein_series_polys (n-1)) =
            map eisenstein_series_poly [0..<Suc (n-1)]"
    proof (rule eisenstein_polys_step_correct)
      have "eisenstein_series_polys (n - 1) = map eisenstein_series_poly [0..<max 2 (n-1)]"
        by (rule less.IH) (use True in auto)
      thus "eisenstein_series_polys (n - 1) = map eisenstein_series_poly [0..<n-1]"
        using True by simp
    qed (use True in auto)
    also have "eisenstein_polys_step (eisenstein_series_polys (n-1)) = eisenstein_series_polys n"
      by (simp add: eisenstein_series_polys_def eval_nat_numeral n_eq)
    also have "Suc (n - 1) = max 2 n"
      using True by auto
    finally show ?thesis .
  qed
qed


lemma funpow_rec_right: "n > 0 \<Longrightarrow> (f ^^ n) xs = (f ^^ (n-1)) (f xs)"
  by (cases n) (auto simp del: funpow.simps simp: funpow_Suc_right)

context complex_lattice
begin

lemma eisenstein_series_polys_correct':
  assumes "eisenstein_series_polys m = ps"
  shows   "list_all (\<lambda>i. G (2*i+4) = poly2 (map_poly2 of_rat (ps ! i)) (G 4) (G 6)) [0..<m]"
  unfolding assms [symmetric] eisenstein_series_polys_correct
  using eisenstein_series_poly_correct by (auto simp: list_all_iff)

text \<open>
  We now compute the relations up to $G_{20}$ for demonstration purposes. This could in
  principle be turned into a proof method as well.
\<close>
lemma eisenstein_series_relations:
  "G  8 = 3 / 7 * G 4 ^ 2" (is ?th8)
  "G 10 = 5 / 11 * G 4 * G 6" (is ?th10)
  "G 12 = 18 / 143 * G 4 ^ 3 + 25 / 143 * G 6 ^ 2" (is ?th12)
  "G 14 = 30 / 143 * G 4 ^ 2 * G 6" (is ?th14)
  "G 16 = 27225 / 668525 * G 4 ^ 4 + 300 / 2431 * G 4 * G 6 ^ 2" (is ?th16)
  "G 18 = 3915 / 46189 * G 4 ^ 3 * G 6 + 2750 / 92378 * G 6 ^ 3" (is ?th18)
  "G 20 = 54 / 4199 * G 4 ^ 5 + 36375 / 508079 * G 4 ^ 2 * G 6 ^ 2" (is ?th20)
proof -
  have eq: "eisenstein_series_polys 9 = 
              [[:[:0, 1:]:], [:0, [:1:]:], [:[:0, 0, 3 / 7:]:],
               [:0, [:0, 5 / 11:]:], [:[:0, 0, 0, 18 / 143:], 0, [:25 / 143:]:],
               [:0, [:0, 0, 30 / 143:]:], [:[:0, 0, 0, 0, 9 / 221:], 0, [:0, 300 / 2431:]:],
               [:0, [:0, 0, 0, 3915 / 46189:], 0, [:125 / 4199:]:],
               [:[:0, 0, 0, 0, 0, 54 / 4199:], 0, [:0, 0, 36375 / 508079:]:]]"
    by (simp add: eisenstein_series_polys_def eisenstein_polys_step_def
                  funpow_rec_right numeral_poly smult_add_right smult_diff_right flip: pCons_one)
  thus ?th8 ?th10 ?th12 ?th14 ?th16 ?th18 ?th20
    using eisenstein_series_polys_correct'[OF eq]
    by (simp_all add: upt_rec map_poly2_def of_rat_divide power_numeral_reduce field_simps)
qed

end

end
