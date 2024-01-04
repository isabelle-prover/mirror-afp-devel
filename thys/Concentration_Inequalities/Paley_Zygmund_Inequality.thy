section \<open>Paley-Zygmund Inequality\<close>

text \<open>This section proves slight improvements of the Paley-Zygmund Inequality~\cite{paley1932note}.
Unfortunately, the improvements are on Wikipedia with no citation.\<close>

theory Paley_Zygmund_Inequality
  imports Lp.Lp
begin

context prob_space
begin

theorem paley_zygmund_inequality_holder:
  assumes p: "1 < (p::real)"
  assumes rv: "random_variable borel Z"
  assumes intZp: "integrable M (\<lambda>z. \<bar>Z z\<bar> powr p)"
  assumes t: "\<theta> \<le> 1"
  assumes ZAEpos: "AE z in M. Z z \<ge> 0"
  shows "
    (expectation (\<lambda>x. \<bar>Z x - \<theta> * expectation Z\<bar> powr p) powr (1 / (p-1))) *
    prob {z \<in> space M. Z z > \<theta> * expectation Z}
      \<ge> ((1-\<theta>) powr (p / (p-1)) * expectation Z powr (p / (p-1))) "
proof -
  have intZ: "integrable M Z"
    apply (subst bound_L1_Lp[OF _ rv intZp])
    using p by auto

  define eZ where "eZ = expectation Z"
  have "eZ \<ge> 0"
    unfolding eZ_def
    using ZAEpos intZ integral_ge_const prob_Collect_eq_1 by auto

  have ezp: "expectation (\<lambda>x. \<bar>Z x - \<theta> * eZ\<bar> powr p) \<ge> 0"
    by (meson Bochner_Integration.integral_nonneg powr_ge_pzero)

  have "expectation (\<lambda>z. Z z - \<theta> * eZ) = expectation (\<lambda>z. Z z + (- \<theta> * eZ))"
    by auto
  moreover have "... = expectation Z + expectation (\<lambda>z. - \<theta> * eZ)"
    apply (subst Bochner_Integration.integral_add)
    using intZ by auto
  moreover have "... = eZ + (- \<theta> * eZ)"
    apply (subst lebesgue_integral_const)
    using eZ_def prob_space by auto
  ultimately have *: "expectation (\<lambda>z. Z z - \<theta> * eZ) = eZ - \<theta> * eZ"
    by linarith

  have ev: "{z \<in> space M. \<theta> * eZ < Z z} \<in> events"
    using rv unfolding borel_measurable_iff_greater
    by auto

  define q where "q = p / (p-1)"

  have sqI:"(indicat_real E x) powr q = indicat_real E (x::'a)" for E x
    unfolding q_def
    by (metis indicator_simps(1) indicator_simps(2) powr_0 powr_one_eq_one)

  have bm1: "(\<lambda>z. (Z z - \<theta> * eZ)) \<in> borel_measurable M"
    using borel_measurable_const borel_measurable_diff rv by blast
  have bm2: "(\<lambda>z. indicat_real {z \<in> space M. Z z > \<theta> * eZ} z) \<in> borel_measurable M"
    using borel_measurable_indicator ev by blast
  have "integrable M (\<lambda>x. \<bar>Z x + (-\<theta> * eZ)\<bar> powr p)"
    apply (intro Minkowski_inequality[OF _ rv _ intZp])
    using p by auto
  then have int1: "integrable M (\<lambda>x. \<bar>Z x - \<theta> * eZ\<bar> powr p)"
     by auto

  have "integrable M
   (\<lambda>x. 1 * indicat_real {z \<in> space M. \<theta> * eZ < Z z} x)"
    apply (intro integrable_real_mult_indicator[OF ev])
    by auto

  then have int2: " integrable M
     (\<lambda>x. \<bar>indicat_real {z \<in> space M. \<theta> * eZ < Z z} x\<bar> powr q)"
     by (auto simp add: sqI )

  have pq:"p > (0::real)" "q > 0" "1/p + 1/q = 1"
    unfolding q_def using p by (auto simp:divide_simps)
  from Holder_inequality[OF pq bm1 bm2 int1 int2]
  have hi: "expectation (\<lambda>x. (Z x - \<theta> * eZ) * indicat_real {z \<in> space M. \<theta> * eZ < Z z} x)
    \<le> expectation (\<lambda>x. \<bar>Z x - \<theta> * eZ\<bar> powr p) powr (1 / p) *
      expectation (\<lambda>x. \<bar>indicat_real {z \<in> space M. \<theta> * eZ < Z z} x\<bar> powr q) powr (1 / q)"
    by auto

  have "eZ - \<theta> * eZ \<le>
    expectation (\<lambda>z. (Z z - \<theta> * eZ) * indicat_real {z \<in> space M. Z z > \<theta> * eZ} z)"
    unfolding *[symmetric]
    apply (intro integral_mono)
    using intZ ev apply auto[1]
    apply (auto intro!: integrable_real_mult_indicator simp add: intZ ev)[1]
    unfolding indicator_def of_bool_def
    by (auto simp add: mult_nonneg_nonpos2)

  also have "... \<le>
      expectation (\<lambda>x. \<bar>Z x - \<theta> * eZ\<bar> powr p) powr (1 / p) *
      expectation (\<lambda>x. indicat_real {z \<in> space M. \<theta> * eZ < Z z} x) powr (1 / q)"
    using hi by (auto simp add: sqI)

  finally have "eZ - \<theta> * eZ \<le>
     expectation (\<lambda>x. \<bar>Z x - \<theta> * eZ\<bar> powr p) powr (1 / p) *
     expectation (\<lambda>x. indicat_real {z \<in> space M. \<theta> * eZ < Z z} x) powr (1 / q)"
    by auto

  then have "(eZ - \<theta> * eZ) powr q \<le>
     (expectation (\<lambda>x. \<bar>Z x - \<theta> * eZ\<bar> powr p) powr (1 / p) *
     expectation (\<lambda>x. indicat_real {z \<in> space M. \<theta> * eZ < Z z} x) powr (1 / q)) powr q"
    by (smt (verit, ccfv_SIG) \<open>0 \<le> eZ\<close> mult_left_le_one_le powr_mono2 pq(2) right_diff_distrib' t zero_le_mult_iff)

  also have "... =
     (expectation (\<lambda>x. \<bar>Z x - \<theta> * eZ\<bar> powr p) powr (1 / p)) powr q *
     (expectation (\<lambda>x. indicat_real {z \<in> space M. \<theta> * eZ < Z z} x) powr (1 / q)) powr q"
    using powr_ge_pzero powr_mult by presburger
  also have "... =
     (expectation (\<lambda>x. \<bar>Z x - \<theta> * eZ\<bar> powr p) powr (1 / p)) powr q *
     (expectation (\<lambda>x. indicat_real {z \<in> space M. \<theta> * eZ < Z z} x))"
    by (smt (verit, ccfv_SIG) Bochner_Integration.integral_nonneg divide_le_eq_1_pos indicator_pos_le nonzero_eq_divide_eq p powr_one powr_powr q_def)
  also have "... =
     (expectation (\<lambda>x. \<bar>Z x - \<theta> * eZ\<bar> powr p) powr (1 / (p-1))) *
     (expectation (\<lambda>x. indicat_real {z \<in> space M. \<theta> * eZ < Z z} x))"
   by (smt (verit, ccfv_threshold) divide_divide_eq_right divide_self_if p powr_powr q_def times_divide_eq_left)
  also have "... =
     (expectation (\<lambda>x. \<bar>Z x - \<theta> * eZ\<bar> powr p) powr (1 / (p-1))) *
     prob {z \<in> space M. Z z > \<theta> * eZ}"
    by (simp add: ev)

  finally have 1: "(eZ - \<theta> * eZ) powr q \<le>
     (expectation (\<lambda>x. \<bar>Z x - \<theta> * eZ\<bar> powr p) powr (1 / (p-1))) *
     prob {z \<in> space M. Z z > \<theta> * eZ}" by linarith

  have "(eZ - \<theta> * eZ) powr q = ((1 - \<theta>) * eZ) powr q"
    by (simp add: mult.commute right_diff_distrib)
  also have "... = (1 - \<theta>) powr q * eZ powr q"
    by (simp add: \<open>0 \<le> eZ\<close> powr_mult t)
  finally show ?thesis using 1 eZ_def q_def by force
qed

corollary paley_zygmund_inequality:
  assumes rv: "random_variable borel Z"
  assumes intZsq: "integrable M (\<lambda>z. (Z z)^2)"
  assumes t: "\<theta> \<le> 1"
  assumes Zpos: "\<And>z. z \<in> space M \<Longrightarrow> Z z \<ge> 0"
  shows "
    (variance Z + (1-\<theta>)^2 * (expectation Z)^2) *
    prob {z \<in> space M. Z z > \<theta> * expectation Z}
      \<ge> (1-\<theta>)^2 * (expectation Z)^2"
proof -
  have ZAEpos: "AE z in M. Z z \<ge> 0"
    by (simp add: Zpos)

  define p where "p = (2::real)"
  have p1: "1 < p" using p_def by auto
  have " integrable M (\<lambda>z. \<bar>Z z\<bar> powr p)" unfolding p_def
    using intZsq by auto

  from paley_zygmund_inequality_holder[OF p1 rv this t ZAEpos]
  have "(1 - \<theta>) powr (p / (p - 1)) * (expectation Z powr (p / (p - 1)))
    \<le> expectation (\<lambda>x. \<bar>Z x - \<theta> * expectation Z\<bar> powr p) powr (1 / (p - 1)) *
       prob {z \<in> space M.  \<theta> * expectation Z < Z z}" .

  then have hi: "(1 - \<theta>)^2 * (expectation Z)^2
    \<le> expectation (\<lambda>x. (Z x - \<theta> * expectation Z)^2) *
       prob {z \<in> space M.  \<theta> * expectation Z < Z z}"
    unfolding p_def by (auto simp add: Zpos t)

  have intZ: "integrable M Z"
    apply (subst square_integrable_imp_integrable[OF rv intZsq])
    by auto

  define eZ where "eZ = expectation Z"
  have "eZ \<ge> 0"
    unfolding eZ_def
    using Bochner_Integration.integral_nonneg Zpos by blast

  have ezp: "expectation (\<lambda>x. \<bar>Z x - \<theta> * eZ\<bar> powr p) \<ge> 0"
    by (meson Bochner_Integration.integral_nonneg powr_ge_pzero)

  have "expectation (\<lambda>z. Z z - \<theta> * eZ) = expectation (\<lambda>z. Z z + (- \<theta> * eZ))"
    by auto
  also have "... = expectation Z + expectation (\<lambda>z. - \<theta> * eZ)"
    apply (subst Bochner_Integration.integral_add)
    using intZ by auto
  also have "... = eZ + (- \<theta> * eZ)"
    apply (subst lebesgue_integral_const)
    using eZ_def prob_space by auto
  finally have *: "expectation (\<lambda>z. Z z - \<theta> * eZ) = eZ - \<theta> * eZ"
    by linarith
  have "variance Z =
     variance (\<lambda>z. (Z z - \<theta> * eZ))"
    using "*" eZ_def by auto
  also have "... =
    expectation (\<lambda>z. (Z z - \<theta> * eZ)^2)
    - (expectation (\<lambda>x. Z x - \<theta> * eZ))\<^sup>2"
    apply (subst variance_eq)
    by (auto simp add: intZ power2_diff intZsq)
  also have "... = expectation (\<lambda>z. (Z z - \<theta> * eZ)^2) - ((1-\<theta>)^2 * eZ^2)"
    unfolding * by (auto simp:algebra_simps power2_eq_square)
  finally have veq: "expectation (\<lambda>z. (Z z - \<theta> * eZ)^2) = (variance Z + (1-\<theta>)^2 * eZ^2)"
    by linarith
  thus ?thesis
    using hi by (simp add: eZ_def)
qed

end

end