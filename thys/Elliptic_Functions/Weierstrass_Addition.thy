section \<open>Addition and duplication theorems for $\wp$\<close>
theory Weierstrass_Addition
  imports Eisenstein_Series
begin

text \<open>
  In this section, we shall derive the addition theorem for $\wp$, and from it the duplication
  theorem. The addition theorem is:
  \[\wp(w + z) = 
      -\wp(w) - \wp(z) + \tfrac{1}{4}\left(\frac{\wp'(w)-\wp'(z)}{\wp(w)-\wp(z)}\right)^2\]
  We first prove this with the additional assumptions that $w$ and $z$ are in ``general position'',
  i.e.\ we have neither $w + 2z \in \Lambda$ nor $z + 2w \in \Lambda$.

  After that, we will drop these unnecessary assumptions using analytic continuation.
  Our proof follows Lang's presentation~\<^cite>\<open>lang\<close>.
\<close>

lemma pos_sum_eq_0_imp_empty:
  fixes f :: "'a \<Rightarrow> 'b :: ordered_comm_monoid_add"
  assumes "(\<Sum>x\<in>A. f x) = 0" "\<And>x. x \<in> A \<Longrightarrow> f x > 0" "finite A"
  shows   "A = {}"
proof (rule ccontr)
  assume "A \<noteq> {}"
  hence "(\<Sum>x\<in>A. f x) > 0"
    by (intro sum_pos) (use assms in auto)
  with assms(1) show False by simp
qed

context complex_lattice
begin

lemma weierstrass_fun_add_aux:
  assumes u12: "u1 \<notin> \<Lambda>" "u2 \<notin> \<Lambda>" "\<not>rel u1 u2" "\<not>rel u1 (-u2)"
  assumes general_position: "u1 + 2 * u2 \<notin> \<Lambda>" "2 * u1 + u2 \<notin> \<Lambda>"
  shows   "\<wp> (u1 + u2) = -\<wp> u1 - \<wp> u2 + ((\<wp>' u1 - \<wp>' u2) / (\<wp> u1 - \<wp> u2))\<^sup>2 / 4"
proof -
  note [simp] = weierstrass_fun.eval_to_fund_parallelogram 
                weierstrass_fun_deriv.eval_to_fund_parallelogram

  text \<open>
    We introduce the copies $u_1'$, $u_2'$ of $u_1$ and $u_2$ in the fundamental parallelogram
    for convenience.
  \<close>
  define u1' where "u1' = to_fund_parallelogram u1"
  define u2' where "u2' = to_fund_parallelogram u2"
  have [simp]: "u1' \<noteq> u2'" "u2' \<noteq> u1'"
    using u12 by (auto simp: u1'_def u2'_def rel_sym)

  text \<open>
    Let $a$ and $b$ be such that $(u_1, \wp(u_1))$ and $(u_2, \wp(u_2))$ lie on the line 
    $ax + b = 0$, i.e.\ such that $u_1$ and $u_2$ are both solutions of the linear equation
    $\wp'(u) = a \wp(u) + b$.
  \<close>
  define a where "a = (\<wp>' u1 - \<wp>' u2) / (\<wp> u1 - \<wp> u2)"
  define b where "b = \<wp>' u1 - a * \<wp> u1"
  have ab: "\<wp>' u1 = a * \<wp> u1 + b" "\<wp>' u2 = a * \<wp> u2 + b"
  proof -
    show "\<wp>' u1 = a * \<wp> u1 + b"
      using u12 by (auto simp: b_def)
    have "a * (\<wp> u1 - \<wp> u2) = (\<wp>' u1 - \<wp>' u2)"
      unfolding a_def using u12 by (simp add: weierstrass_fun_eq_iff)
    thus "\<wp>' u2 = a * \<wp> u2 + b"
      by (simp add: algebra_simps b_def)
  qed

  text \<open>
    We define the function $f(z) = \wp'(z) - (a\wp(z) + b)$ and note that it has a triple pole
    at the lattice points and no other poles and therefore order 3.
  \<close>
  define f where "f = remove_sings (\<lambda>z. \<wp>' z - (a * \<wp> z + b))"
  interpret f: nicely_elliptic_function \<omega>1 \<omega>2 f
    unfolding f_def by (intro elliptic_function_intros)
  note [simp] = f.zorder.eval_to_fund_parallelogram f.eval_to_fund_parallelogram
  have f_eq: "f z = \<wp>' z - (a * \<wp> z + b)" if "z \<notin> \<Lambda>" for z
    unfolding f_def by (rule remove_sings_at_analytic) (auto intro!: analytic_intros simp: that)

  have pole_f: "is_pole f z" "zorder f z = -3" if "z \<in> \<Lambda>" for z
  proof -
    define F where "F = fls_deriv fls_weierstrass - (fls_const a * fls_weierstrass + fls_const b)"
    have F: "f has_laurent_expansion F" unfolding f_def F_def
      by (intro laurent_expansion_intros)

    have "fls_nth F n = 0" if "n < -3" for n
      unfolding F_def using that by (auto simp: fls_weierstrass_def)
    moreover have "fls_nth F (-3) \<noteq> 0"
      unfolding F_def by (auto simp: fls_weierstrass_def)
    ultimately have "fls_subdegree F = -3"
      using fls_subdegree_eqI by blast
    with F have "zorder f 0 = -3" "is_pole f 0"
      using has_laurent_expansion_imp_is_pole_0 has_laurent_expansion_zorder_0 by fastforce+
    thus "is_pole f z" "zorder f z = -3"
      using f.poles.lattice_cong[of z 0] f.zorder.lattice_cong[of z 0] that
      by (simp_all add: rel_def)
  qed

  have is_pole_f_iff: "is_pole f z \<longleftrightarrow> z \<in> \<Lambda>" for z
  proof -
    have "f analytic_on -\<Lambda>"
      unfolding f_def by (intro analytic_intros remove_sings_analytic_on) auto
    with pole_f[of z] show ?thesis
      by (meson ComplI analytic_at_imp_no_pole analytic_on_analytic_at)
  qed

  have analytic_at_f: "f analytic_on {z}" if "z \<notin> \<Lambda>" for z
    unfolding f_def using that by (intro analytic_intros remove_sings_analytic_on) auto

  interpret f: nonconst_nicely_elliptic_function \<omega>1 \<omega>2 f
  proof
    have "elliptic_order f \<noteq> 0"
      using pole_f[of 0] by (subst f.elliptic_order_eq_0_iff_no_poles) auto
    thus "elliptic_order f > 0"
      by linarith
  qed

  have order_f: "elliptic_order f = 3"
  proof -
    have "elliptic_order f = (\<Sum>z | z \<in> period_parallelogram 0 \<and> is_pole f z. nat (- zorder f z))"
      by (rule f.poles_eq_elliptic_order [of 0, symmetric])
    also have "\<dots> = (\<Sum>z\<in>{0::complex}. 3)"
    proof (intro sum.cong)
      have "{z \<in> period_parallelogram 0. is_pole f z} \<subseteq> {0}"
        using fund_period_parallelogram_in_lattice_iff by (auto simp: is_pole_f_iff)
      moreover have "{0} \<subseteq> {z \<in> period_parallelogram 0. is_pole f z}"
        using pole_f[of 0] by auto
      ultimately show "{z \<in> period_parallelogram 0. is_pole f z} = {0}"
        by blast
    qed (use pole_f in auto)
    finally show ?thesis
      by simp
  qed


  text \<open>
    We now look at the zeros of $f$. We know that $u_1$ and $u_2$ are zeros.
  \<close>
  define Z where "Z = {z. z \<in> period_parallelogram 0 \<and> isolated_zero f z}"
  have "finite Z"
    unfolding Z_def by (rule f.finite_zeros_in_parallelogram)
  have in_Z_iff: "z \<in> Z \<longleftrightarrow> z \<in> period_parallelogram 0 - {0} \<and> f z = 0" for z
    by (auto simp: f.isolated_zero_iff' Z_def is_pole_f_iff fund_period_parallelogram_in_lattice_iff)

  have "{u1', u2'} \<subseteq> Z"
    using u12 ab by (auto simp: analytic_at_f is_pole_f_iff u1'_def u2'_def f_eq in_Z_iff)
  have zorder_pos: "zorder f z > 0" if "z \<in> Z" for z using that
    by (auto simp: Z_def analytic_at_f u1'_def u2'_def f.isolated_zero_iff' is_pole_f_iff
             intro!: zorder_isolated_zero_pos)
  have zorder_pos': "zorder f u1 > 0" "zorder f u2 > 0"
    using zorder_pos[of u1'] zorder_pos[of u2'] \<open>{u1', u2'} \<subseteq> Z\<close> by (auto simp: u1'_def u2'_def)

  text \<open>
    We know that the sum of the multiplicities of the zeros must be 3. We already split the sum
    into the contributions of $u_1$ and $u_2$ and those of any remaining zeros.
  \<close>
  have sum_zorder_eq:
    "nat (zorder f u1) + nat (zorder f u2) + (\<Sum>z\<in>Z-{u1',u2'}. nat (zorder f z)) = 3"
  proof -
    have "elliptic_order f = (\<Sum>z\<in>Z. nat (zorder f z))"
      unfolding Z_def by (rule f.zeros_eq_elliptic_order[of 0, symmetric])
    also have "Z = {u1', u2'} \<union> (Z - {u1', u2'})"
      using \<open>{u1', u2'} \<subseteq> Z\<close> by auto
    also have "(\<Sum>z\<in>\<dots>. nat (zorder f z)) = 
                 nat (zorder f u1) + nat (zorder f u2) + (\<Sum>z\<in>Z-{u1',u2'}. nat (zorder f z))"
      by (subst sum.union_disjoint)
         (use \<open>finite Z\<close> u12 zorder_pos' \<open>{u1', u2'} \<subseteq> Z\<close> in \<open>auto simp: u1'_def u2'_def\<close>)
    finally show ?thesis
      using order_f by simp
  qed

  text \<open>
    We also know that the sum of the zeros and poles, weighted by their multiplicity, is a lattice
    point. Since the pole is at the origin, it does not contribute anything to the sum.
  \<close>
  have sum_zeros_in_lattice:
    "of_int (zorder f u1) * u1 + of_int (zorder f u2) * u2 + 
       (\<Sum>z\<in>Z-{u1',u2'}. of_int (zorder f z) * z) \<in> \<Lambda>"
  proof -
    have "(\<Sum>z | z \<in> period_parallelogram 0 \<and> (isolated_zero f z \<or> is_pole f z). 
             of_int (zorder f z) * z) \<in> \<Lambda>"
      by (rule f.sum_zeros_poles_in_lattice[of 0])
    also have "{z. z \<in> period_parallelogram 0 \<and> (isolated_zero f z \<or> is_pole f z)} = insert 0 Z"
      using pole_f by (auto simp: Z_def fund_period_parallelogram_in_lattice_iff is_pole_f_iff)
    also have "(\<Sum>z\<in>insert 0 Z. of_int (zorder f z) * z) = (\<Sum>z\<in>Z. of_int (zorder f z) * z)"
      by (rule sum.mono_neutral_right) (use \<open>finite Z\<close> in auto)
    also have "Z = {u1',u2'} \<union> (Z-{u1',u2'})"
      using \<open>{u1', u2'} \<subseteq> Z\<close> by auto
    also have "(\<Sum>z\<in>\<dots>. of_int (zorder f z) * z) = 
                 of_int (zorder f u1) * u1' + of_int (zorder f u2) * u2' + 
                 (\<Sum>z\<in>Z-{u1',u2'}. of_int (zorder f z) * z)"
      by (subst sum.union_disjoint) 
         (use \<open>finite Z\<close> u12 zorder_pos' \<open>{u1', u2'} \<subseteq> Z\<close> in \<open>auto simp: u1'_def u2'_def\<close>)
    also have "rel (of_int (zorder f u1) * u1' + of_int (zorder f u2) * u2' + 
                     (\<Sum>z\<in>Z-{u1',u2'}. of_int (zorder f z) * z))
                   (of_int (zorder f u1) * u1 + of_int (zorder f u2) * u2 + 
                     (\<Sum>z\<in>Z-{u1',u2'}. of_int (zorder f z) * z))"
      unfolding u1'_def u2'_def by (intro lattice_intros) auto
    finally show ?thesis .
  qed

  text \<open>
    We now show that the zeros $u_1$ and $u_2$ must be simple. If they were not simple, they would
    be the only zeros and consequently we would have either $2u_1 + u_2$ or $u_1 + 2 u_2$, which
    contradicts our assumption that $u_1$ and $u_2$ are in general position.
  \<close>
  have [simp]: "zorder f u1 = 1"
  proof (rule ccontr)
    assume "zorder f u1 \<noteq> 1"
    hence [simp]: "zorder f u1 = 2" "zorder f u2 = 1"
      using sum_zorder_eq zorder_pos' \<open>{u1', u2'} \<subseteq> Z\<close>
      by (auto simp add: u1'_def u2'_def)
    have "(\<Sum>z\<in>Z-{u1',u2'}. nat (zorder f z)) = 0"
      using sum_zorder_eq by simp
    hence *: "Z-{u1',u2'} = {}"
      by (rule pos_sum_eq_0_imp_empty) (use \<open>finite Z\<close> in \<open>auto intro: zorder_pos\<close>)
    have "2 * u1 + u2 \<in> \<Lambda>"
      using sum_zeros_in_lattice unfolding * by simp
    with general_position show False by simp
  qed

  have [simp]: "zorder f u2 = 1"
  proof (rule ccontr)
    assume "zorder f u2 \<noteq> 1"
    hence [simp]: "zorder f u1 = 1" "zorder f u2 = 2"
      using sum_zorder_eq zorder_pos' \<open>{u1', u2'} \<subseteq> Z\<close>
      by (auto simp add: u1'_def u2'_def)
    have "(\<Sum>z\<in>Z-{u1',u2'}. nat (zorder f z)) = 0"
      using sum_zorder_eq by simp
    hence *: "Z-{u1',u2'} = {}"
      by (rule pos_sum_eq_0_imp_empty) (use \<open>finite Z\<close> in \<open>auto intro: zorder_pos\<close>)
    have "u1 + 2 * u2 \<in> \<Lambda>"
      using sum_zeros_in_lattice unfolding * by simp
    with general_position show False by simp
  qed


  text \<open>
    Thus we can conclude that there must be a third root $u_3$. It is simple, and there are no
    further roots.
  \<close>
  obtain u3 where u3: "u3 \<in> Z - {u1', u2'}" "zorder f u3 = 1" and Z_eq: "Z = {u1', u2', u3}"
  proof -
    have "(\<Sum>z\<in>Z - {u1', u2'}. nat (zorder f z)) = 1"
      using sum_zorder_eq by simp
    then obtain u3 where u3: "Z - {u1', u2'} = {u3}" "nat (zorder f u3) = 1"
    proof (rule sum_nat_eq_1E)
      fix u assume u: "u \<in> Z - {u1', u2'}"
      have "f analytic_on {u}"
        unfolding f_def
        by (intro analytic_intros remove_sings_analytic_on) 
           (use u in \<open>auto simp: in_Z_iff fund_period_parallelogram_in_lattice_iff\<close>)
      thus "nat (zorder f u) > 0" using u
        by (auto intro!: zorder_isolated_zero_pos simp: Z_def)
    qed auto
    show ?thesis
    proof (rule that[of u3])
      have "u1' \<in> Z" "u2' \<in> Z"
        using u12 ab by (auto simp: u1'_def u2'_def in_Z_iff f.eval_to_fund_parallelogram f_eq)
      thus "Z = {u1', u2', u3}"
        using u3(1) by blast
    qed (use u3 in auto)
  qed
  have "u3 \<notin> \<Lambda>"
    using u3(1) by (auto simp: in_Z_iff fund_period_parallelogram_in_lattice_iff)

  text \<open>
    Since the zeros sum to a lattice point, we have $u_3 \sim -(u_1 + u_2)$.
  \<close>
  have rel_u3: "rel u3 (-(u1 + u2))"
    using sum_zeros_in_lattice u3 unfolding Z_eq
    by (simp add: u1'_def u2'_def insert_Diff_if rel_def algebra_simps split: if_splits)

  text \<open>
    By definition of $f$, the fact that $u_3$ is a zero means that $(u_3, \wp(u_3))$ also lies on
    the line $ax + b = 0$.
  \<close>
  have "f u3 = 0"
    using u3 f.isolated_zero_iff[of u3] by (auto simp: Z_def)
  hence u3_ab: "\<wp>' u3 = a * \<wp> u3 + b"
    using \<open>u3 \<notin> \<Lambda>\<close> by (subst (asm) f_eq) auto

  text \<open>
    From our assumptions, it also follows that $\wp$ takes on a different value for each of
    $u_1$, $u_2$, $u_3$.
  \<close>
  have inj: "inj_on \<wp> {u1', u2', u3}"
  proof -
    have "-(u1 + u2) \<notin> \<Lambda>"
      using \<open>u3 \<notin> \<Lambda>\<close> rel_lattice_trans_right rel_u3 by blast
    have "\<wp> u1' \<noteq> \<wp> u2'"
      using u12 by (auto simp: u1'_def u2'_def weierstrass_fun_eq_iff)
    moreover have "\<wp> u1' \<noteq> \<wp> u3"
    proof
      assume "\<wp> u1' = \<wp> u3"
      hence "\<wp> u1 = \<wp> (-(u1 + u2))"
        using weierstrass_fun.lattice_cong[OF rel_u3] by (auto simp: u1'_def)
      thus False
        using u12 general_position \<open>-(u1 + u2) \<notin> \<Lambda>\<close>
        by (auto simp: weierstrass_fun_eq_iff rel_def uminus_in_lattice_iff)
    qed
    moreover have "\<wp> u2' \<noteq> \<wp> u3"
    proof
      assume "\<wp> u2' = \<wp> u3"
      hence "\<wp> u2 = \<wp> (-(u1 + u2))"
        using weierstrass_fun.lattice_cong[OF rel_u3] by (auto simp: u2'_def)
      thus False
        using u12 general_position \<open>-(u1 + u2) \<notin> \<Lambda>\<close>
        by (auto simp: weierstrass_fun_eq_iff rel_def uminus_in_lattice_iff add_ac)
    qed
    ultimately show ?thesis
      by auto
  qed

  text \<open>
    We now define the polynomial $P(X) = 4X^3 - g_2 X - g_3 - (aX - b) ^ 2$.
    Combining the fact that $u_1, u_2, u_3$ are all solutions of $\wp'(u) = a\wp(u) + b$ with the
    ODE satisfied by $\wp$, we know that $\wp(u_1), \wp(u_2), \wp(u_3)$ are roots of $P$.
    Since we also showed that the three are distinct, $P$ has no other roots.
  \<close>
  define P where "P = [: -\<g>\<^sub>3, -\<g>\<^sub>2, 0,  4 :] - [: b, a :] ^ 2"
  have P_roots: "poly P (\<wp> u) = 0" if "u \<notin> \<Lambda>" "\<wp>' u = a * \<wp> u + b" for u
  proof -
    have "poly P (\<wp> u) = 4 * \<wp> u ^ 3 - \<g>\<^sub>2 * \<wp> u - \<g>\<^sub>3 - (a * \<wp> u + b) ^ 2"
      by (simp add: P_def algebra_simps power3_eq_cube)
    also have "4 * \<wp> u ^ 3 - \<g>\<^sub>2 * \<wp> u - \<g>\<^sub>3 = \<wp>' u ^ 2"
      using that weierstrass_fun_ODE1'[of u] by simp
    also have "a * \<wp> u + b = \<wp>' u"
      using that by (simp add: algebra_simps)
    finally show ?thesis 
      by simp
  qed

  text \<open>
    Consequently, we can write $P$ in the form 
    $P(X) = 4(X - \wp(u_1))(X - \wp(u_2))(X - \wp(u_3))$.
  \<close>
  define Q where "Q = 4 * (\<Prod>u\<in>{u1',u2',u3}. [: -\<wp> u, 1 :])"

  have P_Q: "P = Q"
  proof (rule poly_eqI_degree_lead_coeff)
    have "poly.coeff P 3 = 4"
      by (simp add: P_def power2_eq_square eval_nat_numeral)
    moreover have "lead_coeff Q = 4"
      by (simp add: lead_coeff_mult lead_coeff_prod numeral_poly Q_def)
    moreover have "degree Q = 3"
      using u3 u12 by (auto simp: degree_mult_eq degree_prod_eq_sum_degree card_insert_if Q_def)
    ultimately show "poly.coeff P 3 = poly.coeff Q 3"
      by simp
  next
    show "degree P \<le> 3"
      by (rule degree_le) (auto simp: P_def eval_nat_numeral Suc_less_eq2 coeff_pCons')
  next
    show "degree Q \<le> 3"
      by (auto simp: degree_mult_eq degree_prod_eq_sum_degree card_insert_if Q_def)
  next
    show "3 \<le> card (\<wp> ` {u1', u2', u3})"
    proof -
      have "3 \<le> card {u1', u2', u3}"
        using u3 by (auto simp: card_insert_if)
      also have "\<dots> = card (\<wp> ` {u1', u2', u3})"
        using inj by (rule card_image [symmetric])
      finally show ?thesis .
    qed
  next
    show "poly P z = poly Q z" 
      if "z \<in> \<wp> ` {u1', u2', u3}" for z
    proof -
      from that obtain u where [simp]: "z = \<wp> u" and u: "u \<in> {u1', u2', u3}"
        by auto
      have "poly P (\<wp> u) = 0"
        by (rule P_roots) (use u u3 u3_ab u12 \<open>u3 \<notin> \<Lambda>\<close> ab in \<open>auto simp: u1'_def u2'_def\<close>)
      moreover have "poly Q (\<wp> u) = 0"
        using u by (auto simp: poly_prod Q_def)
      ultimately show ?thesis by simp
    qed
  qed

  text \<open>
    All that remains now is to compare the coefficient of $X^2$ in these polynomials for $X^2$ and 
    simplify.
  \<close>
  have "\<wp> (u1 + u2) = \<wp> (-(u1 + u2))"
    by (simp only: weierstrass_fun.even)
  also have "\<dots> = \<wp> u3"
    by (rule weierstrass_fun.lattice_cong) (use rel_u3 in \<open>auto simp: rel_sym\<close>)
  also have "\<dots> =  - \<wp> u1' - \<wp> u2' + a ^ 2 / 4"
  proof -
    have "poly.coeff P 2 = poly.coeff Q 2"
      by (simp only: P_Q)
    also have "poly.coeff P 2 = -a\<^sup>2"
      by (simp add: P_def power2_eq_square eval_nat_numeral)
    also have "poly.coeff Q 2 = -4 * (\<wp> u1' + \<wp> u2' + \<wp> u3)"
      using u3 by (auto simp: Q_def eval_nat_numeral numeral_poly)
    finally show ?thesis
      by (simp add: field_simps)
  qed
  finally show "\<wp> (u1 + u2) = -\<wp> u1 - \<wp> u2 + ((\<wp>' u1 - \<wp>' u2) / (\<wp> u1 - \<wp> u2))\<^sup>2 / 4"
    by (simp add: u1'_def u2'_def a_def)
qed

text \<open>
  We now use analytic continuation to get rid of the ``general position'' assumption.

  For this purpose, we regard $u_1$ as fixed and view the left-hand side and the right-hand side
  as a function of $u_2$. The set of values $u_2$ that we have to exclude is sparse, so analytic
  continuation works.
\<close>
theorem weierstrass_fun_add:
  assumes u12: "u1 \<notin> \<Lambda>" "u2 \<notin> \<Lambda>" "\<not>rel u1 u2" "\<not>rel u1 (-u2)"
  shows   "\<wp> (u1 + u2) = -\<wp> u1 - \<wp> u2 + ((\<wp>' u1 - \<wp>' u2) / (\<wp> u1 - \<wp> u2))\<^sup>2 / 4"
    (is "?lhs u2 = ?rhs u2")
proof -
  define A where "A = -(\<Lambda> \<union> {z. rel u1 z} \<union> {z. rel u1 (-z)})"
  define B where "B = A - {z. u1 + 2 * z \<in> \<Lambda>} - {z. 2 * u1 + z \<in> \<Lambda>}"

  have A_altdef: "A = UNIV - (\<Lambda> \<union> ((+) (-u1) -` \<Lambda>) \<union> ((+) u1 -` \<Lambda>))"
    by (auto simp: A_def rel_def add_ac diff_in_lattice_commute)
  have B_altdef: "B = A - (\<lambda>z. 2 * z + u1) -` \<Lambda> -  ((+) (2*u1)) -` \<Lambda>"
    unfolding B_def A_altdef by (auto simp: A_def add_ac)

  show ?thesis
  proof (rule analytic_continuation_open[where f = ?lhs and g = ?rhs])
    text \<open>
      Our set $B$ can be written as the complex plane minus some shifted and scaled copies of the
      lattice, i.e.\ an uncountable set minus a countable set. Therefore, $B$ is clearly non-empty.
    \<close>
    show "B \<noteq> {}"
    proof -
      have "B = UNIV - (\<Lambda> \<union> (+) u1 ` \<Lambda> \<union> (+) (-u1) ` \<Lambda> \<union> (\<lambda>z. 2 * z + u1) -` \<Lambda> \<union> (+) (-2*u1) ` \<Lambda>)"
        unfolding A_altdef B_altdef unfolding image_plus_conv_vimage_plus by auto
      also have "(\<lambda>z. 2 * z + u1) -` \<Lambda> = (\<lambda>z. (z - u1) / 2) ` \<Lambda>"
      proof safe
        fix z assume "2 * z + u1 \<in> \<Lambda>"
        thus "z \<in> (\<lambda>z. (z - u1) / 2) ` \<Lambda>"
          by (intro image_eqI[of _ _ "u1 + 2 * z"]) (auto simp: algebra_simps)
      qed auto
      finally have "B = UNIV - (\<Lambda> \<union> (+) u1 ` \<Lambda> \<union> (+) (-u1) ` \<Lambda> \<union> 
                                (\<lambda>z. (z - u1) / 2) ` \<Lambda> \<union> (+) (-2*u1) ` \<Lambda>)" .
      also have "uncountable \<dots>"
        by (intro uncountable_minus_countable countable_Un countable_lattice
                  countable_image uncountable_UNIV_complex)
      finally have "uncountable B" .
      thus "B \<noteq> {}"
        by auto
    qed
  next
    text \<open>
      Similarly, $A$ can be written as the complex plane minus some shifted copies of the lattice,
      i.e.\ the complement of a sparse set. Clearly, what remains is still connected.
    \<close>
    show "connected A"
    proof -
      have "(\<Lambda> \<union> (+) u1 ` \<Lambda> \<union> (+) (-u1) ` \<Lambda>) sparse_in UNIV"
        unfolding A_altdef by (intro sparse_in_union' sparse_in_translate_UNIV lattice_sparse)
      also have "\<Lambda> \<union> (+) u1 ` \<Lambda> \<union> (+) (-u1) ` \<Lambda> = \<Lambda> \<union> (+) (-u1) -` \<Lambda> \<union> (+) u1 -` \<Lambda>"
        unfolding image_plus_conv_vimage_plus by (simp add: Un_ac)
      finally have "connected (UNIV - \<dots>)"
        by (intro sparse_imp_connected) auto
      also have "\<dots> = A"
        by (auto simp: A_altdef)
      finally show "connected A" .
    qed
  next
    text \<open>
      $A$ and $B$ can both be written in the form ``the complex plane minus continuous
      deformations of the lattice''. Since the lattice is a closed set, $A$ and $B$ are open.
    \<close>
    show "open A" unfolding A_altdef
      by (intro open_Diff closed_Un closed_lattice closed_vimage continuous_intros) auto?
    show "open B" unfolding B_altdef
      by (intro open_Diff \<open>open A\<close> closed_lattice closed_vimage continuous_intros) auto?
  next
    text \<open>
      Finally, we apply the restricted version of the identity we already proved before.
    \<close>
    show "?lhs u2 = ?rhs u2" if "u2 \<in> B" for u2
      using weierstrass_fun_add_aux[of u1 u2] u12(1) that by (auto simp: A_def B_def)
  qed (use u12 in \<open>auto simp: A_def B_def intro!: holomorphic_intros simp: rel_def weierstrass_fun_eq_iff\<close>)
qed

lemma weierstrass_fun_diff:
  assumes u12: "u1 \<notin> \<Lambda>" "u2 \<notin> \<Lambda>" "\<not>rel u1 u2" "\<not>rel u1 (-u2)"
  shows   "\<wp> (u1 - u2) = -\<wp> u1 - \<wp> u2 + ((\<wp>' u1 + \<wp>' u2) / (\<wp> u1 - \<wp> u2))\<^sup>2 / 4"
proof -
  have "\<wp> (u1 + (-u2)) = -\<wp> u1 - \<wp> (- u2) + ((\<wp>' u1 + \<wp>' u2) / (\<wp> u1 - \<wp> (- u2)))\<^sup>2 / 4"
    by (subst weierstrass_fun_add) (use u12 in \<open>auto simp: uminus_in_lattice_iff\<close>)
  thus ?thesis
    by (simp add: weierstrass_fun.even)
qed
  
text \<open>
  Using the addition theorem for $\wp(z + w)$ and letting $w\to z$ gives us the duplication
  theorem: $\wp(2z) = -2\wp(z) + \frac{1}{4}(\wp''(z)/\wp'(z))^2$

  This is Exercise~1.9 in Apostol's book.
\<close>
theorem weierstrass_fun_double:
  assumes z: "2 * z \<notin> \<Lambda>"
  shows   "\<wp> (2 * z) = -2 * \<wp> z + (deriv \<wp>' z / \<wp>' z)\<^sup>2 / 4"
proof (rule tendsto_unique)
  have z': "z \<notin> \<Lambda>"
    using z by (metis assms add_in_lattice mult_2)

  show "(\<lambda>w. -\<wp> z - \<wp> w + ((\<wp>' z - \<wp>' w) / (\<wp> z - \<wp> w))\<^sup>2 / 4) \<midarrow>z\<rightarrow> \<wp> (2 * z)"
  proof (rule Lim_transform_eventually)
    show "(\<lambda>w. \<wp> (z + w)) \<midarrow>z\<rightarrow> \<wp> (2 * z)"
      by (rule tendsto_eq_intros refl)+ (use z in auto)
  next
    have "eventually (\<lambda>w. w \<in> -(\<Lambda> \<union> (+) z -` \<Lambda> \<union> (+) (-z) -` (\<Lambda>-{0})) - {z}) (at z)"
      using z z' by (intro eventually_at_in_open open_Compl closed_Un closed_vimage
                           closed_subset_lattice) (auto intro!: continuous_intros)
    thus "eventually (\<lambda>w. \<wp> (z + w) = -\<wp> z - \<wp> w + ((\<wp>' z - \<wp>' w) / (\<wp> z - \<wp> w))\<^sup>2 / 4) (at z)"
    proof eventually_elim
      case (elim w)
      show ?case
        by (subst weierstrass_fun_add) (use z' elim in \<open>auto simp: rel_def diff_in_lattice_commute\<close>)
    qed
  qed

  show "(\<lambda>w. -\<wp> z - \<wp> w + ((\<wp>' z - \<wp>' w) / (\<wp> z - \<wp> w))\<^sup>2 / 4) \<midarrow>z\<rightarrow> 
          -2 * \<wp> z + (deriv \<wp>' z / \<wp>' z) ^ 2 / 4"
  proof -
    have *: "(\<lambda>w. (\<wp>' z - \<wp>' w) / (\<wp> z - \<wp> w)) \<midarrow>z\<rightarrow> (-deriv \<wp>' z) / (-\<wp>' z)"
      by (rule lhopital_complex_simple[OF _ _ _ _ _ refl])
        (use z z' in \<open>auto simp: weierstrass_fun_deriv_eq_0_iff weierstrass_fun_ODE2 
                           intro!: derivative_eq_intros\<close>)
    have "(\<lambda>w. -\<wp> z - \<wp> w + ((\<wp>' z - \<wp>' w) / (\<wp> z - \<wp> w))\<^sup>2 / 4)
                 \<midarrow>z\<rightarrow> -\<wp> z - \<wp> z + ((-deriv \<wp>' z) / (-\<wp>' z)) ^ 2 / 4"
      by (rule * tendsto_intros z')+ auto
    thus ?thesis
      by simp
  qed
qed auto

end

end