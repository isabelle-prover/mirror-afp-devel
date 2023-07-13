theory EC_Common
  imports
    "Elliptic_Curves_Group_Law.Elliptic_Test"
    "More_Residues"
begin

section \<open>Edits to Elliptic_Test\<close>
text \<open>There are a few edits we need to make to the AFP entry we build on here.  First there
are several variables defined in its last section that we need to ignore.  In particular, we want
to ignore the definitions of "m", "a", etc. so that we can use those names otherwise.  To be
entirely safe, and because we don't use these definitions anywhere, we scrub them entirely.\<close>

hide_const Elliptic_Test.m
hide_fact  Elliptic_Test.m_def
hide_const Elliptic_Test.a
hide_fact  Elliptic_Test.a_def
hide_const Elliptic_Test.b
hide_fact  Elliptic_Test.b_def
hide_const Elliptic_Test.gx
hide_fact  Elliptic_Test.gx_def
hide_const Elliptic_Test.gy
hide_fact  Elliptic_Test.gy_def
hide_const Elliptic_Test.priv
hide_fact  Elliptic_Test.priv_def
hide_const Elliptic_Test.pubx
hide_fact  Elliptic_Test.pubx_def
hide_const Elliptic_Test.puby
hide_fact  Elliptic_Test.puby_def
hide_const Elliptic_Test.order
hide_fact  Elliptic_Test.order_def

text \<open>The second thing we need to "edit" is this.  We need to be able to use this lemma for
checking test vectors.  So we need it to be designated with [code].\<close>
lemmas (in residues_prime_gt2) [code] = on_curve_residues_eq


section \<open>EC_Common\<close>
text \<open>This section has facts about the arithmetic of points on an elliptic curve.\<close>

lemma (in euclidean_semiring_cancel) mod_pow_cong:
  "a mod c = b mod c \<Longrightarrow> (a ^ n) mod c = (b ^ n) mod c"
  by (induction n) (auto intro!: mod_mult_cong)

declare (in domain)    integral_iff[simp]
declare (in field)      divide_self[simp]
declare (in field)  divide_eq_0_iff[simp]

lemma (in cring) power2_sum:
  assumes [simp]: "x \<in> carrier R"  "y \<in> carrier R"
  shows   "(x \<oplus> y)[^](2::nat) = x[^](2::nat) \<oplus> y[^](2::nat) \<oplus> \<guillemotleft>2\<guillemotright> \<otimes> x \<otimes> y"
proof -
  have 1: "(2::int) = 1 + 1" by arith
  have 2: "\<guillemotleft>2\<guillemotright> = \<one> \<oplus> \<one>" unfolding 1 of_int_add by simp
  show ?thesis
    by (simp add: power2_eq_square 2 minus_eq l_distr r_distr a_ac m_ac minus_add r_minus)
qed

lemma (in ring) diff_same[simp]: "a \<in> carrier R \<Longrightarrow> a \<ominus> a = \<zero>"
  using eq_diff0 by force

lemma (in cring) power2_diff:
  assumes [simp]: "x \<in> carrier R"  "y \<in> carrier R"
  shows   "(x \<ominus> y)[^](2::nat) = x[^](2::nat) \<oplus> y[^](2::nat) \<ominus> \<guillemotleft>2\<guillemotright> \<otimes> x \<otimes> y"
proof -
  have 1: "(2::int) = 1 + 1" by arith
  have 2: "\<guillemotleft>2\<guillemotright> = \<one> \<oplus> \<one>"
    unfolding 1 of_int_add by simp
  show ?thesis
    by (simp add: power2_eq_square 2 minus_eq l_distr r_distr a_ac m_ac minus_add r_minus)
qed

lemma (in ring) power3_eq_cube:
  "x \<in> carrier R \<Longrightarrow> x[^]\<^bsub>R\<^esub>(3::nat) = x \<otimes>\<^bsub>R\<^esub> x \<otimes>\<^bsub>R\<^esub> x"
  by (simp add: numeral_3_eq_3)

lemma (in ring) zero_pow_nat[simp]: "n \<noteq> 0 \<Longrightarrow> \<zero>\<^bsub>R\<^esub> [^]\<^bsub>R\<^esub> (n::nat) = \<zero>\<^bsub>R\<^esub>"
  using nat_pow_zero by blast

lemma (in comm_group) m_one_iff: "p \<in> carrier G \<Longrightarrow> q \<in> carrier G \<Longrightarrow> p \<otimes> q = \<one> \<longleftrightarrow> p = inv q"
  using local.inv_equality by auto

lemma (in residues) res_diff_eq: "x \<ominus> y = (x - y) mod m"
  unfolding a_minus_def diff_conv_add_uminus res_neg_eq res_add_eq by (simp add: mod_simps)

lemma (in field) nonzero_mult_divide_mult_cancel_left' [simp]:
  assumes [simp]: "a \<in> carrier R"  "b \<in> carrier R"  "c \<in> carrier R"  "b \<noteq> \<zero>"  "c \<noteq> \<zero>"
  shows   "(a \<otimes> c) \<oslash> (b \<otimes> c) = a \<oslash> b"
  by (subst (1 2) m_comm) simp_all

lemma (in field) nonzero_mult_divide_divide_cancel_left [simp]:
  assumes [simp]: "a \<in> carrier R"  "b \<in> carrier R"  "c \<in> carrier R"  "b \<noteq> \<zero>"  "c \<noteq> \<zero>"
  shows   "(a \<oslash> c) \<oslash> (b \<oslash> c) = a \<oslash> b"
  by (subst (1 3) m_div_def) (simp add: nonzero_imp_inverse_nonzero)

lemma (in field) l_diff_distr:
  "x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> z \<in> carrier R \<Longrightarrow> (x \<ominus> y) \<otimes> z = x \<otimes> z \<ominus> y \<otimes> z"
  using r_diff_distr[of x y z] by (simp add: m_ac)

lemma (in field) l_diff_div_distr:
  "x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> z \<in> carrier R \<Longrightarrow> (x \<ominus> y) \<oslash> z = (x \<oslash> z) \<ominus> (y \<oslash> z)"
  by (auto simp: m_div_def l_diff_distr)

lemma (in field) of_natural_nat_pow: "\<guillemotleft>n\<guillemotright>\<^sub>\<nat> [^] (p::nat) = \<guillemotleft>n^p\<guillemotright>\<^sub>\<nat>"
  by (induction p) (auto simp: m_ac)

lemma (in field) of_integer_int[simp]: "\<guillemotleft>int n\<guillemotright> = \<guillemotleft>n\<guillemotright>\<^sub>\<nat>"
  by (induction n) auto

lemma (in field) of_integer_numeral: "\<guillemotleft>numeral n\<guillemotright> = \<guillemotleft>numeral n\<guillemotright>\<^sub>\<nat>"
  apply (subst semiring_1_class.of_nat_numeral[symmetric])
  apply (subst of_integer_int)
  ..

lemma (in field) divide_mult_comm:
  "a \<in> carrier R \<Longrightarrow> b \<in> carrier R \<Longrightarrow> c \<in> carrier R \<Longrightarrow> b \<noteq> \<zero> \<Longrightarrow> (a \<oslash> b) \<otimes> c = a \<otimes> (c \<oslash> b)"
  by (subst times_divide_eq_left) (auto simp flip: times_divide_eq_right)

lemma (in field) div_cancel:
  assumes [simp]: "a \<in> carrier R"  "b \<in> carrier R"  "c \<in> carrier R"  "c \<noteq> \<zero>"
  shows   "a \<oslash> c = b \<oslash> c \<longleftrightarrow> a = b"
proof
  assume "a \<oslash> c = b \<oslash> c"
  then have "(a \<oslash> c) \<oslash> inv c  = (b \<oslash> c) \<oslash> inv c"
    by simp
  then show "a = b"
    by (subst (asm) (1 2) nonzero_divide_divide_eq_left)
       (auto simp: nonzero_imp_inverse_nonzero)
qed simp

lemma (in group) pow_dbl_eq_pow_of_prime_ord_gt_2:
  "e \<in> carrier G \<Longrightarrow> prime (ord e) \<Longrightarrow> ord e > 2 \<Longrightarrow> e [^] (2 * n :: nat) = \<one> \<longleftrightarrow> e [^] n = \<one>"
  by (subst (1 2) pow_eq_id)
     (auto simp: prime_dvd_mult_nat)

lemma (in ring) add_eq_iff_eq_minus:
  "a \<in> carrier R \<Longrightarrow> b \<in> carrier R \<Longrightarrow> c \<in> carrier R \<Longrightarrow> a \<oplus> b = c \<longleftrightarrow> a = c \<ominus> b"
  by (metis a_minus_def add.inv_solve_right)

lemma (in field) mult_eq_iff_eq_divide:
  "a \<in> carrier R \<Longrightarrow> b \<in> carrier R \<Longrightarrow> c \<in> carrier R \<Longrightarrow> b \<noteq> \<zero> \<Longrightarrow> a \<otimes> b = c \<longleftrightarrow> a = c \<oslash> b"
  by (metis (full_types) cring_simprules(14) div_closed divide_mult_comm l_one 
        local.divide_self m_lcancel)

lemma (in field) eq_mult_iff_divide_eq:
  "a \<in> carrier R \<Longrightarrow> b \<in> carrier R \<Longrightarrow> c \<in> carrier R \<Longrightarrow> b \<noteq> \<zero> \<Longrightarrow> c = a \<otimes> b \<longleftrightarrow> c \<oslash> b = a"
  by (metis mult_eq_iff_eq_divide)

lemma (in cring) r_distr_diff:
  assumes "x \<in> carrier R" "y \<in> carrier R" "z \<in> carrier R"
  shows   "x \<otimes> (y \<ominus> z) = x \<otimes> y \<ominus> x \<otimes> z"
  using assms by (simp add: cring.cring_simprules(15) is_cring r_distr r_minus)

lemma (in field) divide_eq_divide_iff_mult_eq_mult:
  assumes [simp]: "x \<in> carrier R" "y \<in> carrier R" "z \<in> carrier R" "w \<in> carrier R" "y \<noteq> \<zero>" "w \<noteq> \<zero>"
  shows   "x \<oslash> y = z \<oslash> w \<longleftrightarrow> x \<otimes> w = z \<otimes> y"
  by (simp add: mult_eq_iff_eq_divide flip: eq_mult_iff_divide_eq)

lemma (in field) inv_pow_distr:
  assumes "x \<in> carrier R"  "x \<noteq> \<zero>"
  shows   "inv (x[^](k::nat)) = (inv x)[^]k"
  by (metis assms comm_inv_char inv_closed nat_pow_closed nat_pow_one r_inv nat_pow_distrib)

lemma (in field) inv_Suc_pow_cancel:
  assumes "x \<in> carrier R"  "x \<noteq> \<zero>"
  shows   "x \<otimes> (inv x)[^](Suc (k::nat)) = (inv x)[^]k"
  using assms r_inv nat_pow_Suc m_lcomm by fastforce

lemma (in ell_field) xz_coord_padd_simp:
  assumes "on_curvep a b (x1, y1, z)"
    and   "on_curvep a b (x2, y2, z)"
    and   "(x3, y3, z3) = padd a (x1, y1, z) (x2, y2, z)"
    and   ab_in_carrier[simp]: "a \<in> carrier R" "b \<in> carrier R"
    and   "(x2 \<ominus> x1) \<otimes> z \<noteq> \<zero>"
  shows   "x3 = (x2 \<ominus> x1) \<otimes> z[^](4::nat) \<otimes> ((x1 \<otimes> x2 \<oplus> a \<otimes> z[^](2::nat)) 
              \<otimes> (x1 \<oplus> x2) \<oplus> \<guillemotleft>2\<guillemotright> \<otimes> b \<otimes> z[^](3::nat) \<ominus> \<guillemotleft>2\<guillemotright> \<otimes> y1 \<otimes> y2 \<otimes> z)
         \<and> z3 = (x2 \<ominus> x1)[^](3::nat) \<otimes> z[^](5::nat)"
proof -
  define u where "u = x2 \<otimes> z \<ominus> x1 \<otimes> z"
  have carrier: "x1 \<in> carrier R" "y1 \<in> carrier R" "x2 \<in> carrier R" "y2 \<in> carrier R" "z \<in> carrier R"
    using assms(1) assms(2) unfolding on_curvep_def by blast+
  then have z_nz: "z \<noteq> \<zero>" using assms(1) assms(6) domain.integral_iff
    unfolding on_curvep_def by force
  have u_nz: "u \<noteq> \<zero>" using assms(1) assms(6) carrier u_def unfolding on_curvep_def
    by (simp add: cring_axioms cring.cring_simprules(14) cring.r_distr_diff)
  have [simp]: "in_carrierp (x1, y1, z)" "in_carrierp (x2, y2, z)"
     using assms(1) assms(2) on_curvep_imp_in_carrierp by blast+
  then have on_curvep3: "on_curvep a b (x3, y3, z3)"
     by (simp add: assms(3) padd_closed assms(1) assms(2))
  then have carrier3: "x3 \<in> carrier R" "y3 \<in> carrier R" "z3 \<in> carrier R"
    using on_curvep_imp_in_carrierp in_carrierp_def by auto
  have p1_ec_eqn: "y1[^](2::nat) \<otimes> z = x1[^](3::nat) \<oplus> a \<otimes> x1 \<otimes> z[^](2::nat) \<oplus> b \<otimes> z[^](3::nat)"
    using assms(1) z_nz prod_cases3 carrier unfolding on_curvep_def by (auto split: prod.splits)
  have p2_ec_eqn: "y2[^](2::nat) \<otimes> z = x2[^](3::nat) \<oplus> a \<otimes> x2 \<otimes> z[^](2::nat) \<oplus> b \<otimes> z[^](3::nat)"
    using assms(2) z_nz prod_cases3 unfolding on_curvep_def by (auto split: prod.splits)
  have z3: "z3 = (x2 \<ominus> x1)[^](3::nat) \<otimes> z[^](5::nat)"
    using assms(3) u_nz z_nz carrier padd_def p1_ec_eqn p2_ec_eqn unfolding u_def Let_def
    by (auto split: prod.splits, field, simp)
  have x3: "x3 = (x2 \<ominus> x1) \<otimes> z[^](4::nat) \<otimes> ((y2[^](2::nat) \<otimes> z)
        \<oplus> (y1[^](2::nat) \<otimes> z) \<ominus> \<guillemotleft>2\<guillemotright> \<otimes> y1 \<otimes> y2 \<otimes> z \<ominus> (x1 \<oplus> x2) \<otimes> (x2 \<ominus> x1)[^](2::nat))"
    using assms(3) u_nz z_nz carrier padd_def unfolding u_def Let_def
    by (auto split: prod.splits, field, simp)
  then have x3': "\<dots> = (x2 \<ominus> x1) \<otimes> z[^](4::nat)
    \<otimes> ((x1 \<otimes> x2 \<oplus> a \<otimes> z[^](2::nat)) \<otimes> (x1 \<oplus> x2) \<oplus> \<guillemotleft>2\<guillemotright> \<otimes> b \<otimes> z[^](3::nat) \<ominus> \<guillemotleft>2\<guillemotright> \<otimes> y1 \<otimes> y2 \<otimes> z)"
    apply (subst p1_ec_eqn, subst p2_ec_eqn) using carrier ab_in_carrier by (field, simp)
  then show ?thesis using x3 x3' z3 by simp
qed

lemma (in ell_field) pdouble_remove_y_eqn:
  assumes on_curvep: "on_curvep \<guillemotleft>-3\<guillemotright> b (x, y, z)"
    and   [simp]: "b \<in> carrier R"  "z \<noteq> \<zero>"  "y \<noteq> \<zero>"
    and   double: "Point qx qy = make_affine (pdouble \<guillemotleft>-3\<guillemotright> (x, y, z))"
  shows   "qx \<otimes> (\<guillemotleft>2\<guillemotright> \<otimes> y \<otimes> z) [^](2::nat) = 
           (x [^](2::nat) \<oplus> \<guillemotleft>3\<guillemotright> \<otimes> z [^](2::nat)) [^](2::nat) \<ominus> \<guillemotleft>8\<guillemotright> \<otimes> b \<otimes> x \<otimes> z [^](3::nat)"
proof -
  have in_carrierp[simp]: "x \<in> carrier R"  "y \<in> carrier R"  "z \<in> carrier R"
    using assms(1) on_curvep unfolding on_curvep_def by fast+
  then have "on_curve \<guillemotleft>-3\<guillemotright> b (Point qx qy)"
    using on_curvep double pdouble_closed assms(1) assms(2) assms(3) on_curvep_iff_on_curve
      of_int_closed pdouble_in_carrierp in_carrierp on_curvep_imp_in_carrierp by metis
  define l where "l = \<guillemotleft>2\<guillemotright> \<otimes> y \<otimes> z"
  define m where "m = \<guillemotleft>3\<guillemotright> \<otimes> x [^] (2::nat) \<oplus> \<guillemotleft>-3\<guillemotright> \<otimes> z[^](2::nat)"
  define t where "t = inv (l[^](3::nat))"
  have 0: "l \<noteq> \<zero>" by (simp add: l_def)
  have 1: "l[^](3::nat) \<noteq> \<zero>" by (simp add: l_def)
  then have 2: "t \<otimes> l \<otimes> l[^](2::nat) = \<one>" using t_def l_def
    by (simp add: m_assoc numeral_2_eq_2 numeral_3_eq_3)
  have [simp]: "l \<in> carrier R" "t \<in> carrier R" "m \<in> carrier R"
    using l_def inv_closed l_def m_def t_def m_closed a_closed nat_pow_closed 1 by auto
  then have 3: "qx = (m[^](2::nat) \<ominus> \<guillemotleft>4\<guillemotright> \<otimes> x \<otimes> y \<otimes> l) \<otimes> t \<otimes> l"
    using assms(3) assms(4) double in_carrierp m_comm int_pow_int 0 1 m_div_def t_def
    unfolding make_affine_def pdouble_def Let_def l_def m_def by (simp add: 0 1 m_div_def m_ac)
  then have 4: "qx \<otimes> l[^](2::nat) = m[^](2::nat) \<ominus> \<guillemotleft>4\<guillemotright> \<otimes> x \<otimes> y \<otimes> l" using 2
    by (simp add: 2 m_assoc numeral_2_eq_2 numeral_3_eq_3)
  have 4: "y[^](2::nat) \<otimes> z = x[^](3::nat) \<oplus> \<guillemotleft>-3\<guillemotright> \<otimes> x \<otimes> z[^](2::nat) \<oplus> b \<otimes> z[^](3::nat)"
    using assms unfolding on_curvep_def by fast
  then have 5: "m[^](2::nat) \<ominus> \<guillemotleft>4\<guillemotright> \<otimes> x \<otimes> y \<otimes> l =
               (x[^](2::nat) \<oplus> \<guillemotleft>3\<guillemotright> \<otimes> z[^](2::nat))[^](2::nat) \<ominus> \<guillemotleft>8\<guillemotright> \<otimes> b \<otimes> x \<otimes> z[^](3::nat)"
    unfolding m_def l_def apply (field 4) by (rule TrueI)
  then show ?thesis using 4 l_def 2 3 m_assoc by auto
qed

lemma (in cring) on_curvep_nz:
  "\<lbrakk>on_curvep a b (x, y, z); z \<noteq> \<zero>\<rbrakk> \<Longrightarrow>
      y [^] (2::nat) \<otimes> z = x [^] (3::nat) \<oplus> a \<otimes> x \<otimes> z [^] (2::nat) \<oplus> b \<otimes> z [^] (3::nat)"
  by (simp add: on_curvep_def)

lemma (in field) on_curvep_nz_identity:
  assumes "on_curvep a b (x, y, z)"  "z \<noteq> \<zero>"  "a \<in> carrier R"  "b \<in> carrier R"
  shows   "(\<guillemotleft>4\<guillemotright> \<otimes> x \<otimes> (x[^](2::nat) \<oplus> a \<otimes> z[^](2::nat)) \<oplus> \<guillemotleft>4\<guillemotright> \<otimes> b \<otimes> z[^](3::nat)) \<otimes> z =
           (\<guillemotleft>2\<guillemotright> \<otimes> y \<otimes> z)[^](2::nat)"
proof -
  have x: "x \<in> carrier R" "y \<in> carrier R" "z \<in> carrier R" 
    using assms(1) on_curvep_def by simp_all
  have 0: "x [^] (3::nat) \<oplus> a \<otimes> x \<otimes> z [^] (2::nat) \<oplus> b \<otimes> z [^] (3::nat) = y [^] (2::nat) \<otimes> z"
    using assms on_curvep_nz by simp
  have 1: "(\<guillemotleft>4\<guillemotright> \<otimes> x \<otimes> (x[^](2::nat) \<oplus> a \<otimes> z[^](2::nat)) \<oplus> \<guillemotleft>4\<guillemotright> \<otimes> b \<otimes> z[^](3::nat)) \<otimes> z =
           \<guillemotleft>4\<guillemotright> \<otimes> (x[^](3::nat) \<oplus> a \<otimes> x \<otimes> z[^](2::nat) \<oplus> b \<otimes> z[^](3::nat)) \<otimes> z"
    by (field, simp)
  have 2: "\<dots> = \<guillemotleft>4\<guillemotright> \<otimes> y [^] (2::nat) \<otimes> z \<otimes> z" by (simp add: 0 x m_assoc)
  show ?thesis using assms x by (simp add: 1 2, field, simp)
qed

lemma (in residues_prime) res_inv_mult:
  assumes "z \<noteq> 0"  "z \<in> carrier R"
    shows "z ^ (p - 2) * z mod p = (inv z) * z mod p"
proof -
  have "\<not> p dvd (nat z)"
    using assms R_def residues.res_carrier_eq residues_axioms nat_dvd_not_less by auto
  then have "z ^ (p - 1) mod p = 1"
    by (metis cong_def dvd_eq_mod_eq_0 int_nat_eq euler_theorem mod_0 nat_int
              of_nat_dvd_iff one_cong p_coprime_right_int res_one_eq prime_totient_eq)
  then show ?thesis
    by (metis R_def Suc_1 Suc_diff_Suc assms l_inv p_prime prime_gt_1_nat res_one_eq
              residues.res_mult_eq residues_axioms semiring_normalization_rules(28) zero_cong)
qed

lemma (in residues_prime) res_inv_one:
  assumes "z \<noteq> 0"  "z \<in> carrier R"
    shows "z ^ (p - 2) * z mod p = 1"
  using assms res_inv_mult l_inv res_mult_eq res_one_eq res_zero_eq
  by auto

lemma (in residues_prime) res_mult_div:
  assumes "z \<noteq> 0"  "z \<in> carrier R"
    shows "x * z ^ (p - 2) mod p = x \<oslash> z"
proof -
  have "z \<otimes> inv z = \<one>"
    using assms r_inv zero_cong by blast
  then have "z ^ (p - 2) mod p = (inv z) mod p"
    by (metis assms comm_inv_char mod_in_carrier mult_cong res_mult_eq
              semiring_normalization_rules(7) res_inv_mult)
  then show ?thesis using assms
    by (metis m_div_def mod_mult_right_eq res_mult_eq zero_cong)
qed

lemma (in residues_prime_gt2) add_pnts_eqn_x:
  assumes p1_on_curve: "on_curve a b (Point x1 y1)"
    and   p2_on_curve: "on_curve a b (Point x2 y2)"
    and   p1_plus_p2: "Point x3 y3 = add a (Point x1 y1) (Point x2 y2)"
    and   nz_cond: "x1 = x2 \<Longrightarrow> y1 = y2"
    and   ab_in_carrier: "a \<in> carrier R"  "b \<in> carrier R"
  shows   "x3 \<otimes> (x2 \<ominus> x1)[^](2::nat) = (a \<oplus> x1 \<otimes> x2) \<otimes> (x1 \<oplus> x2) \<oplus> \<guillemotleft>2\<guillemotright> \<otimes> b \<ominus> \<guillemotleft>2\<guillemotright> \<otimes> y1 \<otimes> y2"
proof cases
  assume "x1 = x2"
  with nz_cond p1_on_curve
  have [simp]: "y1 = y2" "x1 = x2" "x2 \<in> carrier R" "y2 \<in> carrier R"
    and *: "y2 [^] (2::nat) = x2 [^] (3::nat) \<oplus> a \<otimes> x2 \<oplus> b"
    by (auto simp add: on_curve_def)
  have "on_curve a b (Point x3 y3)"
    unfolding p1_plus_p2 by (intro add_closed assms)
  then have [simp]: "x3 \<in> carrier R" "y3 \<in> carrier R"
    by (auto simp add: on_curve_def)

  show ?thesis
    using *
    apply (simp add: local.power2_eq_square local.m_assoc)
    apply field
    apply simp
    done
next
  assume nz_cond: "x1 \<noteq> x2"
  have carrier[simp]: "x1 \<in> carrier R" "y1 \<in> carrier R" "x2 \<in> carrier R" "y2 \<in> carrier R"
    using assms(1) assms(2) unfolding on_curve_def by simp_all
  have y1sq: "y1[^](2::nat) = x1[^](3::nat) \<oplus> a \<otimes> x1 \<oplus> b" 
    using p1_on_curve unfolding on_curve_def by simp
  have y2sq: "y2[^](2::nat) = x2[^](3::nat) \<oplus> a \<otimes> x2 \<oplus> b" 
    using p2_on_curve unfolding on_curve_def by simp
  have denom_nz: "(x2 \<ominus> x1)[^](2::nat) \<noteq> \<zero> \<and> (x2 \<ominus> x1)[^](2::nat) \<in> carrier R"
    using nz_cond by auto
  then have r_cancel: "\<forall> z \<in> carrier R. z \<otimes> (x2 \<ominus> x1)[^](2::nat) \<oslash> (x2 \<ominus> x1)[^](2::nat) = z"
    using denom_nz divide_self m_assoc by (metis local.times_divide_eq_right r_one)
  have 0: "x3 = ((y2 \<ominus> y1) \<oslash> (x2 \<ominus> x1))[^](2::nat) \<ominus> (x1 \<oplus> x2)"
    using p1_plus_p2 nz_cond add.m_assoc nz_cond cring_simprules(15) eq_diff0 local.minus_add
    unfolding add_def Let_def by force
  then have 1: "\<dots> = (y2 \<ominus> y1)[^](2::nat) \<oslash> (x2 \<ominus> x1) [^](2::nat) \<ominus> (x1 \<oplus> x2)"
    using nonzero_power_divide nz_cond by auto
  then have "\<dots> = ((y2 \<ominus> y1)[^](2::nat) \<ominus> (x1 \<oplus> x2) \<otimes> (x2 \<ominus> x1)[^](2::nat))
                                                                \<oslash> (x2 \<ominus> x1)[^](2::nat)"
    using l_diff_distr denom_nz carrier r_cancel by (simp add: m_div_def)
  then have 2:
    "x3 \<otimes> (x2 \<ominus> x1)[^](2::nat) = (y2 \<ominus> y1)[^](2::nat) \<ominus> (x1 \<oplus> x2) \<otimes> (x2 \<ominus> x1)[^](2::nat)"
    using r_cancel 0 1 by (simp add: denom_nz)
  then have "\<dots> = (a \<oplus> x1 \<otimes> x2) \<otimes> (x1 \<oplus> x2) \<oplus> \<guillemotleft>2\<guillemotright> \<otimes> b \<ominus> \<guillemotleft>2\<guillemotright> \<otimes> y1 \<otimes> y2"
    using p1_on_curve p2_on_curve ab_in_carrier unfolding on_curve_def by (field y1sq y2sq, simp)
  then show ?thesis using 2 by simp
qed

lemma (in residues_prime_gt2) add_eliminate_ys_simp:
  assumes p1_on_curve: "on_curve a b (Point x1 y1)"
    and   p2_on_curve: "on_curve a b (Point x2 y2)"
    and   p1_plus_p2: "Point x3 y3 = add a (Point x1 y1) (Point x2 y2)"
    and   mp1_plus_p2: "Point xd yd = add a (opp (Point x1 y1)) (Point x2 y2)"
    and   x1_neq_x2: "x1 \<noteq> x2"
    and   ab_in_carrier: "a \<in> carrier R"  "b \<in> carrier R"
  shows   "(x3 \<oplus> xd) \<otimes> (x2 \<ominus> x1)[^](2::nat) = \<guillemotleft>2\<guillemotright> \<otimes> (a \<oplus> x1 \<otimes> x2) \<otimes> (x1 \<oplus> x2) \<oplus> \<guillemotleft>4\<guillemotright> \<otimes> b"
proof -
  have carrier[simp]: "x1 \<in> carrier R" "y1 \<in> carrier R" "x2 \<in> carrier R" "y2 \<in> carrier R"
    using assms(1) assms(2) unfolding on_curve_def by simp_all
  have "on_curve a b (Point x3 y3)" "on_curve a b (Point xd yd)"
    using p1_plus_p2 mp1_plus_p2 p1_on_curve p2_on_curve opp_closed add_closed
    by (simp add: ab_in_carrier)+
  then have x3_xd_carrier[simp]: "x3 \<in> carrier R" "xd \<in> carrier R"
    unfolding on_curve_def by simp_all
  have x3: "x3 \<otimes> (x2 \<ominus> x1)[^](2::nat) = (a \<oplus> x1 \<otimes> x2) \<otimes> (x1 \<oplus> x2) \<oplus> \<guillemotleft>2\<guillemotright> \<otimes> b \<ominus> \<guillemotleft>2\<guillemotright> \<otimes> y1 \<otimes> y2"
    using assms add_pnts_eqn_x by blast
  have 0: "on_curve a b (Point x1 (\<ominus> y1))" using p1_on_curve opp_closed opp_def by fastforce
  have "Point xd yd = add a (Point x1 (\<ominus> y1)) (Point x2 y2)"
    using mp1_plus_p2 unfolding opp_def by simp
  then have
    "xd \<otimes> (x2 \<ominus> x1)[^](2::nat) = (a \<oplus> x1 \<otimes> x2) \<otimes> (x1 \<oplus> x2) \<oplus> \<guillemotleft>2\<guillemotright> \<otimes> b \<ominus> \<guillemotleft>2\<guillemotright> \<otimes> (\<ominus> y1) \<otimes> y2"
    using carrier p1_on_curve p2_on_curve x1_neq_x2 add_pnts_eqn_x minus_minus 0
      cring_simprules(15) ab_in_carrier
    by blast
  then have xd: "xd \<otimes> (x2 \<ominus> x1)[^](2::nat) = (a \<oplus> x1 \<otimes> x2) \<otimes> (x1 \<oplus> x2) \<oplus> \<guillemotleft>2\<guillemotright> \<otimes> b
                                                \<oplus> \<guillemotleft>2\<guillemotright> \<otimes> y1 \<otimes> y2"
    by (simp add: cring_simprules(28) cring_simprules(29) local.minus_eq)
  have sum: "(x3 \<oplus> xd) \<otimes> (x2 \<ominus> x1)[^](2::nat) = x3 \<otimes> (x2 \<ominus> x1)[^](2::nat)
                                                   \<oplus> xd \<otimes> (x2 \<ominus> x1)[^](2::nat)"
    using x3_xd_carrier carrier by (field, simp)
  have "\<dots> = \<guillemotleft>2\<guillemotright> \<otimes> (a \<oplus> x1 \<otimes> x2) \<otimes> (x1 \<oplus> x2) \<oplus> \<guillemotleft>4\<guillemotright> \<otimes> b" unfolding x3 xd by (field, simp)
  then show ?thesis using sum by presburger
qed

named_theorems remove_mod

lemma mmult_mod_mod[remove_mod]: "(a mod m) **\<^bsub>m\<^esub> (b mod m) = (a * b) mod m"
  unfolding mmult_def mod_mult_eq ..

lemma madd_mod_mod[remove_mod]: "(a mod m) ++\<^bsub>m\<^esub> (b mod m) = (a + b) mod m"
  unfolding madd_def mod_add_eq ..

lemma msub_mod_mod[remove_mod]: "(a mod m) --\<^bsub>m\<^esub> (b mod m) = (a - b) mod m"
  unfolding msub_def mod_diff_eq ..

lemma mpow_mod[remove_mod]: "(a mod m) ^^^\<^bsub>m\<^esub> n = (a ^ n) mod m"
  unfolding mpow_def power_mod ..

lemma madd_mod: "(x ++\<^bsub>m\<^esub> y) mod m = x ++\<^bsub>m\<^esub> y"
  by (simp add: madd_def)

lemma msub_same_eq_zero[simp]: "x --\<^bsub>m\<^esub> y = 0 \<longleftrightarrow> x mod m = y mod m"
  by (metis (no_types, opaque_lifting) cancel_ab_semigroup_add_class.diff_right_commute
        eq_iff_diff_eq_0 mod_0 msub_def msub_mod_mod)

definition mpdouble_nz :: "int \<Rightarrow> int \<Rightarrow> int ppoint \<Rightarrow> int ppoint" where
  "mpdouble_nz m a = (\<lambda>(x, y, z).
    let
      l = 2 mod m **\<^bsub>m\<^esub> y **\<^bsub>m\<^esub> z;
      n = 3 mod m **\<^bsub>m\<^esub> x ^^^\<^bsub>m\<^esub> 2 ++\<^bsub>m\<^esub> a **\<^bsub>m\<^esub> z ^^^\<^bsub>m\<^esub> 2
    in
      (l **\<^bsub>m\<^esub> (n ^^^\<^bsub>m\<^esub> 2 --\<^bsub>m\<^esub> 4 mod m **\<^bsub>m\<^esub> x **\<^bsub>m\<^esub> y **\<^bsub>m\<^esub> l),
       n **\<^bsub>m\<^esub> (6 mod m **\<^bsub>m\<^esub> x **\<^bsub>m\<^esub> y **\<^bsub>m\<^esub> l --\<^bsub>m\<^esub> n ^^^\<^bsub>m\<^esub> 2) --\<^bsub>m\<^esub>
       2 mod m **\<^bsub>m\<^esub> y ^^^\<^bsub>m\<^esub> 2 **\<^bsub>m\<^esub> l ^^^\<^bsub>m\<^esub> 2,
       l ^^^\<^bsub>m\<^esub> 3))"

lemma mpdouble_eq_mpdouble_nz:
  "snd (snd p) \<noteq> 0 \<Longrightarrow> mpdouble_nz m a p = mpdouble m a p"
  by (auto simp add: mpdouble_def mpdouble_nz_def split: prod.split)

locale ell_prime_field = residues_prime_gt2 +
  fixes   A B :: nat
  assumes AB_in_carrier[simp]: "A \<in> carrier R" "B \<in> carrier R"
  and     non_singular:        "(4 * A ^ 3 + 27 * B ^ 2) mod p \<noteq> 0"
begin

definition curve :: "int point monoid" where
  "curve =
  \<lparr> carrier = ({ P. on_curve A B P }),
    monoid.mult = add A,
    monoid.one = Infinity \<rparr>"

lemma curve_simps:
  shows in_carrier_curve: "P \<in> carrier curve \<longleftrightarrow> on_curve A B P"
    and add_curve: "x \<otimes>\<^bsub>curve\<^esub> y = add A x y"
    and one_curve: "\<one>\<^bsub>curve\<^esub> = Infinity"
  by (simp_all add: curve_def)

lemma
  assumes "Point x y \<in> carrier curve"
  shows    Point_in_carrierD1: "x \<in> carrier R"
  and      Point_in_carrierD2: "y \<in> carrier R"
  using assms by (auto simp: in_carrier_curve on_curve_def)

text \<open>Just a few basic facts for casting a nat as an int.\<close>
lemma nat_int_eq:   "a = b \<longleftrightarrow> int a = int b" by simp
lemma nat_int_less: "a < b \<longleftrightarrow> int a < int b" by simp
lemma nat_int_le:   "a \<le> b \<longleftrightarrow> int a \<le> int b" by simp

lemma nonsingular_in_bf: "nonsingular A B"
  using non_singular
  unfolding nonsingular_def res_of_natural_eq res_of_integer_eq res_mult_eq
    res_add_eq res_pow_eq res_zero_eq nat_int_eq zmod_int
  by (simp add: mod_simps)

sublocale curve: comm_group curve
  apply (intro comm_groupI)
  using nonsingular_in_bf
  apply (auto simp: curve_simps add_0_l add_0_r Units_def
                    add_assoc[of "int A" "int B" _ _ _, symmetric]
                    add_comm[of A B] opp_closed
              intro!: add_closed)
  apply (intro bexI[of _ "opp _"])
  apply (auto simp: add_opp curve_simps intro!: opp_closed)
  done

lemma inv_curve: "x \<in> carrier curve \<Longrightarrow> inv\<^bsub>curve\<^esub> x = opp x"
  by (intro curve.inv_unique'[symmetric])
     (auto simp: curve_simps add_opp add_comm[of A B _ x] opp_closed)

lemma curve_square_is_mult: "P [^]\<^bsub>curve\<^esub> (2::nat) = P \<otimes>\<^bsub>curve\<^esub> P"
  unfolding nat_pow_def apply (simp add: curve_def curve_simps)
  by (simp add: ell_field_axioms ell_field.add_0_l)

lemma finite_curve[simp]: "finite (carrier curve)"
proof (rule finite_subset)
  show "carrier curve \<subseteq> case_prod Point ` (carrier R \<times> carrier R) \<union> { Infinity }"
    by (auto simp: in_carrier_curve on_curve_def split: point.splits)
qed auto

lemma Point_ne_one[simp]: "Point x y \<noteq> \<one>\<^bsub>curve\<^esub>"  "\<one>\<^bsub>curve\<^esub> \<noteq> Point x y"
  by (simp_all add: one_curve)

lemma odd_p: "odd p"
  using p_prime gt2 using prime_odd_nat by auto

lemma mod_of_in_carrier: "x \<in> carrier R \<Longrightarrow> x mod int p = x"
  by (simp add: res_carrier_eq)

lemma nz_in_carrier_gcd:
  assumes "x \<in> carrier R"  "x \<noteq> 0"
  shows   "gcd x (int p) = 1"
proof -
  have "0 < x \<and> x < int p" using assms res_carrier_eq by auto
  then show ?thesis using p_prime by (simp add: p_coprime_right_int zdvd_not_zless)
qed

text \<open>xy_to_pnt is for implementations that use (0,0) to represent Infinity.  Below are
many lemmas that relate pairs of ints and the point type.  Similarly, xyz_to_pnt is useful
for implementations that use triples of integers to represent points on the curve in 
projective form.\<close>
definition xy_to_pnt :: "int \<times> int \<Rightarrow> int point" where
  "xy_to_pnt =
    (\<lambda>(x, y). if x mod int p = 0 \<and> y mod int p = 0 then Infinity else Point (x mod p) (y mod p))"

lemma xy_to_pnt_eq:
  "x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow>
    xy_to_pnt (x, y) = (if x = \<zero>\<^bsub>R\<^esub> \<and> y = \<zero>\<^bsub>R\<^esub> then \<one>\<^bsub>curve\<^esub> else Point x y)"
  by (simp add: xy_to_pnt_def mod_of_in_carrier one_curve res_zero_eq)

lemma xy_to_pnt_Point:
  assumes "xy_to_pnt (x, y) = Point x' y'"
  shows   "x mod p = x' \<and> y mod p = y'"
proof -
  have "x mod int p \<noteq> 0 \<or> y mod int p \<noteq> 0"
    using assms unfolding xy_to_pnt_def by force
  then have "xy_to_pnt (x, y) = Point (x mod p) (y mod p)"
    using assms unfolding xy_to_pnt_def by fastforce
  then show ?thesis using assms by simp
qed

lemma xy_to_pnt_Infinity:
  assumes "xy_to_pnt (x, y) = Infinity"
  shows   "x mod p = 0 \<and> y mod p = 0"
proof -
  have "Infinity = (if x mod int p = 0 \<and> y mod int p = 0 then Infinity
                    else Point (x mod int p) (y mod int p))"
    using assms xy_to_pnt_def by force
  then show ?thesis by (metis (no_types) point.simps(3))
qed

definition xyz_to_pnt :: "int \<times> int \<times> int \<Rightarrow> int point" where
  "xyz_to_pnt = (\<lambda>(x, y, z). if z mod int p = 0 then Infinity
           else Point ((x mod int p) \<oslash>\<^bsub>R\<^esub> (z mod int p)) ((y mod int p) \<oslash>\<^bsub>R\<^esub> (z mod int p)))"

lemma xyz_to_pnt_zero_z[simp]: "xyz_to_pnt (x, y, \<zero>\<^bsub>R\<^esub>) = \<one>\<^bsub>curve\<^esub>"
  by (simp add: xyz_to_pnt_def mod_of_in_carrier one_curve zero_cong)

lemma xyz_to_pnt_zero[simp]: "xyz_to_pnt (x, y, 0) = Infinity"
  by (simp add: xyz_to_pnt_def res_zero_eq)

lemma xyz_to_pnt_eq:
  "x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> z \<in> carrier R \<Longrightarrow>
    xyz_to_pnt (x, y, z) = (if z = \<zero>\<^bsub>R\<^esub> then \<one>\<^bsub>curve\<^esub> else Point (x \<oslash>\<^bsub>R\<^esub> z) (y \<oslash>\<^bsub>R\<^esub> z))"
  using xyz_to_pnt_def mod_of_in_carrier res_zero_eq one_curve by simp

lemma xyz_to_pnt_z_1:
  assumes [simp]: "x \<in> carrier R"  "y \<in> carrier R"
  shows "xyz_to_pnt (x, y, \<one>\<^bsub>R\<^esub>) = Point x y"
proof -
  have "(1::int) \<in> carrier R" using res_carrier_eq gt2 by auto
  then show ?thesis 
     unfolding xyz_to_pnt_def using mod_of_in_carrier m_gt_one assms divide_1 res_one_eq by auto
qed

lemma xyz_to_pnt_eq_make_affine:
  "x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> z \<in> carrier R \<Longrightarrow>
    xyz_to_pnt (x, y, z) = make_affine (x, y, z)"
  by (simp add: xyz_to_pnt_def make_affine_def mod_of_in_carrier res_zero_eq)

lemma xyz_to_pnt_in_carrier_on_curvep:
  assumes [simp]: "x \<in> carrier R"  "y \<in> carrier R"  "z \<in> carrier R"
                  "xyz_to_pnt (x, y, z) \<in> carrier curve"
  shows   "on_curvep A B (x, y, z)"
proof -
  have "on_curve A B (make_affine (x, y, z))"
    by (simp flip: xyz_to_pnt_eq_make_affine in_carrier_curve)
  then show ?thesis
    by (subst on_curvep_iff_on_curve) (simp_all add: in_carrierp_def)
qed

lemma xyz_to_pnt_scale[symmetric]:
  assumes [simp]: "x \<in> carrier R"  "y \<in> carrier R"  "z \<in> carrier R"  "c \<in> carrier R"  "c \<noteq> \<zero>\<^bsub>R\<^esub>"
  shows   "xyz_to_pnt (x, y, z) = xyz_to_pnt (x \<otimes>\<^bsub>R\<^esub> c, y \<otimes>\<^bsub>R\<^esub> c, z \<otimes>\<^bsub>R\<^esub> c)"
  by (simp add: xyz_to_pnt_eq)

lemma xyz_to_pnt_scale'[symmetric]:
  assumes [simp]: "x \<in> carrier R"  "y \<in> carrier R"  "z \<in> carrier R"  "c \<in> carrier R"
      and zc:     "z \<noteq> \<zero>\<^bsub>R\<^esub> \<Longrightarrow> c \<noteq> \<zero>\<^bsub>R\<^esub>"
  shows           "xyz_to_pnt (x, y, z) = xyz_to_pnt (x \<otimes>\<^bsub>R\<^esub> c, y \<otimes>\<^bsub>R\<^esub> c, z \<otimes>\<^bsub>R\<^esub> c)"
proof cases
  assume "z = \<zero>\<^bsub>R\<^esub>" then show ?thesis
    using assms by (simp add: xyz_to_pnt_eq in_carrierp_def)
next
  assume "z \<noteq> \<zero>\<^bsub>R\<^esub>" with zc show ?thesis
    using assms by (simp add: xyz_to_pnt_scale in_carrierp_def)
qed

lemma xyz_to_pnt_mod:
  "xyz_to_pnt (x mod int p, y mod int p, z mod int p) = xyz_to_pnt (x, y, z)"
  by (simp add: mod_of_in_carrier xyz_to_pnt_def)

lemma inv_xyz_to_pnt:
  "x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> z \<in> carrier R \<Longrightarrow> xyz_to_pnt (x, y, z) \<in> carrier curve \<Longrightarrow>
    inv\<^bsub>curve\<^esub> (xyz_to_pnt (x, y, z)) = xyz_to_pnt (x, \<ominus> y, z)"
  unfolding inv_curve opp_def by (auto simp add: xyz_to_pnt_eq one_curve)

lemma xyz_to_pnt_dbl:
  assumes [simp]: "x \<in> carrier R"  "y \<in> carrier R"  "z \<in> carrier R"
  shows "xyz_to_pnt (x, y, z) \<otimes>\<^bsub>curve\<^esub> xyz_to_pnt (x, y, z) =
    (let l = \<guillemotleft>2\<guillemotright> \<otimes> y \<otimes> z; m = \<guillemotleft>3\<guillemotright> \<otimes> x [^] (2::nat) \<oplus> A \<otimes> z [^] (2::nat) in
      xyz_to_pnt (
        l \<otimes> (m [^] (2::nat) \<ominus> \<guillemotleft>4\<guillemotright> \<otimes> x \<otimes> y \<otimes> l),
        m \<otimes> (\<guillemotleft>6\<guillemotright> \<otimes> x \<otimes> y \<otimes> l \<ominus> m [^] (2::nat)) \<ominus> \<guillemotleft>2\<guillemotright> \<otimes> y [^] (2::nat) \<otimes> l [^] (2::nat),
        l [^] (3::nat)))" (is "?l = ?r")
proof -
  have "?l = make_affine (pdouble A (x, y, z))"
    by (simp add: pdouble_correct in_carrierp_def add_curve xyz_to_pnt_eq_make_affine)
  also have "\<dots> = ?r"
    by (simp add: pdouble_def Let_def one_curve xyz_to_pnt_eq_make_affine)
  finally show ?thesis .
qed

lemma xyz_to_pnt_square:
  assumes "x \<in> carrier R"  "y \<in> carrier R"  "z \<in> carrier R"
  shows "xyz_to_pnt (x, y, z) [^]\<^bsub>curve\<^esub> (2::nat) =
    (let l = \<guillemotleft>2\<guillemotright> \<otimes> y \<otimes> z; m = \<guillemotleft>3\<guillemotright> \<otimes> x [^] (2::nat) \<oplus> A \<otimes> z [^] (2::nat) in
      xyz_to_pnt (
        l \<otimes> (m [^] (2::nat) \<ominus> \<guillemotleft>4\<guillemotright> \<otimes> x \<otimes> y \<otimes> l),
        m \<otimes> (\<guillemotleft>6\<guillemotright> \<otimes> x \<otimes> y \<otimes> l \<ominus> m [^] (2::nat)) \<ominus> \<guillemotleft>2\<guillemotright> \<otimes> y [^] (2::nat) \<otimes> l [^] (2::nat),
        l [^] (3::nat)))" (is "?l = ?r")
  unfolding curve_square_is_mult by (rule xyz_to_pnt_dbl) fact+

lemma xyz_to_pnt_add:
  assumes [simp]:   "x\<^sub>1 \<in> carrier R"  "y\<^sub>1 \<in> carrier R"  "z\<^sub>1 \<in> carrier R"
  assumes [simp]:   "x\<^sub>2 \<in> carrier R"  "y\<^sub>2 \<in> carrier R"  "z\<^sub>2 \<in> carrier R"
  assumes in_curve: "xyz_to_pnt (x\<^sub>1, y\<^sub>1, z\<^sub>1) \<in> carrier curve"
                    "xyz_to_pnt (x\<^sub>2, y\<^sub>2, z\<^sub>2) \<in> carrier curve"
  assumes ne:       "xyz_to_pnt (x\<^sub>1, y\<^sub>1, z\<^sub>1) \<noteq> xyz_to_pnt (x\<^sub>2, y\<^sub>2, z\<^sub>2)"
  and     [simp]:   "z\<^sub>1 \<noteq> \<zero>" "z\<^sub>2 \<noteq> \<zero>"
  shows   "xyz_to_pnt (x\<^sub>1, y\<^sub>1, z\<^sub>1) \<otimes>\<^bsub>curve\<^esub> xyz_to_pnt (x\<^sub>2, y\<^sub>2, z\<^sub>2) =
    (let d\<^sub>1 = x\<^sub>2 \<otimes> z\<^sub>1; d\<^sub>2 = x\<^sub>1 \<otimes> z\<^sub>2;
         l = d\<^sub>1 \<ominus> d\<^sub>2; m = y\<^sub>2 \<otimes> z\<^sub>1 \<ominus> y\<^sub>1 \<otimes> z\<^sub>2;
         h = m [^] (2::nat) \<otimes> z\<^sub>1 \<otimes> z\<^sub>2 \<ominus> (d\<^sub>1 \<oplus> d\<^sub>2) \<otimes> l [^] (2::nat)
    in xyz_to_pnt (l \<otimes> h, (d\<^sub>2 \<otimes> l [^] (2::nat) \<ominus> h) \<otimes> m \<ominus> l [^] (3::nat) \<otimes> y\<^sub>1 \<otimes> z\<^sub>2,
                   l [^] (3::nat) \<otimes> z\<^sub>1 \<otimes> z\<^sub>2))" (is "?l = ?r")
proof -
  from ne have *: "\<not> (y\<^sub>2 \<otimes> z\<^sub>1 = y\<^sub>1 \<otimes> z\<^sub>2 \<and> x\<^sub>2 \<otimes> z\<^sub>1 = x\<^sub>1 \<otimes> z\<^sub>2)"
    by (auto simp add: xyz_to_pnt_eq simp flip: mult_eq_iff_eq_divide eq_mult_iff_divide_eq)

  have "?l = make_affine (padd A (x\<^sub>1, y\<^sub>1, z\<^sub>1) (x\<^sub>2, y\<^sub>2, z\<^sub>2))"
    using in_curve
    by (simp add: padd_correct[where b=B] in_carrierp_def curve_simps
                  xyz_to_pnt_eq_make_affine on_curvep_iff_on_curve)
  also have "\<dots> = ?r"
    using *
    by (auto simp add: padd_def Let_def xyz_to_pnt_eq_make_affine
                simp flip: one_curve)
  finally show ?thesis .
qed

lemma xyz_to_pnt_padd:
  assumes [simp]:   "x\<^sub>1 \<in> carrier R"  "y\<^sub>1 \<in> carrier R"  "z\<^sub>1 \<in> carrier R"
  assumes [simp]:   "x\<^sub>2 \<in> carrier R"  "y\<^sub>2 \<in> carrier R"  "z\<^sub>2 \<in> carrier R"
  assumes in_curve: "xyz_to_pnt (x\<^sub>1, y\<^sub>1, z\<^sub>1) \<in> carrier curve"
                    "xyz_to_pnt (x\<^sub>2, y\<^sub>2, z\<^sub>2) \<in> carrier curve"
  shows   "xyz_to_pnt (padd A (x\<^sub>1, y\<^sub>1, z\<^sub>1) (x\<^sub>2, y\<^sub>2, z\<^sub>2)) =
           xyz_to_pnt (x\<^sub>1, y\<^sub>1, z\<^sub>1) \<otimes>\<^bsub>curve\<^esub> xyz_to_pnt (x\<^sub>2, y\<^sub>2, z\<^sub>2)"
  apply (subst (1 2) xyz_to_pnt_eq_make_affine)
  apply (simp_all add: curve_simps)
  apply (subst padd_correct[symmetric, OF AB_in_carrier])
  using in_curve
  apply (simp_all add: xyz_to_pnt_eq_make_affine padd_def pdouble_def Let_def curve_simps
      on_curvep_iff_on_curve in_carrierp_def)
  done

lemma Point_Point_eq_one_iff:
  assumes 1: "Point x1 y1 \<in> carrier curve"
  and     2: "Point x2 y2 \<in> carrier curve"
  shows "Point x1 y1 \<otimes>\<^bsub>curve\<^esub> Point x2 y2 = \<one>\<^bsub>curve\<^esub> \<longleftrightarrow> (x1 = x2 \<and> y1 = \<ominus> y2)"
  by (subst curve.m_one_iff[OF 1 2]) (simp add: inv_curve 1 2 opp_def)

lemma y_coord_eq_or_eq_neg:
  "Point x y1 \<in> carrier curve \<Longrightarrow> Point x y2 \<in> carrier curve \<Longrightarrow> y1 = y2 \<or> y1 = \<ominus> y2"
  by (auto simp: in_carrier_curve on_curve_def eq_commute[of _ "_  \<oplus> _"] power2_eq_square
                 square_eq_iff)

lemma yz_coord_eq_or_eq_neg:
  assumes [simp]:
    "x \<in> carrier R"  "y1 \<in> carrier R"  "y2 \<in> carrier R"  "z \<in> carrier R"
  shows "xyz_to_pnt (x, y1, z) \<in> carrier curve \<Longrightarrow>
         xyz_to_pnt (x, y2, z) \<in> carrier curve \<Longrightarrow> z \<noteq> \<zero>\<^bsub>R\<^esub> \<Longrightarrow> y1 = y2 \<or> y1 = \<ominus> y2"
  using y_coord_eq_or_eq_neg[of "x \<oslash> z" "y1 \<oslash> z" "y2 \<oslash> z"]
  by (auto simp add: xyz_to_pnt_eq div_cancel)

lemma xyz_coord_eq_or_eq_neg:
  assumes [simp]: "x1 \<in> carrier R"  "y1 \<in> carrier R"  "z1 \<in> carrier R"
                  "x2 \<in> carrier R"  "y2 \<in> carrier R"  "z2 \<in> carrier R"
  assumes 1:      "xyz_to_pnt (x1, y1, z1) \<in> carrier curve"
  assumes 2:      "xyz_to_pnt (x2, y2, z2) \<in> carrier curve"
  and     [simp]: "z1 \<noteq> \<zero>"  "z2 \<noteq> \<zero>"
  and     x: "x1 \<otimes> z2 = x2 \<otimes> z1"
  shows "y1 \<otimes> z2 = y2 \<otimes> z1 \<or> y1 \<otimes> z2 = \<ominus> y2 \<otimes> z1"
  apply (subst (1 2) divide_eq_divide_iff_mult_eq_mult[symmetric])
  apply (simp_all flip: minus_divide_left)
  using 1 2 x y_coord_eq_or_eq_neg[of "x1 \<oslash> z1" "y1 \<oslash> z1" "y2 \<oslash> z2"]
  apply (subst (asm) divide_eq_divide_iff_mult_eq_mult[symmetric])
  apply (auto simp: xyz_to_pnt_eq split: if_splits)
  done

end (* of ell_prime_field locale *)

section \<open>Added for SEC1\<close>
text \<open>This section adds more facts about an elliptic curve as a group.  For example, we examine
the order of points on the curve and the order of the curve itself.\<close>

context ell_prime_field
begin

lemma multEqPowInCurve:
  assumes "on_curve A B P" 
  shows   "point_mult A x P = P [^]\<^bsub>curve\<^esub> x"
proof (induct x)
  case 0
  then show ?case by (simp add: one_curve) 
next
  case (Suc x)
  then show ?case
    using add_curve curve.nat_pow_Suc2 in_carrier_curve assms point_mult.simps(2) 
    by presburger 
qed

text \<open>If P is not the point at infinity, n is a prime, and nP = the point at infinity, then
n is actually the order of P.  So if 0 < x < n, xP \<noteq> the point at infinity.\<close>
lemma order_n: 
  assumes "x < n"  "0 < x"  "on_curve A B P"  "P \<noteq> Infinity"  "point_mult A n P = Infinity" 
          "prime (n::nat)"
  shows   "point_mult A x P \<noteq> Infinity"
proof - 
  have 1: "gcd n x = 1" 
    by (metis assms(1,2,6) gcd_dvd1 gcd_le2_nat neq0_conv not_le prime_nat_iff) 
  obtain i and j where 2: "i*(int n) + j*(int x) = 1" 
    by (metis bezw_aux 1 int_ops(2))
  have 3: "P = P [^]\<^bsub>curve\<^esub>(i*(int n) + j*(int x))"  
    by (simp add: 2 assms(3) in_carrier_curve) 
  have 4: "P = P [^]\<^bsub>curve\<^esub>(i*(int n)) \<otimes>\<^bsub>curve\<^esub> P [^]\<^bsub>curve\<^esub>(j*(int x))"
    using assms(3) in_carrier_curve 3 curve.int_pow_mult by auto
  have 5: "P = (P [^]\<^bsub>curve\<^esub>(int n))[^]\<^bsub>curve\<^esub>i \<otimes>\<^bsub>curve\<^esub> 
               (P [^]\<^bsub>curve\<^esub>(int x))[^]\<^bsub>curve\<^esub>j"
    by (metis assms(3) in_carrier_curve 4 curve.int_pow_pow mult_of_nat_commute)
  have 6: "P = (P [^]\<^bsub>curve\<^esub>(int x))[^]\<^bsub>curve\<^esub>j" 
    by (metis assms(3,5) in_carrier_curve 5 curve.int_pow_closed curve.int_pow_one one_curve
              curve.l_one int_pow_int multEqPowInCurve) 
  have 7: "P [^]\<^bsub>curve\<^esub> x = \<one>\<^bsub>curve\<^esub> \<longrightarrow> P = \<one>\<^bsub>curve\<^esub>"
    by (metis 6 curve.int_pow_one int_pow_int) 
  show ?thesis 
    using assms(3,4) 7 one_curve multEqPowInCurve by auto 
qed

lemma order_n': 
  assumes "x < n"  "0 < x"  "on_curve A B P"  "P \<noteq> Infinity"  "point_mult A n P = Infinity"
          "prime (n::nat)"
  shows   "P [^]\<^bsub>curve\<^esub> x \<noteq> \<one>\<^bsub>curve\<^esub>"
  using assms order_n one_curve multEqPowInCurve in_carrier_curve by algebra

text \<open>The idea for the next two lemmas is that every point on the cycle of order n are the "same."
So if you start at one point on the cycle (not Infinity), then you can get to any other point on
the cycle by multiplying by some scalar x.  Then the point you land on will also be on the curve,
have order n, and not be infinity (as long as n does not divide x.)\<close>
lemma order_n_cycle:
  assumes "on_curve A B P"  "point_mult A n P = Infinity"  "Q = point_mult A x P"
  shows   "point_mult A n Q = Infinity"
  by (metis AB_in_carrier(1,2) assms(1,2,3) curve.int_pow_one curve.int_pow_pow curve_simps(1) 
            int_pow_int mult.commute multEqPowInCurve one_curve point_mult_closed)

lemma order_n_cycle':
  assumes "x < n"  "0 < x"  "on_curve A B P"  "P \<noteq> Infinity"  "point_mult A n P = Infinity" 
          "prime (n::nat)"  "Q = point_mult A x P" 
  shows   "on_curve A B Q \<and> Q \<noteq> Infinity \<and> point_mult A n Q = Infinity"
  using AB_in_carrier(1,2) assms order_n order_n_cycle point_mult_closed 
  by presburger

lemma multQmodn:
  assumes "on_curve A B Q"  "point_mult A n Q = Infinity" 
  shows   "point_mult A x Q = point_mult A (x mod n) Q"
proof - 
  let ?d = "x div n"
  let ?m = "x mod n"
  have 1: "x = ?d*n + ?m"  using div_mod_decomp by blast 
  have 2: "point_mult A x Q = Q [^]\<^bsub>curve\<^esub> (?d*n + ?m)"
    using in_carrier_curve assms(1) multEqPowInCurve by presburger 
  have 3: "Q [^]\<^bsub>curve\<^esub> (?d*n + ?m) = Q [^]\<^bsub>curve\<^esub>(?d*n)\<otimes>\<^bsub>curve\<^esub>Q [^]\<^bsub>curve\<^esub>?m"
    using curve.nat_pow_mult assms(1) in_carrier_curve by presburger
  have 4: "Q [^]\<^bsub>curve\<^esub>(?d*n) = (Q [^]\<^bsub>curve\<^esub>n)[^]\<^bsub>curve\<^esub>?d" 
    by (simp add: curve.nat_pow_pow assms(1) in_carrier_curve mult.commute) 
  have 5: "Q [^]\<^bsub>curve\<^esub>(?d*n) = \<one>\<^bsub>curve\<^esub>" 
    using 4 assms(1,2) curve.nat_pow_one one_curve multEqPowInCurve by algebra
  show ?thesis 
    using 3 5 multEqPowInCurve curve.nat_pow_closed in_carrier_curve assms(1) by force
qed

lemma multQmodn':
  assumes "on_curve A B Q"  "point_mult A n Q = Infinity" 
  shows   "Q[^]\<^bsub>curve\<^esub>x = Q[^]\<^bsub>curve\<^esub>(x mod n)"
  by (metis assms(1,2) multEqPowInCurve multQmodn)

lemma multQmodn'int_pos:
  assumes "on_curve A B Q"  "point_mult A n Q = Infinity"  "0 \<le> (x::int)"
  shows   "Q[^]\<^bsub>curve\<^esub>x = Q[^]\<^bsub>curve\<^esub>(x mod n)"
  by (metis assms int_pow_int multQmodn' zero_le_imp_eq_int zmod_int)

lemma multQmodn'int_neg: 
  assumes "on_curve A B Q"  "point_mult A n Q = Infinity"  "(x::int) < 0"  "1 < n"
  shows   "Q[^]\<^bsub>curve\<^esub>(x::int) = Q[^]\<^bsub>curve\<^esub>(x mod n)"
proof - 
  let ?y = "-x"
  have 1: "Q[^]\<^bsub>curve\<^esub>(?y*n) = \<one>\<^bsub>curve\<^esub>" 
    by (metis assms(1,2) curve.int_pow_one curve.int_pow_pow one_curve int_pow_int 
              multEqPowInCurve mult_of_nat_commute in_carrier_curve) 
  have 2: "0 \<le> x + ?y*n" 
    using assms(3,4) by auto
  have 3: "x mod n = (x + ?y*n) mod n" 
    by presburger 
  have 4: "Q[^]\<^bsub>curve\<^esub>(x + ?y*n) = Q[^]\<^bsub>curve\<^esub>((x + ?y*n) mod n)" 
    using 2 assms(1,2) multQmodn'int_pos by fast
  have 5: "Q[^]\<^bsub>curve\<^esub>(x + ?y*n) = Q[^]\<^bsub>curve\<^esub>x \<otimes>\<^bsub>curve\<^esub> Q[^]\<^bsub>curve\<^esub>(?y*n)"
    using curve.int_pow_mult assms(1) in_carrier_curve by presburger
  have 6: "Q[^]\<^bsub>curve\<^esub>(x + ?y*n) = Q[^]\<^bsub>curve\<^esub>x"
    using 1 5 assms(1) in_carrier_curve by force
  show ?thesis using 3 4 6 by argo
qed

lemma multQmodn'int: 
  assumes "on_curve A B Q"  "point_mult A n Q = Infinity"  "1 < n"
  shows   "Q[^]\<^bsub>curve\<^esub>(x::int) = Q[^]\<^bsub>curve\<^esub>(x mod n)"
  apply (cases "0 \<le> x")
  using assms(1,2)   multQmodn'int_pos apply fast
  using assms(1,2,3) multQmodn'int_neg by simp


text \<open>We use the above to relate to the definition of "ord" for a group.\<close>
lemma curve_ord_n1: 
  assumes "on_curve A B P"  "point_mult A n P = Infinity"  "n dvd x"
  shows   "point_mult A x P = Infinity"
  by (metis assms(1,2,3) dvd_eq_mod_eq_0 multQmodn point_mult.simps(1))

lemma curve_ord_n2: 
  assumes "on_curve A B P"  "P \<noteq> Infinity"  "point_mult A n P = Infinity" 
          "prime (n::nat)"  "\<not> n dvd x"
  shows   "point_mult A x P \<noteq> Infinity"
proof - 
  let ?m = "x mod n"
  have "0 < ?m \<and> ?m < n" 
    by (simp add: assms(4,5) mod_greater_zero_iff_not_dvd prime_gt_0_nat) 
  then show ?thesis by (metis assms(1,2,3,4) order_n multQmodn)
qed

lemma curve_ord_n3: 
  assumes "on_curve A B P"  "P \<noteq> Infinity"  "point_mult A n P = Infinity"  "prime (n::nat)" 
  shows   "(n dvd x) = (point_mult A x P = Infinity)"
  by (meson assms(1,2,3,4) curve_ord_n1 curve_ord_n2)

lemma curve_ord_n4: 
  assumes "on_curve A B P"  "P \<noteq> Infinity"  "point_mult A n P = Infinity"  "prime (n::nat)" 
  shows   "(n dvd x) = (P[^]\<^bsub>curve\<^esub>x = \<one>\<^bsub>curve\<^esub>)"
  using assms curve_ord_n3 multEqPowInCurve one_curve by presburger

lemma curve_ord_n5: 
  assumes "on_curve A B P"  "P \<noteq> Infinity"  "point_mult A n P = Infinity"  "prime (n::nat)" 
  shows   "curve.ord P = n"
  using assms curve_ord_n4 curve.ord_def curve.ord_unique in_carrier_curve by presburger

lemma curve_ord_n6: 
  assumes "on_curve A B P"  "P \<noteq> \<one>\<^bsub>curve\<^esub>"  "point_mult A n P = \<one>\<^bsub>curve\<^esub>"  "prime (n::nat)" 
          "d1 < n"  "d2 < n"  "d1 < d2" 
  shows   "P [^]\<^bsub>curve\<^esub> d1 \<noteq> P [^]\<^bsub>curve\<^esub> d2"
proof - 
  let ?d = "d2 - d1"
  have d1: "0 < ?d \<and> ?d < n"  using assms(5,6,7) by linarith
  have d2: "\<not> n dvd ?d"       using d1 by auto
  have A1: "(P [^]\<^bsub>curve\<^esub> d1 = P [^]\<^bsub>curve\<^esub> d2) \<longrightarrow> P [^]\<^bsub>curve\<^esub> ?d = \<one>\<^bsub>curve\<^esub>" 
    using assms(1) curve.pow_eq_div2 curve_simps(1) by presburger
  show ?thesis by (metis d2 A1 assms(1,2,3,4) curve_ord_n4 curve_simps(3)) 
qed

lemma curve_ord_n7: 
  assumes "on_curve A B P"  "P \<noteq> \<one>\<^bsub>curve\<^esub>"  "point_mult A n P = \<one>\<^bsub>curve\<^esub>"  "prime (n::nat)" 
          "d1 < n"  "d2 < n"  "d1 \<noteq> d2" 
  shows   "P [^]\<^bsub>curve\<^esub> d1 \<noteq> P [^]\<^bsub>curve\<^esub> d2"
  apply (cases "d1 < d2") 
  using assms curve_ord_n6 apply blast 
  by (metis assms curve_ord_n6 verit_comp_simplify(3) verit_la_disequality) 

lemma curve_cycle_n1:
  assumes "on_curve A B P"  "P \<noteq> \<one>\<^bsub>curve\<^esub>"  "point_mult A n P = \<one>\<^bsub>curve\<^esub>"  "prime (n::nat)" 
  shows   "card {Q. (\<exists>d<n. Q = P [^]\<^bsub>curve\<^esub> d)} = n"
proof - 
  let ?S1 = "{d. d<n}"
  let ?S2 = "{Q. (\<exists>d<n. Q = P [^]\<^bsub>curve\<^esub> d)}"
  have 1: "card ?S1 = n"        by force
  let ?f = "\<lambda>d. P [^]\<^bsub>curve\<^esub> d"
  have 2: "inj_on ?f ?S1" 
    by (metis (mono_tags, lifting) assms curve_ord_n7 inj_on_def mem_Collect_eq)
  have 3: "?f ` ?S1 = ?S2"      by blast
  have 4: "bij_betw ?f ?S1 ?S2" by (simp add: 2 3 bij_betw_def) 
  show ?thesis                  using 1 4 bij_betw_same_card by force  
qed

lemma curve_cycle_n2:
  assumes "on_curve A B P"  "P \<noteq> Infinity"  "point_mult A n P = Infinity"  "prime (n::nat)" 
  shows   "card {Q. (\<exists>d<n. Q = point_mult A d P)} = n"
  using assms curve_cycle_n1 multEqPowInCurve one_curve by presburger 

end (* of ell_prime_field context *)

section \<open>Additions to Elliptic_test\<close>

text \<open>Elliptic_Test only defines addition and scalar multiplication for integer points that are
in projective form.  We want to have these defined for affine (integer) points.  This becomes
important when we are running test vectors.\<close>

context residues_prime_gt2
begin

definition point_madd :: "nat \<Rightarrow> int point \<Rightarrow> int point \<Rightarrow> int point" where
  "point_madd a p\<^sub>1 p\<^sub>2 = (case p\<^sub>1 of
       Infinity \<Rightarrow> p\<^sub>2
     | Point x\<^sub>1 y\<^sub>1 \<Rightarrow> (case p\<^sub>2 of
         Infinity \<Rightarrow> p\<^sub>1
       | Point x\<^sub>2 y\<^sub>2 \<Rightarrow>
           if x\<^sub>1 = x\<^sub>2 then
             if (y\<^sub>1 = - y\<^sub>2 mod (int p)) then Infinity
             else
               let
                 twoy1   = nat ((2*y\<^sub>1) mod (int p));
                 inv_2y1 = int (inv_mod p twoy1);
                 l       = ((3 * x\<^sub>1^2 + (int a)) * inv_2y1) mod p;
                 x\<^sub>3 = (l^2 - 2*x\<^sub>1) mod (int p);
                 y\<^sub>3 = (- y\<^sub>1 - l * (x\<^sub>3 - x\<^sub>1)) mod (int p)
               in
                 Point x\<^sub>3 y\<^sub>3
           else
             let
               x2_x1     = nat ((x\<^sub>2 - x\<^sub>1) mod (int p));
               inv_x2_x1 = int (inv_mod p x2_x1);
               l = ((y\<^sub>2 - y\<^sub>1) * inv_x2_x1) mod (int p);
               x\<^sub>3 = (l^2 - x\<^sub>1 - x\<^sub>2) mod (int p);
               y\<^sub>3 = (- y\<^sub>1 - l * (x\<^sub>3 - x\<^sub>1)) mod (int p)
             in
               Point x\<^sub>3 y\<^sub>3 ) )"

fun point_mmult :: "nat \<Rightarrow> nat \<Rightarrow> int point \<Rightarrow> int point" where
    "point_mmult a 0 P = Infinity"
  | "point_mmult a (Suc n) P = point_madd a P (point_mmult a n P)"

lemma add_eq_h1:
  assumes  "p\<^sub>1 = Point x1 y1" "p\<^sub>2 = Point x2 y2" "x1 = x2" "y1 \<noteq> \<ominus>\<^bsub>R\<^esub> y2"
           "l = (\<guillemotleft>3\<guillemotright> \<otimes>\<^bsub>R\<^esub> x1 [^] (2::nat) \<oplus>\<^bsub>R\<^esub> a) \<oslash>\<^bsub>R\<^esub> (\<guillemotleft>2\<guillemotright> \<otimes>\<^bsub>R\<^esub> y1)"
           "x3 = l [^] (2::nat) \<ominus>\<^bsub>R\<^esub> \<guillemotleft>2\<guillemotright> \<otimes>\<^bsub>R\<^esub> x1" "y3 = (\<ominus>\<^bsub>R\<^esub> y1 \<ominus>\<^bsub>R\<^esub> l \<otimes>\<^bsub>R\<^esub> (x3 \<ominus>\<^bsub>R\<^esub> x1))"
  shows    "add a p\<^sub>1 p\<^sub>2 = Point x3 y3"
  unfolding add_def Let_def using assms point.distinct
  by simp 

lemma add_eq_h2: 
  assumes  "p\<^sub>1 = Point x1 y1" "p\<^sub>2 = Point x2 y2" "x1 = x2" "(y1 \<noteq> - y2 mod (int p))" 
           "twoy1 = nat ((2*y1) mod (int p))" "inv_2y1 = int (inv_mod p twoy1)"
           "l = ((3 * x1^2 + (int a)) * inv_2y1) mod p" "x3 = (l^2 - 2*x1) mod (int p)"
           "y3 = (- y1 - l * (x3 - x1)) mod (int p)"
  shows    "point_madd a p\<^sub>1 p\<^sub>2 = Point x3 y3"
  unfolding point_madd_def Let_def using assms point.distinct by simp

lemma point_add_eq [code]: "add a p\<^sub>1 p\<^sub>2 = point_madd a p\<^sub>1 p\<^sub>2"
proof (cases p\<^sub>1)
  case Infinity
  then show ?thesis by (simp add: point_madd_def add_0_l) 
next
  case P1: (Point x1 y1)
  show ?thesis proof (cases p\<^sub>2)
    case Infinity
    then show ?thesis using P1 point_madd_def add_0_r by auto 
  next
    case P2: (Point x2 y2)
    then show ?thesis proof (cases "x1 = x2")
      case x_eq: True
      then show ?thesis proof (cases "y1 = \<ominus>\<^bsub>R\<^esub> y2")
        case y_neg: True
        have A1: "(y1 = - y2 mod (int p))"        using res_neg_eq y_neg by blast 
        have A2:        "add a p\<^sub>1 p\<^sub>2 = Infinity"   using add_def P1 P2 x_eq y_neg by fastforce
        have A3: "point_madd a p\<^sub>1 p\<^sub>2 = Infinity"   using point_madd_def P1 P2 x_eq A1 by force
        show ?thesis                              using A2 A3 by presburger 
      next
        case y_nneg: False
        have B0: "(y1 \<noteq> - y2 mod (int p))"        using y_nneg res_neg_eq by algebra
        let ?twoy1   = "((2*y1) mod (int p))"
        let ?inv_2y1 = "int (inv_mod p (nat ?twoy1))"
        let ?l       = "((3 * x1^2 + (int a)) * ?inv_2y1) mod p"
        let ?l'      = "(\<guillemotleft>3\<guillemotright> \<otimes>\<^bsub>R\<^esub> x1 [^] (2::nat) \<oplus>\<^bsub>R\<^esub> a) \<oslash>\<^bsub>R\<^esub> (\<guillemotleft>2\<guillemotright> \<otimes>\<^bsub>R\<^esub> y1)"
        have B1: "\<guillemotleft>2\<guillemotright> \<otimes>\<^bsub>R\<^esub> y1 = (2*y1) mod (int p)"
          by (simp add: mod_mult_right_eq mult.commute res_mult_eq res_of_integer_eq)
        have B2: "0 \<le> (2*y1) mod (int p)"
          using gt2 by auto
        have B3: "(\<guillemotleft>3\<guillemotright> \<otimes>\<^bsub>R\<^esub> x1 [^] (2::nat) \<oplus>\<^bsub>R\<^esub> a) = (3 * x1^2 + (int a)) mod p"
          by (metis mod_mod_trivial res_add_eq local.of_int_add local.of_int_mult 
                    res_of_integer_eq res_pow_eq)
        have B4: "?inv_2y1 mod p = ?inv_2y1"
          by (metis inv_mod_def mod_mod_trivial zmod_int) 
        have B5: "?l = (((3 * x1^2 + (int a)) mod p) * ?inv_2y1) mod p" 
          by (metis mod_mult_left_eq) 
        have B6: "?l = ((3 * x1^2 + (int a)) mod p) \<oslash>\<^bsub>R\<^esub> ?twoy1" 
          by (smt (verit, ccfv_SIG) B2 B4 R_def cring_class.of_nat_0 gt2 int_distrib(4) 
              int_nat_eq inv_mod_0' m_div_def m_gt_one mod_in_carrier nat_int of_nat_0_less_iff 
              res_to_cong_simps(2) res_zero_eq residues_prime.inv_mod_p_inv_in_ring 
              residues_prime.p_prime residues_prime_axioms) 
        have B7: "?l = (\<guillemotleft>3\<guillemotright> \<otimes>\<^bsub>R\<^esub> x1 [^] (2::nat) \<oplus>\<^bsub>R\<^esub> a) \<oslash>\<^bsub>R\<^esub> ?twoy1" using B6 B3 by argo
        have B8: "?l = ?l'" using B7 B1 by argo
        let ?x3  = "(?l^2 - 2*x1) mod (int p)"
        let ?x3' = "?l' [^] (2::nat) \<ominus>\<^bsub>R\<^esub> \<guillemotleft>2\<guillemotright> \<otimes>\<^bsub>R\<^esub> x1"
        have B9: "?x3 = ?x3'" 
          by (metis B8 of_int_diff mod_mult_left_eq res_mult_eq res_of_integer_eq res_pow_eq)
        let ?y3  = "(- y1 - ?l * (?x3 - x1)) mod (int p)"
        let ?y3' = "(\<ominus>\<^bsub>R\<^esub> y1 \<ominus>\<^bsub>R\<^esub> ?l' \<otimes>\<^bsub>R\<^esub> (?x3 \<ominus>\<^bsub>R\<^esub> x1))"
        have B10: "?y3 = ?y3'" 
          by (smt (verit) B8 B9 mod_diff_eq mod_mod_trivial mult_cong res_diff_eq res_neg_eq) 
        have B11: "add a p\<^sub>1 p\<^sub>2 = Point ?x3 ?y3"  
          using y_nneg add_eq_h1 B9 B10 P1 P2 x_eq by blast
        have B12: "point_madd a p\<^sub>1 p\<^sub>2 = Point ?x3 ?y3" 
          using B0 add_eq_h2 B9 B10 P1 P2 x_eq by algebra
        show ?thesis using B11 B12 by argo 
      qed
    next
      case x_neq: False
      let ?x2_x1     = "((x2 - x1) mod (int p))"
      let ?inv_x2_x1 = "int (inv_mod p (nat ?x2_x1))"
      let ?l  = "((y2 - y1) * ?inv_x2_x1) mod (int p)"
      let ?x3 = "(?l^2 - x1 - x2) mod (int p)"
      let ?y3 = "(- y1 - ?l * (?x3 - x1)) mod (int p)"
      have C1: "point_madd a p\<^sub>1 p\<^sub>2 = Point ?x3 ?y3" 
        unfolding point_madd_def Let_def using x_neq P1 P2 by auto
      let ?l'  = "(y2 \<ominus>\<^bsub>R\<^esub> y1) \<oslash>\<^bsub>R\<^esub> (x2 \<ominus>\<^bsub>R\<^esub> x1)"
      let ?x3' = "?l' [^] (2::nat) \<ominus>\<^bsub>R\<^esub> x1 \<ominus>\<^bsub>R\<^esub> x2"
      let ?y3' = "(\<ominus>\<^bsub>R\<^esub> y1 \<ominus>\<^bsub>R\<^esub> ?l' \<otimes>\<^bsub>R\<^esub> (?x3' \<ominus>\<^bsub>R\<^esub> x1))"
      have C2: "add a p\<^sub>1 p\<^sub>2 = Point ?x3' ?y3'" 
        unfolding add_def Let_def using x_neq P1 P2 by auto
      have C3: "?l = ?l'"
        by (smt (verit, ccfv_threshold) Euclidean_Rings.pos_mod_sign R_m_def gt2
        int_nat_eq int_ops(1) integral_iff inv_mod_0' m_div_def mod_in_carrier mod_mod_trivial 
        mult_cong nat_int nat_less_iff res_diff_eq residues.res_mult_eq residues_axioms zero_cong
        residues_prime.inv_mod_p_inv_in_ring residues_prime.p_prime residues_prime_axioms)
      have C4: "?x3 = ?x3'" 
        by (simp add: C3 mod_diff_left_eq res_diff_eq res_pow_eq) 
      have C5: "?y3 = ?y3'" 
        by (smt (verit) C3 C4 mod_diff_eq mod_mod_trivial mult_cong res_diff_eq res_neg_eq) 
      show ?thesis using C1 C2 C4 C5 by argo
    qed 
  qed
qed

lemma point_mult_eq [code]: "point_mult a n P = point_mmult a n P"
  apply (induct n) apply simp using point_add_eq by force

text \<open>Also in Elliptic_Test, they provide methods for converting a point in projective coordinates
to a point in affine coordinates, but not the other way around.  Here we provide a few more tools
for going between affine and projective coordinates.\<close>

definition get_x :: "int point \<Rightarrow> int" where
  "get_x P = (case P of
      Infinity  \<Rightarrow> 0
    | Point x y \<Rightarrow> x)"

definition get_y :: "int point \<Rightarrow> int" where
  "get_y P = (case P of
      Infinity  \<Rightarrow> 0
    | Point x y \<Rightarrow> y)"

lemma get_coords_correct:
  assumes "P = Point x y"
  shows   "P = Point (get_x P) (get_y P)"
  by (simp add: assms get_x_def get_y_def)

definition mmake_proj :: "int point \<Rightarrow> int ppoint" where
  "mmake_proj P = (if P = Infinity then (1,1,0) else (get_x P, get_y P, 1))"

lemma bezout_coeff_1: 
  assumes "1 < (x::nat)" 
  shows   "bezout_coefficients 1 x = (1,0)"
proof - 
  have 10: "1 div x = 0"  using assms(1) by fastforce 
  have 11: "x \<noteq> 0"        using assms(1) by fastforce
  have 12: "euclid_ext_aux 1 0 0 1 1 x = euclid_ext_aux 0 (1 - 0 * 0) 1 (0 - 0 * 1) x (1 mod x)"
    by (smt (verit, ccfv_threshold) 10 11 euclid_ext_aux.simps mult_cancel_left1 of_nat_1 
        of_nat_eq_0_iff of_nat_mod unique_euclidean_semiring_with_nat_class.of_nat_div) 
  have 1: "euclid_ext_aux 1 0 0 1 1 x = euclid_ext_aux 0 1 1 0 x 1"
    using 12 assms(1) by force
  have 20: "x div 1 = x"  by simp
  have 21: "(1::int) \<noteq> 0" by simp
  have 22: "euclid_ext_aux 0 1 1 0 x 1 = euclid_ext_aux 1 (0 - x * 1) 0 (1 - x * 0) 1 (x mod 1)"
    by (smt (verit, ccfv_threshold)20 21 euclid_ext_aux.simps mult_cancel_left1 of_nat_1 
        of_nat_eq_0_iff of_nat_mod unique_euclidean_semiring_with_nat_class.of_nat_div mod_by_1)
  have 2:  "euclid_ext_aux 0 1 1 0 x 1 = euclid_ext_aux 1 (0 - x) 0 1 1 0" 
    using 22 assms(1) by simp
  have 3: "euclid_ext_aux 1 (0 - x) 0 1 1 0 = ((1,0), 1)"
    by (metis (no_types, lifting) euclid_ext_aux.simps div_by_1 mult_1 mult_eq_0_iff 
        normalize_div unit_factor_1) 
  have 4: "euclid_ext 1 x = ((1,0), 1)"
    using 1 2 3 by presburger
  show ?thesis using 4 by simp
qed

lemma to_proj_to_aff: 
  assumes "0 \<le> get_x P" "get_x P < p" "0 \<le> get_y P" "get_y P < p" 
  shows   "mmake_affine (int p) (mmake_proj P) = P"
proof (cases P)
  case Infinity
  then show ?thesis using mmake_proj_def mmake_affine_def by simp
next
  case C: (Point x y)
  have Cx: "x = get_x P"            by (simp add: C get_x_def)
  have Cy: "y = get_y P"            by (simp add: C get_y_def)
  have C1: "mmake_proj P = (x,y,1)" using C Cx Cy mmake_proj_def by fastforce
  have C2: "bezout_coefficients 1 (int p) = (1,0)" using bezout_coeff_1 m_gt_one by fastforce 
  have C3: "1 **\<^bsub>(int p)\<^esub> x = x"    using assms(1,2) mmult_def Cx by simp
  have C4: "1 **\<^bsub>(int p)\<^esub> y = y"    using assms(3,4) mmult_def Cy by simp
  have C5: "mmake_affine (int p) (x,y,1) = Point x y"  using mmake_affine_def C2 C3 C4 by force
  show ?thesis                      using C C1 C5 by presburger 
qed

end (* residues_prime_gt2 context *)
end
