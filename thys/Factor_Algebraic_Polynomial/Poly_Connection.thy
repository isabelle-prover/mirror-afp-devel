section \<open>Resultants and Multivariate Polynomials\<close>

subsection \<open>Connecting Univariate and Multivariate Polynomials\<close>

text \<open>We define a conversion of multivariate polynomials into univariate polynomials
  w.r.t.\ a fixed variable $x$ and multivariate polynomials as coefficients.\<close>

theory Poly_Connection
  imports 
    Polynomials.MPoly_Type_Univariate
    Jordan_Normal_Form.Missing_Misc
    Polynomial_Interpolation.Ring_Hom_Poly
    Hermite_Lindemann.More_Multivariate_Polynomial_HLW
    Polynomials.MPoly_Type_Class
begin

lemma mpoly_is_unitE:
  fixes p :: "'a :: {comm_semiring_1, semiring_no_zero_divisors} mpoly"
  assumes "p dvd 1"
  obtains c where "p = Const c" "c dvd 1"
proof -
  obtain r where r: "p * r = 1"
    using assms by auto
  from r have [simp]: "p \<noteq> 0" "r \<noteq> 0"
    by auto
  have "0 = lead_monom (1 :: 'a mpoly)"
    by simp
  also have "1 = p * r"
    using r by simp
  also have "lead_monom (p * r) = lead_monom p + lead_monom r"
    by (intro lead_monom_mult) auto
  finally have "lead_monom p = 0"
    by simp
  hence "vars p = {}"
    by (simp add: lead_monom_eq_0_iff)
  hence *: "p = Const (lead_coeff p)"
    by (auto simp: vars_empty_iff)

  have "1 = lead_coeff (1 :: 'a mpoly)"
    by simp
  also have "1 = p * r"
    using r by simp
  also have "lead_coeff (p * r) = lead_coeff p * lead_coeff r"
    by (intro lead_coeff_mult) auto
  finally have "lead_coeff p dvd 1"
    using dvdI by blast
  with * show ?thesis using that
    by blast
qed

lemma Const_eq_Const_iff [simp]:
  "Const c = Const c' \<longleftrightarrow> c = c'"
  by (metis lead_coeff_Const)

lemma is_unit_ConstI [intro]: "c dvd 1 \<Longrightarrow> Const c dvd 1"
  by (metis dvd_def mpoly_Const_1 mpoly_Const_mult)

lemma is_unit_Const_iff:
  fixes c :: "'a :: {comm_semiring_1, semiring_no_zero_divisors}"
  shows "Const c dvd 1 \<longleftrightarrow> c dvd 1"
proof
  assume "Const c dvd 1"
  thus "c dvd 1"
    by (auto elim!: mpoly_is_unitE)
qed auto

lemma vars_emptyE: "vars p = {} \<Longrightarrow> (\<And>c. p = Const c \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: vars_empty_iff)

lemma degree_geI:
  assumes "MPoly_Type.coeff p m \<noteq> 0"
  shows   "MPoly_Type.degree p i \<ge> Poly_Mapping.lookup m i"
proof -
  have "lookup m i \<le> Max (insert 0 ((\<lambda>m. lookup m i) ` keys (mapping_of p)))"
  proof (rule Max.coboundedI)
    show "lookup m i \<in> insert 0 ((\<lambda>m. lookup m i) ` keys (mapping_of p))"
      using assms by (auto simp: coeff_keys)
  qed auto
  thus ?thesis unfolding MPoly_Type.degree_def by auto
qed

lemma monom_of_degree_exists:
  assumes "p \<noteq> 0"
  obtains m where "MPoly_Type.coeff p m \<noteq> 0" "Poly_Mapping.lookup m i = MPoly_Type.degree p i"
proof (cases "MPoly_Type.degree p i = 0")
  case False
  have "MPoly_Type.degree p i = Max (insert 0 ((\<lambda>m. lookup m i) ` keys (mapping_of p)))"
    by (simp add: MPoly_Type.degree_def)
  also have "\<dots> \<in> insert 0 ((\<lambda>m. lookup m i) ` keys (mapping_of p))"
    by (rule Max_in) auto
  finally show ?thesis
    using False that by (auto simp: coeff_keys)
next
  case [simp]: True
  from assms obtain m where m: "MPoly_Type.coeff p m \<noteq> 0"
    using coeff_all_0 by blast
  show ?thesis using degree_geI[of p m i] m
    by (intro that[of m]) auto
qed

lemma degree_leI:
  assumes "\<And>m. Poly_Mapping.lookup m i > n \<Longrightarrow> MPoly_Type.coeff p m = 0"
  shows   "MPoly_Type.degree p i \<le> n"
proof (cases "p = 0")
  case False
  obtain m where m: "MPoly_Type.coeff p m \<noteq> 0" "Poly_Mapping.lookup m i = MPoly_Type.degree p i"
    using monom_of_degree_exists False by blast
  with assms show ?thesis
    by force
qed auto

lemma coeff_gt_degree_eq_0:
  assumes "Poly_Mapping.lookup m i > MPoly_Type.degree p i"
  shows   "MPoly_Type.coeff p m = 0"
  using assms degree_geI leD by blast

lemma vars_altdef: "vars p = (\<Union>m\<in>{m. MPoly_Type.coeff p m \<noteq> 0}. keys m)"
  unfolding vars_def
  by (intro arg_cong[where f = "\<Union>"] image_cong refl) (simp flip: coeff_keys)

lemma degree_pos_iff: "MPoly_Type.degree p x > 0 \<longleftrightarrow> x \<in> vars p"
proof
  assume "MPoly_Type.degree p x > 0"
  hence "p \<noteq> 0" by auto
  then obtain m where m: "lookup m x = MPoly_Type.degree p x" "MPoly_Type.coeff p m \<noteq> 0"
    using monom_of_degree_exists[of p x] by metis
  from m and \<open>MPoly_Type.degree p x > 0\<close> have "x \<in> keys m"
    by (simp add: in_keys_iff)
  with m show "x \<in> vars p"
    by (auto simp: vars_altdef)
next
  assume "x \<in> vars p"
  then obtain m where m: "x \<in> keys m" "MPoly_Type.coeff p m \<noteq> 0"
    by (auto simp: vars_altdef)
  have "0 < lookup m x"
    using m by (auto simp: in_keys_iff)
  also from m have "\<dots> \<le> MPoly_Type.degree p x"
    by (intro degree_geI) auto
  finally show "MPoly_Type.degree p x > 0" .
qed 

lemma degree_eq_0_iff: "MPoly_Type.degree p x = 0 \<longleftrightarrow> x \<notin> vars p"
  using degree_pos_iff[of p x] by auto

lemma MPoly_Type_monom_zero[simp]: "MPoly_Type.monom m 0 = 0"
  by (simp add: More_MPoly_Type.coeff_monom coeff_all_0)

lemma vars_monom_keys': "vars (MPoly_Type.monom m c) = (if c = 0 then {} else keys m)"
  by (cases "c = 0") (auto simp: vars_monom_keys)

lemma Const_eq_0_iff [simp]: "Const c = 0 \<longleftrightarrow> c = 0"
  by (metis lead_coeff_Const mpoly_Const_0)

lemma monom_remove_key: "MPoly_Type.monom m (a :: 'a :: semiring_1) = 
  MPoly_Type.monom (remove_key x m) a * MPoly_Type.monom (Poly_Mapping.single x (lookup m x)) 1"
  unfolding MPoly_Type.mult_monom
  by (rule arg_cong2[of _ _ _ _ MPoly_Type.monom], auto simp: remove_key_sum)

lemma MPoly_Type_monom_0_iff[simp]: "MPoly_Type.monom m x = 0 \<longleftrightarrow> x = 0"
  by (metis (full_types) MPoly_Type_monom_zero More_MPoly_Type.coeff_monom when_def) 

lemma vars_signof[simp]: "vars (signof x) = {}" 
  by (simp add: sign_def)

lemma prod_mset_Const: "prod_mset (image_mset Const A) = Const (prod_mset A)"
  by (induction A) (auto simp: mpoly_Const_mult)

lemma Const_eq_product_iff:
  fixes c :: "'a :: idom"
  assumes "c \<noteq> 0"
  shows   "Const c = a * b \<longleftrightarrow> (\<exists>a' b'. a = Const a' \<and> b = Const b' \<and> c = a' * b')"
proof
  assume *: "Const c = a * b"
  have "lead_monom (a * b) = 0"
    by (auto simp flip: *)
  hence "lead_monom a = 0 \<and> lead_monom b = 0"
    by (subst (asm) lead_monom_mult) (use assms * in auto)
  hence "vars a = {}" "vars b = {}"
    by (auto simp: lead_monom_eq_0_iff)
  then obtain a' b' where "a = Const a'" "b = Const b'"
    by (auto simp: vars_empty_iff)
  with * show "(\<exists>a' b'. a = Const a' \<and> b = Const b' \<and> c = a' * b')"
    by (auto simp flip: mpoly_Const_mult)
qed (auto simp: mpoly_Const_mult)

lemma irreducible_Const_iff [simp]:
  "irreducible (Const (c :: 'a :: idom)) \<longleftrightarrow> irreducible c"
proof
  assume *: "irreducible (Const c)"
  show "irreducible c"
  proof (rule irreducibleI)
    fix a b assume "c = a * b"
    hence "Const c = Const a * Const b"
      by (simp add: mpoly_Const_mult)
    with * have "Const a dvd 1 \<or> Const b dvd 1"
      by blast
    thus "a dvd 1 \<or> b dvd 1"
      by (meson is_unit_Const_iff)
  qed (use * in \<open>auto simp: irreducible_def\<close>)
next
  assume *: "irreducible c"
  have [simp]: "c \<noteq> 0"
    using * by auto
  show "irreducible (Const c)"
  proof (rule irreducibleI)
    fix a b assume "Const c = a * b"
    then obtain a' b' where [simp]: "a = Const a'" "b = Const b'" and "c = a' * b'"
      by (auto simp: Const_eq_product_iff)
    hence "a' dvd 1 \<or> b' dvd 1"
      using * by blast
    thus "a dvd 1 \<or> b dvd 1"
      by auto
  qed (use * in \<open>auto simp: irreducible_def is_unit_Const_iff\<close>)
qed

lemma Const_dvd_Const_iff [simp]: "Const a dvd Const b \<longleftrightarrow> a dvd b"
proof
  assume "a dvd b"
  then obtain c where "b = a * c"
    by auto
  hence "Const b = Const a * Const c"
    by (auto simp: mpoly_Const_mult)
  thus "Const a dvd Const b"
    by simp
next
  assume "Const a dvd Const b"
  then obtain p where p: "Const b = Const a * p"
    by auto
  have "MPoly_Type.coeff (Const b) 0 = MPoly_Type.coeff (Const a * p) 0"
    using p by simp
  also have "\<dots> = MPoly_Type.coeff (Const a) 0 * MPoly_Type.coeff p 0"
    using mpoly_coeff_times_0 by blast
  finally show "a dvd b"
    by (simp add: mpoly_coeff_Const)
qed


text \<open>The lemmas above should be moved into the right theories. The part below is on the new 
connection between multivariate polynomials and univariate polynomials.\<close>

text \<open>The imported theories only allow a conversion from one-variable mpoly's to poly and vice-versa.
  However, we require a conversion from arbitrary mpoly's into poly's with mpolys as coefficients.\<close>

(* converts a multi-variate polynomial into a univariate polynomial with multivariate coefficients *)
definition mpoly_to_mpoly_poly :: "nat \<Rightarrow> 'a :: comm_ring_1 mpoly \<Rightarrow> 'a mpoly poly" where
  "mpoly_to_mpoly_poly x p = (\<Sum>m .
        Polynomial.monom (MPoly_Type.monom (remove_key x m) (MPoly_Type.coeff p m)) (lookup m x))" 

lemma mpoly_to_mpoly_poly_add [simp]:
  "mpoly_to_mpoly_poly x (p + q) = mpoly_to_mpoly_poly x p + mpoly_to_mpoly_poly x q" 
  unfolding mpoly_to_mpoly_poly_def  More_MPoly_Type.coeff_add[symmetric]  MPoly_Type.monom_add add_monom[symmetric]
  by (rule Sum_any.distrib) auto

lemma mpoly_to_mpoly_poly_monom: "mpoly_to_mpoly_poly x (MPoly_Type.monom m a) = Polynomial.monom (MPoly_Type.monom (remove_key x m) a) (lookup m x)" 
proof -
  have "mpoly_to_mpoly_poly x (MPoly_Type.monom m a) = 
    (\<Sum> m'. Polynomial.monom (MPoly_Type.monom (remove_key x m') a) (lookup m' x) when m' = m)" 
    unfolding mpoly_to_mpoly_poly_def 
    by (intro Sum_any.cong, auto simp: when_def More_MPoly_Type.coeff_monom)
  also have "\<dots> = Polynomial.monom (MPoly_Type.monom (remove_key x m) a) (lookup m x)" 
    unfolding Sum_any_when_equal ..
  finally show ?thesis .
qed

lemma remove_key_transfer [transfer_rule]:
  "rel_fun (=) (rel_fun (pcr_poly_mapping (=) (=)) (pcr_poly_mapping (=) (=)))
     (\<lambda>k0 f k. f k when k \<noteq> k0) remove_key"
  unfolding pcr_poly_mapping_def cr_poly_mapping_def OO_def
  by (auto simp: rel_fun_def remove_key_lookup)

lemma remove_key_0 [simp]: "remove_key x 0 = 0"
  by transfer auto

lemma remove_key_single' [simp]:
  "x \<noteq> y \<Longrightarrow> remove_key x (Poly_Mapping.single y n) = Poly_Mapping.single y n"
  by transfer (auto simp: when_def fun_eq_iff)


lemma poly_coeff_Sum_any: 
  assumes "finite {x. f x \<noteq> 0}"
  shows   "poly.coeff (Sum_any f) n = Sum_any (\<lambda>x. poly.coeff (f x) n)"
proof -
  have "Sum_any f = (\<Sum>x | f x \<noteq> 0. f x)"
    by (rule Sum_any.expand_set)
  also have "poly.coeff \<dots> n = (\<Sum>x | f x \<noteq> 0. poly.coeff (f x) n)"
    by (simp add: Polynomial.coeff_sum)
  also have "\<dots> = Sum_any (\<lambda>x. poly.coeff (f x) n)"
    by (rule Sum_any.expand_superset [symmetric]) (use assms in auto)
  finally show ?thesis .
qed

lemma coeff_coeff_mpoly_to_mpoly_poly:
  "MPoly_Type.coeff (poly.coeff (mpoly_to_mpoly_poly x p) n) m =
     (MPoly_Type.coeff p (m + Poly_Mapping.single x n) when lookup m x = 0)"
proof -
  have "MPoly_Type.coeff (poly.coeff (mpoly_to_mpoly_poly x p) n) m =
          MPoly_Type.coeff (\<Sum>a. MPoly_Type.monom (remove_key x a) (MPoly_Type.coeff p a) when lookup a x = n) m"
    unfolding mpoly_to_mpoly_poly_def by (subst poly_coeff_Sum_any) (auto simp: when_def)
  also have "\<dots> = (\<Sum>xa. MPoly_Type.coeff (MPoly_Type.monom (remove_key x xa) (MPoly_Type.coeff p xa)) m when lookup xa x = n)"
    by (subst coeff_Sum_any, force) (auto simp: when_def intro!: Sum_any.cong)
  also have "\<dots> = (\<Sum>a. MPoly_Type.coeff p a when lookup a x = n \<and> m = remove_key x a)"
    by (intro Sum_any.cong) (simp add: More_MPoly_Type.coeff_monom when_def)
  also have "(\<lambda>a. lookup a x = n \<and> m = remove_key x a) =
             (\<lambda>a. lookup m x = 0 \<and> a = m + Poly_Mapping.single x n)"
    by (rule ext, transfer) (auto simp: fun_eq_iff when_def)
  also have "(\<Sum>a. MPoly_Type.coeff p a when \<dots> a) =
             (\<Sum>a. MPoly_Type.coeff p a when lookup m x = 0 when a = m + Poly_Mapping.single x n)"
    by (intro Sum_any.cong) (auto simp: when_def)
  also have "\<dots> = (MPoly_Type.coeff p (m + Poly_Mapping.single x n) when lookup m x = 0)"
    by (rule Sum_any_when_equal)
  finally show ?thesis .
qed

lemma mpoly_to_mpoly_poly_Const [simp]:
  "mpoly_to_mpoly_poly x (Const c) = [:Const c:]"
proof -
  have "mpoly_to_mpoly_poly x (Const c) =
          (\<Sum>m. Polynomial.monom (MPoly_Type.monom (remove_key x m)
                  (MPoly_Type.coeff (Const c) m)) (lookup m x) when m = 0)"
    unfolding mpoly_to_mpoly_poly_def 
    by (intro Sum_any.cong) (auto simp: when_def mpoly_coeff_Const)
  also have "\<dots> = [:Const c:]"
    by (subst Sum_any_when_equal)
       (auto simp: mpoly_coeff_Const monom_altdef simp flip: Const_conv_monom)
  finally show ?thesis .
qed

lemma mpoly_to_mpoly_poly_Var:
  "mpoly_to_mpoly_poly x (Var y) = (if x = y then [:0, 1:] else [:Var y:])"
proof -
  have "mpoly_to_mpoly_poly x (Var y) = 
          (\<Sum>a. Polynomial.monom (MPoly_Type.monom (remove_key x a) 1) (lookup a x)
             when a = Poly_Mapping.single y 1)"
    unfolding mpoly_to_mpoly_poly_def by (intro Sum_any.cong) (auto simp: when_def coeff_Var)
  also have "\<dots> = (if x = y then [:0, 1:] else [:Var y:])"
    by (auto simp: Polynomial.monom_altdef lookup_single Var_altdef)
  finally show ?thesis .
qed

lemma mpoly_to_mpoly_poly_Var_this [simp]:
  "mpoly_to_mpoly_poly x (Var x) = [:0, 1:]"
  "x \<noteq> y \<Longrightarrow> mpoly_to_mpoly_poly x (Var y) = [:Var y:]"
  by (simp_all add: mpoly_to_mpoly_poly_Var)

lemma mpoly_to_mpoly_poly_uminus [simp]:
  "mpoly_to_mpoly_poly x (-p) = -mpoly_to_mpoly_poly x p"
  unfolding mpoly_to_mpoly_poly_def
  by (auto simp: monom_uminus Sum_any_uminus simp flip: minus_monom)

lemma mpoly_to_mpoly_poly_diff [simp]:
  "mpoly_to_mpoly_poly x (p - q) = mpoly_to_mpoly_poly x p - mpoly_to_mpoly_poly x q"
  by (subst diff_conv_add_uminus, subst mpoly_to_mpoly_poly_add) auto

lemma mpoly_to_mpoly_poly_0 [simp]:
  "mpoly_to_mpoly_poly x 0 = 0"
  unfolding mpoly_Const_0 [symmetric] mpoly_to_mpoly_poly_Const by simp

lemma mpoly_to_mpoly_poly_1 [simp]:
  "mpoly_to_mpoly_poly x 1 = 1"
  unfolding mpoly_Const_1 [symmetric] mpoly_to_mpoly_poly_Const by simp

lemma mpoly_to_mpoly_poly_of_nat [simp]:
  "mpoly_to_mpoly_poly x (of_nat n) = of_nat n"
  unfolding of_nat_mpoly_eq mpoly_to_mpoly_poly_Const of_nat_poly ..

lemma mpoly_to_mpoly_poly_of_int [simp]:
  "mpoly_to_mpoly_poly x (of_int n) = of_int n"
  unfolding of_nat_mpoly_eq mpoly_to_mpoly_poly_Const of_nat_poly by (cases n) auto

lemma mpoly_to_mpoly_poly_numeral [simp]:
  "mpoly_to_mpoly_poly x (numeral n) = numeral n"
  using mpoly_to_mpoly_poly_of_nat[of x "numeral n"] by (simp del: mpoly_to_mpoly_poly_of_nat)

lemma coeff_monom_mult':
  "MPoly_Type.coeff (MPoly_Type.monom m a * q) m' =
   (a * MPoly_Type.coeff q (m' - m) when lookup m' \<ge> lookup m)"
proof (cases "lookup m' \<ge> lookup m")
  case True
  have "a * MPoly_Type.coeff q (m' - m) = MPoly_Type.coeff (MPoly_Type.monom m a * q) (m + (m' - m))"
    by (rule More_MPoly_Type.coeff_monom_mult [symmetric])
  also have "m + (m' - m) = m'"
    using True by transfer (auto simp: le_fun_def)
  finally show ?thesis 
    using True by (simp add: when_def)
next
  case False
  have "MPoly_Type.coeff (MPoly_Type.monom m a * q) m' =
          (\<Sum>m1. a * (\<Sum>m2. MPoly_Type.coeff q m2 when m' = m1 + m2) when m1 = m)"
    unfolding coeff_mpoly_times prod_fun_def
    by (intro Sum_any.cong) (auto simp: More_MPoly_Type.coeff_monom when_def)
  also have "\<dots> = a * (\<Sum>m2. MPoly_Type.coeff q m2 when m' = m + m2)"
    by (subst Sum_any_when_equal) auto
  also have "(\<lambda>m2. m' = m + m2) = (\<lambda>m2. False)"
    by (rule ext) (use False in \<open>transfer, auto simp: le_fun_def\<close>)
  finally show ?thesis
    using False by simp
qed

lemma mpoly_to_mpoly_poly_mult_monom:
  "mpoly_to_mpoly_poly x (MPoly_Type.monom m a * q) =
     Polynomial.monom (MPoly_Type.monom (remove_key x m) a) (lookup m x) * mpoly_to_mpoly_poly x q"
  (is "?lhs = ?rhs")
proof (rule poly_eqI, rule mpoly_eqI)
  fix n :: nat and mon :: "nat \<Rightarrow>\<^sub>0 nat"
  have "MPoly_Type.coeff (poly.coeff ?lhs n) mon =
          (a * MPoly_Type.coeff q (mon + Poly_Mapping.single x n - m)
          when lookup m \<le> lookup (mon + Poly_Mapping.single x n) \<and> lookup mon x = 0)"
    by (simp add: coeff_coeff_mpoly_to_mpoly_poly coeff_monom_mult' when_def)
  have "MPoly_Type.coeff (poly.coeff ?rhs n) mon =
          (a * MPoly_Type.coeff q (mon - remove_key x m + Poly_Mapping.single x (n - lookup m x))
          when lookup (remove_key x m) \<le> lookup mon \<and> lookup m x \<le> n \<and> lookup mon x = 0)"
    by (simp add: coeff_coeff_mpoly_to_mpoly_poly coeff_monom_mult' lookup_minus_fun
                  remove_key_lookup Missing_Polynomial.coeff_monom_mult when_def)
  also have "lookup (remove_key x m) \<le> lookup mon \<and> lookup m x \<le> n \<and> lookup mon x = 0 \<longleftrightarrow>
             lookup m \<le> lookup (mon + Poly_Mapping.single x n) \<and> lookup mon x = 0" (is "_ = ?P")
    by transfer (auto simp: when_def le_fun_def)
  also have "mon - remove_key x m + Poly_Mapping.single x (n - lookup m x) = mon + Poly_Mapping.single x n - m" if ?P
    using that by transfer (auto simp: fun_eq_iff when_def)
  hence "(a * MPoly_Type.coeff q (mon - remove_key x m + Poly_Mapping.single x (n - lookup m x)) when ?P) =
         (a * MPoly_Type.coeff q \<dots> when ?P)"
    by (intro when_cong) auto
  also have "\<dots> = MPoly_Type.coeff (poly.coeff ?lhs n) mon"
    by (simp add: coeff_coeff_mpoly_to_mpoly_poly coeff_monom_mult' when_def)
  finally show "MPoly_Type.coeff (poly.coeff ?lhs n) mon = MPoly_Type.coeff (poly.coeff ?rhs n) mon" ..
qed

lemma mpoly_to_mpoly_poly_mult [simp]:
  "mpoly_to_mpoly_poly x (p * q) = mpoly_to_mpoly_poly x p * mpoly_to_mpoly_poly x q"
  by (induction p arbitrary: q rule: mpoly_induct)
     (simp_all add: mpoly_to_mpoly_poly_monom mpoly_to_mpoly_poly_mult_monom ring_distribs)

lemma coeff_mpoly_to_mpoly_poly:
  "Polynomial.coeff (mpoly_to_mpoly_poly x p) n =
     Sum_any (\<lambda>m. MPoly_Type.monom (remove_key x m) (MPoly_Type.coeff p m) when Poly_Mapping.lookup m x = n)"
  unfolding mpoly_to_mpoly_poly_def by (subst poly_coeff_Sum_any) (auto simp: when_def)

lemma mpoly_coeff_to_mpoly_poly_coeff:
  "MPoly_Type.coeff p m = MPoly_Type.coeff (poly.coeff (mpoly_to_mpoly_poly x p) (lookup m x)) (remove_key x m)"
proof -
  have "MPoly_Type.coeff (poly.coeff (mpoly_to_mpoly_poly x p) (lookup m x)) (remove_key x m) =
        (\<Sum>xa. MPoly_Type.coeff (MPoly_Type.monom (remove_key x xa) (MPoly_Type.coeff p xa) when
             lookup xa x = lookup m x) (remove_key x m))"
    by (subst coeff_mpoly_to_mpoly_poly, subst coeff_Sum_any) auto
  also have "\<dots> = (\<Sum>xa. MPoly_Type.coeff (MPoly_Type.monom (remove_key x xa) (MPoly_Type.coeff p xa)) (remove_key x m)
                    when lookup xa x = lookup m x)"
    by (intro Sum_any.cong) (auto simp: when_def)
  also have "\<dots> = (\<Sum>xa. MPoly_Type.coeff p xa when remove_key x m = remove_key x xa \<and> lookup xa x = lookup m x)"
    by (intro Sum_any.cong) (auto simp: More_MPoly_Type.coeff_monom when_def)
  also have "(\<lambda>xa. remove_key x m = remove_key x xa \<and> lookup xa x = lookup m x) = (\<lambda>xa. xa = m)"
    using remove_key_sum by metis
  also have "(\<Sum>xa. MPoly_Type.coeff p xa when xa = m) = MPoly_Type.coeff p m"
    by simp
  finally show ?thesis ..
qed

lemma degree_mpoly_to_mpoly_poly [simp]:
  "Polynomial.degree (mpoly_to_mpoly_poly x p) = MPoly_Type.degree p x"
proof (rule antisym)
  show "Polynomial.degree (mpoly_to_mpoly_poly x p) \<le> MPoly_Type.degree p x"
  proof (intro Polynomial.degree_le allI impI)
    fix i assume i: "i > MPoly_Type.degree p x"
    have "poly.coeff (mpoly_to_mpoly_poly x p) i =
            (\<Sum>m. 0 when lookup m x = i)"
      unfolding coeff_mpoly_to_mpoly_poly using i
      by (intro Sum_any.cong when_cong refl) (auto simp: coeff_gt_degree_eq_0)
    also have "\<dots> = 0"
      by simp
    finally show "poly.coeff (mpoly_to_mpoly_poly x p) i = 0" .
  qed
next
  show "Polynomial.degree (mpoly_to_mpoly_poly x p) \<ge> MPoly_Type.degree p x"
  proof (cases "p = 0")
    case False
    then obtain m where m: "MPoly_Type.coeff p m \<noteq> 0" "lookup m x = MPoly_Type.degree p x"
      using monom_of_degree_exists by blast
    show "Polynomial.degree (mpoly_to_mpoly_poly x p) \<ge> MPoly_Type.degree p x"
    proof (rule Polynomial.le_degree)
      have "0 \<noteq> MPoly_Type.coeff p m"
        using m by auto
      also have "MPoly_Type.coeff p m = MPoly_Type.coeff (poly.coeff (mpoly_to_mpoly_poly x p) (lookup m x)) (remove_key x m)"
        by (rule mpoly_coeff_to_mpoly_poly_coeff)
      finally show "poly.coeff (mpoly_to_mpoly_poly x p) (MPoly_Type.degree p x) \<noteq> 0"
        using m by auto
    qed
  qed auto
qed

text \<open>The upcoming lemma is similar to @{thm reduce_nested_mpoly_extract_var}.\<close>
lemma poly_mpoly_to_mpoly_poly:
  "poly (mpoly_to_mpoly_poly x p) (Var x) = p" 
proof (induct p rule: mpoly_induct)
  case (monom m a)
  show ?case unfolding mpoly_to_mpoly_poly_monom poly_monom
    by (transfer, simp add: Var\<^sub>0_power mult_single remove_key_sum)
next
  case (sum p1 p2 m a)
  then show ?case by (simp add: mpoly_to_mpoly_poly_add)
qed

lemma mpoly_to_mpoly_poly_eq_iff [simp]:
  "mpoly_to_mpoly_poly x p = mpoly_to_mpoly_poly x q \<longleftrightarrow> p = q"
proof
  assume "mpoly_to_mpoly_poly x p = mpoly_to_mpoly_poly x q"
  hence "poly (mpoly_to_mpoly_poly x p) (Var x) =
         poly (mpoly_to_mpoly_poly x q) (Var x)"
    by simp
  thus "p = q"
    by (auto simp: poly_mpoly_to_mpoly_poly)
qed auto

text \<open>Evaluation, i.e., insertion of concrete values is identical\<close>
lemma insertion_mpoly_to_mpoly_poly: assumes "\<And> y. y \<noteq> x \<Longrightarrow> \<beta> y = \<alpha> y" 
  shows "poly (map_poly (insertion \<beta>) (mpoly_to_mpoly_poly x p)) (\<alpha> x) = insertion \<alpha> p" 
proof (induct p rule: mpoly_induct)
  case (monom m a)
  let ?rkm = "remove_key x m" 
  have to_alpha: "insertion \<beta> (MPoly_Type.monom ?rkm a) = insertion \<alpha> (MPoly_Type.monom ?rkm a)" 
    by (rule insertion_irrelevant_vars, rule assms, insert vars_monom_subset[of ?rkm a], auto simp: remove_key_keys[symmetric])
  have main: "insertion \<alpha> (MPoly_Type.monom ?rkm a) * \<alpha> x ^ lookup m x = insertion \<alpha> (MPoly_Type.monom m a)" 
    unfolding monom_remove_key[of m a x] insertion_mult
    by (metis insertion_single mult.left_neutral)
  show ?case using main to_alpha
    by (simp add: mpoly_to_mpoly_poly_monom map_poly_monom poly_monom)
next
  case (sum p1 p2 m a)
  then show ?case by (simp add: mpoly_to_mpoly_poly_add insertion_add map_poly_add) 
qed

lemma mpoly_to_mpoly_poly_dvd_iff [simp]:
  "mpoly_to_mpoly_poly x p dvd mpoly_to_mpoly_poly x q \<longleftrightarrow> p dvd q"
proof
  assume "mpoly_to_mpoly_poly x p dvd mpoly_to_mpoly_poly x q"
  hence "poly (mpoly_to_mpoly_poly x p) (Var x) dvd poly (mpoly_to_mpoly_poly x q) (Var x)"
    by (intro poly_hom.hom_dvd)
  thus "p dvd q"
    by (simp add: poly_mpoly_to_mpoly_poly)
qed auto

lemma vars_coeff_mpoly_to_mpoly_poly: "vars (poly.coeff (mpoly_to_mpoly_poly x p) i) \<subseteq> vars p - {x}" 
  unfolding mpoly_to_mpoly_poly_def Sum_any.expand_set Polynomial.coeff_sum More_MPoly_Type.coeff_monom
  apply (rule order.trans[OF vars_setsum], force)
  apply (rule UN_least, simp)
  apply (intro impI order.trans[OF vars_monom_subset])
  by (simp add: remove_key_keys[symmetric] Diff_mono SUP_upper2 coeff_keys vars_def)


locale transfer_mpoly_to_mpoly_poly =
  fixes x :: nat
begin

definition R :: "'a :: comm_ring_1 mpoly poly \<Rightarrow> 'a mpoly \<Rightarrow> bool" where
  "R p p' \<longleftrightarrow> p = mpoly_to_mpoly_poly x p'"

context
  includes lifting_syntax
begin

lemma transfer_0 [transfer_rule]: "R 0 0"
  and transfer_1 [transfer_rule]: "R 1 1"
  and transfer_Const [transfer_rule]: "R [:Const c:] (Const c)"
  and transfer_uminus [transfer_rule]: "(R ===> R) uminus uminus"
  and transfer_of_nat [transfer_rule]: "((=) ===> R) of_nat of_nat"
  and transfer_of_int [transfer_rule]: "((=) ===> R) of_nat of_nat"
  and transfer_numeral [transfer_rule]: "((=) ===> R) of_nat of_nat"
  and transfer_add [transfer_rule]: "(R ===> R ===> R) (+) (+)"
  and transfer_diff [transfer_rule]: "(R ===> R ===> R) (+) (+)"
  and transfer_mult [transfer_rule]: "(R ===> R ===> R) (*) (*)"
  and transfer_dvd [transfer_rule]: "(R ===> R ===> (=)) (dvd) (dvd)"
  and transfer_monom [transfer_rule]:
        "((=) ===> (=) ===> R)
          (\<lambda>m a. Polynomial.monom (MPoly_Type.monom (remove_key x m) a) (lookup m x))
          MPoly_Type.monom"
  and transfer_coeff [transfer_rule]:
        "(R ===> (=) ===> (=))
           (\<lambda>p m. MPoly_Type.coeff (poly.coeff p (lookup m x)) (remove_key x m))
           MPoly_Type.coeff"
  and transfer_degree [transfer_rule]:
        "(R ===> (=)) Polynomial.degree (\<lambda>p. MPoly_Type.degree p x)"
  unfolding R_def
  by (auto simp: rel_fun_def mpoly_to_mpoly_poly_monom 
           simp flip: mpoly_coeff_to_mpoly_poly_coeff)


lemma transfer_vars [transfer_rule]:
  assumes [transfer_rule]: "R p p'"
  shows   "(\<Union>i. vars (poly.coeff p i)) \<union> (if Polynomial.degree p = 0 then {} else {x}) = vars p'"
    (is "?A \<union> ?B = _")
proof (intro equalityI)
  have "vars p' = vars (poly p (Var x))"
    using assms by (simp add: R_def poly_mpoly_to_mpoly_poly)
  also have "poly p (Var x) = (\<Sum>i\<le>Polynomial.degree p. poly.coeff p i * Var x ^ i)"
    unfolding poly_altdef ..
  also have "vars \<dots> \<subseteq> (\<Union>i. vars (poly.coeff p i) \<union> (if Polynomial.degree p = 0 then {} else {x}))"
  proof (intro order.trans[OF vars_sum] UN_mono order.trans[OF vars_mult] Un_mono)
    fix i :: nat
    assume i: "i \<in> {..Polynomial.degree p}"
    show "vars (Var x ^ i) \<subseteq> (if Polynomial.degree p = 0 then {} else {x})"
    proof (cases "Polynomial.degree p = 0")
      case False
      thus ?thesis
        by (intro order.trans[OF vars_power]) (auto simp: vars_Var)
    qed (use i in auto)
  qed auto
  finally show "vars p' \<subseteq> ?A \<union> ?B" by blast
next
  have "?A \<subseteq> vars p'"
    using assms vars_coeff_mpoly_to_mpoly_poly by (auto simp: R_def)
  moreover have "?B \<subseteq> vars p'"
    using assms by (auto simp: R_def degree_pos_iff)
  ultimately show "?A \<union> ?B \<subseteq> vars p'"
    by blast
qed   
    
lemma right_total [transfer_rule]: "right_total R"
  unfolding right_total_def
proof safe
  fix p' :: "'a mpoly"
  show "\<exists>p. R p p'"
    by (rule exI[of _ "mpoly_to_mpoly_poly x p'"]) (auto simp: R_def)
qed

lemma bi_unique [transfer_rule]: "bi_unique R"
  unfolding bi_unique_def by (auto simp: R_def)

end

end


lemma mpoly_degree_mult_eq:
  fixes p q :: "'a :: idom mpoly"
  assumes "p \<noteq> 0" "q \<noteq> 0"
  shows   "MPoly_Type.degree (p * q) x = MPoly_Type.degree p x + MPoly_Type.degree q x"
proof -
  interpret transfer_mpoly_to_mpoly_poly x .
  define deg :: "'a mpoly \<Rightarrow> nat" where "deg = (\<lambda>p. MPoly_Type.degree p x)"
  have [transfer_rule]: "rel_fun R (=) Polynomial.degree deg"
    using transfer_degree unfolding deg_def .

  have "deg (p * q) = deg p + deg q"
    using assms unfolding deg_def [symmetric]
    by transfer (simp add: degree_mult_eq)
  thus ?thesis
    by (simp add: deg_def)
qed



text \<open>Converts a multi-variate polynomial into a univariate polynomial via inserting values for all but one variable\<close>
definition partial_insertion :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a :: comm_ring_1 mpoly \<Rightarrow> 'a poly" where
  "partial_insertion \<alpha> x p = map_poly (insertion \<alpha>) (mpoly_to_mpoly_poly x p)" 

lemma comm_ring_hom_insertion: "comm_ring_hom (insertion \<alpha>)"
  by (unfold_locales, auto simp: insertion_add insertion_mult)


lemma partial_insertion_add: "partial_insertion \<alpha> x (p + q) = partial_insertion \<alpha> x p + partial_insertion \<alpha> x q" 
proof -
  interpret i: comm_ring_hom "insertion \<alpha>" by (rule comm_ring_hom_insertion)
  show ?thesis unfolding partial_insertion_def mpoly_to_mpoly_poly_add hom_distribs ..
qed

lemma partial_insertion_monom: "partial_insertion \<alpha> x (MPoly_Type.monom m a) = Polynomial.monom (insertion \<alpha> (MPoly_Type.monom (remove_key x m) a)) (lookup m x)" 
  unfolding partial_insertion_def mpoly_to_mpoly_poly_monom 
  by (subst map_poly_monom, auto)

text \<open>Partial insertion + insertion of last value is identical to (full) insertion\<close>
lemma insertion_partial_insertion: assumes "\<And> y. y \<noteq> x \<Longrightarrow> \<beta> y = \<alpha> y" 
  shows "poly (partial_insertion \<beta> x p) (\<alpha> x) = insertion \<alpha> p" 
proof (induct p rule: mpoly_induct)
  case (monom m a)
  let ?rkm = "remove_key x m" 
  have to_alpha: "insertion \<beta> (MPoly_Type.monom ?rkm a) = insertion \<alpha> (MPoly_Type.monom ?rkm a)" 
    by (rule insertion_irrelevant_vars, rule assms, insert vars_monom_subset[of ?rkm a], auto simp: remove_key_keys[symmetric])
  have main: "insertion \<alpha> (MPoly_Type.monom ?rkm a) * \<alpha> x ^ lookup m x = insertion \<alpha> (MPoly_Type.monom m a)" 
    unfolding monom_remove_key[of m a x] insertion_mult
    by (metis insertion_single mult.left_neutral)
  show ?case using main to_alpha by (simp add: partial_insertion_monom poly_monom)
next
  case (sum p1 p2 m a)
  then show ?case by (simp add: partial_insertion_add insertion_add map_poly_add) 
qed

lemma insertion_coeff_mpoly_to_mpoly_poly[simp]: 
  "insertion \<alpha> (coeff (mpoly_to_mpoly_poly x p) k) = coeff (partial_insertion \<alpha> x p) k"
  unfolding partial_insertion_def 
  by (subst coeff_map_poly, auto)

lemma degree_map_poly_Const: "degree (map_poly (Const :: 'a :: semiring_0 \<Rightarrow> _) f) = degree f" 
  by (rule degree_map_poly, auto)

lemma degree_partial_insertion_le_mpoly: "degree (partial_insertion \<alpha> x p) \<le> degree (mpoly_to_mpoly_poly x p)" 
  unfolding partial_insertion_def by (rule degree_map_poly_le)

end