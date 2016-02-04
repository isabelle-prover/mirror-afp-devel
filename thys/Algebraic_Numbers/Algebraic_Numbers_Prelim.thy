(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Algebraic Numbers -- Excluding Addition and Multiplication\<close>

text \<open>This theory contains basic definition and results on algebraic numbers, namely that
  algebraic numbers are closed under negation, inversion, $n$-th roots, and
  that every rational number is algebraic. For all of these closure properties, corresponding
  polynomial witnesses are available. 

  Moreover, this theory contains the uniqueness result,
  that for every algebraic number there is exactly one monic irreducible polynomial for it.
  This result is stronger than similar ones which you find in many textbooks.
  The reason is that here we do not require a least degree construction.

  This is essential, since given some monic irreducible polynomial for x,
  how should we check whether the degree is optimal. In the formalized result, this is
  no longer required. The result is proven via GCDs, and that the GCD does not change
  when executed on the rational numbers or on the reals or complex numbers.\<close>
  
text \<open>The results are taken from the textbook \cite[pages 317ff]{AlgNumbers}.\<close>

theory Algebraic_Numbers_Prelim
imports
  "~~/src/HOL/Library/Fundamental_Theorem_Algebra"
  "../Polynomial_Factorization/Rational_Factorization"
begin

subsection \<open>Polynomial Evaluation of Rational Polynomials in Fields.\<close>

abbreviation rpoly :: "rat poly \<Rightarrow> 'a :: field_char_0 \<Rightarrow> 'a"
where
  "rpoly \<equiv> eval_poly of_rat"

interpretation rpoly: inj_field_hom_0 of_rat
  by (unfold_locales, auto simp: of_rat_add of_rat_mult of_rat_inverse of_rat_minus)

abbreviation real_of_rat_poly :: "rat poly \<Rightarrow> real poly" where
  "real_of_rat_poly \<equiv> map_poly real_of_rat"

lemma poly_real_of_rat_poly: "poly (real_of_rat_poly p) = rpoly p" 
  by (rule rpoly.poly_map_poly_eval_poly)

lemma real_of_rat_poly_0[simp]: "real_of_rat_poly p = 0 \<longleftrightarrow> p = 0"
  by (rule rpoly.map_poly_0_iff)

subsection \<open>Algebraic Numbers -- Definition, Inverse, and Roots\<close>

lemma algebraic_altdef_rpoly: 
  fixes x :: "'a :: field_char_0"
  shows "algebraic x \<longleftrightarrow> (\<exists>p. rpoly p x = 0 \<and> p \<noteq> 0)"
unfolding algebraic_altdef
proof (safe, goal_cases)
  case (1 p)
  def the_rat \<equiv> "\<lambda>x::'a. THE r. x = of_rat r"
  def p' \<equiv> "map_poly the_rat p"
  have of_rat_the_rat: "of_rat (the_rat x) = x" if "x \<in> \<rat>" for x
    unfolding the_rat_def by (rule sym, rule theI') (insert that, auto simp: Rats_def)
  have the_rat_0_iff: "the_rat x = 0 \<longleftrightarrow> x = 0" if "x \<in> \<rat>"
    using of_rat_the_rat[OF that] by auto
  
  have "map_poly of_rat p' = map_poly (of_rat \<circ> the_rat) p"
      by (simp add: p'_def map_poly_map_poly)
  also from 1 of_rat_the_rat have "\<dots> = p"
    by (subst poly_eq_iff) (auto simp: coeff_map_poly)
  finally have p_p': "map_poly of_rat p' = p" .

  show ?case
  proof (intro exI conjI notI)
    from 1 show "rpoly p' x = 0"
      by (simp add: rpoly.poly_map_poly_eval_poly [symmetric] p_p')
  next
    assume "p' = 0"
    hence "p = 0" by (simp add: p_p' [symmetric])
    with \<open>p \<noteq> 0\<close> show False by contradiction
  qed
next
  case (2 p)
  thus ?case
    by (intro exI[of _ "map_poly of_rat p"]) 
       (auto simp: rpoly.poly_map_poly_eval_poly)
qed  

definition alg_poly :: "'a :: field_char_0 \<Rightarrow> rat poly \<Rightarrow> bool" where
  "alg_poly x p = (rpoly p x = 0 \<and> p \<noteq> 0)"

lemma alg_polyI[intro]: "rpoly p x = 0 \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> alg_poly x p"
  unfolding alg_poly_def by auto

lemma alg_polyD[dest]: assumes "alg_poly x p"
  shows "p \<noteq> 0" "rpoly p x = 0" using assms unfolding alg_poly_def by auto

definition poly_rat :: "rat \<Rightarrow> rat poly" where
  "poly_rat x = [:-x,1:]"

lemma irr_monic_root_free_poly_rat[simp]: "irreducible (poly_rat x)" "monic (poly_rat x)" "root_free (poly_rat x)"
  unfolding poly_rat_def by (rule linear_irreducible, auto simp: root_free_def)

lemma rpoly_rat[simp]: "rpoly (poly_rat x) y = y - of_rat x" "poly_rat x \<noteq> 0"
  unfolding poly_rat_def eval_poly_def by (auto simp add: of_rat_minus)

lemma alg_poly_for_rat: "alg_poly x (poly_rat x)"
  by (intro alg_polyI, unfold rpoly_rat, auto)

lemma alg_poly_of_rat: "alg_poly (of_rat x) (poly_rat x)"
  by (intro alg_polyI, unfold rpoly_rat, auto)

lemma rpoly_smult_0_iff: assumes c: "c \<noteq> 0" 
  shows "(rpoly (smult c p) x = (0 :: real)) = (rpoly p x = 0)"
  unfolding rpoly.poly_map_poly_eval_poly[symmetric] rpoly.map_poly_smult
  using c by simp

definition factors_of_rat_poly :: "factorization_mode \<Rightarrow> rat poly \<Rightarrow> rat poly list" where
  "factors_of_rat_poly mode p = map fst (snd (factorize_rat_poly mode p))"

lemma factors_of_rat_poly:  
  defines "rp \<equiv> rpoly :: rat poly \<Rightarrow> 'a :: field_char_0 \<Rightarrow> 'a"
  assumes "factors_of_rat_poly mode p = qs"
  shows "\<And> q. q \<in> set qs \<Longrightarrow> monic q \<and> (mode = Full_Factorization \<or> mode = Check_Irreducible \<longrightarrow> irreducible q) \<and> 
    (mode = Check_Root_Free \<longrightarrow> root_free q) \<and> degree q \<le> degree p"
  "p \<noteq> 0 \<Longrightarrow> rp p x = 0 \<longleftrightarrow> (\<exists> q \<in> set qs. rp q x = 0)" 
proof -
  obtain c qis where factt: "factorize_rat_poly mode p = (c,qis)" by force
  from assms[unfolded factors_of_rat_poly_def factt] have qs: "qs = map fst qis" by auto
  note fact = factorize_rat_poly[OF factt]
  {
    fix q
    assume "q \<in> set qs"
    then obtain i where qi: "(q,i) \<in> set qis" unfolding qs by auto
    then obtain bef aft where qis: "qis = bef @ (q,i) # aft" unfolding in_set_conv_decomp by blast
    from factt qi have p: "p \<noteq> 0" by auto
    with fact(1) have zero: "c \<noteq> 0" "(\<Prod>(q, i)\<leftarrow>qis. q ^ i) \<noteq> 0" by auto
    from fact(2)[OF qi] have q: "(mode = Full_Factorization \<or> mode = Check_Irreducible \<longrightarrow> irreducible q) \<and> 
    (mode = Check_Root_Free \<longrightarrow> root_free q)" "i \<noteq> 0" "monic q" by auto
    have "degree p = degree (\<Prod>(x, y)\<leftarrow>qis. x ^ y)" unfolding fact(1) degree_smult_eq using zero by simp
    also have "\<dots> = listsum (map degree (map (\<lambda> (x,y). x ^ y) qis))"
      by (rule degree_listprod_eq, insert zero[unfolded listprod_zero_iff], force)
    also have "\<dots> \<ge> degree (q ^ i)" unfolding qis by auto
    also have "degree (q ^ i) = degree q * i" 
      by (rule degree_power_eq, insert q, auto)
    finally have "degree q * i \<le> degree p" by auto
    with q(2) have "degree q \<le> degree p" by (cases i, auto)
    with q show "monic q \<and> (mode = Full_Factorization \<or> mode = Check_Irreducible \<longrightarrow> irreducible q) \<and> 
      (mode = Check_Root_Free \<longrightarrow> root_free q) \<and> degree q \<le> degree p" by auto
  }
  assume p: "p \<noteq> 0"
  from fact(1) p have c: "c \<noteq> 0" by auto
  let ?r = "of_rat :: rat \<Rightarrow> 'a"
  let ?rp = "map_poly ?r"
  have rp: "\<And> x p. rp p x = 0 \<longleftrightarrow> poly (?rp p) x = 0"
    unfolding rp_def rpoly.poly_map_poly_eval_poly ..  
  interpret rp: semiring_hom ?rp by (rule rpoly.semiring_hom_map_poly)
  have "rp p x = 0 \<longleftrightarrow> rp (\<Prod>(x, y)\<leftarrow>qis. x ^ y) x = 0" unfolding fact(1) rp
    rpoly.map_poly_smult using c by auto
  also have "\<dots> = (\<exists> (q,i) \<in>set qis. poly (?rp (q ^ i)) x = 0)" 
    unfolding qs rp rp.hom_listprod poly_listprod_zero_iff set_map by fastforce
  also have "\<dots> = (\<exists> (q,i) \<in>set qis. poly (?rp q) x = 0)"
    unfolding rp.hom_power poly_power_zero_iff  using fact(2) by auto
  also have "\<dots> = (\<exists> q \<in> set qs. rp q x = 0)" unfolding rp qs by force
  finally show "rp p x = 0 \<longleftrightarrow> (\<exists> q \<in> set qs. rp q x = 0)" by auto
qed
  

lemma alg_poly_factors_rat_poly: assumes p: "alg_poly x p"
  shows "\<exists> q \<in> set (factors_of_rat_poly mode p). alg_poly x q \<and> monic q 
  \<and> (mode = Full_Factorization \<or> mode = Check_Irreducible \<longrightarrow> irreducible q) \<and> 
    (mode = Check_Root_Free \<longrightarrow> root_free q) \<and> degree q \<le> degree p"
proof -
  from alg_polyD[OF p] have p: "p \<noteq> 0" and rt: "rpoly p x = 0" by auto
  note fact = factors_of_rat_poly[of mode p, OF refl]
  from fact(2)[OF p, of x] rt obtain q where q: "q \<in> set (factors_of_rat_poly mode p)" and 
    rt: "rpoly q x = 0" by auto
  from fact(1)[OF q] rt show ?thesis
    by (intro bexI[OF _ q], auto)
qed

lemma irreducible_monic_gcd: assumes "irreducible p" and "monic p"
  shows "gcd p q \<in> {1,p}"
proof -
  def g \<equiv> "gcd p q"
  note irr = irreducibleD[OF assms(1)]
  have dvd: "g dvd p" unfolding g_def by auto
  have mg: "monic g" unfolding g_def using `monic p` 
    by (metis leading_coeff_0_iff poly_gcd_monic)
  from dvd_imp_degree_le[OF dvd] irr have "degree g \<le> degree p" by force
  with dvd irr(2)[of g] have "degree g = 0 \<or> degree g = degree p" by linarith
  thus ?thesis
  proof
    assume "degree g = 0"
    with mg have "g = 1" using monic_degree_0 by blast
    thus ?thesis unfolding g_def by auto
  next
    assume "degree g = degree p"
    with dvd mg `monic p` have "g = p" 
      by (metis degree_0 degree_mod_less g_def gcd_poly.simps 
      irr(1) poly_divides_conv0 poly_dvd_antisym poly_gcd_commute poly_gcd_dvd2 smult_dvd_iff)
    thus ?thesis unfolding g_def by auto
  qed
qed

lemma irreducible_monic_gcd_twice: 
  assumes p: "irreducible p" "monic p" 
  and q: "irreducible q" "monic q"
  shows "gcd p q = 1 \<or> p = q"
proof (cases "gcd p q = 1")
  case False note pq = this
  have id: "gcd p q = gcd q p" by (simp add: poly_gcd_commute)
  have "p = gcd p q" using irreducible_monic_gcd[OF p] pq by force
  also have "\<dots> = q" using irreducible_monic_gcd[OF q] pq unfolding id by force
  finally show ?thesis by auto
qed simp
  
lemma alg_poly_irreducible_unique: assumes "algebraic x"
  shows "\<exists>! p. alg_poly x p \<and> monic p \<and> irreducible p"
proof -
  let ?p = "\<lambda> p. alg_poly x p \<and> monic p \<and> irreducible p"
  note irrD = irreducibleD
  from assms obtain p where
    "alg_poly x p" unfolding algebraic_altdef_rpoly alg_poly_def by auto
  from alg_poly_factors_rat_poly[OF this] obtain p where
    p: "?p p" by auto
  show ?thesis
  proof (rule ex1I)
    show "?p p" by fact
    fix q
    assume q: "?p q"
    show "q = p" 
    proof (rule ccontr)
      let ?rp = "map_poly of_rat"
      assume "q \<noteq> p"
      with irreducible_monic_gcd_twice[of p q] p q have gcd: "gcd p q = 1" by auto
      from p q have rt: "rpoly p x = 0" "rpoly q x = 0" unfolding alg_poly_def by auto
      have rt: "poly (?rp p) x = 0" "poly (?rp q) x = 0"
        using rt unfolding rpoly.poly_map_poly_eval_poly[symmetric] by auto
      hence "[:-x,1:] dvd ?rp p" "[:-x,1:] dvd ?rp q" 
        unfolding poly_eq_0_iff_dvd by auto
      hence "[:-x,1:] dvd gcd (?rp p) (?rp q)" by blast
      also have "gcd (?rp p) (?rp q) = 1" 
        unfolding rpoly.map_poly_gcd[symmetric] gcd rpoly.map_poly_1 .. 
      finally show False by (simp add: dvd_iff_poly_eq_0)
    qed
  qed
qed

lemma poly_compose_eval_poly: "p \<circ>\<^sub>p q = eval_poly (\<lambda> a. [:a:]) p q"
  unfolding eval_poly_def by (induct p;simp)

lemma rpoly_poly_compose: "rpoly (p \<circ>\<^sub>p q) x = rpoly p (rpoly q x)"
proof (induct p)
  case (pCons a p)
  have "rpoly ((pCons a p) \<circ>\<^sub>p q) x = of_rat a + rpoly (q * p \<circ>\<^sub>p q) x" 
    by (simp add: eval_poly_def)
  also have "rpoly (q * p \<circ>\<^sub>p q) x = 
    rpoly q x * rpoly (p \<circ>\<^sub>p q) x"
    unfolding eval_poly_def rpoly.map_poly_mult poly_mult ..
  also have "rpoly (p \<circ>\<^sub>p q) x = rpoly p (rpoly q x)" unfolding pCons(2) ..
  also have "of_rat a + rpoly q x * \<dots> = rpoly (pCons a p) (rpoly q x)"
    unfolding eval_poly_def map_poly_pCons[OF pCons(1)] by simp
  finally show ?case .
qed simp

definition poly_uminus :: "'a :: field poly \<Rightarrow> 'a poly" where
  "poly_uminus p = p \<circ>\<^sub>p [:0,-1:]"

lemma degree_poly_uminus[simp]: "degree (poly_uminus p) = degree p"
  unfolding poly_uminus_def by simp

lemma rpoly_uminus[simp]: "rpoly (poly_uminus p) (-x) = rpoly p x"
  unfolding poly_uminus_def rpoly_poly_compose by (simp add: eval_poly_def)

lemma poly_uminus_0[simp]: "poly_uminus p = 0 \<longleftrightarrow> p = 0"
  unfolding poly_uminus_def 
  by (rule pcompose_eq_0, auto)

lemma alg_poly_uminus: assumes alg: "alg_poly x p"
  shows "alg_poly (-x) (poly_uminus p)"
proof -
  from alg_polyD[OF alg] have "p \<noteq> 0" and rp: "rpoly p x = 0" by auto
  hence 0: "poly_uminus p \<noteq> 0" by simp
  show ?thesis
    by (rule alg_polyI[OF _ 0], insert rp, auto)
qed


definition poly_inverse :: "'a :: field poly \<Rightarrow> 'a poly" where
  [code del]: "poly_inverse p = (\<Sum> i \<le> degree p. monom (coeff p (degree p - i)) i)"

lemma poly_inverse_code[code]: 
  "poly_inverse p = (listsum (map (\<lambda> i. monom (coeff p (degree p - i)) i) [0 ..< Suc (degree p)]))"
  (is "_ = ?r")
proof -
  have "poly_inverse p = setsum (\<lambda> i. monom (coeff p (degree p - i)) i) (set [0 ..< Suc (degree p)])"
    unfolding poly_inverse_def
    by (rule setsum.cong, auto)
  also have "\<dots> = ?r" unfolding setsum.set_conv_list
    by (subst distinct_remdups_id, auto)
  finally show ?thesis .
qed  

lemma degree_poly_inverse_le: "degree (poly_inverse p) \<le> degree p"
  unfolding poly_inverse_def 
  by (rule degree_setsum_le, force, rule order_trans[OF degree_monom_le], auto)

lemma inverse_pow_minus: assumes "x \<noteq> (0 :: 'a :: field)"
  and "i \<le> n"
  shows "inverse x ^ n * x ^ i = inverse x ^ (n - i)" 
  using assms by (simp add: field_class.field_divide_inverse power_diff power_inverse)

lemma rpoly_inverse: assumes x: "x \<noteq> 0" 
  shows "rpoly (poly_inverse p) (inverse x) = (inverse x) ^ (degree p) * rpoly p x"
  (is "?l = ?r")
proof -
  from poly_as_sum_of_monoms[of p]
  have id: "rpoly p x = rpoly ((\<Sum>x\<le>degree p. monom (coeff p x) x)) x" by simp
  let ?f = "\<lambda> k. rpoly (monom (coeff p (degree p - k)) k) (inverse x)"
  have "?r = (\<Sum>n\<le>degree p. inverse x ^ degree p * rpoly (monom (coeff p n) n) x)" 
    unfolding id rpoly.eval_poly_setsum setsum_right_distrib by simp  
  have "?l = (\<Sum>k\<le>degree p. ?f k)"
    unfolding poly_inverse_def rpoly.eval_poly_setsum by simp 
  also have "\<dots> = (\<Sum>k \<le> degree p. ?f (degree p - k))"
    by (subst setsum.reindex_cong[of "\<lambda> i. degree p - i" "{..degree p}"], auto simp: inj_on_def)
     (metis (full_types) atMost_iff diff_diff_cancel diff_le_mono2 diff_zero image_iff le0)
  also have "\<dots> = (\<Sum>n\<le>degree p. inverse x ^ degree p * rpoly (monom (coeff p n) n) x)"
    by (rule setsum.cong, auto simp: rpoly.eval_poly_monom inverse_pow_minus[OF x])
  also have "\<dots> = ?r"
    unfolding id rpoly.eval_poly_setsum setsum_right_distrib by simp  
  finally show ?thesis .
qed

lemma poly_inverse_0[simp]: "poly_inverse p = 0 \<longleftrightarrow> p = 0"
  unfolding poly_inverse_def 
  by (subst setsum_monom_0_iff, force+)

lemma alg_poly_inverse: assumes x: "x \<noteq> 0"
  and alg: "alg_poly x p"
  shows "alg_poly (inverse x) (poly_inverse p)"
proof -
  from alg_polyD[OF alg] have "p \<noteq> 0" and rp: "rpoly p x = 0" by auto
  hence 0: "poly_inverse p \<noteq> 0" by simp
  show ?thesis
    by (rule alg_polyI[OF _ 0], unfold rpoly_inverse[OF x] rp, simp)
qed

context
  fixes n :: nat
begin
definition poly_nth_root :: "'a :: field poly \<Rightarrow> 'a poly" where
  "poly_nth_root p = p \<circ>\<^sub>p monom 1 n"

lemma rpoly_nth_root:  "rpoly (poly_nth_root p) x = rpoly p (x ^ n)"
  unfolding poly_nth_root_def rpoly_poly_compose
  by (simp add: eval_poly_def map_poly_monom poly_monom)

context
  assumes n: "n \<noteq> 0"
begin
lemma poly_nth_root_0[simp]: "poly_nth_root p = 0 \<longleftrightarrow> p = 0"
  unfolding poly_nth_root_def
  by (rule pcompose_eq_0, insert n, auto simp: degree_monom_eq)

lemma alg_poly_nth_root: assumes y: "y^n = x" and
     alg: "alg_poly x p"
  shows "alg_poly y (poly_nth_root p)"
proof -
  from alg_polyD[OF alg] have "p \<noteq> 0" and rp: "rpoly p x = 0" by auto
  hence 0: "poly_nth_root p \<noteq> 0" by simp
  show ?thesis
    by (rule alg_polyI[OF _ 0], unfold rpoly_nth_root y rp, simp)
qed

lemma alg_poly_nth_root_odd_real: assumes alg: "alg_poly x p"
  and odd: "odd n"
  shows "alg_poly (root n x) (poly_nth_root p)"
  by (rule alg_poly_nth_root[OF odd_real_root_pow[OF odd] alg])

lemma alg_poly_nth_root_pos_real: assumes alg: "alg_poly x p"
  and pos: "x > 0"
  shows "alg_poly (root n x) (poly_nth_root p)"
proof -
  from n have id: "Suc (n - 1) = n" by auto
  show ?thesis
  proof (rule alg_poly_nth_root[OF _ alg])
    show "root n x ^ n = x" using id pos by auto  
  qed
qed

lemma alg_poly_nth_root_neg_real: assumes alg: "alg_poly x p"
  and neg: "x < 0"
  shows "alg_poly (root n x) (poly_uminus (poly_nth_root (poly_uminus p)))"
proof -
  have rt: "root n x = - root n (-x)" unfolding real_root_minus by simp
  show ?thesis unfolding rt 
    by (rule alg_poly_uminus[OF alg_poly_nth_root_pos_real[OF alg_poly_uminus[OF alg]]], insert neg, auto)
qed
end
end

lemma alg_poly_csqrt: assumes alg: "alg_poly x p"
  shows "alg_poly (csqrt x) (poly_nth_root 2 p)"
  by (rule alg_poly_nth_root[OF _ _ alg], auto)

lemma alg_poly_sqrt: assumes alg: "alg_poly x p"
  and pos: "x \<ge> 0"
  shows "alg_poly (sqrt x) (poly_nth_root 2 p)"
  by (rule alg_poly_nth_root[OF _ _ alg], insert pos, auto)

lemma alg_poly_degree: assumes "alg_poly x p"
  shows "degree p \<noteq> 0" 
proof 
  assume "degree p = 0"
  from degree0_coeffs[OF this] obtain c where p: "p = [:c:]" by auto
  from assms[unfolded alg_poly_def p]
  show False by (auto simp: eval_poly_def)
qed

lemma irreducible_preservation: assumes irr: "irreducible p" and mon: "monic p"
  and x: "alg_poly x p" 
  and y: "alg_poly y q"
  and deg: "degree p \<ge> degree q"
  and f: "\<And> q. alg_poly y q \<Longrightarrow> alg_poly x (f q) \<and> degree (f q) \<le> degree q"
  shows "irreducible q"
proof (rule ccontr)
  have dq: "degree q \<noteq> 0" using y by (rule alg_poly_degree)
  from x have ax: "algebraic x" unfolding algebraic_altdef_rpoly alg_poly_def by blast
  assume "\<not> ?thesis"
  from this[unfolded irreducible_def] dq obtain r where 
    r: "degree r \<noteq> 0" "degree r < degree q" and "r dvd q"
    by auto
  then obtain rr where q: "q = r * rr" unfolding dvd_def by auto
  have "degree q = degree r + degree rr" using dq unfolding q
    by (subst degree_mult_eq, auto)
  with r have rr: "degree rr \<noteq> 0" "degree rr < degree q" by auto
  from alg_polyD(2)[OF y, unfolded q eval_poly_def rpoly.map_poly_mult] 
  have "rpoly r y = 0 \<or> rpoly rr y = 0" unfolding eval_poly_def by auto
  with r rr have "alg_poly y r \<or> alg_poly y rr" unfolding alg_poly_def by auto
  with r rr obtain r where r: "alg_poly y r" "degree r < degree q" by blast
  from f[OF r(1)] deg r(2) obtain r where r: "alg_poly x r" "degree r < degree p" by auto
  from alg_poly_factors_rat_poly[OF r(1)] r(2) obtain r where 
    r: "alg_poly x r" "irreducible r" "monic r" and deg: "degree r < degree p" by force
  from alg_poly_irreducible_unique[OF ax] r irr mon x have "r = p" by auto
  with deg show False by auto
qed

end