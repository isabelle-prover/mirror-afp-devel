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

lemma irr_monic_root_free_poly_rat[simp]: "irreducible (poly_rat x)" 
  "monic (poly_rat x)" "root_free (poly_rat x)"
  "square_free (poly_rat x)"
  unfolding poly_rat_def by (auto simp: root_free_def intro!: irreducible_square_free linear_irreducible)

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
    (mode = Check_Root_Free \<longrightarrow> root_free q) \<and> (mode \<noteq> Check_Root_Free \<or> square_free p \<longrightarrow> square_free q) \<and> degree q \<le> degree p"
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
    from fact(2-3)[OF qi] have q: "(mode = Full_Factorization \<or> mode = Check_Irreducible \<longrightarrow> irreducible q) \<and> 
    (mode = Check_Root_Free \<longrightarrow> root_free q) \<and> (mode \<noteq> Check_Root_Free \<or> square_free p \<longrightarrow> square_free q)" "i \<noteq> 0" "monic q" by auto
    have "degree p = degree (\<Prod>(x, y)\<leftarrow>qis. x ^ y)" unfolding fact(1) degree_smult_eq using zero by simp
    also have "\<dots> = listsum (map degree (map (\<lambda> (x,y). x ^ y) qis))"
      by (rule degree_listprod_eq, insert zero[unfolded listprod_zero_iff], force)
    also have "\<dots> \<ge> degree (q ^ i)" unfolding qis by auto
    also have "degree (q ^ i) = degree q * i" 
      by (rule degree_power_eq, insert q, auto)
    finally have "degree q * i \<le> degree p" by auto
    with q(2) have "degree q \<le> degree p" by (cases i, auto)
    with q show "monic q \<and> (mode = Full_Factorization \<or> mode = Check_Irreducible \<longrightarrow> irreducible q) \<and> 
      (mode = Check_Root_Free \<longrightarrow> root_free q) \<and> 
      (mode \<noteq> Check_Root_Free \<or> square_free p \<longrightarrow> square_free q) \<and>
      degree q \<le> degree p" by auto
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
  have mg: "monic g" unfolding g_def using \<open>monic p\<close>
    using poly_gcd_monic[of p q] by (auto simp add: lead_coeff_def)
  hence [simp]: "g \<noteq> 0" by auto
  from dvd_imp_degree_le[OF dvd] irr have "degree g \<le> degree p" by force
  with dvd irr(2)[of g] have "degree g = 0 \<or> degree g = degree p" by linarith
  thus ?thesis
  proof
    assume "degree g = 0"
    with mg have "g = 1" using monic_degree_0 by blast
    thus ?thesis unfolding g_def by auto
  next
    assume deg: "degree g = degree p"
    def d \<equiv> "p div g"
    with dvd have p: "p = g * d" by simp
    with deg have "degree d = 0" by (cases "d = 0") (simp_all add: degree_mult_eq)
    then obtain d' where [simp]: "d = [:d':]" by (elim degree_eq_zeroE)
    with p mg assms(2) have "p = g" by (simp split: if_split_asm)
    thus ?thesis by (simp add: g_def)
  qed
qed

lemma irreducible_monic_gcd_twice: 
  assumes p: "irreducible p" "monic p" 
  and q: "irreducible q" "monic q"
  shows "gcd p q = 1 \<or> p = q"
proof (cases "gcd p q = 1")
  case False note pq = this
  have id: "gcd p q = gcd q p" by (simp add: gcd.commute)
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
      hence "[:-x,1:] dvd gcd (?rp p) (?rp q)" by (rule gcd_greatest)
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

definition poly_uminus :: "'a :: field_char_0 poly \<Rightarrow> 'a poly" where
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

lemma poly_inverse_rev_coeffs[code]: 
  "poly_inverse p = poly_of_list (rev (coeffs p))"
proof (cases "p = 0")
  case True
  thus ?thesis by (auto simp: poly_inverse_def)
next
  case False
  show ?thesis unfolding poly_of_list_def poly_eq_iff
  proof 
    fix n
    have "coeff (poly_inverse p) n = (if n \<le> degree p then coeff p (degree p - n) else 0)"
      unfolding poly_inverse_def coeff_setsum coeff_monom
      by (cases "n \<le> degree p", auto, subst setsum.remove[of _ n], auto)
    also have "\<dots> = coeff (Poly (rev (coeffs p))) n"
      unfolding poly_inverse_def coeff_setsum coeff_monom coeff_Poly
      by (cases "n < length (coeffs p)", 
        auto simp: nth_default_def length_coeffs_degree[OF False], subst rev_nth,
        auto simp: length_coeffs_degree[OF False] coeffs_nth[OF False])
    finally show "coeff (poly_inverse p) n = coeff (Poly (rev (coeffs p))) n" .
  qed
qed  

lemma degree_poly_inverse_le: "degree (poly_inverse p) \<le> degree p"
  unfolding poly_inverse_def 
  by (rule degree_setsum_le, force, rule order_trans[OF degree_monom_le], auto)

lemma inverse_pow_minus: assumes "x \<noteq> (0 :: 'a :: field)"
  and "i \<le> n"
  shows "inverse x ^ n * x ^ i = inverse x ^ (n - i)" 
  using assms by (simp add: field_class.field_divide_inverse power_diff power_inverse)

lemma poly_inverse: assumes x: "x \<noteq> 0"
  shows "poly (poly_inverse p) (inverse x) = (inverse x) ^ (degree p) * poly p x" (is "?l = ?r")
proof -
  from poly_as_sum_of_monoms[of p]
  have id: "poly p x = poly ((\<Sum>x\<le>degree p. monom (coeff p x) x)) x" by simp
  let ?f = "\<lambda> k. poly (monom (coeff p (degree p - k)) k) (inverse x)"
  have "?r = (\<Sum>n\<le>degree p. inverse x ^ degree p * poly (monom (coeff p n) n) x)" 
    unfolding id poly_setsum setsum_right_distrib by simp  
  have "?l = (\<Sum>k\<le>degree p. ?f k)"
    unfolding poly_inverse_def poly_setsum by simp 
  also have "\<dots> = (\<Sum>k \<le> degree p. ?f (degree p - k))"
    by (subst setsum.reindex_cong[of "\<lambda> i. degree p - i" "{..degree p}"], auto simp: inj_on_def)
     (metis (full_types) atMost_iff diff_diff_cancel diff_le_mono2 diff_zero image_iff le0)
  also have "\<dots> = (\<Sum>n\<le>degree p. inverse x ^ degree p * poly (monom (coeff p n) n) x)"
    by (rule setsum.cong, auto simp: poly_monom inverse_pow_minus[OF x])
  also have "\<dots> = ?r"
    unfolding id poly_setsum setsum_right_distrib by simp  
  finally show ?thesis .
qed

lemma poly_inverse_root: assumes p: "p \<noteq> 0" shows 
  "(poly (poly_inverse p) x = 0) = (x \<noteq> 0 \<and> poly p (inverse x) = 0)"
proof (cases "x = 0")
  case False
  hence ix: "inverse x \<noteq> 0" by auto
  show ?thesis using poly_inverse[OF ix] False by auto
next
  case True
  show ?thesis unfolding True poly_inverse_def poly_setsum
    by (subst setsum.remove[of _ 0], insert p, auto simp: poly_monom)
qed

lemma (in inj_field_hom) poly_inverse_hom: 
  "poly_inverse (map_poly hom p) = map_poly hom (poly_inverse p)"
proof -
  interpret poly: inj_ring_hom "map_poly hom" by (rule inj_ring_hom_map_poly)
  show ?thesis unfolding poly_inverse_def degree_map_poly by simp
qed


lemma rpoly_inverse: assumes x: "(x :: 'a :: field_char_0) \<noteq> 0" 
  shows "rpoly (poly_inverse p) (inverse x) = (inverse x) ^ (degree p) * rpoly p x" (is "?l = ?r")
proof -
  let ?or = "of_rat :: rat \<Rightarrow> 'a"
  have hom: "inj_field_hom ?or" ..
  show ?thesis
    using poly_inverse[OF x, of "map_poly ?or p"] unfolding eval_poly_def
    by (simp add: inj_field_hom.poly_inverse_hom[OF hom])
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

locale factor_preserving = fixes f :: "'a :: field poly \<Rightarrow> 'a poly"
  assumes deg: "degree (f q) = degree q"
  and comp: "f (q * r) = f q * f r"
begin

lemma square_free_preservation: assumes sf: "square_free (f p)"
  shows "square_free p"
proof (rule ccontr)
  assume "\<not> square_free p"
  then obtain q where p0: "p \<noteq> 0" and d: "degree q \<noteq> 0" and qp: "q * q dvd p" 
    unfolding square_free_def by auto
  then obtain r where p: "p = q * q * r" unfolding dvd_def by auto
  from arg_cong[OF p, of f, unfolded comp] deg[of q] d 
  have "\<exists> q. degree q \<noteq> 0 \<and> q * q dvd f p"
    unfolding dvd_def by (auto intro: exI[of _ "f q"])
  with sf[unfolded square_free_def] have "f p = 0" by auto
  with deg[of p] have dp: "degree p = 0" by auto
  from qp have "q dvd p" unfolding dvd_def by auto
  from divides_degree[OF this, unfolded dp] d p0 show False by auto
qed

lemma irreducible_preservation: assumes irr: "irreducible (f p)"
  shows "irreducible p"
proof (rule ccontr)
  assume p: "\<not> irreducible p"
  from irreducibleD[OF irr] have "degree (f p) \<noteq> 0" by auto
  with deg[of p] have dp: "degree p \<noteq> 0" by auto
  from p dp obtain q where d: "degree q \<noteq> 0" and qp: "q dvd p" and qp: "degree q < degree p"
    unfolding irreducible_def by auto   
  then obtain r where p: "p = q  * r" unfolding dvd_def by auto
  from arg_cong[OF p, of f, unfolded comp] have dvd: "f q dvd f p" by auto
  from d deg[of q] have "degree (f q) \<noteq> 0" by auto
  from irreducibleD(2)[OF irr this] dvd have "\<not> degree (f q) < degree (f p)" by auto
  with qp show False unfolding deg by auto
qed
end

lemma factor_preserving_poly_uminus: "factor_preserving poly_uminus"
  by (standard, force, auto simp: poly_uminus_def pcompose_mult)

lemma poly_uminus_inv[simp]: "poly_uminus (poly_uminus p) = p"
  unfolding poly_uminus_def
  by (rule poly_ext, simp add: poly_pcompose)

lemma poly_uminus_irreducible: assumes p: "irreducible p" 
  shows "irreducible (poly_uminus p)"
  by (rule factor_preserving.irreducible_preservation[OF factor_preserving_poly_uminus], simp add: p)

lemma poly_uminus_square_free: assumes p: "square_free p" 
  shows "square_free (poly_uminus p)"
  by (rule factor_preserving.square_free_preservation[OF factor_preserving_poly_uminus], simp add: p)

definition poly_add_rat :: "rat \<Rightarrow> rat poly \<Rightarrow> rat poly" where
  "poly_add_rat r p \<equiv> p \<circ>\<^sub>p [:-r,1:]"

lemma degree_poly_add_rat[simp]: "degree (poly_add_rat r p) = degree p"
  unfolding poly_add_rat_def degree_pcompose by auto

lemma rpoly_add_rat: "rpoly (poly_add_rat r p) x = rpoly p (x - of_rat r)"
  unfolding poly_add_rat_def rpoly_poly_compose
  by (simp add: eval_poly_def)

lemma poly_add_rat_0[simp]: "poly_add_rat r p = 0 \<longleftrightarrow> p = 0"
  unfolding poly_add_rat_def 
  by (rule pcompose_eq_0, auto)

lemma alg_poly_add_rat: assumes "alg_poly x p"
  shows "alg_poly (of_rat r + x) (poly_add_rat r p)"
  using assms unfolding alg_poly_def rpoly_add_rat by simp

lemma factor_preserving_poly_add_rat: "factor_preserving (poly_add_rat r)"
  by (standard, force, auto simp: poly_add_rat_def pcompose_mult)

lemma poly_add_rat_inv[simp]: "poly_add_rat (-r) (poly_add_rat r p) = p"
  unfolding poly_add_rat_def 
  by (rule poly_ext, simp add: poly_pcompose)

lemma poly_add_rat_irreducible: assumes p: "irreducible p" 
  shows "irreducible (poly_add_rat r p)"
  by (rule factor_preserving.irreducible_preservation[OF factor_preserving_poly_add_rat[of "-r"]],
  simp add: p)

lemma poly_add_rat_square_free: assumes p: "square_free p" 
  shows "square_free (poly_add_rat r p)"
  by (rule factor_preserving.square_free_preservation[OF factor_preserving_poly_add_rat[of "-r"]],
  simp add: p)

definition poly_mult_rat :: "rat \<Rightarrow> rat poly \<Rightarrow> rat poly" where
  "poly_mult_rat r p \<equiv> p \<circ>\<^sub>p [:0,inverse r:]"

lemma degree_poly_mult_rat_le: "degree (poly_mult_rat r p) \<le> degree p"
  unfolding poly_mult_rat_def degree_pcompose by auto

lemma degree_poly_mult_rat[simp]: "r \<noteq> 0 \<Longrightarrow> degree (poly_mult_rat r p) = degree p"
  unfolding poly_mult_rat_def degree_pcompose by auto

lemma rpoly_mult_rat: "rpoly (poly_mult_rat r p) x = rpoly p (x * inverse (of_rat r))"
  unfolding poly_mult_rat_def rpoly_poly_compose
  by (simp add: eval_poly_def)

lemma poly_mult_rat_0[simp]: "r \<noteq> 0 \<Longrightarrow> poly_mult_rat r p = 0 \<longleftrightarrow> p = 0"
  unfolding poly_mult_rat_def 
  by (rule pcompose_eq_0, auto)

lemma alg_poly_mult_rat: assumes r: "r \<noteq> 0"
  and "alg_poly x p"
  shows "alg_poly (of_rat r * x) (poly_mult_rat r p)"
  using assms
  unfolding alg_poly_def rpoly_mult_rat by (simp add: field_simps)

lemma poly_mult_rat_inv[simp]: "r \<noteq> 0 \<Longrightarrow> poly_mult_rat (inverse r) (poly_mult_rat r p) = p"
  unfolding poly_mult_rat_def 
  by (rule poly_ext, simp add: poly_pcompose field_simps)

lemma factor_preserving_poly_mult_rat: "r \<noteq> 0 \<Longrightarrow> factor_preserving (poly_mult_rat r)"
  by (standard, force, auto simp: poly_mult_rat_def pcompose_mult)

lemma poly_mult_rat_irreducible: assumes "r \<noteq> 0" "irreducible p" 
  shows "irreducible (poly_mult_rat r p)"
  by (rule factor_preserving.irreducible_preservation[OF factor_preserving_poly_mult_rat[of "inverse r"]],
    insert assms, auto)

lemma poly_mult_rat_square_free: assumes "r \<noteq> 0" "square_free p" 
  shows "square_free (poly_mult_rat r p)"
  by (rule factor_preserving.square_free_preservation[OF factor_preserving_poly_mult_rat[of "inverse r"]],
    insert assms, auto)

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

lemma poly_inverse_irreducible: assumes p: "irreducible p" "monic p" 
  and x: "alg_poly x p"
  and x0: "x \<noteq> 0"
  shows "irreducible (poly_inverse p)"
proof -
  from alg_poly_inverse[OF x0 x] have y: "alg_poly (inverse x) (poly_inverse p)" .
  from x0 have ix0: "inverse x \<noteq> 0" by auto
  show ?thesis
  proof (rule irreducible_preservation[OF p x y degree_poly_inverse_le])
    fix q
    assume "alg_poly (inverse x) q"
    from alg_poly_inverse[OF ix0 this] have "alg_poly x (poly_inverse q)" by simp
    with degree_poly_inverse_le
    show " alg_poly x (poly_inverse q) \<and> degree (poly_inverse q) \<le> degree q" by auto
  qed
qed

lemma coeff_poly_inverse_degree: "coeff (poly_inverse p) (degree p) = coeff p 0"
  unfolding poly_inverse_def coeff_setsum
  by (subst setsum.remove[of _ "degree p"], auto)

lemma degree_poly_inverse_no_0: assumes 0: "coeff p 0 \<noteq> 0" 
  shows "degree (poly_inverse p) = degree p"
proof -
  have "coeff (poly_inverse p) (degree p) \<noteq> 0"
    unfolding coeff_poly_inverse_degree using 0 by simp
  hence "degree p \<le> degree (poly_inverse p)" by (rule le_degree)
  moreover have "degree (poly_inverse p) \<le> degree p" by (rule degree_poly_inverse_le)
  ultimately show ?thesis by auto
qed

lemma degree_poly_inverse_rsquarefree_0: assumes 0: "coeff p 0 = 0" 
  and sf: "rsquarefree p"
  shows "Suc (degree (poly_inverse p)) = degree p"
proof -
  let ?ip = "poly_inverse p"
  let ?n = "degree p"
  from sf have p0: "p \<noteq> 0" unfolding rsquarefree_def by auto
  from p0 have ip0: "?ip \<noteq> 0" by simp
  from degree_poly_inverse_le[of p] have deg: "degree ?ip \<le> ?n" .
  have "coeff ?ip ?n = 0" unfolding coeff_poly_inverse_degree 0 by simp
  with ip0 have "degree ?ip \<noteq> ?n" by (metis leading_coeff_0_iff)
  with deg have deg: "degree ?ip < ?n" by auto
  then obtain n where dp: "degree p = Suc n" by (cases ?n, auto)
  have "degree ?ip = n"
  proof (rule ccontr)
    assume "degree ?ip \<noteq> n" 
    with dp deg have "degree ?ip < n" by auto
    hence "coeff ?ip n = 0" by (rule coeff_eq_0)
    also have "coeff ?ip n = coeff p 1" unfolding poly_inverse_def coeff_setsum dp
      by (subst setsum.remove[of _ "Suc n"], force+, subst setsum.remove[of _ n], auto)
    finally have 1: "coeff p 1 = 0" .
    from 0 have "poly p 0 = 0" unfolding poly_altdef by auto
    hence "[:0,1:] dvd p" by (simp add: dvd_iff_poly_eq_0)    
    then obtain k where p: "p = [:0,1:] * k" unfolding dvd_def by auto
    also have "\<dots> = monom 1 1 * k" by (simp add: x_as_monom)
    finally have "p = monom 1 1 * k" by simp
    from 1[unfolded this coeff_monom_mult]
    have "coeff k 0 = 0" by simp
    hence "poly k 0 = 0" unfolding poly_altdef by auto
    hence "[:0,1:] dvd k" by (simp add: dvd_iff_poly_eq_0)    
    then obtain l where k: "k = [:0,1:] * l" unfolding dvd_def by auto
    have p: "p = [:-0,1:]^2 * l" unfolding p k by (simp add: power2_eq_square)
    have "[:-0,1:]^2 dvd p" unfolding p by simp
    from this[unfolded order_divides] have "p = 0 \<or> \<not> order 0 p \<le> 1" by auto
    with sf[unfolded rsquarefree_def'] 
    show False by auto
  qed
  with dp show ?thesis by auto
qed

lemma degree_poly_inverse_rsquarefree: assumes "rsquarefree p"
  shows "degree p = (if poly p 0 = 0 then Suc (degree (poly_inverse p)) else degree (poly_inverse p))"
proof -
  have id: "poly p 0 = coeff p 0" unfolding poly_altdef by auto
  show ?thesis unfolding id 
    using degree_poly_inverse_rsquarefree_0[OF _ assms] degree_poly_inverse_no_0[of p]
    by auto
qed

lemma poly_inverse_square_free_complex: assumes sf: "square_free (p :: complex poly)" 
  shows "square_free (poly_inverse p)"
proof (cases "poly_inverse p = 0")
  case True
  thus ?thesis unfolding square_free_def by auto
next
  case False
  hence p: "p \<noteq> 0" by (cases p, auto simp: poly_inverse_def)
  let ?ip = "poly_inverse p"
  from square_free_rsquarefree[OF p sf] have sf: "rsquarefree p" .
  from sf[unfolded rsquarefree_card_degree[OF p]] have card: "card {x. poly p x = 0} = degree p" .
  also have "\<dots> = (if poly p 0 = 0 then Suc (degree ?ip) else degree ?ip)"
    by (rule degree_poly_inverse_rsquarefree[OF sf])
  also have "card {x. poly p x = 0} = (if poly p 0 = 0 then Suc (card ({x. poly p x = 0} - {0})) else
    (card ({x. poly p x = 0} - {0})))"
    by (cases "poly p 0 = 0", auto, subst card.remove[of _ 0], auto simp: poly_roots_finite[OF p])
  finally have deg: "degree ?ip = card ({x. poly p x = 0} - {0})" by (auto split: if_splits)
  have sf: "rsquarefree ?ip" unfolding rsquarefree_card_degree[OF False] deg
    unfolding poly_inverse_root[OF p]
  proof (rule bij_betw_same_card[of inverse], unfold bij_betw_def inj_on_def, 
    auto simp: image_def, goal_cases)
    case (1 x)
    thus ?case by (intro exI[of _ "inverse x"], auto)
  qed
  show ?thesis
    by (rule rsquarefree_square_free_complex[OF sf])
qed

lemma poly_inverse_square_free: assumes p: "square_free (p :: rat poly)" 
  shows "square_free (poly_inverse p)"
proof -
  let ?c = "of_rat :: rat \<Rightarrow> complex"
  interpret c: inj_field_hom_0 ?c ..
  have "inj_field_hom_0 ?c" ..
  note sf_c = inj_field_hom_0.square_free_map_poly[OF this]
  from poly_inverse_square_free_complex[OF assms[folded sf_c]]
  have "square_free (poly_inverse (map_poly ?c p))" .
  also have "poly_inverse (map_poly ?c p) = map_poly ?c (poly_inverse p)"
    by (rule inj_field_hom.poly_inverse_hom, standard)
  finally show ?thesis unfolding sf_c .
qed
end
