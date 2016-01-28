(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Complex Roots of Real Valued Polynomials\<close>

text \<open>We provide conversion functions between polynomials over the real and the complex numbers,
  and prove that the complex roots of real-valued polynomial always come in conjugate pairs.
  We further show that also the order of the complex conjugate roots is identical.

  As a consequence, we derive that every real-valued polynomial can be factored into real factors of 
  degree at most 2, and we prove that every polynomial over the reals with odd degree has a real
  root.\<close>

theory Complex_Roots_Real_Poly
imports 
  "~~/src/HOL/Library/Fundamental_Theorem_Algebra"
  "../Polynomial_Factorization/Order_Polynomial"
  "../Polynomial_Factorization/Explicit_Roots"
  "../Polynomial_Interpolation/Ring_Hom_Poly"
begin

lemma real_poly_real_coeff: assumes "set (coeffs p) \<subseteq> \<real>"
  shows "coeff p x \<in> \<real>"
proof -
  have "coeff p x \<in> range (coeff p)" by auto
  from this[unfolded range_coeff] assms show ?thesis by auto
qed


lemma complex_conjugate_root: 
  assumes real: "set (coeffs p) \<subseteq> \<real>" and rt: "poly p c = 0"
  shows "poly p (cnj c) = 0"
proof -
  let ?c = "cnj c"
  {
    fix x
    have "coeff p x \<in> \<real>" 
      by (rule real_poly_real_coeff[OF real]) 
    hence "cnj (coeff p x) = coeff p x" by (cases "coeff p x", auto)
  } note cnj_coeff = this
  have "poly p ?c = poly (\<Sum>x\<le>degree p. monom (coeff p x) x) ?c"
    unfolding poly_as_sum_of_monoms ..
  also have "\<dots> = (\<Sum>x\<le>degree p . coeff p x * cnj (c ^ x))"
    unfolding poly_setsum poly_monom complex_cnj_power ..
  also have "\<dots> = (\<Sum>x\<le>degree p . cnj (coeff p x * c ^ x))"
    unfolding complex_cnj_mult cnj_coeff ..
  also have "\<dots> = cnj (\<Sum>x\<le>degree p . coeff p x * c ^ x)"
    unfolding cnj_setsum ..
  also have "(\<Sum>x\<le>degree p . coeff p x * c ^ x) = 
    poly (\<Sum>x\<le>degree p. monom (coeff p x) x) c"
    unfolding poly_setsum poly_monom ..
  also have "\<dots> = 0" unfolding poly_as_sum_of_monoms rt ..
  also have "cnj 0 = 0" by simp
  finally show ?thesis .
qed

context
  fixes p :: "complex poly"
  assumes coeffs: "set (coeffs p) \<subseteq> \<real>"
begin
lemma map_poly_Re_poly: fixes x :: real 
  shows "poly (map_poly Re p) x = poly p (of_real x)"
proof -
  interpret cr: ring_hom complex_of_real by (unfold_locales, auto)
  have id: "map_poly (of_real o Re) p = p"
    by (rule map_poly_eqI, insert coeffs, auto)
  show ?thesis unfolding arg_cong[OF id, of poly, symmetric]
    by (subst map_poly_compose[symmetric], force+)
qed

lemma map_poly_Re_coeffs:  
  "coeffs (map_poly Re p) = map Re (coeffs p)"
proof (rule coeffs_map_poly)
  fix x
  assume "x \<in> range (coeff p)"
  hence x: "x \<in> \<real>" using coeffs by (auto simp: range_coeff)
  show "(Re x = 0) = (x = 0)"
    using of_real_Re[OF x] by auto
qed

lemma map_poly_Re_0: "map_poly Re p = 0 \<Longrightarrow> p = 0"
  using map_poly_Re_coeffs by auto

end


lemma real_poly_add: 
  assumes "set (coeffs p) \<subseteq> \<real>" "set (coeffs q) \<subseteq> \<real>"
  shows "set (coeffs (p + q)) \<subseteq> \<real>" 
proof -
  def pp \<equiv> "coeffs p" def qq \<equiv> "coeffs q"
  show ?thesis using assms
  unfolding coeffs_plus_eq_plus_coeffs pp_def[symmetric] qq_def[symmetric]
    by (induct pp qq rule: plus_coeffs.induct, auto simp: cCons_def)
qed

lemma real_poly_setsum: 
  assumes "\<And> x. x \<in> S \<Longrightarrow> set (coeffs (f x)) \<subseteq> \<real>"
  shows "set (coeffs (setsum f S)) \<subseteq> \<real>" 
  using assms
proof (induct S rule: infinite_finite_induct)
  case (insert x S) 
  hence id: "setsum f (insert x S) = f x + setsum f S" by auto
  show ?case unfolding id
    by (rule real_poly_add[OF _ insert(3)], insert insert, auto)
qed auto

lemma real_poly_smult: fixes p :: "'a :: {idom,real_algebra_1} poly"
  assumes "c \<in> \<real>" "set (coeffs p) \<subseteq> \<real>"
  shows "set (coeffs (smult c p)) \<subseteq> \<real>" 
  using assms by (auto simp: coeffs_smult)

lemma real_poly_pCons: 
  assumes "c \<in> \<real>" "set (coeffs p) \<subseteq> \<real>"
  shows "set (coeffs (pCons c p)) \<subseteq> \<real>" 
  using assms by (auto simp: cCons_def)


lemma real_poly_mult: fixes p :: "'a :: {idom,real_algebra_1} poly"
  assumes p: "set (coeffs p) \<subseteq> \<real>" and q: "set (coeffs q) \<subseteq> \<real>"
  shows "set (coeffs (p * q)) \<subseteq> \<real>" using p
proof (induct p)
  case (pCons a p)
  show ?case unfolding mult_pCons_left
    by (intro real_poly_add real_poly_smult real_poly_pCons pCons(2) q,
    insert pCons(1,3), auto simp: cCons_def if_splits)
qed simp

lemma real_poly_power: fixes p :: "'a :: {idom,real_algebra_1} poly"
  assumes p: "set (coeffs p) \<subseteq> \<real>"
  shows "set (coeffs (p ^ n)) \<subseteq> \<real>"
proof (induct n)
  case (Suc n)
  from real_poly_mult[OF p this]
  show ?case by simp
qed simp


lemma real_poly_setprod: fixes f :: "'a \<Rightarrow> 'b :: {idom,real_algebra_1} poly"
  assumes "\<And> x. x \<in> S \<Longrightarrow> set (coeffs (f x)) \<subseteq> \<real>"
  shows "set (coeffs (setprod f S)) \<subseteq> \<real>" 
  using assms
proof (induct S rule: infinite_finite_induct)
  case (insert x S) 
  hence id: "setprod f (insert x S) = f x * setprod f S" by auto
  show ?case unfolding id
    by (rule real_poly_mult[OF _ insert(3)], insert insert, auto)
qed auto

lemma real_poly_uminus: 
  assumes "set (coeffs p) \<subseteq> \<real>" 
  shows "set (coeffs (-p)) \<subseteq> \<real>" 
  using assms unfolding coeffs_uminus by auto

lemma real_poly_minus: 
  assumes "set (coeffs p) \<subseteq> \<real>" "set (coeffs q) \<subseteq> \<real>"
  shows "set (coeffs (p - q)) \<subseteq> \<real>" 
  using assms unfolding diff_conv_add_uminus
  by (intro real_poly_uminus real_poly_add, auto)

lemma real_poly_pdivmod: fixes p :: "'a :: real_field poly" 
  assumes p: "set (coeffs p) \<subseteq> \<real>" 
  and *: "set (coeffs q) \<subseteq> \<real>"
    "pdivmod q p = (r,s)"
  shows "set (coeffs r) \<subseteq> \<real> \<and> set (coeffs s) \<subseteq> \<real>"
  using *
proof (induct q arbitrary: r s)
  case 0
  thus ?case unfolding pdivmod_0 by auto
next
  case (pCons a q r s)
  from pCons(1,3) have a: "a \<in> \<real>" and q: "set (coeffs q) \<subseteq> \<real>" by auto
  note res = pCons(4)[unfolded pdivmod_pCons]
  show ?case
  proof (cases "p = 0")
    case True
    with res pCons(3) show ?thesis by auto
  next
    case False
    obtain ss rr where r: "pdivmod q p = (ss, rr)" by force
    from pCons(2)[OF q r] have IH: "set (coeffs ss) \<subseteq> \<real>" "set (coeffs rr) \<subseteq> \<real>" by auto
    def c \<equiv> "coeff (pCons a rr) (degree p) / coeff p (degree p)"
    {
      have "coeff (pCons a rr) (degree p) \<in> \<real>"
        by (rule real_poly_real_coeff, insert IH(2) a, intro real_poly_pCons)
      moreover have "coeff p (degree p) \<in> \<real>" 
        by (rule real_poly_real_coeff[OF p])
      ultimately have "c \<in> \<real>" unfolding c_def by simp
    } note c = this
    from res[unfolded Let_def r split] False
    have r: "r = pCons c ss" and s: "s = pCons a rr - smult c p" 
      unfolding c_def by auto
    have "set (coeffs r) \<subseteq> \<real>" using c IH unfolding r by (intro real_poly_pCons)
    moreover have "set (coeffs s) \<subseteq> \<real>" using c IH unfolding s using c a p
      by (intro real_poly_minus real_poly_smult real_poly_pCons, auto)
    ultimately show ?thesis by auto
  qed
qed

lemma real_poly_div: fixes p :: "'a :: real_field poly" 
  assumes p: "set (coeffs p) \<subseteq> \<real>" 
  and q: "set (coeffs q) \<subseteq> \<real>"    
  shows "set (coeffs (p div q)) \<subseteq> \<real>"
proof -
  obtain r s where pq: "pdivmod p q = (r,s)" by force
  from real_poly_pdivmod[OF q p this]
  show ?thesis using pq[unfolded pdivmod_def] by auto
qed

lemma real_poly_factor: fixes p :: "'a :: real_field poly"
  assumes "set (coeffs (p * q)) \<subseteq> \<real>"
   "set (coeffs p) \<subseteq> \<real>"
  "p \<noteq> 0"
  shows "set (coeffs q) \<subseteq> \<real>" 
proof -
  have "q = p * q div p" using `p \<noteq> 0` by simp
  hence id: "coeffs q = coeffs (p * q div p)" by simp
  show ?thesis unfolding id
    by (rule real_poly_div, insert assms, auto)
qed

lemma complex_conjugate_order: assumes real: "set (coeffs p) \<subseteq> \<real>"
  "p \<noteq> 0"
  shows "order (cnj c) p = order c p"
proof -
  def n \<equiv> "degree p"
  have "degree p \<le> n" unfolding n_def by auto
  thus ?thesis using assms
  proof (induct n arbitrary: p)
    case (0 p)
    {
      fix x
      have "order x p \<le> degree p"
        by (rule order_degree[OF 0(3)])
      hence "order x p = 0" using 0 by auto
    }
    thus ?case by simp
  next
    case (Suc m p)
    note order = order[OF `p \<noteq> 0`]
    let ?c = "cnj c"
    show ?case
    proof (cases "poly p c = 0")
      case True note rt1 = this
      from complex_conjugate_root[OF Suc(3) True]
      have rt2: "poly p ?c = 0" .
      show ?thesis
      proof (cases "c \<in> \<real>")
        case True
        hence "?c = c" by (cases c, auto)
        thus ?thesis by auto
      next
        case False
        hence neq: "?c \<noteq> c" by (cases c, auto)
        let ?fac1 = "[: -c, 1 :]"
        let ?fac2 = "[: -?c, 1 :]"
        let ?fac = "?fac1 * ?fac2"
        from rt1 have "?fac1 dvd p" unfolding poly_eq_0_iff_dvd .
        from this[unfolded dvd_def] obtain q where p: "p = ?fac1 * q" by auto
        from rt2[unfolded p poly_mult] neq have "poly q ?c = 0" by auto
        hence "?fac2 dvd q" unfolding poly_eq_0_iff_dvd .
        from this[unfolded dvd_def] obtain r where q: "q = ?fac2 * r" by auto
        have p: "p = ?fac * r" unfolding p q by algebra
        from `p \<noteq> 0` have nz: "?fac1 \<noteq> 0" "?fac2 \<noteq> 0" "?fac \<noteq> 0" "r \<noteq> 0" unfolding p by auto
        have id: "?fac = [: ?c * c, - (?c + c), 1 :]" by simp
        have cfac: "coeffs ?fac = [ ?c * c, - (?c + c), 1 ]" unfolding id by simp
        have cfac: "set (coeffs ?fac) \<subseteq> \<real>" unfolding cfac by (cases c, auto simp: field_simps)
        have "degree p = degree ?fac + degree r" unfolding p
          by (rule degree_mult_eq, insert nz, auto)
        also have "degree ?fac = degree ?fac1 + degree ?fac2"
          by (rule degree_mult_eq, insert nz, auto)
        finally have "degree p = 2 + degree r" by simp
        with Suc have deg: "degree r \<le> m" by auto
        from real_poly_factor[OF Suc(3)[unfolded p] cfac] nz  have "set (coeffs r) \<subseteq> \<real>" by auto
        from Suc(1)[OF deg this `r \<noteq> 0`] have IH: "order ?c r = order c r" .
        {
          fix cc
          have "order cc p = order cc ?fac + order cc r" using `p \<noteq> 0` unfolding p
            by (rule order_mult)
          also have "order cc ?fac = order cc ?fac1 + order cc ?fac2"
            by (rule order_mult, rule nz)
          also have "order cc ?fac1 = (if cc = c then 1 else 0)" 
            unfolding order_linear' by simp
          also have "order cc ?fac2 = (if cc = ?c then 1 else 0)"
            unfolding order_linear' by simp
          finally have "order cc p = 
            (if cc = c then 1 else 0) + (if cc = cnj c then 1 else 0) + order cc r" .
        } note order = this
        show ?thesis unfolding order IH by auto
      qed
    next
      case False note rt1 = this
      {
        assume "poly p ?c = 0"
        from complex_conjugate_root[OF Suc(3) this] rt1
        have False by auto
      }
      hence rt2: "poly p ?c \<noteq> 0" by auto
      from rt1 rt2 show ?thesis 
        unfolding order_root by simp
    qed
  qed
qed

lemma map_poly_of_real_Re: assumes "set (coeffs p) \<subseteq> \<real>"
  shows "map_poly of_real (map_poly Re p) = p"
  by (subst map_poly_compose, force+, rule map_poly_eqI, insert assms, auto)

lemma map_poly_Re_of_real: "map_poly Re (map_poly of_real p) = p"
  by (subst map_poly_compose, force+, rule map_poly_eqI, auto)

lemma map_poly_Re_mult: assumes p: "set (coeffs p) \<subseteq> \<real>"
  and q: "set (coeffs q) \<subseteq> \<real>" shows "map_poly Re (p * q) = map_poly Re p * map_poly Re q"
proof -
  let ?r = "map_poly Re"
  let ?c = "map_poly complex_of_real"
  interpret c: inj_field_hom_0 complex_of_real by (unfold_locales, auto)
  have "?r (p * q) = ?r (?c (?r p) * ?c (?r q))" 
    unfolding map_poly_of_real_Re[OF p] map_poly_of_real_Re[OF q] by simp
  also have "?c (?r p) * ?c (?r q) = ?c (?r p * ?r q)"
    unfolding c.map_poly_mult ..
  also have "?r \<dots> = ?r p * ?r q" unfolding map_poly_Re_of_real ..
  finally show ?thesis .
qed
  
lemma map_poly_Re_power: assumes p: "set (coeffs p) \<subseteq> \<real>"
 shows "map_poly Re (p^n) = (map_poly Re p)^n" 
proof (induct n)
  case (Suc n)
  let ?r = "map_poly Re"
  have "?r (p^Suc n) = ?r (p * p^n)" by simp
  also have "\<dots> = ?r p * ?r (p^n)"
    by (rule map_poly_Re_mult[OF p real_poly_power[OF p]])
  also have "?r (p^n) = (?r p)^n" by (rule Suc)
  finally show ?case by simp
qed (simp add: one_poly_def)

lemma real_degree_2_factorization_exists_complex: fixes p :: "complex poly"
  assumes pR: "set (coeffs p) \<subseteq> \<real>"
  shows "\<exists> qs. p = listprod qs \<and> (\<forall> q \<in> set qs. set (coeffs q) \<subseteq> \<real> \<and> degree q \<le> 2)"
proof -
  obtain n where "degree p = n" by auto
  thus ?thesis using pR
  proof (induct n arbitrary: p rule: less_induct)
    case (less n p)
    hence pR: "set (coeffs p) \<subseteq> \<real>" by auto
    show ?case
    proof (cases "n \<le> 2")
      case True
      thus ?thesis using pR
        by (intro exI[of _ "[p]"], insert less(2), auto)
    next
      case False
      hence degp: "degree p \<ge> 2" using less(2) by auto
      hence "\<not> constant (poly p)" by (simp add: constant_degree)
      from fundamental_theorem_of_algebra[OF this] obtain x where x: "poly p x = 0" by auto
      from x have dvd: "[: -x, 1 :] dvd p" using poly_eq_0_iff_dvd by blast
      have "\<exists> f. f dvd p \<and> set (coeffs f) \<subseteq> \<real> \<and> 1 \<le> degree f \<and> degree f \<le> 2"
      proof (cases "x \<in> \<real>")
        case True
        with dvd show ?thesis 
          by (intro exI[of _ "[: -x, 1:]"], auto)
      next
        case False
        let ?x = "cnj x"
        let ?a = "?x * x"
        let ?b = "- ?x - x"
        from complex_conjugate_root[OF pR x]
        have xx: "poly p ?x = 0" by auto
        from False have diff: "x \<noteq> ?x" by (simp add: Reals_cnj_iff)
        from dvd obtain r where p: "p = [: -x, 1 :] * r" unfolding dvd_def by auto
        from xx[unfolded this] diff have "poly r ?x = 0" by simp
        hence "[: -?x, 1 :] dvd r" using poly_eq_0_iff_dvd by blast
        then obtain s where r: "r = [: -?x, 1 :] * s" unfolding dvd_def by auto
        have "p = ([: -x, 1:] * [: -?x, 1 :]) * s" unfolding p r by algebra
        also have "[: -x, 1:] * [: -?x, 1 :] = [: ?a, ?b, 1 :]" by simp
        finally have "[: ?a, ?b, 1 :] dvd p" unfolding dvd_def by auto
        moreover have "?a \<in> \<real>" by (simp add: Reals_cnj_iff)
        moreover have "?b \<in> \<real>" by (simp add: Reals_cnj_iff)
        ultimately show ?thesis by (intro exI[of _ "[:?a,?b,1:]"], auto)
      qed
      then obtain f where dvd: "f dvd p" and fR: "set (coeffs f) \<subseteq> \<real>" and degf: "1 \<le> degree f" "degree f \<le> 2" by auto
      from dvd obtain r where p: "p = f * r" unfolding dvd_def by auto
      from degp have p0: "p \<noteq> 0" by auto
      with p have f0: "f \<noteq> 0" and r0: "r \<noteq> 0" by auto
      from real_poly_factor[OF pR[unfolded p] fR f0] have rR: "set (coeffs r) \<subseteq> \<real>" .
      have deg: "degree p = degree f + degree r" unfolding p
        by (rule degree_mult_eq[OF f0 r0])
      with degf less(2) have degr: "degree r < n" by auto        
      from less(1)[OF this refl rR] obtain qs 
        where IH: "r = listprod qs" "(\<forall>q\<in>set qs. set (coeffs q) \<subseteq> \<real> \<and> degree q \<le> 2)" by auto
      from IH(1) have p: "p = listprod (f # qs)" unfolding p by auto
      with IH(2) fR degf show ?thesis
        by (intro exI[of _ "f # qs"], auto)
    qed
  qed
qed

lemma real_degree_2_factorization_exists: fixes p :: "real poly"
  shows "\<exists> qs. p = listprod qs \<and> (\<forall> q \<in> set qs. degree q \<le> 2)"
proof -
  interpret cr: inj_field_hom complex_of_real by (unfold_locales, auto)
  let ?cp = "map_poly complex_of_real"
  let ?rp = "map_poly Re"
  let ?p = "?cp p"
  have "set (coeffs ?p) \<subseteq> \<real>" unfolding cr.coeffs_map_poly by auto
  from real_degree_2_factorization_exists_complex[OF this]
  obtain qs where p: "?p = listprod qs" and 
    qs: "\<And> q. q \<in> set qs \<Longrightarrow> set (coeffs q) \<subseteq> \<real> \<and> degree q \<le> 2" by auto
  have p: "p = ?rp (listprod qs)" unfolding arg_cong[OF p, of ?rp, symmetric]
    by (subst map_poly_compose, force+, rule sym, rule map_poly_eqI, auto)
  from qs have "\<exists> rs. listprod qs = ?cp (listprod rs) \<and> (\<forall> r \<in> set rs. degree r \<le> 2)"
  proof (induct qs)
    case Nil
    show ?case by (auto intro!: exI[of _ Nil] simp: one_poly_def)
  next
    case (Cons q qs)
    then obtain rs where qs: "listprod qs = ?cp (listprod rs)"
      and rs: "\<And> q. q\<in>set rs \<Longrightarrow> degree q \<le> 2" by force+
    from Cons(2)[of q] have q: "set (coeffs q) \<subseteq> \<real>" and dq: "degree q \<le> 2" by auto
    def r \<equiv> "?rp q"
    have q: "q = ?cp r" unfolding r_def
      by (subst map_poly_compose, force+, rule sym, rule map_poly_eqI, insert q, auto)
    have dr: "degree r \<le> 2" using dq unfolding q by (simp add: degree_map_poly)
    show ?case
      by (rule exI[of _ "r # rs"], unfold listprod.Cons cr.map_poly_mult qs q, insert dr rs, auto)
  qed
  then obtain rs where id: "listprod qs = ?cp (listprod rs)" and deg: "\<forall> r \<in> set rs. degree r \<le> 2" by auto
  show ?thesis unfolding p id
    by (intro exI, rule conjI[OF _ deg], subst map_poly_compose, force+, rule map_poly_eqI, auto)
qed
    
  
lemma odd_degree_imp_real_root: assumes "odd (degree p)"
  shows "\<exists> x. poly p x = (0 :: real)"
proof -
  from real_degree_2_factorization_exists[of p] obtain qs where
    id: "p = listprod qs" and qs: "\<And> q. q \<in> set qs \<Longrightarrow> degree q \<le> 2" by auto
  show ?thesis using assms qs unfolding id
  proof (induct qs)
    case (Cons q qs)
    from Cons(3)[of q] have dq: "degree q \<le> 2" by auto    
    show ?case
    proof (cases "degree q = 1")
      case True
      from roots1[OF this] show ?thesis by auto
    next
      case False
      with dq have deg: "degree q = 0 \<or> degree q = 2" by arith
      from Cons(2) have "q * listprod qs \<noteq> 0" by auto
      hence "q \<noteq> 0" "listprod qs \<noteq> 0" by auto
      from degree_mult_eq[OF this]
      have "degree (listprod (q # qs)) = degree q + degree (listprod qs)" by simp
      from Cons(2)[unfolded this] deg have "odd (degree (listprod qs))" by auto
      from Cons(1)[OF this Cons(3)] obtain x where "poly (listprod qs) x = 0" by auto
      thus ?thesis by auto
    qed
  qed simp
qed

end
