subsection \<open>Part 2 -- Extensions With Importing Univariate Polynomials\<close>

theory Preliminaries_on_Polynomials_2
  imports 
    Preliminaries_on_Polynomials_1
    Factor_Algebraic_Polynomial.Poly_Connection
begin

text \<open>Several definitions have the same name for univariate and multivariate polynomials,
  so we use a prefix m for multi-variate.\<close>

hide_const (open) Symmetric_Polynomials.lead_coeff

abbreviation mdegree where "mdegree \<equiv> MPoly_Type.degree"   
abbreviation mcoeff where "mcoeff \<equiv> MPoly_Type.coeff"
abbreviation mmonom where "mmonom \<equiv> MPoly_Type.monom"

lemma range_coeff_poly_to_mpoly: assumes "mcoeff (poly_to_mpoly x p) m \<noteq> 0" 
  shows "\<exists> d. m = monomial d x"                        
  using assms 
  unfolding coeff_def poly_to_mpoly_def MPoly_inverse[OF Set.UNIV_I] lookup_Abs_poly_mapping[OF poly_to_mpoly_finite]
  by simp (metis keys_subset_singleton_imp_monomial)

lemma degree_poly_to_mpoly[simp]: "mdegree (poly_to_mpoly x p) x = degree p" 
proof (cases "p = 0")
  case True
  thus ?thesis by (simp add: poly_to_mpoly0)
next
  case p: False
  let ?q = "poly_to_mpoly x p" 
  define q where "q = ?q" 
  define dp where "dp = degree p" 
  define dq where "dq = mdegree q x" 
  from p have q: "?q \<noteq> 0"
    by (metis poly_to_mpoly0 poly_to_mpoly_inverse)
  have pq: "p = mpoly_to_poly x q" unfolding q_def
    by (simp add: poly_to_mpoly_inverse)
  {
    have "0 \<noteq> coeff p dp" using p by (auto simp: dp_def)
    also have "coeff p dp = coeff (mpoly_to_poly x q) dp" unfolding pq by simp
    also have "\<dots> = mcoeff q (monomial dp x)" unfolding coeff_mpoly_to_poly by simp
    finally have "mcoeff q (monomial dp x) \<noteq> 0" by simp
  }
  hence first_part: "dq \<ge> dp" unfolding dq_def by (metis degree_geI lookup_single_eq)
  {
    from monom_of_degree_exists[OF q, folded q_def, of x] obtain m where mc: "mcoeff q m \<noteq> 0" 
      and look: "lookup m x = dq" by (auto simp: dq_def)
    from range_coeff_poly_to_mpoly[OF mc[unfolded q_def]] obtain d where m: "m = monomial d x" by auto
    from m look have m: "m = monomial dq x" by simp
    have "coeff p dq = mcoeff q (monomial dq x)" 
      unfolding coeff_poly_to_mpoly[of x, symmetric] q_def dq_def by auto
    also have "\<dots> \<noteq> 0" using m mc by auto
    finally have "dp \<ge> dq" unfolding dp_def by (rule le_degree)
  }
  with first_part have "dp = dq" by auto
  thus ?thesis unfolding dp_def dq_def q_def by auto
qed

lemma degree_mpoly_to_poly: assumes "vars p \<subseteq> {x}" 
  shows "degree (mpoly_to_poly x p) = mdegree p x" 
proof -
  define q where "q = mpoly_to_poly x p" 
  from mpoly_to_poly_inverse[OF assms]
  have "mdegree p x = mdegree (poly_to_mpoly x (mpoly_to_poly x p)) x" by simp
  also have "\<dots> = degree (mpoly_to_poly x p)" by simp
  finally show ?thesis ..
qed

lemma degree_partial_insertion_bound: "degree (partial_insertion a x p) \<le> MPoly_Type.degree p x" 
  using degree_partial_insertion_le_mpoly by auto

lemma insertion_partial_insertion_vars: assumes "\<And> y. y \<noteq> x \<Longrightarrow> y \<in> vars p \<Longrightarrow> \<beta> y = \<alpha> y" 
  shows "poly (partial_insertion \<beta> x p) (\<alpha> x) = insertion \<alpha> p" 
proof -
  let ?\<alpha> = "(\<lambda> y. if y \<in> insert x (vars p) then \<alpha> y else \<beta> y)" 
  have "insertion \<alpha> p = insertion ?\<alpha> p" 
    by (rule insertion_irrelevant_vars, auto)
  also have "\<dots> = poly (partial_insertion \<beta> x p) (?\<alpha> x)" 
    by (rule insertion_partial_insertion[symmetric], insert assms, auto)
  finally show ?thesis by auto
qed

lemma degree_mpoly_of_poly[simp]: "mdegree (mpoly_of_poly x p) x = degree p"
proof -
  have "mdegree (mpoly_of_poly x p) x \<le> degree p"
    by (simp add: coeff_eq_0 coeff_mpoly_of_poly degree_leI)
  moreover have "degree p \<le> mdegree (mpoly_of_poly x p) x" 
  proof (cases "degree p = 0")
    case True
    thus ?thesis by auto
  next
    case 0: False
    hence "coeff p (degree p) \<noteq> 0" by auto
    also have "coeff p (degree p) = MPoly_Type.coeff (mpoly_of_poly x p) (monomial (degree p) x)" 
      by simp
    finally show ?thesis by (metis degree_geI lookup_single_eq)
  qed
  ultimately show ?thesis by auto
qed

lemma mpoly_extI: assumes "\<And> \<alpha>. insertion \<alpha> p = insertion \<alpha> (q :: 'a :: {ring_char_0,idom} mpoly)" 
  shows "p = q"
proof -
  have main: "finite vs \<Longrightarrow> vars p \<subseteq> vs \<Longrightarrow> vars q \<subseteq> vs \<Longrightarrow> (\<And> \<alpha>. insertion \<alpha> p = insertion \<alpha> q) \<Longrightarrow> p = q" for vs
  proof (induction vs arbitrary: p q rule: finite_induct)
    case (insert x vs p q)
    have "p = q \<longleftrightarrow> mpoly_to_mpoly_poly x p = mpoly_to_mpoly_poly x q"
      by (metis poly_mpoly_to_mpoly_poly)
    also have "\<dots> \<longleftrightarrow> (\<forall> m. coeff (mpoly_to_mpoly_poly x p) m = coeff (mpoly_to_mpoly_poly x q) m)"
      by (metis poly_eqI)
    also have \<dots> using insert 
    proof (intro allI insert.IH)
      fix m \<alpha>
      show "vars (coeff (mpoly_to_mpoly_poly x p) m) \<subseteq> vs" using insert.prems(1)
        by (metis Diff_eq_empty_iff Diff_insert2 dual_order.trans vars_coeff_mpoly_to_mpoly_poly)
      show "vars (coeff (mpoly_to_mpoly_poly x q) m) \<subseteq> vs" using insert.prems(2)
        by (metis Diff_eq_empty_iff Diff_insert2 dual_order.trans vars_coeff_mpoly_to_mpoly_poly)
      have IH: "partial_insertion \<alpha> x p = partial_insertion \<alpha> x q" 
      proof (intro poly_ext)
        fix y
        have "poly (partial_insertion \<alpha> x p) y = poly (partial_insertion \<alpha> x q) y \<longleftrightarrow>
         insertion (\<alpha>(x := y)) p = insertion (\<alpha>(x := y)) q"  
          using insertion_partial_insertion[of x \<alpha> "\<alpha>(x := y)"] by simp
        moreover have \<dots> by (intro insert)
        finally show "poly (partial_insertion \<alpha> x p) y = poly (partial_insertion \<alpha> x q) y" by blast
      qed
      show "insertion \<alpha> (coeff (mpoly_to_mpoly_poly x p) m) = insertion \<alpha> (coeff (mpoly_to_mpoly_poly x q) m)" 
        using insert.prems(3) by (simp add: IH)
    qed
    finally show ?case .
  next
    case (empty p q)
    hence vars: "vars p = {}" "vars q = {}" by auto
    from vars_emptyE[OF vars(1)] obtain c where p: "p = Const c" .
    from vars_emptyE[OF vars(2)] obtain d where q: "q = Const d" .
    from empty(3)[of undefined, unfolded p q] have "c = d" by auto
    thus ?case unfolding p q by simp
  qed
  show ?thesis
    by (rule main[of "vars p \<union> vars q"], insert assms, auto simp: vars_finite)
qed

lemma vars_empty_Const: assumes "vars (p :: 'a :: {ring_char_0,idom} mpoly) = {}"
  shows "\<exists> c. p = Const c" 
proof -
  {
    fix \<alpha>
    have "insertion \<alpha> p = insertion (\<lambda> _. 0) p" using assms
      by (intro insertion_irrelevant_vars, auto)
    also have "\<dots> = mcoeff p 0" by simp
    also have "\<dots> = insertion \<alpha> (Const (mcoeff p 0))" unfolding insertion_Const ..
    finally have "insertion \<alpha> p = insertion \<alpha> (Const (mcoeff p 0))" .
  }
  hence "p = (Const (mcoeff p 0))" by (rule mpoly_extI)
  thus ?thesis by auto
qed


context
  assumes ge1: "\<And> c :: 'a :: linordered_idom. c > 0 \<Longrightarrow> \<exists> x. c * x \<ge> 1"  
begin

lemma poly_ext_bounded: 
  fixes p q :: "'a poly"
  assumes "\<And>x. x \<ge> b \<Longrightarrow> poly p x = poly q x" shows "p = q"
proof -
  define r where "r = p - q" 
  from assms have r: "x \<ge> b \<Longrightarrow> poly r x = 0" for x by (auto simp: r_def)
  have "?thesis \<longleftrightarrow> r = 0" unfolding r_def by simp
  also have "\<dots>" 
  proof (cases "degree r = 0")
    case True
    from degree0_coeffs[OF this] r[of b] show ?thesis by auto
  next
    case dr: False
    define lc where "lc = lead_coeff r" 
    from dr have lc: "lc \<noteq> 0" by (auto simp: lc_def)
    define d where "d = degree r" 
    define s where "s = r - monom lc d" 
    have ds: "degree s < d" unfolding s_def lc_def using dr 
      by (smt (verit, del_insts) Polynomial.coeff_diff Polynomial.coeff_monom 
          cancel_comm_monoid_add_class.diff_cancel coeff_eq_0 d_def degree_0 
          diff_is_0_eq leading_coeff_0_iff linorder_neqE_nat linorder_not_le zero_diff)
    {
      fix x
      have "poly r x = poly (monom lc d + s) x" unfolding s_def by simp
      also have "\<dots> = lc * x ^ d + poly s x" by (simp add: poly_monom)
      finally have "poly r x = lc * x ^ d + poly s x" .
    } note eq = this
    have "\<exists> p c. (\<forall> x \<ge> b. (c :: 'a) * x ^ d + poly p x = 0) \<and> c > 0 \<and> degree p < d" 
    proof (cases "lc > 0")
      case True
      show ?thesis by (rule exI[of _ s], rule exI[of _ lc], insert True eq r ds, auto)
    next
      case False
      with lc have True: "- lc > 0" by auto 
      show ?thesis 
      proof (rule exI[of _ "- s"], rule exI[of _ "- lc"], intro conjI allI True)
        fix x
        show "b \<le> x \<longrightarrow> - lc * x ^ d + poly (- s) x = 0" using r[of x] eq[of x] by auto
      qed (insert ds, auto)
    qed
    then obtain p and c :: 'a 
      where c: "c > 0" and dp: "degree p < d" and 0: "\<And> x. x \<ge> b \<Longrightarrow> c * x ^ d + poly p x = 0" 
      by auto
    define m where "m = Max (insert 1 ((\<lambda> i. abs (coeff p i)) ` {..degree p}))"
    define M where "M = (1 + of_nat (degree p)) * m" 
    have m1: "m \<ge> 1" unfolding m_def by auto
    have mc: "i \<le> degree p \<Longrightarrow> m \<ge> abs (coeff p i)" for i unfolding m_def 
      by (intro Max_ge, auto)
    define B where "B = max b 1" 
    {
      fix x
      assume x: "x \<ge> B" 
      hence x1: "x \<ge> 1" unfolding B_def by auto
      have "abs (poly p x) = abs (\<Sum>i\<le>degree p. coeff p i * x ^ i)" 
        by (simp add: poly_altdef)
      also have "\<dots> \<le> (\<Sum>i\<le>degree p. abs (coeff p i * x ^ i))" by blast
      also have "\<dots> \<le> (\<Sum>i\<le>degree p. m * x ^ degree p)" 
      proof (intro sum_mono)
        fix i
        assume "i \<in> {..degree p}" 
        hence i: "i \<le> degree p" by auto
        have "\<bar>coeff p i * x ^ i\<bar> = \<bar>coeff p i\<bar> * \<bar>x ^ i\<bar>" by (auto simp: abs_mult)
        also have "\<dots> \<le> m * x ^ degree p" 
        proof (intro mult_mono)
          show "\<bar>coeff p i\<bar> \<le> m" using mc i by auto 
          show "0 \<le> m" using m1 by auto
          have "\<bar>x ^ i\<bar> = \<bar>x\<bar> ^ i" unfolding power_abs ..
          also have "\<dots> = x ^ i" using x1 by simp
          also have "\<dots> \<le> x ^ degree p" using x1 i
            using power_increasing by blast
          finally show "\<bar>x ^ i\<bar> \<le> x ^ degree p" by auto
        qed simp
        finally show "\<bar>coeff p i * x ^ i\<bar> \<le> m * x ^ degree p" by simp
      qed
      also have "\<dots> = M * x ^ degree p" by (simp add: M_def)
      finally have ineq: "\<bar>poly p x\<bar> \<le> M * x ^ degree p" .

      have "x \<ge> b" using x unfolding B_def by auto
      from 0[OF this] have "abs (c * x ^ d) = abs (poly p x)" by auto
      with ineq have ineq: "c * x ^ d \<le> M * x ^ degree p" by auto

      define k where "k = d - Suc (degree p)" 
      from dp have d: "d = degree p + Suc k" unfolding k_def by auto
      have xp: "x ^ degree p \<ge> 1" using x1 by simp
      have "c * x ^ d = (c * x ^ k * x) * x ^ degree p" unfolding d 
        by (simp add: algebra_simps power_add)
      from ineq[unfolded this] have ineq: "c * x ^ k * x \<le> M" using xp by simp
      have "c * x \<le> c * x^k * x" using c x1 by fastforce
      also have "\<dots> \<le> M" by fact
      finally have "c * x \<le> M" .
    }
    hence contra: "B \<le> x \<Longrightarrow> c * x \<le> M" for x .
    have "\<exists> x. c * x \<ge> 1" using c ge1 by auto
    then obtain d where cd: "c * d \<ge> 1" by auto
    with c have d: "d > 0"
      by (meson less_numeral_extra(1) order_less_le_trans zero_less_mult_pos)
    have M1: "M \<ge> 1" unfolding M_def using m1
      by (simp add: order_trans)
  
    have "M < M + 1" by auto 
    also have "\<dots> \<le> (c * d) * (M + 1)" using cd M1 by simp
    also have "\<dots> \<le> c * max B (d * (M + 1))" using M1 c d by auto
    also have "\<dots> \<le> M" using contra[of "max B (d * (M + 1))"]  by simp
    finally have False by simp
    thus ?thesis ..
  qed
  finally show ?thesis by simp
qed


lemma mpoly_ext_bounded:
  assumes "\<And> \<alpha>. (\<And> x. \<alpha> x \<ge> b) \<Longrightarrow> insertion \<alpha> p = insertion \<alpha> (q :: 'a :: linordered_idom mpoly)" 
  shows "p = q"
proof -
  have main: "finite vs \<Longrightarrow> vars p \<subseteq> vs \<Longrightarrow> vars q \<subseteq> vs \<Longrightarrow> (\<And> \<alpha>. (\<And> x. \<alpha> x \<ge> b) \<Longrightarrow> insertion \<alpha> p = insertion \<alpha> q) \<Longrightarrow> p = q" for vs
  proof (induction vs arbitrary: p q rule: finite_induct)
    case (insert x vs p q)
    have "p = q \<longleftrightarrow> mpoly_to_mpoly_poly x p = mpoly_to_mpoly_poly x q"
      by (metis poly_mpoly_to_mpoly_poly)
    also have "\<dots> \<longleftrightarrow> (\<forall> m. coeff (mpoly_to_mpoly_poly x p) m = coeff (mpoly_to_mpoly_poly x q) m)"
      by (metis poly_eqI)
    also have \<dots> 
    proof (intro allI insert.IH)
      fix m \<alpha>
      show "vars (coeff (mpoly_to_mpoly_poly x p) m) \<subseteq> vs" using insert.prems(1)
        by (metis Diff_eq_empty_iff Diff_insert2 dual_order.trans vars_coeff_mpoly_to_mpoly_poly)
      show "vars (coeff (mpoly_to_mpoly_poly x q) m) \<subseteq> vs" using insert.prems(2)
        by (metis Diff_eq_empty_iff Diff_insert2 dual_order.trans vars_coeff_mpoly_to_mpoly_poly)
      assume alpha: "\<And> x. \<alpha> (x :: nat) \<ge> (b :: 'a)" 
      have IH: "partial_insertion \<alpha> x p = partial_insertion \<alpha> x q" 
      proof (intro poly_ext_bounded[of b])
        fix y
        assume y: "y \<ge> (b :: 'a)" 
        have "poly (partial_insertion \<alpha> x p) y = poly (partial_insertion \<alpha> x q) y \<longleftrightarrow>
         insertion (\<alpha>(x := y)) p = insertion (\<alpha>(x := y)) q"  
          using insertion_partial_insertion[of x \<alpha> "\<alpha>(x := y)"] by simp
        moreover have \<dots> by (intro insert, insert y alpha, auto)
        finally show "poly (partial_insertion \<alpha> x p) y = poly (partial_insertion \<alpha> x q) y" by blast
      qed
      show "insertion \<alpha> (coeff (mpoly_to_mpoly_poly x p) m) = insertion \<alpha> (coeff (mpoly_to_mpoly_poly x q) m)" 
        using insert.prems(3) by (simp add: IH)
    qed
    finally show ?case .
  next
    case (empty p q)
    hence vars: "vars p = {}" "vars q = {}" by auto
    from vars_emptyE[OF vars(1)] obtain c where p: "p = Const c" .
    from vars_emptyE[OF vars(2)] obtain d where q: "q = Const d" .
    from empty(3)[of "\<lambda> _. b", unfolded p q] have "c = d"
      by (simp add: coeff_Const)
    thus ?case unfolding p q by simp
  qed
  show ?thesis
    by (rule main[of "vars p \<union> vars q"], insert assms, auto simp: vars_finite)
qed
end

lemma mpoly_ext_bounded_int:
  assumes "\<And> \<alpha>. (\<And> x. \<alpha> x \<ge> b) \<Longrightarrow> insertion \<alpha> p = insertion \<alpha> (q :: int mpoly)" 
  shows "p = q"
  by (rule mpoly_ext_bounded[of b], insert assms, auto simp: exI[of _ 1])

lemma mpoly_ext_bounded_field:
  assumes "\<And> \<alpha>. (\<And> x. \<alpha> x \<ge> b) \<Longrightarrow> insertion \<alpha> p = insertion \<alpha> (q :: 'a :: linordered_field mpoly)" 
  shows "p = q"
  apply (rule mpoly_ext_bounded[of b])
  subgoal for c by (intro exI[of _ "inverse c"], auto)
  subgoal using assms by auto
  done

lemma mpoly_of_poly_is_poly_to_mpoly: "mpoly_of_poly = poly_to_mpoly"
  unfolding poly_to_mpoly_def
  apply transfer'
  apply (unfold mpoly_of_poly_aux_def) 
  apply transfer'
  apply (unfold when_def[symmetric]) 
  by (intro ext, auto)

lemma insertion_poly_to_mpoly [simp]: "insertion f (poly_to_mpoly i p) = poly p (f i)"
  unfolding mpoly_of_poly_is_poly_to_mpoly[symmetric] by simp

lemma substitute_poly_to_mpoly: 
  assumes x: "\<alpha> x = poly_to_mpoly y (q :: 'a :: {ring_char_0,idom} poly)" 
  shows "substitute \<alpha> (poly_to_mpoly x p) = poly_to_mpoly y (pcompose p q)" 
  apply (rule mpoly_extI)
  apply (unfold insertion_substitute insertion_poly_to_mpoly x) 
  apply (unfold poly_pcompose)
  by auto

lemma total_degree_add_Const: "total_degree (p + Const (c :: 'a :: comm_ring_1)) = total_degree p" 
proof -
  have "total_degree (p + Const c) \<le> total_degree p" 
    by (rule total_degree_add, auto)
  moreover have "total_degree ((p + Const c) + Const (-c)) \<le> total_degree (p + Const c)"  
    by (rule total_degree_add, auto)
  moreover have "(p + Const c) + Const (- c) = p" by (simp add: Const_add[symmetric])
  ultimately show ?thesis by auto
qed

lemma mpoly_as_sum_any: "(p :: 'a :: comm_ring_1 mpoly) = Sum_any (\<lambda> m. mmonom m (mcoeff p m))" 
proof (induct p rule: mpoly_induct)
  case (monom m a)
  thus ?case 
    by transfer (smt (verit) Sum_any.cong Sum_any_when_equal' lookup_single_eq lookup_single_not_eq single_zero when_neq_zero when_simps(1))
next
  case 1: (sum p1 p2 m a)
  show ?case
    apply (subst 1(1), subst 1(2))
    apply (unfold coeff_add monom_add)
    by (smt (z3) "1"(1) "1"(2) MPoly_Type_monom_zero Sum_any.cong Sum_any.distrib Sum_any.infinite add_cancel_left_left add_cancel_left_right mpoly_coeff_0)
qed

lemma mpoly_as_sum: "(p :: 'a :: comm_ring_1 mpoly) = sum (\<lambda> m. mmonom m (mcoeff p m)) {m . mcoeff p m \<noteq> 0}" 
  apply (subst mpoly_as_sum_any)
  by (smt (verit, ccfv_SIG) Collect_cong MPoly_Type_monom_0_iff Sum_any.expand_set)

lemma monom_as_prod: "mmonom m c = Const (c :: 'a :: comm_semiring_1) * prod (\<lambda> i. Var i ^ lookup m i) (keys m)" 
  unfolding var_list
  apply (intro arg_cong[of _ _ "\<lambda> x. _ * x"])
  apply transfer'
  apply (subst prod.distinct_set_conv_list[symmetric])
  subgoal unfolding distinct_map by (auto simp: inj_on_def)
  subgoal unfolding set_map image_comp set_sorted_list_of_set[OF finite_keys]
    by (smt (verit, best) case_prod_conv finite_keys o_def prod.cong prod.inject prod.reindex_nontrivial)
  done  
  
lemma poly_to_mpoly_substitute_same: assumes "poly_to_mpoly x q = substitute (\<lambda>i. Var x) p"
  shows "poly q a = insertion (\<lambda>x. a) p"
  using arg_cong[OF assms, of "insertion (\<lambda> _. a)", unfolded insertion_poly_to_mpoly
         insertion_substitute insertion_Var]
  by simp

lemma substitute_monom: fixes c :: "'a :: comm_semiring_1"
  shows "substitute a (mmonom m c) = Const c * prod (\<lambda> i. a i ^ lookup m i) (keys m)" 
  by (subst monom_as_prod) (simp add: substitute_prod o_def)

lemma degree_prod: assumes "prod p A \<noteq> (0 :: 'a :: idom mpoly)"
  shows "mdegree (prod p A) x = sum (\<lambda> i. mdegree (p i) x) A" 
  using assms
  by (induct A rule: infinite_finite_induct) (auto simp: mpoly_degree_mult_eq)

lemma degree_prod_le: fixes p :: "_ \<Rightarrow> 'a :: idom mpoly" 
  shows "mdegree (prod p A) x \<le> sum (\<lambda> i. mdegree (p i) x) A"
  using degree_prod[of p A x] by (cases "prod p A = 0"; auto)

lemma degree_power: assumes "p \<noteq> (0 :: 'a :: idom mpoly)"
  shows "mdegree (p^n) x = n * mdegree p x" 
  by (induct n) (insert assms, auto simp: mpoly_degree_mult_eq)

lemma mdegree_Const_mult_le: "mdegree (Const (c :: 'a :: idom) * p) x \<le> mdegree p x"
  using mpoly_degree_mult_eq[of "Const c" p x]
  by (cases "c = 0"; cases "p = 0"; auto)

lemma degree_substitute_const_same_var: "mdegree (substitute (\<lambda>i. Const (c i) * Var x) (p :: 'a :: idom mpoly)) x \<le> total_degree p"
proof -
  {
    fix i
    let ?x = "Var x :: 'a mpoly" 
    assume i: "mcoeff p i \<noteq> 0" 
    have "mdegree (\<Prod>ia\<in>keys i. (Const (c ia) * ?x) ^ lookup i ia) x \<le> total_degree p" 
      apply (intro order.trans[OF _ degree_monon_le_total_degree[of p i, OF i]])
      apply (intro order.trans[OF degree_prod_le])
      apply (rule order.trans[OF sum_mono[of _ _ "lookup i"]])
       apply (unfold power_mult_distrib Const_power[symmetric])
       apply (rule order.trans[OF mdegree_Const_mult_le])
       apply (subst degree_power, force)
       apply (subst degree_Var)
      by (auto simp add: degree_monom_def)
  } note main = this
  show ?thesis
    apply (subst (5) mpoly_as_sum)
    apply (unfold substitute_sum o_def substitute_monom substitute_mult)
    apply (intro degree_sum_leI)
    apply (rule order.trans[OF mdegree_Const_mult_le])
    using main by auto
qed

lemma degree_substitute_same_var: "mdegree (substitute (\<lambda>i. Var x) (p :: 'a :: idom mpoly)) x \<le> total_degree p" 
  using degree_substitute_const_same_var[of "\<lambda> _. 1", unfolded Const_1] by auto

lemma poly_pinfty_ge_int: assumes "0 < lead_coeff (p :: int poly)"
  and "degree p \<noteq> 0" 
  shows "\<exists>n. \<forall>x\<ge>n. b \<le> poly p x" 
proof -
  let ?q = "of_int_poly p :: real poly" 
  from assms have "0 < lead_coeff ?q" "degree ?q \<noteq> 0" by auto
  from poly_pinfty_ge[OF this, of "of_int b"] obtain n 
    where le: "\<And> x. x \<ge> n \<Longrightarrow> real_of_int b \<le> poly ?q x" by auto
  show ?thesis
  proof (intro exI[of _ "ceiling n"] allI impI)
    fix x
    assume "x \<ge>  \<lceil>n\<rceil>" 
    hence "of_int x \<ge> n" by linarith
    from le[OF this] show "b \<le> poly p x" by simp
  qed
qed

context
  assumes poly_pinfty_ge: "\<And> p b. 0 < lead_coeff (p :: 'a :: linordered_idom poly)
    \<Longrightarrow> degree p \<noteq> 0 \<Longrightarrow> \<exists>n. \<forall>x\<ge>n. b \<le> poly p x" 
begin
lemma degree_mono_generic: assumes pos: "lead_coeff p \<ge> (0 :: 'a)"
  and le: "\<And> x. x \<ge> c \<Longrightarrow> poly p x \<le> poly q x" 
shows "degree p \<le> degree q" 
proof (rule ccontr)
  let ?lc = lead_coeff
  define r where "r = p - q" 
  assume "\<not> ?thesis" 
  hence deg: "degree p > degree q" by auto
  hence deg_eq: "degree r = degree p" unfolding r_def
    by (metis degree_add_eq_right degree_minus uminus_add_conv_diff)
  from deg have "?lc p \<noteq> 0" by auto
  with pos have pos: "?lc p > 0" by auto
  have "?lc r = ?lc p" unfolding r_def 
    using deg_eq le_degree r_def deg by fastforce
  with pos have lcr: "?lc r > 0" by auto
  from deg_eq deg have dr: "degree r \<noteq> 0" by auto
  have "x \<ge> c \<Longrightarrow> poly r x \<le> 0" for x using le[of x] unfolding r_def by auto
  with poly_pinfty_ge[OF lcr dr] show False
    by (metis dual_order.trans nle_le not_one_le_zero)
qed

lemma degree_mono'_generic: assumes le: "\<And> x. x \<ge> c \<Longrightarrow> (bnd :: 'a) \<le> poly p x \<and> poly p x \<le> poly q x" 
  shows "degree p \<le> degree q" 
proof (cases "degree p = 0")
  case deg: False
  show ?thesis
  proof (rule degree_mono_generic[of _ c])
    show "\<And>x. c \<le> x \<Longrightarrow> poly p x \<le> poly q x" using le by auto  
    let ?lc = lead_coeff
    show "0 \<le> ?lc p" 
    proof (rule ccontr)
      assume "\<not> ?thesis" 
      hence "?lc (- p) > 0" "degree (- p) \<noteq> 0" using deg by auto
      from poly_pinfty_ge[OF this, of "- bnd + 1", simplified]
      obtain n where "\<And> x. x \<ge> n \<Longrightarrow> 1 - bnd \<le> - poly p x" by auto
      from le[of "max n c"] this[of "max n c"] show False by auto
    qed
  qed
qed auto

end

definition nneg_poly :: "'a :: {linordered_semidom, semiring_no_zero_divisors} poly \<Rightarrow> bool" where 
  "nneg_poly p = ((\<forall> x. x \<ge> 0 \<longrightarrow> poly p x \<ge> 0) \<and> lead_coeff p \<ge> 0)" 

lemma nneg_poly_nneg: assumes "nneg_poly p" 
  and "x \<ge> 0" 
shows "poly p x \<ge> 0" 
  using assms unfolding nneg_poly_def by auto
    

lemma nneg_poly_lead_coeff: assumes "nneg_poly p" 
  shows "p \<noteq> 0 \<Longrightarrow> lead_coeff p > 0" 
  using assms unfolding nneg_poly_def
  by (metis antisym_conv2 leading_coeff_neq_0)

lemma nneg_poly_add: assumes "nneg_poly p" "nneg_poly q" 
  shows "nneg_poly (p + q)" "degree (p + q) = max (degree p) (degree q)" 
proof -
  {
    fix p q :: "'a poly" 
    assume le: "degree p \<le> degree q" and pq: "nneg_poly p" "nneg_poly q"
    have "nneg_poly (p + q) \<and> degree (p + q) = max (degree p) (degree q)"
    proof (cases "degree p = degree q")
      case True
      show ?thesis
      proof (cases "p = 0 \<or> q = 0")
        case True
        thus ?thesis using pq by auto
      next
        case False
        with nneg_poly_lead_coeff[of p] nneg_poly_lead_coeff[of q] pq
        have lc: "lead_coeff p > 0" "lead_coeff q > 0" by auto
        have "degree (p + q) = degree q" using lc True
          by (smt (verit, del_insts) Polynomial.coeff_add add_cancel_left_left add_le_same_cancel2 le_degree leading_coeff_0_iff linorder_not_le order_less_le)
        with lc pq True show ?thesis unfolding nneg_poly_def by auto
      qed
    next
      case False
      with le have lt: "degree p < degree q" by auto
      hence 1: "degree (p + q) = degree q"
        by (simp add: degree_add_eq_right)
      with lt have 2: "lead_coeff (p + q) = lead_coeff q"
        using lead_coeff_add_le by blast
      from 1 2 pq lt show ?thesis by (auto simp: nneg_poly_def)
    qed
  } note main = this
  have "degree p \<le> degree q \<or> degree q \<le> degree p" by linarith
  with main[of p q] main[of q p] assms
  have "nneg_poly (p + q) \<and> degree (p + q) = max (degree p) (degree q)"
    by (auto simp: ac_simps)
  thus "nneg_poly (p + q)" "degree (p + q) = max (degree p) (degree q)" 
    by auto
qed
  

lemma nneg_poly_mult: assumes "nneg_poly p" "nneg_poly q"
  shows "nneg_poly (p * q)" 
  using assms unfolding nneg_poly_def poly_mult Polynomial.lead_coeff_mult
  by (intro allI conjI mult_nonneg_nonneg impI, auto)

lemma nneg_poly_const[simp]: "nneg_poly [:c:] = (c \<ge> 0)" 
  unfolding nneg_poly_def by (auto dest: spec[of _ 0] simp add: coeff_const)

lemma nneg_poly_pCons[simp]: "a \<ge> 0 \<and> nneg_poly p \<Longrightarrow> nneg_poly (pCons a p)" 
  unfolding nneg_poly_def by (auto simp: coeff_pCons split: nat.splits)

lemma nneg_poly_0[simp]: "nneg_poly 0" 
  unfolding nneg_poly_def by auto

lemma nneg_poly_pcompose: assumes "nneg_poly p" "nneg_poly q"
  shows "nneg_poly (pcompose p q)" 
proof (cases "degree q > 0")
  case True
  show ?thesis unfolding nneg_poly_def poly_pcompose lead_coeff_comp[OF True]
    using assms unfolding nneg_poly_def by auto
next
  case False
  hence "degree q = 0" by auto
  from degree0_coeffs[OF this] obtain c where q: "q = [:c:]" by auto
  with assms[unfolded nneg_poly_def] have c: "c \<ge> 0" by auto
  have pq: "p \<circ>\<^sub>p q = [: poly p c :]" unfolding q
    by (metis (no_types, opaque_lifting) add.right_neutral coeff_pCons_0 mult_zero_left pcompose_0' pcompose_assoc poly_pCons poly_pcompose)  
  show ?thesis using assms(1) unfolding nneg_poly_def pq using c by auto
qed


lemma nneg_poly_degree_add_1: assumes p: "nneg_poly p" and a: "a1 > 0" "a2 > 0" 
  shows "degree (p * [:b, a1:] + [:c, a2:]) = 1 + degree p" 
proof (cases "degree p = 0")
  case False
  thus ?thesis
    apply (subst degree_add_eq_left, insert p) 
    subgoal using a
      by (metis One_nat_def degree_mult_eq_0 degree_pCons_eq_if irreducible\<^sub>d_multD less_one linear_irreducible\<^sub>d linorder_neqE_nat order_less_le pCons_eq_0_iff)
    subgoal using a
      by (metis Suc_eq_plus1 add.commute add.right_neutral degree_mult_eq degree_pCons_eq_if not_pos_poly_0 pCons_eq_0_iff pos_poly_pCons)
    done
next
  case True
  then obtain c where p: "p = [:c:]" and c: "c \<ge> 0" using p degree0_coeffs[of p] by auto
  show ?thesis unfolding p using c a by (auto simp: add_nonneg_eq_0_iff) 
qed

lemma nneg_poly_degree_add: assumes pq: "nneg_poly (p :: 'a :: linordered_idom poly)" "nneg_poly q" 
  and a: "a3 > 0" "a2 > 0" "a1 > 0" 
shows "degree ([:a3:] * q * p + ([:a2:] * q + [:a1:] * p + [:a0:])) = degree p + degree q" 
proof -
  {
    fix p q :: "'a poly" and a2 a1 :: 'a
    assume pq: "nneg_poly p" "nneg_poly q" 
     and dq: "degree q \<noteq> 0" 
     and a: "a2 > 0" "a1 > 0"
    have deg0: "p \<noteq> 0 \<Longrightarrow> degree ([:a3:] * q * p) = degree p + degree q" using dq \<open>a3 > 0\<close> a 
      by (metis (no_types, lifting) add.commute add_cancel_left_left degree_mult_eq degree_pCons_eq_if linorder_not_le nle_le pCons_eq_0_iff)
    have degmax: "degree ([:a2:] * q + [:a1:] * p + [:a0:]) \<le> max (degree q) (degree p)"
      by (simp add: degree_add_le)
    have deg: "degree ([:a3:] * q * p + ([:a2:] * q + [:a1:] * p + [:a0:])) = degree p + degree q" 
    proof (cases "degree p = 0")
      case False
      have id: "degree ([:a3:] * q * p) = degree p + degree q" by (rule deg0, insert False, auto)
      moreover have "max (degree q) (degree p) < degree p + degree q" using False dq by auto
      ultimately show ?thesis by (subst degree_add_eq_left, insert degmax, auto)
    next
      case True
      with pq obtain c where p: "p = [:c:]" and c: "c \<ge> 0" using degree0_coeffs[of p] by auto
      define d where "d = c * a3 + a2" 
      from a \<open>a3 > 0\<close> c have d0: "d \<noteq> 0"
        by (simp add: add_nonneg_eq_0_iff d_def)
      have id: "[:a3:] * q * [:c:] + ([:a2:] * q + [:a1:] * [:c:] + [:a0:]) 
         = [:c * a1 + a0:] + [:d:] * q" 
        by (simp add: smult_add_left d_def) 
      show ?thesis unfolding p unfolding id
        by (subst degree_add_eq_right, insert d0 dq, auto)
    qed
  } note main = this
  show ?thesis
  proof (cases "degree q = 0")
    case False
    from main[OF pq False a(2,3)] show ?thesis .
  next
    case dq: True
    show ?thesis
    proof (cases "degree p = 0")
      case False
      from main[OF pq(2,1) False a(3,2)] show ?thesis by (simp add: algebra_simps)
    next
      case dp: True
      from degree0_coeffs[OF dp] degree0_coeffs[OF dq] show ?thesis by auto
    qed
  qed
qed


lemma poly_pinfty_gt_lc: (* TODO: change in distribution where this lemma is proved for type real *)
  fixes p :: "'a :: linordered_field poly"
  assumes "lead_coeff p > 0"
  shows "\<exists>n. \<forall> x \<ge> n. poly p x \<ge> lead_coeff p"
  using assms
proof (induct p)
  case 0
  then show ?case by auto
next
  case (pCons a p)
  from this(1) consider "a \<noteq> 0" "p = 0" | "p \<noteq> 0" by auto
  then show ?case
  proof cases
    case 1
    then show ?thesis by auto
  next
    case 2
    with pCons obtain n1 where gte_lcoeff: "\<forall>x\<ge>n1. lead_coeff p \<le> poly p x"
      by auto
    from pCons(3) \<open>p \<noteq> 0\<close> have gt_0: "lead_coeff p > 0" by auto
    define n where "n = max n1 (1 + \<bar>a\<bar> / lead_coeff p)"
    have "lead_coeff (pCons a p) \<le> poly (pCons a p) x" if "n \<le> x" for x
    proof -
      from gte_lcoeff that have "lead_coeff p \<le> poly p x"
        by (auto simp: n_def)
      with gt_0 have "\<bar>a\<bar> / lead_coeff p \<ge> \<bar>a\<bar> / poly p x" and "poly p x > 0"
        by (auto intro: frac_le)
      with \<open>n \<le> x\<close>[unfolded n_def] have "x \<ge> 1 + \<bar>a\<bar> / poly p x"
        by auto
      with \<open>lead_coeff p \<le> poly p x\<close> \<open>poly p x > 0\<close> \<open>p \<noteq> 0\<close>
      show "lead_coeff (pCons a p) \<le> poly (pCons a p) x"
        by (auto simp: field_simps)
    qed
    then show ?thesis by blast
  qed
qed

lemma poly_pinfty_ge: (* TODO: change in AFP to from real 'a *)
  fixes p :: "'a :: linordered_field poly"
  assumes "lead_coeff p > 0" "degree p \<noteq> 0" 
  shows "\<exists>n. \<forall> x \<ge> n. poly p x \<ge> b"
proof -
  let ?p = "p - [:b - lead_coeff p :]" 
  have id: "lead_coeff ?p = lead_coeff p" using assms(2)
    by (cases p, auto)
  with assms(1) have "lead_coeff ?p > 0" by auto
  from poly_pinfty_gt_lc[OF this, unfolded id] obtain n
    where "\<And> x. x \<ge> n \<Longrightarrow> 0 \<le> poly p x - b" by auto
  thus ?thesis by auto
qed

lemma nneg_polyI: fixes p :: "'a::linordered_field poly"
  assumes "\<And> x. 0 \<le> x \<Longrightarrow> 0 \<le> poly p x" 
  shows "nneg_poly p" 
  unfolding nneg_poly_def
proof (intro allI conjI impI assms)
  
  {
    assume lc: "lead_coeff p < 0" 
    hence lc0: "lead_coeff (- p) > 0" by auto
    from lc assms[of 0] have "degree p \<noteq> 0" using degree0_coeffs[of p] 
      by (cases "degree p = 0"; auto)
    from poly_pinfty_ge[OF lc0, of 1] this obtain n where "\<And> x. x \<ge> n \<Longrightarrow> poly p x \<le> - 1" 
      by auto
    with assms have False
      by (meson neg_0_le_iff_le nle_le not_one_le_zero order_trans)
  }
  thus "lead_coeff p \<ge> 0" by force
qed


lemma poly_bounded: fixes x :: "'a:: linordered_idom" 
    assumes "abs x \<le> b" 
    shows "abs (poly p x) \<le> (\<Sum>i \<le> degree p. abs (coeff p i) * b ^ i)" 
  unfolding poly_altdef
  apply (intro order.trans[OF sum_abs] sum_mono)
  apply (unfold abs_mult power_abs, intro mult_left_mono power_mono assms)
  by auto

lemma poly_degree_le_large_const: 
  assumes pq: "degree (p :: 'a :: linordered_field poly) \<ge> degree q" 
   and p0: "\<And> x. x \<ge> 0 \<Longrightarrow> poly p x \<ge> 0" (* it does not suffice to be monotone, e.g., take p = x - 1 and q = 0 *)   
 shows "\<exists> H. \<forall> h \<ge> H. \<forall> x \<ge> 0. h * poly p x + h \<ge> poly q x" 
proof (cases "degree p = 0")
  case True
  with pq p0[of 0] obtain c d where p: "p = [:c:]" and q: "q = [:d:]" and c: "c \<ge> 0" 
    using degree0_coeffs[of p] degree0_coeffs[of q] by auto
  show ?thesis unfolding p q using c 
    apply (intro exI[of _ "max d 0"], cases "d \<le> 0") 
    subgoal using order_trans by fastforce 
    by (simp add: add.commute add_increasing2)
next
  case False
  define lc where "lc = lead_coeff p" 
  define dp where "dp = degree p"
  have dp1: "dp \<ge> 1" using False unfolding dp_def by auto
  from p0 have "lc \<ge> 0" unfolding lc_def using poly_pinfty_ge[of "-p" 1]
    by (metis (no_types, opaque_lifting) False degree_minus lead_coeff_minus linorder_not_le neg_le_0_iff_le nle_le not_one_le_zero order_le_less_trans poly_minus)
  with False have lc: "lc > 0" by (cases "lc = 0", auto simp: lc_def)
  define d where "d = inverse lc" 
  define dlc where "dlc = d * lc" 
  have dlc: "dlc \<ge> 1" using lc by (auto simp: field_simps d_def dlc_def)
  with lc have d: "d > 0" unfolding dlc_def 
    by (simp add: d_def)
  define h1 where "h1 = d * (1 + abs (coeff q dp))"   
  define r where "r = smult h1 p - q"
  have "coeff r dp = h1 * lc - coeff q dp" unfolding r_def lc_def dp_def by simp
  also have "\<dots> = dlc * (1 + abs (coeff q dp)) - coeff q dp" unfolding h1_def dlc_def by simp 
  also have "- \<dots> \<le> - ((1 + abs (coeff q dp)) - coeff q dp)" 
    unfolding neg_le_iff_le using dlc
    by (intro diff_right_mono)
      (simp add: abs_add_one_gt_zero)
  also have "\<dots> \<le> - 1" by simp
  finally have coeff_r: "coeff r dp > 0" by auto

  have dpr: "dp = degree r" 
  proof -
    have le: "dp \<le> degree r" using coeff_r
      by (simp add: le_degree)
    have "degree r \<le> dp" unfolding dp_def r_def using assms(1) 
      by (simp add: degree_diff_le)
    with le show ?thesis by auto
  qed
  with coeff_r have lcr: "lead_coeff r > 0" by auto
  from dpr dp1 have "degree r \<noteq> 0" by auto
  from poly_pinfty_ge[OF lcr this, of 0]
  obtain n where n: "\<And> x. x \<ge> n \<Longrightarrow> 0 \<le> poly r x" by auto
  define M where "M = max n 0" 
  from poly_bounded[of _ M r] obtain h2 where h2: "abs x \<le> M \<Longrightarrow> abs (poly r x) \<le> h2" for x by blast
  have h20: "h2 \<ge> 0" using h2[of 0] unfolding M_def by auto
  have h10: "h1 > 0" using d unfolding h1_def by auto
  define H where "H = max h1 h2" 
  have H0: "H \<ge> 0" using h10 unfolding H_def by auto
  show ?thesis
  proof (intro exI[of _ H] conjI allI impI)
    fix h x :: 'a
    assume h: "h \<ge> H" 
    with H0 have h0: "h \<ge> 0" by auto
    assume x0: "x \<ge> 0" 
    show "poly q x \<le> h * poly p x + h" 
    proof (cases "x \<ge> M")
      case x: True
      have h: "h \<ge> h1" using h H_def by auto
      define h3 where "h3 = h - h1" 
      have h: "h = h1 + h3" and h2: "h3 \<ge> 0" using h unfolding h3_def by auto
      have r: "0 \<le> poly r x" and p: "0 \<le> poly p x" 
        using x n[of x] p0[of x] unfolding M_def by auto
      have "h * poly p x = h1 * poly p x + h3 * poly p x" unfolding h by (simp add: algebra_simps)
      also have "- \<dots> \<le> - (h1 * poly p x)" 
        unfolding neg_le_iff_le using h2 p by auto
      also have "\<dots> \<le> - (poly q x)" 
        unfolding neg_le_iff_le using r unfolding r_def
        by simp
      finally have "h * poly p x \<ge> poly q x" by simp
      with h0 show ?thesis by auto
    next
      case False
      with x0 have "abs x \<le> M" by auto
      from h2[OF this] have "poly r x \<ge> - h2" by auto
      from this[unfolded r_def]
      have "poly q x \<le> h1 * poly p x + h2" by simp
      also have "\<dots> \<le> h * poly p x + h" 
        by (intro add_mono mult_right_mono p0 x0)
        (insert h, auto simp: H_def)
      finally show ?thesis .
    qed
  qed
qed

lemma degree_monom_0[simp]: "degree_monom 0 = 0" 
  unfolding degree_monom_def by auto

lemma degree_monom_monomial[simp]: "degree_monom (monomial n x) = n" 
  unfolding degree_monom_def by auto

lemma keys_add: "keys (m + n :: monom) = keys m \<union> keys n" 
  by (rule keys_plus_ninv_comm_monoid_add)

lemma degree_monom_add[simp]: "degree_monom (m + n) = degree_monom m + degree_monom n" 
  unfolding degree_monom_def keys_add lookup_plus_fun 
proof (transfer, goal_cases)
  case (1 m n)
  have id: "{k. m k \<noteq> 0} \<union> {k. n k \<noteq> 0} = 
    {k. m k \<noteq> 0} \<inter> {k. n k = 0} \<union> {k. n k \<noteq> 0} \<inter> {k. m k = 0}
  \<union> {k. m k \<noteq> 0} \<inter> {k. n k \<noteq> 0}" by auto
  have id1: "sum m {k. m k \<noteq> 0} = sum m ({k. m k \<noteq> 0} \<inter> {k. n k = 0} \<union> {k. m k \<noteq> 0} \<inter> {k. n k \<noteq> 0})" 
    by (rule sum.cong, auto)
  have id2: "sum n {k. n k \<noteq> 0} = sum n ({k. n k \<noteq> 0} \<inter> {k. m k = 0} \<union> {k. m k \<noteq> 0} \<inter> {k. n k \<noteq> 0})" 
    by (rule sum.cong, auto)
  show ?case unfolding id
    apply (subst sum.union_disjoint)
    subgoal using 1 by auto
    subgoal using 1 by auto
    subgoal by auto
    apply (subst sum.union_disjoint)
    subgoal using 1 by auto
    subgoal using 1 by auto
    subgoal by auto
    apply (unfold id1)
    apply (subst sum.union_disjoint)
    subgoal using 1 by auto
    subgoal using 1 by auto
    subgoal by auto
    apply (unfold id2)
    apply (subst sum.union_disjoint)
    subgoal using 1 by auto
    subgoal using 1 by auto
    subgoal by auto
    by (simp add: sum.distrib) 
qed

lemma degree_monom_of_set: "finite xs \<Longrightarrow> degree_monom (monom_of_set xs) = card xs" 
  unfolding degree_monom_def
  by (transfer, auto)

lemma keys_singletonE: assumes "keys m = {x}" 
  shows "\<exists> c. m = monomial c x \<and> c = degree_monom m \<and> c \<noteq> 0" 
proof -
  define c where "c = degree_monom m" 
  from assms have mc: "m = monomial c x" unfolding c_def
    by (metis degree_monom_monomial except_keys group_cancel.rule0 plus_except)
  have "c \<noteq> 0" using assms unfolding mc by (simp split: if_splits)
  from mc c_def this show ?thesis by blast
qed

lemma degree_monom_0_iff: "degree_monom m = 0 \<longleftrightarrow> m = 0" 
  unfolding degree_monom_def
  by transfer auto

lemma degree_0_imp_Const: fixes p :: "'a :: comm_ring_1 mpoly" 
  assumes d0: "total_degree p = 0"
  shows "\<exists> c. p = Const c" 
proof -
  {
    fix m 
    assume "mcoeff p m \<noteq> 0" 
    from degree_monon_le_total_degree[OF this, unfolded d0]
    have "m = 0" by (auto simp: degree_monom_0_iff)
  }
  hence "{m . mcoeff p m \<noteq> 0} = {} \<or> {m . mcoeff p m \<noteq> 0} = {0}" by auto
  thus ?thesis
  proof
    assume id: "{m . mcoeff p m \<noteq> 0} = {}" 
    have "p = sum (\<lambda> m. mmonom m (mcoeff p m)) {m . mcoeff p m \<noteq> 0}" 
      by (rule mpoly_as_sum)
    also have "\<dots> = 0" unfolding id by simp
    also have "\<dots> = Const 0" by simp
    finally show ?thesis by blast
  next
    assume id: "{m. mcoeff p m \<noteq> 0} = {0}" 
    have "p = sum (\<lambda> m. mmonom m (mcoeff p m)) {m . mcoeff p m \<noteq> 0}" 
      by (rule mpoly_as_sum)
    also have "\<dots> = mmonom 0 (mcoeff p 0)" unfolding id by simp
    also have "\<dots> = Const (mcoeff p 0)"
      using mpoly_monom_0_eq_Const by blast
    finally show ?thesis by blast
  qed
qed

lemma binary_degree_2_poly: fixes p :: "'a :: {ring_char_0,idom} mpoly" 
  assumes td: "total_degree p \<le> 2" 
  and vars: "vars p = {x,y}"
  and xy: "x \<noteq> y" 
shows "\<exists> a b c d e f. 
  p = Const a + Const b * Var x + Const c * Var y + 
      Const d * Var x * Var x + Const e * Var y * Var y + Const f * Var x * Var y"
proof -
  let ?p = "mcoeff p" 
  let ?x = "monomial 1 x" 
  let ?y = "monomial 1 y" 
  let ?a = "?p 0"
  let ?b = "?p ?x" 
  let ?c = "?p ?y" 
  let ?d = "?p (monomial 2 x)" 
  let ?e = "?p (monomial 2 y)" 
  let ?f = "?p (monom_of_set {x,y})" 
  define XY where "XY = {m :: nat \<Rightarrow>\<^sub>0 nat. keys m \<subseteq> {x,y} \<and> degree_monom m \<le> 2}" 
  let ?xy = "[0,?x,?y, monomial 2 x, monomial 2 y, monom_of_set {x,y}]" 
  have eq: "m = n \<Longrightarrow> keys m = keys n" for m n :: monom by auto 
  have xy: "distinct ?xy" using xy 
    by (auto dest: eq)
  have XY: "XY = set ?xy" 
  proof 
    show "set ?xy \<subseteq> XY" unfolding XY_def by (simp add: keys_add degree_monom_of_set card_insert_if)
    show "XY \<subseteq> set ?xy" 
    proof
      fix m
      assume "m \<in> XY" 
      hence keys: "keys m \<subseteq> {x,y}" and deg: "degree_monom m \<le> 2" unfolding XY_def by auto
      define km where "km = keys m" 
      from keys have "keys m \<in> {{}, {x}, {y}, {x,y}}" unfolding km_def[symmetric] by auto  
      then consider (e) "keys m = {}" | (x) "keys m = {x}" | (y) "keys m = {y}" | (xy) "keys m = {x,y}" by auto
      thus "m \<in> set ?xy" 
      proof cases 
        case e
        thus ?thesis by auto
      next
        case x
        from keys_singletonE[OF this]
        obtain c where m: "m = monomial c x" and c: "c = degree_monom m" "c \<noteq> 0" by auto
        from c deg have "c \<in> {1,2}" by auto
        with m show ?thesis by auto
      next
        case y
        from keys_singletonE[OF this]
        obtain c where m: "m = monomial c y" and c: "c = degree_monom m" "c \<noteq> 0" by auto
        from c deg have "c \<in> {1,2}" by auto
        with m show ?thesis by auto
      next
        case xy
        have "m = monom_of_set {x, y}" using xy deg \<open>x \<noteq> y\<close>
          unfolding degree_monom_def
        proof (transfer, goal_cases)
          case (1 m x y)
          have xy: "m x \<noteq> 0" "m y \<noteq> 0" using 1(2) by auto
          have "sum m {k. m k \<noteq> 0} = m x + m y + sum m ({k. m k \<noteq> 0} - {x,y})" 
            using xy 1(1,2,4) by auto
          with 1(3) xy have xy: "m x = 1" "m y = 1" and 
            rest: "sum m ({k. m k \<noteq> 0} - {x,y}) = 0" by auto
          from rest have rest: "z \<notin> {x,y} \<Longrightarrow> m z = 0" for z using 1(2) by blast
          show ?case by (intro ext, insert xy rest, auto)
        qed
        thus ?thesis by auto
      qed
    qed
  qed
  have "p = (\<Sum>m. mmonom m (mcoeff p m))" 
    by (rule mpoly_as_sum_any)
  also have "\<dots> = (\<Sum>m\<in>{a. mmonom a (mcoeff p a) \<noteq> 0}. mmonom m (mcoeff p m))" 
    unfolding Sum_any.expand_set by simp
  also have "\<dots> = (\<Sum>m\<in>{a. mmonom a (mcoeff p a) \<noteq> 0} \<inter> XY. mmonom m (mcoeff p m))" 
    apply (rule sum.mono_neutral_right; (intro ballI)?)
    subgoal by auto
    subgoal by auto
    subgoal for m using vars order.trans[OF degree_monon_le_total_degree[of p m] td] unfolding XY_def
      by simp (smt (verit, best) DiffD2 MPoly_Type_monom_zero coeff_notin_vars mem_Collect_eq)
    done
  also have "\<dots> = (\<Sum>m\<in>XY. mmonom m (mcoeff p m))" 
    apply (rule sum.mono_neutral_left)
    subgoal unfolding XY by auto
    subgoal by auto
    subgoal by auto
    done
  also have "\<dots> = (\<Sum>m \<leftarrow> ?xy. mmonom m (mcoeff p m))" 
    unfolding XY using xy by force
  also have "\<dots> = Const ?a + Const ?b * Var x + Const ?c * Var y + 
      Const ?d * Var x * Var x + Const ?e * Var y * Var y + Const ?f * Var x * Var y" 
    apply (intro mpoly_extI)
    unfolding insertion_sum_list map_map o_def insertion_add insertion_mult insertion_Const insertion_Var
       sum_list.Cons list.simps insertion_single insertion_monom_of_set mpoly_monom_0_eq_Const
    using xy
    by (simp add: power2_eq_square)
  finally show ?thesis by blast
qed

lemma bounded_negative_factor: assumes "\<And> x. c \<le> (x :: 'a :: linordered_field) \<Longrightarrow> a * x \<le> b"
  shows "a \<le> 0" 
proof (rule ccontr)
  assume "\<not> ?thesis" 
  hence "a > 0" by auto
  hence "y \<ge> c \<Longrightarrow> y \<ge> 0 \<Longrightarrow> y \<le> b" for y using assms[of "inverse a * y"]
    by (metis (no_types, opaque_lifting) assms dual_order.trans linorder_not_le mult.commute mult_imp_less_div_pos nle_le)
  from this[of "1 + max 0 (max c b)"]
  show False by linarith
qed


end