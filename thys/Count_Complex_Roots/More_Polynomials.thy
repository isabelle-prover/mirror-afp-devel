(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)
section \<open>More useful lemmas related polynomials\<close>

theory More_Polynomials imports 
  Winding_Number_Eval.Missing_Algebraic
  Winding_Number_Eval.Missing_Transcendental
  Sturm_Tarski.PolyMisc
begin

subsection \<open>More about @{term map_poly} and @{term of_real}\<close>

lemma of_real_poly_map_pCons[simp]:"map_poly of_real (pCons a p) = pCons (of_real a) (map_poly of_real p)" 
  by (simp add: map_poly_pCons)    
    
lemma of_real_poly_map_plus[simp]: "map_poly of_real (p + q) = map_poly of_real p +  map_poly of_real q" 
  apply (rule poly_eqI)
  by (auto simp add: coeff_map_poly)  
 
lemma of_real_poly_map_smult[simp]:"map_poly of_real (smult s p) = smult (of_real s) (map_poly of_real p)" 
  apply (rule poly_eqI)
  by (auto simp add: coeff_map_poly)    

lemma of_real_poly_map_mult[simp]:"map_poly of_real (p*q) = map_poly of_real p * map_poly of_real q"
  by (induct p,intro poly_eqI,auto)
    
lemma of_real_poly_map_poly:
  "of_real (poly p x) = poly (map_poly of_real p) (of_real x)" 
  by (induct p,auto)    

lemma of_real_poly_map_power:"map_poly of_real (p^n) = (map_poly of_real p) ^ n"
  by (induct n,auto)

subsection \<open>More about @{term order}\<close>

lemma order_normalize[simp]:"order x (normalize p) = order x p"      
  by (metis dvd_normalize_iff normalize_eq_0_iff order_1 order_2 order_unique_lemma)

lemma order_gcd:
  assumes "p\<noteq>0" "q\<noteq>0"
  shows "order x (gcd p q) = min (order x p) (order x q)"
proof -
  define xx op oq where "xx=[:- x, 1:]" and "op = order x p" and "oq = order x q"
  obtain pp where pp:"p = xx ^ op * pp" "\<not> xx dvd pp"
    using order_decomp[OF \<open>p\<noteq>0\<close>,of x,folded xx_def op_def] by auto
  obtain qq where qq:"q = xx ^ oq * qq" "\<not> xx dvd qq"
    using order_decomp[OF \<open>q\<noteq>0\<close>,of x,folded xx_def oq_def] by auto
  define pq where "pq = gcd pp qq"

  have p_unfold:"p = (pq * xx ^ (min op oq)) * ((pp div pq) * xx ^ (op - min op oq))"
        and [simp]:"coprime xx (pp div pq)" and "pp\<noteq>0"
  proof -
    have "xx ^ op = xx ^ (min op oq) * xx ^ (op - min op oq)" 
      by (simp flip:power_add)
    moreover have "pp = pq * (pp div pq)" 
      unfolding pq_def by simp
    ultimately show "p = (pq * xx ^ (min op oq)) * ((pp div pq) * xx ^ (op - min op oq))"
      unfolding pq_def pp by(auto simp:algebra_simps)
    show "coprime xx (pp div pq)" 
      apply (rule prime_elem_imp_coprime[OF 
                    prime_elem_linear_poly[of 1 "-x",simplified],folded xx_def])
      using \<open>pp = pq * (pp div pq)\<close> pp(2) by auto
  qed (use pp \<open>p\<noteq>0\<close> in auto)
  have q_unfold:"q = (pq * xx ^ (min op oq)) * ((qq div pq) * xx ^ (oq - min op oq))"
         and [simp]:"coprime xx (qq div pq)" 
  proof -
    have "xx ^ oq = xx ^ (min op oq) * xx ^ (oq - min op oq)" 
      by (simp flip:power_add)
    moreover have "qq = pq * (qq div pq)" 
      unfolding pq_def by simp
    ultimately show "q = (pq * xx ^ (min op oq)) * ((qq div pq) * xx ^ (oq - min op oq))"
      unfolding pq_def qq by(auto simp:algebra_simps)
    show "coprime xx (qq div pq)" 
      apply (rule prime_elem_imp_coprime[OF 
                    prime_elem_linear_poly[of 1 "-x",simplified],folded xx_def])
      using \<open>qq = pq * (qq div pq)\<close> qq(2) by auto
  qed

  have "gcd p q=normalize (pq * xx ^ (min op oq))"
  proof -
    have "coprime (pp div pq * xx ^ (op - min op oq)) (qq div pq * xx ^ (oq - min op oq))"
    proof (cases "op>oq")
      case True
      then have "oq - min op oq = 0" by auto
      moreover have "coprime (xx ^ (op - min op oq)) (qq div pq)" by auto
      moreover have "coprime (pp div pq) (qq div pq)"
        apply (rule div_gcd_coprime[of pp qq,folded pq_def])
        using \<open>pp\<noteq>0\<close> by auto
      ultimately show ?thesis by auto
    next
      case False
      then have "op - min op oq = 0" by auto
      moreover have "coprime (pp div pq) (xx ^ (oq - min op oq))" 
        by (auto simp:coprime_commute)
      moreover have "coprime (pp div pq) (qq div pq)"
        apply (rule div_gcd_coprime[of pp qq,folded pq_def])
        using \<open>pp\<noteq>0\<close> by auto
      ultimately show ?thesis by auto
    qed 
    then show ?thesis unfolding p_unfold q_unfold
      apply (subst gcd_mult_left)
      by auto
  qed
  then have "order x (gcd p q) = order x pq + order x (xx ^ (min op oq))"
    apply simp
    apply (subst order_mult)
    using assms(1) p_unfold by auto
  also have "... = order x (xx ^ (min op oq))"
    using pp(2) qq(2) unfolding pq_def xx_def 
    by (auto simp add: order_0I poly_eq_0_iff_dvd)
  also have "... = min op oq"
    unfolding xx_def by (rule order_power_n_n)
  also have "... = min (order x p) (order x q)" unfolding op_def oq_def by simp
  finally show ?thesis .
qed

lemma pderiv_power: "pderiv (p ^ n) = smult (of_nat n) (p ^ (n-1)) * pderiv p"
  apply (cases n)
  using pderiv_power_Suc by auto

(*TODO: to replace the one (with the same name) in the library, as this version does 
  not require 'a to be a field?*)
lemma order_pderiv:
  fixes p::"'a::{idom,semiring_char_0} poly"
  assumes "p\<noteq>0" "poly p x=0"
  shows "order x p = Suc (order x (pderiv p))" using assms
proof -
  define xx op where "xx=[:- x, 1:]" and "op = order x p"
  have "op \<noteq>0" unfolding op_def using assms order_root by blast
  obtain pp where pp:"p = xx ^ op * pp" "\<not> xx dvd pp"
    using order_decomp[OF \<open>p\<noteq>0\<close>,of x,folded xx_def op_def] by auto
  have p_der:"pderiv p = smult (of_nat op) (xx^(op -1)) * pp + xx^op*pderiv pp"
    unfolding pp(1) by (auto simp:pderiv_mult pderiv_power xx_def algebra_simps pderiv_pCons)
  have "xx^(op -1) dvd (pderiv p)"
    unfolding p_der 
    by (metis One_nat_def Suc_pred assms(1) assms(2) dvd_add dvd_mult_right dvd_triv_left 
        neq0_conv op_def order_root power_Suc smult_dvd_cancel)
  moreover have "\<not> xx^op dvd (pderiv p)"
  proof 
    assume "xx ^ op dvd pderiv p"
    then have "xx ^ op dvd smult (of_nat op) (xx^(op -1) * pp)"
      unfolding p_der by (simp add: dvd_add_left_iff)
    then have "xx ^ op dvd (xx^(op -1)) * pp"
      apply (elim dvd_monic[rotated])
      using \<open>op\<noteq>0\<close> by (auto simp:lead_coeff_power xx_def)
    then have "xx ^ (op-1) * xx dvd (xx^(op -1))"
      using \<open>\<not> xx dvd pp\<close> by (simp add: \<open>op \<noteq> 0\<close> mult.commute power_eq_if)
    then have "xx dvd 1" 
      using assms(1) pp(1) by auto
    then show False unfolding xx_def by (meson assms(1) dvd_trans one_dvd order_decomp)
  qed
  ultimately have "op - 1 = order x (pderiv p)"
    using order_unique_lemma[of x "op-1" "pderiv p",folded xx_def] \<open>op\<noteq>0\<close> 
    by auto
  then show ?thesis using \<open>op\<noteq>0\<close> unfolding op_def by auto
qed

subsection \<open>More about @{term rsquarefree}\<close>

lemma rsquarefree_0[simp]: "\<not> rsquarefree 0"
  unfolding rsquarefree_def by simp

lemma rsquarefree_times:
  assumes "rsquarefree (p*q)"
  shows "rsquarefree q" using assms
proof (induct p rule:poly_root_induct_alt)
  case 0
  then show ?case by simp
next
  case (no_proots p)
  then have [simp]:"p\<noteq>0" "q\<noteq>0" "\<And>a. order a p = 0" 
    using order_0I by auto
  have "order a (p * q) = 0 \<longleftrightarrow> order a q = 0"
       "order a (p * q) = 1 \<longleftrightarrow> order a q = 1"
       for a
    subgoal by (subst order_mult) auto
    subgoal by (subst order_mult) auto
    done
  then show ?case using \<open>rsquarefree (p * q)\<close>
    unfolding rsquarefree_def by simp
next
  case (root a p)
  define pq aa where "pq = p * q" and "aa = [:- a, 1:]"
  have [simp]:"pq\<noteq>0" "aa\<noteq>0" "order a aa=1"
    subgoal using pq_def root.prems by auto
    subgoal by (simp add: aa_def)
    subgoal by (metis aa_def order_power_n_n power_one_right)
    done
  have "rsquarefree (aa * pq)"
    unfolding aa_def pq_def using root(2) by (simp add:algebra_simps)
  then have "rsquarefree pq"
    unfolding rsquarefree_def by (auto simp add:order_mult)
  from root(1)[OF this[unfolded pq_def]] show ?case .
qed

lemma rsquarefree_smult_iff:
  assumes "s\<noteq>0"
  shows "rsquarefree (smult s p) \<longleftrightarrow> rsquarefree p"
  unfolding rsquarefree_def using assms by (auto simp add:order_smult)

lemma card_proots_within_rsquarefree:
  assumes "rsquarefree p"
  shows "proots_count p s = card (proots_within p s)" using assms
proof (induct rule:poly_root_induct[of _ "\<lambda>x. x\<in>s"])
  case 0
  then have False by simp
  then show ?case by simp
next
  case (no_roots p)
  then show ?case 
    by (metis all_not_in_conv card_empty proots_count_def proots_within_iff sum.empty)
next
  case (root a p)
  have "proots_count ([:a, - 1:] * p) s = 1 + proots_count p s"
    apply (subst proots_count_times)
    subgoal using root.prems rsquarefree_def by blast
    subgoal by (metis (no_types, hide_lams) add.inverse_inverse add.inverse_neutral 
                  minus_pCons proots_count_pCons_1_iff proots_count_uminus root.hyps(1))  
    done
  also have "... = 1 + card (proots_within p s)"
  proof -
    have "rsquarefree p" using \<open>rsquarefree ([:a, - 1:] * p)\<close> 
      by (elim rsquarefree_times)
    from root(2)[OF this] show ?thesis by simp
  qed
  also have "... = card (proots_within ([:a, - 1:] * p) s)" unfolding proots_within_times 
  proof (subst card_Un_disjoint)
    have [simp]:"p\<noteq>0" using root.prems by auto
    show "finite (proots_within [:a, - 1:] s)" "finite (proots_within p s)"
      by auto
    show " 1 + card (proots_within p s) = card (proots_within [:a, - 1:] s)
               + card (proots_within p s)"
      using \<open>a \<in> s\<close>
      apply (subst proots_within_pCons_1_iff)
      by simp
    have "poly p a\<noteq>0" 
    proof (rule ccontr)
      assume "\<not> poly p a \<noteq> 0"
      then have "order a p >0" by (simp add: order_root)
      moreover have "order a [:a,-1:] = 1"
        by (metis (no_types, hide_lams) add.inverse_inverse add.inverse_neutral minus_pCons 
            order_power_n_n order_uminus power_one_right)
      ultimately have "order a  ([:a, - 1:] * p) > 1"
        apply (subst order_mult)
        subgoal using root.prems by auto
        subgoal by auto
        done
      then show False using \<open>rsquarefree ([:a, - 1:] * p)\<close> 
        unfolding rsquarefree_def using gr_implies_not0 less_not_refl2 by blast
    qed
    then show " proots_within [:a, - 1:] s \<inter> proots_within p s = {}"
      using proots_within_pCons_1_iff(2) by auto
  qed
  finally show ?case .
qed

lemma rsquarefree_gcd_pderiv:
  fixes p::"'a::{factorial_ring_gcd,semiring_char_0} poly"
  assumes "p\<noteq>0"
  shows "rsquarefree (p div (gcd p (pderiv p)))"
proof (cases "pderiv p = 0")
  case True
  have "poly (unit_factor p) x \<noteq>0" for x 
    using unit_factor_is_unit[OF \<open>p\<noteq>0\<close>] 
    by (meson assms dvd_trans order_decomp poly_eq_0_iff_dvd unit_factor_dvd)
  then have "order x (unit_factor p) = 0" for x
    using order_0I by blast
  then show ?thesis using True \<open>p\<noteq>0\<close> unfolding rsquarefree_def by simp
next
  case False
  define q where "q = p div (gcd p (pderiv p))"
  have "q\<noteq>0" unfolding q_def by (simp add: assms dvd_div_eq_0_iff)

  have order_pq:"order x p = order x q + min (order x p) (order x (pderiv p))"
    for x
  proof -
    have *:"p = q * gcd p (pderiv p)"
      unfolding q_def by simp
    show ?thesis
      apply (subst *)
      using \<open>q\<noteq>0\<close> \<open>p\<noteq>0\<close> \<open>pderiv p\<noteq>0\<close> by (simp add:order_mult order_gcd)
  qed
  have "order x q = 0 \<or> order x q=1" for x
  proof (cases "poly p x=0")
    case True
    from order_pderiv[OF \<open>p\<noteq>0\<close> this] 
    have "order x p = order x (pderiv p) + 1" by simp
    then show ?thesis using order_pq[of x] by auto
  next
    case False
    then have "order x p = 0" by (simp add: order_0I)
    then have "order x q = 0" using order_pq[of x] by simp
    then show ?thesis by simp
  qed 
  then show ?thesis using \<open>q\<noteq>0\<close> unfolding rsquarefree_def q_def
    by auto
qed

lemma poly_gcd_pderiv_iff:
  fixes p::"'a::{semiring_char_0,factorial_ring_gcd} poly"
  shows "poly (p div (gcd p (pderiv p))) x =0 \<longleftrightarrow> poly p x=0"
proof (cases "pderiv p=0")
  case True
  then obtain a where "p=[:a:]" using pderiv_iszero by auto
  then show ?thesis by (auto simp add: unit_factor_poly_def)
next
  case False
  then have "p\<noteq>0" using pderiv_0 by blast
  define q where "q = p div (gcd p (pderiv p))"
  have "q\<noteq>0" unfolding q_def by (simp add: \<open>p\<noteq>0\<close> dvd_div_eq_0_iff)

  have order_pq:"order x p = order x q + min (order x p) (order x (pderiv p))" for x
  proof -
    have *:"p = q * gcd p (pderiv p)"
      unfolding q_def by simp
    show ?thesis
      apply (subst *)
      using \<open>q\<noteq>0\<close> \<open>p\<noteq>0\<close> \<open>pderiv p\<noteq>0\<close> by (simp add:order_mult order_gcd)
  qed

  have "order x q =0 \<longleftrightarrow> order x p = 0" 
  proof (cases "poly p x=0")
    case True
    from order_pderiv[OF \<open>p\<noteq>0\<close> this] 
    have "order x p = order x (pderiv p) + 1" by simp
    then show ?thesis using order_pq[of x] by auto
  next
    case False
    then have "order x p = 0" by (simp add: order_0I)
    then have "order x q = 0" using order_pq[of x] by simp
    then show ?thesis using \<open>order x p = 0\<close> by simp
  qed 
  then show ?thesis 
    apply (fold q_def)
    unfolding order_root using \<open>p\<noteq>0\<close> \<open>q\<noteq>0\<close> by auto
qed

subsection \<open>Composition of a polynomial and a rational function\<close>

(*composition of a polynomial and a rational function. Maybe a more general version in the future?*)
definition fcompose::"'a ::field poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "fcompose p q r = fst (fold_coeffs (\<lambda>a (c,d). (d*[:a:] + q * c,r*d)) p (0,1))"

lemma fcompose_0 [simp]: "fcompose 0 q r = 0"
  by (simp add: fcompose_def)

lemma fcompose_const[simp]:"fcompose [:a:] q r = [:a:]"
  unfolding fcompose_def by (cases "a=0") auto

lemma fcompose_pCons: 
  "fcompose (pCons a p) q1 q2 = smult a (q2^(degree (pCons a p))) + q1 * fcompose p q1 q2"
proof (cases "p=0")
  case False
  define ff where "ff=(\<lambda>a (c, d). (d * [:a:] + q1 * c, q2 * d))"
  define fc where "fc=fold_coeffs ff p (0, 1)"
  have snd_ff:"snd fc = (if p=0 then 1 else q2^(degree p + 1))" unfolding fc_def
    apply (induct p)
    subgoal by simp
    subgoal for a p
      by (auto simp add:ff_def split:if_splits prod.splits)
    done

  have "fcompose (pCons a p) q1 q2 = fst (fold_coeffs ff (pCons a p) (0, 1))"
    unfolding fcompose_def ff_def by simp
  also have "... = fst (ff a fc)"
    using False unfolding fc_def by auto
  also have "... = snd fc * [:a:] + q1 * fst fc"
    unfolding ff_def by (auto split:prod.splits)
  also have "... = smult a (q2^(degree (pCons a p))) + q1 * fst fc"
    using snd_ff False by auto
  also have "... = smult a (q2^(degree (pCons a p))) + q1 * fcompose p q1 q2"
    unfolding fc_def ff_def fcompose_def by simp
  finally show ?thesis .
qed simp

lemma fcompose_uminus:
  "fcompose (-p) q r = - fcompose p q r"
  by (induct p) (auto simp:fcompose_pCons)

lemma fcompose_add_less:
  assumes "degree p1 > degree p2"
  shows "fcompose (p1+p2) q1 q2 
            = fcompose p1 q1 q2 + q2^(degree p1-degree p2) * fcompose p2 q1 q2"
  using assms
proof (induction p1 p2 rule: poly_induct2)
  case (pCons a1 p1 a2 p2)
  have ?case when "p2=0"
    using that by (simp add:fcompose_pCons smult_add_left)
  moreover have ?case when "p2\<noteq>0" "\<not> degree p2 < degree p1"
    using that pCons(2) by auto
  moreover have ?case when "p2\<noteq>0" "degree p2< degree p1"
  proof -
    define d1 d2 where "d1=degree (pCons a1 p1)" and "d2=degree (pCons a2 p2) "
    define fp1 fp2 where "fp1= fcompose p1 q1 q2" and "fp2=fcompose p2 q1 q2"

    have "fcompose (pCons a1 p1 + pCons a2 p2) q1 q2 
            = fcompose (pCons (a1+a2) (p1+p2)) q1 q2"
      by simp
    also have "... = smult (a1 + a2) (q2 ^ d1) + q1 * fcompose (p1 + p2) q1 q2"
    proof -
      have "degree (pCons (a1 + a2) (p1 + p2)) = d1"
        unfolding d1_def using that degree_add_eq_left by fastforce
      then show ?thesis unfolding fcompose_pCons by simp
    qed
    also have "... = smult (a1 + a2) (q2 ^ d1) + q1 * (fp1 + q2 ^ (d1 - d2) * fp2)"
    proof -
      have "degree p1 - degree p2 = d1 - d2"
        unfolding d1_def d2_def using that by simp
      then show ?thesis 
        unfolding pCons(1)[OF that(2),folded fp1_def fp2_def] by simp
    qed
    also have "... = fcompose (pCons a1 p1) q1 q2 + q2 ^ (d1 - d2) 
                        * fcompose (pCons a2 p2) q1 q2"
    proof -
      have "d1 > d2" unfolding d1_def d2_def using that by auto
      then show ?thesis
        unfolding fcompose_pCons
        apply (fold d1_def d2_def fp1_def fp2_def)
        by (simp add:algebra_simps smult_add_left power_add[symmetric])
    qed
    finally show ?thesis unfolding d1_def d2_def .
  qed
  ultimately show ?case by blast
qed simp

lemma fcompose_add_eq:
  assumes "degree p1 = degree p2"
  shows "q2^(degree p1 - degree (p1+p2)) * fcompose (p1+p2) q1 q2 
            = fcompose p1 q1 q2 + fcompose p2 q1 q2"
  using assms
proof (induction p1 p2 rule: poly_induct2)
  case (pCons a1 p1 a2 p2)
  have ?case when "p1+p2=0"
  proof -
    have "p2=-p1" using that by algebra
    then show ?thesis by (simp add:fcompose_pCons fcompose_uminus smult_add_left)
  qed
  moreover have ?case when "p1=0"
  proof -
    have "p2=0"
      using pCons(2) that by (auto split:if_splits)
    then show ?thesis using that by simp
  qed
  moreover have ?case when "p1\<noteq>0" "p1+p2\<noteq>0"
  proof -
    define d1 d2 dp where "d1=degree (pCons a1 p1)" and "d2=degree (pCons a2 p2)"
                            and "dp = degree p1 - degree (p1+p2)"
    define fp1 fp2 where "fp1= fcompose p1 q1 q2" and "fp2=fcompose p2 q1 q2"

    have "q2 ^ (degree (pCons a1 p1) - degree (pCons a1 p1 + pCons a2 p2)) *
             fcompose (pCons a1 p1 + pCons a2 p2) q1 q2 
                = q2 ^ dp * fcompose (pCons (a1+a2) (p1 +p2)) q1 q2"
      unfolding dp_def using that by auto
    also have "... = smult (a1 + a2) (q2 ^ d1) + q1 * (q2 ^ dp * fcompose (p1 + p2) q1 q2)"
    proof -
      have "degree p1 \<ge> degree (p1 + p2)" 
        by (metis degree_add_le degree_pCons_eq_if not_less_eq_eq order_refl pCons.prems zero_le)
      then show ?thesis 
        unfolding fcompose_pCons dp_def d1_def using that
        by (simp add:algebra_simps power_add[symmetric])
    qed
    also have "... =  smult (a1 + a2) (q2 ^ d1) + q1 * (fp1 + fp2)"
      apply (subst pCons(1)[folded dp_def fp1_def fp2_def])
      subgoal by (metis degree_pCons_eq_if diff_Suc_Suc diff_zero not_less_eq_eq pCons.prems zero_le)
      subgoal by simp
      done
    also have "... = fcompose (pCons a1 p1) q1 q2 + fcompose (pCons a2 p2) q1 q2"
    proof -
      have *:"d1 = degree (pCons a2 p2)"
        unfolding d1_def using pCons(2) by simp
      show ?thesis 
        unfolding fcompose_pCons
        apply (fold d1_def fp1_def fp2_def *)
        by (simp add:smult_add_left algebra_simps)
    qed
    finally show ?thesis .
  qed
  ultimately show ?case by blast
qed simp

lemma fcompose_add_const:
  "fcompose ([:a:] + p) q1 q2 = smult a (q2 ^ degree p) + fcompose p q1 q2"
  apply (cases p)
  by (auto simp add:fcompose_pCons smult_add_left)

lemma fcompose_smult: "fcompose (smult a p) q1 q2 = smult a (fcompose p q1 q2)"
  by (induct p) (simp_all add:fcompose_pCons smult_add_right)

lemma fcompose_mult: "fcompose (p1*p2) q1 q2 = fcompose p1 q1 q2 * fcompose p2 q1 q2"
proof (induct p1)
  case 0
  then show ?case by simp
next
  case (pCons a p1)
  have ?case when "p1=0 \<or> p2=0" 
    using that by (auto simp add:fcompose_smult)
  moreover have ?case when "p1\<noteq>0" "p2\<noteq>0" "a=0"
    using that by (simp add:fcompose_pCons pCons)
  moreover have ?case when "p1\<noteq>0" "p2\<noteq>0" "a\<noteq>0"
  proof -
    have "fcompose (pCons a p1 * p2) q1 q2 
            = fcompose (pCons 0 (p1 * p2) + smult a p2) q1 q2"
      by (simp add:algebra_simps)
    also have "... =  fcompose (pCons 0 (p1 * p2)) q1 q2 
                        + q2 ^ (degree p1 +1) * fcompose (smult a p2) q1 q2"
    proof -
      have "degree (pCons 0 (p1 * p2)) > degree (smult a p2)"
        using that by (simp add: degree_mult_eq)
      from fcompose_add_less[OF this,of q1 q2] that 
      show ?thesis by (simp add:degree_mult_eq)
    qed
    also have "... = fcompose (pCons a p1) q1 q2 * fcompose p2 q1 q2"
      using that by (simp add:fcompose_pCons fcompose_smult pCons algebra_simps)
    finally show ?thesis .
  qed
  ultimately show ?case by blast
qed

lemma fcompose_poly:
  assumes "poly q2 x\<noteq>0"
  shows "poly p (poly q1 x/poly q2 x) = poly (fcompose p q1 q2) x / poly (q2^(degree p)) x"
  apply (induct p)
  using assms by (simp_all add:fcompose_pCons field_simps)

lemma poly_fcompose:
   assumes "poly q2 x\<noteq>0"
   shows "poly (fcompose p q1 q2) x = poly p (poly q1 x/poly q2 x) * (poly q2 x)^(degree p)"
  using fcompose_poly[OF assms] assms by (auto simp add:field_simps)
lemma poly_fcompose_0_denominator:
  assumes "poly q2 x=0"
  shows "poly (fcompose p q1 q2) x = poly q1 x ^ degree p * lead_coeff p"
  apply (induct p)
  using assms by (auto simp add:fcompose_pCons)

lemma fcompose_0_denominator:"fcompose p q1 0 = smult (lead_coeff p) (q1^degree p)"
  apply (induct p)
  by (auto simp:fcompose_pCons)

lemma fcompose_nzero:
  fixes p::"'a::field poly"
  assumes "p\<noteq>0" and "q2\<noteq>0" and nconst:"\<forall>c. q1 \<noteq> smult c q2"
      and infi:"infinite (UNIV::'a set)"
  shows "fcompose p q1 q2 \<noteq> 0" using \<open>p\<noteq>0\<close>
proof (induct p rule:poly_root_induct_alt)
  case 0
  then show ?case by simp
next
  case (no_proots p)
  have False when "fcompose p q1 q2 = 0"
  proof -
    obtain x where "poly q2 x\<noteq>0" 
    proof -
      have "finite (proots q2)" using \<open>q2\<noteq>0\<close> by auto
      then have "\<exists>x. poly q2 x\<noteq>0" 
        by (meson UNIV_I ex_new_if_finite infi proots_withinI)
      then show ?thesis using that by auto
    qed
    define y where "y = poly q1 x / poly q2 x"
    have "poly p y = 0"
      using \<open>fcompose p q1 q2 = 0\<close> fcompose_poly[OF \<open>poly q2 x\<noteq>0\<close>,of p q1,folded y_def] 
      by simp
    then show False using no_proots(1) by auto
  qed
  then show ?case by auto
next
  case (root a p)
  have "fcompose [:- a, 1:] q1 q2 \<noteq> 0" 
    unfolding fcompose_def using nconst[rule_format,of a]
    by simp
  moreover have "fcompose p q1 q2 \<noteq> 0" 
    using root by fastforce
  ultimately show ?case unfolding fcompose_mult by auto
qed

lemma poly_circlepath_tan_eq:
  fixes z0::complex and r::real and p::"complex poly"
  defines "q1\<equiv> fcompose p [:(z0+r)*\<i>,z0-r:] [:\<i>,1:]" and "q2 \<equiv> [:\<i>,1:] ^ degree p"
  assumes "0\<le>t" "t\<le>1" "t\<noteq>1/2"
  shows "poly p (circlepath z0 r t) = poly q1 (tan (pi*t)) / poly q2 (tan (pi*t))" 
    (is "?L = ?R")
proof -
  have "?L = poly p (z0+ r*exp (2 * of_real pi * \<i>  * t))" 
    unfolding circlepath by simp
  also have "... = ?R"
  proof -
    define f where "f = (poly p \<circ> (\<lambda>x::real. z0 + r * exp (\<i> * x)))"
    have f_eq:"f t = ((\<lambda>x::real. poly q1 x / poly q2 x) o  (\<lambda>x. tan (x/2)) ) t" 
      when "cos (t / 2) \<noteq> 0" for t
    proof -
      have "f t = poly p (z0 + r * (cos t + \<i> * sin t)) " 
        unfolding f_def exp_Euler  by (auto simp add:cos_of_real sin_of_real)
      also have "... = poly p ((\<lambda>x. ((z0-r)*x+(z0+r)*\<i>) / (\<i>+x)) (tan (t/2)))"
      proof -
        define tt where "tt=complex_of_real (tan (t / 2))"
        define rr where "rr = complex_of_real r"
        have "cos t = (1-tt*tt) / (1 + tt * tt)" 
             "sin t = 2*tt  / (1 + tt * tt)"
          unfolding sin_tan_half[of "t/2",simplified] cos_tan_half[of "t/2",OF that, simplified] tt_def
          by (auto simp add:power2_eq_square)
        moreover have "1 + tt * tt \<noteq> 0" unfolding tt_def 
          apply (fold of_real_mult)
          by (metis (no_types, hide_lams) mult_numeral_1 numeral_One of_real_add of_real_eq_0_iff
              of_real_numeral sum_squares_eq_zero_iff zero_neq_one)
        ultimately have "z0 +  r * ( (cos t) + \<i> * (sin t))
            =(z0*(1+tt*tt)+rr*(1-tt*tt)+\<i>*rr*2*tt ) / (1 + tt * tt) "
          apply (fold rr_def,simp add:add_divide_distrib)
          by (simp add:algebra_simps)
        also have "... = ((z0-rr)*tt+z0*\<i>+rr*\<i>) / (tt + \<i>)"
        proof -
          have "tt + \<i> \<noteq> 0" 
            using \<open>1 + tt * tt \<noteq> 0\<close> 
            by (metis i_squared neg_eq_iff_add_eq_0 square_eq_iff)
          then show ?thesis 
            using \<open>1 + tt * tt \<noteq> 0\<close> by (auto simp add:divide_simps algebra_simps)
        qed
        finally have "z0 +  r * ( (cos t) + \<i> * (sin t)) = ((z0-rr)*tt+z0*\<i>+rr*\<i>) / (tt + \<i>)" .
        then show ?thesis unfolding tt_def rr_def 
          by (auto simp add:algebra_simps power2_eq_square)
      qed
      also have "... = (poly p o ((\<lambda>x. ((z0-r)*x+(z0+r)*\<i>) / (\<i>+x)) o (\<lambda>x. tan (x/2)) )) t"
        unfolding comp_def by (auto simp:tan_of_real)
      also have "... = ((\<lambda>x::real. poly q1 x / poly q2 x) o  (\<lambda>x. tan (x/2)) ) t"
        unfolding q2_def q1_def
        apply (subst fcompose_poly[symmetric])
        subgoal for x
          apply simp
          by (metis Re_complex_of_real add_cancel_right_left complex_i_not_zero imaginary_unit.sel(1) plus_complex.sel(1) rcis_zero_arg rcis_zero_mod)
        subgoal by (auto simp:tan_of_real algebra_simps)
        done
      finally show ?thesis .
    qed
    
    have "cos (pi * t) \<noteq>0" unfolding cos_zero_iff_int2
    proof 
      assume "\<exists>i. pi * t = real_of_int i * pi + pi / 2"
      then obtain i where "pi * t = real_of_int i * pi + pi / 2" by auto
      then have "pi * t=pi * (real_of_int i + 1 / 2)" by (simp add:algebra_simps)
      then have "t=real_of_int i + 1 / 2" by auto
      then show False using \<open>0\<le>t\<close> \<open>t\<le>1\<close> \<open>t\<noteq>1/2\<close> by auto
    qed
    from f_eq[of "2*pi*t",simplified,OF this] 
    show "?thesis"
      unfolding f_def comp_def by (auto simp add:algebra_simps)
  qed
  finally show ?thesis .
qed

end