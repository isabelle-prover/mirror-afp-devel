(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)
section \<open>Extra lemmas related to polynomials\<close>

theory CC_Polynomials_Extra imports 
  Winding_Number_Eval.Missing_Algebraic
  Winding_Number_Eval.Missing_Transcendental
  Sturm_Tarski.PolyMisc
  Budan_Fourier.BF_Misc
  "Polynomial_Interpolation.Ring_Hom_Poly" (*Move to the standard distribution?*)
begin

subsection \<open>Misc\<close>

lemma poly_linepath_comp': 
  fixes a::"'a::{real_normed_vector,comm_semiring_0,real_algebra_1}"
  shows "poly p (linepath a b t) = poly (p \<circ>\<^sub>p [:a, b-a:]) (of_real t)"
  by (auto simp add:poly_pcompose linepath_def scaleR_conv_of_real algebra_simps)

lemma path_poly_comp[intro]:
  fixes p::"'a::real_normed_field poly"
  shows "path g \<Longrightarrow> path (poly p o g)"
  apply (elim path_continuous_image)
  by (auto intro:continuous_intros)

lemma cindex_poly_noroot:
  assumes "\<forall>x. a<x \<and> x<b \<longrightarrow> poly p x\<noteq>0"
  shows "cindex_poly a b q p = 0" 
  unfolding cindex_poly_def
  by (metis (lifting) assms mem_Collect_eq sum.neutral)

subsection \<open>More polynomial homomorphism interpretations\<close>

interpretation of_real_poly_hom:map_poly_inj_idom_hom of_real ..

interpretation Re_poly_hom:map_poly_comm_monoid_add_hom Re 
  by unfold_locales simp_all

interpretation Im_poly_hom:map_poly_comm_monoid_add_hom Im
  by unfold_locales simp_all

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
        using \<open>pp \<noteq> 0\<close> div_gcd_coprime pq_def by blast
      ultimately show ?thesis by auto
    next
      case False
      then have "op - min op oq = 0" by auto
      moreover have "coprime (pp div pq) (xx ^ (oq - min op oq))" 
        by (auto simp:coprime_commute)
      moreover have "coprime (pp div pq) (qq div pq)"
        using \<open>pp \<noteq> 0\<close> div_gcd_coprime pq_def by blast
      ultimately show ?thesis by auto
    qed 
    then show ?thesis unfolding p_unfold q_unfold
      by (simp add: gcd_mult_left)
  qed
  then have "order x (gcd p q) = order x pq + order x (xx ^ (min op oq))"
    by (metis assms(1) mult_zero_left order_mult order_normalize p_unfold)
  also have "\<dots> = order x (xx ^ (min op oq))"
    using pp(2) qq(2) unfolding pq_def xx_def 
    by (auto simp add: order_0I poly_eq_0_iff_dvd)
  also have "\<dots> = min op oq"
    unfolding xx_def by (rule order_power_n_n)
  also have "\<dots> = min (order x p) (order x q)" unfolding op_def oq_def by simp
  finally show ?thesis .
qed

lemma pderiv_power: "pderiv (p ^ n) = smult (of_nat n) (p ^ (n-1)) * pderiv p"
  apply (cases n)
  using pderiv_power_Suc by auto

(*TODO: to replace the one (with the same name) in the library, as this version does 
  not require 'a to be a field?*)
thm order_pderiv
      lemma order_pderiv:
        fixes p::"'a::{idom,semiring_char_0} poly"
        assumes "p\<noteq>0" "poly p x=0"
        shows "order x p = Suc (order x (pderiv p))" using assms
      proof -
        define xx op where "xx=[:- x, 1:]" and "op = order x p"
        have "op \<noteq> 0" unfolding op_def using assms order_root by blast
        obtain pp where pp:"p = xx ^ op * pp" "\<not> xx dvd pp"
          using order_decomp[OF \<open>p\<noteq>0\<close>,of x,folded xx_def op_def] by auto
        have p_der:"pderiv p = smult (of_nat op) (xx^(op -1)) * pp + xx^op*pderiv pp"
          unfolding pp(1) by (auto simp:pderiv_mult pderiv_power xx_def algebra_simps pderiv_pCons)
        have "xx^(op -1) dvd (pderiv p)"
          unfolding p_der
          by (metis \<open>op \<noteq> 0\<close> dvd_add_left_iff dvd_mult2 dvd_refl dvd_smult dvd_triv_right
              power_eq_if) 
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
  shows "rsquarefree q"
  using assms by (metis order_mult rsquarefree_def rsquarefree_def' add_leE mult_zero_right)

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
    by (metis all_not_in_conv card.empty proots_count_def proots_within_iff sum.empty)
next
  case (root a p)
  have "proots_count ([:a, - 1:] * p) s = 1 + proots_count p s"
  proof (subst proots_count_times)
    show "[:a, - 1:] * p \<noteq> 0"
      using root.prems rsquarefree_def by blast
    show "proots_count [:a, - 1:] s + proots_count p s = 1 + proots_count p s"
      by (metis (no_types, opaque_lifting) add.inverse_inverse add.inverse_neutral minus_pCons
          proots_count_pCons_1_iff proots_count_uminus root.hyps(1))
  qed
  also have "\<dots> = 1 + card (proots_within p s)"
    by (metis root.hyps(2) root.prems rsquarefree_times)
  also have "\<dots> = card (proots_within ([:a, - 1:] * p) s)" unfolding proots_within_times 
  proof (subst card_Un_disjoint)
    have [simp]:"p\<noteq>0" using root.prems by auto
    show "finite (proots_within [:a, - 1:] s)" "finite (proots_within p s)"
      by auto
    show " 1 + card (proots_within p s) = card (proots_within [:a, - 1:] s)
               + card (proots_within p s)"
      using \<open>a \<in> s\<close>
      by (simp add: proots_within_pCons_1_iff(2))
    have "poly p a\<noteq>0" 
    proof (rule ccontr)
      assume "\<not> poly p a \<noteq> 0"
      then have "order a p >0" by (simp add: order_root)
      moreover have "order a [:a,-1:] = 1"
        by (metis add.inverse_inverse add.inverse_neutral minus_pCons order_linear
            order_uminus)
      ultimately have "order a  ([:a, - 1:] * p) > 1"
        by (metis root.prems order_mult add_cancel_right_right linorder_neqE_nat not_add_less1 rsquarefree_0)
      then show False using \<open>rsquarefree ([:a, - 1:] * p)\<close> 
        unfolding rsquarefree_def using gr_implies_not0 less_not_refl2 by blast
    qed
    then show " proots_within [:a, - 1:] s \<inter> proots_within p s = {}"
      using proots_within_pCons_1_iff(2) by auto
  qed
  finally show ?case .
qed

lemma rsquarefree_gcd_pderiv:
  fixes p::"'a::{factorial_ring_gcd,semiring_gcd_mult_normalize,semiring_char_0} poly"
  assumes "p\<noteq>0"
  shows "rsquarefree (p div (gcd p (pderiv p)))"
proof (cases "pderiv p = 0")
  case True
  have "poly (unit_factor p) x \<noteq> 0" for x 
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
    have "p = q * gcd p (pderiv p)"
      unfolding q_def by simp
    then show ?thesis
      by (metis CC_Polynomials_Extra.order_gcd False assms order_mult)
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
  fixes p::"'a::{semiring_char_0,factorial_ring_gcd,semiring_gcd_mult_normalize} poly"
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
      by (metis "*" CC_Polynomials_Extra.order_gcd False \<open>p \<noteq> 0\<close> order_mult)
  qed
  have "order x q = 0 \<longleftrightarrow> order x p = 0"
    by (metis order_pderiv \<open>p \<noteq> 0\<close> add.commute add_0 lessI min_0L
        min_less_iff_disj order_0I order_pq less_irrefl) 
  then show ?thesis
    using \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close> order_root q_def by blast 
qed

subsection \<open>Composition of a polynomial and a circular path\<close>

lemma poly_circlepath_tan_eq:
  fixes z0::complex and r::real and p::"complex poly"
  defines "q1\<equiv> fcompose p [:(z0+r)*\<i>,z0-r:] [:\<i>,1:]" and "q2 \<equiv> [:\<i>,1:] ^ degree p"
  assumes "0\<le>t" "t\<le>1" "t\<noteq>1/2"
  shows "poly p (circlepath z0 r t) = poly q1 (tan (pi*t)) / poly q2 (tan (pi*t))" 
    (is "?L = ?R")
proof -
  have "?L = poly p (z0+ r*exp (2 * of_real pi * \<i>  * t))" 
    unfolding circlepath by simp
  also have "\<dots> = ?R"
  proof -
    define f where "f = (poly p \<circ> (\<lambda>x::real. z0 + r * exp (\<i> * x)))"
    have f_eq:"f t = ((\<lambda>x::real. poly q1 x / poly q2 x) o  (\<lambda>x. tan (x/2)) ) t" 
      when "cos (t / 2) \<noteq> 0" for t
    proof -
      have "f t = poly p (z0 + r * (cos t + \<i> * sin t)) " 
        unfolding f_def exp_Euler  by (auto simp add:cos_of_real sin_of_real)
      also have "\<dots> = poly p ((\<lambda>x. ((z0-r)*x+(z0+r)*\<i>) / (\<i>+x)) (tan (t/2)))"
      proof -
        define tt where "tt=complex_of_real (tan (t / 2))"
        define rr where "rr = complex_of_real r"
        have \<section>: "cos t = (1-tt*tt) / (1 + tt * tt)" 
                "sin t = 2*tt  / (1 + tt * tt)"
          unfolding sin_tan_half[of "t/2",simplified] cos_tan_half[of "t/2",OF that, simplified] tt_def
          by (auto simp add:power2_eq_square)
        then have "1 + tt * tt \<noteq> 0"
          by (metis cmod_unit_one division_ring_divide_zero mult_2 mult_zero_right norm_eq_zero
              zero_neq_one)
        with \<section> have "z0 +  r * ( (cos t) + \<i> * (sin t))
            =(z0*(1+tt*tt)+rr*(1-tt*tt)+\<i>*rr*2*tt ) / (1 + tt * tt) "
          apply (simp flip: rr_def add: add_divide_distrib)
          by (simp add:algebra_simps)
        also have "\<dots> = ((z0-rr)*tt+z0*\<i>+rr*\<i>) / (tt + \<i>)"
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
      also have "\<dots> = (poly p o ((\<lambda>x. ((z0-r)*x+(z0+r)*\<i>) / (\<i>+x)) o (\<lambda>x. tan (x/2)) )) t"
        unfolding comp_def by (auto simp:tan_of_real)
      also have "\<dots> = ((\<lambda>x::real. poly q1 x / poly q2 x) o  (\<lambda>x. tan (x/2)) ) t"
        unfolding q2_def q1_def
        apply (subst fcompose_poly[symmetric])
          using Re_poly_hom.base.hom_add_eq_zero apply fastforce
        by (auto simp:tan_of_real algebra_simps)
      finally show ?thesis .
    qed
    
    have "cos (pi * t) \<noteq> 0" unfolding cos_zero_iff_int2
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

subsection \<open>Combining two real polynomials into a complex one\<close>  

definition cpoly_of:: "real poly \<Rightarrow> real poly \<Rightarrow> complex poly" where
  "cpoly_of pR pI = map_poly of_real pR + smult \<i> (map_poly of_real pI)"

lemma cpoly_of_eq_0_iff[iff]:
  "cpoly_of pR pI = 0 \<longleftrightarrow> pR = 0 \<and> pI = 0"
proof -
  have "pR = 0 \<and> pI = 0" when "cpoly_of pR pI = 0"
  proof -
    have "complex_of_real (coeff pR n) + \<i> * complex_of_real (coeff pI n) = 0" for n
      using that unfolding poly_eq_iff cpoly_of_def by (auto simp:coeff_map_poly)
    then have "coeff pR n = 0 \<and> coeff pI n = 0" for n
      using Complex_eq Complex_eq_0 by force
    then show ?thesis unfolding poly_eq_iff by auto 
  qed
  then show ?thesis by (auto simp:cpoly_of_def)
qed

lemma cpoly_of_decompose:
    "p = cpoly_of (map_poly Re p) (map_poly Im p)"
  unfolding cpoly_of_def 
  by (induct p) (auto simp add: map_poly_map_poly complex_eq)

lemma cpoly_of_dist_right:
    "cpoly_of (pR*g) (pI*g) = cpoly_of pR pI * (map_poly of_real g)"
  unfolding cpoly_of_def by (simp add: distrib_right)
  
lemma poly_cpoly_of_real:
    "poly (cpoly_of pR pI) (of_real x) = Complex (poly pR x) (poly pI x)"
  unfolding cpoly_of_def by (simp add: Complex_eq)
    
lemma poly_cpoly_of_real_iff:
  shows "poly (cpoly_of pR pI) (of_real t) =0 \<longleftrightarrow> poly pR t = 0 \<and> poly pI t=0 "  
  unfolding  poly_cpoly_of_real using Complex_eq_0 by blast  

lemma order_cpoly_gcd_eq:
  assumes "pR\<noteq>0 \<or> pI\<noteq>0"
  shows "order t (cpoly_of pR pI) = order t (gcd pR pI)"
proof -
  define g where "g = gcd pR pI"
  have [simp]:"g\<noteq>0" unfolding g_def using assms by auto
  obtain pr pi where pri: "pR = pr * g" "pI = pi * g" "coprime pr pi"
    unfolding g_def using assms(1) gcd_coprime_exists \<open>g \<noteq> 0\<close> g_def by blast
  then have "pr \<noteq> 0 \<or> pi \<noteq> 0" using assms mult_zero_left by blast

  have "order t (cpoly_of pR pI) = order t (cpoly_of pr pi * (map_poly of_real g))"
    unfolding pri cpoly_of_dist_right by simp
  also have "\<dots> = order t (cpoly_of pr pi) + order t g"
    using \<open>pr \<noteq> 0 \<or> pi \<noteq> 0\<close> \<open>g \<noteq> 0\<close>
    by (simp add: map_poly_order_of_real order_mult)
  also have "\<dots> = order t g"
  proof -
    have "poly (cpoly_of pr pi) t \<noteq> 0" unfolding poly_cpoly_of_real_iff
      using \<open>coprime pr pi\<close> coprime_poly_0 by blast
    then have "order t (cpoly_of pr pi) = 0" by (simp add: order_0I)
    then show ?thesis by auto
  qed
  finally show ?thesis unfolding g_def .
qed

lemma cpoly_of_times:
  shows "cpoly_of pR pI * cpoly_of qR qI = cpoly_of (pR * qR - pI * qI) (pI*qR+pR*qI)"
proof -
  define PR PI where "PR = map_poly complex_of_real pR"
                 and "PI = map_poly complex_of_real pI"
  define QR QI where "QR = map_poly complex_of_real qR"
                 and "QI = map_poly complex_of_real qI"
  show ?thesis 
    unfolding cpoly_of_def  
    by (simp add:algebra_simps of_real_poly_hom.hom_minus smult_add_right 
          flip: PR_def PI_def QR_def QI_def)
qed

lemma map_poly_Re_cpoly[simp]:
  "map_poly Re (cpoly_of pR pI) = pR"
  unfolding cpoly_of_def smult_map_poly
  by (simp add:map_poly_map_poly Re_poly_hom.hom_add comp_def coeff_map_poly poly_eq_iff)

lemma map_poly_Im_cpoly[simp]:
  "map_poly Im (cpoly_of pR pI) = pI"
  unfolding cpoly_of_def smult_map_poly
  by (simp add:map_poly_map_poly Im_poly_hom.hom_add comp_def coeff_map_poly poly_eq_iff)

end