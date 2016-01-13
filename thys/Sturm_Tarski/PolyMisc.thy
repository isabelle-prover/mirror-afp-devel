(*
    Author:     Wenda Li <wl302@cam.ac.uk>
*)

theory PolyMisc imports
  Complex_Main 
  "~~/src/HOL/Library/Poly_Deriv"
begin

section{*Misc*}

lemma smult_cancel:
  fixes p::"'a::idom poly"
  assumes "c\<noteq>0" and smult: "smult c p = smult c q" 
  shows "p=q" 
proof -
  have "smult c (p-q)=0" using smult by (metis diff_self smult_diff_right)
  thus ?thesis using `c\<noteq>0` by auto
qed

lemma dvd_monic:
  fixes p q:: "'a :: idom poly" 
  assumes monic:"lead_coeff p=1" and "p dvd (smult c q)" and "c\<noteq>0"
  shows "p dvd q" using assms
proof (cases "q=0 \<or> degree p=0")
  case True
  thus ?thesis using assms unfolding lead_coeff_def 
    by (metis coeff_1 dvd_0_right le_0_eq le_degree one_dvd poly_eqI)
next
  case False
  hence "q\<noteq>0" and "degree p\<noteq>0" by auto
  obtain k where k:"smult c q = p*k" using assms by (blast elim: dvdE)  
  hence "k\<noteq>0" by (metis False assms(3) mult_zero_right smult_eq_0_iff)
  hence deg_eq:"degree q=degree p + degree k"
    using degree_mult_eq monic k unfolding lead_coeff_def
    by (metis assms(3) degree_smult_eq leading_coeff_0_iff zero_neq_one)
  have c_dvd:"\<forall>n\<le>degree k. c dvd coeff k (degree k - n)" 
    proof (rule,rule)
      fix n assume "n \<le> degree k "
      thus "c dvd coeff k (degree k - n)"
        proof (induct n rule:nat_less_induct) 
          case (1 n) 
          def T\<equiv>"(\<lambda>i. coeff p i * coeff k (degree p+degree k - n - i))"
          have "c * coeff q (degree q - n) = (\<Sum>i\<le>degree q - n. coeff p i * coeff k (degree q - n - i))"
            using coeff_mult[of p k "degree q - n"] k coeff_smult[of c q "degree q -n"] by auto
          also have "...=(\<Sum>i\<le>degree p+degree k - n. T i)"
            using deg_eq unfolding T_def by auto 
          also have "...=(\<Sum>i\<in>{0..<degree p}. T i) + setsum T {(degree p)}+ 
                  setsum T {degree p + 1..degree p + degree k - n}" 
            proof -
              def C\<equiv>"{{0..<degree p}, {degree p},{degree p+1..degree p+degree k-n}}"
              have "\<forall>A\<in>C. finite A" unfolding C_def by auto
              moreover have "\<forall>A\<in>C. \<forall>B\<in>C. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
                unfolding C_def by auto
              ultimately have "setsum T (\<Union>C) = setsum (setsum T) C" 
                using setsum.Union_disjoint by auto
              moreover have "\<Union>C={..degree p + degree k - n}" 
                using `n \<le> degree k` unfolding C_def by auto
              moreover have  "setsum (setsum T) C= setsum T {0..<degree p} + setsum T {(degree p)} + 
                  setsum T {degree p + 1..degree p + degree k - n}"
                proof -
                  have "{0..<degree p}\<noteq>{degree p}" 
                    by (metis atLeast0LessThan insertI1 lessThan_iff less_imp_not_eq)  
                  moreover have "{degree p}\<noteq>{degree p + 1..degree p + degree k - n}" 
                    by (metis add.commute add_diff_cancel_right' atLeastAtMost_singleton_iff 
                      diff_self_eq_0 eq_imp_le not_one_le_zero)
                  moreover have "{0..<degree p}\<noteq>{degree p + 1..degree p + degree k - n}" 
                    using `degree k\<ge>n` `degree p\<noteq>0` by fastforce
                  ultimately show ?thesis unfolding C_def by auto
                qed
              ultimately show ?thesis by auto
            qed
          also have "...=(\<Sum>i\<in>{0..<degree p}. T i) +  coeff k (degree k - n)"
            proof -
              have "\<forall>x\<in>{degree p + 1..degree p + degree k - n}. T x=0" 
                using coeff_eq_0[of p] unfolding T_def by simp
              hence "setsum T {degree p + 1..degree p + degree k - n}=0" by auto
              moreover have "T (degree p)=coeff k (degree k - n)"
                using monic unfolding T_def lead_coeff_def by auto
              ultimately show ?thesis by auto
            qed
          finally have c_coeff: "c * coeff q (degree q - n) = setsum T {0..<degree p} 
              + coeff k (degree k - n)" .
          show ?case
          proof (cases "n = 0")
            assume "n \<noteq> 0"
            have "c dvd setsum T {0..<degree p}" 
            proof (rule dvd_setsum)
              fix i assume i:"i \<in> {0..<degree p}"
              hence "(n+i-degree p)\<le>degree k" using `n \<le> degree k` by auto
              moreover have "n + i - degree p <n" using i `n\<noteq>0` by auto 
              ultimately have "c dvd coeff k (degree k - (n+i-degree p))"
                using 1(1) by auto
              hence "c dvd coeff k (degree p + degree k - n - i)"
                by (metis add_diff_cancel_left' deg_eq diff_diff_left dvd_0_right le_degree 
                  le_diff_conv add.commute ordered_cancel_comm_monoid_diff_class.diff_diff_right)
              thus "c dvd T i" unfolding T_def by auto
            qed
            moreover have "c dvd setsum T {0..<degree p} + coeff k (degree k - n)"
              by (subst c_coeff [symmetric]) simp
            ultimately show ?case by (subst (asm) dvd_add_right_iff)
          next
            assume "n=0"
            hence "\<forall>i\<in>{0..<degree p}. coeff k (degree p + degree k - n - i) =0" 
              using coeff_eq_0[of k] by simp
            hence "c * coeff q (degree q - n) = coeff k (degree k - n)"
              using c_coeff unfolding T_def by auto
            thus ?thesis by (metis dvdI)
          qed
        qed
    qed
  hence "\<forall>n. c dvd coeff k n"
    by (metis diff_diff_cancel dvd_0_right le_add2 le_add_diff_inverse le_degree)
  then obtain f where f:"\<forall>n. c * f n = coeff k n" unfolding dvd_def by metis
  from MOST_conjI[OF ALL_MOST[OF f] MOST_coeff_eq_0[of k]] have "\<forall>\<^sub>\<infinity>n. f n = 0"
    by (rule MOST_rev_mp) (auto intro!: ALL_MOST simp: `c \<noteq> 0`)
  hence "smult c (Abs_poly f)=k" 
    using f smult.abs_eq[of c "Abs_poly f"] Abs_poly_inverse[of f] coeff_inverse[of k]
    by simp
  hence "q=p* Abs_poly f" using k `c\<noteq>0` smult_cancel by auto
  thus ?thesis unfolding dvd_def by auto
qed

lemma poly_power_n_eq:
  fixes x::"'a :: idom"
  assumes "n\<noteq>0"
  shows "poly ([:-a,1:]^n) x=0 \<longleftrightarrow> (x=a)" using assms 
by (induct n,auto)

lemma poly_power_n_odd:
  fixes x a:: real
  assumes "odd n"
  shows "poly ([:-a,1:]^n) x>0 \<longleftrightarrow> (x>a)" using assms 
proof -
  have "poly ([:-a,1:]^n) x\<ge>0 = (poly [:- a, 1:] x \<ge>0)" 
    unfolding poly_power using zero_le_odd_power[OF `odd n`] by blast 
  also have "(poly [:- a, 1:] x \<ge>0) = (x\<ge>a)" by fastforce
  finally have "poly ([:-a,1:]^n) x\<ge>0 = (x\<ge>a)" .
  moreover have "poly ([:-a,1:]^n) x=0 = (x=a)" by(rule poly_power_n_eq, metis assms even_zero)    
  ultimately show ?thesis by linarith
qed

lemma div_gcd_coprime_poly:
  fixes p q::"'a::field poly"
  assumes nz: "p \<noteq> 0 \<or> q \<noteq> 0"
  shows "coprime (p div gcd p q) (q div gcd p q)"
proof -
  def g \<equiv> "gcd p q"
  def p' \<equiv> "p div g" and  q' \<equiv> "q div g"
  def g' \<equiv> "gcd p' q'"
  have "g dvd p" "g dvd q" "g' dvd p'" "g' dvd q'"  unfolding g_def g'_def by simp_all
  then obtain kp kq kp' kq' where
      kab: "p = g * kp" "q = g * kq" "p' = g' * kp'" "q' = g' * kq'"
    unfolding dvd_def g_def g'_def by blast
  hence "g * p' = (g * g') * kp'" "g * q' = (g * g') * kq'" by simp_all
  then have dvdgg':"g * g' dvd p" "g* g' dvd q"
    using dvd_def dvd_mult_div_cancel [OF `g dvd p`,folded p'_def]
      dvd_mult_div_cancel [OF `g dvd q`,folded q'_def]
    by auto
  hence "g * g' dvd g" using poly_gcd_greatest g_def by auto
  hence "degree g + degree g' \<le> degree g"
    using degree_mult_eq nz dvd_imp_degree_le
    by (metis degree_0 g_def monoid_add_class.add.right_neutral order_refl poly_gcd_zero_iff)
  hence "degree g'=0" by auto
  moreover have "coeff g' (degree g') = 1" 
    using poly_gcd_monic[of p' q',folded g'_def] nz unfolding p'_def q'_def 
    by (metis `g dvd p` `g dvd q` dvd_div_mult_self mult_eq_0_iff)
  ultimately have "g'=1" by (metis coeff_1 coeff_eq_0 neq0_conv poly_eq_iff) 
  thus ?thesis unfolding g'_def p'_def q'_def g_def .
qed

lemma gcd_coprime_poly:
  fixes p q::"'a::field poly"
  assumes nz: "p \<noteq> 0 \<or> q \<noteq> 0" and p': "p = p' * gcd p q" and
    q': "q = q' * gcd p q"
  shows "coprime p' q'"
proof -
  have "p' = p div gcd p q" 
    using p' nz by (metis div_mult_self2_is_id poly_gcd_zero_iff)
  moreover have "q'= q div gcd p q"   
    using q' nz by (metis div_mult_self2_is_id poly_gcd_zero_iff)
  ultimately show ?thesis using div_gcd_coprime_poly[OF nz] by auto
qed


section{*Bound of polynomials*}

definition sgn_pos_inf :: "('a::real_normed_vector) poly \<Rightarrow> 'a" where 
  "sgn_pos_inf p \<equiv> sgn (lead_coeff p)"
definition sgn_neg_inf :: "('a::real_normed_vector) poly \<Rightarrow> 'a" where 
  "sgn_neg_inf p \<equiv> if even (degree p) then sgn (lead_coeff p) else -sgn (lead_coeff p)"

lemma sgn_inf_sym:
  fixes p::"real poly"
  shows "sgn_pos_inf (pcompose p [:0,-1:]) = sgn_neg_inf p" (is "?L=?R")
proof -
  have "?L= sgn (lead_coeff p * (- 1) ^ degree p)" 
    unfolding sgn_pos_inf_def by (subst lead_coeff_comp,unfold lead_coeff_def,auto)
  thus ?thesis unfolding sgn_neg_inf_def 
    by (metis mult.right_neutral mult_minus1_right neg_one_even_power neg_one_odd_power sgn_minus)
qed

lemma poly_sgn_eventually_at_top:
  fixes p::"real poly"
  shows "eventually (\<lambda>x. sgn (poly p x) = sgn_pos_inf p) at_top"
proof (cases "p=0")
  case True
  thus ?thesis unfolding sgn_pos_inf_def by auto
next
  case False
  obtain ub where ub:"\<forall>x\<ge>ub. sgn (poly p x) = sgn_pos_inf p"
    proof (cases "lead_coeff p>0")
      case True
      thus ?thesis 
        using that poly_pinfty_gt_lc[of p] unfolding sgn_pos_inf_def by fastforce 
    next
      case False
      hence "lead_coeff (-p) > 0" and "lead_coeff p < 0" unfolding lead_coeff_minus
        using leading_coeff_neq_0[OF `p\<noteq>0`,folded lead_coeff_def] by auto
      then obtain n where "\<forall>x\<ge>n. lead_coeff p \<ge> poly p x"
        using poly_pinfty_gt_lc[of "-p"] unfolding lead_coeff_minus by auto
      thus ?thesis using `lead_coeff p<0` that[of n] unfolding sgn_pos_inf_def by fastforce
    qed
  thus ?thesis unfolding eventually_at_top_linorder by auto
qed

lemma poly_sgn_eventually_at_bot:
  fixes p::"real poly"
  shows "eventually (\<lambda>x. sgn (poly p x) = sgn_neg_inf p) at_bot"
using 
  poly_sgn_eventually_at_top[of "pcompose p [:0,-1:]",unfolded poly_pcompose sgn_inf_sym,simplified]
  eventually_filtermap[of _ uminus "at_bot::real filter",folded at_top_mirror]
by auto
   
lemma root_ub:
  fixes p:: "real poly"
  assumes "p\<noteq>0"
  obtains ub where "\<forall>x. poly p x=0 \<longrightarrow> x<ub"
    and "\<forall>x\<ge>ub. sgn (poly p x) = sgn_pos_inf p"
proof -
  obtain ub1 where ub1:"\<forall>x. poly p x=0 \<longrightarrow> x<ub1"
    proof (cases "\<exists> r. poly p r=0")
      case False
      thus ?thesis using that by auto
    next
      case True
      def max_r\<equiv>"Max {x . poly p x=0}"
      hence "\<forall>x. poly p x=0 \<longrightarrow> x\<le>max_r"
        using  poly_roots_finite[OF `p\<noteq>0`] True by auto
      thus ?thesis using that[of "max_r+1"] 
        by (metis add.commute add_strict_increasing zero_less_one)
    qed
  obtain ub2 where ub2:"\<forall>x\<ge>ub2. sgn (poly p x) = sgn_pos_inf p"
    using poly_sgn_eventually_at_top[unfolded eventually_at_top_linorder] by auto
  def ub\<equiv>"max ub1 ub2"
  have "\<forall>x. poly p x=0 \<longrightarrow> x<ub" using ub1 ub_def 
    by (metis eq_iff less_eq_real_def less_linear max.bounded_iff)
  thus ?thesis using that[of ub] ub2 ub_def by auto
qed

lemma root_lb:
  fixes p:: "real poly"
  assumes "p\<noteq>0"
  obtains lb where "\<forall>x. poly p x=0 \<longrightarrow> x>lb"
    and "\<forall>x\<le>lb. sgn (poly p x) = sgn_neg_inf p"
proof -
  obtain lb1 where lb1:"\<forall>x. poly p x=0 \<longrightarrow> x>lb1"
    proof (cases "\<exists> r. poly p r=0")
      case False
      thus ?thesis using that by auto
    next
      case True
      def min_r\<equiv>"Min {x . poly p x=0}"
      hence "\<forall>x. poly p x=0 \<longrightarrow> x\<ge>min_r"
        using  poly_roots_finite[OF `p\<noteq>0`] True by auto
      thus ?thesis using that[of "min_r - 1"] by (metis lt_ex order.strict_trans2 that) 
    qed
  obtain lb2 where lb2:"\<forall>x\<le>lb2. sgn (poly p x) = sgn_neg_inf p"
    using poly_sgn_eventually_at_bot[unfolded eventually_at_bot_linorder] by auto
  def lb\<equiv>"min lb1 lb2"
  have "\<forall>x. poly p x=0 \<longrightarrow> x>lb" using lb1 lb_def 
    by (metis (poly_guards_query) less_not_sym min_less_iff_conj neq_iff)
  thus ?thesis using that[of lb] lb2 lb_def by auto
qed
        
end

