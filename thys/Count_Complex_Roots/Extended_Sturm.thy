(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section \<open>An alternative Sturm sequences\<close>

theory Extended_Sturm imports 
  "Sturm_Tarski.Sturm_Tarski" 
  "Winding_Number_Eval.Cauchy_Index_Theorem"
  CC_Polynomials_Extra
begin 
  
text \<open>The main purpose of this theory is to provide an effective way to compute 
  @{term "cindexE a b f"} when @{term f} is a rational function. The idea is similar to and based
  on the evaluation of @{term cindex_poly} through @{thm cindex_poly_changes_itv_mods}.\<close>   
  
text \<open>
This alternative version of remainder sequences is inspired by the paper 
  "The Fundamental Theorem of Algebra made effective: 
  an elementary real-algebraic proof via Sturm chains" 
by Michael Eisermann.
\<close>  
  
hide_const Permutations.sign  
  
subsection \<open>Misc\<close> 

lemma path_of_real[simp]:"path (of_real :: real \<Rightarrow> 'a::real_normed_algebra_1)"
  unfolding path_def by (rule continuous_on_of_real_id)

lemma pathfinish_of_real[simp]:"pathfinish of_real = 1"
  unfolding pathfinish_def by simp
lemma pathstart_of_real[simp]:"pathstart of_real = 0"
  unfolding pathstart_def by simp
   
lemma is_unit_pCons_ex_iff:
  fixes p::"'a::field poly"
  shows "is_unit p \<longleftrightarrow> (\<exists>a. a\<noteq>0 \<and> p=[:a:])"
  using is_unit_poly_iff is_unit_triv 
  by (metis is_unit_pCons_iff)
  
lemma eventually_poly_nz_at_within:
  fixes x :: "'a::{idom,euclidean_space} "
  assumes "p\<noteq>0" 
  shows "eventually (\<lambda>x. poly p x\<noteq>0) (at x within S)"     
proof -
  have "eventually (\<lambda>x. poly p x\<noteq>0) (at x within S) 
      = (\<forall>\<^sub>F x in (at x within S). \<forall>y\<in>proots p. x \<noteq> y)"
    apply (rule eventually_subst,rule eventuallyI)
    by (auto simp add:proots_def)
  also have "... = (\<forall>y\<in>proots p. \<forall>\<^sub>F x in (at x within S). x \<noteq> y)"
    apply (subst eventually_ball_finite_distrib)
    using \<open>p\<noteq>0\<close> by auto
  also have "..."
    unfolding eventually_at
    by (metis gt_ex not_less_iff_gr_or_eq zero_less_dist_iff) 
  finally show ?thesis .
qed
    
lemma sgn_power:
  fixes x::"'a::linordered_idom"
  shows "sgn (x^n) = (if n=0 then 1 else if even n then \<bar>sgn x\<bar> else sgn x)"
  apply (induct n)
  by (auto simp add:sgn_mult)

lemma poly_divide_filterlim_at_top: 
  fixes p q::"real poly"
  defines "ll\<equiv>( if degree q<degree p then 
                    at 0 
                else if degree q=degree p then 
                    nhds (lead_coeff q / lead_coeff p)
                else if sgn_pos_inf q * sgn_pos_inf p > 0 then 
                    at_top
                else 
                    at_bot)"
  assumes "p\<noteq>0" "q\<noteq>0"
  shows "filterlim (\<lambda>x. poly q x / poly p x) ll at_top"
proof -
  define pp where "pp=(\<lambda>x. poly p x / x^(degree p))"    
  define qq where "qq=(\<lambda>x. poly q x / x^(degree q))"
  define dd where "dd=(\<lambda>x::real. if degree p>degree q then 1/x^(degree p - degree q) else 
                                x^(degree q - degree p))"
  have divide_cong:"\<forall>\<^sub>Fx in at_top. poly q x / poly p x = qq x / pp x * dd x"
  proof (rule eventually_at_top_linorderI[of 1])
    fix x assume "(x::real)\<ge>1"
    then have "x\<noteq>0" by auto
    then show "poly q x / poly p x = qq x / pp x * dd x"
      unfolding qq_def pp_def dd_def using assms 
      by (auto simp add:field_simps power_diff) 
  qed
  have qqpp_tendsto:"((\<lambda>x. qq x / pp x) \<longlongrightarrow> lead_coeff q / lead_coeff p) at_top"
  proof -
    have "(qq \<longlongrightarrow> lead_coeff q) at_top"
      unfolding qq_def using poly_divide_tendsto_aux[of q]  
      by (auto elim!:filterlim_mono simp:at_top_le_at_infinity)
    moreover have "(pp \<longlongrightarrow> lead_coeff p) at_top"
      unfolding pp_def using poly_divide_tendsto_aux[of p]  
      by (auto elim!:filterlim_mono simp:at_top_le_at_infinity)
    ultimately show ?thesis using \<open>p\<noteq>0\<close> by (auto intro!:tendsto_eq_intros)
  qed
  
  have ?thesis when "degree q<degree p"
  proof -
    have "filterlim (\<lambda>x. poly q x / poly p x) (at 0) at_top"
    proof (rule filterlim_atI)
      show "((\<lambda>x. poly q x / poly p x) \<longlongrightarrow> 0) at_top"
        using poly_divide_tendsto_0_at_infinity[OF that]
        by (auto elim:filterlim_mono simp:at_top_le_at_infinity)
      have "\<forall>\<^sub>F x in at_top. poly q x \<noteq>0" "\<forall>\<^sub>F x in at_top. poly p x \<noteq>0"
        using poly_eventually_not_zero[OF \<open>q\<noteq>0\<close>] poly_eventually_not_zero[OF \<open>p\<noteq>0\<close>]
              filter_leD[OF at_top_le_at_infinity]
        by auto
      then show "\<forall>\<^sub>F x in at_top. poly q x / poly p x \<noteq> 0"
        apply eventually_elim
        by auto
    qed
    then show ?thesis unfolding ll_def using that by auto
  qed
  moreover have ?thesis when "degree q=degree p"
  proof -
    have "((\<lambda>x. poly q x / poly p x) \<longlongrightarrow> lead_coeff q / lead_coeff p) at_top"
      using divide_cong qqpp_tendsto that unfolding dd_def
      by (auto dest:tendsto_cong)
    then show ?thesis unfolding ll_def using that by auto
  qed
  moreover have ?thesis when "degree q>degree p" "sgn_pos_inf q * sgn_pos_inf p > 0"
  proof -
    have "filterlim (\<lambda>x. (qq x / pp x) * dd x) at_top at_top"
    proof (subst filterlim_tendsto_pos_mult_at_top_iff[OF qqpp_tendsto])
      show "0 < lead_coeff q / lead_coeff p" using that(2) unfolding sgn_pos_inf_def
        by (simp add: zero_less_divide_iff zero_less_mult_iff)
      show "filterlim dd at_top at_top"
        unfolding dd_def using that(1) 
        by (auto intro!:filterlim_pow_at_top simp:filterlim_ident)
    qed
    then have "LIM x at_top. poly q x / poly p x :> at_top" 
      using filterlim_cong[OF _ _ divide_cong] by blast
    then show ?thesis unfolding ll_def using that by auto
  qed
  moreover have ?thesis  when "degree q>degree p" "\<not> sgn_pos_inf q * sgn_pos_inf p > 0"
  proof -
    have "filterlim (\<lambda>x. (qq x / pp x) * dd x) at_bot at_top"
    proof (subst filterlim_tendsto_neg_mult_at_bot_iff[OF qqpp_tendsto])
      show "lead_coeff q / lead_coeff p < 0" 
        using that(2) \<open>p\<noteq>0\<close> \<open>q\<noteq>0\<close> unfolding sgn_pos_inf_def
        by (metis divide_eq_0_iff divide_sgn leading_coeff_0_iff 
            linorder_neqE_linordered_idom sgn_divide sgn_greater)
      show "filterlim dd at_top at_top"
        unfolding dd_def using that(1) 
        by (auto intro!:filterlim_pow_at_top simp:filterlim_ident)
    qed
    then have "LIM x at_top. poly q x / poly p x :> at_bot" 
      using filterlim_cong[OF _ _ divide_cong] by blast
    then show ?thesis unfolding ll_def using that by auto
  qed
  ultimately show ?thesis by linarith
qed

lemma poly_divide_filterlim_at_bot: 
  fixes p q::"real poly"
  defines "ll\<equiv>( if degree q<degree p then 
                    at 0 
                else if degree q=degree p then 
                    nhds (lead_coeff q / lead_coeff p)
                else if sgn_neg_inf q * sgn_neg_inf p > 0 then 
                    at_top
                else 
                    at_bot)"
  assumes "p\<noteq>0" "q\<noteq>0"
  shows "filterlim (\<lambda>x. poly q x / poly p x) ll at_bot"
proof -
  define pp where "pp=(\<lambda>x. poly p x / x^(degree p))"    
  define qq where "qq=(\<lambda>x. poly q x / x^(degree q))"
  define dd where "dd=(\<lambda>x::real. if degree p>degree q then 1/x^(degree p - degree q) else 
                                x^(degree q - degree p))"
  have divide_cong:"\<forall>\<^sub>Fx in at_bot. poly q x / poly p x = qq x / pp x * dd x"
  proof (rule eventually_at_bot_linorderI[of "-1"])
    fix x assume "(x::real)\<le>-1"
    then have "x\<noteq>0" by auto
    then show "poly q x / poly p x = qq x / pp x * dd x"
      unfolding qq_def pp_def dd_def using assms 
      by (auto simp add:field_simps power_diff) 
  qed
  have qqpp_tendsto:"((\<lambda>x. qq x / pp x) \<longlongrightarrow> lead_coeff q / lead_coeff p) at_bot"
  proof -
    have "(qq \<longlongrightarrow> lead_coeff q) at_bot"
      unfolding qq_def using poly_divide_tendsto_aux[of q]  
      by (auto elim!:filterlim_mono simp:at_bot_le_at_infinity)
    moreover have "(pp \<longlongrightarrow> lead_coeff p) at_bot"
      unfolding pp_def using poly_divide_tendsto_aux[of p]  
      by (auto elim!:filterlim_mono simp:at_bot_le_at_infinity)
    ultimately show ?thesis using \<open>p\<noteq>0\<close> by (auto intro!:tendsto_eq_intros)
  qed
  
  have ?thesis when "degree q<degree p"
  proof -
    have "filterlim (\<lambda>x. poly q x / poly p x) (at 0) at_bot"
    proof (rule filterlim_atI)
      show "((\<lambda>x. poly q x / poly p x) \<longlongrightarrow> 0) at_bot"
        using poly_divide_tendsto_0_at_infinity[OF that]
        by (auto elim:filterlim_mono simp:at_bot_le_at_infinity)
      have "\<forall>\<^sub>F x in at_bot. poly q x \<noteq>0" "\<forall>\<^sub>F x in at_bot. poly p x \<noteq>0"
        using poly_eventually_not_zero[OF \<open>q\<noteq>0\<close>] poly_eventually_not_zero[OF \<open>p\<noteq>0\<close>]
              filter_leD[OF at_bot_le_at_infinity]
        by auto
      then show "\<forall>\<^sub>F x in at_bot. poly q x / poly p x \<noteq> 0"
        by eventually_elim auto
    qed
    then show ?thesis unfolding ll_def using that by auto
  qed
  moreover have ?thesis when "degree q=degree p"
  proof -
    have "((\<lambda>x. poly q x / poly p x) \<longlongrightarrow> lead_coeff q / lead_coeff p) at_bot"
      using divide_cong qqpp_tendsto that unfolding dd_def
      by (auto dest:tendsto_cong)
    then show ?thesis unfolding ll_def using that by auto
  qed
  moreover have ?thesis when "degree q>degree p" "sgn_neg_inf q * sgn_neg_inf p > 0"
  proof -
    define cc where "cc=lead_coeff q / lead_coeff p"
    have "(cc > 0 \<and> even (degree q - degree p)) \<or> (cc<0 \<and> odd (degree q - degree p))"
    proof -
      have "even (degree q - degree p) \<longleftrightarrow> 
            (even (degree q) \<and> even (degree p)) \<or> (odd (degree q) \<and> odd (degree p))"
        using \<open>degree q>degree p\<close> by auto
      then show ?thesis
        using that \<open>p\<noteq>0\<close> \<open>q\<noteq>0\<close> unfolding sgn_neg_inf_def cc_def zero_less_mult_iff 
          divide_less_0_iff zero_less_divide_iff 
        apply (simp add:if_split[of "(<) 0"] if_split[of "(>) 0"])
        by argo
    qed
    moreover have "filterlim (\<lambda>x. (qq x / pp x) * dd x) at_top at_bot"
      when "cc>0" "even (degree q - degree p)"
    proof (subst filterlim_tendsto_pos_mult_at_top_iff[OF qqpp_tendsto])
      show "0 < lead_coeff q / lead_coeff p" using \<open>cc>0\<close> unfolding cc_def by auto
      show "filterlim dd at_top at_bot"
        unfolding dd_def using \<open>degree q>degree p\<close> that(2)
        by (auto intro!:filterlim_pow_at_bot_even simp:filterlim_ident)
    qed
    moreover have "filterlim (\<lambda>x. (qq x / pp x) * dd x) at_top at_bot"
      when "cc<0" "odd (degree q - degree p)"
    proof (subst filterlim_tendsto_neg_mult_at_top_iff[OF qqpp_tendsto])
      show "0 > lead_coeff q / lead_coeff p" using \<open>cc<0\<close> unfolding cc_def by auto
      show "filterlim dd at_bot at_bot"
        unfolding dd_def using \<open>degree q>degree p\<close> that(2)
        by (auto intro!:filterlim_pow_at_bot_odd simp:filterlim_ident)
    qed
    ultimately have "filterlim (\<lambda>x. (qq x / pp x) * dd x) at_top at_bot"
      by blast
    then have "LIM x at_bot. poly q x / poly p x :> at_top"
      using filterlim_cong[OF _ _ divide_cong] by blast
    then show ?thesis unfolding ll_def using that by auto
  qed
  moreover have ?thesis  when "degree q>degree p" "\<not> sgn_neg_inf q * sgn_neg_inf p > 0"
  proof -
    define cc where "cc=lead_coeff q / lead_coeff p"
    have "(cc < 0 \<and> even (degree q - degree p)) \<or> (cc > 0 \<and> odd (degree q - degree p))"
    proof -
      have "even (degree q - degree p) \<longleftrightarrow> 
            (even (degree q) \<and> even (degree p)) \<or> (odd (degree q) \<and> odd (degree p))"
        using \<open>degree q>degree p\<close> by auto
      then show ?thesis
        using that \<open>p\<noteq>0\<close> \<open>q\<noteq>0\<close> unfolding sgn_neg_inf_def cc_def zero_less_mult_iff 
          divide_less_0_iff zero_less_divide_iff
        apply (simp add:if_split[of "(<) 0"] if_split[of "(>) 0"])
        by (metis leading_coeff_0_iff linorder_neqE_linordered_idom)
    qed
    moreover have "filterlim (\<lambda>x. (qq x / pp x) * dd x) at_bot at_bot"
      when "cc<0" "even (degree q - degree p)"
    proof (subst filterlim_tendsto_neg_mult_at_bot_iff[OF qqpp_tendsto])
      show "0 > lead_coeff q / lead_coeff p" using \<open>cc<0\<close> unfolding cc_def by auto
      show "filterlim dd at_top at_bot"
        unfolding dd_def using \<open>degree q>degree p\<close> that(2)
        by (auto intro!:filterlim_pow_at_bot_even simp:filterlim_ident)
    qed
    moreover have "filterlim (\<lambda>x. (qq x / pp x) * dd x) at_bot at_bot"
      when "cc>0" "odd (degree q - degree p)"
    proof (subst filterlim_tendsto_pos_mult_at_bot_iff[OF qqpp_tendsto])
      show "0 < lead_coeff q / lead_coeff p" using \<open>cc>0\<close> unfolding cc_def by auto
      show "filterlim dd at_bot at_bot"
        unfolding dd_def using \<open>degree q>degree p\<close> that(2)
        by (auto intro!:filterlim_pow_at_bot_odd simp:filterlim_ident)
    qed
    ultimately have "filterlim (\<lambda>x. (qq x / pp x) * dd x) at_bot at_bot"
      by blast
    then have "LIM x at_bot. poly q x / poly p x :> at_bot"
      using filterlim_cong[OF _ _ divide_cong] by blast
    then show ?thesis unfolding ll_def using that by auto
  qed
  ultimately show ?thesis by linarith
qed

(*TODO: move*)
lemma sgnx_poly_times:
  assumes "F=at_bot \<or> F=at_top \<or> F=at_right x \<or> F=at_left x"
  shows "sgnx (poly (p*q)) F = sgnx (poly p) F * sgnx (poly q) F"
    (is  "?PQ = ?P * ?Q")
proof  -
  have "(poly p has_sgnx ?P) F" 
        "(poly q has_sgnx ?Q) F" 
    by (rule sgnx_able_sgnx;use assms sgnx_able_poly in blast)+
  from has_sgnx_times[OF this]            
  have "(poly (p*q) has_sgnx ?P*?Q) F"
    by (simp flip:poly_mult)
  moreover have "(poly (p*q) has_sgnx ?PQ) F" 
    by (rule sgnx_able_sgnx;use assms sgnx_able_poly in blast)+
  ultimately show ?thesis 
    using has_sgnx_unique assms by auto
qed

(*TODO: move*)
lemma sgnx_poly_plus:
  assumes "poly p x=0" "poly q x\<noteq>0" and F:"F=at_right x \<or> F=at_left x"
  shows "sgnx (poly (p+q)) F = sgnx (poly q) F" (is "?L=?R")
proof -
  have "((poly (p+q)) has_sgnx ?R) F"
  proof -
    have "sgnx (poly q) F = sgn (poly q x)"
      using F assms(2) sgnx_poly_nz(1) sgnx_poly_nz(2) by presburger
    moreover have "((\<lambda>x. poly (p+q) x) has_sgnx sgn (poly q x)) F" 
    proof (rule tendsto_nonzero_has_sgnx)
      have "((poly p) \<longlongrightarrow> 0) F" 
        by (metis F assms(1) poly_tendsto(2) poly_tendsto(3))
      then have "((\<lambda>x. poly p x + poly  q x) \<longlongrightarrow> poly q x) F"
        apply (elim tendsto_add[where a=0,simplified])
        using F poly_tendsto(2) poly_tendsto(3) by blast
      then show "((\<lambda>x. poly (p + q) x) \<longlongrightarrow> poly q x) F"
        by auto
    qed fact
    ultimately show ?thesis by metis
  qed
  from has_sgnx_imp_sgnx[OF this] F
  show ?thesis by auto
qed

(*TODO: move*)
lemma sign_r_pos_plus_imp:
  assumes "sign_r_pos p x" "sign_r_pos q x"
  shows "sign_r_pos (p+q) x"
  using assms unfolding sign_r_pos_def
  by eventually_elim auto

(*TODO: move*)
lemma cindex_poly_combine:
  assumes "a<b" "b<c"
  shows "cindex_poly a b q p + jump_poly q p b + cindex_poly b c q p = cindex_poly a c q p"
proof (cases "p\<noteq>0")
  case True
  define A B C D where "A = {x. poly p x = 0 \<and> a < x \<and> x < c}"
                and "B = {x. poly p x = 0 \<and> a < x \<and> x < b}"
                and "C = (if poly p b = 0 then {b} else {})"
                and "D = {x. poly p x = 0 \<and> b < x \<and> x < c}"
  let ?sum="sum (\<lambda>x. jump_poly q p x)"

  have "cindex_poly a c q p = ?sum A"
    unfolding cindex_poly_def A_def by simp
  also have "... = ?sum (B \<union> C \<union> D)"
    apply (rule arg_cong2[where f=sum])
    unfolding A_def B_def C_def D_def using less_linear assms by auto
  also have "... = ?sum B + ?sum C + ?sum D"
  proof -
    have "finite B" "finite C" "finite D" 
      unfolding B_def C_def D_def using True 
      by (auto simp add: poly_roots_finite)
    moreover have "B \<inter> C = {}" "C \<inter> D = {}" "B \<inter> D = {}" 
      unfolding B_def C_def D_def using assms by auto
    ultimately show ?thesis
      by (subst sum.union_disjoint;auto)+ 
  qed
  also have "... = cindex_poly a b q p + jump_poly q p b + cindex_poly b c q p"
  proof -
    have "?sum C = jump_poly q p b" 
      unfolding C_def using jump_poly_not_root by auto
    then show ?thesis unfolding cindex_poly_def B_def D_def
      by auto
  qed
  finally show ?thesis by simp
qed auto

lemma coprime_linear_comp: \<comment>\<open>TODO: need to be generalised\<close>
  fixes b c::real
  defines "r0 \<equiv> [:b,c:]"
  assumes "coprime p q" "c\<noteq>0"
  shows "coprime (p \<circ>\<^sub>p r0) (q \<circ>\<^sub>p r0)"
proof -
  define g where "g = gcd (p \<circ>\<^sub>p r0) (q \<circ>\<^sub>p r0)"
  define p' where "p' = (p \<circ>\<^sub>p r0) div g"
  define q' where "q' = (q \<circ>\<^sub>p r0) div g"
  define r1 where "r1 = [:-b/c,1/c:]"
  
  have r_id:
      "r0 \<circ>\<^sub>p r1 = [:0,1:]"
      "r1 \<circ>\<^sub>p r0 = [:0,1:]"
    unfolding r0_def r1_def using \<open>c\<noteq>0\<close> 
    by (simp add: pcompose_pCons)+
     
  have "p = (g \<circ>\<^sub>p r1) * (p' \<circ>\<^sub>p r1)"
  proof -
    from r_id have "p = p \<circ>\<^sub>p (r0 \<circ>\<^sub>p r1)"
      by (metis pcompose_idR)
    also have "... =  (g * p') \<circ>\<^sub>p r1"
      unfolding g_def p'_def by (auto simp:pcompose_assoc)
    also have "... = (g \<circ>\<^sub>p r1) * (p' \<circ>\<^sub>p r1)"
      unfolding pcompose_mult by simp
    finally show ?thesis .
  qed
  moreover have "q = (g \<circ>\<^sub>p r1) * (q' \<circ>\<^sub>p r1)" 
  proof -
    from r_id have "q = q \<circ>\<^sub>p (r0 \<circ>\<^sub>p r1)"
      by (metis pcompose_idR)
    also have "... =  (g * q') \<circ>\<^sub>p r1"
      unfolding g_def q'_def by (auto simp:pcompose_assoc)
    also have "... = (g \<circ>\<^sub>p r1) * (q' \<circ>\<^sub>p r1)"
      unfolding pcompose_mult by simp
    finally show ?thesis .
  qed
  ultimately have "(g \<circ>\<^sub>p r1) dvd gcd p q" by simp
  then have "g \<circ>\<^sub>p r1 dvd 1"
    using \<open>coprime p q\<close> by auto
  from pcompose_hom.hom_dvd_1[OF this]
  have "is_unit (g \<circ>\<^sub>p (r1 \<circ>\<^sub>p r0))"
    by (auto simp:pcompose_assoc)
  then have "is_unit g"
    using r_id pcompose_idR by auto
  then show "coprime (p \<circ>\<^sub>p r0) (q \<circ>\<^sub>p r0)" unfolding g_def
    using is_unit_gcd by blast
qed

lemma finite_ReZ_segments_poly_rectpath:
    "finite_ReZ_segments (poly p \<circ> rectpath a b) z"
  unfolding rectpath_def Let_def path_compose_join
  by ((subst finite_ReZ_segments_joinpaths
            |intro path_poly_comp conjI);
        (simp add:poly_linepath_comp finite_ReZ_segments_poly_of_real path_compose_join 
          pathfinish_compose pathstart_compose poly_pcompose)?)+

lemma valid_path_poly_linepath: 
  fixes a b::"'a::real_normed_field"
  shows "valid_path (poly p o linepath a b)"
proof (rule valid_path_compose)
  show "valid_path (linepath a b)" by simp
  show "\<And>x. x \<in> path_image (linepath a b) \<Longrightarrow> poly p field_differentiable at x"
    by simp
  show "continuous_on (path_image (linepath a b)) (deriv (poly p))"
    unfolding deriv_pderiv by (auto intro:continuous_intros)
qed

lemma valid_path_poly_rectpath: "valid_path (poly p o rectpath a b)"
  unfolding rectpath_def Let_def path_compose_join
  by (simp add: pathfinish_compose pathstart_compose valid_path_poly_linepath)

subsection \<open>Sign difference\<close>

definition psign_diff :: "real poly \<Rightarrow>real poly \<Rightarrow> real \<Rightarrow> int" where
  "psign_diff p q x = (if poly p x = 0 \<and> poly q x = 0 then
      1 else \<bar>sign (poly p x) - sign (poly q x)\<bar>)"

lemma psign_diff_alt:
  assumes "coprime p q"
  shows "psign_diff p q x = \<bar>sign (poly p x) - sign (poly q x)\<bar>"
  unfolding psign_diff_def by (meson assms coprime_poly_0)

lemma psign_diff_0[simp]:
  "psign_diff 0 q x = 1"
  "psign_diff p 0 x = 1"
  unfolding psign_diff_def by (auto simp add:sign_def)

lemma psign_diff_poly_commute:
  "psign_diff p q x = psign_diff q p x"
  unfolding psign_diff_def 
  by (metis abs_minus_commute gcd.commute)

lemma normalize_real_poly:
  "normalize p = smult (1/lead_coeff p) (p::real poly)"
  unfolding normalize_poly_def
  by (smt (z3) div_unit_factor normalize_eq_0_iff normalize_poly_def 
      normalize_unit_factor smult_eq_0_iff smult_eq_iff 
      smult_normalize_field_eq unit_factor_1)

lemma psign_diff_cancel:
  assumes "poly r x\<noteq>0"
  shows "psign_diff (r*p) (r*q) x = psign_diff p q x"
proof  -
  have "poly (r * p) x = 0 \<longleftrightarrow> poly p x=0" 
    by (simp add: assms)
  moreover have "poly (r * q) x = 0 \<longleftrightarrow> poly q x=0" by (simp add: assms)
  moreover have "\<bar>sign (poly (r * p) x) - sign (poly (r * q) x)\<bar> 
                    = \<bar>sign (poly p x) - sign (poly q x)\<bar>"
  proof -
    have "\<bar>sign (poly (r * p) x) - sign (poly (r * q) x)\<bar>
       = \<bar>sign (poly r x) * (sign (poly p x) - sign (poly q x))\<bar>"
      by (simp add:algebra_simps sign_times)
    also have "... = \<bar>sign (poly r x) \<bar> 
                        * \<bar>sign (poly p x) - sign (poly q x)\<bar>"
      unfolding abs_mult by simp
    also have "... = \<bar>sign (poly p x) - sign (poly q x)\<bar>"
      by (simp add: Sturm_Tarski.sign_def assms)
    finally show ?thesis .
  qed
  ultimately show ?thesis
    unfolding psign_diff_def by auto
qed

lemma psign_diff_clear: "psign_diff p q x = psign_diff 1 (p * q) x"
  unfolding  psign_diff_def
  apply (simp add:sign_times )
  by (simp add: sign_def)

lemma psign_diff_linear_comp:
  fixes b c::real
  defines "h \<equiv> (\<lambda>p. pcompose p [:b,c:])"
  shows "psign_diff (h p) (h q) x = psign_diff p q (c * x + b)"
  unfolding psign_diff_def h_def poly_pcompose
  by (smt (verit, del_insts) mult.commute mult_eq_0_iff poly_0 poly_pCons)

subsection \<open>Alternative definition of cross\<close>
 
definition cross_alt :: "real poly \<Rightarrow>real poly \<Rightarrow> real \<Rightarrow> real \<Rightarrow> int" where
  "cross_alt p q a b= psign_diff p q a - psign_diff p q b"

lemma cross_alt_0[simp]:
  "cross_alt 0 q a b = 0"
  "cross_alt p 0 a b = 0"
  unfolding cross_alt_def by simp_all

lemma cross_alt_poly_commute:
  "cross_alt p q a b = cross_alt q p a b"
  unfolding cross_alt_def using psign_diff_poly_commute by auto

lemma cross_alt_clear:
  "cross_alt p q a b = cross_alt 1 (p*q) a b"
  unfolding cross_alt_def using psign_diff_clear by metis

lemma cross_alt_alt:
  "cross_alt p q a b = sign (poly (p*q) b) - sign (poly (p*q) a)"
  apply (subst cross_alt_clear)
  unfolding cross_alt_def psign_diff_def by (auto simp add:sign_def)

lemma cross_alt_coprime_0:
  assumes "coprime p q" "p=0\<or>q=0"
  shows "cross_alt p q a b=0" 
proof -
  have ?thesis when "p=0" 
  proof -
    have "is_unit q" using that \<open>coprime p q\<close> 
      by simp
    then obtain a where "a\<noteq>0" "q=[:a:]" using is_unit_pCons_ex_iff by blast
    then show ?thesis using that unfolding cross_alt_def by auto
  qed
  moreover have ?thesis when "q=0" 
  proof -
    have "is_unit p" using that \<open>coprime p q\<close> 
      by simp
    then obtain a where "a\<noteq>0" "p=[:a:]" using is_unit_pCons_ex_iff by blast
    then show ?thesis using that unfolding cross_alt_def by auto
  qed 
  ultimately show ?thesis using \<open>p=0\<or>q=0\<close> by auto
qed  

lemma cross_alt_cancel:
  assumes "poly q a\<noteq>0" "poly q b\<noteq>0"
  shows "cross_alt (q * r) (q * s) a b = cross_alt r s a b"
  unfolding cross_alt_def using psign_diff_cancel assms by auto

lemma cross_alt_noroot:
  assumes "a<b" and "\<forall>x. a\<le>x \<and> x\<le>b \<longrightarrow> poly (p*q) x\<noteq>0"
  shows "cross_alt p q a b = 0" 
proof -
  define pq where "pq = p*q"
  have "cross_alt p q a b = psign_diff 1 pq a - psign_diff 1 pq b "
    apply (subst cross_alt_clear)
    unfolding cross_alt_def pq_def by simp
  also have "... = \<bar>1 - sign (poly pq a)\<bar> - \<bar>1 - sign (poly pq b)\<bar>"
    unfolding psign_diff_def by simp
  also have "... = sign (poly pq b) - sign (poly pq a)"
    unfolding sign_def by auto
  also have "... = 0"
  proof (rule ccontr)
    assume "sign (poly pq b) - sign (poly pq a) \<noteq> 0"
    then have "poly pq a * poly pq b < 0" 
      by (smt (verit, best) Sturm_Tarski.sign_def assms(1) assms(2) 
          divisors_zero eq_iff_diff_eq_0 pq_def zero_less_mult_pos zero_less_mult_pos2)
    from poly_IVT[OF \<open>a<b\<close> this] 
    have "\<exists>x>a. x < b \<and> poly pq x = 0" .
    then show False using \<open>\<forall>x. a\<le>x \<and> x\<le>b \<longrightarrow> poly (p*q) x\<noteq>0\<close> \<open>a<b\<close> 
      apply (fold pq_def)
      by auto
  qed
  finally show ?thesis .
qed

(*
lemma cross_alt_clear_n:
  assumes "coprime p q"
  shows "cross_alt p q a b = cross_alt 1 (p*q) a b"
proof -
  have "\<bar>sign (poly p a) - sign (poly q a)\<bar>  = \<bar>1 - sign (poly p a) * sign (poly q a)\<bar>"
  proof (cases "poly p a=0 \<and> poly q a=0")
    case True
    then have False using assms using coprime_poly_0 by blast
    then show ?thesis by auto
  next
    case False
    then show ?thesis 
      unfolding Sturm_Tarski.sign_def
      by force
  qed
  moreover have "\<bar>sign (poly p b) - sign (poly q b)\<bar>  = \<bar>1 - sign (poly p b) * sign (poly q b)\<bar>"
  proof (cases "poly p b=0 \<and> poly q b=0")
    case True
    then have False using assms using coprime_poly_0 by blast
    then show ?thesis by auto
  next
    case False
    then show ?thesis 
      unfolding Sturm_Tarski.sign_def
      by force
  qed  
  ultimately show ?thesis
    by (simp add: cross_alt_def sign_times)
qed   
*)

lemma cross_alt_linear_comp:
  fixes b c::real
  defines "h \<equiv> (\<lambda>p. pcompose p [:b,c:])"
  shows "cross_alt (h p) (h q) lb ub = cross_alt p q (c * lb + b) (c * ub + b)"
  unfolding cross_alt_def  h_def
  by (subst (1 2) psign_diff_linear_comp;simp)

subsection \<open>Alternative sign variation sequencse\<close>  
  
fun changes_alt:: "('a ::linordered_idom) list \<Rightarrow> int" where
  "changes_alt [] = 0"|
  "changes_alt [_] = 0" |
  "changes_alt (x1#x2#xs) = abs(sign x1 - sign x2) + changes_alt (x2#xs)"  
  
definition changes_alt_poly_at::"('a ::linordered_idom) poly list \<Rightarrow> 'a \<Rightarrow> int" where
  "changes_alt_poly_at ps a= changes_alt (map (\<lambda>p. poly p a) ps)"

definition changes_alt_itv_smods:: "real \<Rightarrow> real \<Rightarrow>real poly \<Rightarrow> real poly \<Rightarrow>  int" where
  "changes_alt_itv_smods a b p q= (let ps= smods p q 
                                    in changes_alt_poly_at ps a - changes_alt_poly_at ps b)"  
 
lemma changes_alt_itv_smods_rec:
  assumes "a<b" "coprime p q" 
  shows "changes_alt_itv_smods a b p q  = cross_alt p q a b + changes_alt_itv_smods a b q (-(p mod q))"
proof (cases "p = 0 \<or> q = 0 \<or> q dvd p")
  case True
  moreover have "p=0 \<or> q=0 \<Longrightarrow> ?thesis"
    using cross_alt_coprime_0 
    unfolding changes_alt_itv_smods_def changes_alt_poly_at_def by fastforce
  moreover have "\<lbrakk>p\<noteq>0;q\<noteq>0;p mod q = 0\<rbrakk> \<Longrightarrow> ?thesis"  
    unfolding changes_alt_itv_smods_def changes_alt_poly_at_def cross_alt_def
      psign_diff_alt[OF \<open>coprime p q\<close>]
    by (simp add:sign_times)
  ultimately show ?thesis 
    by auto (auto elim: dvdE)
next
  case False
  hence "p\<noteq>0" "q\<noteq>0" "p mod q\<noteq>0" by auto
  then obtain ps where ps:"smods p q=p#q#-(p mod q)#ps" "smods q (-(p mod q)) = q#-(p mod q)#ps"
    by auto
  define changes_diff where "changes_diff\<equiv>\<lambda>x. changes_alt_poly_at (p#q#-(p mod q)#ps) x 
    - changes_alt_poly_at (q#-(p mod q)#ps) x"
  have "changes_diff a - changes_diff b=cross_alt p q a b" 
    unfolding changes_diff_def changes_alt_poly_at_def cross_alt_def 
        psign_diff_alt[OF \<open>coprime p q\<close>]
    by simp 
  thus ?thesis unfolding changes_alt_itv_smods_def changes_diff_def changes_alt_poly_at_def ps 
    by force
qed 
  
subsection \<open>jumpF on polynomials\<close>

definition jumpF_polyR:: "real poly \<Rightarrow> real poly \<Rightarrow> real \<Rightarrow> real" where
  "jumpF_polyR q p a = jumpF (\<lambda>x. poly q x / poly p x) (at_right a)"
  
definition jumpF_polyL:: "real poly \<Rightarrow> real poly \<Rightarrow> real \<Rightarrow> real" where
  "jumpF_polyL q p a = jumpF (\<lambda>x. poly q x / poly p x) (at_left a)"

definition jumpF_poly_top:: "real poly \<Rightarrow> real poly \<Rightarrow> real" where
  "jumpF_poly_top q p = jumpF (\<lambda>x. poly q x / poly p x) at_top"

definition jumpF_poly_bot:: "real poly \<Rightarrow> real poly \<Rightarrow> real" where
  "jumpF_poly_bot q p = jumpF (\<lambda>x. poly q x / poly p x) at_bot"

  
lemma jumpF_polyR_0[simp]: "jumpF_polyR 0 p a = 0" "jumpF_polyR q 0 a = 0" 
  unfolding jumpF_polyR_def by auto
    
lemma jumpF_polyL_0[simp]: "jumpF_polyL 0 p a = 0" "jumpF_polyL q 0 a = 0" 
  unfolding jumpF_polyL_def by auto
    
lemma jumpF_polyR_mult_cancel:
  assumes "p'\<noteq>0"
  shows "jumpF_polyR (p' * q) (p' * p) a = jumpF_polyR q p a"
unfolding jumpF_polyR_def
proof (rule jumpF_cong)
  obtain ub where "a < ub" "\<forall>z. a < z \<and> z \<le> ub \<longrightarrow> poly p' z \<noteq> 0"
    using next_non_root_interval[OF \<open>p'\<noteq>0\<close>,of a] by auto
  then show "\<forall>\<^sub>F x in at_right a. poly (p' * q) x / poly (p' * p) x = poly q x / poly p x"
    apply (unfold eventually_at_right)
    apply (intro exI[where x=ub])
    by auto
qed simp
  
lemma jumpF_polyL_mult_cancel:
  assumes "p'\<noteq>0"
  shows "jumpF_polyL (p' * q) (p' * p) a = jumpF_polyL q p a"
unfolding jumpF_polyL_def
proof (rule jumpF_cong)
  obtain lb where "lb < a" "\<forall>z. lb \<le> z \<and> z < a \<longrightarrow> poly p' z \<noteq> 0 "
    using last_non_root_interval[OF \<open>p'\<noteq>0\<close>,of a] by auto
  then show "\<forall>\<^sub>F x in at_left a. poly (p' * q) x / poly (p' * p) x = poly q x / poly p x"
    apply (unfold eventually_at_left)
    apply (intro exI[where x=lb])
    by auto
qed simp  
      
lemma jumpF_poly_noroot: 
  assumes "poly p a\<noteq>0"
  shows "jumpF_polyL q p a = 0" "jumpF_polyR q p a = 0" 
  subgoal unfolding jumpF_polyL_def using assms
    apply (intro jumpF_not_infinity)
    by (auto intro!:continuous_intros)  
  subgoal unfolding jumpF_polyR_def using assms
    apply (intro jumpF_not_infinity)
    by (auto intro!:continuous_intros)
  done

lemma jumpF_polyR_coprime': 
  assumes "poly p x\<noteq>0 \<or> poly q x\<noteq>0"
  shows "jumpF_polyR q p x = (if p \<noteq> 0 \<and> q \<noteq> 0 \<and> poly p x=0 then 
                                if sign_r_pos p x \<longleftrightarrow> poly q x>0 then 1/2 else - 1/2 else 0)"
proof (cases "p=0 \<or> q=0 \<or> poly p x\<noteq>0")
  case True
  then show ?thesis using jumpF_poly_noroot by fastforce
next
  case False
  then have asm:"p\<noteq>0" "q\<noteq>0" "poly p x=0" by auto  
  then have "poly q x\<noteq>0" using assms using coprime_poly_0 by blast
  have ?thesis when "sign_r_pos p x \<longleftrightarrow> poly q x>0"
  proof -
    have "(poly p has_sgnx sgn (poly q x)) (at_right x)"
      by (smt (z3) False \<open>poly q x \<noteq> 0\<close> has_sgnx_imp_sgnx 
          poly_has_sgnx_values(2) sgn_real_def sign_r_pos_sgnx_iff that 
          trivial_limit_at_right_real)
    then have "LIM x at_right x. poly q x / poly p x :> at_top"    
      apply (subst filterlim_divide_at_bot_at_top_iff[of _ "poly q x"])
      apply (auto simp add:\<open>poly q x\<noteq>0\<close>)
      by (metis asm(3) poly_tendsto(3))
    then have "jumpF_polyR q p x = 1/2"
      unfolding jumpF_polyR_def jumpF_def by auto
    then show ?thesis using that False by auto
  qed
  moreover have ?thesis when "\<not> (sign_r_pos p x \<longleftrightarrow> poly q x>0)"
  proof -
    have "(poly p has_sgnx - sgn (poly q x)) (at_right x)"
    proof -
      have "(0::real) < 1 \<or> \<not> (1::real) < 0 \<and> sign_r_pos p x 
          \<or> (poly p has_sgnx - sgn (poly q x)) (at_right x)"
        by simp
      then show ?thesis
        by (metis (no_types) False \<open>poly q x \<noteq> 0\<close> add.inverse_inverse has_sgnx_imp_sgnx 
            neg_less_0_iff_less poly_has_sgnx_values(2) sgn_if sgn_less sign_r_pos_sgnx_iff 
            that trivial_limit_at_right_real)
    qed
    then have "LIM x at_right x. poly q x / poly p x :> at_bot"    
      apply (subst filterlim_divide_at_bot_at_top_iff[of _ "poly q x"])
      apply (auto simp add:\<open>poly q x\<noteq>0\<close>)
      by (metis asm(3) poly_tendsto(3)) 
    then have "jumpF_polyR q p x = - 1/2"
      unfolding jumpF_polyR_def jumpF_def by auto
    then show ?thesis using that False by auto  
  qed
  ultimately show ?thesis by auto
qed

lemma jumpF_polyR_coprime:
  assumes "coprime p q"
  shows "jumpF_polyR q p x = (if p \<noteq> 0 \<and> q \<noteq> 0 \<and> poly p x=0 then 
                                if sign_r_pos p x \<longleftrightarrow> poly q x>0 then 1/2 else - 1/2 else 0)"
  apply (rule jumpF_polyR_coprime')
  using assms coprime_poly_0 by blast

lemma jumpF_polyL_coprime':
  assumes "poly p x\<noteq>0 \<or> poly q x\<noteq>0"
  shows "jumpF_polyL q p x = (if p \<noteq> 0 \<and> q \<noteq> 0 \<and> poly p x=0 then 
                if even (order x p) \<longleftrightarrow> sign_r_pos p x \<longleftrightarrow> poly q x>0 then 1/2 else - 1/2 else 0)"  
proof (cases "p=0 \<or> q=0 \<or> poly p x\<noteq>0")
  case True
  then show ?thesis using jumpF_poly_noroot by fastforce
next  
  case False
  then have asm:"p\<noteq>0" "q\<noteq>0" "poly p x=0" by auto  
  then have "poly q x\<noteq>0" using assms using coprime_poly_0 by blast
  have ?thesis when "even (order x p) \<longleftrightarrow> sign_r_pos p x \<longleftrightarrow> poly q x>0"
  proof -
    consider (lt) "poly q x>0" | (gt) " poly q x<0" using \<open>poly q x\<noteq>0\<close> by linarith
    then have "sgnx (poly p) (at_left x) = sgn (poly q x)"
      apply cases
      subgoal using that sign_r_pos_sgnx_iff poly_sgnx_values[OF \<open>p\<noteq>0\<close>,of x]
        apply (subst poly_sgnx_left_right[OF \<open>p\<noteq>0\<close>])
        by auto
      subgoal using that sign_r_pos_sgnx_iff poly_sgnx_values[OF \<open>p\<noteq>0\<close>,of x]
        apply (subst poly_sgnx_left_right[OF \<open>p\<noteq>0\<close>])
        by auto
      done
    then have "(poly p has_sgnx sgn (poly q x)) (at_left x)"
      by (metis sgnx_able_poly(2) sgnx_able_sgnx)
    then have "LIM x at_left x. poly q x / poly p x :> at_top"    
      apply (subst filterlim_divide_at_bot_at_top_iff[of _ "poly q x"])
      apply (auto simp add:\<open>poly q x\<noteq>0\<close>)
      by (metis asm(3) poly_tendsto(2))   
    then have "jumpF_polyL q p x = 1/2"
      unfolding jumpF_polyL_def jumpF_def by auto
    then show ?thesis using that False by auto
  qed
  moreover have ?thesis when "\<not> (even (order x p) \<longleftrightarrow> sign_r_pos p x \<longleftrightarrow> poly q x>0)"
  proof -
    consider (lt) "poly q x>0" | (gt) " poly q x<0" using \<open>poly q x\<noteq>0\<close> by linarith
    then have "sgnx (poly p) (at_left x) = - sgn (poly q x)"
      apply cases
      subgoal using that sign_r_pos_sgnx_iff poly_sgnx_values[OF \<open>p\<noteq>0\<close>,of x]
        apply (subst poly_sgnx_left_right[OF \<open>p\<noteq>0\<close>])
        by auto
      subgoal using that sign_r_pos_sgnx_iff poly_sgnx_values[OF \<open>p\<noteq>0\<close>,of x]
        apply (subst poly_sgnx_left_right[OF \<open>p\<noteq>0\<close>])
        by auto
      done
    then have "(poly p has_sgnx - sgn (poly q x)) (at_left x)"
      by (metis sgnx_able_poly(2) sgnx_able_sgnx)
    then have "LIM x at_left x. poly q x / poly p x :> at_bot"    
      apply (subst filterlim_divide_at_bot_at_top_iff[of _ "poly q x"])
      apply (auto simp add:\<open>poly q x\<noteq>0\<close>)
      by (metis asm(3) poly_tendsto(2))   
    then have "jumpF_polyL q p x = - 1/2"
      unfolding jumpF_polyL_def jumpF_def by auto
    then show ?thesis using that False by auto 
  qed
  ultimately show ?thesis by auto
qed

lemma jumpF_polyL_coprime:
  assumes "coprime p q"
  shows "jumpF_polyL q p x = (if p \<noteq> 0 \<and> q \<noteq> 0 \<and> poly p x=0 then 
                if even (order x p) \<longleftrightarrow> sign_r_pos p x \<longleftrightarrow> poly q x>0 then 1/2 else - 1/2 else 0)"  
  apply (rule jumpF_polyL_coprime')
  using assms coprime_poly_0 by blast
    
lemma jumpF_times:
  assumes tendsto:"(f \<longlongrightarrow> c) F" and "c\<noteq>0" "F\<noteq>bot"
  shows "jumpF (\<lambda>x. f x * g x) F = sgn c * jumpF g F"  
proof -
  have "c>0 \<or> c<0" using \<open>c\<noteq>0\<close> by auto
  moreover have ?thesis when "c>0"
  proof -
    note filterlim_tendsto_pos_mult_at_top_iff[OF tendsto \<open>c>0\<close>,of g]
    moreover note filterlim_tendsto_pos_mult_at_bot_iff[OF tendsto \<open>c>0\<close>,of g]
    moreover have "sgn c = 1" using \<open>c>0\<close> by auto
    ultimately show ?thesis unfolding jumpF_def by auto
  qed
  moreover have ?thesis when "c<0"
  proof -
    define atbot where "atbot = filterlim g at_bot F"
    define attop where "attop = filterlim g at_top F"    
    have "jumpF (\<lambda>x. f x * g x) F = (if atbot then 1 / 2 else if attop then - 1 / 2 else 0)"
    proof -
      note filterlim_tendsto_neg_mult_at_top_iff[OF tendsto \<open>c<0\<close>,of g]
      moreover note filterlim_tendsto_neg_mult_at_bot_iff[OF tendsto \<open>c<0\<close>,of g]
      ultimately show ?thesis unfolding jumpF_def atbot_def attop_def by auto
    qed
    also have "... = - (if attop then 1 / 2 else if atbot then - 1 / 2 else 0)"
    proof -
      have False when atbot attop
        using filterlim_at_top_at_bot[OF _ _ \<open>F\<noteq>bot\<close>] that unfolding atbot_def attop_def by auto
      then show ?thesis by fastforce    
    qed
    also have "... = sgn c * jumpF g F"
      using \<open>c<0\<close> unfolding jumpF_def attop_def atbot_def by auto
    finally show ?thesis .
  qed
  ultimately show ?thesis by auto
qed

lemma jumpF_polyR_inverse_add:
  assumes "coprime p q"
  shows "jumpF_polyR q p x + jumpF_polyR p q x = jumpF_polyR 1 (q*p) x"
proof (cases "p=0 \<or> q=0")
  case True
  then show ?thesis by auto
next
  case False
  have jumpF_add:
    "jumpF_polyR q p x= jumpF_polyR 1 (q*p) x" when "poly p x=0" "coprime p q" for p q
  proof (cases "p=0")
    case True
    then show ?thesis by auto
  next
    case False
    have "poly q x\<noteq>0" using that coprime_poly_0 by blast
    then have "q\<noteq>0" by auto
    moreover have "sign_r_pos p x = (0 < poly q x) \<longleftrightarrow> sign_r_pos (q * p) x"
      using sign_r_pos_mult[OF \<open>q\<noteq>0\<close> \<open>p\<noteq>0\<close>] sign_r_pos_rec[OF \<open>q\<noteq>0\<close>] \<open>poly q x\<noteq>0\<close>
      by auto
    ultimately show ?thesis using \<open>poly p x=0\<close>  
      unfolding jumpF_polyR_coprime[OF \<open>coprime p q\<close>,of x] jumpF_polyR_coprime[of "q*p" 1 x,simplified]
      by auto
  qed
  have False when "poly p x=0" "poly q x=0" 
    using \<open>coprime p q\<close> that coprime_poly_0 by blast
  moreover have ?thesis when "poly p x=0" "poly q x\<noteq>0" 
  proof -
    have "jumpF_polyR p q x = 0" using jumpF_poly_noroot[OF \<open>poly q x\<noteq>0\<close>] by auto
    then show ?thesis using jumpF_add[OF \<open>poly p x=0\<close> \<open>coprime p q\<close>] by auto
  qed
  moreover have ?thesis when "poly p x\<noteq>0" "poly q x=0" 
  proof -
    have "jumpF_polyR q p x = 0" using jumpF_poly_noroot[OF \<open>poly p x\<noteq>0\<close>] by auto
    then show ?thesis using jumpF_add[OF \<open>poly q x=0\<close>,of p] \<open>coprime p q\<close> 
      by (simp add: ac_simps)
  qed  
  moreover have ?thesis when "poly p x\<noteq>0" "poly q x\<noteq>0" 
    by (simp add: jumpF_poly_noroot(2) that(1) that(2))
  ultimately show ?thesis by auto
qed

lemma jumpF_polyL_inverse_add:
  assumes "coprime p q"
  shows "jumpF_polyL q p x + jumpF_polyL p q x = jumpF_polyL 1 (q*p) x"  
proof (cases "p=0 \<or> q=0")
  case True
  then show ?thesis by auto
next
  case False
  have jumpF_add:
    "jumpF_polyL q p x= jumpF_polyL 1 (q*p) x" when "poly p x=0" "coprime p q" for p q
  proof (cases "p=0")
    case True
    then show ?thesis by auto
  next
    case False
    have "poly q x\<noteq>0" using that coprime_poly_0 by blast
    then have "q\<noteq>0" by auto
    moreover have "sign_r_pos p x = (0 < poly q x) \<longleftrightarrow> sign_r_pos (q * p) x"
      using sign_r_pos_mult[OF \<open>q\<noteq>0\<close> \<open>p\<noteq>0\<close>] sign_r_pos_rec[OF \<open>q\<noteq>0\<close>] \<open>poly q x\<noteq>0\<close>
      by auto
    moreover have "order x p = order x (q * p)" 
      by (metis \<open>poly q x \<noteq> 0\<close> add_cancel_right_left divisors_zero order_mult order_root)
    ultimately show ?thesis using \<open>poly p x=0\<close>  
      unfolding jumpF_polyL_coprime[OF \<open>coprime p q\<close>,of x] jumpF_polyL_coprime[of "q*p" 1 x,simplified]
      by auto
  qed
  have False when "poly p x=0" "poly q x=0" 
    using \<open>coprime p q\<close> that coprime_poly_0 by blast
  moreover have ?thesis when "poly p x=0" "poly q x\<noteq>0" 
  proof -
    have "jumpF_polyL p q x = 0" using jumpF_poly_noroot[OF \<open>poly q x\<noteq>0\<close>] by auto
    then show ?thesis using jumpF_add[OF \<open>poly p x=0\<close> \<open>coprime p q\<close>] by auto
  qed
  moreover have ?thesis when "poly p x\<noteq>0" "poly q x=0" 
  proof -
    have "jumpF_polyL q p x = 0" using jumpF_poly_noroot[OF \<open>poly p x\<noteq>0\<close>] by auto
    then show ?thesis using jumpF_add[OF \<open>poly q x=0\<close>,of p] \<open>coprime p q\<close> 
      by (simp add: ac_simps)
  qed  
  moreover have ?thesis when "poly p x\<noteq>0" "poly q x\<noteq>0" 
    by (simp add: jumpF_poly_noroot that(1) that(2))
  ultimately show ?thesis by auto
qed    
  

lemma jumpF_polyL_smult_1:
  "jumpF_polyL (smult c q) p x = sgn c * jumpF_polyL q p x"
proof (cases "c=0")
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis 
    unfolding jumpF_polyL_def 
    apply (subst jumpF_times[of "\<lambda>_. c",symmetric])
    by auto
qed  

lemma jumpF_polyR_smult_1:
  "jumpF_polyR (smult c q) p x = sgn c * jumpF_polyR q p x"
proof (cases "c=0")
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis
    unfolding jumpF_polyR_def using False 
    apply (subst jumpF_times[of "\<lambda>_. c",symmetric])
    by auto
qed  
  

lemma
  shows jumpF_polyR_mod:"jumpF_polyR q p x = jumpF_polyR (q mod p) p x" and
        jumpF_polyL_mod:"jumpF_polyL q p x = jumpF_polyL (q mod p) p x"
proof -
  define f where "f=(\<lambda>x. poly (q div p) x)"
  define g where "g=(\<lambda>x. poly (q mod p) x / poly p x)"
  have jumpF_eq:"jumpF (\<lambda>x. poly q x / poly p x) (at y within S) = jumpF g (at y within S)" 
    when "p\<noteq>0" for y S
  proof -
    let ?F = "at y within S"
    have "\<forall>\<^sub>F x in at y within S. poly p x \<noteq> 0" 
      using eventually_poly_nz_at_within[OF \<open>p\<noteq>0\<close>,of y S] .
    then have "eventually (\<lambda>x. (poly q x / poly p x) = (f x+ g x)) ?F"
    proof (rule eventually_mono)
      fix x
      assume P: "poly p x \<noteq> 0"
      have "poly q x = poly (q div p * p + q mod p) x"
        by simp
      also have "\<dots> = f x * poly p x + poly (q mod p) x"
        by (simp only: poly_add poly_mult f_def g_def)
      moreover have "poly (q mod p) x = g x * poly p x"
        using P by (simp add: g_def)
      ultimately show "poly q x / poly p x = f x + g x"
        using P by simp
    qed
    then have "jumpF (\<lambda>x. poly q x / poly p x) ?F = jumpF (\<lambda>x. f x+ g x) ?F"
      by (intro jumpF_cong,auto)
    also have "... = jumpF g ?F"  
    proof -
      have "(f \<longlongrightarrow> f y) (at y within S)"
        unfolding f_def by (intro tendsto_intros)  
      from filterlim_tendsto_add_at_bot_iff[OF this,of g] filterlim_tendsto_add_at_top_iff[OF this,of g] 
      show ?thesis unfolding jumpF_def by auto
    qed
    finally show ?thesis .
  qed
  show "jumpF_polyR q p x = jumpF_polyR (q mod p) p x"
    apply (cases "p=0")
    subgoal by auto
    subgoal using jumpF_eq unfolding g_def jumpF_polyR_def by auto
    done
  show "jumpF_polyL q p x = jumpF_polyL (q mod p) p x"
    apply (cases "p=0")
    subgoal by auto
    subgoal using jumpF_eq unfolding g_def jumpF_polyL_def by auto
    done  
qed 

lemma 
  assumes "order x p \<le> order x r"
  shows jumpF_polyR_order_leq: "jumpF_polyR (r+q) p x = jumpF_polyR q p x"
    and jumpF_polyL_order_leq: "jumpF_polyL (r+q) p x = jumpF_polyL q p x"
proof -
  define f g h where "f=(\<lambda>x. poly (q + r) x / poly p x)"
                    and "g=(\<lambda>x. poly q x / poly p x)"
                    and "h=(\<lambda>x. poly r x / poly p x)"

  have "\<exists>c. h \<midarrow>x\<rightarrow> c" if "p\<noteq>0" "r\<noteq>0"
  proof -
    define xo where "xo=[:- x, 1:] ^ order x p"
    obtain p' where "p = xo * p'" "\<not> [:- x, 1:] dvd p'"
      using order_decomp[OF \<open>p\<noteq>0\<close>,of x] unfolding xo_def by auto
    define r' where "r'= r div xo"
    define h' where "h' = (\<lambda>x. poly r' x/ poly p' x)"
    
    have "\<forall>\<^sub>F x in at x. h x = h' x" 
    proof -
      obtain S where "open S" "x\<in>S" by blast
      moreover have " h w = h' w" if "w\<in>S" "w\<noteq>x" for w 
      proof -
        have "r=xo * r'"
        proof -
          have "xo dvd r"
            unfolding xo_def using \<open>r\<noteq>0\<close> assms
            by (subst order_divides) simp
          then show ?thesis unfolding r'_def by simp
        qed
        moreover have "poly xo w\<noteq>0" 
          unfolding xo_def using \<open>w\<noteq>x\<close> by simp
        moreover note \<open>p = xo * p'\<close>
        ultimately show ?thesis
          unfolding h_def h'_def by auto
      qed
      ultimately show ?thesis
        unfolding eventually_at_topological by auto
    qed
    moreover have "h'\<midarrow>x\<rightarrow> h' x" 
    proof -
      have "poly p' x\<noteq>0" 
        using \<open>\<not> [:- x, 1:] dvd p'\<close> poly_eq_0_iff_dvd by blast
      then show ?thesis
        unfolding h'_def
        by (auto intro!:tendsto_eq_intros)
    qed
    ultimately have "h \<midarrow>x\<rightarrow> h' x" 
      using tendsto_cong by auto
    then show ?thesis by auto
  qed
  then obtain c where left:"(h \<longlongrightarrow> c) (at_left x)"
                  and right:"(h \<longlongrightarrow> c) (at_right x)"
                if "p\<noteq>0" "r\<noteq>0"
    unfolding filterlim_at_split by auto

  show "jumpF_polyR (r+q) p x = jumpF_polyR q p x"
  proof (cases "p=0 \<or> r=0")
    case False
    have "jumpF_polyR (r+q) p x = 
          (if filterlim (\<lambda>x. h x + g x) at_top (at_right x) 
          then 1 / 2
          else if filterlim (\<lambda>x. h x + g x) at_bot (at_right x) 
          then - 1 / 2 else 0)"
      unfolding jumpF_polyR_def jumpF_def g_def h_def
      by (simp add:poly_add add_divide_distrib)
    also have "... = 
        (if filterlim g at_top (at_right x) then 1 / 2
            else if filterlim g at_bot (at_right x) then - 1 / 2 else 0)"
      using filterlim_tendsto_add_at_top_iff[OF right]
        filterlim_tendsto_add_at_bot_iff[OF right] False
      by simp
    also have "... = jumpF_polyR q p x"
      unfolding jumpF_polyR_def jumpF_def g_def by simp
    finally show "jumpF_polyR (r + q) p x = jumpF_polyR q p x" .
  qed auto

  show "jumpF_polyL (r+q) p x = jumpF_polyL q p x"
  proof (cases "p=0 \<or> r=0")
    case False
    have "jumpF_polyL (r+q) p x = 
          (if filterlim (\<lambda>x. h x + g x) at_top (at_left x) 
          then 1 / 2
          else if filterlim (\<lambda>x. h x + g x) at_bot (at_left x) 
          then - 1 / 2 else 0)"
      unfolding jumpF_polyL_def jumpF_def g_def h_def
      by (simp add:poly_add add_divide_distrib)
    also have "... = 
        (if filterlim g at_top (at_left x) then 1 / 2
            else if filterlim g at_bot (at_left x) then - 1 / 2 else 0)"
      using filterlim_tendsto_add_at_top_iff[OF left]
        filterlim_tendsto_add_at_bot_iff[OF left] False
      by simp
    also have "... = jumpF_polyL q p x"
      unfolding jumpF_polyL_def jumpF_def g_def by simp
    finally show "jumpF_polyL (r + q) p x = jumpF_polyL q p x" .
  qed auto
qed

lemma 
  assumes "order x q < order x r" "q\<noteq>0"
  shows jumpF_polyR_order_le:"jumpF_polyR (r+q) p x = jumpF_polyR q p x"
    and jumpF_polyL_order_le:"jumpF_polyL (r+q) p x = jumpF_polyL q p x"
proof -
  have "jumpF_polyR (r+q) p x = jumpF_polyR q p x"
    "jumpF_polyL (r+q) p x = jumpF_polyL q p x"
    if "p=0 \<or> r=0 \<or> order x p \<le> order x r" 
    using jumpF_polyR_order_leq jumpF_polyL_order_leq that by auto
  moreover have 
    "jumpF_polyR (r+q) p x = jumpF_polyR q p x"
    "jumpF_polyL (r+q) p x = jumpF_polyL q p x"
    if "p\<noteq>0" "r\<noteq>0" "order x p > order x r"
  proof -
    define xo where "xo=[:- x, 1:] ^ order x q"
    have [simp]:"xo\<noteq>0" unfolding xo_def by simp
    have xo_q:"order x xo = order x q"
      unfolding xo_def by (meson order_power_n_n)
    obtain q' where q:"q = xo * q'" and "\<not> [:- x, 1:] dvd q'"
      using order_decomp[OF \<open>q\<noteq>0\<close>,of x] unfolding xo_def by auto
    from this(2)
    have "poly q' x\<noteq>0" using poly_eq_0_iff_dvd by blast
    define p' r' where "p'= p div xo" and "r' = r div xo"
    have p:"p = xo * p'" 
    proof -
      have "order x q < order x p"
        using assms(1) less_trans that(3) by blast
      then have "xo dvd p"
        unfolding xo_def by (metis less_or_eq_imp_le order_divides)
      then show ?thesis by (simp add: p'_def)
    qed
    have r:"r = xo * r'" 
    proof -
      have "xo dvd r"
        unfolding xo_def by (meson assms(1) less_or_eq_imp_le order_divides)
      then show ?thesis by (simp add: r'_def)
    qed
    have "poly r' x=0"
    proof -
      have "order x r = order x xo + order x r'"
        unfolding r using \<open>r \<noteq> 0\<close> r order_mult by blast
      with xo_q have "order x r' = order x r - order x q"
        by auto
      then have "order x r' >0"
        using \<open>order x r < order x p\<close> assms(1) by linarith
      then show "poly r' x=0" using order_root by blast
    qed
    have "poly p' x=0"
    proof -
      have "order x p = order x xo + order x p'"
        unfolding p using \<open>p \<noteq> 0\<close> p order_mult by blast
      with xo_q have "order x p' = order x p - order x q"
        by auto
      then have "order x p' >0"
        using \<open>order x r < order x p\<close> assms(1) by linarith
      then show "poly p' x=0" using order_root by blast
    qed
  
    have "jumpF_polyL (r+q) p x = jumpF_polyL (xo * (r'+q')) (xo*p') x"
      unfolding p q r by (simp add:algebra_simps)
    also have "... = jumpF_polyL (r'+q') p' x"
      by (rule jumpF_polyL_mult_cancel) simp
    also have "... = (if even (order x p') = (sign_r_pos p' x 
          = (0 < poly (r' + q') x)) then 1 / 2 else - 1 / 2)"
    proof -
      have "poly (r' + q') x \<noteq> 0"
        using \<open>poly q' x\<noteq>0\<close> \<open>poly r' x = 0\<close> by auto
      then show ?thesis
        apply (subst jumpF_polyL_coprime')
        subgoal by simp
        subgoal by (smt (z3) \<open>p \<noteq> 0\<close> \<open>poly p' x = 0\<close> mult.commute 
              mult_zero_left p poly_0)
        done
    qed
    also have "... = (if even (order x p') = (sign_r_pos p' x 
          = (0 < poly q' x)) then 1 / 2 else - 1 / 2)"
      using \<open>poly r' x=0\<close> by auto
    also have "... = jumpF_polyL q' p' x"
      apply (subst jumpF_polyL_coprime')
      subgoal using \<open>poly q' x \<noteq> 0\<close> by blast
      subgoal using \<open>p \<noteq> 0\<close> \<open>poly p' x = 0\<close> assms(2) p q by simp
      done
    also have "... = jumpF_polyL q p x"
      unfolding p q by (subst jumpF_polyL_mult_cancel) simp_all
    finally show "jumpF_polyL (r+q) p x = jumpF_polyL q p x" .

    have "jumpF_polyR (r+q) p x = jumpF_polyR (xo * (r'+q')) (xo*p') x"
      unfolding p q r by (simp add:algebra_simps)
    also have "... = jumpF_polyR (r'+q') p' x"
      by (rule jumpF_polyR_mult_cancel) simp
    also have "... = (if sign_r_pos p' x = (0 < poly (r' + q') x) 
      then 1 / 2 else - 1 / 2)"
    proof -
      have "poly (r' + q') x \<noteq> 0"
        using \<open>poly q' x\<noteq>0\<close> \<open>poly r' x = 0\<close> by auto
      then show ?thesis
        apply (subst jumpF_polyR_coprime')
        subgoal by simp
        subgoal 
          by (smt (z3) \<open>p \<noteq> 0\<close> \<open>poly p' x = 0\<close> mult.commute 
              mult_zero_left p poly_0)
        done
    qed
    also have "... = (if sign_r_pos p' x = (0 < poly q' x) 
      then 1 / 2 else - 1 / 2)"
      using \<open>poly r' x=0\<close> by auto
    also have "... = jumpF_polyR q' p' x"
      apply (subst jumpF_polyR_coprime')
      subgoal using \<open>poly q' x \<noteq> 0\<close> by blast
      subgoal using \<open>p \<noteq> 0\<close> \<open>poly p' x = 0\<close> assms(2) p q by force
      done
    also have "... = jumpF_polyR q p x"
      unfolding p q by (subst jumpF_polyR_mult_cancel) simp_all
    finally show "jumpF_polyR (r+q) p x = jumpF_polyR q p x" .
  qed
  ultimately show 
      "jumpF_polyR (r+q) p x = jumpF_polyR q p x"
      "jumpF_polyL (r+q) p x = jumpF_polyL q p x" 
    by force +
qed

lemma jumpF_poly_top_0[simp]: "jumpF_poly_top 0 p = 0" "jumpF_poly_top q 0 = 0"
  unfolding jumpF_poly_top_def by auto

lemma jumpF_poly_bot_0[simp]: "jumpF_poly_bot 0 p = 0" "jumpF_poly_bot q 0 = 0"
  unfolding jumpF_poly_bot_def by auto

lemma jumpF_poly_top_code:
  "jumpF_poly_top q p = (if p\<noteq>0 \<and> q\<noteq>0 \<and> degree q>degree p then 
          if sgn_pos_inf q * sgn_pos_inf p > 0 then 1/2 else -1/2 else 0)"
proof (cases "p\<noteq>0 \<and> q\<noteq>0 \<and> degree q>degree p")
  case True
  have ?thesis when "sgn_pos_inf q * sgn_pos_inf p > 0"
  proof -
    have "LIM x at_top. poly q x / poly p x :> at_top"
      using poly_divide_filterlim_at_top[of p q] True that by auto
    then have "jumpF (\<lambda>x. poly q x / poly p x) at_top = 1/2"
      unfolding jumpF_def by auto
    then show ?thesis unfolding jumpF_poly_top_def using that True by auto
  qed
  moreover have ?thesis when "\<not> sgn_pos_inf q * sgn_pos_inf p > 0"
  proof -
    have "LIM x at_top. poly q x / poly p x :> at_bot"
      using poly_divide_filterlim_at_top[of p q] True that by auto
    then have "jumpF (\<lambda>x. poly q x / poly p x) at_top = - 1/2"
      unfolding jumpF_def by auto
    then show ?thesis unfolding jumpF_poly_top_def using that True by auto
  qed
  ultimately show ?thesis by auto
next
  case False
  define P where "P= (\<not> (LIM x at_top. poly q x / poly p x :> at_bot) 
                      \<and> \<not> (LIM x at_top. poly q x / poly p x :> at_top))"
  have P when "p=0 \<or> q=0"
    unfolding P_def using that 
    by (auto elim!:filterlim_at_bot_nhds filterlim_at_top_nhds)
  moreover have P when "p\<noteq>0" "q\<noteq>0" "degree p> degree q"
  proof -
    have "LIM x at_top. poly q x / poly p x :> at 0"
      using poly_divide_filterlim_at_top[OF that(1,2)] that(3) by auto
    then show ?thesis unfolding P_def 
      by (auto elim!:filterlim_at_bot_nhds filterlim_at_top_nhds simp:filterlim_at)
  qed 
  moreover have P when "p\<noteq>0" "q\<noteq>0" "degree p = degree q"
  proof -
    have "((\<lambda>x. poly q x / poly p x) \<longlongrightarrow> lead_coeff q / lead_coeff p) at_top"
      using poly_divide_filterlim_at_top[OF that(1,2)] using that by auto
    then show ?thesis unfolding P_def 
      by (auto elim!:filterlim_at_bot_nhds filterlim_at_top_nhds)
  qed
  ultimately have P using False by fastforce
  then have "jumpF (\<lambda>x. poly q x / poly p x) at_top = 0"
    unfolding jumpF_def P_def by auto
  then show ?thesis unfolding jumpF_poly_top_def using False by presburger
qed

lemma jumpF_poly_bot_code:
  "jumpF_poly_bot q p = (if p\<noteq>0 \<and> q\<noteq>0 \<and> degree q>degree p then 
          if sgn_neg_inf q * sgn_neg_inf p > 0 then 1/2 else -1/2 else 0)"
proof (cases "p\<noteq>0 \<and> q\<noteq>0 \<and> degree q>degree p")
  case True
  have ?thesis when "sgn_neg_inf q * sgn_neg_inf p > 0"
  proof -
    have "LIM x at_bot. poly q x / poly p x :> at_top"
      using poly_divide_filterlim_at_bot[of p q] True that by auto
    then have "jumpF (\<lambda>x. poly q x / poly p x) at_bot = 1/2"
      unfolding jumpF_def by auto
    then show ?thesis unfolding jumpF_poly_bot_def using that True by auto
  qed
  moreover have ?thesis when "\<not> sgn_neg_inf q * sgn_neg_inf p > 0"
  proof -
    have "LIM x at_bot. poly q x / poly p x :> at_bot"
      using poly_divide_filterlim_at_bot[of p q] True that by auto
    then have "jumpF (\<lambda>x. poly q x / poly p x) at_bot = - 1/2"
      unfolding jumpF_def by auto
    then show ?thesis unfolding jumpF_poly_bot_def using that True by auto
  qed
  ultimately show ?thesis by auto
next
  case False
  define P where "P= (\<not> (LIM x at_bot. poly q x / poly p x :> at_bot) 
                      \<and> \<not> (LIM x at_bot. poly q x / poly p x :> at_top))"
  have P when "p=0 \<or> q=0"
    unfolding P_def using that 
    by (auto elim!:filterlim_at_bot_nhds filterlim_at_top_nhds)
  moreover have P when "p\<noteq>0" "q\<noteq>0" "degree p> degree q"
  proof -
    have "LIM x at_bot. poly q x / poly p x :> at 0"
      using poly_divide_filterlim_at_bot[OF that(1,2)] that(3) by auto
    then show ?thesis unfolding P_def 
      by (auto elim!:filterlim_at_bot_nhds filterlim_at_top_nhds simp:filterlim_at)
  qed 
  moreover have P when "p\<noteq>0" "q\<noteq>0" "degree p = degree q"
  proof -
    have "((\<lambda>x. poly q x / poly p x) \<longlongrightarrow> lead_coeff q / lead_coeff p) at_bot"
      using poly_divide_filterlim_at_bot[OF that(1,2)] using that by auto
    then show ?thesis unfolding P_def 
      by (auto elim!:filterlim_at_bot_nhds filterlim_at_top_nhds)
  qed
  ultimately have P using False by fastforce
  then have "jumpF (\<lambda>x. poly q x / poly p x) at_bot = 0"
    unfolding jumpF_def P_def by auto
  then show ?thesis unfolding jumpF_poly_bot_def using False by presburger
qed

lemma jump_poly_jumpF_poly:
  shows "jump_poly q p x = jumpF_polyR q p x - jumpF_polyL q p x"
proof (cases "p=0 \<or> q=0")
  case True
  then show ?thesis by auto
next
  case False

  have *:"jump_poly q p x = jumpF_polyR q p x - jumpF_polyL q p x"
    if "coprime q p" for q p
  proof (cases "p=0 \<or> q=0 \<or> poly p x\<noteq>0")
    case True
    moreover have ?thesis if "p=0 \<or> q=0" using that by auto
    moreover have ?thesis if "poly p x\<noteq>0" 
      by (simp add: jumpF_poly_noroot(1) jumpF_poly_noroot(2) jump_poly_not_root that)
    ultimately show ?thesis by blast
  next
    case False
    then have " p \<noteq> 0" "q \<noteq> 0" "poly p x = 0" by auto

    have "jump_poly q p x = jump (\<lambda>x. poly q x / poly p x) x"
      using jump_jump_poly by simp 
    also have "real_of_int ... = jumpF (\<lambda>x. poly q x / poly p x) (at_right x) - 
                                    jumpF (\<lambda>x. poly q x / poly p x) (at_left x)"
    proof (rule jump_jumpF)
      have "poly q x\<noteq>0" by (meson False coprime_poly_0 that)
      then show "isCont (inverse \<circ> (\<lambda>x. poly q x / poly p x)) x"
        unfolding comp_def by simp
      define l where "l = sgnx (\<lambda>x. poly q x / poly p x) (at_left x)"
      define r where "r = sgnx (\<lambda>x. poly q x / poly p x) (at_right x)"
      show "((\<lambda>x. poly q x / poly p x) has_sgnx l) (at_left x)"
        unfolding l_def by (auto intro!:sgnx_intros sgnx_able_sgnx)
      show "((\<lambda>x. poly q x / poly p x) has_sgnx r) (at_right x)"
        unfolding r_def by (auto intro!:sgnx_intros sgnx_able_sgnx)
      show "l\<noteq>0" unfolding l_def
        apply (subst sgnx_divide)
        using poly_sgnx_values[OF \<open>p\<noteq>0\<close>, of x] poly_sgnx_values[OF \<open>q\<noteq>0\<close>, of x] 
        by auto
      show "r\<noteq>0" unfolding r_def
        apply (subst sgnx_divide)
        using poly_sgnx_values[OF \<open>p\<noteq>0\<close>, of x] poly_sgnx_values[OF \<open>q\<noteq>0\<close>, of x] 
        by auto
    qed
    also have "... = jumpF_polyR q p x - jumpF_polyL q p x"
      unfolding jumpF_polyR_def jumpF_polyL_def by simp
    finally show ?thesis .
  qed

  obtain p' q' g where pq:"p=g*p'" "q=g*q'" and "coprime q' p'" "g=gcd p q"
    using gcd_coprime_exists[of p q] 
    by (metis False coprime_commute gcd_coprime_exists gcd_eq_0_iff mult.commute)
  then have "g\<noteq>0" using False mult_zero_left by blast
  then have "jump_poly q p x = jump_poly q' p' x"
    unfolding pq using jump_poly_mult by auto
  also have "... = jumpF_polyR q' p' x - jumpF_polyL q' p' x"
    using *[OF \<open>coprime q' p'\<close>] .
  also have "... = jumpF_polyR q p x - jumpF_polyL q p x"
    unfolding pq using \<open>g\<noteq>0\<close> jumpF_polyL_mult_cancel jumpF_polyR_mult_cancel by auto
  finally show ?thesis .
qed
  
subsection \<open>The extended Cauchy index on polynomials\<close>

definition cindex_polyE:: "real \<Rightarrow> real \<Rightarrow> real poly \<Rightarrow> real poly \<Rightarrow> real" where
  "cindex_polyE a b q p = jumpF_polyR q p a + cindex_poly a b q p - jumpF_polyL q p b"
  
definition cindex_poly_ubd::"real poly \<Rightarrow> real poly \<Rightarrow> int" where
  "cindex_poly_ubd q p = (THE l. (\<forall>\<^sub>F r in at_top. cindexE (-r) r (\<lambda>x. poly q x/poly p x) = of_int l))"
   
lemma cindex_polyE_0[simp]: "cindex_polyE a b 0 p = 0" "cindex_polyE a b q 0 = 0"
  unfolding cindex_polyE_def by auto
  
lemma cindex_polyE_mult_cancel:
  fixes p q p'::"real poly"
  assumes "p'\<noteq> 0"  
  shows "cindex_polyE a b (p' * q ) (p' * p) = cindex_polyE a b q p"
  unfolding cindex_polyE_def
  using cindex_poly_mult[OF \<open>p'\<noteq>0\<close>] jumpF_polyL_mult_cancel[OF \<open>p'\<noteq>0\<close>] 
    jumpF_polyR_mult_cancel[OF \<open>p'\<noteq>0\<close>] 
  by simp
  
lemma cindexE_eq_cindex_polyE: 
  assumes "a<b"
  shows "cindexE a b (\<lambda>x. poly q x/poly p x) = cindex_polyE a b q p"
proof (cases "p=0 \<or> q=0")
  case True
  then show ?thesis by (auto simp add: cindexE_constI)
next
  case False
  then have "p\<noteq>0" "q\<noteq>0" by auto
  define g where "g=gcd p q"
  define p' q' where "p'=p div g" and "q' = q div g"
  define f' where "f'=(\<lambda>x. poly q' x / poly p' x)"
  have "g\<noteq>0" using False g_def by auto  
  have pq_f:"p=g*p'" "q=g*q'" and "coprime p' q'"
    unfolding g_def p'_def q'_def 
    apply simp_all 
    using False div_gcd_coprime by blast    
  have "cindexE a b (\<lambda>x. poly q x/poly p x) = cindexE a b (\<lambda>x. poly q' x/poly p' x)" 
  proof -
    define f where "f=(\<lambda>x. poly q x / poly p x)"
    define f' where "f'=(\<lambda>x. poly q' x / poly p' x)"
    have "jumpF f (at_right x) = jumpF f' (at_right x)" for x
    proof (rule jumpF_cong)
      obtain ub where "x < ub" "\<forall>z. x < z \<and> z \<le> ub \<longrightarrow> poly g z \<noteq> 0"
        using next_non_root_interval[OF \<open>g\<noteq>0\<close>,of x] by auto
      then show "\<forall>\<^sub>F x in at_right x. f x = f' x" 
        unfolding eventually_at_right f_def f'_def pq_f
        apply (intro exI[where x=ub])
        by auto
    qed simp
    moreover have "jumpF f (at_left x) = jumpF f' (at_left x)" for x 
    proof (rule jumpF_cong)
      obtain lb where "lb < x" "\<forall>z. lb \<le> z \<and> z < x \<longrightarrow> poly g z \<noteq> 0 "
        using last_non_root_interval[OF \<open>g\<noteq>0\<close>,of x] by auto
      then show "\<forall>\<^sub>F x in at_left x. f x = f' x" 
        unfolding eventually_at_left f_def f'_def pq_f
        apply (intro exI[where x=lb])
        by auto    
    qed simp    
    ultimately show ?thesis unfolding cindexE_def
      apply (fold f_def f'_def)
      by auto
  qed
  also have "... = jumpF f' (at_right a) + real_of_int (cindex a b f') - jumpF f' (at_left b)" 
    unfolding f'_def 
    apply (rule cindex_eq_cindexE_divide)
    subgoal using \<open>a<b\<close> .
    subgoal 
    proof -
      have "finite (proots (q'*p'))" 
        using False poly_roots_finite pq_f(1) pq_f(2) by auto
      then show "finite {x. (poly q' x = 0 \<or> poly p' x = 0) \<and> a \<le> x \<and> x \<le> b}"
        by (elim rev_finite_subset) auto
    qed
    subgoal using \<open>coprime p' q'\<close> poly_gcd_0_iff by force
    subgoal by (auto intro:continuous_intros)
    subgoal by (auto intro:continuous_intros)
    done
  also have "... = cindex_polyE a b q' p'"
    using cindex_eq_cindex_poly unfolding cindex_polyE_def jumpF_polyR_def jumpF_polyL_def f'_def
    by auto
  also have "... = cindex_polyE a b q p"
    using cindex_polyE_mult_cancel[OF \<open>g\<noteq>0\<close>] unfolding pq_f by auto
  finally show ?thesis .
qed
 
lemma cindex_polyE_cross:
  fixes p::"real poly" and a b::real
  assumes "a<b" 
  shows "cindex_polyE a b 1 p = cross_alt 1 p a b / 2" 
proof (induct "degree p" arbitrary:p rule:nat_less_induct) 
  case induct:1
  have ?case when "p=0" 
    using that unfolding cross_alt_def by auto
  moreover have ?case when "p\<noteq>0" and noroot:"{x.  a< x\<and> x< b \<and> poly p x=0 } = {}"
  proof -
    have "cindex_polyE a b 1 p = jumpF_polyR 1 p a  - jumpF_polyL 1 p b" 
    proof -
      have "cindex_poly a b 1 p = 0" unfolding cindex_poly_def
        apply (rule sum.neutral)
        using that by auto
      then show ?thesis unfolding cindex_polyE_def by auto
    qed
    also have "... = cross_alt 1 p a b / 2"  
    proof -
      define f where "f = (\<lambda>x. 1 / poly p x)"
      define ja where "ja = jumpF f (at_right a)"  
      define jb where "jb = jumpF f (at_left b)"
      define right where "right = (\<lambda>R. R ja (0::real) \<or> (continuous (at_right a) f \<and> R (poly p a) 0))"
      define left where "left = (\<lambda>R. R jb (0::real) \<or> (continuous (at_left b) f \<and> R (poly p b) 0))" 
        
      note ja_alt=jumpF_polyR_coprime[of p 1 a,unfolded jumpF_polyR_def,simplified,folded f_def ja_def]
      note jb_alt=jumpF_polyL_coprime[of p 1 b,unfolded jumpF_polyL_def,simplified,folded f_def jb_def]  
      
      have [simp]:"0 < ja \<longleftrightarrow> jumpF_polyR 1 p a = 1/2" "0 > ja \<longleftrightarrow> jumpF_polyR 1 p a = -1/2"
           "0 < jb \<longleftrightarrow> jumpF_polyL 1 p b = 1/2" "0 > jb \<longleftrightarrow> jumpF_polyL 1 p b = -1/2"
        unfolding ja_def jb_def jumpF_polyR_def jumpF_polyL_def f_def jumpF_def
        by auto           
      have [simp]: 
          "poly p a \<noteq>0 \<Longrightarrow> continuous (at_right a) f"
          "poly p b \<noteq>0 \<Longrightarrow> continuous (at_left b) f"  
        unfolding f_def by (auto intro!: continuous_intros )  
      have not_right_left: False when "(right greater \<and> left less \<or> right less \<and> left greater)"
      proof - 
        have [simp]: "f a > 0 \<longleftrightarrow> poly p a > 0" "f a < 0 \<longleftrightarrow> poly p a < 0"
             "f b > 0 \<longleftrightarrow> poly p b > 0" "f b < 0 \<longleftrightarrow> poly p b < 0" 
           unfolding f_def by auto  
        have "continuous_on {a<..<b} f" 
          unfolding f_def using noroot by (auto intro!: continuous_intros)
        then have "\<exists>x>a. x < b \<and> f x = 0" 
          apply (elim jumpF_IVT[OF \<open>a<b\<close>,of f])
          using that unfolding right_def left_def by (fold ja_def jb_def,auto)
        then show False using noroot using f_def by auto
      qed
      have ?thesis when "poly p a>0 \<and> poly p b>0 \<or> poly p a<0 \<and> poly p b<0" 
        using that jumpF_poly_noroot 
        unfolding cross_alt_def psign_diff_def by auto
      moreover have False when "poly p a>0 \<and> poly p b<0 \<or> poly p a<0 \<and> poly p b>0" 
        apply (rule not_right_left)
        unfolding right_def left_def using that by auto
      moreover have ?thesis when "poly p a=0" "poly p b>0 \<or> poly p b <0" 
      proof -
        have "ja>0 \<or> ja < 0" using ja_alt \<open>p\<noteq>0\<close> \<open>poly p a=0\<close> by argo
        moreover have False when "ja > 0 \<and> poly p b<0 \<or> ja < 0 \<and> poly p b>0" 
          apply (rule not_right_left)
          unfolding right_def left_def using that by fastforce
        moreover have ?thesis when "ja >0 \<and> poly p b>0 \<or> ja < 0 \<and> poly p b<0"
          using that jumpF_poly_noroot \<open>poly p a=0\<close> 
          unfolding cross_alt_def psign_diff_def by auto 
        ultimately show ?thesis using that jumpF_poly_noroot unfolding cross_alt_def by auto 
      qed
      moreover have ?thesis when "poly p b=0" "poly p a>0 \<or> poly p a <0" 
      proof -
        have "jb>0 \<or> jb < 0" using jb_alt \<open>p\<noteq>0\<close> \<open>poly p b=0\<close> by argo
        moreover have False when "jb > 0 \<and> poly p a<0 \<or> jb < 0 \<and> poly p a>0" 
          apply (rule not_right_left)
          unfolding right_def left_def using that by fastforce
        moreover have ?thesis when "jb >0 \<and> poly p a>0 \<or> jb < 0 \<and> poly p a<0"
          using that jumpF_poly_noroot \<open>poly p b=0\<close> 
          unfolding cross_alt_def psign_diff_def by auto 
        ultimately show ?thesis using that jumpF_poly_noroot unfolding cross_alt_def by auto 
      qed  
      moreover have ?thesis when "poly p a=0" "poly p b=0"
      proof -
        have "jb>0 \<or> jb < 0" using jb_alt \<open>p\<noteq>0\<close> \<open>poly p b=0\<close> by argo
        moreover have "ja>0 \<or> ja < 0" using ja_alt \<open>p\<noteq>0\<close> \<open>poly p a=0\<close> by argo
        moreover have False when "ja>0 \<and> jb<0 \<or> ja<0 \<and> jb>0"
          apply (rule not_right_left)
          unfolding right_def left_def using that by fastforce
        moreover have ?thesis when "ja>0 \<and> jb>0 \<or> ja<0 \<and> jb<0"
          using that jumpF_poly_noroot \<open>poly p b=0\<close> \<open>poly p a=0\<close> 
          unfolding cross_alt_def psign_diff_def by auto
        ultimately show ?thesis by blast
      qed
      ultimately show ?thesis by argo
    qed
    finally show ?thesis .
  qed    
  moreover have ?case when "p\<noteq>0" and no_empty:"{x.  a< x\<and> x< b \<and> poly p x=0 } \<noteq> {}"
  proof -
    define roots where "roots\<equiv>{x.  a< x\<and> x< b \<and> poly p x=0 }"
    have "finite roots" unfolding roots_def using poly_roots_finite[OF \<open>p\<noteq>0\<close>] by auto
    define max_r where "max_r\<equiv>Max roots"
    hence "poly p max_r=0" and "a<max_r" and "max_r<b" 
      using Max_in[OF \<open>finite roots\<close>] no_empty  unfolding roots_def by auto
    define max_rp where "max_rp\<equiv>[:-max_r,1:]^order max_r p"
    then obtain p' where p'_def:"p=p'*max_rp" and "\<not> [:-max_r,1:] dvd p'"  
      by (metis \<open>p\<noteq>0\<close> mult.commute order_decomp)
    hence "p'\<noteq>0" and "max_rp\<noteq>0" and max_r_nz:"poly p' max_r\<noteq>0"(*and "poly p' a\<noteq>0" and "poly p' b\<noteq>0" *)
      (*and  "poly max_rp a\<noteq>0" and "poly max_rp b\<noteq>0"*) 
      using \<open>p\<noteq>0\<close> by (auto simp add: dvd_iff_poly_eq_0)
    define max_r_sign where "max_r_sign\<equiv>if odd(order max_r p) then -1 else 1::int"
    define roots' where "roots'\<equiv>{x.  a< x\<and> x< b \<and> poly p' x=0}"
  
    have "cindex_polyE a b 1 p = jumpF_polyR 1 p a + (\<Sum>x\<in>roots. jump_poly 1 p x) - jumpF_polyL 1 p b"  
      unfolding cindex_polyE_def cindex_poly_def roots_def by (simp,meson)
    also have "... = max_r_sign * cindex_poly a b 1 p' + jump_poly 1 p max_r 
        + max_r_sign * jumpF_polyR 1 p' a - jumpF_polyL 1 p' b"
    proof -
      have "(\<Sum>x\<in>roots. jump_poly 1 p x) = max_r_sign * cindex_poly a b 1 p' + jump_poly 1 p max_r"  
      proof -
        have "(\<Sum>x\<in>roots. jump_poly 1 p x)= (\<Sum>x\<in>roots'. jump_poly 1 p x)+ jump_poly 1 p max_r"
        proof -
          have "roots = insert max_r roots'" 
            unfolding roots_def roots'_def p'_def 
            using \<open>poly p max_r=0\<close> \<open>a<max_r\<close> \<open>max_r<b\<close> \<open>p\<noteq>0\<close> order_root
            apply (subst max_rp_def)
            by auto
          moreover have "finite roots'" 
            unfolding roots'_def using poly_roots_finite[OF \<open>p'\<noteq>0\<close>] by auto 
          moreover have "max_r \<notin> roots'" 
            unfolding roots'_def using max_r_nz
            by auto
          ultimately show ?thesis using sum.insert[of roots' max_r] by auto   
        qed
        moreover have "(\<Sum>x\<in>roots'. jump_poly 1 p x) = max_r_sign * cindex_poly a b 1 p'"
        proof -
          have "(\<Sum>x\<in>roots'. jump_poly 1 p x) = (\<Sum>x\<in>roots'. max_r_sign * jump_poly 1 p' x)"
          proof (rule sum.cong,rule refl)
            fix x assume "x \<in> roots'" 
            hence "x\<noteq>max_r" using max_r_nz unfolding roots'_def 
              by auto
            hence "poly max_rp x\<noteq>0" using poly_power_n_eq unfolding max_rp_def by auto
            hence "order x max_rp=0"  by (metis order_root)
            moreover have "jump_poly 1 max_rp x=0" 
              using \<open>poly max_rp x\<noteq>0\<close> by (metis jump_poly_not_root)
            moreover have "x\<in>roots"
              using \<open>x \<in> roots'\<close> unfolding roots_def roots'_def p'_def by auto
            hence "x<max_r" 
              using Max_ge[OF \<open>finite roots\<close>,of x] \<open>x\<noteq>max_r\<close> by (fold max_r_def,auto)
            hence "sign (poly max_rp x) = max_r_sign" 
              using \<open>poly max_rp x \<noteq> 0\<close> unfolding max_r_sign_def max_rp_def sign_def
              by (subst poly_power,simp add:linorder_class.not_less zero_less_power_eq)
            ultimately show "jump_poly 1 p x = max_r_sign * jump_poly 1 p' x" 
              using jump_poly_1_mult[of p' x max_rp]  unfolding p'_def 
              by (simp add: \<open>poly max_rp x \<noteq> 0\<close>)
          qed
          also have "... = max_r_sign * (\<Sum>x\<in>roots'. jump_poly 1 p' x)" 
            by (simp add: sum_distrib_left) 
          also have "... = max_r_sign * cindex_poly a b 1 p'"
            unfolding cindex_poly_def roots'_def by meson
          finally show ?thesis .
        qed
        ultimately show ?thesis by simp
      qed
      moreover have "jumpF_polyR 1 p a = max_r_sign * jumpF_polyR 1 p' a"
      proof -
        define f where "f = (\<lambda>x. 1 / poly max_rp x)"
        define g where "g = (\<lambda>x. 1 / poly p' x)"
        have "jumpF_polyR 1 p a = jumpF (\<lambda>x. f x * g x) (at_right a)"  
          unfolding jumpF_polyR_def f_def g_def p'_def 
          by (auto simp add:field_simps)
        also have "... = sgn (f a) * jumpF g (at_right a)" 
        proof (rule jumpF_times) 
          have [simp]: "poly max_rp a \<noteq>0" 
            unfolding max_rp_def using \<open>max_r>a\<close> by auto  
          show "(f \<longlongrightarrow> f a) (at_right a)" "f a \<noteq> 0"
            unfolding f_def by (auto intro:tendsto_intros)
        qed auto      
        also have "... = max_r_sign * jumpF_polyR 1 p' a"
        proof -
          have "sgn (f a) = max_r_sign" 
            unfolding max_r_sign_def f_def max_rp_def using \<open>a<max_r\<close>
            by (auto simp add:sgn_power)
          then show ?thesis unfolding jumpF_polyR_def g_def by auto
        qed
        finally show ?thesis .
      qed
      moreover have "jumpF_polyL 1 p b =  jumpF_polyL 1 p' b"
      proof -
        define f where "f = (\<lambda>x. 1 / poly max_rp x)"
        define g where "g = (\<lambda>x. 1 / poly p' x)"
        have "jumpF_polyL 1 p b = jumpF (\<lambda>x. f x * g x) (at_left b)"  
          unfolding jumpF_polyL_def f_def g_def p'_def 
          by (auto simp add:field_simps)
        also have "... = sgn (f b) * jumpF g (at_left b)" 
        proof (rule jumpF_times) 
          have [simp]: "poly max_rp b \<noteq>0" 
            unfolding max_rp_def using \<open>max_r<b\<close> by auto  
          show "(f \<longlongrightarrow> f b) (at_left b)" "f b \<noteq> 0"
            unfolding f_def by (auto intro:tendsto_intros)
        qed auto      
        also have "... = jumpF_polyL 1 p' b"
        proof -
          have "sgn (f b) = 1" 
            unfolding max_r_sign_def f_def max_rp_def using \<open>b>max_r\<close>
            by (auto simp add:sgn_power)
          then show ?thesis unfolding jumpF_polyL_def g_def by auto
        qed
        finally show ?thesis .
      qed 
      ultimately show ?thesis by auto
    qed
    also have "... = max_r_sign * cindex_polyE a b 1 p' + jump_poly 1 p max_r 
        + (max_r_sign - 1) * jumpF_polyL 1 p' b"
      unfolding cindex_polyE_def roots'_def by (auto simp add:algebra_simps)
    also have "... = max_r_sign * cross_alt 1 p' a b / 2 + jump_poly 1 p max_r 
        + (max_r_sign - 1) * jumpF_polyL 1 p' b"
    proof -
      have "degree max_rp>0" unfolding max_rp_def degree_linear_power
        using \<open>poly p max_r=0\<close> order_root \<open>p\<noteq>0\<close> by blast
      then have "degree p'<degree p" unfolding p'_def 
        using degree_mult_eq[OF \<open>p'\<noteq>0\<close> \<open>max_rp\<noteq>0\<close>] by auto
      from induct[rule_format, OF this] 
      have "cindex_polyE a b 1 p' = real_of_int (cross_alt 1 p' a b) / 2" by auto
      then show ?thesis by auto
    qed
    also have "... = real_of_int (cross_alt 1 p a b) / 2"
    proof -
      have sjump_p:"jump_poly 1 p max_r = (if odd (order max_r p) then sign (poly p' max_r) else 0)"
      proof -
        note max_r_nz 
        moreover then have "poly max_rp max_r=0" 
          using \<open>poly p max_r = 0\<close> p'_def by auto
        ultimately have "jump_poly 1 p max_r = sign (poly p' max_r) * jump_poly 1 max_rp max_r"
          unfolding p'_def using jump_poly_1_mult[of p' max_r max_rp] 
          by auto
        also have "... = (if odd (order max_r max_rp) then sign (poly p' max_r) else 0)"  
        proof -
          have "sign_r_pos max_rp max_r"
            unfolding max_rp_def using sign_r_pos_power by auto
          then show ?thesis using \<open>max_rp\<noteq>0\<close> unfolding jump_poly_def by auto
        qed
        also have "... = (if odd (order max_r p) then sign (poly p' max_r) else 0)"
        proof -
          have "order max_r p'=0" by (simp add: \<open>poly p' max_r \<noteq> 0\<close> order_0I)
          then have "order max_r max_rp = order max_r p" 
            unfolding p'_def using \<open>p'\<noteq>0\<close> \<open>max_rp\<noteq>0\<close>
            apply (subst order_mult)
            by auto  
          then show ?thesis by auto
        qed
        finally show ?thesis .
      qed
      have ?thesis when "even (order max_r p)"
      proof -
        have "sign (poly p x) =  (sign (poly p' x)::int)" when "x\<noteq>max_r" for x
        proof -
          have "sign (poly max_rp x) = (1::int)"
            unfolding max_rp_def using \<open>even (order max_r p)\<close> that 
            apply (simp add:sign_power )
            by (simp add: Sturm_Tarski.sign_def)
          then show ?thesis unfolding p'_def by (simp add:sign_times)
        qed    
        from this[of a] this[of b] \<open>a<max_r\<close> \<open>max_r<b\<close> 
        have "cross_alt 1 p' a b = cross_alt 1 p a b" 
          unfolding cross_alt_def psign_diff_def by auto 
        then show ?thesis using that unfolding max_r_sign_def sjump_p by auto
      qed
      moreover have ?thesis when "odd (order max_r p)" 
      proof -
        let ?thesis2 = "sign (poly p' max_r) * 2 - cross_alt 1 p' a b - 4 * jumpF_polyL 1 p' b 
              = cross_alt 1 p a b"    
        have ?thesis2 when "poly p' b=0"
        proof -
          have "jumpF_polyL 1 p' b = 1/2 \<or> jumpF_polyL 1 p' b=-1/2"  
            using jumpF_polyL_coprime[of p' 1 b,simplified] \<open>p'\<noteq>0\<close> \<open>poly p' b=0\<close> by auto
          moreover have "poly p' max_r>0 \<or> poly p' max_r<0" 
            using max_r_nz by auto
          moreover have False when "poly p' max_r>0 \<and> jumpF_polyL 1 p' b=-1/2 
                \<or> poly p' max_r<0 \<and> jumpF_polyL 1 p' b=1/2"
          proof -
            define f where "f= (\<lambda>x. 1/ poly p' x)"
            have noroots:"poly p' x\<noteq>0" when "x\<in>{max_r<..<b}" for x
            proof (rule ccontr)
              assume " \<not> poly p' x \<noteq> 0"
              then have "poly p x =0" unfolding p'_def by auto
              then have "x\<in>roots" unfolding roots_def using that \<open>a<max_r\<close> by auto
              then have "x\<le>max_r" using Max_ge[OF \<open>finite roots\<close>] unfolding max_r_def by auto
              moreover have "x>max_r" using that by auto
              ultimately show False by auto
            qed  
            have "continuous_on {max_r<..<b} f"
              unfolding f_def using noroots by (auto intro!:continuous_intros)
            moreover have "continuous (at_right max_r) f" 
              unfolding f_def using max_r_nz
              by (auto intro!:continuous_intros)
            moreover have "f max_r>0 \<and> jumpF f (at_left b)<0 
                \<or> f max_r<0 \<and> jumpF f (at_left b)>0"
              using that unfolding f_def jumpF_polyL_def by auto  
            ultimately have "\<exists>x>max_r. x < b \<and> f x = 0"
              apply (intro jumpF_IVT[OF \<open>max_r<b\<close>])
              by auto
            then show False using noroots unfolding f_def by auto
          qed
          moreover have ?thesis when "poly p' max_r>0 \<and> jumpF_polyL 1 p' b=1/2
              \<or> poly p' max_r<0 \<and> jumpF_polyL 1 p' b=-1/2"
          proof -
            have "poly max_rp a < 0" "poly max_rp b>0"
              unfolding max_rp_def using \<open>odd (order max_r p)\<close> \<open>a<max_r\<close> \<open>max_r<b\<close>
              by (simp_all add:zero_less_power_eq)
            then have "cross_alt 1 p a b = - cross_alt 1 p' a b" 
              unfolding cross_alt_def p'_def using \<open>poly p' b=0\<close> 
              apply (simp add:sign_times)
              by (auto simp add: Sturm_Tarski.sign_def psign_diff_def zero_less_mult_iff)
            with that show ?thesis by auto
          qed
          ultimately show ?thesis by blast  
        qed
        moreover have ?thesis2 when "poly p' b\<noteq>0"
        proof -
          have [simp]:"jumpF_polyL 1 p' b = 0" 
            using jumpF_polyL_coprime[of p' 1 b,simplified] \<open>poly p' b\<noteq>0\<close> by auto 
          have [simp]:"poly max_rp a < 0" "poly max_rp b>0"
            unfolding max_rp_def using \<open>odd (order max_r p)\<close> \<open>a<max_r\<close> \<open>max_r<b\<close>
            by (simp_all add:zero_less_power_eq)
          have "poly p' b>0 \<or> poly p' b<0" 
            using \<open>poly p' b\<noteq>0\<close> by auto
          moreover have "poly p' max_r>0 \<or> poly p' max_r<0" 
            using max_r_nz by auto
          moreover have ?thesis when "poly p' b>0 \<and> poly p' max_r>0 "  
            using that unfolding cross_alt_def p'_def psign_diff_def
            apply (simp add:sign_times)
            by (simp add: Sturm_Tarski.sign_def)  
          moreover have ?thesis when "poly p' b<0 \<and> poly p' max_r<0"      
            using that unfolding cross_alt_def p'_def psign_diff_def
            apply (simp add:sign_times)
            by (simp add: Sturm_Tarski.sign_def)  
          moreover have False when "poly p' b>0 \<and> poly p' max_r<0 \<or> poly p' b<0 \<and> poly p' max_r>0"
          proof -
            have "\<exists>x>max_r. x < b \<and> poly p' x = 0"
              apply (rule poly_IVT[OF \<open>max_r<b\<close>,of p'])
              using that mult_less_0_iff by blast
            then obtain x where "max_r<x" "x<b" "poly p x=0" unfolding p'_def by auto
            then have "x\<in>roots" using \<open>a<max_r\<close> unfolding roots_def by auto
            then have "x\<le>max_r" unfolding max_r_def using Max_ge[OF \<open>finite roots\<close>] by auto    
            then show False using \<open>max_r<x\<close> by auto
          qed
          ultimately show ?thesis by blast
        qed
        ultimately have ?thesis2 by auto 
        then show ?thesis unfolding max_r_sign_def sjump_p using that by simp
      qed
      ultimately show ?thesis by auto
    qed
    finally show ?thesis . 
  qed
  ultimately show ?case by fast
qed          
     
lemma cindex_polyE_inverse_add:
  fixes p q::"real poly" 
  assumes cp:"coprime p q"
  shows "cindex_polyE a b q p + cindex_polyE a b p q=cindex_polyE a b 1 (q*p)"
  unfolding cindex_polyE_def
  using cindex_poly_inverse_add[OF cp,symmetric] jumpF_polyR_inverse_add[OF cp,symmetric] 
    jumpF_polyL_inverse_add[OF cp,symmetric]
  by auto    

lemma cindex_polyE_inverse_add_cross:
  fixes p q::"real poly"
  assumes "a < b" "coprime p q" 
  shows "cindex_polyE a b q p  + cindex_polyE a b p q = cross_alt p q a b / 2" 
  apply (subst cindex_polyE_inverse_add[OF \<open>coprime p q\<close>])
  apply (subst cindex_polyE_cross[OF \<open>a<b\<close>])
  apply (subst mult.commute)  
  apply (subst (2) cross_alt_clear)
  by simp

lemma cindex_polyE_inverse_add_cross':
  fixes p q::"real poly"
  assumes "a < b" "poly p a\<noteq>0 \<or> poly q a\<noteq>0" "poly p b\<noteq>0 \<or> poly q b\<noteq>0" 
  shows "cindex_polyE a b q p  + cindex_polyE a b p q = cross_alt p q a b / 2" 
proof -
  define g1 where "g1 = gcd p q"
  obtain p' q' where pq:"p=g1*p'" "q=g1*q'" and "coprime p' q'"
    unfolding g1_def 
    by (metis assms(2) coprime_commute div_gcd_coprime dvd_mult_div_cancel gcd_dvd1 
        gcd_dvd2 order_root)
  have [simp]:"g1\<noteq>0"
    unfolding g1_def using assms(2) by force

  have "cindex_polyE a b q' p' + cindex_polyE a b p' q' = (cross_alt p' q' a b) / 2"
    using cindex_polyE_inverse_add_cross[OF \<open>a<b\<close> \<open>coprime p' q'\<close>] .
  moreover have "cindex_polyE a b p' q' = cindex_polyE a b p q "
    unfolding pq 
    apply (subst cindex_polyE_mult_cancel)
    by simp_all
  moreover have "cindex_polyE a b q' p' = cindex_polyE a b q p"
    unfolding pq 
    apply (subst cindex_polyE_mult_cancel)
    by simp_all
  moreover have "cross_alt p' q' a b = cross_alt p q a b"
    unfolding pq
    apply (subst cross_alt_cancel)
    subgoal using assms(2) g1_def poly_gcd_0_iff by blast
    subgoal using assms(3) g1_def poly_gcd_0_iff by blast
    by simp
  ultimately show ?thesis by auto
qed

lemma cindex_polyE_smult_1: 
  fixes p q::"real poly" and c::real
  shows "cindex_polyE a b (smult c q) p =  (sgn c) * cindex_polyE a b q p"
proof -
  have "real_of_int (sign c) = sgn c"
    by (simp add: sgn_if)
  then show ?thesis
    unfolding cindex_polyE_def jumpF_polyL_smult_1 jumpF_polyR_smult_1 cindex_poly_smult_1 
    by (auto simp add: algebra_simps)
qed

lemma cindex_polyE_smult_2: 
  fixes p q::"real poly" and c::real
  shows "cindex_polyE a b q (smult c p) =  (sgn c) * cindex_polyE a b q p"
proof (cases "c=0")
  case True
  then show ?thesis by simp
next
  case False
  then have "cindex_polyE a b q (smult c p)
          = cindex_polyE a b ([:1/c:]*q) ([:1/c:]*(smult c p))"
    apply (subst cindex_polyE_mult_cancel)
    by simp_all
  also have "... = cindex_polyE a b (smult (1/c) q) p"
    by simp
  also have "... = (sgn (1/c)) * cindex_polyE a b q p"
    using cindex_polyE_smult_1 by simp
  also have "... = (sgn c) * cindex_polyE a b q p"
    by simp
  finally show ?thesis .
qed

lemma cindex_polyE_mod:
  fixes p q::"real poly" 
  shows "cindex_polyE a b q p =  cindex_polyE a b (q mod p) p"
  unfolding cindex_polyE_def
  apply (subst cindex_poly_mod)
  apply (subst jumpF_polyR_mod)
  apply (subst jumpF_polyL_mod)
  by simp

lemma cindex_polyE_rec:
  fixes p q::"real poly"
  assumes "a < b" "coprime p q"
  shows "cindex_polyE a b q p  = cross_alt q p a b/2  +  cindex_polyE a b (- (p mod q)) q"  
proof -
  note cindex_polyE_inverse_add_cross[OF assms]
  moreover have "cindex_polyE a b (- (p mod q)) q = - cindex_polyE a b p q"
    using cindex_polyE_mod cindex_polyE_smult_1[of a b "-1"]
    by auto
  ultimately show ?thesis by (auto simp add:field_simps cross_alt_poly_commute)
qed    
     
lemma cindex_polyE_changes_alt_itv_mods: 
  assumes "a<b" "coprime p q"
  shows "cindex_polyE a b q p = changes_alt_itv_smods a b p q / 2" using \<open>coprime p q\<close>
proof (induct "smods p q" arbitrary:p q)
  case Nil
  then have "p=0" by (metis smods_nil_eq)
  then show ?case by (simp add:changes_alt_itv_smods_def changes_alt_poly_at_def) 
next
  case (Cons x xs)
  then have "p\<noteq>0" by auto
  have ?case when "q=0" 
    using that by (simp add:changes_alt_itv_smods_def changes_alt_poly_at_def)
  moreover have ?case when "q\<noteq>0"
  proof -
    define r where "r\<equiv>- (p mod q)"
    obtain ps where ps:"smods p q=p#q#ps" "smods q r=q#ps" and "xs=q#ps"
      unfolding r_def using \<open>q\<noteq>0\<close> \<open>p\<noteq>0\<close> \<open>x # xs = smods p q\<close> 
      by (metis list.inject smods.simps)
    from Cons.prems \<open>q \<noteq> 0\<close> have "coprime q r" 
      by (simp add: r_def ac_simps)
    then have "cindex_polyE a b r q = real_of_int (changes_alt_itv_smods a b q r) / 2"
      apply (rule_tac Cons.hyps(1))
      using ps \<open>xs=q#ps\<close> by simp_all  
    moreover have "changes_alt_itv_smods a b p q = cross_alt p q a b + changes_alt_itv_smods a b q r" 
      using changes_alt_itv_smods_rec[OF \<open>a<b\<close> \<open>coprime p q\<close>,folded r_def] .
    moreover have "cindex_polyE a b q p = real_of_int (cross_alt q p a b) / 2 + cindex_polyE a b r q"
      using cindex_polyE_rec[OF \<open>a<b\<close> \<open>coprime p q\<close>,folded r_def] .
    ultimately show ?case 
      by (auto simp add:field_simps cross_alt_poly_commute)
  qed
  ultimately show ?case by blast
qed
  
lemma cindex_poly_ubd_eventually:
  shows "\<forall>\<^sub>F r in at_top. cindexE (-r) r (\<lambda>x. poly q x/poly p x) = of_int (cindex_poly_ubd q p)" 
proof -
  define f where "f=(\<lambda>x. poly q x/poly p x)"
  obtain R where R_def: "R>0" "proots p \<subseteq> {-R<..<R}"
    if "p\<noteq>0" 
  proof (cases "p=0")
    case True
    then show ?thesis using that[of 1] by auto
  next
    case False
    then have "finite (proots p)" by auto
    from finite_ball_include[OF this,of 0] 
    obtain r where "r>0" and r_ball:"proots p \<subseteq> ball 0 r"
      by auto
    have "proots p \<subseteq> {-r<..<r}"
    proof 
      fix x assume "x \<in> proots p"
      then have "x\<in>ball 0 r" using r_ball by auto
      then have "abs x<r" using mem_ball_0 by auto
      then show "x \<in> {- r<..<r}" using \<open>r>0\<close> by auto
    qed
    then show ?thesis using that[of r] False \<open>r>0\<close> by auto
  qed
  define l where "l=(if p=0  then 0 else cindex_poly (-R) R q p)"  
  define P where "P=(\<lambda>l. (\<forall>\<^sub>F r in at_top. cindexE (-r) r f = of_int l))"
  have "P l " 
  proof (cases "p=0 ")
    case True
    then show ?thesis
      unfolding P_def f_def l_def using True
      by (auto intro!: eventuallyI cindexE_constI)
  next
    case False
    have "P l" unfolding P_def
    proof (rule eventually_at_top_linorderI[of R])  
      fix r assume "R \<le> r" 
      then have "cindexE (- r) r f =  cindex_polyE (-r) r q p"
        unfolding f_def using R_def[OF \<open>p\<noteq>0\<close>] by (auto intro: cindexE_eq_cindex_polyE)
      also have "... = of_int (cindex_poly (- r) r q p)"
      proof -
        have "jumpF_polyR q p (- r) = 0"
          apply (rule jumpF_poly_noroot)
          using \<open>R\<le>r\<close> R_def[OF \<open>p\<noteq>0\<close>] by auto
        moreover have "jumpF_polyL q p r = 0"
          apply (rule jumpF_poly_noroot)
          using \<open>R\<le>r\<close> R_def[OF \<open>p\<noteq>0\<close>] by auto
        ultimately show ?thesis unfolding cindex_polyE_def by auto
      qed  
      also have "... = of_int (cindex_poly (- R) R q p)"
      proof -
        define rs where "rs={x. poly p x = 0 \<and> - r < x \<and> x < r}"
        define Rs where "Rs={x. poly p x = 0 \<and> - R < x \<and> x < R}"
        have "rs=Rs" 
          using R_def[OF \<open>p\<noteq>0\<close>] \<open>R\<le>r\<close> unfolding rs_def Rs_def by force    
        then show ?thesis
          unfolding cindex_poly_def by (fold rs_def Rs_def,auto)
      qed
      also have "... = of_int l" unfolding l_def using False by auto
      finally show "cindexE (- r) r f = real_of_int l" .
    qed
    then show ?thesis unfolding P_def by auto
  qed
  moreover have "x=l" when "P x" for x 
  proof -
    have "\<forall>\<^sub>F r in at_top. cindexE (- r) r f = real_of_int x"
         "\<forall>\<^sub>F r in at_top. cindexE (- r) r f = real_of_int l"
      using \<open>P x\<close> \<open>P l\<close> unfolding P_def by auto
    from eventually_conj[OF this] 
    have "\<forall>\<^sub>F r::real in at_top. real_of_int x = real_of_int l"
      by (elim eventually_mono,auto)
    then have "real_of_int x = real_of_int l" by auto
    then show ?thesis by simp
  qed
  ultimately have "P (THE x. P x)" using theI[of P l] by blast
  then show ?thesis unfolding P_def f_def cindex_poly_ubd_def by auto 
qed
  
lemma cindex_poly_ubd_0:
  assumes "p=0 \<or> q=0"
  shows "cindex_poly_ubd q p = 0"  
proof -
  have "\<forall>\<^sub>F r in at_top. cindexE (-r) r (\<lambda>x. poly q x/poly p x) = 0"
    apply (rule eventuallyI)
    using assms by (auto intro:cindexE_constI)
  from eventually_conj[OF this cindex_poly_ubd_eventually[of q p]]
  have "\<forall>\<^sub>F r::real in at_top.  (cindex_poly_ubd q p) = (0::int)"
    apply (elim eventually_mono)
    by auto
  then show ?thesis by auto
qed
  
lemma cindex_poly_ubd_code:
  shows "cindex_poly_ubd q p = changes_R_smods p q"
proof (cases "p=0")
  case True
  then show ?thesis using cindex_poly_ubd_0 by auto
next
  case False
  define ps where "ps\<equiv>smods p q"
  have "p\<in>set ps" using ps_def \<open>p\<noteq>0\<close> by auto
  obtain lb where lb:"\<forall>p\<in>set ps. \<forall>x. poly p x=0 \<longrightarrow> x>lb"
      and lb_sgn:"\<forall>x\<le>lb. \<forall>p\<in>set ps. sgn (poly p x) = sgn_neg_inf p"
      and "lb<0"
    using root_list_lb[OF no_0_in_smods,of p q,folded ps_def] 
    by auto
  obtain ub where ub:"\<forall>p\<in>set ps. \<forall>x. poly p x=0 \<longrightarrow> x<ub"
      and ub_sgn:"\<forall>x\<ge>ub. \<forall>p\<in>set ps. sgn (poly p x) = sgn_pos_inf p"
      and "ub>0"
    using root_list_ub[OF no_0_in_smods,of p q,folded ps_def] 
    by auto
  define f where "f=(\<lambda>t. poly q t/ poly p t)"
  define P where "P=(\<lambda>l. (\<forall>\<^sub>F r in at_top. cindexE (-r) r f = of_int l))"
  have "P (changes_R_smods p q)" unfolding P_def
  proof (rule eventually_at_top_linorderI[of "max \<bar>lb\<bar> \<bar>ub\<bar> + 1"])
    fix r assume r_asm:"r\<ge>max \<bar>lb\<bar> \<bar>ub\<bar> + 1"
    have "cindexE (- r) r f =  cindex_polyE (-r) r q p"
      unfolding f_def using r_asm by (auto intro: cindexE_eq_cindex_polyE)
    also have "... = of_int (cindex_poly (- r) r q p)"
    proof -
      have "jumpF_polyR q p (- r) = 0"
        apply (rule jumpF_poly_noroot)
        using r_asm lb[rule_format,OF \<open>p\<in>set ps\<close>,of "-r"] by linarith
      moreover have "jumpF_polyL q p r = 0"
        apply (rule jumpF_poly_noroot)
        using r_asm ub[rule_format,OF \<open>p\<in>set ps\<close>,of "r"] by linarith
      ultimately show ?thesis unfolding cindex_polyE_def by auto
    qed
    also have "... = of_int (changes_itv_smods (- r) r p q)"
      apply (rule cindex_poly_changes_itv_mods[THEN arg_cong])
      using r_asm lb[rule_format,OF \<open>p\<in>set ps\<close>,of "-r"] ub[rule_format,OF \<open>p\<in>set ps\<close>,of "r"]
      by linarith+
    also have "... = of_int (changes_R_smods p q)"
    proof -
      have "map (sgn \<circ> (\<lambda>p. poly p (-r))) ps = map sgn_neg_inf ps"
          and "map (sgn \<circ> (\<lambda>p. poly p r)) ps = map sgn_pos_inf ps"
        using lb_sgn[THEN spec,of "-r",simplified] ub_sgn[THEN spec,of r,simplified] r_asm 
        by auto
      hence "changes_poly_at ps (-r)=changes_poly_neg_inf ps
          \<and> changes_poly_at ps r=changes_poly_pos_inf ps"
        unfolding changes_poly_neg_inf_def changes_poly_at_def changes_poly_pos_inf_def
        by (subst (1 3)  changes_map_sgn_eq,metis map_map)
      thus ?thesis unfolding changes_R_smods_def changes_itv_smods_def ps_def
        by metis
    qed
    finally show "cindexE (- r) r f =  of_int (changes_R_smods p q)" .
  qed
  moreover have "x = changes_R_smods p q" when "P x" for x 
  proof -
    have "\<forall>\<^sub>F r in at_top. cindexE (- r) r f = real_of_int (changes_R_smods p q)" 
        "\<forall>\<^sub>F r in at_top. cindexE (- r) r f = real_of_int x"
      using \<open>P (changes_R_smods p q)\<close> \<open>P x\<close> unfolding P_def by auto
    from eventually_conj[OF this] 
    have "\<forall>\<^sub>F (r::real) in at_top. of_int x = of_int (changes_R_smods p q)"
      by (elim eventually_mono,auto)
    then have "of_int x = of_int (changes_R_smods p q)" 
      using eventually_const_iff by auto
    then show ?thesis using of_int_eq_iff by blast
  qed
  ultimately have "(THE x. P x) = changes_R_smods p q" 
    using the_equality[of P "changes_R_smods p q"] by blast
  then show ?thesis unfolding cindex_poly_ubd_def P_def f_def by auto
qed  


lemma cindexE_ubd_poly: "cindexE_ubd (\<lambda>x. poly q x/poly p x) = cindex_poly_ubd q p"
proof (cases "p=0")
  case True
  then show ?thesis using cindex_poly_ubd_0 unfolding cindexE_ubd_def 
    by auto
next
  case False
  define mx mn where "mx = Max {x. poly p x = 0}" and "mn = Min {x. poly p x=0}"
  define rr where "rr= 1+ (max \<bar>mx\<bar> \<bar>mn\<bar>)"
  have rr:"-rr < x \<and> x< rr" when "poly p x = 0 " for x
  proof -
    have "finite {x. poly p x = 0}" using \<open>p\<noteq>0\<close> poly_roots_finite by blast
    then have "mn \<le> x" "x\<le>mx"
      using Max_ge Min_le that unfolding mn_def mx_def by simp_all
    then show ?thesis unfolding rr_def by auto
  qed
  define f where "f=(\<lambda>x. poly q x / poly p x)"
  have "\<forall>\<^sub>F r in at_top. cindexE (- r) r f = cindexE_ubd f"
  proof (rule eventually_at_top_linorderI[of rr])
    fix r assume "r\<ge>rr"
    define R1 R2 where "R1={x. jumpF f (at_right x) \<noteq> 0 \<and> - r \<le> x \<and> x < r}"
                       and "R2 = {x. jumpF f (at_right x) \<noteq> 0}"
    define L1 L2 where "L1={x. jumpF f (at_left x) \<noteq> 0 \<and> - r < x \<and> x \<le> r}"
                       and "L2={x. jumpF f (at_left x) \<noteq> 0}"
    have "R1=R2"
    proof -
      have "jumpF f (at_right x) = 0" when "\<not> (- r \<le> x \<and> x < r)" for x 
      proof -
        have "jumpF f (at_right x) = jumpF_polyR q p x"
          unfolding f_def jumpF_polyR_def by simp
        also have "... = 0"
          apply (rule jumpF_poly_noroot)
          using  that \<open>r\<ge>rr\<close> by (auto dest:rr)
        finally show ?thesis .
      qed
      then show ?thesis unfolding R1_def R2_def by blast
    qed
    moreover have "L1=L2"
    proof -
      have "jumpF f (at_left x) = 0" when "\<not> (- r < x \<and> x \<le> r)" for x 
      proof -
        have "jumpF f (at_left x) = jumpF_polyL q p x"
          unfolding f_def jumpF_polyL_def by simp
        also have "... = 0"
          apply (rule jumpF_poly_noroot)
          using that \<open>r\<ge>rr\<close> by (auto dest:rr)
        finally show ?thesis .
      qed
      then show ?thesis unfolding L1_def L2_def by blast
    qed
    ultimately show "cindexE (- r) r f = cindexE_ubd f" 
      unfolding cindexE_def cindexE_ubd_def
      apply (fold R1_def R2_def L1_def L2_def)
      by auto
  qed
  moreover have "\<forall>\<^sub>F r in at_top. cindexE (- r) r f = cindex_poly_ubd q p"
    using cindex_poly_ubd_eventually unfolding f_def by auto
  ultimately have "\<forall>\<^sub>F r in at_top. cindexE (- r) r f = cindexE_ubd f 
                          \<and> cindexE (- r) r f = cindex_poly_ubd q p"
    using eventually_conj by auto
  then have "\<forall>\<^sub>F (r::real) in at_top. cindexE_ubd f = cindex_poly_ubd q p"
    by (elim eventually_mono) auto
  then show ?thesis unfolding f_def by auto
qed

lemma cindex_polyE_noroot:
  assumes "a<b" "\<forall>x. a\<le>x \<and> x\<le>b \<longrightarrow> poly p x\<noteq>0"
  shows "cindex_polyE a b q p = 0"
proof -
  have "jumpF_polyR q p a = 0"
    apply (rule jumpF_poly_noroot)
    using assms by auto
  moreover have "jumpF_polyL q p b = 0"
    apply (rule jumpF_poly_noroot)
    using assms by auto
  moreover have "cindex_poly a b q p =0" 
    apply (rule cindex_poly_noroot)
    using assms by auto
  ultimately show ?thesis unfolding cindex_polyE_def by auto
qed

lemma cindex_polyE_combine:
  assumes "a<b" "b<c"
  shows "cindex_polyE a b q p + cindex_polyE b c q p = cindex_polyE a c q p"
proof -
  define A B where "A=cindex_poly a b q p - jumpF_polyL q p b"
               and "B=jumpF_polyR q p b + cindex_poly b c q p"
  have "cindex_polyE a b q p + cindex_polyE b c q p = 
                    jumpF_polyR q p a + (A +B) - jumpF_polyL q p c"
    unfolding cindex_polyE_def A_def B_def by auto
  also have "... = jumpF_polyR q p a + cindex_poly a c q p - jumpF_polyL q p c"
  proof -
    have "A+B = cindex_poly a b q p + (jumpF_polyR q p b - jumpF_polyL q p b) 
                    + cindex_poly b c q p"
      unfolding A_def B_def by auto
    also have "... = cindex_poly a b q p + real_of_int (jump_poly q p b) + cindex_poly b c q p"
      using jump_poly_jumpF_poly by auto
    also have "... = cindex_poly a c q p"
      using assms
      apply (subst (3) cindex_poly_combine[symmetric,of _ b])
      by auto
    finally show ?thesis by auto
  qed
  also have "... = cindex_polyE a c q p"
    unfolding cindex_polyE_def by simp
  finally show ?thesis .
qed

lemma cindex_polyE_linear_comp:
  fixes b c::real
  defines "h \<equiv> (\<lambda>p. pcompose p [:b,c:])"
  assumes "lb<ub" "c\<noteq>0"
  shows "cindex_polyE lb ub (h q) (h p) = 
              (if 0 < c then cindex_polyE (c * lb + b) (c * ub + b) q p
               else - cindex_polyE (c * ub + b) (c * lb + b) q p)"
proof -
  have "cindex_polyE lb ub (h q) (h p) = cindexE lb ub (\<lambda>x. poly (h q) x / poly (h p) x)"
    apply (subst cindexE_eq_cindex_polyE[symmetric,OF \<open>lb<ub\<close>])
    by simp
  also have "... = cindexE lb ub ((\<lambda>x. poly q x / poly p x) \<circ> (\<lambda>x. c * x + b))"
    unfolding comp_def h_def poly_pcompose by (simp add:algebra_simps)
  also have "... = (if 0 < c then cindexE (c * lb + b) (c * ub + b) (\<lambda>x. poly q x / poly p x)
     else - cindexE (c * ub + b) (c * lb + b) (\<lambda>x. poly q x / poly p x))"
    apply (subst cindexE_linear_comp[OF \<open>c\<noteq>0\<close>])
    by simp
  also have "... = (if 0 < c then cindex_polyE (c * lb + b) (c * ub + b) q p
               else - cindex_polyE (c * ub + b) (c * lb + b) q p)"
  proof  -
    have "cindexE (c * lb + b) (c * ub + b) (\<lambda>x. poly q x / poly p x)
            = cindex_polyE (c * lb + b) (c * ub + b) q p" if "c>0" 
      apply (subst cindexE_eq_cindex_polyE)
      using that \<open>lb<ub\<close> by auto
    moreover have "cindexE (c * ub + b) (c * lb + b) (\<lambda>x. poly q x / poly p x)
            = cindex_polyE (c * ub + b) (c * lb + b) q p" if  "\<not> c>0" 
      apply (subst cindexE_eq_cindex_polyE)
      using that assms by auto
    ultimately show ?thesis by auto
  qed
  finally show ?thesis .
qed

lemma cindex_polyE_product':
  fixes p r q s::"real poly" and a b ::real
  assumes "a<b" "coprime q p" "coprime s r"
  shows "cindex_polyE a b (p * r - q * s) (p * s + q * r) 
        = cindex_polyE a b p q + cindex_polyE a b r s 
          - cross_alt (p * s + q * r) (q * s) a b / 2" (is "?L = ?R")
proof (cases "q=0 \<or> s=0 \<or> p=0 \<or> r=0 \<or> p * s + q * r = 0")
  case True
  moreover have ?thesis if "q=0"
  proof -
    have "p\<noteq>0" 
      using assms(2) coprime_poly_0 poly_0 that by blast
    then show ?thesis using that cindex_polyE_mult_cancel by simp
  qed
  moreover have ?thesis if "s=0"
  proof -
    have "r\<noteq>0" using assms(3) coprime_poly_0 poly_0 that by blast
    then have "?L = cindex_polyE a b (r * p) (r * q)"
      using that by (simp add:algebra_simps)
    also have "... = ?R"
      using that cindex_polyE_mult_cancel \<open>r\<noteq>0\<close> by simp
    finally show ?thesis .
  qed
  moreover have ?thesis if "p * s + q * r = 0" "s\<noteq>0" "q\<noteq>0"
  proof -
    have "cindex_polyE a b p q = cindex_polyE a b (s*p) (s*q)"
      using cindex_polyE_mult_cancel[OF \<open>s\<noteq>0\<close>] by simp
    also have "...  = cindex_polyE a b (-(q * r)) (q* s)"
      using that(1) 
      by (metis add.inverse_inverse add.inverse_unique mult.commute)
    also have "... = - cindex_polyE a b (q * r) (q* s)"
      using cindex_polyE_smult_1[where c="-1",simplified] by simp
    also have "... = - cindex_polyE a b r s"
      using cindex_polyE_mult_cancel[OF \<open>q\<noteq>0\<close>] by simp
    finally have "cindex_polyE a b p q = - cindex_polyE a b r s" .
    then show ?thesis using that(1) by simp
  qed
  moreover have ?thesis if "p=0"  
  proof -
    have "poly q a\<noteq>0" 
      using assms(2) coprime_poly_0 order_root that(1) by blast
    have "poly q b\<noteq>0"
      by (metis assms(2) coprime_poly_0 mpoly_base_conv(1) that)
    then have "q\<noteq>0"  using poly_0 by blast

    have "?L= - cindex_polyE a b s r"
      using that cindex_polyE_smult_1[where c="-1",simplified]
            cindex_polyE_mult_cancel[OF \<open>q\<noteq>0\<close>]
      by simp
    also have "... = cindex_polyE a b r s  - (cross_alt r s a b) / 2"
      apply (subst cindex_polyE_inverse_add_cross[symmetric])
      using \<open>a<b\<close> \<open>coprime s r\<close> by (auto simp:coprime_commute)
    also have "... = ?R"
      using \<open>p=0\<close> \<open>poly q a\<noteq>0\<close> \<open>poly q b\<noteq>0\<close> cross_alt_cancel
      by simp
    finally show ?thesis .
  qed
  moreover have ?thesis if "r=0" 
  proof -
    have "poly s a\<noteq>0" 
      using assms(3) coprime_poly_0 order_root that by blast
    have "poly s b\<noteq>0"
      using assms(3) coprime_poly_0 order_root that by blast
    then have "s\<noteq>0" using poly_0 by blast

    have "cindex_polyE a b (- (q * s)) (p * s)
          = - cindex_polyE a b (q * s) (p * s)"
      using cindex_polyE_smult_1[where c="-1",simplified] by auto
    also have "... = - cindex_polyE a b (s * q) (s * p)"
      by (simp add:algebra_simps)
    also have "... = -  cindex_polyE a b q p"
      using cindex_polyE_mult_cancel[OF \<open>s\<noteq>0\<close>] by simp
    finally have "cindex_polyE a b (- (q * s)) (p * s) 
        = - cindex_polyE a b q p" .
    moreover have "cross_alt (p * s) (q * s) a b / 2 
        = cindex_polyE a b q p + cindex_polyE a b p q" 
    proof -
      have "cross_alt (p * s) (q * s) a b 
              = cross_alt (s * p) (s * q) a b"
        by (simp add:algebra_simps)
      also have "... = cross_alt p q a b"
        using cross_alt_cancel by (simp add: \<open>poly s a \<noteq> 0\<close> \<open>poly s b \<noteq> 0\<close>)
      also have "... / 2 =  cindex_polyE a b q p + cindex_polyE a b p q"
        apply (subst cindex_polyE_inverse_add_cross[symmetric])
        using \<open>a<b\<close> \<open>coprime q p\<close> coprime_commute by auto
      finally show ?thesis .
    qed
    ultimately show ?thesis using that by simp
  qed
  ultimately show ?thesis by argo
next
  case False
  define P where "P=(p * s + q * r)"
  define Q where "Q = q * s * P"

  from False have "q\<noteq>0" "s\<noteq>0" "p\<noteq>0" "r\<noteq>0" "P \<noteq> 0" "Q\<noteq>0"
    unfolding P_def Q_def by auto
  then have finite:"finite (proots_within Q {x. a\<le>x \<and> x\<le>b})"
    unfolding P_def Q_def
    by (auto intro: finite_proots)

  have sign_pos_eq:
      "sign_r_pos Q a = (poly Q b>0)" 
      "poly Q a \<noteq>0 \<Longrightarrow> poly Q a >0 = (poly Q b>0)" 
    if "a<b" and noroot:"\<forall>x. a<x \<and> x\<le>b \<longrightarrow> poly Q x\<noteq>0" for a b Q
  proof -
    have "sign_r_pos Q a = (sgnx (poly Q) (at_right a) >0)"
      unfolding sign_r_pos_sgnx_iff by simp
    also have "...  = (sgnx (poly Q) (at_left b) >0)"
    proof (rule ccontr)
      assume "(0 < sgnx (poly Q) (at_right a)) 
                  \<noteq> (0 < sgnx (poly Q) (at_left b))"
      then have "\<exists>x>a. x < b \<and> poly Q x = 0"
        using sgnx_at_left_at_right_IVT[OF _ \<open>a<b\<close>] by auto
      then show False using that(2) by auto
    qed
    also have "... =  (poly Q b>0)"
      apply (subst sgnx_poly_nz)
      using that by auto
    finally show "sign_r_pos Q a = (poly Q b>0)"  .
    show "(poly Q a >0)  = (poly Q b>0)" if "poly Q a\<noteq>0"
    proof (rule ccontr)
      assume "(0 < poly Q a) \<noteq> (0 < poly Q b)"
      then have "poly Q a * poly Q b < 0"
        by (metis \<open>sign_r_pos Q a = (0 < poly Q b)\<close> poly_0 sign_r_pos_rec that)
      from poly_IVT[OF \<open>a<b\<close> this]
      have "\<exists>x>a. x < b \<and> poly Q x = 0" .
      then show False using noroot by auto
    qed
  qed

  define Case where "Case=(\<lambda>a b. cindex_polyE a b (p * r - q * s) P 
                                  = cindex_polyE a b p q + cindex_polyE a b r s 
                                       - (cross_alt P (q * s) a b) / 2)"

  have basic_case:"Case a b" 
    if noroot0:"proots_within Q {x. a<x \<and> x<b} = {}"
      and noroot_disj:"poly Q a\<noteq>0 \<or> poly Q b\<noteq>0"
      and "a<b"
    for a b
  proof -
    let ?thesis' = "\<lambda>p r q s a. cindex_polyE a b (p * r - q * s) (p * s + q * r) =
                        cindex_polyE a b p q + cindex_polyE a b r s -
                            (cross_alt (p * s + q * r) (q * s) a b) / 2"
    have base_case:"?thesis' p r q s a" 
        if "proots_within (q * s * (p * s + q * r)) {x. a < x \<and> x \<le> b} = {}"
           and "coprime q p" "coprime s r"
            "q\<noteq>0" "s\<noteq>0" "p\<noteq>0" "r\<noteq>0" "p * s + q * r \<noteq> 0"
            "a<b"
          for p r q s a 
    proof -
      define P where "P=(p * s + q * r)"
      have noroot1:"proots_within (q * s * P) {x. a < x \<and> x \<le> b} = {}"
        using that(1) unfolding P_def .
      have "P\<noteq>0" using \<open>p * s + q * r \<noteq> 0\<close> unfolding P_def by simp

      have cind1:"cindex_polyE a b (p * r - q * s) P
            = (if poly P a = 0 then jumpF_polyR (p * r - q * s) P a else 0)"
      proof -
        have "cindex_poly a b (p * r - q * s) P = 0"
          apply (rule cindex_poly_noroot[OF \<open>a<b\<close>])
          using noroot1 by fastforce
        moreover have "jumpF_polyL (p * r - q * s) P b  = 0"
          apply (rule jumpF_poly_noroot)
          using noroot1 \<open>a<b\<close> by auto
        ultimately show ?thesis
          unfolding cindex_polyE_def by (simp add: jumpF_poly_noroot(2))
      qed
      have cind2:"cindex_polyE a b p q 
            = (if poly q a = 0 then jumpF_polyR p q a else 0)"
      proof -
        have "cindex_poly a b p q = 0" 
          apply (rule cindex_poly_noroot)
          using noroot1 \<open>a<b\<close> by auto fastforce
        moreover have "jumpF_polyL p q b = 0" 
          apply (rule jumpF_poly_noroot)
          using noroot1 \<open>a<b\<close> by auto
        ultimately show ?thesis
          unfolding cindex_polyE_def 
          by (simp add: jumpF_poly_noroot(2))
      qed
      have cind3:"cindex_polyE a b r s 
            = (if poly s a = 0 then jumpF_polyR r s a else 0)"
      proof -
        have "cindex_poly a b r  s = 0" 
          apply (rule cindex_poly_noroot)
          using noroot1 \<open>a<b\<close> by auto fastforce
        moreover have "jumpF_polyL r s b = 0" 
          apply (rule jumpF_poly_noroot)
          using noroot1 \<open>a<b\<close> by auto
        ultimately show ?thesis
          unfolding cindex_polyE_def 
          by (simp add: jumpF_poly_noroot(2))
      qed
  
      have ?thesis if "poly (q * s * P) a\<noteq>0"
      proof -
        have noroot2:"proots_within (q * s * P) {x. a\<le>x \<and> x\<le>b} = {}"
          using that noroot1 by force
        have "cindex_polyE a b (p * r - q * s) P = 0"
          apply (rule cindex_polyE_noroot)
          using noroot2 \<open>a < b\<close> by auto
        moreover have "cindex_polyE a b p q = 0"
          apply (rule cindex_polyE_noroot)
          using noroot2 \<open>a < b\<close> by auto
        moreover have "cindex_polyE a b r s = 0"
          apply (rule cindex_polyE_noroot)
          using noroot2 \<open>a < b\<close> by auto
        moreover have "cross_alt P (q * s) a b = 0"
          apply (rule cross_alt_noroot[OF \<open>a<b\<close>])
          using noroot2 by auto
        ultimately show ?thesis unfolding P_def by auto
      qed
      moreover have ?thesis if "poly (q * s * P) a=0"
      proof -
        have ?thesis if "poly q a =0" "poly s a\<noteq>0" 
        proof -
          have "poly P a\<noteq>0"
            using that coprime_poly_0[OF \<open>coprime q p\<close>] unfolding P_def
            by simp
          then have "cindex_polyE a b (p * r - q * s) P = 0"
            using cind1 by auto
          moreover have "cindex_polyE a b p q = (cross_alt P (q * s) a b) / 2" 
          proof -
            have "cindex_polyE a b p q = jumpF_polyR p q a"
              using cind2 that(1) by auto
            also have "... = (cross_alt 1 (q * s * P) a b) / 2" 
            proof -
              have sign_eq:"(sign_r_pos q a \<longleftrightarrow> poly p a>0)
                         = (poly (q * s * P) b > 0)"
              proof -
                have "(sign_r_pos q a \<longleftrightarrow> poly p a>0)
                      = (sgnx (poly (q*p)) (at_right a) >0)"
                proof -
                  have "(poly p a>0) = (sgnx (poly p) (at_right a) > 0)"
                    apply (subst sgnx_poly_nz)
                    using \<open>coprime q p\<close> coprime_poly_0 that(1) by auto
                  then show ?thesis
                    unfolding sign_r_pos_sgnx_iff 
                    apply (subst sgnx_poly_times[of _  a])
                    subgoal by simp
                    using poly_sgnx_values \<open>p\<noteq>0\<close> \<open>q\<noteq>0\<close>
                    by (metis (no_types, opaque_lifting) add.inverse_inverse 
                        mult.right_neutral mult_minus_right zero_less_one)
                qed
                also have "... = (sgnx (poly ((q*p) * s^2)) (at_right a) > 0)"
                proof (subst (2) sgnx_poly_times)
                  have "sgnx (poly (s\<^sup>2)) (at_right a) > 0"
                    using sgn_zero_iff sgnx_poly_nz(2) that(2) by auto
                  then show "(0 < sgnx (poly (q * p)) (at_right a)) =
                        (0 < sgnx (poly (q * p)) (at_right a) 
                        * sgnx (poly (s\<^sup>2)) (at_right a))" 
                    by (simp add: zero_less_mult_iff)
                qed auto
                also have "... = (sgnx (poly (q * s)) (at_right a) 
                    * sgnx (poly (p * s)) (at_right a)> 0)"
                  unfolding power2_eq_square
                  apply (subst sgnx_poly_times[where x=a],simp)+
                  by (simp add:algebra_simps)
                also have "... = (sgnx (poly (q * s)) (at_right a) 
                    * sgnx (poly P) (at_right a)> 0)"
                proof -
                  have "sgnx (poly P) (at_right a) =  
                          sgnx (poly (q * r + p * s)) (at_right a)"
                    unfolding P_def by (simp add:algebra_simps)
                  also have "... = sgnx (poly (p * s)) (at_right a)"
                    apply (rule sgnx_poly_plus[where x=a])
                    subgoal using \<open>poly q a=0\<close> by simp
                    subgoal using \<open>coprime q p\<close> coprime_poly_0 poly_mult_zero_iff 
                        that(1) that(2) by blast
                    by simp
                  finally show ?thesis by auto
                qed
                also have "... = (0 < sgnx (poly (q * s * P)) (at_right a))"
                  apply (subst sgnx_poly_times[where x=a],simp)+
                  by (simp add:algebra_simps)
                also have "... = (0 < sgnx (poly (q * s * P)) (at_left b))"
                proof -
                  have "sgnx (poly (q * s * P)) (at_right a) 
                        = sgnx (poly (q * s * P)) (at_left b)"
                  proof (rule ccontr)
                    assume "sgnx (poly (q * s * P)) (at_right a) 
                                \<noteq> sgnx (poly (q * s * P)) (at_left b)"
                    from sgnx_at_left_at_right_IVT[OF this \<open>a<b\<close>]
                    have "\<exists>x>a. x < b \<and> poly (q * s * P) x = 0" .
                    then show False using noroot1 by fastforce
                  qed
                  then show ?thesis by auto
                qed
                also have "... = (poly (q * s * P) b > 0)"
                  apply (subst sgnx_poly_nz)
                  using noroot1 \<open>a<b\<close> by auto
                finally show ?thesis .
              qed
              have psign_a:"psign_diff 1 (q * s * P) a = 1"
                unfolding psign_diff_def using \<open>poly (q * s * P) a=0\<close>
                by simp
  
              have "poly (q * s * P) b \<noteq>0" 
                using noroot1 \<open>a<b\<close> by blast
              moreover have ?thesis if "poly (q * s * P) b >0"
              proof -
                have "psign_diff 1 (q * s * P) b = 0"
                  using that unfolding psign_diff_def by auto
                moreover have "jumpF_polyR p q a = 1/2" 
                  unfolding jumpF_polyR_coprime[OF \<open>coprime q p\<close>]
                  using \<open>p \<noteq> 0\<close> \<open>poly q a = 0\<close> \<open>q \<noteq> 0\<close> sign_eq that by presburger
                ultimately show ?thesis 
                  unfolding cross_alt_def using psign_a by auto
              qed
              moreover have ?thesis if "poly (q * s * P) b <0"
              proof -
                have "psign_diff 1 (q * s * P) b = 2"
                  using that unfolding psign_diff_def by auto
                moreover have "jumpF_polyR p q a = - 1/2" 
                  unfolding jumpF_polyR_coprime[OF \<open>coprime q p\<close>]
                  using \<open>p \<noteq> 0\<close> \<open>poly q a = 0\<close> \<open>q \<noteq> 0\<close> sign_eq that by auto
                ultimately show ?thesis 
                  unfolding cross_alt_def using psign_a by auto
              qed
              ultimately show ?thesis by argo
            qed
            also have "... = (cross_alt P (q * s) a b) / 2"
              apply (subst cross_alt_clear[symmetric])
              using \<open>poly P a \<noteq> 0\<close> noroot1 \<open>a<b\<close> cross_alt_poly_commute
              by auto
            finally show ?thesis .
          qed
          moreover have "cindex_polyE a b r s = 0"
            using cind3 that by auto
          ultimately show ?thesis using that 
            apply (fold P_def)
            by auto
        qed
        moreover have ?thesis if "poly q a \<noteq>0" "poly s a=0" 
        proof -
          have "poly P a\<noteq>0"
            using that coprime_poly_0[OF \<open>coprime s r\<close>] unfolding P_def
            by simp
          then have "cindex_polyE a b (p * r - q * s) P = 0"
            using cind1 by auto
          moreover have "cindex_polyE a b r s = (cross_alt P (q * s) a b) / 2" 
          proof -
            have "cindex_polyE a b r s = jumpF_polyR r s a"
              using cind3 that by auto
            also have "... = (cross_alt 1 (s * q * P) a b) / 2" 
            proof -
              have sign_eq:"(sign_r_pos s a \<longleftrightarrow> poly r a>0)
                         = (poly (s * q * P) b > 0)"
              proof -
                have "(sign_r_pos s a \<longleftrightarrow> poly r a>0)
                      = (sgnx (poly (s*r)) (at_right a) >0)"
                proof -
                  have "(poly r a>0) = (sgnx (poly r) (at_right a) > 0)"
                    apply (subst sgnx_poly_nz)
                    using \<open>coprime s r\<close> coprime_poly_0 that(2) by auto
                  then show ?thesis
                    unfolding sign_r_pos_sgnx_iff 
                    apply (subst sgnx_poly_times[of _  a])
                    subgoal by simp
                    subgoal using \<open>r \<noteq> 0\<close> \<open>s \<noteq> 0\<close>
                      by (metis (no_types, opaque_lifting) add.inverse_inverse
                          mult.right_neutral mult_minus_right poly_sgnx_values(2) 
                          zero_less_one)
                    done
                qed
                also have "... = (sgnx (poly ((s*r) * q^2)) (at_right a) > 0)"
                proof (subst (2) sgnx_poly_times)
                  have "sgnx (poly (q\<^sup>2)) (at_right a) > 0"
                    by (metis \<open>q \<noteq> 0\<close> power2_eq_square sign_r_pos_mult sign_r_pos_sgnx_iff)
                  then show "(0 < sgnx (poly (s * r)) (at_right a)) =
                        (0 < sgnx (poly (s * r)) (at_right a) 
                        * sgnx (poly (q\<^sup>2)) (at_right a))" 
                    by (simp add: zero_less_mult_iff)
                qed auto
                also have "... = (sgnx (poly (s * q)) (at_right a) 
                    * sgnx (poly (r * q)) (at_right a)> 0)"
                  unfolding power2_eq_square
                  apply (subst sgnx_poly_times[where x=a],simp)+
                  by (simp add:algebra_simps)
                also have "... = (sgnx (poly (s * q)) (at_right a) 
                    * sgnx (poly P) (at_right a)> 0)"
                proof -
                  have "sgnx (poly P) (at_right a) =  
                          sgnx (poly (p * s + q * r )) (at_right a)"
                    unfolding P_def by (simp add:algebra_simps)
                  also have "... = sgnx (poly (q * r)) (at_right a)"
                    apply (rule sgnx_poly_plus[where x=a])
                    subgoal using \<open>poly s a=0\<close> by simp
                    subgoal 
                      using \<open>coprime s r\<close> coprime_poly_0 poly_mult_zero_iff that(1) 
                        that(2) by blast
                    by simp
                  finally show ?thesis by (auto simp:algebra_simps)
                qed
                also have "... = (0 < sgnx (poly (s * q * P)) (at_right a))"
                  apply (subst sgnx_poly_times[where x=a],simp)+
                  by (simp add:algebra_simps)
                also have "... = (0 < sgnx (poly (s * q * P)) (at_left b))"
                proof -
                  have "sgnx (poly (s * q * P)) (at_right a) 
                        = sgnx (poly (s * q * P)) (at_left b)"
                  proof (rule ccontr)
                    assume "sgnx (poly (s * q * P)) (at_right a) 
                                \<noteq> sgnx (poly (s * q * P)) (at_left b)"
                    from sgnx_at_left_at_right_IVT[OF this \<open>a<b\<close>]
                    have "\<exists>x>a. x < b \<and> poly (s * q * P) x = 0" .
                    then show False using noroot1 by fastforce
                  qed
                  then show ?thesis by auto
                qed
                also have "... = (poly (s * q * P) b > 0)"
                  apply (subst sgnx_poly_nz)
                  using noroot1 \<open>a<b\<close> by auto
                finally show ?thesis .
              qed
              have psign_a:"psign_diff 1 (s * q * P) a = 1"
                unfolding psign_diff_def using \<open>poly (q * s * P) a=0\<close>
                by (simp add:algebra_simps)
  
              have "poly (s * q * P) b \<noteq>0" 
                using noroot1 \<open>a<b\<close> by (auto simp:algebra_simps)
              moreover have ?thesis if "poly (s * q * P) b >0"
              proof -
                have "psign_diff 1 (s * q * P) b = 0"
                  using that unfolding psign_diff_def by auto
                moreover have "jumpF_polyR r s a = 1/2" 
                  unfolding jumpF_polyR_coprime[OF \<open>coprime s r\<close>]
                  using \<open>poly s a = 0\<close> \<open>r \<noteq> 0\<close> \<open>s \<noteq> 0\<close> sign_eq that by presburger
                ultimately show ?thesis 
                  unfolding cross_alt_def using psign_a by auto
              qed
              moreover have ?thesis if "poly (s * q * P) b <0"
              proof -
                have "psign_diff 1 (s * q * P) b = 2"
                  using that unfolding psign_diff_def by auto
                moreover have "jumpF_polyR r s a = - 1/2" 
                  unfolding jumpF_polyR_coprime[OF \<open>coprime s r\<close>]
                  using \<open>poly s a = 0\<close> \<open>r \<noteq> 0\<close> sign_eq that by auto
                ultimately show ?thesis 
                  unfolding cross_alt_def using psign_a by auto
              qed
              ultimately show ?thesis by argo
            qed
            also have "... = (cross_alt P (q * s) a b) / 2"
              apply (subst cross_alt_clear[symmetric])
              using \<open>poly P a \<noteq> 0\<close> noroot1 \<open>a<b\<close> cross_alt_poly_commute
              by (auto simp:algebra_simps)
            finally show ?thesis .
          qed
          moreover have "cindex_polyE a b p q = 0"
            using cind2 that by auto
          ultimately show ?thesis using that 
            apply (fold P_def)
            by auto
        qed  
        moreover have ?thesis if "poly P a =0" "poly q a\<noteq>0" "poly s a\<noteq>0" 
        proof -
          have "cindex_polyE a b (p * r - q * s) P  
              = jumpF_polyR (p * r - q * s) P a"
            using cind1 that by auto
          also have "... = (if sign_r_pos P a = (0 < poly (p * r - q * s) a) 
            then 1 / 2 else - 1 / 2)" (is "_ = ?R")
          proof (subst jumpF_polyR_coprime')
            let ?C="(P \<noteq> 0 \<and> p * r - q * s \<noteq> 0 \<and> poly P a = 0)"
            have "?C"
              by (smt (z3) P_def \<open>P \<noteq> 0\<close> add.left_neutral diff_add_cancel 
                  poly_add poly_mult_zero_iff sign_r_pos_mult sign_r_pos_rec that(1) that(2) that(3))
            then show "(if ?C then ?R else 0) = ?R" by auto
            show "poly P a \<noteq> 0 \<or> poly (p * r - q * s) a \<noteq> 0" 
              by (smt (z3) P_def mult_less_0_iff poly_add poly_diff poly_mult 
                  poly_mult_zero_iff that(2) that(3))
          qed
          also have "... = - cross_alt P (q * s) a b / 2"
          proof -
            have "(sign_r_pos P a = (0 < poly (p * r - q * s) a))
                    =(\<not> (poly (q * s * P) b > 0))" 
            proof -
              have "(poly (q * s * P) b > 0) 
                      = (sgnx (poly (q * s * P)) (at_left b) >0)"
                apply (subst sgnx_poly_nz)
                using noroot1 \<open>a<b\<close> by auto
              also have "... = (sgnx (poly (q * s * P)) (at_right a) >0)"
              proof (rule ccontr)
                define F where "F=(q * s * P)"
                assume "(0 < sgnx (poly F) (at_left b)) 
                            \<noteq> (0 < sgnx (poly F) (at_right a))"
                then have "sgnx (poly F) (at_right a) \<noteq> sgnx (poly F) (at_left b)"
                  by auto
                then have "\<exists>x>a. x < b \<and> poly F x = 0"
                  using sgnx_at_left_at_right_IVT[OF _ \<open>a<b\<close>] by auto
                then show False using noroot1[folded F_def] \<open>a<b\<close> by fastforce
              qed
              also have "... = sign_r_pos (q * s * P) a"
                using sign_r_pos_sgnx_iff by simp
              also have "... = (sign_r_pos P a = sign_r_pos (q * s) a)"
                apply (subst sign_r_pos_mult[symmetric])
                using \<open>P\<noteq>0\<close> \<open>q\<noteq>0\<close> \<open>s\<noteq>0\<close> by (auto simp add:algebra_simps)
              also have "... = (sign_r_pos P a = (0 \<ge> poly (p * r - q * s) a))" 
              proof -
                have "sign_r_pos (q * s) a=(poly (q * s) a > 0)"
                  by (metis poly_0 poly_mult_zero_iff sign_r_pos_rec 
                      that(2) that(3))
                also have "... = (0 \<ge> poly (p * r - q * s) a)"
                  using \<open>poly P a =0\<close> unfolding P_def 
                  by (smt (verit, ccfv_threshold) \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close> \<open>r \<noteq> 0\<close> \<open>s \<noteq> 0\<close> divisors_zero 
                      poly_add poly_diff poly_mult_zero_iff sign_r_pos_mult sign_r_pos_rec that(2) 
                      that(3))
                finally show ?thesis by simp
              qed
              finally have "(0 < poly (q * s * P) b) 
                = (sign_r_pos P a = (poly (p * r - q * s) a \<le> 0))" .
              then show ?thesis by argo
            qed
            moreover have "cross_alt P (q * s) a b = 
                (if poly (q * s * P) b > 0 then 1 else -1)"
            proof -
              have "psign_diff P (q * s) a = 1" 
                by (smt (verit, ccfv_threshold) Sturm_Tarski.sign_def 
                    dvd_div_mult_self gcd_dvd1 gcd_dvd2 poly_mult_zero_iff 
                    psign_diff_def that(1) that(2) that(3))
              moreover have "psign_diff P (q * s) b 
                      = (if poly (q * s * P) b > 0 then 0 else 2)" 
              proof -
                define F where "F = q * s * P"
                have "psign_diff P (q * s) b = psign_diff 1 F b"
                  apply (subst psign_diff_clear)
                  using noroot1 \<open>a<b\<close> unfolding F_def 
                  by (auto simp:algebra_simps)
                also have "... = (if 0 < poly F b then 0 else 2)"
                proof -
                  have "poly F b\<noteq>0" 
                    unfolding F_def using \<open>a<b\<close> noroot1 by auto
                  then show ?thesis 
                    unfolding psign_diff_def by auto
                qed
                finally show ?thesis unfolding F_def .
              qed
              ultimately show ?thesis unfolding cross_alt_def by auto
            qed
            ultimately show ?thesis by auto
          qed
          finally have "cindex_polyE a b (p * r - q * s) P 
                            = - cross_alt P (q * s) a b / 2 "  .
          moreover have "cindex_polyE a b p q = 0" 
            using cind2 that by auto
          moreover have "cindex_polyE a b r s = 0" 
            using cind3 that by auto
          ultimately show ?thesis 
            by (fold P_def) auto
        qed
        moreover have ?thesis if "poly q a=0" "poly s a=0"
        proof -
          have "poly p a\<noteq>0" 
            using \<open>coprime q p\<close> coprime_poly_0 that(1) by blast
          have "poly r a\<noteq>0"
            using \<open>coprime s r\<close> coprime_poly_0 that(2) by blast
          have "poly P a=0" 
            unfolding P_def using that by simp
  
          define ff where "ff=(\<lambda>x. if x then 1/(2::real) else -1/2)"
          define C1 C2 C3 C4 C5 where "C1 = (sign_r_pos P a)"
                and "C2 =(0 < poly p a)"
                and "C3= (0 < poly r a)"
                and "C4=(sign_r_pos q a)"
                and "C5=(sign_r_pos s a)"
          note CC_def = C1_def C2_def C3_def C4_def C5_def
  
          have "cindex_polyE a b (p * r - q * s) P = ff ((C1 = C2) = C3)"
          proof -
            have "cindex_polyE a b (p * r - q * s) P 
                       = jumpF_polyR (p * r - q * s) P a"
              using cind1 \<open>poly P a=0\<close> by auto
            also have "... = (ff (sign_r_pos P a 
                = (0 < poly (p * r - q * s) a)) )"
              unfolding ff_def
              apply (subst jumpF_polyR_coprime')
              subgoal 
                by (simp add: \<open>poly p a \<noteq> 0\<close> \<open>poly r a \<noteq> 0\<close> that(1))
              subgoal 
                by (smt (z3) \<open>P \<noteq> 0\<close> \<open>poly P a = 0\<close> 
                    \<open>poly P a \<noteq> 0 \<or> poly (p * r - q * s) a \<noteq> 0\<close> poly_0)
              done
            also have "... = (ff (sign_r_pos P a = (0 < poly (p * r) a)))"
            proof -
              have "(0 < poly (p * r - q * s) a) = (0 < poly (p * r) a)"
                by (simp add: that(1))
              then show ?thesis by simp
            qed
            also have "... = ff ((C1 = C2) = C3)"
              unfolding CC_def
              by (smt (z3) \<open>p \<noteq> 0\<close> \<open>poly p a \<noteq> 0\<close> \<open>poly r a \<noteq> 0\<close> \<open>r \<noteq> 0\<close> no_zero_divisors 
                  poly_mult_zero_iff sign_r_pos_mult sign_r_pos_rec)
            finally show ?thesis .
          qed
          moreover have "cindex_polyE a b p q
             = ff (C4 = C2)"
          proof -
            have "cindex_polyE a b p q = jumpF_polyR p q a"
              using cind2 \<open>poly q a=0\<close> by auto
            also have "... = ff (sign_r_pos q a = (0 < poly p a))"
              apply (subst jumpF_polyR_coprime')
              subgoal using \<open>poly p a \<noteq> 0\<close> by auto
              subgoal using \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close> ff_def that(1) by presburger
              done
            also have "... = ff (C4 = C2)"
              using \<open>a<b\<close> noroot1 unfolding CC_def by auto
            finally show ?thesis .
          qed
          moreover have " cindex_polyE a b r s = ff (C5 = C3)"
          proof -
            have "cindex_polyE a b r s = jumpF_polyR r s a"
              using cind3 \<open>poly s a=0\<close> by auto
            also have "... = ff (sign_r_pos s a = (0 < poly r a))"
              apply (subst jumpF_polyR_coprime')
              subgoal using \<open>poly r a \<noteq> 0\<close> by auto
              subgoal using \<open>r \<noteq> 0\<close> \<open>s \<noteq> 0\<close> ff_def that(2) by presburger
              done
            also have "... = ff (C5 = C3)"
              using \<open>a<b\<close> noroot1 unfolding CC_def by auto
            finally show ?thesis .
          qed
          moreover have "cross_alt P (q * s) a b = 2 * ff ((C1 = C4) = C5)"
          proof -
            have "cross_alt P (q * s) a b 
                      = sign (poly P b * (poly q b * poly s b))"
              apply (subst cross_alt_clear)
              apply (subst cross_alt_alt)
              using that by auto
            also have "...  = 2 * ff ((C1 = C4) = C5)"
            proof -
              have "sign_r_pos P a = (poly P b>0)"
                apply (rule sign_pos_eq)
                using \<open>a<b\<close> noroot1 by auto
              moreover have "sign_r_pos q a = (poly q b>0)" 
                apply (rule sign_pos_eq)
                using \<open>a<b\<close> noroot1 by auto
              moreover have "sign_r_pos s a = (poly s b>0)" 
                apply (rule sign_pos_eq)
                using \<open>a<b\<close> noroot1 by auto
              ultimately show ?thesis
                unfolding CC_def ff_def
                apply (simp add:sign_times)
                using noroot1 \<open>a<b\<close> by (auto simp:sign_def)
            qed
            finally show ?thesis .
          qed
          ultimately have "?thesis = (ff ((C1 = C2) = C3) = ff (C4 = C2) + 
                              ff (C5 = C3) - ff ((C1 = C4) = C5))"
            by (fold P_def) auto
          moreover have "ff ((C1 = C2) = C3) = ff (C4 = C2) + 
                              ff (C5 = C3) - ff ((C1 = C4) = C5)"
          proof -
            have pp:"(0 < poly p a) = sign_r_pos p a"
              apply (subst sign_r_pos_rec)
              using \<open>poly p a\<noteq>0\<close> by auto
            have rr:"(0 < poly r a) = sign_r_pos r a"
                apply (subst sign_r_pos_rec)
              using \<open>poly r a\<noteq>0\<close> by auto
  
            have "C1" if "C2=C5" "C3=C4"
            proof -
              have "sign_r_pos (p * s) a"
                apply (subst sign_r_pos_mult)
                using pp \<open>C2=C5\<close> \<open>p\<noteq>0\<close> \<open>s\<noteq>0\<close> unfolding CC_def by auto
              moreover have "sign_r_pos (q * r) a"
                apply (subst sign_r_pos_mult)
                using rr \<open>C3=C4\<close> \<open>q\<noteq>0\<close> \<open>r\<noteq>0\<close> unfolding CC_def by auto
              ultimately show ?thesis unfolding CC_def P_def
                using sign_r_pos_plus_imp by auto
            qed
            moreover have foo2:"\<not>C1" if "C2\<noteq>C5" "C3\<noteq>C4" 
            proof -
              have "(0 < poly p a) = sign_r_pos (-s) a"
                apply (subst sign_r_pos_minus)
                using \<open>s\<noteq>0\<close> \<open>C2\<noteq>C5\<close> unfolding CC_def by auto
              then have "sign_r_pos (p * (-s)) a"
                apply (subst sign_r_pos_mult)
                unfolding pp using \<open>p\<noteq>0\<close> \<open>s\<noteq>0\<close> by auto
              moreover have "(0 < poly r a) = sign_r_pos (-q) a"
                apply (subst sign_r_pos_minus)
                using \<open>q\<noteq>0\<close> \<open>C3\<noteq>C4\<close> unfolding CC_def by auto
              then have "sign_r_pos (r * (-q)) a"
                apply (subst sign_r_pos_mult)
                unfolding rr using \<open>r\<noteq>0\<close> \<open>q\<noteq>0\<close> by auto
              ultimately have "sign_r_pos (p * (-s) + r * (-q)) a"
                using sign_r_pos_plus_imp by blast
              then have "sign_r_pos (- (p * s + q * r)) a"
                by (simp add:algebra_simps)
              then have "\<not> sign_r_pos P a"
                apply (subst sign_r_pos_minus)
                using \<open>P\<noteq>0\<close> unfolding P_def by auto
              then show ?thesis unfolding CC_def .
            qed
            ultimately show ?thesis unfolding ff_def by auto
          qed
          ultimately show ?thesis by simp
        qed
        ultimately show ?thesis using that by auto
      qed
      ultimately show ?thesis by auto
    qed

    have "?thesis' p r q s a" if "poly Q b \<noteq> 0"
      apply (rule base_case[OF  _ \<open>coprime q p\<close> \<open>coprime s r\<close>])
      subgoal using noroot0 that unfolding Q_def P_def by fastforce
      using False \<open>a<b\<close> by auto
    moreover have "?thesis' p r q s a" if "poly Q b = 0" 
    proof -
      have "poly Q a\<noteq>0" using noroot_disj that by auto

      define h where  "h=(\<lambda>p. p \<circ>\<^sub>p [:a + b, - 1:])"

      have h_rw:
          "h p - h q = h (p - q)"
          "h p * h q = h (p * q)"
          "h p + h q = h (p + q)"
          "cindex_polyE a b (h q) (h p) = - cindex_polyE a b q p"
          "cross_alt (h p) (h q) a b = cross_alt p q b a"
          for p q
        unfolding h_def pcompose_diff pcompose_mult pcompose_add
          cindex_polyE_linear_comp[OF \<open>a<b\<close>, of "-1" _ "a+b",simplified]
          cross_alt_linear_comp[of p "a+b" "-1" q a b,simplified]
        by simp_all
      have "?thesis' (h p) (h r) (h q) (h s) a"
      proof (rule base_case)
        have "proots_within (h q * h s * (h p * h s + h q * h r)) {x. a < x \<and> x \<le> b}
                = proots_within (h Q) {x. a < x \<and> x \<le> b}"
          unfolding Q_def P_def h_def
          by (simp add:pcompose_diff pcompose_mult pcompose_add)
        also have "...  = {}"
          unfolding proots_within_def h_def poly_pcompose
          using \<open>a<b\<close> that[folded Q_def] noroot0[unfolded P_def, folded Q_def] \<open>poly Q a\<noteq>0\<close>
          by (auto simp:order.order_iff_strict proots_within_def)
        finally show "proots_within (h q * h s * (h p * h s + h q * h r)) 
                        {x. a < x \<and> x \<le> b} = {}" . 
        show "coprime (h q) (h p)" unfolding h_def
          apply (rule coprime_linear_comp)
          using \<open>coprime q p\<close> by auto
        show "coprime (h s) (h r)" unfolding h_def
          apply (rule coprime_linear_comp)
          using \<open>coprime s r\<close> by auto
        show "h q \<noteq> 0" "h s \<noteq> 0" " h p \<noteq> 0" " h r \<noteq> 0"
          using False unfolding h_def 
          by (subst pcompose_eq_0;auto)+
        have "h (p * s + q * r) \<noteq> 0"
          using False unfolding h_def 
          by (subst pcompose_eq_0;auto)
        then show "h p * h s + h q * h r \<noteq> 0"
          unfolding h_def pcompose_mult pcompose_add by simp
        show "a < b" by fact
      qed
      moreover have "cross_alt (p * s + q * r) (q * s) b a
                        = - cross_alt (p * s + q * r) (q * s) a b" 
        unfolding cross_alt_def by auto
      ultimately show ?thesis unfolding h_rw by auto
    qed
    ultimately show ?thesis unfolding Case_def P_def by blast
  qed

  show ?thesis using \<open>a<b\<close>
  proof (induct "card (proots_within (q * s * P) {x. a<x \<and> x\<le>b})" arbitrary:a)
    case 0
    have "Case a b"
    proof (rule basic_case)
      have *:"proots_within Q {x. a < x \<and> x \<le> b} = {}" 
        using 0 \<open>Q\<noteq>0\<close> unfolding Q_def by auto
      then show "proots_within Q {x. a < x \<and> x < b} = {}" by force
      show "poly Q a \<noteq> 0 \<or> poly Q b \<noteq> 0"
        using * \<open>a<b\<close> by blast
      show "a < b" by fact
    qed
    then show ?case unfolding Case_def P_def by simp
  next
    case (Suc n)

    define S where "S=(\<lambda>a. proots_within Q {x. a < x \<and> x \<le> b})"
    have Sa_Suc:"Suc n = card (S a)"
      using Suc(2) unfolding S_def Q_def by auto

    define mroot where "mroot = Min (S a)"
    have fin_S:"finite (S a)" for a
      using Suc(2) unfolding S_def Q_def
      by (simp add: \<open>P \<noteq> 0\<close> \<open>q \<noteq> 0\<close> \<open>s \<noteq> 0\<close>)
    have mroot_in:"mroot \<in> S a" and mroot_min:"\<forall>x\<in>S a. mroot\<le>x"
    proof -
      have "S a\<noteq>{}" 
        unfolding S_def Q_def using Suc.hyps(2) by force
      then show "mroot \<in> S a" unfolding mroot_def 
        using Min_in fin_S by auto
      show "\<forall>x\<in>S a. mroot\<le>x"
        using \<open>finite (S a)\<close> Min_le unfolding mroot_def by auto
    qed
    have mroot_nzero:"poly Q x\<noteq>0" if "a<x" "x<mroot" for x
      using mroot_in mroot_min that unfolding S_def 
      by (metis (no_types, lifting) dual_order.strict_trans leD 
          le_less_linear mem_Collect_eq proots_within_iff )

    define C1 where "C1=(\<lambda>a b. cindex_polyE a b (p * r - q * s) P)"
    define C2 where "C2=(\<lambda>a b. cindex_polyE a b p q)"
    define C3 where "C3=(\<lambda>a b. cindex_polyE a b r s)"
    define C4 where "C4=(\<lambda>a b. cross_alt P (q * s) a b)"
    note CC_def = C1_def C2_def C3_def C4_def
    
    
    have hyps:"C1 mroot b = C2 mroot b + C3 mroot b - C4 mroot b / 2"
      if "mroot < b"
      unfolding C1_def C2_def C3_def C4_def P_def
    proof (rule Suc.hyps(1)[OF _ that])
      have "Suc n = card (S a)" using Sa_Suc by auto
      also have "... = card (insert mroot (S mroot))" 
      proof -
        have "S a = proots_within Q {x. a < x \<and> x \<le> b}"
          unfolding S_def Q_def by simp
        also have "... = proots_within Q ({x. a < x \<and> x \<le> mroot} \<union> {x. mroot < x \<and> x \<le> b})"
          apply (rule arg_cong2[where f=proots_within])
          using mroot_in unfolding S_def by auto
        also have "... = proots_within Q {x. a < x \<and> x \<le> mroot} \<union> S mroot"
          unfolding S_def Q_def
          apply (subst proots_within_union)
          by auto
        also have "... = {mroot} \<union> S mroot"
        proof -
          have "proots_within Q {x. a < x \<and> x \<le> mroot} = {mroot}"
            using mroot_in  mroot_min unfolding S_def
            by auto force
          then show ?thesis by auto
        qed
        finally have "S a = insert mroot (S mroot)" by auto
        then show ?thesis by auto
      qed
      also have "... = Suc (card (S mroot))"
        apply (rule card_insert_disjoint)
        using fin_S unfolding S_def by auto
      finally have "Suc n = Suc (card (S mroot))" .
      then have "n = card (S mroot)" by simp
      then show "n = card (proots_within (q * s * P) {x. mroot < x \<and> x \<le> b})"
        unfolding S_def Q_def by simp
    qed

    have ?case if "mroot = b"
    proof -
      have nzero:"poly Q x \<noteq>0" if "a<x" "x<b" for x
        using mroot_nzero \<open>mroot = b\<close> that by auto

      define m where "m=(a+b)/2"
      have [simp]:"a<m" "m<b" using \<open>a<b\<close> unfolding m_def by auto

      have "Case a m"
      proof (rule basic_case)
        show "proots_within Q {x. a < x \<and> x < m} = {}"
          using nzero \<open>a<b\<close> unfolding m_def by auto
        have "poly Q m \<noteq> 0" using nzero \<open>a<m\<close> \<open>m<b\<close> by auto
        then show "poly Q a \<noteq> 0 \<or> poly Q m \<noteq> 0" by auto
      qed simp
      moreover have "Case m b"
      proof (rule basic_case)
        show "proots_within Q {x. m < x \<and> x < b} = {}"
          using nzero \<open>a<b\<close> unfolding m_def by auto
        have "poly Q m \<noteq> 0" using nzero \<open>a<m\<close> \<open>m<b\<close> by auto
        then show "poly Q m \<noteq> 0 \<or> poly Q b \<noteq> 0" by auto
      qed simp
      ultimately have "C1 a m + C1 m b = (C2 a m + C2 m b) 
                           + (C3 a m + C3 m b) - (C4 a m + C4 m b)/2"
        unfolding Case_def C1_def
        apply simp
        unfolding C2_def C3_def C4_def by (auto simp:algebra_simps)
      moreover have 
          "C1 a m + C1 m b = C1 a b"
          "C2 a m + C2 m b = C2 a b"
          "C3 a m + C3 m b = C3 a b"
        unfolding CC_def
        by (rule cindex_polyE_combine;auto)+
      moreover have "C4 a m + C4 m b = C4 a b"
        unfolding C4_def cross_alt_def by simp
      ultimately have "C1 a b = C2 a b + C3 a b - C4 a b/2"
        by auto
      then show ?thesis unfolding CC_def P_def by auto
    qed
    moreover have ?case if "mroot \<noteq>b"
    proof - 
      have [simp]:"a<mroot" "mroot < b" 
        using mroot_in that unfolding S_def by auto
      
      define m where "m=(a+mroot)/2"
      have [simp]:"a<m" "m<mroot" 
        using mroot_in unfolding m_def S_def by auto
      have "poly Q m \<noteq> 0" 
        by (rule mroot_nzero) auto

      have "C1 mroot b = C2 mroot b + C3 mroot b - C4 mroot b / 2" 
        using hyps \<open>mroot<b\<close> by simp
      moreover have "Case a m" 
        apply (rule basic_case)
        subgoal 
          by (smt (verit) Collect_empty_eq \<open>m < mroot\<close> mem_Collect_eq mroot_nzero proots_within_def)
        subgoal using \<open>poly Q m \<noteq> 0\<close> by auto
        by fact
      then have "C1 a m = C2 a m + C3 a m - C4 a m / 2"
        unfolding Case_def CC_def by auto
      moreover have "Case m mroot" 
        apply (rule basic_case)
        subgoal 
          by (smt (verit) Collect_empty_eq \<open>a < m\<close> mem_Collect_eq mroot_nzero proots_within_def)
        subgoal using \<open>poly Q m \<noteq> 0\<close> by auto
        by fact
      then have "C1 m mroot = C2 m mroot + C3 m mroot - C4 m mroot / 2" 
        unfolding Case_def CC_def by auto
      ultimately have "C1 a m + C1 m mroot + C1 mroot b =
                          (C2 a m + C2 m mroot + C2 mroot b)
                            + (C3 a m + C3 m mroot + C3 mroot b)
                              - (C4 a m + C4 m mroot + C4 mroot b) / 2"
        by simp (simp add:algebra_simps)
      moreover have 
          "C1 a m + C1 m mroot + C1 mroot b = C1 a b"
          "C2 a m + C2 m mroot + C2 mroot b = C2 a b"
          "C3 a m + C3 m mroot + C3 mroot b = C3 a b"
        unfolding CC_def 
        by (subst cindex_polyE_combine;simp?)+
      moreover have "C4 a m + C4 m mroot + C4 mroot b = C4 a b"
        unfolding C4_def cross_alt_def by simp
      ultimately have "C1 a b = C2 a b + C3 a b - C4 a b/2"
        by auto
      then show ?thesis unfolding CC_def P_def by auto
    qed
    ultimately show ?case by auto
  qed
qed


lemma cindex_polyE_product:
  fixes p r q s::"real poly" and a b ::real
  assumes "a<b" (*"p\<noteq>0 \<or> q\<noteq>0" "r\<noteq>0 \<or> s\<noteq>0"*) 
    and "poly p a\<noteq>0 \<or> poly q a\<noteq>0" "poly p b\<noteq>0 \<or> poly q b\<noteq>0"
    and "poly r a\<noteq>0 \<or> poly s a\<noteq>0" "poly r b\<noteq>0 \<or> poly s b\<noteq>0"
  shows "cindex_polyE a b (p * r - q * s) (p * s + q * r) 
        = cindex_polyE a b p q + cindex_polyE a b r s 
          - cross_alt (p * s + q * r) (q * s) a b / 2"
proof -
  define g1 where "g1 = gcd p q"
  obtain p' q' where pq:"p=g1*p'" "q=g1*q'" and "coprime q' p'"
    unfolding g1_def 
    by (metis assms(2) coprime_commute div_gcd_coprime dvd_mult_div_cancel gcd_dvd1 
        gcd_dvd2 order_root)

  define g2 where "g2 = gcd r s"
  obtain r' s' where rs:"r=g2*r'" "s = g2 * s'" "coprime s' r'"
    unfolding g2_def using assms(4) 
    by (metis coprime_commute div_gcd_coprime dvd_mult_div_cancel gcd_dvd1 gcd_dvd2 order_root)
  define g where "g=g1 * g2"
  have [simp]:"g\<noteq>0" "g1\<noteq>0" "g2\<noteq>0" 
    unfolding g_def g1_def g2_def 
    using assms by auto
  have [simp]:"poly g a \<noteq> 0" "poly g b \<noteq> 0" 
    unfolding g_def g1_def g2_def 
    subgoal by (metis assms(2) assms(4) poly_gcd_0_iff poly_mult_zero_iff)
    subgoal by (metis assms(3) assms(5) poly_gcd_0_iff poly_mult_zero_iff)
    done 

  have "cindex_polyE a b (p' * r' - q' * s') (p' * s' + q' * r') =
          cindex_polyE a b p' q' + cindex_polyE a b r' s' -
              (cross_alt (p' * s' + q' * r') (q' * s') a b) / 2"
    using cindex_polyE_product'[OF \<open>a<b\<close> \<open>coprime q' p'\<close> \<open>coprime s' r'\<close>] .
  moreover have "cindex_polyE a b (p * r - q * s) (p * s + q * r)
                     = cindex_polyE a b (g*(p' * r' - q' * s')) (g*(p' * s' + q' * r'))"
    unfolding pq rs g_def by (auto simp:algebra_simps)
  then have "cindex_polyE a b (p * r - q * s) (p * s + q * r)
                     = cindex_polyE a b (p' * r' - q' * s') (p' * s' + q' * r')"
    apply (subst (asm) cindex_polyE_mult_cancel)
    by simp
  moreover have "cindex_polyE a b p q =  cindex_polyE a b p' q'"
    unfolding pq using cindex_polyE_mult_cancel by simp
  moreover have "cindex_polyE a b r s  =cindex_polyE a b r' s'"
    unfolding rs using cindex_polyE_mult_cancel by simp
  moreover have "cross_alt (p * s + q * r) (q * s) a b 
                    = cross_alt (g*(p' * s' + q' * r')) (g*(q' * s')) a b "
    unfolding pq rs g_def by (auto simp:algebra_simps)
  then have "cross_alt (p * s + q * r) (q * s) a b 
                    = cross_alt (p' * s' + q' * r') (q' * s') a b "
    apply (subst (asm) cross_alt_cancel)
    by simp_all
  ultimately show ?thesis by auto
qed

(*TODO: move to Winding_Number_Eval*)
lemma cindex_pathE_linepath_on:
  assumes "z \<in> closed_segment a b"
  shows "cindex_pathE (linepath a b) z  = 0"
proof -
  obtain u where "0\<le>u" "u\<le>1" 
      and z_eq:"z = complex_of_real (1 - u) * a + complex_of_real u * b" 
    using assms unfolding in_segment scaleR_conv_of_real
    by auto

  define U where "U = [:-u, 1:]"
  have "U\<noteq>0" unfolding U_def by auto

  have "cindex_pathE (linepath a b) z
        = cindexE 0 1 (\<lambda>t. (Im a + t * Im b - (Im z + t * Im a)) 
                          / (Re a + t * Re b - (Re z + t * Re a)))"
    unfolding cindex_pathE_def
    by (simp add:linepath_def algebra_simps)
  also have "...  = cindexE 0 1
     (\<lambda>t. ( (Im b - Im a) * (t-u)) 
        / ( (Re b - Re a) * (t-u)))"
    unfolding z_eq
    by (simp add:algebra_simps)
  also have "... = cindex_polyE 0 1 (U*[:Im b - Im a:]) (U*[:Re b - Re a:])"
  proof (subst cindexE_eq_cindex_polyE[symmetric])
    have " (Im b - Im a) * (t - u) / ((Re b - Re a) * (t - u))
            =  poly (U * [:Im b - Im a:]) t / poly (U * [:Re b - Re a:]) t" for t
      unfolding U_def by (simp add:algebra_simps)
    then show "cindexE 0 1 (\<lambda>t. (Im b - Im a) * (t - u) / ((Re b - Re a) * (t - u))) =
                  cindexE 0 1 (\<lambda>x. poly (U * [:Im b - Im a:]) x / poly (U * [:Re b - Re a:]) x)"
      by auto
  qed simp
  also have "... = cindex_polyE 0 1 [:Im b - Im a:] [:Re b - Re a:]"
    apply (rule cindex_polyE_mult_cancel)
    by fact
  also have "... = cindexE 0 1 (\<lambda>x. (Im b - Im a) / (Re b - Re a))"
    apply (subst cindexE_eq_cindex_polyE[symmetric])
    by auto
  also have "... = 0"
    apply (rule cindexE_constI)
    by auto
  finally show ?thesis .
qed

subsection \<open>More Cauchy indices on polynomials\<close>

definition cindexP_pathE::"complex poly \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow> real" where
  "cindexP_pathE p g = cindex_pathE (poly p o g) 0"

definition cindexP_lineE :: "complex poly \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> real" where
  "cindexP_lineE p a b = cindexP_pathE p (linepath a b)"

lemma cindexP_pathE_const:"cindexP_pathE [:c:] g = 0"
  unfolding cindexP_pathE_def by (auto intro:cindex_pathE_constI)

lemma cindex_poly_pathE_joinpaths:
  assumes "finite_ReZ_segments (poly p o g1) 0" 
      and "finite_ReZ_segments (poly p o g2) 0" 
      and "path g1" and "path g2" 
      and "pathfinish g1 = pathstart g2"
  shows "cindexP_pathE p (g1 +++ g2) 
            = cindexP_pathE p g1 + cindexP_pathE p g2"
proof -
  have "path (poly p o g1)" "path (poly p o g2)"
    using \<open>path g1\<close> \<open>path g2\<close> by auto
  moreover have "pathfinish (poly p o g1) = pathstart (poly p o g2)"
    using \<open>pathfinish g1 = pathstart g2\<close> 
    by (simp add: pathfinish_compose pathstart_def)
  ultimately have 
    "cindex_pathE ((poly p \<circ> g1) +++ (poly p \<circ> g2)) 0 =
      cindex_pathE (poly p \<circ> g1) 0 + cindex_pathE (poly p \<circ> g2) 0"
    using cindex_pathE_joinpaths[OF assms(1,2)] by auto
  then show ?thesis 
    unfolding cindexP_pathE_def
    by (simp add:path_compose_join)
qed

lemma cindexP_lineE_polyE:
  fixes p::"complex poly" and a b::complex
  defines "pp \<equiv> pcompose p [:a, b-a:]"
  defines "pR \<equiv> map_poly Re pp"
      and "pI \<equiv> map_poly Im pp"
    shows "cindexP_lineE p a b = cindex_polyE 0 1 pI pR"
proof -
  have "cindexP_lineE p a b = cindexE 0 1
           (\<lambda>t. Im (poly (p \<circ>\<^sub>p [:a, b - a:]) (complex_of_real t)) /
                Re (poly (p \<circ>\<^sub>p [:a, b - a:]) (complex_of_real t)))"
    unfolding cindexP_lineE_def cindexP_pathE_def cindex_pathE_def
    by (simp add:poly_linepath_comp')
  also have "... = cindexE 0 1 (\<lambda>t. poly pI t/poly pR t)"
    unfolding pI_def pR_def pp_def
    by (simp add:Im_poly_of_real Re_poly_of_real)
  also have "... = cindex_polyE 0 1 pI pR"
    apply (subst cindexE_eq_cindex_polyE)
    by simp_all
  finally show ?thesis .
qed

definition psign_aux :: "complex poly \<Rightarrow> complex poly \<Rightarrow> complex \<Rightarrow> int" where 
  "psign_aux p q b = 
      sign (Im (poly p b * poly q b) * (Im (poly p b) * Im (poly q b))) 
      + sign (Re (poly p b * poly q b) * Im (poly p b * poly q b))
      - sign (Re (poly p b) * Im (poly p b)) 
      - sign (Re (poly q b) * Im (poly q b))"

definition cdiff_aux :: "complex poly \<Rightarrow> complex poly \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> int" where
  "cdiff_aux p q a b = psign_aux p q b - psign_aux p q a"

lemma cindexP_lineE_times:
  fixes p q::"complex poly" and a b::complex
  assumes "poly p a\<noteq>0" "poly p b\<noteq>0" "poly q a\<noteq>0" "poly q b\<noteq>0"
  shows "cindexP_lineE (p*q) a b = cindexP_lineE p a b + cindexP_lineE q a b+cdiff_aux p q a b/2"
proof -
  define pR pI where "pR = map_poly Re (p \<circ>\<^sub>p [:a, b - a:])"
                 and "pI = map_poly Im (p \<circ>\<^sub>p [:a, b - a:])"
  define qR qI where "qR = map_poly Re (q \<circ>\<^sub>p [:a, b - a:])"
                 and "qI = map_poly Im (q \<circ>\<^sub>p [:a, b - a:])"
  define P1 P2 where "P1 = pR * qI + pI * qR" and "P2=pR * qR - pI * qI"

  have p_poly:
      "poly pR 0 = Re (poly p a)" 
      "poly pI 0 = Im (poly p a)" 
      "poly pR 1 = Re (poly p b)" 
      "poly pI 1 = Im (poly p b)" 
    unfolding pR_def pI_def
    by (simp flip:Re_poly_of_real Im_poly_of_real add:poly_pcompose)+
  have q_poly:
      "poly qR 0 = Re (poly q a)" 
      "poly qI 0 = Im (poly q a)" 
      "poly qR 1 = Re (poly q b)" 
      "poly qI 1 = Im (poly q b)" 
    unfolding qR_def qI_def
    by (simp flip:Re_poly_of_real Im_poly_of_real add:poly_pcompose)+

  have P2_poly:
       "poly P2 0 = Re (poly (p*q) a)"
       "poly P2 1 = Re (poly (p*q) b)"
    unfolding P2_def pR_def qI_def pI_def qR_def
    by (simp flip:Re_poly_of_real Im_poly_of_real add:poly_pcompose)+
  have P1_poly:
       "poly P1 0 = Im (poly (p*q) a)"
       "poly P1 1 = Im (poly (p*q) b)"
    unfolding P1_def pR_def qI_def pI_def qR_def
    by (simp flip:Re_poly_of_real Im_poly_of_real add:poly_pcompose)+

  have p_nzero:"poly pR 0 \<noteq> 0 \<or> poly pI 0 \<noteq> 0" "poly pR 1 \<noteq> 0 \<or> poly pI 1 \<noteq> 0"
    unfolding p_poly
    using assms(1,2) complex_eqI by force+
  have q_nzero:"poly qR 0 \<noteq> 0 \<or> poly qI 0 \<noteq> 0" "poly qR 1 \<noteq> 0 \<or> poly qI 1 \<noteq> 0"
    unfolding q_poly using assms(3,4) complex_eqI by force+

  have P12_nzero:"poly P2 0 \<noteq> 0 \<or> poly P1 0 \<noteq> 0" "poly P2 1 \<noteq> 0 \<or> poly P1 1 \<noteq> 0"
    unfolding P1_poly P2_poly using assms
    by (metis Im_poly_hom.base.hom_zero Re_poly_hom.base.hom_zero 
        complex_eqI poly_mult_zero_iff)+

  define C1 C2 where "C1 = (\<lambda>p q. cindex_polyE 0 1 p q)"
                 and "C2 = (\<lambda>p q. real_of_int (cross_alt p q 0 1) /2)"
  define CR where "CR = C2 P1 (pI * qI) +C2 P2 P1 - C2 pR pI - C2 qR qI"
 
  have "cindexP_lineE (p*q) a b = 
          cindex_polyE 0 1 (map_poly Im (cpoly_of pR pI * cpoly_of qR qI))
              (map_poly Re (cpoly_of pR pI * cpoly_of qR qI))"
  proof -
    have "p \<circ>\<^sub>p [:a, b - a:] = cpoly_of pR pI" 
      using cpoly_of_decompose pI_def pR_def by blast
    moreover have "q \<circ>\<^sub>p [:a, b - a:] = cpoly_of qR qI" 
      using cpoly_of_decompose qI_def qR_def by blast
    ultimately show ?thesis
      apply (subst cindexP_lineE_polyE)
      unfolding pcompose_mult by simp
  qed
  also have "... = cindex_polyE 0 1 (pR * qI + pI * qR ) (pR * qR - pI * qI)"
    unfolding cpoly_of_times by (simp add:algebra_simps)
  also have "... = cindex_polyE 0 1 P1 P2"
    unfolding P1_def P2_def by simp
  also have "... = cindex_polyE 0 1 pI pR + cindex_polyE 0 1 qI qR + CR"
  proof -
    have "C1 P2 P1 = C1 pR pI + C1 qR qI - C2 P1 (pI * qI)"
      unfolding P1_def P2_def C1_def C2_def
      apply (rule cindex_polyE_product)  thm cindex_polyE_product
      by simp fact+
    moreover have "C1 P2 P1 = C2 P2 P1 - C1 P1 P2"
      unfolding C1_def C2_def
      apply (subst cindex_polyE_inverse_add_cross'[symmetric])
      using P12_nzero by simp_all
    moreover have "C1 pR pI = C2 pR pI - C1 pI pR"
      unfolding C1_def C2_def
      apply (subst cindex_polyE_inverse_add_cross'[symmetric])
      using p_nzero by simp_all
    moreover have "C1 qR qI = C2 qR qI - C1 qI qR"
      unfolding C1_def C2_def
      apply (subst cindex_polyE_inverse_add_cross'[symmetric])
      using q_nzero by simp_all
    ultimately have "C2 P2 P1 - C1 P1 P2 = (C2 pR pI - C1 pI pR) 
                        + (C2 qR qI - C1 qI qR) - C2 P1 (pI * qI)"
      by auto
    then have "C1 P1 P2 = C1 pI pR + C1 qI qR + CR"
      unfolding CR_def by (auto simp:algebra_simps)
    then show ?thesis unfolding C1_def .
  qed
  also have "... = cindexP_lineE p a b +cindexP_lineE q a b + CR"
    unfolding C1_def pI_def pR_def qI_def qR_def
    apply (subst (1 2) cindexP_lineE_polyE)
    by simp
  also have "... = cindexP_lineE p a b +cindexP_lineE q a b + cdiff_aux p q a b/2"
  proof -
    have "CR = cdiff_aux p q a b/2"
      unfolding CR_def C2_def cross_alt_alt cdiff_aux_def psign_aux_def
      by (simp add:P1_poly P2_poly p_poly q_poly del:times_complex.sel)
    then show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma cindexP_lineE_changes:
  fixes p::"complex poly" and a b ::complex
  assumes "p\<noteq>0" "a\<noteq>b"
  shows "cindexP_lineE p a b = 
    (let p1 = pcompose p [:a, b-a:];
        pR1 = map_poly Re p1;
        pI1 = map_poly Im p1;
        gc1 = gcd pR1 pI1
    in
      real_of_int (changes_alt_itv_smods 0 1 
                        (pR1 div gc1) (pI1 div gc1)) / 2)"
proof -
  define p1 pR1 pI1 gc1 where "p1 = pcompose p [:a, b-a:]"
    and "pR1 = map_poly Re p1" and "pI1 = map_poly Im p1"
    and "gc1 = gcd pR1 pI1"

  have "gc1 \<noteq>0" 
  proof (rule ccontr)
    assume "\<not> gc1 \<noteq> 0"
    then have "pI1 = 0" "pR1 = 0" unfolding gc1_def by auto
    then have "p1 = 0" unfolding pI1_def pR1_def 
      by (metis cpoly_of_decompose map_poly_0)
    then have "p=0" unfolding p1_def
      apply (subst (asm) pcompose_eq_0)
      using \<open>a\<noteq>b\<close> by auto
    then show False using \<open>p\<noteq>0\<close> by auto
  qed

  have "cindexP_lineE p a b = 
            cindexE 0 1 (\<lambda>t. Im (poly p (linepath a b t)) 
              / Re (poly p (linepath a b t)))"
    unfolding cindexP_lineE_def cindex_pathE_def cindexP_pathE_def by simp
  also have "... = cindexE 0 1 (\<lambda>t. poly pI1 t / poly pR1 t)"
    unfolding pI1_def pR1_def p1_def poly_linepath_comp'
    by (simp add:Im_poly_of_real Re_poly_of_real)
  also have "... = cindex_polyE 0 1 pI1 pR1 "
    by (simp add: cindexE_eq_cindex_polyE)
  also have "... = cindex_polyE 0 1 (pI1 div gc1) (pR1 div gc1)"
    using \<open>gc1\<noteq>0\<close>
    apply (subst (2) cindex_polyE_mult_cancel[of gc1,symmetric])
    by (simp_all add: gc1_def)  
  also have "... = real_of_int (changes_alt_itv_smods 0 1 
                        (pR1 div gc1) (pI1 div gc1)) / 2"
    apply (rule cindex_polyE_changes_alt_itv_mods)
    apply simp
    by (metis \<open>gc1 \<noteq> 0\<close> div_gcd_coprime gc1_def gcd_eq_0_iff)
  finally show ?thesis
    by (metis gc1_def p1_def pI1_def pR1_def)
qed

lemma cindexP_lineE_code[code]:
  "cindexP_lineE p a b = (if p\<noteq>0 \<and> a\<noteq>b then 
      (let p1 = pcompose p [:a, b-a:];
        pR1 = map_poly Re p1;
        pI1 = map_poly Im p1;
        gc1 = gcd pR1 pI1
    in
      real_of_int (changes_alt_itv_smods 0 1 
                        (pR1 div gc1) (pI1 div gc1)) / 2)
    else 
    Code.abort (STR ''cindexP_lineE fails for now'') 
            (\<lambda>_. cindexP_lineE p a b))"
  using cindexP_lineE_changes by auto


  
end
