(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section \<open>Some useful lemmas in algebra\<close>

theory Missing_Algebraic imports
  "HOL-Computational_Algebra.Polynomial_Factorial"
  "HOL-Computational_Algebra.Fundamental_Theorem_Algebra"
  "HOL-Analysis.Analysis"
  Missing_Topology
begin

subsection \<open>Misc\<close>

(*adapted from the poly_root_induct in Polynomial.thy.*)
lemma poly_root_induct_alt [case_names 0 no_proots root]:
  fixes p :: "'a :: idom poly"
  assumes "Q 0"
  assumes "\<And>p. (\<And>a. poly p a \<noteq> 0) \<Longrightarrow> Q p"
  assumes "\<And>a p. Q p \<Longrightarrow> Q ([:-a, 1:] * p)"
  shows   "Q p"
proof (induction "degree p" arbitrary: p rule: less_induct)
  case (less p)
  have ?case when "p=0" using \<open>Q 0\<close> that by auto
  moreover have ?case when "\<nexists>a. poly p a = 0"
    using assms(2) that by blast
  moreover have ?case when "\<exists>a. poly p a = 0" "p\<noteq>0"
  proof -
    obtain a where "poly p a =0" using \<open>\<exists>a. poly p a = 0\<close> by auto
    then obtain q where pq:"p= [:-a,1:] * q" by (meson dvdE poly_eq_0_iff_dvd)
    then have "q\<noteq>0" using \<open>p\<noteq>0\<close> by auto
    then have "degree q<degree p" unfolding pq by (subst degree_mult_eq,auto)
    then have "Q q" using less by auto
    then show ?case using assms(3) unfolding pq by auto
  qed
  ultimately show ?case by auto
qed

(*refined version of the library one with the same name, by relaxing type restrictions.*)  
lemma poly_isCont[simp]: 
  fixes x::"'a::real_normed_field"
  shows "isCont (\<lambda>x. poly p x) x"
by (rule poly_DERIV [THEN DERIV_isCont])

lemma order_uminus[simp]: "order x (-p) = order x p"
  by (metis neg_equal_0_iff_equal order_smult smult_1_left smult_minus_left) 

lemma tendsto_poly [tendsto_intros]: "(f \<longlongrightarrow> a) F \<Longrightarrow> ((\<lambda>x. poly p (f x)) \<longlongrightarrow> poly p a) F"
  for f :: "_ \<Rightarrow> 'a::real_normed_field"  
  by (rule isCont_tendsto_compose [OF poly_isCont])

lemma continuous_within_poly: "continuous (at z within s) (poly p)"
  for z :: "'a::{real_normed_field}"
  by (simp add: continuous_within tendsto_poly)  
    
lemma continuous_poly [continuous_intros]: "continuous F f \<Longrightarrow> continuous F (\<lambda>x. poly p (f x))"
  for f :: "_ \<Rightarrow> 'a::real_normed_field"
  unfolding continuous_def by (rule tendsto_poly)
    
lemma continuous_on_poly [continuous_intros]: "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. poly p (f x))"
  for f :: "_ \<Rightarrow> 'a::real_normed_field"
  unfolding continuous_on_def by (auto intro: tendsto_poly)
      
lemma poly_holomorphic_on[simp]:
  "(poly p) holomorphic_on s"
apply (rule holomorphic_onI)
apply (unfold field_differentiable_def)
apply (rule_tac x="poly (pderiv p) x" in exI)
by (simp add:has_field_derivative_at_within)
    
lemma order_zorder:
  fixes p::"complex poly" and z::complex
  assumes "poly p z=0" and "p\<noteq>0"
  shows "order z p = zorder (poly p) z"
proof -
  define n where "n=zorder (poly p) z" 
  define h where "h=zer_poly (poly p) z"
  have "\<exists>w. poly p w \<noteq> 0" using assms(2) poly_all_0_iff_0 by auto
  then obtain r where "0 < n" "0 < r" "cball z r \<subseteq> UNIV" and 
      h_holo: "h holomorphic_on cball z r" and
      poly_prod:"(\<forall>w\<in>cball z r. poly p w = h w * (w - z) ^ n \<and> h w \<noteq> 0)"
    using zorder_exist[of UNIV z "poly p",folded n_def h_def] `poly p z=0` poly_holomorphic_on
    by auto
  then have "h holomorphic_on ball z r"
    and "(\<forall>w\<in>ball z r. poly p w = h w * (w - z) ^ n)" 
    and "h z\<noteq>0"
    by auto
  then have "order z p = n" using `p\<noteq>0`
    proof (induct n arbitrary:p h)
      case 0
      then have "poly p z=h z" using `r>0` by auto 
      then have "poly p z\<noteq>0" using `h z\<noteq>0` by auto
      then show ?case using order_root by blast
    next
      case (Suc n)
      define sn where "sn=Suc n"
      define h' where "h'\<equiv> \<lambda>w. deriv h w * (w-z)+ sn * h w"
      have "(poly p has_field_derivative poly (pderiv p) w) (at w)" for w
        using poly_DERIV[of p w] .
      moreover have "(poly p has_field_derivative (h' w)*(w-z)^n ) (at w)" when "w\<in>ball z r" for w
        proof (subst DERIV_cong_ev[of w w "poly p" "\<lambda>w.  h w * (w - z) ^ Suc n" ],simp_all)
          show "\<forall>\<^sub>F x in nhds w. poly p x = h x * ((x - z) * (x - z) ^ n)"
            unfolding eventually_nhds using Suc(3) `w\<in>ball z r`
            apply (intro exI[where x="ball z r"])
            by auto
        next
          have "(h has_field_derivative deriv h w) (at w)" 
            using `h holomorphic_on ball z r` `w\<in>ball z r`  
              holomorphic_on_imp_differentiable_at 
            by (simp add: holomorphic_derivI)
          then have "((\<lambda>w. h w * ((w - z) ^ sn)) 
              has_field_derivative h' w * (w - z) ^ (sn - 1)) (at w)"
            unfolding h'_def
            apply (auto intro!: derivative_eq_intros simp add:field_simps)
            by (auto simp add:field_simps sn_def)
          then show "((\<lambda>w. h w * ((w - z) * (w - z) ^ n)) 
              has_field_derivative h' w * (w - z) ^ n) (at w)"
            unfolding sn_def by auto
        qed
      ultimately have "\<forall>w\<in>ball z r. poly (pderiv p) w = h' w * (w - z) ^ n"
        using DERIV_unique by blast  
      moreover have "h' holomorphic_on ball z r"
        unfolding h'_def using `h holomorphic_on ball z r`
        by (auto intro!: holomorphic_intros)
      moreover have "h' z\<noteq>0" unfolding h'_def sn_def using `h z \<noteq> 0` of_nat_neq_0 by auto
      moreover have "pderiv p \<noteq> 0"  
        proof 
          assume "pderiv p = 0"
          obtain c where "p=[:c:]" using `pderiv p = 0` using pderiv_iszero by blast
          then have "c=0"
            using Suc(3)[rule_format,of z] `r>0` by auto
          then show False using `p\<noteq>0` using `p=[:c:]` by auto
        qed
      ultimately have "order z (pderiv p) = n" 
        by (auto elim: Suc.hyps)
      moreover have "order z p \<noteq> 0"
        using Suc(3)[rule_format,of z] `r>0` order_root `p\<noteq>0` by auto
      ultimately show ?case using order_pderiv[OF `pderiv p \<noteq> 0`] by auto
    qed
  then show ?thesis unfolding n_def .
qed  
 
lemma pcompose_pCons_0:"pcompose p [:a:] = [:poly p a:]"
  apply (induct p)
  by (auto simp add:pcompose_pCons algebra_simps)      
  
lemma Im_poly_of_real:
  "Im (poly p (of_real x)) = poly (map_poly Im p) x"
  apply (induct p)
  by (auto simp add:map_poly_pCons)
 
lemma Re_poly_of_real:
  "Re (poly p (of_real x)) = poly (map_poly Re p) x"
  apply (induct p)
  by (auto simp add:map_poly_pCons)    
   
lemma pcompose_coeff_0:
  "coeff (pcompose p q) 0 = poly p (coeff q 0)"
  apply (induct p)
  by (auto simp add:pcompose_pCons coeff_mult)  
    
lemma poly_field_differentiable_at[simp]:
  "poly p field_differentiable (at x within s)"
apply (unfold field_differentiable_def)
apply (rule_tac x="poly (pderiv p) x" in exI)
by (simp add:has_field_derivative_at_within)  
  
lemma deriv_pderiv:
  "deriv (poly p) = poly (pderiv p)"
apply (rule ext)  
apply (rule DERIV_imp_deriv)  
  using poly_DERIV . 
    
lemma lead_coeff_map_poly_nz:
  assumes "f (lead_coeff p) \<noteq>0" "f 0=0"
  shows "lead_coeff (map_poly f p) = f (lead_coeff p) "
proof -
  have "lead_coeff (Poly (map f (coeffs p))) = f (lead_coeff p)"
    by (metis (mono_tags, lifting) antisym assms(1) assms(2) coeff_0_degree_minus_1 coeff_map_poly 
        degree_Poly degree_eq_length_coeffs le_degree length_map map_poly_def)
  then show ?thesis
    by (simp add: map_poly_def)
qed 

lemma filterlim_poly_at_infinity:
  fixes p::"'a::real_normed_field poly"
  assumes "degree p>0"
  shows "filterlim (poly p) at_infinity at_infinity"
using assms
proof (induct p)
  case 0
  then show ?case by auto
next
  case (pCons a p)
  have ?case when "degree p=0"
  proof -
    obtain c where c_def:"p=[:c:]" using \<open>degree p = 0\<close> degree_eq_zeroE by blast
    then have "c\<noteq>0" using \<open>0 < degree (pCons a p)\<close> by auto
    then show ?thesis unfolding c_def 
      apply (auto intro!:tendsto_add_filterlim_at_infinity)
      apply (subst mult.commute)
      by (auto intro!:tendsto_mult_filterlim_at_infinity filterlim_ident)
  qed
  moreover have ?case when "degree p\<noteq>0"
  proof -
    have "filterlim (poly p) at_infinity at_infinity"
      using that by (auto intro:pCons)
    then show ?thesis 
      by (auto intro!:tendsto_add_filterlim_at_infinity filterlim_at_infinity_times filterlim_ident)
  qed
  ultimately show ?case by auto
qed  
       
lemma poly_divide_tendsto_aux:
  fixes p::"'a::real_normed_field poly"
  shows "((\<lambda>x. poly p x/x^(degree p)) \<longlongrightarrow> lead_coeff p) at_infinity"  
proof (induct p)
  case 0
  then show ?case by (auto intro:tendsto_eq_intros)
next
  case (pCons a p)
  have ?case when "p=0"
    using that by auto
  moreover have ?case when "p\<noteq>0"
  proof -
    define g where "g=(\<lambda>x. a/(x*x^degree p))"
    define f where "f=(\<lambda>x. poly p x/x^degree p)"
    have "\<forall>\<^sub>Fx in at_infinity. poly (pCons a p) x / x ^ degree (pCons a p) = g x + f x"
    proof (rule eventually_at_infinityI[of 1])
      fix x::'a assume "norm x\<ge>1"
      then have "x\<noteq>0" by auto
      then show "poly (pCons a p) x / x ^ degree (pCons a p) = g x + f x"
        using that unfolding g_def f_def by (auto simp add:field_simps)
    qed
    moreover have "((\<lambda>x. g x+f x) \<longlongrightarrow>  lead_coeff (pCons a p)) at_infinity"
    proof -
      have "(g \<longlongrightarrow>  0) at_infinity"
        unfolding g_def using filterlim_poly_at_infinity[of "monom 1 (Suc (degree p))"]
        apply (auto intro!:tendsto_intros tendsto_divide_0 simp add: degree_monom_eq)
        apply (subst filterlim_cong[where g="poly (monom 1 (Suc (degree p)))"])
        by (auto simp add:poly_monom)
      moreover have "(f \<longlongrightarrow>  lead_coeff (pCons a p)) at_infinity"
        using pCons \<open>p\<noteq>0\<close> unfolding f_def by auto
      ultimately show ?thesis by (auto intro:tendsto_eq_intros)
    qed
    ultimately show ?thesis by (auto dest:tendsto_cong)  
  qed
  ultimately show ?case by auto  
qed
  
lemma filterlim_power_at_infinity:
  assumes "n\<noteq>0"
  shows "filterlim (\<lambda>x::'a::real_normed_field. x^n) at_infinity at_infinity" 
  using filterlim_poly_at_infinity[of "monom 1 n"] assms
  apply (subst filterlim_cong[where g="poly (monom 1 n)"])
  by (auto simp add:poly_monom degree_monom_eq)
   
lemma poly_divide_tendsto_0_at_infinity: 
  fixes p::"'a::real_normed_field poly"
  assumes "degree p > degree q" 
  shows "((\<lambda>x. poly q x / poly p x) \<longlongrightarrow> 0 ) at_infinity" 
proof -
  define pp where "pp=(\<lambda>x. x^(degree p) / poly p x)"    
  define qq where "qq=(\<lambda>x. poly q x/x^(degree q))"
  define dd where "dd=(\<lambda>x::'a. 1/x^(degree p - degree q))"
  have "\<forall>\<^sub>Fx in at_infinity.  poly q x / poly p x = qq x * pp x * dd x"
  proof (rule eventually_at_infinityI[of 1])
    fix x::'a assume "norm x\<ge>1"
    then have "x\<noteq>0" by auto
    then show "poly q x / poly p x = qq x * pp x * dd x"
      unfolding qq_def pp_def dd_def using assms 
      by (auto simp add:field_simps divide_simps power_diff) 
  qed
  moreover have "((\<lambda>x. qq x * pp x * dd x) \<longlongrightarrow> 0) at_infinity"
  proof -
    have "(qq \<longlongrightarrow> lead_coeff q) at_infinity" 
      unfolding qq_def using poly_divide_tendsto_aux[of q] .
    moreover have "(pp \<longlongrightarrow> 1/lead_coeff p) at_infinity"
    proof -
      have "p\<noteq>0" using assms by auto
      then show ?thesis
        unfolding pp_def using poly_divide_tendsto_aux[of p] 
        apply (drule_tac tendsto_inverse)
        by (auto simp add:inverse_eq_divide)
    qed  
    moreover have "(dd \<longlongrightarrow> 0) at_infinity" 
      unfolding dd_def
      apply (rule tendsto_divide_0)
      by (auto intro!: filterlim_power_at_infinity simp add:assms)
    ultimately show ?thesis by (auto intro:tendsto_eq_intros)
  qed
  ultimately show ?thesis by (auto dest:tendsto_cong)
qed
    
lemma lead_coeff_list_def:
  "lead_coeff p= (if coeffs p=[] then 0 else last (coeffs p))"
by (simp add: last_coeffs_eq_coeff_degree)
  
lemma poly_linepath_comp: 
  fixes a::"'a::{real_normed_vector,comm_semiring_0,real_algebra_1}"
  shows "poly p o (linepath a b) = poly (p \<circ>\<^sub>p [:a, b-a:]) o of_real"
  apply rule
  by (auto simp add:poly_pcompose linepath_def scaleR_conv_of_real algebra_simps)
    
subsection \<open>More about @{term degree}\<close>
   
lemma degree_div_less:
  fixes x y::"'a::field poly"
  assumes "degree x\<noteq>0" "degree y\<noteq>0"
  shows "degree (x div y) < degree x"
proof -
  have "x\<noteq>0" "y\<noteq>0" using assms by auto
  define q r where "q=x div y" and "r=x mod y"
  have *:"eucl_rel_poly x y (q, r)" unfolding q_def r_def 
    by (simp add: eucl_rel_poly)
  then have "r = 0 \<or> degree r < degree y" using \<open>y\<noteq>0\<close> unfolding eucl_rel_poly_iff by auto
  moreover have ?thesis when "r=0"
  proof -
    have "x = q * y" using * that unfolding eucl_rel_poly_iff by auto
    then have "q\<noteq>0" using \<open>x\<noteq>0\<close> \<open>y\<noteq>0\<close> by auto
    from degree_mult_eq[OF this \<open>y\<noteq>0\<close>] \<open>x = q * y\<close> 
    have "degree x = degree q +degree y" by auto
    then show ?thesis unfolding q_def using assms by auto
  qed
  moreover have ?thesis when "degree r<degree y"
  proof (cases "degree y>degree x")
    case True
    then have "q=0" unfolding q_def using div_poly_less by auto
    then show ?thesis unfolding q_def using assms(1) by auto
  next
    case False
    then have "degree x>degree r" using that by auto
    then have "degree x = degree (x-r)" using degree_add_eq_right[of "-r" x] by auto
    have "x-r = q*y" using * unfolding eucl_rel_poly_iff by auto
    then have "q\<noteq>0" using \<open>degree r < degree x\<close> by auto
    have "degree x = degree q +degree y" 
      using  degree_mult_eq[OF \<open>q\<noteq>0\<close> \<open>y\<noteq>0\<close>] \<open>x-r = q*y\<close> \<open>degree x = degree (x-r)\<close> by auto
    then show ?thesis unfolding q_def using assms by auto
  qed
  ultimately show ?thesis by auto
qed  
  
lemma map_poly_degree_eq:
  assumes "f (lead_coeff p) \<noteq>0"
  shows "degree (map_poly f p) = degree p"  
  using assms
  unfolding map_poly_def degree_eq_length_coeffs coeffs_Poly lead_coeff_list_def
  by (metis (full_types) last_conv_nth_default length_map no_trailing_unfold nth_default_coeffs_eq 
      nth_default_map_eq strip_while_idem)
  
lemma map_poly_degree_less:
  assumes "f (lead_coeff p) =0" "degree p\<noteq>0"
  shows "degree (map_poly f p) < degree p" 
proof -
  have "length (coeffs p) >1" 
    using \<open>degree p\<noteq>0\<close> by (simp add: degree_eq_length_coeffs)  
  then obtain xs x where xs_def:"coeffs p=xs@[x]" "length xs>0"  
    by (metis One_nat_def add.commute add_diff_cancel_left' append_Nil assms(2) 
        degree_eq_length_coeffs length_greater_0_conv list.size(3) list.size(4) not_less_zero
        rev_exhaust) 
  have "f x=0" using assms(1) by (simp add: lead_coeff_list_def xs_def(1))
  have "degree (map_poly f p) = length (strip_while ((=) 0) (map f (xs@[x]))) - 1" 
    unfolding map_poly_def degree_eq_length_coeffs coeffs_Poly
    by (subst xs_def,auto)
  also have "... = length (strip_while ((=) 0) (map f xs)) - 1"   
    using \<open>f x=0\<close> by simp
  also have "... \<le> length xs -1"
    using length_strip_while_le by (metis diff_le_mono length_map)
  also have "... < length (xs@[x]) - 1"
    using xs_def(2) by auto
  also have "... = degree p"
    unfolding degree_eq_length_coeffs xs_def by simp
  finally show ?thesis .
qed
  
lemma map_poly_degree_leq[simp]:
  shows "degree (map_poly f p) \<le> degree p"
  unfolding map_poly_def degree_eq_length_coeffs
  by (metis coeffs_Poly diff_le_mono length_map length_strip_while_le)  
    
subsection {*roots / zeros of a univariate function*}

definition roots_within::"('a \<Rightarrow> 'b::zero) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "roots_within f s = {x\<in>s. f x = 0}"
  
abbreviation roots::"('a \<Rightarrow> 'b::zero) \<Rightarrow> 'a set" where
  "roots f \<equiv> roots_within f UNIV"
  
subsection {*polynomial roots / zeros*}

definition proots_within::"'a::comm_semiring_0 poly \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "proots_within p s = {x\<in>s. poly p x=0}"

abbreviation proots::"'a::comm_semiring_0 poly \<Rightarrow> 'a set" where
  "proots p \<equiv> proots_within p UNIV"

lemma proots_def: "proots p = {x. poly p x=0}" 
  unfolding proots_within_def by auto 

lemma proots_within_empty[simp]:
  "proots_within p {} = {}" unfolding proots_within_def by auto

lemma proots_within_0[simp]:
  "proots_within 0 s = s" unfolding proots_within_def by auto

lemma proots_withinI[intro,simp]:
  "poly p x=0 \<Longrightarrow> x\<in>s \<Longrightarrow> x\<in>proots_within p s"
  unfolding proots_within_def by auto

lemma proots_within_iff[simp]:
  "x\<in>proots_within p s \<longleftrightarrow> poly p x=0 \<and> x\<in>s"
  unfolding proots_within_def by auto

lemma proots_within_times:
  fixes s::"'a::{semiring_no_zero_divisors,comm_semiring_0} set"
  shows "proots_within (p*q) s = proots_within p s \<union> proots_within q s"
unfolding proots_within_def by auto

lemma proots_within_gcd:
  fixes s::"'a::factorial_ring_gcd set"
  shows "proots_within (gcd p q) s= proots_within p s \<inter> proots_within q s"
unfolding proots_within_def 
by (auto simp add: poly_eq_0_iff_dvd) 

lemma proots_within_inter:
    "NO_MATCH UNIV s \<Longrightarrow> proots_within p s = proots p \<inter> s" 
  unfolding proots_within_def by auto

lemma proots_within_proots[simp]:
  "proots_within p s \<subseteq> proots p"
unfolding proots_within_def by auto

lemma finite_proots[simp]: 
  fixes p :: "'a::idom poly"
  shows "p\<noteq>0 \<Longrightarrow> finite (proots_within p s)"
  unfolding proots_within_def using poly_roots_finite by fast

lemma proots_within_pCons_1_iff:
  fixes a::"'a::idom"
  shows "proots_within [:-a,1:] s = (if a\<in>s then {a} else {})"
  by (cases "a\<in>s",auto)
    
lemma proots_within_uminus[simp]:
  fixes p :: "'a::comm_ring poly"
  shows "proots_within (- p) s = proots_within p s"
by auto

lemma proots_within_smult:
  fixes a::"'a::{semiring_no_zero_divisors,comm_semiring_0}"
  assumes "a\<noteq>0"
  shows "proots_within (smult a p) s = proots_within p s"
  unfolding proots_within_def using assms by auto

lemma argument_principle_poly:
  assumes "p\<noteq>0" and valid:"valid_path g" and loop: "pathfinish g = pathstart g" 
    and no_proots:"path_image g \<subseteq> - proots p"  
  shows "contour_integral g (\<lambda>x. deriv (poly p) x / poly p x) = 2 * of_real pi * \<i> * 
            (\<Sum>x\<in>proots p. winding_number g x * of_nat (order x p))"  
proof -
  have "contour_integral g (\<lambda>x. deriv (poly p) x / poly p x) = 2 * of_real pi * \<i> * 
          (\<Sum>x | poly p x = 0. winding_number g x * of_nat (zorder (poly p) x))"
    apply (rule argument_principle[of UNIV "poly p" "{}" "\<lambda>_. 1" g,simplified,OF _ valid loop])
    using no_proots[unfolded proots_def] by (auto simp add:poly_roots_finite[OF \<open>p\<noteq>0\<close>] )
  also have "... =  2 * of_real pi * \<i> * (\<Sum>x\<in>proots p. winding_number g x * of_nat (order x p))"
  proof -
    have "zorder (poly p) x = order x p" when "x\<in>proots p" for x 
      using order_zorder[OF _ \<open>p\<noteq>0\<close>] that unfolding proots_def by auto
    then show ?thesis unfolding proots_def by (auto intro!:comm_monoid_add_class.sum.cong)
  qed
  finally show ?thesis . 
qed  
  
subsection \<open>The number of polynomial roots counted with multiplicities.\<close>
  
(*counting the number of proots WITH MULTIPLICITIES within a set*)
definition proots_count::"'a::idom poly \<Rightarrow> 'a set \<Rightarrow> nat" where
  "proots_count p s = (\<Sum>r\<in>proots_within p s. order r p)"  

lemma proots_count_emtpy[simp]:"proots_count p {} = 0"
  unfolding proots_count_def by auto
  
lemma proots_count_times:
  fixes s :: "'a::idom set"
  assumes "p*q\<noteq>0"
  shows "proots_count (p*q) s = proots_count p s + proots_count q s"
proof -
  define pts where "pts=proots_within p s" 
  define qts where "qts=proots_within q s"
  have [simp]: "finite pts" "finite qts" 
    using `p*q\<noteq>0` unfolding pts_def qts_def by auto
  have "(\<Sum>r\<in>pts \<union> qts. order r p) =  (\<Sum>r\<in>pts. order r p)" 
    proof (rule comm_monoid_add_class.sum.mono_neutral_cong_right,simp_all)
      show "\<forall>i\<in>pts \<union> qts - pts. order i p = 0" 
        unfolding pts_def qts_def proots_within_def using order_root by fastforce
    qed
  moreover have "(\<Sum>r\<in>pts \<union> qts. order r q) = (\<Sum>r\<in>qts. order r q)" 
    proof (rule comm_monoid_add_class.sum.mono_neutral_cong_right,simp_all)
      show "\<forall>i\<in>pts \<union> qts - qts. order i q = 0" 
        unfolding pts_def qts_def proots_within_def using order_root by fastforce
    qed
  ultimately show ?thesis unfolding proots_count_def
    apply (simp add:proots_within_times order_mult[OF `p*q\<noteq>0`] sum.distrib)
    apply (fold pts_def qts_def)
    by auto
qed

lemma proots_count_power_n_n:
  shows "proots_count ([:- a, 1:]^n) s = (if a\<in>s \<and> n>0 then n else 0)"
proof -
  have "proots_within ([:- a, 1:] ^ n) s= (if a\<in>s \<and> n>0 then {a} else {})"
    unfolding proots_within_def by auto
  thus ?thesis unfolding proots_count_def using order_power_n_n by auto
qed

lemma degree_proots_count:
  fixes p::"complex poly"
  shows "degree p = proots_count p UNIV"
proof (induct "degree p" arbitrary:p )
  case 0
  then obtain c where c_def:"p=[:c:]" using degree_eq_zeroE by auto
  then show ?case unfolding proots_count_def 
    apply (cases "c=0")
    by (auto intro!:sum.infinite simp add:infinite_UNIV_char_0 order_0I)
next
  case (Suc n)
  then have "degree p\<noteq>0" and "p\<noteq>0" by auto
  obtain z where "poly p z = 0" 
    using Fundamental_Theorem_Algebra.fundamental_theorem_of_algebra `degree p\<noteq>0` constant_degree[of p]
    by auto
  define onez where "onez=[:-z,1:]" 
  have [simp]: "onez\<noteq>0" "degree onez = 1" unfolding onez_def by auto
  obtain q where q_def:"p= onez * q" 
    using poly_eq_0_iff_dvd `poly p z = 0` dvdE unfolding onez_def by blast
  hence "q\<noteq>0" using `p\<noteq>0` by auto
  hence "n=degree q" using degree_mult_eq[of onez q] `Suc n = degree p` 
    apply (fold q_def)
    by auto
  hence "degree q = proots_count q UNIV" using Suc.hyps(1) by simp
  moreover have " Suc 0 = proots_count onez UNIV" 
    unfolding onez_def using proots_count_power_n_n[of z 1 UNIV]
    by auto
  ultimately show ?case 
    unfolding q_def using degree_mult_eq[of onez q] proots_count_times[of onez q UNIV] `q\<noteq>0`
    by auto
qed
  
lemma proots_count_smult:
  fixes a::"'a::{semiring_no_zero_divisors,idom}"
  assumes "a\<noteq>0"
  shows "proots_count (smult a p) s= proots_count p s"
proof (cases "p=0")
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis 
    unfolding proots_count_def
    using order_smult[OF assms] proots_within_smult[OF assms] by auto
qed

 
lemma proots_count_pCons_1_iff:
  fixes a::"'a::idom"
  shows "proots_count [:-a,1:] s = (if a\<in>s then 1 else 0)"
  unfolding proots_count_def 
  by (cases "a\<in>s",auto simp add:proots_within_pCons_1_iff order_power_n_n[of _ 1,simplified])
      
lemma proots_count_uminus[simp]:
  "proots_count (- p) s = proots_count p s"
  unfolding proots_count_def by simp
    
lemma card_proots_within_leq:
  assumes "p\<noteq>0"
  shows "proots_count p s \<ge> card (proots_within p s)" using assms
proof (induct rule:poly_root_induct[of _ "\<lambda>x. x\<in>s"])
  case 0
  then show ?case unfolding proots_within_def proots_count_def by auto
next
  case (no_roots p)
  then have "proots_within p s = {}" by auto
  then show ?case unfolding proots_count_def by auto
next
  case (root a p)
  have "card (proots_within ([:- a, 1:] * p) s) 
      \<le> card (proots_within [:- a, 1:] s)+card (proots_within p s)" 
    unfolding proots_within_times by (auto simp add:card_Un_le)
  also have "... \<le> 1+ proots_count p s"
  proof -
    have "card (proots_within [:- a, 1:] s) \<le> 1"
    proof (cases "a\<in>s")
      case True
      then have "proots_within [:- a, 1:] s = {a}" by auto
      then show ?thesis by auto
    next
      case False
      then have "proots_within [:- a, 1:] s = {}" by auto
      then show ?thesis by auto
    qed
    moreover have "card (proots_within p s) \<le> proots_count p s"
      apply (rule root.hyps)
      using root by auto
    ultimately show ?thesis by auto
  qed
  also have "... =  proots_count ([:- a,1:] * p) s"
    apply (subst proots_count_times)
    subgoal by (metis mult_eq_0_iff pCons_eq_0_iff root.prems zero_neq_one)  
    using root by (auto simp add:proots_count_pCons_1_iff)
  finally have "card (proots_within ([:- a, 1:] * p) s) \<le> proots_count ([:- a, 1:] * p) s" .
  then show ?case 
    by (metis (no_types, hide_lams) add.inverse_inverse add.inverse_neutral minus_pCons 
        mult_minus_left proots_count_uminus proots_within_uminus)
qed
 
lemma proots_count_leq_degree:
  assumes "p\<noteq>0"
  shows "proots_count p s\<le> degree p" using assms
proof (induct rule:poly_root_induct[of _ "\<lambda>x. x\<in>s"])
  case 0
  then show ?case by auto
next
  case (no_roots p)
  then have "proots_within p s = {}" by auto
  then show ?case unfolding proots_count_def by auto
next
  case (root a p)
  have "proots_count ([:a, - 1:] * p) s = proots_count [:a, - 1:] s + proots_count p s"
    apply (subst proots_count_times)
    using root by auto
  also have "... = 1 + proots_count p s"
  proof -
    have "proots_count [:a, - 1:] s  =1"
      by (metis (no_types, lifting) add.inverse_inverse add.inverse_neutral minus_pCons 
          proots_count_pCons_1_iff proots_count_uminus root.hyps(1))
    then show ?thesis by auto
  qed
  also have "... \<le>  degree ([:a,-1:] * p)" 
    apply (subst degree_mult_eq)
    subgoal by auto
    subgoal using root by auto
    subgoal using root by (simp add: \<open>p \<noteq> 0\<close>)
    done
  finally show ?case .
qed
 
  
end
