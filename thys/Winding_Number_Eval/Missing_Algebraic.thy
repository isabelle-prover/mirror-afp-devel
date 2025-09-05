(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section \<open>Some useful lemmas in algebra\<close>

theory Missing_Algebraic imports
  "HOL-Computational_Algebra.Polynomial_Factorial"
  "HOL-Computational_Algebra.Fundamental_Theorem_Algebra"
  "HOL-Complex_Analysis.Complex_Analysis"
  Missing_Topology
  "Budan_Fourier.BF_Misc"
begin

subsection \<open>Misc\<close>

lemma poly_holomorphic_on[simp]: "(poly p) holomorphic_on s"
  by (meson field_differentiable_def has_field_derivative_at_within holomorphic_onI poly_DERIV)

lemma order_zorder:
  fixes p::"complex poly" and z::complex
  assumes "p\<noteq>0"
  shows "order z p = nat (zorder (poly p) z)"
proof -
  define n where "n=nat (zorder (poly p) z)" 
  define h where "h=zor_poly (poly p) z"
  have "\<exists>w. poly p w \<noteq> 0" using assms poly_all_0_iff_0 by auto
  then obtain r where "0 < r" "cball z r \<subseteq> UNIV" and 
      h_holo: "h holomorphic_on cball z r" and
      poly_prod:"(\<forall>w\<in>cball z r. poly p w = h w * (w - z) ^ n \<and> h w \<noteq> 0)"
    using zorder_exist_zero[of "poly p" UNIV z,folded h_def] poly_holomorphic_on
    unfolding n_def by auto
  then have "h holomorphic_on ball z r"
    and "(\<forall>w\<in>ball z r. poly p w = h w * (w - z) ^ n)" 
    and "h z\<noteq>0"
    by auto
  then have "order z p = n" using \<open>p\<noteq>0\<close>
  proof (induct n arbitrary:p h)
    case 0
    then have "poly p z=h z" using \<open>r>0\<close> by auto 
    then have "poly p z\<noteq>0" using \<open>h z\<noteq>0\<close> by auto
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
        unfolding eventually_nhds using Suc(3) \<open>w\<in>ball z r\<close>
        by (metis Elementary_Metric_Spaces.open_ball power_Suc)
      next
        have "(h has_field_derivative deriv h w) (at w)" 
          using \<open>h holomorphic_on ball z r\<close> \<open>w\<in>ball z r\<close> holomorphic_on_imp_differentiable_at 
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
      unfolding h'_def using \<open>h holomorphic_on ball z r\<close>
      by (auto intro!: holomorphic_intros)
    moreover have "h' z\<noteq>0" unfolding h'_def sn_def using \<open>h z \<noteq> 0\<close> of_nat_neq_0 by auto
    moreover have "pderiv p \<noteq> 0"  
    proof 
      assume "pderiv p = 0"
      obtain c where "p=[:c:]" using \<open>pderiv p = 0\<close> using pderiv_iszero by blast
      then have "c=0"
        using Suc(3)[rule_format,of z] \<open>r>0\<close> by auto
      then show False using \<open>p\<noteq>0\<close> using \<open>p=[:c:]\<close> by auto
    qed
    ultimately have "order z (pderiv p) = n" by (auto elim: Suc.hyps)
    moreover have "order z p \<noteq> 0"
      using Suc(3)[rule_format,of z] \<open>r>0\<close> order_root \<open>p\<noteq>0\<close> by auto
    ultimately show ?case using order_pderiv[OF \<open>pderiv p \<noteq> 0\<close>] by auto
  qed
  then show ?thesis unfolding n_def .
qed  
    
lemma poly_field_differentiable_at[simp]:
  "poly p field_differentiable (at x within s)"
  using field_differentiable_at_within field_differentiable_def poly_DERIV by blast
  
lemma deriv_pderiv: "deriv (poly p) = poly (pderiv p)"
  by (meson ext DERIV_imp_deriv poly_DERIV)
        
lemma poly_linepath_comp: 
  fixes a::"'a::{real_normed_vector,comm_semiring_0,real_algebra_1}"
  shows "poly p o (linepath a b) = poly (p \<circ>\<^sub>p [:a, b-a:]) o of_real"
  by (force simp add: poly_pcompose linepath_def scaleR_conv_of_real algebra_simps)
      
subsection \<open>roots / zeros of a univariate function\<close>

definition roots_within::"('a \<Rightarrow> 'b::zero) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "roots_within f s = {x\<in>s. f x = 0}"
  
abbreviation roots::"('a \<Rightarrow> 'b::zero) \<Rightarrow> 'a set" where
  "roots f \<equiv> roots_within f UNIV"

subsection \<open>The argument principle specialised to polynomials.\<close>

lemma argument_principle_poly:
  assumes "p\<noteq>0" and valid:"valid_path g" and loop: "pathfinish g = pathstart g" 
    and no_proots:"path_image g \<subseteq> - proots p"  
  shows "contour_integral g (\<lambda>x. deriv (poly p) x / poly p x) = 2 * of_real pi * \<i> * 
            (\<Sum>x\<in>proots p. winding_number g x * of_nat (order x p))"  
proof -
  have "contour_integral g (\<lambda>x. deriv (poly p) x / poly p x) = 2 * of_real pi * \<i> * 
          (\<Sum>x | poly p x = 0. winding_number g x * of_int (zorder (poly p) x))"
    apply (rule argument_principle[of UNIV "poly p" "{}" "\<lambda>_. 1" g,simplified,OF _ valid loop])
    using no_proots[unfolded proots_def] by (auto simp add:poly_roots_finite[OF \<open>p\<noteq>0\<close>] )
  also have "\<dots> =  2 * of_real pi * \<i> * (\<Sum>x\<in>proots p. winding_number g x * of_nat (order x p))"
  proof -
    have "nat (zorder (poly p) x) = order x p" when "x\<in>proots p" for x 
      using order_zorder[OF \<open>p\<noteq>0\<close>] that unfolding proots_def by auto
    then show ?thesis unfolding proots_def 
      apply (auto intro!: sum.cong)
      by (metis assms(1) nat_eq_iff2 of_nat_nat order_root)
  qed
  finally show ?thesis . 
qed  
  
end
