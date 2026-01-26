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
