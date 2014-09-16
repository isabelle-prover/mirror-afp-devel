header {* Polynomials\label{sec.poly.ext} *}

theory Polynomial_extension
imports
  Main
  "~~/src/HOL/Library/Permutations"
  "~~/src/HOL/Library/Polynomial"  
begin

text{* This theory contains auxiliary lemmas on polynomials. *}

lemma degree_setprod_le: "degree (\<Prod>i\<in>S. f i) \<le> (\<Sum>i\<in>S. degree (f i))"
  apply(cases "finite S")
  apply(simp_all)
  apply(induct rule: finite_induct)
  apply(simp_all)
  apply(metis (lifting) degree_mult_le dual_order.trans nat_add_left_cancel_le)
  done

lemma coeff_mult_sum: "degree p \<le> m \<Longrightarrow> 
                       degree q \<le> n \<Longrightarrow> coeff (p * q) (m + n) = coeff p m * coeff q n"
  apply(insert coeff_mult_degree_sum[of p q] coeff_eq_0[of q n] coeff_eq_0[of p m] 
               degree_mult_le[of p q] coeff_eq_0[of "p*q" "m + n"])
  apply(cases "degree p = m \<and> degree q = n")
  apply(simp) 
  apply(cases "degree p < m")
  apply(simp_all)
  done

lemma coeff_mult_setprod_setsum:
  "coeff (\<Prod>i\<in>S. f i) (\<Sum>i\<in>S. degree (f i)) = (\<Prod>i\<in>S. coeff (f i) (degree (f i)))"
  apply(cases "finite S")
  apply(induct rule: finite_induct)
  apply(simp_all add: coeff_mult_sum degree_setprod_le)
  done

lemma degree_setsum_smaller:
  assumes "n > 0" "finite A"
  shows " \<forall>x\<in>A. degree (f x) < n \<Longrightarrow> degree (\<Sum>x\<in>A. f x) < n" 
  using `finite A`
  by(induct rule: finite_induct)
    (simp_all add: degree_add_less assms)

lemma degree_setsum_le:
  assumes "finite A"
  shows " \<forall>x\<in>A. degree (f x) \<le> n \<Longrightarrow> degree (\<Sum>x\<in>A. f x) \<le> n"
  using `finite A`
  by(induct rule: finite_induct)
    (auto intro!: degree_add_le)

lemma degree_setsum_le_max:
  fixes F :: "('n::finite \<Rightarrow> 'n) set" and f :: "_ \<Rightarrow> 'a::comm_ring_1 poly"
  shows "degree (setsum f F) \<le> Max { degree (f p) | p. p\<in>F}"
  by(intro degree_setsum_le)
    (auto intro!: Max.coboundedI)

lemma degree_smaller:
  assumes "n > 0"
  shows "degree (\<Sum>x::nat | x < n . monom (coeff (f x) x) x) < n"
  using assms degree_monom_le
  apply(auto intro!: degree_setsum_smaller)
  apply(subst le_less_trans[where z=n])
  apply(auto)
  done

lemma poly_as_sum_of_monoms: "(\<Sum>x\<le>degree a . monom (coeff a x) x) = a"
proof-
  have eq: "\<And>n. {.. degree a} \<inter> {n} = (if n \<le> degree a then {n} else {})"
    by auto
  show ?thesis  
    by(simp add: poly_eq_iff coeff_setsum setsum.If_cases eq coeff_eq_0)
qed

lemma poly_euclidean_division: 
  assumes "degree a > 0"
  shows "\<exists> b :: 'a. \<exists> a'\<in>{ x::('a::comm_ring_1 poly) . degree x < degree a}.    
         a = monom b (degree a) + a'"
proof-
  have "a = (\<Sum>x\<le>degree a . monom (coeff a x) x)" 
    using poly_as_sum_of_monoms[of a] by auto
  also have "\<dots> = (\<Sum>x\<in>{degree a}\<union>{..< degree a} . monom (coeff a x) x)" 
    unfolding sup.commute using ivl_disj_un_singleton(2) by (metis calculation)
  finally have "a = (\<Sum>x\<in>{degree a} . monom (coeff a x) x) 
                  + (\<Sum>x<degree a . monom (coeff a x) x)"
    by simp
  also have "degree (\<Sum>x<degree a . monom (coeff a x) x) < degree a"
    using assms degree_monom_le le_less_trans
    by(auto intro!: degree_setsum_smaller) (blast)
  ultimately show ?thesis
    by auto
qed 

lemma sign_permut: "\<And>p q. degree (of_int (sign p) * q) = degree q" 
  by(simp add: sign_def)

lemma monom_poly_degree_one: "degree(monom 1 (Suc 0) - [: a::'a::comm_ring_1 :]) = (Suc 0)"
  by(simp add: monom_0 monom_Suc)
 
end
