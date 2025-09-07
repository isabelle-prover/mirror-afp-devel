(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section \<open>Misc polynomial lemmas for the Sturm--Tarski theorem\<close>

theory PolyMisc imports
  "HOL-Computational_Algebra.Polynomial_Factorial"
begin

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
    unfolding poly_power using zero_le_odd_power[OF \<open>odd n\<close>] by blast
  also have "(poly [:- a, 1:] x \<ge>0) = (x\<ge>a)" by fastforce
  finally have "poly ([:-a,1:]^n) x\<ge>0 = (x\<ge>a)" .
  moreover have "poly ([:-a,1:]^n) x=0 = (x=a)" by(rule poly_power_n_eq, metis assms even_zero)    
  ultimately show ?thesis by linarith
qed

lemma pseudo_divmod_0[simp]: "pseudo_divmod f 0 = (0,f)"
  unfolding pseudo_divmod_def by auto

lemma map_poly_eq_iff:
  assumes "f 0=0" "inj f"
  shows "map_poly f x =map_poly f y \<longleftrightarrow> x=y" 
  using assms
  by (auto simp: poly_eq_iff coeff_map_poly dest:injD)
      
lemma pseudo_mod_0[simp]:
  shows "pseudo_mod p 0= p" "pseudo_mod 0 q = 0"
  unfolding pseudo_mod_def pseudo_divmod_def by (auto simp add: length_coeffs_degree)

lemma pseudo_mod_mod:
  assumes "g\<noteq>0"
  shows "smult (lead_coeff g ^ (Suc (degree f) - degree g)) (f mod g) = pseudo_mod f g"
proof -
  define a where "a=lead_coeff g ^ (Suc (degree f) - degree g)"
  have "a\<noteq>0" unfolding a_def by (simp add: assms)  
  define r where "r = pseudo_mod f g" 
  define r' where "r' = pseudo_mod (smult (1/a) f) g"
  obtain q where pdm: "pseudo_divmod f g = (q,r)" using r_def[unfolded pseudo_mod_def]
    apply (cases "pseudo_divmod f g")
    by auto
  obtain q' where pdm': "pseudo_divmod (smult (1/a) f) g = (q',r')" using r'_def[unfolded pseudo_mod_def] 
    apply (cases "pseudo_divmod (smult (1/a) f) g")
    by auto
  have "smult a f = q * g + r" and deg_r:"r = 0 \<or> degree r < degree g"
    using pseudo_divmod[OF assms pdm] unfolding a_def by auto
  moreover have "f = q' * g + r'" and deg_r':"r' = 0 \<or> degree r' < degree g"
    using \<open>a\<noteq>0\<close>  pseudo_divmod[OF assms pdm'] unfolding a_def degree_smult_eq 
    by auto  
  ultimately have gr:"(smult a q' - q) * g =  r - smult a r'" 
    by (auto simp add:smult_add_right algebra_simps)
  have "smult a r' = r" when "r=0" "r'=0"
    using that by auto
  moreover have "smult a r' = r" when "r\<noteq>0 \<or> r'\<noteq>0"
  proof -
    have "smult a q' - q =0"
    proof (rule ccontr)
      assume asm:"smult a q' - q \<noteq> 0 "
      have "degree (r - smult a r') < degree g"
        using deg_r deg_r' degree_diff_less that by force
      also have "... \<le> degree (( smult a q' - q)*g)"
        using degree_mult_right_le[OF asm,of g] by (simp add: mult.commute) 
      also have "... = degree (r - smult a r')"
        using gr by auto
      finally have "degree (r - smult a r') < degree (r - smult a r')" .
      then show False by simp
    qed
    then show ?thesis using gr by auto
  qed
  ultimately have "smult a r' = r" by argo
  then show ?thesis unfolding r_def r'_def a_def mod_poly_def 
    using assms by (auto simp add:field_simps)
qed    
    
lemma poly_pseudo_mod:
  assumes "poly q x=0" "q\<noteq>0"
  shows "poly (pseudo_mod p q) x = (lead_coeff q ^ (Suc (degree p) - degree q)) * poly p x"
proof -
  define a where "a=coeff q (degree q) ^ (Suc (degree p) - degree q)"
  obtain f r where fr:"pseudo_divmod p q = (f, r)" by fastforce
  then have "smult a p = q * f + r" "r = 0 \<or> degree r < degree q"
    using pseudo_divmod[OF \<open>q\<noteq>0\<close>] unfolding a_def by auto
  then have "poly (q*f+r) x = poly (smult a p) x" by auto    
  then show ?thesis
    using assms(1) fr unfolding pseudo_mod_def a_def
    by auto
qed  

lemma degree_less_timesD:
  fixes q::"'a::idom poly"
  assumes "q*g=r" and deg:"r=0 \<or> degree g>degree r" and "g\<noteq>0"
  shows "q=0 \<and> r=0"
proof -
  have ?thesis when "r=0"
    using assms(1) assms(3) no_zero_divisors that by blast    
  moreover have False when "r\<noteq>0"
  proof -
    have "degree r < degree g"
      using deg that by auto
    also have "... \<le> degree r"
      by (metis assms(1) degree_mult_right_le mult.commute mult_zero_right that)
    finally have "degree r<degree r" .
    then show False ..
  qed
  ultimately show ?thesis by auto
qed

end
