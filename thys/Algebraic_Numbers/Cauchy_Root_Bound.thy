(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Cauchy's Root Bound\<close>

text \<open>This theory contains a formalization of Cauchy's root bound, i.e., 
  given an integer polynomial it determines a bound \<open>b\<close> such that all real or complex
  roots of the polynomials have a norm below \<open>b\<close>.\<close>

theory Cauchy_Root_Bound
imports 
  Algebraic_Numbers_Pre_Impl
begin

hide_const (open) UnivPoly.coeff
hide_const (open) Module.smult

text \<open>Division of integers, rounding to the upper value.\<close>
definition div_ceiling :: "int \<Rightarrow> int \<Rightarrow> int" where
  "div_ceiling x y = (let q = x div y in if q * y = x then q else q + 1)" 

definition root_bound :: "int poly \<Rightarrow> rat" where 
  "root_bound p \<equiv> let 
     n = degree p;
     m = 1 + div_ceiling (max_list_non_empty (map (\<lambda>i. abs (coeff p i)) [0..<n])) 
          (abs (lead_coeff p))
     \<comment> \<open>round to the next higher number \<open>2^n\<close>, so that bisection will\<close>
     \<comment> \<open>stay on integers for as long as possible\<close>
   in of_int (2 ^ (log_ceiling 2 m))"
  
  
lemma root_imp_deg_nonzero: assumes "p \<noteq> 0" "poly p x = 0"
  shows "degree p \<noteq> 0" 
proof
  assume "degree p = 0" 
  from degree0_coeffs[OF this] assms show False by auto
qed
  
lemma cauchy_root_bound: fixes x :: "'a :: real_normed_field"
  assumes x: "poly p x = 0" and p: "p \<noteq> 0" 
  shows "norm x \<le> 1 + max_list_non_empty (map (\<lambda> i. norm (coeff p i)) [0 ..< degree p]) 
    / norm (lead_coeff p)" (is "_ \<le> _ + ?max / ?nlc")
proof -
  let ?n = "degree p" 
  let ?p = "coeff p" 
  let ?lc = "lead_coeff p" 
  define ml where "ml = ?max / ?nlc" 
  from p have lc: "?lc \<noteq> 0" by auto
  hence nlc: "norm ?lc > 0" by auto
  from root_imp_deg_nonzero[OF p x] have *: "0 \<in> set [0 ..< degree p]" by auto
  have "0 \<le> norm (?p 0)" by simp
  also have "\<dots> \<le> ?max" 
    by (rule max_list_non_empty, insert *, auto)
  finally have max0: "?max \<ge> 0" .
  with nlc have ml0: "ml \<ge> 0" unfolding ml_def by auto
  hence easy: "norm x \<le> 1 \<Longrightarrow> ?thesis" unfolding ml_def[symmetric] by auto
  show ?thesis
  proof (cases "norm x \<le> 1")
    case True
    thus ?thesis using easy by auto
  next
    case False
    hence nx: "norm x > 1" by simp 
    hence x0: "x \<noteq> 0" by auto
    hence xn0: "0 < norm x ^ ?n" by auto
    from x[unfolded poly_altdef] have "x ^ ?n * ?lc = x ^ ?n * ?lc - (\<Sum>i\<le>?n. x ^ i * ?p i)" 
      unfolding poly_altdef by (simp add: ac_simps)    
    also have "(\<Sum>i\<le>?n. x ^ i * ?p i) = x ^ ?n * ?lc + (\<Sum>i < ?n. x ^ i * ?p i)" 
      by (subst sum.remove[of _ ?n], auto intro: sum.cong)
    finally have "x ^ ?n * ?lc = - (\<Sum>i < ?n. x ^ i * ?p i)" by simp
    with lc have "x ^ ?n = - (\<Sum>i < ?n. x ^ i * ?p i) / ?lc" by (simp add: field_simps)
    from arg_cong[OF this, of norm]
    have "norm x ^ ?n = norm ((\<Sum>i < ?n. x ^ i * ?p i) / ?lc)" unfolding norm_power by simp
    also have "(\<Sum>i < ?n. x ^ i * ?p i) / ?lc = (\<Sum>i < ?n. x ^ i * ?p i / ?lc)" 
      by (rule sum_divide_distrib)
    also have "norm \<dots> \<le> (\<Sum>i < ?n. norm (x ^ i * (?p i / ?lc)))" 
      by (simp add: field_simps, rule norm_sum)
    also have "\<dots> = (\<Sum>i < ?n. norm x ^ i * norm (?p i / ?lc))" 
      unfolding norm_mult norm_power ..
    also have "\<dots> \<le> (\<Sum>i < ?n. norm x ^ i * ml)" 
    proof (rule sum_mono)
      fix i
      assume "i \<in> {..<?n}" 
      hence i: "i < ?n" by simp
      show "norm x ^ i * norm (?p i / ?lc) \<le> norm x ^ i * ml" 
      proof (rule mult_left_mono)
        show "0 \<le> norm x ^ i" using nx by auto
        show "norm (?p i / ?lc) \<le> ml" unfolding norm_divide ml_def
          by (rule divide_right_mono[OF max_list_non_empty], insert nlc i, auto)
      qed
    qed
    also have "\<dots> = ml * (\<Sum>i < ?n. norm x ^ i)" 
      unfolding sum_distrib_right[symmetric] by simp
    also have "(\<Sum>i < ?n. norm x ^ i) = (norm x ^ ?n - 1) / (norm x - 1)" 
      by (rule geometric_sum, insert nx, auto)
    finally have "norm x ^ ?n \<le> ml * (norm x ^ ?n - 1) / (norm x - 1)" by simp        
    from mult_left_mono[OF this, of "norm x - 1"]
    have "(norm x - 1) * (norm x ^ ?n) \<le> ml * (norm x ^ ?n - 1)" using nx by auto
    also have "\<dots> = (ml * (1 - 1 / (norm x ^ ?n))) * norm x ^ ?n" 
      using nx False x0 by (simp add: field_simps)
    finally have "(norm x - 1) * (norm x ^ ?n) \<le> (ml * (1 - 1 / (norm x ^ ?n))) * norm x ^ ?n" .
    from mult_right_le_imp_le[OF this xn0]
    have "norm x - 1 \<le> ml * (1 - 1 / (norm x ^ ?n))" by simp
    hence "norm x \<le> 1 + ml - ml / (norm x ^ ?n)" by (simp add: field_simps)
    also have "\<dots> \<le> 1 + ml" using ml0 xn0 by auto
    finally show ?thesis unfolding ml_def .
  qed
qed
      
lemma div_le_div_ceiling: "x div y \<le> div_ceiling x y" 
  unfolding div_ceiling_def Let_def by auto
    
lemma div_ceiling: assumes q: "q \<noteq> 0"  
  shows "(of_int x :: 'a :: floor_ceiling) / of_int q \<le> of_int (div_ceiling x q)" 
proof (cases "q dvd x")
  case True
  then obtain k where xqk: "x = q * k" unfolding dvd_def by auto
  hence id: "div_ceiling x q = k" unfolding div_ceiling_def Let_def using q by auto
  show ?thesis unfolding id unfolding xqk using q by simp
next
  case False
  {
    assume "x div q * q = x" 
    hence "x = q * (x div q)" by (simp add: ac_simps)
    hence "q dvd x" unfolding dvd_def by auto
    with False have False by simp
  }
  hence id: "div_ceiling x q = x div q + 1" 
    unfolding div_ceiling_def Let_def using q by auto
  show ?thesis unfolding id
    by (metis floor_divide_of_int_eq le_less add1_zle_eq floor_less_iff)
qed
  
lemma max_list_non_empty_map: assumes hom: "\<And> x y. max (f x) (f y) = f (max x y)"  
  shows "xs \<noteq> [] \<Longrightarrow> max_list_non_empty (map f xs) = f (max_list_non_empty xs)" 
  by (induct xs rule: max_list_non_empty.induct, auto simp: hom)

lemma root_bound: assumes "root_bound p = B" and deg: "degree p > 0"
  shows "ipoly p (x :: 'a :: real_normed_field) = 0 \<Longrightarrow> norm x \<le> of_rat B" "B \<ge> 0" 
proof -
  let ?r = "of_rat :: _ \<Rightarrow> 'a" 
  let ?i = "of_int :: _ \<Rightarrow> 'a" 
  let ?p = "map_poly ?i p"
  define n where "n = degree p"
  let ?lc = "coeff p n" 
  let ?list = "map (\<lambda>i. abs (coeff p i)) [0..<n]" 
  let ?list' = "(map (\<lambda>i. real_of_int (abs ((coeff p i)))) [0..<n])" 
  define m where "m = max_list_non_empty ?list"
  define m_up where "m_up = 1 + div_ceiling m (abs ?lc)"
  define C where "C = rat_of_int (2^(log_ceiling 2 m_up))"
  from deg have p0: "p \<noteq> 0" by auto
  from p0 have alc0: "abs ?lc \<noteq> 0" unfolding n_def by auto
  from deg have mem: "abs (coeff p 0) \<in> set ?list" unfolding n_def by auto
  from max_list_non_empty[OF this, folded m_def]    
  have m0: "m \<ge> 0" by auto
  have "div_ceiling m (abs ?lc) \<ge> 0" 
    by (rule order_trans[OF _ div_le_div_ceiling[of m "abs ?lc"]], subst
    pos_imp_zdiv_nonneg_iff, insert p0 m0, auto simp: n_def)
  hence mup: "m_up \<ge> 1" unfolding m_up_def by auto
  have "m_up \<le> 2 ^ (log_ceiling 2 m_up)" using  mup log_ceiling_sound(1) by auto
  hence Cmup: "C \<ge> of_int m_up" unfolding C_def by linarith
  with mup have C: "C \<ge> 1" by auto      
  from assms(1)[unfolded root_bound_def Let_def]
  have B: "C = B" unfolding C_def m_up_def n_def m_def by auto
  note dc = div_le_div_ceiling[of m "abs ?lc"] 
  with C show "B \<ge> 0" unfolding B by auto
  assume "ipoly p x = 0" 
  hence rt: "poly ?p x = 0" by simp
  from root_imp_deg_nonzero[OF _ this] p0 have n0: "n \<noteq> 0" unfolding n_def by auto
  from cauchy_root_bound[OF rt] p0
  have "norm x \<le> 1 + max_list_non_empty ?list' / real_of_int (abs ?lc)" 
    by (simp add: n_def)
  also have "?list' = map real_of_int ?list" by simp
  also have "max_list_non_empty \<dots> = real_of_int m" unfolding m_def
    by (rule max_list_non_empty_map, insert mem, auto)
  also have "1 + m / real_of_int (abs ?lc) \<le> real_of_int m_up" 
    unfolding m_up_def using div_ceiling[OF alc0, of m] by auto
  also have "\<dots> \<le> real_of_rat C" using Cmup using of_rat_less_eq by force
  finally have "norm x \<le> real_of_rat C" .
  thus "norm x \<le> real_of_rat B" unfolding B by simp
qed
  
end
