theory Additional_Lemmas

imports 
  Main
  infnorm
  Partition
  Lattice_int
  Digits_int
begin

section \<open>Additional Lemmas\<close>

text \<open>Lemma about length and concat.\<close>
lemma length_concat_map_5: 
  "length (concat (map (\<lambda>i. [f1 i, f2 i, f3 i, f4 i, f5 i]) xs)) = length xs * 5" 
by (induct xs, auto)

text \<open>Lemma about splitting the index of sums.\<close>
lemma sum_split_idx_prod:
  "(\<Sum>i=0..<k*l::nat. f i) = (\<Sum>i=0..<k. (\<Sum>j=0..<l. f (i*l+j)))"
proof -
  have set_rew: "{0..<k*l} = (\<lambda>(i,j). i*l+j) ` ({0..<k} \<times> {0..<l})"
  proof (safe, goal_cases)
    case (1 x)
    have "x = (\<lambda>(i,j). i*l+j) (x div l, x mod l)" by auto
    moreover have "(x div l, x mod l)\<in>{0..<k} \<times> {0..<l}" using 1 less_mult_imp_div_less
      by (metis le_less_trans lessThan_atLeast0 lessThan_iff mem_Sigma_iff
        mod_less_divisor mult_zero_right neq0_conv zero_le)
    ultimately show ?case by blast
  next
    case (2 x i j)
    then show ?case 
    by (auto, metis less_nat_zero_code linorder_neqE_nat mod_lemma mult.commute nat_mod_lem)
  qed
  have inj: "inj_on (\<lambda>(i, y). i * l + y) ({0..<k} \<times> {0..<l})" 
    unfolding inj_on_def by (auto) 
      (metis add.commute add_right_imp_eq linorder_neqE_nat mod_mult_self2 mult.commute 
        mult_cancel_right nat_mod_lem not_less_zero, 
       metis add.commute le0 le_less_trans mod_mult_self2 mult.commute nat_mod_lem)
  have "(\<Sum> i\<in>{0..<k*l}. f i) = (\<Sum>(i,j)\<in>{0..<k}\<times>{0..<l}. f (i*l+j))" 
    unfolding set_rew using inj
    by (subst sum.reindex[of "(\<lambda>(i, j). i * l + j)" "({0..<k} \<times> {0..<l})" f])
       (auto simp add: prod.case_distrib)
  also have "\<dots> = (\<Sum>i\<in>{0..<k}. (\<Sum>j\<in>{0..<l}. f (i*l+j)))"
    using sum.cartesian_product[of "(\<lambda>i j. f (i*l+j))" "{0..<l}" "{0..<k}", symmetric]
    by auto
  finally show ?thesis by auto
qed

text \<open>Helping lemma to split sums.\<close>

lemma lt_M:
  assumes "M > (\<Sum>i<(n::nat). \<bar>b i\<bar>::int)"
          "\<forall>i<n. \<bar>x i\<bar> \<le> 1" 
  shows "\<bar>(\<Sum>i<n. x i * b i)\<bar> < M"
proof - 
  have "\<bar>(\<Sum>i<(n::nat). x i * b i)::int\<bar> \<le> (\<Sum>i<n. \<bar>x i * b i\<bar>)" using sum_abs by auto
  moreover have "\<dots> = (\<Sum>i<n. \<bar>x i\<bar> * \<bar>b i\<bar>)" using abs_mult by metis
  moreover have "\<dots> \<le> (\<Sum>i<n. \<bar>b i\<bar>)" using assms 
    by (smt (verit, best) lessThan_iff mult_cancel_right2 sum_mono zero_less_mult_iff)
  moreover have "\<dots> = (\<Sum>i<n. \<bar>b i\<bar>)" using sum_distrib_left by metis
  ultimately have "\<bar>(\<Sum>i<n. x i * b i)\<bar> \<le> (\<Sum>i<n. \<bar>b i\<bar>)" by linarith
  then show ?thesis using assms by auto
qed



lemma split_sum:
  "(\<Sum>i<(n::nat). x i * (a i + M * b i)::int) = (\<Sum>i<n. x i * a i) + M * (\<Sum>i<n. x i * b i)"
proof -
  have "(\<Sum>i<(n::nat). x i * (a i + M * b i)) = (\<Sum>i<n. x i * a i) + (\<Sum>i<n. M * x i * b i)"
    by (simp add: distrib_left mult.commute mult.left_commute)
  also have "\<dots> = (\<Sum>i<n. x i * a i) + M * (\<Sum>i<n. x i * b i)"
    using sum_distrib_left[symmetric, where r=M and f="(\<lambda>i. x i*b i)" and A = "{0..<n}"]  
    by (metis (no_types, lifting) lessThan_atLeast0 mult.assoc sum.cong)
  finally show ?thesis by blast
qed



lemma split_eq_system:
  assumes "M > (\<Sum>i<n::nat. \<bar>a i\<bar>::int)"
          "\<forall>i<n. \<bar>x i\<bar> \<le> 1" 
          "(\<Sum>i<n. x i * (a i + M * b i)) = 0" 
  shows   "(\<Sum>i<n. x i * a i) = 0 \<and> (\<Sum>i<n. x i * b i) = 0"
using assms proof (safe, goal_cases)
  case 1
  then show ?case 
  proof (cases "(\<Sum>i<n. x i * b i) = 0")
    case True
    then show ?thesis using assms(3) split_sum[of x a M b n] by auto
  next
    case False
    then have "\<bar>(\<Sum>i<n. x i * a i)\<bar> < M * \<bar>(\<Sum>i<n. x i * b i)\<bar>" 
      using lt_M[OF assms(1) assms(2)] False
      by (smt (verit, best) mult_less_cancel_left2)
    moreover have "\<bar>(\<Sum>i<n. x i * a i)\<bar> = M * \<bar>(\<Sum>i<n. x i * b i)\<bar>" 
      using assms(3) split_sum[of x a M b n] calculation by linarith
    ultimately have False by linarith 
    then show ?thesis by auto
  qed
next
  case 2
  then show ?case 
  proof (cases "(\<Sum>i<n. x i * b i) = 0")
    case True
    then show ?thesis using split_sum 2 using lt_M[OF assms(1) assms(2)]
       by auto
  next
    case False
    then have "\<bar>(\<Sum>i<n. x i * a i)\<bar> < M * \<bar>(\<Sum>i<n. x i * b i)\<bar>" 
      using lt_M[OF assms(1) assms(2)] False
      by (smt (verit, best) mult_less_cancel_left2)
    moreover have "\<bar>(\<Sum>i<n. x i * a i)\<bar> = M * \<bar>(\<Sum>i<n. x i * b i)\<bar>" 
      using split_sum[of x a M b n] assms calculation by linarith
    ultimately have False by linarith 
    then show ?thesis by auto
  qed
qed


text \<open>Lemmas about splitting into 4 or 5 cases.\<close>
text \<open>Split into $4$ modulo classes\<close>
lemma lt_4_split: "(i::nat) < 4 \<longrightarrow> i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
by auto 

lemma mod_exhaust_less_4_int: "(i::int) mod 4 = 0 \<or> i mod 4 = 1 \<or> i mod 4 = 2 \<or> i mod 4 = 3"
using MacLaurin.mod_exhaust_less_4 by auto

lemma mod_4_choices:
  assumes "i mod 4 = 0 \<longrightarrow> P i"
          "i mod 4 = 1 \<longrightarrow> P i"
          "i mod 4 = 2 \<longrightarrow> P i"
          "i mod 4 = 3 \<longrightarrow> P i"
  shows "P (i::nat)"
using assms mod_exhaust_less_4 by auto

lemma mod_4_if_split:
  assumes "i mod 4 = 0 \<longrightarrow> P = P0 i"
          "i mod 4 = 1 \<longrightarrow> P = P1 i"
          "i mod 4 = 2 \<longrightarrow> P = P2 i"
          "i mod 4 = 3 \<longrightarrow> P = P3 i"
  shows "P = (if i mod 4 = 0 then P0 i else
               (if i mod 4 = 1 then P1 i else
               (if i mod 4 = 2 then P2 i else P3 (i::nat))))" (is "?P i")
using mod_exhaust_less_4  by (auto simp add: assms)

text \<open>Split into $5$ modulo classes\<close>

lemma lt_5_split: "(i::nat) < 5 \<longrightarrow> i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4"
by auto

lemma mod_exhaust_less_5_int: 
  "(i::int) mod 5 = 0 \<or> i mod 5 = 1 \<or> i mod 5 = 2 \<or> i mod 5 = 3 \<or> i mod 5 = 4"
using lt_5_split by linarith

lemma mod_exhaust_less_5: 
  "(i::nat) mod 5 = 0 \<or> i mod 5 = 1 \<or> i mod 5 = 2 \<or> i mod 5 = 3 \<or> i mod 5 = 4"
using lt_5_split by linarith

lemma mod_5_choices:
  assumes "i mod 5 = 0 \<longrightarrow> P i"
          "i mod 5 = 1 \<longrightarrow> P i"
          "i mod 5 = 2 \<longrightarrow> P i"
          "i mod 5 = 3 \<longrightarrow> P i"
          "i mod 5 = 4 \<longrightarrow> P i"
  shows "P (i::nat)"
using assms mod_exhaust_less_5 by auto

lemma mod_5_if_split:
  assumes "i mod 5 = 0 \<longrightarrow> P = P0 i"
          "i mod 5 = 1 \<longrightarrow> P = P1 i"
          "i mod 5 = 2 \<longrightarrow> P = P2 i"
          "i mod 5 = 3 \<longrightarrow> P = P3 i"
          "i mod 5 = 4 \<longrightarrow> P = P4 i"
  shows "P = (if i mod 5 = 0 then P0 i else
               (if i mod 5 = 1 then P1 i else
               (if i mod 5 = 2 then P2 i else
               (if i mod 5 = 3 then P3 i else
                                    P4 (i::nat)))))" (is "?P i")
using mod_exhaust_less_5  by (auto simp add: assms)

text \<open>Representation of natural number in interval using lower bound.\<close>

lemma split_lower_plus_diff:
  assumes "s \<in> {n..<m::nat}"
  obtains j where "s = n+j" and "j<m-n"
using assms 
by (metis atLeastLessThan_iff diff_diff_left le_Suc_ex zero_less_diff)


end