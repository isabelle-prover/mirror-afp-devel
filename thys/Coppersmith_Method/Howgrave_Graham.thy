section \<open> Howgrave-Graham's theorem \<close>

text \<open> In this file, we prove a result due to Howgrave-Graham on small-enough roots of 
  polynomials mod M (see Theorem 19.1.2 in "Mathematics of Public Key Cryptography" by Galbraith). \<close>

theory Howgrave_Graham

imports Coppersmith_Algorithm
  "HOL-Analysis.L2_Norm"
  "LLL_Basis_Reduction.Norms"
begin

abbreviation euclidean_norm_int_vec::"int vec \<Rightarrow> real"
where "euclidean_norm_int_vec v \<equiv> sqrt (sq_norm_vec v)"

abbreviation euclidean_norm_real_vec::"real vec \<Rightarrow> real"
where "euclidean_norm_real_vec v \<equiv> sqrt (sq_norm_vec v)"

lemma euclidean_norm_int_vec_eq:
  shows "euclidean_norm_int_vec v = sqrt (\<Sum>i<(dim_vec v). (v$i)^2)"
  unfolding sq_norm_vec_def sum_list_sum_nth
  by (auto simp add: list_of_vec_index lessThan_atLeast0 power2_eq_square)

lemma euclidean_norm_real_vec_eq:
  shows "sqrt (sq_norm_vec v) = sqrt (\<Sum>i<(dim_vec v). (v$i)^2)"
  unfolding sq_norm_vec_def sum_list_sum_nth
  by (auto simp add: list_of_vec_index lessThan_atLeast0 power2_eq_square)

lemma euclidean_norm_gteq0:
  shows "euclidean_norm_real_vec (a::real vec) \<ge> 0"
        "euclidean_norm_int_vec (c::int vec) \<ge> 0"
  by (auto simp add: sq_norm_vec_ge_0) 

lemma dim_vec_vec_associated_to_poly[simp]:
  shows "dim_vec (vec_associated_to_poly F X) = degree F + 1"
  unfolding vec_associated_to_poly_def by auto

lemma Cauchy_Schwarz_sum:
  fixes n:: "nat"
  fixes x:: "nat \<Rightarrow> real"
  shows "(\<Sum>i\<le>n. x i) \<le> sqrt ((n+1) * (\<Sum>i\<le>n. (x i)^2))"
proof -
  have "(\<Sum>i\<le>n. x i) \<le> (\<Sum>i\<le>n. \<bar>x i\<bar> * \<bar>1\<bar>)"
    by (auto intro!: sum_mono)
  also have "... \<le> L2_set x {..n} * L2_set (\<lambda>_. 1) {..n}"
    using L2_set_mult_ineq
    by fastforce
  also have "... = sqrt (\<Sum>i\<le>n. (x i)\<^sup>2) * sqrt (\<Sum>i\<le>n. 1\<^sup>2)"
    unfolding L2_set_def by auto
  also have "... = sqrt ( (n+1) * (\<Sum>i\<le>n. (x i)\<^sup>2))"
    using real_sqrt_mult by auto
  finally show ?thesis .
qed

lemma abs_mult_sum:
  fixes f g:: "nat \<Rightarrow> real"
  fixes n:: "nat"
  shows "abs(\<Sum>i\<le>n. (f i)*(g i))
    \<le> (\<Sum>i\<le>n. (abs (f i))*(abs (g i)))"
proof (induct n)
  case 0
  have " \<bar>f 0 * g 0\<bar> \<le> \<bar>f 0\<bar> * \<bar>g 0\<bar>"
    by (simp add: abs_mult)
  then show ?case using 0 
    by auto 
  case (Suc n)
  then have "\<bar>\<Sum>i\<le>Suc n. f i * g i\<bar> \<le> \<bar>\<Sum>i\<le>n. f i * g i\<bar> + \<bar>f (Suc n) * g (Suc n)\<bar> "
    by (simp add: abs_triangle_ineq)
  then have "\<bar>\<Sum>i\<le>Suc n. f i * g i\<bar> \<le> (\<Sum>i\<le>n. \<bar>f i\<bar> * \<bar>g i\<bar>) + \<bar>f (Suc n) * g (Suc n)\<bar>"
    using Suc by auto 
  then show ?case 
    using abs_mult[of "f (Suc n)" "g (Suc n)"]
    by (metis (mono_tags, lifting) sum.atMost_Suc) 
qed

lemma sum_helper:
  fixes g h:: "nat \<Rightarrow> real"
  assumes "\<forall> i \<le> n. f i \<ge> 0"
  assumes "\<forall>i \<le> n. g i \<le> h i"
  shows "(\<Sum>i\<le>n. (f i)* (g i)) \<le> (\<Sum>i\<le>n. (f i)* (h i))"
  using assms 
proof (induct n)
  case 0
  have "0 \<le> f 0 \<Longrightarrow> g 0 \<le> h 0 \<Longrightarrow> f 0 * g 0 \<le> f 0 * h 0"
    by (simp add: mult_left_mono)
  then show ?case using 0
    by auto 
next
  case (Suc n)
  have "0 \<le> f (Suc n) \<Longrightarrow> g (Suc n) \<le> h (Suc n) \<Longrightarrow> f (Suc n) * g (Suc n) \<le> f (Suc n) * h (Suc n)"
    by (simp add: mult_left_mono)
  then have Suc_h: "f (Suc n) * g (Suc n) \<le> f (Suc n) * h (Suc n)"
    using Suc by auto
  have ind_h: "(\<Sum>i\<le>n. f i * g i) \<le> (\<Sum>i\<le>n. f i * h i)"
    using Suc by auto
  show ?case using ind_h Suc_h
    by auto 
qed

theorem Howgrave_Graham:
  fixes F :: "real poly"
  fixes M X :: "nat"
  fixes x0 k :: "int"
  assumes M_gt: "M > 0"
  assumes root_mod_M: "poly F (real_of_int x0) = k * M"
  assumes root_bound: "abs x0 \<le> X"
  assumes norm_bound: "sqrt (\<parallel>vec_associated_to_poly F X\<parallel>\<^sup>2) < M / sqrt (degree F + 1)"
  shows "poly F x0 = 0"
proof -
  let ?d = "degree F"
  let ?bF = "vec_associated_to_poly F X"

  have h2: "i\<le>?d \<Longrightarrow> real_of_int(\<bar>x0\<bar> ^ i) \<le> real (X ^ i)" for i
    using root_bound
    by (simp add: linordered_semidom_class.power_mono) 

  have "abs (poly F x0) =
    abs (\<Sum>i\<le>?d. (coeff F i)* x0^i)"
    using poly_altdef
    by (smt (verit) of_int_power sum.cong)
  also have "... \<le> (\<Sum>n\<le>?d. \<bar>poly.coeff F n * real_of_int (x0 ^ n)\<bar>)"
    by blast
  also have "... = (\<Sum>n\<le>?d. \<bar>poly.coeff F n\<bar> * real_of_int (\<bar>x0\<bar> ^ n))"
    by (simp add: abs_mult power_abs)
  also have "... \<le> (\<Sum>n\<le>?d. \<bar>poly.coeff F n\<bar> * (X^n))"
     using h2
     by (auto intro:sum_mono simp add: mult_left_mono)
  also have "... \<le> sqrt ((?d+1)*(\<Sum>n\<le>?d. (\<bar>poly.coeff F n\<bar> * (X^n))^2))"
    using  Cauchy_Schwarz_sum  by blast
  also have "... = sqrt ((?d+1)*(\<Sum>n\<le>?d. (poly.coeff F n * (X^n))^2))"
    by (simp add: power_mult_distrib)
  also have "... =  sqrt ((?d+1)*(\<Sum>i\<le>?d. (?bF $ i)^2))"
    unfolding vec_associated_to_poly_def by auto
  also have "... =  sqrt ((?d+1)*(\<Sum>i<?d+1. (?bF $ i)^2))"
    using Suc_eq_plus1 lessThan_Suc_atMost by presburger
  also have "... =  sqrt (?d+1) * sqrt (\<Sum>i<?d+1. (?bF $ i)^2)"
    using real_sqrt_mult by blast
  also have "... =  sqrt (?d+1) * sqrt (sq_norm_vec ?bF)"
    unfolding euclidean_norm_real_vec_eq
    by force
  also have "... < M"
    using norm_bound
    by (smt (verit, ccfv_SIG) Groups.mult_ac(2) add_is_0 eq_numeral_extra(2) mult_imp_div_pos_le of_nat_le_0_iff real_sqrt_gt_zero) 
  finally have "abs (poly F x0) < M" .
  then have "-M < poly F x0 \<and> poly F x0 < M"
    by linarith
  thus ?thesis 
    using root_mod_M M_gt
    by (smt (verit, del_insts) aux_abs_int mult.commute mult_eq_0_iff of_int_hom.hom_0_iff of_int_less_iff of_int_of_nat_eq)
qed

abbreviation int_poly_to_real_poly:: "int poly \<Rightarrow> real poly"
  where "int_poly_to_real_poly F \<equiv> map_poly real_of_int F"

lemma int_poly_to_real_poly_same_norm:
  fixes X :: nat
  shows "euclidean_norm_int_vec (vec_associated_to_int_poly F X) = 
      euclidean_norm_real_vec (vec_associated_to_real_poly (int_poly_to_real_poly F) X)"
proof -
  let ?d = "dim_vec (vec_associated_to_int_poly F X)"
  have same_dim: "dim_vec (vec_associated_to_int_poly F X) =
    dim_vec (vec_associated_to_real_poly (int_poly_to_real_poly F) X)"
    by simp
  have "\<And>i. i < ?d \<Longrightarrow> (vec_associated_to_real_poly (int_poly_to_real_poly F) X $ i) = (real_of_int (vec_associated_to_int_poly F X $ i))"
    unfolding vec_associated_to_poly_def by auto
  then have "(\<Sum>x<?d. (real_of_int (vec_associated_to_int_poly F X $ x))\<^sup>2) =
    (\<Sum>i<?d. (vec_associated_to_real_poly (int_poly_to_real_poly F) X $ i)\<^sup>2)"
    by fastforce
  then show ?thesis
    unfolding euclidean_norm_int_vec_eq euclidean_norm_real_vec_eq
    using same_dim
    by auto
qed

text \<open> Now we restate the result over int polys. \<close>
lemma Howgrave_Graham_int_poly:
  fixes F:: "int poly"
  fixes M X:: "nat"
  fixes x0:: "int"
  assumes M_gt: "M > 0"
  assumes root_mod_M: "poly F x0 mod M = 0"
  assumes root_bound: "abs x0 \<le> X"
  assumes norm_bound: "sqrt (sq_norm_vec (vec_associated_to_int_poly F X)) < M / sqrt (degree F + 1)"
  shows "poly F x0 = 0"
proof - 
  let ?rF = "int_poly_to_real_poly F"
  from root_mod_M have \<open>M dvd poly F x0\<close>
    by presburger
  then obtain k where \<open>poly F x0 = int M * k\<close> ..
  then have "poly ?rF (real_of_int x0) = 0"
    apply (intro Howgrave_Graham[OF M_gt _ root_bound])
    using assms int_poly_to_real_poly_same_norm[of F X] by auto
  thus ?thesis by auto
qed

end
