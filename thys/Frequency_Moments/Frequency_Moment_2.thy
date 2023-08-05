section \<open>Frequency Moment $2$\<close>

theory Frequency_Moment_2
  imports
    Universal_Hash_Families.Carter_Wegman_Hash_Family
    Universal_Hash_Families.Universal_Hash_Families_More_Finite_Fields
    Equivalence_Relation_Enumeration.Equivalence_Relation_Enumeration
    Landau_Ext
    Median_Method.Median
    Product_PMF_Ext
    Frequency_Moments 
begin

text \<open>This section contains a formalization of the algorithm for the second frequency moment.
It is based on the algorithm described in \<^cite>\<open>\<open>\textsection 2.2\<close> in "alon1999"\<close>.
The only difference is that the algorithm is adapted to work with prime field of odd order, which
greatly reduces the implementation complexity.\<close>

fun f2_hash where
  "f2_hash p h k = (if even (ring.hash (mod_ring p) k h) then int p - 1 else - int p - 1)"

type_synonym f2_state = "nat \<times> nat \<times> nat \<times> (nat \<times> nat \<Rightarrow> nat list) \<times> (nat \<times> nat \<Rightarrow> int)"

fun f2_init :: "rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> f2_state pmf" where
  "f2_init \<delta> \<epsilon> n =
    do {
      let s\<^sub>1 = nat \<lceil>6 / \<delta>\<^sup>2\<rceil>;
      let s\<^sub>2 = nat \<lceil>-(18 * ln (real_of_rat \<epsilon>))\<rceil>;
      let p = prime_above (max n 3);
      h \<leftarrow> prod_pmf ({..<s\<^sub>1} \<times> {..<s\<^sub>2}) (\<lambda>_. pmf_of_set (bounded_degree_polynomials (mod_ring p) 4));
      return_pmf (s\<^sub>1, s\<^sub>2, p, h, (\<lambda>_ \<in> {..<s\<^sub>1} \<times> {..<s\<^sub>2}. (0 :: int)))
    }"

fun f2_update :: "nat \<Rightarrow> f2_state \<Rightarrow> f2_state pmf" where
  "f2_update x (s\<^sub>1, s\<^sub>2, p, h, sketch) = 
    return_pmf (s\<^sub>1, s\<^sub>2, p, h, \<lambda>i \<in> {..<s\<^sub>1} \<times> {..<s\<^sub>2}. f2_hash p (h i) x + sketch i)"

fun f2_result :: "f2_state \<Rightarrow> rat pmf" where
  "f2_result (s\<^sub>1, s\<^sub>2, p, h, sketch) = 
    return_pmf (median s\<^sub>2 (\<lambda>i\<^sub>2 \<in> {..<s\<^sub>2}. 
      (\<Sum>i\<^sub>1\<in>{..<s\<^sub>1} . (rat_of_int (sketch (i\<^sub>1, i\<^sub>2)))\<^sup>2) / (((rat_of_nat p)\<^sup>2-1) * rat_of_nat s\<^sub>1)))"

fun f2_space_usage :: "(nat \<times> nat \<times> rat \<times> rat) \<Rightarrow> real" where
  "f2_space_usage (n, m, \<epsilon>, \<delta>) = (
    let s\<^sub>1 = nat \<lceil>6 / \<delta>\<^sup>2 \<rceil> in
    let s\<^sub>2 = nat \<lceil>-(18 * ln (real_of_rat \<epsilon>))\<rceil> in 
    3 +
    2 * log 2 (s\<^sub>1 + 1) +
    2 * log 2 (s\<^sub>2 + 1) +
    2 * log 2 (9 + 2 * real n) +
    s\<^sub>1 * s\<^sub>2 * (5 + 4*log 2 (8 + 2 * real n) + 2 * log 2 (real m * (18 + 4 * real n) + 1 )))"

definition encode_f2_state :: "f2_state \<Rightarrow> bool list option" where
  "encode_f2_state = 
    N\<^sub>e \<Join>\<^sub>e (\<lambda>s\<^sub>1. 
    N\<^sub>e \<Join>\<^sub>e (\<lambda>s\<^sub>2. 
    N\<^sub>e \<Join>\<^sub>e (\<lambda>p. 
    (List.product [0..<s\<^sub>1] [0..<s\<^sub>2] \<rightarrow>\<^sub>e P\<^sub>e p 4) \<times>\<^sub>e
    (List.product [0..<s\<^sub>1] [0..<s\<^sub>2] \<rightarrow>\<^sub>e I\<^sub>e))))"

lemma "inj_on encode_f2_state (dom encode_f2_state)"
proof -
  have " is_encoding encode_f2_state"
    unfolding encode_f2_state_def
    by (intro dependent_encoding exp_golomb_encoding fun_encoding list_encoding int_encoding poly_encoding)
      
  thus ?thesis
    by (rule encoding_imp_inj)
qed

context
  fixes \<epsilon> \<delta> :: rat
  fixes n :: nat
  fixes as :: "nat list"
  fixes result
  assumes \<epsilon>_range: "\<epsilon> \<in> {0<..<1}"
  assumes \<delta>_range: "\<delta> > 0"
  assumes as_range: "set as \<subseteq> {..<n}"
  defines "result \<equiv> fold (\<lambda>a state. state \<bind> f2_update a) as (f2_init \<delta> \<epsilon> n) \<bind> f2_result"
begin  

private definition s\<^sub>1 where "s\<^sub>1 = nat \<lceil>6 / \<delta>\<^sup>2\<rceil>"

lemma s1_gt_0: "s\<^sub>1 > 0"
    using \<delta>_range by (simp add:s\<^sub>1_def)

private definition s\<^sub>2 where "s\<^sub>2 = nat \<lceil>-(18* ln (real_of_rat \<epsilon>))\<rceil>"

lemma s2_gt_0: "s\<^sub>2 > 0"
    using \<epsilon>_range by (simp add:s\<^sub>2_def)

private definition p where "p = prime_above (max n 3)"
 
lemma p_prime: "Factorial_Ring.prime p" 
  unfolding p_def using prime_above_prime by blast

lemma p_ge_3: "p \<ge> 3"
    unfolding p_def by (meson max.boundedE prime_above_lower_bound)

lemma p_gt_0: "p > 0" using p_ge_3 by linarith

lemma p_gt_1: "p > 1" using p_ge_3 by simp

lemma p_ge_n: "p \<ge> n" unfolding p_def
  by (meson max.boundedE prime_above_lower_bound )

interpretation carter_wegman_hash_family "mod_ring p" 4
  using carter_wegman_hash_familyI[OF mod_ring_is_field mod_ring_finite]
  using p_prime by auto

definition sketch where "sketch = fold (\<lambda>a state. state \<bind> f2_update a) as (f2_init \<delta> \<epsilon> n)"
private definition \<Omega> where"\<Omega> = prod_pmf ({..<s\<^sub>1} \<times> {..<s\<^sub>2}) (\<lambda>_. pmf_of_set space)" 
private definition \<Omega>\<^sub>p where"\<Omega>\<^sub>p = measure_pmf \<Omega>" 
private definition sketch_rv where "sketch_rv \<omega> = of_int (sum_list (map (f2_hash p \<omega>) as))^2"
private definition mean_rv where "mean_rv \<omega> = (\<lambda>i\<^sub>2. (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. sketch_rv (\<omega> (i\<^sub>1, i\<^sub>2))) / (((of_nat p)\<^sup>2 - 1) * of_nat s\<^sub>1))"
private definition result_rv where "result_rv \<omega> = median s\<^sub>2 (\<lambda>i\<^sub>2\<in>{..<s\<^sub>2}. mean_rv \<omega> i\<^sub>2)"

lemma mean_rv_alg_sketch:
  "sketch = \<Omega> \<bind> (\<lambda>\<omega>. return_pmf (s\<^sub>1, s\<^sub>2, p, \<omega>, \<lambda>i \<in> {..<s\<^sub>1} \<times> {..<s\<^sub>2}. sum_list (map (f2_hash p (\<omega> i)) as)))"
proof -
  have "sketch =  fold (\<lambda>a state. state \<bind> f2_update a) as (f2_init \<delta> \<epsilon> n)"
    by (simp add:sketch_def)
  also have "... = \<Omega> \<bind> (\<lambda>\<omega>. return_pmf (s\<^sub>1, s\<^sub>2, p, \<omega>, 
      \<lambda>i \<in> {..<s\<^sub>1} \<times> {..<s\<^sub>2}. sum_list (map (f2_hash p (\<omega> i)) as)))"
  proof (induction as rule:rev_induct)
    case Nil
    then show ?case 
      by (simp add:s\<^sub>1_def s\<^sub>2_def space_def p_def[symmetric] \<Omega>_def restrict_def Let_def) 
  next
    case (snoc a as)
    have "fold (\<lambda>a state. state \<bind> f2_update a) (as @ [a]) (f2_init \<delta> \<epsilon> n) = \<Omega> \<bind> 
      (\<lambda>\<omega>. return_pmf (s\<^sub>1, s\<^sub>2, p, \<omega>, \<lambda>s \<in> {..<s\<^sub>1} \<times> {..<s\<^sub>2}. (\<Sum>x \<leftarrow> as.  f2_hash p (\<omega> s) x)) \<bind> f2_update a)"
      using snoc by (simp add: bind_assoc_pmf restrict_def del:f2_hash.simps f2_init.simps)
    also have "... =  \<Omega> \<bind> (\<lambda>\<omega>. return_pmf (s\<^sub>1, s\<^sub>2, p, \<omega>, \<lambda>i \<in> {..<s\<^sub>1} \<times> {..<s\<^sub>2}. (\<Sum>x \<leftarrow> as@[a].  f2_hash p (\<omega> i) x)))"
      by (subst bind_return_pmf) (simp add: add.commute del:f2_hash.simps cong:restrict_cong)
    finally show ?case by blast
  qed
  finally show ?thesis by auto
qed

lemma distr:  "result = map_pmf result_rv \<Omega>"
proof -
  have "result = sketch \<bind> f2_result"
    by (simp add:result_def sketch_def)
  also have "... = \<Omega> \<bind> (\<lambda>x. f2_result (s\<^sub>1, s\<^sub>2, p, x, \<lambda>i\<in>{..<s\<^sub>1} \<times> {..<s\<^sub>2}. sum_list (map (f2_hash p (x i)) as)))"
    by (simp add: mean_rv_alg_sketch  bind_assoc_pmf bind_return_pmf)
  also have "... = map_pmf result_rv \<Omega>"
    by (simp add:map_pmf_def result_rv_def mean_rv_def sketch_rv_def lessThan_atLeast0 cong:restrict_cong)
  finally show ?thesis by simp
qed

private lemma f2_hash_pow_exp:
  assumes "k < p"
  shows
    "expectation (\<lambda>\<omega>. real_of_int (f2_hash p \<omega> k) ^m) = 
     ((real p - 1) ^ m * (real p + 1) + (- real p - 1) ^ m * (real p - 1)) / (2 * real p)"
proof -

  have "odd p" using p_prime p_ge_3 prime_odd_nat assms by simp
  then obtain t where t_def: "p=2*t+1" 
    using oddE by blast

  have "Collect even \<inter> {..<2 * t + 1} \<subseteq> (*) 2 ` {..<t + 1}" 
    by (rule in_image_by_witness[where g="\<lambda>x. x div 2"], simp, linarith)
  moreover have " (*) 2 ` {..<t + 1} \<subseteq> Collect even \<inter> {..<2 * t + 1}"
    by (rule image_subsetI, simp)
  ultimately have "card ({k. even k} \<inter> {..<p}) = card ((\<lambda>x. 2*x) ` {..<t+1})"
    unfolding t_def using order_antisym by metis
  also have "... = card {..<t+1}" 
    by (rule card_image, simp add: inj_on_mult)
  also have "... =  t+1" by simp
  finally have card_even: "card ({k. even k} \<inter> {..<p}) = t+1" by simp
  hence "card ({k. even k} \<inter> {..<p}) * 2 = (p+1)" by (simp add:t_def)
  hence prob_even: "prob {\<omega>. hash k \<omega> \<in> Collect even} = (real p + 1)/(2*real p)"
    using assms by (subst prob_range, auto simp:frac_eq_eq p_gt_0 mod_ring_def) 

  have "p = card {..<p}" by simp
  also have "... = card (({k. odd k} \<inter> {..<p}) \<union> ({k. even k} \<inter> {..<p}))" 
    by (rule arg_cong[where f="card"], auto)
  also have "... = card ({k. odd k} \<inter> {..<p}) +  card ({k. even k} \<inter> {..<p})"
    by (rule card_Un_disjoint, simp, simp, blast)
  also have "... = card ({k. odd k} \<inter> {..<p}) + t+1"
    by (simp add:card_even)
  finally have "p = card ({k. odd k} \<inter> {..<p}) + t+1"
    by simp
  hence "card ({k. odd k} \<inter> {..<p}) * 2 = (p-1)" 
    by (simp add:t_def)
  hence prob_odd: "prob {\<omega>. hash k \<omega> \<in> Collect odd} = (real p - 1)/(2*real p)"
    using assms by (subst prob_range, auto simp add: frac_eq_eq mod_ring_def)

  have "expectation (\<lambda>x. real_of_int (f2_hash p x k) ^ m) =
    expectation (\<lambda>\<omega>. indicator {\<omega>. even (hash k \<omega>)} \<omega> * (real p - 1)^m + 
      indicator {\<omega>. odd (hash k \<omega>)} \<omega> * (-real p - 1)^m)" 
    by (rule Bochner_Integration.integral_cong, simp, simp)
  also have "... = 
     prob {\<omega>. hash  k \<omega> \<in> Collect even}  * (real p - 1) ^ m  + 
     prob {\<omega>. hash  k \<omega> \<in> Collect odd}  * (-real p - 1) ^ m "
    by (simp, simp add:M_def)
  also have "... = (real p + 1) * (real p - 1) ^ m / (2 * real p) + (real p - 1) * (- real p - 1) ^ m / (2 * real p)"
    by (subst prob_even, subst prob_odd, simp)
  also have "... =  
    ((real p - 1) ^ m * (real p + 1) + (- real p - 1) ^ m * (real p - 1)) / (2 * real p)"
    by (simp add:add_divide_distrib ac_simps)
  finally show "expectation (\<lambda>x. real_of_int (f2_hash p x k) ^ m) = 
    ((real p - 1) ^ m * (real p + 1) + (- real p - 1) ^ m * (real p - 1)) / (2 * real p)" by simp
qed

lemma 
  shows var_sketch_rv:"variance sketch_rv \<le> 2*(real_of_rat (F 2 as)^2) * ((real p)\<^sup>2-1)\<^sup>2" (is "?A")
  and exp_sketch_rv:"expectation sketch_rv = real_of_rat (F 2 as) * ((real p)\<^sup>2-1)" (is "?B")
proof -
  define h where "h = (\<lambda>\<omega> x. real_of_int (f2_hash p \<omega> x))"
  define c where "c = (\<lambda>x. real (count_list as x))"
  define r where "r = (\<lambda>(m::nat). ((real p - 1) ^ m * (real p + 1) + (- real p - 1) ^ m * (real p - 1)) / (2 * real p))"
  define h_prod where "h_prod = (\<lambda>as \<omega>. prod_list (map (h \<omega>) as))" 

  define exp_h_prod :: "nat list \<Rightarrow> real" where "exp_h_prod = (\<lambda>as. (\<Prod>i \<in> set as. r (count_list as i)))"

  have f_eq: "sketch_rv = (\<lambda>\<omega>. (\<Sum>x \<in> set as. c x * h \<omega> x)^2)"
    by (rule ext, simp add:sketch_rv_def c_def h_def sum_list_eval del:f2_hash.simps)

  have r_one: "r (Suc 0) = 0"
    by (simp add:r_def algebra_simps)

  have r_two: "r 2 = (real p^2-1)"
    using p_gt_0 unfolding r_def power2_eq_square 
    by (simp add:nonzero_divide_eq_eq, simp add:algebra_simps)

  have"(real p)^2 \<ge> 2^2"
    by (rule power_mono, use p_gt_1 in linarith, simp)
  hence p_square_ge_4: "(real p)\<^sup>2 \<ge> 4" by simp

  have "r 4 = (real p)^4+2*(real p)\<^sup>2 - 3" 
    using p_gt_0 unfolding r_def
    by (subst nonzero_divide_eq_eq, auto simp:power4_eq_xxxx power2_eq_square algebra_simps)
  also have "... \<le> (real p)^4+2*(real p)\<^sup>2 + 3"
    by simp
  also have "... \<le> 3 * r 2 * r 2"
    using p_square_ge_4
    by (simp add:r_two power4_eq_xxxx power2_eq_square algebra_simps mult_left_mono)
  finally have r_four_est: "r 4 \<le> 3 * r 2 * r 2"  by simp

  have exp_h_prod_elim: "exp_h_prod = (\<lambda>as. prod_list (map (r \<circ> count_list as) (remdups as)))" 
    by (simp add:exp_h_prod_def prod.set_conv_list[symmetric])

  have exp_h_prod: "\<And>x. set x \<subseteq> set as \<Longrightarrow> length x \<le> 4 \<Longrightarrow> expectation (h_prod x) = exp_h_prod x"
  proof -
    fix x 
    assume "set x \<subseteq> set as"
    hence x_sub_p: "set x \<subseteq> {..<p}" using as_range p_ge_n by auto
    hence x_le_p: "\<And>k. k \<in> set x \<Longrightarrow> k < p" by auto
    assume "length x \<le> 4"
    hence card_x: "card (set x) \<le> 4" using card_length dual_order.trans by blast

    have "set x \<subseteq> carrier (mod_ring p) "
      using x_sub_p by (simp add:mod_ring_def)

    hence h_indep: "indep_vars (\<lambda>_. borel) (\<lambda>i \<omega>. h \<omega> i ^ count_list x i) (set x)"
      using k_wise_indep_vars_subset[OF k_wise_indep] card_x as_range h_def
      by (auto intro:indep_vars_compose2[where X="hash" and M'=" (\<lambda>_. discrete)"])

    have "expectation (h_prod x) = expectation (\<lambda>\<omega>. \<Prod> i \<in> set x. h \<omega> i^(count_list x i))"
      by (simp add:h_prod_def prod_list_eval)
    also have "... = (\<Prod>i \<in> set x. expectation (\<lambda>\<omega>. h \<omega> i^(count_list x i)))"
      by (simp add: indep_vars_lebesgue_integral[OF _ h_indep])
    also have "... = (\<Prod>i \<in> set x. r (count_list x i))"
      using f2_hash_pow_exp x_le_p 
      by (simp add:h_def r_def M_def[symmetric] del:f2_hash.simps)
    also have "... = exp_h_prod x"
      by (simp add:exp_h_prod_def)
    finally show "expectation (h_prod x) = exp_h_prod x" by simp
  qed

  have "\<And>x y. kernel_of x = kernel_of y \<Longrightarrow> exp_h_prod x = exp_h_prod y" 
  proof -
    fix x y :: "nat list"
    assume a:"kernel_of x = kernel_of y"
    then obtain f where b:"bij_betw f (set x) (set y)" and c:"\<And>z. z \<in> set x \<Longrightarrow> count_list x z = count_list y (f z)"
      using kernel_of_eq_imp_bij by blast
    have "exp_h_prod x = prod ( (\<lambda>i. r(count_list y i)) \<circ> f) (set x)"
      by (simp add:exp_h_prod_def c)
    also have "... = (\<Prod>i \<in> f ` (set x). r(count_list y i))"
      by (metis b bij_betw_def prod.reindex)
    also have "... = exp_h_prod y"
      unfolding exp_h_prod_def
      by (rule prod.cong, metis b bij_betw_def) simp
    finally show "exp_h_prod x = exp_h_prod y" by simp
  qed

  hence exp_h_prod_cong: "\<And>p x. of_bool (kernel_of x = kernel_of p) * exp_h_prod p = 
    of_bool (kernel_of x = kernel_of p) * exp_h_prod x" 
    by (metis (full_types) of_bool_eq_0_iff vector_space_over_itself.scale_zero_left)

  have c:"(\<Sum>p\<leftarrow>enum_rgfs n. of_bool (kernel_of xs = kernel_of p) * r) = r"
    if a:"length xs = n" for xs :: "nat list" and n and r :: real
  proof -
    have "(\<Sum>p\<leftarrow>enum_rgfs n. of_bool (kernel_of xs = kernel_of p) * 1) = (1::real)"
      using equiv_rels_2[OF a[symmetric]] by (simp add:equiv_rels_def comp_def) 
    thus "(\<Sum>p\<leftarrow>enum_rgfs n. of_bool (kernel_of xs = kernel_of p) * r) = (r::real)" 
      by (simp add:sum_list_mult_const)
  qed

  have "expectation sketch_rv = (\<Sum>i\<in>set as. (\<Sum>j\<in>set as. c i * c j * expectation (h_prod [i,j])))"
    by (simp add:f_eq h_prod_def power2_eq_square sum_distrib_left sum_distrib_right Bochner_Integration.integral_sum algebra_simps)
  also have "... = (\<Sum>i\<in>set as. (\<Sum>j\<in>set as. c i * c j * exp_h_prod [i,j]))"
    by (simp add:exp_h_prod)
  also have "... = (\<Sum>i \<in> set as. (\<Sum>j \<in> set as.  
    c i * c j * (sum_list (map (\<lambda>p. of_bool (kernel_of [i,j] = kernel_of p) * exp_h_prod p) (enum_rgfs 2)))))"
    by (subst exp_h_prod_cong, simp add:c)
  also have "... = (\<Sum>i\<in>set as. c i * c i * r 2)"
    by (simp add: numeral_eq_Suc kernel_of_eq All_less_Suc exp_h_prod_elim r_one distrib_left sum.distrib sum_collapse)
  also have "... = real_of_rat (F 2 as) * ((real p)^2-1)"
    by (simp add: sum_distrib_right[symmetric] c_def F_def power2_eq_square of_rat_sum of_rat_mult r_two)
  finally show b:?B by simp

  have "expectation (\<lambda>x. (sketch_rv x)\<^sup>2) = (\<Sum>i1 \<in> set as. (\<Sum>i2 \<in> set as. (\<Sum>i3 \<in> set as. (\<Sum>i4 \<in> set as.
    c i1 * c i2 * c i3 * c i4 * expectation (h_prod [i1, i2, i3, i4])))))"
    by (simp add:f_eq h_prod_def power4_eq_xxxx sum_distrib_left sum_distrib_right Bochner_Integration.integral_sum algebra_simps)
  also have "... = (\<Sum>i1 \<in> set as. (\<Sum>i2 \<in> set as. (\<Sum>i3 \<in> set as. (\<Sum>i4 \<in> set as. 
    c i1 * c i2 * c i3 * c i4 * exp_h_prod [i1,i2,i3,i4]))))"
    by (simp add:exp_h_prod)
  also have "... = (\<Sum>i1 \<in> set as. (\<Sum>i2 \<in> set as. (\<Sum>i3 \<in> set as. (\<Sum>i4 \<in> set as. 
    c i1 * c i2 * c i3 * c i4 * 
    (sum_list (map (\<lambda>p. of_bool (kernel_of [i1,i2,i3,i4] = kernel_of p) * exp_h_prod p) (enum_rgfs 4)))))))"
    by (subst exp_h_prod_cong, simp add:c)
  also have "... = 
    3 * (\<Sum>i \<in> set as. (\<Sum>j \<in> set as. c i^2 * c j^2 * r 2 * r 2)) + ((\<Sum> i \<in> set as. c i^4 * r 4) - 3 *  (\<Sum> i \<in> set as. c i ^ 4 * r 2 * r 2))"
    apply (simp add: numeral_eq_Suc exp_h_prod_elim r_one) (* large intermediate terms *)
    apply (simp add: kernel_of_eq All_less_Suc numeral_eq_Suc distrib_left sum.distrib sum_collapse neq_commute of_bool_not_iff)
    apply (simp add: algebra_simps sum_subtractf sum_collapse)
    apply (simp add: sum_distrib_left algebra_simps)
    done
  also have "... = 3 * (\<Sum>i \<in> set as. c i^2 * r 2)^2 + (\<Sum> i \<in> set as. c i ^ 4 * (r 4 - 3 * r 2 * r 2))"
    by (simp add:power2_eq_square sum_distrib_left algebra_simps sum_subtractf)
  also have "... = 3 * (\<Sum>i \<in> set as. c i^2)^2 * (r 2)^2 + (\<Sum>i \<in> set as. c i ^ 4 * (r 4 - 3 * r 2 * r 2))"
    by (simp add:power_mult_distrib sum_distrib_right[symmetric])
  also have "... \<le> 3 * (\<Sum>i \<in> set as. c i^2)^2 * (r 2)^2 + (\<Sum>i \<in> set as. c i ^ 4 * 0)"
    using r_four_est  
    by (auto intro!: sum_nonpos simp add:mult_nonneg_nonpos)
  also have "... = 3 * (real_of_rat (F 2 as)^2) * ((real p)\<^sup>2-1)\<^sup>2" 
    by (simp add:c_def r_two F_def of_rat_sum of_rat_power)
  finally have "expectation (\<lambda>x. (sketch_rv x)\<^sup>2) \<le> 3 * (real_of_rat (F 2 as)^2) * ((real p)\<^sup>2-1)\<^sup>2"
    by simp
  
  thus "variance sketch_rv \<le> 2*(real_of_rat (F 2 as)^2) * ((real p)\<^sup>2-1)\<^sup>2"
     by (simp add: variance_eq, simp add:power_mult_distrib b)
qed

lemma space_omega_1 [simp]: "Sigma_Algebra.space \<Omega>\<^sub>p = UNIV"
    by (simp add:\<Omega>\<^sub>p_def)

interpretation \<Omega>: prob_space "\<Omega>\<^sub>p"
  by (simp add:\<Omega>\<^sub>p_def prob_space_measure_pmf)

lemma integrable_\<Omega>:
  fixes f :: "((nat \<times> nat) \<Rightarrow> (nat list)) \<Rightarrow> real"
  shows "integrable \<Omega>\<^sub>p f"
  unfolding \<Omega>\<^sub>p_def \<Omega>_def
  by (rule integrable_measure_pmf_finite, auto intro:finite_PiE simp:set_prod_pmf)

lemma sketch_rv_exp:
  assumes "i\<^sub>2 < s\<^sub>2"
  assumes "i\<^sub>1 \<in> {0..<s\<^sub>1}"
  shows "\<Omega>.expectation (\<lambda>\<omega>. sketch_rv (\<omega> (i\<^sub>1, i\<^sub>2))) = real_of_rat (F 2 as) * ((real p)\<^sup>2 - 1)"
proof -
  have "\<Omega>.expectation (\<lambda>\<omega>.  (sketch_rv (\<omega> (i\<^sub>1, i\<^sub>2))) :: real) = expectation sketch_rv"
    using integrable_\<Omega> integrable_M assms
    unfolding \<Omega>_def \<Omega>\<^sub>p_def M_def
    by (subst expectation_Pi_pmf_slice, auto)
  also have "... = (real_of_rat (F 2 as)) * ((real p)\<^sup>2 - 1)"
    using exp_sketch_rv by simp
  finally show ?thesis by simp
qed

lemma sketch_rv_var:
  assumes "i\<^sub>2 < s\<^sub>2"
  assumes "i\<^sub>1 \<in> {0..<s\<^sub>1}"
  shows "\<Omega>.variance (\<lambda>\<omega>. sketch_rv (\<omega> (i\<^sub>1, i\<^sub>2))) \<le> 2 * (real_of_rat (F 2 as))\<^sup>2 * ((real p)\<^sup>2 - 1)\<^sup>2"
proof -
  have "\<Omega>.variance (\<lambda>\<omega>. (sketch_rv (\<omega> (i\<^sub>1, i\<^sub>2)) :: real)) = variance sketch_rv"
    using integrable_\<Omega> integrable_M assms
    unfolding \<Omega>_def \<Omega>\<^sub>p_def M_def
    by (subst variance_prod_pmf_slice, auto)
  also have "... \<le>  2 * (real_of_rat (F 2 as))\<^sup>2 * ((real p)\<^sup>2 - 1)\<^sup>2"
    using var_sketch_rv by simp
  finally show ?thesis by simp
qed

lemma mean_rv_exp:
  assumes "i < s\<^sub>2"
  shows "\<Omega>.expectation (\<lambda>\<omega>. mean_rv \<omega> i) = real_of_rat (F 2 as)"
proof -
  have a:"(real p)\<^sup>2 > 1" using p_gt_1 by simp

  have "\<Omega>.expectation (\<lambda>\<omega>. mean_rv \<omega> i) = (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. \<Omega>.expectation (\<lambda>\<omega>. sketch_rv (\<omega> (i\<^sub>1, i)))) / (((real p)\<^sup>2 - 1) * real s\<^sub>1)"
    using assms integrable_\<Omega> by (simp add:mean_rv_def)
  also have "... = (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. real_of_rat (F 2 as) * ((real p)\<^sup>2 - 1)) / (((real p)\<^sup>2 - 1) * real s\<^sub>1)" 
    using sketch_rv_exp[OF assms] by simp
  also have "... = real_of_rat (F 2 as)"
    using s1_gt_0 a by simp
  finally show ?thesis by simp
qed

lemma mean_rv_var:
  assumes "i < s\<^sub>2"
  shows "\<Omega>.variance (\<lambda>\<omega>. mean_rv \<omega> i) \<le> (real_of_rat (\<delta> * F 2 as))\<^sup>2 / 3"
proof -
  have a: "\<Omega>.indep_vars (\<lambda>_. borel) (\<lambda>i\<^sub>1 x. sketch_rv (x (i\<^sub>1, i))) {0..<s\<^sub>1}"
    using assms
    unfolding \<Omega>\<^sub>p_def \<Omega>_def
    by (intro indep_vars_restrict_intro'[where f="fst"])
     (auto simp add: restrict_dfl_def case_prod_beta lessThan_atLeast0)

  have p_sq_ne_1: "(real p)^2 \<noteq> 1" 
    by (metis p_gt_1 less_numeral_extra(4) of_nat_power one_less_power pos2 semiring_char_0_class.of_nat_eq_1_iff)

  have s1_bound: " 6 / (real_of_rat \<delta>)\<^sup>2 \<le> real s\<^sub>1"
    unfolding s\<^sub>1_def
    by  (metis (mono_tags, opaque_lifting) of_rat_ceiling of_rat_divide of_rat_numeral_eq of_rat_power real_nat_ceiling_ge)

  have "\<Omega>.variance (\<lambda>\<omega>. mean_rv \<omega> i) = \<Omega>.variance (\<lambda>\<omega>. \<Sum>i\<^sub>1 = 0..<s\<^sub>1. sketch_rv (\<omega> (i\<^sub>1, i))) / (((real p)\<^sup>2 - 1) * real s\<^sub>1)\<^sup>2"
    unfolding mean_rv_def by (subst \<Omega>.variance_divide[OF integrable_\<Omega>], simp)
  also have "... = (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. \<Omega>.variance (\<lambda>\<omega>. sketch_rv (\<omega> (i\<^sub>1, i)))) / (((real p)\<^sup>2 - 1) * real s\<^sub>1)\<^sup>2"
    by (subst \<Omega>.var_sum_all_indep[OF _ _ integrable_\<Omega> a]) (auto simp: \<Omega>_def \<Omega>\<^sub>p_def)
  also have "... \<le>  (\<Sum>i\<^sub>1 = 0..<s\<^sub>1. 2*(real_of_rat (F 2 as)^2) * ((real p)\<^sup>2-1)\<^sup>2)  / (((real p)\<^sup>2 - 1) * real s\<^sub>1)\<^sup>2"
    by (rule divide_right_mono, rule sum_mono[OF sketch_rv_var[OF assms]], auto)
  also have "... = 2 * (real_of_rat (F 2 as)^2) / real s\<^sub>1"
    using p_sq_ne_1 s1_gt_0 by (subst frac_eq_eq, auto simp:power2_eq_square)
  also have "... \<le> 2 * (real_of_rat (F 2 as)^2) / (6 / (real_of_rat \<delta>)\<^sup>2)"
    using  s1_gt_0 \<delta>_range by (intro divide_left_mono mult_pos_pos s1_bound) auto
  also have "... = (real_of_rat (\<delta> * F 2 as))\<^sup>2 / 3"
    by (simp add:of_rat_mult algebra_simps)
  finally show ?thesis by simp
qed

lemma mean_rv_bounds:
  assumes "i < s\<^sub>2"
  shows "\<Omega>.prob {\<omega>. real_of_rat \<delta> * real_of_rat (F 2 as) < \<bar>mean_rv \<omega> i - real_of_rat (F 2 as)\<bar>} \<le> 1/3"
proof (cases "as = []")
  case True
  then show ?thesis
    using assms by (subst mean_rv_def, subst sketch_rv_def, simp add:F_def)
next
  case False
  hence "F 2 as > 0" using F_gr_0 by auto

  hence a: "0 < real_of_rat (\<delta> * F 2 as)"
    using \<delta>_range by simp
  have [simp]: "(\<lambda>\<omega>. mean_rv \<omega> i) \<in> borel_measurable \<Omega>\<^sub>p"
    by (simp add:\<Omega>_def \<Omega>\<^sub>p_def)
  have "\<Omega>.prob {\<omega>. real_of_rat \<delta> * real_of_rat (F 2 as) < \<bar>mean_rv \<omega> i - real_of_rat (F 2 as)\<bar>} \<le> 
      \<Omega>.prob {\<omega>. real_of_rat (\<delta> * F 2 as) \<le> \<bar>mean_rv \<omega> i - real_of_rat (F 2 as)\<bar>}"
    by (rule \<Omega>.pmf_mono[OF \<Omega>\<^sub>p_def], simp add:of_rat_mult)
  also have "... \<le>  \<Omega>.variance (\<lambda>\<omega>. mean_rv \<omega> i) / (real_of_rat (\<delta> * F 2 as))\<^sup>2"
    using \<Omega>.Chebyshev_inequality[where a="real_of_rat (\<delta> * F 2 as)" and f="\<lambda>\<omega>. mean_rv \<omega> i",simplified] 
      a prob_space_measure_pmf[where p="\<Omega>"] mean_rv_exp[OF assms] integrable_\<Omega> by simp
  also have "... \<le> ((real_of_rat (\<delta> * F 2 as))\<^sup>2/3) / (real_of_rat (\<delta> * F 2 as))\<^sup>2"
    by (rule divide_right_mono, rule mean_rv_var[OF assms], simp)
  also  have "... = 1/3" using a by force
  finally show ?thesis by blast
qed

lemma f2_alg_correct':
   "\<P>(\<omega> in measure_pmf result. \<bar>\<omega> - F 2 as\<bar> \<le> \<delta> * F 2 as) \<ge> 1-of_rat \<epsilon>"
proof -
  have a: "\<Omega>.indep_vars (\<lambda>_. borel) (\<lambda>i \<omega>. mean_rv \<omega> i) {0..<s\<^sub>2}" 
    using s1_gt_0 unfolding \<Omega>\<^sub>p_def \<Omega>_def
    by (intro indep_vars_restrict_intro'[where f="snd"])
      (auto simp: \<Omega>\<^sub>p_def \<Omega>_def mean_rv_def restrict_dfl_def)

  have b: "- 18 * ln (real_of_rat \<epsilon>) \<le> real s\<^sub>2" 
    unfolding  s\<^sub>2_def using of_nat_ceiling by auto

  have "1 - of_rat \<epsilon> \<le> \<Omega>.prob {\<omega>.  \<bar>median s\<^sub>2 (mean_rv \<omega>) -  real_of_rat (F 2 as) \<bar> \<le> of_rat \<delta> * of_rat (F 2 as)}"
    using \<epsilon>_range \<Omega>.median_bound_2[OF _ a b, where \<delta>="real_of_rat \<delta> * real_of_rat (F 2 as)"
        and \<mu>="real_of_rat (F 2 as)"] mean_rv_bounds
    by simp
  also have "... = \<Omega>.prob {\<omega>.  \<bar>real_of_rat (result_rv \<omega>) - of_rat (F 2 as) \<bar> \<le> of_rat \<delta> * of_rat (F 2 as)}"
    by (simp add:result_rv_def median_restrict lessThan_atLeast0 median_rat[OF s2_gt_0]
         mean_rv_def sketch_rv_def of_rat_divide of_rat_sum of_rat_mult of_rat_diff of_rat_power)
  also have "... = \<Omega>.prob {\<omega>. \<bar>result_rv \<omega> - F 2 as\<bar> \<le> \<delta> * F 2 as} " 
    by (simp add:of_rat_less_eq of_rat_mult[symmetric]  of_rat_diff[symmetric] set_eq_iff)
  finally have "\<Omega>.prob {y. \<bar>result_rv y - F 2 as\<bar> \<le> \<delta> * F 2 as} \<ge> 1-of_rat \<epsilon> " by simp
  thus ?thesis by (simp add: distr \<Omega>\<^sub>p_def)
qed

lemma f2_exact_space_usage':
   "AE \<omega> in sketch . bit_count (encode_f2_state \<omega>) \<le> f2_space_usage (n, length as, \<epsilon>, \<delta>)"
proof -
  have "p \<le> 2 * max n 3 + 2"
    by (subst p_def, rule prime_above_upper_bound)
  also have "... \<le> 2 * n + 8"
    by (cases "n \<le> 2", simp_all)
  finally have p_bound: "p \<le> 2 * n + 8" 
    by simp
  have "bit_count (N\<^sub>e p) \<le> ereal (2 * log 2 (real p + 1) + 1)"
    by (rule exp_golomb_bit_count)
  also have "... \<le> ereal (2 * log 2 (2 * real n + 9) + 1)"
    using p_bound by simp
  finally have p_bit_count: "bit_count (N\<^sub>e p) \<le> ereal (2 * log 2 (2 * real n + 9) + 1)"
    by simp

  have a: "bit_count (encode_f2_state (s\<^sub>1, s\<^sub>2, p, y, \<lambda>i\<in>{..<s\<^sub>1} \<times> {..<s\<^sub>2}. 
      sum_list (map (f2_hash p (y i)) as))) \<le> ereal (f2_space_usage (n, length as, \<epsilon>, \<delta>))"
    if a:"y\<in>{..<s\<^sub>1} \<times> {..<s\<^sub>2} \<rightarrow>\<^sub>E bounded_degree_polynomials (mod_ring p) 4" for y
  proof -
    have "y \<in> extensional ({..<s\<^sub>1} \<times> {..<s\<^sub>2})" using a PiE_iff by blast
    hence y_ext: "y \<in> extensional (set (List.product [0..<s\<^sub>1] [0..<s\<^sub>2]))"
      by (simp add:lessThan_atLeast0)

    have h_bit_count_aux: "bit_count (P\<^sub>e p 4 (y x)) \<le> ereal (4 + 4 * log 2 (8 + 2 * real n))"
      if b:"x \<in>  set (List.product [0..<s\<^sub>1] [0..<s\<^sub>2])" for x
    proof -
      have "y x \<in> bounded_degree_polynomials (mod_ring p) 4"
        using b a by force
      hence "bit_count (P\<^sub>e p 4 (y x)) \<le> ereal (real 4 * (log 2 (real p) + 1))"
        by (rule bounded_degree_polynomial_bit_count[OF p_gt_1] )
      also have "... \<le> ereal (real 4 * (log 2 (8 + 2 * real n) + 1) )"
        using p_gt_0 p_bound by simp
      also have "... \<le> ereal (4 + 4 * log 2 (8 + 2 * real n))"
        by simp
      finally show ?thesis
        by blast
    qed

    have h_bit_count: 
      "bit_count ((List.product [0..<s\<^sub>1] [0..<s\<^sub>2] \<rightarrow>\<^sub>e P\<^sub>e p 4) y) \<le> ereal (real s\<^sub>1 * real s\<^sub>2 * (4 + 4 * log 2 (8 + 2 * real n)))"
      using fun_bit_count_est[where e="P\<^sub>e p 4", OF y_ext h_bit_count_aux]
      by simp

    have sketch_bit_count_aux:
      "bit_count (I\<^sub>e (sum_list (map (f2_hash p (y x)) as))) \<le> ereal (1 + 2 * log 2 (real (length as) * (18 + 4 * real n) + 1))" (is "?lhs \<le> ?rhs")
      if " x \<in> {0..<s\<^sub>1} \<times> {0..<s\<^sub>2}" for x
    proof -
      have "\<bar>sum_list (map (f2_hash p (y x)) as)\<bar> \<le> sum_list (map (abs \<circ> (f2_hash p (y x))) as)" 
        by (subst map_map[symmetric])  (rule sum_list_abs)
      also have "... \<le>  sum_list (map (\<lambda>_. (int p+1)) as)"
        by (rule sum_list_mono) (simp add:p_gt_0) 
      also have "... = int (length as) * (int p+1)"
        by (simp add: sum_list_triv)
      also have "... \<le> int (length as) * (9+2*(int n))"
        using p_bound by (intro mult_mono, auto)
      finally  have "\<bar>sum_list (map (f2_hash p (y x)) as)\<bar> \<le> int (length as) * (9 + 2 * int n)" by simp
      hence "?lhs \<le> ereal (2 * log 2 (real_of_int (2* (int (length as) * (9 + 2 * int n)) + 1)) + 1)"
        by (rule int_bit_count_est)
      also have "... = ?rhs" by (simp add:algebra_simps)
      finally show "?thesis" by simp
    qed

    have 
      "bit_count ((List.product [0..<s\<^sub>1] [0..<s\<^sub>2] \<rightarrow>\<^sub>e I\<^sub>e) (\<lambda>i\<in>{..<s\<^sub>1} \<times> {..<s\<^sub>2}. sum_list (map (f2_hash p (y i)) as)))
      \<le> ereal (real (length (List.product [0..<s\<^sub>1] [0..<s\<^sub>2]))) * (ereal (1 + 2 * log 2 (real (length as) * (18 + 4 * real n) + 1)))"
      by (intro fun_bit_count_est)  
       (simp_all add:extensional_def lessThan_atLeast0 sketch_bit_count_aux del:f2_hash.simps)
    also have "... = ereal (real s\<^sub>1 * real s\<^sub>2 * (1 + 2 * log 2 (real (length as) * (18 + 4 * real n) + 1)))"
      by simp
    finally have sketch_bit_count: 
       "bit_count ((List.product [0..<s\<^sub>1] [0..<s\<^sub>2] \<rightarrow>\<^sub>e I\<^sub>e) (\<lambda>i\<in>{..<s\<^sub>1} \<times> {..<s\<^sub>2}. sum_list (map (f2_hash p (y i)) as))) \<le>
      ereal (real s\<^sub>1 * real s\<^sub>2 * (1 + 2 * log 2 (real (length as) * (18 + 4 * real n) + 1)))" by simp

    have "bit_count (encode_f2_state (s\<^sub>1, s\<^sub>2, p, y, \<lambda>i\<in>{..<s\<^sub>1} \<times> {..<s\<^sub>2}. sum_list (map (f2_hash p (y i)) as))) \<le> 
      bit_count (N\<^sub>e s\<^sub>1) + bit_count (N\<^sub>e s\<^sub>2) +bit_count (N\<^sub>e p) +
      bit_count ((List.product [0..<s\<^sub>1] [0..<s\<^sub>2] \<rightarrow>\<^sub>e P\<^sub>e p 4) y) +
      bit_count ((List.product [0..<s\<^sub>1] [0..<s\<^sub>2] \<rightarrow>\<^sub>e I\<^sub>e) (\<lambda>i\<in>{..<s\<^sub>1} \<times> {..<s\<^sub>2}. sum_list (map (f2_hash p (y i)) as)))"   
      by (simp add:Let_def s\<^sub>1_def s\<^sub>2_def encode_f2_state_def dependent_bit_count add.assoc)
    also have "... \<le> ereal (2 * log 2 (real s\<^sub>1 + 1) + 1) + ereal (2 * log 2 (real s\<^sub>2 + 1) + 1) + ereal (2 * log 2 (2 * real n + 9) + 1) + 
      (ereal (real s\<^sub>1 * real s\<^sub>2) * (4 + 4 * log 2 (8 + 2 * real n))) + 
      (ereal (real s\<^sub>1 * real s\<^sub>2) * (1 + 2 * log 2 (real (length as) * (18 + 4 * real n) + 1) ))"
      by (intro add_mono exp_golomb_bit_count p_bit_count, auto intro: h_bit_count sketch_bit_count)
    also have "... = ereal (f2_space_usage (n, length as, \<epsilon>, \<delta>))"
      by (simp add:distrib_left add.commute s\<^sub>1_def[symmetric] s\<^sub>2_def[symmetric] Let_def)
    finally show "bit_count (encode_f2_state (s\<^sub>1, s\<^sub>2, p, y, \<lambda>i\<in>{..<s\<^sub>1} \<times> {..<s\<^sub>2}. sum_list (map (f2_hash p (y i)) as))) \<le>  
      ereal (f2_space_usage (n, length as, \<epsilon>, \<delta>))" 
      by simp
  qed

  have "set_pmf \<Omega> = {..<s\<^sub>1} \<times> {..<s\<^sub>2} \<rightarrow>\<^sub>E bounded_degree_polynomials (mod_ring p) 4"
    by (simp add: \<Omega>_def set_prod_pmf) (simp add: space_def)
  thus ?thesis
    by (simp  add:mean_rv_alg_sketch AE_measure_pmf_iff del:f2_space_usage.simps, metis a)
qed

end


text \<open>Main results of this section:\<close>

theorem f2_alg_correct:
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "\<delta> > 0"
  assumes "set as \<subseteq> {..<n}"
  defines "\<Omega> \<equiv> fold (\<lambda>a state. state \<bind> f2_update a) as (f2_init \<delta> \<epsilon> n) \<bind> f2_result"
  shows "\<P>(\<omega> in measure_pmf \<Omega>. \<bar>\<omega> - F 2 as\<bar> \<le> \<delta> * F 2 as) \<ge> 1-of_rat \<epsilon>"
  using f2_alg_correct'[OF assms(1,2,3)] \<Omega>_def by auto

theorem f2_exact_space_usage:
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "\<delta> > 0"
  assumes "set as \<subseteq> {..<n}"
  defines "M \<equiv> fold (\<lambda>a state. state \<bind> f2_update a) as (f2_init \<delta> \<epsilon> n)"
  shows "AE \<omega> in M. bit_count (encode_f2_state \<omega>) \<le> f2_space_usage (n, length as, \<epsilon>, \<delta>)"
  using f2_exact_space_usage'[OF assms(1,2,3)]
  by (subst (asm) sketch_def[OF assms(1,2,3)], subst M_def, simp)

theorem f2_asymptotic_space_complexity:
  "f2_space_usage \<in> O[at_top \<times>\<^sub>F at_top \<times>\<^sub>F at_right 0 \<times>\<^sub>F at_right 0](\<lambda> (n, m, \<epsilon>, \<delta>). 
  (ln (1 / of_rat \<epsilon>)) / (of_rat \<delta>)\<^sup>2 * (ln (real n) + ln (real m)))"
  (is "_ \<in> O[?F](?rhs)")
proof -
  define n_of :: "nat \<times> nat \<times> rat \<times> rat \<Rightarrow> nat" where "n_of = (\<lambda>(n, m, \<epsilon>, \<delta>). n)"
  define m_of :: "nat \<times> nat \<times> rat \<times> rat \<Rightarrow> nat" where "m_of = (\<lambda>(n, m, \<epsilon>, \<delta>). m)"
  define \<epsilon>_of :: "nat \<times> nat \<times> rat \<times> rat \<Rightarrow> rat" where "\<epsilon>_of = (\<lambda>(n, m, \<epsilon>, \<delta>). \<epsilon>)"
  define \<delta>_of :: "nat \<times> nat \<times> rat \<times> rat \<Rightarrow> rat" where "\<delta>_of = (\<lambda>(n, m, \<epsilon>, \<delta>). \<delta>)"

  define g where "g = (\<lambda>x. (1/ (of_rat (\<delta>_of x))\<^sup>2) * (ln (1 / of_rat (\<epsilon>_of x))) * (ln (real (n_of x)) + ln (real (m_of x))))"

  have evt: "(\<And>x. 
    0 < real_of_rat (\<delta>_of x) \<and> 0 < real_of_rat (\<epsilon>_of x) \<and> 
    1/real_of_rat (\<delta>_of x) \<ge> \<delta> \<and> 1/real_of_rat (\<epsilon>_of x) \<ge> \<epsilon> \<and>
    real (n_of x) \<ge> n \<and> real (m_of x) \<ge> m\<Longrightarrow> P x) 
    \<Longrightarrow> eventually P ?F"  (is "(\<And>x. ?prem x \<Longrightarrow> _) \<Longrightarrow> _")
    for \<delta> \<epsilon> n m P
    apply (rule eventually_mono[where P="?prem" and Q="P"])
    apply (simp add:\<epsilon>_of_def case_prod_beta' \<delta>_of_def n_of_def m_of_def)
     apply (intro eventually_conj eventually_prod1' eventually_prod2' 
        sequentially_inf eventually_at_right_less inv_at_right_0_inf)
    by (auto simp add:prod_filter_eq_bot)

  have unit_1: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. 1 / (real_of_rat (\<delta>_of x))\<^sup>2)"
    using one_le_power
    by (intro landau_o.big_mono evt[where \<delta>="1"], auto simp add:power_one_over[symmetric])

  have unit_2: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x)))"
    by (intro landau_o.big_mono  evt[where \<epsilon>="exp 1"])
     (auto intro!:iffD2[OF ln_ge_iff] simp add:abs_ge_iff)

  have unit_3: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. real (n_of x))"
    by (intro landau_o.big_mono evt, auto)

  have unit_4: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. real (m_of x))"
    by (intro landau_o.big_mono evt, auto)

  have unit_5: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. ln (real (n_of x)))"
    by (auto intro!: landau_o.big_mono evt[where n="exp 1"])
      (metis abs_ge_self linorder_not_le ln_ge_iff not_exp_le_zero order.trans)

  have unit_6: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. ln (real (n_of x)) + ln (real (m_of x)))"
    by (intro landau_sum_1 evt unit_5 iffD2[OF ln_ge_iff], auto)

  have unit_7: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. 1 / real_of_rat (\<epsilon>_of x))"
    by (intro landau_o.big_mono  evt[where \<epsilon>="1"], auto)
 
  have unit_8: "(\<lambda>_. 1) \<in> O[?F](g)" 
    unfolding g_def by (intro landau_o.big_mult_1 unit_1 unit_2 unit_6)

  have unit_9: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. real (n_of x) * real (m_of x))"
    by (intro landau_o.big_mult_1 unit_3 unit_4)

  have " (\<lambda>x. 6 * (1 / (real_of_rat (\<delta>_of x))\<^sup>2)) \<in> O[?F](\<lambda>x. 1 / (real_of_rat (\<delta>_of x))\<^sup>2)"
    by (subst landau_o.big.cmult_in_iff, simp_all)
  hence l1: "(\<lambda>x. real (nat \<lceil>6 / (\<delta>_of x)\<^sup>2\<rceil>)) \<in> O[?F](\<lambda>x. 1 / (real_of_rat (\<delta>_of x))\<^sup>2)"
    by (intro landau_real_nat  landau_rat_ceil[OF unit_1]) (simp_all add:of_rat_divide of_rat_power)

  have "(\<lambda>x. - ( ln (real_of_rat (\<epsilon>_of x)))) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x)))"
    by (intro landau_o.big_mono evt) (subst ln_div, auto)
  hence l2: "(\<lambda>x. real (nat \<lceil>- (18 * ln (real_of_rat (\<epsilon>_of x)))\<rceil>)) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x)))"
    by (intro landau_real_nat landau_ceil[OF unit_2], simp)

  have l3_aux: " (\<lambda>x. real (m_of x) * (18 + 4 * real (n_of x)) + 1) \<in> O[?F](\<lambda>x. real (n_of x) * real (m_of x))"
    by (rule sum_in_bigo[OF _unit_9], subst mult.commute)
      (intro landau_o.mult sum_in_bigo, auto simp:unit_3)

  have "(\<lambda>x. ln (real (m_of x) * (18 + 4 * real (n_of x)) + 1)) \<in> O[?F](\<lambda>x. ln (real (n_of x) * real (m_of x)))"
     apply (rule landau_ln_2[where a="2"], simp, simp)
      apply (rule evt[where m="2" and n="1"])
     apply (metis dual_order.trans mult_left_mono mult_of_nat_commute of_nat_0_le_iff verit_prod_simplify(1))
    using l3_aux by simp
  also have "(\<lambda>x. ln (real (n_of x) * real (m_of x))) \<in> O[?F](\<lambda>x. ln (real (n_of x)) + ln(real (m_of x)))"
    by (intro landau_o.big_mono evt[where m="1" and n="1"], auto simp add:ln_mult)
  finally have l3: "(\<lambda>x. ln (real (m_of x) * (18 + 4 * real (n_of x)) + 1)) \<in> O[?F](\<lambda>x. ln (real (n_of x)) + ln (real (m_of x)))"
    using  landau_o.big_trans by simp

  have l4: "(\<lambda>x. ln (8 + 2 * real (n_of x))) \<in> O[?F](\<lambda>x. ln (real (n_of x)) + ln (real (m_of x)))"
    by (intro landau_sum_1  evt[where n="2"] landau_ln_2[where a="2"] iffD2[OF ln_ge_iff])
     (auto intro!: sum_in_bigo simp add:unit_3)

  have l5: "(\<lambda>x. ln (9 + 2 * real (n_of x))) \<in> O[?F](\<lambda>x. ln (real (n_of x)) + ln (real (m_of x)))"
    by (intro landau_sum_1  evt[where n="2"] landau_ln_2[where a="2"] iffD2[OF ln_ge_iff])
     (auto intro!: sum_in_bigo simp add:unit_3)

  have l6: "(\<lambda>x. ln (real (nat \<lceil>6 / (\<delta>_of x)\<^sup>2\<rceil>) + 1)) \<in> O[?F](g)"
    unfolding g_def
    by (intro landau_o.big_mult_1 landau_ln_3 sum_in_bigo unit_6 unit_2 l1 unit_1, simp)

  have l7: "(\<lambda>x. ln (9 + 2 * real (n_of x))) \<in> O[?F](g)"
    unfolding g_def
    by (intro landau_o.big_mult_1' unit_1 unit_2 l5)

  have l8: "(\<lambda>x. ln (real (nat \<lceil>- (18 * ln (real_of_rat (\<epsilon>_of x)))\<rceil>) + 1) ) \<in> O[?F](g)"
    unfolding g_def
    by (intro landau_o.big_mult_1 unit_6 landau_o.big_mult_1' unit_1 landau_ln_3 sum_in_bigo l2 unit_2) simp

  have l9: "(\<lambda>x. 5 + 4 * ln (8 + 2 * real (n_of x)) / ln 2 + 2 * ln (real (m_of x) * (18 + 4 * real (n_of x)) + 1) / ln 2)
      \<in> O[?F](\<lambda>x. ln (real (n_of x)) + ln (real (m_of x)))"
    by (intro sum_in_bigo, auto simp: l3 l4 unit_6)

  have l10: "(\<lambda>x. real (nat \<lceil>6 / (\<delta>_of x)\<^sup>2\<rceil>) * real (nat \<lceil>- (18 * ln (real_of_rat (\<epsilon>_of x)))\<rceil>) * 
      (5 + 4 * ln (8 + 2 * real (n_of x)) / ln 2 + 2 * ln(real (m_of x) * (18 + 4 * real (n_of x)) + 1) / ln 2))
      \<in> O[?F](g)"
    unfolding g_def by (intro landau_o.mult, auto simp: l1 l2 l9)

  have "f2_space_usage = (\<lambda>x. f2_space_usage (n_of x, m_of x, \<epsilon>_of x, \<delta>_of x))"
    by (simp add:case_prod_beta' n_of_def \<epsilon>_of_def \<delta>_of_def m_of_def)
  also have "... \<in> O[?F](g)"
    by (auto intro!:sum_in_bigo simp:Let_def log_def l6 l7 l8 l10 unit_8)
  also have "... = O[?F](?rhs)"
    by (simp add:case_prod_beta' g_def n_of_def \<epsilon>_of_def \<delta>_of_def m_of_def)
  finally show ?thesis by simp
qed

end
