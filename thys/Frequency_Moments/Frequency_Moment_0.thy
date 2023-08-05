section \<open>Frequency Moment $0$\label{sec:f0}\<close>

theory Frequency_Moment_0
  imports
    Frequency_Moments_Preliminary_Results
    Median_Method.Median 
    K_Smallest 
    Universal_Hash_Families.Carter_Wegman_Hash_Family
    Frequency_Moments
    Landau_Ext 
    Product_PMF_Ext
    Universal_Hash_Families.Universal_Hash_Families_More_Finite_Fields
begin

text \<open>This section contains a formalization of a new algorithm for the zero-th frequency moment
inspired by ideas described in \<^cite>\<open>"baryossef2002"\<close>.
It is a KMV-type ($k$-minimum value) algorithm with a rounding method and matches the space complexity 
of the best algorithm described in \<^cite>\<open>"baryossef2002"\<close>.

In addition to the Isabelle proof here, there is also an informal hand-written proof in
Appendix~\ref{sec:f0_proof}.\<close>

type_synonym f0_state = "nat \<times> nat \<times> nat \<times> nat \<times> (nat \<Rightarrow> nat list) \<times> (nat \<Rightarrow> float set)"

definition hash where "hash p = ring.hash (mod_ring p)"

fun f0_init :: "rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> f0_state pmf" where
  "f0_init \<delta> \<epsilon> n =
    do {
      let s = nat \<lceil>-18 * ln (real_of_rat \<epsilon>)\<rceil>;
      let t = nat \<lceil>80 / (real_of_rat \<delta>)\<^sup>2\<rceil>;
      let p = prime_above (max n 19);
      let r = nat (4 * \<lceil>log 2 (1 / real_of_rat \<delta>)\<rceil> + 23); 
      h \<leftarrow> prod_pmf {..<s} (\<lambda>_. pmf_of_set (bounded_degree_polynomials (mod_ring p) 2));
      return_pmf (s, t, p, r, h, (\<lambda>_ \<in> {0..<s}. {}))
    }"

fun f0_update :: "nat \<Rightarrow> f0_state \<Rightarrow> f0_state pmf" where
  "f0_update x (s, t, p, r, h, sketch) = 
    return_pmf (s, t, p, r, h, \<lambda>i \<in> {..<s}.
      least t (insert (float_of (truncate_down r (hash p x (h i)))) (sketch i)))"

fun f0_result :: "f0_state \<Rightarrow> rat pmf" where
  "f0_result (s, t, p, r, h, sketch) = return_pmf (median s (\<lambda>i \<in> {..<s}.
      (if card (sketch i) < t then of_nat (card (sketch i)) else
        rat_of_nat t* rat_of_nat p / rat_of_float (Max (sketch i)))
    ))"

fun f0_space_usage :: "(nat \<times> rat \<times> rat) \<Rightarrow> real" where
  "f0_space_usage (n, \<epsilon>, \<delta>) = (
    let s = nat \<lceil>-18 * ln (real_of_rat \<epsilon>)\<rceil> in 
    let r = nat (4 * \<lceil>log 2 (1 / real_of_rat \<delta>)\<rceil> + 23) in
    let t = nat \<lceil>80 / (real_of_rat \<delta>)\<^sup>2 \<rceil> in
    6 +
    2 * log 2 (real s + 1) +
    2 * log 2 (real t + 1) +
    2 * log 2 (real n + 21) +
    2 * log 2 (real r + 1) +
    real s * (5 + 2 * log 2 (21 + real n) +
    real t * (13 + 4 * r + 2 * log 2 (log 2 (real n + 13)))))"

definition encode_f0_state :: "f0_state \<Rightarrow> bool list option" where
  "encode_f0_state = 
    N\<^sub>e \<Join>\<^sub>e (\<lambda>s. 
    N\<^sub>e \<times>\<^sub>e (
    N\<^sub>e \<Join>\<^sub>e (\<lambda>p. 
    N\<^sub>e \<times>\<^sub>e ( 
    ([0..<s] \<rightarrow>\<^sub>e (P\<^sub>e p 2)) \<times>\<^sub>e
    ([0..<s] \<rightarrow>\<^sub>e (S\<^sub>e F\<^sub>e))))))"

lemma "inj_on encode_f0_state (dom encode_f0_state)"
proof -
  have "is_encoding encode_f0_state" 
    unfolding encode_f0_state_def
    by (intro dependent_encoding exp_golomb_encoding poly_encoding fun_encoding set_encoding float_encoding)
  thus ?thesis  by (rule encoding_imp_inj)
qed

context
  fixes \<epsilon> \<delta> :: rat
  fixes n :: nat
  fixes as :: "nat list"
  fixes result
  assumes \<epsilon>_range: "\<epsilon> \<in> {0<..<1}"
  assumes \<delta>_range: "\<delta> \<in> {0<..<1}"
  assumes as_range: "set as \<subseteq> {..<n}"
  defines "result \<equiv> fold (\<lambda>a state. state \<bind> f0_update a) as (f0_init \<delta> \<epsilon> n) \<bind> f0_result"
begin  

private definition t where "t = nat \<lceil>80 / (real_of_rat \<delta>)\<^sup>2\<rceil>"
private lemma t_gt_0: "t > 0" using \<delta>_range by (simp add:t_def)

private definition s where "s = nat \<lceil>-(18 * ln (real_of_rat \<epsilon>))\<rceil>"
private lemma s_gt_0: "s > 0" using \<epsilon>_range by (simp add:s_def)

private definition p where "p = prime_above (max n 19)"

private lemma p_prime:"Factorial_Ring.prime p"
  using p_def prime_above_prime by presburger

private lemma p_ge_18: "p \<ge> 18"
proof -
  have "p \<ge> 19" 
    by (metis p_def prime_above_lower_bound max.bounded_iff)
  thus ?thesis by simp
qed

private lemma p_gt_0: "p > 0" using p_ge_18 by simp
private lemma p_gt_1: "p > 1" using p_ge_18 by simp

private lemma n_le_p: "n \<le> p"
proof -
  have "n \<le> max n 19" by simp
  also have "... \<le> p"
    unfolding p_def by (rule prime_above_lower_bound)
  finally show ?thesis by simp
qed

private lemma p_le_n: "p \<le> 2*n + 40"
proof -
  have "p \<le> 2 * (max n 19) + 2"
    by (subst p_def, rule prime_above_upper_bound)
  also have "... \<le> 2 * n + 40"
    by (cases "n \<ge> 19", auto)
  finally show ?thesis by simp
qed

private lemma as_lt_p: "\<And>x. x \<in> set as \<Longrightarrow> x < p" 
  using as_range atLeastLessThan_iff
  by (intro order_less_le_trans[OF _ n_le_p]) blast

private lemma as_subset_p: "set as \<subseteq> {..<p}"
   using as_lt_p  by (simp add: subset_iff)

private definition r where "r = nat (4 * \<lceil>log 2 (1 / real_of_rat \<delta>)\<rceil> + 23)"

private lemma r_bound: "4 * log 2 (1 / real_of_rat \<delta>) + 23 \<le> r"
proof -
  have "0 \<le> log 2 (1 / real_of_rat \<delta>)" using \<delta>_range by simp 
  hence "0 \<le> \<lceil>log 2 (1 / real_of_rat \<delta>)\<rceil>" by simp
  hence "0 \<le> 4 * \<lceil>log 2 (1 / real_of_rat \<delta>)\<rceil> + 23"
    by (intro add_nonneg_nonneg mult_nonneg_nonneg, auto)
  thus ?thesis by (simp add:r_def)
qed

private lemma r_ge_23: "r \<ge> 23"
proof -
  have "(23::real) = 0 + 23" by simp
  also have "... \<le> 4 * log 2 (1 / real_of_rat \<delta>) + 23" 
    using \<delta>_range by (intro add_mono mult_nonneg_nonneg, auto) 
  also have "... \<le> r" using r_bound by simp
  finally show "23 \<le> r" by simp
qed

private lemma two_pow_r_le_1: "0 < 1 - 2 powr - real r"
proof -
  have a: "2 powr (0::real) = 1"
    by simp
  show ?thesis using r_ge_23 
    by (simp, subst a[symmetric], intro powr_less_mono, auto)
qed

interpretation carter_wegman_hash_family "mod_ring p" 2
  rewrites "ring.hash (mod_ring p) = Frequency_Moment_0.hash p"
  using carter_wegman_hash_familyI[OF mod_ring_is_field mod_ring_finite]
  using hash_def p_prime by auto

private definition tr_hash where "tr_hash x \<omega> = truncate_down r (hash x \<omega>)"

private definition sketch_rv where
  "sketch_rv \<omega> = least t ((\<lambda>x. float_of (tr_hash x \<omega>)) ` set as)"

private definition estimate 
   where "estimate S = (if card S < t then of_nat (card S) else of_nat t * of_nat p / rat_of_float (Max S))"

private definition sketch_rv' where "sketch_rv' \<omega> = least t ((\<lambda>x. tr_hash x \<omega>) ` set as)"
private definition estimate' where "estimate' S = (if card S < t then real (card S) else real t * real p / Max S)"

private definition \<Omega>\<^sub>0 where "\<Omega>\<^sub>0 = prod_pmf {..<s} (\<lambda>_. pmf_of_set space)"

private lemma f0_alg_sketch:
  defines "sketch \<equiv> fold (\<lambda>a state. state \<bind> f0_update a) as (f0_init \<delta> \<epsilon> n)"
  shows "sketch = map_pmf (\<lambda>x. (s,t,p,r, x, \<lambda>i \<in> {..<s}. sketch_rv (x i))) \<Omega>\<^sub>0" 
  unfolding sketch_rv_def 
proof (subst sketch_def, induction as rule:rev_induct)
  case Nil
  then show ?case
    by (simp add:s_def p_def[symmetric] map_pmf_def t_def r_def Let_def least_def restrict_def space_def \<Omega>\<^sub>0_def)
next
  case (snoc x xs)
  let ?sketch = "\<lambda>\<omega> xs. least t ((\<lambda>a. float_of (tr_hash a \<omega>)) ` set xs)"
  have "fold (\<lambda>a state. state \<bind> f0_update a) (xs @ [x]) (f0_init \<delta> \<epsilon> n) =
     (map_pmf (\<lambda>\<omega>. (s, t, p, r, \<omega>, \<lambda>i \<in> {..<s}. ?sketch (\<omega> i) xs)) \<Omega>\<^sub>0) \<bind> f0_update x"
    by (simp add: restrict_def snoc del:f0_init.simps)
  also have "... = \<Omega>\<^sub>0 \<bind> (\<lambda>\<omega>. f0_update x (s, t, p, r, \<omega>, \<lambda>i\<in>{..<s}. ?sketch (\<omega> i) xs)) "
    by (simp add:map_pmf_def bind_assoc_pmf bind_return_pmf del:f0_update.simps)
  also have "... = map_pmf (\<lambda>\<omega>. (s, t, p, r, \<omega>, \<lambda>i\<in>{..<s}. ?sketch (\<omega> i) (xs@[x]))) \<Omega>\<^sub>0"
    by (simp add:least_insert map_pmf_def tr_hash_def cong:restrict_cong)
  finally show ?case by blast
qed

private lemma card_nat_in_ball:
  fixes x :: nat
  fixes q :: real
  assumes "q \<ge> 0"
  defines "A \<equiv> {k. abs (real x - real k) \<le> q \<and> k \<noteq> x}"
  shows "real (card A) \<le> 2 * q" and "finite A"
proof -
  have a: "of_nat x \<in> {\<lceil>real x-q\<rceil>..\<lfloor>real x+q\<rfloor>}"
    using assms 
    by (simp add: ceiling_le_iff)

  have "card A = card (int ` A)"
    by (rule card_image[symmetric], simp)
  also have "... \<le> card ({\<lceil>real x-q\<rceil>..\<lfloor>real x+q\<rfloor>} - {of_nat x})"
    by (intro card_mono image_subsetI, simp_all add:A_def abs_le_iff, linarith)
  also have "... = card {\<lceil>real x-q\<rceil>..\<lfloor>real x+q\<rfloor>} - 1"
    by (rule card_Diff_singleton, rule a)
  also have "... = int (card {\<lceil>real x-q\<rceil>..\<lfloor>real x+q\<rfloor>}) - int 1"
    by (intro of_nat_diff)
     (metis a card_0_eq empty_iff finite_atLeastAtMost_int less_one linorder_not_le)
  also have "... \<le> \<lfloor>q+real x\<rfloor>+1 -\<lceil>real x-q\<rceil> - 1"
    using assms by (simp, linarith)
  also have "... \<le> 2*q"
    by linarith
  finally show "card A \<le> 2 * q"
    by simp

  have "A \<subseteq> {..x + nat \<lceil>q\<rceil>}"
    by (rule subsetI, simp add:A_def abs_le_iff, linarith)
  thus "finite A"
    by (rule finite_subset, simp)
qed

private lemma prob_degree_lt_1:
   "prob {\<omega>. degree \<omega> < 1} \<le> 1/real p" 
proof -
  have "space \<inter> {\<omega>. length \<omega> \<le> Suc 0} = bounded_degree_polynomials (mod_ring p) 1"
    by (auto simp:set_eq_iff bounded_degree_polynomials_def space_def)
  moreover have "field_size = p" by (simp add:mod_ring_def)
  hence "real (card (bounded_degree_polynomials (mod_ring p) (Suc 0))) / real (card space) = 1 / real p"
    by (simp add:space_def bounded_degree_polynomials_card power2_eq_square)
  ultimately show ?thesis
    by (simp add:M_def measure_pmf_of_set)
qed

private lemma collision_prob:
  assumes "c \<ge> 1"
  shows "prob {\<omega>. \<exists>x \<in> set as. \<exists>y \<in> set as. x \<noteq> y \<and> tr_hash x \<omega> \<le> c \<and> tr_hash x \<omega> = tr_hash y \<omega>} \<le> 
    (5/2) * (real (card (set as)))\<^sup>2 * c\<^sup>2 * 2 powr -(real r) / (real p)\<^sup>2 + 1/real p" (is "prob {\<omega>. ?l \<omega>} \<le> ?r1 + ?r2")
proof -
  define \<rho> :: real where "\<rho> = 9/8"

  have rho_c_ge_0: "\<rho> * c \<ge> 0" unfolding \<rho>_def using assms by simp 

  have c_ge_0: "c\<ge>0" using assms by simp
  
  have "degree \<omega> \<ge> 1 \<Longrightarrow> \<omega> \<in> space \<Longrightarrow> degree \<omega> = 1" for \<omega>
    by (simp add:bounded_degree_polynomials_def space_def) 
     (metis One_nat_def Suc_1 le_less_Suc_eq less_imp_diff_less list.size(3) pos2)

  hence a: "\<And>\<omega> x y. x < p \<Longrightarrow> y < p \<Longrightarrow>  x \<noteq> y \<Longrightarrow> degree \<omega> \<ge> 1 \<Longrightarrow> \<omega> \<in> space \<Longrightarrow>  hash x \<omega> \<noteq> hash y \<omega>" 
    using inj_onD[OF inj_if_degree_1]  mod_ring_carr by blast 

  have b: "prob {\<omega>. degree \<omega> \<ge> 1 \<and> tr_hash x \<omega> \<le> c \<and> tr_hash x \<omega> = tr_hash y \<omega>} \<le> 5 * c\<^sup>2 * 2 powr (-real r) /(real p)\<^sup>2"
    if b_assms: "x \<in> set as"  "y \<in> set as"  "x < y" for x y
  proof -
    have c: "real u \<le> \<rho> * c \<and> \<bar>real u - real v\<bar> \<le> \<rho> * c * 2 powr (-real r)"
      if c_assms:"truncate_down r (real u) \<le> c" "truncate_down r (real u) = truncate_down r (real v)" for u v
    proof -
      have "9 * 2 powr - real r \<le> 9 * 2 powr (- real 23)" 
        using r_ge_23 by (intro mult_left_mono powr_mono, auto)

      also have "... \<le> 1" by simp

      finally have "9 * 2 powr - real r \<le> 1" by simp

      hence "1 \<le> \<rho> * (1 - 2 powr (- real r))" 
        by (simp add:\<rho>_def)

      hence d: "(c*1) / (1 - 2 powr (-real r)) \<le> c * \<rho>" 
        using assms two_pow_r_le_1 by (simp add: pos_divide_le_eq)

      have "\<And>x. truncate_down r (real x) \<le> c \<Longrightarrow> real x * (1 - 2 powr - real r) \<le> c * 1" 
        using  truncate_down_pos[OF of_nat_0_le_iff] order_trans by (simp, blast)

      hence "\<And>x. truncate_down r (real x) \<le>  c  \<Longrightarrow> real x \<le> c * \<rho>"
        using two_pow_r_le_1 by (intro order_trans[OF _ d], simp add: pos_le_divide_eq) 

      hence e: "real u \<le> c * \<rho>" "real v \<le> c * \<rho>" 
        using c_assms by auto

      have " \<bar>real u - real v\<bar> \<le> (max \<bar>real u\<bar> \<bar>real v\<bar>) * 2 powr (-real r)"
        using c_assms by (intro truncate_down_eq, simp)

      also have "... \<le> (c * \<rho>) * 2 powr (-real r)"
        using e by (intro mult_right_mono, auto)

      finally have "\<bar>real u - real v\<bar> \<le> \<rho> * c * 2 powr (-real r)"
        by (simp add:algebra_simps)

      thus ?thesis using e by (simp add:algebra_simps)
    qed

    have "prob {\<omega>. degree \<omega> \<ge> 1 \<and> tr_hash x \<omega> \<le> c \<and> tr_hash x \<omega> = tr_hash y \<omega>} \<le>
      prob (\<Union> i \<in> {(u,v) \<in> {..<p} \<times> {..<p}. u \<noteq> v \<and> truncate_down r u \<le> c \<and> truncate_down r u = truncate_down r v}.
      {\<omega>.  hash x \<omega> = fst i \<and> hash y \<omega> = snd i})"
      using a by (intro pmf_mono[OF M_def], simp add:tr_hash_def) 
       (metis hash_range mod_ring_carr b_assms as_subset_p lessThan_iff nat_neq_iff subset_eq) 

    also have "... \<le> (\<Sum> i\<in> {(u,v) \<in> {..<p} \<times> {..<p}. u \<noteq> v \<and>
      truncate_down r u \<le> c \<and> truncate_down r u = truncate_down r v}. 
      prob {\<omega>. hash x \<omega> = fst i \<and> hash  y \<omega> = snd i})"
      by (intro measure_UNION_le finite_cartesian_product finite_subset[where B="{0..<p} \<times> {0..<p}"])
       (auto simp add:M_def)

    also have "... \<le> (\<Sum> i\<in> {(u,v) \<in> {..<p} \<times> {..<p}. u \<noteq> v \<and>
      truncate_down r u \<le> c \<and> truncate_down r u = truncate_down r v}. 
      prob {\<omega>. (\<forall>u \<in> {x,y}. hash u \<omega> = (if u = x then (fst i) else (snd i)))})" 
      by (intro sum_mono  pmf_mono[OF M_def]) force

    also have "... \<le> (\<Sum> i\<in> {(u,v) \<in> {..<p} \<times> {..<p}. u \<noteq> v \<and>
      truncate_down r u \<le> c \<and> truncate_down r u = truncate_down r v}. 1/(real p)\<^sup>2)"
      using assms as_subset_p b_assms
      by (intro sum_mono, subst hash_prob)  (auto simp add: mod_ring_def power2_eq_square)

    also have "... = 1/(real p)\<^sup>2 * 
      card {(u,v) \<in> {0..<p} \<times> {0..<p}. u \<noteq> v \<and> truncate_down r u \<le> c \<and> truncate_down r u = truncate_down r v}"
      by simp

    also have "... \<le> 1/(real p)\<^sup>2 * 
      card {(u,v) \<in> {..<p} \<times> {..<p}. u \<noteq> v \<and> real u \<le> \<rho> * c \<and> abs (real u - real v) \<le> \<rho> * c * 2 powr (-real r)}"
      using c
      by (intro mult_mono of_nat_mono card_mono finite_cartesian_product finite_subset[where B="{..<p}\<times>{..<p}"])
        auto

    also have "... \<le> 1/(real p)\<^sup>2 * card (\<Union>u' \<in> {u. u < p \<and> real u \<le> \<rho> * c}.
        {(u::nat,v::nat). u = u' \<and> abs (real u - real v) \<le> \<rho> * c * 2 powr (-real r) \<and> v < p \<and> v \<noteq> u'})"
      by (intro mult_left_mono of_nat_mono card_mono finite_cartesian_product finite_subset[where B="{..<p}\<times>{..<p}"])
       auto

    also have "... \<le> 1/(real p)\<^sup>2 * (\<Sum> u' \<in> {u. u < p \<and> real u \<le> \<rho> * c}.
      card  {(u,v). u = u' \<and> abs (real u - real v) \<le> \<rho> * c * 2 powr (-real r) \<and> v < p \<and> v \<noteq> u'})"
      by (intro mult_left_mono of_nat_mono card_UN_le, auto)

    also have "... = 1/(real p)\<^sup>2 * (\<Sum> u' \<in> {u. u < p \<and>  real u \<le> \<rho> * c}.
      card ((\<lambda>x. (u' ,x)) ` {v. abs (real u' - real v) \<le> \<rho> * c * 2 powr (-real r) \<and> v < p \<and> v \<noteq> u'}))"
      by (intro arg_cong2[where f="(*)"] arg_cong[where f="real"] sum.cong arg_cong[where f="card"])
       (auto simp add:set_eq_iff)

    also have "... \<le> 1/(real p)\<^sup>2 * (\<Sum> u' \<in> {u. u < p \<and> real u \<le> \<rho> * c}.
      card {v. abs (real u' - real v) \<le> \<rho> * c * 2 powr (-real r) \<and> v < p \<and> v \<noteq> u'})"
      by (intro mult_left_mono of_nat_mono sum_mono card_image_le, auto)

    also have "... \<le> 1/(real p)\<^sup>2 * (\<Sum> u' \<in> {u. u < p \<and> real u \<le> \<rho> * c}.
      card {v. abs (real u' - real v) \<le> \<rho> * c * 2 powr (-real r) \<and> v \<noteq> u'})"
      by (intro mult_left_mono sum_mono of_nat_mono card_mono card_nat_in_ball subsetI)  auto

    also have "... \<le> 1/(real p)\<^sup>2 * (\<Sum> u' \<in> {u. u < p \<and> real u \<le> \<rho> * c}.
      real (card {v. abs (real u' - real v) \<le> \<rho> * c * 2 powr (-real r) \<and> v \<noteq> u'}))"
      by simp

    also have "... \<le> 1/(real p)\<^sup>2 * (\<Sum> u' \<in> {u. u < p \<and> real u \<le> \<rho> * c}. 2 * (\<rho> * c * 2 powr (-real r)))"
      by (intro mult_left_mono sum_mono card_nat_in_ball(1), auto)

    also have "... =  1/(real p)\<^sup>2 * (real (card {u. u < p \<and> real u \<le> \<rho> * c}) * (2 * (\<rho> * c * 2 powr (-real r))))"
      by simp

    also have "... \<le>  1/(real p)\<^sup>2 * (real (card {u. u \<le> nat (\<lfloor>\<rho> * c \<rfloor>)}) * (2 * (\<rho> * c * 2 powr (-real r))))"
      using rho_c_ge_0 le_nat_floor
      by (intro mult_left_mono mult_right_mono of_nat_mono card_mono subsetI) auto

    also have "... \<le>  1/(real p)\<^sup>2 * ((1+\<rho> * c) * (2 * (\<rho> * c * 2 powr (-real r))))"
      using rho_c_ge_0 by (intro mult_left_mono mult_right_mono, auto)

    also have "... \<le>  1/(real p)\<^sup>2 * (((1+\<rho>) * c) * (2 * (\<rho> * c * 2 powr (-real r))))" 
      using assms by (intro mult_mono, auto simp add:distrib_left distrib_right \<rho>_def)

    also have "... = (\<rho> * (2 + \<rho> * 2)) * c\<^sup>2 * 2 powr (-real r) /(real p)\<^sup>2"
      by (simp add:ac_simps power2_eq_square) 

    also have "... \<le> 5 * c\<^sup>2 *  2 powr (-real r) /(real p)\<^sup>2"
      by (intro divide_right_mono mult_right_mono) (auto simp add:\<rho>_def)

    finally show ?thesis by simp
  qed

  have "prob {\<omega>. ?l \<omega> \<and> degree \<omega> \<ge> 1} \<le> 
    prob (\<Union> i \<in> {(x,y) \<in> (set as) \<times> (set as). x < y}. {\<omega>. degree \<omega> \<ge> 1 \<and> tr_hash (fst i) \<omega> \<le> c \<and>
    tr_hash (fst i) \<omega> = tr_hash (snd i) \<omega>})"
    by (rule pmf_mono[OF M_def], simp, metis linorder_neqE_nat)

  also have "... \<le> (\<Sum> i \<in> {(x,y) \<in> (set as) \<times> (set as). x < y}. prob 
    {\<omega>. degree \<omega> \<ge> 1 \<and> tr_hash  (fst i) \<omega> \<le> c \<and> tr_hash (fst i) \<omega> = tr_hash (snd i) \<omega>})"
    unfolding M_def
    by (intro measure_UNION_le finite_cartesian_product finite_subset[where B="(set as) \<times> (set as)"])
      auto

  also have "... \<le> (\<Sum> i \<in> {(x,y) \<in> (set as) \<times> (set as). x < y}. 5  * c\<^sup>2 * 2 powr (-real r) /(real p)\<^sup>2)"
    using b by (intro sum_mono, simp add:case_prod_beta)

  also have "... =  ((5/2) * c\<^sup>2  * 2 powr (-real r) /(real p)\<^sup>2) * (2 * card  {(x,y) \<in> (set as) \<times> (set as). x < y})"
    by simp

  also have "... =  ((5/2) * c\<^sup>2  * 2 powr (-real r) /(real p)\<^sup>2) * (card (set as) * (card (set as) - 1))"
    by (subst card_ordered_pairs, auto) 

  also have "... \<le> ((5/2) * c\<^sup>2 * 2 powr (-real r) /(real p)\<^sup>2) * (real (card (set as)))\<^sup>2"
    by (intro mult_left_mono) (auto simp add:power2_eq_square mult_left_mono)

  also have "... = (5/2) * (real (card (set as)))\<^sup>2 * c\<^sup>2 * 2 powr (-real r) /(real p)\<^sup>2"
    by (simp add:algebra_simps)

  finally have f:"prob {\<omega>. ?l \<omega> \<and> degree \<omega> \<ge> 1} \<le> ?r1" by simp

  have "prob {\<omega>. ?l \<omega>} \<le> prob {\<omega>. ?l \<omega> \<and> degree \<omega> \<ge> 1} + prob {\<omega>. degree \<omega> < 1}"
    by (rule pmf_add[OF M_def], auto)
  also have "... \<le> ?r1 + ?r2"
    by (intro add_mono f prob_degree_lt_1)
  finally show ?thesis by simp
qed

private lemma of_bool_square: "(of_bool x)\<^sup>2 = ((of_bool x)::real)"
  by (cases x, auto)

private definition Q where "Q y \<omega> = card {x \<in> set as. int (hash x \<omega>) < y}"

private definition m where "m = card (set as)"

private lemma
  assumes "a \<ge> 0"
  assumes "a \<le> int p"
  shows exp_Q: "expectation (\<lambda>\<omega>. real (Q a \<omega>)) = real m * (of_int a) / p"
  and var_Q: "variance (\<lambda>\<omega>. real (Q a \<omega>)) \<le> real m * (of_int a) / p"
proof -
  have exp_single: "expectation (\<lambda>\<omega>. of_bool (int (hash x \<omega>) < a)) = real_of_int a /real p"
    if a:"x \<in> set as" for x
  proof -
    have x_le_p: "x < p" using a as_lt_p by simp
    have "expectation (\<lambda>\<omega>. of_bool (int (hash x \<omega>) < a)) = expectation (indicat_real {\<omega>. int (Frequency_Moment_0.hash p x \<omega>) < a})"
      by (intro arg_cong2[where f="integral\<^sup>L"] ext, simp_all)
    also have "... = prob {\<omega>. hash x \<omega> \<in> {k. int k < a}}"
      by (simp add:M_def)
    also have "... = card ({k. int k < a} \<inter> {..<p}) / real p"
      by (subst prob_range, simp_all add: x_le_p mod_ring_def)
    also have "... = card {..<nat a} / real p"
      using assms by (intro arg_cong2[where f="(/)"] arg_cong[where f="real"] arg_cong[where f="card"])
       (auto simp add:set_eq_iff) 
    also have "... =  real_of_int a/real p"
      using assms by simp
    finally show "expectation (\<lambda>\<omega>. of_bool (int (hash x \<omega>) < a)) = real_of_int a /real p"
      by simp
  qed

  have "expectation(\<lambda>\<omega>. real (Q a \<omega>)) = expectation (\<lambda>\<omega>. (\<Sum>x \<in> set as. of_bool (int (hash x \<omega>) < a)))"
    by (simp add:Q_def Int_def)
  also have "... =  (\<Sum>x \<in> set as. expectation (\<lambda>\<omega>. of_bool (int (hash x \<omega>) < a)))"
    by (rule Bochner_Integration.integral_sum, simp)
  also have "... = (\<Sum> x \<in> set as. a /real p)"
    by (rule sum.cong, simp, subst exp_single, simp, simp)
  also have "... = real m *  real_of_int a / real p"
    by (simp add:m_def)
  finally show "expectation (\<lambda>\<omega>. real (Q a \<omega>)) = real m * real_of_int a / p" by simp

  have indep: "J \<subseteq> set as \<Longrightarrow> card J = 2 \<Longrightarrow> indep_vars (\<lambda>_. borel) (\<lambda>i x. of_bool (int (hash i x) < a)) J" for J
    using as_subset_p mod_ring_carr
    by (intro indep_vars_compose2[where Y="\<lambda>i x. of_bool (int x < a)" and M'="\<lambda>_. discrete"]
        k_wise_indep_vars_subset[OF k_wise_indep] finite_subset[OF _ finite_set]) auto

  have rv: "\<And>x. x \<in> set as \<Longrightarrow> random_variable borel (\<lambda>\<omega>. of_bool (int (hash x \<omega>) < a))"
     by (simp add:M_def)

  have "variance (\<lambda>\<omega>. real (Q a \<omega>)) = variance (\<lambda>\<omega>. (\<Sum>x \<in> set as. of_bool (int (hash x \<omega>) < a)))"
    by (simp add:Q_def Int_def)
  also have "... = (\<Sum>x \<in> set as. variance (\<lambda>\<omega>. of_bool (int (hash x \<omega>) < a)))"
    by (intro var_sum_pairwise_indep_2 indep rv) auto
  also have "... \<le> (\<Sum> x \<in> set as. a / real p)"
    by (rule sum_mono, simp add: variance_eq of_bool_square, simp add: exp_single)
  also have "... = real m * real_of_int a /real p"
    by (simp add:m_def)
  finally show "variance (\<lambda>\<omega>. real (Q a \<omega>)) \<le> real m * real_of_int a / p"
    by simp
qed

private lemma t_bound: "t \<le> 81 / (real_of_rat \<delta>)\<^sup>2"
proof -
  have "t \<le> 80 / (real_of_rat \<delta>)\<^sup>2 + 1" using t_def t_gt_0 by linarith
  also have "... \<le> 80 / (real_of_rat \<delta>)\<^sup>2 + 1 /  (real_of_rat \<delta>)\<^sup>2"
    using \<delta>_range by (intro add_mono, simp, simp add:power_le_one)
  also have "... = 81 / (real_of_rat \<delta>)\<^sup>2" by simp
  finally show ?thesis by simp
qed

private lemma t_r_bound:
  "18 * 40 * (real t)\<^sup>2 * 2 powr (-real r) \<le> 1"
proof -
  have "720 * (real t)\<^sup>2 * 2 powr (-real r) \<le> 720 * (81 / (real_of_rat \<delta>)\<^sup>2)\<^sup>2 * 2 powr (-4 * log 2 (1 / real_of_rat \<delta>) - 23)"
    using r_bound t_bound by (intro mult_left_mono mult_mono power_mono powr_mono, auto)

  also have "... \<le> 720 * (81 / (real_of_rat \<delta>)\<^sup>2)\<^sup>2 * (2 powr (-4 * log 2 (1 / real_of_rat \<delta>)) * 2 powr (-23))"
    using \<delta>_range by (intro mult_left_mono mult_mono power_mono add_mono)
     (simp_all add:power_le_one powr_diff)

  also have "... = 720 * (81\<^sup>2 / (real_of_rat \<delta>)^4) * (2 powr (log 2 ((real_of_rat \<delta>)^4))  * 2 powr (-23))"
    using \<delta>_range by (intro arg_cong2[where f="(*)"])
      (simp_all add:power2_eq_square power4_eq_xxxx log_divide log_powr[symmetric])

  also have "... = 720 * 81\<^sup>2 * 2 powr (-23)" using \<delta>_range by simp

  also have "... \<le> 1" by simp

  finally show ?thesis by simp
qed

private lemma m_eq_F_0: "real m = of_rat (F 0 as)"
  by (simp add:m_def F_def)

private lemma estimate'_bounds:
  "prob {\<omega>. of_rat \<delta> * real_of_rat (F 0 as) < \<bar>estimate' (sketch_rv' \<omega>) - of_rat (F 0 as)\<bar>} \<le> 1/3"
proof (cases "card (set as) \<ge> t")
  case True
  define \<delta>' where "\<delta>' = 3 * real_of_rat \<delta> / 4"
  define u where "u = \<lceil>real t * p / (m * (1+\<delta>'))\<rceil>"
  define v where "v = \<lfloor>real t * p / (m * (1-\<delta>'))\<rfloor>"

  define has_no_collision where 
    "has_no_collision = (\<lambda>\<omega>. \<forall>x\<in> set as. \<forall>y \<in> set as. (tr_hash x \<omega> = tr_hash y \<omega> \<longrightarrow> x = y) \<or> tr_hash x \<omega> > v)"

  have "2 powr (-real r) \<le> 2 powr (-(4 * log 2 (1 / real_of_rat \<delta>) + 23))"
    using r_bound by (intro powr_mono, linarith, simp)
  also have "... = 2 powr (-4 * log 2 (1 /real_of_rat \<delta>) -23)"
    by (rule arg_cong2[where f="(powr)"], auto simp add:algebra_simps)
  also have "... \<le> 2 powr ( -1 * log 2 (1 /real_of_rat \<delta>) -4)"
    using \<delta>_range by (intro powr_mono diff_mono, auto)
  also have "... = 2 powr ( -1 * log 2 (1 /real_of_rat \<delta>)) /  16"
    by (simp add: powr_diff)
  also have "... = real_of_rat \<delta> / 16"
    using \<delta>_range by (simp add:log_divide)
  also have "... < real_of_rat \<delta> / 8"
    using \<delta>_range by (subst pos_divide_less_eq, auto)
  finally have r_le_\<delta>: "2 powr (-real r) < real_of_rat \<delta> / 8"
    by simp

  have \<delta>'_gt_0: "\<delta>' > 0" using \<delta>_range by (simp add:\<delta>'_def)
  have "\<delta>' < 3/4" using \<delta>_range by (simp add:\<delta>'_def)+
  also have "... < 1" by simp
  finally have \<delta>'_lt_1: "\<delta>' < 1" by simp

  have "t \<le> 81 / (real_of_rat \<delta>)\<^sup>2"
    using t_bound by simp
  also have "... = (81*9/16) / (\<delta>')\<^sup>2"
    by (simp add:\<delta>'_def power2_eq_square)
  also have "... \<le> 46 / \<delta>'\<^sup>2"
    by (intro divide_right_mono, simp, simp)
  finally have t_le_\<delta>': "t \<le> 46/ \<delta>'\<^sup>2" by simp

  have "80 \<le> (real_of_rat \<delta>)\<^sup>2 * (80 / (real_of_rat \<delta>)\<^sup>2)" using \<delta>_range by simp
  also have "... \<le> (real_of_rat \<delta>)\<^sup>2 * t"
    by (intro mult_left_mono, simp add:t_def of_nat_ceiling, simp)
  finally have "80 \<le> (real_of_rat \<delta>)\<^sup>2 * t" by simp
  hence t_ge_\<delta>': "45 \<le> t * \<delta>' * \<delta>'" by (simp add:\<delta>'_def power2_eq_square)

  have "m \<le> card {..<n}" unfolding m_def using as_range by (intro card_mono, auto)
  also have "... \<le> p" using n_le_p by simp
  finally have m_le_p: "m \<le> p" by simp

  hence t_le_m: "t \<le> card (set as)" using True by simp
  have m_ge_0: "real m > 0" using m_def True t_gt_0 by simp

  have "v \<le> real t * real p / (real m * (1 - \<delta>'))" by (simp add:v_def)

  also have "... \<le> real t * real p / (real m * (1/4))"
    using \<delta>'_lt_1 m_ge_0 \<delta>_range
    by (intro divide_left_mono mult_left_mono mult_nonneg_nonneg mult_pos_pos, simp_all add:\<delta>'_def)

  finally have v_ubound: "v \<le> 4 * real t * real p / real m" by (simp add:algebra_simps)

  have a_ge_1: "u \<ge> 1" using \<delta>'_gt_0 p_gt_0 m_ge_0 t_gt_0
    by (auto intro!:mult_pos_pos divide_pos_pos simp add:u_def) 
  hence a_ge_0: "u \<ge> 0" by simp
  have "real m * (1 - \<delta>') < real m" using \<delta>'_gt_0 m_ge_0 by simp
  also have "... \<le> 1 * real p" using m_le_p by simp
  also have "... \<le> real t * real p" using t_gt_0 by (intro mult_right_mono, auto)
  finally have " real m * (1 - \<delta>') < real t * real p" by simp
  hence v_gt_0: "v > 0" using mult_pos_pos m_ge_0 \<delta>'_lt_1 by (simp add:v_def)
  hence v_ge_1: "real_of_int v \<ge> 1" by linarith

  have "real t \<le> real m" using True m_def by linarith
  also have "... < (1 + \<delta>') * real m" using \<delta>'_gt_0 m_ge_0 by force
  finally have a_le_p_aux: "real t < (1 + \<delta>') * real m"  by simp

  have "u \<le> real t * real p / (real m * (1 + \<delta>'))+1" by (simp add:u_def)
  also have "... < real p + 1" 
    using m_ge_0 \<delta>'_gt_0 a_le_p_aux  a_le_p_aux p_gt_0
    by (simp add: pos_divide_less_eq ac_simps) 
  finally have "u \<le> real p" 
    by (metis int_less_real_le not_less of_int_le_iff of_int_of_nat_eq)
  hence u_le_p: "u \<le> int p" by linarith

  have "prob {\<omega>. Q u \<omega> \<ge> t} \<le> prob {\<omega> \<in> Sigma_Algebra.space M. abs (real (Q u \<omega>) - 
    expectation (\<lambda>\<omega>. real (Q u \<omega>))) \<ge> 3 * sqrt (m * real_of_int u / p)}"
  proof (rule pmf_mono[OF M_def])
    fix \<omega>
    assume "\<omega> \<in> {\<omega>. t \<le> Q u \<omega>}"
    hence t_le: "t \<le> Q u \<omega>" by simp
    have "real m * real_of_int u / real p \<le> real m * (real t * real p / (real m * (1 + \<delta>'))+1) / real p"
      using m_ge_0 p_gt_0 by (intro divide_right_mono mult_left_mono, simp_all add: u_def)
    also have "... = real m * real t * real p / (real m * (1+\<delta>') * real p) + real m / real p"
      by (simp add:distrib_left add_divide_distrib)
    also have "... = real t / (1+\<delta>') + real m / real p"
      using p_gt_0 m_ge_0 by simp
    also have "... \<le> real t / (1+\<delta>') + 1"
      using m_le_p p_gt_0 by (intro add_mono, auto)
    finally have "real m * real_of_int u / real p \<le> real t / (1 + \<delta>') + 1"
      by simp

    hence "3 * sqrt (real m * of_int u / real p) + real m * of_int u / real p \<le> 
      3 * sqrt (t / (1+\<delta>')+1)+(t/(1+\<delta>')+1)"
      by (intro add_mono mult_left_mono real_sqrt_le_mono, auto)
    also have "... \<le> 3 * sqrt (real t+1) + ((t * (1 - \<delta>' / (1+\<delta>'))) + 1)"
      using \<delta>'_gt_0 t_gt_0 by (intro add_mono mult_left_mono real_sqrt_le_mono)
        (simp_all add: pos_divide_le_eq left_diff_distrib)
    also have "... = 3 * sqrt (real t+1) + (t - \<delta>' * t / (1+\<delta>')) + 1" by (simp add:algebra_simps)
    also have "... \<le> 3 * sqrt (46 / \<delta>'\<^sup>2 + 1 / \<delta>'\<^sup>2) + (t - \<delta>' * t/2) + 1 / \<delta>'"
      using \<delta>'_gt_0 t_gt_0 \<delta>'_lt_1 add_pos_pos  t_le_\<delta>'
      by (intro add_mono mult_left_mono real_sqrt_le_mono add_mono)
       (simp_all add: power_le_one pos_le_divide_eq)
    also have "... \<le> (21 / \<delta>' + (t - 45 / (2*\<delta>'))) + 1 / \<delta>'" 
      using \<delta>'_gt_0 t_ge_\<delta>' by (intro add_mono)
         (simp_all add:real_sqrt_divide divide_le_cancel real_le_lsqrt pos_divide_le_eq ac_simps)
    also have "... \<le> t" using \<delta>'_gt_0 by simp
    also have "... \<le> Q u \<omega>" using t_le by simp
    finally have "3 * sqrt (real m * of_int u / real p) + real m * of_int u / real p \<le> Q u \<omega>"
      by simp
    hence " 3 * sqrt (real m * real_of_int u / real p) \<le> \<bar>real (Q u \<omega>) - expectation (\<lambda>\<omega>. real (Q u \<omega>))\<bar>"
      using a_ge_0 u_le_p  True by (simp add:exp_Q abs_ge_iff)

    thus "\<omega> \<in> {\<omega> \<in> Sigma_Algebra.space M. 3 * sqrt (real m * real_of_int u / real p) \<le> 
      \<bar>real (Q u \<omega>) - expectation (\<lambda>\<omega>. real (Q u \<omega>))\<bar>}"
      by (simp add: M_def)
  qed
  also have "... \<le> variance  (\<lambda>\<omega>. real (Q u \<omega>)) / (3 * sqrt (real m * of_int u / real p))\<^sup>2"
    using a_ge_1 p_gt_0 m_ge_0 
    by (intro Chebyshev_inequality, simp add:M_def, auto) 

  also have "... \<le> (real m * real_of_int u / real p) / (3 * sqrt (real m * of_int u / real p))\<^sup>2"
    using a_ge_0 u_le_p by (intro divide_right_mono var_Q, auto)

  also have "... \<le> 1/9" using a_ge_0 by simp

  finally have case_1: "prob {\<omega>. Q u \<omega> \<ge> t} \<le> 1/9" by simp

  have case_2: "prob {\<omega>. Q v \<omega> < t} \<le> 1/9"
  proof (cases "v \<le> p")
    case True
    have "prob {\<omega>. Q v \<omega> < t} \<le> prob {\<omega> \<in> Sigma_Algebra.space M. abs (real (Q v \<omega>) - expectation (\<lambda>\<omega>. real (Q v \<omega>))) 
      \<ge> 3 * sqrt (m * real_of_int v / p)}"
    proof (rule pmf_mono[OF M_def])
      fix \<omega>
      assume "\<omega> \<in> set_pmf (pmf_of_set space)"
      have "(real t + 3 * sqrt (real t / (1 - \<delta>') )) * (1 - \<delta>') = real t - \<delta>' * t + 3 * ((1-\<delta>') * sqrt( real t / (1-\<delta>') ))"
        by (simp add:algebra_simps)

      also have "... = real t - \<delta>' * t + 3 * sqrt (  (1-\<delta>')\<^sup>2 * (real t /  (1-\<delta>')))"
        using \<delta>'_lt_1 by (subst real_sqrt_mult, simp)

      also have "... = real t - \<delta>' * t + 3 * sqrt ( real t * (1- \<delta>'))"
        by (simp add:power2_eq_square distrib_left)

      also have "... \<le> real t - 45/ \<delta>' + 3 * sqrt ( real t )"
        using \<delta>'_gt_0 t_ge_\<delta>' \<delta>'_lt_1 by (intro add_mono mult_left_mono real_sqrt_le_mono)
         (simp_all add:pos_divide_le_eq ac_simps left_diff_distrib power_le_one)

       also have "... \<le> real t - 45/ \<delta>' + 3 * sqrt ( 46 / \<delta>'\<^sup>2)"
         using  t_le_\<delta>' \<delta>'_lt_1 \<delta>'_gt_0
         by (intro add_mono mult_left_mono real_sqrt_le_mono, simp_all add:pos_divide_le_eq power_le_one)

      also have "... = real t + (3 * sqrt(46) - 45)/ \<delta>'"
        using \<delta>'_gt_0 by (simp add:real_sqrt_divide diff_divide_distrib)

      also have "... \<le> t"
        using \<delta>'_gt_0 by (simp add:pos_divide_le_eq real_le_lsqrt)

      finally have aux: "(real t + 3 * sqrt (real t / (1 - \<delta>'))) * (1 - \<delta>') \<le> real t "
        by simp

      assume "\<omega> \<in> {\<omega>. Q v \<omega> < t}"
      hence "Q v \<omega> < t" by simp

      hence "real (Q v \<omega>) + 3 * sqrt (real m * real_of_int v / real p) 
        \<le> real t - 1 + 3 * sqrt (real m * real_of_int v / real p)"
        using m_le_p p_gt_0 by (intro add_mono, auto simp add: algebra_simps add_divide_distrib)

      also have "... \<le> (real t-1) + 3 * sqrt (real m * (real t * real p / (real m * (1- \<delta>'))) / real p)"
        by (intro add_mono mult_left_mono real_sqrt_le_mono divide_right_mono)
         (auto simp add:v_def)

      also have "... \<le> real t + 3 * sqrt(real t / (1-\<delta>')) - 1"
        using m_ge_0 p_gt_0 by simp

      also have "... \<le> real t / (1-\<delta>')-1" 
        using \<delta>'_lt_1 aux by (simp add: pos_le_divide_eq)   
      also have "... \<le> real m * (real t * real p / (real m * (1-\<delta>'))) / real p - 1"
        using p_gt_0 m_ge_0 by simp
      also have "... \<le> real m * (real t * real p / (real m * (1-\<delta>'))) / real p - real m / real p"
          using m_le_p p_gt_0
          by (intro diff_mono, auto)
      also have "... = real m * (real t * real p / (real m * (1-\<delta>'))-1) / real p" 
          by (simp add: left_diff_distrib right_diff_distrib diff_divide_distrib)
      also have "... \<le>  real m * real_of_int v / real p"      
        by (intro divide_right_mono mult_left_mono, simp_all add:v_def)

      finally have "real (Q v \<omega>) + 3 * sqrt (real m * real_of_int v / real p) 
        \<le> real m * real_of_int v / real p" by simp

      hence " 3 * sqrt (real m * real_of_int v / real p) \<le> \<bar>real (Q v \<omega>) -expectation (\<lambda>\<omega>. real (Q v \<omega>))\<bar>"  
        using v_gt_0 True by (simp add: exp_Q abs_ge_iff)

      thus "\<omega> \<in> {\<omega>\<in> Sigma_Algebra.space M. 3 * sqrt (real m * real_of_int v / real p) \<le> 
        \<bar>real (Q v \<omega>) - expectation (\<lambda>\<omega>. real (Q v \<omega>))\<bar>}" 
        by (simp add:M_def)
    qed
    also have "... \<le> variance (\<lambda>\<omega>. real (Q v \<omega>)) / (3 * sqrt (real m * real_of_int v / real p))\<^sup>2" 
      using v_gt_0 p_gt_0 m_ge_0 
      by (intro Chebyshev_inequality, simp add:M_def, auto)

    also have "... \<le> (real m * real_of_int v / real p) / (3 * sqrt (real m * real_of_int v / real p))\<^sup>2"
      using  v_gt_0 True  by (intro divide_right_mono var_Q, auto)

    also have "... = 1/9"
      using p_gt_0 v_gt_0 m_ge_0 by (simp add:power2_eq_square)

    finally show ?thesis by simp
  next
    case False
    have "prob {\<omega>. Q v \<omega> < t} \<le> prob {\<omega>. False}"
    proof (rule pmf_mono[OF M_def])
      fix \<omega>
      assume a:"\<omega> \<in> {\<omega>. Q v \<omega> < t}"
      assume "\<omega> \<in> set_pmf (pmf_of_set space)"
      hence b:"\<And>x. x < p \<Longrightarrow> hash x \<omega> < p" 
        using hash_range mod_ring_carr by (simp add:M_def measure_pmf_inverse) 
      have "t \<le> card (set as)" using True by simp
      also have "... \<le> Q v \<omega>"
        unfolding Q_def  using b False as_lt_p by (intro card_mono subsetI, simp, force) 
      also have "... < t" using a by simp
      finally have "False" by auto
      thus "\<omega> \<in> {\<omega>. False}" by simp
    qed
    also have "... = 0" by auto
    finally show ?thesis by simp
  qed

  have "prob {\<omega>. \<not>has_no_collision \<omega>} \<le>
    prob {\<omega>. \<exists>x \<in> set as. \<exists>y \<in> set as. x \<noteq> y \<and> tr_hash x \<omega> \<le> real_of_int v \<and> tr_hash x \<omega> = tr_hash y \<omega>}"
    by (rule pmf_mono[OF M_def]) (simp add:has_no_collision_def M_def, force) 

  also have "... \<le> (5/2) * (real (card (set as)))\<^sup>2 * (real_of_int v)\<^sup>2 * 2 powr - real r / (real p)\<^sup>2 + 1 / real p"
    using collision_prob v_ge_1 by blast

  also have "... \<le> (5/2) * (real m)\<^sup>2 * (real_of_int v)\<^sup>2 * 2 powr - real r / (real p)\<^sup>2 + 1 / real p"
    by (intro divide_right_mono add_mono mult_right_mono mult_mono power_mono, simp_all add:m_def)

  also have "... \<le> (5/2) * (real m)\<^sup>2 * (4 * real t * real p / real m)\<^sup>2 * (2 powr - real r) / (real p)\<^sup>2 + 1 / real p"
    using v_def v_ge_1 v_ubound
    by (intro add_mono divide_right_mono  mult_right_mono  mult_left_mono, auto)

  also have "... = 40 * (real t)\<^sup>2 * (2 powr -real r) + 1 / real p"
    using p_gt_0 m_ge_0 t_gt_0 by (simp add:algebra_simps power2_eq_square)

  also have "... \<le> 1/18 + 1/18"
    using t_r_bound p_ge_18 by (intro add_mono, simp_all add: pos_le_divide_eq)

  also have "... = 1/9" by simp

  finally have case_3: "prob {\<omega>. \<not>has_no_collision \<omega>} \<le> 1/9" by simp

  have "prob {\<omega>. real_of_rat \<delta> * of_rat (F 0 as) < \<bar>estimate' (sketch_rv' \<omega>) - of_rat (F 0 as)\<bar>} \<le> 
    prob {\<omega>. Q u \<omega> \<ge> t \<or> Q v \<omega> < t \<or> \<not>(has_no_collision \<omega>)}"
  proof (rule pmf_mono[OF M_def], rule ccontr)
    fix \<omega>
    assume "\<omega> \<in> set_pmf (pmf_of_set space)"
    assume "\<omega> \<in> {\<omega>. real_of_rat \<delta> * real_of_rat (F 0 as) < \<bar>estimate' (sketch_rv' \<omega>) - real_of_rat (F 0 as)\<bar>}"
    hence est: "real_of_rat \<delta> * real_of_rat (F 0 as) < \<bar>estimate' (sketch_rv' \<omega>) - real_of_rat (F 0 as)\<bar>" by simp
    assume "\<omega> \<notin> {\<omega>. t \<le> Q u \<omega> \<or> Q v \<omega> < t \<or> \<not> has_no_collision \<omega>}"
    hence "\<not>( t \<le> Q u \<omega> \<or> Q v \<omega> < t \<or> \<not> has_no_collision \<omega>)" by simp
    hence lb: "Q u \<omega> < t" and ub: "Q v \<omega> \<ge> t" and no_col: "has_no_collision \<omega>" by simp+

    define y where "y =  nth_mset (t-1) {#int (hash x \<omega>). x \<in># mset_set (set as)#}"
    define y' where "y' = nth_mset (t-1) {#tr_hash x \<omega>. x \<in># mset_set (set as)#}"

    have rank_t_lb: "u \<le> y"
      unfolding y_def using True t_gt_0 lb
      by (intro nth_mset_bound_left, simp_all add:count_less_def swap_filter_image Q_def)
  
    have rank_t_ub: "y \<le> v - 1"
      unfolding y_def using True t_gt_0 ub
      by (intro nth_mset_bound_right, simp_all add:Q_def swap_filter_image count_le_def)

    have y_ge_0: "real_of_int y \<ge> 0" using rank_t_lb a_ge_0 by linarith

    have "mono (\<lambda>x. truncate_down r (real_of_int x))" 
      by (metis truncate_down_mono mono_def of_int_le_iff)
    hence y'_eq: "y' = truncate_down r y"
      unfolding y_def y'_def  using True t_gt_0
      by (subst nth_mset_commute_mono[where f="(\<lambda>x. truncate_down r (of_int x))"]) 
        (simp_all add: multiset.map_comp comp_def tr_hash_def)

    have "real_of_int u * (1 - 2 powr -real r) \<le> real_of_int y * (1 - 2 powr (-real r))"
      using rank_t_lb of_int_le_iff two_pow_r_le_1
      by (intro mult_right_mono, auto)
    also have "... \<le> y'"
      using y'_eq truncate_down_pos[OF y_ge_0] by simp
    finally have rank_t_lb': "u * (1 - 2 powr -real r) \<le> y'" by simp

    have "y' \<le> real_of_int y"
      by (subst y'_eq, rule truncate_down_le, simp)
    also have "... \<le> real_of_int (v-1)"
      using rank_t_ub of_int_le_iff by blast
    finally have rank_t_ub': "y' \<le> v-1"
      by simp

    have "0 < u * (1-2 powr -real r)"
      using a_ge_1 two_pow_r_le_1 by (intro mult_pos_pos, auto)
    hence y'_pos: "y' > 0" using rank_t_lb' by linarith

    have no_col': "\<And>x. x \<le> y' \<Longrightarrow> count {#tr_hash x \<omega>. x \<in># mset_set (set as)#} x \<le> 1"
      using  rank_t_ub' no_col 
      by (simp add:vimage_def card_le_Suc0_iff_eq count_image_mset has_no_collision_def) force

    have h_1: "Max (sketch_rv' \<omega>) = y'"
      using True t_gt_0 no_col'
      by (simp add:sketch_rv'_def y'_def nth_mset_max)

    have "card (sketch_rv' \<omega>) = card (least ((t-1)+1) (set_mset {#tr_hash x \<omega>. x \<in># mset_set (set as)#}))"
      using t_gt_0 by (simp add:sketch_rv'_def)
    also have "... = (t-1) +1"
      using True t_gt_0 no_col' by (intro nth_mset_max(2), simp_all add:y'_def)
    also have "... = t" using t_gt_0 by simp
    finally have "card (sketch_rv' \<omega>) = t" by simp
    hence h_3: "estimate' (sketch_rv' \<omega>) = real t * real p / y'"
      using h_1 by (simp add:estimate'_def)

    have "(real t) * real p \<le>  (1 + \<delta>') * real m * ((real t) * real p / (real m * (1 + \<delta>')))" 
      using \<delta>'_lt_1 m_def True t_gt_0 \<delta>'_gt_0 by auto
    also have "... \<le> (1+\<delta>') * m * u"
      using \<delta>'_gt_0 by (intro mult_left_mono, simp_all add:u_def)
    also have "... < ((1 + real_of_rat \<delta>)*(1-real_of_rat \<delta>/8)) * m * u"
      using True m_def t_gt_0 a_ge_1 \<delta>_range
      by (intro mult_strict_right_mono, auto simp add:\<delta>'_def right_diff_distrib)
    also have "... \<le> ((1 + real_of_rat \<delta>)*(1-2 powr (-r))) * m * u"
      using r_le_\<delta> \<delta>_range a_ge_0 by (intro mult_right_mono mult_left_mono, auto)
    also have "... = (1 + real_of_rat \<delta>) * m * (u * (1-2 powr -real r))" 
      by simp
    also have "... \<le> (1 + real_of_rat \<delta>) * m * y'"
      using \<delta>_range by (intro mult_left_mono rank_t_lb', simp)
    finally have "real t * real p < (1 + real_of_rat \<delta>) * m * y'" by simp
    hence f_1: "estimate' (sketch_rv' \<omega>) < (1 + real_of_rat \<delta>) * m"
      using y'_pos by (simp add: h_3 pos_divide_less_eq)

    have "(1 - real_of_rat \<delta>) * m * y' \<le> (1 - real_of_rat \<delta>) * m * v" 
      using \<delta>_range rank_t_ub' y'_pos by (intro mult_mono rank_t_ub', simp_all)
    also have "... = (1-real_of_rat \<delta>) * (real m * v)"
      by simp
    also have "... < (1-\<delta>') * (real m * v)" 
      using \<delta>_range m_ge_0 v_ge_1
      by (intro mult_strict_right_mono mult_pos_pos, simp_all add:\<delta>'_def)
    also have "... \<le> (1-\<delta>') * (real m * (real t * real p / (real m * (1-\<delta>'))))"
      using \<delta>'_gt_0 \<delta>'_lt_1 by (intro mult_left_mono, auto simp add:v_def)
    also have "... = real t * real p"
      using \<delta>'_gt_0 \<delta>'_lt_1 t_gt_0 p_gt_0 m_ge_0 by auto
    finally have "(1 - real_of_rat \<delta>) * m * y' < real t * real p" by simp
    hence f_2: "estimate' (sketch_rv' \<omega>) > (1 - real_of_rat \<delta>) * m"
      using y'_pos by (simp add: h_3 pos_less_divide_eq)

    have "abs (estimate' (sketch_rv' \<omega>) - real_of_rat (F 0 as)) < real_of_rat \<delta> * (real_of_rat (F 0 as))"
      using f_1 f_2 by (simp add:abs_less_iff algebra_simps m_eq_F_0)
    thus "False" using est by linarith
  qed
  also have "... \<le> 1/9 + (1/9 + 1/9)"
    by (intro pmf_add_2[OF M_def] case_1 case_2 case_3)
  also have "... = 1/3" by simp
  finally show ?thesis by simp
next
  case False
  have "prob {\<omega>. real_of_rat \<delta> * of_rat (F 0 as) < \<bar>estimate' (sketch_rv' \<omega>) - of_rat (F 0 as)\<bar>} \<le>
    prob {\<omega>. \<exists>x \<in> set as. \<exists>y \<in> set as. x \<noteq> y \<and> tr_hash x \<omega> \<le> real p \<and> tr_hash x \<omega> = tr_hash y \<omega>}" 
  proof (rule pmf_mono[OF M_def])
    fix \<omega>
    assume a:"\<omega> \<in> {\<omega>. real_of_rat \<delta> * real_of_rat (F 0 as) < \<bar>estimate' (sketch_rv' \<omega>) - real_of_rat (F 0 as)\<bar>}"
    assume b:"\<omega> \<in> set_pmf (pmf_of_set space)" 
    have c: "card (set as) < t" using False by auto
    hence "card ((\<lambda>x. tr_hash x \<omega>) ` set as) < t"
      using card_image_le order_le_less_trans by blast
    hence d:"card (sketch_rv' \<omega>) = card ((\<lambda>x. tr_hash x \<omega>) ` (set as))"
      by (simp add:sketch_rv'_def card_least)
    have "card (sketch_rv' \<omega>) < t"
      by (metis List.finite_set  c d card_image_le  order_le_less_trans)
    hence "estimate' (sketch_rv' \<omega>) = card (sketch_rv' \<omega>)" by (simp add:estimate'_def)
    hence "card (sketch_rv' \<omega>) \<noteq> real_of_rat (F 0 as)"
      using a \<delta>_range by simp 
        (metis abs_zero cancel_comm_monoid_add_class.diff_cancel of_nat_less_0_iff pos_prod_lt zero_less_of_rat_iff)
    hence "card (sketch_rv' \<omega>) \<noteq> card (set as)"
      using m_def m_eq_F_0 by linarith
    hence "\<not>inj_on (\<lambda>x. tr_hash x \<omega>) (set as)"
      using card_image d by auto
    moreover have "tr_hash x \<omega> \<le> real p" if a:"x \<in> set as" for x
    proof -
      have "hash x \<omega> < p" 
        using hash_range as_lt_p a b by (simp add:mod_ring_carr M_def)
      thus "tr_hash x \<omega> \<le> real p" using truncate_down_le by (simp add:tr_hash_def)
    qed
   ultimately show "\<omega> \<in> {\<omega>. \<exists>x \<in> set as. \<exists>y \<in> set as. x \<noteq> y \<and> tr_hash x \<omega> \<le> real p \<and> tr_hash x \<omega> = tr_hash y \<omega>}"
     by (simp add:inj_on_def, blast)
  qed
  also have "... \<le> (5/2) * (real (card (set as)))\<^sup>2 * (real p)\<^sup>2 * 2 powr - real r / (real p)\<^sup>2 + 1 / real p"
    using p_gt_0 by (intro collision_prob, auto)
  also have "... = (5/2) * (real (card (set as)))\<^sup>2 * 2 powr (- real r) + 1 / real p"
    using p_gt_0 by (simp add:ac_simps power2_eq_square)
  also have "... \<le> (5/2) * (real t)\<^sup>2 * 2 powr (-real r) + 1 / real p"
    using False by (intro add_mono mult_right_mono mult_left_mono power_mono, auto)
  also have "... \<le> 1/6 + 1/6"
    using t_r_bound p_ge_18 by (intro add_mono, simp_all)
  also have "... \<le> 1/3" by simp
  finally show ?thesis by simp
qed

private lemma median_bounds:
  "\<P>(\<omega> in measure_pmf \<Omega>\<^sub>0. \<bar>median s (\<lambda>i. estimate (sketch_rv (\<omega> i))) - F 0 as\<bar> \<le> \<delta> * F 0 as) \<ge> 1 - real_of_rat \<epsilon>"
proof -
  have "strict_mono_on A real_of_float" for A by (meson less_float.rep_eq strict_mono_onI)
  hence real_g_2: "\<And>\<omega>.  sketch_rv' \<omega> = real_of_float ` sketch_rv \<omega>" 
    by (simp add: sketch_rv'_def sketch_rv_def tr_hash_def least_mono_commute image_comp)

  moreover have "inj_on real_of_float A" for A
    using  real_of_float_inject by (simp add:inj_on_def)
  ultimately have card_eq: "\<And>\<omega>. card (sketch_rv \<omega>) = card (sketch_rv' \<omega>)" 
    using real_g_2 by (auto intro!: card_image[symmetric])

  have "Max (sketch_rv' \<omega>) = real_of_float (Max (sketch_rv \<omega>))" if a:"card (sketch_rv' \<omega>) \<ge> t" for \<omega> 
  proof -
    have "mono real_of_float"
      using less_eq_float.rep_eq mono_def by blast
    moreover have "finite (sketch_rv \<omega>)"
      by (simp add:sketch_rv_def least_def)
    moreover have " sketch_rv \<omega> \<noteq> {}"
      using card_eq[symmetric] card_gt_0_iff t_gt_0 a by (simp, force)  
    ultimately show ?thesis
      by (subst mono_Max_commute[where f="real_of_float"], simp_all add:real_g_2)
  qed
  hence real_g: "\<And>\<omega>. estimate' (sketch_rv' \<omega>) = real_of_rat (estimate (sketch_rv \<omega>))"
    by (simp add:estimate_def estimate'_def card_eq of_rat_divide of_rat_mult of_rat_add real_of_rat_of_float)

  have indep: "prob_space.indep_vars (measure_pmf \<Omega>\<^sub>0) (\<lambda>_. borel) (\<lambda>i \<omega>. estimate' (sketch_rv' (\<omega> i))) {0..<s}"
    unfolding \<Omega>\<^sub>0_def
    by (rule indep_vars_restrict_intro', auto simp add:restrict_dfl_def lessThan_atLeast0)

  moreover have "- (18 * ln (real_of_rat \<epsilon>)) \<le> real s"
    using of_nat_ceiling by (simp add:s_def) blast

  moreover have "i < s \<Longrightarrow> measure \<Omega>\<^sub>0 {\<omega>. of_rat \<delta> * of_rat (F 0 as) < \<bar>estimate' (sketch_rv' (\<omega> i)) - of_rat (F 0 as)\<bar>} \<le> 1/3"
    for i
    using estimate'_bounds unfolding \<Omega>\<^sub>0_def M_def
    by (subst prob_prod_pmf_slice, simp_all)
 
  ultimately have "1-real_of_rat \<epsilon> \<le> \<P>(\<omega> in measure_pmf \<Omega>\<^sub>0.
      \<bar>median s (\<lambda>i. estimate' (sketch_rv' (\<omega> i))) - real_of_rat (F 0 as)\<bar> \<le>  real_of_rat \<delta> * real_of_rat (F 0 as))"
    using \<epsilon>_range prob_space_measure_pmf
    by (intro prob_space.median_bound_2) auto
  also have "... = \<P>(\<omega> in measure_pmf \<Omega>\<^sub>0. 
      \<bar>median s (\<lambda>i. estimate (sketch_rv (\<omega> i))) - F 0 as\<bar> \<le>  \<delta> * F 0 as)"
    using s_gt_0 median_rat[symmetric] real_g by (intro arg_cong2[where f="measure"]) 
      (simp_all add:of_rat_diff[symmetric] of_rat_mult[symmetric] of_rat_less_eq)
  finally show "\<P>(\<omega> in measure_pmf \<Omega>\<^sub>0. \<bar>median s (\<lambda>i. estimate (sketch_rv (\<omega> i))) - F 0 as\<bar> \<le> \<delta> * F 0 as) \<ge> 1-real_of_rat \<epsilon>"
    by blast
qed

lemma f0_alg_correct':
  "\<P>(\<omega> in measure_pmf result. \<bar>\<omega> - F 0 as\<bar> \<le> \<delta> * F 0 as) \<ge> 1 - of_rat \<epsilon>"
proof -
  have f0_result_elim: "\<And>x. f0_result (s, t, p, r, x, \<lambda>i\<in>{..<s}. sketch_rv (x i)) =
    return_pmf (median s (\<lambda>i. estimate (sketch_rv (x i))))"
    by (simp add:estimate_def, rule median_cong, simp)
 
  have "result = map_pmf (\<lambda>x. (s, t, p, r, x, \<lambda>i\<in>{..<s}. sketch_rv (x i))) \<Omega>\<^sub>0 \<bind> f0_result"
    by (subst result_def, subst f0_alg_sketch, simp)
  also have "... = \<Omega>\<^sub>0 \<bind> (\<lambda>x. return_pmf (s, t, p, r, x, \<lambda>i\<in>{..<s}. sketch_rv (x i))) \<bind> f0_result"
    by (simp add:t_def p_def r_def s_def map_pmf_def)
  also have "... = \<Omega>\<^sub>0 \<bind> (\<lambda>x. return_pmf (median s (\<lambda>i. estimate (sketch_rv (x i)))))"
    by (subst bind_assoc_pmf, subst bind_return_pmf, subst f0_result_elim)  simp
  finally have a:"result =  \<Omega>\<^sub>0 \<bind> (\<lambda>x. return_pmf (median s (\<lambda>i. estimate (sketch_rv (x i)))))"
    by simp

  show ?thesis
    using median_bounds by (simp add: a map_pmf_def[symmetric])
qed

private lemma f_subset:
  assumes "g ` A \<subseteq> h ` B"
  shows "(\<lambda>x. f (g x)) ` A \<subseteq> (\<lambda>x. f (h x)) ` B"
  using assms by auto

lemma f0_exact_space_usage':
  defines "\<Omega> \<equiv> fold (\<lambda>a state. state \<bind> f0_update a) as (f0_init \<delta> \<epsilon> n)"
  shows "AE \<omega> in \<Omega>. bit_count (encode_f0_state \<omega>) \<le> f0_space_usage (n, \<epsilon>, \<delta>)"
proof -
  
  have log_2_4: "log 2 4 = 2" 
    by (metis log2_of_power_eq mult_2 numeral_Bit0 of_nat_numeral power2_eq_square)

  have a: "bit_count (F\<^sub>e (float_of (truncate_down r y))) \<le> 
    ereal (12 + 4 * real r + 2 * log 2 (log 2 (n+13)))" if a_1:"y \<in> {..<p}" for y
  proof (cases "y \<ge> 1")
    case True

    have aux_1: " 0 < 2 + log 2 (real y)" 
      using True by (intro add_pos_nonneg, auto)
    have aux_2: "0 < 2 + log 2 (real p)"
      using p_gt_1 by (intro add_pos_nonneg, auto)

    have "bit_count (F\<^sub>e (float_of (truncate_down r y))) \<le> 
      ereal (10 + 4 * real r + 2 * log 2 (2 + \<bar>log 2 \<bar>real y\<bar>\<bar>))"
      by (rule truncate_float_bit_count)
    also have "... = ereal (10 + 4 * real r + 2 * log 2 (2 + (log 2 (real y))))"
      using True by simp
    also have "... \<le> ereal (10 + 4 * real r + 2 * log 2 (2 + log 2 p))"
      using aux_1 aux_2 True p_gt_0 a_1 by simp
    also have "... \<le> ereal (10 + 4 * real r + 2 * log 2 (log 2 4 + log 2 (2 * n + 40)))"
      using log_2_4 p_le_n p_gt_0
      by (intro ereal_mono add_mono mult_left_mono log_mono of_nat_mono add_pos_nonneg, auto)
    also have "... = ereal (10 + 4 * real r + 2 * log 2 (log 2 (8 * n + 160)))"
      by (simp add:log_mult[symmetric])
    also have "... \<le> ereal (10 + 4 * real r + 2 * log 2 (log 2 ((n+13) powr 2)))"
      by (intro ereal_mono add_mono mult_left_mono log_mono of_nat_mono add_pos_nonneg)
       (auto simp add:power2_eq_square algebra_simps)
    also have "... = ereal (10 +  4 * real r + 2 * log 2 (log 2 4 * log 2 (n + 13)))"
      by (subst log_powr, simp_all add:log_2_4)
    also have "... = ereal (12 +  4 * real r + 2 * log 2 (log 2 (n + 13)))"
      by (subst log_mult, simp_all add:log_2_4)
    finally show ?thesis by simp
  next
    case False
    hence "y = 0" using a_1 by simp
    then show ?thesis by (simp add:float_bit_count_zero)
  qed

  have "bit_count (encode_f0_state (s, t, p, r, x, \<lambda>i\<in>{..<s}. sketch_rv (x i))) \<le> 
        f0_space_usage (n, \<epsilon>, \<delta>)" if b: "x \<in> {..<s} \<rightarrow>\<^sub>E space" for x
  proof -
    have c: "x \<in> extensional {..<s}" using b by (simp add:PiE_def) 

    have d: "sketch_rv (x y) \<subseteq> (\<lambda>k. float_of (truncate_down r k)) ` {..<p} "
      if d_1: "y < s" for y
    proof -
      have "sketch_rv (x y) \<subseteq> (\<lambda>xa. float_of (truncate_down r (hash xa (x y)))) ` set as"
        using least_subset by (auto simp add:sketch_rv_def tr_hash_def) 
      also have "... \<subseteq> (\<lambda>k. float_of (truncate_down r (real k))) ` {..<p}"
        using b hash_range as_lt_p d_1
        by (intro f_subset[where f="\<lambda>x. float_of (truncate_down r (real x))"] image_subsetI)
         (simp add: PiE_iff mod_ring_carr)
      finally show ?thesis
        by simp
    qed

    have "\<And>y. y < s \<Longrightarrow> finite (sketch_rv (x y))"
      unfolding sketch_rv_def by (rule finite_subset[OF least_subset], simp)
    moreover have card_sketch: "\<And>y. y < s \<Longrightarrow> card (sketch_rv (x y)) \<le> t "
      by (simp add:sketch_rv_def card_least)
    moreover have "\<And>y z. y < s \<Longrightarrow> z \<in> sketch_rv (x y) \<Longrightarrow> 
      bit_count (F\<^sub>e z) \<le> ereal (12 + 4 * real r + 2 * log 2 (log 2 (real n + 13)))"
      using a d by auto
    ultimately have e: "\<And>y. y < s \<Longrightarrow> bit_count (S\<^sub>e F\<^sub>e (sketch_rv (x y))) 
      \<le> ereal (real t) * (ereal (12 + 4 * real r + 2 * log 2 (log 2 (real (n + 13)))) + 1) + 1"
      using float_encoding by (intro set_bit_count_est, auto)

    have f: "\<And>y. y < s \<Longrightarrow> bit_count (P\<^sub>e p 2 (x y)) \<le> ereal (real 2 * (log 2 (real p) + 1))"
      using p_gt_1 b
      by (intro bounded_degree_polynomial_bit_count) (simp_all add:space_def PiE_def Pi_def)

    have "bit_count (encode_f0_state (s, t, p, r, x, \<lambda>i\<in>{..<s}. sketch_rv (x i))) =
      bit_count (N\<^sub>e s) + bit_count (N\<^sub>e t) +  bit_count (N\<^sub>e p) + bit_count (N\<^sub>e r) +
      bit_count (([0..<s] \<rightarrow>\<^sub>e P\<^sub>e p 2) x) +
      bit_count (([0..<s] \<rightarrow>\<^sub>e S\<^sub>e F\<^sub>e) (\<lambda>i\<in>{..<s}. sketch_rv (x i)))"
      by (simp add:encode_f0_state_def dependent_bit_count lessThan_atLeast0
        s_def[symmetric] t_def[symmetric] p_def[symmetric] r_def[symmetric] ac_simps)
    also have "... \<le> ereal (2* log 2 (real s + 1) + 1) + ereal  (2* log 2 (real t + 1) + 1)
      + ereal (2* log 2 (real p + 1) + 1) + ereal (2 * log 2 (real r + 1) + 1)
      + (ereal (real s) * (ereal (real 2 * (log 2 (real p) + 1)))) 
      + (ereal (real s) * ((ereal (real t) * 
            (ereal (12 + 4 * real r + 2 * log 2 (log 2 (real (n + 13)))) + 1) + 1)))"
      using c e f
      by (intro add_mono exp_golomb_bit_count fun_bit_count_est[where xs="[0..<s]", simplified])
       (simp_all add:lessThan_atLeast0)
    also have "... = ereal ( 4 + 2 * log 2 (real s + 1) + 2 * log 2 (real t + 1) + 
      2 * log 2 (real p + 1) + 2 * log 2 (real r + 1) + real s * (3 + 2 * log 2 (real p) + 
      real t * (13 + (4 * real r + 2 * log 2 (log 2 (real n + 13))))))"
      by (simp add:algebra_simps)
    also have "... \<le> ereal ( 4 + 2 * log 2 (real s + 1)  + 2 * log 2 (real t + 1) + 
      2 * log 2 (2 * (21 + real n)) + 2 * log 2 (real r + 1) + real s * (3 + 2 * log 2 (2 * (21 + real n)) + 
      real t * (13 + (4 * real r + 2 * log 2 (log 2 (real n + 13))))))"
      using p_le_n p_gt_0
      by (intro ereal_mono add_mono mult_left_mono, auto)
    also have "... =  ereal (6 + 2 * log 2 (real s + 1) + 2 * log 2 (real t + 1) + 
      2 * log 2 (21 + real n) + 2 * log 2 (real r + 1) + real s * (5 + 2 * log 2 (21 + real n) + 
      real t * (13 + (4 * real r + 2 * log 2 (log 2 (real n + 13))))))"
      by (subst (1 2) log_mult, auto)
    also have "... \<le> f0_space_usage (n, \<epsilon>, \<delta>)"
      by (simp add:s_def[symmetric] r_def[symmetric] t_def[symmetric] Let_def)
       (simp add:algebra_simps)
    finally show "bit_count (encode_f0_state (s, t, p, r, x, \<lambda>i\<in>{..<s}. sketch_rv (x i))) \<le> 
        f0_space_usage (n, \<epsilon>, \<delta>)" by simp
  qed
  hence "\<And>x. x \<in> set_pmf \<Omega>\<^sub>0 \<Longrightarrow>
         bit_count (encode_f0_state (s, t, p, r, x, \<lambda>i\<in>{..<s}. sketch_rv (x i)))  \<le> ereal (f0_space_usage (n, \<epsilon>, \<delta>))"
    by (simp add:\<Omega>\<^sub>0_def set_prod_pmf del:f0_space_usage.simps)
  hence "\<And>y. y \<in> set_pmf \<Omega> \<Longrightarrow> bit_count (encode_f0_state y) \<le> ereal (f0_space_usage (n, \<epsilon>, \<delta>))"
    by (simp add: \<Omega>_def f0_alg_sketch del:f0_space_usage.simps f0_init.simps)
     (metis (no_types, lifting) image_iff pmf.set_map)
  thus ?thesis
    by (simp add: AE_measure_pmf_iff del:f0_space_usage.simps)
qed

end

text \<open>Main results of this section:\<close>

theorem f0_alg_correct:
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "\<delta> \<in> {0<..<1}"
  assumes "set as \<subseteq> {..<n}"
  defines "\<Omega> \<equiv> fold (\<lambda>a state. state \<bind> f0_update a) as (f0_init \<delta> \<epsilon> n) \<bind> f0_result"
  shows "\<P>(\<omega> in measure_pmf \<Omega>. \<bar>\<omega> - F 0 as\<bar> \<le> \<delta> * F 0 as) \<ge> 1 - of_rat \<epsilon>"
  using f0_alg_correct'[OF assms(1-3)] unfolding \<Omega>_def by blast

theorem f0_exact_space_usage:
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "\<delta> \<in> {0<..<1}"
  assumes "set as \<subseteq> {..<n}"
  defines "\<Omega> \<equiv> fold (\<lambda>a state. state \<bind> f0_update a) as (f0_init \<delta> \<epsilon> n)"
  shows "AE \<omega> in \<Omega>. bit_count (encode_f0_state \<omega>) \<le> f0_space_usage (n, \<epsilon>, \<delta>)"
  using f0_exact_space_usage'[OF assms(1-3)] unfolding \<Omega>_def by blast

theorem f0_asymptotic_space_complexity:
  "f0_space_usage \<in> O[at_top \<times>\<^sub>F at_right 0 \<times>\<^sub>F at_right 0](\<lambda>(n, \<epsilon>, \<delta>). ln (1 / of_rat \<epsilon>) * 
  (ln (real n) + 1 / (of_rat \<delta>)\<^sup>2 * (ln (ln (real n)) + ln (1 / of_rat \<delta>))))"
  (is "_ \<in> O[?F](?rhs)")
proof -
  define n_of :: "nat \<times> rat \<times> rat \<Rightarrow> nat" where "n_of = (\<lambda>(n, \<epsilon>, \<delta>). n)"
  define \<epsilon>_of :: "nat \<times> rat \<times> rat \<Rightarrow> rat" where "\<epsilon>_of = (\<lambda>(n, \<epsilon>, \<delta>). \<epsilon>)"
  define \<delta>_of :: "nat \<times> rat \<times> rat \<Rightarrow> rat" where "\<delta>_of = (\<lambda>(n, \<epsilon>, \<delta>). \<delta>)"
  define t_of where "t_of = (\<lambda>x. nat \<lceil>80 / (real_of_rat (\<delta>_of x))\<^sup>2\<rceil>)"
  define s_of where "s_of = (\<lambda>x. nat \<lceil>-(18 * ln (real_of_rat (\<epsilon>_of x)))\<rceil>)"
  define r_of where "r_of = (\<lambda>x. nat (4 * \<lceil>log 2 (1 / real_of_rat (\<delta>_of x))\<rceil> + 23))"

  define g where "g = (\<lambda>x. ln (1 / of_rat (\<epsilon>_of x)) * (ln (real (n_of x)) + 
    1 / (of_rat (\<delta>_of x))\<^sup>2 * (ln (ln (real (n_of x))) + ln (1 / of_rat (\<delta>_of x)))))"

  have evt: "(\<And>x. 
    0 < real_of_rat (\<delta>_of x) \<and> 0 < real_of_rat (\<epsilon>_of x) \<and> 
    1/real_of_rat (\<delta>_of x) \<ge> \<delta> \<and> 1/real_of_rat (\<epsilon>_of x) \<ge> \<epsilon> \<and>
    real (n_of x) \<ge> n \<Longrightarrow> P x) \<Longrightarrow> eventually P ?F"  (is "(\<And>x. ?prem x \<Longrightarrow> _) \<Longrightarrow> _")
    for \<delta> \<epsilon> n P
    apply (rule eventually_mono[where P="?prem" and Q="P"])
    apply (simp add:\<epsilon>_of_def case_prod_beta' \<delta>_of_def n_of_def)
     apply (intro eventually_conj eventually_prod1' eventually_prod2' 
        sequentially_inf eventually_at_right_less inv_at_right_0_inf)
    by (auto simp add:prod_filter_eq_bot)

  have exp_pos: "exp k \<le> real x \<Longrightarrow> x > 0" for k x
    using exp_gt_zero gr0I by force 

  have exp_gt_1: "exp 1 \<ge> (1::real)"
    by simp

  have 1: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x)))"
    by (auto intro!:landau_o.big_mono evt[where \<epsilon>="exp 1"] iffD2[OF ln_ge_iff] simp add:abs_ge_iff)

  have 2: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<delta>_of x)))" 
    by (auto intro!:landau_o.big_mono evt[where \<delta>="exp 1"] iffD2[OF ln_ge_iff] simp add:abs_ge_iff)

  have 3: " (\<lambda>x. 1) \<in> O[?F](\<lambda>x. ln (ln (real (n_of x))) + ln (1 / real_of_rat (\<delta>_of x)))"
    using exp_pos
    by (intro landau_sum_2 2 evt[where n="exp 1" and \<delta>="1"] ln_ge_zero  iffD2[OF ln_ge_iff], auto)
  have 4: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. 1 / (real_of_rat (\<delta>_of x))\<^sup>2)" 
    using one_le_power
    by (intro landau_o.big_mono evt[where \<delta>="1"], auto simp add:power_one_over[symmetric])

  have "(\<lambda>x. 80 * (1 / (real_of_rat (\<delta>_of x))\<^sup>2)) \<in> O[?F](\<lambda>x. 1 / (real_of_rat (\<delta>_of x))\<^sup>2)"
    by (subst landau_o.big.cmult_in_iff, auto)
  hence 5: "(\<lambda>x. real (t_of x)) \<in> O[?F](\<lambda>x. 1 / (real_of_rat (\<delta>_of x))\<^sup>2)"
    unfolding  t_of_def 
    by (intro landau_real_nat landau_ceil 4, auto)

  have "(\<lambda>x. ln (real_of_rat (\<epsilon>_of x))) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x)))"
    by (intro landau_o.big_mono evt[where \<epsilon>="1"], auto simp add:ln_div)
  hence 6: "(\<lambda>x. real (s_of x)) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x)))"
    unfolding s_of_def by (intro landau_nat_ceil 1, simp)

  have 7: " (\<lambda>x. 1) \<in> O[?F](\<lambda>x. ln (real (n_of x)))"
    using exp_pos by (auto intro!: landau_o.big_mono evt[where n="exp 1"] iffD2[OF ln_ge_iff] simp: abs_ge_iff)

  have 8:" (\<lambda>_. 1) \<in> 
    O[?F](\<lambda>x. ln (real (n_of x)) + 1 / (real_of_rat (\<delta>_of x))\<^sup>2 * (ln (ln (real (n_of x))) + ln (1 / real_of_rat (\<delta>_of x))))"
    using order_trans[OF exp_gt_1] exp_pos
    by (intro landau_sum_1 7 evt[where n="exp 1" and \<delta>="1"] ln_ge_zero  iffD2[OF ln_ge_iff] 
        mult_nonneg_nonneg add_nonneg_nonneg) auto

  have "(\<lambda>x. ln (real (s_of x) + 1)) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<epsilon>_of x)))"
    by (intro landau_ln_3 sum_in_bigo 6 1, simp)

  hence 9: "(\<lambda>x. log 2 (real (s_of x) + 1)) \<in> O[?F](g)"
    unfolding g_def by (intro landau_o.big_mult_1 8, auto simp:log_def)
  have 10: "(\<lambda>x. 1) \<in> O[?F](g)"
    unfolding g_def by (intro landau_o.big_mult_1 8 1)

  have "(\<lambda>x. ln (real (t_of x) + 1)) \<in> 
    O[?F](\<lambda>x. 1 / (real_of_rat (\<delta>_of x))\<^sup>2 * (ln (ln (real (n_of x))) + ln (1 / real_of_rat (\<delta>_of x))))"
    using 5 by (intro landau_o.big_mult_1 3 landau_ln_3 sum_in_bigo 4, simp_all)
  hence " (\<lambda>x. log 2 (real (t_of x) + 1)) \<in> 
  O[?F](\<lambda>x. ln (real (n_of x)) + 1 / (real_of_rat (\<delta>_of x))\<^sup>2 * (ln (ln (real (n_of x))) + ln (1 / real_of_rat (\<delta>_of x))))"
    using order_trans[OF exp_gt_1] exp_pos
    by (intro landau_sum_2  evt[where n="exp 1" and \<delta>="1"] ln_ge_zero  iffD2[OF ln_ge_iff] 
        mult_nonneg_nonneg add_nonneg_nonneg) (auto simp add:log_def)
  hence 11: "(\<lambda>x. log 2 (real (t_of x) + 1)) \<in> O[?F](g)"
    unfolding g_def  by (intro landau_o.big_mult_1' 1, auto)
  have " (\<lambda>x. 1) \<in> O[?F](\<lambda>x. real (n_of x))" 
    by (intro landau_o.big_mono evt[where n="1"], auto)
  hence "(\<lambda>x. ln (real (n_of x) + 21)) \<in> O[?F](\<lambda>x. ln (real (n_of x)))" 
    by (intro landau_ln_2[where a="2"] evt[where n="2"] sum_in_bigo, auto)

  hence 12: "(\<lambda>x. log 2 (real (n_of x) + 21)) \<in> O[?F](g)"
    unfolding g_def using exp_pos order_trans[OF exp_gt_1]
    by (intro landau_o.big_mult_1' 1 landau_sum_1  evt[where n="exp 1" and \<delta>="1"] 
        ln_ge_zero  iffD2[OF ln_ge_iff] mult_nonneg_nonneg add_nonneg_nonneg)  (auto simp add:log_def)

  have "(\<lambda>x. ln (1 / real_of_rat (\<delta>_of x))) \<in> O[?F](\<lambda>x. 1 / (real_of_rat (\<delta>_of x))\<^sup>2)" 
    by (intro landau_ln_3 evt[where \<delta>="1"] landau_o.big_mono) 
      (auto simp add:power_one_over[symmetric] self_le_power)
  hence " (\<lambda>x. real (nat (4*\<lceil>log 2 (1 / real_of_rat (\<delta>_of x))\<rceil>+23))) \<in> O[?F](\<lambda>x. 1 / (real_of_rat (\<delta>_of x))\<^sup>2)"
    using 4 by (auto intro!: landau_real_nat sum_in_bigo landau_ceil simp:log_def)
  hence " (\<lambda>x. ln (real (r_of x) + 1)) \<in> O[?F](\<lambda>x. 1 / (real_of_rat (\<delta>_of x))\<^sup>2)"
    unfolding r_of_def
    by (intro landau_ln_3 sum_in_bigo 4, auto)
  hence " (\<lambda>x. log 2 (real (r_of x) + 1)) \<in> 
    O[?F](\<lambda>x. (1 / (real_of_rat (\<delta>_of x))\<^sup>2) * (ln (ln (real (n_of x))) + ln (1 / real_of_rat (\<delta>_of x))))"
    by (intro landau_o.big_mult_1 3, simp add:log_def)
  hence " (\<lambda>x. log 2 (real (r_of x) + 1)) \<in> 
    O[?F](\<lambda>x. ln (real (n_of x)) + 1 / (real_of_rat (\<delta>_of x))\<^sup>2 * (ln (ln (real (n_of x))) + ln (1 / real_of_rat (\<delta>_of x))))"
    using exp_pos order_trans[OF exp_gt_1]
    by (intro landau_sum_2 evt[where n="exp 1" and \<delta>="1"] ln_ge_zero  
        iffD2[OF ln_ge_iff] add_nonneg_nonneg mult_nonneg_nonneg) (auto)
  hence 13: "(\<lambda>x. log 2 (real (r_of x) + 1)) \<in> O[?F](g)"
    unfolding g_def  by (intro landau_o.big_mult_1' 1, auto)
  have 14: "(\<lambda>x. 1) \<in> O[?F](\<lambda>x. real (n_of x))" 
    by (intro landau_o.big_mono evt[where n="1"], auto)

  have "(\<lambda>x. ln (real (n_of x) + 13)) \<in> O[?F](\<lambda>x. ln (real (n_of x)))" 
    using 14 by (intro landau_ln_2[where a="2"]  evt[where n="2"] sum_in_bigo, auto)

  hence "(\<lambda>x. ln (log 2 (real (n_of x) + 13))) \<in> O[?F](\<lambda>x. ln (ln (real (n_of x))))"
    using exp_pos by (intro landau_ln_2[where a="2"] iffD2[OF ln_ge_iff] evt[where n="exp 2"])
        (auto simp add:log_def)

  hence "(\<lambda>x. log 2 (log 2 (real (n_of x) + 13))) \<in> O[?F](\<lambda>x. ln (ln (real (n_of x))) + ln (1 / real_of_rat (\<delta>_of x)))"
    using exp_pos by (intro landau_sum_1 evt[where n="exp 1" and \<delta>="1"] ln_ge_zero  iffD2[OF ln_ge_iff])
     (auto simp add:log_def)

  moreover have  "(\<lambda>x. real (r_of x)) \<in> O[?F](\<lambda>x. ln (1 / real_of_rat (\<delta>_of x)))"
    unfolding r_of_def using 2
    by (auto intro!: landau_real_nat sum_in_bigo landau_ceil simp:log_def)
  hence "(\<lambda>x. real (r_of x)) \<in> O[?F](\<lambda>x. ln (ln (real (n_of x))) + ln (1 / real_of_rat (\<delta>_of x)))"
    using exp_pos 
    by (intro landau_sum_2 evt[where n="exp 1" and \<delta>="1"] ln_ge_zero  iffD2[OF ln_ge_iff], auto)

  ultimately have 15:" (\<lambda>x. real (t_of x) * (13 + 4 * real (r_of x) + 2 * log 2 (log 2 (real (n_of x) + 13))))
      \<in> O[?F](\<lambda>x. 1 / (real_of_rat (\<delta>_of x))\<^sup>2 * (ln (ln (real (n_of x))) + ln (1 / real_of_rat (\<delta>_of x))))"
    using 5 3 
    by (intro landau_o.mult sum_in_bigo, auto)

  have "(\<lambda>x. 5 + 2 * log 2 (21 + real (n_of x)) + real (t_of x) * (13 + 4 * real (r_of x) + 2 * log 2 (log 2 (real (n_of x) + 13))))
      \<in> O[?F](\<lambda>x. ln (real (n_of x)) + 1 / (real_of_rat (\<delta>_of x))\<^sup>2 * (ln (ln (real (n_of x))) + ln (1 / real_of_rat (\<delta>_of x))))"
  proof -
    have "\<forall>\<^sub>F x in ?F. 0 \<le> ln (real (n_of x))" 
      by (intro evt[where n="1"] ln_ge_zero, auto)
    moreover have "\<forall>\<^sub>F x in ?F. 0 \<le> 1 / (real_of_rat (\<delta>_of x))\<^sup>2 * (ln (ln (real (n_of x))) + ln (1 / real_of_rat (\<delta>_of x)))"
      using exp_pos
      by (intro evt[where n="exp 1" and \<delta>="1"] mult_nonneg_nonneg add_nonneg_nonneg 
          ln_ge_zero iffD2[OF ln_ge_iff]) auto
    moreover have " (\<lambda>x. ln (21 + real (n_of x))) \<in> O[?F](\<lambda>x. ln (real (n_of x)))" 
      using 14 by (intro landau_ln_2[where a="2"] sum_in_bigo evt[where n="2"], auto)
    hence "(\<lambda>x. 5 + 2 * log 2 (21 + real (n_of x))) \<in> O[?F](\<lambda>x. ln (real (n_of x)))"
      using 7  by (intro sum_in_bigo, auto simp add:log_def)
    ultimately show ?thesis
      using 15 by (rule landau_sum)
  qed

  hence 16: "(\<lambda>x. real (s_of x) * (5 + 2 * log 2 (21 + real (n_of x)) + real (t_of x) *
    (13 + 4 * real (r_of x) + 2 * log 2 (log 2 (real (n_of x) + 13)))))  \<in> O[?F](g)"
    unfolding g_def
    by (intro landau_o.mult 6, auto)

  have "f0_space_usage = (\<lambda>x. f0_space_usage (n_of x, \<epsilon>_of x, \<delta>_of x))"
    by (simp add:case_prod_beta' n_of_def \<epsilon>_of_def \<delta>_of_def)
  also have "... \<in>  O[?F](g)"
    using 9 10 11 12 13 16
    by (simp add:fun_cong[OF s_of_def[symmetric]] fun_cong[OF t_of_def[symmetric]] 
        fun_cong[OF r_of_def[symmetric]] Let_def) (intro sum_in_bigo, auto)
  also have "... = O[?F](?rhs)"
    by (simp add:case_prod_beta' g_def n_of_def \<epsilon>_of_def \<delta>_of_def)
  finally show ?thesis
    by simp
qed

end
