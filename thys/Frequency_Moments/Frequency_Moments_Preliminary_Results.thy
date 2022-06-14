section \<open>Preliminary Results\<close>

theory Frequency_Moments_Preliminary_Results
  imports 
    "HOL.Transcendental" 
    "HOL-Computational_Algebra.Primes"
    "HOL-Library.Extended_Real"
    "HOL-Library.Multiset"
    "HOL-Library.Sublist"
    Prefix_Free_Code_Combinators.Prefix_Free_Code_Combinators
    Bertrands_Postulate.Bertrand
begin

text \<open>This section contains various preliminary results.\<close>

lemma card_ordered_pairs:
  fixes M :: "('a ::linorder) set" 
  assumes "finite M"
  shows "2 * card {(x,y) \<in> M \<times> M. x < y} = card M * (card M - 1)"
proof -
  have a: "finite (M \<times> M)" using assms by simp

  have inj_swap: "inj (\<lambda>x. (snd x, fst x))"
    by (rule inj_onI, simp add: prod_eq_iff)

  have "2 * card {(x,y) \<in> M \<times> M. x < y} =
    card {(x,y) \<in> M \<times> M. x < y} + card ((\<lambda>x. (snd x, fst x))`{(x,y) \<in> M \<times> M. x < y})"
    by (simp add: card_image[OF inj_on_subset[OF inj_swap]])
  also have "... = card {(x,y) \<in> M \<times> M. x < y} + card {(x,y) \<in> M \<times> M. y < x}"
    by (auto intro: arg_cong[where f="card"] simp add:set_eq_iff image_iff)
  also have "... = card ({(x,y) \<in> M \<times> M. x < y} \<union> {(x,y) \<in> M \<times> M. y < x})"
    by (intro card_Un_disjoint[symmetric] a finite_subset[where B="M \<times> M"] subsetI) auto
  also have "... = card ((M \<times> M) - {(x,y) \<in> M \<times> M. x = y})"
    by (auto intro: arg_cong[where f="card"] simp add:set_eq_iff) 
  also have "... = card (M \<times> M) - card {(x,y) \<in> M \<times> M. x = y}"
    by (intro card_Diff_subset a finite_subset[where B="M \<times> M"] subsetI) auto
  also have "... = card M ^ 2 - card ((\<lambda>x. (x,x)) ` M)"
    using assms
    by (intro arg_cong2[where f="(-)"] arg_cong[where f="card"])
      (auto simp:power2_eq_square set_eq_iff image_iff)
  also have "... = card M ^ 2 - card M"
    by (intro arg_cong2[where f="(-)"] card_image inj_onI, auto)
  also have "... = card M * (card M - 1)"
    by (cases "card M \<ge> 0", auto simp:power2_eq_square algebra_simps)
  finally show ?thesis by simp
qed

lemma ereal_mono: "x \<le> y \<Longrightarrow> ereal x \<le> ereal y"
  by simp

lemma log_mono: "a > 1 \<Longrightarrow> x \<le> y \<Longrightarrow> 0 < x \<Longrightarrow> log a x \<le> log a y"
  by (subst log_le_cancel_iff, auto)

lemma abs_ge_iff: "((x::real) \<le> abs y) = (x \<le> y \<or> x \<le> -y)"
  by linarith

lemma count_list_gr_1:
  "(x \<in> set xs) = (count_list xs x \<ge> 1)"
  by (induction xs, simp, simp)

lemma count_list_append: "count_list (xs@ys) v = count_list xs v + count_list ys v"
  by (induction xs, simp, simp)

lemma count_list_lt_suffix:
  assumes "suffix a b"
  assumes "x \<in> {b ! i| i. i <  length b - length a}"
  shows  "count_list a x < count_list b x"
proof -
  have "length a \<le> length b" using assms(1) 
    by (simp add: suffix_length_le)
  hence "x \<in> set (nths b {i. i < length b - length a})"
    using assms diff_commute by (auto simp add:set_nths) 
  hence a:"x \<in> set (take (length b - length a) b)"
    by (subst (asm) lessThan_def[symmetric], simp)
  have "b = (take (length b - length a) b)@drop (length b - length a) b"
    by simp
  also have "... = (take (length b - length a) b)@a"
    using assms(1) suffix_take by auto 
  finally have b:"b = (take (length b - length a) b)@a" by simp

  have "count_list a x < 1 + count_list a x" by simp
  also have "... \<le> count_list (take (length b - length a) b) x + count_list a x"
    using a count_list_gr_1
    by (intro add_mono, fast, simp)  
  also have "... = count_list b x"
    using b count_list_append by metis
  finally show ?thesis by simp
qed

lemma suffix_drop_drop:
  assumes "x \<ge> y"
  shows "suffix (drop x a) (drop y a)"
proof -
  have "drop y a = take (x - y) (drop y a)@drop (x- y) (drop y a)"
    by (subst append_take_drop_id, simp)
  also have " ... = take (x-y) (drop y a)@drop x a"
    using assms by simp
  finally have "drop y a = take (x-y) (drop y a)@drop x a" by simp
  thus ?thesis 
    by (auto simp add:suffix_def) 
qed

lemma count_list_card: "count_list xs x = card {k. k < length xs \<and> xs ! k = x}"
proof -
  have "count_list xs x = length (filter ((=) x) xs)"
    by (induction xs, simp, simp)
  also have "... = card {k. k < length xs \<and> xs ! k = x}"
    by (subst length_filter_conv_card, metis)
  finally show ?thesis by simp
qed

lemma card_gr_1_iff:
  assumes "finite S"  "x \<in> S"  "y \<in> S"  "x \<noteq> y"
  shows "card S > 1"
  using assms card_le_Suc0_iff_eq leI by auto

lemma count_list_ge_2_iff:
  assumes "y < z"
  assumes "z < length xs"
  assumes "xs ! y = xs ! z"
  shows "count_list xs (xs ! y) > 1"
proof -
  have " 1 < card {k. k < length xs \<and> xs ! k = xs ! y}"
    using assms by (intro card_gr_1_iff[where x="y" and y="z"], auto)

  thus ?thesis
    by (simp add: count_list_card)
qed

text \<open>Results about multisets and sorting\<close>

text \<open>This is a induction scheme over the distinct elements of a multisets: 
We can represent each multiset as a sum like: 
@{text "replicate_mset n\<^sub>1 x\<^sub>1 + replicate_mset n\<^sub>2 x\<^sub>2 + ... + replicate_mset n\<^sub>k x\<^sub>k"} where the 
@{term "x\<^sub>i"} are distinct.\<close>

lemma disj_induct_mset:
  assumes "P {#}"
  assumes "\<And>n M x. P M \<Longrightarrow> \<not>(x \<in># M) \<Longrightarrow> n > 0 \<Longrightarrow> P (M + replicate_mset n x)"
  shows "P M"
proof (induction "size M" arbitrary: M rule:nat_less_induct)
  case 1
  show ?case
  proof (cases "M = {#}")
    case True
    then show ?thesis using assms by simp
  next
    case False
    then obtain x where x_def: "x \<in># M" using multiset_nonemptyE by auto
    define M1 where "M1 = M - replicate_mset (count M x) x"
    then have M_def: "M = M1 + replicate_mset (count M x) x"
      by (metis count_le_replicate_mset_subset_eq dual_order.refl subset_mset.diff_add)
    have "size M1 < size M"
      by (metis M_def x_def count_greater_zero_iff less_add_same_cancel1 size_replicate_mset size_union)
    hence "P M1" using 1 by blast
    then show "P M" 
      apply (subst M_def, rule assms(2), simp)
      by (simp add:M1_def x_def count_eq_zero_iff[symmetric])+
  qed
qed

lemma prod_mset_conv: 
  fixes f :: "'a \<Rightarrow> 'b::{comm_monoid_mult}"
  shows "prod_mset (image_mset f A) = prod (\<lambda>x. f x^(count A x)) (set_mset A)"
proof (induction A rule: disj_induct_mset)
  case 1
  then show ?case by simp
next
  case (2 n M x)
  moreover have "count M x = 0" using 2 by (simp add: count_eq_zero_iff)
  moreover have "\<And>y. y \<in> set_mset M \<Longrightarrow> y \<noteq> x" using 2 by blast
  ultimately show ?case by (simp add:algebra_simps) 
qed

text \<open>There is a version @{thm [source] sum_list_map_eq_sum_count} but it doesn't work
if the function maps into the reals.\<close>

lemma sum_list_eval:
  fixes f :: "'a \<Rightarrow> 'b::{ring,semiring_1}"
  shows "sum_list (map f xs) = (\<Sum>x \<in> set xs. of_nat (count_list xs x) * f x)"
proof -
  define M where "M = mset xs"
  have "sum_mset (image_mset f M) = (\<Sum>x \<in> set_mset M. of_nat (count M x) * f x)"
  proof (induction "M" rule:disj_induct_mset)
    case 1
    then show ?case by simp
  next
    case (2 n M x)
    have a:"\<And>y. y \<in> set_mset M \<Longrightarrow> y \<noteq> x" using 2(2) by blast
    show ?case using 2 by (simp add:a  count_eq_zero_iff[symmetric])
  qed
  moreover have "\<And>x. count_list xs x = count (mset xs) x" 
    by (induction xs, simp, simp)
  ultimately show ?thesis
    by (simp add:M_def sum_mset_sum_list[symmetric])
qed

lemma prod_list_eval:
  fixes f :: "'a \<Rightarrow> 'b::{ring,semiring_1,comm_monoid_mult}"
  shows "prod_list (map f xs) = (\<Prod>x \<in> set xs. (f x)^(count_list xs x))"
proof -
  define M where "M = mset xs"
  have "prod_mset (image_mset f M) = (\<Prod>x \<in> set_mset M. f x ^ (count M x))"
  proof (induction "M" rule:disj_induct_mset)
    case 1
    then show ?case by simp
  next
    case (2 n M x)
    have a:"\<And>y. y \<in> set_mset M \<Longrightarrow> y \<noteq> x" using 2(2) by blast
    have b:"count M x = 0" using 2 by (subst  count_eq_zero_iff) blast 
    show ?case using 2  by (simp add:a b mult.commute)
  qed
  moreover have "\<And>x. count_list xs x = count (mset xs) x" 
    by (induction xs, simp, simp)
  ultimately show ?thesis
    by (simp add:M_def prod_mset_prod_list[symmetric])
qed

lemma sorted_sorted_list_of_multiset: "sorted (sorted_list_of_multiset M)"
  by (induction M, auto simp:sorted_insort) 

lemma count_mset: "count (mset xs) a = count_list xs a"
  by (induction xs, auto)

lemma swap_filter_image: "filter_mset g (image_mset f A) = image_mset f (filter_mset (g \<circ> f) A)"
  by (induction A, auto)

lemma list_eq_iff:
  assumes "mset xs = mset ys"
  assumes "sorted xs"
  assumes "sorted ys"
  shows "xs = ys" 
  using assms properties_for_sort by blast

lemma sorted_list_of_multiset_image_commute:
  assumes "mono f"
  shows "sorted_list_of_multiset (image_mset f M) = map f (sorted_list_of_multiset M)"
proof -
  have "sorted (sorted_list_of_multiset (image_mset f M))" 
    by (simp add:sorted_sorted_list_of_multiset)
  moreover have " sorted_wrt (\<lambda>x y. f x \<le> f y) (sorted_list_of_multiset M)"
    by (rule sorted_wrt_mono_rel[where P="\<lambda>x y. x \<le> y"]) 
      (auto intro: monoD[OF assms] sorted_sorted_list_of_multiset)
  hence "sorted (map f (sorted_list_of_multiset M))"
    by (subst sorted_wrt_map)
  ultimately show ?thesis
    by (intro list_eq_iff, auto)
qed

text \<open>Results about rounding and floating point numbers\<close>

lemma round_down_ge:
  "x \<le> round_down prec x + 2 powr (-prec)"
  using round_down_correct by (simp, meson diff_diff_eq diff_eq_diff_less_eq)

lemma truncate_down_ge:
  "x \<le> truncate_down prec x + abs x * 2 powr (-prec)"
proof (cases "abs x > 0")
  case True
  have "x \<le> round_down (int prec - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>) x + 2 powr (-real_of_int(int prec - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>))"
    by (rule round_down_ge)
  also have "... \<le> truncate_down prec x + 2 powr ( \<lfloor>log 2 \<bar>x\<bar>\<rfloor>) * 2 powr (-real prec)"
    by (rule add_mono, simp_all add:powr_add[symmetric] truncate_down_def)
  also have "... \<le> truncate_down prec x + \<bar>x\<bar> * 2 powr (-real prec)"
    using True
    by (intro add_mono mult_right_mono, simp_all add:le_log_iff[symmetric])
  finally show ?thesis by simp
next
  case False
  then show ?thesis by simp
qed

lemma truncate_down_pos:
  assumes "x \<ge> 0"
  shows "x * (1 - 2 powr (-prec)) \<le> truncate_down prec x"
  by (simp add:right_diff_distrib diff_le_eq)
   (metis truncate_down_ge assms  abs_of_nonneg)

lemma truncate_down_eq:
  assumes "truncate_down r x = truncate_down r y"
  shows "abs (x-y) \<le> max (abs x) (abs y) * 2 powr (-real r)"
proof - 
  have "x - y \<le> truncate_down r x + abs x * 2 powr (-real r) - y"
    by (rule diff_right_mono, rule truncate_down_ge)
  also have "... \<le> y + abs x * 2 powr (-real r) - y"
    using truncate_down_le
    by (intro diff_right_mono add_mono, subst assms(1), simp_all)
  also have "... \<le> abs x * 2 powr (-real r)" by simp
  also have "... \<le> max (abs x) (abs y) * 2 powr (-real r)" by simp
  finally have a:"x - y \<le> max (abs x) (abs y) * 2 powr (-real r)" by simp

  have "y - x \<le> truncate_down r y + abs y * 2 powr (-real r) - x"
    by (rule diff_right_mono, rule truncate_down_ge)
  also have "... \<le> x + abs y * 2 powr (-real r) - x"
    using truncate_down_le
    by (intro diff_right_mono add_mono, subst assms(1)[symmetric], auto)
  also have "... \<le> abs y * 2 powr (-real r)" by simp
  also have "... \<le> max (abs x) (abs y) * 2 powr (-real r)" by simp
  finally have b:"y - x \<le> max (abs x) (abs y) * 2 powr (-real r)" by simp

  show ?thesis
    using abs_le_iff a b by linarith
qed

definition rat_of_float :: "float \<Rightarrow> rat" where 
  "rat_of_float f = of_int (mantissa f) * 
    (if exponent f \<ge> 0 then 2 ^ (nat (exponent f)) else 1 / 2 ^ (nat (-exponent f)))" 

lemma real_of_rat_of_float: "real_of_rat (rat_of_float x) = real_of_float x"
proof -
  have "real_of_rat (rat_of_float x) = mantissa x * (2 powr (exponent x))"
    by (simp add:rat_of_float_def of_rat_mult of_rat_divide of_rat_power powr_realpow[symmetric] powr_minus_divide)
  also have "... = real_of_float x"
    using mantissa_exponent by simp
  finally show ?thesis by simp 
qed

lemma log_est: "log 2 (real n + 1) \<le> n"
proof -
  have "1 + real n = real (n + 1)"
    by simp
  also have "... \<le> real (2 ^ n)"
    by (intro of_nat_mono suc_n_le_2_pow_n)
  also have "... = 2 powr (real n)"
    by (simp add:powr_realpow)
  finally have "1 + real n \<le> 2 powr (real n)"
    by simp
  thus ?thesis
    by (simp add: Transcendental.log_le_iff)
qed

lemma truncate_mantissa_bound:
  "abs (\<lfloor>x * 2 powr (real r - real_of_int \<lfloor>log 2 \<bar>x\<bar>\<rfloor>)\<rfloor>) \<le> 2 ^ (r+1)" (is "?lhs \<le> _")
proof -
  define q where "q = \<lfloor>x * 2 powr (real r - real_of_int (\<lfloor>log 2 \<bar>x\<bar>\<rfloor>))\<rfloor>"

  have "abs q \<le> 2 ^ (r + 1)" if a:"x > 0"
  proof -
    have "abs q = q"
      using a by (intro abs_of_nonneg, simp add:q_def)
    also have "... \<le> x * 2 powr (real r - real_of_int \<lfloor>log 2 \<bar>x\<bar>\<rfloor>)"
      unfolding q_def using of_int_floor_le by blast
    also have "... = x * 2 powr real_of_int (int r - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>)"
      by auto
    also have "... = 2 powr (log 2 x + real_of_int (int r - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>))"
      using a by (simp add:powr_add)
    also have "... \<le> 2 powr (real r + 1)"
      using a by (intro powr_mono, linarith+) 
    also have "... = 2 ^ (r+1)"
      by (subst powr_realpow[symmetric], simp_all add:add.commute)
    finally show "abs q \<le> 2 ^ (r+1)" 
      by (metis of_int_le_iff of_int_numeral of_int_power)
  qed
    
  moreover have "abs q \<le> (2 ^ (r + 1))" if a: "x < 0"
  proof -
    have "-(2 ^ (r+1) + 1) = -(2 powr (real r + 1)+1)"
      by (subst powr_realpow[symmetric], simp_all add: add.commute)
    also have  "... < -(2 powr (log 2 (- x) + (r - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>)) + 1)"
      using a by (simp, linarith)
    also have "... = x * 2 powr (r - \<lfloor>log 2 \<bar>x\<bar>\<rfloor>) - 1"
      using a by (simp add:powr_add)
    also have "... \<le> q"
      by (simp add:q_def)
    also have "... = - abs q"
      using a
      by (subst abs_of_neg, simp_all add: mult_pos_neg2 q_def)
    finally have "-(2 ^ (r+1)+1) < - abs q" using of_int_less_iff by fastforce
    hence "-(2 ^ (r+1)) \<le> - abs q" by linarith
    thus "abs q \<le> 2^(r+1)" by linarith
  qed

  moreover have "x = 0 \<Longrightarrow> abs q \<le> 2^(r+1)"
    by (simp add:q_def)
  ultimately have "abs q \<le> 2^(r+1)"
    by fastforce
  thus ?thesis using q_def by blast
qed

lemma truncate_float_bit_count:
  "bit_count (F\<^sub>e (float_of (truncate_down r x))) \<le> 10 + 4 * real r + 2*log 2 (2 + \<bar>log 2 \<bar>x\<bar>\<bar>)" 
  (is "?lhs \<le> ?rhs")
proof -
  define m where "m = \<lfloor>x * 2 powr (real r - real_of_int \<lfloor>log 2 \<bar>x\<bar>\<rfloor>)\<rfloor>"
  define e where "e = \<lfloor>log 2 \<bar>x\<bar>\<rfloor> - int r"

  have a: "(real_of_int \<lfloor>log 2 \<bar>x\<bar>\<rfloor> - real r) = e"
    by (simp add:e_def)
  have "abs m + 2 \<le> 2 ^ (r + 1) + 2^1"
    using truncate_mantissa_bound
    by (intro add_mono, simp_all add:m_def)
  also have "... \<le> 2 ^ (r+2)"
    by simp
  finally have b:"abs m + 2 \<le> 2 ^ (r+2)" by simp
  hence "real_of_int (\<bar>m\<bar> + 2) \<le> real_of_int (4 * 2 ^ r)" 
    by (subst of_int_le_iff, simp)
  hence "\<bar>real_of_int m\<bar> + 2 \<le> 4 * 2 ^ r" 
    by simp
  hence c:"log 2 (real_of_int (\<bar>m\<bar> + 2)) \<le> r+2"
    by (simp add: Transcendental.log_le_iff powr_add powr_realpow)

  have "real_of_int (abs e + 1) \<le> real_of_int \<bar>\<lfloor>log 2 \<bar>x\<bar>\<rfloor>\<bar> +  real_of_int r + 1"
    by (simp add:e_def)
  also have "... \<le> 1 + abs (log 2 (abs x)) + real_of_int r + 1"
    by (simp add:abs_le_iff, linarith)
  also have "... \<le> (real_of_int r+ 1) * (2 + abs (log 2 (abs x)))"
    by (simp add:distrib_left distrib_right)
  finally have d:"real_of_int (abs e + 1) \<le> (real_of_int r+ 1) * (2 + abs (log 2 (abs x)))" by simp

  have "log 2 (real_of_int (abs e + 1)) \<le> log 2 (real_of_int r + 1) + log 2 (2 + abs (log 2 (abs x)))"
    using d by (simp add: log_mult[symmetric])
  also have "... \<le> r + log 2 (2 + abs (log 2 (abs x)))"
    using log_est by (intro add_mono, simp_all add:add.commute)
  finally have e: "log 2 (real_of_int (abs e + 1)) \<le> r + log 2 (2 + abs (log 2 (abs x)))" by simp

  have "?lhs =  bit_count (F\<^sub>e (float_of (real_of_int m * 2 powr real_of_int e)))"
    by (simp add:truncate_down_def round_down_def m_def[symmetric] a)
  also have "... \<le> ereal (6 + (2 * log 2 (real_of_int (\<bar>m\<bar> + 2)) + 2 * log 2 (real_of_int (\<bar>e\<bar> + 1))))"
    using float_bit_count_2 by simp
  also have "... \<le> ereal (6 + (2 * real (r+2) + 2 * (r + log 2 (2 + abs (log 2 (abs x))))))"
    using c e
    by (subst ereal_less_eq, intro add_mono mult_left_mono, linarith+) 
  also have "... = ?rhs" by simp
  finally show ?thesis by simp
qed

definition prime_above :: "nat \<Rightarrow> nat" 
  where "prime_above n = (SOME x. x \<in> {n..(2*n+2)} \<and> prime x)"

text \<open>The term @{term"prime_above n"} returns a prime between @{term "n::nat"} and @{term "2*(n::nat)+2"}.
Because of Bertrand's postulate there always is such a value. In a refinement of the algorithms, it may make sense to
replace this with an algorithm, that finds such a prime exactly or approximately.

The definition is intentionally inexact, to allow refinement with various algorithms, without modifying the
high-level mathematical correctness proof.\<close>

lemma ex_subset:
  assumes "\<exists>x \<in> A. P x"
  assumes "A \<subseteq> B"
  shows "\<exists>x \<in> B. P x"
  using assms by auto

lemma
  shows prime_above_prime: "prime (prime_above n)"
  and prime_above_range: "prime_above n \<in> {n..(2*n+2)}"
proof -
  define r where "r = (\<lambda>x. x \<in> {n..(2*n+2)} \<and> prime x)"
  have "\<exists>x. r x"
  proof (cases "n>2")
    case True
    hence "n-1 > 1" by simp
    hence "\<exists>x \<in> {(n-1)<..<(2*(n-1))}. prime x"
      using bertrand by simp
    moreover have "{n - 1<..<2 * (n - 1)} \<subseteq> {n..2 * n + 2}"
      by (intro subsetI, auto) 
    ultimately have "\<exists>x \<in> {n..(2*n+2)}. prime x"
      by (rule ex_subset)
    then show ?thesis by (simp add:r_def Bex_def)
  next
    case False
    hence "2 \<in> {n..(2*n+2)}" 
      by simp
    moreover have "prime (2::nat)" 
      using two_is_prime_nat by blast
    ultimately have "r 2"
      using r_def by simp
    then show ?thesis by (rule exI)
  qed
  moreover have "prime_above n = (SOME x. r x)"
    by (simp add:prime_above_def r_def)
  ultimately have a:"r (prime_above n)"
    using someI_ex by metis
  show "prime (prime_above n)"
    using a unfolding r_def by blast
  show "prime_above n \<in> {n..(2*n+2)}"
    using a unfolding r_def by blast
qed

lemma prime_above_min:  "prime_above n \<ge> 2"
  using prime_above_prime 
  by (simp add: prime_ge_2_nat)

lemma prime_above_lower_bound: "prime_above n \<ge> n"
  using prime_above_range
  by simp

lemma prime_above_upper_bound: "prime_above n \<le> 2*n+2"
  using prime_above_range
  by simp

end
