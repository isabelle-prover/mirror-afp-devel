section \<open>Intervals are Borel measurable\<close>

theory Median
  imports "HOL-Probability.Hoeffding" "HOL-Library.Multiset"
begin

text \<open>This section contains a proof that intervals are Borel measurable, where an interval is
defined as a convex subset of linearly ordered space, more precisely, a set is an interval, if 
for each triple of points $x < y < z$: If $x$ and $z$ are in the set so is $y$.
This includes ordinary intervals like @{term "{a..b}"}, @{term "{a<..<b}"} but also for example
@{term [show_types] "{(x::rat). x * x < 2}"} which cannot be expressed in the standard notation.

In the @{theory "HOL-Analysis.Borel_Space"} there are proofs for the measurability of each specific
type of interval, but those unfortunately do not help if we want to express the result about the
median bound for arbitrary types of intervals.\<close>

definition interval :: "('a :: linorder) set \<Rightarrow> bool" where
  "interval I = (\<forall>x y z. x \<in> I \<longrightarrow> z \<in> I \<longrightarrow> x \<le> y \<longrightarrow> y \<le> z \<longrightarrow> y \<in> I)"

definition up_ray :: "('a :: linorder) set \<Rightarrow> bool" where
  "up_ray I = (\<forall>x y. x \<in> I \<longrightarrow> x \<le> y \<longrightarrow> y \<in> I)"

lemma up_ray_borel:
  assumes "up_ray (I :: (('a :: linorder_topology) set))"
  shows "I \<in> borel"
proof (cases "closed I")
  case True
  then show ?thesis using borel_closed by blast
next
  case False
  hence b:"\<not> closed I" by blast

  have "open I"
  proof (rule Topological_Spaces.openI)
    fix x
    assume c:"x \<in> I"
    show "\<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> I"
    proof (cases "\<exists>y. y < x \<and> y \<in> I")
      case True
      then obtain y where a:"y < x \<and> y \<in> I" by blast
      have "open {y<..}" by simp
      moreover have "x \<in> {y<..}" using a by simp
      moreover have "{y<..} \<subseteq> I"
        apply (rule subsetI)
        using a assms(1) apply (simp add: up_ray_def) 
        by (metis less_le_not_le)
      ultimately show ?thesis by blast
    next
      case False
      hence "I \<subseteq> {x..}" using linorder_not_less by auto
      moreover have "{x..} \<subseteq> I"
        using c assms(1)  apply (simp add: up_ray_def) 
        by blast
      ultimately have "I = {x..}" 
        by (rule order_antisym)
      moreover have "closed {x..}" by simp
      ultimately have "False" using b by auto
      then show ?thesis by simp
    qed
  qed
  then show ?thesis by simp
qed

definition down_ray :: "('a :: linorder) set \<Rightarrow> bool" where
  "down_ray I = (\<forall>x y. y \<in> I \<longrightarrow> x \<le> y \<longrightarrow> x \<in> I)"

lemma down_ray_borel:
  assumes "down_ray (I :: (('a :: linorder_topology) set))"
  shows "I \<in> borel"
proof -
  have "up_ray (-I)" using assms 
    by (simp add: up_ray_def down_ray_def, blast)
  hence "(-I) \<in> borel" using up_ray_borel by blast
  thus "I \<in> borel" 
    by (metis borel_comp double_complement)
qed

text \<open>Main result of this section:\<close>

lemma interval_borel:
  assumes "interval (I :: (('a :: linorder_topology) set))"
  shows "I \<in> borel"
proof (cases "I = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain x where a:"x \<in> I" by blast
  have "\<And>y z. y \<in> I \<union> {x..} \<Longrightarrow> y \<le> z \<Longrightarrow> z \<in> I \<union> {x..}" 
    by (metis assms a interval_def  IntE UnE Un_Int_eq(1) Un_Int_eq(2) atLeast_iff nle_le order.trans)
  hence "up_ray (I \<union> {x..})"
    using up_ray_def by blast
  hence b:"I \<union> {x..} \<in> borel" 
    using up_ray_borel by blast

  have "\<And>y z. y \<in> I \<union> {..x} \<Longrightarrow> z \<le> y \<Longrightarrow> z \<in> I \<union> {..x}" 
    by (metis assms a interval_def UnE UnI1 UnI2 atMost_iff dual_order.trans linorder_le_cases)
  hence "down_ray (I \<union> {..x})"
    using down_ray_def by blast
  hence c:"I \<union> {..x} \<in> borel"
    using down_ray_borel by blast

  have "I = (I \<union> {x..}) \<inter> (I \<union> {..x})"
    using a by fastforce    

  then show ?thesis using b c
    by (metis sets.Int)
qed

section \<open>Order statistics are Borel measurable\<close>

text \<open>This section contains a proof that order statistics of Borel measurable random variables are
themselves Borel measurable.

The proof relies on the existence of branch-free comparison-sort algorithms. Given a sequence length
these algorithms perform compare-swap operations on predefined pairs of positions. In particular the
result of a comparison does not affect future operations. An example for a branch-free comparison
sort algorithm is shell-sort and also bubble-sort without the early exit.

The advantage of using such a comparison-sort algorithm is that it can be lifted to work on random
variables, where the result of a comparison-swap operation on two random variables @{term"X"} and
@{term"Y"} can be represented as the expressions @{term "\<lambda>\<omega>. min (X \<omega>) (Y \<omega>)"} and
@{term "\<lambda>\<omega>. max (X \<omega>) (Y \<omega>)"}.

Because taking the point-wise minimum (resp. maximum) of two random variables is still
Borel measurable, and because the entire sorting operation can be represented using such
compare-swap operations, we can show that all order statistics are Borel measuable.\<close>

fun sort_primitive where
  "sort_primitive i j f k = (if k = i then min (f i) (f j) else (if k = j then max (f i) (f j) else f k))"

fun sort_map where
  "sort_map f n = fold id [sort_primitive j i. i <- [0..<n], j <- [0..<i]] f"

lemma sort_map_ind:
  "sort_map f (Suc n) = fold id [sort_primitive j n. j <- [0..<n]] (sort_map f n)"
  by simp

lemma sort_map_strict_mono:
  fixes f :: "nat \<Rightarrow> 'b :: linorder"
  shows "j < n \<Longrightarrow> i < j \<Longrightarrow> sort_map f n i \<le> sort_map f n j"
proof (induction n arbitrary: i j)
  case 0
  then show ?case by simp
next
  case (Suc n)
  define g where "g = (\<lambda>k. fold id [sort_primitive j n. j <- [0..<k]] (sort_map f n))"
  define k where "k = n"
  have a:"(\<forall>i j. j < n \<longrightarrow> i < j \<longrightarrow> g k i \<le> g k j) \<and> (\<forall>l. l < k \<longrightarrow> g k l \<le> g k n)"
  proof (induction k)
    case 0
    then show ?case using Suc by (simp add:g_def del:sort_map.simps)
  next
    case (Suc k)
    have "g (Suc k) = sort_primitive k n (g k)" 
      by (simp add:g_def)
    then show ?case using Suc
      apply (cases "g k k \<le> g k n")
       apply (simp add:min_def max_def)
       using less_antisym apply blast
      apply (cases "g k n \<le> g k k")
       apply (simp add:min_def max_def)
       apply (metis less_antisym max.coboundedI2 max.orderE)
      by simp
  qed

  hence "\<And>i j. j < Suc n \<Longrightarrow> i < j \<Longrightarrow> g n i \<le> g n j"
    apply (simp add:k_def) using less_antisym by blast
  moreover have "sort_map f (Suc n) = g n" 
    by (simp add:sort_map_ind g_def del:sort_map.simps)
  ultimately show ?case
    apply (simp del:sort_map.simps)
    using Suc by blast
qed

lemma sort_map_mono:
  fixes f :: "nat \<Rightarrow> 'b :: linorder"
  shows "j < n \<Longrightarrow> i \<le> j \<Longrightarrow> sort_map f n i \<le> sort_map f n j"
  by (metis sort_map_strict_mono eq_iff le_imp_less_or_eq)

lemma sort_map_perm:
  fixes f :: "nat \<Rightarrow> 'b :: linorder"
  shows "image_mset (sort_map f n) (mset [0..<n]) = image_mset f (mset [0..<n])"
proof -
  define is_swap where "is_swap = (\<lambda>(ts :: ((nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'b)). \<exists>i < n. \<exists>j < n. ts = sort_primitive i j)"
  define t :: "((nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'b) list" 
    where "t = [sort_primitive j i. i <- [0..<n], j <- [0..<i]]"

  have a: "\<And>x f. is_swap x \<Longrightarrow> image_mset (x f) (mset_set {0..<n}) = image_mset f (mset_set {0..<n})"
  proof -
    fix x
    fix f :: "nat \<Rightarrow> 'b :: linorder"
    assume "is_swap x"
    then obtain i j where x_def: "x = sort_primitive i j" and i_bound: "i < n" and j_bound:"j < n" 
      using is_swap_def by blast
    define inv where "inv = mset_set {k. k < n \<and> k \<noteq> i \<and> k \<noteq> j}"
    have b:"{0..<n} = {k. k < n \<and> k \<noteq> i \<and> k \<noteq> j} \<union> {i,j}"
      apply (rule order_antisym, rule subsetI, simp, blast, rule subsetI, simp)
      using i_bound j_bound by meson
    have c:"\<And>k. k \<in># inv \<Longrightarrow> (x f) k = f k" 
      by (simp add:x_def inv_def)
    have "image_mset (x f) inv = image_mset f inv"
      apply (rule multiset_eqI)
      using c multiset.map_cong0 by force
    moreover have "image_mset (x f) (mset_set {i,j}) = image_mset f (mset_set {i,j})"
      apply (cases "i = j")
      by (simp add:x_def max_def min_def)+
    moreover have "mset_set {0..<n} = inv + mset_set {i,j}"
      by (simp only:inv_def b, rule mset_set_Union, simp, simp, simp) 
    ultimately show "image_mset (x f) (mset_set {0..<n}) = image_mset f (mset_set {0..<n})"
      by simp
  qed

  have "(\<forall>x \<in> set t. is_swap x) \<Longrightarrow> image_mset (fold id t f) (mset [0..<n]) = image_mset f (mset [0..<n])"
    by (induction t arbitrary:f, simp, simp add:a) 
  moreover have "\<And>x. x \<in> set t \<Longrightarrow> is_swap x" 
    apply (simp add:t_def is_swap_def) 
    by (meson atLeastLessThan_iff imageE less_imp_le less_le_trans)  
  ultimately have "image_mset (fold id t f) (mset [0..<n]) = image_mset f (mset [0..<n])" by blast
  then show ?thesis by (simp add:t_def)
qed

lemma list_eq_iff:
  assumes "mset xs = mset ys"
  assumes "sorted xs"
  assumes "sorted ys"
  shows "xs = ys" 
  using assms properties_for_sort by blast

lemma sort_map_eq_sort:
  fixes f :: "nat \<Rightarrow> ('b :: linorder)"
  shows "map (sort_map f n) [0..<n] = sort (map f [0..<n])" (is "?A = ?B")
proof -
  have "mset ?A = mset ?B"
    using sort_map_perm[where f="f" and n="n"]
    by (simp del:sort_map.simps)
  moreover have "sorted ?B"
    by simp
  moreover have "sorted ?A"
    apply (subst sorted_wrt_iff_nth_less)
    apply (simp del:sort_map.simps)
    by (metis sort_map_mono nat_less_le)
  ultimately show "?A = ?B" 
    using list_eq_iff by blast
qed

lemma order_statistics_measurable_aux: 
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> ('b :: {linorder_topology, second_countable_topology})"
  assumes "n \<ge> 1" 
  assumes "j < n"
  assumes "\<And>i. i < n \<Longrightarrow> X i \<in> measurable M borel"
  shows "(\<lambda>x. (sort_map (\<lambda>i. X i x) n) j) \<in> measurable M borel"
proof -
  have n_ge_0:"n > 0" using assms by simp
  define is_swap where "is_swap = (\<lambda>(ts :: ((nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'b)). \<exists>i < n. \<exists>j < n. ts = sort_primitive i j)"
  define t :: "((nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'b) list" 
    where "t = [sort_primitive j i. i <- [0..<n], j <- [0..<i]]"

  define meas_ptw :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> bool"
    where "meas_ptw = (\<lambda>f. (\<forall>k. k < n \<longrightarrow> f k \<in> borel_measurable M))"

  have ind_step:
    "\<And>x (g :: nat \<Rightarrow> 'a \<Rightarrow> 'b). meas_ptw g \<Longrightarrow> is_swap x \<Longrightarrow> meas_ptw (\<lambda>k \<omega>. x (\<lambda>i. g i \<omega>) k)"
  proof -
    fix x g
    assume "meas_ptw g"
    hence a:"\<And>k. k < n \<Longrightarrow> g k \<in> borel_measurable M" by (simp add:meas_ptw_def)
    assume "is_swap x"
    then obtain i j where x_def:"x=sort_primitive i j" and i_le:"i < n" and j_le:"j < n"
      by (simp add:is_swap_def, blast)
    have "\<And>k. k < n \<Longrightarrow> (\<lambda>\<omega>. x (\<lambda>i. g i \<omega>) k) \<in> borel_measurable M"
    proof -
      fix k
      assume "k < n"
      thus " (\<lambda>\<omega>. x (\<lambda>i. g i \<omega>) k) \<in> borel_measurable M"
        apply (simp add:x_def)
        apply (cases "k = i", simp)
        using a i_le j_le borel_measurable_min apply blast
        apply (cases "k = j", simp)
        using a i_le j_le borel_measurable_max apply blast
        using a by simp
    qed
    thus "meas_ptw (\<lambda>k \<omega>. x (\<lambda>i. g i \<omega>) k)" 
      by (simp add:meas_ptw_def)
  qed

  have "(\<forall>x \<in> set t. is_swap x) \<Longrightarrow> meas_ptw (\<lambda> k \<omega>. (fold id t (\<lambda>k. X k \<omega>)) k)"
  proof (induction t rule:rev_induct)
    case Nil
    then show ?case using assms by (simp add:meas_ptw_def)
  next
    case (snoc x xs)
    have a:"meas_ptw (\<lambda>k \<omega>. fold (\<lambda>a. a) xs (\<lambda>k. X k \<omega>) k)" using snoc by simp
    have b:"is_swap x" using snoc by simp
    show ?case using ind_step[OF a b] by simp
  qed
  moreover have "\<And>x. x \<in> set t \<Longrightarrow> is_swap x" 
    apply (simp add:t_def is_swap_def) 
    by (meson atLeastLessThan_iff imageE less_imp_le less_le_trans)  
  ultimately show ?thesis using assms
    by (simp add:t_def[symmetric] meas_ptw_def)
qed

text \<open>Main results of this section:\<close>

lemma order_statistics_measurable:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> ('b :: {linorder_topology, second_countable_topology})"
  assumes "n \<ge> 1" 
  assumes "j < n"
  assumes "\<And>i. i < n \<Longrightarrow> X i \<in> measurable M borel"
  shows "(\<lambda>x. (sort (map (\<lambda>i. X i x) [0..<n])) ! j) \<in> measurable M borel"
  apply (subst sort_map_eq_sort[symmetric])
  using assms by (simp add:order_statistics_measurable_aux del:sort_map.simps)

definition median where
  "median n f =  sort (map f [0..<n]) ! (n div 2)"

lemma median_measurable:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> ('b :: {linorder_topology, second_countable_topology})"
  assumes "n \<ge> 1" 
  assumes "\<And>i. i < n \<Longrightarrow> X i \<in> measurable M borel"
  shows "(\<lambda>x. median n (\<lambda>i. X i x)) \<in> measurable M borel"
  apply (simp add:median_def)
  apply (rule order_statistics_measurable[OF assms(1) _ assms(2)])
  using assms(1) by force+

section \<open>The Median Method\<close>

text \<open>This section contains the proof for the probability that the median of independent random
variables will be in an interval with high probability if the individual variables are in the
same interval with probability larger than $\frac{1}{2}$.

The proof starts with the elementary observation that the median of a seqeuence with $n$ elements
is in an interval $I$ if at least half of them are in $I$. This works because after sorting the
sequence the elements that will be in the interval must necessarily form a consecutive subsequence,
if its length is larger than $\frac{n}{2}$ the median must be in it.

The remainder follows the proof in \cite[\textsection 2.1]{alon1999} using the Hoeffding inequality
to estimate the probability that at least half of the sequence elements will be in the interval $I$.\<close>

lemma interval_rule:
  assumes "interval I"
  assumes "a \<le> x" "x \<le> b"
  assumes "a \<in> I"
  assumes "b \<in> I"
  shows "x \<in> I"
  using assms(1) apply (simp add:interval_def)
  using assms by blast

lemma sorted_int:
  assumes "interval I"
  assumes "sorted xs"
  assumes "k < length xs" "i \<le> j" "j \<le> k "
  assumes "xs ! i \<in> I" "xs ! k \<in> I"
  shows "xs ! j \<in> I"
  apply (rule interval_rule[where a="xs ! i" and b="xs ! k"])
  using assms by (simp add: sorted_nth_mono)+

lemma mid_in_interval:
  assumes "2*length (filter (\<lambda>x. x \<in> I) xs) > length xs"
  assumes "interval I"
  assumes "sorted xs"
  shows "xs ! (length xs div 2) \<in> I"
proof -
  have "length (filter (\<lambda>x. x \<in> I) xs) > 0"  using assms(1) by linarith
  then obtain v where v_1: "v < length xs" and v_2: "xs ! v \<in> I" 
    by (metis filter_False in_set_conv_nth length_greater_0_conv)

  define J where "J = {k. k < length xs \<and> xs ! k \<in> I}"

  have card_J_min: "2*card J > length xs"
    using assms(1) by (simp add:J_def length_filter_conv_card)

  consider
    (a) "xs ! (length xs div 2) \<in> I" |
    (b) "xs ! (length xs div 2) \<notin> I \<and> v > (length xs div 2)" |
    (c) "xs ! (length xs div 2) \<notin> I \<and> v < (length xs div 2)"
    by (metis linorder_cases v_2)
  thus ?thesis
  proof (cases)
    case a
    then show ?thesis by simp
  next
    case b
    have p:"\<And>k. k \<le> length xs div 2 \<Longrightarrow> xs ! k \<notin> I"
      using b v_2 sorted_int[OF assms(2) assms(3) v_1, where j="length xs div 2"] apply simp by blast
    have "card J \<le> card {Suc (length xs div 2)..<length xs}"
      apply (rule card_mono, simp)
      apply (rule subsetI, simp add:J_def not_less_eq_eq[symmetric])
      using p by metis
    hence "card J \<le> length xs - (Suc (length xs div 2))"
      using card_atLeastLessThan by metis
    hence "length xs \<le> 2*( length xs - (Suc (length xs div 2)))"
      using card_J_min by linarith
    hence "False"
      apply (simp add:nat_distrib)
      apply (subst (asm) le_diff_conv2) using b v_1 apply linarith
      by simp
    then show ?thesis by simp
  next
    case c
    have p:"\<And>k. k \<ge> length xs div 2 \<Longrightarrow> k < length xs \<Longrightarrow> xs ! k \<notin> I"
      using c v_1 v_2 sorted_int[OF assms(2) assms(3), where i ="v" and j="length xs div 2"] apply simp by blast
    have "card J \<le> card {0..<(length xs div 2)}"
      apply (rule card_mono, simp)
      apply (rule subsetI, simp add:J_def not_less_eq_eq[symmetric])
      using p linorder_le_less_linear by blast
    hence "card J \<le> (length xs div 2)"
      using card_atLeastLessThan by simp
    then show ?thesis using card_J_min by linarith
  qed
qed

lemma median_est:
  assumes "interval I"
  assumes "2*card {k. k < n \<and> f k \<in> I} > n"
  shows "median n f \<in> I"
proof -
  have a:"{k. k < n \<and> f k \<in> I} = {i. i < n \<and> map f [0..<n] ! i \<in> I}"
    apply (rule order_antisym, rule subsetI, simp)
    by (rule subsetI, simp, metis add_0 diff_zero nth_map_upt)

  show ?thesis
    apply (simp add:median_def)
    apply (rule mid_in_interval[where I="I" and xs="sort (map f [0..<n])", simplified])
     using assms a apply (simp add:filter_sort comp_def length_filter_conv_card)
    by (simp add:assms)
qed

text \<open>Main results of this section:\<close>

theorem (in prob_space) median_bound:
  fixes n :: nat
  fixes I :: "('b :: {linorder_topology, second_countable_topology}) set"
  assumes "interval I"
  assumes "\<alpha> > 0"
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "indep_vars (\<lambda>_. borel) X {0..<n}"
  assumes "n \<ge> - ln \<epsilon> / (2 * \<alpha>\<^sup>2)"
  assumes "\<And>i. i < n \<Longrightarrow> \<P>(\<omega> in M. X i \<omega> \<in> I) \<ge> 1/2+\<alpha>" 
  shows "\<P>(\<omega> in M. median n (\<lambda>i. X i \<omega>) \<in> I) \<ge> 1-\<epsilon>"
proof -
  define Y :: "nat \<Rightarrow> 'a \<Rightarrow> real" where "Y = (\<lambda>i. indicator I \<circ> (X i))"

  define t where "t = (\<Sum>i = 0..<n. expectation (Y i)) - n/2"
  have "0 < -ln \<epsilon> / (2 * \<alpha>\<^sup>2)"  
    apply (rule divide_pos_pos)
     apply (simp, subst ln_less_zero_iff)
    using assms by auto
  also have "... \<le> real n" using assms by simp
  finally have "real n > 0" by simp
  hence n_ge_1:"n \<ge> 1" by linarith
  hence n_ge_0:"n > 0" by simp

  have ind_comp: "\<And>i. indicator I \<circ> (X i) = indicator {\<omega>. X i \<omega> \<in> I}"
    by (rule ext, simp add:indicator_def comp_def)

  have "\<alpha> * n \<le> (\<Sum> i =0..<n. 1/2 + \<alpha>) - n/2"
    by (simp add:algebra_simps)
  also have "... \<le> (\<Sum> i = 0..<n. expectation (Y i)) - n/2"
    apply (rule diff_right_mono, rule sum_mono)
    using assms(6) by (simp add:Y_def ind_comp Collect_conj_eq inf_commute)
  also have "... = t" by (simp add:t_def)
  finally have t_ge_a: "t \<ge> \<alpha> * n" by simp

  have d: "0 \<le> \<alpha> * n" 
    apply (rule mult_nonneg_nonneg)
    using assms(2) n_ge_0 by simp+
  also have "... \<le> t" using t_ge_a by simp
  finally have t_ge_0: "t \<ge> 0" by simp

  have  "(\<alpha> * n)\<^sup>2 \<le> t\<^sup>2" using t_ge_a d power_mono by blast
  hence t_ge_a_sq: "\<alpha>\<^sup>2 * real n * real n \<le> t\<^sup>2"
    by (simp add:algebra_simps power2_eq_square)

  have Y_indep: "indep_vars (\<lambda>_. borel) Y {0..<n}"
    apply (subst Y_def)
    apply (rule indep_vars_compose[where M'="(\<lambda>_. borel)", OF assms(4)])
    using interval_borel[OF assms(1)] by simp
 
  hence b:"Hoeffding_ineq M {0..<n} Y (\<lambda>i. 0) (\<lambda>i. 1)" 
    apply (simp add:Hoeffding_ineq_def indep_interval_bounded_random_variables_def)
    by (simp add:prob_space_axioms indep_interval_bounded_random_variables_axioms_def Y_def Y_indep)

  have c: "\<And>\<omega>. (\<Sum>i = 0..<n. Y i \<omega>) > n/2 \<Longrightarrow> median n (\<lambda>i. X i \<omega>) \<in> I"
  proof -
    fix \<omega>
    assume "(\<Sum>i = 0..<n. Y i \<omega>) > n/2"
    hence "n < 2 * card ({0..<n} \<inter> {i. X i \<omega> \<in> I})" 
      by (simp add:Y_def indicator_def) 
    also have "... = 2 * card {i. i < n \<and> X i \<omega> \<in> I}"
      apply (simp, rule arg_cong[where f="card"])
      by (rule order_antisym, rule subsetI, simp, rule subsetI, simp)
    finally have "2 * card {i. i < n \<and> X i \<omega> \<in> I} > n" by simp
    thus "median n (\<lambda>i. X i \<omega>) \<in> I"
      using median_est[OF assms(1)] by simp
  qed

  have "1 - \<epsilon> \<le> 1- exp (- (2 * \<alpha>\<^sup>2 * real n))" 
    apply (simp, subst ln_ge_iff[symmetric])
    using assms(3) apply simp
    using assms(5) apply (subst (asm) pos_divide_le_eq) 
     apply (simp add: assms(2) power2_eq_square)
    by (simp add: mult_of_nat_commute)
  also have "... \<le> 1- exp (- (2 * t\<^sup>2 / real n))" 
    apply simp
    apply (subst pos_le_divide_eq) using n_ge_0 apply simp
    using t_ge_a_sq by linarith
  also have "... \<le> 1 - \<P>(\<omega> in M. (\<Sum>i = 0..<n. Y i \<omega>) \<le> n/2)" 
    using Hoeffding_ineq.Hoeffding_ineq_le[OF b, where \<epsilon>="t", simplified] n_ge_0 t_ge_0
    by (simp add:t_def) 
  also have "... = \<P>(\<omega> in M. (\<Sum>i = 0..<n. Y i \<omega>) > n/2)" 
    apply (subst prob_compl[symmetric])
     apply measurable
     using Y_indep apply (simp add:indep_vars_def)
    apply (rule arg_cong2[where f="measure"], simp)
    by (rule order_antisym, rule subsetI, simp add:not_le, rule subsetI, simp add:not_le)
  also have "... \<le> \<P>(\<omega> in M. median n (\<lambda>i. X i \<omega>) \<in> I)"
    apply (rule finite_measure_mono)
     apply (rule subsetI) using c apply simp 
    using interval_borel[OF assms(1)] apply measurable
    apply (rule median_measurable[OF n_ge_1])
    using assms(4) by (simp add:indep_vars_def)
  finally show ?thesis by simp
qed

text \<open>This is a specialization of the above to closed real intervals.\<close>

corollary (in prob_space) median_bound_1:
  assumes "\<alpha> > 0"
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "indep_vars (\<lambda>_. borel) X {0..<n}"
  assumes "n \<ge> - ln \<epsilon> / (2 * \<alpha>\<^sup>2)"
  assumes "\<forall>i \<in> {0..<n}. \<P>(\<omega> in M. X i \<omega> \<in> ({a..b} :: real set)) \<ge> 1/2+\<alpha>" 
  shows "\<P>(\<omega> in M. median n (\<lambda>i. X i \<omega>) \<in> {a..b}) \<ge> 1-\<epsilon>" 
  apply (rule median_bound[OF _ assms(1) assms(2) assms(3) assms(4)])
   apply (simp add:interval_def)
  using assms(5) by auto

text \<open>This is a specialization of the above, where $\alpha = \frac{1}{6}$ and the interval is described
using a mid point @{term "\<mu>"} and radius @{term "\<delta>"}. The choice of $\alpha = \frac{1}{6}$ implies
a success probability per random variable of $\frac{2}{3}$. It is a commonly chosen success
probability for Monte-Carlo algorithms (cf. \cite[\textsection 4]{baryossef2002} or
\cite[\textsection 1]{kane2010}).\<close>

corollary (in prob_space) median_bound_2:
  fixes \<mu> \<delta> :: real
  assumes "\<epsilon> \<in> {0<..<1}"
  assumes "indep_vars (\<lambda>_. borel) X {0..<n}"
  assumes "n \<ge> -18 * ln \<epsilon>"
  assumes "\<And>i. i < n \<Longrightarrow> \<P>(\<omega> in M. abs (X i \<omega> - \<mu>) > \<delta>) \<le> 1/3" 
  shows "\<P>(\<omega> in M. abs (median n (\<lambda>i. X i \<omega>) - \<mu>) \<le> \<delta>) \<ge> 1-\<epsilon>"
proof -
  have b:"\<And>i. i < n \<Longrightarrow> space M - {\<omega> \<in> space M. X i \<omega> \<in> {\<mu> - \<delta>..\<mu> + \<delta>}} =  {\<omega> \<in> space M. abs (X i \<omega> - \<mu>) > \<delta>}"
    apply (rule order_antisym, rule subsetI, simp, linarith)
    by (rule subsetI, simp, linarith)

  have "\<And>i. i < n \<Longrightarrow> 1 - \<P>(\<omega> in M. X i \<omega> \<in> {\<mu>- \<delta>..\<mu>+\<delta>}) \<le> 1/3"
    apply (subst prob_compl[symmetric])
     apply (measurable)
     using assms(2) apply (simp add:indep_vars_def)
    apply (subst b, simp)
    using assms(4) by simp

  hence a:"\<And>i. i < n \<Longrightarrow> \<P>(\<omega> in M. X i \<omega> \<in> {\<mu>- \<delta>..\<mu>+\<delta>}) \<ge> 2/3" by simp
  
  have "1-\<epsilon> \<le> \<P>(\<omega> in M. median n (\<lambda>i. X i \<omega>) \<in> {\<mu>-\<delta>..\<mu>+\<delta>})"
    apply (rule median_bound_1[OF _ assms(1) assms(2), where \<alpha>="1/6"], simp) 
     using assms(3) apply (simp add:power2_eq_square)
    using a by simp
  also have "... = \<P>(\<omega> in M. abs (median n (\<lambda>i. X i \<omega>) - \<mu>) \<le> \<delta>)"
    apply (rule arg_cong2[where f="measure"], simp)
    apply (rule order_antisym, rule subsetI, simp, linarith)
    by (rule subsetI, simp, linarith)
  finally show ?thesis by simp
qed

section \<open>Some additional results about the median\<close>

lemma sorted_mono_map: 
  assumes "sorted xs"
  assumes "mono f"
  shows "sorted (map f xs)"
  using assms apply (simp add:sorted_wrt_map)
  apply (rule sorted_wrt_mono_rel[where P="(\<le>)"])
  by (simp add:mono_def, simp)

text \<open>This could be added to @{theory "HOL.List"}:\<close>
lemma map_sort:
  assumes "mono f"
  shows "sort (map f xs) = map f (sort xs)"
  apply (rule properties_for_sort)
   apply simp
  by (rule sorted_mono_map, simp, simp add:assms)

lemma median_cong:
  assumes "\<And>i. i < n \<Longrightarrow> f i = g i"
  shows "median n f = median n g"
  apply (cases "n = 0", simp add:median_def)
  apply (simp add:median_def)
  apply (rule arg_cong2[where f="(!)"])
   apply (rule arg_cong[where f="sort"], rule map_cong, simp, simp add:assms)
  by simp

lemma median_restrict: 
  "median n (\<lambda>i \<in> {0..<n}.f i) = median n f"
  by (rule median_cong, simp)

lemma median_commute_mono:
  assumes "n > 0"
  assumes "mono g"
  shows "g (median n f) = median n (g \<circ> f)"
  apply (simp add: median_def del:map_map)
  apply (subst map_map[symmetric])
  apply (subst map_sort[OF assms(2)])
  apply (subst nth_map, simp) using assms apply fastforce
  by simp

lemma median_rat:
  assumes "n > 0"
  shows "real_of_rat (median n f) = median n (\<lambda>i. real_of_rat (f i))"
  apply (subst (2) comp_def[where g="f", symmetric])
  apply (rule median_commute_mono[OF assms(1)])
  by (simp add: mono_def of_rat_less_eq)

lemma median_const:
  assumes "k > 0"
  shows "median k (\<lambda>i \<in> {0..<k}. a) = a"
proof -
  have b: "sorted (map (\<lambda>_. a) [0..<k])" 
    by (subst sorted_wrt_map, simp)
  have a: "sort (map (\<lambda>_. a) [0..<k]) = map (\<lambda>_. a) [0..<k]"
    by (subst sorted_sort_id[OF b], simp)
  have "median k (\<lambda>i \<in> {0..<k}. a) = median k (\<lambda>_. a)"
    by (subst median_restrict, simp)
  also have "... = a"
    apply (simp add:median_def a)
    apply (subst nth_map)
    using assms by simp+
  finally show ?thesis by simp
qed

end
