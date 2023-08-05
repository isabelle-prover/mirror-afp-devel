section \<open>Intervals are Borel measurable\<close>

theory Median
  imports 
    "HOL-Probability.Probability" 
    "HOL-Library.Multiset" 
    "Universal_Hash_Families.Universal_Hash_Families_More_Independent_Families"
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
        using a assms(1) by (auto simp: up_ray_def) 
      ultimately show ?thesis by blast
    next
      case False
      hence "I \<subseteq> {x..}" using linorder_not_less by auto
      moreover have "{x..} \<subseteq> I"
        using c assms(1) unfolding up_ray_def by blast
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
    using Suc by (simp del:sort_map.simps)
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

definition median :: "nat \<Rightarrow> (nat \<Rightarrow> ('a :: linorder)) \<Rightarrow> 'a" where
  "median n f = sort (map f [0..<n]) ! (n div 2)"

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

The remainder follows the proof in \<^cite>\<open>\<open>\textsection 2.1\<close> in "alon1999"\<close> using the Hoeffding inequality
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

lemma prod_pmf_bernoulli_mono:
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i \<and> f i \<le> g i \<and> g i \<le> 1"
  assumes "\<And>x y. x \<in> A \<Longrightarrow> (\<forall>i \<in> I. x i \<le> y i) \<Longrightarrow> y \<in> A"
  shows "measure (Pi_pmf I d (bernoulli_pmf \<circ> f)) A \<le> measure (Pi_pmf I d (bernoulli_pmf \<circ> g)) A"
    (is "?L \<le> ?R")
proof -
  define q where "q i = pmf_of_list [(0::nat, f i), (1, g i - f i), (2, 1 - g i)]" for i

  have wf:"pmf_of_list_wf [(0::nat, f i), (1, g i - f i), (2, 1 - g i)]" if "i \<in> I" for i
    using assms(2)[OF that] by (intro pmf_of_list_wfI) auto

  have 0: "bernoulli_pmf (f i) = map_pmf (\<lambda>x. x = 0) (q i)" (is "?L1 = ?R1") 
    if "i \<in> I" for i
  proof -
    have "0 \<le> f i" "f i \<le> 1" using assms(2)[OF that] by auto
    hence "pmf ?L1 x = pmf ?R1 x" for x
      unfolding q_def pmf_map measure_pmf_of_list[OF wf[OF that]] 
      by (cases x;simp_all add:vimage_def)
    thus ?thesis
      by (intro pmf_eqI) auto
  qed

  have 1: "bernoulli_pmf (g i) = map_pmf (\<lambda>x. x \<in> {0,1}) (q i)" (is "?L1 = ?R1")
    if "i \<in> I" for i
  proof -
    have "0 \<le> g i" "g i \<le> 1" using assms(2)[OF that] by auto
    hence "pmf ?L1 x = pmf ?R1 x" for x
      unfolding q_def pmf_map measure_pmf_of_list[OF wf[OF that]] 
      by (cases x;simp_all add:vimage_def)
    thus ?thesis
      by (intro pmf_eqI) auto
  qed

  have 2: "(\<lambda>k. x k = 0) \<in> A \<Longrightarrow> (\<lambda>k. x k = 0 \<or> x k = Suc 0) \<in> A" for x
    by (erule assms(3)) auto

  have "?L = measure (Pi_pmf I d (\<lambda>i. map_pmf (\<lambda>x. x = 0) (q i))) A"
    unfolding comp_def by (simp add:0 cong: Pi_pmf_cong)
  also have "... = measure (map_pmf ((\<circ>) (\<lambda>x. x = 0)) (Pi_pmf I (if d then 0 else 2) q)) A"
    by (intro arg_cong2[where f="measure_pmf.prob"] Pi_pmf_map[OF assms(1)]) auto 
  also have "... = measure (Pi_pmf I (if d then 0 else 2) q) {x. (\<lambda>k. x k = 0) \<in> A}"
    by (simp add:comp_def vimage_def)
  also have "... \<le> measure (Pi_pmf I (if d then 0 else 2) q) {x. (\<lambda>k. x k \<in> {0,1}) \<in> A}"
    using 2 by (intro measure_pmf.finite_measure_mono subsetI) auto 
  also have "... = measure (map_pmf ((\<circ>) (\<lambda>x. x \<in> {0,1})) (Pi_pmf I (if d then 0 else 2) q)) A"
    by (simp add:vimage_def comp_def)
  also have "... = measure (Pi_pmf I d (\<lambda>i. map_pmf (\<lambda>x. x \<in> {0,1}) (q i))) A"
    by (intro arg_cong2[where f="measure_pmf.prob"] Pi_pmf_map[OF assms(1), symmetric]) auto
  also have "... = ?R" 
    unfolding comp_def by (simp add:1 cong: Pi_pmf_cong)
  finally show ?thesis by simp
qed

lemma discrete_measure_eqI:
  assumes "sets M = count_space UNIV"
  assumes "sets N = count_space UNIV" 
  assumes "countable \<Omega>"
  assumes "\<And>x. x \<in> \<Omega> \<Longrightarrow> emeasure M {x} = emeasure N {x} \<and> emeasure M {x} \<noteq> \<infinity>"
  assumes "AE x in M. x \<in> \<Omega>"
  assumes "AE x in N. x \<in> \<Omega>"
  shows "M = N"
proof -
  define E where "E = insert {} ((\<lambda>x. {x}) ` \<Omega>)"

  have 0: "Int_stable E" unfolding E_def by (intro Int_stableI) auto
  have 1: "countable E" using assms(3) unfolding E_def by simp

  have "E \<subseteq> Pow \<Omega>" unfolding E_def by auto
  have "emeasure M A = emeasure N A" if A_range: "A \<in> E" for A
    using that assms(4) unfolding E_def by auto
  moreover have "sets M = sets N" using assms(1,2) by simp
  moreover have "\<Omega> \<in> sets M" using assms(1) by simp
  moreover have "E \<noteq> {}" unfolding E_def by simp
  moreover have "\<Union>E = \<Omega>" unfolding E_def by simp
  moreover have "emeasure M a \<noteq> \<infinity>" if "a \<in> E" for a
    using that assms(4) unfolding E_def by auto
  moreover have "sets (restrict_space M \<Omega>) = Pow \<Omega>"
    using assms(1) by (simp add:sets_restrict_space range_inter)
  moreover have "sets (restrict_space N \<Omega>) = Pow \<Omega>"
    using assms(2) by (simp add:sets_restrict_space range_inter)
  moreover have "sigma_sets \<Omega> E = Pow \<Omega>"
    unfolding E_def by (intro sigma_sets_singletons_and_empty assms(3)) 
  ultimately show ?thesis
    by (intro measure_eqI_restrict_generator[OF 0 _ _ _ _ _ _ assms(5,6) 1]) auto
qed

text \<open>Main results of this section:\<close>

text \<open>The next theorem establishes a bound for the probability of the median of independent random
variables using the binomial distribution. In a follow-up step, we will establish tail bounds
for the binomial distribution and corresponding median bounds.

This two-step strategy was suggested by Yong Kiam Tan. In a previous version, I only had verified 
the exponential tail bound (see theorem \verb+median_bound+ below).\<close>

theorem (in prob_space) median_bound_raw:
  fixes I :: "('b :: {linorder_topology, second_countable_topology}) set"
  assumes "n > 0" "p \<ge> 0"
  assumes "interval I"
  assumes "indep_vars (\<lambda>_. borel) X {0..<n}"
  assumes "\<And>i. i < n \<Longrightarrow> \<P>(\<omega> in M. X i \<omega> \<in> I) \<ge> p" 
  shows "\<P>(\<omega> in M. median n (\<lambda>i. X i \<omega>) \<in> I) \<ge> 1 - measure (binomial_pmf n p) {..n div 2}" 
    (is "?L \<ge> ?R")
proof -
  let ?pi = "Pi_pmf {..<n} undefined"
  define q where "q i = \<P>(\<omega> in M. X i \<omega> \<in> I)" for i

  have n_ge_1: "n \<ge> 1" using assms(1) by simp

  have 0: "{k. k < n \<and> (k < n \<longrightarrow> X k \<omega> \<in> I)} = {k. k < n \<and> X k \<omega> \<in> I}" for \<omega>
    by auto

  have "countable ({..<n} \<rightarrow>\<^sub>E (UNIV ::  bool set))"
    by (intro countable_PiE) auto
  hence countable_ext: "countable (extensional {..<n} :: (nat \<Rightarrow> bool) set)"
    unfolding PiE_def by auto

  have m0: "I \<in> sets borel"
    using interval_borel[OF assms(3)] by simp

  have m1: "random_variable borel (\<lambda>x. X k x)" if "k \<in> {..<n}" for k 
    using assms(4) that unfolding indep_vars_def by auto

  have m2: "(\<lambda>x. x \<in> I) \<in> borel \<rightarrow>\<^sub>M (measure_pmf ((bernoulli_pmf \<circ> q) k))"  
    for k using m0 by measurable
  hence m3: "random_variable (measure_pmf ((bernoulli_pmf \<circ> q) k)) (\<lambda>x. X k x \<in> I)"
    if "k \<in> {..<n}" for k 
    by (intro measurable_compose[OF m1] that)

  hence m4: "random_variable (PiM {..<n} (bernoulli_pmf \<circ> q)) (\<lambda>\<omega>. \<lambda>k\<in>{..<n}. X k \<omega> \<in> I)" 
    by (intro measurable_restrict) auto
  moreover have "A \<in> sets (Pi\<^sub>M {..<n} (\<lambda>x. measure_pmf (bernoulli_pmf (q x))))"
    if "A \<subseteq> extensional {..<n}" for A 
  proof -
    have "A = (\<Union>a \<in> A. {a})" by auto
    also have "... = (\<Union>a \<in> A. PiE {..<n} (\<lambda>k. {a k}))"
      using that by (intro arg_cong[where f="Union"] image_cong refl PiE_singleton[symmetric]) auto
    also have "... \<in> sets (Pi\<^sub>M {..<n} (\<lambda>x. measure_pmf (bernoulli_pmf (q x))))"
      using that countable_ext countable_subset
      by (intro sets.countable_Union countable_image image_subsetI sets_PiM_I_finite) auto
    finally show ?thesis by simp
  qed
  hence m5: "id \<in> (PiM {..<n} (bernoulli_pmf \<circ> q)) \<rightarrow>\<^sub>M (count_space UNIV)"
    by (intro measurableI) (simp_all add:vimage_def space_PiM PiE_def)
  ultimately have "random_variable (count_space UNIV) (id \<circ> (\<lambda>\<omega>. \<lambda>k\<in>{..<n}. X k \<omega> \<in> I))"
    by (rule measurable_comp)
  hence m6: "random_variable (count_space UNIV) (\<lambda>\<omega>. \<lambda>k\<in>{..<n}. X k \<omega> \<in> I)" by simp

  have indep: "indep_vars (bernoulli_pmf \<circ> q) (\<lambda>i x. X i x \<in> I) {0..<n}" 
    by (intro indep_vars_compose2[OF assms(4)] m2)

  have "measure M {x \<in> space M. (X k x \<in> I) = \<omega>} = measure (bernoulli_pmf (q k)) {\<omega>}"
    if "k < n" for \<omega> k
  proof (cases "\<omega>")
    case True
    then show ?thesis unfolding q_def  by (simp add:measure_pmf_single)
  next
    case False
    have "{x \<in> space M. X k x \<in> I} \<in> events"
      using that m0 by (intro measurable_sets_Collect[OF m1]) auto
    hence "prob {x \<in> space M. X k x \<notin> I} = 1 - prob {\<omega> \<in> space M. X k \<omega> \<in> I}" 
      by (subst prob_neg) auto
    thus ?thesis using False unfolding q_def by (simp add:measure_pmf_single)
  qed

  hence 1: "emeasure M {x \<in> space M. (X k x \<in> I) = \<omega>} = emeasure (bernoulli_pmf (q k)) {\<omega>}"
    if "k < n" for \<omega> k
    using that unfolding emeasure_eq_measure measure_pmf.emeasure_eq_measure by simp

  interpret product_sigma_finite "(bernoulli_pmf \<circ> q)"
    by standard

  have "distr M (count_space UNIV) (\<lambda>\<omega>. (\<lambda>k\<in>{..<n} . X k \<omega> \<in> I)) = distr 
    (distr M (PiM {..<n} (bernoulli_pmf \<circ> q)) (\<lambda>\<omega>. \<lambda>k\<in>{..<n}. X k \<omega> \<in> I)) (count_space UNIV) id"
    by (subst distr_distr[OF m5 m4]) (simp add:comp_def) 
  also have "... = distr (PiM {..<n} (\<lambda>i. (distr M ((bernoulli_pmf \<circ> q) i) (\<lambda>\<omega>. X i \<omega> \<in> I) )))
    (count_space UNIV) id" 
    using assms(1) indep atLeast0LessThan by (intro arg_cong2[where f="\<lambda>x y. distr x y id"] 
        iffD1[OF indep_vars_iff_distr_eq_PiM'] m3) auto 
  also have "... = distr (PiM {..<n} (bernoulli_pmf \<circ> q)) (count_space UNIV) id"
    using m3 1 by (intro distr_cong PiM_cong refl discrete_measure_eqI[where \<Omega>="UNIV"])
        (simp_all add:emeasure_distr vimage_def Int_def conj_commute)
  also have "... = ?pi (bernoulli_pmf \<circ> q)"
  proof (rule discrete_measure_eqI[where \<Omega>="extensional {..<n}"], goal_cases)
    case 1 show ?case by simp
  next
    case 2 show ?case by simp
  next
    case 3 show ?case using countable_ext by simp
  next
    case (4 x)
    have "emeasure (Pi\<^sub>M {..<n} (bernoulli_pmf \<circ> q)) {x} = 
      emeasure (Pi\<^sub>M {..<n} (bernoulli_pmf \<circ> q)) (PiE {..<n} (\<lambda>k. {x k}))"
      using PiE_singleton[OF 4] by simp
    also have "... = (\<Prod>i<n. emeasure (measure_pmf (bernoulli_pmf (q i))) {x i})"
      by (subst emeasure_PiM) auto
    also have "... = emeasure (Pi_pmf {..<n} undefined (bernoulli_pmf\<circ>q)) 
      (PiE_dflt {..<n} undefined (\<lambda>k. {x k}))"
      unfolding measure_pmf.emeasure_eq_measure
      by (subst measure_Pi_pmf_PiE_dflt) (simp_all add:prod_ennreal)
    also have "... = emeasure (Pi_pmf {..<n} undefined (bernoulli_pmf\<circ>q)) {x}"
      using 4 by (intro arg_cong2[where f="emeasure"]) (auto simp add:PiE_dflt_def extensional_def)
    finally have "emeasure (Pi\<^sub>M {..<n} (bernoulli_pmf \<circ> q)) {x} = 
      emeasure (Pi_pmf {..<n} undefined (bernoulli_pmf \<circ> q)) {x}"
      by simp
    thus ?case using 4 
      by (subst (1 2) emeasure_distr[OF m5]) (simp_all add:vimage_def space_PiM PiE_def)
  next
    case 5
    have "AE x in Pi\<^sub>M {..<n} (bernoulli_pmf \<circ> q). x \<in> extensional {..<n}"
      by (intro AE_I2) (simp add:space_PiM PiE_def)
    then show ?case by (subst AE_distr_iff[OF m5]) simp_all
  next
    case 6
    then show ?case by (intro AE_pmfI) (simp add: set_Pi_pmf PiE_dflt_def extensional_def)
  qed
  finally have 2: "distr M (count_space UNIV) (\<lambda>\<omega>. (\<lambda>k\<in>{..<n}. X k \<omega> \<in> I)) = ?pi (bernoulli_pmf\<circ>q)"
    by simp

  have 3: "n < 2 * card {k. k < n \<and> y k}" if 
    "n < 2 * card {k. k < n \<and> x k}" "\<And>i. i < n \<Longrightarrow> x i \<Longrightarrow> y i" for x y
  proof -
    have "2 * card {k. k < n \<and> x k} \<le> 2 * card {k. k < n \<and> y k}"
      using that(2) by (intro mult_left_mono card_mono) auto
    thus ?thesis using that(1) by simp
  qed

  have 4: "0 \<le> p \<and> p \<le> q i \<and> q i \<le> 1" if "i < n" for i
    unfolding q_def using assms(2,5) that by auto

  have p_range: "p \<in> {0..1}"
    using 4[OF assms(1)] by auto

  have "?R = 1 - measure_pmf.prob (binomial_pmf n p) {k. 2 * k \<le> n}"
    by (intro arg_cong2[where f="(-)"] arg_cong2[where f="measure_pmf.prob"]) auto
  also have "... = measure (binomial_pmf n p) {k. n < 2 * k}"
    by (subst measure_pmf.prob_compl[symmetric]) (simp_all add:set_diff_eq not_le)
  also have "... = measure (?pi (bernoulli_pmf \<circ> (\<lambda>_. p))) {\<omega>. n < 2 * card {k. k < n \<and> \<omega> k}}"
    using p_range by (subst binomial_pmf_altdef'[where A="{..<n}" and dflt="undefined"]) auto
  also have "... \<le> measure (?pi (bernoulli_pmf \<circ> q)) {\<omega>. n < 2 * card {k. k < n \<and> \<omega> k}}"
    using 3 4 by (intro prod_pmf_bernoulli_mono) auto
  also have "... = 
    \<P>(\<omega> in distr M (count_space UNIV) (\<lambda>\<omega>. \<lambda>k\<in>{..<n}. X k \<omega> \<in> I). n<2*card {k. k < n \<and> \<omega> k})"
    unfolding 2 by simp
  also have "... = \<P>(\<omega> in M. n < 2*card {k. k < n \<and> X k \<omega> \<in> I})" 
    by (subst measure_distr[OF m6]) (simp_all add:vimage_def Int_def conj_commute 0)
  also have "... \<le> ?L"
    using median_est[OF assms(3)] m0 m1
    by (intro finite_measure_mono measurable_sets_Collect[OF median_measurable[OF n_ge_1]]) auto 
  finally show "?R \<le> ?L" by simp
qed

text \<open>Cumulative distribution of the binomial distribution (contributed by Yong Kiam Tan):\<close>

lemma prob_binomial_pmf_upto:
  assumes "0 \<le> p" "p \<le> 1"
  shows "measure_pmf.prob (binomial_pmf n p) {..m} =
    sum (\<lambda>i. real (n choose i) * p^i * (1 - p) ^(n-i)) {0..m}"
  by (auto simp: pmf_binomial[OF assms] measure_measure_pmf_finite intro!: sum.cong)

text \<open>A tail bound for the binomial distribution using Hoeffding's inequality:\<close>

lemma binomial_pmf_tail:
  assumes "p \<in> {0..1}" "real k \<le> real n * p"
  shows "measure (binomial_pmf n p) {..k} \<le> exp (- 2 * real n * (p - real k / n)^2)" 
    (is "?L \<le> ?R")
proof (cases "n = 0")
  case True then show ?thesis by simp
next
  case False
  let ?A = "{..<n}"
  let ?pi = "Pi_pmf ?A undefined (\<lambda>_. bernoulli_pmf p)"

  define \<mu> where "\<mu> = (\<Sum>i<n. (\<integral>x. (of_bool (x i) :: real) \<partial> ?pi))"
  define \<epsilon> :: real where "\<epsilon> = \<mu> - k" (* eps \<ge> 0 <-> k \<le> mu *)

  have "\<mu> = (\<Sum>i<n. (\<integral>x. (of_bool x :: real) \<partial> (map_pmf (\<lambda>\<omega>. \<omega> i) ?pi)))"
    unfolding \<mu>_def by simp
  also have "... = (\<Sum>i<n. (\<integral>x. (of_bool x :: real) \<partial> (bernoulli_pmf p)))"
    by (simp add: Pi_pmf_component)
  also have "... = real n * p" using assms(1) by simp
  finally have \<mu>_alt: "\<mu> = real n * p"
    by simp

  have \<epsilon>_ge_0: "\<epsilon> \<ge> 0"
    using assms(2) unfolding \<epsilon>_def \<mu>_alt by auto

  have indep: "prob_space.indep_vars ?pi (\<lambda>_. borel) (\<lambda>k \<omega>. of_bool (\<omega> k)) {..<n}"
    by (intro prob_space.indep_vars_compose2[OF prob_space_measure_pmf indep_vars_Pi_pmf]) auto
  interpret Hoeffding_ineq "?pi" "{..<n}" "\<lambda>k \<omega>. of_bool (\<omega> k)" "\<lambda>_.0" "\<lambda>_.1" \<mu>
    using indep unfolding \<mu>_def by (unfold_locales) simp_all  
  
  have "?L = measure (map_pmf (\<lambda>f. card {x \<in> ?A. f x}) ?pi) {..k}"
    by (intro arg_cong2[where f="measure_pmf.prob"] binomial_pmf_altdef' assms(1)) auto
  also have "... = \<P>(\<omega> in ?pi. (\<Sum>i<n. of_bool (\<omega> i)) \<le> \<mu> - \<epsilon>)"
    unfolding \<epsilon>_def by (simp add:vimage_def Int_def)
  also have "... \<le> exp (- 2 * \<epsilon>\<^sup>2 / (\<Sum>i<n. (1 - 0)\<^sup>2))"
    using False by (intro Hoeffding_ineq_le \<epsilon>_ge_0) auto
  also have "... = ?R"
    unfolding \<epsilon>_def \<mu>_alt by (simp add:power2_eq_square field_simps) 
  finally show ?thesis by simp
qed

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
  have "0 < -ln \<epsilon> / (2 * \<alpha>\<^sup>2)"  
    using assms by (intro divide_pos_pos) auto
  also have "... \<le> real n" using assms by simp
  finally have "real n > 0" by simp
  hence n_ge_0:"n > 0" by simp

  have d0: "real_of_int \<lfloor>real n / 2\<rfloor> * 2 / real n \<le> 1"
    using n_ge_0 by simp linarith

  hence d1: "real (nat \<lfloor>real n / 2\<rfloor>) \<le> real n * (1 / 2)"
    using n_ge_0 by (simp add:field_simps)
  also have "... \<le> real n * (1 / 2 + \<alpha>)"
    using assms(2) by (intro mult_left_mono) auto
  finally have d1: "real (nat \<lfloor>real n / 2\<rfloor>) \<le> real n * (1 / 2 + \<alpha>)" by simp

  have "1/2 + \<alpha> \<le> \<P>(\<omega> in M. X 0 \<omega> \<in> I)" using n_ge_0 by (intro assms(6))
  also have "... \<le> 1" by simp
  finally have d2: "1 / 2 + \<alpha> \<le> 1" by simp

  have d3: "nat \<lfloor>real n / 2\<rfloor> = n div 2" by linarith

  have "1 - \<epsilon> \<le> 1 - exp (- 2 * real n * \<alpha>\<^sup>2)" 
    using assms(2,3,5) by (intro diff_mono order.refl iffD1[OF ln_ge_iff]) (auto simp:field_simps)
  also have "... \<le> 1 - exp (- 2 * real n * ((1/2+\<alpha>) - real (nat \<lfloor>real n/2\<rfloor>) / real n)\<^sup>2)"
    using d0 n_ge_0 assms(2)
    by (intro diff_mono order.refl iffD2[OF exp_le_cancel_iff] mult_left_mono_neg power_mono) auto 
  also have "... \<le> 1 - measure (binomial_pmf n (1/2+\<alpha>)) {..nat \<lfloor>real n/2\<rfloor>}"
    using assms(2) d1 d2 by (intro diff_mono order.refl binomial_pmf_tail) auto
  also have "... = 1 - measure (binomial_pmf n (1/2+\<alpha>)) {..n div 2}" by (simp add:d3)
  also have "... \<le> \<P>(\<omega> in M. median n (\<lambda>i. X i \<omega>) \<in> I)"
    using assms(2) by (intro median_bound_raw n_ge_0 assms(1,4,6) add_nonneg_nonneg) auto
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
  using assms(5) by (intro median_bound[OF _ assms(1,2,3,4)]) (auto simp:interval_def)

text \<open>This is a specialization of the above, where $\alpha = \frac{1}{6}$ and the interval is 
described using a mid point @{term "\<mu>"} and radius @{term "\<delta>"}. The choice of 
$\alpha = \frac{1}{6}$ implies a success probability per random variable of $\frac{2}{3}$. It is a 
commonly chosen success probability for Monte-Carlo algorithms 
(cf. \<^cite>\<open>\<open>\textsection 4\<close> in "baryossef2002"\<close> or \<^cite>\<open>\<open>\textsection 1\<close> in "kane2010"\<close>).\<close>

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
  using assms by (intro properties_for_sort sorted_mono_map) auto

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
  also have "... = a" using assms by (simp add:median_def a)
  finally show ?thesis by simp
qed

end
