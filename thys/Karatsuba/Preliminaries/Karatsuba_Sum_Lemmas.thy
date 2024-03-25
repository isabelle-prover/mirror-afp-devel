section "Auxiliary Sum Lemmas"

theory Karatsuba_Sum_Lemmas
  imports Karatsuba_Preliminaries "Expander_Graphs.Extra_Congruence_Method"
begin

lemma sum_list_eq: "(\<And>x. x \<in> set xs \<Longrightarrow> f x = g x) \<Longrightarrow> sum_list (map f xs) = sum_list (map g xs)"
  by (rule arg_cong[OF list.map_cong0])

lemma sum_list_split_0: "(\<Sum>i \<leftarrow> [0..<Suc n]. f i) = f 0 + (\<Sum>i \<leftarrow> [1..<Suc n]. f i)"
  using upt_eq_Cons_conv 
proof -
  have "[0..<Suc n] = 0 # [1..<Suc n]" using upt_eq_Cons_conv by auto
  then show ?thesis by simp
qed
lemma sum_list_index_trafo: "(\<Sum>i \<leftarrow> xs. f (g i)) = (\<Sum>i \<leftarrow> map g xs. f i)"
  by (induction xs) simp_all
lemma sum_list_index_shift: "(\<Sum>i \<leftarrow> [a..<b]. f (i + c)) = (\<Sum>i \<leftarrow> [a+c..<b+c]. f i)"
proof -
  have "(\<Sum>i \<leftarrow> [a..<b]. f (i + c)) = (\<Sum>i \<leftarrow> (map (\<lambda>j. j + c) [a..<b]). f i)"
    by (intro sum_list_index_trafo)
  also have "map (\<lambda>j. j + c) [a..<b] = [a+c..<b+c]"
    using map_add_const_upt by simp
  finally show ?thesis .
qed

lemma list_sum_index_shift: "n = j - k \<Longrightarrow> (\<Sum>i \<leftarrow> [k+1..<j+1]. f i) = (\<Sum>i \<leftarrow> [k..<j]. f (i + 1))"
  using sum_list_index_trafo[where g = "\<lambda>l. l + 1" and xs = "[k..<j]" and f = f, symmetric]
  using map_Suc_upt by simp

lemma list_sum_index_shift': "(\<Sum>i \<leftarrow> [0..<m]. a (i + c)) = (\<Sum>i \<leftarrow> [c..<m+c]. a i)"
  by (induction m arbitrary: a c) auto

lemma list_sum_index_concat: "(\<Sum>i \<leftarrow> [0..<m]. a i) + (\<Sum>i \<leftarrow> [m..<m+c]. a i) = (\<Sum>i \<leftarrow> [0..<m+c]. a i)"
proof -
  have "(\<Sum>i \<leftarrow> [0..<m+c]. a i) = (\<Sum>i \<leftarrow> [0..<m] @ [m..<m+c]. a i)"
    using upt_add_eq_append[of 0 m c] by simp
  then show ?thesis using sum_list_append by simp
qed

lemma sum_list_linear:
  assumes "\<And>a b. f (a + b) = f a + f b"
  assumes "f 0 = 0"
  shows "f (\<Sum>i \<leftarrow> xs. g i) = (\<Sum>i \<leftarrow> xs. f (g i))"
  using assms
  by (induction xs) simp_all
lemma sum_list_int:
  shows "int (\<Sum>i \<leftarrow> xs. g i) = (\<Sum>i \<leftarrow> xs. int (g i))"
  by (intro sum_list_linear int_ops(5) int_ops(1))

lemma sum_list_split_Suc:
  assumes "n = Suc n'"
  shows "(\<Sum>i \<leftarrow> [0..<n]. f i) = (\<Sum>i \<leftarrow> [0..<n']. f i) + f n'"
  using assms by simp

lemma sum_list_estimation_leq:
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> f i \<le> B"
  shows "(\<Sum>i \<leftarrow> xs. f i) \<le> length xs * B"
  using assms by (induction xs)(simp, fastforce)

lemma sum_list_estimation_le:
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> f i < B"
  assumes "xs \<noteq> []"
  shows "(\<Sum>i \<leftarrow> xs. f i) < length xs * B"
proof -
  from \<open>xs \<noteq> []\<close> have "length xs > 0" by simp
  from \<open>xs \<noteq> []\<close> obtain x where "x \<in> set xs" by fastforce
  then have "B > 0" using assms(1) by fastforce
  then obtain B' where "B = Suc B'" using not0_implies_Suc by blast
  with assms(1) have "\<And>i. i \<in> set xs \<Longrightarrow> f i \<le> B'" by fastforce
  with sum_list_estimation_leq have "(\<Sum>i \<leftarrow> xs. f i) \<le> length xs * B'" by blast
  also have "... < length xs * B" using \<open>B = Suc B'\<close> \<open>length xs > 0\<close> by simp
  finally show ?thesis .
qed

subsection "@{class semiring_1} Sums"

lemma (in semiring_1) of_bool_mult: "of_bool x * a = (if x then a else 0)"
  by simp

lemma (in semiring_1_cancel) of_bool_disj: "of_bool (x \<or> y) = of_bool x + of_bool y - of_bool x * of_bool y"
  by simp
lemma (in semiring_1) of_bool_disj_excl: "\<not> (x \<and> y) \<Longrightarrow> of_bool (x \<or> y) = of_bool x + of_bool y"
  by simp

lemma (in semiring_1) of_bool_var_swap:
  "(\<Sum>i \<leftarrow> xs. of_bool (i = j) * f i) = (\<Sum>i \<leftarrow> xs. of_bool (i = j) * f j)"
  by (induction xs) simp_all
lemma "(\<Sum>i \<leftarrow> xs. of_bool (i = j) * f i) = count_list xs j * f j"
  by (induction xs) simp_all
lemma (in semiring_1) of_bool_distinct:
  "distinct xs \<Longrightarrow> (\<Sum>i \<leftarrow> xs. of_bool (i = j) * f i j) = of_bool (j \<in> set xs) * f j j"
  by (induction xs) auto
lemma (in semiring_1) of_bool_distinct_in:
  "distinct xs \<Longrightarrow> j \<in> set xs \<Longrightarrow> (\<Sum>i \<leftarrow> xs. of_bool (i = j) * f i j) = f j j"
  using of_bool_distinct[of xs j f] of_bool_mult by simp

lemma (in linordered_semiring_1) of_bool_sum_leq_1:
  assumes "distinct xs"
  assumes "\<And>i j. i \<in> set xs \<Longrightarrow> j \<in> set xs \<Longrightarrow> P i \<Longrightarrow> P j \<Longrightarrow> i = j"
  shows "(\<Sum>l \<leftarrow> xs. of_bool (P l)) \<le> 1"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  consider "P a" | "\<not> P a" by blast
  then show ?case
  proof cases
    case 1
    then have r: "(\<Sum>l\<leftarrow>a # xs. of_bool (P l)) = 1 + (\<Sum>l\<leftarrow>xs. of_bool (P l))"
      by simp
    have "of_bool (P l) = 0" if "l \<in> set xs" for l
    proof -
      from that have "a \<noteq> l" using Cons by auto
      then have "\<not> P l" using Cons \<open>l \<in> set xs\<close> 1 by force
      then show "of_bool (P l) = 0" by simp
    qed
    then have "(\<Sum>l\<leftarrow>xs. of_bool (P l)) = (\<Sum>l\<leftarrow>xs. 0)"
      using list.map_cong0[of xs] by metis
    then show ?thesis using r by simp
  next
    case 2
    then have "(\<Sum>l\<leftarrow>a # xs. of_bool (P l)) = (\<Sum>l\<leftarrow>xs. of_bool (P l))"
      by simp
    then show ?thesis using Cons by simp
  qed
qed
instantiation nat :: linordered_semiring_1
begin
  instance ..
end

lemma (in semiring_1) sum_list_mult_sum_list: "(\<Sum>i \<leftarrow> xs. f i) * (\<Sum>j \<leftarrow> ys. g j) = (\<Sum>i \<leftarrow> xs. \<Sum>j \<leftarrow> ys. f i * g j)"
  by (simp add: sum_list_const_mult sum_list_mult_const)

lemma (in semiring_1) semiring_1_sum_list_eq:
"(\<And>i. i \<in> set xs \<Longrightarrow> f i = g i) \<Longrightarrow> (\<Sum>i \<leftarrow> xs. f i) = (\<Sum>i \<leftarrow> xs. g i)"
  using arg_cong[OF list.map_cong0] by blast

lemma (in semiring_1) sum_swap:
"(\<Sum>i \<leftarrow> xs. (\<Sum>j \<leftarrow> ys. f i j)) = (\<Sum>j \<leftarrow> ys. (\<Sum>i \<leftarrow> xs. f i j))"
proof (induction xs)
  case (Cons a xs)
  have "(\<Sum>i \<leftarrow> (a # xs). (\<Sum>j \<leftarrow> ys. f i j)) = (\<Sum>j \<leftarrow> ys. f a j) + (\<Sum>i \<leftarrow> xs. (\<Sum>j \<leftarrow> ys. f i j))"
    by simp
  also have "... = (\<Sum>j \<leftarrow> ys. f a j) + (\<Sum>j \<leftarrow> ys. (\<Sum>i \<leftarrow> xs. f i j))"
    using Cons by simp
  also have "... = (\<Sum>j \<leftarrow> ys. f a j + (\<Sum>i \<leftarrow> xs. f i j))"
    using sum_list_addf[of "\<lambda>j. f a j" _ ys] by simp
  also have "... = (\<Sum>j \<leftarrow> ys. (\<Sum>i \<leftarrow> (a # xs). f i j))" by simp
  finally show ?case .
qed simp

lemma (in semiring_1) sum_append:
  "(\<Sum>i \<leftarrow> (xs @ ys). f i) = (\<Sum>i \<leftarrow> xs. f i) + (\<Sum>i \<leftarrow> ys. f i)"
  by (induction xs) (simp_all add: add.assoc)

lemma (in semiring_1) sum_append':
  assumes "zs = xs @ ys"
  shows "(\<Sum>i \<leftarrow> zs. f i) = (\<Sum>i \<leftarrow> xs. f i) + (\<Sum>i \<leftarrow> ys. f i)"
  using assms sum_append by blast

subsubsection "Power Sums"


lemma (in semiring_1) sum_list_of_bool_filter: "(\<Sum>i \<leftarrow> xs. of_bool (P i) * f i) = (\<Sum>i \<leftarrow> filter P xs. f i)"
  by (induction xs; simp)

lemma upt_filter_less: "filter (\<lambda>i. i < c) [a..<b] = [a..<min b c]"
  by (induction b; simp)

lemma upt_filter_geq: "filter (\<lambda>i. i \<ge> c) [a..<b] = [max a c..<b]"
  by (induction b; simp)

lemma (in semiring_1) sum_list_of_bool_less: "(\<Sum>i \<leftarrow> [a..<b]. of_bool (i < c) * f i) = (\<Sum>i \<leftarrow> [a..<min b c]. f i)"
  unfolding sum_list_of_bool_filter upt_filter_less by (rule refl)

lemma (in semiring_1) sum_list_of_bool_geq: "(\<Sum>i \<leftarrow> [a..<b]. of_bool (i \<ge> c) * f i) = (\<Sum>i \<leftarrow> [max a c..<b]. f i)"
  unfolding sum_list_of_bool_filter upt_filter_geq by (rule refl)

lemma (in semiring_1) sum_list_of_bool_range: "(\<Sum>i \<leftarrow> [a..<b]. of_bool (i \<in> set [c..<d]) * f i) =
    (\<Sum>i \<leftarrow> [max a c..<min b d]. f i)"
proof -
  have "(\<Sum>i \<leftarrow> [a..<b]. of_bool (i \<in> set [c..<d]) * f i) =
      (\<Sum>i \<leftarrow> [a..<b]. of_bool (i \<ge> c) * (of_bool (i < d) * f i))"
    by (intro semiring_1_sum_list_eq; simp)
  then show ?thesis unfolding sum_list_of_bool_geq sum_list_of_bool_less .
qed

lemma (in comm_semiring_1) cauchy_product:
"(\<Sum>i \<leftarrow> [0..<n]. f i) * (\<Sum>j \<leftarrow> [0..<m]. g j) =
    (\<Sum>k \<leftarrow> [0..<n + m - 1]. \<Sum>l \<leftarrow> [k + 1 - m..<min (k + 1) n]. f l * g (k - l))"
proof  -
  have "(\<Sum>i \<leftarrow> [0..<n]. f i) * (\<Sum>j \<leftarrow> [0..<m]. g j) =
    (\<Sum>i \<leftarrow> [0..<n]. \<Sum>j \<leftarrow> [0..<m]. f i * g j)"
    unfolding sum_list_mult_const[symmetric]
    unfolding sum_list_const_mult[symmetric]
    by (rule refl)
  also have "... = (\<Sum>i \<leftarrow> [0..<n]. \<Sum>j \<leftarrow> [0..<m]. \<Sum>k \<leftarrow> [0..<n + m - 1]. of_bool (k = i + j) * (f i * g j))"
    by (intro semiring_1_sum_list_eq of_bool_distinct_in[symmetric]; simp)
  also have "... = (\<Sum>k \<leftarrow> [0..<n + m - 1]. \<Sum>i \<leftarrow> [0..<n]. \<Sum>j \<leftarrow> [0..<m]. of_bool (k = i + j) * (f i * g j))"
    unfolding sum_swap[where xs = "[0..<m]" and ys = "[0..<n + m - 1]"]
    unfolding sum_swap[where xs = "[0..<n]" and ys = "[0..<n + m - 1]"]
    by (rule refl)
  also have "... = (\<Sum>k \<leftarrow> [0..<n + m - 1]. \<Sum>i \<leftarrow> [0..<n]. \<Sum>j \<leftarrow> [0..<m]. of_bool (k \<ge> i \<and> j = k - i) * (f i * g j))"
    by (intro semiring_1_sum_list_eq; simp)
  also have "... = (\<Sum>k \<leftarrow> [0..<n + m - 1]. \<Sum>i \<leftarrow> [0..<n]. \<Sum>j \<leftarrow> [0..<m]. of_bool (j = k - i) * (of_bool (k \<ge> i) * (f i * g j)))"
    by (intro semiring_1_sum_list_eq; simp)
  also have "... = (\<Sum>k \<leftarrow> [0..<n + m - 1]. \<Sum>i \<leftarrow> [0..<n]. of_bool (k - i \<in> set [0..<m]) * ((of_bool (k \<ge> i) * (f i * g (k - i)))))"
    by (intro semiring_1_sum_list_eq of_bool_distinct distinct_upt)
  also have "... = (\<Sum>k \<leftarrow> [0..<n + m - 1]. \<Sum>i \<leftarrow> [0..<n]. of_bool (i \<ge> k + 1 - m) * ((of_bool (k + 1 > i) * (f i * g (k - i)))))"
    by (intro semiring_1_sum_list_eq; auto)
  also have "... = (\<Sum>k \<leftarrow> [0..<n + m - 1]. \<Sum>l \<leftarrow> [k + 1 - m..<min (k + 1) n]. f l * g (k - l))"
    apply (intro semiring_1_sum_list_eq)
    unfolding sum_list_of_bool_geq sum_list_of_bool_less max_0L min.commute[of n]
    by (rule refl)
  finally show ?thesis .
qed

lemma (in comm_semiring_1) power_sum_product:
  assumes "m > 0"
  assumes "n \<ge> m"
  shows
"(\<Sum>i\<leftarrow>[0..<n]. f i * x ^ i) * (\<Sum>j\<leftarrow>[0..<m]. g j * x ^ j) =
  (\<Sum>k\<leftarrow>[0..<m]. (\<Sum>i\<leftarrow>[0..<Suc k]. f i * g (k - i)) * x ^ k) +
  (\<Sum>k\<leftarrow>[m..<n]. (\<Sum>i\<leftarrow>[Suc k - m..<Suc k]. f i * g (k - i)) * x ^ k) +
  (\<Sum>k\<leftarrow>[n..<n + m - 1]. (\<Sum>i\<leftarrow>[Suc k - m..<n]. f i * g (k - i)) * x ^ k)"
proof -
  have 1: "[0..<n + m - 1] = [0..<m] @ [m..<n] @ [n..<n + m - 1]"
    using upt_add_eq_append'[of 0 m "n + m - 1"] upt_add_eq_append'[of m n "n + m - 1"] assms by simp

  have "(\<Sum>i \<leftarrow> [0..<n]. f i * x ^ i) * (\<Sum>j \<leftarrow> [0..<m]. g j * x ^ j) =
      (\<Sum>k \<leftarrow> [0..<n + m - 1]. \<Sum>l \<leftarrow> [k + 1 - m..<min (k + 1) n]. (f l * x ^ l) * (g (k - l) * x ^ (k - l)))"
    by (rule cauchy_product)
  also have "... = (\<Sum>k \<leftarrow> [0..<n + m - 1]. \<Sum>l \<leftarrow> [k + 1 - m..<min (k + 1) n]. f l * g (k - l) * x ^ k)"
    apply (intro semiring_1_sum_list_eq)
    using mult.commute mult.assoc power_add[symmetric]
    by simp
  also have "... = (\<Sum>k \<leftarrow> [0..<n + m - 1]. (\<Sum>l \<leftarrow> [k + 1 - m..<min (k + 1) n]. f l * g (k - l)) * x ^ k)"
    by (intro semiring_1_sum_list_eq sum_list_mult_const)
  also have "... = (\<Sum>k\<leftarrow>[0..<m]. (\<Sum>i\<leftarrow>[k + 1 - m..<min (k + 1) n]. f i * g (k - i)) * x ^ k) +
      (\<Sum>k\<leftarrow>[m..<n]. (\<Sum>i\<leftarrow>[k + 1 - m..<min (k + 1) n]. f i * g (k - i)) * x ^ k) +
      (\<Sum>k\<leftarrow>[n..<n + m - 1]. (\<Sum>i\<leftarrow>[k + 1 - m..<min (k + 1) n]. f i * g (k - i)) * x ^ k)"
    unfolding 1 sum_append add.assoc by (rule refl)
  also have "... = (\<Sum>k\<leftarrow>[0..<m]. (\<Sum>i\<leftarrow>[0..<Suc k]. f i * g (k - i)) * x ^ k) +
      (\<Sum>k\<leftarrow>[m..<n]. (\<Sum>i\<leftarrow>[Suc k - m..<Suc k]. f i * g (k - i)) * x ^ k) +
      (\<Sum>k\<leftarrow>[n..<n + m - 1]. (\<Sum>i\<leftarrow>[Suc k - m..<n]. f i * g (k - i)) * x ^ k)"
    using assms by (intro_cong "[cong_tag_2 (+)]" more: semiring_1_sum_list_eq; simp)
  finally show ?thesis .
qed

lemma (in comm_semiring_1) power_sum_product_same_length:
  assumes "n > 0"
  shows "(\<Sum>i\<leftarrow>[0..<n]. f i * x ^ i) * (\<Sum>j\<leftarrow>[0..<n]. g j * x ^ j) =
  (\<Sum>k\<leftarrow>[0..<n]. (\<Sum>i\<leftarrow>[0..<Suc k]. f i * g (k - i)) * x ^ k) +
  (\<Sum>k\<leftarrow>[n..<2 * n - 1]. (\<Sum>i\<leftarrow>[Suc k - n..<n]. f i * g (k - i)) * x ^ k)"
  using power_sum_product[of n n f x g, OF assms order.refl]
  by (simp add: semiring_numeral_class.mult_2)

lemma (in semiring_1) sum_index_transformation:
  shows "(\<Sum>i \<leftarrow> xs. f (g i)) = (\<Sum>j \<leftarrow> map g xs. f j)"
  by (induction xs) simp_all

lemma (in comm_semiring_1) power_sum_split:
  fixes f :: "nat \<Rightarrow> 'a"
  fixes x :: 'a
  fixes c :: nat
  assumes "j \<le> n"
  shows "(\<Sum>i \<leftarrow> [0..<n]. f i * x ^ (i * c)) =
      (\<Sum>i \<leftarrow> [0..<j]. f i * x ^ (i * c)) +
      x ^ (j * c) * (\<Sum>i \<leftarrow> [0..<n - j]. f (j + i) * x ^ (i * c))"
proof -
  have "(\<lambda>i. i + j) = (+) j" by fastforce
  have "(\<Sum>i \<leftarrow> [0..<n]. f i * x ^ (i * c)) =
    (\<Sum>i \<leftarrow> [0..<j]. f i * x ^ (i * c)) + (\<Sum>i \<leftarrow> [j..<n]. f i * x ^ (i * c))"
    apply (intro sum_append' upt_add_eq_append') using \<open>j \<le> n\<close> by auto
  also have "(\<Sum>i \<leftarrow> [j..<n]. f i * x ^ (i * c)) =
    (\<Sum>i \<leftarrow> map ((+) j) [0..<n - j]. f i * x ^ (i * c))"
    apply (intro_cong "[cong_tag_1 sum_list, cong_tag_2 map]" more: refl)
    using \<open>j \<le> n\<close> map_add_upt[of j "n - j"] \<open>(\<lambda>i. i + j) = (+) j\<close> by simp
  also have "... = (\<Sum>i \<leftarrow> [0..<n - j]. f (j + i) * x ^ ((j + i) * c))"
    by (intro sum_index_transformation[symmetric])
  also have "... = (\<Sum>i \<leftarrow> [0..<n - j]. x ^ (j * c) * (f (j + i) * x ^ (i * c)))"
    apply (intro semiring_1_sum_list_eq)
    using mult.commute mult.assoc by (simp add: power_add add_mult_distrib)
  also have "... = x ^ (j * c) * (\<Sum>i \<leftarrow> [0..<n - j]. (f (j + i) * x ^ (i * c)))"
    by (intro sum_list_const_mult)
  finally show ?thesis .
qed

subsection "@{type nat} Sums"
lemma geo_sum_nat:
  assumes "(q :: nat) > 1"
  shows "(q - 1) * (\<Sum>i \<leftarrow> [0..<n]. q ^ i) = q ^ n - 1"
proof (induction n)
  case (Suc n)
  have "(q - 1) * (\<Sum>i \<leftarrow> [0..<Suc n]. q ^ i) = (q - 1) * (q ^ n + (\<Sum>i \<leftarrow> [0..<n]. q ^ i))"
    by simp
  also have "... = (q - 1) * q ^ n + (q - 1) * (\<Sum>i \<leftarrow> [0..<n]. q ^ i)"
    using add_mult_distrib mult.commute by metis
  also have "... = (q - 1) * q ^ n + (q ^ n - 1)"
    using Suc.IH by simp
  also have "... = q * q ^ n - 1" using \<open>q > 1\<close> by (simp add: diff_mult_distrib)
  finally show ?case by simp
qed simp

lemma geo_sum_bound:
  assumes "(q :: nat) > 1"
  assumes "\<And>i. i < n \<Longrightarrow> f i < q"
  shows "(\<Sum>i \<leftarrow> [0..<n]. f i * q ^ i) < q ^ n"
proof -
  from assms have "\<And>i. i < n \<Longrightarrow> f i \<le> (q - 1)" by fastforce
  then have "(\<Sum>i \<leftarrow> [0..<n]. f i * q ^ i) \<le> (\<Sum>i \<leftarrow> [0..<n]. (q - 1) * q ^ i)"
    apply (intro sum_list_mono mult_le_mono1)
    using assms by simp
  also have "... = (q - 1) * (\<Sum>i \<leftarrow> [0..<n]. q ^ i)"
    by (intro sum_list_const_mult)
  also have "... = q ^ n - 1"
    by (intro geo_sum_nat assms)
  also have "... < q ^ n" using \<open>q > 1\<close> by simp
  finally show ?thesis .
qed

lemma power_sum_nat_split_div_mod:
  assumes "x > 1"
  assumes "c > 0"
  assumes "\<And>i. i < n \<Longrightarrow> (f i :: nat) < x ^ c"
  assumes "j \<le> n"
  shows "(\<Sum>i \<leftarrow> [0..<n]. f i * x ^ (i * c)) div x ^ (j * c)
      = (\<Sum>i \<leftarrow> [0..<n - j]. f (j + i) * x ^ (i * c))"
        "(\<Sum>i \<leftarrow> [0..<n]. f i * x ^ (i * c)) mod x ^ (j * c)
      = (\<Sum>i \<leftarrow> [0..<j]. f i * x ^ (i * c))"
proof -
  define sum where "sum = (\<Sum>i \<leftarrow> [0..<n]. f i * x ^ (i * c))"
  then have "sum = (\<Sum>i \<leftarrow> [0..<j]. f i * x ^ (i * c)) +
      x ^ (j * c) * (\<Sum>i \<leftarrow> [0..<n - j]. f (j + i) * x ^ (i * c))"
    (is "sum = ?sum1 + x ^ (j * c) * ?sum2")
    using power_sum_split \<open>j \<le> n\<close> by blast
  have "?sum1 = (\<Sum>i \<leftarrow> [0..<j]. f i * (x ^ c) ^ i)"
    apply (intro_cong "[cong_tag_2 (*)]" more: semiring_1_sum_list_eq refl)
    using power_mult mult.commute by metis
  also have "... < (x ^ c) ^ j"
    apply (intro geo_sum_bound)
    subgoal using assms one_less_power by blast
    subgoal using assms by simp
    done
  finally have "?sum1 < x ^ (j * c)" by (simp add: power_mult mult.commute)
  then show "sum mod x ^ (j * c) = ?sum1" "sum div (x ^ (j * c)) = ?sum2" using \<open>sum = ?sum1 + x ^ (j * c) * ?sum2\<close>
    using assms(1) by fastforce+
qed

lemma power_sum_nat_extract_coefficient:
  assumes "x > 1"
  assumes "c > 0"
  assumes "\<And>i. i < n \<Longrightarrow> (f i :: nat) < x ^ c"
  assumes "j < n"
  shows "((\<Sum>i \<leftarrow> [0..<n]. f i * x ^ (i * c)) div x ^ (j * c)) mod x ^ c = f j"
proof -
  have "(\<Sum>i \<leftarrow> [0..<n]. f i * x ^ (i * c)) div x ^ (j * c) =
    (\<Sum>i \<leftarrow> [0..<n - j]. f (j + i) * x ^ (i * c))" (is "?sum = _")
    apply (intro power_sum_nat_split_div_mod(1) assms)
    using assms by simp_all
  moreover have "... mod x ^ (1 * c) = (\<Sum>i \<leftarrow> [0..<1]. f (j + i) * x ^ (i * c))"
    apply (intro power_sum_nat_split_div_mod(2) assms)
    using assms by simp_all
  ultimately show "?sum mod x ^ c = f j" by simp
qed

lemma power_sum_nat_eq:
  assumes "x > 1"
  assumes "c > 0"
  assumes "\<And>i. i < n \<Longrightarrow> (f i :: nat) < x ^ c"
  assumes "\<And>i. i < n \<Longrightarrow> g i < x ^ c"
  assumes "(\<Sum>i \<leftarrow> [0..<n]. f i * x ^ (i * c)) = (\<Sum>i \<leftarrow> [0..<n]. g i * x ^ (i * c))"
    (is "?sumf = ?sumg")
  shows "\<And>i. i < n \<Longrightarrow> f i = g i"
proof -
  fix i
  assume "i < n"
  then have "f i = (?sumf div x ^ (i * c)) mod x ^ c"
    apply (intro power_sum_nat_extract_coefficient[symmetric] assms) by assumption
  also have "... = (?sumg div x ^ (i * c)) mod x ^ c"
    using assms by argo
  also have "... = g i"
    apply (intro power_sum_nat_extract_coefficient assms) using \<open>i < n\<close> by simp_all
  finally show "f i = g i" .
qed

end