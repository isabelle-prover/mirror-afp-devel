section \<open>Maximum Segment Sum\<close>

theory Maximum_Segment_Sum
  imports Main
begin

text \<open>The \emph{maximum segment sum} problem is to compute, given a list of numbers,
the largest of the sums of the contiguous segments of that list. It is also known
as the \emph{maximum sum subarray} problem and has been considered many times in the literature;
the Wikipedia article
\href{https://en.wikipedia.org/wiki/Maximum\_subarray\_problem}{Maximum subarray problem} is a good starting point.

We assume that the elements of the list are not necessarily numbers but just elements
of some linearly ordered group.\<close>

class linordered_group_add = linorder + group_add +
assumes add_left_mono: "a \<le> b \<Longrightarrow> c + a \<le> c + b"
assumes add_right_mono: "a \<le> b \<Longrightarrow> a + c \<le> b + c"
begin

lemma max_add_distrib_left: "max y z + x = max (y+x) (z+x)"
by (metis add_right_mono max.absorb_iff1 max_def)

lemma max_add_distrib_right: "x + max y z = max (x+y) (x+z)"
by (metis add_left_mono max.absorb1 max.cobounded2 max_def)

subsection \<open>Naive Solution\<close>

fun mss_rec_naive_aux :: "'a list \<Rightarrow> 'a" where
  "mss_rec_naive_aux [] = 0"
| "mss_rec_naive_aux (x#xs) = max 0 (x + mss_rec_naive_aux xs)"

fun mss_rec_naive :: "'a list \<Rightarrow> 'a" where
  "mss_rec_naive [] = 0"
| "mss_rec_naive (x#xs) = max (mss_rec_naive_aux (x#xs)) (mss_rec_naive xs)"

definition fronts :: "'a list \<Rightarrow> 'a list set" where
  "fronts xs = {as. \<exists>bs. xs = as @ bs}"

definition "front_sums xs \<equiv> sum_list ` fronts xs"

lemma fronts_cons: "fronts (x#xs) = ((#) x) ` fronts xs \<union> {[]}" (is "?l = ?r")
proof
  show "?l \<subseteq> ?r"
  proof
    fix as assume "as \<in> ?l"
    then show "as \<in> ?r" by (cases as) (auto simp: fronts_def)
  qed
  show "?r \<subseteq> ?l" unfolding fronts_def by auto
qed

lemma front_sums_cons: "front_sums (x#xs) = (+) x ` front_sums xs \<union> {0}"
proof -
  have "sum_list ` ((#) x) ` fronts xs = (+) x ` front_sums xs" unfolding front_sums_def by force
  then show ?thesis by (simp add: front_sums_def fronts_cons)
qed

lemma finite_fronts: "finite (fronts xs)"
  by (induction xs) (simp add: fronts_def, simp add: fronts_cons)

lemma finite_front_sums: "finite (front_sums xs)"
  using front_sums_def finite_fronts by simp

lemma front_sums_not_empty: "front_sums xs \<noteq> {}"
  unfolding front_sums_def fronts_def using image_iff by fastforce

lemma max_front_sum: "Max (front_sums (x#xs)) = max 0 (x + Max (front_sums xs))"
using finite_front_sums front_sums_not_empty
by (auto simp add: front_sums_cons hom_Max_commute max_add_distrib_right)

lemma mss_rec_naive_aux_front_sums: "mss_rec_naive_aux xs = Max (front_sums xs)"
by (induction xs) (simp add: front_sums_def fronts_def, auto simp: max_front_sum)

lemma front_sums: "front_sums xs = {s. \<exists>as bs. xs = as @ bs \<and> s = sum_list as}"
unfolding front_sums_def fronts_def by auto

lemma mss_rec_naive_aux: "mss_rec_naive_aux xs = Max {s. \<exists>as bs. xs = as @ bs \<and> s = sum_list as}"
using front_sums mss_rec_naive_aux_front_sums by simp
  

definition mids :: "'a list \<Rightarrow> 'a list set" where
  "mids xs \<equiv> {bs. \<exists>as cs. xs = as @ bs @ cs}"

definition "mid_sums xs \<equiv> sum_list ` mids xs"

lemma fronts_mids: "bs \<in> fronts xs \<Longrightarrow> bs \<in> mids xs"
unfolding fronts_def mids_def by auto

lemma mids_mids_cons: "bs \<in> mids xs \<Longrightarrow> bs \<in> mids (x#xs)"
proof-
  fix bs assume "bs \<in> mids xs"
  then obtain as cs where "xs = as @ bs @ cs" unfolding mids_def by blast
  then have "x # xs = (x#as) @ bs @ cs" by simp
  then show "bs \<in> mids (x#xs)" unfolding mids_def by blast
qed

lemma mids_cons: "mids (x#xs) = fronts (x#xs) \<union> mids xs" (is "?l = ?r")
proof
  show "?l \<subseteq> ?r"
  proof
    fix bs assume "bs \<in> ?l"
    then obtain as cs where as_bs_cs: "(x#xs) = as @ bs @ cs" unfolding mids_def by blast
    then show "bs \<in> ?r"
    proof (cases as)
      case Nil
      then have "bs \<in> fronts (x#xs)" by (simp add: fronts_def as_bs_cs)
      then show ?thesis by simp
    next
      case (Cons a as')
      then have "xs = as' @ bs @ cs" using as_bs_cs by simp
      then show ?thesis unfolding mids_def by auto
    qed
  qed
  show "?r \<subseteq> ?l" using fronts_mids mids_mids_cons by auto
qed

lemma mid_sums_cons: "mid_sums (x#xs) = front_sums (x#xs) \<union> mid_sums xs"
  unfolding mid_sums_def by (auto simp: mids_cons front_sums_def)

lemma finite_mids: "finite (mids xs)"
  by (induction xs) (simp add: mids_def, simp add: mids_cons finite_fronts)

lemma finite_mid_sums: "finite (mid_sums xs)"
  by (simp add: mid_sums_def finite_mids)

lemma mid_sums_not_empty: "mid_sums xs \<noteq> {}"
  unfolding mid_sums_def mids_def by blast

lemma max_mid_sums_cons: "Max (mid_sums (x#xs)) = max (Max (front_sums (x#xs))) (Max (mid_sums xs))"
  by (auto simp: mid_sums_cons Max_Un finite_front_sums finite_mid_sums front_sums_not_empty mid_sums_not_empty)

lemma mss_rec_naive_max_mid_sum: "mss_rec_naive xs = Max (mid_sums xs)"
  by (induction xs) (simp add: mid_sums_def mids_def, auto simp: max_mid_sums_cons mss_rec_naive_aux front_sums)

lemma mid_sums: "mid_sums xs = {s. \<exists>as bs cs. xs = as @ bs @ cs \<and> s = sum_list bs}"
  by (auto simp: mid_sums_def mids_def)

theorem mss_rec_naive: "mss_rec_naive xs = Max {s. \<exists>as bs cs. xs = as @ bs @ cs \<and> s = sum_list bs}"
  unfolding mss_rec_naive_max_mid_sum mid_sums by simp


subsection \<open>Kadane's Algorithms\<close>

fun kadane :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "kadane [] cur m = m"
| "kadane (x#xs) cur m =
    (let cur' = max (cur + x) x in
      kadane xs cur' (max m cur'))"

definition "mss_kadane xs \<equiv> kadane xs 0 0"

lemma Max_front_sums_geq_0: "Max (front_sums xs) \<ge> 0"
proof-
  have "[] \<in> fronts xs" unfolding fronts_def by blast
  then have "0 \<in> front_sums xs" unfolding front_sums_def by force
  then show ?thesis using finite_front_sums Max_ge by simp
qed

lemma Max_mid_sums_geq_0: "Max (mid_sums xs) \<ge> 0"
proof-
  have "0 \<in> mid_sums xs" unfolding mid_sums_def mids_def by force
  then show ?thesis using finite_mid_sums Max_ge by simp
qed

lemma kadane: "m \<ge> cur \<Longrightarrow> m \<ge> 0 \<Longrightarrow> kadane xs cur m = max m (max (cur + Max (front_sums xs)) (Max (mid_sums xs)))"
proof (induction xs cur m rule: kadane.induct)
  case (1 cur m)
  then show ?case unfolding front_sums_def fronts_def mid_sums_def mids_def by auto
next
  case (2 x xs cur m)
  then show ?case
    apply (auto simp: max_front_sum max_mid_sums_cons Let_def)
    by (smt (verit, ccfv_threshold) Max_front_sums_geq_0 add_assoc add_0_right max.assoc max.coboundedI1 max.left_commute max.orderE max_add_distrib_left max_add_distrib_right)
qed

lemma Max_front_sums_leq_Max_mid_sums: "Max (front_sums xs) \<le> Max (mid_sums xs)"
proof-
  have "front_sums xs \<subseteq> mid_sums xs" unfolding front_sums_def mid_sums_def using fronts_mids subset_iff by blast
  then show ?thesis using front_sums_not_empty finite_mid_sums Max_mono by blast
qed

lemma mss_kadane_mid_sums: "mss_kadane xs = Max (mid_sums xs)"
  unfolding mss_kadane_def using kadane Max_mid_sums_geq_0 Max_front_sums_leq_Max_mid_sums by auto

theorem mss_kadane: "mss_kadane xs = Max {s. \<exists>as bs cs. xs = as @ bs @ cs \<and> s = sum_list bs}"
  using mss_kadane_mid_sums mid_sums by auto

end

end