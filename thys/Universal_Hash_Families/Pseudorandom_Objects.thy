section \<open>Pseudorandom Objects\<close>

theory Pseudorandom_Objects
  imports Universal_Hash_Families_More_Product_PMF
begin

text \<open>This section introduces a combinator library for pseudorandom objects~\cite{vadhan2012}.
These can be thought of as PRNGs but with rigorous mathematical properties, which can be used to
in algorithms to reduce their randomness usage.

Such an object represents a non-empty multiset, with an efficient mechanism to sample from
it. They have a natural interpretation as a probability space (each element is selected with a
probability proportional to its occurrence count in the multiset).

The following section will introduce a construction of k-independent hash families as a pseudorandom
object. The AFP entry @{verbatim Expander_Graphs} then follows up with expander walks as 
pseudorandom objects.\<close>

record 'a pseudorandom_object =
  pro_last :: nat
  pro_select :: "nat \<Rightarrow> 'a"

definition pro_size where "pro_size S = pro_last S + 1"
definition sample_pro where "sample_pro S = map_pmf (pro_select S) (pmf_of_set {0..pro_last S})"

declare [[coercion sample_pro]]

abbreviation pro_set where "pro_set S \<equiv> set_pmf (sample_pro S)"

lemma sample_pro_alt: "sample_pro S = map_pmf (pro_select S) (pmf_of_set {..<pro_size S})"
  unfolding pro_size_def sample_pro_def
  using Suc_eq_plus1 atLeast0AtMost lessThan_Suc_atMost by presburger

lemma pro_size_gt_0: "pro_size S > 0"
  unfolding pro_size_def by auto

lemma set_sample_pro: "pro_set S = pro_select S ` {..<pro_size S}"
  using pro_size_gt_0 unfolding sample_pro_alt set_map_pmf
  by (subst set_pmf_of_set) auto

lemma set_pmf_of_set_sample_size[simp]:
  "set_pmf (pmf_of_set {..<pro_size S}) =  {..<pro_size S}"
  using pro_size_gt_0 by (intro set_pmf_of_set) auto

lemma pro_select_in_set: "pro_select S (x mod pro_size S) \<in> pro_set S"
  unfolding set_sample_pro by (intro imageI) (simp add:pro_size_gt_0)

lemma finite_pro_set: "finite (pro_set S)"
  unfolding set_sample_pro by (intro finite_imageI) auto

lemma integrable_sample_pro[simp]:
  fixes f :: "'a \<Rightarrow> 'c::{banach, second_countable_topology}"
  shows "integrable (measure_pmf (sample_pro S)) f"
  by (intro integrable_measure_pmf_finite finite_pro_set)

(* List sample space *)

definition list_pro :: "'a list \<Rightarrow> 'a pseudorandom_object" where
  "list_pro ls = \<lparr> pro_last = length ls - 1, pro_select = (!) ls \<rparr>"

lemma list_pro:
  assumes "xs \<noteq> []"
  shows "sample_pro (list_pro xs) = pmf_of_multiset (mset xs)" (is "?L = ?R")
proof -
  have "?L = map_pmf ((!) xs) (pmf_of_set {..<length xs})"
    using assms unfolding list_pro_def sample_pro_alt pro_size_def by simp
  also have "... = pmf_of_multiset (image_mset ((!) xs) (mset_set {..<length xs}))"
    using assms by (subst map_pmf_of_set) auto
  also have "... = ?R"
    by (metis map_nth mset_map mset_set_upto_eq_mset_upto)
  finally show ?thesis by simp
qed

lemma list_pro_2:
  assumes "xs \<noteq> []" "distinct xs"
  shows "sample_pro (list_pro xs) = pmf_of_set (set xs)" (is "?L = ?R")
proof -
  have "?L = map_pmf ((!) xs) (pmf_of_set {..<length xs})"
    using assms unfolding list_pro_def sample_pro_alt pro_size_def by simp
  also have "... = pmf_of_set ((!) xs ` {..<length xs})"
    using assms nth_eq_iff_index_eq by (intro map_pmf_of_set_inj inj_onI) auto
  also have "... = ?R"
    by (intro arg_cong[where f="pmf_of_set"]) (metis atLeast_upt list.set_map map_nth)
  finally show ?thesis by simp
qed

lemma list_pro_size:
  assumes "xs \<noteq> []"
  shows "pro_size (list_pro xs) = length xs"
  using assms unfolding pro_size_def list_pro_def by auto

lemma list_pro_set:
  assumes "xs \<noteq> []"
  shows "pro_set (list_pro xs) = set xs"
proof -
  have "(!) xs ` {..<length xs} = set xs" by (metis atLeast_upt list.set_map map_nth)
  thus ?thesis unfolding set_sample_pro list_pro_size[OF assms] by (simp add:list_pro_def)
qed

(* Nat sample space *)

definition nat_pro :: "nat \<Rightarrow> nat pseudorandom_object" where
  "nat_pro n = \<lparr> pro_last = n-1, pro_select = id \<rparr>"

lemma nat_pro_size:
  assumes "n > 0"
  shows"pro_size (nat_pro n) = n"
  using assms unfolding nat_pro_def pro_size_def by auto

lemma nat_pro:
  assumes "n > 0"
  shows "sample_pro (nat_pro n) = pmf_of_set {..<n}"
  unfolding sample_pro_alt nat_pro_size[OF assms] by (simp add:nat_pro_def)

lemma nat_pro_set:
  assumes "n > 0"
  shows "pro_set (nat_pro n) = {..<n}"
  using assms unfolding nat_pro[OF assms] by (simp add: lessThan_empty_iff)

(* Geometric sample space *)

fun count_zeros :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "count_zeros 0 k = 0" |
  "count_zeros (Suc n) k = (if odd k then 0 else 1 + count_zeros n (k div 2))"

lemma count_zeros_iff: "j \<le> n \<Longrightarrow> count_zeros n k \<ge> j \<longleftrightarrow> 2^j dvd k"
proof (induction j arbitrary: n k)
  case 0
  then show ?case by simp
next
  case (Suc j)
  then obtain n' where n_def: "n = Suc n'" using Suc_le_D by presburger
  show ?case using Suc unfolding n_def by auto
qed

lemma count_zeros_max:
  "count_zeros n k \<le> n"
  by (induction n arbitrary: k) auto

definition geom_pro :: "nat \<Rightarrow> nat pseudorandom_object" where
  "geom_pro n = \<lparr> pro_last = 2^n - 1, pro_select = count_zeros n \<rparr>"

lemma geom_pro_size: "pro_size (geom_pro n) = 2^n"
  unfolding geom_pro_def pro_size_def by simp

lemma geom_pro_range: "pro_set (geom_pro n) \<subseteq> {..n}"
  using count_zeros_max unfolding sample_pro_alt unfolding geom_pro_def by auto

lemma geom_pro_prob:
  "measure (sample_pro (geom_pro n)) {\<omega>. \<omega> \<ge> j} = of_bool (j \<le> n) / 2^j" (is "?L = ?R")
proof (cases "j \<le> n")
  case True
  have a:"{..<(2^n)::nat} \<noteq> {}"
    by (simp add: lessThan_empty_iff)
  have b:"finite {..<(2^n)::nat}" by simp

  define f :: "nat \<Rightarrow> nat" where "f = (\<lambda>x. x * 2^j)"
  have d:"inj_on f {..<2^(n-j)}" unfolding f_def by (intro inj_onI) simp

  have e:"2^j > (0::nat)" by simp

  have "y \<in> f ` {..< 2^(n-j)} \<longleftrightarrow> y \<in> {x. x < 2^n \<and> 2^j dvd x}" for y :: nat
  proof -
    have "y \<in> f ` {..< 2^(n-j)} \<longleftrightarrow> (\<exists>x. x < 2 ^ (n - j) \<and> y = 2 ^ j * x)"
      unfolding f_def by auto
    also have "... \<longleftrightarrow> (\<exists>x. 2^j * x < 2^j * 2 ^ (n-j) \<and> y = 2 ^ j * x)"
      using e by simp
    also have "... \<longleftrightarrow> (\<exists>x. 2^j * x < 2^n \<and> y = 2 ^ j * x)"
      using True by (subst power_add[symmetric]) simp
    also have "... \<longleftrightarrow> (\<exists>x. y < 2^n \<and> y = x * 2 ^ j)"
      by (metis Groups.mult_ac(2))
    also have "... \<longleftrightarrow> y \<in> {x. x < 2^n \<and> 2^j dvd x}" by auto
    finally show ?thesis by simp
  qed

  hence c:"f ` {..< 2^(n-j)} = {x. x < 2^n \<and> 2^j dvd x}" by auto

  have "?L = measure (pmf_of_set {..<2^n}) {\<omega>. count_zeros n \<omega> \<ge> j}"
    unfolding sample_pro_alt geom_pro_size by (simp add:geom_pro_def)
  also have "... = real (card {x::nat. x < 2^n \<and> 2^j dvd x}) / 2^n"
    by (simp add: measure_pmf_of_set[OF a b] count_zeros_iff[OF True])
     (simp add:lessThan_def Collect_conj_eq)
  also have "... = real (card (f ` {..<2^(n-j)})) / 2^n"
    by (simp add:c)
  also have "... = real (card ({..<(2^(n-j)::nat)})) / 2^n"
    by (simp add: card_image[OF d])
  also have "... = ?R"
    using True by (simp add:frac_eq_eq power_add[symmetric])
  finally show ?thesis by simp
next
  case False
  have "set_pmf (sample_pro (geom_pro n)) \<subseteq> {..n}"
    using geom_pro_range by simp
  hence "?L = measure (sample_pro (geom_pro n)) {}"
    using False by (intro measure_pmf_cong) auto
  also have "... = ?R"
    using False by simp
  finally show ?thesis
    by simp
qed

lemma geom_pro_prob_single:
  "measure (sample_pro (geom_pro n)) {j} \<le> 1 / 2^j" (is "?L \<le> ?R")
proof -
  have "?L = measure (sample_pro (geom_pro n)) ({j..}-{j+1..})"
    by (intro measure_pmf_cong) auto
  also have "... = measure (sample_pro (geom_pro n)) {j..} - measure (sample_pro (geom_pro n)) {j+1..}"
    by (intro measure_Diff) auto
  also have "... = measure (sample_pro (geom_pro n)) {\<omega>. \<omega> \<ge> j}-measure (sample_pro (geom_pro n)) {\<omega>. \<omega> \<ge> (j+1)}"
    by (intro arg_cong2[where f="(-)"] measure_pmf_cong) auto
  also have "... = of_bool (j \<le> n) * 1 / 2 ^ j - of_bool (j + 1 \<le> n) / 2 ^ (j + 1)"
    unfolding geom_pro_prob by simp
  also have "... \<le> 1/2^j - 0"
    by (intro diff_mono) auto
  also have "... = ?R" by simp
  finally show ?thesis by simp
qed

(* Pair sample space *)

definition prod_pro ::
  "'a pseudorandom_object \<Rightarrow> 'b pseudorandom_object \<Rightarrow> ('a \<times> 'b) pseudorandom_object"
  where
    "prod_pro P Q =
      \<lparr> pro_last = pro_size P * pro_size Q - 1,
        pro_select = (\<lambda>k. (pro_select P (k mod pro_size P), pro_select Q (k div pro_size P))) \<rparr>"

lemma prod_pro_size:
  "pro_size (prod_pro P Q) = pro_size P * pro_size Q"
  unfolding prod_pro_def by (subst pro_size_def) (simp add:pro_size_gt_0)

lemma prod_pro:
  "sample_pro (prod_pro P Q) = pair_pmf (sample_pro P) (sample_pro Q)" (is "?L = ?R")
proof -
  let ?p = "pro_size P"
  let ?q = "pro_size Q"
  have "?L = map_pmf (\<lambda>k. (pro_select P (k mod ?p),pro_select Q (k div ?p))) (pmf_of_set{..<?p*?q})"
    unfolding sample_pro_alt prod_pro_size by (simp add:prod_pro_def)
  also have "... = map_pmf (map_prod (pro_select P) (pro_select Q))
    (map_pmf (\<lambda>k. (k mod ?p, k div ?p)) (pmf_of_set{..<?p*?q}))"
    unfolding map_pmf_comp by simp
  also have "... = ?R"
    unfolding split_pmf_mod_div[OF pro_size_gt_0 pro_size_gt_0] sample_pro_alt map_prod_def map_pair
    by simp
  finally show ?thesis by simp
qed

lemma prod_pro_set:
  "pro_set (prod_pro P Q) = pro_set P \<times> pro_set Q"
  unfolding prod_pro set_pair_pmf by simp

end