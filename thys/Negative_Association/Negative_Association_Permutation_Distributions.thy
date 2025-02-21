section \<open>Permutation Distributions\label{sec:permutation_distributions}\<close>

text \<open>One of the fundamental examples for negatively associated random variables are permutation
distributions.

Let $x_1, \ldots, x_n$ be $n$ (not-necessarily) distinct values from a totally ordered set, then we
choose a permutation $\sigma : \{0,\ldots,n-1\} \rightarrow \{0,\ldots,n-1\}$ uniformly at random
Then the random variables defined by $X_i(\sigma) = x_{\sigma(i)}$ are negatively associated.

An important special case is the case where $x$ consists of $1$ one and $(n-1)$ zeros, modelling
randomly putting a ball into one of $n$ bins. Of course the process can be repeated independently,
the resulting distribution is also referred to as the balls into bins process. Because of the
closure properties established before, it is possible to conclude that the number of hits of each
bin in such a process are also negatively associated random variables.

In this section, we will derive that permutation distributions are negatively associated. The proof
follows Dubashi~\cite[Th. 10]{dubhashi1996} closely. A very short proof was presented
in the work by Joag-Dev~\cite{joagdev1983}, however after close inspection that proof seemed to
missing a lot of details. In fact, I don't think it is correct.\<close>

theory Negative_Association_Permutation_Distributions
  imports
    Negative_Association_Definition
    Negative_Association_FKG_Inequality
    Negative_Association_More_Lattices
    Finite_Fields.Finite_Fields_More_PMF
    "HOL-Types_To_Sets.Types_To_Sets"
    Executable_Randomized_Algorithms.Randomized_Algorithm
    Twelvefold_Way.Card_Bijections
begin

text \<open>The following introduces a lattice for n-element subsets of a finite set (with size larger
or equal to n.) A subset $x$ is smaller or equal to $y$, if the smallest element of $x$ is
smaller or equal to the smallest element of $y$, the second smallest element of $x$ is smaller or
equal to the second smallest element of $y$, etc.)

The lattice is introduced without name by Dubashi~\cite[Example 7]{dubashi1998}.\<close>

definition le_ordered_set_lattice :: "('a::linorder) set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "le_ordered_set_lattice S T = list_all2 (\<le>) (sorted_list_of_set S) (sorted_list_of_set T)"

definition ordered_set_lattice :: "('a :: linorder) set \<Rightarrow> nat \<Rightarrow> 'a set gorder"
  where "ordered_set_lattice S n =
    \<lparr> carrier = {T. T \<subseteq> S \<and> finite T \<and> card T = n},
      eq = (=),
      le = le_ordered_set_lattice \<rparr>"

definition osl_repr ::  "('a :: linorder) set \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a"
  where "osl_repr S n e = (\<lambda>i \<in> {..<n}. sorted_list_of_set e ! i)"

lemma osl_carr_sorted_list_of_set:
  assumes "finite S" "n \<le> card S"
  assumes "s \<in> carrier (ordered_set_lattice S n)"
  defines "t \<equiv> sorted_list_of_set s"
  shows "finite s" "card s = n" "s \<subseteq> S" "length t = n" "set t = s" "sorted_wrt (<) t"
  using assms unfolding ordered_set_lattice_def by auto

lemma ordered_set_lattice_carrier_intro:
  assumes "finite S" "n \<le> card S"
  assumes "set s \<subseteq> S" "distinct s" "length s = n"
  shows "set s \<in> carrier (ordered_set_lattice S n)"
  using assms distinct_card unfolding ordered_set_lattice_def by auto

lemma osl_list_repr_inj:
  assumes "finite S" "n \<le> card S"
  assumes "s \<in> carrier (ordered_set_lattice S n)"
  assumes "t \<in> carrier (ordered_set_lattice S n)"
  assumes "\<And>i. osl_repr S n s i = osl_repr S n t i"
  shows "s = t"
proof -
  note c1 = osl_carr_sorted_list_of_set[OF assms(1,2,3)]
  note c2 = osl_carr_sorted_list_of_set[OF assms(1,2,4)]

  have "sorted_list_of_set s ! i = sorted_list_of_set t ! i " if "i < n" for i
    using assms(5) that unfolding osl_repr_def lessThan_iff restrict_def by metis
  hence "sorted_list_of_set s = sorted_list_of_set t"
    using c1(4) c2(4) by (intro nth_equalityI) auto
  thus "s = t"
    using c1(1) c2(1) sorted_list_of_set_inject by auto
qed

lemma osl_leD:
  assumes "finite S" "n \<le> card S"
  assumes "e \<in> carrier (ordered_set_lattice S n)"
  assumes "f \<in> carrier (ordered_set_lattice S n)"
  shows "e \<sqsubseteq>\<^bsub>ordered_set_lattice S n\<^esub> f \<longleftrightarrow> (\<forall>i. osl_repr S n e i \<le> osl_repr S n f i)" (is "?L = ?R")
proof -
  note c1 = osl_carr_sorted_list_of_set[OF assms(1,2,3)]
  note c2 = osl_carr_sorted_list_of_set[OF assms(1,2,4)]

  have "?L = list_all2 (\<le>) (sorted_list_of_set e) (sorted_list_of_set f)"
    unfolding ordered_set_lattice_def le_ordered_set_lattice_def by simp
  also have "\<dots> = ?R" using c1(4) c2(4) unfolding list_all2_conv_all_nth osl_repr_def by simp
  finally show ?thesis by simp
qed

lemma ordered_set_lattice_partial_order:
  fixes S :: "('a :: linorder) set"
  assumes "finite S" "n \<le> card S"
  shows "partial_order (ordered_set_lattice S n)"
proof -
  let ?L = "ordered_set_lattice S n"

  note osl_list_repr_inj = osl_list_repr_inj[OF assms]
  note osl_leD = osl_leD[OF assms]

  have ref:"x \<sqsubseteq>\<^bsub>?L\<^esub> x" if "x \<in> carrier ?L" for x
    using osl_leD that by auto

  have antisym:"x = y" if "x \<sqsubseteq>\<^bsub>?L\<^esub> y" "y \<sqsubseteq>\<^bsub>?L\<^esub> x" "x \<in> carrier ?L" "y \<in> carrier ?L" for x y
    using osl_leD osl_list_repr_inj that by (metis order_antisym)

  have trans:"x \<sqsubseteq>\<^bsub>?L\<^esub> z"
    if "x \<sqsubseteq>\<^bsub>?L\<^esub> y" "y \<sqsubseteq>\<^bsub>?L\<^esub> z" "x \<in> carrier ?L" "y \<in> carrier ?L" "z \<in> carrier ?L"  for x y z
    using osl_leD that by (meson order_trans)

  have eq_eq: "(.= \<^bsub>?L\<^esub>) = (=)" unfolding ordered_set_lattice_def by simp

  show "partial_order ?L"
    using ref antisym trans eq_eq by (unfold_locales) presburger+
qed

lemma map2_max_mono:
  fixes xs :: "('a :: linorder) list"
  assumes "length xs = length ys"
  assumes "sorted_wrt (<) xs" "sorted_wrt (<) ys"
  shows "sorted_wrt (<) (map2 max xs ys)"
  using assms
proof (induction xs ys rule:list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  have "max x y < max a b" if "(a,b) \<in> set (zip xs ys)" for a b
  proof -
    have "x < a" using set_zip_leftD[OF that] Cons(3) by auto
    moreover have "y < b" using set_zip_rightD[OF that] Cons(4) by auto
    ultimately show ?thesis by (auto intro: max.strict_coboundedI1 max.strict_coboundedI2)
  qed
  moreover have "sorted_wrt (<) (map2 max xs ys)"
    using Cons(3,4) by (intro Cons(2)) auto
  ultimately show ?case by auto
qed

lemma map2_min_mono:
  fixes xs :: "('a :: linorder) list"
  assumes "length xs = length ys"
  assumes "sorted_wrt (<) xs" "sorted_wrt (<) ys"
  shows "sorted_wrt (<) (map2 min xs ys)"
  using assms
proof (induction xs ys rule:list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  have "min x y < min a b" if "(a,b) \<in> set (zip xs ys)" for a b
  proof -
    have "x < a" using set_zip_leftD[OF that] Cons(3) by auto
    moreover have "y < b" using set_zip_rightD[OF that] Cons(4) by auto
    ultimately show ?thesis by (auto intro: min.strict_coboundedI1 min.strict_coboundedI2)
  qed
  moreover have "sorted_wrt (<) (map2 min xs ys)"
    using Cons(3,4) by (intro Cons(2)) auto
  ultimately show ?case by auto
qed

lemma ordered_set_lattice_carrier_finite_ne:
  assumes "finite S" "n \<le> card S"
  shows "carrier (ordered_set_lattice S n) \<noteq> {}" "finite (carrier (ordered_set_lattice S n))"
proof -
  let ?C = "carrier (ordered_set_lattice S n)"

  have "0 < (card S choose n)" by (intro zero_less_binomial assms(2))
  also have "\<dots> = card {T. T \<subseteq> S \<and> card T = n}" unfolding n_subsets[OF assms(1)] by simp
  also have "\<dots> = card {T. T \<subseteq> S \<and> finite T \<and> card T = n}"
    using assms(1) finite_subset by (intro arg_cong[where f="card"] Collect_cong) auto
  also have "\<dots> = card ?C" unfolding ordered_set_lattice_def by simp
  finally have "card ?C > 0" by simp
  thus "?C \<noteq> {}" "finite ?C" unfolding card_gt_0_iff by auto
qed

lemma ordered_set_lattice_lattice:
  fixes S :: "('a :: linorder) set"
  assumes "finite S" "n \<le> card S"
  shows "finite_ne_distrib_lattice (ordered_set_lattice S n)"
proof -
  let ?L = "ordered_set_lattice S n"

  note osl_leD = osl_leD[OF assms]
  note osl_list_repr_inj = osl_list_repr_inj[OF assms]

  interpret partial_order "?L" by (intro ordered_set_lattice_partial_order assms)

  define lmax where "lmax x y = set (map2 max (sorted_list_of_set x) (sorted_list_of_set y))"
    for x y :: "'a set"

  define lmin where "lmin x y = set (map2 min (sorted_list_of_set x) (sorted_list_of_set y))"
    for x y :: "'a set"

  have lmax_1:
    "osl_repr S n (lmax s t) i = max (osl_repr S n s i) (osl_repr S n t i)" (is "?L1 = ?R1")
    "lmax s t \<in> carrier ?L"
    if "s \<in> carrier ?L" "t \<in> carrier ?L" for s t i
  proof -
    note s_carr = osl_carr_sorted_list_of_set[OF assms that(1)]
    note t_carr = osl_carr_sorted_list_of_set[OF assms that(2)]

    have s:"sorted_wrt (<) (map2 max (sorted_list_of_set s) (sorted_list_of_set t))"
      using s_carr t_carr by (intro map2_max_mono) auto
    hence "?L1 = (\<lambda>i \<in> {..<n}. (map2 max (sorted_list_of_set s) (sorted_list_of_set t)) ! i) i"
      unfolding lmax_def osl_repr_def  strict_sorted_iff
      by (subst linorder_class.sorted_list_of_set.idem_if_sorted_distinct) auto
    also have "\<dots> = (\<lambda>i \<in> {..<n}. max (sorted_list_of_set s ! i) (sorted_list_of_set t ! i)) i"
      using s_carr t_carr by simp
    also have "\<dots> = ?R1" unfolding osl_repr_def by auto
    finally show "?L1 = ?R1" by simp

    have "set (zip (sorted_list_of_set s) (sorted_list_of_set t)) \<subseteq> S \<times> S"
      using s_carr(3,5) t_carr(3,5) by (auto intro:set_zip_leftD set_zip_rightD)
    hence "set (map2 max (sorted_list_of_set s) (sorted_list_of_set t)) \<subseteq> S"
      by (auto simp:max_def)
    thus "lmax s t \<in> carrier ?L"
      using s_carr t_carr s unfolding lmax_def strict_sorted_iff
      by (intro ordered_set_lattice_carrier_intro[OF assms]) auto
  qed

  have lmin_1:
    "osl_repr S n (lmin s t) i = min (osl_repr S n s i) (osl_repr S n t i)" (is "?L1 = ?R1")
    "lmin s t \<in> carrier ?L"
    if "s \<in> carrier ?L" "t \<in> carrier ?L" for s t i
  proof -
    note s_carr = osl_carr_sorted_list_of_set[OF assms that(1)]
    note t_carr = osl_carr_sorted_list_of_set[OF assms that(2)]

    have s:"sorted_wrt (<) (map2 min (sorted_list_of_set s) (sorted_list_of_set t))"
      using s_carr t_carr by (intro map2_min_mono) auto
    hence "?L1 = (\<lambda>i \<in> {..<n}. (map2 min (sorted_list_of_set s) (sorted_list_of_set t)) ! i) i"
      unfolding lmin_def osl_repr_def  strict_sorted_iff
      by (subst linorder_class.sorted_list_of_set.idem_if_sorted_distinct) auto
    also have "\<dots> = (\<lambda>i \<in> {..<n}. min (sorted_list_of_set s ! i) (sorted_list_of_set t ! i)) i"
      using s_carr t_carr by simp
    also have "\<dots> = ?R1" unfolding osl_repr_def by auto
    finally show "?L1 = ?R1" by simp

    have "set (zip (sorted_list_of_set s) (sorted_list_of_set t)) \<subseteq> S \<times> S"
      using s_carr(3,5) t_carr(3,5) by (auto intro:set_zip_leftD set_zip_rightD)
    hence "set (map2 min (sorted_list_of_set s) (sorted_list_of_set t)) \<subseteq> S"
      by (auto simp:min_def)
    thus "lmin s t \<in> carrier ?L"
      using s_carr t_carr s unfolding lmin_def strict_sorted_iff
      by (intro ordered_set_lattice_carrier_intro[OF assms]) auto
  qed

  have lmax: "is_lub ?L (lmax x y) {x,y}" if "x \<in> carrier ?L" "y \<in> carrier ?L" for x y
    using that lmax_1 osl_leD by (intro least_UpperI) (auto simp:Upper_def)
  hence "\<exists>s. is_lub ?L s {x, y}" if "x \<in> carrier ?L" "y \<in> carrier ?L" for x y
    using that by auto
  hence 1: "upper_semilattice ?L" by (unfold_locales) auto

  have lmin: "is_glb ?L (lmin x y) {x,y}" if "x \<in> carrier ?L" "y \<in> carrier ?L" for x y
    using that lmin_1 osl_leD by (intro greatest_LowerI) (auto simp:Lower_def)
  hence "\<exists>s. is_glb ?L s {x, y}" if "x \<in> carrier ?L" "y \<in> carrier ?L" for x y
    using that by auto
  hence 2: "lower_semilattice ?L" by (unfold_locales) auto

  have 4:"lattice ?L" using 1 2 unfolding lattice_def by auto
  interpret lattice ?L using 4 by simp

  have join_eq: "x \<sqinter>\<^bsub>?L\<^esub> y = lmin x y"  if "x \<in> carrier ?L" "y \<in> carrier ?L" for x y
    by (intro glb_unique[symmetric] that lmin)

  have meet_eq: "x \<squnion>\<^bsub>?L\<^esub> y = lmax x y"  if "x \<in> carrier ?L" "y \<in> carrier ?L" for x y
    by (intro lub_unique[symmetric] that lmax)

  have "(x \<sqinter>\<^bsub>?L\<^esub> (y \<squnion>\<^bsub>?L\<^esub> z)) = (x \<sqinter>\<^bsub>?L\<^esub> y) \<squnion>\<^bsub>?L\<^esub> (x \<sqinter>\<^bsub>?L\<^esub> z)"
    if  "x \<in> carrier ?L" "y \<in> carrier ?L" "z \<in> carrier ?L" for x y z
  proof -
    have "osl_repr S n (lmin x (lmax y z)) i = osl_repr S n (lmax (lmin x y) (lmin x z)) i" for i
      using lmax_1 that lmin_1 by (simp add:min_max_distrib2)
    hence "lmin x (lmax y z) = lmax (lmin x y) (lmin x z)"
      by (intro osl_list_repr_inj lmax_1 lmin_1 that allI)
    thus ?thesis using that by (simp add: meet_eq join_eq lmax_1 lmin_1)
  qed
  thus ?thesis using 4 ordered_set_lattice_carrier_finite_ne[OF assms(1,2)] by (unfold_locales) auto
qed

lemma insort_eq:
  fixes xs :: "('a :: linorder) list"
  assumes "sorted xs"
  shows "\<exists>ys zs. insort e xs = ys@e#zs \<and> ys@zs=xs \<and> set ys \<subseteq> {..<e} \<and> set zs \<subseteq> {e..}"
proof -
  let ?ys = "takeWhile (\<lambda>x. x < e) xs"
  let ?zs = "dropWhile (\<lambda>x. x < e) xs"

  have a:"insort e xs = ?ys@e#?zs" by (induction xs) auto

  have "sorted (?ys@e#?zs)" unfolding a[symmetric] using assms sorted_insort by auto
  hence "sorted ([e]@?zs)" by (simp add: sorted_append)
  hence "set ?zs \<subseteq> {e..}" unfolding sorted_append by auto
  moreover have "set ?ys \<subseteq> {..<e}" by (metis lessThan_iff set_takeWhileD subset_eq)
  moreover have "?ys @ ?zs = xs" by simp
  ultimately show ?thesis using a by blast
qed

lemma list_all2_insort:
  fixes xs ys :: "('a :: linorder) list"
  assumes "length xs = length ys" "sorted xs" "sorted ys"
  shows  "list_all2 (\<le>) xs ys \<longleftrightarrow> list_all2 (\<le>) (insort e xs) (insort e ys)"
proof -
  obtain x1 x3 where xs:
    "xs = x1@x3" "insort e xs = x1@e#x3" "set x1 \<subseteq> {..<e}" "set x3 \<subseteq> {e..}"
    using insort_eq[OF assms(2)] by blast
  obtain y1 y3 where ys: "ys = y1@y3"
    "insort e ys = y1@e#y3" "set y1 \<subseteq> {..<e}" "set y3 \<subseteq> {e..}"
    using insort_eq[OF assms(3)] by blast

  have l: "length y1 + length y3 = length x1 + length x3" using assms(1) xs(1) ys(1) by simp

  have "list_all2 (\<le>) xs ys \<longleftrightarrow> list_all2 (\<le>) (x1@x3) (y1@y3)" by (simp add: xs ys)
  also have "\<dots> \<longleftrightarrow> list_all2 (\<le>) (x1@e#x3) (y1@e#y3)" (is "?L \<longleftrightarrow> ?R")
  proof (cases "length x1 < length y1")
    case True
    have "length x3 > 0" using l True by linarith

    hence "(x1@x3) ! length x1 \<ge> e"
      using xs(4) nth_mem in_mono unfolding nth_append by fastforce
    moreover have "(y1@y3) ! length x1 < e"
      using True ys(3) nth_mem unfolding nth_append by auto
    moreover have "length x1 < length (x1@x3)" using l True by auto
    ultimately have 1:"?L = False"
      unfolding xs ys list_all2_conv_all_nth by (meson leD order.trans)

    have "(y1@e#y3) ! length x1 < e"
      using True ys(3) nth_mem unfolding nth_append by auto
    moreover have "(x1@e#x3) ! length x1 = e" by simp
    moreover have "length x1 < length (x1@e#x3)" using l True by auto
    ultimately have "?R = False"
      unfolding xs(2) ys(2) list_all2_conv_all_nth by (metis leD)

    thus  ?thesis using 1 by auto
  next
    case False
    let ?x1 = "take (length y1) x1"
    define x2 where [simp]: "x2 = drop (length y1) x1"

    define y2 where [simp]: "y2 = take (length x1-length y1) y3"
    let ?y3 = "drop (length x1-length y1) y3"

    have l2: "length x2 = length y2" using False l by simp
    have set_x2: "set x2 \<subseteq> {..<e}"
      unfolding x2_def using xs(3) set_drop_subset subset_trans by metis
    have set_y2: "set y2 \<subseteq> {e..}"
      unfolding y2_def using ys(4) set_take_subset subset_trans by metis

    have "set (x2@[e]) \<subseteq> {..e}" "set (e#y2) \<subseteq> {e..}"
      using set_x2 set_y2 by auto
    hence a':"list_all2 (\<lambda>x y. x \<le> e \<and> e \<le> y) (x2@[e]) (e#y2)"
      using l2  set_zip_leftD set_zip_rightD by (intro list_all2I conjI ballI case_prodI2) fastforce+
    have a:"list_all2 (\<le>) (x2@[e]) (e#y2)" by (intro list_all2_mono[OF a']) auto

    have b':"list_all2 (\<lambda>x y. x \<le> e \<and> e \<le> y) x2 y2"
      using l2 set_x2 set_y2  set_zip_leftD set_zip_rightD by (intro list_all2I conjI ballI case_prodI2) fastforce+
    have b:"list_all2 (\<le>) x2 y2" by (intro list_all2_mono[OF b']) auto

    have "?L \<longleftrightarrow> list_all2 (\<le>) ((?x1@x2)@x3) (y1@y2@?y3)" by simp
    also have "\<dots> \<longleftrightarrow> list_all2 (\<le>) (?x1@x2@x3) (y1@y2@?y3)" using append_assoc by metis
    also have "\<dots> \<longleftrightarrow> list_all2 (\<le>) ?x1 y1 \<and> list_all2 (\<le>) (x2@x3) (y2@?y3)"
      using False by (intro list_all2_append) auto
    also have "\<dots> \<longleftrightarrow> list_all2 (\<le>) ?x1 y1 \<and> (list_all2 (\<le>) x2 y2 \<and> list_all2 (\<le>) x3 ?y3)"
      using l False by (intro arg_cong2[where f="(\<and>)"] refl list_all2_append) simp
    also have "\<dots> \<longleftrightarrow> list_all2 (\<le>) ?x1 y1\<and>(list_all2 (\<le>) (x2@[e]) (e#y2)\<and>list_all2 (\<le>) x3 ?y3)"
      using a b by simp
    also have "\<dots> \<longleftrightarrow> list_all2 (\<le>) ?x1 y1 \<and> (list_all2 (\<le>) ((x2@[e])@x3) ((e#y2)@?y3))"
      using l False by (intro arg_cong2[where f="(\<and>)"] refl list_all2_append[symmetric]) simp
    also have "\<dots> \<longleftrightarrow> list_all2 (\<le>) (?x1@((x2@[e])@x3)) (y1@((e#y2)@?y3))"
      using False by (intro list_all2_append[symmetric]) auto
    also have "\<dots> \<longleftrightarrow> list_all2 (\<le>) ((?x1@x2)@(e#x3)) (y1@e#(y2@?y3))"
      using append_assoc by (intro arg_cong2[where f="list_all2 (\<le>)"]) simp_all
    also have "\<dots> \<longleftrightarrow> ?R" by simp
    finally show ?thesis by simp
  qed
  also have "\<dots> \<longleftrightarrow> list_all2 (\<le>) (insort e xs) (insort e ys)" using xs ys by simp
  finally show ?thesis by simp
qed

lemma le_ordered_set_lattice_diff:
  fixes x y :: "('a :: linorder) set"
  assumes "finite x" "finite y" "card x = card y"
  shows "le_ordered_set_lattice x y \<longleftrightarrow> le_ordered_set_lattice (x - y) (y - x)"
proof -
  let ?le = "le_ordered_set_lattice"
  define u v S where vars:"u = x - y" "v = y - x" "S = x \<inter> y"

  have fins: "finite S" "finite u" "finite v" unfolding vars using assms by auto

  have disj: "S \<inter> u = {}" "S \<inter> v = {}" unfolding vars by auto

  have cards: "card u = card v" unfolding vars  using assms
    by (simp add: card_le_sym_Diff order_antisym)

  have "?le x y = ?le (u \<union> S) (v \<union> S)" unfolding vars by (intro arg_cong2[where f="?le"]) auto
  also have "\<dots> = ?le u v" using fins(1) disj
  proof (induction S rule:finite_induct)
    case empty thus ?case by simp
  next
    case (insert x F)
    define us where "us = sorted_list_of_set (u \<union> F)"
    define vs where "vs = sorted_list_of_set (v \<union> F)"
    have "card (u \<union> F) = card u + card F" using insert fins by (intro card_Un_disjoint) auto
    also have "\<dots> = card v + card F" using cards by auto
    also have "\<dots> = card (v \<union> F)" using insert fins by (intro card_Un_disjoint[symmetric]) auto
    finally have cards': "card (u \<union> F) = card (v \<union> F)" by simp

    have "?le (u \<union> insert x F) (v \<union> insert x F) = ?le (insert x (u \<union> F)) (insert x (v \<union> F))"
      by simp
    also have "\<dots> = list_all2 (\<le>) (insort x us) (insort x vs)"
      unfolding le_ordered_set_lattice_def us_def vs_def using insert fins(2,3)
      by (intro arg_cong2[where f="list_all2 (\<le>)"] sorted_list_of_set_insert ) auto
    also have "\<dots> = list_all2 (\<le>) us vs"
      using cards' by (intro list_all2_insort[symmetric]) (simp_all add:us_def vs_def)
    also have "\<dots> = ?le (u \<union> F) (v \<union> F)"
      unfolding le_ordered_set_lattice_def us_def vs_def by simp
    also have "\<dots> = ?le u v" using insert by (intro insert) auto
    finally show ?case by simp
  qed
  also have "\<dots> = ?le (x- y) (y-x)" unfolding vars by simp
  finally show ?thesis by simp
qed

lemma ordered_set_lattice_carrier:
  assumes "T \<in> carrier (ordered_set_lattice S n)"
  shows "finite T" "card T = n" "T \<subseteq> S"
  using assms unfolding ordered_set_lattice_def by auto

lemma ordered_set_lattice_dual:
  assumes "finite S" "n \<le> card S"
  defines "L \<equiv> ordered_set_lattice S n"
  defines "M \<equiv> ordered_set_lattice S (card S - n)"
  shows
    "\<And>x. x \<in> carrier L \<Longrightarrow> (S-x) \<in> carrier M"
    "\<And>x. x \<in> carrier M \<Longrightarrow> (S-x) \<in> carrier L"
    "\<And>x y. x \<in> carrier L \<and> y \<in> carrier L \<Longrightarrow> x \<sqsubseteq>\<^bsub>L\<^esub> y \<longleftrightarrow> (S-y) \<sqsubseteq>\<^bsub>M\<^esub> (S-x)"
proof (goal_cases)
  case (1 x)
  thus ?case using assms(1,2) unfolding ordered_set_lattice_def M_def L_def
    by (auto intro:card_Diff_subset)
next
  case (2 x)
  thus ?case using assms(1,2) unfolding ordered_set_lattice_def M_def L_def
    by (auto simp:card_Diff_subset_Int Int_absorb1)
next
  case (3 x y)
  hence a:"finite x" "finite y" "card x = card y" "x \<subseteq> S" "y \<subseteq> S"
    unfolding ordered_set_lattice_def M_def L_def by auto

  have b:"card (S - m) = card S - card m" if "m \<subseteq> S" for m
    using that assms(1) card_Diff_subset finite_subset[OF _ assms(1)] by auto

  have "le_ordered_set_lattice x y = le_ordered_set_lattice (x-y) (y-x)"
    by (intro le_ordered_set_lattice_diff a)
  also have "\<dots> = le_ordered_set_lattice ((S-y)-(S-x)) ((S-x)-(S-y))"
    using a by (intro arg_cong2[where f="le_ordered_set_lattice"]) auto
  also have "\<dots> = le_ordered_set_lattice (S - y) (S - x)"
    using a b assms(1) by (intro le_ordered_set_lattice_diff[symmetric]) auto
  finally have "le_ordered_set_lattice x y = le_ordered_set_lattice (S - y) (S - x)" by simp
  thus ?case unfolding ordered_set_lattice_def M_def L_def by simp
qed

lemma bij_betw_ord_set_lattice_pairs:
  assumes "finite S" "n \<le> card S"
  defines "L \<equiv> ordered_set_lattice S n"
  assumes "x \<in> carrier L" "y \<in> carrier L" "x \<sqsubseteq>\<^bsub>L\<^esub> y"
  shows "\<exists>\<phi>. bij_betw \<phi> x y \<and> strict_mono_on x \<phi> \<and> (\<forall>e. \<phi> e \<ge> e)"
proof -
  let ?xs = "sorted_list_of_set x"
  let ?ys = "sorted_list_of_set y"

  let ?p1 = "the_inv_into {..<n} (\<lambda>i. ?xs ! i)"
  let ?p2 = "(\<lambda>i. ?ys ! i)"

  have x: "card x = n" "finite x" using assms(4) unfolding L_def ordered_set_lattice_def by auto
  have y: "card y = n" "finite y" using assms(5) unfolding L_def ordered_set_lattice_def by auto
  have l_xs: "length ?xs = n" using length_sorted_list_of_set x by simp
  have l_ys: "length ?ys = n" using length_sorted_list_of_set y by simp

  have le: "?xs ! i \<le> ?ys ! i" if "i \<in> {..<n}" for i
    using assms(6) l_xs l_ys that unfolding L_def ordered_set_lattice_def le_ordered_set_lattice_def
    by (auto simp add:list_all2_conv_all_nth)

  have xs_strict_mono: "strict_mono_on {..<n} ((!) ?xs)"
    using strict_sorted_list_of_set
    by (metis l_xs lessThan_iff sorted_wrt_iff_nth_less strict_mono_onI)

  hence inj_xs: "inj_on ((!) ?xs) {..<n}" using strict_mono_on_imp_inj_on by auto
  have "set ?xs = x" using set_sorted_list_of_set x by simp
  hence ran_xs: "((!) ?xs) ` {..<n} = x" using set_conv_nth unfolding l_xs[symmetric] by fast

  have "set ?ys = y"  using set_sorted_list_of_set y by simp
  hence ran_ys: "((!) ?ys) ` {..<n} = y" using set_conv_nth unfolding l_ys[symmetric] by fast

  have p1_strict_mono: "strict_mono_on x ?p1"
  proof (rule strict_mono_onI)
    fix r s assume a: "r \<in> x" "s \<in> x" "r < s"
    have "?p1 r \<in> {..<n}" using a ran_xs by (intro the_inv_into_into[OF inj_xs]) auto
    moreover have "?p1 s \<in> {..<n}" using a ran_xs by (intro the_inv_into_into[OF inj_xs]) auto
    moreover have "?xs ! (?p1 r) = r" using a ran_xs by (intro f_the_inv_into_f[OF inj_xs]) auto
    moreover have "?xs ! (?p1 s) = s" using a ran_xs by (intro f_the_inv_into_f[OF inj_xs]) auto
    ultimately show "?p1 r < ?p1 s" using a(3) strict_mono_on_leD[OF xs_strict_mono] by fastforce
  qed

  have ran_p1: "?p1 ` x = {..<n}" using ran_xs the_inv_into_onto[OF inj_xs] by simp

  have p2_strict_mono: "strict_mono_on {..<n} ?p2"
    using strict_sorted_list_of_set
    by (metis l_ys lessThan_iff sorted_wrt_iff_nth_less strict_mono_onI)

  define \<phi> where "\<phi> = (\<lambda>e. if e \<in> x then (?p2 (?p1 e)) else e)"

  have "strict_mono_on x (?p2 \<circ> ?p1)"
  proof (rule strict_mono_onI)
    fix r s assume a: "r \<in> x" "s \<in> x" "r < s"
    have "?p1 r < ?p1 s" using a strict_mono_onD[OF p1_strict_mono] by auto
    moreover have "?p1 r \<in> {..<n}" "?p1 s \<in> {..<n}" using a ran_p1 by auto
    ultimately show "(?p2 \<circ> ?p1) r < (?p2 \<circ> ?p1) s"
      using strict_mono_onD[OF p2_strict_mono] by simp
  qed

  hence \<phi>_strict_mono: "strict_mono_on x \<phi>" unfolding \<phi>_def strict_mono_on_def by simp
  hence \<phi>_inj: "inj_on \<phi> x" using strict_mono_on_imp_inj_on by auto

  have "\<phi> ` x \<subseteq> y" using ran_p1 ran_ys unfolding \<phi>_def by auto
  hence "\<phi> ` x = y" using card_image[OF \<phi>_inj] x y by (intro card_seteq) auto
  hence "bij_betw \<phi> x y" using \<phi>_inj unfolding bij_betw_def by auto

  moreover have "\<phi> e \<ge> e" for e
  proof (cases "e \<in> x")
    case True
    have "e = ?xs ! (?p1 e)"
      using True ran_xs by (intro f_the_inv_into_f[symmetric] inj_xs) auto
    also have "\<dots> \<le> ?p2 (?p1 e)" using ran_p1 True by (intro le) auto
    also have "\<dots> = \<phi> e" using True by (simp add:\<phi>_def)
    finally show ?thesis by simp
  next
    case False
    then show ?thesis  unfolding \<phi>_def by simp
  qed

  ultimately show ?thesis using \<phi>_strict_mono by auto
qed

definition "bij_pmf I F = pmf_of_set {f. bij_betw f I F \<and> f \<in> extensional I}"

lemma card_bijections':
  assumes "finite A" "finite B" "card A = card B"
  shows "card {f. bij_betw f A B \<and> f \<in> extensional A} = fact (card A)" (is "?L = ?R")
proof -
  have "?L = card {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B}"
    using bij_betw_imp_surj_on[where A="A" and B="B"]
    by (intro arg_cong[where f="card"] Collect_cong) (auto simp:PiE_def Pi_def)
  also have "\<dots> = fact (card A)" using card_bijections[OF assms] assms(3) by simp
  finally show ?thesis by simp
qed

lemma bij_betw_non_empty_finite:
  assumes "finite I" "finite F" "card I = card F"
  shows
    "finite {f. bij_betw f I F \<and> f \<in> extensional I}" (is ?T1)
    "{f. bij_betw f I F \<and> f \<in> extensional I} \<noteq> {}" (is ?T2)
proof -
  have "fact (card I) > (0::nat)" using fact_gt_zero by simp
  thus ?T1 ?T2
    using card_bijections'[OF assms]  card_gt_0_iff by force+
qed

lemma bij_pmf:
  assumes "finite I" "finite F" "card I = card F"
  shows
    "set_pmf (bij_pmf I F) = {f. bij_betw f I F \<and> f \<in> extensional I}"
    "finite (set_pmf (bij_pmf I F))"
  using bij_betw_non_empty_finite[OF assms] unfolding bij_pmf_def by auto

lemma expectation_ge_eval_at_point:
  assumes "\<And>y. y \<in> set_pmf p \<Longrightarrow> f y \<ge> (0::real)"
  assumes "integrable p f"
  shows "pmf p x * f x \<le> (\<integral>x. f x \<partial>p)" (is "?L \<le> ?R")
proof -
  have "?L = (\<Sum>a\<in>{x}. f a * of_bool(a=x) * pmf p a)" by simp
  also have "\<dots> = (\<integral>a. f a * of_bool (a = x) \<partial>p)"
    by (intro integral_measure_pmf_real[symmetric]) auto
  also have "\<dots> \<le> ?R"
    using assms by (intro integral_mono_AE' AE_pmfI) auto
  finally show ?thesis by simp
qed

lemma split_bij_pmf:
  assumes "finite I" "finite F" "card I = card F" "J \<subseteq> I"
  shows "bij_pmf I F =
    do {
      S \<leftarrow> pmf_of_set {S. card S = card J \<and> S \<subseteq> F};
      \<phi> \<leftarrow> bij_pmf J S;
      \<psi> \<leftarrow> bij_pmf (I-J) (F-S);
      return_pmf (merge J (I-J) (\<phi>, \<psi>))
    }" (is "?L = ?R")
proof (rule pmf_eq_iff_le)
  fix x

  let ?p1 = "pmf_of_set {S. card S = card J \<and> S \<subseteq> F}"
  let ?p2 = "bij_pmf J"
  let ?p3 = "(\<lambda>S. bij_pmf (I-J) (F-S))"

  have f0: "finite J" using finite_subset assms(1,4) by metis
  have f1: "finite (I-J)" using finite_subset assms(1,4) by force

  note pos1 = pmf_of_set[OF bij_betw_non_empty_finite(2,1)[OF assms(1-3)]]

  show "pmf (bij_pmf I F) x \<le> pmf ?R x"
  proof (cases "x \<in> set_pmf ?L")
    case True
    hence a:"bij_betw x I F" "x \<in> extensional I"
      using bij_pmf[OF assms(1-3)] by auto

    define T where "T = x ` J"
    define y where "y = restrict x J"
    define z where "z = restrict x (I-J)"

    have x_on_compl: "x ` (I-J) = (F-T)" using a assms(4) unfolding T_def bij_betw_def
      by (subst inj_on_image_set_diff[where C="I"]) auto

    have T_F: "T \<subseteq> F" using bij_betw_imp_surj_on[OF a(1)] assms(4) unfolding T_def by auto

    have f2: "finite T" using assms(2) T_F finite_subset by auto
    have f3: "finite (F - T)" using assms(2) T_F finite_subset by auto
    have c1: "card J = card T"
      unfolding T_def using assms(4) inj_on_subset bij_betw_imp_inj_on[OF a(1)]
      by (intro card_image[symmetric]) auto
    have c2: "card (I-J) = card (F-T)"
      unfolding x_on_compl[symmetric] using inj_on_subset bij_betw_imp_inj_on[OF a(1)]
      by (intro card_image[symmetric]) force

    have "restrict x (J \<union> (I - J)) = restrict x I" using assms(4) by force
    also have "\<dots> = x" using a extensional_restrict by auto
    finally have b:"restrict x (J \<union> (I - J)) = x" by simp

    have y: "y \<in> extensional J" "bij_betw y J T"
      using assms(4) inj_on_subset a y_def unfolding bij_betw_def T_def by auto

    have "z ` (I-J) = (F-T)" using x_on_compl unfolding z_def by auto
    hence z: "z \<in> extensional (I-J)" "bij_betw z (I-J) (F-T)"
      using a z_def unfolding bij_betw_def T_def by (auto intro:inj_on_diff)

    have pos_assms2: "{S. card S = card J \<and> S \<subseteq> F} \<noteq> {}" "finite {S. card S = card J \<and> S \<subseteq> F}"
      using T_F c1 by (auto intro!:  finite_subset[OF _ iffD2[OF finite_Pow_iff assms(2)]])

    note pos3 =
      pmf_of_set[OF bij_betw_non_empty_finite(2,1)[OF f0 f2 c1]]
      pmf_of_set[OF bij_betw_non_empty_finite(2,1)[OF f1 f3 c2]]

    have fin_pmf1: "finite (set_pmf ?p1)" using pos_assms2 set_pmf_of_set by simp
    note [simp] = integrable_measure_pmf_finite[OF fin_pmf1, where 'b="real"]

    have fin_pmf2: "finite (set_pmf (?p2 T))" by (intro bij_pmf[OF f0 f2 c1])
    note [simp] = integrable_measure_pmf_finite[OF fin_pmf2, where 'b="real"]

    have fin_pmf3: "finite (set_pmf (?p3 T))" by (intro bij_pmf[OF f1 f3 c2])
    note [simp] = integrable_measure_pmf_finite[OF fin_pmf3, where 'b="real"]

    have "pmf ?L x =  1 / real (card {f. bij_betw f I F \<and> f \<in> extensional I})"
      using a pos1 unfolding bij_pmf_def by simp
    also have "\<dots> = 1 / real (fact (card I))" using assms by (simp add: card_bijections')
    also have "\<dots> = 1 / real (fact (card J) * fact (card I-card J) * (card I choose card J))"
      using assms(1,4) card_mono by (subst binomial_fact_lemma) auto
    also have "\<dots> = 1 / real ((card F choose card J) * fact (card J) *  fact (card (I-J)))"
      using assms(3) card_Diff_subset[OF f0 assms(4)] by simp
    also have "\<dots> = 1/real(card {S. S\<subseteq>F\<and>card S=card J} * card {f. bij_betw f J T\<and>f\<in>extensional J} *
      card {f. bij_betw f (I-J) (F-T)\<and>f\<in>extensional (I-J)})"
      using f0 f1 f2 f3 assms(2) c1 c2 by (simp add:card_bijections' n_subsets)
    also have "\<dots> = pmf ?p1 T * pmf (?p2 T) y * pmf (?p3 T) z"
      using y z c1 T_F unfolding bij_pmf_def pos3 pmf_of_set[OF pos_assms2]
      by (simp add:conj_commute)
    also have "\<dots> = pmf ?p1 T * (pmf (?p2 T) y * (pmf (?p3 T) z * of_bool(merge J (I-J) (y, z) = x)))"
      unfolding y_def z_def merge_restrict merge_x_x_eq_restrict b by simp
    also have "\<dots> \<le> pmf ?p1 T * (pmf (?p2 T) y * (\<integral>\<psi>. of_bool(merge J (I-J) (y, \<psi>) = x) \<partial>?p3 T))"
      by (intro mult_left_mono expectation_ge_eval_at_point integral_nonneg_AE AE_pmfI) simp_all
    also have "\<dots> \<le> pmf ?p1 T * (\<integral>\<phi>. (\<integral>\<psi>. of_bool(merge J (I-J) (\<phi>, \<psi>) = x) \<partial>?p3 T) \<partial>?p2 T)"
      by (intro mult_left_mono expectation_ge_eval_at_point integral_nonneg_AE AE_pmfI) simp_all
    also have "\<dots> \<le> (\<integral>S. (\<integral>\<phi>. (\<integral>\<psi>. of_bool(merge J (I-J) (\<phi>, \<psi>) = x) \<partial>?p3 S) \<partial>?p2 S) \<partial>?p1)"
      by (intro expectation_ge_eval_at_point integral_nonneg_AE AE_pmfI) simp_all
    also have "\<dots> = pmf ?R x" unfolding pmf_bind by (simp add:indicator_def)
    finally show ?thesis by simp
  next
    case False
    hence "pmf ?L x = 0" by (simp add: set_pmf_iff)
    also have "\<dots> \<le> pmf ?R x" by simp
    finally show ?thesis by simp
  qed
qed

lemma map_bij_pmf:
  assumes "finite I" "finite F" "card I = card F" "inj_on \<phi> F"
  shows "map_pmf (\<lambda>f. (\<lambda>x\<in>I. \<phi>(f x))) (bij_pmf I F) = bij_pmf I (\<phi> ` F)"
proof-
  let ?h = "the_inv_into F \<phi>"

  have h_bij: "bij_betw ?h (\<phi> ` F) F"
    using assms(4) by (simp add: bij_betw_the_inv_into inj_on_imp_bij_betw)

  have "bij_betw  (\<lambda>f. (\<lambda>x\<in>I. \<phi>(f x)))
    {f. bij_betw f I F \<and> f \<in> extensional I} {f. bij_betw f I (\<phi> ` F) \<and> f \<in> extensional I}"
  proof (intro bij_betwI[where g="(\<lambda>f. (\<lambda>x\<in>I. ?h(f x)))"], goal_cases)
    case 1 thus ?case
      using bij_betw_trans[OF _ inj_on_imp_bij_betw[OF assms(4)], where A="I"]
      by (auto simp:comp_def)
  next
    case 2 thus ?case
      using bij_betw_trans[OF _ h_bij, where A="I"] by (auto simp:comp_def)
  next
    case (3 x)
    hence "x \<in> I \<rightarrow> F" "x \<in> extensional I" using bij_betw_imp_surj_on by auto
    hence "(\<lambda>\<omega>\<in>I. ?h ((\<lambda>y\<in>I. \<phi> (x y)) \<omega>)) \<omega> = x \<omega>" for \<omega>
      by (auto intro!:the_inv_into_f_f[OF assms(4)] simp: restrict_def extensional_def)
    thus ?case by auto
  next
    case (4 y)
    hence "y \<in> I \<rightarrow> (\<phi> ` F)" "y \<in> extensional I" using bij_betw_imp_surj_on by blast+
    hence "(\<lambda>x\<in>I. \<phi> ((\<lambda>x\<in>I. the_inv_into F \<phi> (y x)) x)) \<omega> = y \<omega>" for \<omega>
      by (auto intro!:f_the_inv_into_f[OF assms(4)] simp: restrict_def extensional_def)
    thus ?case by auto
  qed
  thus ?thesis
    unfolding bij_pmf_def by (intro map_pmf_of_set_bij_betw bij_betw_non_empty_finite assms)
qed

lemma pmf_of_multiset_eq_pmf_of_setI:
  assumes "c > 0"  "x \<noteq> {#}"
  assumes "\<And>i. i \<in> y \<Longrightarrow> count x i = c"
  assumes "\<And>i. i \<in># x \<Longrightarrow> i \<in> y"
  shows "pmf_of_multiset x = pmf_of_set y"
proof (rule pmf_eqI)
  fix i

  have a:"set_mset x = y" using assms(1,3,4) count_eq_zero_iff by force
  hence y_ne: "y \<noteq> {}" "finite y" using assms(2) by auto

  have "size x =  sum (count x) y" unfolding size_multiset_overloaded_eq a by simp
  also have "\<dots> = sum (\<lambda>_. c) y" by (intro sum.cong refl assms(3)) auto
  also have "\<dots> = c *card y" using y_ne by simp
  finally have "c * card y = size x" by simp
  hence rel: "real (size x)/real c = real (card y)"
    using assms(1) by (simp add:field_simps flip:of_nat_mult)

  have "pmf (pmf_of_multiset x) i = real (count x i) / real (size x)"
    using assms(2) by simp
  also have "\<dots> = real c * of_bool(i \<in> y) / real (size x)"
    using assms by (auto simp:of_bool_def count_eq_zero_iff)
  also have "\<dots> = of_bool(i \<in> y) / real (card y)"
    unfolding rel[symmetric] by simp
  also have "\<dots> = pmf (pmf_of_set y) i"
    using y_ne by simp
  finally show "pmf (pmf_of_multiset x) i = pmf (pmf_of_set y) i" by simp
qed

lemma card_multi_bij:
  assumes "finite J"
  assumes "I = \<Union>(A ` J)" "disjoint_family_on A J"
  assumes "\<And>j. j \<in> J \<Longrightarrow> finite (A j) \<and> finite (B j) \<and> card (A j) = card (B j)"
    shows "card {f. (\<forall>j\<in>J. bij_betw f (A j) (B j)) \<and> f\<in>extensional I} = (\<Prod>i\<in>J. fact (card (A i)))"
      (is "card ?L = ?R")
proof -
  define g where "g i = (THE j. j \<in> J \<and> i \<in> A j)" for i
  have g: "g i = j" if "i \<in> A j" "j \<in> J" for i j unfolding g_def
  proof (rule the1_equality)
    show "\<exists>!j. j \<in> J \<and> i \<in> A j"
      using assms(3) that unfolding bex1_def disjoint_family_on_def by auto
    show "j \<in> J \<and> i \<in> A j" using that by auto
  qed

  have "bij_betw (\<lambda>\<phi>. (\<lambda>i\<in>I. \<phi> (g i) i))
    (PiE J (\<lambda>j. {f. bij_betw f (A j) (B j) \<and> f\<in>extensional (A j)})) ?L"
  proof (intro bij_betwI[where g= "\<lambda>x. \<lambda>i\<in>J. restrict x (A i)"] Pi_I, goal_cases)
    case (1 x)
    have "bij_betw (\<lambda>i\<in>I. x (g i) i) (A j) (B j)" if "j \<in> J" for j
    proof -
      have last:"bij_betw (x j) (A j) (B j)" using that 1 by auto
      have "A j \<subseteq> I" using that assms(2) by auto
      thus ?thesis using g that by (intro iffD2[OF bij_betw_cong last]) auto
    qed
    thus ?case using 1 by auto
  next
    case (2 x)
    thus ?case by (intro iffD2[OF restrict_PiE_iff] ballI) simp
  next
    case (3 x)
    have "restrict (\<lambda>i\<in>I. x (g i) i) (A j) = x j" if "j \<in> J" for j
    proof -
      have "A j \<subseteq> I" using that assms(2) by auto
      moreover have "x j \<in> extensional (A j)" using that 3 by auto
      hence "restrict (\<lambda>i. x (g i) i) (A j) = x j"
        using g that unfolding restrict_def extensional_def by auto
      ultimately show ?thesis unfolding restrict_restrict using Int_absorb1 by metis
    qed
    thus ?case using 3 unfolding extensional_def PiE_def  by auto
  next
    case (4 y)
    have "(\<lambda>j\<in>J. restrict y (A j)) (g i) i = y i" if that':"i \<in> I" for i
    proof -
      obtain j where "i \<in> A j" "j \<in> J" using that' assms(2) by auto
      thus ?thesis using g by simp
    qed
    thus ?case using 4 unfolding extensional_def by auto
  qed

  hence "card ?L = card (PiE J (\<lambda>j. {f. bij_betw f (A j) (B j)\<and> f\<in>extensional (A j)}))"
    using bij_betw_same_card[symmetric] by auto
  also have "\<dots> = (\<Prod>i\<in>J. card {f. bij_betw f (A i) (B i) \<and> f \<in> extensional (A i)})"
    unfolding card_PiE[OF assms(1)] by simp
  also have "\<dots> = (\<Prod>i\<in>J. fact (card (A i)))"
    using assms(4) by (intro prod.cong card_bijections') auto
  finally show ?thesis by simp
qed

lemma map_bij_pmf_non_inj:
  fixes I :: "'a set"
  fixes F :: "'b set"
  fixes \<phi> :: "'b \<Rightarrow> 'c"
  assumes "finite I" "finite F" "card I = card F"
  defines "q \<equiv> {f. f \<in> extensional I \<and> {#f x. x \<in># mset_set I#} = {#\<phi> x. x\<in># mset_set F#}}"
  shows "map_pmf (\<lambda>f. (\<lambda>x\<in>I. \<phi>(f x))) (bij_pmf I F) = pmf_of_set q" (is "?L = _")
proof -
  let ?G = "{# \<phi> x. x \<in># mset_set F #}"
  let ?G' = "set_mset ?G"
  define c :: nat where "c = (\<Prod>i \<in> set_mset ?G. fact (count ?G i))"

  note ne = bij_betw_non_empty_finite[OF assms(1-3)]
  note cim = count_image_mset_eq_card_vimage

  have "c \<ge> 1" unfolding c_def by (intro prod_ge_1) auto
  hence c_gt_0: "c > 0" by simp

  have "?L = pmf_of_multiset {#\<lambda>x\<in>I. \<phi> (f x). f \<in># mset_set {f. bij_betw f I F\<and>f\<in>extensional I}#}"
    unfolding bij_pmf_def by (intro map_pmf_of_set[OF ne])
  also have "\<dots> = pmf_of_set q" unfolding q_def
  proof (rule pmf_of_multiset_eq_pmf_of_setI[OF c_gt_0],goal_cases)
    case 1
    have "card {f. bij_betw f I F \<and> f \<in> extensional I} > 0" using ne by fastforce
    thus ?case by (simp add:nonempty_has_size)
  next
    case (2 f)

    hence a: "image_mset f (mset_set I) = image_mset \<phi> (mset_set F)" by simp
    hence "card {x \<in> F. \<phi> x = g} = card {x \<in> I. f x = g}" for g
      using cim[OF assms(1)] cim[OF assms(2)] by metis
    hence b: "card (\<phi> -` {g} \<inter> F) = card (f -` {g} \<inter> I)" for g
      by (auto simp add:Int_def conj_commute)

    have c:"bij_betw \<omega> I F \<and> (\<lambda>i\<in>I. \<phi> (\<omega> i))=f \<longleftrightarrow> (\<forall>g\<in>?G'. bij_betw \<omega> (f -`{g} \<inter>I) (\<phi>-`{g} \<inter>F))"
      (is "?L1 = ?R1") for \<omega>
    proof
      assume ?L1
      hence d:"bij_betw \<omega> I F" and e: "\<forall>i \<in> I. \<phi> (\<omega> i) = f i" by auto
      have "bij_betw \<omega> (f -`{g} \<inter> I) (\<phi> -` {g} \<inter> F)" if "g \<in> ?G'" for g
      proof -
        have "card (\<phi> -` {g} \<inter> F) =  card (\<omega> ` (f -` {g} \<inter> I))"
          unfolding b using d
          by (intro card_image[symmetric]) (simp add: bij_betw_imp_inj_on inj_on_Int)
        hence " \<omega> ` (f -` {g} \<inter> I) = \<phi> -` {g} \<inter> F"
          using assms(2) e bij_betw_imp_surj_on[OF d] by (intro card_seteq image_subsetI) auto
        thus ?thesis by (intro bij_betw_subset[OF d]) auto
      qed
      thus ?R1 by auto
    next
      assume f:?R1

      have g: "\<phi> (\<omega> i) = f i" if "i \<in> I" for i
      proof -
        have "f i \<in> ?G'" unfolding a[symmetric] using that assms(1) by auto
        hence "\<omega> ` (f -` {f i} \<inter> I) = (\<phi> -` {f i} \<inter> F)"
          using bij_betw_imp_surj_on using f by metis
        thus ?thesis using that by (auto simp add:vimage_def)
      qed
      have "x = y" if "x \<in> I" "y \<in> I" "\<omega> x = \<omega> y" for x y
      proof -
        have "f x \<in> ?G'" unfolding a[symmetric] using that assms(1) by auto
        hence "inj_on \<omega> (f -` {f x} \<inter> I)" using f bij_betw_imp_inj_on by blast
        moreover have "f x = f y" using that g by metis
        ultimately show "x = y" using that(1,2,3) inj_onD[where f="\<omega>", OF _ that(3)] by fastforce
      qed
      hence h:"inj_on \<omega> I" by (rule inj_onI)

      have i: "\<omega> ` I \<subseteq> F"
      proof (rule image_subsetI)
        fix x assume "x \<in> I"
        hence "f x \<in> ?G'" "x \<in> (f -` {f x} \<inter> I)" using assms(1) unfolding a[symmetric] by auto
        thus "\<omega> x \<in> F" using bij_betw_imp_surj_on f by fast
      qed
      have "bij_betw \<omega> I F"
        using card_image[OF h] assms(3) unfolding bij_betw_def
        by (intro conjI card_seteq i h assms) auto
      thus ?L1 using g 2 unfolding restrict_def extensional_def by auto
    qed

    have j: "f ` I \<subseteq> \<phi> ` F" using a
      by (metis assms(1,2) finite_set_mset_mset_set multiset.set_map set_eq_subset)

    have "c = (\<Prod>g \<in> ?G'. fact (card (f -` {g} \<inter> I)))"
      unfolding b[symmetric] c_def cim[OF assms(2)]
      by (simp add:vimage_def Int_def conj_commute)
    also have "\<dots> = card {\<omega>. (\<forall>g \<in> ?G'. bij_betw \<omega> (f-`{g} \<inter> I) (\<phi>-`{g} \<inter> F)) \<and> \<omega> \<in> extensional I}"
      using assms(1,2) j b
      by (intro card_multi_bij[symmetric]) (auto simp: vimage_def disjoint_family_on_def)
    also have "\<dots> = card {\<omega>. bij_betw \<omega> I F \<and> \<omega> \<in> extensional I \<and> (\<lambda>i\<in>I. \<phi> (\<omega> i)) = f}"
      using c by (intro arg_cong[where f="card"] Collect_cong) auto
    finally show ?case using ne by (subst count_image_mset_eq_card_vimage) auto
  next
    case (3 f)
    then obtain u where u_def:"bij_betw u I F" "u \<in> extensional I" "f = (\<lambda>x. \<lambda>xa\<in>I. \<phi> (x xa)) u"
      using ne by auto

    have "image_mset f (mset_set I) = image_mset \<phi> (image_mset u (mset_set I))"
      using assms(1) unfolding u_def(3) multiset.map_comp by (intro image_mset_cong) auto
    also have "\<dots> = image_mset \<phi> (mset_set F)" using image_mset_mset_set u_def(1)
      unfolding bij_betw_def by (intro arg_cong2[where f="image_mset"] refl) auto
    finally have "image_mset f (mset_set I) = image_mset \<phi> (mset_set F)" by simp

    moreover have "f \<in> extensional I" unfolding u_def(3) by auto
    ultimately show ?case by simp
  qed
  finally show ?thesis by simp
qed

lemmas fkg_inequality_pmf_internalized = fkg_inequality_pmf[unoverload_type 'a]

lemma permutation_distributions_are_neg_associated:
  fixes F :: "('a :: linorder_topology) set"
  fixes I :: "'b set"
  assumes "finite F" "finite I" "card I = card F"
  shows "measure_pmf.neg_assoc (bij_pmf I F) (\<lambda>i \<omega>. \<omega> i) I"
proof (rule measure_pmf.neg_assocI2, goal_cases)
  case (1 i) thus ?case by simp
next
  case (2 f g J)

  have fin_J: "finite J"  using 2(1) assms(2) finite_subset by metis
  have fin_I_J: "finite (I-J)"  using 2(1) assms(2) finite_subset by blast

  define k where "k = card J"

  have k_le_F: "k \<le> card F" unfolding k_def using 2(1) assms(2,3) card_mono by force

  let ?p0 = "bij_pmf I F"
  let ?p1 = "pmf_of_set {S. card S = card J \<and> S \<subseteq> F}"
  let ?p2 = "\<lambda>S. bij_pmf J S"
  let ?p3 = "\<lambda>S. bij_pmf (I - J) (F - S)"

  note set_pmf_p0 = bij_pmf[OF assms(2,1,3)]

  note integrable_p0[simp] = integrable_measure_pmf_finite[OF set_pmf_p0(2), where 'b="real"]

  note dep_f = 2(2)
  note dep_g = 2(3)

  have bounded_f: "bounded (f ` S)" for S using bounded_subset[OF 2(6) image_mono] by simp
  have bounded_g: "bounded (g ` S)" for S using bounded_subset[OF 2(7) image_mono] by simp

  note mono_f = 2(4)
  note mono_g = 2(5)

  let ?L = "ordered_set_lattice F k"

  define f' where "f' S = (\<integral>\<phi>. f \<phi> \<partial>?p2 S)" for S
  define g' where "g' S = (\<integral>\<phi>. g \<phi> \<partial>?p3 S)" for S

  interpret L: finite_ne_distrib_lattice "ordered_set_lattice F k"
    by (intro ordered_set_lattice_lattice assms(1) k_le_F)

  have carr_L_ne: "carrier ?L \<noteq> {}" and fin_L: "finite (carrier ?L)"
    using ordered_set_lattice_carrier_finite_ne[OF assms(1) k_le_F] by auto

  have mono_f': "monotone_on (carrier ?L) (\<sqsubseteq>\<^bsub>?L\<^esub>) (\<le>) f'"
  proof (rule monotone_onI)
    fix S T
    assume a:"S \<sqsubseteq>\<^bsub>?L\<^esub> T" "S \<in> carrier ?L" "T \<in> carrier ?L"
    then obtain \<rho> where \<rho>_bij: "bij_betw \<rho> S T" and \<rho>_inc: "\<And>e. \<rho> e \<ge> e"
      using bij_betw_ord_set_lattice_pairs[OF assms(1) k_le_F] by blast

    note S_carr = ordered_set_lattice_carrier[OF a(2)]
    have c:"card J = card S" using S_carr k_def by auto

    note set_pmf_p2 = bij_pmf[OF fin_J S_carr(1) c]
    note int = integrable_measure_pmf_finite[OF set_pmf_p2(2)]

    have "f' S = (\<integral>\<phi>. f (\<lambda>\<omega>\<in>J. \<phi> \<omega>) \<partial>?p2 S)" unfolding f'_def
      using set_pmf_p2 extensional_restrict by (intro integral_cong_AE AE_pmfI) force+
    also have "\<dots> \<le> (\<integral>\<phi>. f (\<lambda>\<omega>\<in>J. \<rho>(\<phi> \<omega>)) \<partial>?p2 S)" unfolding f'_def
      using \<rho>_inc unfolding restrict_def
      by (intro integral_mono_AE AE_pmfI monoD[OF mono_f] int) (auto simp: le_fun_def)
    also have "\<dots> = (\<integral>\<phi>. f \<phi> \<partial>(map_pmf (\<lambda>\<phi>. (\<lambda>\<omega>\<in>J. \<rho>(\<phi> \<omega>))) (?p2 S)))" by simp
    also have "\<dots> = (\<integral>\<phi>. f \<phi> \<partial>(?p2 (\<rho> ` S)))"
      using ordered_set_lattice_carrier[OF a(2)] k_def
      by (intro arg_cong2[where f="measure_pmf.expectation"] map_bij_pmf refl
          bij_betw_imp_inj_on[OF \<rho>_bij] fin_J) auto
    also have "\<dots> = (\<integral>\<phi>. f \<phi> \<partial>?p2 T)" using bij_betw_imp_surj_on[OF \<rho>_bij] by simp
    finally show "f' S \<le> f' T" unfolding f'_def by simp
  qed

  have mono_g': "monotone_on (carrier ?L) (\<sqsubseteq>\<^bsub>?L\<^esub>) (\<le>) ((*)(-1) \<circ> g')"
  proof (rule monotone_onI)
    fix S T
    let ?M = "ordered_set_lattice F (card F-k)"
    assume a:"S \<sqsubseteq>\<^bsub>?L\<^esub> T" "S \<in> carrier ?L" "T \<in> carrier ?L"
    hence a': "(F-T) \<sqsubseteq>\<^bsub>?M\<^esub> (F-S)" "(F-S) \<in> carrier ?M" "(F-T) \<in> carrier ?M"
      using ordered_set_lattice_dual[OF assms(1) k_le_F] by auto
    then obtain \<rho> where \<rho>_bij: "bij_betw \<rho> (F-T) (F-S)" and \<rho>_inc: "\<And>e. \<rho> e \<ge> e"
      using bij_betw_ord_set_lattice_pairs[OF assms(1)] k_le_F by (meson diff_le_self)
    note T_carr = ordered_set_lattice_carrier[OF a'(3)]

    have c: "card (I-J) = card (F-T)"
      using assms ordered_set_lattice_carrier[OF a(3)] k_def 2(1) fin_J
      by (simp add: card_Diff_subset)
    note set_pmf_p3 = bij_pmf[OF fin_I_J T_carr(1) c]
    note int = integrable_measure_pmf_finite[OF set_pmf_p3(2)]

    have "g' T = (\<integral>\<phi>. g (\<lambda>\<omega>\<in>I-J. \<phi> \<omega>) \<partial>?p3 T)" unfolding g'_def
      using set_pmf_p3 extensional_restrict by (intro integral_cong_AE AE_pmfI) force+
    also have "\<dots> \<le> (\<integral>\<phi>. g (\<lambda>\<omega>\<in>I-J. \<rho>(\<phi> \<omega>)) \<partial>?p3 T)" unfolding g'_def restrict_def using \<rho>_inc
      by (intro integral_mono_AE AE_pmfI monoD[OF mono_g] int) (auto simp: le_fun_def)
    also have "\<dots> = (\<integral>\<phi>. g \<phi> \<partial>(map_pmf (\<lambda>\<phi>. (\<lambda>\<omega>\<in>I-J. \<rho>(\<phi> \<omega>))) (?p3 T)))" by simp
    also have "\<dots> = (\<integral>\<phi>. g \<phi> \<partial>(bij_pmf (I - J) (\<rho> ` (F-T))))" using assms
      by (intro arg_cong2[where f="measure_pmf.expectation"] map_bij_pmf refl
          bij_betw_imp_inj_on[OF \<rho>_bij] fin_J c) auto
    also have "\<dots> = (\<integral>\<phi>. g \<phi> \<partial>?p3 S)" using bij_betw_imp_surj_on[OF \<rho>_bij] by simp
    finally have "g' T \<le> g' S" unfolding g'_def by simp
    thus "((*) (- 1) \<circ> g') S \<le> ((*) (- 1) \<circ> g') T" by simp
  qed

  have "(\<integral>S. f' S * g' S \<partial>?p1) \<le> (\<integral>S. f' S \<partial>?p1) * (\<integral>S. g' S \<partial>?p1)"
    if td: "\<exists>(Rep :: 'x \<Rightarrow> 'a set) Abs. type_definition Rep Abs (carrier ?L)"
  proof -
    obtain Rep :: "'x \<Rightarrow> 'a set" and Abs where td:"type_definition Rep Abs (carrier ?L)"
      using td by auto
    interpret type_definition Rep Abs "carrier ?L" using td by auto

    have carr_L: "carrier ?L = {S. card S = card J \<and> S \<subseteq> F}"
      using finite_subset[OF _ assms(1)] unfolding ordered_set_lattice_def k_def
      by (auto simp add:set_eq_iff)

    have Rep_bij: "bij_betw Rep UNIV {S. card S = card J \<and> S \<subseteq> F}"
      using Rep_range Rep_inject carr_L unfolding bij_betw_def by (intro conjI inj_onI) auto

    have fin_UNIV: "finite (UNIV :: 'x set)"
      using fin_L carr_L Rep_bij  bij_betw_finite by metis

    let ?p1' = "pmf_of_set (UNIV :: 'x set)"
    have rep_p1: "?p1 = map_pmf Rep ?p1'"
      by (intro UNIV_not_empty map_pmf_of_set_bij_betw[symmetric] Rep_bij fin_UNIV)

    note * = L.transfer_to_type[OF fin_L td]

    note fkg = fkg_inequality_pmf_internalized[OF *]

    have mono_rep_f': "monotone (\<lambda>S T. Rep S \<sqsubseteq>\<^bsub>?L\<^esub> Rep T) (\<le>) (f' \<circ> Rep)"
      using mono_f' Rep unfolding monotone_on_def by simp
    have mono_rep_g': "monotone (\<lambda>S T. Rep S \<sqsubseteq>\<^bsub>?L\<^esub> Rep T) (\<ge>) (g' \<circ> Rep)"
      using mono_g' Rep unfolding monotone_on_def by simp
    have pmf_const: "pmf ?p1' x = 1/(real (CARD('x)))" for x
      by (subst pmf_of_set[OF _ fin_UNIV]) auto

    have "(\<integral>S. f' S * g' S \<partial>?p1) = (\<integral>S. f' (Rep S) * g' (Rep S) \<partial>?p1')"
      unfolding rep_p1 by simp
    also have "\<dots> \<le> (\<integral>S. f' (Rep S)  \<partial>?p1') *  (\<integral>S. g' (Rep S)  \<partial>?p1')"
      using mono_rep_f' mono_rep_g'
      by (intro fkg[where \<tau>="Fwd" and \<sigma>="Rev", simplified]) (simp_all add:comp_def pmf_const)
    also have "\<dots> = (\<integral>S. f' S  \<partial>?p1) *  (\<integral>S. g' S  \<partial>?p1)"
      unfolding rep_p1 by simp
    finally show "(\<integral>S. f' S * g' S \<partial>?p1) \<le> (\<integral>S. f' S \<partial>?p1) * (\<integral>S. g' S \<partial>?p1)" by simp
  qed

  note core_result = this[cancel_type_definition, OF carr_L_ne]

  note split_p0 = split_bij_pmf[OF assms(2,1,3) 2(1)]

  have "(\<integral>x. f x * g x \<partial>bij_pmf I F)  =
    (\<integral>S. (\<integral>\<phi>. (\<integral>\<psi>. f(merge J (I-J) (\<phi>,\<psi>))*g(merge J (I-J) (\<phi>,\<psi>)) \<partial>?p3 S) \<partial>?p2 S) \<partial>?p1)"
    unfolding k_def by (simp add:split_p0 bounded_intros bounded_f bounded_g integral_bind_pmf)
  also have "\<dots> = (\<integral>S. (\<integral>\<phi>. (\<integral>\<psi>. f \<phi>*g \<psi> \<partial>?p3 S) \<partial>?p2 S) \<partial>?p1)"
    by (intro integral_cong_AE AE_pmfI arg_cong2[where f="(*)"] depends_onD2[OF dep_f]
        depends_onD2[OF dep_g]) simp_all
  also have "\<dots> = (\<integral>S. (\<integral>\<phi>. f \<phi> \<partial>?p2 S) * (\<integral>\<psi>. g \<psi> \<partial>?p3 S) \<partial>?p1)" by simp
  also have "\<dots> \<le> (\<integral>S. (\<integral>\<phi>. f \<phi> \<partial>?p2 S) \<partial>?p1) * (\<integral>S. (\<integral>\<phi>. g \<phi> \<partial>?p3 S) \<partial>?p1)"
    using core_result unfolding f'_def g'_def by simp
  also have "\<dots> = (\<integral>S.(\<integral>\<phi>.(\<integral>\<psi>. f \<phi> \<partial>?p3 S) \<partial>?p2 S) \<partial>?p1) * (\<integral>S.(\<integral>\<phi>.(\<integral>\<psi>. g \<psi> \<partial>?p3 S) \<partial>?p2 S) \<partial>?p1)"
    by simp
  also have "\<dots> =
    (\<integral>S. (\<integral>\<phi>. (\<integral>\<psi>. f (merge J (I-J) (\<phi>,\<psi>)) \<partial>?p3 S) \<partial>?p2 S) \<partial>?p1) *
    (\<integral>S. (\<integral>\<phi>. (\<integral>\<psi>. g (merge J (I-J) (\<phi>,\<psi>)) \<partial>?p3 S) \<partial>?p2 S) \<partial>?p1)"
    by (intro arg_cong2[where f="(*)"] integral_cong_AE AE_pmfI depends_onD2[OF dep_f]
        depends_onD2[OF dep_g]) simp_all
  also have "\<dots> = (\<integral>x. f x \<partial>?p0) * (\<integral>x. g x \<partial>?p0)"
    unfolding k_def by (simp add:split_p0 bounded_intros bounded_f bounded_g integral_bind_pmf)
  finally show "(\<integral>x. f x * g x \<partial>?p0) \<le> (\<integral>x. f x \<partial>?p0)*(\<integral>x. g x \<partial>?p0)" by simp
qed

lemma multiset_permutation_distributions_are_neg_associated:
  fixes F :: "('a :: linorder_topology) multiset"
  fixes I :: "'b set"
  assumes "finite I" "card I = size F"
  defines "p \<equiv> pmf_of_set {\<phi>. \<phi> \<in> extensional I \<and> image_mset \<phi> (mset_set I) = F}"
  shows "measure_pmf.neg_assoc p (\<lambda>i \<omega>. \<omega> i) I"
proof -
  let ?xs = "sorted_list_of_multiset F"
  define \<alpha> where "\<alpha> k = ?xs ! (min k (length ?xs -1))" for k

  let ?N = "{..<size F}"
  let ?h = "(\<lambda>f. (\<lambda>i\<in>I. \<alpha> (f i)))"

  have sorted_xs: "sorted ?xs" by (induction F, auto simp:sorted_insort)

  have mono_\<alpha>: "mono \<alpha>"
  proof (cases "?xs = []")
    case True thus ?thesis unfolding \<alpha>_def by simp
  next
    case False thus ?thesis unfolding \<alpha>_def
      by (intro monoI sorted_nth_mono[OF sorted_xs]) (simp_all add: min.strict_coboundedI2)
  qed

  have l_xs: "length ?xs = size F" by (metis mset_sorted_list_of_multiset size_mset)

  have "image_mset \<alpha> (mset_set {..<size F}) = image_mset ((!) ?xs) (mset_set {..<size F})"
    unfolding \<alpha>_def l_xs[symmetric] by (intro image_mset_cong) auto
  also have "\<dots> = mset ?xs" unfolding l_xs[symmetric]
    by (metis map_nth mset_map mset_set_upto_eq_mset_upto)
  also have "\<dots> = F" by simp
  finally have 0:"image_mset \<alpha> (mset_set {..<size F}) = F" by simp

  have "map_pmf (\<lambda>f. (\<lambda>i\<in>I. \<alpha> (f i))) (bij_pmf I ?N) =
    pmf_of_set {f \<in> extensional I. image_mset f (mset_set I) = image_mset \<alpha> (mset_set {..<size F})}"
    using assms by (intro map_bij_pmf_non_inj) auto
  also have "\<dots> = p" unfolding p_def 0 by simp
  finally have 1:"map_pmf (\<lambda>f. (\<lambda>i\<in>I. \<alpha> (f i))) (bij_pmf I ?N) = p" by simp

  have 2:"measure_pmf.neg_assoc (bij_pmf I {..<size F}) (\<lambda>i \<omega>. \<omega> i) I"
    using assms(1,2) by (intro permutation_distributions_are_neg_associated) auto

  have "measure_pmf.neg_assoc (bij_pmf I {..<size F}) (\<lambda>i \<omega>. if i \<in> I then \<alpha>(\<omega> i) else undefined) I"
    using mono_\<alpha> by (intro measure_pmf.neg_assoc_compose_simple[OF assms(1) 2, where \<eta>="Fwd"]
    borel_measurable_continuous_onI) simp_all
  hence "measure_pmf.neg_assoc (map_pmf (\<lambda>f. (\<lambda>i\<in>I. \<alpha>(f i))) (bij_pmf I {..<size F})) (\<lambda>i \<omega>. \<omega> i) I"
    by (simp add:neg_assoc_map_pmf restrict_def if_distrib if_distribR)
  thus ?thesis unfolding 1 by simp
qed

lemma n_subsets_prob:
  assumes "d \<le> card S" "finite S" "s \<in> S"
  shows
    "measure_pmf.prob (pmf_of_set {a. a \<subseteq> S \<and> card a = d}) {\<omega>. s \<notin> \<omega>} = (1 - real d/card S)"
    "measure_pmf.prob (pmf_of_set {a. a \<subseteq> S \<and> card a = d}) {\<omega>. s \<in> \<omega>} = real d/card S"
proof -
  let ?C = "{a. a \<subseteq> S \<and> card a = d}"

  have "card ?C > 0" unfolding  n_subsets[OF assms(2)] using zero_less_binomial[OF assms(1)] by simp
  hence ne:"?C \<noteq> {}" "finite ?C" using card_gt_0_iff by blast+

  have card_S_gt_0: "card S > 0" using assms(2,3) card_gt_0_iff by auto

  have "measure (pmf_of_set ?C) {x. s \<notin> x} = real (card {T. T\<subseteq>S \<and> card T = d \<and> s \<notin> T}) / card ?C"
    by (subst measure_pmf_of_set[OF ne]) (simp_all add:Int_def)
  also have "\<dots> = real (card {T. T\<subseteq>(S-{s}) \<and> card T = d}) / card ?C"
    by (intro arg_cong2[where f="(\<lambda>x y. real (card x)/y)"] Collect_cong) auto
  also have "\<dots> = real(card (S - {s}) choose d) / real (card S choose d)"
    using assms(1,2) by (subst (1 2) n_subsets) auto
  also have "\<dots> = real((card S - 1) choose d) / real (card S choose d)" using assms by simp
  also have "\<dots> = real(card S *((card S-1) choose d)) / real (card S * (card S choose d))"
    using card_S_gt_0 by simp
  also have "\<dots> = real (card S - d) / real (card S)"
    unfolding binomial_absorb_comp[symmetric] by simp
  also have "\<dots> = (real (card S) - real d) / real (card S)"
    using assms by (subst of_nat_diff) auto
  also have "\<dots> = (1 - real d/card S)" using card_S_gt_0 by (simp add:field_simps)
  finally show "measure (pmf_of_set ?C) {x. s \<notin> x} = (1 - real d/card S)" by simp

  hence \<open>1-measure (pmf_of_set ?C) {x. s \<notin> x} = real d/card S\<close> by simp
  thus "measure_pmf.prob (pmf_of_set ?C) {\<omega>. s \<in> \<omega>} = real d/card S"
    by (subst (asm) measure_pmf.prob_compl[symmetric]) (auto simp:diff_eq Compl_eq)
qed

lemma n_subsets_distribution_neg_assoc:
  assumes "finite S" "k \<le> card S"
  defines "p \<equiv> pmf_of_set {T. T \<subseteq> S \<and> card T = k}"
  shows "measure_pmf.neg_assoc p (\<in>) S"
proof -
  define F :: "bool multiset" where "F = replicate_mset k True + replicate_mset (card S - k) False"
  let ?qset = "{ \<phi> \<in> extensional S. image_mset \<phi> (mset_set S) = F }"
  define q where "q = pmf_of_set ?qset"

  have a: "card S = size F" unfolding F_def using assms(2) by simp

  have b: "image_mset \<phi> (mset_set S) = F \<longleftrightarrow> card (\<phi> -` {True} \<inter> S) = k"
    (is "?L \<longleftrightarrow> ?R") for \<phi>
  proof -
    have de:"card (\<phi>-`{False}\<inter>S) + card (\<phi>-`{True}\<inter>S) = card S"
      using assms(1) by (subst card_Un_disjoint[symmetric]) (auto intro:arg_cong[where f="card"])

    have "?L \<longleftrightarrow> (\<forall>i. count {#\<phi> x. x\<in>#mset_set S#} i = count F i)" using multiset_eq_iff by blast
    also have "\<dots> \<longleftrightarrow> (\<forall>i. card (\<phi> -` {i} \<inter> S) = count F i)"
      unfolding count_image_mset_eq_card_vimage[OF assms(1)] vimage_def Int_def
      by (simp add:conj_commute)
    also have "\<dots> \<longleftrightarrow> card (\<phi> -` {True} \<inter> S) = k \<and> card (\<phi> -` {False} \<inter> S) = (card S-k)"
      unfolding F_def using assms(1) by auto
    also have "\<dots> \<longleftrightarrow> ?R" using assms(2) de by auto
    finally show ?thesis by simp
  qed

  have "bij_betw (\<lambda>\<omega>. \<lambda>s\<in>S. s\<in>\<omega>) {T. T\<subseteq>S \<and> card T = k} ?qset" unfolding b
    by (intro bij_betwI[where g="\<lambda>\<phi>. {x. x \<in> S \<and> \<phi> x}"] Pi_I ext)
     (auto intro: arg_cong[where f="card"] simp:extensional_def vimage_def Int_def conj_commute)
  moreover have "card {T. T \<subseteq> S \<and> card T = k} > 0"
    unfolding n_subsets[OF assms(1)] by (intro zero_less_binomial assms(2))
  hence "{T. T \<subseteq> S \<and> card T = k} \<noteq> {} \<and> finite {T. T \<subseteq> S \<and> card T = k}"
    using card_gt_0_iff by blast
  ultimately have c: "map_pmf (\<lambda>\<omega>. \<lambda>s\<in>S. s\<in>\<omega>) p = q"
    unfolding p_def q_def by (intro map_pmf_of_set_bij_betw) auto

  have "measure_pmf.neg_assoc (map_pmf (\<lambda>\<omega>. \<lambda>s\<in>S. s\<in>\<omega>) p) (\<lambda>i \<omega>. \<omega> i) S"
    unfolding c q_def by (intro multiset_permutation_distributions_are_neg_associated a assms(1))
  hence d:"measure_pmf.neg_assoc p (\<lambda>s \<omega>. if s \<in> S then (s \<in> \<omega>) else undefined) S"
    unfolding neg_assoc_map_pmf by (simp add:restrict_def cong:if_cong)
  show ?thesis by (intro measure_pmf.neg_assoc_cong[OF assms(1) _ d] AE_pmfI) auto
qed

end