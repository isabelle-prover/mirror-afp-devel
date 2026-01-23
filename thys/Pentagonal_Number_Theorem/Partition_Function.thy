section \<open>The partition function\<close>
theory Partition_Function
imports
  Pentagonal_Numbers
  "Theta_Functions.Jacobi_Triple_Product"
  "Card_Number_Partitions.Card_Number_Partitions"
begin

subsection \<open>Definition\<close>

text \<open>
  In the AFP, there is already a definition of the restricted partition number $p_k(n)$, which 
  counts the number of ways to write the integer $n$ as a sum of exactly $k$ positive integers 
  (without taking order into account). More formally, it counts the number of multisets $X$ such 
  that $X \subseteq \mathbb{N}\setminus\{0\}$ and $|X| = k$ and $\sum X = n$.

  We now define the partition function $p(n)$, which counts the number of unrestricted number
  partitions, i.e.\ it removes the condition that there be exactly $k$ parts~\oeiscite{A000041}.
  In other words: $p(n) = \sum_{k\leq n} p_k(n)$.
\<close>
definition Partition' :: "nat \<Rightarrow> nat"
  where "Partition' n = (\<Sum>k\<le>n. Partition n k)"
                                      
lemma Partition'_0 [simp]: "Partition' 0 = 1"
  by (simp add: Partition'_def)

lemma Partition'_eq_card: "Partition' n = card {f. f partitions n}"
  using card_partitions[of n] by (simp add: Partition'_def)

lemma Partition'_pos: "Partition' n > 0"
proof -
  have *: "(\<lambda>i. if i = 1 then n else 0) partitions n"
    unfolding partitions_def
  proof
    have "(\<Sum>i\<le>n. (if i = 1 then n else 0) * i) = (\<Sum>i\<in>(if n = 0 then {} else {1::nat}). n)"
      by (rule sum.mono_neutral_cong_right) (auto split: if_splits)
    also have "\<dots> = n"
      by auto
    finally show "(\<Sum>i\<le>n. (if i = 1 then n else 0) * i) = n" .
  qed auto
  have "Partition' n = card {f. f partitions n}"
    unfolding Partition'_eq_card ..
  also have "\<dots> > 0"
    by (subst card_gt_0_iff) (use * in \<open>auto intro: finite_partitions\<close>)
  finally show ?thesis .
qed

lemma Partition'_Suc_gt:
  assumes "0 < m"
  shows   "Partition' m < Partition' (Suc m)"
proof -
  have "1 = Partition m 1"
    using assms Partition_parts1[of "m-1"] by simp
  also have "Partition m 1 = (\<Sum>k\<in>{0}. Partition (m - k) (Suc k))"
    by simp
  also have "(\<Sum>k\<in>{0}. Partition (m - k) (Suc k)) \<le> (\<Sum>k\<le>m. Partition (m - k) (Suc k))"
    by (intro sum_mono2) auto
  finally have pos: "(\<Sum>k\<le>m. Partition (m - k) (Suc k)) > 0"
    by linarith

  have "Partition' (Suc m) = (\<Sum>k\<le>Suc m. Partition (Suc m) k)"
    by (simp add: Partition'_def)
  also have "\<dots> = (\<Sum>k\<le>m. Partition (Suc m) (Suc k))"
    by (subst sum.atMost_Suc_shift) simp
  also have "\<dots> = Partition' m + (\<Sum>k\<le>m. Partition (m - k) (Suc k))"
    by (simp add: sum.distrib Partition'_def)
  finally have "Partition' (Suc m) = Partition' m + (\<Sum>k\<le>m. Partition (m - k) (Suc k))" .
  with pos show ?thesis
    by linarith
qed

lemma Partition'_strict_mono:
  assumes "0 < m" "m < n"
  shows   "Partition' m < Partition' n"
  using assms(2)
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n = Suc m")
    case True
    thus ?thesis
      using less.prems \<open>m > 0\<close> by (simp add: Partition'_Suc_gt)
  next
    case False
    have "Partition' m < Partition' (n - 1)"
      by (rule less.IH) (use False \<open>m > 0\<close> less.prems in auto)
    also have "\<dots> < Partition' (Suc (n - 1))"
      by (rule Partition'_Suc_gt) (use False \<open>m > 0\<close> less.prems in auto)
    also have "Suc (n - 1) = n"
      using False \<open>m > 0\<close> less.prems by simp
    finally show ?thesis .
  qed
qed

lemma Partition'_mono:
  assumes "m \<le> n"
  shows   "Partition' m \<le> Partition' n"
  using Partition'_strict_mono assms 
  by (metis Partition'_0 Partition'_pos bot_nat_0.extremum_strict
            less_one linorder_le_less_linear order_le_less)


subsection \<open>Generating function\<close>

text \<open>
  Next, we will move on to derive a closed-form expression for the generating function
  $\sum_{n\geq 0} p(n) X^n$ of $p(n)$ in terms of an infinite product.

  The first step is the following lemma: there is a one-to-once correspondence between
  the number partitions of $n$ and the ways to distribute $n$ balls onto the natural numbers 
  such that the number of balls in the $i$-th bin is a multiple of $i+1$.
\<close>
lemma bij_betw_multisets_of_size_partitions:
  "bij_betw (\<lambda>X i. if i = 0 then 0 else count X (i - 1) div i)
     {X\<in>multisets_of_size UNIV n. \<forall>i. Suc i dvd count X i} {h. h partitions n}"
proof -
  define f :: "nat multiset \<Rightarrow> nat \<Rightarrow> nat"
    where "f = (\<lambda>X i. if i = 0 then 0 else count X (i - 1) div i)"
  define g :: "(nat \<Rightarrow> nat) \<Rightarrow> nat multiset"
    where "g = (\<lambda>h. Abs_multiset (\<lambda>i. h (Suc i) * Suc i))"
  have count_g: "count (g h) = (\<lambda>i. h (Suc i) * Suc i)" if h: "h partitions n" for h
    unfolding g_def
  proof (rule count_Abs_multiset)
    have "finite {i. i > 0 \<and> h i > 0}"
      using _ partitions_imp_finite_elements[OF h]
      by (rule finite_subset) auto
    also have "bij_betw (\<lambda>i. i-1) {i. i > 0 \<and> h i > 0} {i. h (Suc i) * Suc i > 0}"
      by (rule bij_betwI[of _ _ _ "\<lambda>i. i + 1"]) auto
    hence "finite {i. i > 0 \<and> h i > 0} \<longleftrightarrow> finite {i. h (Suc i) * Suc i > 0}"
      by (rule bij_betw_finite)
    finally show "finite {i. h (Suc i) * Suc i > 0}" .
  qed

  define A where "A = {X\<in>multisets_of_size UNIV n. \<forall>i. Suc i dvd count X i}"
  have "bij_betw f A {h. h partitions n}"
  proof (rule bij_betwI)
    show f: "f \<in> A \<rightarrow> {h. h partitions n}"
    proof safe
      fix X assume X: "X \<in> A"
      have X': "size X = n" "\<And>i. Suc i dvd count X i"
        using X by (auto simp: A_def multisets_of_size_def)
      have X_support: "i < n" if i: "i \<in># X" for i
      proof -
        have "Suc i \<le> count X i"
          using dvd_imp_le[OF X'(2)[of i]] i by (auto simp: f_def)
        also have "\<dots> \<le> size X"
          by (rule count_le_size)
        also have "\<dots> = n"
          using X'(1) by simp
        finally show "i < n"
          by simp
      qed

      show "f X partitions n"
      proof (rule partitionsI)
        fix i assume i: "f X i \<noteq> 0"
        hence "count X (i - 1) \<noteq> 0"
          by (intro notI) (auto simp: f_def split: if_splits)
        hence "(i - 1) \<in># X"
          by simp
        moreover have "i > 0"
          using i by (auto simp: f_def split: if_splits)
        ultimately show "1 \<le> i \<and> i \<le> n"
          using X_support[of "i-1"] by (auto simp: f_def)
      next
        have "(\<Sum>i\<le>n. f X i * i) = (\<Sum>i=1..n. f X i * i)"
          by (rule sum.mono_neutral_right) auto
        also have "\<dots> = (\<Sum>i<n. f X (Suc i) * Suc i)"
          by (intro sum.reindex_bij_witness[of _ "\<lambda>i. i+1" "\<lambda>i. i-1"]) auto
        also have "\<dots> = (\<Sum>i<n. count X i)"
        proof (rule sum.cong)
          fix i assume "i \<in> {..<n}"
          have "f X (Suc i) * Suc i = count X i div Suc i * Suc i"
            by (simp add: f_def)
          also have "\<dots> = count X  i"
            using X'(2)[of i] by (rule dvd_div_mult_self)
          finally show "f X (Suc i) * Suc i = count X i" .
        qed auto
        also have "\<dots> = (\<Sum>i\<in>set_mset X. count X i)"
          by (intro sum.mono_neutral_right) (use X_support in \<open>auto simp: not_in_iff\<close>)
        also have "\<dots> = size X"
          by (simp add: size_multiset_overloaded_eq)
        also have "\<dots> = n"
          using X'(1) by simp
        finally show "(\<Sum>i\<le>n. f X i * i) = n" .
      qed
    qed

    show g: "g \<in> {h. h partitions n} \<rightarrow> A"
      unfolding A_def
    proof safe
      fix h assume h: "h partitions n"
      note count_g = count_g[OF h]

      show "Suc i dvd count (g h) i" for i
        unfolding count_g by (rule dvd_triv_right)
      have support: "{i. count (g h) i > 0} \<subseteq> {..<n}"
      proof safe
        fix i assume "count (g h) i > 0"
        hence "h (Suc i) > 0"
          by (auto simp: count_g)
        hence "Suc i \<le> n"
          using partitionsE(1)[OF h] by blast
        thus "i < n"
          by auto
      qed

      have "size (g h) = (\<Sum>i | count (g h) i > 0. count (g h) i)"
        unfolding size_multiset_overloaded_eq by (rule sum.cong) auto
      also have "\<dots> = (\<Sum>i<n. count (g h) i)"
        by (rule sum.mono_neutral_left) (use support in \<open>auto simp: not_in_iff\<close>)
      also have "\<dots> = (\<Sum>i=1..n. count (g h) (i-1))"
        by (rule sum.reindex_bij_witness[of _ "\<lambda>i. i-1" "\<lambda>i. i+1"]) auto
      also have "\<dots> = (\<Sum>i=1..n. h i * i)"
        by (intro sum.cong) (auto simp: count_g algebra_simps)
      also have "\<dots> = (\<Sum>i\<le>n. h i * i)"
        by (intro sum.mono_neutral_left) auto
      also have "\<dots> = n"
        using h by (simp add: partitions_def)
      finally show "g h \<in> multisets_of_size UNIV n"
        unfolding multisets_of_size_def by simp
    qed

    show "g (f X) = X" if X: "X \<in> A" for X
    proof (rule multiset_eqI)
      fix i :: nat
      have dvd: "Suc i dvd count X i"
        using that by (auto simp: A_def)
      have "f X partitions n"
        using f X by blast
      hence "count (g (f X)) i = f X (Suc i) * Suc i"
        by (simp add: count_g)
      also have "\<dots> = count X i div Suc i * Suc i"
        by (simp add: f_def)
      also have "\<dots> = count X i"
        using dvd by (rule dvd_div_mult_self)
      finally show "count (g (f X)) i = count X i" .
    qed

    show "f (g h) = h" if h: "h \<in> {h. h partitions n}" for h
    proof
      fix i :: nat
      have count_g: "count (g h) = (\<lambda>i. h (Suc i) * Suc i)"
        using count_g[of h] h by simp
      show "f (g h) i = h i"
      proof (cases "i = 0")
        case True
        have "h 0 = 0"
          using that by (auto simp: partitions_def)
        thus ?thesis
          using True by (auto simp: f_def)
      next
        case False
        thus ?thesis
          by (simp add: f_def count_g algebra_simps)
      qed
    qed
  qed
  thus ?thesis
    unfolding f_def A_def .
qed

text \<open>
  We can now easily derive our closed-form expression, namely:
  \[\sum_{n\geq 0} p(n) X^n = \prod_{k\geq 1} \frac{1}{1-X^k} = \frac{1}{\phi(X)}\]
  where $\phi(X)$ is Euler's function (not to be confused with Euler's totient function
  $\varphi(n)$).
\<close>
lemma has_prod_Partition'_aux:
  "(\<lambda>k. \<Prod>i\<le>k. 1 / (1 - fps_X ^ Suc i)) \<longlonglongrightarrow> Abs_fps (\<lambda>n. of_nat (Partition' n) 
      :: 'a :: {field, t2_space})" (is "?F \<longlonglongrightarrow> ?G")
proof -
  define F :: "nat \<Rightarrow> 'a fps" where "F = (\<lambda>i. 1 / (1 - fps_X ^ Suc i))"
  have F_altdef: "F i = fps_compose (Abs_fps (\<lambda>_. 1)) (fps_X ^ Suc i)" for i
    by (simp add: fps_compose_sub_distrib gp F_def del: power_Suc)
  have fps_nth_F: "fps_nth (F i) j = (if Suc i dvd j then 1 else 0)" for i j
    by (auto simp: F_altdef fps_nth_compose_X_power simp del: power_Suc)
  have subdegree_F: "subdegree (1 - F i) = Suc i" for i
  proof -
    have "F i - 1 = fps_compose (Abs_fps (\<lambda>_. 1) - 1) (fps_X ^ Suc i)"
      by (simp add: F_altdef fps_compose_sub_distrib)
    also have "subdegree \<dots> = subdegree (Abs_fps (\<lambda>_. 1 :: 'a) - 1) * Suc i"
      by (subst subdegree_fps_compose) auto
    also have "subdegree (Abs_fps (\<lambda>_. 1::'a) - 1) = 1"
      by (rule subdegreeI) auto
    finally show ?thesis
      by simp
  qed
  have [simp]: "F i \<noteq> 0" for i
    using subdegree_F[of i] by auto
  have ev: "eventually (\<lambda>i. N \<le> subdegree (F i - 1)) at_top" for N
    using eventually_ge_at_top[of N]
    by eventually_elim (auto simp del: power_Suc simp: subdegree_F)

  have "(\<lambda>n. prod F {..n}) \<longlonglongrightarrow> 
          Abs_fps (\<lambda>n. \<Sum>X\<in>multisets_of_size {..n} n. \<Prod>i\<le>n. fps_nth (F i) (count X i))"
  proof (rule tendsto_prod_fps)
    have "Abs_fps (\<lambda>_. 1 :: 'a) \<noteq> 0"
      by (auto simp: fps_eq_iff)
    thus "F k \<noteq> 0" for k
      unfolding F_altdef by (auto simp: fps_compose_eq_0_iff)
  next
    fix n k :: nat
    assume "n < k"
    thus "n < subdegree (F k - 1)"
      by (auto simp: subdegree_F)
  qed

  also have "(\<lambda>n. \<Sum>X\<in>multisets_of_size {..n} n. \<Prod>i\<le>n. fps_nth (F i) (count X i)) = (\<lambda>n. of_nat (Partition' n))"
  proof
    fix n :: nat
    have "(\<Sum>X\<in>multisets_of_size {..n} n. \<Prod>i\<le>n. fps_nth (F i) (count X i)) = 
          (\<Sum>X\<in>multisets_of_size {..n} n. if \<exists>i\<le>n. \<not>Suc i dvd count X i then 0 else 1::'a)"
      by (rule sum.cong) (auto simp: fps_nth_F)
    also have "(\<Sum>X\<in>multisets_of_size {..n} n. if \<exists>i\<le>n. \<not>Suc i dvd count X i then 0 else 1::'a) =
               (\<Sum>X | X \<in> multisets_of_size {..n} n \<and> (\<forall>i\<le>n. Suc i dvd count X i). 1)"
      by (rule sum.mono_neutral_cong_right) auto
    also have "\<dots> = of_nat (card {X. X \<in> multisets_of_size {..n} n \<and> (\<forall>i\<le>n. Suc i dvd count X i)})"
      by simp
    also have "{X. X \<in> multisets_of_size {..n} n \<and> (\<forall>i\<le>n. Suc i dvd count X i)} =
               {X. X \<in> multisets_of_size UNIV n \<and> (\<forall>i. Suc i dvd count X i)}" (is "?lhs = ?rhs")
    proof (intro equalityI subsetI)
      fix X assume X: "X \<in> ?lhs"
      hence X: "X \<in> multisets_of_size {..n} n" "\<And>i. i \<le> n \<Longrightarrow> Suc i dvd count X i"
        by blast+
      have dvd: "Suc i dvd count X i" for i
      proof (cases "i \<le> n")
        case False
        hence "i \<notin># X"
          using X(1) by (auto simp: multisets_of_size_def)
        thus ?thesis
          by (simp add: not_in_iff)
      qed (use X(2) in auto)
      thus "X \<in> ?rhs"
        using X multisets_of_size_mono[of "{..n}" UNIV] by auto
    next
      fix X assume X: "X \<in> ?rhs"
      hence X: "size X = n" "\<And>i. Suc i dvd count X i"
        unfolding multisets_of_size_def by auto
      have "set_mset X \<subseteq> {..n}"
      proof safe
        fix i assume "i \<in># X"
        hence "Suc i \<le> count X i "
          by (intro dvd_imp_le[OF X(2)]) auto
        also have "\<dots> \<le> size X"
          by (simp add: count_le_size)
        also have "\<dots> = n"
          using X(1) by simp
        finally show "i \<le> n"
          by simp
      qed
      thus "X \<in> ?lhs"
        using X by (simp_all add: multisets_of_size_def)
    qed
    also have "card \<dots> = card {h. h partitions n}"
      by (rule bij_betw_same_card, rule bij_betw_multisets_of_size_partitions)
    also have "\<dots> = Partition' n"
      by (simp add: Partition'_eq_card)
    finally show "(\<Sum>X\<in>multisets_of_size {..n} n. \<Prod>i\<le>n. fps_nth (F i) (count X i)) = 
                    of_nat (Partition' n)" .
  qed
  finally show ?thesis
    unfolding F_def .
qed

theorem has_prod_Partition':
  "(\<lambda>i. 1 / (1 - fps_X ^ Suc i)) has_prod Abs_fps (\<lambda>n. of_nat (Partition' n) 
      :: 'a :: {field, t2_space})" (is "?F has_prod ?G")
proof -
  have "fps_nth (Abs_fps (\<lambda>n. of_nat (Partition' n))) 0 \<noteq> fps_nth 0 0"
    by (auto simp: Partition'_def)
  hence "Abs_fps (\<lambda>n. of_nat (Partition' n) :: 'a) \<noteq> 0"
    by metis
  hence "raw_has_prod ?F 0 ?G"
    unfolding raw_has_prod_def using has_prod_Partition'_aux[where ?'a = 'a] by simp
  thus ?thesis
    unfolding has_prod_def by blast
qed

end