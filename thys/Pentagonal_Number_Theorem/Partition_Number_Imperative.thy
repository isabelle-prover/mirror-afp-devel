subsection \<open>Efficient implementation\<close>
theory Partition_Number_Imperative
imports
  Pentagonal_Number_Theorem
  "Refine_Monadic.Refine_Monadic"
  "Refine_Imperative_HOL.IICF"
begin

text \<open>
  Using the aforementioned recurrence, we can easily compute $p(n)$ given $p(0),\ldots,p(n-1)$.
  We split the sum into one sum for $k > 0$ and one for $k < 0$. In the first one, we start with
  $k = 1$, add $(-1)^{k+1} p(n - g_k)$ to our accumulator, and increment $k$, until $g_k > n$.
  The second sum is analogous except that we start with $k = -1$ and decrement in every step.

  We do not show it, but the number of terms to sum over is roughly  
  $\frac{\sqrt{24n}}{3}\approx 1.633 \sqrt{n} \in O(n^{1/2})$.
  Since $p(n)$ has roughly $3.7 \sqrt{n} \in \Theta(n^{1/2})$ bits, this means that in order to
  compute $p(0), \ldots, p(n)$ we have to do add $O(n^{3/2})$ numbers with up to $O(n^{1/2})$
  bits each, which gives the total algorithm a running time of roughly $O(n^2)$.
  Since the output itself has $O(n^{3/2})$ bits, this is not too bad.

  What we are doing here to compute $p(0),\ldots,p(n)$ is in fact to take the power series of
  $\phi(X)$ and compute $(1 / \phi(X))\ \text{mod}\ X^{n+1}$ (i.e.\ the first $n$ coefficients of its
  multiplicative inverse) in the na\"ive way. This works very well, since the power series of 
  $\phi(X)$ is easy to compute and also very sparse (i.e.\ out of the
  first $n$ coefficients, only $O(\sqrt{n})$ are non-zero).

  One way to get a better running time would be to use a more sophisticated method of computing
  reciprocals of power series, e.g.\ by Hensel lifting. In principle, this is very easy to implement
  and prove correct, but to be faster than the present method in practice it requires a fast
  algorithm for polynomial multiplication: if used with a polynomial multiplication algorithm that
  uses $O(M(n))$ coefficient operations (i.e.\ addition/multiplication of coefficients) for a 
  polynomial of degree $n$, Hensel lifting also uses $O(M(n))$ coefficient operations.
  Since the coefficients have size up to $O(n^{1/2})$ bits, this gives us a total running time of
  $O(M(n) n^{1/2})$. For an FFT-based $O(n \log n)$ multiplication algorithm, we therefore
  have the quasi-optimal $O(n^{3/2} \log(n))$. However, for less sophisticated algorithms such as
  Karatsuba multiplication or na\"ive multiplication, this actually ends up being less efficient
  than the above approach.

  Note that if one only wants to compute a single $p(n)$, this can be done much faster, namely
  in $O(\sqrt{n})$ time, using Rademacher's sum. However, this requires a significant additional
  amount of mathematics and, more importantly, infrastructure to approximate transcendental 
  functions to high precision.
\<close>

definition Partition'_list :: "nat \<Rightarrow> int list"
  where "Partition'_list n = map (int \<circ> Partition') [0..<n+1]"


subsubsection \<open>The first sum\<close>

definition partition_impl1_inner1_aux where
  "partition_impl1_inner1_aux n ps k =
     (\<Sum>i=1..<k. (if even i then -1 else 1) * ps ! nat (n - int (pent_num i)))"

definition partition_impl1_inner1_aux' where
  "partition_impl1_inner1_aux' n ps =
     (\<Sum>i | i \<ge> 1 \<and> int (pent_num i) \<le> n. (if even i then -1 else 1) * ps ! nat (n - int (pent_num i)))"

definition partition_impl1_inner1_invar where
  "partition_impl1_inner1_invar n ps acc0 = (\<lambda>(k,acc).
     k > 0 \<and> int (pent_num (k - 1)) \<le> n \<and>
     acc = acc0 + partition_impl1_inner1_aux n ps k)"

definition partition_impl1_inner1 :: "int \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> int nres" where
  "partition_impl1_inner1 n ps acc = do {
     (k,acc) \<leftarrow>
       WHILE\<^sub>T\<^bsup>partition_impl1_inner1_invar n ps acc\<^esup> (\<lambda>(k,_). int (pent_num k) \<le> n) (\<lambda>(k,acc). do {
         ASSERT (n - int (pent_num k) \<in> {0..<int (length ps)});
         let x = ps ! nat (n - int (pent_num k));
         RETURN (k + 1, if even k then acc - x else acc + x)
       })
       (1, acc);
     RETURN acc
  }"

lemma partition_impl1_inner1_aux_rec:
  assumes k: "k \<ge> 1"
  shows   "partition_impl1_inner1_aux n ps (1 + k) =
             partition_impl1_inner1_aux n ps k + (if even k then -1 else 1) * ps ! nat (n - int (pent_num k))" 
proof -
  have "partition_impl1_inner1_aux n ps (1 + k) = 
        (\<Sum>i\<in>insert k {1..<k}. (if even i then - 1 else 1) * ps ! nat (n - int (pent_num i)))"
    unfolding partition_impl1_inner1_aux_def using k by (intro sum.cong refl) auto
  also have "\<dots> = partition_impl1_inner1_aux n ps k + (if even k then -1 else 1) * ps ! nat (n - int (pent_num k))"
    by (subst sum.insert) (auto simp: partition_impl1_inner1_aux_def add_ac)
  finally show ?thesis .
qed

lemma partition_impl1_final:
  assumes "partition_impl1_inner1_invar n ps acc (k, acc')" "int (pent_num k) > n"
  shows "acc' = acc + partition_impl1_inner1_aux' n ps"
proof -
  have "partition_impl1_inner1_aux n ps k = partition_impl1_inner1_aux' n ps"
    unfolding partition_impl1_inner1_aux_def partition_impl1_inner1_aux'_def
  proof (intro sum.cong refl)
    have "pent_num (i - 1) < pent_num i" if "i > 0" for i
      by (rule strict_mono_pent_num) (use that in auto)
    show "{1..<k} = {i. 1 \<le> i \<and> int (pent_num i) \<le> n}"
    proof (intro equalityI subsetI)
      fix i assume i: "i \<in> {1..<k}"
      have "pent_num i \<le> pent_num (k-1)"
        using i by (auto simp: pent_num_le_iff_nonneg)
      also have "\<dots> \<le> n"
        using assms by (auto simp: partition_impl1_inner1_invar_def)
      finally show "i \<in> {i. 1 \<le> i \<and> int (pent_num i) \<le> n}"
        using i by auto
    next
      fix i assume i: "i \<in> {i. 1 \<le> i \<and> int (pent_num i) \<le> n}"
      have k: "int (pent_num (k - 1)) \<le> n" "k > 0"
        using assms by (auto simp: partition_impl1_inner1_invar_def)
      have "int (pent_num i) \<le> n"
        using i by simp
      also have "n < int (pent_num k)"
        using assms by auto
      finally have "pent_num i < pent_num k"
        by linarith
      hence "i < k"
        using i \<open>k > 0\<close> by (simp add: pent_num_less_iff_nonneg)
      with i show "i \<in> {1..<k}"
        by auto
    qed
  qed
  thus ?thesis
    using assms(1) by (simp add: partition_impl1_inner1_invar_def)
qed

lemma partition_impl1_inner1_correct [refine_vcg]:
  assumes "n \<in> {1..int (length ps)}"
  shows   "partition_impl1_inner1 n ps acc \<le>
             SPEC (\<lambda>acc'. acc' = acc + partition_impl1_inner1_aux' n ps)"
  unfolding partition_impl1_inner1_def
  apply refine_vcg
       apply (rule wf_measure[of "\<lambda>(k,_). nat n + 1 - pent_num k"])
  subgoal
    using assms
    by (auto simp: partition_impl1_inner1_invar_def partition_impl1_inner1_aux_def)
  subgoal for k_acc' k acc
    using assms strict_mono_pent_num[of 0 k]
    by (auto simp: partition_impl1_inner1_invar_def)
  subgoal for k_acc' k acc'
    using assms
    by (auto simp: partition_impl1_inner1_invar_def partition_impl1_inner1_aux_rec algebra_simps
                   nat_diff_distrib)
  subgoal for k_acc' k acc'
    using assms
    by (auto simp: partition_impl1_inner1_invar_def intro!: diff_less_mono2 simp: strict_mono_pent_num)
  subgoal for k_acc' k acc'
    using partition_impl1_final[of n ps acc k acc'] by simp
  done


definition partition_impl2_inner1 :: "int \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> int nres" where
  "partition_impl2_inner1 n ps acc = do {
     (_, _, acc') \<leftarrow>
       WHILE\<^sub>T (\<lambda>(k,i,_). i \<ge> 0) (\<lambda>(k,i,acc). do {
         ASSERT (nat i < length ps);
         let x = ps ! nat i;
         RETURN (k + 1, i - (3 * k + 1), if even k then acc - x else acc + x)
       })
       (1, n - 1, acc);
     RETURN acc'
  }"

lemma partition_impl2_inner1_refine [refine]:
  "partition_impl2_inner1 n ps acc \<le> \<Down>Id (partition_impl1_inner1 n ps acc)"
proof -
  define R where "R = br (\<lambda>(k,i,acc). (k,acc)) (\<lambda>(k,i,acc::int). i = n - int (pent_num k))"
  note [refine_dref_RELATES] =  RELATESI[of R]
  (* TODO: Why do I have to do this manually? refine_rcg refuses to take R as a relator\<dots> *)
  define w2 where "w2 = WHILE\<^sub>T (\<lambda>(k, i, _). 0 \<le> i)
     (\<lambda>(k, i, acc).
         ASSERT (nat i < length ps) \<bind>
         (\<lambda>_. let x = ps ! nat i
               in RETURN (k + 1, i - (3 * k + 1), if even k then acc - x else acc + x))) (1, n - 1, acc)"
  define w1 where "w1 = WHILE\<^sub>T\<^bsup>partition_impl1_inner1_invar n ps acc\<^esup>
          (\<lambda>(k, _). int (pent_num k) \<le> n)
          (\<lambda>(k, acc).
              ASSERT (n - int (pent_num k) \<in> {0..<int (length ps)}) \<bind>
              (\<lambda>_. let x = ps ! nat (n - int (pent_num k))
                    in RETURN (k + 1, if even k then acc - x else acc + x))) (1, acc)"
  have [refine_vcg]: "w2 \<le> \<Down>R w1"
    unfolding w1_def w2_def
    by refine_rcg (auto simp: R_def br_def pent_num_def[of 1] pent_num_increment)
  have "do {(_,_,acc') \<leftarrow> w2; RETURN acc'} \<le> \<Down>int_rel (do {(_,acc') \<leftarrow> w1; RETURN acc'})"
    by refine_vcg (auto simp: R_def br_def)
  thus ?thesis
    unfolding partition_impl2_inner1_def partition_impl1_inner1_def w1_def w2_def .
qed

lemma partition_impl2_inner1_correct [refine_vcg]:
  assumes "n \<in> {1..int (length ps)}"
  shows   "partition_impl2_inner1 n ps acc \<le> SPEC (\<lambda>acc'. acc' = acc + partition_impl1_inner1_aux' n ps)"
proof (rule order.trans[OF _ partition_impl1_inner1_correct[OF assms]])
  show "partition_impl2_inner1 n ps acc \<le> partition_impl1_inner1 n ps acc"
    using partition_impl2_inner1_refine[of n ps acc] by simp
qed


definition partition_impl1_inner2_aux where
  "partition_impl1_inner2_aux n ps k =
     (\<Sum>i=1..<k. (if even i then -1 else 1) * ps ! nat (n - int (pent_num (-i))))"

definition partition_impl1_inner2_aux' where
  "partition_impl1_inner2_aux' n ps =
     (\<Sum>i | i \<ge> 1 \<and> int (pent_num (-i)) \<le> n. (if even i then -1 else 1) * ps ! nat (n - int (pent_num (-i))))"

definition partition_impl1_inner2_invar where
  "partition_impl1_inner2_invar n ps acc0 = (\<lambda>(k,acc).
     k > 0 \<and> int (pent_num (-(k - 1))) \<le> n \<and>
     acc = acc0 + partition_impl1_inner2_aux n ps k)"

definition partition_impl1_inner2 :: "int \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> int nres" where
  "partition_impl1_inner2 n ps acc = do {
     (k,acc) \<leftarrow>
       WHILE\<^sub>T\<^bsup>partition_impl1_inner2_invar n ps acc\<^esup> (\<lambda>(k,_). int (pent_num (-k)) \<le> n) (\<lambda>(k,acc). do {
         ASSERT (n - int (pent_num (-k)) \<in> {0..<int (length ps)});
         let x = ps ! nat (n - int (pent_num (-k)));
         RETURN (k + 1, if even k then acc - x else acc + x)
       })
       (1, acc);
     RETURN acc
  }"

lemma partition_impl1_inner2_aux_rec:
  assumes k: "k \<ge> 1"
  shows   "partition_impl1_inner2_aux n ps (1 + k) =
             partition_impl1_inner2_aux n ps k + (if even k then -1 else 1) * ps ! nat (n - int (pent_num (-k)))" 
proof -
  have "partition_impl1_inner2_aux n ps (1 + k) = 
        (\<Sum>i\<in>insert k {1..<k}. (if even i then - 1 else 1) * ps ! nat (n - int (pent_num (-i))))"
    unfolding partition_impl1_inner2_aux_def using k by (intro sum.cong refl) auto
  also have "\<dots> = partition_impl1_inner2_aux n ps k + (if even k then -1 else 1) * ps ! nat (n - int (pent_num (-k)))"
    by (subst sum.insert) (auto simp: partition_impl1_inner2_aux_def add_ac)
  finally show ?thesis .
qed

lemma partition_impl1_inner2_final:
  assumes "partition_impl1_inner2_invar n ps acc (k, acc')" "int (pent_num (-k)) > n"
  shows "acc' = acc + partition_impl1_inner2_aux' n ps"
proof -
  have "partition_impl1_inner2_aux n ps k = partition_impl1_inner2_aux' n ps"
    unfolding partition_impl1_inner2_aux_def partition_impl1_inner2_aux'_def
  proof (intro sum.cong refl)
    have "pent_num (-(i-1)) < pent_num (-i)" if "i > 0" for i
      by (rule strict_antimono_pent_num) (use that in auto)
    show "{1..<k} = {i. 1 \<le> i \<and> int (pent_num (-i)) \<le> n}"
    proof (intro equalityI subsetI)
      fix i assume i: "i \<in> {1..<k}"
      have "pent_num (-i) \<le> pent_num (-(k-1))"
        using i by (auto simp: pent_num_le_iff_nonpos)
      also have "\<dots> \<le> n"
        using assms by (auto simp: partition_impl1_inner2_invar_def)
      finally show "i \<in> {i. 1 \<le> i \<and> int (pent_num (-i)) \<le> n}"
        using i by auto
    next
      fix i assume i: "i \<in> {i. 1 \<le> i \<and> int (pent_num (-i)) \<le> n}"
      have k: "int (pent_num (-(k - 1))) \<le> n" "k > 0"
        using assms by (auto simp: partition_impl1_inner2_invar_def)
      have "int (pent_num (-i)) \<le> n"
        using i by simp
      also have "n < int (pent_num (-k))"
        using assms by auto
      finally have "pent_num (-i) < pent_num (-k)"
        by linarith
      hence "i < k"
        using i \<open>k > 0\<close> by (simp add: pent_num_less_iff_nonpos)
      with i show "i \<in> {1..<k}"
        by auto
    qed
  qed
  thus ?thesis
    using assms(1) by (simp add: partition_impl1_inner2_invar_def)
qed

lemma partition_impl1_inner2_correct [refine_vcg]:
  assumes "n \<in> {1..int (length ps)}"
  shows   "partition_impl1_inner2 n ps acc \<le>
             SPEC (\<lambda>acc'. acc' = acc + partition_impl1_inner2_aux' n ps)"
  unfolding partition_impl1_inner2_def
  apply refine_vcg
       apply (rule wf_measure[of "\<lambda>(k,_). nat n + 1 - pent_num (-k)"])
  subgoal
    using assms
    by (auto simp: partition_impl1_inner2_invar_def partition_impl1_inner2_aux_def)
  subgoal for k_acc' k acc'
    using assms strict_antimono_pent_num[of "-k" 0]
    by (auto simp: partition_impl1_inner2_invar_def)
  subgoal for k_acc' k acc'
    using assms
    by (auto simp: partition_impl1_inner2_invar_def partition_impl1_inner2_aux_rec algebra_simps
                   nat_diff_distrib)
  subgoal for k_acc' k acc'
    using assms
    by (auto simp: partition_impl1_inner2_invar_def intro!: diff_less_mono2 simp: strict_antimono_pent_num)
  subgoal for k_acc' k acc'
    using partition_impl1_inner2_final[of n ps acc k acc'] by simp
  done


subsubsection \<open>The second sum\<close>

definition partition_impl2_inner2 :: "int \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> int nres" where
  "partition_impl2_inner2 n ps acc = do {
     (_, _, acc') \<leftarrow>
       WHILE\<^sub>T (\<lambda>(k,i,_). i \<ge> 0) (\<lambda>(k,i,acc). do {
         ASSERT (nat i < length ps);
         let x = ps ! nat i;
         RETURN (k + 1, i - (3 * k + 2), if even k then acc - x else acc + x)
       })
       (1, n - 2, acc);
     RETURN acc'
  }"

lemma partition_impl2_inner2_refine [refine]:
  "partition_impl2_inner2 n ps acc \<le> \<Down>Id (partition_impl1_inner2 n ps acc)"
proof -
  define R where "R = br (\<lambda>(k,i,acc). (k,acc)) (\<lambda>(k,i,acc::int). i = n - int (pent_num (-k)))"
  note [refine_dref_RELATES] =  RELATESI[of R]
  (* TODO: Why do I have to do this manually? refine_rcg refuses to take R as a relator\<dots> *)
  define w2 where "w2 = WHILE\<^sub>T (\<lambda>(k, i, _). 0 \<le> i)
     (\<lambda>(k, i, acc).
         ASSERT (nat i < length ps) \<bind>
         (\<lambda>_. let x = ps ! nat i
               in RETURN (k + 1, i - (3 * k + 2), if even k then acc - x else acc + x))) (1, n - 2, acc)"
  define w1 where "w1 = WHILE\<^sub>T\<^bsup>partition_impl1_inner2_invar n ps acc\<^esup>
          (\<lambda>(k, _). int (pent_num (-k)) \<le> n)
          (\<lambda>(k, acc).
              ASSERT (n - int (pent_num (-k)) \<in> {0..<int (length ps)}) \<bind>
              (\<lambda>_. let x = ps ! nat (n - int (pent_num (-k)))
                    in RETURN (k + 1, if even k then acc - x else acc + x))) (1, acc)"
  have [refine_vcg]: "w2 \<le> \<Down>R w1"
    unfolding w1_def w2_def
    by refine_rcg (auto simp: R_def br_def pent_num_def[of "-1"] pent_num_decrement)
  have "do {(_,_,acc') \<leftarrow> w2; RETURN acc'} \<le> \<Down>int_rel (do {(_,acc') \<leftarrow> w1; RETURN acc'})"
    by refine_vcg (auto simp: R_def br_def)
  thus ?thesis
    unfolding partition_impl2_inner2_def partition_impl1_inner2_def w1_def w2_def .
qed


subsubsection \<open>Computing the next number\<close>

definition partition_impl2_inner where
  "partition_impl2_inner n ps = 
     do {acc \<leftarrow> partition_impl2_inner1 n ps 0;
         partition_impl2_inner2 n ps acc}"

lemma partition_impl2_inner2_correct [refine_vcg]:
  assumes "n \<in> {1..int (length ps)}"
  shows   "partition_impl2_inner2 n ps acc \<le> SPEC (\<lambda>acc'. acc' = acc + partition_impl1_inner2_aux' n ps)"
proof (rule order.trans[OF _ partition_impl1_inner2_correct[OF assms]])
  show "partition_impl2_inner2 n ps acc \<le> partition_impl1_inner2 n ps acc"
    using partition_impl2_inner2_refine[of n ps acc] by simp
qed

lemma partition_impl2_inner_correct_aux:
  assumes  "n \<in> {1..int (length ps)}" "\<And>i. int i < n \<Longrightarrow> ps ! i = int (Partition' i)"
  shows    "partition_impl1_inner1_aux' (int n) ps + partition_impl1_inner2_aux' (int n) ps =
              int (Partition' n)" (is "?lhs = ?rhs")
proof -
  define S :: "int set \<Rightarrow> int \<Rightarrow> int" where
    "S = (\<lambda>A c. (\<Sum>i | i \<in> A \<and> int (pent_num (c*i)) \<le> int n.
              (if even (c*i) then -1 else 1) * ps ! nat (int n - int (pent_num (c * i)))))"

  have "?lhs = S {1..} 1 + S {1..} (-1)"
    unfolding partition_impl1_inner1_aux'_def partition_impl1_inner2_aux'_def S_def by simp
  also have "S {1..} (-1) = S {..-1} 1"
    unfolding S_def by (rule sum.reindex_bij_witness[of _ uminus uminus]) auto
  also have "S {1..} 1 + S {..-1} 1 = S (-{0}) 1" unfolding S_def
    by (subst sum.union_disjoint [symmetric])
       (auto intro!: sum.cong finite_subset[OF _ finite_pent_num_le[of n]])
  also have "\<dots> = (\<Sum>i | i \<in> - {0} \<and> int (pent_num (1 * i)) \<le> int n.
                    (if even (1 * i) then - 1 else 1) * Partition' (n - pent_num i))"
    unfolding S_def by (intro sum.cong) (use assms in \<open>auto simp: nat_diff_distrib pent_num_pos_iff\<close>)
  also have "\<dots> = (\<Sum>i | i \<in> {1..n} \<and> i \<in> pent_nums.
                     (if even (inv_pent_num i) then -1 else 1) * int (Partition' (n - i)))"
    by (rule sum.reindex_bij_witness[of _ inv_pent_num pent_num])
       (auto simp: Suc_le_eq pent_num_pos_iff pent_nums_def)
  also have "\<dots> = int (Partition' n)"
    by (subst (2) Partition'_recurrence) (use assms(1) in auto)
  finally show ?thesis .
qed

lemma partition_impl2_inner_correct [refine_vcg]:
  assumes "n \<in> {1..int (length ps)}" "\<And>i. int i < n \<Longrightarrow> ps ! i = int (Partition' i)"
  shows   "partition_impl2_inner n ps \<le> SPEC (\<lambda>x. x = Partition' n)"
  unfolding partition_impl2_inner_def
  apply refine_vcg
  subgoal
    using assms by simp
  subgoal
    using assms by simp
  subgoal for acc acc'
    using partition_impl2_inner_correct_aux[of n ps] assms by simp
  done


subsubsection \<open>The full algorithm\<close>

definition partition_impl2 where
  "partition_impl2 n = do {
     ps \<leftarrow> RETURN (op_array_replicate (n+1) 0);
     ASSERT (length ps > 0);
     let ps' = ps[0 := 1];
     (_, ps'') \<leftarrow>
        WHILE\<^sub>T\<^bsup>\<lambda>(m,ps). m\<in>{1..n+1} \<and> length ps = n+1 \<and> (\<forall>i<m. ps ! i = int (Partition' i))\<^esup>
         (\<lambda>(m,ps). m \<le> n) 
         (\<lambda>(m,ps). 
           do {
             x \<leftarrow> partition_impl2_inner m ps;
             ASSERT (m < length ps);
             RETURN (m+1, ps[m := x])
           }) (1, ps');
         RETURN ps''
       }"

lemma partition_impl2_correct [refine_vcg]:
  "partition_impl2 n \<le> SPEC (\<lambda>xs. xs = Partition'_list n)"
  unfolding partition_impl2_def Partition'_list_def
  apply refine_vcg
  apply simp
              apply (rule wf_measure[of "\<lambda>(m,_). n + 1 - m"])
            apply (auto simp: nth_list_update' simp del: upt_Suc intro!: nth_equalityI)
  done

lemma param_dvd_nat [param, sepref_import_param]:
  "((dvd), (dvd)) \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> bool_rel" 
  "((dvd), (dvd)) \<in> int_rel \<rightarrow> int_rel \<rightarrow> bool_rel" 
  by simp_all

sepref_definition partition_impl3 is
  "partition_impl2" :: "nat_assn\<^sup>d \<rightarrow>\<^sub>a array_assn int_assn"
  unfolding partition_impl2_def partition_impl2_inner_def
            partition_impl2_inner1_def partition_impl2_inner2_def
  by sepref

lemma partition_impl3_correct':
  "(partition_impl3, \<lambda>n. RETURN (Partition'_list n)) \<in> nat_assn\<^sup>d \<rightarrow>\<^sub>a array_assn int_assn"
proof -
  have *: "(partition_impl2, \<lambda>n. RETURN (Partition'_list n)) \<in> nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
    by refine_vcg simp?
  show ?thesis
    using partition_impl3.refine[FCOMP *] .
qed

theorem partition_impl3_correct:
   "<nat_assn n n> partition_impl3 n <array_assn int_assn (Partition'_list n)>\<^sub>t"
proof -
  have [simp]: "nofail (partition_impl2 n)"
    using partition_impl2_correct[of n] le_RES_nofailI by blast
  have 1: "xs = Partition'_list n" if "RETURN xs \<le> partition_impl2 n" for xs
    using that partition_impl2_correct[of n] by (simp add: pw_le_iff)
  note rl = partition_impl3.refine[THEN hfrefD, of n n, THEN hn_refineD, simplified]
  show ?thesis
    apply (rule cons_rule[OF _ _ rl])
    apply (sep_auto simp: pure_def)
    apply (sep_auto simp: pure_def dest!: 1)
    done
qed

end