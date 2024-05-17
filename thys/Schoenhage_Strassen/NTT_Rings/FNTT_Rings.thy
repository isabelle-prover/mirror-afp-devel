subsection "Fast Number Theoretic Transforms in Rings"

theory FNTT_Rings
  imports NTT_Rings "Number_Theoretic_Transform.Butterfly"
begin

context cring begin

text "The following lemma is the essence of Fast Number Theoretic Transforms (FNTTs)."

lemma NTT_recursion:
  assumes "even n"
  assumes "primitive_root n \<mu>"
  assumes[simp]: "length a = n"
  assumes[simp]: "j < n"
  assumes[simp]: "set a \<subseteq> carrier R"
  defines "j' \<equiv> (if j < n div 2 then j else j - n div 2)"
  shows "j' < n div 2" "j = (if j < n div 2 then j' else j' + n div 2)"
  and "(NTT \<mu> a) ! j = (NTT (\<mu> [^] (2::nat)) [a ! i. i \<leftarrow> filter even [0..<n]]) ! j'
    \<oplus> \<mu> [^] j \<otimes> (NTT (\<mu> [^] (2::nat)) [a ! i. i \<leftarrow> filter odd [0..<n]]) ! j'"
proof -
  from assms have "n > 0" by linarith
  have[simp]: "\<mu> \<in> carrier R" using \<open>primitive_root n \<mu>\<close> unfolding primitive_root_def root_of_unity_def by blast
  then have \<mu>_pow_carrier[simp]: "\<mu> [^] i \<in> carrier R" for i :: nat by simp
  show "j' < n div 2" unfolding j'_def using \<open>j < n\<close> \<open>even n\<close> by fastforce
  show j'_alt: "j = (if j < n div 2 then j' else j' + n div 2)"
    unfolding j'_def by simp

  have a_even_carrier[simp]: "a ! (2 * i) \<in> carrier R" if "i < n div 2" for i
    using set_subseteqD[OF \<open>set a \<subseteq> carrier R\<close>] assms that by simp
  have a_odd_carrier[simp]: "a ! (2 * i + 1) \<in> carrier R" if "i < n div 2" for i
    using set_subseteqD[OF \<open>set a \<subseteq> carrier R\<close>] assms that by simp

  have \<mu>_pow: "\<mu> [^] (j * (2 * i)) = (\<mu> [^] (2::nat)) [^] (j' * i)" for i
  proof -
    have "\<mu> [^] (j * (2 * i)) = (\<mu> [^] (j * 2)) [^] i"
      using mult.assoc nat_pow_pow[symmetric] by simp
    also have "\<mu> [^] (j * 2) = \<mu> [^] (j' * 2)"
    proof (cases "j < n div 2")
      case True
      then show ?thesis unfolding j'_def by simp
    next
      case False
      then have "\<mu> [^] (j * 2) = \<mu> [^] (j' * 2 + n)"
        using j'_alt by (simp add: \<open>even n\<close>)
      also have "... = \<mu> [^] (j' * 2)"
        using \<open>n > 0\<close> \<open>primitive_root n \<mu>\<close>
        by (intro root_of_unity_powers_nat[of n]) auto
      finally show ?thesis .
    qed
    finally show ?thesis unfolding nat_pow_pow[OF \<open>\<mu> \<in> carrier R\<close>]
      by (simp add: mult.assoc mult.commute)
  qed

  have "(NTT \<mu> a) ! j = (\<Oplus>i \<leftarrow> [0..<n]. a ! i \<otimes> (\<mu> [^] (j * i)))"
    using NTT_nth_2[of a n j \<mu>] by simp
  also have "... = (\<Oplus>i \<leftarrow> [0..<n div 2]. a ! (2 * i) \<otimes> (\<mu> [^] (j * (2 * i))))
      \<oplus> (\<Oplus>i \<leftarrow> [0..<n div 2]. a ! (2 * i + 1) \<otimes> (\<mu> [^] (j * (2 * i + 1))))"
    using \<open>even n\<close>
    by (intro monoid_sum_list_even_odd_split m_closed nat_pow_closed set_subseteqD) simp_all
  also have "(\<Oplus>i \<leftarrow> [0..<n div 2]. a ! (2 * i + 1) \<otimes> (\<mu> [^] (j * (2 * i + 1))))
           = (\<Oplus>i \<leftarrow> [0..<n div 2]. \<mu> [^] j \<otimes> (a ! (2 * i + 1) \<otimes> (\<mu> [^] (j * (2 * i)))))"
  proof (intro monoid_sum_list_cong)
    fix i
    assume "i \<in> set [0..<n div 2]"
    then have[simp]: "i < n div 2" by simp
    have "a ! (2 * i + 1) \<otimes> (\<mu> [^] (j * (2 * i + 1))) =
          a ! (2 * i + 1) \<otimes> (\<mu> [^] (j * (2 * i)) \<otimes> \<mu> [^] j)"
      unfolding distrib_left mult_1_right
      unfolding nat_pow_mult[symmetric, OF \<open>\<mu> \<in> carrier R\<close>]
      by (rule refl)
    also have "... = (a ! (2 * i + 1) \<otimes> \<mu> [^] (j * (2 * i))) \<otimes> \<mu> [^] j"
      using a_odd_carrier[OF \<open>i < n div 2\<close>]
      by (intro m_assoc[symmetric]; simp)
    also have "... = \<mu> [^] j \<otimes> (a ! (2 * i + 1) \<otimes> \<mu> [^] (j * (2 * i)))"
      using a_odd_carrier[OF \<open>i < n div 2\<close>]
      by (intro m_comm; simp)
    finally show "a ! (2 * i + 1) \<otimes> \<mu> [^] (j * (2 * i + 1)) = ..." .
  qed
  also have "... = \<mu> [^] j \<otimes> (\<Oplus>i \<leftarrow> [0..<n div 2]. a ! (2 * i + 1) \<otimes> (\<mu> [^] (j * (2 * i))))"
    using a_odd_carrier by (intro monoid_sum_list_in_left; simp)
  finally have "(NTT \<mu> a) ! j = (\<Oplus>i \<leftarrow> [0..<n div 2]. a ! (2 * i) \<otimes> (\<mu> [^] (2::nat)) [^] (j' * i))
      \<oplus> \<mu> [^] j \<otimes> (\<Oplus>i \<leftarrow> [0..<n div 2]. a ! (2 * i + 1) \<otimes> (\<mu> [^] (2::nat)) [^] (j' * i))"
    unfolding \<mu>_pow .
  also have "... = (\<Oplus>i \<leftarrow> [0..<n div 2]. [a ! i. i \<leftarrow> filter even [0..<n]] ! i \<otimes> (\<mu> [^] (2::nat)) [^] (j' * i))
      \<oplus> \<mu> [^] j \<otimes> (\<Oplus>i \<leftarrow> [0..<n div 2]. [a ! i. i \<leftarrow> filter odd [0..<n]] ! i \<otimes> (\<mu> [^] (2::nat)) [^] (j' * i))"
    by (intro_cong "[cong_tag_2 (\<oplus>), cong_tag_2 (\<otimes>)]" more: monoid_sum_list_cong)
       (simp_all add: filter_even_nth length_filter_even length_filter_odd filter_odd_nth)
  also have "... = (NTT (\<mu> [^] (2::nat)) [a ! i. i \<leftarrow> filter even [0..<n]]) ! j'
      \<oplus> \<mu> [^] j \<otimes> (NTT (\<mu> [^] (2::nat)) [a ! i. i \<leftarrow> filter odd [0..<n]]) ! j'"
    by (intro_cong "[cong_tag_2 (\<oplus>), cong_tag_2 (\<otimes>)]" more: NTT_nth_2[symmetric])
       (simp_all add: length_filter_even length_filter_odd \<open>even n\<close> \<open>j' < n div 2\<close>)
  finally show "(NTT \<mu> a) ! j = ..." .
qed

lemma NTT_recursion_1:
  assumes "even n"
  assumes "primitive_root n \<mu>"
  assumes[simp]: "length a = n"
  assumes[simp]: "j < n div 2"
  assumes[simp]: "set a \<subseteq> carrier R"
  shows "(NTT \<mu> a) ! j =
        (NTT (\<mu> [^] (2::nat)) [a ! i. i \<leftarrow> filter even [0..<n]]) ! j
      \<oplus> \<mu> [^] j \<otimes> (NTT (\<mu> [^] (2::nat)) [a ! i. i \<leftarrow> filter odd [0..<n]]) ! j"
proof -
  have "j < n" using \<open>j < n div 2\<close> by linarith
  show ?thesis
    using NTT_recursion[OF \<open>even n\<close> \<open>primitive_root n \<mu>\<close> \<open>length a = n\<close> \<open>j < n\<close> \<open>set a \<subseteq> carrier R\<close>]
    using \<open>j < n div 2\<close> by presburger
qed

lemma NTT_recursion_2:
  assumes "even n"
  assumes "primitive_root n \<mu>"
  assumes[simp]: "length a = n"
  assumes[simp]: "j < n div 2"
  assumes[simp]: "set a \<subseteq> carrier R"
  assumes halfway_property: "\<mu> [^] (n div 2) = \<ominus> \<one>"
  shows "(NTT \<mu> a) ! (n div 2 + j) =
        (NTT (\<mu> [^] (2::nat)) [a ! i. i \<leftarrow> filter even [0..<n]]) ! j
      \<ominus> \<mu> [^] j \<otimes> (NTT (\<mu> [^] (2::nat)) [a ! i. i \<leftarrow> filter odd [0..<n]]) ! j"
proof -
  from assms have "\<mu> \<in> carrier R" unfolding primitive_root_def root_of_unity_def by simp
  then have carrier_1: "\<mu> [^] j \<in> carrier R"
    by simp
  have carrier_2: "NTT (\<mu> [^] (2::nat)) (map ((!) a) (filter odd [0..<n])) ! j \<in> carrier R"
    apply (intro NTT_nth_closed[where n = "n div 2"])
    subgoal using \<open>set a \<subseteq> carrier R\<close> \<open>length a = n\<close> by fastforce
    subgoal using \<open>\<mu> \<in> carrier R\<close> by simp
    subgoal by (simp add: length_filter_odd)
    subgoal using \<open>j < n div 2\<close> .
    done
  have "n div 2 + j < n" using \<open>j < n div 2\<close> \<open>even n\<close> by linarith
  then have "(NTT \<mu> a) ! (n div 2 + j) =
        (NTT (\<mu> [^] (2::nat)) [a ! i. i \<leftarrow> filter even [0..<n]]) ! j
      \<oplus> \<mu> [^] (n div 2 + j) \<otimes> (NTT (\<mu> [^] (2::nat)) [a ! i. i \<leftarrow> filter odd [0..<n]]) ! j"
    using NTT_recursion[OF \<open>even n\<close> \<open>primitive_root n \<mu>\<close> \<open>length a = n\<close> \<open>n div 2 + j < n\<close> \<open>set a \<subseteq> carrier R\<close>]
    by simp
  also have "\<mu> [^] (n div 2 + j) = \<ominus> (\<mu> [^] j)"
    unfolding nat_pow_mult[symmetric, OF \<open>\<mu> \<in> carrier R\<close>] halfway_property
    by (intro minus_eq_mult_one[symmetric]; simp add: \<open>\<mu> \<in> carrier R\<close>)
  finally show ?thesis unfolding minus_eq l_minus[OF carrier_1 carrier_2] .
qed

lemma NTT_diffs:
  assumes "even n"
  assumes "primitive_root n \<mu>"
  assumes "length a = n"
  assumes "j < n div 2"
  assumes "set a \<subseteq> carrier R"
  assumes "\<mu> [^] (n div 2) = \<ominus> \<one>"
  shows "NTT \<mu> a ! j \<ominus> NTT \<mu> a ! (n div 2 + j) = nat_embedding 2 \<otimes> (\<mu> [^] j \<otimes> NTT (\<mu> [^] (2::nat)) (map ((!) a) (filter odd [0..<n])) ! j)"
proof -
  have[simp]: "\<mu> \<in> carrier R" using \<open>primitive_root n \<mu>\<close> unfolding primitive_root_def root_of_unity_def by blast
  define ntt1 where "ntt1 = NTT (\<mu> [^] (2::nat)) (map ((!) a) (filter even [0..<n])) ! j"
  have "ntt1 \<in> carrier R" unfolding ntt1_def
    apply (intro set_subseteqD[OF NTT_closed] set_subseteqI)
    subgoal for i
      using set_subseteqD[OF \<open>set a \<subseteq> carrier R\<close>]
      by (simp add: filter_even_nth \<open>length a = n\<close> \<open>even n\<close> length_filter_even)
    subgoal by simp
    subgoal using assms by (simp add: length_filter_even \<open>even n\<close>)
    done
  define ntt2 where "ntt2 = NTT (\<mu> [^] (2::nat)) (map ((!) a) (filter odd [0..<n])) ! j"
  have "ntt2 \<in> carrier R" unfolding ntt2_def
    apply (intro set_subseteqD[OF NTT_closed] set_subseteqI)
    subgoal for i
      using set_subseteqD[OF \<open>set a \<subseteq> carrier R\<close>]
      by (simp add: filter_odd_nth \<open>length a = n\<close> \<open>even n\<close> length_filter_odd)
    subgoal by simp
    subgoal using assms by (simp add: length_filter_odd \<open>even n\<close>)
    done
  have "NTT \<mu> a ! j \<ominus> NTT \<mu> a ! (n div 2 + j) =
    (ntt1 \<oplus> \<mu> [^] j \<otimes> ntt2) \<ominus> (ntt1 \<ominus> \<mu> [^] j \<otimes> ntt2)"
    apply (intro arg_cong2[where f = "\<lambda>i j. i \<ominus> j"])
    unfolding ntt1_def ntt2_def
    subgoal by (intro NTT_recursion_1 assms)
    subgoal by (intro NTT_recursion_2 assms)
    done
  also have "... = \<mu> [^] j \<otimes> (ntt2 \<oplus> ntt2)"
    using \<open>ntt1 \<in> carrier R\<close> \<open>ntt2 \<in> carrier R\<close> nat_pow_closed[OF \<open>\<mu> \<in> carrier R\<close>]
    by algebra
  also have "... = \<mu> [^] j \<otimes> ((\<one> \<oplus> \<one>) \<otimes> ntt2)"
    using \<open>ntt2 \<in> carrier R\<close> one_closed by algebra
  also have "... = \<mu> [^] j \<otimes> (nat_embedding 2 \<otimes> ntt2)"
    by (simp add: numeral_2_eq_2)
  also have "... = nat_embedding 2 \<otimes> (\<mu> [^] j \<otimes> ntt2)"
    using nat_pow_closed[OF \<open>\<mu> \<in> carrier R\<close>] \<open>ntt2 \<in> carrier R\<close> nat_embedding_closed
    by algebra
  finally show ?thesis unfolding ntt2_def .
qed

text "The following algorithm is adapted from @{theory Number_Theoretic_Transform.Butterfly}"
lemma FNTT_term_aux[simp]: "length (filter P [0..<l]) < Suc l"
  by (metis diff_zero le_imp_less_Suc length_filter_le length_upt)
fun FNTT :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"FNTT \<mu> [] = []"
| "FNTT \<mu> [x] = [x]"
| "FNTT \<mu> [x, y] = [x \<oplus> y, x \<ominus> y]"
| "FNTT \<mu> a = (let n = length a;
                  nums1 = [a!i.  i \<leftarrow> filter even [0..<n]];
                  nums2 = [a!i.  i \<leftarrow> filter odd [0..<n]];
                  b = FNTT (\<mu> [^] (2::nat)) nums1;
                  c = FNTT (\<mu> [^] (2::nat)) nums2;
                  g = [b!i \<oplus> (\<mu> [^] i) \<otimes> c!i. i \<leftarrow> [0..<(n div 2)]];
                  h = [b!i \<ominus> (\<mu> [^] i) \<otimes> c!i. i \<leftarrow> [0..<(n div 2)]]
               in g@h)"
lemmas [simp del] = FNTT_term_aux

declare FNTT.simps[simp del]

lemma length_FNTT[simp]:
  assumes "length a = 2 ^ k"
  shows "length (FNTT \<mu> a) = length a"
  using assms
proof (induction rule: FNTT.induct)
  case (1 \<mu>)
  then show ?case by simp
next
  case (2 \<mu> x)
  then show ?case by (simp add: FNTT.simps)
next
  case (3 \<mu> x y)
  then show ?case by (simp add: FNTT.simps)
next
  case (4 \<mu> a1 a2 a3 as)
  define a where "a = a1 # a2 # a3 # as"
  define n where "n = length a"
  with a_def have "even n" using 4(3)
    by (cases "k = 0") simp_all
  define nums1 where "nums1 = [a!i.  i \<leftarrow> filter even [0..<n]]"
  define nums2 where "nums2 = [a!i.  i \<leftarrow> filter odd [0..<n]]"
  define b where "b = FNTT (\<mu> [^] (2::nat)) nums1"
  define c where "c = FNTT (\<mu> [^] (2::nat)) nums2"
  define g where "g = [b!i \<oplus> (\<mu> [^] i) \<otimes> c!i. i \<leftarrow> [0..<(n div 2)]]"
  define h where "h = [b!i \<ominus> (\<mu> [^] i) \<otimes> c!i. i \<leftarrow> [0..<(n div 2)]]"

  note defs = a_def n_def nums1_def nums2_def b_def c_def g_def h_def

  have "length (FNTT \<mu> a) = length g + length h"
    using defs by (simp add: Let_def FNTT.simps)
  also have "... = (n div 2) + (n div 2)" unfolding g_def h_def by simp
  also have "... = n" using \<open>even n\<close> by fastforce
  finally show ?case by (simp only: a_def n_def)
qed

theorem FNTT_NTT:
  assumes[simp]: "\<mu> \<in> carrier R"
  assumes "n = 2 ^ k"
  assumes "primitive_root n \<mu>"
  assumes halfway_property: "\<mu> [^] (n div 2) = \<ominus> \<one>"
  assumes[simp]: "length a = n"
  assumes "set a \<subseteq> carrier R"
  shows "FNTT \<mu> a = NTT \<mu> a"
  using assms
proof (induction \<mu> a arbitrary: n k rule: FNTT.induct)
  case (1 \<mu>)
  then show ?case unfolding NTT_def by simp
next
  case (2 \<mu> x)
  then have "n = 1" by simp
  then have "k = 0" using \<open>n = 2 ^ k\<close> by simp
  moreover have "x \<in> carrier R" using 2 by simp
  ultimately show ?case unfolding NTT_def by (simp add: Let_def FNTT.simps)
next
  case (3 \<mu> x y)
  then have[simp]: "x \<in> carrier R" "y \<in> carrier R" by simp_all
  from 3 have "n = 2" by simp
  with \<open>\<mu> [^] (n div 2) = \<ominus> \<one>\<close> have "\<mu> [^] (1 :: nat) = \<ominus> \<one>" by simp
  then have "\<mu> = \<ominus> \<one>" by (simp add: \<open>\<mu> \<in> carrier R\<close>)
  have "NTT \<mu> [x, y] = [x \<oplus> y, x \<ominus> y]"
    unfolding NTT_def
    apply (simp add: Let_def 3 \<open>\<mu> = \<ominus> \<one>\<close>)
    using \<open>x \<in> carrier R\<close> \<open>y \<in> carrier R\<close> by algebra
  then show ?case by (simp add: FNTT.simps)
next
  case (4 \<mu> a1 a2 a3 as)
  define a where "a = a1 # a2 # a3 # as"
  then have[simp]: "length a = n" using 4(7) by simp
  define nums1 where "nums1 = [a!i.  i \<leftarrow> filter even [0..<n]]"
  define nums2 where "nums2 = [a!i.  i \<leftarrow> filter odd [0..<n]]"
  define b where "b = FNTT (\<mu> [^] (2::nat)) nums1"
  define c where "c = FNTT (\<mu> [^] (2::nat)) nums2"
  define g where "g = [b!i \<oplus> (\<mu> [^] i) \<otimes> c!i. i \<leftarrow> [0..<(n div 2)]]"
  then have "length g = n div 2" by simp
  define h where "h = [b!i \<ominus> (\<mu> [^] i) \<otimes> c!i. i \<leftarrow> [0..<(n div 2)]]"
  then have "length h = n div 2" by simp

  note defs = a_def nums1_def nums2_def b_def c_def g_def h_def

  have "k > 0"
    using \<open>length (a1 # a2 # a3 # as) = n\<close> \<open>n = 2 ^ k\<close>
    by (cases "k = 0") simp_all
  then have "even n" "n div 2 = 2 ^ (k - 1)"
    using \<open>n = 2 ^ k\<close> by (simp_all add: power_diff)

  have "FNTT \<mu> (a1 # a2 # a3 # as) = g @ h"
    unfolding FNTT.simps
    using \<open>length (a1 # a2 # a3 # as) = n\<close> by (simp only: Let_def defs)
  then have "FNTT \<mu> a = g @ h" using a_def by simp

  have recursive_halfway: "(\<mu> [^] (2 :: nat)) [^] (n div 2 div 2) = \<ominus> \<one>"
  proof -
    have "n \<ge> 3"
      using \<open>length (a1 # a2 # a3 # as) = n\<close> by simp
    then have "k \<ge> 2" using \<open>n = 2 ^ k\<close> by (cases "k \<in> {0, 1}") auto
    then have "even (n div 2)" using \<open>n div 2 = 2 ^ (k - 1)\<close> by fastforce
    then show ?thesis
      by (simp add: nat_pow_pow \<open>\<mu> \<in> carrier R\<close> \<open>\<mu> [^] (n div 2) = \<ominus> \<one>\<close>)
  qed

  have "b = NTT (\<mu> [^] (2::nat)) nums1"
    unfolding b_def
    apply (intro 4(1)[of n nums1 nums2 "n div 2" "k - 1"])
    subgoal using \<open>length (a1 # a2 # a3 # as) = n\<close> by simp
    subgoal using nums1_def a_def by simp
    subgoal using nums2_def a_def by simp
    subgoal using \<open>\<mu> \<in> carrier R\<close> by simp
    subgoal using \<open>n div 2 = 2 ^ (k - 1)\<close> .
    subgoal using primitive_root_recursion \<open>even n\<close> \<open>primitive_root n \<mu>\<close> by blast
    subgoal using recursive_halfway .
    subgoal using nums1_def length_filter_even \<open>even n\<close> by simp
    subgoal
      unfolding nums1_def
      apply (intro set_subseteqI)
      using set_subseteqD[OF \<open>set (a1 # a2 # a3 # as) \<subseteq> carrier R\<close>]
      by (simp add: a_def[symmetric] filter_even_nth length_filter_even \<open>even n\<close>)
    done

  have "c = NTT (\<mu> [^] (2::nat)) nums2"
    unfolding c_def
    apply (intro 4(2)[of n nums1 nums2 b "n div 2" "k - 1"])
    subgoal using \<open>length (a1 # a2 # a3 # as) = n\<close> by simp
    subgoal unfolding nums1_def a_def by simp
    subgoal unfolding nums2_def a_def by simp
    subgoal using b_def .
    subgoal using \<open>\<mu> \<in> carrier R\<close> by simp
    subgoal using \<open>n div 2 = 2 ^ (k - 1)\<close> .
    subgoal using primitive_root_recursion \<open>even n\<close> \<open>primitive_root n \<mu>\<close> by blast
    subgoal using recursive_halfway .
    subgoal unfolding nums2_def using length_filter_odd by simp
    subgoal
      unfolding nums2_def
      apply (intro set_subseteqI)
      using set_subseteqD[OF \<open>set (a1 # a2 # a3 # as) \<subseteq> carrier R\<close>]
      by (simp add: a_def[symmetric] filter_odd_nth length_filter_odd)
    done

  show ?case
  proof (intro nth_equalityI)
    have[simp]: "length (FNTT \<mu> (a1 # a2 # a3 # as)) = n"
      using \<open>length (a1 # a2 # a3 # as) = n\<close> \<open>n = 2 ^ k\<close> length_FNTT[of "a1 # a2 # a3 # as"]
      by blast
    then show "length (FNTT \<mu> (a1 # a2 # a3 # as)) = length (NTT \<mu> (a1 # a2 # a3 # as))"
      using NTT_length[of \<mu> "a1 # a2 # a3 # as"] \<open>length (a1 # a2 # a3 # as) = n\<close> by argo
    fix i
    assume "i < length (FNTT \<mu> (a1 # a2 # a3 # as))"
    then have "i < n" by simp

    have "FNTT \<mu> a ! i = NTT \<mu> a ! i"
    proof (cases "i < n div 2")
      case True
      then have "NTT \<mu> a ! i =
        (NTT (\<mu> [^] (2::nat)) [a ! i. i \<leftarrow> filter even [0..<n]]) ! i
      \<oplus> \<mu> [^] i \<otimes> (NTT (\<mu> [^] (2::nat)) [a ! i. i \<leftarrow> filter odd [0..<n]]) ! i"
        apply (intro NTT_recursion_1)
        using True \<open>even n\<close> \<open>primitive_root n \<mu>\<close> \<open>set (a1 # a2 # a3 # as) \<subseteq> carrier R\<close> a_def
        using \<open>\<mu> \<in> carrier R\<close> \<open>length (a1 # a2 # a3 # as) = n\<close>
        by simp_all

      also have "... = (NTT (\<mu> [^] (2::nat)) nums1) ! i
      \<oplus> \<mu> [^] i \<otimes> (NTT (\<mu> [^] (2::nat)) nums2) ! i"
        unfolding nums1_def nums2_def by blast
      also have "... = b ! i \<oplus> \<mu> [^] i \<otimes> c ! i"
        using \<open>b = NTT (\<mu> [^] 2) nums1\<close> \<open>c = NTT (\<mu> [^] 2) nums2\<close> by blast
      also have "... = g ! i"
        unfolding g_def using True by simp
      also have "... = FNTT \<mu> a ! i"
        using \<open>FNTT \<mu> a = g @ h\<close> \<open>length g = n div 2\<close> True
        by (simp add: nth_append)

      finally show ?thesis by simp
    next
      case False
      then obtain j where j_def: "i = n div 2 + j" "j < n div 2"
        using \<open>i < n\<close> \<open>even n\<close>
        by (metis add_diff_inverse_nat add_self_div_2 div_plus_div_distrib_dvd_right nat_add_left_cancel_less)
      have "NTT \<mu> a ! (n div 2 + j) =
        (NTT (\<mu> [^] (2::nat)) [a ! i. i \<leftarrow> filter even [0..<n]]) ! j
      \<ominus> \<mu> [^] j \<otimes> (NTT (\<mu> [^] (2::nat)) [a ! i. i \<leftarrow> filter odd [0..<n]]) ! j"
        apply (intro NTT_recursion_2)
        subgoal using \<open>even n\<close> .
        subgoal using \<open>primitive_root n \<mu>\<close> .
        subgoal using \<open>length (a1 # a2 # a3 # as) = n\<close> a_def by simp
        subgoal using j_def by simp
        subgoal using \<open>set (a1 # a2 # a3 # as) \<subseteq> carrier R\<close> a_def by simp
        subgoal using \<open>\<mu> [^] (n div 2) = \<ominus> \<one>\<close> .
        done

      also have "... = (NTT (\<mu> [^] (2::nat)) nums1) ! j
      \<ominus> \<mu> [^] j \<otimes> (NTT (\<mu> [^] (2::nat)) nums2) ! j"
        unfolding nums1_def nums2_def by blast
      also have "... = b ! j \<ominus> \<mu> [^] j \<otimes> c ! j"
        using \<open>b = NTT (\<mu> [^] 2) nums1\<close> \<open>c = NTT (\<mu> [^] 2) nums2\<close> by blast
      also have "... = h ! j"
        unfolding g_def h_def using j_def by simp
      also have "... = FNTT \<mu> a ! i"
        using \<open>FNTT \<mu> a = g @ h\<close> \<open>length g = n div 2\<close> j_def
        by (simp add: nth_append)

      finally show ?thesis using j_def by simp
    qed
    then show "FNTT \<mu> (a1 # a2 # a3 # as) ! i = NTT \<mu> (a1 # a2 # a3 # as) ! i"
      using a_def by simp
  qed
qed

end

text "The following is copied from @{theory Number_Theoretic_Transform.Butterfly} and moved outside
of the @{locale butterfly} locale."

fun evens_odds where
"evens_odds _ [] = []"
| "evens_odds True (x#xs)= (x # evens_odds False xs)"
| "evens_odds False (x#xs) = evens_odds True xs"

lemma map_filter_shift: " map f (filter even [0..<Suc g]) = 
        f 0 #  map (\<lambda> x. f (x+1)) (filter odd [0..<g])"
  by (induction g) auto

lemma map_filter_shift': " map f (filter odd [0..<Suc g]) = 
          map (\<lambda> x. f (x+1)) (filter even [0..<g])"
  by (induction g) auto

lemma filter_comprehension_evens_odds:
      "[xs ! i. i \<leftarrow> filter even [0..<length xs]] = evens_odds True xs \<and>
       [xs ! i. i \<leftarrow> filter odd [0..<length xs]] = evens_odds False xs "
  apply(induction xs)
   apply simp
  subgoal for x xs
    apply rule
    subgoal 
      apply(subst evens_odds.simps)
      apply(rule trans[of _ "map ((!) (x # xs)) (filter even [0..<Suc (length xs)])"])
      subgoal by simp
      apply(rule trans[OF  map_filter_shift[of "(!) (x # xs)" "length xs"]])
      apply simp
      done

      apply(subst evens_odds.simps)
      apply(rule trans[of _ "map ((!) (x # xs)) (filter odd [0..<Suc (length xs)])"])
      subgoal by simp
      apply(rule trans[OF  map_filter_shift'[of "(!) (x # xs)" "length xs"]])
      apply simp
    done
  done

lemma FNTT'_termination_aux[simp]: "length (evens_odds True xs) < Suc (length xs)" 
              "length (evens_odds False xs) < Suc (length xs)"
  by (metis filter_comprehension_evens_odds le_imp_less_Suc length_filter_le length_map map_nth)+

text "(End of copy)"

lemma map_evens_odds: "map f (evens_odds x a) = evens_odds x (map f a)"
  by (induction x a rule: evens_odds.induct) simp_all

lemma length_evens_odds:
  "length (evens_odds True a) = (if even (length a) then length a div 2 else length a div 2 + 1)"
  "length (evens_odds False a) = length a div 2"
  using filter_comprehension_evens_odds[of a] length_filter_even[of "length a"] length_filter_odd[of "length a"]
  using length_map by (metis, metis)

lemma set_evens_odds:
  "set (evens_odds x a) \<subseteq> set a"
  by (induction x a rule: evens_odds.induct) fastforce+

context cring begin

text "Similar to @{theory Number_Theoretic_Transform.Butterfly}, we give an abstract algorithm that can be
refined more easily to a verifiably efficient FNTT algorithm."

fun FNTT' :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"FNTT' \<mu> [] = []"
| "FNTT' \<mu> [x] = [x]"
| "FNTT' \<mu> [x, y] = [x \<oplus> y, x \<ominus> y]"
| "FNTT' \<mu> a = (let n = length a;
                  nums1 = evens_odds True a;
                  nums2 = evens_odds False a;
                  b = FNTT' (\<mu> [^] (2::nat)) nums1;
                  c = FNTT' (\<mu> [^] (2::nat)) nums2;
                  g = [b!i \<oplus> (\<mu> [^] i) \<otimes> c!i. i \<leftarrow> [0..<(n div 2)]];
                  h = [b!i \<ominus> (\<mu> [^] i) \<otimes> c!i. i \<leftarrow> [0..<(n div 2)]]
               in g@h)"

lemma FNTT'_FNTT: "FNTT' \<mu> xs = FNTT \<mu> xs"
  apply (induction \<mu> xs rule: FNTT'.induct)
  subgoal by (simp add: FNTT.simps)
  subgoal by (simp add: FNTT.simps)
  subgoal by (simp add: FNTT.simps)
  subgoal for \<mu> a1 a2 a3 as
    unfolding FNTT.simps FNTT'.simps Let_def
    using filter_comprehension_evens_odds[of "a1 # a2 # a3 # as"] by presburger
  done

fun FNTT'' :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"FNTT'' \<mu> [] = []"
| "FNTT'' \<mu> [x] = [x]"
| "FNTT'' \<mu> [x, y] = [x \<oplus> y, x \<ominus> y]"
| "FNTT'' \<mu> a = (let n = length a;
                  nums1 = evens_odds True a;
                  nums2 = evens_odds False a;
                  b = FNTT'' (\<mu> [^] (2::nat)) nums1;
                  c = FNTT'' (\<mu> [^] (2::nat)) nums2;
                  g = map2 (\<oplus>) b (map2 (\<otimes>) [\<mu> [^] i. i \<leftarrow> [0..<(n div 2)]] c);
                  h = map2 (\<lambda>x y. x \<ominus> y) b (map2 (\<otimes>) [\<mu> [^] i. i \<leftarrow> [0..<(n div 2)]] c)
               in g@h)"

lemma FNTT''_FNTT':
  assumes "length a = 2 ^ k"
  shows "FNTT'' \<mu> a = FNTT' \<mu> a"
  using assms
proof (induction \<mu> a arbitrary: k rule: FNTT''.induct)
  case (4 \<mu> a1 a2 a3 as)
  define a where "a = a1 # a2 # a3 # as"
  define n where "n = length a"
  then have "n = 2 ^ k" using 4 a_def by simp
  then have "k \<ge> 2" using n_def a_def by (cases "k = 0"; cases "k = 1") simp_all
  then have "even n" using \<open>n = 2 ^ k\<close> by simp
  have "n div 2 = 2 ^ (k - 1)" using \<open>n = 2 ^ k\<close> \<open>k \<ge> 2\<close> by (simp add: power_diff)
  then have "even (n div 2)" using \<open>k \<ge> 2\<close> by simp
  define nums1 where "nums1 = evens_odds True a"
  then have "length nums1 = n div 2"
    using length_filter_even[of n] filter_comprehension_evens_odds[of a] n_def \<open>even n\<close>
    by (metis length_map)
  define nums2 where "nums2 = evens_odds False a"
  then have "length nums2 = n div 2"
    using length_filter_odd[of n] filter_comprehension_evens_odds[of a] n_def
    by (metis length_map)
  define b where "b = FNTT' (\<mu> [^] (2::nat)) nums1"
  then have "length b = n div 2"
    by (simp add: FNTT'_FNTT \<open>length nums1 = n div 2\<close> \<open>n div 2 = 2 ^ (k - 1)\<close>)
  define c where "c = FNTT' (\<mu> [^] (2::nat)) nums2"
  then have "length c = n div 2"
    by (simp add: FNTT'_FNTT \<open>length nums2 = n div 2\<close> \<open>n div 2 = 2 ^ (k - 1)\<close>)
  define g1 where "g1 = [b!i \<oplus> (\<mu> [^] i) \<otimes> c!i. i \<leftarrow> [0..<(n div 2)]]"
  then have "length g1 = n div 2" by simp
  define h1 where "h1 = [b!i \<ominus> (\<mu> [^] i) \<otimes> c!i. i \<leftarrow> [0..<(n div 2)]]"
  then have "length h1 = n div 2" by simp
  define g2 where "g2 = map2 (\<oplus>) b (map2 (\<otimes>) [\<mu> [^] i. i \<leftarrow> [0..<(n div 2)]] c)"
  then have "length g2 = n div 2"
    by (simp add: \<open>length b = n div 2\<close> \<open>length c = n div 2\<close>)

  have "g1 = g2"
    apply (intro nth_equalityI)
    subgoal by (simp only: \<open>length g1 = n div 2\<close> \<open>length g2 = n div 2\<close>)
    subgoal for i
      by (simp add: g1_def g2_def \<open>length b = n div 2\<close> \<open>length c = n div 2\<close>)
    done
    
  define h2 where "h2 = map2 (\<lambda>x y. x \<ominus> y) b (map2 (\<otimes>) [\<mu> [^] i. i \<leftarrow> [0..<(n div 2)]] c)"
  then have "length h2 = n div 2"
    by (simp add: \<open>length b = n div 2\<close> \<open>length c = n div 2\<close>)

  have "h1 = h2"
    apply (intro nth_equalityI)
    subgoal by (simp only: \<open>length h1 = n div 2\<close> \<open>length h2 = n div 2\<close>)
    subgoal for i
      by (simp add: h1_def h2_def \<open>length b = n div 2\<close> \<open>length c = n div 2\<close>)
    done

  have 1: "FNTT'' (\<mu> [^] (2::nat)) nums1 = FNTT' (\<mu> [^] (2::nat)) nums1"
    apply (intro 4(1))
    using a_def n_def \<open>length (a1 # a2 # a3 # as) = 2 ^ k\<close> \<open>length nums1 = n div 2\<close> \<open>n div 2 = 2 ^ (k - 1)\<close>
    by (simp_all add: nums1_def)
  have 2: "FNTT'' (\<mu> [^] (2::nat)) nums2 = FNTT' (\<mu> [^] (2::nat)) nums2"
    apply (intro 4(2))
    using a_def n_def \<open>length (a1 # a2 # a3 # as) = 2 ^ k\<close> \<open>length nums2 = n div 2\<close> \<open>n div 2 = 2 ^ (k - 1)\<close>
    by (simp_all add: nums2_def)

  show ?case
    apply (simp only: FNTT'.simps FNTT''.simps)
    apply (simp only: Let_def 1 2 a_def[symmetric] nums1_def[symmetric] nums2_def[symmetric]
        b_def[symmetric] c_def[symmetric])
    using \<open>h1 = h2\<close> \<open>g1 = g2\<close>  n_def g1_def h1_def g2_def h2_def
    by argo
qed simp_all

end

end