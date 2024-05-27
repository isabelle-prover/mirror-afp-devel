section "Number Theoretic Transforms in Rings"

theory NTT_Rings
imports
  "Number_Theoretic_Transform.NTT"
  Karatsuba.Monoid_Sums
  Karatsuba.Karatsuba_Preliminaries
  "../Preliminaries/Schoenhage_Strassen_Preliminaries"
  "../Preliminaries/Schoenhage_Strassen_Ring_Lemmas"
begin

lemma max_dividing_power_factorization:
  fixes a :: nat
  assumes "a \<noteq> 0"
  assumes "k = Max {s. p ^ s dvd a}"
  assumes "r = a div (p ^ k)"
  assumes "prime p"
  shows "a = r * p ^ k" "coprime p r"
  subgoal
  proof -
    have "p ^ 0 dvd a" by simp
    then have "{s. p ^ s dvd a} \<noteq> {}" by blast
    with assms have "p ^ k dvd a"
      by (metis Max_in finite_divisor_powers mem_Collect_eq not_prime_unit)
    with assms show ?thesis by simp
  qed
  subgoal
  proof (rule ccontr)
    assume "\<not> coprime p r"
    then have "p dvd r" using prime_imp_coprime_nat \<open>prime p\<close> by blast
    then have "p ^ (k + 1) dvd a" using \<open>a = r * p ^ k\<close> by simp
    then have "k \<ge> k + 1"
      using assms Max_ge[of "{s. p ^ s dvd a}" k] Max_in[of "{s. p ^ s dvd a}"]
      by (metis Max.coboundedI finite_divisor_powers mem_Collect_eq not_prime_unit)
    then show "False" by simp
  qed
  done

context cring
begin    

interpretation units_group: group "units_of R"
  by (rule units_group)

interpretation units_subgroup: multiplicative_subgroup R "Units R" "units_of R"
  by (rule units_subgroup)

subsection "Roots of Unity"

definition root_of_unity :: "nat \<Rightarrow> 'a \<Rightarrow> bool" where
"root_of_unity n \<mu> \<equiv> \<mu> \<in> carrier R \<and> \<mu> [^] n = \<one>"

lemma root_of_unityI[intro]: "\<mu> \<in> carrier R \<Longrightarrow> \<mu> [^] n = \<one> \<Longrightarrow> root_of_unity n \<mu>"
  unfolding root_of_unity_def by simp

lemma root_of_unityD[simp]: "root_of_unity n \<mu> \<Longrightarrow> \<mu> [^] n = \<one>"
  unfolding root_of_unity_def by simp

lemma root_of_unity_closed[simp]: "root_of_unity n \<mu> \<Longrightarrow> \<mu> \<in> carrier R"
  unfolding root_of_unity_def by simp


context
  fixes n :: nat
  assumes "n > 0"
begin

lemma roots_Units[simp]:
  assumes "root_of_unity n \<mu>"
  shows "\<mu> \<in> Units R"
proof -
  from \<open>n > 0\<close> obtain n' where "n = Suc n'"
    using gr0_implies_Suc by auto
  then have "\<one> = \<mu> \<otimes> (\<mu> [^] n')"
    using assms nat_pow_Suc2 unfolding root_of_unity_def by auto
  then show "\<mu> \<in> Units R" using assms m_comm[of \<mu> "\<mu> [^] n'"] nat_pow_closed[of \<mu> n']
    unfolding Units_def root_of_unity_def by auto
qed

definition roots_of_unity_group where
"roots_of_unity_group \<equiv> \<lparr> carrier = {\<mu>. root_of_unity n \<mu>}, monoid.mult = (\<otimes>), one = \<one> \<rparr>"

lemma roots_of_unity_group_is_group:
  shows "group roots_of_unity_group"
  apply (intro groupI)
  unfolding roots_of_unity_group_def root_of_unity_def
  apply (simp_all add: nat_pow_distrib m_assoc)
  subgoal for x
    using \<open>n > 0\<close>
      by (metis Group.nat_pow_Suc Nat.lessE mult.commute nat_pow_closed nat_pow_one nat_pow_pow)
    done

interpretation root_group : group "roots_of_unity_group"
  by (rule roots_of_unity_group_is_group)

interpretation root_subgroup : multiplicative_subgroup R "{\<mu>. root_of_unity n \<mu>}" roots_of_unity_group
  apply unfold_locales
  subgoal using roots_Units \<open>n > 0\<close> by blast
  subgoal unfolding roots_of_unity_group_def by simp
  done

lemma root_of_unity_inv:
  assumes "root_of_unity n \<mu>"
  shows "root_of_unity n (inv \<mu>)"
  using assms root_group.inv_closed[of \<mu>] root_subgroup.carrier_M root_subgroup.inv_eq[of \<mu>] by simp

lemma inv_root_of_unity:
  assumes "root_of_unity n \<mu>"
  shows "inv \<mu> = \<mu> [^] (n - 1)"
proof -
  have "\<mu> \<in> Units R" using assms
    using roots_Units by blast
  then have "inv \<mu> = \<mu> [^] (-1 :: int)"
    using units_group.int_pow_neg units_subgroup.inv_eq units_subgroup.int_pow_eq
    using units_group.int_pow_1 by force
  also have "... = \<one> \<otimes> \<mu> [^] (-1 :: int)"
    apply (intro l_one[symmetric])
    using \<open>\<mu> \<in> Units R\<close> by (metis Units_inv_closed calculation)
  also have "... = \<mu> [^] n \<otimes> \<mu> [^] (-1 :: int)"
    using assms by simp
  also have "... = \<mu> [^] (int n) \<otimes> \<mu> [^] (-1 :: int)"
    using Units_closed[OF \<open>\<mu> \<in> Units R\<close>]
    by (simp add: int_pow_int)
  also have "... = \<mu> [^] (int n - 1)"
    using units_group.int_pow_mult[of \<mu>] \<open>\<mu> \<in> Units R\<close> units_subgroup.int_pow_eq[of \<mu>]
    using units_of_mult units_subgroup.carrier_M 
    by (metis add.commute uminus_add_conv_diff)
  also have "... = \<mu> [^] (n - 1)"
    using \<open>n > 0\<close> Units_closed[OF \<open>\<mu> \<in> Units R\<close>]
    by (metis Suc_diff_1 add_diff_cancel_left' int_pow_int mult_Suc_right nat_mult_1 of_nat_1 of_nat_add)
  finally show ?thesis .
qed

lemma inv_pow_root_of_unity:
  assumes "root_of_unity n \<mu>"
  assumes "i \<in> {1..<n}"
  shows "(inv \<mu>) [^] i = \<mu> [^] (n - i)" "n - i \<in> {1..<n}"
proof -
  have "(inv \<mu>) [^] i = (\<mu> [^] (n - (1::nat))) [^] i"
    using assms inv_root_of_unity by algebra
  also have "... = \<mu> [^] ((n - 1) * i)"
    apply (intro nat_pow_pow) using assms roots_Units Units_closed by blast
  also have "... = \<mu> [^] n \<otimes> \<mu> [^] ((n - 1) * i)"
    using assms root_of_unity_def[of n \<mu>] by fastforce
  also have "... = \<mu> [^] (n + (n - 1) * i)"
    apply (intro nat_pow_mult) using assms roots_Units Units_closed by blast
  also have "... = \<mu> [^] (n * i + (n - i))"
  proof (intro arg_cong[where f = "([^]) \<mu>"])
    have "int (n + (n - 1) * i) = int (n * i + (n - i))"
    proof -
      have "int (n + (n - 1) * i) = int n + int (n - 1) * int i"
        by simp
      also have "... = int n + (int n - int 1) * int i"
        using \<open>n > 0\<close> by fastforce
      also have "... = int n + int n * int i - int i"
        by (simp add: left_diff_distrib')
      also have "... = int n * int i + (int n - int i)"
        by simp
      also have "... = int (n * i) + int (n - i)"
        using assms(2) by fastforce
      finally show ?thesis by presburger
    qed
    then show "n + (n - 1) * i = n * i + (n - i)" by presburger
  qed
  also have "... = (\<mu> [^] n) [^] i \<otimes> \<mu> [^] (n - i)"
    using nat_pow_mult nat_pow_pow
    using assms roots_Units Units_closed by algebra
  also have "... = \<mu> [^] (n - i)"
    using assms unfolding root_of_unity_def by simp
  finally show "(inv \<mu>) [^] i = \<mu> [^] (n - i)" by blast
  show "n - i \<in> {1..<n}" using assms by auto
qed

lemma root_of_unity_nat_pow_closed:
  assumes "root_of_unity n \<mu>"
  shows "root_of_unity n (\<mu> [^] (m :: nat))"
  using assms root_group.nat_pow_closed root_subgroup.nat_pow_eq by simp

lemma root_of_unity_powers:
  assumes "root_of_unity n \<mu>"
  shows "\<mu> [^] i = \<mu> [^] (i mod n)"
proof -
  have[simp]: "\<mu> \<in> carrier R" using assms by simp
  define s t where "s = i div n" "t = i mod n"
  then have "i = s * n + t" "t < n" using \<open>n > 0\<close> by simp_all
  then have "\<mu> [^] i = \<mu> [^] (s * n) \<otimes> \<mu> [^] t" by (simp add: nat_pow_mult)
  also have "\<mu> [^] (s * n) = (\<mu> [^] n) [^] s" by (simp add: nat_pow_pow mult.commute)
  also have "... = \<one>" using assms by simp
  finally show ?thesis using \<open>t = i mod n\<close> by simp
qed

lemma root_of_unity_powers_modint:
  assumes "root_of_unity n \<mu>"
  shows "\<mu> [^] (i :: int) = \<mu> [^] (i mod int n)"
proof -
  have "\<mu> \<in> Units R" "\<mu> [^] n = \<one>" using assms by simp_all
  define s t where "s = i div int n" "t = i mod int n"
  then have "i = s * int n + t" "t \<ge> 0" "t < int n" using \<open>n > 0\<close> by simp_all
  then have "\<mu> [^] i = \<mu> [^] (s * int n) \<otimes> \<mu> [^] t"
    using int_pow_mult[OF \<open>\<mu> \<in> Units R\<close>] by simp
  also have "... = (\<mu> [^] int n) [^] s \<otimes> \<mu> [^] t"
    by (intro_cong "[cong_tag_2 (\<otimes>)]" more: refl) (simp add: int_pow_pow \<open>\<mu> \<in> Units R\<close> mult.commute)
  also have "... = (\<mu> [^] n) [^] s \<otimes> \<mu> [^] t"
    apply (intro_cong "[cong_tag_2 (\<otimes>), cong_tag_1 (\<lambda>i. i [^] s)]" more: refl)
    using \<open>n > 0\<close> by (simp add: int_pow_int)
  also have "... = \<mu> [^] t"
    using int_pow_closed[OF \<open>\<mu> \<in> Units R\<close>] Units_closed l_one
    by (simp add: \<open>\<mu> [^] n = \<one>\<close> int_pow_one int_pow_closed)
  finally show ?thesis unfolding s_t_def .
qed

lemma root_of_unity_powers_nat:
  assumes "root_of_unity n \<mu>"
  assumes "i mod n = j mod n"
  shows "\<mu> [^] i = \<mu> [^] j"
  using assms root_of_unity_powers by metis

lemma root_of_unity_powers_int:
  assumes "root_of_unity n \<mu>"
  assumes "i mod int n = j mod int n"
  shows "\<mu> [^] i = \<mu> [^] j"
  using assms root_of_unity_powers_modint by metis

end

subsection "Primitive Roots"

definition primitive_root :: "nat \<Rightarrow> 'a \<Rightarrow> bool" where
"primitive_root n \<mu> \<equiv> root_of_unity n \<mu> \<and> (\<forall>i \<in> {1..<n}. \<mu> [^] i \<noteq> \<one>)"

lemma primitive_rootI[intro]:
  assumes "\<mu> \<in> carrier R"
  assumes "\<mu> [^] n = \<one>"
  assumes "\<And>i. i > 0 \<Longrightarrow> i < n \<Longrightarrow> \<mu> [^] i \<noteq> \<one>"
  shows "primitive_root n \<mu>"
  unfolding primitive_root_def root_of_unity_def using assms by simp

lemma primitive_root_is_root_of_unity[simp]: "primitive_root n \<mu> \<Longrightarrow> root_of_unity n \<mu>"
  unfolding primitive_root_def by simp

lemma primitive_root_recursion:
  assumes "even n"
  assumes "primitive_root n \<mu>"
  shows "primitive_root (n div 2) (\<mu> [^] (2 :: nat))"
  unfolding primitive_root_def root_of_unity_def
  apply (intro conjI)
  subgoal
    using assms(2) unfolding primitive_root_def root_of_unity_def by blast
  subgoal
    using nat_pow_pow[of \<mu> "2::nat" "n div 2"] assms apply simp
    unfolding primitive_root_def root_of_unity_def apply simp
    done
  subgoal
  proof
    fix i
    assume "i \<in> {1..<n div 2}"
    then have "2 * i \<in> {1..<n}" using \<open>even n\<close> by auto
    have "(\<mu> [^] (2::nat)) [^] i = \<mu> [^] (2 * i)"
      using assms unfolding primitive_root_def root_of_unity_def by (simp add: nat_pow_pow)
    also have "... \<noteq> \<one>"
      using assms unfolding primitive_root_def using \<open>2 * i \<in> {1..<n}\<close> by blast
    finally show "(\<mu> [^] (2::nat)) [^] i \<noteq> \<one>" .
  qed
  done

lemma primitive_root_inv:
  assumes "n > 0"
  assumes "primitive_root n \<mu>"
  shows "primitive_root n (inv \<mu>)"
  unfolding primitive_root_def
proof (intro conjI)
  show "root_of_unity n (inv \<mu>)" using assms unfolding primitive_root_def
    by (simp add: root_of_unity_inv)
  show "\<forall>i\<in>{1..<n}. inv \<mu> [^] i \<noteq> \<one>" using assms unfolding primitive_root_def
    by (metis Group.nat_pow_0 Units_inv_inv bot_nat_0.extremum_strict nat_neq_iff root_of_unity_def root_of_unity_inv roots_Units)
qed

subsection "Number Theoretic Transforms"

definition NTT :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"NTT \<mu> a \<equiv> let n = length a in [\<Oplus>j \<leftarrow> [0..<n]. (a ! j) \<otimes> (\<mu> [^] i) [^] j. i \<leftarrow> [0..<n]]"

lemma NTT_length[simp]: "length (NTT \<mu> a) = length a"
  unfolding NTT_def by (metis length_map map_nth)

lemma NTT_nth:
  assumes "length a = n"
  assumes "i < n"
  shows "NTT \<mu> a ! i = (\<Oplus>j \<leftarrow> [0..<n]. (a ! j) \<otimes> (\<mu> [^] i) [^] j)"
  unfolding NTT_def using assms by auto

lemma NTT_nth_2:
  assumes "length a = n"
  assumes "i < n"
  assumes "\<mu> \<in> carrier R"
  shows "NTT \<mu> a ! i = (\<Oplus>j \<leftarrow> [0..<n]. (a ! j) \<otimes> (\<mu> [^] (i * j)))"
  unfolding NTT_nth[OF assms(1) assms(2)]
  by (intro monoid_sum_list_cong arg_cong[where f = "(\<otimes>) _"] nat_pow_pow assms(3))

lemma NTT_nth_closed:
  assumes "set a \<subseteq> carrier R"
  assumes "\<mu> \<in> carrier R"
  assumes "length a = n"
  assumes "i < n"
  shows "NTT \<mu> a ! i \<in> carrier R"
proof -
  have "NTT \<mu> a ! i = (\<Oplus>j \<leftarrow> [0..<length a]. (a ! j) \<otimes> (\<mu> [^] i) [^] j)"
    using NTT_nth assms by blast
  also have "... \<in> carrier R"
    by (intro monoid_sum_list_closed m_closed nat_pow_closed assms(2) set_subseteqD[OF assms(1)]) simp
  finally show ?thesis .
qed

lemma NTT_closed:
  assumes "set a \<subseteq> carrier R"
  assumes "\<mu> \<in> carrier R"
  shows "set (NTT \<mu> a) \<subseteq> carrier R"
  using assms NTT_nth_closed[of a \<mu>]
  by (intro subsetI)(metis NTT_length in_set_conv_nth)

lemma "primitive_root 1 \<one>"
  unfolding primitive_root_def root_of_unity_def
  by simp
  
lemma "(\<ominus> \<one>) [^] (2::nat) = \<one>"
  by (simp add: numeral_2_eq_2) algebra
lemma "\<one> \<oplus> \<one> \<noteq> \<zero> \<Longrightarrow> primitive_root 2 (\<ominus> \<one>)"
  unfolding primitive_root_def root_of_unity_def
  apply (intro conjI)
  subgoal by simp
  subgoal by (simp add: numeral_2_eq_2, algebra)
  subgoal
  proof (standard, rule ccontr)
    fix i
    assume "\<one> \<oplus> \<one> \<noteq> \<zero>" "i \<in> {1::nat..<2}"
    then have "i = 1" by simp
    assume "\<not> \<ominus> \<one> [^] i \<noteq> \<one>"
    then have "\<ominus> \<one> = \<one>" using \<open>i = 1\<close> by simp
    then have "\<one> \<oplus> \<one> = \<zero>" using l_neg by fastforce
    thus False using \<open>\<one> \<oplus> \<one> \<noteq> \<zero>\<close> by simp
  qed
  done

subsubsection "Inversion Rule"

theorem inversion_rule:
  fixes \<mu> :: 'a
  fixes n :: nat
  assumes "n > 0"
  assumes "primitive_root n \<mu>"
  assumes good: "\<And>i. i \<in> {1..<n} \<Longrightarrow> (\<Oplus>j \<leftarrow> [0..<n]. (\<mu> [^] i) [^] j) = \<zero>"
  assumes[simp]: "length a = n"
  assumes[simp]: "set a \<subseteq> carrier R"
  shows "NTT (inv \<mu>) (NTT \<mu> a) = map (\<lambda>x. nat_embedding n \<otimes> x) a"
proof (intro nth_equalityI)
  have "\<mu> \<in> Units R" using assms unfolding primitive_root_def using roots_Units by blast
  then have[simp]: "\<mu> \<in> carrier R" by blast
  show "length (NTT (inv \<mu>) (NTT \<mu> a)) = length (map ((\<otimes>) (nat_embedding n)) a)" using NTT_length
    by simp
  fix i
  assume "i < length (NTT (inv \<mu>) (NTT \<mu> a))"
  then have "i < n" by simp

  have[simp]: "inv \<mu> \<in> carrier R" using assms roots_Units unfolding primitive_root_def by blast
  then have[simp]: "\<And>i :: nat. (inv \<mu>) [^] i \<in> carrier R" by simp

  have 0: "NTT (inv \<mu>) (NTT \<mu> a) ! i = (\<Oplus>j \<leftarrow> [0..<n]. (NTT \<mu> a ! j) \<otimes> ((inv \<mu>) [^] i) [^] j)"
    using NTT_nth
    using assms NTT_length \<open>i < n\<close> by blast
  also have "... = (\<Oplus>j \<leftarrow> [0..<n]. (\<Oplus>k \<leftarrow> [0..<n]. a ! k \<otimes> \<mu> [^] ((int k - int i) * int j)))"
  proof (intro monoid_sum_list_cong)
    fix j
    assume "j \<in> set [0..<n]"
    then have[simp]: "j < n" by simp
    have nj: "(NTT \<mu> a ! j) = (\<Oplus>k \<leftarrow> [0..<n]. a ! k \<otimes> (\<mu> [^] j) [^] k)"
      using NTT_nth by simp
    have "... \<otimes> ((inv \<mu>) [^] i) [^] j = (\<Oplus>k \<leftarrow> [0..<n]. a ! k \<otimes> ((\<mu> [^] j) [^] k) \<otimes> ((inv \<mu>) [^] i) [^] j)"
      apply (intro monoid_sum_list_in_right[symmetric] nat_pow_closed m_closed)
      using set_subseteqD[OF assms(5)] by simp_all
    also have "... = (\<Oplus>k \<leftarrow> [0..<n]. a ! k \<otimes> \<mu> [^] ((int k - int i) * int j))"
    proof (intro monoid_sum_list_cong)
      fix k
      assume "k \<in> set [0..<n]"
      have "a ! k \<otimes> (\<mu> [^] j) [^] k \<otimes> (inv \<mu> [^] i) [^] j = a ! k \<otimes> ((\<mu> [^] j) [^] k \<otimes> (inv \<mu> [^] i) [^] j)"
        apply (intro m_assoc nat_pow_closed)
        using set_subseteqD[OF assms(5)] \<open>k \<in> set [0..<n]\<close> by simp_all
      also have "inv \<mu> [^] i = \<mu> [^] (- int i)"
        by (metis \<open>\<mu> \<in> Units R\<close> cring.units_int_pow_neg int_pow_int is_cring)
      also have "((\<mu> [^] j) [^] k \<otimes> (\<mu> [^] (- int i)) [^] j) = \<mu> [^] (int j * int k - int i * int j)"
        using \<open>\<mu> \<in> Units R\<close>
        by (simp add: int_pow_int[symmetric] int_pow_pow int_pow_mult)
      also have "... = \<mu> [^] ((int k - int i) * int j)"
        apply (intro arg_cong[where f = "([^]) _"])
        by (simp add: mult.commute right_diff_distrib')
      finally show "a ! k \<otimes> (\<mu> [^] j) [^] k \<otimes> (inv \<mu> [^] i) [^] j = a ! k \<otimes> \<mu> [^] ((int k - int i) * int j)"
        using \<open>inv \<mu> [^] i = \<mu> [^] (- int i)\<close> by argo
    qed
    finally show "NTT \<mu> a ! j \<otimes> (inv \<mu> [^] i) [^] j = monoid_sum_list (\<lambda>k. a ! k \<otimes> \<mu> [^] ((int k - int i) * int j)) [0..<n]"
      by (simp add: nj)
  qed
  also have "... = (\<Oplus>k \<leftarrow> [0..<n]. (\<Oplus>j \<leftarrow> [0..<n]. a ! k \<otimes> \<mu> [^] ((int k - int i) * int j)))"
    apply (intro monoid_sum_list_swap m_closed)
    subgoal for j k
      using assms by (metis atLeastLessThan_iff atLeastLessThan_upt nth_mem subset_eq)
    subgoal for j k
      using \<open>\<mu> \<in> Units R\<close>
      using units_of_int_pow[OF \<open>\<mu> \<in> Units R\<close>]
      using group.int_pow_closed[OF units_group, of \<mu>]
      by (metis Units_closed units_of_carrier)
    done
  also have "... = (\<Oplus>k \<leftarrow> [0..<n]. a ! k \<otimes> (\<Oplus>j \<leftarrow> [0..<n]. \<mu> [^] ((int k - int i) * int j)))"
    apply (intro monoid_sum_list_cong monoid_sum_list_in_left)
    subgoal using set_subseteqD[OF assms(5)] by simp
    subgoal for j
      by (simp add: Units_closed int_pow_closed \<open>\<mu> \<in> Units R\<close>)
    done
  also have "... = (\<Oplus>k \<leftarrow> [0..<n]. a ! k \<otimes> (if i = k then nat_embedding n else \<zero>))"
  proof (intro monoid_sum_list_cong arg_cong[where f = "(\<otimes>) _"])
    fix k
    assume "k \<in> set [0..<n]"
    then have[simp]: "k < n" by simp
    consider "i < k" | "i = k" | "i > k" by fastforce
    then show "(\<Oplus>j \<leftarrow> [0..<n]. \<mu> [^] ((int k - int i) * int j)) = (if i = k then nat_embedding n else \<zero>)"
    proof (cases)
      case 1
      then have "\<And>j. j < n \<Longrightarrow> \<mu> [^] ((int k - int i) * int j) = (\<mu> [^] (k - i)) [^] j"
      proof -
        fix j
        assume "j < n"
        have "(int k - int i) * int j = int ((k - i) * j)" using 1 by auto
        then have "\<mu> [^] ((int k - int i) * int j) = \<mu> [^] int ((k - i) * j)"
          by argo
        also have "... = \<mu> [^] ((k - i) * j)"
          by (intro int_pow_int)
        also have "... = (\<mu> [^] (k - i)) [^] j"
          by (intro nat_pow_pow[symmetric] \<open>\<mu> \<in> carrier R\<close>)
        finally show "\<mu> [^] ((int k - int i) * int j) = (\<mu> [^] (k - i)) [^] j" .
      qed
      then have "(\<Oplus>j \<leftarrow> [0..<n]. \<mu> [^] ((int k - int i) * int j)) = (\<Oplus>j \<leftarrow> [0..<n]. (\<mu> [^] (k - i)) [^] j)"
        by (intro monoid_sum_list_cong, simp)
      also have "... = \<zero>"
        using good[of "k - i"]
      proof
        show "k - i \<in> {1..<n}" using 1 \<open>k < n\<close> by (simp add: less_imp_diff_less)
      qed simp
      finally show ?thesis using 1 by simp
    next
      case 2
      then have "\<And>j. j < n \<Longrightarrow> \<mu> [^] ((int k - int i) * int j) = \<one>" by simp
      then have "(\<Oplus>j \<leftarrow> [0..<n]. \<mu> [^] ((int k - int i) * int j)) = nat_embedding n"
        using monoid_sum_list_const[of \<one> "[0..<n]"]
        using monoid_sum_list_cong[of "[0..<n]" "\<lambda>j. \<mu> [^] ((int k - int i) * int j)" "\<lambda>j. \<one>"]
        by simp
      then show ?thesis using 2 by simp
    next
      case 3
      then have "\<And>j. j < n \<Longrightarrow> \<mu> [^] ((int k - int i) * int j) = (\<mu> [^] (n + k - i)) [^] j"
      proof -
        fix j
        assume "j < n"
        have "\<mu> [^] ((int k - int i) * int j) = (\<mu> [^] (int k - int i)) [^] j"
          using int_pow_pow by (metis \<open>\<mu> \<in> Units R\<close> int_pow_int)
        also have "... = (\<mu> [^] n \<otimes> \<mu> [^] (int k - int i)) [^] j"
        proof -
          have "\<mu> [^] (int k - int i) \<in> carrier R"
            using \<open>\<mu> \<in> Units R\<close> int_pow_closed Units_closed by simp
          then have "\<mu> [^] (int k - int i) = \<mu> [^] n \<otimes> \<mu> [^] (int k - int i)"
            using l_one assms(2) unfolding primitive_root_def root_of_unity_def
            by presburger
          then show ?thesis by simp
        qed
        also have "... = (\<mu> [^] (int n) \<otimes> \<mu> [^] (int k - int i)) [^] j"
          by (simp add: int_pow_int)
        also have "... = (\<mu> [^] (int n + int k - int i)) [^] j"
          using \<open>\<mu> \<in> Units R\<close> by (simp add: int_pow_mult add_diff_eq)
        finally show "\<mu> [^] ((int k - int i) * int j) = (\<mu> [^] (n + k - i)) [^] j" using 3
          by (metis (no_types, opaque_lifting) \<open>i < n\<close> diff_cancel2 diff_diff_cancel diff_le_self int_plus int_pow_int less_or_eq_imp_le of_nat_diff)
      qed
      then have "(\<Oplus>j \<leftarrow> [0..<n]. \<mu> [^] ((int k - int i) * int j)) = (\<Oplus>j \<leftarrow> [0..<n]. (\<mu> [^] (n + k - i)) [^] j)"
        by (intro monoid_sum_list_cong, simp)
      also have "... = \<zero>"
        using good[of "n + k - i"]
      proof
        show "n + k - i \<in> {1..<n}" using 3 \<open>k < n\<close> \<open>i < n\<close> by fastforce
      qed simp
      finally show ?thesis using 3 by simp
    qed
  qed
  also have "... = (\<Oplus>k \<leftarrow> [0..<n]. a ! k \<otimes> (nat_embedding n \<otimes> delta k i))"
    apply (intro monoid_sum_list_cong)
    unfolding delta_def
    by simp
  also have "... = (\<Oplus>k \<leftarrow> [0..<n]. nat_embedding n \<otimes> (delta k i \<otimes> a ! k))"
    apply (intro monoid_sum_list_cong)
    using m_assoc m_comm delta_closed set_subseteqD[OF assms(5)] nat_embedding_closed by simp
  also have "... = nat_embedding n \<otimes> (\<Oplus>k \<leftarrow> [0..<n]. delta k i \<otimes> a ! k)"
    using set_subseteqD[OF assms(5)]
    by (intro monoid_sum_list_in_left) auto
  also have "... = nat_embedding n \<otimes> a ! i"
    using monoid_sum_list_delta[of n "\<lambda>k. a ! k" i] \<open>i < n\<close> assms
    by (metis (no_types, lifting) nth_mem subsetD)
  finally show "NTT (inv \<mu>) (NTT \<mu> a) ! i = map ((\<otimes>) (nat_embedding n)) a ! i"
    using nth_map \<open>i < n\<close> \<open>length a = n\<close> NTT_length 0
    by simp
qed

lemma inv_good:
  assumes "n > 0"
  assumes "primitive_root n \<mu>"
  assumes good: "\<And>i. i \<in> {1..<n} \<Longrightarrow> (\<Oplus>j \<leftarrow> [0..<n]. (\<mu> [^] i) [^] j) = \<zero>"
  shows "primitive_root n (inv \<mu>)"
      "\<And>i. i \<in> {1..<n} \<Longrightarrow> (\<Oplus>j \<leftarrow> [0..<n]. ((inv \<mu>) [^] i) [^] j) = \<zero>"
  subgoal using assms by (simp add: primitive_root_inv)
  subgoal for i
  proof -
    assume "i \<in> {1..<n}"
    then have "n - i \<in> {1..<n}" by auto
    then have "(\<Oplus>j \<leftarrow> [0..<n]. (\<mu> [^] (n - i)) [^] j) = \<zero>"
      using assms by blast
    moreover have "\<mu> [^] (n - i) = inv \<mu> [^] i"
      using assms inv_pow_root_of_unity[of n \<mu> i] \<open>i \<in> {1..<n}\<close>
      by auto
    ultimately show "(\<Oplus>j \<leftarrow> [0..<n]. ((inv \<mu>) [^] i) [^] j) = \<zero>" by simp
  qed
  done

lemma inv_halfway_property:
  assumes "\<mu> \<in> Units R"
  assumes "\<mu> [^] (i::nat) = \<ominus> \<one>"
  shows "(inv \<mu>) [^] i = \<ominus> \<one>"
proof -
  have "(inv \<mu>) [^] i = (inv\<^bsub>units_of R\<^esub> \<mu>) [^] i"
    by (intro arg_cong[where f = "\<lambda>j. j [^] i"] units_of_inv[symmetric] assms(1))
  also have "... = (inv\<^bsub>units_of R\<^esub> \<mu>) [^]\<^bsub>units_of R\<^esub> i"
    apply (intro units_of_pow[symmetric])
    using units_group.Units_inv_Units assms(1) by simp
  also have "... = inv\<^bsub>units_of R\<^esub> (\<mu> [^]\<^bsub>units_of R\<^esub> i)"
    apply (intro units_group.nat_pow_inv)
    using assms(1) by (simp add: units_of_def)
  also have "... = inv (\<mu> [^]\<^bsub>units_of R\<^esub> i)"
    apply (intro units_of_inv)
    using assms(1) units_group.nat_pow_closed by (simp add: units_of_def)
  also have "... = inv (\<mu> [^] i)"
    using units_of_pow assms(1) by simp
  finally have "(inv \<mu>) [^] i = inv (\<mu> [^] i)" .
  also have "... = inv (\<ominus> \<one>)" using assms(2) by simp
  also have "... = \<ominus> \<one>" by simp
  finally show ?thesis .
qed

lemma sufficiently_good_aux:
  assumes "primitive_root m \<eta>"
  assumes "m = 2 ^ j"
  assumes "\<eta> [^] (m div 2) = \<ominus> \<one>"
  assumes "odd r"
  assumes "r * 2 ^ k < m"
  shows "(\<Oplus>l \<leftarrow> [0..<m]. (\<eta> [^] (r * 2 ^ k)) [^] l) = \<zero>"
  using assms
proof (induction k arbitrary: \<eta> m j)
  case 0
  then have "root_of_unity m \<eta>" by simp
  then have "\<eta> \<in> carrier R" by simp
  have "j > 0"
  proof (rule ccontr)
    assume "\<not> j > 0"
    then have "j = 0" by simp
    then have "m = 1" using 0 by simp
    then have "r * 2 ^ k = 0" using 0 by simp
    then have "r = 0" by simp
    then show "False" using \<open>odd r\<close> by simp
  qed
  then have "even m" using 0 by simp
  then have "m = m div 2 + m div 2" by auto
  then have "(\<Oplus>l \<leftarrow> [0..<m]. (\<eta> [^] (r * 2 ^ 0)) [^] l) = (\<Oplus>l \<leftarrow> [0..<m div 2 + m div 2]. (\<eta> [^] r) [^] l)"
    by simp
  also have "... = (\<Oplus>l \<leftarrow> [0..<m div 2]. (\<eta> [^] r) [^] l) \<oplus> (\<Oplus>l \<leftarrow> [m div 2..<m div 2 + m div 2]. (\<eta> [^] r) [^] l)"
    by (intro monoid_sum_list_split[symmetric] nat_pow_closed, rule \<open>\<eta> \<in> carrier R\<close>)
  also have "... = (\<Oplus>l \<leftarrow> [0..<m div 2]. (\<eta> [^] r) [^] l) \<oplus> (\<Oplus>l \<leftarrow> [0..<m div 2]. (\<eta> [^] r) [^] (m div 2 + l))"
    by (intro arg_cong[where f = "(\<oplus>) _"] monoid_sum_list_index_shift_0)
  also have "... = (\<Oplus>l \<leftarrow> [0..<m div 2]. (\<eta> [^] r) [^] l \<oplus> (\<eta> [^] r) [^] (m div 2 + l))"
    by (intro monoid_sum_list_add_in nat_pow_closed; rule \<open>\<eta> \<in> carrier R\<close>)
  also have "... = (\<Oplus>l \<leftarrow> [0..<m div 2]. (\<eta> [^] r) [^] l \<ominus> (\<eta> [^] r) [^] l)"
  proof (intro monoid_sum_list_cong)
    fix l
    have "(\<eta> [^] r) [^] (m div 2 + l) = (\<eta> [^] r) [^] (m div 2) \<otimes> (\<eta> [^] r) [^] l"
      by (intro nat_pow_mult[symmetric] nat_pow_closed, rule \<open>\<eta> \<in> carrier R\<close>)
    also have "(\<eta> [^] r) [^] (m div 2) = (\<ominus> \<one>) [^] r"
      unfolding nat_pow_pow[OF \<open>\<eta> \<in> carrier R\<close>] mult.commute[of r _]
      by (simp only: nat_pow_pow[symmetric] \<open>\<eta> \<in> carrier R\<close> \<open>\<eta> [^] (m div 2) = \<ominus> \<one>\<close>)
    also have "... = \<ominus> \<one>" using \<open>odd r\<close>
      by (simp add: powers_of_negative)
    finally have "(\<eta> [^] r) [^] (m div 2 + l) = \<ominus> ((\<eta> [^] r) [^] l)"
      using \<open>\<eta> \<in> carrier R\<close> nat_pow_closed by algebra
    then show "(\<eta> [^] r) [^] l \<oplus> (\<eta> [^] r) [^] (m div 2 + l) = (\<eta> [^] r) [^] l \<ominus> (\<eta> [^] r) [^] l"
      unfolding minus_eq
      by (intro arg_cong[where f = "(\<oplus>) _"])
  qed
  also have "... = (\<Oplus>l \<leftarrow> [0..<m div 2]. \<zero>)"
    by (intro monoid_sum_list_cong) (simp add: \<open>\<eta> \<in> carrier R\<close>)
  also have "... = \<zero>" by simp
  finally show ?case .
next
  case (Suc k)
  have "j > 0"
  proof (rule ccontr)
    assume "\<not> j > 0"
    then have "j = 0" by simp
    then have "m = 1" using Suc by simp
    then have "r * 2 ^ k = 0" using Suc by simp
    then have "r = 0" by simp
    then show "False" using \<open>odd r\<close> by simp
  qed
  then have "even m" using Suc by simp
  then have "m = m div 2 + m div 2" by auto
  have "root_of_unity m \<eta>" using \<open>primitive_root m \<eta>\<close> by simp
  then have "\<eta> \<in> carrier R" by simp
  from \<open>j > 0\<close> obtain j' where "j = Suc j'"
    using gr0_implies_Suc by blast
  then have "m div 2 = 2 ^ j'" using \<open>m = 2 ^ j\<close> by simp
  have "j' > 0"
  proof (rule ccontr)
    assume "\<not> j' > 0"
    then have "j' = 0" by simp
    then have "m = 2" using \<open>m = 2 ^ j\<close> \<open>j = Suc j'\<close> by simp
    then have "r * 2 ^ Suc k < 2" using Suc by simp
    then show "False" using \<open>odd r\<close> by simp
  qed
  then have "even (m div 2)" using \<open>m div 2 = 2 ^ j'\<close> by simp
  have IH': "(\<Oplus>l \<leftarrow> [0..<m div 2]. ((\<eta> [^] (2::nat)) [^] (r * 2 ^ k)) [^] l) = \<zero>"
    apply (intro Suc.IH[of "m div 2" "\<eta> [^] (2::nat)" j'])
    subgoal using primitive_root_recursion[OF \<open>even m\<close>, OF \<open>primitive_root m \<eta>\<close>] .
    subgoal using \<open>m = 2 ^ j\<close> \<open>j = Suc j'\<close> by simp
    subgoal
      by (simp add: \<open>\<eta> \<in> carrier R\<close> nat_pow_pow \<open>even (m div 2)\<close> \<open>\<eta> [^] (m div 2) = \<ominus> \<one>\<close>)
    subgoal using \<open>odd r\<close> .
    subgoal using \<open>r * 2 ^ (Suc k) < m\<close> \<open>even m\<close> by auto
    done
  have "(\<Oplus>l \<leftarrow> [0..<m]. (\<eta> [^] (r * 2 ^ (Suc k))) [^] l) = (\<Oplus>l \<leftarrow> [0..<m]. ((\<eta> [^] (2::nat)) [^] (r * 2 ^ k)) [^] l)"
    unfolding nat_pow_pow[OF \<open>\<eta> \<in> carrier R\<close>]
    apply (intro monoid_sum_list_cong arg_cong[where f = "\<lambda>i. i [^] _"])
    apply (intro arg_cong[where f = "([^]) _"])
    by simp
  also have "... = (\<Oplus>l \<leftarrow> [0..<m div 2 + m div 2]. ((\<eta> [^] (2::nat)) [^] (r * 2 ^ k)) [^] l)"
    using \<open>m = m div 2 + m div 2\<close> by argo
  also have "... = (\<Oplus>l \<leftarrow> [0..<m div 2]. ((\<eta> [^] (2::nat)) [^] (r * 2 ^ k)) [^] l) \<oplus> (\<Oplus>l \<leftarrow> [m div 2..<m div 2 + m div 2]. ((\<eta> [^] (2::nat)) [^] (r * 2 ^ k)) [^] l)"
    by (intro monoid_sum_list_split[symmetric] nat_pow_closed, rule \<open>\<eta> \<in> carrier R\<close>)
  also have "... = \<zero> \<oplus> (\<Oplus>l \<leftarrow> [m div 2..<m div 2 + m div 2]. ((\<eta> [^] (2::nat)) [^] (r * 2 ^ k)) [^] l)"
    using IH' by argo
  also have "... = (\<Oplus>l \<leftarrow> [m div 2..<m div 2 + m div 2]. ((\<eta> [^] (2::nat)) [^] (r * 2 ^ k)) [^] l)"
    by (intro l_zero monoid_sum_list_closed nat_pow_closed, rule \<open>\<eta> \<in> carrier R\<close>)
  also have "... = (\<Oplus>l \<leftarrow> [0..<m div 2]. ((\<eta> [^] (2::nat)) [^] (r * 2 ^ k)) [^] (m div 2 + l))"
    by (intro monoid_sum_list_index_shift_0)
  also have "... = (\<Oplus>l \<leftarrow> [0..<m div 2]. ((\<eta> [^] (2::nat)) [^] (r * 2 ^ k)) [^] (m div 2) \<otimes> ((\<eta> [^] (2::nat)) [^] (r * 2 ^ k)) [^] l)"
    by (intro monoid_sum_list_cong nat_pow_mult[symmetric] nat_pow_closed, rule \<open>\<eta> \<in> carrier R\<close>)
  also have "... = ((\<eta> [^] (2::nat)) [^] (r * 2 ^ k)) [^] (m div 2) \<otimes> (\<Oplus>l \<leftarrow> [0..<m div 2]. ((\<eta> [^] (2::nat)) [^] (r * 2 ^ k)) [^] l)"
    by (intro monoid_sum_list_in_left nat_pow_closed; rule \<open>\<eta> \<in> carrier R\<close>)
  also have "... = ((\<eta> [^] (2::nat)) [^] (r * 2 ^ k)) [^] (m div 2) \<otimes> \<zero>"
    using IH' by argo
  also have "... = \<zero>"
    by (intro r_null nat_pow_closed, rule \<open>\<eta> \<in> carrier R\<close>)
  finally show ?case .
qed


lemma sufficiently_good:
  assumes "primitive_root n \<mu>"
  assumes "domain R \<or> (n = 2 ^ k \<and> \<mu> [^] (n div 2) = \<ominus> \<one>)"
  shows good: "\<And>i. i \<in> {1..<n} \<Longrightarrow> (\<Oplus>j \<leftarrow> [0..<n]. (\<mu> [^] i) [^] j) = \<zero>"
proof (cases "domain R")
  case True
  fix i
  assume "i \<in> {1..<n}"

  have "root_of_unity n \<mu>" using assms(1) by simp
  then have "\<mu> \<in> carrier R" "\<mu> [^] n = \<one>" by simp_all

  have "\<mu> [^] i \<noteq> \<one>" using assms(1) \<open>i \<in> {1..<n}\<close> unfolding primitive_root_def
    by simp
  then have "\<one> \<ominus> \<mu> [^] i \<noteq> \<zero>" using \<open>\<mu> \<in> carrier R\<close> by simp

  have "(\<mu> [^] i) [^] n = \<one>"
    unfolding nat_pow_pow[OF \<open>\<mu> \<in> carrier R\<close>]
    using root_of_unity_powers[OF _ \<open>root_of_unity n \<mu>\<close>, of "i * n"]
    by (cases "n > 0"; simp)
  then have "\<zero> = \<one> \<ominus> (\<mu> [^] i) [^] n" by algebra
  also have "... = (\<one> \<ominus> \<mu> [^] i) \<otimes> (\<Oplus>j \<leftarrow> [0..<n]. (\<mu> [^] i) [^] j)"
    by (intro geo_monoid_list_sum[symmetric] nat_pow_closed \<open>\<mu> \<in> carrier R\<close>)
  finally show "(\<Oplus>j \<leftarrow> [0..<n]. (\<mu> [^] i) [^] j) = \<zero>"
    using \<open>\<one> \<ominus> \<mu> [^] i \<noteq> \<zero>\<close> True \<open>\<mu> \<in> carrier R\<close>
    by (metis domain.integral minus_closed monoid_sum_list_closed nat_pow_closed one_closed)
next
  case False
  then have "n = 2 ^ k" "\<mu> [^] (n div 2) = \<ominus> \<one>" using assms(2) by auto

  have "root_of_unity n \<mu>" using \<open>primitive_root n \<mu>\<close> by simp
  then have "\<mu> \<in> carrier R" "\<mu> [^] n = \<one>" by simp_all
  
  fix i
  assume "i \<in> {1..<n}"
  define l where "l = Max {s. 2 ^ s dvd i}"
  define r where "r = i div 2 ^ l"
  from \<open>i \<in> {1..<n}\<close> have "i \<noteq> 0" by simp
  then have "i = r * 2 ^ l" "odd r" using max_dividing_power_factorization[of i l 2 r]
    using l_def r_def coprime_left_2_iff_odd[of r] by simp_all

  show "(\<Oplus>j \<leftarrow> [0..<n]. (\<mu> [^] i) [^] j) = \<zero>"
    apply (simp only: \<open>i = r * 2 ^ l\<close>)
    apply (intro sufficiently_good_aux[of n \<mu> k r l, OF \<open>primitive_root n \<mu>\<close> \<open>n = 2 ^ k\<close> \<open>\<mu> [^] (n div 2) = \<ominus> \<one>\<close> \<open>odd r\<close>])
    using \<open>i = r * 2 ^ l\<close> \<open>i \<in> {1..<n}\<close> by simp
qed

corollary inversion_rule_inv:
  fixes \<mu> :: 'a
  fixes n :: nat
  assumes "n > 0"
  assumes "primitive_root n \<mu>"
  assumes good: "\<And>i. i \<in> {1..<n} \<Longrightarrow> (\<Oplus>j \<leftarrow> [0..<n]. (\<mu> [^] i) [^] j) = \<zero>"
  assumes[simp]: "length a = n"
  assumes[simp]: "set a \<subseteq> carrier R"
  shows "NTT \<mu> (NTT (inv \<mu>) a) = map (\<lambda>x. nat_embedding n \<otimes> x) a"
  using assms inv_good[of n \<mu>] inversion_rule[of n "inv \<mu>" a]
  using Units_inv_inv[of \<mu>]
  using roots_Units[of n \<mu>]
  unfolding primitive_root_def
  by algebra

subsubsection "Convolution Theorem"

lemma root_of_unity_power_sum_product:
  assumes "root_of_unity n x"
  assumes[simp]: "\<And>i. i < n \<Longrightarrow> f i \<in> carrier R"
  assumes[simp]: "\<And>i. i < n \<Longrightarrow> g i \<in> carrier R"
  shows "(\<Oplus>i \<leftarrow> [0..<n]. f i \<otimes> x [^] i) \<otimes> (\<Oplus>i \<leftarrow> [0..<n]. g i \<otimes> x [^] i) =
    (\<Oplus>k \<leftarrow> [0..<n]. (\<Oplus>i \<leftarrow> [0..<n]. f i \<otimes> g ((n + k - i) mod n)) \<otimes> x [^] k)"
proof (cases "n > 0")
  case False
  then have "n = 0" by simp
  then show ?thesis by simp
next
  case True
  have[simp]: "x \<in> carrier R" using \<open>root_of_unity n x\<close> by simp

  have "(\<Oplus>k \<leftarrow> [0..<n]. (\<Oplus>i \<leftarrow> [0..<n]. f i \<otimes> g ((n + k - i) mod n)) \<otimes> x [^] k) =
      (\<Oplus>k \<leftarrow> [0..<n]. (\<Oplus>i \<leftarrow> [0..<n]. f i \<otimes> g ((n + k - i) mod n) \<otimes> x [^] k))"
    by (intro monoid_sum_list_cong monoid_sum_list_in_right[symmetric] nat_pow_closed m_closed)
        simp_all
  also have "... = (\<Oplus>k \<leftarrow> [0..<n]. (\<Oplus>i \<leftarrow> [0..<n]. f i \<otimes> g ((n + k - i) mod n) \<otimes> x [^] ((n + k - i) mod n + i)))"
    apply (intro monoid_sum_list_cong arg_cong[where f = "(\<otimes>) _"])
    apply (intro root_of_unity_powers_nat[OF \<open>n > 0\<close> \<open>root_of_unity n x\<close>])
    by (simp add: add.commute mod_add_right_eq)
  also have "... = (\<Oplus>k \<leftarrow> [0..<n]. (\<Oplus>i \<leftarrow> [0..<n]. f i \<otimes> g ((n + k - i) mod n) \<otimes> (x [^] ((n + k - i) mod n) \<otimes> x [^] i)))"
    by (intro monoid_sum_list_cong arg_cong[where f = "(\<otimes>) _"] nat_pow_mult[symmetric]) simp
  also have "... = (\<Oplus>k \<leftarrow> [0..<n]. (\<Oplus>i \<leftarrow> [0..<n]. f i \<otimes> x [^] i \<otimes> (g ((n + k - i) mod n) \<otimes> x [^] ((n + k - i) mod n))))"
  proof -
    have reorder: "\<And>a b c d. \<lbrakk> a \<in> carrier R; b \<in> carrier R; c \<in> carrier R; d \<in> carrier R \<rbrakk> \<Longrightarrow>
      a \<otimes> b \<otimes> (c \<otimes> d) = a \<otimes> d \<otimes> (b \<otimes> c)"
      using m_comm m_assoc by algebra
    show ?thesis
      by (intro monoid_sum_list_cong reorder nat_pow_closed) simp_all
  qed
  also have "... = (\<Oplus>i \<leftarrow> [0..<n]. (\<Oplus>k \<leftarrow> [0..<n]. f i \<otimes> x [^] i \<otimes> (g ((n + k - i) mod n) \<otimes> x [^] ((n + k - i) mod n))))"
    by (intro monoid_sum_list_swap m_closed nat_pow_closed) simp_all
  also have "... = (\<Oplus>i \<leftarrow> [0..<n]. f i \<otimes> x [^] i \<otimes> (\<Oplus>k \<leftarrow> [0..<n]. (g ((n + k - i) mod n) \<otimes> x [^] ((n + k - i) mod n))))"
    by (intro monoid_sum_list_cong monoid_sum_list_in_left m_closed nat_pow_closed) simp_all
  also have "... = (\<Oplus>i \<leftarrow> [0..<n]. f i \<otimes> x [^] i \<otimes> (\<Oplus>j \<leftarrow> [0..<n]. (g j \<otimes> x [^] j)))"
    (is "(\<Oplus>i \<leftarrow> _. _ \<otimes> ?lhs i) = (\<Oplus>i \<leftarrow> _. _ \<otimes> ?rhs i)")
  proof -
    have "\<And>i. i \<in> set [0..<n] \<Longrightarrow> ?lhs i = ?rhs i"
    proof (intro monoid_sum_list_index_permutation[symmetric] m_closed nat_pow_closed)
      fix i
      assume "i \<in> set [0..<n]"
      have "bij_betw (\<lambda>ia. (n - i + ia) mod n) {0..<n} {0..<n}"
        by (intro const_add_mod_bij)
      also have "bij_betw (\<lambda>ia. (n - i + ia) mod n) {0..<n} {0..<n} =
        bij_betw (\<lambda>ia. (n + ia - i) mod n) {0..<n} {0..<n}"
        apply (intro bij_betw_cong)
        using \<open>i \<in> set [0..<n]\<close> by simp
      finally show "bij_betw (\<lambda>ia. (n + ia - i) mod n) (set [0..<n]) (set [0..<n])" by simp
    qed simp_all
    then show ?thesis
      by (intro monoid_sum_list_cong) (intro arg_cong[where f = "(\<otimes>) _"])
  qed
  also have "... = (\<Oplus>i \<leftarrow> [0..<n]. f i \<otimes> x [^] i) \<otimes> (\<Oplus>j \<leftarrow> [0..<n]. (g j \<otimes> x [^] j))"
    by (intro monoid_sum_list_in_right monoid_sum_list_closed) simp_all
  finally show ?thesis by argo
qed

context
  fixes n :: nat
begin

definition cyclic_convolution :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "\<star>" 70) where
  "cyclic_convolution a b \<equiv> [(\<Oplus>\<sigma> \<leftarrow> [0..<n]. (a ! \<sigma> \<otimes> b ! ((n + i - \<sigma>) mod n))). i \<leftarrow> [0..<n]]"

lemma cyclic_convolution_length[simp]:
  "length (a \<star> b) = n" unfolding cyclic_convolution_def by simp

lemma cyclic_convolution_nth:
"i < n \<Longrightarrow> (a \<star> b) ! i = (\<Oplus>\<sigma> \<leftarrow> [0..<n]. (a ! \<sigma> \<otimes> b ! ((n + i - \<sigma>) mod n)))"
  unfolding cyclic_convolution_def by simp

lemma cyclic_convolution_closed:
  assumes "length a = n" "length b = n"
  assumes "set a \<subseteq> carrier R" "set b \<subseteq> carrier R"
  shows "set (a \<star> b) \<subseteq> carrier R"
proof (intro set_subseteqI)
  fix i
  assume "i < length (a \<star> b)"
  then have "i < n" using assms(1) assms(2) by simp
  then have "(a \<star> b) ! i = (\<Oplus>\<sigma> \<leftarrow> [0..<n]. (a ! \<sigma> \<otimes> b ! ((n + i - \<sigma>) mod n)))"
    using cyclic_convolution_nth by presburger
  also have "... \<in> carrier R"
    apply (intro monoid_sum_list_closed m_closed)
    subgoal for \<sigma> using set_subseteqD[OF assms(3)] \<open>length a = n\<close> by simp
    subgoal for \<sigma> using set_subseteqD[OF assms(4)] \<open>length b = n\<close> by simp
    done
  finally show "(a \<star> b) ! i \<in> carrier R" .
qed

theorem convolution_rule:
  assumes "length a = n"
  assumes "length b = n"
  assumes "set a \<subseteq> carrier R"
  assumes "set b \<subseteq> carrier R"
  assumes "root_of_unity n \<mu>"
  assumes "i < n"
  shows "NTT \<mu> a ! i \<otimes> NTT \<mu> b ! i = NTT \<mu> (a \<star> b) ! i"
proof (cases "n > 0")
  case False
  then show ?thesis using \<open>i < n\<close> by simp
next
  case True

  then interpret root_group : group "roots_of_unity_group n"
    by (rule roots_of_unity_group_is_group)

  interpret root_subgroup : multiplicative_subgroup R "{\<mu>. root_of_unity n \<mu>}" "roots_of_unity_group n"
    apply unfold_locales
    subgoal using roots_Units \<open>n > 0\<close> by blast
    subgoal unfolding roots_of_unity_group_def[OF \<open>n > 0\<close>] by simp
    done

  have "\<mu> \<in> carrier R" using assms(5) by simp
  have "NTT \<mu> a ! i \<otimes> NTT \<mu> b ! i =
    (\<Oplus>j \<leftarrow> [0..<n]. a ! j \<otimes> (\<mu> [^] i) [^] j) \<otimes> (\<Oplus>j \<leftarrow> [0..<n]. b ! j \<otimes> (\<mu> [^] i) [^] j)"
    unfolding NTT_nth[OF assms(1) \<open>i < n\<close>] NTT_nth[OF assms(2) \<open>i < n\<close>] by argo
  also have "... = (\<Oplus>j \<leftarrow> [0..<n]. (\<Oplus>k \<leftarrow> [0..<n]. (a ! k) \<otimes> (b ! ((n + j - k) mod n))) \<otimes> (\<mu> [^] i) [^] j)"
    apply (intro root_of_unity_power_sum_product root_of_unity_nat_pow_closed)
    using True \<open>root_of_unity n \<mu>\<close> set_subseteqD[OF assms(3)] set_subseteqD[OF assms(4)] assms(1) assms(2)
    by simp_all
  also have "... = (\<Oplus>j \<leftarrow> [0..<n]. (a \<star> b) ! j \<otimes> (\<mu> [^] i) [^] j)"
    apply (intro monoid_sum_list_cong arg_cong[where f = "\<lambda>j. j \<otimes> _"] cyclic_convolution_nth[symmetric])
    by simp
  also have "... = NTT \<mu> (a \<star> b) ! i"
    apply (intro NTT_nth[symmetric]) using \<open>i < n\<close> by simp_all
  finally show ?thesis .
qed

end

end

end