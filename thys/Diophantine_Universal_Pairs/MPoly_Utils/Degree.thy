theory Degree
  imports Notation
begin

subsection \<open>Degree of a given variable\<close>

lemma degree_Const [simp]: "degree (Const x) v = 0"
  unfolding degree_def Const_def Const\<^sub>0_def
  by (simp add: MPoly_inverse)

lemma degree_Var [simp]:
  "degree ((Var v):: 'a::comm_semiring_1 mpoly) v' = (if v = v' then 1 else 0)"
  unfolding degree_def Var_def Var\<^sub>0_def
  by (simp add: MPoly_inverse lookup_single)

lemma degree_neg:
  fixes P :: "'a::ab_group_add mpoly"
  shows "degree (- P) = degree P"
  unfolding degree.rep_eq uminus_mpoly.rep_eq keys.rep_eq
  by auto

lemma degree_add:
  fixes P Q :: "'a::ab_group_add mpoly"
  shows "degree (P + Q) v \<le> max (degree P v) (degree Q v)"
proof - 
  { fix m assume "m \<in> keys (mapping_of (P + Q))" 
    hence "m \<in> keys (mapping_of P) \<or> m \<in> keys (mapping_of Q)"
      by (metis add.right_neutral coeff_add coeff_keys)
    moreover have "m \<in> keys (mapping_of P) \<Longrightarrow> lookup m v \<le> degree P v"
      by (simp add: degree_def)
    moreover have "m \<in> keys (mapping_of Q) \<Longrightarrow> lookup m v \<le> degree Q v"
      by (simp add: degree_def)
    ultimately have "lookup m v \<le> max (degree P v) (degree Q v)"
      by auto }
  thus ?thesis by (simp add: degree_def)
qed

lemma degree_add':
  fixes P Q :: "'a::ab_group_add mpoly"
  shows "degree (P + Q) v \<le> degree P v + degree Q v"
  using degree_add
  by (metis max_def trans_le_add1 trans_le_add2)

lemma degree_add_different_degree:
  fixes P :: "'a::ab_group_add mpoly"
  assumes "degree P v \<noteq> degree Q v"
  shows "degree (P + Q) v = max (degree P v) (degree Q v)"
proof -
  have 0: "Max (insert 0 ((\<lambda>m. lookup m v) ` keys (mapping_of P))) \<noteq>
           Max (insert 0 ((\<lambda>m. lookup m v) ` keys (mapping_of Q)))"
    using assms unfolding degree.rep_eq .
  have "Max (insert 0 ((\<lambda>m. lookup m v) ` keys (mapping_of P + mapping_of Q))) =
        max (Max (insert 0 ((\<lambda>m. lookup m v) ` keys (mapping_of P))))
            (Max (insert 0 ((\<lambda>m. lookup m v) ` keys (mapping_of Q))))"
  proof cases
    assume 1: "(\<lambda>m. lookup m v) ` keys (mapping_of P) = {}"
    show ?thesis
    proof cases
      assume 2: "(\<lambda>m. lookup m v) ` keys (mapping_of Q) = {}"
      show ?thesis using 0 1 assms unfolding degree.rep_eq by simp
    next
      assume 3: "(\<lambda>m. lookup m v) ` keys (mapping_of Q) \<noteq> {}"
      have "(\<lambda>m. lookup m v) ` keys (mapping_of P + mapping_of Q) =
            (\<lambda>m. lookup m v) ` keys (mapping_of Q)"
        using 1 3 by auto
      thus ?thesis using 1 by auto
    qed
  next
    assume 4: "(\<lambda>m. lookup m v) ` keys (mapping_of P) \<noteq> {}"
    show ?thesis
    proof cases
      assume 5: "(\<lambda>m. lookup m v) ` keys (mapping_of Q) = {}"
      have "(\<lambda>m. lookup m v) ` keys (mapping_of P + mapping_of Q) =
            (\<lambda>m. lookup m v) ` keys (mapping_of P)"
        using 4 5 by auto
      thus ?thesis using 5 by auto
    next
      assume 6: "(\<lambda>m. lookup m v) ` keys (mapping_of Q) \<noteq> {}"
      have 7: "(\<lambda>m. lookup m v) ` keys (mapping_of P + mapping_of Q) \<noteq> {}"
        using 0 eq_neg_iff_add_eq_0 by force
      obtain a where 8: "lookup a v = (MAX m\<in>keys (mapping_of P). lookup m v)"
                        "lookup (mapping_of P) a \<noteq> 0"
                        "\<And>m. lookup (mapping_of P) m \<noteq> 0 \<Longrightarrow> lookup m v \<le> lookup a v"
        using 4
        by (smt (verit, best) Max_ge Max_in finite_imageI finite_keys image_iff in_keys_iff)
      obtain b where 9: "lookup b v = (MAX m\<in>keys (mapping_of Q). lookup m v)"
                        "lookup (mapping_of Q) b \<noteq> 0"
                        "\<And>m. lookup (mapping_of Q) m \<noteq> 0 \<Longrightarrow> lookup m v \<le> lookup b v"
        using 6
        by (smt (verit, best) Max_ge Max_in finite_imageI finite_keys image_iff in_keys_iff)
      obtain c where 10: "lookup c v = (MAX m\<in>keys (mapping_of P + mapping_of Q). lookup m v)"
                         "lookup (mapping_of P) c + lookup (mapping_of Q) c \<noteq> 0"
                         "\<And>m. lookup (mapping_of P) m + lookup (mapping_of Q) m \<noteq> 0 
                          \<Longrightarrow> lookup m v \<le> lookup c v"
        using 7
        by (smt (verit, del_insts) Max_ge Max_in finite_imageI finite_keys image_iff 
            lookup_not_eq_zero_eq_in_keys plus_poly_mapping.rep_eq)
      have 11: "lookup a v \<noteq> lookup b v" unfolding 8(1) 9(1) using 0 4 6 by simp
      have "lookup c v = max (lookup a v) (lookup b v)"
        using 8 9 10 11
        by (smt (verit, del_insts) add_cancel_right_right max.bounded_iff order_class.order_eq_iff)
      hence "(MAX m\<in>keys (mapping_of P + mapping_of Q). lookup m v) =
             max (MAX m\<in>keys (mapping_of P). lookup m v)
                 (MAX m\<in>keys (mapping_of Q). lookup m v)"
        unfolding 8(1) 9(1) 10(1) .
      thus ?thesis using 4 6 7 by auto
    qed
  qed
  thus ?thesis unfolding degree.rep_eq plus_mpoly.rep_eq plus_poly_mapping.rep_eq .
qed

lemma degree_diff:
  fixes P Q :: "'a::ab_group_add mpoly"
  shows "degree (P - Q) v \<le> max (degree P v) (degree Q v)"
  unfolding diff_conv_add_uminus[of P] degree_neg[of Q, symmetric]
  by (rule degree_add)

lemma degree_diff':
  fixes P Q :: "'a::ab_group_add mpoly"
  shows "degree (P - Q) v \<le> degree P v + degree Q v"
  unfolding diff_conv_add_uminus[of P] degree_neg[of Q, symmetric]
  by (rule degree_add')

lemma degree_diff_different_degree:
  fixes P :: "'a::ab_group_add mpoly"
  assumes "degree P v \<noteq> degree Q v"
  shows "degree (P - Q) v = max (degree P v) (degree Q v)"
  unfolding diff_conv_add_uminus[of P] degree_neg[of Q, symmetric]
  apply (rule degree_add_different_degree)
  unfolding degree_neg apply (rule assms)
  done

lemma degree_sum:
  fixes P :: "'a \<Rightarrow> 'b::ab_group_add mpoly"
  assumes S_fin: "finite S"
  shows "degree (sum P S) v \<le> Max (insert 0 ((\<lambda>i. degree (P i) v) ` S))"
proof (induct rule:finite_induct[OF S_fin])
  case 1 show ?case by simp
next 
  case (2 x S)
  have "degree (sum P (insert x S)) v = degree (sum P S + P x) v"
    by (simp add: "2.hyps" add.commute)
  also have "... \<le> max (degree (sum P S) v) (degree (P x) v)"
    using degree_add by auto
  also have "... \<le> max (Max (insert 0 ((\<lambda>i. degree (P i) v) ` S))) (degree (P x) v)"
    using "2.hyps" by auto
  also have "... = Max (insert (degree (P x) v) (insert 0 ((\<lambda>i. degree (P i) v) ` S)))"
    by (simp add: "2.hyps")
  also have "... = Max (insert 0 ((\<lambda>i. degree (P i) v) ` (insert x S)))"
    by (simp add: insert_commute)
  finally show ?case .
qed

lemma degree_mult: "degree (P * Q) v \<le> degree P v + degree Q v"
proof -
  have "m \<in> keys (mapping_of (P * Q)) \<Longrightarrow>
        lookup m v \<le> degree P v + degree Q v" for m
  proof -
    assume "m \<in> keys (mapping_of (P * Q))"
    hence "m \<in> keys (mapping_of P * mapping_of Q)"
      by (simp add: times_mpoly.rep_eq)
    hence "m \<in> {a + b | a b. a \<in> keys (mapping_of P) \<and> b \<in> keys (mapping_of Q)}"
      using keys_mult by blast
    then obtain a b where m_def: "m = a + b"
                      and a_key: "a \<in> keys (mapping_of P)"
                      and b_key: "b \<in> keys (mapping_of Q)"
      by blast
    from a_key have a_bound: "lookup a v \<le> degree P v"
      unfolding degree.rep_eq by simp
    from b_key have b_bound: "lookup b v \<le> degree Q v"
      unfolding degree.rep_eq by simp
    have "lookup m v = lookup a v + lookup b v"
      unfolding m_def lookup_add by simp
    thus "lookup m v \<le> degree P v + degree Q v"
      using a_bound b_bound by simp
  qed
  thus ?thesis unfolding degree.rep_eq by simp
qed

lemma degree_mult_non_zero:
  fixes P Q :: "'a::idom mpoly"
  assumes "P \<noteq> 0" "Q \<noteq> 0"
  shows "degree (P * Q) v = degree P v + degree Q v"
proof (rule antisym)
  show "degree (P * Q) v \<le> degree P v + degree Q v" by (rule degree_mult)
next
  define a where "a = Max ((\<lambda>m. lookup m v) ` keys (mapping_of P))"
  define b where "b = Max ((\<lambda>m. lookup m v) ` keys (mapping_of Q))"
  define c where "c = Max ((\<lambda>m. lookup m v) ` keys (mapping_of (P * Q)))"
  define p where "p = Max {m \<in> keys (mapping_of P). lookup m v = a}"
  define q where "q = Max {m \<in> keys (mapping_of Q). lookup m v = b}"
  define r where "r = Max {m \<in> keys (mapping_of (P * Q)). lookup m v = c}"
  have 0: "P * Q \<noteq> 0" using assms by auto
  have 1: "keys (mapping_of P) \<noteq> {}"
          "keys (mapping_of Q) \<noteq> {}"
          "keys (mapping_of (P * Q)) \<noteq> {}"
    using assms 0 mapping_of_inject zero_mpoly.rep_eq
    by (metis keys_eq_empty)+
  have 2: "a \<in> (\<lambda>m. lookup m v) ` keys (mapping_of P)"
          "b \<in> (\<lambda>m. lookup m v) ` keys (mapping_of Q)"
          "c \<in> (\<lambda>m. lookup m v) ` keys (mapping_of (P * Q))"
    unfolding a_def b_def c_def
    using 1 Max_in
    by simp+
  have 3: "p \<in> {m \<in> keys (mapping_of P). lookup m v = a}"
          "q \<in> {m \<in> keys (mapping_of Q). lookup m v = b}"
          "r \<in> {m \<in> keys (mapping_of (P * Q)). lookup m v = c}"
    unfolding p_def q_def r_def
    using 2 Max_in[of "{m \<in> keys (mapping_of _). lookup m v = _}"]
    by auto
  have 4: "\<And>m. m \<in> keys (mapping_of P) \<Longrightarrow> lookup m v \<le> a"
          "\<And>m. m \<in> keys (mapping_of Q) \<Longrightarrow> lookup m v \<le> b"
          "\<And>m. m \<in> keys (mapping_of (P * Q)) \<Longrightarrow> lookup m v \<le> c"
    unfolding a_def b_def c_def
    by auto
  have 5: "\<And>m. m \<in> keys (mapping_of P) \<Longrightarrow> lookup m v = a \<Longrightarrow> m \<le> p"
          "\<And>m. m \<in> keys (mapping_of Q) \<Longrightarrow> lookup m v = b \<Longrightarrow> m \<le> q"
          "\<And>m. m \<in> keys (mapping_of (P * Q)) \<Longrightarrow> lookup m v = c \<Longrightarrow> m \<le> r"
    unfolding p_def q_def r_def
    by auto
  have "p' + q' = p + q \<Longrightarrow>
        lookup (mapping_of P) p' \<noteq> 0 \<Longrightarrow>
        lookup (mapping_of Q) q' \<noteq> 0 \<Longrightarrow>
        p' = p \<and> q' = q" for p' q'
  proof -
    assume 6: "p' + q' = p + q"
    assume 7: "lookup (mapping_of P) p' \<noteq> 0" "lookup (mapping_of Q) q' \<noteq> 0"
    have 8: "lookup p' v \<le> lookup p v" "lookup q' v \<le> lookup q v"
      using 3 4 7 unfolding in_keys_iff by auto
    have "lookup p' v + lookup q' v = lookup p v + lookup q v"
      using 6
      by (metis lookup_add)
    hence "lookup p' v = lookup p v \<and> lookup q' v = lookup q v"
      using 8
      by linarith
    hence "p' \<le> p" "q' \<le> q"
      using 3 5 7 unfolding in_keys_iff by blast+
    thus "p' = p \<and> q' = q"
      using 6
      by (metis add.commute add_le_cancel_left antisym)
  qed
  hence 9: "(p + q = p' + q' \<and>
             lookup (mapping_of P) p' \<noteq> 0 \<and>
             lookup (mapping_of Q) q' \<noteq> 0) \<longleftrightarrow>
            (p', q') = (p, q)" for p' q'
    using 3 by auto
  have "lookup (mapping_of (P * Q)) (p + q) =
        (\<Sum>(p', q'). lookup (mapping_of P) p' * lookup (mapping_of Q) q' when p + q = p' + q')"
    unfolding times_mpoly.rep_eq times_poly_mapping.rep_eq
    by (rule prod_fun_unfold_prod; simp)
  also have "... = (\<Sum>(p', q'). lookup (mapping_of P) p' * lookup (mapping_of Q) q' 
              when p + q = p' + q' \<and> lookup (mapping_of P) p' \<noteq> 0 \<and> lookup (mapping_of Q) q' \<noteq> 0)"
    apply (rule Sum_any.cong)
    unfolding when_def apply auto
    done
  also have "... = Sum_any (\<lambda>a. (case a of (p', q') 
                    \<Rightarrow> lookup (mapping_of P) p' * lookup (mapping_of Q) q') when a = (p, q))"
    unfolding 9
    by (rule Sum_any.cong; auto)
  also have "... = lookup (mapping_of P) p * lookup (mapping_of Q) q"
    unfolding Sum_any_when_equal
    by auto
  also have "... \<noteq> 0"
    using 3 by auto
  finally have 10: "lookup (mapping_of (P * Q)) (p + q) \<noteq> 0" .
  have "a + b = lookup (p + q) v"
    using 3
    unfolding plus_poly_mapping.rep_eq by simp
  also have "... \<le> c"
    by (rule 4(3)[unfolded in_keys_iff]; rule 10)
  finally show "degree P v + degree Q v \<le> degree (P * Q) v"
    unfolding a_def b_def c_def degree.rep_eq
    using 1
    by simp
qed

lemma degree_pow: "degree (P ^ n) v \<le> n * degree P v"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have "degree (P ^ Suc n) v \<le> degree P v + degree (P ^ n) v"
    using degree_mult by auto
  also have "... \<le> degree P v + n * degree P v"
    using Suc by auto
  also have "... = Suc n * degree P v"
    by auto
  finally show ?case .
qed

lemma degree_pow_positive:
  fixes P :: "'a::idom mpoly"
  assumes "n > 0"
  shows "degree (P ^ n) v = n * degree P v"
proof (induction rule: nat_induct_non_zero[OF assms])
  show "degree (P ^ 1) v = 1 * degree P v" by simp
next
  fix m :: nat
  assume 0: "m > 0"
  assume 1: "degree (P ^ m) v = m * degree P v"
  show "degree (P ^ Suc m) v = Suc m * degree P v"
  proof cases
    assume 2: "P = 0"
    show ?thesis unfolding 2 by simp
  next
    assume 3: "P \<noteq> 0"
    show ?thesis
      unfolding power_Suc2
      apply (subst degree_mult_non_zero)
      subgoal using 0 3 pow_positive by blast
      subgoal using 3 .
      subgoal using 1 by simp
      done
  qed
qed

lemma degree_prod:
  assumes S_fin: "finite S"
  shows "degree (prod P S) v \<le> sum (\<lambda>i. degree (P i) v) S"
proof (induct rule:finite_induct[OF S_fin])
  case 1 show ?case by simp
next
  case (2 x S)
  have "degree (prod P (insert x S)) v = degree (prod P S * P x) v"
    by (simp add: "2.hyps" mult.commute)
  also have "... \<le> (degree (prod P S) v) + (degree (P x) v)"
    using degree_mult by auto
  also have "... \<le> (sum (\<lambda>i. degree (P i) v) S) + (degree (P x) v)"
    using "2.hyps" by auto
  also have "... = sum (\<lambda>i. degree (P i) v) (insert x S)"
    by (simp add: "2.hyps")
  finally show ?case .
qed


end
