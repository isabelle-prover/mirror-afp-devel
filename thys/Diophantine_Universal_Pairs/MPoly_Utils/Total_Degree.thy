theory Total_Degree
  imports Variables
begin

subsection \<open>Total degree\<close>

named_theorems total_degree_simps "Lemmas about the total_degree function"

lemma total_degree_Const [simp]: "total_degree (Const x) = 0"
  unfolding total_degree_def Const_def Const\<^sub>0_def
  by (simp add: MPoly_inverse)

lemma total_degree_Var [simp]:
  "total_degree ((Var v):: 'a::comm_semiring_1 mpoly) = 1"
  unfolding total_degree_def Var_def Var\<^sub>0_def
  by (simp add: MPoly_inverse lookup_single)

lemma total_degree_zero_degree_zero:
  assumes "total_degree P = 0"
  shows "degree P v = 0"
proof -
  have "insert 0 ((\<lambda>m. sum (lookup m) (keys m)) ` keys (mapping_of P)) \<subseteq> {0}"
    using assms unfolding total_degree.rep_eq
    by (metis (no_types, lifting) Max_ge finite_imageI finite_insert finite_keys le_zero_eq singleton_iff subsetI)
  hence "m \<in> keys (mapping_of P) \<Longrightarrow> sum (lookup m) (keys m) = 0" for m by blast
  hence "m \<in> keys (mapping_of P) \<Longrightarrow> (lookup m) v = 0" for m
    unfolding keys_def by simp
  thus ?thesis unfolding degree.rep_eq
    by (metis (no_types, lifting) Max_insert2 finite_imageI finite_keys imageE zero_order(2))
qed

lemma total_degree_zero:
  assumes "total_degree P = 0"
  shows "\<exists>c. P = Const c"
proof -
  have "vars P = {}"
    unfolding vars_non_zero_degree
    using total_degree_zero_degree_zero[OF assms]
    by simp
  thus ?thesis by (rule vars_empty)
qed

lemma total_degree_neg[total_degree_simps]:
  fixes P :: "'a::ab_group_add mpoly"
  shows "total_degree (- P) = total_degree P"
  unfolding total_degree.rep_eq uminus_mpoly.rep_eq keys.rep_eq
  by auto
  
lemma total_degree_add[total_degree_simps]:
  shows "total_degree (P + Q) \<le> max (total_degree P) (total_degree Q)"
proof -
  have "m \<in> keys (mapping_of (P + Q)) \<Longrightarrow>
        sum (lookup m) (keys m) \<le> max (total_degree P) (total_degree Q)" for m
  proof -
    assume "m \<in> keys (mapping_of (P + Q))"
    hence "m \<in> keys (mapping_of P + mapping_of Q)"
      by (simp add: plus_mpoly.rep_eq)
    hence in_union: "m \<in> keys (mapping_of P) \<union> keys (mapping_of Q)"
      by (meson Poly_Mapping.keys_add in_mono)
    have "m \<in> keys (mapping_of P) \<Longrightarrow> sum (lookup m) (keys m) \<le> total_degree P"
      unfolding total_degree.rep_eq by (rule Max_ge; auto)
    moreover have "m \<in> keys (mapping_of Q) \<Longrightarrow> sum (lookup m) (keys m) \<le> total_degree Q"
      unfolding total_degree.rep_eq by (rule Max_ge; auto)
    ultimately show "sum (lookup m) (keys m) \<le> max (total_degree P) (total_degree Q)"
      using in_union by force
  qed
  thus ?thesis unfolding total_degree.rep_eq by simp
qed

lemma total_degree_add_different_total_degree:
  fixes P :: "'a::ab_group_add mpoly"
  assumes "total_degree P \<noteq> total_degree Q"
  shows "total_degree (P + Q) = max (total_degree P) (total_degree Q)"

proof(cases "total_degree P > total_degree Q")
  case first:True
  hence P_notzero:"total_degree P > 0" by auto
  obtain m where m_prop1:"m \<in> keys (mapping_of P) \<and> Max ((\<lambda>l. sum (lookup l) (keys l)) ` keys (mapping_of P)) = sum (lookup m) (keys m)" 
    using P_notzero
    by (metis (mono_tags, lifting) MPoly_Type.total_degree_zero Max_in finite_imageI finite_keys imageE image_empty keys_zero not_less_zero total_degree.rep_eq zero_mpoly.rep_eq)
  hence m_prop2:"total_degree P = sum (lookup m) (keys m)"
    by (metis (no_types, lifting) Max.insert empty_iff finite_imageI finite_keys image_is_empty max_nat.left_neutral total_degree.rep_eq)

  have sum_pres_map:"mapping_of P + mapping_of Q = mapping_of (P+Q)" by (simp add: plus_mpoly.rep_eq)
  have "m \<notin> keys (mapping_of Q)" using m_prop2 first
    by (metis (no_types, lifting) Max.insert Max_ge empty_iff finite_imageI finite_keys image_eqI linorder_not_le max_nat.left_neutral total_degree.rep_eq)
  hence "m \<in> keys (mapping_of (P+Q))" using m_prop1 sum_pres_map
    by (metis (no_types, lifting) add.right_neutral in_keys_iff plus_poly_mapping.rep_eq)
  hence geq:"total_degree (P+Q) \<ge> total_degree P" using m_prop2 by (simp add: total_degree.rep_eq)

  have "total_degree (P+Q) \<le> max (total_degree P) (total_degree Q)" using total_degree_add by auto
  hence "total_degree (P+Q) = total_degree P" using first geq by auto
  thus ?thesis using first by auto

next
  case False
  hence second:"total_degree Q > total_degree P" using assms by auto
  hence Q_notzero:"total_degree Q > 0" by auto
  obtain n where n_prop1:"n \<in> keys (mapping_of Q) \<and> Max ((\<lambda>l. sum (lookup l) (keys l)) ` keys (mapping_of Q)) = sum (lookup n) (keys n)" 
    using Q_notzero
    by (metis (mono_tags, lifting) MPoly_Type.total_degree_zero Max_in finite_imageI finite_keys imageE image_empty keys_zero not_less_zero total_degree.rep_eq zero_mpoly.rep_eq)
  hence n_prop2:"total_degree Q = sum (lookup n) (keys n)"
    by (metis (no_types, lifting) Max.insert empty_iff finite_imageI finite_keys image_is_empty max_nat.left_neutral total_degree.rep_eq)

  have sum_pres_map:"mapping_of P + mapping_of Q = mapping_of (P+Q)" by (simp add: plus_mpoly.rep_eq)
  have "n \<notin> keys (mapping_of P)" using n_prop2 second
    by (metis (no_types, lifting) Max.insert Max_ge empty_iff finite_imageI finite_keys image_eqI linorder_not_le max_nat.left_neutral total_degree.rep_eq)
  hence "n \<in> keys (mapping_of (P+Q))" using n_prop1 sum_pres_map
    by (metis (no_types, lifting) add.commute add.right_neutral coeff_def coeff_keys plus_poly_mapping.rep_eq)
  hence geq:"total_degree (P+Q) \<ge> total_degree Q" using n_prop2 by (simp add: total_degree.rep_eq)

  have "total_degree (P+Q) \<le> max (total_degree P) (total_degree Q)" using total_degree_add by auto
  hence "total_degree (P+Q) = total_degree Q" using second geq by auto
  thus ?thesis using second by auto
qed

lemma total_degree_diff[total_degree_simps]: 
  fixes P :: "'a::ab_group_add mpoly"
  shows "total_degree (P - Q) \<le> max (total_degree P) (total_degree Q)"
  unfolding diff_conv_add_uminus[of P] total_degree_neg[of Q, symmetric]
  by (rule total_degree_add)

lemma total_degree_diff_different_total_degree:
  fixes P :: "'a::ab_group_add mpoly"
  assumes "total_degree P \<noteq> total_degree Q"
  shows "total_degree (P - Q) = max (total_degree P) (total_degree Q)"
  unfolding diff_conv_add_uminus[of P] total_degree_neg[of Q, symmetric]
  apply (rule total_degree_add_different_total_degree)
  unfolding total_degree_neg apply (rule assms)
  done

lemma total_degree_mult[total_degree_simps]:
  "total_degree (P * Q) \<le> total_degree P + total_degree Q"
proof -
  have "m \<in> keys (mapping_of (P * Q)) \<Longrightarrow>
        sum (lookup m) (keys m) \<le> total_degree P + total_degree Q" for m
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
    have a_bound: "sum (lookup a) (keys a) \<le> total_degree P"
      unfolding total_degree.rep_eq
      apply (rule Max_ge)
      subgoal by simp
      subgoal using a_key by auto
      done
    have b_bound: "sum (lookup b) (keys b) \<le> total_degree Q"
      unfolding total_degree.rep_eq
      apply (rule Max_ge)
      subgoal by simp
      subgoal using b_key by auto
      done
    have "sum (lookup m) (keys m) = sum (lookup a) (keys a) + sum (lookup b) (keys b)"
      unfolding m_def
      by (rule setsum_keys_plus_distrib; auto)
    thus "sum (lookup m) (keys m) \<le> total_degree P + total_degree Q"
      using a_bound b_bound by simp
  qed
  thus ?thesis unfolding total_degree.rep_eq by simp
qed

lemma total_degree_mult_non_zero:
  fixes P Q :: "'a::idom mpoly"
  assumes "P \<noteq> 0" "Q \<noteq> 0"
  shows "total_degree (P * Q) = total_degree P + total_degree Q"
proof (rule antisym)
  show "total_degree (P * Q) \<le> total_degree P + total_degree Q" by (rule total_degree_mult)
next
  define a where "a = Max ((\<lambda>m. sum (lookup m) (keys m)) ` keys (mapping_of P))"
  define b where "b = Max ((\<lambda>m. sum (lookup m) (keys m)) ` keys (mapping_of Q))"
  define c where "c = Max ((\<lambda>m. sum (lookup m) (keys m)) ` keys (mapping_of (P * Q)))"
  define p where "p = Max {m \<in> keys (mapping_of P). sum (lookup m) (keys m) = a}"
  define q where "q = Max {m \<in> keys (mapping_of Q). sum (lookup m) (keys m) = b}"
  define r where "r = Max {m \<in> keys (mapping_of (P * Q)). sum (lookup m) (keys m) = c}"
  have 0: "P * Q \<noteq> 0" using assms by auto
  have 1: "keys (mapping_of P) \<noteq> {}"
          "keys (mapping_of Q) \<noteq> {}"
          "keys (mapping_of (P * Q)) \<noteq> {}"
    using assms 0 mapping_of_inject zero_mpoly.rep_eq
    apply fastforce
    apply (metis assms(2) keys_eq_empty mapping_of_inverse zero_mpoly.abs_eq)
    by (metis "0" keys_eq_empty mapping_of_inverse zero_mpoly.abs_eq)
  have 2: "a \<in> (\<lambda>m. sum (lookup m) (keys m)) ` keys (mapping_of P)"
          "b \<in> (\<lambda>m. sum (lookup m) (keys m)) ` keys (mapping_of Q)"
          "c \<in> (\<lambda>m. sum (lookup m) (keys m)) ` keys (mapping_of (P * Q))"
    unfolding a_def b_def c_def
    using 1 Max_in
    by simp+
  have 3: "p \<in> {m \<in> keys (mapping_of P). sum (lookup m) (keys m) = a}"
          "q \<in> {m \<in> keys (mapping_of Q). sum (lookup m) (keys m) = b}"
          "r \<in> {m \<in> keys (mapping_of (P * Q)). sum (lookup m) (keys m) = c}"
    unfolding p_def q_def r_def
    using 2 Max_in[of "{m \<in> keys (mapping_of _). sum (lookup m) (keys m) = _}"]
    by auto
  have 4: "\<And>m. m \<in> keys (mapping_of P) \<Longrightarrow> sum (lookup m) (keys m) \<le> a"
          "\<And>m. m \<in> keys (mapping_of Q) \<Longrightarrow> sum (lookup m) (keys m) \<le> b"
          "\<And>m. m \<in> keys (mapping_of (P * Q)) \<Longrightarrow> sum (lookup m) (keys m) \<le> c"
    unfolding a_def b_def c_def
    by auto
  have 5: "\<And>m. m \<in> keys (mapping_of P) \<Longrightarrow> sum (lookup m) (keys m) = a \<Longrightarrow> m \<le> p"
          "\<And>m. m \<in> keys (mapping_of Q) \<Longrightarrow> sum (lookup m) (keys m) = b \<Longrightarrow> m \<le> q"
          "\<And>m. m \<in> keys (mapping_of (P * Q)) \<Longrightarrow> sum (lookup m) (keys m) = c \<Longrightarrow> m \<le> r"
    unfolding p_def q_def r_def
    by auto
  have "p' + q' = p + q \<Longrightarrow>
        lookup (mapping_of P) p' \<noteq> 0 \<Longrightarrow>
        lookup (mapping_of Q) q' \<noteq> 0 \<Longrightarrow>
        p' = p \<and> q' = q" for p' q'
  proof -
    assume 6: "p' + q' = p + q"
    assume 7: "lookup (mapping_of P) p' \<noteq> 0" "lookup (mapping_of Q) q' \<noteq> 0"
    have 8: "sum (lookup p') (keys p') \<le> sum (lookup p) (keys p)" "sum (lookup q') (keys q') \<le> sum (lookup q) (keys q)"
      using 3 4 7 unfolding in_keys_iff by auto
    have "sum (lookup p') (keys p') + sum (lookup q') (keys q') = sum (lookup p) (keys p) + sum (lookup q) (keys q)"
      using 6 setsum_keys_plus_distrib[of "\<lambda>_ x. x" p q] setsum_keys_plus_distrib[of "\<lambda>_ x. x" p' q']
      by auto
    hence "sum (lookup p') (keys p') = sum (lookup p) (keys p) \<and> sum (lookup q') (keys q') = sum (lookup q) (keys q)"
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
  also have "... = (\<Sum>(p', q'). lookup (mapping_of P) p' * lookup (mapping_of Q) q' when p + q = p' + q' \<and> lookup (mapping_of P) p' \<noteq> 0 \<and> lookup (mapping_of Q) q' \<noteq> 0)"
    apply (rule Sum_any.cong)
    unfolding when_def apply auto
    done
  also have "... = Sum_any (\<lambda>a. (case a of (p', q') \<Rightarrow> lookup (mapping_of P) p' * lookup (mapping_of Q) q') when a = (p, q))"
    unfolding 9
    by (rule Sum_any.cong; auto)
  also have "... = lookup (mapping_of P) p * lookup (mapping_of Q) q"
    unfolding Sum_any_when_equal
    by auto
  also have "... \<noteq> 0"
    using 3 by auto
  finally have 10: "lookup (mapping_of (P * Q)) (p + q) \<noteq> 0" .
  have "a + b = sum (lookup (p + q)) (keys (p + q))"
    using 3 setsum_keys_plus_distrib[of "\<lambda>_ x. x" p q]
    by simp
  also have "... \<le> c"
    by (rule 4(3)[unfolded in_keys_iff]; rule 10)
  finally show "total_degree P + total_degree Q \<le> total_degree (P * Q)"
    unfolding a_def b_def c_def total_degree.rep_eq
    using 1
    by simp
qed

lemma total_degree_pow: "total_degree (P ^ n) \<le> n * total_degree P"
  apply (induction n, auto simp: degree_mult)
  by (meson nat_add_left_cancel_le order_trans total_degree_mult)

lemma total_degree_pow_positive[total_degree_simps]:
  fixes P :: "'a::idom mpoly"
  assumes "n > 0"
  shows "total_degree (P ^ n) = n * total_degree P"
proof (induction rule: nat_induct_non_zero[OF assms])
  show "total_degree (P ^ 1) = 1 * total_degree P" by simp
next
  fix m :: nat
  assume 0: "m > 0"
  assume 1: "total_degree (P ^ m) = m * total_degree P"
  show "total_degree (P ^ Suc m) = Suc m * total_degree P"
  proof cases
    assume 2: "P = 0"
    show ?thesis unfolding 2 by simp
  next
    assume 3: "P \<noteq> 0"
    show ?thesis
      unfolding power_Suc2
      apply (subst total_degree_mult_non_zero)
      subgoal using 0 3 pow_positive by blast
      subgoal using 3 .
      subgoal using 1 by simp
      done
  qed
qed

lemma total_degree_sum:
  fixes P :: "'a \<Rightarrow> 'b::comm_monoid_add mpoly"
  assumes S_fin: "finite S"
  shows "total_degree (sum P S) \<le> Max (insert 0 ((\<lambda>i. total_degree (P i)) ` S))"
  apply (induct rule: finite_induct[OF S_fin], auto)
  apply (rule le_trans[OF total_degree_add], simp)
  by (smt (verit) Max_insert bot_nat_def finite.insertI finite_imageI insert_absorb2 le_trans
          insert_not_empty le_cases3 le_max_iff_disj max_bot2 insert_commute)

lemma total_degree_prod:
  assumes S_fin: "finite S"
  shows "total_degree (prod P S) \<le> sum (\<lambda>i. total_degree (P i)) S"
  apply (induct rule: finite_induct[OF S_fin], auto)
  by (rule le_trans[OF total_degree_mult]) simp

lemma Max_function_mono:
  fixes f g :: "'a \<Rightarrow> nat"
  assumes "finite A"
  assumes "A \<noteq> {}"
  assumes "\<forall>a\<in>A. f a \<le> g a"
  shows "Max (f ` A) \<le> Max (g ` A)"
  apply (subst Max.boundedI, auto simp: assms)
  by (rule le_trans[of "f _" "g _", OF _ Max_ge], auto simp: assms)

lemma degree_total_degree_bound:
  "degree P v \<le> total_degree P"
proof (cases "v \<in> vars P")
  case True
  have "m \<in> keys (mapping_of P) \<Longrightarrow> lookup m v \<le> sum (lookup m) (keys m)" for m
    apply (cases "v \<in> keys m")
    apply (subst member_le_sum, auto)
    using lookup_not_eq_zero_eq_in_keys by fastforce
  hence "Max ((\<lambda>m. lookup m v) ` keys (mapping_of P))
         \<le> Max ((\<lambda>m. sum (lookup m) (keys m)) ` keys (mapping_of P))"
    using True[unfolded vars_def] by (subst Max_function_mono, auto)
  then show ?thesis
    using True[unfolded vars_def]
    unfolding total_degree.rep_eq degree.rep_eq
    by (smt (verit, ccfv_threshold) Max_ge Max_in dual_order.trans empty_not_insert finite_imageI
            finite_insert finite_keys image_is_empty insert_iff)
next
  case False
  then show ?thesis
    by (simp add: in_vars_non_zero_degree)
qed

lemma total_degree_bound:
  "total_degree P \<le> sum (degree P) (vars P)"
  unfolding total_degree.rep_eq degree.rep_eq
  apply (subst Max.boundedI, auto simp: vars_def)
  by (subst sum_le_included[of _ _ _ "\<lambda>x. x"], auto)

end