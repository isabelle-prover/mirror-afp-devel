subsection \<open>Binary masking is Diophantine\<close>

theory Binary_Masking
  imports Binary_Orthogonal
begin

lemma lm0243_masks_binom_equiv: "(b \<preceq> c) \<longleftrightarrow> odd (c choose b)" (is "?P \<longleftrightarrow> ?Q")
proof-
  consider (lt) "b < c" | (eq) "b = c" | (gt) "b > c" using nat_neq_iff by blast
  then show ?thesis
  proof(cases)
    case lt
    hence "\<exists>a. c = a + b" using less_imp_add_positive semiring_normalization_rules(24) by blast
    then obtain a where a_def:"c = a + b" ..
    have "a \<bottom> b \<longleftrightarrow> b \<preceq> a + b" (is "?P \<longleftrightarrow> ?Q")
    proof
      assume ?P
      then show ?Q
        using ortho_mult_equiv no_carry_mult_equiv masks_leq_equiv[of b "a+b"]
              sum_digit_formula nth_bit_bounded
        by auto (metis add.commute add.right_neutral lessI less_one mod_less
                        nat_less_le one_add_one plus_1_eq_Suc zero_le)
    next
      assume ?Q
      have "?Q \<Longrightarrow> \<forall>k. a \<exclamdown> k + b \<exclamdown> k \<le> 1"
      proof(rule ccontr)
        assume "\<not>(\<forall>k. a \<exclamdown> k + b \<exclamdown> k \<le> 1) "
        then obtain k where k1:"\<not>(a \<exclamdown> k + b \<exclamdown> k \<le> 1)" and k2:"\<forall>r<k. a \<exclamdown> r + b \<exclamdown> r \<le> 1"
          by (auto dest: obtain_smallest)
        have c1: "bin_carry a b k = 1"
          using `?Q` masks_leq_equiv sum_digit_formula carry_bounded nth_bit_bounded k1
          by (metis add.commute add.left_neutral add_self_mod_2 less_one nat_less_le not_le)
        then show False using carry_digit_impl[of a b k] k2 by auto
      qed
      then show ?P
        using `?Q` ortho_mult_equiv no_carry_mult_equiv masks_leq_equiv[of b "a+b"]
              sum_digit_formula nth_bit_bounded
        by auto (metis add_le_same_cancel2 le_0_eq le_SucE)
    qed
    then show ?thesis using lm0241_ortho_binom_equiv a_def by auto
  next
    case eq
    hence "odd (c choose b)" by simp
    moreover have "b \<preceq> c" using digit_wise_equiv masks_leq_equiv eq by blast
    ultimately show ?thesis by simp
  next
    case gt
    hence "\<not> odd (c choose b)" by (simp add: binomial_eq_0)
    moreover have "\<not> (b \<preceq> c)" using masks_leq_equiv masks_leq gt not_le by blast
    ultimately show ?thesis by simp
  qed
qed

definition masking ("_ [\<preceq>] _" 60)
  where "P [\<preceq>] Q \<equiv> (BINARY (\<lambda>a b. a \<preceq> b) P Q)"

lemma masking_dioph[dioph]:
  fixes P Q
  defines "DR \<equiv> (P [\<preceq>] Q)"
  shows "is_dioph_rel DR"
proof -
  define P' Q' where pushed_def: "P' \<equiv> push_param P 1" "Q' \<equiv> push_param Q 1"

  define DS where "DS \<equiv> [\<exists>] [Param 0 = Q' choose P'] [\<and>] ODD Param 0"

  have "eval DS a = eval DR a" for a
    unfolding DS_def DR_def defs pushed_def masking_def
    using push_push1 by (simp add: push0 lm0243_masks_binom_equiv)

  moreover have "is_dioph_rel DS"
    unfolding DS_def by (simp add: dioph)

  ultimately show ?thesis
    by (auto simp: is_dioph_rel_def)
qed

declare masking_def[defs]

end