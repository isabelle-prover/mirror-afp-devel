theory Schoenhage_Strassen_Ring_Lemmas
  imports "HOL-Algebra.Ring" "HOL-Algebra.Multiplicative_Group"
begin

context cring
begin

lemma diff_diff:
  assumes "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
  shows "a \<ominus> (b \<ominus> c) = a \<ominus> b \<oplus> c"
  using assms by algebra
lemma minus_eq_mult_one:
  assumes "a \<in> carrier R"
  shows "\<ominus> a = (\<ominus> \<one>) \<otimes> a"
  using assms by algebra
lemma diff_eq_add_mult_one:
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "a \<ominus> b = a \<oplus> (\<ominus> \<one>) \<otimes> b"
  using assms by algebra
lemma minus_cancel:
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "a \<ominus> b \<oplus> b = a"
  using assms by algebra
lemma assoc4:
  assumes "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R" "d \<in> carrier R"
  shows "a \<otimes> (b \<otimes> (c \<otimes> d)) = a \<otimes> b \<otimes> c \<otimes> d"
  using assms by algebra
lemma diff_sum:
  assumes "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R" "d \<in> carrier R"
  shows "(a \<ominus> c) \<oplus> (b \<ominus> d) = (a \<oplus> b) \<ominus> (c \<oplus> d)"
  using assms by algebra

end

lemma (in ring) inv_cancel_left:
  assumes "x \<in> carrier R"
  assumes "y \<in> carrier R"
  assumes "z \<in> Units R"
  assumes "x = z \<otimes> y"
  shows "inv z \<otimes> x = y"
  using assms
  by (metis Units_closed Units_inv_closed Units_l_inv l_one m_assoc)

lemma (in ring) r_distr_diff:
  assumes "x \<in> carrier R"
  assumes "y \<in> carrier R"
  assumes "z \<in> carrier R"
  shows "x \<otimes> (y \<ominus> z) = x \<otimes> y \<ominus> x \<otimes> z"
  using assms by algebra

lemma (in group)
  assumes "x \<in> carrier G"
  shows "\<And>i. i \<in> {1..<ord x} \<Longrightarrow> x [^] i \<noteq> \<one>"
  using assms using pow_eq_id by auto

subsection "Multiplicative Subgroups"
locale multiplicative_subgroup = cring +
  fixes X
  fixes M
  assumes Units_subset: "X \<subseteq> Units R"
  assumes M_def: "M = \<lparr> carrier = X, monoid.mult = (\<otimes>), one = \<one> \<rparr>"
  assumes M_group: "group M"
begin

lemma carrier_M[simp]: "carrier M = X" using M_def by auto

lemma one_eq: "\<one>\<^bsub>M\<^esub> = \<one>" using M_def by simp

lemma mult_eq: "a \<otimes>\<^bsub>M\<^esub> b = a \<otimes> b" using M_def by simp

lemma inv_eq:
  assumes "x \<in> X"
  shows "inv\<^bsub>M\<^esub> x = inv x"
proof (intro comm_inv_char[symmetric])
  show "x \<in> carrier R" using assms Units_subset by blast
  from assms have "inv\<^bsub>M\<^esub> x \<in> X" using group.inv_closed[OF M_group] by simp
  then show "inv\<^bsub>M\<^esub> x \<in> carrier R" using Units_subset by blast
  have "x \<otimes>\<^bsub>M\<^esub> inv\<^bsub>M\<^esub> x = \<one>\<^bsub>M\<^esub>"
    using group.Units_eq[OF M_group] monoid.Units_r_inv[OF group.is_monoid[OF M_group]]
    using assms by simp
  then show "x \<otimes> inv\<^bsub>M\<^esub> x = \<one>" using M_def by simp
qed

lemma nat_pow_eq: "x [^]\<^bsub>M\<^esub> (m :: nat) = x [^] m"
  by (induction m) (simp_all add: M_def)

lemma int_pow_eq:
  assumes "x \<in> X"
  shows "x [^]\<^bsub>M\<^esub> (i :: int) = x [^] i"
proof (cases "i \<ge> 0")
  case True
  then have "x [^]\<^bsub>M\<^esub> i = x [^]\<^bsub>M\<^esub> (nat i)"
    by simp
  also have "... = x [^] (nat i)"
    using nat_pow_eq by simp
  also have "... = x [^] i"
    using True by simp
  finally show ?thesis .
next
  case False
  then have "x [^]\<^bsub>M\<^esub> i = inv\<^bsub>M\<^esub> (x [^]\<^bsub>M\<^esub> (nat (- i)))"
    using int_pow_def2[of M] by presburger
  also have "... = inv (x [^]\<^bsub>M\<^esub> (nat (- i)))"
    apply (intro inv_eq)
    using monoid.nat_pow_closed[OF group.is_monoid[OF M_group]] assms by simp
  also have "... = inv (x [^] (nat (- i)))"
    by (simp add: nat_pow_eq)
  also have "... = x [^] i"
    using int_pow_def2 False by (metis leI)
  finally show ?thesis .
qed

end

context cring
begin

interpretation units_group: group "units_of R"
  by (rule units_group)

lemma units_subgroup: "multiplicative_subgroup R (Units R) (units_of R)"
  apply unfold_locales unfolding units_of_def by simp_all

interpretation units_subgroup: multiplicative_subgroup R "Units R" "units_of R"
  by (rule units_subgroup)

lemma inv_nat_pow:
  assumes "a \<in> Units R"
  shows "inv (a [^] (b :: nat)) = inv a [^] b"
proof -
  have "inv (a [^] b) = inv\<^bsub>units_of R\<^esub> (a [^]\<^bsub>units_of R\<^esub> b)"
    using assms units_subgroup.nat_pow_eq units_subgroup.inv_eq Units_pow_closed by simp
  also have "... = inv\<^bsub>units_of R\<^esub> a [^]\<^bsub>units_of R\<^esub> b"
    apply (intro group.nat_pow_inv[OF units_group, symmetric])
    using assms units_subgroup.carrier_M by argo
  also have "... = inv a [^] b"
    using assms units_subgroup.nat_pow_eq units_subgroup.inv_eq by simp
  finally show ?thesis .
qed
lemma int_pow_mult:
  fixes m1 m2 :: int
  assumes "x \<in> Units R"
  shows "x [^] m1 \<otimes> x [^] m2 = x [^] (m1 + m2)"
  using units_group.int_pow_mult[of x]
  unfolding units_subgroup.carrier_M
  using assms units_subgroup.int_pow_eq[OF assms]
  by (simp add: units_subgroup.mult_eq)
lemma int_pow_pow:
  fixes m1 m2 :: int
  assumes "x \<in> Units R"
  shows "(x [^] m1) [^] m2 = x [^] (m1 * m2)"
  using units_group.int_pow_pow[of x] assms
  unfolding units_subgroup.carrier_M
  using units_group.int_pow_closed units_subgroup.int_pow_eq by auto
lemma int_pow_one:
  "\<one> [^] (i :: int) = \<one>"
  using units_group.int_pow_one[of i]
  using units_subgroup.int_pow_eq[OF Units_one_closed] units_subgroup.one_eq by simp
lemma int_pow_closed:
  assumes "x \<in> Units R"
  shows "x [^] (i :: int) \<in> Units R"
  using units_group.int_pow_closed units_subgroup.carrier_M assms units_subgroup.int_pow_eq
  by simp

lemma units_of_int_pow: "\<mu> \<in> Units R \<Longrightarrow> \<mu> [^]\<^bsub>(units_of R)\<^esub> i = \<mu> [^] (i :: int)"
  using units_of_pow[of \<mu>]
  apply (simp add: int_pow_def)
  by (metis Units_pow_closed nat_pow_def units_of_inv)

lemma units_int_pow_neg: "\<mu> \<in> Units R \<Longrightarrow> (inv \<mu>) [^] (n :: int) = \<mu> [^] (- n)"
  by (metis Units_inv_Units units_of_int_pow units_group.int_pow_inv units_group.int_pow_neg units_of_carrier units_of_inv)

lemma units_inv_int_pow: "\<mu> \<in> Units R \<Longrightarrow> inv \<mu> = \<mu> [^] (- (1 :: int))"
  using units_int_pow_neg[of \<mu> "1 :: int"]
  by (simp add: int_pow_def2)

lemma inv_prod: "\<mu> \<in> Units R \<Longrightarrow> \<nu> \<in> Units R \<Longrightarrow> inv (\<mu> \<otimes> \<nu>) = inv \<nu> \<otimes> inv \<mu>"
  by (metis Units_m_closed group.inv_mult_group units_group units_of_carrier units_of_inv units_of_mult)

lemma powers_of_negative:
  fixes r :: nat
  assumes "x \<in> carrier R"
  shows "even r \<Longrightarrow> (\<ominus> x) [^] r = x [^] r" "odd r \<Longrightarrow> (\<ominus> x) [^] r = \<ominus> (x [^] r)"
   using assms by (induction r) (simp_all add: l_minus r_minus)

end

subsection "Additive Subgroups"

locale additive_subgroup = cring + 
  fixes X
  fixes M
  assumes Units_subset: "X \<subseteq> carrier R"
  assumes M_def: "M = \<lparr> carrier = X, monoid.mult = (\<oplus>), one = \<zero> \<rparr>"
  assumes M_group: "group M"
begin

lemma carrier_M[simp]: "carrier M = X"
  unfolding M_def by simp

lemma one_eq: "\<one>\<^bsub>M\<^esub> = \<zero>" unfolding M_def by simp

lemma mult_eq: "a \<otimes>\<^bsub>M\<^esub> b = a \<oplus> b"
  unfolding M_def by simp

lemma inv_eq:
  assumes "a \<in> X"
  shows "inv\<^bsub>M\<^esub> a = \<ominus> a"
  apply (intro sum_zero_eq_neg set_mp[OF Units_subset] assms)
  subgoal using group.inv_closed[OF M_group] assms unfolding carrier_M by simp
  subgoal
    unfolding mult_eq[symmetric] one_eq[symmetric]
    apply (intro group.l_inv M_group)
    unfolding carrier_M using assms .
  done

end

end