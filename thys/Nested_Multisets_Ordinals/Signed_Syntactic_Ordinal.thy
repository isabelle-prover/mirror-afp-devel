(*  Title:       Signed Syntactic Ordinals in Cantor Normal Form
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Author:      Mathias Fleury <mfleury at mpi-inf.mpg.de>, 2016
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>Signed Syntactic Ordinals in Cantor Normal Form\<close>

theory Signed_Syntactic_Ordinal
imports Signed_Hereditary_Multiset "$AFP/Nested_Multisets_Ordinals/Syntactic_Ordinal"
begin


subsection \<open>Embedding and Projections of Syntactic Ordinals\<close>

abbreviation zhmset_of_hmset :: "hmultiset \<Rightarrow> yhmultiset" where
  "zhmset_of_hmset M \<equiv> ZHMSet (zmset_of_mset (hmsetmset M))"

lemma zhmset_of_hmset_inject[simp]: "zhmset_of_hmset M = zhmset_of_hmset N \<longleftrightarrow> M = N"
  by simp

lemma zhmset_of_hmset_less: "zhmset_of_hmset M < zhmset_of_hmset N \<longleftrightarrow> M < N"
  by (simp add: zmset_of_mset_less)

lemma zhmset_of_hmset_le: "zhmset_of_hmset M \<le> zhmset_of_hmset N \<longleftrightarrow> M \<le> N"
  by (simp add: zmset_of_mset_le)

abbreviation hmset_pos :: "yhmultiset \<Rightarrow> hmultiset" where
  "hmset_pos M \<equiv> HMSet (mset_pos (zhmsetmset M))"

abbreviation hmset_neg :: "yhmultiset \<Rightarrow> hmultiset" where
  "hmset_neg M \<equiv> HMSet (mset_neg (zhmsetmset M))"


subsection \<open>Natural (Hessenberg) Sum and Difference\<close>

instantiation yhmultiset :: cancel_comm_monoid_add
begin

lift_definition zero_yhmultiset :: yhmultiset is "{#}\<^sub>z" .

lift_definition plus_yhmultiset :: "yhmultiset \<Rightarrow> yhmultiset \<Rightarrow> yhmultiset" is
  "\<lambda>A B. A + B" .

lift_definition minus_yhmultiset :: "yhmultiset \<Rightarrow> yhmultiset \<Rightarrow> yhmultiset" is
  "\<lambda>A B. A - B" .

lemmas ZHMSet_plus = plus_yhmultiset.abs_eq[symmetric]
lemmas ZHMSet_diff = minus_yhmultiset.abs_eq[symmetric]
lemmas zhmsetmset_plus = plus_yhmultiset.rep_eq
lemmas zhmsetmset_diff = minus_yhmultiset.rep_eq

lemma zhmset_of_hmset_plus: "zhmset_of_hmset (A + B) = zhmset_of_hmset A + zhmset_of_hmset B"
  by (simp add: hmsetmset_plus ZHMSet_plus zmset_of_mset_plus)

lemma hmsetmset_0[simp]: "hmsetmset 0 = {#}"
  by (rule hmultiset.inject[THEN iffD1]) (simp add: zero_hmultiset_def)

instance
  by (standard; transfer) (auto intro: linordered_field_class.sign_simps(1) add.commute)

end

lemma hmset_pos_plus:
  "hmset_pos (A + B) = (hmset_pos A - hmset_neg B) + (hmset_pos B - hmset_neg A)"
  by (simp add: HMSet_diff HMSet_plus zhmsetmset_plus)

lemma hmset_neg_plus:
  "hmset_neg (A + B) = (hmset_neg A - hmset_pos B) + (hmset_neg B - hmset_pos A)"
  by (simp add: HMSet_diff HMSet_plus zhmsetmset_plus)

lemma zhmset_pos_neg_partition: "M = zhmset_of_hmset (hmset_pos M) - zhmset_of_hmset (hmset_neg M)"
  by (cases M, simp add: ZHMSet_diff[symmetric], rule mset_pos_neg_partition)

lemma zhmset_pos_as_neg: "zhmset_of_hmset (hmset_pos M) = zhmset_of_hmset (hmset_neg M) + M"
  using mset_pos_as_neg zhmsetmset_plus zhmsetmset_inject by fastforce

lemma zhmset_neg_as_pos: "zhmset_of_hmset (hmset_neg M) = zhmset_of_hmset (hmset_pos M) - M"
  using zhmsetmset_diff mset_neg_as_pos zhmsetmset_inject by fastforce

lemma hmset_pos_neg_dual:
  "hmset_pos a + hmset_pos b + (hmset_neg a - hmset_pos b) + (hmset_neg b - hmset_pos a) =
   hmset_neg a + hmset_neg b + (hmset_pos a - hmset_neg b) + (hmset_pos b - hmset_neg a)"
  by (simp add: HMSet_plus[symmetric] HMSet_diff[symmetric]) (rule mset_pos_neg_dual)

lemma zhmset_of_hmset_sum_list: "zhmset_of_hmset (sum_list Ms) = sum_list (map zhmset_of_hmset Ms)"
  by (induct Ms) (auto simp: zero_yhmultiset_def zhmset_of_hmset_plus)


instantiation yhmultiset :: ab_group_add
begin

lift_definition uminus_yhmultiset :: "yhmultiset \<Rightarrow> yhmultiset" is "\<lambda>A. - A" .

lemmas ZHMSet_uminus = uminus_yhmultiset.abs_eq[symmetric]
lemmas zhmsetmset_uminus = uminus_yhmultiset.rep_eq

instance
  by (standard; transfer; simp)

end


subsection \<open>Natural (Hessenberg) Product\<close>

instantiation yhmultiset :: one
begin

lift_definition one_yhmultiset :: yhmultiset is "{#0#}\<^sub>z" .

instance
  by standard

end

lemma zhmset_of_hmset_0: "zhmset_of_hmset 0 = 0"
  by (simp add: zero_yhmultiset_def)

lemma zhmset_of_hmset_1: "zhmset_of_hmset 1 = 1"
  by (simp add: one_hmultiset_def one_yhmultiset_def)

lemma mult_assoc_zhmset_aux:
  "An * (Bn * Cn + Bp * Cp - (Bn * Cp + Cn * Bp)) +
    (Cn * (An * Bp + Bn * Ap - (An * Bn + Ap * Bp)) +
     (Ap * (Bn * Cp + Cn * Bp - (Bn * Cn + Bp * Cp)) +
      Cp * (An * Bn + Ap * Bp - (An * Bp + Bn * Ap)))) =
    An * (Bn * Cp + Cn * Bp - (Bn * Cn + Bp * Cp)) +
    (Cn * (An * Bn + Ap * Bp - (An * Bp + Bn * Ap)) +
     (Ap * (Bn * Cn + Bp * Cp - (Bn * Cp + Cn * Bp)) +
      Cp * (An * Bp + Bn * Ap - (An * Bn + Ap * Bp))))"
  for Ap An Bp Bn Cp Cn Dp Dn :: hmultiset
  apply (simp add: algebra_simps)
  apply (unfold add.assoc[symmetric])

  apply (rule add_right_cancel[THEN iffD1, of _ "Cp * (An * Bp + Ap * Bn)"])
  apply (unfold add.assoc)
  apply (subst times_diff_plus_sym_hmset)
  apply (unfold add.assoc[symmetric])
  apply (subst (12) add.commute)
  apply (subst (11) add.commute)
  apply (unfold add.assoc[symmetric])

  apply (rule add_right_cancel[THEN iffD1, of _ "Cn * (An * Bn + Ap * Bp)"])
  apply (unfold add.assoc)
  apply (subst times_diff_plus_sym_hmset)
  apply (unfold add.assoc[symmetric])
  apply (subst (14) add.commute)
  apply (subst (13) add.commute)
  apply (unfold add.assoc[symmetric])

  apply (rule add_right_cancel[THEN iffD1, of _ "Ap * (Bn * Cn + Bp * Cp)"])
  apply (unfold add.assoc)
  apply (subst times_diff_plus_sym_hmset)
  apply (unfold add.assoc[symmetric])
  apply (subst (16) add.commute)
  apply (subst (15) add.commute)
  apply (unfold add.assoc[symmetric])

  apply (rule add_right_cancel[THEN iffD1, of _ "An * (Bn * Cp + Bp * Cn)"])
  apply (unfold add.assoc)
  apply (subst times_diff_plus_sym_hmset)
  apply (unfold add.assoc[symmetric])
  apply (subst (18) add.commute)
  apply (subst (17) add.commute)
  apply (unfold add.assoc[symmetric])

  by (simp add: algebra_simps)

instantiation yhmultiset :: comm_ring_1
begin

lift_definition times_yhmultiset :: "yhmultiset \<Rightarrow> yhmultiset \<Rightarrow> yhmultiset" is
  "\<lambda>M N.
       zmset_of_mset (hmsetmset (HMSet (mset_pos M) * HMSet (mset_pos N)))
     - zmset_of_mset (hmsetmset (HMSet (mset_pos M) * HMSet (mset_neg N)))
     + zmset_of_mset (hmsetmset (HMSet (mset_neg M) * HMSet (mset_neg N)))
     - zmset_of_mset (hmsetmset (HMSet (mset_neg M) * HMSet (mset_pos N)))" .

lemmas zhmsetmset_times = times_yhmultiset.rep_eq

instance
proof (standard, goal_cases mult_assoc mult_comm mult_1 distrib zero_neq_one)
  case (mult_assoc a b c)
  show ?case
    apply transfer
    apply (auto simp: algebra_simps)
    apply (simp add: zmset_of_mset_plus[symmetric] hmsetmset_plus[symmetric] HMSet_diff)
    by (rule mult_assoc_zhmset_aux)
next
  case (mult_comm a b)
  show ?case
    by transfer (auto simp: algebra_simps)
next
  case (mult_1 a)
  show ?case
    by transfer (auto simp: algebra_simps mset_pos_neg_partition[symmetric])
next
  case (distrib a b c)

  show ?case
    apply (unfold times_yhmultiset_def)
    apply (simp add: ZHMSet_plus[symmetric])
    apply (simp add: algebra_simps)
    apply (simp add: zmset_of_mset_plus[symmetric] hmsetmset_plus[symmetric])
    apply (simp add: add.assoc[symmetric])

    apply (unfold hmset_pos_plus hmset_neg_plus)
    apply (simp add: algebra_simps)

    apply (simp add: mult.commute[of _ "hmset_pos c"] mult.commute[of _ "hmset_neg c"])
    apply (simp add:
        add.commute[of "hmset_neg c * M" "hmset_pos c * N" for M N]
        add.left_commute[of "hmset_neg c * M" "hmset_pos c * N" for M N])
    apply (unfold ring_distribs(1)[symmetric])
    apply (simp add: add.assoc[symmetric])
    apply (unfold ring_distribs(1)[symmetric])
    apply (unfold hmset_pos_neg_dual)
    apply (rule refl)
    done
next
  case zero_neq_one
  show ?case
    unfolding zero_yhmultiset_def one_yhmultiset_def by simp
qed

end

lemma zhmset_of_hmset_times: "zhmset_of_hmset (A * B) = zhmset_of_hmset A * zhmset_of_hmset B"
  by transfer simp

lemma zhmset_of_hmset_prod_list:
  "zhmset_of_hmset (prod_list Ms) = prod_list (map zhmset_of_hmset Ms)"
  by (induct Ms) (auto simp: one_hmultiset_def one_yhmultiset_def zhmset_of_hmset_times)


subsection \<open>Omega\<close>

definition \<omega>\<^sub>z :: yhmultiset where
  "\<omega>\<^sub>z = ZHMSet {#1#}\<^sub>z"

lemma \<omega>\<^sub>z_as_\<omega>: "\<omega>\<^sub>z = zhmset_of_hmset \<omega>"
  unfolding \<omega>\<^sub>z_def \<omega>_def by simp


subsection \<open>Embedding of Natural Numbers\<close>

lemma of_nat_zhmset: "of_nat n = zhmset_of_hmset (of_nat n)"
  by (induct n) (auto simp: zero_yhmultiset_def zhmset_of_hmset_plus zhmset_of_hmset_1)

lemma of_nat_inject_zhmset[simp]: "(of_nat m :: yhmultiset) = of_nat n \<longleftrightarrow> m = n"
  unfolding of_nat_zhmset by simp

lemma plus_of_nat_plus_of_nat_zhmset:
  "k + of_nat m + of_nat n = k + of_nat (m + n)" for k :: yhmultiset
  by (simp add: add.assoc)

lemma plus_of_nat_minus_of_nat_zhmset:
  fixes k :: yhmultiset
  assumes "n \<le> m"
  shows "k + of_nat m - of_nat n = k + of_nat (m - n)"
  using assms by (metis add.left_commute add_diff_cancel_left' le_add_diff_inverse of_nat_add)

lemma of_nat_lt_\<omega>\<^sub>z[simp]: "of_nat n < \<omega>\<^sub>z"
  by (simp add: \<omega>\<^sub>z_as_\<omega> of_nat_zhmset zmset_of_mset_less)

lemma of_nat_ne_\<omega>\<^sub>z[simp]: "of_nat n \<noteq> \<omega>\<^sub>z"
  by (metis of_nat_lt_\<omega>\<^sub>z mset_le_asym mset_lt_single_iff)

lemma of_nat_lt_iff_lt_zhmset[simp]: "(of_nat M :: yhmultiset) < of_nat N \<longleftrightarrow> M < N"
  by (simp add: of_nat_zhmset zmset_of_mset_less)

lemma of_nat_le_iff_le_zhmset[simp]: "(of_nat M :: yhmultiset) \<le> of_nat N \<longleftrightarrow> M \<le> N"
  by (simp add: of_nat_zhmset zmset_of_mset_le)


subsection \<open>Embedding of Extended Natural Numbers\<close>

primrec zhmset_of_enat :: "enat \<Rightarrow> yhmultiset" where
  "zhmset_of_enat (enat n) = of_nat n"
| "zhmset_of_enat \<infinity> = \<omega>\<^sub>z"

lemma zhmset_of_enat_0[simp]: "zhmset_of_enat 0 = 0"
  by (simp add: zero_enat_def)

lemma zhmset_of_enat_1[simp]: "zhmset_of_enat 1 = 1"
  by (simp add: one_enat_def del: One_nat_def)

lemma zhmset_of_enat_of_nat[simp]: "zhmset_of_enat (of_nat n) = of_nat n"
  using of_nat_eq_enat by auto

lemma zhmset_of_enat_numeral[simp]: "zhmset_of_enat (numeral n) = numeral n"
  by (simp add: numeral_eq_enat)

lemma zhmset_of_enat_le_\<omega>\<^sub>z[simp]: "zhmset_of_enat n \<le> \<omega>\<^sub>z"
  using of_nat_lt_\<omega>\<^sub>z[THEN less_imp_le] by (cases n) auto

lemma zhmset_of_enat_eq_\<omega>\<^sub>z_iff[simp]: "zhmset_of_enat n = \<omega>\<^sub>z \<longleftrightarrow> n = \<infinity>"
  by (cases n) auto


subsection \<open>Infimum and Supremum\<close>

instantiation yhmultiset :: inf
begin

definition inf_yhmultiset :: "yhmultiset \<Rightarrow> yhmultiset \<Rightarrow> yhmultiset" where
  "inf_yhmultiset A B = (if A < B then A else B)"

instance
  by intro_classes

end

instantiation yhmultiset :: sup
begin

definition sup_yhmultiset :: "yhmultiset \<Rightarrow> yhmultiset \<Rightarrow> yhmultiset" where
  "sup_yhmultiset A B = (if B > A then B else A)"

instance
  by intro_classes

end


subsection \<open>Inequalities\<close>

instance yhmultiset :: ordered_cancel_comm_monoid_add
  by (standard; transfer) (auto simp: add_left_mono)

instance yhmultiset :: ordered_ab_group_add
  by (standard; transfer; simp)

instantiation yhmultiset :: distrib_lattice
begin

instance
  by intro_classes (auto simp: inf_yhmultiset_def sup_yhmultiset_def)

end

instantiation yhmultiset :: zero_less_one
begin

instance
  by (standard, transfer, transfer, auto)

end

instantiation yhmultiset :: linordered_idom
begin

definition sgn_yhmultiset :: "yhmultiset \<Rightarrow> yhmultiset" where
  "sgn_yhmultiset M = (if M = 0 then 0 else if M > 0 then 1 else -1)"

definition abs_yhmultiset :: "yhmultiset \<Rightarrow> yhmultiset" where
  "abs_yhmultiset M = (if M < 0 then - M else M)"

lemma gt_0_times_gt_0_imp:
  fixes a b :: yhmultiset
  assumes a_gt0: "a > 0" and b_gt0: "b > 0"
  shows "a * b > 0"
proof -
  show ?thesis
    using a_gt0 b_gt0
    apply (subst (asm) (2 4) zhmset_pos_neg_partition)
    apply simp
    apply transfer
    apply (simp add: algebra_simps zmset_of_mset_plus[symmetric] hmsetmset_plus[symmetric]
      zmset_of_mset_less)
    apply (fold HMSet_less)
    by (rule mono_cross_mult_less_hmset)
qed

instance
proof standard
  fix a b c :: yhmultiset

  assume
    a_lt_b: "a < b" and
    zero_lt_c: "0 < c"

  have "c * b < c * b + c * (b - a)"
    using gt_0_times_gt_0_imp by (simp add: a_lt_b zero_lt_c)
  hence "c * a + c * (b - a) < c * b + c * (b - a)"
    by (simp add: right_diff_distrib')
  thus "c * a < c * b"
    by simp
qed (auto simp: sgn_yhmultiset_def abs_yhmultiset_def)

end

lemma le_zhmset_of_hmset_pos: "M \<le> zhmset_of_hmset (hmset_pos M)"
  by (metis add_diff_cancel_left diff_le_eq hmultiset.sel less_eq_multiset_plus_left
    less_eq_yhmultiset.abs_eq mset_pos_as_neg zhmsetmset_inverse zmset_of_mset_le
    zmset_of_mset_plus)

lemma minus_zhmset_of_hmset_pos_le: "- zhmset_of_hmset (hmset_neg M) \<le> M"
  by (metis le_zhmset_of_hmset_pos minus_le_iff mset_pos_uminus zhmsetmset_uminus)


subsection \<open>More Inequalities and Some Equalities\<close>

lemma zero_lt_\<omega>\<^sub>z[simp]: "0 < \<omega>\<^sub>z"
  by (metis of_nat_lt_\<omega>\<^sub>z of_nat_0)

lemma one_lt_\<omega>[simp]: "1 < \<omega>\<^sub>z"
  by (metis enat_defs(2) zhmset_of_enat.simps(1) zhmset_of_enat_1 of_nat_lt_\<omega>\<^sub>z)

lemma numeral_lt_\<omega>\<^sub>z[simp]: "numeral n < \<omega>\<^sub>z"
  using zhmset_of_enat_numeral[symmetric] zhmset_of_enat.simps(1) of_nat_lt_\<omega>\<^sub>z numeral_eq_enat
  by presburger

lemma one_le_\<omega>\<^sub>z[simp]: "1 \<le> \<omega>\<^sub>z"
  by (simp add: less_imp_le)

lemma of_nat_le_\<omega>\<^sub>z[simp]: "of_nat n \<le> \<omega>\<^sub>z"
  by (simp add: le_less)

lemma numeral_le_\<omega>\<^sub>z[simp]: "numeral n \<le> \<omega>\<^sub>z"
  by (simp add: less_imp_le)

lemma not_\<omega>\<^sub>z_lt_1[simp]: "\<not> \<omega>\<^sub>z < 1"
  by (simp add: not_less)

lemma not_\<omega>\<^sub>z_lt_of_nat[simp]: "\<not> \<omega>\<^sub>z < of_nat n"
  by (simp add: not_less)

lemma not_\<omega>\<^sub>z_lt_numeral[simp]: "\<not> \<omega>\<^sub>z < numeral n"
  by (simp add: not_less)

lemma not_\<omega>\<^sub>z_le_1[simp]: "\<not> \<omega>\<^sub>z \<le> 1"
  by (simp add: not_le)

lemma not_\<omega>\<^sub>z_le_of_nat[simp]: "\<not> \<omega>\<^sub>z \<le> of_nat n"
  by (simp add: not_le)

lemma not_\<omega>\<^sub>z_le_numeral[simp]: "\<not> \<omega>\<^sub>z \<le> numeral n"
  by (simp add: not_le)

lemma zero_ne_\<omega>\<^sub>z[simp]: "0 \<noteq> \<omega>\<^sub>z"
  using zero_lt_\<omega>\<^sub>z by linarith

lemma one_ne_\<omega>\<^sub>z[simp]: "1 \<noteq> \<omega>\<^sub>z"
  using not_\<omega>\<^sub>z_le_1 by force

lemma numeral_ne_\<omega>\<^sub>z[simp]: "numeral n \<noteq> \<omega>\<^sub>z"
  by (metis not_\<omega>\<^sub>z_le_numeral numeral_le_\<omega>\<^sub>z)

lemma
  \<omega>\<^sub>z_ne_0[simp]: "\<omega>\<^sub>z \<noteq> 0" and
  \<omega>\<^sub>z_ne_1[simp]: "\<omega>\<^sub>z \<noteq> 1" and
  \<omega>\<^sub>z_ne_of_nat[simp]: "\<omega>\<^sub>z \<noteq> of_nat m" and
  \<omega>\<^sub>z_ne_numeral[simp]: "\<omega>\<^sub>z \<noteq> numeral n"
  using zero_ne_\<omega>\<^sub>z one_ne_\<omega>\<^sub>z of_nat_ne_\<omega>\<^sub>z numeral_ne_\<omega>\<^sub>z by metis+

lemma
  zhmset_of_enat_inject[simp]: "zhmset_of_enat m = zhmset_of_enat n \<longleftrightarrow> m = n" and
  zhmset_of_enat_lt_iff_lt[simp]: "zhmset_of_enat m < zhmset_of_enat n \<longleftrightarrow> m < n" and
  zhmset_of_enat_le_iff_le[simp]: "zhmset_of_enat m \<le> zhmset_of_enat n \<longleftrightarrow> m \<le> n"
  by (cases m; cases n; simp)+

lemma of_nat_lt_zhmset_of_enat_iff: "of_nat m < zhmset_of_enat n \<longleftrightarrow> enat m < n"
  by (metis zhmset_of_enat.simps(1) zhmset_of_enat_lt_iff_lt)

lemma of_nat_le_zhmset_of_enat_iff: "of_nat m \<le> zhmset_of_enat n \<longleftrightarrow> enat m \<le> n"
  by (metis zhmset_of_enat.simps(1) zhmset_of_enat_le_iff_le)

lemma zhmset_of_enat_lt_iff_ne_infinity: "zhmset_of_enat x < \<omega>\<^sub>z \<longleftrightarrow> x \<noteq> \<infinity>"
  by (cases x; simp)


subsection \<open>An Example\<close>

text \<open>
A new proof of @{thm waldmann_less}:
\<close>

lemma
  fixes \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<gamma> \<delta> :: hmultiset
  assumes
    \<alpha>\<beta>2\<gamma>_lt_\<alpha>\<beta>1\<gamma>: "\<alpha>2 + \<beta>2 * \<gamma> < \<alpha>1 + \<beta>1 * \<gamma>" and
    \<beta>2_le_\<beta>1: "\<beta>2 \<le> \<beta>1" and
    \<gamma>_lt_\<delta>: "\<gamma> < \<delta>"
  shows "\<alpha>2 + \<beta>2 * \<delta> < \<alpha>1 + \<beta>1 * \<delta>"
proof -
  let ?S = zhmset_of_hmset

  note \<alpha>\<beta>2\<gamma>_lt_\<alpha>\<beta>1\<gamma>' = \<alpha>\<beta>2\<gamma>_lt_\<alpha>\<beta>1\<gamma>[THEN zhmset_of_hmset_less[THEN iffD2],
    simplified zhmset_of_hmset_plus zhmset_of_hmset_times]
  note \<beta>2_le_\<beta>1' = \<beta>2_le_\<beta>1[THEN zhmset_of_hmset_le[THEN iffD2]]
  note \<gamma>_lt_\<delta>' = \<gamma>_lt_\<delta>[THEN zhmset_of_hmset_less[THEN iffD2]]

  have "?S \<alpha>2 + ?S \<beta>2 * ?S \<delta> = ?S \<alpha>2 + ?S \<beta>2 * ?S \<gamma> + ?S \<beta>2 * (?S \<delta> - ?S \<gamma>)"
    by (simp add: algebra_simps)
  also have "\<dots> < ?S \<alpha>1 + ?S \<beta>1 * ?S \<gamma> + ?S \<beta>2 * (?S \<delta> - ?S \<gamma>)"
    using \<alpha>\<beta>2\<gamma>_lt_\<alpha>\<beta>1\<gamma>' by simp
  also have "\<dots> \<le> ?S \<alpha>1 + ?S \<beta>1 * ?S \<gamma> + ?S \<beta>1 * (?S \<delta> - ?S \<gamma>)"
    using \<beta>2_le_\<beta>1' \<gamma>_lt_\<delta>' by simp
  also have "\<dots> = ?S \<alpha>1 + ?S \<beta>1 * ?S \<delta>"
    by (simp add: algebra_simps)
  finally have "?S \<alpha>2 + ?S \<beta>2 * ?S \<delta> < ?S \<alpha>1 + ?S \<beta>1 * ?S \<delta>"
    by assumption
  thus ?thesis
    by (simp add: zmset_of_mset_less zhmset_of_hmset_times[symmetric]
      zhmset_of_hmset_plus[symmetric])
qed

end
