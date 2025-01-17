theory Rotated_Substring
  imports Nat_Mod_Helper
begin

section "Rotated Sublists"

definition is_sublist :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where
"is_sublist xs ys = (\<exists>as bs. xs = as @ ys @ bs)"

definition is_rot_sublist :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where
"is_rot_sublist xs ys = (\<exists>n. is_sublist (rotate n xs) ys)"

definition inc_one_bounded :: "nat \<Rightarrow> nat list \<Rightarrow> bool"
  where
"inc_one_bounded n xs \<equiv>
  (\<forall>i. Suc i < length xs \<longrightarrow> xs ! Suc i = Suc (xs ! i) mod n) \<and>
  (\<forall>i < length xs. xs ! i < n)"

lemma inc_one_boundedD:
  "\<lbrakk>inc_one_bounded n xs; Suc i < length xs\<rbrakk> \<Longrightarrow> xs ! Suc i = Suc (xs ! i) mod n"
  "\<lbrakk>inc_one_bounded n xs; i < length xs\<rbrakk> \<Longrightarrow> xs ! i < n"
  using inc_one_bounded_def by blast+

lemma inc_one_bounded_nth_plus:
  "\<lbrakk>inc_one_bounded n xs; i + k < length xs\<rbrakk> \<Longrightarrow> xs ! (i + k) = (xs ! i + k) mod n"
proof (induct k)
  case 0
  then show ?case
    by (simp add: inc_one_boundedD(2))
next
  case (Suc k)
  then show ?case
    by (metis Suc_lessD add_Suc_right inc_one_bounded_def mod_Suc_eq)
qed

lemma inc_one_bounded_neq:
  "\<lbrakk>inc_one_bounded n xs; length xs \<le> n; i + k < length xs; k \<noteq> 0\<rbrakk> \<Longrightarrow> xs ! (i + k) \<noteq> xs ! i"
  using inc_one_bounded_nth_plus nat_mod_add_neq_self
  by (simp add: inc_one_boundedD(2) linorder_not_le)

corollary inc_one_bounded_neq_nth:
  assumes "inc_one_bounded n xs" 
  and     "length xs \<le> n"
  and     "i < length xs"
  and     "j < length xs"
  and     "i \<noteq> j"
shows "xs ! i \<noteq> xs ! j"
proof (cases "i < j")
  assume "i < j"
  then show ?thesis
    by (metis assms(1,2,4) canonically_ordered_monoid_add_class.lessE inc_one_bounded_neq)
next
  assume "\<not> i < j"
  then show ?thesis
    by (metis assms(1,2,3,5) canonically_ordered_monoid_add_class.lessE inc_one_bounded_neq
              le_neq_implies_less linorder_not_le)
qed

lemma inc_one_bounded_distinct:
  "\<lbrakk>inc_one_bounded n xs; length xs \<le> n\<rbrakk> \<Longrightarrow> distinct xs"
  using distinct_conv_nth inc_one_bounded_neq_nth by blast

lemma inc_one_bounded_subset_upt:
  "\<lbrakk>inc_one_bounded n xs; length xs \<le> n\<rbrakk> \<Longrightarrow> set xs \<subseteq> {0..<n}"
  by (metis atLeastLessThan_iff in_set_conv_nth inc_one_boundedD(2) less_eq_nat.simps(1)
            subset_code(1))

lemma inc_one_bounded_consD:
  "inc_one_bounded n (x # xs) \<Longrightarrow> inc_one_bounded n xs"
  unfolding inc_one_bounded_def
  using bot_nat_0.not_eq_extremum lessI less_zeroE mod_less_divisor by fastforce

lemma inc_one_bounded_nth:
  "\<lbrakk>inc_one_bounded n xs; i < length xs\<rbrakk> \<Longrightarrow> xs ! i = ((\<lambda>x. Suc x mod n)^^i) (xs ! 0)"
proof (induct i)
  case 0
  then show ?case
    by simp
next
  case (Suc i)
  note IH = this

  from IH
  have "xs ! i = ((\<lambda>x. Suc x mod n) ^^ i) (xs ! 0)"
    by simp
  hence "Suc (xs ! i) mod n = ((\<lambda>x. Suc x mod n) ^^ Suc i) (xs ! 0)"
    by force
  moreover
  from inc_one_boundedD(1)[OF IH(2,3)]
  have "xs ! Suc i = Suc (xs ! i) mod n".
  ultimately show ?case
    by presburger
qed

lemma inc_one_bounded_nth_le:
  "\<lbrakk>inc_one_bounded n xs; i < length xs; (xs ! 0) + i < n\<rbrakk> \<Longrightarrow>
   xs ! i = (xs ! 0) + i"
  by (metis add_cancel_right_left inc_one_bounded_nth_plus mod_if)

lemma inc_one_bounded_upt1:
  assumes "inc_one_bounded n xs"
  and     "length xs = Suc k"
  and     "Suc k \<le> n"
  and     "(xs ! 0) + k < n"
shows "xs = [xs ! 0..<(xs ! 0) + Suc k]"
proof (intro list_eq_iff_nth_eq[THEN iffD2] conjI impI allI)
  show "length xs = length [xs ! 0..<xs ! 0 + Suc k]"
    using assms(2) by force
next
  fix i
  assume "i < length xs"
  hence "[xs ! 0..<xs ! 0 + Suc k] ! i = xs ! 0 + i"
    by (metis add_less_cancel_left assms(2) nth_upt)
  moreover
  have "xs ! 0 + i < n"
    using \<open>i < length xs\<close> assms(2,4) by linarith
  with inc_one_bounded_nth_le[OF assms(1) \<open>i < length xs\<close>]
  have "xs ! i = xs ! 0 + i"
    by simp
  ultimately show "xs ! i = [xs ! 0..<xs ! 0 + Suc k] ! i"
    by presburger
qed

lemma inc_one_bounded_upt2:
  assumes "inc_one_bounded n xs" 
  and     "length xs = Suc k"
  and     "Suc k \<le> n"
  and     "n \<le> (xs ! 0) + k"
shows "xs = [xs ! 0..<n] @ [0..<(xs ! 0) + Suc k - n]"
proof (intro list_eq_iff_nth_eq[THEN iffD2] conjI impI allI)
  show "length xs = length ([xs ! 0..<n] @ [0..<xs ! 0 + Suc k - n])"
    using assms(1) assms(2) assms(4) inc_one_boundedD(2) less_or_eq_imp_le by auto
next
  fix i
  assume "i < length xs"
  show "xs ! i = ([xs ! 0..<n] @ [0..<xs ! 0 + Suc k - n]) ! i"
  proof (cases "i < length [xs ! 0..<n]")
    assume "i < length [xs ! 0..<n]"
    hence "([xs ! 0..<n] @ [0..<xs ! 0 + Suc k - n]) ! i = [xs ! 0..<n] ! i"
      by (meson nth_append)
    moreover
    have "[xs ! 0..<n] ! i = xs ! 0 + i"
      using \<open>i < length [xs ! 0..<n]\<close> by force
    moreover
    have "xs ! 0 + i < n"
      using \<open>i < length [xs ! 0..<n]\<close> by auto
    with inc_one_bounded_nth_le[OF assms(1) \<open>i < length xs\<close>]
    have "xs ! i = xs ! 0 + i"
      by blast
    ultimately show "xs ! i = ([xs ! 0..<n] @ [0..<xs ! 0 + Suc k - n]) ! i"
      by simp
  next
    assume "\<not> i < length [xs ! 0..<n]"
    hence "([xs ! 0..<n] @ [0..<xs ! 0 + Suc k - n]) ! i =
           [0..<xs ! 0 + Suc k - n] ! (i - length [xs ! 0..<n] )"
      by (meson nth_append)
    moreover
    have "[0..<xs ! 0 + Suc k - n] ! (i - length [xs ! 0..<n]) = i - (n - xs ! 0)"
      using \<open>i < length xs\<close> add_0 assms(2) assms(4) by fastforce
    moreover
    {
      have "i < n"
        using \<open>i < length xs\<close> assms(2) assms(3) by linarith
      moreover
      from inc_one_boundedD(2)[OF assms(1), of 0]
      have "xs ! 0 < n"
        by (simp add: assms(2))
      moreover
      have "n - xs ! 0 \<le> i"
        using \<open>\<not> i < length [xs ! 0..<n]\<close> by force
      ultimately have "xs ! i = i - (n - xs ! 0)"
        using not_mod_a_pl_b_eq2[of n "xs ! 0" i]
              inc_one_bounded_nth_plus[OF assms(1), of 0 i, simplified, OF \<open>i < length xs\<close>]
        by presburger
    }
    ultimately show "xs ! i = ([xs ! 0..<n] @ [0..<xs ! 0 + Suc k - n]) ! i"
      by argo
  qed
qed

lemmas inc_one_bounded_upt = inc_one_bounded_upt1 inc_one_bounded_upt2

lemma is_rot_sublist_nil:
  "is_rot_sublist xs []"
  by (metis append_Nil is_rot_sublist_def is_sublist_def)

lemma rotate_upt:
  "m \<le> n \<Longrightarrow> rotate m [0..<n] = [m..<n] @ [0..<m]"
  by (metis diff_zero le_Suc_ex length_upt rotate_append upt_add_eq_append zero_order(1))

lemma inc_one_bounded_is_rot_sublist:
  assumes "inc_one_bounded n xs" "length xs \<le> n"
  shows "is_rot_sublist [0..<n] xs"
  unfolding is_rot_sublist_def is_sublist_def
proof (cases "length xs")
  case 0
  then show "\<exists>na as bs. rotate na [0..<n] = as @ xs @ bs"
    using append_Nil by blast
next
  case (Suc k)
  hence "Suc k \<le> n"
    using assms(2) by auto

  have "(xs ! 0) + k < n \<Longrightarrow> \<exists>na as bs. rotate na [0..<n] = as @ xs @ bs"
  proof -
    assume "(xs ! 0) + k < n"
    with inc_one_bounded_upt(1)[OF assms(1) Suc \<open>Suc k \<le> n\<close>]
    have "xs = [xs ! 0..<xs ! 0 + Suc k]"
      by blast
    moreover
    have "xs ! 0 + Suc k \<le> n"
      by (simp add: Suc_leI \<open>xs ! 0 + k < n\<close>)
    with upt_add_eq_append[of "xs ! 0" "xs ! 0 + Suc k" "n - (xs ! 0 + Suc k)"]
    have "[xs ! 0..<n] = [xs ! 0..<xs ! 0 + Suc k] @ [xs ! 0 + Suc k..<n]"
      by (metis le_add1 le_add_diff_inverse)
    with upt_add_eq_append[of 0 "xs ! 0" "n - xs ! 0"]
    have "[0..<n] = [0..<xs ! 0] @ [xs ! 0..<xs ! 0 + Suc k] @ [xs ! 0 + Suc k..<n]"
      using \<open>xs ! 0 + Suc k \<le> n\<close> by fastforce
    ultimately show ?thesis
      by (metis append.right_neutral append_Nil rotate_append)
  qed
  moreover
  have "\<not> (xs ! 0) + k < n \<Longrightarrow> \<exists>na as bs. rotate na [0..<n] = as @ xs @ bs"
  proof -
    assume "\<not> (xs ! 0) + k < n"
    hence "(xs ! 0) + k \<ge> n"
      by simp
    with inc_one_bounded_upt(2)[OF assms(1) Suc \<open>Suc k \<le> n\<close>]
    have "xs = [xs ! 0..<n] @ [0..<xs ! 0 + Suc k - n]"
      by blast
    moreover
    from inc_one_boundedD(2)[OF assms(1), of 0]
    have "xs ! 0 < n"
      by (simp add: Suc)
    with rotate_upt[of "xs ! 0" n]
    have "rotate (xs ! 0) [0..<n] = [xs ! 0..<n] @ [0..<xs ! 0]"
      by linarith
    moreover
    {
      have "0 \<le> xs ! 0 + Suc k - n"
        by simp
      hence "[0..<xs ! 0 + Suc k - n + (n - Suc k)] = 
                [0..<xs ! 0 + Suc k - n] @ [xs ! 0 + Suc k - n..<xs ! 0 + Suc k - n + (n - Suc k)]"
        using upt_add_eq_append[of 0 "xs ! 0 + Suc k - n" "n - Suc k"] by blast
      moreover
      have "xs ! 0 = xs ! 0 + Suc k - n + (n - Suc k)"
        using \<open>Suc k \<le> n\<close> \<open>n \<le> xs ! 0 + k\<close> by auto
      ultimately have "[0..<xs ! 0] = [0..<xs ! 0 + Suc k - n] @ [xs ! 0 + Suc k - n..<xs ! 0]"
        by argo
    }
    ultimately show ?thesis
      by (metis append.assoc append_Nil)
  qed
  ultimately show "\<exists>na as bs. rotate na [0..<n] = as @ xs @ bs"
    by blast
qed

lemma is_rot_sublist_idx:
  "is_rot_sublist [0..<length xs] ys \<Longrightarrow> is_rot_sublist xs (map ((!) xs) ys)"
  unfolding is_rot_sublist_def is_sublist_def
proof (elim exE)
  fix n as bs
  assume "rotate n [0..<length xs] = as @ ys @ bs"
  hence "rotate n xs = map ((!) xs) (as @ ys @ bs)"
    by (metis map_nth rotate_map)
  then show "\<exists>n as bs. rotate n xs = as @ map ((!) xs) ys @ bs"
    by auto
qed

lemma is_rot_sublist_upt_eq_upt_hd:
  "\<lbrakk>is_rot_sublist [0..<Suc n] ys; length ys = Suc n; ys ! 0 = 0\<rbrakk> \<Longrightarrow> ys = [0..<Suc n]"
  unfolding is_rot_sublist_def is_sublist_def
proof (elim exE)
  fix m as bs
  assume A: "length ys = Suc n" "ys ! 0 = 0" "rotate m [0..<Suc n] = as @ ys @ bs"
  with rotate_conv_mod[of m "[0..<Suc n]"]
  have "rotate (m mod length [0..<Suc n]) [0..<Suc n] = as @ ys @ bs"
    by simp
  with rotate_upt[of "m mod length [0..<Suc n]" "Suc n"]
  have "[m mod length [0..<Suc n]..<Suc n] @ [0..<m mod length [0..<Suc n]] = as @ ys @ bs"
    by (metis diff_zero le_Suc_eq length_upt mod_Suc_le_divisor)
  hence "[m mod Suc n..<Suc n] @ [0..<m mod Suc n] = as @ ys @ bs"
    by simp
  moreover
  have "as = []"
    by (metis A(1) A(3) diff_zero length_append length_greater_0_conv length_rotate length_upt 
              less_add_same_cancel2 not_add_less1)
  moreover
  have "bs = []"
    by (metis A(1) A(3) append.right_neutral append_eq_append_conv calculation(2) diff_zero 
              length_rotate length_upt self_append_conv2)
  moreover
  have "m mod Suc n = 0"
    by (metis A add.right_neutral append.right_neutral calculation(2,3) diff_zero length_rotate 
              mod_less_divisor nth_rotate nth_upt self_append_conv2 zero_le zero_less_Suc
              ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
  ultimately show "ys = [0..<Suc n]"
    by simp
qed

lemma is_rot_sublist_upt_eq_upt_last:
  "\<lbrakk>is_rot_sublist [0..<Suc n] ys; length ys = Suc n; ys ! n = n\<rbrakk> \<Longrightarrow> ys = [0..<Suc n]"
  unfolding is_rot_sublist_def is_sublist_def
proof (elim exE)
  fix m as bs
  assume A: "length ys = Suc n" "ys ! n = n" "rotate m [0..<Suc n] = as @ ys @ bs"
 with rotate_conv_mod[of m "[0..<Suc n]"]
  have "rotate (m mod length [0..<Suc n]) [0..<Suc n] = as @ ys @ bs"
    by simp
  with rotate_upt[of "m mod length [0..<Suc n]" "Suc n"]
  have "[m mod length [0..<Suc n]..<Suc n] @ [0..<m mod length [0..<Suc n]] = as @ ys @ bs"
    by (metis diff_zero le_Suc_eq length_upt mod_Suc_le_divisor)
  hence "[m mod Suc n..<Suc n] @ [0..<m mod Suc n] = as @ ys @ bs"
    by simp
  moreover
  have "as = []"
    by (metis A(1) A(3) diff_zero length_append length_greater_0_conv length_rotate length_upt 
              less_add_same_cancel2 not_add_less1)
  moreover
  have "bs = []"
    by (metis A(1) A(3) append.right_neutral append_eq_append_conv calculation(2) diff_zero 
              length_rotate length_upt self_append_conv2)
  moreover
  from list_eq_iff_nth_eq[THEN iffD1, OF calculation(1), simplified, 
                          simplified calculation(2,3), simplified]
  have "Suc n = length ys" "\<forall>i<Suc n. ([m mod Suc n..<n] @ n # [0..<m mod Suc n]) ! i = ys ! i"
    by blast+
  hence "([m mod Suc n..<n] @ n # [0..<m mod Suc n]) ! n = n"
    by (simp add: A(2))
  with nth_append[of "[m mod Suc n..<n]" "n # [0..<m mod Suc n]" n]
  have "n < length [m mod Suc n..<n] \<or> 
        (n # [0..<m mod Suc n]) ! (n - length [m mod Suc n..<n]) = n"
    by argo
  hence "m mod Suc n = 0"
  proof
    assume "n < length [m mod Suc n..<n]"
    then show "m mod Suc n = 0"
      by simp
  next
    assume B: "(n # [0..<m mod Suc n]) ! (n - length [m mod Suc n..<n]) = n"
    show "m mod Suc n = 0"
    proof (cases "n - length [m mod Suc n..<n]")
      case 0
      then show ?thesis
        by simp
    next
      case (Suc x)
      then show ?thesis
        by (metis B One_nat_def add_Suc diff_diff_cancel length_upt lessI mod_Suc_le_divisor 
                    mod_less_divisor nless_le nth_Cons_Suc nth_upt plus_1_eq_Suc zero_less_Suc)
    qed
  qed
  ultimately show "ys = [0..<Suc n]"
    by simp
qed

end