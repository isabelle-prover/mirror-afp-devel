theory List_Util
  imports Main
begin

section \<open>General Lists\<close>

lemma list_cases_3:
  "T = [] \<or> (\<exists>x. T = [x]) \<or> (\<exists>a b xs. T = a # b # xs)"
proof (cases T)
  case Nil
  then show ?thesis by simp
next
  case (Cons a list)
  then show ?thesis
  proof (cases list)
    case Nil
    with \<open>T = a # list\<close>
    show ?thesis
      by simp
  next
    case (Cons a' list')
    with \<open>T = a # list\<close>
    show ?thesis
      by simp
  qed
qed

lemma length_cons_cons:
  "T = a # b # xs \<Longrightarrow> \<exists>n. length T = Suc (Suc n)"
  by simp

lemma length_Suc_Suc:
  "length T = Suc (Suc n) \<Longrightarrow> \<exists>a b xs. T = a # b # xs"
  by (metis length_Suc_conv)

lemma length_Suc_0:
  "length xs = Suc 0 \<Longrightarrow> \<exists>x. xs = [x]"
  by (simp add: length_Suc_conv)

lemma map_eq_replicate:
  "\<forall>x \<in> set xs. f x = k \<Longrightarrow> map f xs = replicate (length xs) k"
  by (metis map_eq_conv map_replicate_const)

lemma map_upt_eq_replicate:
  "\<forall>x \<in> set [i..<j]. f x = k \<Longrightarrow> map f [i..<j] = replicate (j - i) k"
  by (metis length_upt map_eq_replicate)

lemma in_set_list_update:
  "\<lbrakk>x \<in> set xs; xs ! k \<noteq> x\<rbrakk> \<Longrightarrow> x \<in> set (xs[k := y])"
  by (metis in_set_conv_nth length_list_update nth_list_update_neq)

lemma Max_greD:
  "i < length s \<Longrightarrow> Max (set s) \<ge> s ! i"
  by clarsimp


lemma list_neq_rc1:
  "(\<exists>z zs. xs = ys @ z # zs) \<Longrightarrow> xs \<noteq> ys"
  by fastforce

lemma list_neq_rc2:
  "(\<exists>z zs. ys = xs @ z # zs) \<Longrightarrow> xs \<noteq> ys"
  by fastforce

lemma list_neq_rc3:
  "(\<exists>x y as bs cs. xs = as @ x # bs \<and> ys = as @ y # cs \<and> x \<noteq> y) \<Longrightarrow> xs \<noteq> ys"
  by fastforce

lemma list_neq_rc:
  "(\<exists>z zs. xs = ys @ z # zs) \<or>
   (\<exists>z zs. ys = xs @ z # zs) \<or>
   (\<exists>x y as bs cs. xs = as @ x # bs \<and> ys = as @ y # cs \<and> x \<noteq> y) \<Longrightarrow>
    xs \<noteq> ys"
  by (elim disjE conjE list_neq_rc1 list_neq_rc2 list_neq_rc3)

lemma list_neq_fc:
  "xs \<noteq> ys \<Longrightarrow>
   (\<exists>z zs. xs = ys @ z # zs) \<or>
   (\<exists>z zs. ys = xs @ z # zs) \<or>
   (\<exists>x y as bs cs. xs = as @ x # bs \<and> ys = as @ y # cs \<and> x \<noteq> y)"
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case
    by (metis append_Nil list.exhaust)
next
  case (Cons a xs ys)
  note IH = this
  then show ?case
  proof (cases ys)
    case Nil
    then show ?thesis
      by simp
  next
    case (Cons b ys')
    assume "ys = b # ys'"
    show ?thesis
    proof (cases "a = b")
      assume "a \<noteq> b"
      with \<open>ys = b # ys'\<close> 
      show ?thesis
        by blast
    next
      assume "a = b"
      with IH(2) \<open>ys = b # ys'\<close>
      have "xs \<noteq> ys'"
        by simp
      with IH(1)[of ys']
      show ?thesis
        by (metis Cons_eq_appendI \<open>a = b\<close> local.Cons)
    qed
  qed
qed

lemma list_neq_cases:
  "xs \<noteq> ys \<longleftrightarrow>
   (\<exists>z zs. xs = ys @ z # zs) \<or>
   (\<exists>z zs. ys = xs @ z # zs) \<or>
   (\<exists>x y as bs cs. xs = as @ x # bs \<and> ys = as @ y # cs \<and> x \<noteq> y)"
  using list_neq_fc list_neq_rc by blast

section \<open>Find\<close>

lemma findSomeD:
  "find P xs = Some x \<Longrightarrow> P x \<and> x \<in> set xs"
  by (induct xs) (auto split: if_split_asm)

lemma findNoneD:
  "find P xs = None \<Longrightarrow> \<forall>x \<in> set xs. \<not>P x"
  by (induct xs) (auto split: if_split_asm)

section \<open>Filter\<close>

lemma filter_update_nth_success:
  "\<lbrakk>P v; i < length xs\<rbrakk> \<Longrightarrow>
    filter P (xs[i := v]) = (filter P (take i xs)) @ [v] @ (filter P (drop (Suc i) xs))"
  by (simp add: upd_conv_take_nth_drop)

lemma filter_update_nth_fail:
  "\<lbrakk>\<not>P v; i < length xs\<rbrakk> \<Longrightarrow>
    filter P (xs[i := v]) = (filter P (take i xs)) @ (filter P (drop (Suc i) xs))"
  by (simp add: upd_conv_take_nth_drop)

lemma filter_take_nth_drop_success:
  "\<lbrakk>i < length xs; P (xs ! i)\<rbrakk> \<Longrightarrow>
    filter P xs = (filter P (take i xs)) @ [xs ! i] @ (filter P (drop (Suc i) xs))"
  by (metis filter_update_nth_success list_update_id)

lemma filter_take_nth_drop_fail:
  "\<lbrakk>i < length xs; \<not>P (xs ! i)\<rbrakk> \<Longrightarrow>
    filter P xs = (filter P (take i xs)) @ (filter P (drop (Suc i) xs))"
  by (metis filter_update_nth_fail list_update_id)

lemma filter_nth_1:
  "\<lbrakk>i < length xs; P (xs ! i)\<rbrakk> \<Longrightarrow>
   \<exists>i'. i' < length (filter P xs) \<and> (filter P xs) ! i' = xs ! i"
proof (induct xs arbitrary: i)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xs i)
  note IH = this
  show ?case
  proof (cases i)
    case 0
    with IH(3)
    show ?thesis
      by fastforce
  next
    case (Suc n)
    with IH(1)[of n] IH(2,3)
    have "\<exists>i'<length (filter P xs). filter P xs ! i' = xs ! n"
      by fastforce
    then show ?thesis
      using Suc by auto
  qed  
qed

lemma filter_nth_2:
  "\<lbrakk>i < length (filter P xs)\<rbrakk> \<Longrightarrow>
   \<exists>i'. i' < length xs \<and> (filter P xs) ! i = xs ! i'"
proof (induct xs arbitrary: i)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xs i)
  note IH = this
  then show ?case
  proof (cases i)
    case 0
    then show ?thesis
      using Cons.hyps Cons.prems by force
  next
    case (Suc n)
    with IH(1)[of n] IH(2)
    have "\<exists>i'<length xs. filter P xs ! n = xs ! i'"
      by (metis filter.simps(2) length_Cons not_less_eq not_less_iff_gr_or_eq)
    then show ?thesis
      by (metis Cons.hyps Cons.prems Suc filter.simps(2) length_Cons not_less_eq nth_Cons_Suc)
  qed
qed

lemma filter_nth_relative_1:
  "\<lbrakk>i < length xs; P (xs ! i); j < i; P (xs ! j)\<rbrakk> \<Longrightarrow>
   \<exists>i' j'. i' < length (filter P xs) \<and> j' < i' \<and> (filter P xs) ! i' = xs ! i \<and>
    (filter P xs) ! j' = xs ! j"
proof (induct xs arbitrary: i j)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xs i j)
  note IH = this
  show ?case
  proof (cases i)
    case 0
    then show ?thesis
      using IH(4) by blast
  next
    case (Suc n)
    assume "i = Suc n"
    show ?thesis
    proof (cases j)
      case 0
      with filter_nth_1[of n xs P] IH(2,3) \<open>i = Suc n\<close> IH(4-)
      show ?thesis
        by (metis filter.simps(2) length_Cons not_less_eq nth_Cons_0 nth_Cons_Suc zero_less_Suc)
    next
      case (Suc m)
      with IH(1)[of n m] IH(2-) \<open>i = Suc n\<close>
      show ?thesis 
        by fastforce
    qed
  qed
qed

lemma filter_nth_relative_neq_1:
  assumes "i < length xs" "P (xs ! i)" "j < length xs" "P (xs ! j)" "i \<noteq> j"
  shows "\<exists>i' j'. i' < length (filter P xs) \<and> j' < length (filter P xs) \<and> (filter P xs) ! i' = xs ! i \<and>
                 (filter P xs) ! j' = xs ! j \<and> i' \<noteq> j'"
proof (cases "i < j")
  assume "i < j"
  with filter_nth_relative_1[where P = P, OF assms(3,4) _ assms(2)]
  show ?thesis
    by (metis (no_types, lifting) nat_neq_iff order_less_trans)
next
  assume "\<not> i < j"
  with assms(5)
  have "j < i"
    by auto
  with filter_nth_relative_1[where P = P, OF assms(1,2) _ assms(4)]
  show ?thesis
    using order_less_trans by blast
qed

lemma filter_nth_relative_2:
  "\<lbrakk>i < length (filter P xs); j < i\<rbrakk> \<Longrightarrow>
   \<exists>i' j'. i' < length xs \<and> j' < i' \<and> (filter P xs) ! i = xs ! i' \<and> (filter P xs) ! j = xs ! j'"
proof (induct xs arbitrary: i j)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xs i j)
  note IH = this

  let ?goal = "\<exists>i' j'. i' < length (a # xs) \<and> j' < i' \<and> filter P (a # xs) ! i = (a # xs) ! i' \<and>
                       filter P (a # xs) ! j = (a # xs) ! j'"
  show ?case
  proof (cases i)
    case 0
    then show ?goal
      using IH(3) by blast
  next
    case (Suc n)
    assume "i = Suc n"
    show ?thesis
    proof (cases j)
      case 0
      assume "j = 0"
      from filter_nth_2[of n P xs] IH(2)
      have "\<exists>i'<length xs. filter P xs ! n = xs ! i'"
        using Suc order_less_trans by fastforce

      show ?goal
      proof (cases "P a")
        assume "P a"
        then show ?goal
          by (metis "0" Suc \<open>\<exists>i'<length xs. filter P xs ! n = xs ! i'\<close> filter.simps(2)
                    length_Cons not_less_eq nth_Cons_0 nth_Cons_Suc zero_less_Suc)
      next
        assume "\<not> P a"
        then show ?goal
          using Cons.hyps IH(2,3) Suc_less_eq by fastforce
        qed
    next
      case (Suc m)
      with IH(1)[of n m] IH(2-) \<open>i = Suc n\<close>
      have "\<exists>i' j'. i' < length xs \<and> j' < i' \<and> filter P xs ! n = xs ! i' \<and>
                    filter P xs ! m = xs ! j'"
        by (metis filter.simps(2) length_Cons not_less_eq not_less_iff_gr_or_eq)
      then obtain i' j' where
        A: "i' < length xs" "j' < i'" "filter P xs ! n = xs ! i'" "filter P xs ! m = xs ! j'"
        by blast
      show ?goal
      proof (cases "P a")
        assume "P a"
        then show ?goal
          using A Suc \<open>i = Suc n\<close> by force
      next
        assume "\<not> P a"
        then show ?goal
          using Cons.hyps IH(2,3) by fastforce
      qed
    qed
  qed
qed

lemma filter_nth_relative_neq_2:
  assumes "i < length (filter P xs)" "j < length (filter P xs)" "i \<noteq> j"
  shows "\<exists>i' j'. i' < length xs \<and> j' < length xs \<and> xs ! i' = (filter P xs) ! i \<and>
                 xs ! j' = (filter P xs) ! j \<and> i' \<noteq> j'"
proof (cases "i < j")
  assume "i < j"
  with filter_nth_relative_2[OF assms(2), of i]
  show ?thesis
    by (metis dual_order.strict_trans exists_least_iff)
next
  assume "\<not> i < j"
  with assms(3)
  have "j < i"
    by auto
  with filter_nth_relative_2[OF assms(1), of j]
  show ?thesis
    by (metis nat_neq_iff order_less_trans)
qed

lemma filter_find:
  "filter P xs \<noteq> [] \<Longrightarrow> find P xs = Some ((filter P xs) ! 0)"
  by (induct xs; auto)

lemma filter_nth_update_subset:
  "set (filter P (xs[i := v])) \<subseteq> {v} \<union> set (filter P xs)"
proof
  fix x
  assume "x \<in> set (filter P (xs[i := v]))"
  with filter_set member_filter
  have "x \<in> set (xs[i := v])" "P x"
    by auto
  hence "\<exists>k < length (xs[i := v]). (xs[i := v]) ! k = x"
    by (simp add: in_set_conv_nth)
  then obtain k where
    "k < length (xs[i := v])"
    "(xs[i := v]) ! k = x"
    by blast
  hence "k < length xs"
    by simp

  from \<open>(xs[i := v]) ! k = x\<close> \<open>k < length (xs[i := v])\<close>
  have "k = i \<Longrightarrow> x = v"
    by simp
  moreover
  have "k \<noteq> i \<Longrightarrow> x \<in> set (filter P xs)"
    using \<open>P x\<close> \<open>k < length xs\<close> \<open>xs[i := v] ! k = x\<close> by auto
  ultimately
  show "x \<in> {v} \<union> set (filter P xs)"
    by blast
qed

section \<open>Upt\<close>

lemma card_upt:
  "card {0..<n} = n"
  by simp

lemma bounded_distinct_subset_upt_length:
  "\<lbrakk>distinct xs; \<forall>i<length xs. xs ! i < length xs\<rbrakk> \<Longrightarrow> set xs \<subseteq> {0..<length xs}"
  by (intro subsetI; clarsimp simp: in_set_conv_nth)

lemma bounded_distinct_eq_upt_length:
  assumes "distinct xs" 
  assumes "\<forall>i < length xs. xs ! i < length xs"
  shows "set xs = {0..<length xs}"
proof (intro card_subset_eq finite_atLeastLessThan
              bounded_distinct_subset_upt_length[OF assms] )
  from distinct_card[OF assms(1)] card_upt[of "length xs"]
  show "card (set xs) = card {0..<length xs}"
    by simp
qed

lemma set_map_nth_subset:
  assumes "n \<le> length xs"
  shows "set (map (nth xs) [0..<n]) \<subseteq> set xs"
  using assms by clarsimp

lemma set_map_nth_eq:
  "set (map (nth xs) [0..<length xs]) = set xs"
  by (intro equalityI set_map_nth_subset subsetI; simp add: map_nth)

lemma distinct_map_nth:
  assumes "distinct xs"
  assumes "n \<le> length xs"
  shows "distinct (map (nth xs) [0..<n])"
  using assms by (simp add: distinct_conv_nth)
end
