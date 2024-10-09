theory Continuous_Interval
  imports Main
begin

section \<open>Continuous Intervals\<close>

definition 
  continuous_list :: "(nat \<times> nat) list \<Rightarrow> bool"
where
  "continuous_list xs = 
      (\<forall>i. Suc i < length xs \<longrightarrow> fst (xs ! Suc i) = snd (xs ! i))"

lemma continuous_list_nil:
  "continuous_list []"
  by (simp add: continuous_list_def)

lemma continuous_list_singleton:
  "continuous_list [x]"
  by (simp add: continuous_list_def)

lemma continuous_list_cons:
  "continuous_list (x # xs) \<Longrightarrow> continuous_list xs"
  by (simp add: continuous_list_def)

lemma continuous_list_app:
  "continuous_list (xs @ ys) \<Longrightarrow> continuous_list xs \<and> continuous_list ys"
proof (induct xs)
  case Nil
  then show ?case 
    by (clarsimp simp: continuous_list_nil continuous_list_cons)
next
  case (Cons x1 xs)
  note IH1 = this(1) and
       IH2 = this(2)

  from continuous_list_cons IH2
  have "continuous_list (xs @ ys)"
    by simp
  with IH1
  have "continuous_list ys"
    by simp

  have "xs = [] \<or> xs \<noteq> []"
    by simp
  then show ?case
  proof
    assume "xs = []"
    with IH2 continuous_list_singleton
    have "continuous_list (x1 # xs)"
      by blast
    with \<open>continuous_list ys\<close>
    show ?thesis
      by simp
  next
    assume "xs \<noteq> []"
    hence "\<exists>x xs'. xs = x # xs'"
      using neq_Nil_conv by blast
    then obtain x xs' where
      "xs = x # xs'"
      by blast

    have "continuous_list (x1 # (x # xs'))"
      unfolding continuous_list_def
    proof(intro allI impI)
      fix i
      assume "Suc i < length (x1 # (x # xs'))"
      have "i = 0 \<or> i \<noteq> 0"
        by blast
      then show "fst ((x1 # x # xs') ! Suc i) = snd ((x1 # x # xs') ! i)"
      proof
        assume "i = 0"
        then show ?thesis
          using IH2 \<open>xs = x # xs'\<close> continuous_list_def by auto
      next
        assume "i \<noteq> 0"
        then show ?thesis
          using IH1 \<open>Suc i < length (x1 # x # xs')\<close> \<open>continuous_list (xs @ ys)\<close> \<open>xs = x # xs'\<close>
                continuous_list_def
          by auto
      qed
    qed
    with \<open>continuous_list ys\<close> \<open>xs = x # xs'\<close>
    show ?thesis
      by simp
  qed
qed

lemma continuous_list_interval_1:
  assumes "continuous_list xs"
  and     "xs \<noteq> []"
  and     "fst (hd xs) \<le> i"
  and     "i < snd (last xs)"
  shows "\<exists>j < length xs. fst (xs ! j) \<le> i \<and> i < snd (xs ! j)"
  using assms
proof (induct xs)
  case Nil
  then show ?case 
    by simp
next
  case (Cons x1 xs)
  note IH = this

  have "xs = [] \<longrightarrow> ?case"
  proof 
    assume "xs = []"
    with IH(4,5)
    show ?case
      by simp
  qed

  have "xs \<noteq> [] \<longrightarrow> ?case"
  proof
    assume "xs \<noteq> []"
    hence "\<exists>a b xs'. xs = (a, b) # xs'"
      by (metis (full_types) list.exhaust surj_pair)
    then obtain a b xs' where
      "xs = (a, b) # xs'"
      by blast

    from IH(2)
    have "continuous_list xs"
      using continuous_list_cons by blast

    from IH(5) \<open>xs \<noteq> []\<close>
    have "i < snd (last xs)"
      by simp

    have "a \<le> i \<or> i < a"
      by linarith
    then show ?case
    proof
      assume "a \<le> i"
      with IH(1)
            [OF \<open>continuous_list xs\<close> 
                \<open>xs \<noteq> []\<close> _ 
                \<open>i < snd (last xs)\<close>] 
           \<open>xs = (a, b) # xs'\<close>
      show ?thesis
        by auto
    next
      assume "i < a"
      with IH(2) \<open>xs = (a, b) # xs'\<close>
      have "i < snd x1"
        using continuous_list_def by auto
      with IH(4)
      show ?thesis
        by auto
    qed
  qed

  with \<open>xs = [] \<longrightarrow> ?case\<close>
  show ?case
    by blast
qed

lemma continuous_list_interval_2:
  assumes "continuous_list xs"
  and     "length xs = Suc n"
  and     "fst (xs ! 0) \<le> i"
  and     "i < snd (xs ! n)"
  shows "\<exists>j < length xs. fst (xs ! j) \<le> i \<and> i < snd (xs ! j)"
proof -
  from \<open>length xs = Suc n\<close>
  have "xs \<noteq> []"
    by auto

  from \<open>fst (xs ! 0) \<le> i\<close> \<open>xs \<noteq> []\<close>
  have "fst (hd xs) \<le> i"
    by (simp add: hd_conv_nth)

  from \<open>i < snd (xs ! n)\<close> 
        \<open>length xs = Suc n\<close> \<open>xs \<noteq> []\<close>
  have "i < snd (last xs)"
    by (simp add: last_conv_nth)

  from continuous_list_interval_1
          [OF \<open>continuous_list xs\<close> 
              \<open>xs \<noteq> []\<close> 
              \<open>fst (hd xs) \<le> i\<close>
              \<open>i < snd (last xs)\<close>]
  show ?thesis
    by assumption
qed

end