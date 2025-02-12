theory Select_Util
  imports Count_Util
          "SuffixArray.Sorting_Util"
begin

section "Select Definition"

text \<open>Find nth occurrence of an element in a list\<close>

text \<open>Definition 3.8 from \<^cite>\<open>"Cheung_CPP_2025"\<close>: Select\<close>
fun select :: "'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat"
  where
"select [] _ _ = 0" |
"select (a#xs) x 0 = (if x = a then 0 else Suc (select xs x 0))" |
"select (a#xs) x (Suc i)= (if x = a then Suc (select xs x i) else Suc (select xs x (Suc i)))"

section "Select Properties"

subsection "Length Properties"

lemma notin_imp_select_length:
  "x \<notin> set xs \<Longrightarrow> select xs x i = length xs"
proof (induct xs arbitrary: i)
  case Nil
  then show ?case
    by simp 
next
  case (Cons a xs i)
  then show ?case
  proof (cases i)
    case 0
    then show ?thesis
      using Cons.hyps Cons.prems by fastforce
  next
    case (Suc n)
    then show ?thesis
      using Cons.hyps Cons.prems by force
  qed
qed

lemma select_length_imp_count_list_less:
  "select xs x i = length xs \<Longrightarrow> count_list xs x \<le> i"
  by (induct rule: select.induct[of _ xs x i]; simp split: if_splits)

lemma select_Suc_length:
  "select xs x i = length xs \<Longrightarrow> select xs x (Suc i) = length xs"
  by (induct rule: select.induct[of _ xs x i]; clarsimp split: if_splits)

subsection "List Properties"

lemma select_cons_neq:
  "\<lbrakk>select xs x i = j; x \<noteq> a\<rbrakk> \<Longrightarrow> select (a # xs) x i= Suc j"
  by (cases i; simp)

lemma cons_neq_select:
  "\<lbrakk>select (a # xs) x i = Suc j; x \<noteq> a\<rbrakk> \<Longrightarrow> select xs x i = j"
  by (cases i; simp)

lemma cons_eq_select:
  "select (x # xs) x (Suc i) = Suc j \<Longrightarrow> select xs x i = j"
  by simp

lemma select_cons_eq:
  "select xs x i = j \<Longrightarrow> select (x # xs) x (Suc i) = Suc j"
  by simp

subsection "Bound Properties"

lemma select_max:
  "select xs x i \<le> length xs"
  by (induct rule: select.induct[of _ xs x i]; simp)


subsection "Nth Properties"

lemma nth_select:
  "\<lbrakk>j < length xs; count_list (take (Suc j) xs) x = Suc i; xs ! j = x\<rbrakk>
    \<Longrightarrow> select xs x i = j"
proof (induct arbitrary: j rule: select.induct[of _ xs x i])
  case (1 uu uv)
  then show ?case 
    by simp
next
  case (2 a xs x)
  then show ?case
  proof (cases j)
    case 0
    then show ?thesis
      using "2.prems"(3) by auto
  next
    case (Suc n)

    have "xs ! n = x"
      using "2.prems"(3) Suc by auto
    moreover
    have "n < length xs"
      using "2.prems"(1) Suc by auto
    moreover
    have "x \<noteq> a"
    proof (rule ccontr)
      assume "\<not> x \<noteq> a"
      hence "x = a"
        by blast
      moreover
      have "count_list (take (Suc n) xs) x > 0"
        by (simp add: \<open>n < length xs\<close> \<open>xs ! n = x\<close> take_Suc_conv_app_nth)
      ultimately show False
        using "2.prems"(2) Suc by auto
    qed
    moreover
    have "count_list (take (Suc n) xs) x = Suc 0"
      using "2.prems"(2) Suc calculation(3) by auto
    ultimately have "select xs x 0 = n"
      using "2.hyps" by blast
    then show ?thesis
      by (simp add: Suc \<open>x \<noteq> a\<close>)
  qed
next
  case (3 a xs x i)
  then show ?case
  proof (cases j)
    case 0
    then show ?thesis
      using "3.prems"(2) "3.prems"(3) by force
  next
    case (Suc n)
    then show ?thesis
      by (metis "3.hyps" "3.prems" Suc_inject Suc_less_eq  add.right_neutral add_Suc_right
                count_list.simps(2) length_Cons nth_Cons_Suc plus_1_eq_Suc select.simps(3)
                take_Suc_Cons)
  qed
qed

lemma nth_select_alt:
  "\<lbrakk>j < length xs; count_list (take j xs) x = i; xs ! j = x\<rbrakk>
    \<Longrightarrow> select xs x i = j"
proof (induct arbitrary: j rule: select.induct[of _ xs x i])
  case (1 uu uv)
  then show ?case
    by simp
next
  case (2 a xs x j)
  then show ?case
  proof (cases j)
    case 0
    then show ?thesis
      using "2.prems"(3) by auto
  next
    case (Suc n)
    then show ?thesis
      by (metis "2.hyps" "2.prems" Suc_less_eq count_in count_list.simps(2) length_Cons
                list.set_intros(1) not_gr_zero nth_Cons_Suc select.simps(2) take_Suc_Cons)
  qed
next
  case (3 a xs x i)
  then show ?case
  proof (cases j)
    case 0
    then show ?thesis
      using "3.prems"(2) by auto
  next
    case (Suc n)
    then show ?thesis
      by (metis "3.hyps" "3.prems" One_nat_def Suc_inject Suc_less_eq add.right_neutral
                add_Suc_right count_list.simps(2) length_Cons nth_Cons_Suc select.simps(3)
                take_Suc_Cons)
  qed
qed

lemma select_nth:
  "\<lbrakk>select xs x i = j; j < length xs\<rbrakk>
    \<Longrightarrow> count_list (take (Suc j) xs) x = Suc i \<and> xs ! j = x"
proof (induct arbitrary: j rule: select.induct[of _ xs x i])
  case (1 uu uv)
  then show ?case
    by simp
next
  case (2 a xs x j)
  then show ?case
  proof (cases j)
    case 0
    then show ?thesis
      by (metis "2.prems"(1) One_nat_def add.right_neutral add_Suc_right count_list.simps
                nat.simps(3) nth_Cons_0 select_cons_neq take0 take_Suc_Cons)
  next
    case (Suc n)
    then show ?thesis
      using "2.hyps" "2.prems"(1) "2.prems"(2) by auto
  qed
next
  case (3 a xs x i j)
  then show ?case
  proof (cases j)
    case 0
    then show ?thesis
      by (metis "3.prems"(1) nat.simps(3) select_cons_eq select_cons_neq)
  next
    case (Suc n)
    then show ?thesis
      by (metis "3.hyps" "3.prems" One_nat_def Suc_le_eq add.right_neutral add_Suc_right
                count_list.simps(2) length_Cons less_Suc_eq_le nth_Cons_Suc select_cons_eq
                select_cons_neq take_Suc_Cons)
  qed
qed

lemma select_nth_alt:
  "\<lbrakk>select xs x i = j; j < length xs\<rbrakk>
    \<Longrightarrow> count_list (take j xs) x = i \<and> xs ! j = x"
proof (induct arbitrary: j rule: select.induct[of _ xs x i])
  case (1 uu uv)
  then show ?case
    by simp
next
  case (2 a xs x j)
  then show ?case
  proof (cases j)
    case 0
    then show ?thesis
      using "2.prems"(1) order.strict_iff_not by fastforce
  next
    case (Suc n)
    then show ?thesis
      by (metis "2.prems"(1) "2.prems"(2) nat.inject nth_select_alt select_nth)
  qed
next
  case (3 a xs x i j)
  then show ?case
  proof (cases j)
    case 0
    then show ?thesis
      by (metis "3.prems"(1) nat.simps(3) select_cons_eq select_cons_neq)
  next
    case (Suc n)
    then show ?thesis
      by (metis "3.prems" nat.inject nth_select_alt select_nth)
  qed
qed

lemma select_less_0_nth:
  assumes "i < length xs"
  and     "i < select xs x 0"
shows "xs ! i \<noteq> x"
proof (cases "select xs x 0 < length xs")
  assume "select xs x 0 < length xs"
  with select_nth_alt[of xs x 0 "select xs x 0"]
  have "count_list (take (select xs x 0) xs) x = 0" "xs ! select xs x 0 = x"
    by blast+
  with count_list_0_iff
  have "x \<notin> set (take (select xs x 0) xs)"
    by metis
  then show ?thesis
    by (simp add: \<open>select xs x 0 < length xs\<close> assms(2) in_set_conv_nth)
next
  assume "\<not> select xs x 0 < length xs"
  hence "length xs \<le> select xs x 0"
    using linorder_le_less_linear by blast
  with select_max[of xs x 0]
  have "select xs x 0 = length xs"
    by simp
  with select_length_imp_count_list_less
  have "count_list xs x = 0"
    by (metis le_zero_eq)
  with count_list_0_iff
  have "x \<notin> set xs"
    by fastforce
  then show ?thesis
    using assms(1) nth_mem by blast
qed

subsection "Sorted Properties"

text \<open>Theorem 3.10 from \<^cite>\<open>"Cheung_CPP_2025"\<close>: Select Sorted Equivalence\<close> 
lemma sorted_select:
  assumes "sorted xs"
  and     "i < count_list xs x"
shows "select xs x i = card {j. j < length xs \<and> xs ! j < x} + i"
  using assms
proof (induct rule: select.induct[of _ xs x i])
  case (1 uu uv)
  then show ?case
    by simp
next
  case (2 a xs x)
  note IH = this

  from IH(2)
  have "sorted xs"
    by simp

  have "x = a \<or> x \<noteq> a"
    by blast
  moreover
  have "x \<noteq> a \<Longrightarrow> ?case"
  proof -
    assume "x \<noteq> a"
    hence "0 < count_list xs x"
      using IH(3) by fastforce
    with IH(1)[OF `x \<noteq> a` `sorted xs`]
    have "select xs x 0 = card {j. j < length xs \<and> xs ! j < x}"
      by simp
    moreover
    {
      from in_count[OF `0 < count_list xs x`]
      have "x \<in> set xs" .
      with IH(2) `x \<noteq> a`
      have "a < x"
        by (simp add: order_less_le)
      have "{j. j < length (a # xs) \<and> (a # xs) ! j < x} = 
              {0} \<union> Suc ` {j. j < length xs \<and> xs ! j < x}"
      proof (safe)
        show " (a # xs) ! 0 < x"
          by (simp add: \<open>a < x\<close>)
      next
        fix y
        assume "y < length xs"
        then show "Suc y < length (a # xs)"
          by simp
      next
        fix y
        assume "y < length xs" "xs ! y < x"
        then show "(a # xs) ! Suc y < x"
          by simp
      next
        fix j
        assume A: "j \<notin> Suc ` {v. v < length xs \<and> xs ! v < x}" "j < length (a # xs)" 
                  "(a # xs) ! j < x"

        have "\<exists>k. j = Suc k \<Longrightarrow> False"
        proof -
          assume "\<exists>k. j = Suc k"
          then obtain k where
          "j = Suc k"
            by blast
          hence B: "k < length xs" "xs ! k < x" "k \<notin> {v. v < length xs \<and> xs ! v < x}"
            using A by simp_all
          then show False
            by auto
        qed
        then show "j = 0"
          using not0_implies_Suc by blast
      qed
      moreover
      {
        have "finite {0}"
          by blast
        moreover
        have "finite (Suc ` {j. j < length xs \<and> xs ! j < x})"
          by simp
        moreover
        have "{0} \<inter> Suc ` {j. j < length xs \<and> xs ! j < x} = {}"
          by blast
        ultimately have
          "card ({0} \<union> Suc ` {j. j < length xs \<and> xs ! j < x}) = 
            Suc (card (Suc ` {j. j < length xs \<and> xs ! j < x}))"
          using card_Un_disjoint[of "{0}" "Suc ` {j. j < length xs \<and> xs ! j < x}"] by simp
      }
      ultimately have
        "card {j. j < length (a # xs) \<and> (a # xs) ! j < x} =
          Suc (card (Suc `{j. j < length xs \<and> xs ! j < x}))"
        by presburger
      hence "card {j. j < length (a # xs) \<and> (a # xs) ! j < x} =
              Suc (card {j. j < length xs \<and> xs ! j < x})"
        by (simp add: card_image)
    }
    moreover
    have "select (a # xs) x 0 = Suc (select xs x 0)"
      using `x \<noteq> a` select.simps(2)[of a xs x] by auto
    ultimately show ?thesis
      by simp
  qed
  moreover
  have "x = a \<Longrightarrow> ?case"
  proof -
    assume "x = a"
    with IH(2)
    have "{j. j < length (a # xs) \<and> (a # xs) ! j < x} = {}"
      by (metis (no_types, lifting) Collect_empty_eq less_nat_zero_code linorder_not_less neq0_conv
                                    nth_Cons_0 order_refl sorted_nth_less_mono)
    with `x = a`
    show ?thesis
      by force
  qed
  ultimately show ?case
    by blast
next
  case (3 a xs x i)
  note IH = this

  have "sorted xs"

    using IH(3) by auto
  have "a \<le> x"
    by (metis IH(3-) Suc_less_eq2 count_list.simps(2) in_count order_refl sorted_simps(2)
              zero_less_Suc)

  have "x = a \<or> x \<noteq> a"
    by blast
  moreover 
  have "x = a \<Longrightarrow> ?case"
  proof -
    assume "x = a"
    with IH(4)
    have "i < count_list xs x"
      by auto
    with IH(1)[OF `x = a` `sorted xs`]
    have "select xs x i = card {j. j < length xs \<and> xs ! j < x} + i" .
    moreover
    from select.simps(3)[of a xs x i] `x = a`
    have "select (a # xs) x (Suc i) = Suc (select xs x i)"
      by simp
    moreover
    from `a \<le> x` `x = a` IH(3)
    have "{j. j < length (a # xs) \<and> (a # xs) ! j < x} = {}"
      by (metis (no_types, lifting) Collect_empty_eq length_Cons less_nat_zero_code
                                    linorder_not_less nth_Cons_0 sorted_nth_less_mono zero_less_Suc)
    hence "card {j. j < length (a # xs) \<and> (a # xs) ! j < x} = 0"
      by simp
    moreover
    from `a \<le> x` `x = a` IH(3)
    have "{j. j < length xs \<and> xs ! j < x} = {}"
      using nth_mem by fastforce
    hence "card {j. j < length xs \<and> xs ! j < x} = 0"
      by simp
    ultimately show ?thesis
      by simp
  qed
  moreover
  have "x \<noteq> a \<Longrightarrow> ?case"
  proof -
    assume "x \<noteq> a"
    hence "Suc i < count_list xs x"
      using IH(4) by force
    with IH(2)[OF `x \<noteq> a` `sorted xs`]
    have "select xs x (Suc i) = card {j. j < length xs \<and> xs ! j < x} + Suc i" .
    moreover
    from `x \<noteq> a` select.simps(3)[of a xs x i]
    have "select (a # xs) x (Suc i) = Suc (select xs x (Suc i))"
      by simp
    moreover
    {
      have "{j. j < length (a # xs) \<and> (a # xs) ! j < x} =
              {0} \<union> Suc ` {j. j < length xs \<and> xs ! j < x}"
      proof safe
        show "(a # xs) ! 0 < x"
          using \<open>a \<le> x\<close> \<open>x \<noteq> a\<close> by auto
      next
        fix y
        assume "y < length xs" "xs ! y < x"
        then show "Suc y < length (a # xs)"
          by simp
      next
        fix y
        assume "y < length xs" "xs ! y < x"
        then show "(a # xs) ! Suc y < x"
          by simp
      next  
        fix k
        assume A: "k \<notin> Suc ` {j. j < length xs \<and> xs ! j < x}" "k \<notin> {}" "k < length (a # xs)"
                  "(a # xs) ! k < x"

        have "\<exists>l. k = Suc l \<Longrightarrow> False"
        proof -
          assume "\<exists>l. k = Suc l"
          then obtain l where
            "k = Suc l"
            by blast
          hence "l \<notin> {j. j < length xs \<and> xs ! j < x}" "l < length xs" "xs ! l < x"
            using A by simp_all
          then show False
            by blast
        qed
        then show "k = 0"
          using not0_implies_Suc by blast
      qed
      moreover
      have "finite {0}"
        by blast
      moreover
      have "finite (Suc ` {j. j < length xs \<and> xs ! j < x})"
        by simp
      moreover
      have "{0} \<inter> Suc ` {j. j < length xs \<and> xs ! j < x} = {}"
        by blast
      ultimately have
        "card ({j. j < length (a # xs) \<and> (a # xs) ! j < x}) = 
          Suc (card (Suc ` {j. j < length xs \<and> xs ! j < x}))"
        by simp
      hence "card ({j. j < length (a # xs) \<and> (a # xs) ! j < x}) =
              Suc (card {j. j < length xs \<and> xs ! j < x})"
        by (simp add: card_image)
    }
    ultimately show ?thesis
      by simp
  qed
  ultimately show ?case 
    by blast
qed

corollary sorted_select_0_plus:
  assumes "sorted xs"
  and     "i < count_list xs x"
shows "select xs x i = select xs x 0 + i"
  using assms(1) assms(2) sorted_select by fastforce

corollary select_sorted_0:
  assumes "sorted xs"
  and     "0 < count_list xs x"
shows "select xs x 0 = card {j. j < length xs \<and> xs ! j < x}"
  by (simp add: assms(1) assms(2) sorted_select)


end