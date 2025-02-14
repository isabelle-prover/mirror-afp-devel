theory Count_Util
  imports "HOL-Library.Multiset" 
          "HOL-Combinatorics.List_Permutation" 
          "SuffixArray.List_Util"
          "SuffixArray.List_Slice"
begin

section "Counting"

subsection "Count List"

lemma count_in:
  "x \<in> set xs \<Longrightarrow> count_list xs x > 0"
  by (meson count_list_0_iff gr0I)

lemma in_count:
  "count_list xs x > 0 \<Longrightarrow> x \<in> set xs"
  by (metis count_notin less_irrefl)

lemma notin_count:
  "count_list xs x = 0 \<Longrightarrow> x \<notin> set xs"
  by (simp add: count_list_0_iff)

lemma count_list_eq_count:
  "count_list xs x = count (mset xs) x"
  by (induct xs; simp)

lemma count_list_perm:
  "xs <~~> ys \<Longrightarrow> count_list xs x = count_list ys x"
  by (simp add: count_list_eq_count)

lemma in_count_nth_ex:
  "count_list xs x > 0 \<Longrightarrow> \<exists>i < length xs. xs ! i = x"
  by (meson in_count in_set_conv_nth)

lemma in_count_list_slice_nth_ex:
  "count_list (list_slice xs i j) x > 0 \<Longrightarrow> \<exists>k < length xs. i \<le> k \<and> k < j \<and> xs ! k = x"
  by (meson in_count nth_mem_list_slice)

subsection "Cardinality"

lemma count_list_card:
  "count_list xs x = card {j. j < length xs \<and> xs ! j = x}"
proof (induct xs rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc y xs)

  let ?A = "{j. j < length xs \<and> xs ! j = x}"
  let ?B = "{j. j < length (xs @ [y]) \<and> (xs @ [y]) ! j = x}"

  have "length xs \<notin> ?A"
    by simp

  have "?B - {length xs} = ?A"
    by (intro equalityI subsetI; clarsimp simp: nth_append)

  {
    have "y = x \<Longrightarrow> count_list (xs @ [y]) x = Suc (card ?A)"
      by (simp add: snoc)
    moreover
    have "y = x \<Longrightarrow> ?B = insert (length xs) ?A"
      by (metis (mono_tags, lifting) \<open>?B - {length xs} = ?A\<close> insert_Diff length_append_singleton
                                     lessI mem_Collect_eq nth_append_length)
    with card_insert_disjoint[OF _ `length xs \<notin> _`]
    have "y = x \<Longrightarrow> card ?B = Suc (card ?A)"
      by simp
    ultimately have "y = x \<Longrightarrow> ?case"
      by simp
  }
  moreover
  have "y \<noteq> x \<Longrightarrow> count_list (xs @ [y]) x = card ?A"
    by (simp add: snoc)
  hence "y \<noteq> x \<Longrightarrow> ?case"
    using \<open>?B - {length xs} = ?A\<close> by force
  ultimately show ?case
    by blast
qed

lemma card_le_eq_card_less_pl_count_list:
  fixes s :: "'a :: linorder list"
  shows "card {k. k < length s \<and> s ! k \<le> a} = card {k. k < length s \<and> s ! k < a} + count_list s a"
proof -
  let ?A = "{k. k < length s \<and> s ! k \<le> a}"
  let ?B = "{k. k < length s \<and> s ! k < a}"
  let ?C = "{k. k < length s \<and> s ! k = a}"

  have "?B \<inter> ?C = {}"
    by blast
  hence "card (?B \<union> ?C) = card ?B + count_list s a"
    by (simp add: card_Un_disjoint count_list_card)
  moreover
  have "?A = ?B \<union> ?C"
  proof safe
    fix x
    assume "s ! x \<le> a" "s ! x \<noteq> a"
    then show "s ! x < a"
      by simp
  next
    fix x
    assume "s ! x < a"
    then show "s ! x \<le> a"
      by simp
  qed
  hence "card ?A = card (?B \<union> ?C)"
    by simp
  ultimately show ?thesis
    by simp
qed

lemma card_less_idx_upper_strict:
  fixes s :: "'a :: linorder list"
  assumes "a \<in> set s"
  shows "card {k. k < length s \<and> s ! k < a} < length s"
proof -
  have "\<exists>i < length s. s ! i = a"
    by (meson assms in_set_conv_nth)
  then obtain i where P:
    "i < length s" "s ! i = a"
    by blast

  have "{k. k < length s \<and> s ! k < a} \<subseteq> {0..<length s}"
    using atLeastLessThan_iff by blast
  moreover
  have "i \<in> {0..<length s}"
    by (simp add: P(1))
  moreover
  have "i \<notin> {k. k < length s \<and> s ! k < a}"
    by (simp add: P(2))
  ultimately have "{k. k < length s \<and> s ! k < a} \<subset> {0..<length s}"
    by blast
  then show ?thesis
    by (metis card_upt finite_atLeastLessThan psubset_card_mono)
qed

lemma card_less_idx_upper:
  shows "card {k. k < length s \<and> s ! k < a} \<le> length s"
  by (metis (no_types, lifting) atLeastLessThan_iff bot_nat_0.extremum mem_Collect_eq subsetI 
                                subset_eq_atLeast0_lessThan_card)

lemma card_pl_count_list_strict_upper:
  fixes s :: "'a :: linorder list"
  shows "card {i. i < length s \<and> s ! i < a} + count_list s a \<le> length s"
proof -
  let ?X = "{i. i < length s \<and> s ! i < a}"
  let ?Y = "{i. i < length s \<and> s ! i = a}"

  have "?X \<inter> ?Y = {}"
    by blast
  hence "card (?X \<union> ?Y) = card ?X + card ?Y"
    by (simp add: card_Un_disjoint)
  moreover
  have "card ?Y = count_list s a"
    by (simp add: count_list_card)
  moreover
  have "?X \<union> ?Y \<subseteq> {0..<length s}"
    by (simp add: subset_iff)
  hence "card (?X \<union> ?Y) \<le> length s"
    using subset_eq_atLeast0_lessThan_card by blast
  ultimately show ?thesis
    by presburger
qed

subsection "Sorting"

lemma sorted_nth_le:
  assumes "sorted xs"
  and     "card {k. k < length xs \<and> xs ! k < c} < length xs"
shows "c \<le> xs ! card {k. k < length xs \<and> xs ! k < c}"
  using assms
proof (induct xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xs)
  note IH = this

  let ?A = "{k. k < length (a # xs) \<and> (a # xs) ! k < c}"
  let ?B = "{k. k < length xs \<and> xs ! k < c}"

  have "a < c \<or> c \<le> a"
    by fastforce
  then show ?case
  proof
    assume "a < c"

    have "finite ?B"
      by auto
    hence "finite (Suc ` ?B)"
      by blast

    have "card (Suc ` ?B) = card ?B"
      using card_image inj_Suc by blast

    have "{0} \<inter> Suc ` ?B = {}"
      by blast

    have "?A = {0} \<union> Suc ` ?B"
    proof (intro equalityI subsetI)
      fix x
      assume "x \<in> {0} \<union> Suc ` ?B"
      then show "x \<in> ?A"
      proof
        assume "x \<in> {0}"
        hence "x = 0"
          by simp
        then show ?thesis
          by (simp add: \<open>a < c\<close>)
      next
        assume "x \<in> Suc ` ?B"
        hence "\<exists>y. x = Suc y \<and> xs ! y < c"
          by blast
        then show ?thesis
          using \<open>x \<in> Suc ` ?B\<close> by force
      qed
    next
      fix x
      assume "x \<in> ?A"
      hence "x = 0 \<or> (\<exists>y. x = Suc y \<and> xs ! y < c)"
        using not0_implies_Suc by fastforce
      then show "x \<in> {0} \<union> Suc ` ?B"
      proof
        assume "x = 0"
        then show ?thesis
          by blast
      next
        assume "\<exists>y. x = Suc y \<and> xs ! y < c"
        then show ?thesis
          using \<open>x \<in> ?A\<close> by fastforce
      qed
    qed
    with card_Un_disjoint[OF _ \<open>finite (Suc ` ?B)\<close> \<open>_ \<inter> _ = _\<close>]
    have "card ?A = Suc (card ?B)"
      by (simp add: \<open>card (Suc ` ?B) = card ?B\<close>)
    hence "(a # xs) ! card {k. k < length (a # xs) \<and> (a # xs) ! k < c} = 
           xs ! card {k. k < length xs \<and> xs ! k < c}"
      by simp
    then show ?case
      using Cons.hyps IH(2) IH(3) \<open>card ?A = Suc (card ?B)\<close> by auto
  next
    assume "c \<le> a"
    have "{k. k < length (a # xs) \<and> (a # xs) ! k < c} = {}"
    proof safe
      fix x
      assume A: "x < length (a # xs)" "(a # xs) ! x < c"
      show "x \<in> {}"
      proof (cases x)
        case 0
        then show ?thesis
          using A(2) \<open>c \<le> a\<close> by auto
      next
        case (Suc n)
        hence "a \<le> (a # xs) ! x"
          using A(1) IH(2) by auto
        then show ?thesis
          using A(2) \<open>c \<le> a\<close> by auto
      qed
    qed
    then show ?thesis
      by (metis \<open>c \<le> a\<close> card.empty nth_Cons_0)
  qed
qed

lemma sorted_nth_le_gen:
  assumes "sorted xs"
  and     "card {k. k < length xs \<and> xs ! k < c} + i < length xs"
shows "c \<le> xs ! (card {k. k < length xs \<and> xs ! k < c} + i)"
proof (cases i)
  case 0
  then show ?thesis
    using assms(1) assms(2) sorted_nth_le by auto
next
  let ?x = "card {k. k < length xs \<and> xs ! k < c }"
  case (Suc n)
  with sorted_wrt_nth_less[OF assms(1), of ?x "?x + i"]
  have "xs ! ?x \<le> xs ! (?x + i)"
    using assms(1) assms(2) le_add1 sorted_nth_mono by blast
  moreover
  have "c \<le> xs ! ?x"
    using add_lessD1 assms(1) assms(2) sorted_nth_le by blast
  ultimately show ?thesis
    by order
qed

lemma sorted_nth_less_gen:
  assumes "sorted xs"
  and     "i < card {k. k < length xs \<and> xs ! k < c}"
shows     "xs ! i < c"
proof (rule ccontr)
  assume "\<not> xs ! i < c"
  hence "i \<notin> {k. k < length xs \<and> xs ! k < c}"
    by simp
  hence "\<forall>k < length xs. i \<le> k \<longrightarrow> k \<notin> {k. k < length xs \<and> xs ! k < c}"
    using assms(1) sorted_iff_nth_mono by fastforce
  hence "{k. k < length xs \<and> xs ! k < c} \<subseteq> {0..<i}"
    by fastforce
  moreover
  have "card {0..<i} = i"
    by auto
  ultimately show False
    by (metis assms(2) card_mono finite_atLeastLessThan verit_comp_simplify1(3))
qed

lemma sorted_nth_gr_gen:
  assumes "sorted xs"
  and     "card {k. k < length xs \<and> xs ! k < c} + i < length xs"
  and     "count_list xs c \<le> i"
shows     "xs ! (card {k. k < length xs \<and> xs ! k < c} + i) > c"
proof -
  let ?A = "{k. k < length xs \<and> xs ! k < c}"
  have "xs ! (card ?A + i) \<ge> c"
    using assms(1) assms(2) sorted_nth_le_gen by blast
  hence "xs ! (card ?A + i) = c \<or> xs ! (card ?A + i) > c"
    by force
  then show ?thesis
  proof
    assume "xs ! (card ?A + i) > c"
    then show ?thesis .
  next
    assume "xs ! (card ?A + i) = c"

    from sorted_nth_le_gen[OF assms(1)]
    have P1: "\<forall>k < length xs. card ?A \<le> k \<longrightarrow> c \<le> xs ! k"
      by (metis (mono_tags, lifting) assms(1) dual_order.strict_trans2 linorder_not_le
                                     sorted_iff_nth_mono sorted_nth_le)

    have P2: "\<forall>k < length xs. k < card ?A + Suc i \<longrightarrow> xs ! k \<le> c"
      by (metis (mono_tags, lifting) Suc_leI \<open>xs ! (card ?A + i) = c\<close> add_Suc_right
                                      add_le_cancel_left assms(1,2) plus_1_eq_Suc sorted_nth_mono)

    have P3: "\<forall>x \<in> {card ?A..<card ?A + Suc i}. xs ! x = c"
    proof safe
      fix x
      assume "x \<in> {card ?A..<card ?A + Suc i}"
      hence A: "card ?A \<le> x" "x < card ?A + Suc i"
        by simp+

      have "c \<le> xs ! x"
        using P1 A assms(2) by auto
      moreover
      have "xs ! x \<le> c"
        using A(2) P2 assms(2) by force
      ultimately show "xs ! x = c"
        by simp
    qed

    have "{card ?A..<card ?A + Suc i} \<subseteq> {k. k < length xs \<and> xs ! k = c}"
    proof
      fix x
      assume A: "x \<in> {card ?A..<card ?A + Suc i}"
      have "x < card ?A + Suc i"
        using A by simp+
      hence "x < length xs"
        using assms(2) by linarith
      moreover
      have "xs ! x = c"
        using P3 A by blast
      ultimately show "x \<in> {k. k < length xs \<and> xs ! k = c}"
        by blast
    qed
    hence "count_list xs c \<ge> card {card ?A..<card ?A + Suc i}"
      using count_list_card[of xs c] card_mono
      by (metis (mono_tags, lifting) \<open>xs ! (card ?A + i) = c\<close> assms(2) card_ge_0_finite count_in
                                     nth_mem)

    moreover
    have "card {card ?A..<card ?A + Suc i} = Suc i"
      by simp
    ultimately have False
      using assms(3) by linarith
    then show ?thesis
      by blast
  qed
qed

end