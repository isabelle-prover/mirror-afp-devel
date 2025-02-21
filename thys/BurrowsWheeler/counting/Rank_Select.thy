theory Rank_Select
  imports Main 
          Rank_Util
          Select_Util
begin

section "Rank and Select Properties"

subsection "Correctness of Rank and Select"

text \<open>Correctness theorem statements based on \<^cite>\<open>"Affeldt_ITP_2019"\<close>.\<close>

subsubsection "Rank Correctness"

lemma rank_spec:
  "rank s x i = count (mset (take i s)) x"
  by (simp add: count_list_eq_count rank_def)

subsubsection "Select Correctness"

lemma select_spec:
  "select s x i = j
    \<Longrightarrow> (j < length s \<and> rank s x j = i) \<or> (j = length s \<and> count_list s x \<le> i )"
  by (metis le_eq_less_or_eq rank_def select_length_imp_count_list_less select_max select_nth_alt)

text \<open>Theorem 3.9 from \<^cite>\<open>"Cheung_CPP_2025"\<close>: Correctness of Select\<close>
lemma select_correct:
  "select s x i \<le> length s \<and>
   (select s x i < length s \<longrightarrow> rank s x (select s x i) = i) \<and>
   (select s x i = length s \<longrightarrow> count_list s x \<le> i)"
proof -
  have "select s x i \<le> length s"
    by (simp add: select_max)
  moreover
  have "select s x i < length s \<longrightarrow> rank s x (select s x i) = i"
    by (metis rank_def select_nth_alt)
  moreover
  have "select s x i = length s \<longrightarrow> count_list s x \<le> i"
    by (simp add: select_length_imp_count_list_less)
  ultimately show ?thesis
    by blast
qed

subsection "Rank and Select"

lemma rank_select:
  "select xs x i < length xs \<Longrightarrow> rank xs x (select xs x i) = i"
proof -
  let ?j = "select xs x i"

  assume "select xs x i < length xs"
  with select_spec[of xs x i ?j]
  show "rank xs x (select xs x i) = i"
    by auto
qed

lemma select_upper_bound:
  "i < rank xs x j \<Longrightarrow> select xs x i < length xs"
proof (induct xs arbitrary: i j)
  case Nil
  then show ?case
    by (simp add: rank_def)
next
  case (Cons a xs i j)
  note IH = this
  
  from rank_Suc_ex[OF Cons.prems]
  obtain n where
    "j = Suc n"
    by blast

  show ?case
  proof (cases "a = x")
    assume "a = x"
    show ?thesis
    proof (cases i)
      case 0
      then show ?thesis
        by (simp add: \<open>a = x\<close>)
    next
      case (Suc m)
      with rank_cons_same[of a xs n] \<open>j = Suc n\<close> IH(2) \<open>a = x\<close>
      have "m < rank xs x n"
        by force
      with IH(1)
      have "select xs x m < length xs"
        by simp
      then show ?thesis
        by (simp add: Suc \<open>a = x\<close>)
    qed
  next
    assume "a \<noteq> x"
    with Cons.prems rank_cons_diff[of a x xs n] \<open>j = Suc n\<close>
    have "i < rank xs x n"
      by force
    with Cons.hyps
    have "select xs x i < length xs"
      by simp
    then show ?thesis
      by (metis \<open>a \<noteq> x\<close> length_Cons not_less_eq select_cons_neq)
  qed
qed

lemma select_out_of_range:
  assumes "count_list xs a \<le> i"
  and     "mset xs = mset ys"
shows "select ys a i = length ys"
  by (metis assms count_list_perm leD rank_select rank_upper_bound select_nth select_spec)

subsection "Sorted Properties"
(*
lemma sorted_nth:
  assumes "sorted xs"
  and     "card {k. k < length xs \<and> xs ! k < c} < length xs"
  and     "count_list xs c > 0"
shows "xs ! card {k. k < length xs \<and> xs ! k < c} = c"
proof -
  let ?A = "{k. k < length xs \<and> xs ! k < c}"
  let ?i = "card ?A"
  have "?i = select xs c 0"
    by (simp add: assms(1) assms(3) select_sorted_0)
  with select_nth[of xs c 0 ?i]
  show ?thesis
    using assms(2) by argo
qed
*)

lemma sorted_nth_gen:
  assumes "sorted xs"
  and     "card {k. k < length xs \<and> xs ! k < c} < length xs"
  and     "count_list xs c > i"
shows "xs ! (card {k. k < length xs \<and> xs ! k < c} + i) = c"
proof -
  from sorted_select[OF assms(1,3)]
  have "select xs c i = card {j. j < length xs \<and> xs ! j < c} + i" .
  with select_nth[of xs c i]
  show ?thesis
    by (metis assms(3) rank_length select_upper_bound)
qed

lemma sorted_nth_gen_alt:
  assumes "sorted xs"
  and     "card {k. k < length xs \<and> xs ! k < a} \<le> i"
  and     "i < card {k. k < length xs \<and> xs ! k < a} + card {k. k < length xs \<and> xs ! k = a}"
shows "xs ! i = a"
proof (cases "a \<in> set xs")
  assume "a \<notin> set xs"
  hence "card {k. k < length xs \<and> xs ! k = a} = 0"
    by auto
  with assms(2-)
  show ?thesis
    by linarith
next
  assume "a \<in> set xs"

  have "card {k. k < length xs \<and> xs ! k < a} < length xs"
    using \<open>a \<in> set xs\<close> card_less_idx_upper_strict by blast
  moreover
  have "\<exists>k. i = card {k. k < length xs \<and> xs ! k < a} + k"
    using assms(2) le_iff_add by blast
  then obtain k where
    "i = card {k. k < length xs \<and> xs ! k < a} + k"
    by blast
  moreover
  have "k < count_list xs a"
    by (metis (mono_tags, lifting) count_list_card nat_add_left_cancel_less assms(3) calculation(2))
  ultimately show ?thesis
    using sorted_nth_gen[OF assms(1), of a k]
    by blast
qed

end