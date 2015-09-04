(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Auxiliary $\omega$-Word Facts\<close>

theory Words2
  imports "Main" "../../Automatic_Refinement/Lib/Words" 
begin 

subsection \<open>Prefix\<close>

fun prefix :: "nat \<Rightarrow> 'a word \<Rightarrow> 'a list" 
where
  "prefix n w = (map w [0..<n])"

fun prefix_rec :: "nat \<Rightarrow> 'a word \<Rightarrow> 'a list" 
where 
  "prefix_rec 0 _ = []"
| "prefix_rec (Suc i) w = (prefix_rec i w) @ [w i]"

lemma prefix_rec_equiv_def:
  "prefix n w = prefix_rec n w"
  using map_append upt.simps(2) by (induction n) force+

lemma prefix_suffix2:
  "x = (prefix n x) \<frown> (suffix n x)"
  using prefix_suffix by auto

lemma prefix_length:
  "length (prefix i w) = i"
  by simp

lemma prefix_correct:
  "i < j \<Longrightarrow> (prefix j w) ! i = w i"
  using nth_map_upt by simp  

lemma prefix_decompose:
  "prefix (i + j) w = (prefix i w) @ (prefix j (suffix i w))"
  unfolding prefix_rec_equiv_def by (induction j arbitrary: i) simp_all

subsection \<open>Subsequence\<close>

fun subsequence :: "'a word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" ("_ [_ \<rightarrow> _]" 900) 
where
  "subsequence w i j = map w [i..<j]"

lemma subsequence_prefix_suffix:
  "w [i \<rightarrow> j] = prefix (j - i) (suffix i w)"
proof (cases "i \<le> j")
  case True
    have "w [i \<rightarrow> j] = map w (map (\<lambda>n. n + i) [0..<j - i])"
      unfolding map_add_upt using le_add_diff_inverse2[OF True] by force
    also
    have "\<dots> = map (\<lambda>n. w (n + i)) [0..<j - i]"
      unfolding map_map comp_def by blast
    also
    have "\<dots> = prefix (j - i) (suffix i w)"
      unfolding suffix_def add.commute[of i] by simp 
    finally
    show ?thesis .
qed simp

lemma subsequence_append:
  "w [0 \<rightarrow> i + j] = (w [0 \<rightarrow> i]) @ (w [i \<rightarrow> i + j])"
  unfolding subsequence.simps map_append[symmetric] 
  unfolding upt_add_eq_append[OF le0] ..

lemma subsequence_drop:
  "drop i (w [j \<rightarrow> k]) = w [(j+i) \<rightarrow> k]"
  unfolding subsequence.simps drop_map drop_upt ..

lemma subsequence_empty:
  "(j \<le> i) = (w [i \<rightarrow> j] = [])"
  by force

lemma subsequence_length:
  "length (subsequence w i j) = j - i"
  by simp

lemma subsequence_shift:
  "w [i + j \<rightarrow> i + k] = suffix i w [j \<rightarrow> k]"
  unfolding subsequence_prefix_suffix using suffix_suffix by simp

lemma subsequence_shift_simple:
  "w [i \<rightarrow> i + k] = suffix i w [0 \<rightarrow> k]"
  using subsequence_shift Nat.add_0_right by metis

lemma prefix_is_subsequence:
  "prefix n w = w [0 \<rightarrow> n]"
  by simp

subsection \<open>Suffixes\<close>
-- \<open>Compute non empty suffixes of finite words\<close>

fun suffixes
where
  "suffixes [] = []"
| "suffixes (x#xs) = (suffixes xs) @ [x#xs]"

lemma suffixes_append:
  "suffixes (xs @ ys) = (suffixes ys) @ (map (\<lambda>xss. xss @ ys) (suffixes xs))"
  by (induction xs) simp_all

lemma suffixes_alt_def:
  "suffixes xs = rev (map (\<lambda>i. drop i xs) [0..<length xs])" 
proof (induction xs rule: rev_induct)
  case (snoc x xs)
    have "suffixes (xs @ [x]) = [x] # (map (\<lambda>xss. xss @ [x]) (suffixes xs))"
      unfolding suffixes_append by simp
    also
    have "\<dots> = rev ([[x]]) @ rev (map (\<lambda>xss. xss @ [x]) (map (\<lambda>i. drop i xs) [0..<length xs]))"
      using rev.simps(2) rev_map rev_rev_ident rev_append snoc.IH by metis
    also
    have "\<dots> = rev (map (\<lambda>xss. xss @ [x]) (map (\<lambda>i. drop i xs) [0..<length xs]) @ [[x]])"
      using rev_append by fastforce
    also
    have "\<dots> = rev (map (\<lambda>i. drop i (xs @ [x])) [0..<length xs] @ [[x]])"
      unfolding map_map comp_def using drop_append by simp
    also
    have "\<dots> = rev (map (\<lambda>i. drop i (xs @ [x])) [0..<length (xs @ [x])])"
      unfolding length_append_singleton upt_Suc_append[OF le0] by simp
    finally
    show ?case .
qed simp

lemma suffixes_subsequence':
  "suffixes (w [0 \<rightarrow> j]) = rev (map (\<lambda>i. w [i \<rightarrow> j]) [0..<j])"
proof (induction j)
  case (Suc j) 
    have A: "\<And>i. i \<le> j \<Longrightarrow> w [i \<rightarrow> j] @ [w (j)] = w [i \<rightarrow> Suc j]" 
      using upt.simps(2) by fastforce
    have B: "\<And>i j. i \<in> set [0..<Suc j] \<Longrightarrow> i \<le> j"
      by auto
 
    have "suffixes (w [0 \<rightarrow> Suc j]) = [w j] # map (\<lambda>xs. xs @ [w j]) (suffixes (w [0 \<rightarrow> j]))"
      unfolding A[OF le0, symmetric] suffixes_append[of _ "[w (j)]"] by simp
    also 
    have "\<dots> = [w j] # rev (map (\<lambda>xs. xs @ [w j]) (map (\<lambda>i. w [i \<rightarrow> j]) [0..<j]))"
      unfolding Suc.IH using rev_map by metis
    also
    have "\<dots> = rev (map (\<lambda>xs. xs @ [w j]) (map (\<lambda>i. w [i \<rightarrow> j]) [0..<Suc j])) "
      unfolding upt.simps by fastforce
    also
    have "\<dots> = rev (map (\<lambda>i. w [i \<rightarrow> Suc j]) [0..<Suc j])"
      unfolding map_map rev_map map_eq_conv using B[of _ j, THEN A] by simp
    finally
    show ?case 
      by force
qed simp

lemma suffixes_subsequence:
  "suffixes (w [i \<rightarrow> j]) = rev (map (\<lambda>i. w [i \<rightarrow> j]) [i..<j])"
proof (cases i j rule: linorder_cases)
  case less
    then obtain j' where "j = i + j'"
      by (metis less_imp_add_positive)

    have "map (\<lambda>ia. suffix i w [ia \<rightarrow> j']) [0..<j'] = map (\<lambda>ia. w [i + ia \<rightarrow> i + j']) [0..<j']"
      using subsequence_shift by metis
    also
    have "\<dots> = map (\<lambda>ia. w [ia \<rightarrow> i + j']) (map (\<lambda>ia. ia + i) [0..<j'])"
      unfolding map_map by (metis comp_apply add.commute) 
    also
    have "\<dots> = map (\<lambda>ia. w [ia \<rightarrow> i + j']) [i..<i + j']"
      unfolding map_add_upt[of i "j'"] by (metis add.commute)
    finally
    show ?thesis
      using suffixes_subsequence'[of "suffix i w"] subsequence_shift `j = i + j'` 
      by (metis Nat.add_0_right)
qed (simp add: upt.simps(2))+

subsection \<open>Concatenation\<close>

lemma suffix_conc:
  "suffix (length w) (w \<frown> w') = w'"
  unfolding conc_def by force

lemma prefix_conc:
  "prefix (length w) (w \<frown> w') = w"
proof (induction w arbitrary: w' rule: rev_induct)
  case (snoc x xs)
    have "prefix (length [x]) (suffix (length xs) (xs conc [x] conc w')) = [x]"
      unfolding suffix_conc using prefix_suffix2 conc_fst[of _ "[x]" w']  
      by (metis Suc_length_conv conc_fst length_greater_0_conv list.distinct(2) list.size(3) nth_Cons_0 prefix_length)
    hence "prefix (length (xs @ [x])) ((xs @ [x]) conc w') = xs @ [x]"
      unfolding length_append prefix_decompose conc_conc[symmetric] snoc.IH[of "[x] conc w'"] 
      by simp
    thus ?case
      by blast
qed simp

subsection \<open>Limit\<close>

lemma limit_subset:
  "limit f \<subseteq> f ` {n..}"
  using limit_in_range_suffix[of f n] unfolding suffix_def by auto

lemma limit_range_suffix:
  assumes "limit r = range (suffix i r)"
  shows "limit r = range (suffix (i + j) r)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = range (suffix i r)"
    using assms .
  moreover
  have "\<dots> \<supseteq> ?rhs"
    by (metis (mono_tags, hide_lams) calculation imageI image_subsetI iso_tuple_UNIV_I suffix_nth suffix_suffix)
  moreover
  have "\<dots> \<supseteq> ?lhs" 
    using limit_in_range_suffix .
  ultimately
  show "?lhs = ?rhs"
    by (metis antisym_conv limit_in_range_suffix)
qed

lemma common_range_limit:
  assumes "finite (range x)" and "finite (range y)"
  obtains i where "limit x = range (suffix i x)"  
    and "limit y = range (suffix i y)"
proof -
  obtain i j where "limit x = range (suffix i x)"
    and "limit y = range (suffix j y)"
    using assms limit_is_suffix by metis
  hence "limit x = range (suffix (i + j) x)"
    and "limit y = range (suffix (i + j) y)"
    using limit_range_suffix add.commute by metis+
  thus ?thesis
    using that by metis
qed

lemma limit_inter_empty:
  assumes fin: "finite (range w)"
  assumes hyp: "limit w \<inter> S = {}"
  shows "\<forall>\<^sub>\<infinity>n. w n \<notin> S"
proof -
  from fin obtain k where k_def: "limit w = range (suffix k w)"
    using limit_is_suffix by blast
  have "\<And>k'. w (k + k') \<notin> S"
    using hyp unfolding k_def suffix_def image_def by blast
  thus ?thesis
    unfolding MOST_nat_le using le_Suc_ex by blast
qed

end
