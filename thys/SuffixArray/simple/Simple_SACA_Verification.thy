theory Simple_SACA_Verification
  imports 
    "Simple_SACA"  
    "../spec/Suffix_Array"
begin

lemma suf_length_app:
  "i < length xs \<Longrightarrow> length (suffix (xs @ ys) i) = length (suffix xs i) + length ys"
  apply (induct xs)
   apply simp
  apply simp
  done

lemma distinct_natlist_add:
  "distinct (xs :: nat list) \<Longrightarrow> distinct (map ((+) n) xs)"
  apply (induct xs arbitrary: n)
   apply simp
  apply clarsimp
  done

lemma nat_minus_cancel_right:
  "\<lbrakk>(x::nat) \<le> n; y \<le> n; n - x = n - y\<rbrakk> \<Longrightarrow> x = y"
  apply (subst (asm) le_imp_diff_is_add, simp)
  apply (subst (asm) add.commute)
  apply (subst (asm) add_diff_assoc, simp)
  apply (subst (asm) add.commute)
  apply (drule sym)
  apply (subst (asm) Nat.le_imp_diff_is_add, simp)
  apply clarsimp
  done

lemma distinct_natlist_sub:
  "\<lbrakk>distinct (xs :: nat list); \<forall>x \<in> set xs. x \<le> n\<rbrakk> \<Longrightarrow> distinct (map ((-) n) xs)"
  by (meson distinct_map inj_onI nat_minus_cancel_right)

lemma map_suf_app:
  "n \<le> length xs \<Longrightarrow>
    map (length \<circ> suffix (xs @ ys)) [0..<n] = map ((+) (length ys)) (map (length \<circ> (suffix xs)) [0..<n])"
  apply (induct xs)
   apply simp
  apply clarsimp
  apply (subst add.commute)
  apply simp
  done

lemma distinct_map_length_gen_suffixes:
  "distinct (map length (gen_suffixes s))"
  apply (induct s rule: rev_induct)
   apply simp
  apply (simp only: gen_suffixes.simps map_map length_append)
  apply (subst upt_add_eq_append; simp only: map_append)
  apply (subst map_suf_app; simp only: distinct_append)
  apply (rule conjI)
   apply (rule distinct_natlist_add; simp)
  apply (rule conjI; clarsimp)
  done

lemma different_length_different_list:
  "length a \<notin> length ` set xs \<Longrightarrow> a \<notin> set xs"
  apply blast
  done

lemma distinct_map_length_sort:
  "distinct (map length xs) \<Longrightarrow> distinct (map length (sort xs))"
  apply (induct xs)
   apply simp
  apply clarsimp
  apply (rule card_distinct)
  apply simp
  apply (drule distinct_card)
  apply clarsimp
  apply (frule different_length_different_list)
  apply (subst insort_insert_insort[symmetric]; simp)
  apply (subst set_insort_insert)
  apply simp
  done

lemma suffix_ids_def':
  "suffix_ids s xs = map (((-) (length s)) \<circ> length) xs"
  apply simp
  done

lemma distinct_simple_saca:
  "distinct (simple_saca s)"
  apply (subst simple_saca.simps)
  apply (subst suffix_ids_def')
  apply (subst map_map[symmetric])
  apply (rule distinct_natlist_sub)
   apply (rule distinct_map_length_sort[OF distinct_map_length_gen_suffixes])
  apply clarsimp
  done

lemma suf_suffix_id_suf:
  "i < length s \<Longrightarrow> suffix s (length s - length (suffix s i)) = suffix s i"
  apply (induct s arbitrary: i)
   apply simp
  apply clarsimp
  done

lemma in_set_ordlist_sort:
  "(x \<in> set xs) = (x \<in> set (sort xs))"
  by simp

lemma ordlist_sort_conv_nth:
  "(\<exists>i<length xs. xs ! i = x) = (\<exists>i<length xs. (sort xs) ! i = x)"
  by (metis in_set_conv_nth length_sort set_sort)

lemma ordlist_sort_nth_before:
  "\<lbrakk>i < length xs; (sort xs) ! i = x\<rbrakk> \<Longrightarrow>
   \<exists>j<length xs. xs ! j = x"
  apply (subst ordlist_sort_conv_nth)
  apply blast
  done

lemma suf_sort_suf_nth:
  "i < length s \<Longrightarrow>
   suffix s (length s - length ((sort (gen_suffixes s)) ! i)) = 
   sort (gen_suffixes s) ! i"
proof -
  assume "i < length s"


  have "\<exists>x. sort (gen_suffixes s) ! i = x"
    by blast
  then obtain x where
    "sort (gen_suffixes s) ! i = x"
    by blast
  with ordlist_sort_nth_before[of i "gen_suffixes s" x]
  have "\<exists>j<length (gen_suffixes s). gen_suffixes s ! j = x"
    by (simp add: \<open>i < length s\<close>)
  then obtain j where
    "j < length (gen_suffixes s)"
    "gen_suffixes s ! j = x"
    by blast
  hence "sort (gen_suffixes s) ! i = gen_suffixes s ! j"
    using \<open>sort (gen_suffixes s) ! i = x\<close> by blast
  moreover
  have "j < length s"
    using \<open>j < length (gen_suffixes s)\<close> by auto
  hence "gen_suffixes s ! j = suffix s j"
    by simp
  ultimately show ?thesis
    by (metis \<open>j < length s\<close> suf_suffix_id_suf)
qed

lemma map_suf_simple_saca:
  "map (suffix s) (simple_saca s) = sort (gen_suffixes s)"
  apply (simp only: simple_saca.simps suffix_ids.simps)
  apply (subst list_eq_iff_nth_eq)
  apply (rule conjI)
   apply simp
  apply (clarsimp simp del:  gen_suffixes.simps)
  apply (rule suf_sort_suf_nth; simp)
  done

interpretation simple_saca: Suffix_Array_General simple_saca
proof
  fix s :: "('a :: {linorder, order_bot}) list"

  show "simple_saca s <~~> [0..<length s]"
  proof -
    have "set (simple_saca s) = {0..<length s}"
      by force
    with perm_distinct_set_of_upt_iff[THEN iffD2, OF conjI, OF distinct_simple_saca]
    show ?thesis
      by blast
  qed

  show "strict_sorted (map (suffix s) (simple_saca s))"
  proof -
    from `simple_saca s <~~> [0..<length s]`
    have "set (simple_saca s) = {0..<length s}"
      using perm_distinct_set_of_upt_iff by blast
    hence "\<forall>x \<in> set (simple_saca s). x < length s"
      using atLeastLessThan_iff by blast
    with distinct_simple_saca  distinct_suffixes
    have "distinct (map (suffix s) (simple_saca s))"
      by blast

    have "sorted (map (suffix s) (simple_saca s))"
      by (metis map_suf_simple_saca sorted_sort)
    with `distinct (map (suffix s) (simple_saca s))` show ?thesis
      using strict_sorted_iff by blast
  qed
qed

end