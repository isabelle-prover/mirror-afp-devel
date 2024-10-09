theory Suffix_Array_Properties
imports 
  "../util/Fun_Util"
  "../order/Suffix_Util"
  "Suffix_Array"
          
begin

section \<open>General Suffix Array Properties\<close>

context Suffix_Array_General begin

lemma sa_length:
  "length (sa s) = length s"
  by (metis Suffix_Array_General_axioms Suffix_Array_General_def length_upt minus_nat.diff_0
            perm_length)

lemma sa_distinct:
  "distinct (sa s)"
  using Suffix_Array_General.sa_g_permutation Suffix_Array_General_axioms
        perm_distinct_set_of_upt_iff by blast

lemma sa_set_upt:
  "set (sa s) = {0..<length s}"
  using Suffix_Array_General.sa_g_permutation Suffix_Array_General_axioms
        perm_distinct_set_of_upt_iff by blast

lemma sa_nth_ex:
  "i < length s \<Longrightarrow> \<exists>k < length s. sa s ! i = k"
  by (metis atLeastLessThan_iff nth_mem sa_length sa_set_upt)

lemma ex_sa_nth:
  "k < length s \<Longrightarrow> \<exists>i < length s. sa s ! i = k"
  by (metis atLeast0LessThan in_set_conv_nth lessThan_iff sa_length sa_set_upt)

end (* of context *)

lemma Suffix_Array_General_determinism:
  assumes "Suffix_Array_General f"
  and     "Suffix_Array_General g"
shows "f = g"
proof
  fix s
  from distinct_suffixes[OF Suffix_Array_General.sa_distinct[OF assms(1)], of s s]
       Suffix_Array_General.sa_set_upt[OF assms(1), of s]
  have "distinct (map (suffix s) (f s))"
    using atLeastLessThan_iff by blast
  moreover
  from distinct_suffixes[OF Suffix_Array_General.sa_distinct[OF assms(2)], of s s]
       Suffix_Array_General.sa_set_upt[OF assms(2), of s]
  have "distinct (map (suffix s) (g s))"
    using atLeastLessThan_iff by blast
  moreover
  from Suffix_Array_General.sa_set_upt[OF assms(1), of s]
       Suffix_Array_General.sa_set_upt[OF assms(2), of s]
  have "set (map (suffix s) (f s)) = set (map (suffix s) (g s))"
    by simp
  ultimately have "map (suffix s) (f s) = map (suffix s) (g s)"
    using strict_sorted_distinct_set_unique[
            OF Suffix_Array_General.sa_g_sorted[of f, OF assms(1)] _
               Suffix_Array_General.sa_g_sorted[of g, OF assms(2)],
            of s s]
    by blast
  moreover
  from Suffix_Array_General.sa_set_upt[OF assms(1), of s]
       Suffix_Array_General.sa_set_upt[OF assms(2), of s]
  have "inj_on (suffix s) (set (f s) \<union> set (g s))"
    by (simp add: inj_on_def suffix_eq_index)
  ultimately show "f s = g s"
    using map_inj_on[of "suffix s" "f s" "g s"]
    by blast
qed

section \<open>Properties of Suffix Arrays on Valid Lists\<close>

lemma  valid_list_bot_min:
  assumes "valid_list (s @ [bot])"
  and     "sa (s @ [bot]) <~~> [0..<length (s @ [bot])]"
  and     "strict_sorted (map (suffix (s @ [bot])) (sa (s @ [bot])))"
shows "\<exists>xs. sa (s @ [bot]) = length s # xs"
proof -
  have "suffix (s @ [bot]) (length s) = [bot]"
    by simp

  have P: "\<forall>i < length s. suffix (s @ [bot]) (length s) < suffix (s @ [bot]) i"
  proof(safe)
    fix i
    assume "i < length s"
    have "\<exists>a as. suffix (s @ [bot]) i = a # as \<and> a \<noteq> bot"
      by (metis Cons_nth_drop_Suc \<open>i < length s\<close> assms(1) butlast_snoc length_append_singleton
                less_SucI nth_butlast valid_list_ex_def)
    then obtain a as where
      "suffix (s @ [bot]) i = a # as \<and> a \<noteq> bot"
      by blast
    moreover
    from \<open>suffix (s @ [bot]) (length s) = [bot]\<close>
    have "suffix (s @ [bot]) (length s) = bot # []"
      by simp
    ultimately show "suffix (s @ [bot]) (length s) < suffix (s @ [bot]) i"
      by (simp add: bot.not_eq_extremum)
  qed

  have "Min (set (map (suffix (s @ [bot])) (sa (s @ [bot]))))
          = suffix (s @ [bot]) (length s)"
  proof (intro Min_eqI)
    show "finite (set (map (suffix (s @ [bot])) (sa (s @ [bot]))))"
      by blast
  next
    fix y
    assume "y \<in> set (map (suffix (s @ [bot])) (sa (s @ [bot])))"
    with set_perm_upt[OF assms(2)]
    have "\<exists>i < length (s @ [bot]). y = suffix (s @ [bot]) i"
      by auto
    then obtain i where
      "i < length (s @ [bot])"
      "y = suffix (s @ [bot]) i"
      by blast
    hence "i < length s \<or> i = length s"
      by (simp add: less_Suc_eq)
    moreover
    have "i < length s \<Longrightarrow> suffix (s @ [bot]) (length s) < y"
      using P \<open>y = suffix (s @ [bot]) i\<close> dual_order.strict_iff_order by blast
    moreover
    have "i = length s \<Longrightarrow> suffix (s @ [bot]) (length s) \<le> y"
      by (simp add: \<open>y = suffix (s @ [bot]) i\<close>)
    ultimately show "suffix (s @ [bot]) (length s) \<le> y"
      using nless_le by blast
  next
    from assms
    have "length s \<in> set (sa (s @ [bot]))"
      by (metis ex_perm_nth length_append_singleton lessI nth_mem perm_upt_length)
    then show "suffix (s @ [bot]) (length s) \<in> set (map (suffix (s @ [bot])) (sa (s @ [bot])))"
      by force
  qed
  hence "map (suffix (s @ [bot])) (sa (s @ [bot])) ! 0 = suffix (s @ [bot]) (length s)"
    using assms(2,3) strict_sorted_Min by fastforce
  hence "suffix (s @ [bot]) ((sa (s @ [bot])) ! 0) = suffix (s @ [bot]) (length s)"
    by (metis assms(1,2) nth_map perm_upt_length valid_list_length)
  hence "(sa (s @ [bot])) ! 0 = length s"
    by (metis Suc_le_eq \<open>suffix (s @ [bot]) (length s) = [bot]\<close> assms(1) drop_all last_suffix_index
              list.distinct(1) list.sel(1) not_less_eq_eq)
  then show ?thesis
    by (metis append_eq_Cons_conv assms(1,2) id_take_nth_drop perm_upt_length take0
              valid_list_length)
qed

lemma valid_list_bot_perm:
  assumes "valid_list (s @ [bot])"
  and     "sa (s @ [bot]) <~~> [0..<length (s @ [bot])]"
  and     "strict_sorted (map (suffix (s @ [bot])) (sa (s @ [bot])))"
shows "\<exists>xs. sa (s @ [bot]) = length s # xs \<and> xs <~~> [0..<length s]"
proof -
  from valid_list_bot_min[OF assms(1), of sa, OF assms(2,3)]
  obtain xs where
    "sa (s @ [bot]) = length s # xs"
    by blast
  with assms(2)
  have "length s # xs <~~> [0..<length (s @ [bot])]"
    by simp
  then show ?thesis
    by (metis \<open>sa (s @ [bot]) = length s # xs\<close> assms(1) length_append_singleton less_Suc_eq_le
              perm_append2_eq perm_append_single upt_Suc valid_list_length)
qed

lemma valid_list_bot_perm_sort:
  assumes "valid_list (s @ [bot])"
  and     "sa (s @ [bot]) <~~> [0..<length (s @ [bot])]"
  and     "strict_sorted (map (suffix (s @ [bot])) (sa (s @ [bot])))"
shows "\<exists>xs. sa (s @ [bot]) = length s # xs \<and> xs <~~> [0..<length s] \<and>
            strict_sorted (map (suffix s) xs)"
proof -
  from valid_list_bot_perm[OF assms(1), of sa, OF assms(2,3)]
  obtain xs where
    "sa (s @ [bot]) = length s # xs"
    "xs <~~> [0..<length s]"
    by blast
  with assms(3)
  have "strict_sorted (map (suffix (s @ [bot])) (length s # xs))"
    by simp
  hence "strict_sorted ((suffix (s @ [bot]) (length s)) # map (suffix (s @ [bot])) xs)"
    by simp
  hence P: "strict_sorted (map (suffix (s @ [bot])) xs)"
    using strict_sorted_simps(2) by blast

  have "strict_sorted (map (suffix s) xs)"
  proof (intro sorted_wrt_mapI)
    fix i j
    assume "i < j" "j < length xs"
    with sorted_wrt_nth_less[OF P, of i j]
    have "suffix (s @ [bot]) (xs ! i) < suffix (s @ [bot]) (xs ! j)"
      by auto
    moreover
    have "xs ! i < length s"
      using \<open>i < j\<close> \<open>j < length xs\<close> \<open>xs <~~> [0..<length s]\<close> perm_distinct_set_of_upt_iff by auto
    hence "suffix (s @ [bot]) (xs ! i) = suffix s (xs ! i) @ [bot]"
      using suffix_app by blast
    moreover
    have "xs ! j < length s"
      using \<open>j < length xs\<close> \<open>xs <~~> [0..<length s]\<close> perm_distinct_set_of_upt_iff by auto
    hence "suffix (s @ [bot]) (xs ! j) = suffix s (xs ! j) @ [bot]"
      using suffix_app by blast
    moreover
    have "valid_list (suffix s (xs ! i) @ [bot])"
      using \<open>xs ! i < length s\<close> assms valid_suffix by fastforce
    moreover
    have "valid_list (suffix s (xs ! j) @ [bot])"
      using \<open>xs ! j < length s\<close> assms valid_suffix by fastforce
    ultimately show "suffix s (xs ! i) < suffix s (xs ! j)"
      by (simp add: valid_list_list_less_imp)
  qed
  with \<open>sa (s @ [bot]) = length s # xs\<close> \<open>xs <~~> [0..<length s]\<close>
  show ?thesis
    by blast
qed

theorem Suffix_Array_Restricted_valid_list_bot_perm_sort:
  assumes "valid_list (s @ [bot])"
  and     "Suffix_Array_Restricted sa"
shows "\<exists>xs. sa (s @ [bot]) = length s # xs \<and> xs <~~> [0..<length s] \<and>
            strict_sorted (map (suffix s) xs)"
proof (rule valid_list_bot_perm_sort[OF assms(1)])
  from assms
  show "sa (s @ [bot]) <~~> [0..<length (s @ [bot])]"
    using Suffix_Array_Restricted_def by blast
next
  from assms
  show "strict_sorted (map (suffix (s @ [bot])) (sa (s @ [bot])))"
    using Suffix_Array_Restricted_def by blast
qed

lemma Suffix_Array_Restricted_wrapper_permutation:
  assumes "Linorder_to_Nat_List \<alpha> s"
  and "Suffix_Array_Restricted sa"
shows "sa_nat_wrapper \<alpha> sa s <~~> [0..<length s]"
proof -
  let ?\<alpha> = "\<alpha> s"
  let ?f = "\<lambda>x. Suc (?\<alpha> x)"
  let ?s = "map ?f s"

  have "valid_list (?s @ [bot])"
    using valid_list_Suc_mapping by blast
  with Suffix_Array_Restricted_valid_list_bot_perm_sort[OF _ \<open>Suffix_Array_Restricted _\<close>]
  obtain xs where
    "sa (?s @ [bot]) = length ?s # xs"
    "xs <~~> [0..<length ?s]"
    "strict_sorted (map (suffix ?s) xs)"
    by blast
  then show ?thesis
    by (simp add: sa_nat_wrapper_def)
qed

lemma Suffix_Array_Restricted_wrapper_sorted:
  assumes "Linorder_to_Nat_List \<alpha> s"
  and "Suffix_Array_Restricted sa"
shows "strict_sorted (map (suffix s) (sa_nat_wrapper \<alpha> sa s))"
proof -
  let ?\<alpha> = "\<alpha> s"
  let ?f = "\<lambda>x. Suc (?\<alpha> x)"
  let ?s = "map ?f s"

  have "valid_list (?s @ [bot])"
    using valid_list_Suc_mapping by blast
  with Suffix_Array_Restricted_valid_list_bot_perm_sort[OF _ \<open>Suffix_Array_Restricted _\<close>]
  obtain xs where A:
    "sa (?s @ [bot]) = length ?s # xs"
    "xs <~~> [0..<length ?s]"
    "strict_sorted (map (suffix ?s) xs)"
    by blast
  hence "xs <~~> [0..<length s]"
    by simp
  with ordlist_strict_mono_on_strict_sorted_1[
        OF Linorder_to_Nat_List.strict_mono_on_Suc_map_to_nat[OF assms(1)] _ A(3)]
  show ?thesis
    by (simp add: A(1) sa_nat_wrapper_def)
qed

section \<open>Equivalence\<close>

lemma Suffix_Array_General_imp_Restrict:
  "Suffix_Array_General sa_nat \<Longrightarrow> Suffix_Array_Restricted sa_nat"
  using Suffix_Array_General_def Suffix_Array_Restricted.intro by blast

interpretation Linorder_to_Nat_List map_to_nat
proof
  show "strict_mono_on (set xs) (map_to_nat xs)"
    by (simp add: map_to_nat_strict_mono_on)
qed

lemma Suffix_Array_Restricted_imp_General:
  "Suffix_Array_Restricted sa \<Longrightarrow> Suffix_Array_General (sa_nat_wrapper map_to_nat sa)"
  using Linorder_to_Nat_List_axioms Suffix_Array_General_def
        Suffix_Array_Restricted_wrapper_permutation Suffix_Array_Restricted_wrapper_sorted by blast

lemma Suffix_Array_General_Restrict_determinism:
  assumes "Suffix_Array_Restricted f"
  and     "Suffix_Array_General g"
shows "sa_nat_wrapper map_to_nat f = g"
  by (simp add: Suffix_Array_General_determinism Suffix_Array_Restricted_imp_General assms)

end