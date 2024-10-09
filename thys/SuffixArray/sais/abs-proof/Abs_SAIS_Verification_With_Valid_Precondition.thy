theory Abs_SAIS_Verification_With_Valid_Precondition
  imports 
    Abs_Induce_Verification
    Abs_Rename_LMS_Verification
    Abs_Extract_LMS_Verification
    Abs_Order_LMS_Verification
begin

section "SAIS General Helpers"

termination abs_sais
  by (relation "measure (\<lambda>xs. length xs)")
     (simp (no_asm_simp) 
           del: List.list.size(4) 
           add: rename_list_length length_filter_lms)+


(*
lemma abs_extract_lms_eq_lms0_seq:
  "abs_extract_lms T [0..<length T] = lms0_seq T"
  by (metis comp_apply lms_seq_0_zeroth_lms lms_seq_def)
*)

lemma abs_sais_reduced_string:
  assumes "LMS1 = lms0_seq T"
  and     "distinct LMS2"
  and     "set LMS2 = {i. abs_is_lms T i}"
  and     "ordlistns.sorted (map (lms_slice T) LMS2)"
  and     "names =  abs_rename_mapping T LMS2"
  and     "T' = rename_string LMS1 names"
shows "T' = lms_map T (lms0_suffix T)"
proof -
  let ?T' = "lms0_map T"

  have set_LMS1: "set LMS1 = {i. abs_is_lms T i}"
    using assms(1) lms0_seq_has_all_lms by blast

  have "distinct LMS1"
    by (simp add: assms(1) lms_seq_distinct)

  have "T' = map (\<lambda>x. names ! x) LMS1"
    using rename_list_correct assms(6) by auto

  have "\<forall>x \<in> set LMS2. x < length T"
    using assms(3) abs_is_lms_imp_less_length by blast
  with map_abs_rename_mapping[OF assms(2,4), simplified assms(3),
                          of LMS1, simplified \<open>LMS1 = lms0_seq T\<close>]
       \<open>T' = map (\<lambda>x. names ! x) LMS1\<close> \<open>set LMS2 = {i. abs_is_lms T i}\<close>
  have "T' = map (ordlistns.elem_rank (lms_substrs T)) (map (lms_slice T) (lms0_seq T))"
    using assms(1) assms(5) set_LMS1 by blast
  moreover
  have "map (ordlistns.elem_rank (lms_substrs T)) (map (lms_slice T) (lms0_seq T)) = ?T'"
    unfolding lms_map_def
    by (metis (no_types, opaque_lifting) comp_apply lms_substr_seq_def lms_subtrs_seq_id_suffix)
  ultimately show  "T' = ?T'"
    by (simp only:)
qed

section "SAIS cases simplifications"

lemma abs_sais_distinct_simp:
  assumes "T = a # b # xs"
  and     "LMS0 = abs_extract_lms T [0..<length T]"
  and     "SA = abs_sa_induce id T LMS0"
  and     "LMS = abs_extract_lms T SA"
  and     "names = abs_rename_mapping T LMS"
  and     "T' = rename_string LMS0 names"
  and     "distinct T'"
  shows "abs_sais T = abs_sa_induce id T LMS"
proof -
  let ?P = "\<lambda>ys. abs_sais (a # b # xs) = ys"
  from subst[OF abs_sais.simps(3), of ?P a b xs,
             simplified Let_def assms(1-6)[symmetric] assms(7),
             simplified]
  show ?thesis
    by simp
qed

lemma abs_sais_not_distinct_simp:
  assumes "T = a # b # xs"
  and     "LMS0 = abs_extract_lms T [0..<length T]"
  and     "SA = abs_sa_induce id T LMS0"
  and     "LMS = abs_extract_lms T SA"
  and     "names = abs_rename_mapping T LMS"
  and     "T' = rename_string LMS0 names"
  and     "LMS1 = order_lms LMS0 (abs_sais T')"
  and     "\<not> distinct T'"
  shows "abs_sais T = abs_sa_induce id T LMS1"
proof -
  let ?P = "\<lambda>ys. abs_sais (a # b # xs) = ys"
  from subst[OF abs_sais.simps(3), of ?P a b xs,
             simplified Let_def assms(1-7)[symmetric] assms(8),
             simplified]
  show ?thesis
    by simp
qed

section "SAIS returns a permutation"

theorem abs_sais_permutation:
  "valid_list T \<Longrightarrow> abs_sais T <~~> [0..<length T]"
proof(induct rule: abs_sais.induct[of _ T])
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 a b xs)
  note IH = this
  let ?T = "a # b # xs"
  have T: "?T = a # b # xs"
    by (simp only:)
  let ?LMS1 = "abs_extract_lms ?T [0..<length ?T]"
  have LMS1: "?LMS1 = abs_extract_lms ?T [0..<length ?T]"
    by (simp only:)
  let ?SA1 = "abs_sa_induce id ?T ?LMS1"
  have SA1: "?SA1 = abs_sa_induce id ?T ?LMS1"
    by (simp only:)
  let ?LMS2 = "abs_extract_lms ?T ?SA1"
  have LMS2: "?LMS2 = abs_extract_lms ?T ?SA1"
    by (simp only:)
  let ?names = "abs_rename_mapping ?T ?LMS2"
  have names: "?names = abs_rename_mapping ?T ?LMS2"
    by (simp only:)
  let ?T' = "rename_string ?LMS1 ?names"
  have T': "?T' = rename_string ?LMS1 ?names"
    by (simp only:)
  let ?LMS3 = "order_lms ?LMS1 (abs_sais ?T')"
  have LMS3: "?LMS3 = order_lms ?LMS1 (abs_sais ?T')"
    by (simp only:)

  from IH(1)[OF T LMS1 SA1 LMS2 names T']
  have IH': "\<lbrakk>\<not>distinct ?T'; valid_list ?T'\<rbrakk> \<Longrightarrow> abs_sais ?T' <~~> [0..<length ?T']"
    by assumption

  have "distinct ?LMS1"
    using distinct_abs_extract_lms
    by fastforce

  have "set ?LMS1 = {i. abs_is_lms ?T i}"
    using set_abs_extract_lms_eq_all_lms
    by (metis comp_apply)

  have id: "strict_mono (id :: nat \<Rightarrow> nat)" "(id :: nat \<Rightarrow> nat) bot = 0"
    by (simp add: strict_mono_def bot_nat_def)+

  have len: "Suc 0 < length ?T"
    by simp

  from distinct_filter_abs_sa_induce
        [OF `set ?LMS1 = {i. abs_is_lms ?T i}` `distinct ?LMS1` IH(2) id len]
  have distinct_LMS2: "distinct ?LMS2"
    by (metis comp_apply)

  from filter_abs_sa_induce_eq_all_lms
        [OF `set ?LMS1 = {i. abs_is_lms ?T i}` `distinct ?LMS1` IH(2) id len]
  have set_LMS2: "set ?LMS2 = {i. abs_is_lms ?T i}"
    by blast

  from abs_sa_induce_permutation
        [OF `set ?LMS2 = {i. abs_is_lms ?T i}` `distinct ?LMS2` IH(2) id len]
  have "abs_sa_induce id ?T ?LMS2 <~~> [0..<length ?T]"
    by assumption

  from rename_list_length[of ?LMS1 ?names]
  have "length ?T' = length ?LMS1"
    by assumption

  have sorted_LMS2: "ordlistns.sorted (map (lms_slice ?T) ?LMS2)"
    by (metis "3.prems" \<open>distinct ?LMS1\<close> \<open>set ?LMS1 = {i. abs_is_lms ?T i}\<close> comp_apply len id
              ordlistns.sorted_filter abs_sa_induce_prefix_sorted)

  have "?LMS1 = lms0_seq ?T"
    by (metis comp_apply lms_seq_0_zeroth_lms lms_seq_def)
  with abs_sais_reduced_string[OF _ distinct_LMS2 set_LMS2 sorted_LMS2 names T']
  have "?T' = lms0_map ?T"
    by blast

  have "abs_is_lms ?T (lms0 ?T)"
    by (metis "3.prems" abs_find_next_lms_less_length_abs_is_lms length_Cons
              abs_is_lms_last len no_lms_between_i_and_next not_less_eq)

  from valid_list_lms_map[OF IH(2) \<open>abs_is_lms ?T (lms0 ?T)\<close>]
  have "valid_list (lms0_map ?T)" .
  hence "valid_list ?T'"
    by (simp only: \<open>?T' = (lms0_map ?T)\<close>)

  from `length ?T' = length ?LMS1` `distinct ?LMS1` `set ?LMS1 = {i. abs_is_lms ?T i}`
  have R1: "abs_sais ?T' <~~> [0..<length ?T'] \<Longrightarrow> distinct ?LMS3"
    by (metis distinct_abs_order_lms)

  from `length ?T' = length ?LMS1` `distinct ?LMS1` `set ?LMS1 = {i. abs_is_lms ?T i}`
  have R2: "abs_sais ?T' <~~> [0..<length ?T'] \<Longrightarrow> set ?LMS3 = {i. abs_is_lms ?T i}"
    by (metis (no_types, lifting) abs_order_lms_eq_all_lms )

  from abs_sa_induce_permutation[OF R2 R1 IH(2) id len]
  have R3: "abs_sais ?T' <~~> [0..<length ?T'] \<Longrightarrow> 
              abs_sa_induce id ?T ?LMS3 <~~> [0..<length ?T]"
    by blast

  from IH'[OF _ `valid_list ?T'`]
  have "\<not>distinct ?T' \<Longrightarrow> abs_sais ?T' <~~> [0..<length ?T']"
    by assumption
  with R3
  have "\<not>distinct ?T' \<Longrightarrow> abs_sa_induce id ?T ?LMS3 <~~> [0..<length ?T]"
    by blast

  have "distinct ?T' \<or> \<not>distinct ?T'"
    by blast
  then show ?case
  proof
    assume A: "distinct ?T'"
    from abs_sais_distinct_simp[OF T LMS1 SA1 LMS2 names T' A]
         `abs_sa_induce id ?T ?LMS2 <~~> [0..<length ?T]`
    show ?thesis
      by metis
  next
    assume A: "\<not>distinct ?T'"
    from abs_sais_not_distinct_simp[OF T LMS1 SA1 LMS2 names T' LMS3 A]
         `\<not>distinct ?T' \<Longrightarrow> abs_sa_induce id ?T ?LMS3 <~~> [0..<length ?T]`[OF A]
    show ?thesis
      by metis
  qed
qed

section "SAIS Sorted Helpers"

lemma abs_sais_subset_idx:
  assumes "valid_list T"
  shows "set (abs_sais T) \<subseteq> {0..<length T}"
  using assms perm_distinct_set_of_upt_iff abs_sais_permutation by auto

(*
lemma length_abs_sais:
  "valid_list T \<Longrightarrow> length (abs_sais T) = length T"
  using perm_upt_length abs_sais_permutation by blast
*)

section "SAIS sorts suffixes"

theorem abs_sais_sorted_alt:
  "valid_list T \<Longrightarrow>
   ordlistns.strict_sorted (map (suffix T) (abs_sais T))"
proof(induct rule: abs_sais.induct[of _ T])
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 a b xs)
  note IH = this
  let ?T = "a # b # xs"
  have T: "?T = a # b # xs"
    by (simp only:)
  let ?LMS1 = "abs_extract_lms ?T [0..<length ?T]"
  have LMS1: "?LMS1 = abs_extract_lms ?T [0..<length ?T]"
    by (simp only:)
  let ?SA1 = "abs_sa_induce id ?T ?LMS1"
  have SA1: "?SA1 = abs_sa_induce id ?T ?LMS1"
    by (simp only:)
  let ?LMS2 = "abs_extract_lms ?T ?SA1"
  have LMS2: "?LMS2 = abs_extract_lms ?T ?SA1"
    by (simp only:)
  let ?names = "abs_rename_mapping ?T ?LMS2"
  have names: "?names = abs_rename_mapping ?T ?LMS2"
    by (simp only:)
  let ?T' = "rename_string ?LMS1 ?names"
  have T': "?T' = rename_string ?LMS1 ?names"
    by (simp only:)
  let ?LMS3 = "order_lms ?LMS1 (abs_sais ?T')"
  have LMS3: "?LMS3 = order_lms ?LMS1 (abs_sais ?T')"
    by (simp only:)

  from IH(1)[OF T LMS1 SA1 LMS2 names T']
  have IH': "\<lbrakk>\<not>distinct ?T'; valid_list ?T'\<rbrakk> \<Longrightarrow>
             ordlistns.strict_sorted (map (suffix ?T') (abs_sais ?T'))"
    by blast

  from set_abs_extract_lms_eq_all_lms[of ?T]
  have set_LMS1: "set ?LMS1 = {i. abs_is_lms ?T i}"
    by simp

  from distinct_abs_extract_lms[of ?T]
  have distinct_LMS1: "distinct ?LMS1"
    by simp

  have id: "strict_mono (id :: nat \<Rightarrow> nat)" "(id :: nat \<Rightarrow> nat) bot = 0"
    by (simp add: strict_mono_def bot_nat_def)+

  have len: "Suc 0 < length ?T"
    by simp

  from distinct_filter_abs_sa_induce[OF `set ?LMS1 = {i. abs_is_lms ?T i}` `distinct ?LMS1` IH(2) id len]
  have distinct_LMS2: "distinct ?LMS2"
    by blast

  from filter_abs_sa_induce_eq_all_lms[OF `set ?LMS1 = {i. abs_is_lms ?T i}` `distinct ?LMS1` IH(2) id len]
  have set_LMS2: "set ?LMS2 = {i. abs_is_lms ?T i}"
    by blast

  from distinct_set_imp_perm[OF `distinct ?LMS1` `distinct ?LMS2`]
       `set ?LMS1 = {i. abs_is_lms ?T i}`
       `set ?LMS2 = {i. abs_is_lms ?T i}`
  have "?LMS1 <~~> ?LMS2"
    by blast

  have sorted_LMS2: "ordlistns.sorted (map (lms_slice ?T) ?LMS2)"
    by (metis "3.prems" \<open>distinct ?LMS1\<close> \<open>set ?LMS1 = {i. abs_is_lms ?T i}\<close> comp_apply len id
              ordlistns.sorted_filter abs_sa_induce_prefix_sorted)

  have "?LMS1 = lms0_seq ?T"
    by (metis comp_apply lms_seq_0_zeroth_lms lms_seq_def)

  with abs_sais_reduced_string[OF _ distinct_LMS2 set_LMS2 sorted_LMS2 names T']
  have "?T' = lms0_map ?T"
    by blast

  have "abs_is_lms ?T (lms0 ?T)"
    by (metis "3.prems" abs_find_next_lms_less_length_abs_is_lms abs_is_lms_last 
               len length_Cons no_lms_between_i_and_next not_less_eq)

  from valid_list_lms_map[OF IH(2) \<open>abs_is_lms ?T (lms0 ?T)\<close>]
  have "valid_list (lms0_map ?T)" .
  hence "valid_list ?T'"
    by (simp only: \<open>?T' = (lms0_map ?T)\<close>)

  have "distinct ?T' \<or> \<not>distinct ?T'"
    by blast
  hence "ordlistns.sorted (map (suffix ?T) (abs_sais ?T))"
  proof
    assume A: "distinct ?T'"
    hence "distinct (lms0_map ?T)"
      by (simp only: \<open>?T' = (lms0_map ?T)\<close>)
    with sorted_distinct_lms_substr_perm[OF sorted_LMS2]
    have "ordlistns.sorted (map (suffix ?T) ?LMS2)"
      by (metis \<open>?LMS1 = lms0_seq ?T\<close> \<open>?LMS1 <~~> ?LMS2\<close>)
    with abs_sa_induce_suffix_sorted[OF set_LMS2 distinct_LMS2 IH(2) id len]
    have "ordlistns.sorted (map (suffix ?T) (abs_sa_induce id ?T ?LMS2))"
      using ordlistns.strict_sorted_imp_sorted by blast
    with abs_sais_distinct_simp[OF T LMS1 SA1 LMS2 names T' A]
    show ?thesis
      by presburger
  next
    assume A: "\<not>distinct ?T'"
    with IH'[OF _ \<open>valid_list ?T'\<close>]
    have "ordlistns.strict_sorted (map (suffix ?T') (abs_sais ?T'))"
      by blast
    hence C1: "ordlistns.strict_sorted (map (suffix (lms0_map ?T)) (abs_sais (lms0_map ?T)))"
      by (simp only: \<open>?T' = (lms0_map ?T)\<close>)

    from abs_order_lms_eq_map_nth[of ?LMS1 "abs_sais ?T'"] 
         \<open>?LMS1 = lms0_seq ?T\<close> \<open>?T' = lms0_map ?T\<close>
    have C2: "order_lms ?LMS1 (abs_sais ?T') = 
              map (nth (lms0_seq ?T)) (abs_sais (lms0_map ?T))"
      by (simp only:)

    note perm = abs_sais_permutation[OF \<open>valid_list ?T'\<close>,
                                  simplified rename_list_length]

    note set_LMS3 = abs_order_lms_eq_all_lms[OF perm set_LMS1]
    note distinct_LMS3 = distinct_abs_order_lms[OF perm distinct_LMS1]

    from abs_sais_permutation[OF \<open>valid_list (lms0_map ?T)\<close>]
    have "\<forall>y \<in> set (abs_sais (lms0_map ?T)). y < card {i. abs_is_lms ?T i}"
      by (metis atLeastLessThan_iff card_lms_suffixes length_reduced_seq perm_set_eq set_upt)
    with sorted_reduced_seq_imp_lms[OF C1] C2
    have "ordlistns.strict_sorted (map (suffix ?T) ?LMS3)"
      by presburger
    with abs_sa_induce_suffix_sorted[OF set_LMS3 distinct_LMS3 IH(2) id len]
    have "ordlistns.sorted (map (suffix ?T) (abs_sa_induce id ?T ?LMS3))"
      using ordlistns.strict_sorted_imp_sorted by blast
    with abs_sais_not_distinct_simp[OF T LMS1 SA1 LMS2 names T' LMS3 A]
    show ?thesis
      by presburger
  qed
  moreover
  from perm_distinct_set_of_upt_iff[THEN iffD1, OF abs_sais_permutation[OF IH(2)]]
  have "distinct (map (suffix ?T) (abs_sais ?T))"
    by (metis atLeastLessThan_iff distinct_suffixes)
  ultimately show ?case
    using ordlistns.strict_sorted_iff by blast
qed

theorem abs_sais_sorted:
  "valid_list T \<Longrightarrow>
   strict_sorted (map (suffix T) (abs_sais T))"
  using abs_sais_sorted_alt abs_sais_subset_idx valid_list_ordlist_ordlistns_strict_sorted_eq by blast

section "Verification of a SAIS construction algorithm"

interpretation abs_sais: Suffix_Array_Restricted "abs_sais"
  using Suffix_Array_Restricted.intro abs_sais_permutation abs_sais_sorted by blast


end