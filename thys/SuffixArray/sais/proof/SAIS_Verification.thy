theory SAIS_Verification
  imports 
      Get_Types_Verification 
      Induce_Verification
      "../abs-proof/Abs_SAIS_Verification_With_Valid_Precondition" 
      "../def/SAIS"
          
begin

section "SAIS"

termination sais_r0
  apply (relation "measure (\<lambda>xs. length xs)")
   apply simp
  apply (simp (no_asm_simp) 
              del: List.list.size(4)
              only: extract_lms_eq[OF length_get_suffix_types get_suffix_types_correct]
                    rename_mapping_refinement[OF length_get_suffix_types 
                    get_suffix_types_correct] get_suffix_types_eq)
  apply (simp (no_asm_simp) 
            del: List.list.size(4) 
            add: rename_list_length length_filter_lms)
  done

lemma abs_sais_r0_distinct_simp:
  assumes "T = a # b # xs"
  and     "ST = abs_get_suffix_types T"
  and     "LMS0 = extract_lms ST [0..<length T]"
  and     "SA = sa_induce id T ST LMS0"
  and     "LMS = extract_lms ST SA"
  and     "names = rename_mapping T ST LMS"
  and     "T' = rename_string LMS0 names"
  and     "distinct T'"
  shows "sais_r0 T = sa_induce id T ST LMS"
proof -
  let ?P = "\<lambda>ys. sais_r0 (a # b # xs) = ys"
  from subst[OF sais_r0.simps(3), of ?P a b xs, simplified Let_def
        assms(1-7)[symmetric] assms(8), simplified]
  show ?thesis
    by simp
qed

lemma abs_sais_r0_not_distinct_simp:
  assumes "T = a # b # xs"
  and     "ST = abs_get_suffix_types T"
  and     "LMS0 = extract_lms ST [0..<length T]"
  and     "SA = sa_induce id T ST LMS0"
  and     "LMS = extract_lms ST SA"
  and     "names = rename_mapping T ST LMS"
  and     "T' = rename_string LMS0 names"
  and     "LMS1 = order_lms LMS0 (sais_r0 T')"
  and     "\<not>distinct T'"
  shows "sais_r0 T = sa_induce id T ST LMS1"
proof -
  let ?P = "\<lambda>ys. sais_r0 (a # b # xs) = ys"
  from subst[OF sais_r0.simps(3), of ?P a b xs, simplified Let_def
        assms(1-8)[symmetric] assms(9), simplified]
  show ?thesis
    by simp
qed

lemma abs_sais_to_r0:
  "valid_list T \<Longrightarrow> abs_sais T = sais_r0 T"
proof(induct rule: abs_sais.induct[of _ T])
  case 1
  then show ?case
    by simp
next
  case (2 x)
  then show ?case
    by simp
next
  case (3 a b xs)
  note IH = this

  let ?T = "a # b # xs"
  have T: "?T = a # b # xs"
    by (simp only:)

 let ?ST = "abs_get_suffix_types ?T"
  have ST: "?ST = abs_get_suffix_types ?T"
    by (simp only:)
  from get_suffix_types_correct[of ?T] length_abs_get_suffix_types[of ?T]
  have "\<forall>i < length ?ST. ?ST ! i = suffix_type ?T i"
    by (simp add: get_suffix_types_eq)
  note st_thms = length_get_suffix_types[of ?T] 
                 `\<forall>i < length ?ST. ?ST ! i = suffix_type ?T i`

  let ?LMS1 = "abs_extract_lms ?T [0..<length ?T]"
  let ?LMS1' = "extract_lms ?ST [0..<length ?T]"
  have LMS1: "?LMS1 = abs_extract_lms ?T [0..<length ?T]"
    by (simp only:)
  have LMS1': "?LMS1' = extract_lms ?ST [0..<length ?T]"
    by (simp only:)
  have "distinct ?LMS1"
    using distinct_abs_extract_lms
    by fastforce
  have "set ?LMS1 = {i. abs_is_lms ?T i}"
    using set_abs_extract_lms_eq_all_lms
    by (metis comp_apply)
  have "?LMS1 = ?LMS1'"
    by (metis extract_lms_eq get_suffix_types_correct length_get_suffix_types)
  note lms1_thms = `set ?LMS1 = {i. abs_is_lms ?T i}` `distinct ?LMS1` `?LMS1 = ?LMS1'`

  have id: "strict_mono (id :: nat \<Rightarrow> nat)" "(id :: nat \<Rightarrow> nat) bot = 0"
    by (simp add: strict_mono_def bot_nat_def)+

  have len: "Suc 0 < length ?T"
    by simp

  let ?SA1 = "abs_sa_induce id ?T ?LMS1"
  have SA1: "?SA1 = abs_sa_induce id ?T ?LMS1"
    by (simp only:)
  let ?SA1' = "sa_induce id ?T ?ST ?LMS1'"
  have SA1': "?SA1' = sa_induce id ?T ?ST ?LMS1'"
    by (simp only:)
  have "?SA1 = ?SA1'"
    by (metis "3.prems" len lms1_thms id  st_thms abs_sa_induce_to_r2)

  let ?LMS2 = "abs_extract_lms ?T ?SA1"
  let ?LMS2' = "extract_lms ?ST ?SA1'"
  have LMS2: "?LMS2 = abs_extract_lms ?T ?SA1"
    by (simp only:)
  have LMS2': "?LMS2' = extract_lms ?ST ?SA1'"
    by (simp only:)
  have "?LMS2 = ?LMS2'"
    using `?SA1 = ?SA1'` st_thms comp_apply is_lms_refinement 
    by (metis (no_types, lifting) get_suffix_types_eq)
  have "?LMS1 <~~> ?LMS2"
    by (metis "3.prems" distinct_filter_abs_sa_induce lms1_thms len id
              distinct_set_imp_perm filter_abs_sa_induce_eq_all_lms)
  hence "distinct ?LMS2" "set ?LMS2 = {i. abs_is_lms ?T i}"
    using lms1_thms perm_distinct_iff perm_set_eq by blast+
  have "ordlistns.sorted (map (lms_slice ?T) ?LMS2)"
    by (metis "3.prems" \<open>distinct ?LMS1\<close> \<open>set ?LMS1 = {i. abs_is_lms ?T i}\<close> comp_apply len id
              ordlistns.sorted_filter abs_sa_induce_prefix_sorted)
  note lms2_thms = \<open>distinct ?LMS2\<close> \<open>set ?LMS2 = {i. abs_is_lms ?T i}\<close>
                   \<open>ordlistns.sorted (map (lms_slice ?T) ?LMS2)\<close>
                   \<open>?LMS2 = ?LMS2'\<close>

  let ?names = "abs_rename_mapping ?T ?LMS2"
  let ?names' = "rename_mapping ?T ?ST ?LMS2'"
  have names: "?names = abs_rename_mapping ?T ?LMS2"
    by (simp only:)
  have names': "?names' = rename_mapping ?T ?ST ?LMS2'"
    by (simp only:)
  have "?names = ?names'"
    by (metis st_thms lms2_thms(4) rename_mapping_refinement)

  let ?T' = "rename_string ?LMS1 ?names"
  let ?T'' = "rename_string ?LMS1' ?names'"
  have T': "?T' = rename_string ?LMS1 ?names"
    by (simp only:)
  have T'': "?T'' = rename_string ?LMS1' ?names'"
    by (simp only:)
  have "?T' = ?T''"
    using \<open>?names = ?names'\<close> lms1_thms(3) by argo

  let ?LMS3 = "order_lms ?LMS1 (abs_sais ?T')"
  let ?LMS3' = "order_lms ?LMS1' (sais_r0 ?T'')"
  have LMS3: "?LMS3 = order_lms ?LMS1 (abs_sais ?T')"
    by (simp only:)
  have LMS3': "?LMS3' = order_lms ?LMS1' (sais_r0 ?T'')"
    by (simp only:)

  have "?LMS1 = lms0_seq ?T"
    by (metis comp_apply lms_seq_0_zeroth_lms lms_seq_def)
  with abs_sais_reduced_string[OF _ lms2_thms(1-3) names T']
  have "?T' = lms0_map ?T"
    by blast

  have "abs_is_lms ?T (lms0 ?T)"
    by (metis "3.prems" abs_find_next_lms_less_length_abs_is_lms abs_is_lms_last 
              len length_Cons no_lms_between_i_and_next not_less_eq)

  from valid_list_lms_map[OF IH(2) \<open>abs_is_lms ?T (lms0 ?T)\<close>]
  have "valid_list (lms0_map ?T)" .
  hence "valid_list ?T'"
    by (simp only: \<open>?T' = (lms0_map ?T)\<close>)

  have "distinct ?T' \<Longrightarrow> ?case"
  proof -
    assume "distinct ?T'"
    hence "distinct ?T''"
      by (simp only: `?T' = ?T''`)
    note lms2_thms = filter_abs_sa_induce_eq_all_lms[OF lms1_thms(1,2) IH(2) id len]
                     distinct_filter_abs_sa_induce[OF lms1_thms(1,2) IH(2) id len]
    from abs_sa_induce_to_r2 lms2_thms(1,2) IH(2) id len st_thms
    have "abs_sa_induce id ?T ?LMS2 = sa_induce id ?T ?ST ?LMS2'"
      by (metis `?LMS2 = ?LMS2'` comp_apply)
    with abs_sais_distinct_simp[OF T LMS1 SA1 LMS2 names T' `distinct ?T'`]
         abs_sais_r0_distinct_simp[OF T ST LMS1' SA1' LMS2' names' T'' `distinct ?T''`]
    show ?thesis
      by presburger
  qed
  moreover
  have "\<not>distinct ?T' \<Longrightarrow> ?case"
  proof -
    assume "\<not>distinct ?T'"
    hence "\<not>distinct ?T''"
      using `?T' = ?T''` by argo

    from IH(1)[OF T LMS1 SA1 LMS2 names T', OF `\<not>distinct ?T'` `valid_list ?T'`]
    have "abs_sais ?T' = sais_r0 ?T''"
      using \<open>?T' = ?T''\<close> by argo
    hence "?LMS3' = ?LMS3"
      using lms1_thms(3) by argo

    have abs_sais_perm: "abs_sais ?T' <~~> [0..<length ?LMS1]"
      using abs_sais_permutation[OF `valid_list ?T'`, simplified rename_list_length]
      by blast

    note lms3_thms = abs_order_lms_eq_all_lms[OF abs_sais_perm lms1_thms(1)]
                     distinct_abs_order_lms[OF abs_sais_perm lms1_thms(2)]
    from abs_sa_induce_to_r2[OF lms3_thms \<open>valid_list ?T\<close> id len st_thms]
    have "abs_sa_induce id ?T ?LMS3 = sa_induce id ?T ?ST ?LMS3'"
      using \<open>abs_sais ?T' = sais_r0 ?T''\<close> lms1_thms(3) by argo
    with abs_sais_not_distinct_simp[OF T LMS1 SA1 LMS2 names T' LMS3 `\<not>distinct ?T'`]
         abs_sais_r0_not_distinct_simp[OF T ST LMS1' SA1' LMS2' names' T'' LMS3' `\<not>distinct ?T''`]
         `abs_sais ?T' = sais_r0 ?T'`
    show ?thesis
     by presburger
  qed
  ultimately show ?case
    by blast
qed

termination sais_r1
  apply (relation "measure (\<lambda>xs. length xs)")
   apply simp
  apply (simp (no_asm_simp) 
              del: List.list.size(4)
              only: extract_lms_eq[OF length_abs_get_suffix_types get_suffix_types_correct]
                    rename_mapping_refinement[OF length_abs_get_suffix_types get_suffix_types_correct])
  apply (simp (no_asm_simp)
              del: List.list.size(4) 
              add: rename_list_length length_filter_lms)
  apply (metis get_suffix_types_correct get_suffix_types_eq is_lms_refinement 
               length_filter_lms length_get_suffix_types list.discI)
  done

lemma abs_sais_r0_to_r1:
  "sais_r1 T = sais_r0 T"
  apply (induct rule: sais_r0.induct[of _ T])
    apply simp
   apply simp
  apply (subst sais_r1.simps)
  apply (subst get_suffix_types_eq)
  apply (subst sais_r0.simps)
  apply (clarsimp simp only: Let_def split: if_splits)
  by presburger

lemma abs_sais_to_r1:
  "valid_list T \<Longrightarrow> sais_r1 T = abs_sais T"
  by (simp add: abs_sais_r0_to_r1 abs_sais_to_r0)


section "Correctness"

interpretation sais: Suffix_Array_Restricted sais
  by (simp add: Suffix_Array_Restricted.intro Suffix_Array_Restricted.sa_r_permutation
                Suffix_Array_Restricted.sa_r_sorted abs_sais.Suffix_Array_Restricted_axioms abs_sais_to_r1)

interpretation abs_sais_ref_gen: Suffix_Array_General "sa_nat_wrapper map_to_nat sais"
  by (simp add: Suffix_Array_Restricted_imp_General sais.Suffix_Array_Restricted_axioms)

theorem sais_gen_is_Suffix_Array_General:
  "Suffix_Array_General sa \<longleftrightarrow> sa = sa_nat_wrapper map_to_nat sais"
  using Suffix_Array_General_determinism abs_sais_ref_gen.Suffix_Array_General_axioms by auto

end