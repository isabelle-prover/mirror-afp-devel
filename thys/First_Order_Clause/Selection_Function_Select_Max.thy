theory Selection_Function_Select_Max
  imports
    Maximal_Literal
    Selection_Function
begin

text\<open>Example Selection Function\<close>

context maximal_literal
begin

abbreviation select_max where
  "select_max C \<equiv>
    if \<exists>l\<in>#C. is_maximal l C \<and> is_neg l
    then {#SOME l. is_maximal l C \<and> is_neg l#}
    else {#}"

sublocale select_max: selection_function select_max
proof unfold_locales
  fix C

  {
    assume "\<exists>l\<in># C. is_maximal l C \<and> is_neg l" 

    then have "\<exists>l. is_maximal l C \<and> is_neg l"
      by blast
  
    then have "(SOME l. is_maximal l C \<and> is_neg l) \<in># C"
      by (rule someI2_ex) (simp add: maximal_in_clause)
  }

  then show "select_max C \<subseteq># C"
    by auto
next
  fix C l

  {
    assume "\<exists>l\<in>#C. is_maximal l C \<and> is_neg l" 

    then have "\<exists>l. is_maximal l C \<and> is_neg l"
      by blast
  
    then have "is_neg (SOME l. is_maximal l C \<and> is_neg l)"
      by (rule someI2_ex) simp
  }

  then show "l \<in># select_max C \<Longrightarrow> is_neg l"
    by (smt (verit, ccfv_threshold) ex_in_conv set_mset_add_mset_insert set_mset_eq_empty_iff 
        singletonD)
qed

end

end
