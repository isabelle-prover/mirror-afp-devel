(*by Lammich*)
section \<open>Imperative Interface\<close>
theory VEBT_Intf_Imperative
  imports 
  VEBT_Definitions
  VEBT_Uniqueness
  VEBT_Member 
  VEBT_Insert VEBT_InsertCorrectness 
  VEBT_MinMax 
  VEBT_Pred VEBT_Succ  
  VEBT_Delete VEBT_DeleteCorrectness 
  VEBT_Bounds
  VEBT_DeleteBounds
  VEBT_Space
  VEBT_Intf_Functional
  VEBT_List_Assn
  VEBT_BuildupMemImp 
  VEBT_SuccPredImperative
  VEBT_DelImperative
begin

  subsection \<open>Code Export\<close>

  context begin 
    interpretation VEBT_internal .
  
    lemmas [code] = replicatei.simps vebt_memberi.simps highi_def lowi_def vebt_inserti.simps
      minNulli.simps vebt_succi.simps vebt_predi.simps vebt_deletei.simps
  
      greater.simps 
      
  end  
    
  
  export_code 
    vebt_buildupi
    vebt_memberi
    vebt_inserti
    vebt_maxti vebt_minti
    vebt_predi vebt_succi 
    vebt_deletei
  
   checking SML_imp
  
  subsection \<open>Interface\<close> 
  
definition vebt_assn::"nat \<Rightarrow> nat set \<Rightarrow> VEBTi \<Rightarrow> assn" where
"vebt_assn n s ti \<equiv> \<exists>\<^sub>A t. vebt_assn_raw t ti * \<up>(s = set_vebt t \<and> invar_vebt t n)"
  
  
subsubsection \<open>Buildup\<close>

context begin
  interpretation VEBT_internal .
  
  interpretation vebt_inst for n .  


lemma vebt_buildupi_rule_basic[sep_heap_rules]: "n > 0 \<Longrightarrow> <emp> vebt_buildupi n <\<lambda> r. vebt_assn n {} r >"
  unfolding vebt_assn_def 
  apply(rule  post_exI_rule[where x = "vebt_buildup n"])
  using builupicorr[of n] invar_vebt_buildup[of n] set_vebt_buildup[of n]
  apply simp
  done

lemma vebt_buildupi_rule: "<\<up> (n > 0)> vebt_buildupi  n <\<lambda> r. vebt_assn n {} r > T[10 * 2^n]"  
  unfolding vebt_assn_def htt_def
  apply rule
  apply(rule  post_exI_rule[where x = "vebt_buildup n"])
  using vebt_buildupi_rule[of n] invar_vebt_buildup[of  n] set_vebt_buildup[of n] 
  unfolding htt_def 
   apply simp
  using TBOUND_buildupi[of n] unfolding TBOUND_def
  apply simp
  done

subsubsection \<open>Member\<close>
lemma vebt_memberi_rule: "<vebt_assn n s ti> vebt_memberi ti x <\<lambda> r. vebt_assn n s ti *  \<up>(r = (x \<in> s))>T[5 + 5 * (nat \<lceil>lb n \<rceil>)]"
  unfolding vebt_assn_def 
  apply(rule norm_pre_ex_rule_htt) 
  apply(clarsimp simp: norm_pre_pure_iff_htt)
  apply(rule htt_cons_rule[OF htt_vebt_memberi_invar_vebt])
     apply assumption
    apply simp
   apply (sep_auto simp: member_correct)
  apply simp
  done

  
subsubsection \<open>Insert\<close>  
lemma vebt_inserti_rule: "x < 2^n \<Longrightarrow> <vebt_assn n s ti> vebt_inserti ti x <\<lambda> r. vebt_assn n (s \<union> {x}) r >T[13 + 13 * (nat \<lceil>lb n \<rceil>)]"
  apply(sep_auto simp: norm_pre_pure_iff_htt)
  unfolding vebt_assn_def
  apply(rule norm_pre_ex_rule_htt) 
  apply(clarsimp simp: norm_pre_pure_iff_htt)
  apply(rule htt_cons_rule[OF htt_vebt_inserti_invar_vebt])
     apply assumption
    apply simp
   apply sep_auto
      apply (auto simp add: insert_correct) 
     apply (simp add: valid_insert_both_member_options_add set_vebt_def)
    apply (metis UnCI insert_correct)
   apply (metis UnE insert_correct singletonD)
  using valid_pres_insert by presburger


subsubsection \<open>Maximum\<close>  
lemma vebt_maxti_rule: "<vebt_assn n s ti> vebt_maxti ti <\<lambda> r. vebt_assn n s ti *  \<up>( r = Some y \<longleftrightarrow> max_in_set s y)>T[1]"
  unfolding vebt_assn_def 
  apply(rule norm_pre_ex_rule_htt) 
  apply(clarsimp simp: norm_pre_pure_iff_htt)
  apply(rule htt_cons_rule[OF vebt_maxti_hT])
  apply(rule ent_refl)
  apply (sep_auto simp: set_vebt_maxt)
  by simp
  
subsubsection \<open>Minimum\<close>  
lemma vebt_minti_rule: "<vebt_assn n s ti> vebt_minti ti <\<lambda> r. vebt_assn n s ti *  \<up>( r = Some y \<longleftrightarrow> min_in_set s y)>T[1]"
  unfolding vebt_assn_def 
  apply(rule norm_pre_ex_rule_htt) 
  apply(clarsimp simp: norm_pre_pure_iff_htt)
  apply(rule htt_cons_rule[OF vebt_minti_hT])
  apply(rule ent_refl)
  apply (sep_auto simp: set_vebt_mint)
  by auto
  
  
subsubsection \<open>Successor\<close>  
lemma vebt_succi_rule: "<vebt_assn n s ti> vebt_succi ti x <\<lambda> r. vebt_assn n s ti *  \<up>( r = Some y \<longleftrightarrow> is_succ_in_set s x y)>T[7 + 7 * (nat \<lceil>lb n \<rceil>)]"
  unfolding vebt_assn_def 
  apply(rule norm_pre_ex_rule_htt) 
  apply(clarsimp simp: norm_pre_pure_iff_htt)
  apply(rule htt_cons_rule[OF htt_vebt_succi])
  apply assumption
  apply simp
  apply (sep_auto simp: set_vebt_succ)
  apply simp
  done

subsubsection \<open>Predecessor\<close>  
lemma vebt_predi_rule: "<vebt_assn n s ti> vebt_predi ti x <\<lambda> r. vebt_assn n s ti *  \<up>( r = Some y \<longleftrightarrow> is_pred_in_set s x y)>T[7 + 7 * (nat \<lceil>lb n \<rceil>)]"
  unfolding vebt_assn_def 
  apply(rule norm_pre_ex_rule_htt) 
  apply(clarsimp simp: norm_pre_pure_iff_htt)
  apply(rule htt_cons_rule[OF htt_vebt_predi])
  apply assumption
  apply simp
  apply (sep_auto simp: set_vebt_pred)
  apply simp
  done

subsubsection \<open>Delete\<close>  
lemma vebt_deletei_rule: "<vebt_assn n s ti > vebt_deletei ti x <\<lambda> r. vebt_assn n (s - {x}) r >T[20 + 20 * (nat \<lceil>lb n \<rceil>)]"
  unfolding vebt_assn_def
  apply(rule norm_pre_ex_rule_htt) 
  apply(clarsimp simp: norm_pre_pure_iff_htt)
  apply(rule htt_cons_rule[OF htt_vebt_deletei])
  apply assumption
  apply simp
  apply sep_auto
   apply (auto simp add: set_vebt_delete invar_vebt_delete) 
  done

subsection \<open>Setup of VCG\<close>   
lemmas vebt_heap_rules[THEN htt_htD,sep_heap_rules] = 
  vebt_buildupi_rule
  vebt_memberi_rule
  vebt_inserti_rule
  vebt_maxti_rule
  vebt_minti_rule
  vebt_succi_rule
  vebt_predi_rule
  vebt_deletei_rule

end
end
