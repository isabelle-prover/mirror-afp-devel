(*by Ammer*)
theory VEBT_SuccPredImperative
  imports VEBT_BuildupMemImp VEBT_Succ VEBT_Pred
begin

context begin
interpretation VEBT_internal .

section \<open>Imperative Successor\<close>
partial_function (heap_time) vebt_succi::"VEBTi \<Rightarrow> nat \<Rightarrow> (nat option) Heap" where
  "vebt_succi t x = (case t of (Leafi a b) \<Rightarrow>(if x = 0 then (if b then return (Some 1) else return None) 
                                      else return None)|
                      (Nodei info deg treeArray summary) \<Rightarrow> (
                       case info of None \<Rightarrow> return None |
                      (Some mima) \<Rightarrow> ( if deg \<le> 1 then return None else
                                   (if x < fst mima then return (Some (fst mima)) else
                                    if x \<ge> snd mima then return None else
                                      do {
                                          l <- lowi x (deg div 2);
                                          h <- highi x (deg div 2);
                                          aktnode <- Array_Time.nth treeArray h;
                                              maxlow <- vebt_maxti aktnode;
                                              if (maxlow \<noteq> None \<and> (Some l <\<^sub>o  maxlow))
                                              then do {
                                                       succy <- vebt_succi aktnode l;
                                                        return ( Some (2^(deg div 2)) *\<^sub>o Some h +\<^sub>o succy)
                                                       }
                                              else do {
                                                      succsum <-  vebt_succi summary h;
                                                      if succsum = None then
                                                          return None
                                                        else 
                                                          do{
                                                              nextnode <- Array_Time.nth treeArray (the succsum);
                                                              minnext <- vebt_minti nextnode;
                                                              return (Some (2^(deg div 2)) *\<^sub>o succsum +\<^sub>o minnext)
                                                            }
                                                      }
                                          
                                           })
)))"

end

context VEBT_internal begin

partial_function (heap_time) vebt_succi'::"VEBT \<Rightarrow> VEBTi \<Rightarrow> nat \<Rightarrow> (nat option) Heap" where
  "vebt_succi' t ti x = (case ti of (Leafi a b) \<Rightarrow>(if x = 0 then (if b then return (Some 1) else return None) 
                                      else return None)|
                      (Nodei info deg treeArray summary) \<Rightarrow> do { assert'( is_Node t);
                      let (info',deg',treeList,summary') = 
                    (case t of Node info' deg' treeList summary' \<Rightarrow> (info',deg',treeList,summary'));
                      assert'(info'=info \<and> deg'=deg \<and> is_Node t);
                     case info of None \<Rightarrow> return None |
                    (Some mima) \<Rightarrow> (if deg \<le> 1 then return None else
                                   (if x < fst mima then return (Some (fst mima)) else
                                    if x \<ge> snd mima then return None else
                                      do {
                                          l <- lowi x (deg div 2);
                                          h <- highi x (deg div 2);
                                          
                                          assert'(l = low x (deg div 2));
                                          assert'(h = high x (deg div 2));
                                          assert'(h < length treeList);
                                          
                                          aktnode <- Array_Time.nth treeArray h;
                                          let aktnode' = treeList!h;
                                          
                                              maxlow <- vebt_maxti aktnode;
                                              assert' (maxlow = vebt_maxt aktnode');
                                              if (maxlow \<noteq> None \<and> (Some l <\<^sub>o  maxlow))
                                              then do {
                                                       succy <- vebt_succi' aktnode' aktnode l;
                                                        return ( Some (2^(deg div 2)) *\<^sub>o Some h +\<^sub>o succy)
                                                       }
                                              else do {
                                                      succsum <-  vebt_succi' summary' summary h;
                                                      assert'(succsum = None \<longleftrightarrow> vebt_succ summary' h = None);
                                                      if succsum = None then do{
                                                          return None}
                                                        else 
                                                          do{
                                                              nextnode <- Array_Time.nth treeArray (the succsum);
                                                              minnext <- vebt_minti nextnode;
                                                              return (Some (2^(deg div 2)) *\<^sub>o succsum +\<^sub>o minnext)
                                                            }
                                                      }
                                          
                                           })
)})"

theorem vebt_succi'_rf_abstr:"invar_vebt t n \<Longrightarrow> <vebt_assn_raw t ti> vebt_succi' t ti x <\<lambda>r. vebt_assn_raw t ti * \<up>(r = vebt_succ t x)>"             
proof(induction t x arbitrary: ti n rule: vebt_succ.induct)
  case (1 uu b)
  then show ?case by(subst vebt_succi'.simps) (cases ti; sep_auto)
next
  case (2 uv uw n)
  then show ?case by(subst vebt_succi'.simps) (cases ti; sep_auto)
next
  case (3 ux uy uz va)
  then show ?case by(subst vebt_succi'.simps) (cases ti; sep_auto)
next
  case (4 v vc vd ve)
  then show ?case by(subst vebt_succi'.simps) (cases ti; sep_auto)
next
  case (5 v vg vh vi)
  then show ?case by(subst vebt_succi'.simps) (cases ti; sep_auto)
next
  case (6 mi ma va treeList summary x)
  have setprop: "t \<in> set treeList \<Longrightarrow> invar_vebt t (n div 2 )" for t using 6(3) 
    by (cases) simp+
  have listlength: "length treeList = 2^(n - n div 2)" using 6(3) 
    by (cases) simp+
  have sumprop: "invar_vebt summary (n - n div 2)" using 6(3)
    by (cases) simp+
  have xprop [simp]: " \<not> ma \<le> x \<Longrightarrow> high x (Suc (va div 2)) < length treeList" 
    by (smt (z3) "6.prems" deg_deg_n div2_Suc_Suc div_le_dividend high_bound_aux listlength mi_ma_2_deg not_le_imp_less order.strict_trans ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
  hence xprop' [simp]: " \<not> ma \<le> x \<Longrightarrow> x div (2 * 2 ^ (va div 2)) < length treeList" unfolding high_def by simp
  show ?case
    apply (cases ti)
    prefer 2
    subgoal 
      apply simp
    done
    subgoal for x11 x12 x13 x14
      supply [split del] = if_split
      apply (subst vebt_succi'.simps; clarsimp split del: )
      apply (assn_simp; intro normalize_rules) 
      apply simp
      apply(auto split: if_split)
      subgoal 
        apply sep_auto
      done
      apply sep_auto
      using "6.prems" geqmaxNone
      apply fastforce
      apply sep_auto
      apply (extract_pre_pure dest: extract_pre_list_assn_lengthD)
      apply (sep_auto simp: lowi_def low_def heap: highi_h) 
      apply(sep_auto heap: vebt_maxtilist)
      apply sep_auto
      apply(simp add: high_def low_def)
      apply (rewrite in "<\<hole>>_<_>" list_assn_conv_idx)
      apply(rewrite in "<\<hole>>_<_>" listI_assn_extract[where i="(x div (2 * 2 ^ (va div 2)))"])
      apply (smt (z3) "6.prems" atLeastLessThan_iff deg_deg_n div2_Suc_Suc div_le_dividend dual_order.strict_trans2 high_bound_aux high_def le0 le_add_diff_inverse listlength mi_ma_2_deg nat_le_linear power_Suc)
      apply (smt (z3) "6.prems" deg_deg_n div2_Suc_Suc div_le_dividend dual_order.strict_trans2 high_bound_aux high_def le_add_diff_inverse listlength mi_ma_2_deg nat_le_linear power_Suc)
      apply(sep_auto heap: "6.IH"(1))
      apply(simp add: low_def)
      apply(simp add: high_def) 
      apply simp+
      apply(rule setprop) 
        apply simp
      subgoal for tree_is x
        apply sep_auto
        apply (smt (z3) "6.prems" deg_deg_n div2_Suc_Suc div_le_dividend dual_order.strict_trans2 high_bound_aux high_def le_add_diff_inverse less_shift listlength low_def mi_ma_2_deg nat_le_linear option.distinct(1) power_Suc)
        apply(rule ent_trans[where Q=" vebt_assn_raw summary x14 * (x13 \<mapsto>\<^sub>a tree_is )*
                             (list_assn vebt_assn_raw treeList tree_is)"])
        apply (smt (z3) assn_aci(10) atLeastLessThan_iff entails_def leI less_nat_zero_code listI_assn_extract list_assn_conv_idx star_aci(2) xprop')
        apply(rule ent_refl)
       done
      apply simp
      apply sep_auto
      apply(sep_auto heap: "6.IH"(2))  
      apply (simp add: high_def low_def)+
      apply (rule sumprop)
      apply(sep_auto heap: "6.IH"(2)) 
      apply (simp add: high_def low_def)+
      apply (rule sumprop)
      apply sep_auto+
      apply(simp add: high_def low_def)+     
      using helpyd listlength sumprop 
      apply presburger+
      apply (sep_auto heap: vebt_mintilist)
      using helpyd listlength sumprop
      apply presburger
      using helpyd listlength sumprop 
      apply presburger+     
      apply sep_auto
      done
    done   
qed

lemma TBOUND_vebt_succi:
  defines foo_def: "\<And> t x. foo t x \<equiv> 7 * (1+height t)"
  shows "TBOUND (vebt_succi' t ti x) (foo t x)"  
  apply (induction arbitrary: t ti x rule: vebt_succi'.fixp_induct)  
  apply (rule TBOUND_fi'_adm)
  apply (rule TBOUND_empty) 
  apply TBOUND
  apply(simp add: Let_def split!: VEBTi.splits VEBT.splits prod.splits option.splits if_splits)
  apply(simp_all add: foo_def max_idx_list)
  done

lemma vebt_succi_refines: "refines (vebt_succi ti  x) (vebt_succi' t ti x)"
  apply (induction arbitrary: t ti x rule: vebt_succi'.fixp_induct)
  subgoal using refines_adm[where t = "\<lambda> arg. vebt_succi (snd (fst arg)) (snd arg)"]
    by simp
  subgoal by simp
  subgoal for f t ti x
    apply(subst vebt_succi.simps)
    apply refines
   done
  done

lemma htt_vebt_succi: assumes "invar_vebt t n"
  shows  "<vebt_assn_raw t ti> vebt_succi ti x <\<lambda> r. vebt_assn_raw t ti *  \<up>(r = vebt_succ t x) >T[7 + 7*(nat \<lceil>lb n\<rceil>)]"
  apply (rule htt_refine[where c = "vebt_succi' t ti x"])
  prefer 2
  apply(rule vebt_succi_refines)
  apply (rule httI_TBOUND)
  apply(rule vebt_succi'_rf_abstr)
  apply(rule assms)
  apply(rule TBOUND_mono)
  apply(rule TBOUND_vebt_succi)
  apply simp
  apply(rule  Nat.eq_imp_le)
  apply (metis assms nat_int  heigt_uplog_rel)
  done

end

context begin
interpretation VEBT_internal .
  
  
partial_function (heap_time) vebt_predi::"VEBTi \<Rightarrow> nat \<Rightarrow> (nat option) Heap" where
  "vebt_predi t x = (case t of (Leafi a b) \<Rightarrow>(if x \<ge> 2then (if b then return (Some 1) else if a then return (Some 0) else return None) 
                                      else if x = 1 then (if a then return (Some 0) else return None) else return None)|
                      (Nodei info deg treeArray summary) \<Rightarrow> (
                  case info of None \<Rightarrow> return None |
                    (Some mima) \<Rightarrow> ( if deg \<le> 1 then return None else
                                   (if x > snd mima then return (Some (snd mima)) else
                                      do {
                                          l <- lowi x (deg div 2);
                                          h <- highi x (deg div 2);
                                              aktnode <- Array_Time.nth treeArray h;
                                              minlow <- vebt_minti aktnode;
                                              if (minlow \<noteq> None \<and> (Some l >\<^sub>o  minlow))
                                              then do {
                                                       predy <- vebt_predi aktnode l;
                                                        return ( Some (2^(deg div 2)) *\<^sub>o Some h +\<^sub>o predy)
                                                       }
                                              else do {
                                                      predsum <-  vebt_predi summary h;
                                                      if predsum = None then
                                                          if x > fst mima then
                                                              return (Some (fst mima))
                                                              else
                                                                return None
                                                        else 
                                                          do{
                                                              nextnode <- Array_Time.nth treeArray (the predsum);
                                                              maxnext <- vebt_maxti nextnode;
                                                              return (Some (2^(deg div 2)) *\<^sub>o predsum +\<^sub>o maxnext)
                                                            }
                                                      }
                                            }))))"

end
context VEBT_internal begin                                            
                                            
section \<open>Imperative Predecessor\<close>
partial_function (heap_time) vebt_predi'::"VEBT \<Rightarrow> VEBTi \<Rightarrow> nat \<Rightarrow> (nat option) Heap" where
  "vebt_predi' t ti x = (case ti of (Leafi a b) \<Rightarrow>(if x \<ge> 2then (if b then return (Some 1) else if a then return (Some 0) else return None) 
                                      else if x = 1 then (if a then return (Some 0) else return None) else return None)|
                      (Nodei info deg treeArray summary) \<Rightarrow> (  do { assert'( is_Node t);
                      let (info',deg',treeList,summary') = 
                    (case t of Node info' deg' treeList summary' \<Rightarrow> (info',deg',treeList,summary'));
                      assert'(info'=info \<and> deg'=deg \<and> is_Node t);
                  case info of None \<Rightarrow> return None |
                    (Some mima) \<Rightarrow> ( if deg \<le> 1 then return None else
                                   (if x > snd mima then return (Some (snd mima)) else
                                      do {
                                          l <- lowi x (deg div 2);
                                          h <- highi x (deg div 2);
                                           
                                          assert'(l = low x (deg div 2));
                                          assert'(h = high x (deg div 2));
                                          assert'(h < length treeList);
                                        
                                              aktnode <- Array_Time.nth treeArray h;
                                                let aktnode' = treeList!h;
                                              minlow <- vebt_minti aktnode;                                         
                                              assert' (minlow = vebt_mint aktnode');

                                              if (minlow \<noteq> None \<and> (Some l >\<^sub>o  minlow))
                                              then do {
                                                       predy <- vebt_predi' aktnode' aktnode l;
                                                        return ( Some (2^(deg div 2)) *\<^sub>o Some h +\<^sub>o predy)
                                                       }
                                              else do {
                                                      predsum <-  vebt_predi' summary' summary h;
                                                     assert'(predsum = None \<longleftrightarrow> vebt_pred summary' h = None);
                                                      if predsum = None then
                                                          if x > fst mima then
                                                              return (Some (fst mima))
                                                              else
                                                                return None
                                                        else 
                                                          do{
                                                              nextnode <- Array_Time.nth treeArray (the predsum);
                                                              maxnext <- vebt_maxti nextnode;
                                                              return (Some (2^(deg div 2)) *\<^sub>o predsum +\<^sub>o maxnext)
                                                            }
                                                      }
                                            }))}))"

theorem vebt_pred'_rf_abstr:"invar_vebt t n \<Longrightarrow> <vebt_assn_raw t ti> vebt_predi' t ti x <\<lambda>r. vebt_assn_raw t ti * \<up>(r = vebt_pred t x)>"             
proof(induction t x arbitrary: ti n rule: vebt_pred.induct)
  case (1 uu uv)
  then show ?case by(subst vebt_predi'.simps) (cases ti; sep_auto)
next
  case (2 a uw)
  then show ?case  by(subst vebt_predi'.simps) (cases ti; sep_auto)
next
  case (3 a b va)
  then show ?case  by(subst vebt_predi'.simps) (cases ti; sep_auto)
next
  case (4 uy uz va vb)
  then show ?case  by(subst vebt_predi'.simps) (cases ti; sep_auto)
next
  case (5 v vd ve vf)
  then show ?case  by(subst vebt_predi'.simps) (cases ti; sep_auto)
next
  case (6 v vh vi vj)
  then show ?case  by(subst vebt_predi'.simps) (cases ti; sep_auto)
next
  case (7 mi ma va treeList summary x)
  have setprop: "t \<in> set treeList \<Longrightarrow> invar_vebt t (n div 2 )" for t using 7(3) 
    by (cases) simp+
  have listlength: "length treeList = 2^(n - n div 2)" using 7(3) 
    by (cases) simp+
  have sumprop: "invar_vebt summary (n - n div 2)" using 7(3)
    by (cases) simp+
  have mimapr: "ma \<ge> mi" using 7(3) 
    by (cases) simp+  
  show ?case 
    apply (cases ti)
    prefer 2
    subgoal 
      apply simp 
      done
    subgoal
      supply [split del] = if_split
      apply (subst vebt_predi'.simps; clarsimp split del: )
      apply (assn_simp; intro normalize_rules) 
      apply simp
      apply(cases "ma < x")
      subgoal
        apply simp
        apply sep_auto
       done
      apply simp
      apply (extract_pre_pure dest: extract_pre_list_assn_lengthD)
      apply(sep_auto simp: highi_def)
      apply (sep_auto simp: lowi_def)   
      apply sep_auto 
      apply(simp add: low_def)
      apply sep_auto
       apply(simp add: high_def)
      apply sep_auto
      apply (smt (z3) "7.prems" deg_deg_n div2_Suc_Suc div_le_dividend high_bound_aux high_def le_add_diff_inverse linorder_neqE_nat listlength mi_ma_2_deg order.strict_trans power_Suc)
      apply sep_auto
      apply (smt (z3) "7.prems" deg_deg_n div2_Suc_Suc div_le_dividend high_bound_aux high_def le_add_diff_inverse linorder_neqE_nat listlength mi_ma_2_deg order.strict_trans power_Suc)    
      apply (sep_auto heap: vebt_mintilist)
      apply (smt (z3) "7.prems" deg_deg_n div2_Suc_Suc div_le_dividend high_bound_aux high_def le_add_diff_inverse linorder_neqE_nat listlength mi_ma_2_deg order.strict_trans power_Suc)      
      apply sep_auto
      apply (rewrite in "<\<hole>>_<_>" list_assn_conv_idx)
      apply(rewrite in "<\<hole>>_<_>" listI_assn_extract[where i="(x div (2 * 2 ^ (va div 2)))"])
      apply (smt (z3) "7.prems" atLeastLessThan_iff deg_deg_n div2_Suc_Suc div_le_dividend high_bound_aux high_def le0 le_add_diff_inverse linorder_neqE_nat listlength mi_ma_2_deg order.strict_trans power_Suc)     
      apply (smt (z3) "7.prems" deg_deg_n div2_Suc_Suc div_le_dividend high_bound_aux high_def le_add_diff_inverse linorder_neqE_nat listlength mi_ma_2_deg order.strict_trans power_Suc)            
      apply (sep_auto heap: "7.IH"(1))
      apply(simp add: high_def low_def)+
      apply (smt (z3) "7.prems" deg_deg_n div2_Suc_Suc div_le_dividend high_bound_aux high_def le_add_diff_inverse linorder_neqE_nat listlength mi_ma_2_deg order.strict_trans power_Suc)      
      apply(rule DEADID.rel_refl)
      apply (metis greater_shift option.simps(3))
      apply(rule setprop)
      apply(rule nth_mem)
      apply (smt (z3) "7.prems" atLeastLessThan_iff deg_deg_n div2_Suc_Suc div_le_dividend high_bound_aux high_def le0 le_add_diff_inverse linorder_neqE_nat listlength mi_ma_2_deg order.strict_trans power_Suc)     
      apply simp
      subgoal
        apply sep_auto 
        apply (smt (z3) "7.prems" deg_deg_n div2_Suc_Suc div_le_dividend dual_order.strict_trans2 greater_shift high_bound_aux high_def leI le_add_diff_inverse listlength low_def mi_ma_2_deg option.distinct(1) power_Suc)
        apply (rule recomp)
        apply (smt (z3) "7.prems" atLeastLessThan_iff deg_deg_n div2_Suc_Suc div_le_dividend high_bound_aux high_def le0 le_add_diff_inverse linorder_neqE_nat listlength mi_ma_2_deg order.strict_trans power_Suc)     
        apply (smt (z3) "7.prems" deg_deg_n div2_Suc_Suc div_le_dividend dual_order.strict_trans2 greater_shift high_bound_aux high_def leI le_add_diff_inverse listlength low_def mi_ma_2_deg option.distinct(1) power_Suc)
        apply (rule recomp) 
        apply (smt (z3) "7.prems" atLeastLessThan_iff deg_deg_n div2_Suc_Suc div_le_dividend high_bound_aux high_def le0 le_add_diff_inverse linorder_neqE_nat listlength mi_ma_2_deg order.strict_trans power_Suc)     
       done
      apply(sep_auto heap: "7.IH"(2))
      apply(simp add: high_def low_def)+
      apply (smt (z3) "7.prems" atLeastLessThan_iff deg_deg_n div2_Suc_Suc div_le_dividend high_bound_aux high_def le0 le_add_diff_inverse linorder_neqE_nat listlength mi_ma_2_deg order.strict_trans power_Suc)     
      apply(rule DEADID.rel_refl)
      apply (simp add: low_def)
      apply(rule sumprop)
      apply sep_auto
      apply(sep_auto simp: high_def low_def)+
      apply (smt (z3) "7.prems" deg_deg_n div2_Suc_Suc div_le_dividend dual_order.strict_trans2 high_bound_aux high_def leI le_add_diff_inverse listlength mi_ma_2_deg power_Suc)
      apply (simp add: high_def low_def)
      apply (smt (z3) "7.prems" deg_deg_n div2_Suc_Suc div_le_dividend dual_order.strict_trans2 greater.elims(2) high_bound_aux high_def leI le_add_diff_inverse listlength mi_ma_2_deg power_Suc)
      apply sep_auto
      apply(sep_auto simp: high_def low_def)+
      apply presburger
      apply (smt (z3) greater.elims(2) high_def low_def power_Suc)
      apply (simp add: high_def low_def)
      apply sep_auto
      subgoal
        using helpypredd listlength sumprop apply simp
       done
      subgoal
        using helpypredd listlength sumprop apply simp
       done
      apply sep_auto
      apply(rule cons_pre_rule)
      apply(sep_auto heap: vebt_maxti_h)
      apply (rewrite in "<\<hole>>_<_>" list_assn_conv_idx)
      apply (rewrite in "<\<hole>>_<_>" listI_assn_extract[where i="the (vebt_pred summary (x div (2 * 2 ^ (va div 2))))"])
      apply (metis atLeastLessThan_iff helpypredd le0 listlength option.sel sumprop)
      apply (metis helpypredd listlength option.sel sumprop)
      apply (simp add: algebra_simps)
      apply(rule cons_pre_rule)
      apply(rule ext)
      using helpypredd listlength sumprop apply presburger
      apply(sep_auto heap: vebt_maxti_h) 
      apply (rewrite in "<\<hole>>_<_>" list_assn_conv_idx)
      apply (rewrite in "<\<hole>>_<_>" listI_assn_extract[where i="the (vebt_pred summary (x div (2 * 2 ^ (va div 2))))"])
      apply (metis atLeastLessThan_iff helpypredd le0 listlength option.sel sumprop)
      apply (metis helpypredd listlength option.sel sumprop)
      apply simp
      apply(sep_auto heap: vebt_maxti_h)
      apply sep_auto
      apply (smt (z3) "7.prems" deg_deg_n div2_Suc_Suc div_le_dividend dual_order.strict_trans2 high_bound_aux high_def leI le_add_diff_inverse listlength mi_ma_2_deg option.distinct(1) option.sel power_Suc)
      apply (smt (z3) "7.prems" deg_deg_n div2_Suc_Suc div_le_dividend dual_order.strict_trans2 greater.elims(2) high_bound_aux high_def leI le_add_diff_inverse listlength mi_ma_2_deg option.distinct(1) option.sel power_Suc)
      apply(rule txe)
      using helpypredd listlength sumprop apply presburger   
      apply (smt (z3) "7.prems" deg_deg_n div2_Suc_Suc div_le_dividend dual_order.strict_trans2 greater.elims(2) high_bound_aux high_def leI le_add_diff_inverse listlength mi_ma_2_deg option.distinct(1) option.sel power_Suc)
      apply(rule txe)
      using helpypredd listlength sumprop apply presburger
      done 
    done
qed

lemma TBOUND_vebt_predi:
  defines foo_def: "\<And> t x. foo t x \<equiv> 7 * (1+height t)"
  shows "TBOUND (vebt_predi' t ti x) (foo t x)"  
  apply (induction arbitrary: t ti x rule: vebt_predi'.fixp_induct)  
  apply (rule TBOUND_fi'_adm)
  apply (rule TBOUND_empty) 
  apply TBOUND
  apply (simp add: Let_def split!: VEBTi.splits VEBT.splits option.splits prod.splits if_splits)
  apply(simp_all add: foo_def max_idx_list)
  done

lemma vebt_predi_refines: "refines (vebt_predi ti  x) (vebt_predi' t ti x)"
  apply (induction arbitrary: t ti x rule: vebt_predi'.fixp_induct)
  subgoal  using refines_adm[where t = "\<lambda> arg. vebt_predi (snd (fst arg)) (snd arg)"]
    by simp
  subgoal by simp
  subgoal for f t ti x
    apply(subst vebt_predi.simps)
    apply refines
   done
  done

lemma htt_vebt_predi: assumes "invar_vebt t n"
  shows  "<vebt_assn_raw t ti> vebt_predi ti x <\<lambda> r. vebt_assn_raw t ti *  \<up>(r = vebt_pred t x) >T[7 + 7*(nat \<lceil>lb n\<rceil>)]"
  apply (rule htt_refine[where c = "vebt_predi' t ti x"])
  prefer 2
  apply(rule vebt_predi_refines)
  apply (rule httI_TBOUND)
  apply(rule vebt_pred'_rf_abstr)
  apply(rule assms)
  apply(rule TBOUND_mono)
  apply(rule TBOUND_vebt_predi)
  apply simp
  apply(rule  Nat.eq_imp_le)
  apply (metis assms nat_int  heigt_uplog_rel)
  done

end 
end
