(*by Ammer*)
theory VEBT_DelImperative imports VEBT_DeleteCorrectness VEBT_SuccPredImperative
begin

context begin
interpretation VEBT_internal .

section \<open>Imperative Delete\<close>

partial_function (heap_time) vebt_deletei::"VEBTi \<Rightarrow> nat \<Rightarrow> VEBTi Heap" where
  "vebt_deletei t x = (case t of (Leafi a b) \<Rightarrow> (if x = 0 then return (Leafi False b) else 
                                         if x = 1 then return (Leafi a False) else
                                          return (Leafi a b)) |
                            (Nodei info deg treeArray summary) \<Rightarrow> ( 
                                if deg \<le> 1 then return  (Nodei info deg treeArray summary) else 
                                     case info of None \<Rightarrow> return  (Nodei info deg treeArray summary)|
                                           (Some mima) \<Rightarrow> ( if x < fst mima \<or> x > snd mima then return  (Nodei info deg treeArray summary)
                                                      else  if fst mima = x \<and> snd mima = x then return  (Nodei None deg treeArray summary)
                                                  else do{ xminew <- (if x = fst mima then do {
                                                                        firstcluster <- vebt_minti summary;
                                                                        firsttree <- Array_Time.nth  treeArray (the firstcluster);
                                                                        mintft <- vebt_minti firsttree;
                                                                        let xn = (2^(deg div 2) * (the firstcluster) + 
                                                                                    (the mintft) );
                                                                        return (xn, xn)           
                                                                               } 
                                                                      else return (x, fst mima));
                                                          let xnew = fst xminew;
                                                          let minew = snd xminew;
                                                          h <- highi xnew (deg div 2);
                                                          l <- lowi xnew (deg div 2);
                                                          aktnode <- Array_Time.nth treeArray h;
                                                          aktnode'<-vebt_deletei aktnode l;
                                                          treeArray' <- Array_Time.upd h aktnode' treeArray; 
                                                          miny <- vebt_minti aktnode';
                                                         (if (miny = None) then 
                                                          do{
                                                              summary' <-vebt_deletei summary h;
                                                              ma <-  (if xnew = snd mima then
                                                              do{
                                                                  summax <- vebt_maxti summary';
                                                                  if summax = None then
                                                                        return minew
                                                                  else do{
                                                                          maxtree <- Array_Time.nth treeArray' (the summax);
                                                                          mofmtree<- vebt_maxti maxtree;
                                                                          return (the summax * 2^(deg div 2) + 
                                                                                           the mofmtree )
                                                                          }
                                                                 }
                                                                  else return (snd mima));
                                                              return (Nodei (Some (minew, ma)) deg treeArray' summary')
                                                          } else  if xnew = snd mima then
                                                            do{
                                                                nextree <- Array_Time.nth treeArray' h;  
                                                                maxnext<- vebt_maxti nextree;
                                                                let ma = h * 2^(deg div 2) +
                                                                              (the maxnext);
                                                                return (Nodei (Some ( minew, ma)) deg treeArray' summary) 
                                                               }
                                                            else return (Nodei (Some (minew, snd mima)) deg treeArray' summary) )
                                                          })))" 

end

context VEBT_internal begin
                                                          
                                                          
text \<open>Some general lemmas\<close>

lemma midextr:"(P * Q * Q' *R \<Longrightarrow>\<^sub>A X) \<Longrightarrow> (P * R * Q *Q' \<Longrightarrow>\<^sub>A X)"  
  by (smt (verit, ccfv_threshold) ab_semigroup_mult_class.mult.commute assn_aci(9) entails_def mod_frame_fwd)

lemma groupy: "A *B * (C * D) \<Longrightarrow>\<^sub>A X \<Longrightarrow>A *B * C * D \<Longrightarrow>\<^sub>A X " 
  by (simp add: assn_aci(9))

lemma swappa: "B* A* C \<Longrightarrow>\<^sub>A X \<Longrightarrow>A *B * C  \<Longrightarrow>\<^sub>A X " 
  by (simp add: ab_semigroup_mult_class.mult.commute)

lemma mulcomm: "(i::nat) * (2 * 2 ^ (va div 2)) =  (2 * 2 ^ (va div 2)) * i"
  by simp

text \<open>Modified function with ghost variable\<close>

partial_function (heap_time) vebt_deletei'::"VEBT \<Rightarrow> VEBTi \<Rightarrow> nat \<Rightarrow> VEBTi Heap" where
  "vebt_deletei' t ti x = (case ti of (Leafi a b) \<Rightarrow> (if x = 0 then return (Leafi False b) else 
                                         if x = 1 then return (Leafi a False) else
                                          return (Leafi a b)) |
                        (Nodei info deg treeArray summary) \<Rightarrow> ( 
                                 do { assert'( is_Node t);
                      let (info',deg',treeList,summary') = 
                     (case t of Node info' deg' treeList summary' 
                                     \<Rightarrow> (info',deg',treeList,summary'));
                      assert'(info'=info \<and> deg'=deg \<and> is_Node t);
                                if deg \<le> 1 then return  (Nodei info deg treeArray summary) else 
                                     case info of None \<Rightarrow> return  (Nodei info deg treeArray summary)|
                                           (Some mima) \<Rightarrow> (                                                  
                                                  if x < fst mima \<or> x > snd mima then return  (Nodei info deg treeArray summary)
                                                      else  if fst mima = x \<and> snd mima = x then return  (Nodei None deg treeArray summary)
                                                  else do{ xminew <- (if x = fst mima then do {
                                                                        firstcluster <- vebt_minti summary;
                                                                        firsttree <- Array_Time.nth  treeArray (the firstcluster);
                                                                        mintft <- vebt_minti firsttree;
                                                                        let xn = (2^(deg div 2) * (the firstcluster) + 
                                                                                    (the mintft) );
                                                                        return (xn, xn)           
                                                                               } 
                                                                      else return (x, fst mima));
                                                          let xnew = fst xminew;
                                                          let xn' = 
                                                           (if x = fst (the info')
                                                            then the (vebt_mint summary') * 2^(deg div 2) 
                                                             + the (vebt_mint (treeList ! the (vebt_mint summary'))) 
                                                            else x);
                                                          assert' (xnew = xn');
                                                          let minew = snd xminew;
                                                          assert' (minew = (if x = fst (the info') then xn' else  fst (the info')));
                                                          h <- highi xnew (deg div 2);
                                                          assert' (h = high xnew (deg div 2));
                                                          assert'( h < length treeList);
                                                          l <- lowi xnew (deg div 2);
                                                          assert'(l = low xnew (deg div 2));
                                                          aktnode <- Array_Time.nth treeArray h;
                                                          aktnode'<-vebt_deletei' (treeList ! h) aktnode l;
                                                          treeArray' <- Array_Time.upd h aktnode' treeArray;
                                                        let funnode = vebt_delete (treeList !  h) l; 
                                                        let treeList' = treeList[h:= funnode];
                                                          miny <- vebt_minti aktnode';
                                                          assert' (miny = vebt_mint funnode);
                                                         (if (miny = None) then 
                                                          do{
                                                              summaryi' <-vebt_deletei' summary' summary h;
                                                              ma <-  (if xnew = snd mima then
                                                              do{
                                                                  summax <- vebt_maxti summaryi';
                                                                  assert' (summax = vebt_maxt (vebt_delete summary' h));
                                                                  if summax = None then
                                                                        return minew
                                                                  else do{
                                                                          maxtree <- Array_Time.nth treeArray' (the summax);
                                                                          mofmtree<- vebt_maxti maxtree;
                                                                          return (the summax * 2^(deg div 2) + 
                                                                                           the mofmtree )
                                                                          }
                                                                 }
                                                                  else return (snd mima));
                                                              return (Nodei (Some (minew, ma)) deg treeArray' summaryi')
                                                          } else  if xnew = snd mima then
                                                            do{
                                                                nextree <- Array_Time.nth treeArray' h;  
                                                                maxnext<- vebt_maxti nextree;
                                                                assert' (maxnext = vebt_maxt (treeList' ! h));
                                                                let ma = h * 2^(deg div 2) +
                                                                              (the maxnext);
                                                                return (Nodei (Some ( minew, ma)) deg treeArray' summary) 
                                                               }
                                                            else return (Nodei (Some (minew, snd mima)) deg treeArray' summary) )
                                                          })}))" 


theorem deleti'_rf_abstr: "invar_vebt t n \<Longrightarrow> <vebt_assn_raw t ti> vebt_deletei' t ti x< vebt_assn_raw (vebt_delete t x)>"
proof(induction t x arbitrary: ti n rule: vebt_delete.induct)
  case (1 a b)
  then show ?case by(subst vebt_deletei'.simps) (cases ti; sep_auto)
next
  case (2 a b)
  then show ?case by(subst vebt_deletei'.simps) (cases ti; sep_auto)
next
  case (3 a b n)
  then show ?case by(subst vebt_deletei'.simps) (cases ti; sep_auto)
next
  case (4 deg treeList summary uu)
  then show ?case by(subst vebt_deletei'.simps) (cases ti; sep_auto)
next
  case (5 mi ma treeList summary x)
  then show ?case by(subst vebt_deletei'.simps) (cases ti; sep_auto)
next
  case (6 mi ma treeList summary x)
  then show ?case by(subst vebt_deletei'.simps) (cases ti; sep_auto)
next
  case (7 mi ma va treeList summary x)
  have setprop: "t \<in> set treeList \<Longrightarrow> invar_vebt t (n div 2 )" for t using 7(3) 
    by (cases) simp+
  have listlength: "length treeList = 2^(n - n div 2)" using 7(3) 
    by (cases) simp+
  have sumprop: "invar_vebt summary (n - n div 2)" using 7(3)
    by (cases) simp+
  have mimaxprop: "mi \<le> ma \<and> ma \<le> 2^n" using 7(3) 
    by cases  simp+
  hence xbound: "mi \<le> x \<Longrightarrow> x \<le> ma \<Longrightarrow> high x (n div 2) \<le> length treeList "
    using div_le_mono high_def listlength power_minus_is_div by auto
  let ?xn = "  the (vebt_mint summary) * 2 ^ (Suc (Suc va) div 2) + the (vebt_mint (treeList ! the (vebt_mint summary)))"
  obtain xnew where xndef: "xnew = ?xn" by simp
  let ?minn = "?xn" 
  obtain minew where minewdef: "minew =?minn" by simp
  have highboundn:"ma \<noteq> mi \<Longrightarrow>x\<le> ma \<Longrightarrow>high xnew (n div 2 )< length treeList" using xndef  
    by (smt (z3) "7.prems" deg_deg_n diff_diff_cancel div2_Suc_Suc div_le_dividend high_bound_aux leD le_add_diff_inverse less_imp_diff_less listlength mi_ma_2_deg nested_mint power_Suc)
  have highbound: "ma \<noteq> mi \<Longrightarrow>x\<le> ma \<Longrightarrow>high x (n div 2 )< length treeList" 
    by (smt (z3) "7.prems" deg_deg_n div_le_dividend high_bound_aux le_less_trans listlength mi_ma_2_deg ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
  let ?aktnode = "(treeList !
               high (2 * 2 ^ (va div 2) * the (vebt_mint summary) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (Suc (va div 2)))"
  obtain aktnode where aktnodedef:"ma \<noteq> mi \<Longrightarrow>x\<le> ma  \<Longrightarrow>aktnode = ?aktnode"
    by meson
  let ?newnode = "vebt_delete ?aktnode (low ?xn (Suc (Suc va) div 2))"
  obtain newnode where newnodedef:"newnode = ?newnode" by presburger
  let ?newlist="treeList[ high (2 * 2 ^ (va div 2) * the (vebt_mint summary) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (Suc (va div 2)) :=
                    ?newnode]"
  let ?newlist'="treeList[ high x  (Suc (va div 2)) := vebt_delete (treeList ! high x (Suc (va div 2))) (low x (Suc (va div 2)))]"
  show ?case 
    apply(cases ti)
     prefer 2
     subgoal
      apply simp
     done
    supply [split del] = if_split
    apply (subst vebt_deletei'.simps; clarsimp split del: )
    apply (assn_simp; intro normalize_rules) 
    apply simp
    apply(cases "x < mi \<or> ma < x")
    subgoal
      apply simp
      apply sep_auto
      done
    apply simp
    apply(cases "mi = x \<and> ma = x")
    subgoal
      apply simp
      apply sep_auto
      done
    apply (extract_pre_pure dest: extract_pre_list_assn_lengthD)
    apply (cases "mi = x \<and> ma = x"; simp)
    apply(cases "x = mi")
    subgoal
      apply simp
      apply sep_auto
      apply(sep_auto heap: vebt_minti_h)
      apply sep_auto 
      apply (metis "7.prems" listlength mintlistlength option.sel)
      apply sep_auto
      apply (rewrite in "<\<hole>>_<_>" list_assn_conv_idx)
      apply (rewrite in "<\<hole>>_<_>" listI_assn_extract[where i="the (vebt_mint summary)"])
      apply (metis "7.prems" atLeastLessThan_iff le0 listlength mintlistlength option.sel)
      apply (metis "7.prems" listlength mintlistlength option.sel)
      apply(sep_auto heap: vebt_minti_h)
      apply(rule cons_pre_rule)
      apply (rule repack)
      apply (metis "7.prems" listlength mintlistlength option.sel)
      apply sep_auto
      apply (sep_auto heap: highi_h)
      apply sep_auto 
      apply (metis "7.prems" ab_semigroup_mult_class.mult.commute deg_deg_n nested_mint)
      apply (sep_auto heap: lowi_h) 
      apply (metis "7.prems" ab_semigroup_mult_class.mult.commute deg_deg_n div2_Suc_Suc highboundn mimaxprop power_Suc xndef)
      apply sep_auto
      apply (rewrite in "<\<hole>>_<_>" list_assn_conv_idx)
      apply (rewrite in "<\<hole>>_<_>" listI_assn_extract[where i=" high (2 * 2 ^ (va div 2) * the (vebt_mint summary) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (Suc (va div 2))"])
      apply (metis "7.prems" ab_semigroup_mult_class.mult.commute atLeastLessThan_iff deg_deg_n leI less_nat_zero_code nested_mint)
      apply (metis "7.prems" ab_semigroup_mult_class.mult.commute deg_deg_n nested_mint)
      apply sep_auto
      apply(sep_auto heap: "7.IH"(1))
      apply(simp add: algebra_simps)
      apply(simp add: algebra_simps)
      apply (metis "7.prems" ab_semigroup_mult_class.mult.commute deg_deg_n nested_mint)
      apply(rule setprop)
      apply (metis "7.prems" ab_semigroup_mult_class.mult.commute deg_deg_n nested_mint nth_mem)
      apply sep_auto
      apply (metis "7.prems" ab_semigroup_mult_class.mult.commute deg_deg_n nested_mint) 
      apply(simp add: Let_def)
      apply sep_auto
      apply(sep_auto heap: vebt_minti_h)
      apply(rule cons_pre_rule)
      apply(rule big_assn_simp[of "high (2 * 2 ^ (va div 2) * the (vebt_mint summary) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (Suc (va div 2))"
                                   treeList "(low (2 * 2 ^ (va div 2) * the (vebt_mint summary) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (Suc (va div 2)))"
                                   _ _ _ _ summary])
      apply (metis "7.prems" ab_semigroup_mult_class.mult.commute deg_deg_n div2_Suc_Suc highboundn mimaxprop power_Suc xndef)
      apply(cases "vebt_mint (vebt_delete (treeList !
              high (2 * 2 ^ (va div 2) * the (vebt_mint summary) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (Suc (va div 2)))
             (low (2 * 2 ^ (va div 2) * the (vebt_mint summary) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (Suc (va div 2)))) = None")
      apply simp
      subgoal
       apply sep_auto
       apply(sep_auto heap:  "7.IH"(2))
       apply(simp add: algebra_simps)+
       apply (smt (z3) "7.prems" ab_semigroup_add_class.add.commute ab_semigroup_mult_class.mult.left_commute deg_deg_n nested_mint)
       apply(rule DEADID.rel_refl)
       apply(rule DEADID.rel_refl)
       apply(rule minminNull)
       apply (metis ab_semigroup_mult_class.mult.commute)
       apply(rule sumprop)
       apply(rule bind_rule'[where R="\<lambda> r.(let sn =  vebt_delete summary (high (2 * 2 ^ (va div 2) * 
              the (vebt_mint summary) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (Suc (va div 2))) in ( \<up>(r = (
                                 if ?xn = ma then let maxs = vebt_maxt sn in if maxs = None then ?xn
                                         else 2 ^ (Suc (Suc va) div 2) * the maxs + the (vebt_maxt (?newlist ! the maxs)) else ma))))"])
       apply(cases "2 * 2 ^ (va div 2) * the (vebt_mint summary) + the (vebt_mint (treeList ! the (vebt_mint summary))) = ma")
       apply simp+
       apply sep_auto
       apply(sep_auto heap: vebt_maxti_h)
       apply sep_auto
       using delete_pres_valid[of summary "n - n div 2" 
            "(high (2 * 2 ^ (va div 2) * the (vebt_mint summary) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (Suc (va div 2)))"]
              maxt_member[of "vebt_delete summary _" "n-n div 2"] member_bound[of "vebt_delete summary _ " _ "n-n div 2"] listlength sumprop
       apply (metis both_member_options_equiv_member dele_bmo_cont_corr maxbmo member_bound)
       apply sep_auto
       apply (rewrite in "<\<hole>>_<_>" list_assn_conv_idx)
       apply (rewrite in "<\<hole>>_<_>" listI_assn_extract[where i=" the (  vebt_maxt (vebt_delete summary (high (2 * 2 ^ (va div 2) * the (vebt_mint summary) 
                            + the (vebt_mint (treeList ! the (vebt_mint summary)))) (Suc (va div 2)))))"])
       apply (metis atLeastLessThan_iff both_member_options_equiv_member dele_bmo_cont_corr le0 length_list_update listlength maxbmo member_bound option.sel sumprop)
       apply (metis both_member_options_equiv_member dele_bmo_cont_corr length_list_update listlength maxbmo member_bound option.sel sumprop)
       apply(sep_auto heap: vebt_maxti_h)
       apply sep_auto
       apply (simp add: ab_semigroup_mult_class.mult.commute)
       apply auto[1] 
       apply(cases "  the(  vebt_maxt  (vebt_delete summary
              (high (2 * 2 ^ (va div 2) * the (vebt_mint summary) + the (vebt_mint (treeList ! the (vebt_mint summary))))  (Suc (va div 2))))) < length treeList")
       using txe 
       apply (metis length_list_update option.sel)
       apply (metis both_member_options_equiv_member dele_bmo_cont_corr listlength maxbmo member_bound option.sel sumprop)
       apply simp
       apply sep_auto
       apply (metis ab_semigroup_mult_class.mult.commute)
       apply sep_auto
       apply(simp add: Let_def)
       apply(cases " high (the (vebt_mint summary) * (2 * 2 ^ (va div 2)) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (Suc (va div 2)) < length treeList")
       apply simp
       apply(cases "minNull  (vebt_delete  (treeList !
                  high (the (vebt_mint summary) * (2 * 2 ^ (va div 2)) + the (vebt_mint (treeList ! the (vebt_mint summary))))  (Suc (va div 2)))
                 (low (the (vebt_mint summary) * (2 * 2 ^ (va div 2)) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (Suc (va div 2))))")
       subgoal
         apply(sep_auto simp: algebra_simps split: if_split)
        done
       subgoal 
         apply(auto split: if_split)
         apply sep_auto 
         prefer 2
         apply(rule  entails_solve_init)
         apply (tactic \<open>Seplogic_Auto.match_frame_tac  (resolve_tac @{context} @{thms ent_refl}) @{context} 1\<close>)
         apply simp
         apply solve_entails 
         apply (simp add: ab_semigroup_mult_class.mult.commute)
         prefer 3
         apply sep_auto 
         apply (metis ab_semigroup_mult_class.mult.commute minminNull)+
        done
       subgoal
         apply(rule  entails_solve_init)
         apply simp
        done
       subgoal 
         apply(simp add: Let_def)
         apply(auto split: if_split)
         apply sep_auto 
         using "7.prems" deg_deg_n nested_mint apply blast
         apply(rule  entails_solve_init)
         apply (tactic \<open>Seplogic_Auto.match_frame_tac  (resolve_tac @{context} @{thms ent_refl}) @{context} 1\<close>) 
         apply simp
         apply solve_entails 
         apply (simp add: ab_semigroup_mult_class.mult.commute)
         using "7.prems" deg_deg_n nested_mint apply blast
         apply sep_auto
         using "7.prems" deg_deg_n nested_mint apply blast 
         using "7.prems" deg_deg_n nested_mint apply blast
         apply(rule  entails_solve_init)
         apply (tactic \<open>Seplogic_Auto.match_frame_tac (resolve_tac @{context} @{thms ent_refl}) @{context} 1\<close>) 
         apply simp
         apply solve_entails 
         apply (simp add: ab_semigroup_mult_class.mult.commute)
         using "7.prems" deg_deg_n nested_mint apply blast
        done
       subgoal 
         apply(simp add: Let_def)
         apply(auto split: if_split)
         apply sep_auto
         apply(rule  entails_solve_init)
         apply (tactic \<open>Seplogic_Auto.match_frame_tac  (resolve_tac @{context} @{thms ent_refl}) @{context} 1\<close>) 
         apply simp
         apply solve_entails 
         apply (simp add: ab_semigroup_mult_class.mult.commute)
         apply (simp add: ab_semigroup_mult_class.mult.commute minminNull)     
        done 
       using "7.prems" deg_deg_n nested_mint apply blast
      done
      apply(auto split: if_split)
      apply sep_auto 
      apply (metis "7.prems" ab_semigroup_mult_class.mult.commute deg_deg_n nested_mint)
      apply (rewrite in "<\<hole>>_<_>" list_assn_conv_idx)
      apply (rewrite in "<\<hole>>_<_>" listI_assn_extract[where i=" high (2 * 2 ^ (va div 2) * the (vebt_mint summary) + the (vebt_mint (treeList ! the (vebt_mint summary)))) (Suc (va div 2))"])
      apply (metis "7.prems" highboundn ab_semigroup_mult_class.mult.commute atLeastLessThan_iff deg_deg_n div2_Suc_Suc leI length_list_update less_nat_zero_code power_Suc xndef)
      apply (metis "7.prems" ab_semigroup_mult_class.mult.commute deg_deg_n length_list_update nested_mint)
      apply(sep_auto)
      apply(sep_auto heap: vebt_maxti_h)
      apply sep_auto 
      apply (simp add: Let_def)
      apply(auto split: if_split)
      apply(simp add: Let_def)
      apply(auto split: if_split)
      apply (metis minNullmin  mulcomm option.simps(3))
      apply (metis minNullmin mulcomm option.distinct(1))
      subgoal
        apply sep_auto
        apply (simp add: ab_semigroup_mult_class.mult.commute)
        apply(rule  listI_assn_reinsert_upd[ where x = "_ ! _"] ) 
        apply(rule midextr)
        apply(rule midextr)
        apply(rule groupy)
        apply(rule ent_refl)
        apply (metis ab_semigroup_mult_class.mult.commute length_list_update)
        apply (metis ab_semigroup_mult_class.mult.commute atLeastLessThan_iff le0)
        apply(fr_rot 1)
        apply(rule swappa)
        apply(simp add:  mulcomm)
        apply(simp add:  listI_assn_conv)
        apply(rule ent_refl)
       done
     using "7.prems" deg_deg_n nested_mint 
     apply blast
     apply sep_auto
     apply(simp add: Let_def)
     apply(auto split: if_split) 
     apply (simp add: minNullmin mulcomm) 
     apply (simp add: ab_semigroup_mult_class.mult.commute minNullmin)
     apply sep_auto
     apply sep_auto 
     using "7.prems" deg_deg_n nested_mint apply blast
     apply(rule swappa)
     apply(simp add: mulcomm)
     apply(rule ent_refl)
    done
    apply simp
    apply(sep_auto heap: highi_h)
    apply (metis "7.prems" deg_deg_n div2_Suc_Suc highbound leI linorder_neqE_nat)
    apply(sep_auto heap: lowi_h)
    apply (metis "7.prems" deg_deg_n div2_Suc_Suc highbound leI linorder_neqE_nat)
    apply sep_auto
    apply (rewrite in "<\<hole>>_<_>" list_assn_conv_idx)
    apply (rewrite in "<\<hole>>_<_>" listI_assn_extract[where i=" high x (Suc (va div 2))"])
    apply (metis "7.prems" atLeastLessThan_iff deg_deg_n div2_Suc_Suc highbound leI le_neq_implies_less less_nat_zero_code)
    apply (metis "7.prems" antisym_conv2 deg_deg_n div2_Suc_Suc highbound not_le_imp_less)
    apply(sep_auto heap: "7.IH"(1))
    apply (metis "7.prems" antisym_conv2 deg_deg_n div2_Suc_Suc highbound not_le_imp_less)
    apply(rule setprop)
    apply (metis "7.prems" antisym_conv2 deg_deg_n div2_Suc_Suc highbound not_le_imp_less nth_mem)
    apply sep_auto 
    apply (metis "7.prems" deg_deg_n div2_Suc_Suc highbound not_le_imp_less order.not_eq_order_implies_strict)
    apply(sep_auto)
    apply(sep_auto heap: vebt_minti_h)
    apply(rule bind_rule)
    apply(rule assert'_rule) 
    apply (meson mod_pure_star_dist mod_starE)
    apply(rule cons_pre_rule)
    apply(rule big_assn_simp'[])
    apply (metis "7.prems" deg_deg_n div2_Suc_Suc highbound leI le_neq_implies_less) apply auto[1]
    apply(cases "vebt_mint (vebt_delete (treeList ! high x (Suc (va div 2))) (low x (Suc (va div 2))))")
    apply simp
    subgoal
      apply sep_auto
      apply(sep_auto heap: "7.IH"(2))
      apply (metis "7.prems" deg_deg_n div2_Suc_Suc highbound leI le_neq_implies_less)
      apply simp+
      apply(simp add: minminNull)
      apply(rule sumprop)
      apply(rule bind_rule'[where R="\<lambda> r.(let sn =  vebt_delete summary (high x (Suc (va div 2))) in ( \<up>(r = (
                                 if x = ma then let maxs = vebt_maxt sn  in if maxs = None then mi
                                         else 2 ^ (Suc (Suc va) div 2) * the maxs + the (vebt_maxt (?newlist' ! the maxs)) else ma))))"])
      apply(cases "x = ma")
      apply simp
      apply(sep_auto)
      apply(sep_auto heap: vebt_maxti_h)
      apply(cases "vebt_maxt (vebt_delete summary (high ma (Suc (va div 2))))")
      apply simp
      apply sep_auto
      apply simp
      apply sep_auto
      apply (metis both_member_options_equiv_member dele_bmo_cont_corr listlength maxbmo member_bound sumprop)
      apply (rewrite in "<\<hole>>_<_>" list_assn_conv_idx)
      apply (rewrite in "<\<hole>>_<_>" listI_assn_extract[where i="the ( vebt_maxt (vebt_delete summary (high ma (Suc (va div 2)))))"])
      apply (metis atLeastLessThan_iff both_member_options_equiv_member dele_bmo_cont_corr le0 length_list_update listlength maxbmo member_bound option.sel sumprop)
      apply (metis both_member_options_equiv_member dele_bmo_cont_corr length_list_update listlength maxbmo member_bound option.sel sumprop)
      apply sep_auto
      apply(sep_auto heap: vebt_maxti_h)
      apply sep_auto
      apply (smt (verit, ccfv_SIG) ab_semigroup_mult_class.mult.commute ab_semigroup_mult_class.mult.left_commute atLeastLessThan_empty_iff2 atLeastLessThan_iff both_member_options_equiv_member deg_deg_n dele_bmo_cont_corr div2_Suc_Suc div_by_Suc_0 div_mult_self1_is_m div_mult_self_is_m empty_iff ent_refl le0 le_neq_implies_less length_list_update listI_assn_extract list_assn_conv_idx listlength maxbmo member_bound mimaxprop numeral_2_eq_2 option.collapse option.distinct(1) sumprop zero_less_Suc)
      apply simp
      apply sep_auto
      apply sep_auto
      apply(simp add: Let_def)
      apply(cases "high ma (Suc (va div 2)) < length treeList")
      apply simp
      apply(simp add: Let_def)
      apply(cases "high ma (Suc (va div 2)) < length treeList")
      apply simp
      apply(cases "minNull (vebt_delete (treeList ! high ma (Suc (va div 2))) (low ma (Suc (va div 2))))")
      apply simp
      apply(simp add: Let_def)
      apply sep_auto
      apply simp     
      apply sep_auto
      apply (meson minminNull)+
      apply simp
      apply(auto split: if_split)
      apply (metis "7.prems" deg_deg_n div2_Suc_Suc highbound le_refl)
      apply sep_auto
      apply (metis "7.prems" deg_deg_n div2_Suc_Suc highbound le_refl)
      apply (metis "7.prems" deg_deg_n div2_Suc_Suc highbound le_refl)
      apply(simp add: Let_def)
      apply(auto split: if_split)
      apply(simp add: Let_def)
      apply(auto split: if_split)
      apply sep_auto+
      apply (meson minminNull)
      apply sep_auto
      apply (metis "7.prems" deg_deg_n div2_Suc_Suc highbound linorder_neqE_nat not_le_imp_less)
     done
    apply simp
    apply(auto split: if_split)
    apply sep_auto
    apply (metis "7.prems" deg_deg_n div2_Suc_Suc dual_order.refl highbound)
    apply (rewrite in "<\<hole>>_<_>" list_assn_conv_idx)
    apply (rewrite in "<\<hole>>_<_>" listI_assn_extract[where i="high ma (Suc (va div 2))"])
    apply (metis "7.prems" atLeastLessThan_iff deg_deg_n div2_Suc_Suc highbound le0 le_refl length_list_update)
    apply (metis "7.prems" deg_deg_n div2_Suc_Suc highbound le_refl length_list_update)
    apply sep_auto
    apply(sep_auto heap: vebt_maxti_h)
    apply sep_auto
    apply(simp add: Let_def)
    apply(auto split: if_split)
    apply(simp add: Let_def)
    apply(auto split: if_split)
    apply(simp add: Let_def)
    subgoal
      apply sep_auto
      apply (metis minNullmin option.distinct)+
     done
    apply sep_auto
    apply(rule ent_trans)
    apply(rule tcd[where treeList'= treeList])
    apply blast+
    apply(rule swappa)    
    apply(rule ent_refl)
    apply sep_auto
    apply (metis "7.prems" deg_deg_n div2_Suc_Suc highbound le_refl)
    apply (metis "7.prems" deg_deg_n div2_Suc_Suc dual_order.refl highbound)
    apply sep_auto
    apply(simp add: Let_def)
    apply(auto split: if_split)
    apply(simp add: Let_def)
    apply(auto split: if_split)
    apply sep_auto
    apply (metis minNullmin option.distinct(1))
    apply sep_auto+
   done
qed

lemma TBOUND_vebt_deletei:
  defines foo_def: "\<And> t x. foo t x \<equiv> if minNull (vebt_delete t x) then 1 else 20 * (1+height t)"
  shows "TBOUND (vebt_deletei' t ti x) (foo t x)"  
proof-
  have fooNull:"minNull (vebt_delete t x) \<Longrightarrow> foo t x = 1" for t x using foo_def by simp
  have fooElse: "foo t x \<le> 20* (1+ height t)" for t using foo_def by simp
  have succ0foo: "Suc 0 \<le> foo t x" for t x unfolding foo_def by simp
  have fooNull': "vebt_mint (vebt_delete t x) = None \<Longrightarrow> foo t x = 1" for t x 
    by (simp add: fooNull minminNull)
  have fooNull'': "vebt_maxt (vebt_delete t x) = None \<Longrightarrow> foo t x = 1" for t x 
    by (metis fooNull fooNull' vebt_maxt.elims minNull.simps(4) vebt_mint.simps(1) option.simps(3))
  have minNotMaxDel: "x12a \<ge> 2 \<Longrightarrow> c \<noteq> d \<Longrightarrow>
    \<not> minNull (vebt_delete (Node (Some (c, d)) x12a x13 x14) y )" for x12a x13 x14 c d y
    apply(cases "( (Node (Some (c, d)) x12a x13 x14), y )" rule: vebt_delete.cases; simp)
    apply(auto simp add: Let_def)
    done
  have twentyheight:" i< length x13 \<Longrightarrow>n * height (x13 !i) \<le> m + n * max (height x14) (Max (height ` set x13))" for i x13 x14 n m
      by (meson height_i_max mult_le_mono2 trans_le_add2)
  have summheight:"n * height x14 \<le> m + n * max (height x14) (Max (height ` set x13))" for x14 x13 m n 
      apply(simp add: max_def)
      apply (meson mult_le_mono2 trans_le_add2)
      done
  show ?thesis
    apply (induction arbitrary: t ti x rule: vebt_deletei'.fixp_induct)  
      apply (rule TBOUND_fi'_adm)
      apply (rule TBOUND_empty) 
      apply TBOUND
      apply(simp add: Let_def  eq_commute[of "Suc 0" "_" ] succ0foo fooNull' fooNull''
              split!: VEBT.splits VEBTi.splits option.splits prod.splits )
      apply(all \<open>(intro allI impI conjI)?\<close>)
      apply(all \<open>(clarify; simp only: succ0foo; fail)?\<close>)
      apply(simp_all add: foo_def minNotMaxDel twentyheight summheight not_less)
    done
  qed

lemma vebt_deletei_refines: "refines (vebt_deletei ti  x) (vebt_deletei' t ti x)"      
  apply (induction arbitrary: t ti x rule: vebt_deletei'.fixp_induct)
  subgoal
   using refines_adm[where t = "\<lambda> arg. vebt_deletei (snd (fst arg)) (snd arg)"]
   by simp 
  subgoal by simp
  subgoal for f t ti x
    apply(subst vebt_deletei.simps)
    apply refines
  done
  done

lemma htt_vebt_deletei: assumes "invar_vebt t n"
  shows  "<vebt_assn_raw t ti> vebt_deletei ti x <\<lambda> r. vebt_assn_raw (vebt_delete t x) r >T[20 + 20*(nat \<lceil>lb n\<rceil>)]"
  apply (rule htt_refine[where c = "vebt_deletei' t ti x"])
  prefer 2
  apply(rule vebt_deletei_refines)
  apply (rule httI_TBOUND)
  apply(rule deleti'_rf_abstr)
  apply(rule assms)
  apply(rule TBOUND_mono)
  apply(rule TBOUND_vebt_deletei)
  apply (auto simp add: if_split)
  apply(metis assms eq_imp_le heigt_uplog_rel int_eq_iff)
  done  

end
end
