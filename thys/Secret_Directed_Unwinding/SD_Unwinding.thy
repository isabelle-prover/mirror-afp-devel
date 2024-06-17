section \<open>Secret-Directed Unwinding\<close>

text \<open> This theory formalizes the secret-directed unwinding disproof method 
for relative security.  \<close>

theory SD_Unwinding
imports Relative_Security.Relative_Security
begin

context Rel_Sec
begin 

(* Similar to validEtransO, move1, move2 and move12, but working with 
lazy lists instead of lists. Note that, unlike in the case of positive-proof
unwinding which works with states and statuses only, here we need 
a lazy-list customized version because of the sequence of secrets arguments.  *)

fun lvalidEtransO where "lvalidEtransO (s,secl) (s',secl') \<longleftrightarrow> 
  validTransV (s,s') \<and> 
  (\<not> isSecV s \<and> secl = secl' \<or> 
   isSecV s \<and> secl = LCons (getSecV s) secl')"

definition "lmove1 \<Gamma> sv1 secl1 sv2 secl2 \<equiv> 
\<forall> sv1' secl1'. lvalidEtransO (sv1,secl1) (sv1',secl1') \<longrightarrow> \<Gamma> sv1' secl1' sv2 secl2"

definition "lmove2 \<Gamma> sv1 secl1 sv2 secl2 \<equiv> 
\<forall> sv2' secl2'. lvalidEtransO (sv2,secl2) (sv2',secl2') \<longrightarrow> \<Gamma> sv1 secl1 sv2' secl2'"  

definition "lmove12 \<Gamma> sv1 secl1 sv2 secl2 \<equiv> 
\<forall> sv1' secl1' sv2' secl2'. 
  lvalidEtransO (sv1,secl1) (sv1',secl1') \<and> lvalidEtransO (sv2,secl2) (sv2',secl2') 
  \<longrightarrow> \<Gamma> sv1' secl1' sv2' secl2'"

definition lunwindSDCond :: 
"('stateV \<Rightarrow> 'secret llist \<Rightarrow> 'stateV \<Rightarrow> 'secret llist \<Rightarrow> bool) \<Rightarrow> bool" 
where 
"lunwindSDCond \<Gamma> \<equiv> \<forall>sv1 secl1 sv2 secl2. 
 reachV sv1 \<and> reachV sv2 \<and> 
 \<Gamma> sv1 secl1 sv2 secl2 
 \<longrightarrow> 
 (isIntV sv1 \<longleftrightarrow> isIntV sv2) \<and> 
 (\<not> isIntV sv1 \<longrightarrow> lmove1 \<Gamma> sv1 secl1 sv2 secl2 \<and> lmove2 \<Gamma> sv1 secl1 sv2 secl2) \<and> 
 (isIntV sv1 \<and> getActV sv1 = getActV sv2 \<longrightarrow> getObsV sv1 = getObsV sv2 \<and> 
                                          lmove12 \<Gamma> sv1 secl1 sv2 secl2)"

lemma lunwindSDCond_imp: 
assumes "lunwindSDCond \<Gamma>" "reachV sv1" "reachV sv2" "\<Gamma> sv1 secl1 sv2 secl2" 
shows 
"(isIntV sv1 \<longleftrightarrow> isIntV sv2) \<and> 
 (\<not> isIntV sv1 \<longrightarrow> lmove1 \<Gamma> sv1 secl1 sv2 secl2 \<and> lmove2 \<Gamma> sv1 secl1 sv2 secl2) \<and> 
 (isIntV sv1 \<and> getActV sv1 = getActV sv2 \<longrightarrow> getObsV sv1 = getObsV sv2 \<and> 
                lmove12 \<Gamma> sv1 secl1 sv2 secl2)"
using assms unfolding lunwindSDCond_def by auto
 
(* The move12 option is available regardless of whether isIntV holds
(but when it doesn't, we do need the separate move1 and move2 too): *)
lemma lunwindSDCond_lmove12:
assumes unw: "lunwindSDCond \<Gamma>" and gam: "reachV sv1" "reachV sv2" "\<Gamma> sv1 secl1 sv2 secl2"
and i: "isIntV sv1 \<longrightarrow> getActV sv1 = getActV sv2"
shows "lmove12 \<Gamma> sv1 secl1 sv2 secl2"
proof(cases "isIntV sv1")
  case True
  then show ?thesis using unw gam i unfolding lunwindSDCond_def by blast
next
  case False
  then show ?thesis using unw gam unfolding lunwindSDCond_def  
  by (smt (verit) Van.reach.Step fst_conv lmove12_def lmove1_def lmove2_def 
    lvalidEtransO.simps snd_conv)
qed 

(* *)

proposition unwindSDCond_aux_inductive:
assumes unw: "lunwindSDCond \<Gamma>"
and 1: "\<Gamma> sv1 secl1 sv2 secl2" 
"reachV sv1" "Van.validFromS sv1 (trv1 @ [ssv1])" "never isIntV trv1" and 11: "isIntV ssv1" and 
2: "reachV sv2" "Van.validFromS sv2 (trv2 @ [ssv2])" "never isIntV trv2" and 22: "isIntV ssv2" and 
3: "lappend (llist_of (Van.S trv1)) ssecl1 = secl1" "lappend (llist_of (Van.S trv2)) ssecl2 = secl2" 
shows "\<Gamma> (lastt sv1 trv1) ssecl1 (lastt sv2 trv2) ssecl2"
using 1 2 3 proof(induct "length trv1 + length trv2" arbitrary: sv1 sv2 trv1 trv2 secl1 secl2 rule: nat_less_induct)
  case (1 trv1 trv2 sv1 sv2 secl1 secl2)
  show ?case 
  proof(cases "isIntV sv1")
    case True hence sv2: "isIntV sv2" using 1(2-) unw unfolding lunwindSDCond_def by auto
    note isv12 = True this

    have trv1: "trv1 = []" using True 1(4,5) unfolding list_all_nth apply(cases trv1, auto) 
     by (metis Van.validFromS_Cons_iff nth_Cons_0 zero_less_Suc)
    have trv2: "trv2 = []" using sv2 1(7,8) unfolding list_all_nth apply(cases trv2, auto) 
     by (metis Van.validFromS_Cons_iff nth_Cons_0 zero_less_Suc)

    show ?thesis using 1(2-) by (simp add: trv1 trv2 Van.S_def)  
  next
    case False hence "\<not> isIntV sv2" using 1(2-) unw unfolding lunwindSDCond_def by auto
    note isv12 = False this
    have trv1ne: "trv1 \<noteq> []" using isv12 "1.prems"(3) "11" by force
    then obtain sv1' trv1' where trv1: "trv1 = sv1 # trv1'" "validTransV (sv1,sv1')" 
    "Van.validFromS sv1' trv1'" "never isIntV trv1'" 
    using `Van.validFromS sv1 (trv1 @ [ssv1])` `never isIntV trv1` 
    by (metis Simple_Transition_System.validFromS_Cons_iff Simple_Transition_System.validFromS_def 
      Simple_Transition_System.validS_append1 
     Simple_Transition_System.validS_validTrans hd_append2 list_all_simps(1) neq_Nil_conv snoc_eq_iff_butlast)
    have trv2ne: "trv2 \<noteq> []" using isv12 "1.prems"(6) "22" by force
    then obtain sv2' trv2' where trv2: "trv2 = sv2 # trv2'" "validTransV (sv2,sv2')" 
    "Van.validFromS sv2' trv2'" "never isIntV trv2'" 
    using `Van.validFromS sv2 (trv2 @ [ssv2])` `never isIntV trv2` 
    by (metis Simple_Transition_System.validFromS_Cons_iff Simple_Transition_System.validFromS_def 
      Simple_Transition_System.validS_append1 
     Simple_Transition_System.validS_validTrans hd_append2 list_all_simps(1) neq_Nil_conv snoc_eq_iff_butlast)

    show ?thesis 
    proof(cases "length trv1 = Suc 0 \<and> length trv2 = Suc 0") 
     case True
     hence trv12: "trv1 = [sv1] \<and> trv2 = [sv2]" apply(intro conjI) 
       subgoal using 1(4) Van.validFromS_Cons_iff by (cases trv1, auto)
       subgoal using 1(7) Van.validFromS_Cons_iff by (cases trv2, auto) .
     show ?thesis using 1(2) "1.prems"(8,9) trv12 unfolding lastt_def 
     using Van.S.FiltermapBL FiltermapBL.simps(4) by fastforce
    next
     case False note f = False
     show ?thesis 
     proof(cases "length trv1 = Suc 0")
       case True
       hence "length trv2 > Suc 0" using f trv2ne by (simp add: Suc_lessI)
       hence trv2'ne: "trv2' \<noteq> []" by (simp add: trv2(1))

       define secl2' where "secl2' \<equiv> if isSecV sv2 then ltl secl2 else secl2"
       have v2: "lvalidEtransO (sv2,secl2) (sv2',secl2')"
       using trv2 unfolding lvalidEtransO.simps secl2'_def  
       using "1.prems"(9) trv2'ne Van.S.FiltermapBL FiltermapBL.simps(3) by fastforce
       have sl2':  "secl2' = lappend (llist_of (Van.S trv2')) ssecl2"  
       using "1.prems"(9) trv2(1) v2 by (auto simp: trv2'ne)
       have r2': "reachV sv2'" 
       by (metis "1.prems"(5) Van.reach.Step fst_conv snd_conv trv2(2))

       have gam: "\<Gamma> sv1 secl1 sv2' secl2'"
       using `\<Gamma> sv1 secl1 sv2 secl2` v2 unw r2' isv12 unfolding lunwindSDCond_def lmove2_def  
       using 1(2-) by blast

       have gam': "\<Gamma> (lastt sv1 trv1) ssecl1 (lastt sv2' trv2') ssecl2"
       apply(rule 1(1)[rule_format, OF _ _ gam])  
       using trv2 gam sl2' `reachV sv1` `reachV sv2` r2'  
       using "1.prems"(3,4,6,8) 
       by auto (metis Van.validFromS_Cons_iff Van.validFromS_def hd_append trv2'ne)
  
       show ?thesis unfolding trv2 using gam' trv2'ne unfolding lastt_def by auto  
     next
       case False
       hence "length trv1 > Suc 0" using f trv1ne by (simp add: Suc_lessI)
       hence trv1'ne: "trv1' \<noteq> []" by (simp add: trv1(1))

       define secl1' where "secl1' \<equiv> if isSecV sv1 then ltl secl1 else secl1"
       have v1: "lvalidEtransO (sv1,secl1) (sv1',secl1')"
       using trv1  unfolding lvalidEtransO.simps secl1'_def  
       using "1.prems"(8) trv1'ne Van.S.FiltermapBL FiltermapBL.Cons_unfold by fastforce
       have sl1':  "secl1' = lappend (llist_of (Van.S trv1')) ssecl1"  
       using "1.prems"(8) trv1(1) v1 by (auto simp: trv1'ne) 
       have r1': "reachV sv1'" 
       by (metis "1.prems"(2) Van.reach.Step fst_conv snd_conv trv1(2))

       have gam: "\<Gamma> sv1' secl1' sv2 secl2"
       using `\<Gamma> sv1 secl1 sv2 secl2` v1 unw r1' isv12 unfolding lunwindSDCond_def lmove1_def  
       using 1(2-) by blast

       have gam': "\<Gamma> (lastt sv1' trv1') ssecl1 (lastt sv2 trv2) ssecl2"
       apply(rule 1(1)[rule_format, OF _ _ gam])  
       using trv1 gam sl1' `reachV sv2` `reachV sv1` r1'  
       using "1.prems"  
       by auto (metis Van.validFromS_Cons_iff Van.validFromS_def hd_append trv1'ne)
  
       show ?thesis unfolding trv1 using gam' trv1'ne unfolding lastt_def by auto 
     qed
    qed
  qed
qed

proposition unwindSDCond_inductive:
assumes unw: "lunwindSDCond \<Gamma>" 
and gam: "\<Gamma> sv1 secl1 sv2 secl2" and 
trv1: "reachV sv1" "Van.validFromS sv1 (trv1 @ [ssv1])" "never isIntV trv1" "isIntV ssv1"  and 
trv2: "reachV sv2" "Van.validFromS sv2 (trv2 @ [ssv2])" "never isIntV trv2" "isIntV ssv2" and 
s: "lappend (llist_of (map getSecV (filter isSecV trv1))) ssecl1 = secl1" 
   "lappend (llist_of (map getSecV (filter isSecV trv2))) ssecl2 = secl2" 
shows "(getActV ssv1 = getActV ssv2 \<longrightarrow> \<Gamma> ssv1 ssecl1 ssv2 ssecl2) \<and> 
       (getActV ssv1 = getActV ssv2 \<longrightarrow> getObsV ssv1 = getObsV ssv2)"
proof-
  define ssecl1' where "ssecl1' = (if trv1 = [] \<or> (trv1 \<noteq> [] \<and> \<not> isSecV (last trv1)) then ssecl1 else (getSecV (last trv1)) $ ssecl1)"
  define ssecl2' where "ssecl2' = (if trv2 = [] \<or> (trv2 \<noteq> [] \<and>  \<not> isSecV (last trv2)) then ssecl2 else (getSecV (last trv2)) $ ssecl2)"
  have s': "lappend (llist_of (Van.S trv1)) ssecl1' = secl1" 
          "lappend (llist_of (Van.S trv2)) ssecl2' = secl2" 
  subgoal unfolding ssecl1'_def s[symmetric] Van.S.map_filter 
  by simp (metis List_Filtermap.filtermap_def filtermap_butlast holds_filtermap_RCons lappend_llist_of_LCons snoc_eq_iff_butlast)
  subgoal unfolding ssecl2'_def s[symmetric] Van.S.map_filter 
  by simp (metis List_Filtermap.filtermap_def append_butlast_last_id filtermap_butlast holds_filtermap_RCons lappend_llist_of_LCons) . 
 
  have gg: "\<Gamma> (lastt sv1 trv1) ssecl1' (lastt sv2 trv2) ssecl2'"
  using unwindSDCond_aux_inductive[OF unw gam trv1 trv2 s'] .
  have rsv1: "reachV (lastt sv1 trv1)" 
  by (metis Van.reach_validFromS_reach Van.validFromS_def Van.validS_append1 
  append_is_Nil_conv assms(3) assms(4) hd_append lastt_def)
  have rsv2: "reachV (lastt sv2 trv2)" 
  by (metis Van.lvalidFromS_lappend_finite Van.lvalidFromS_llist_of_validFromS 
  Van.reach_validFromS_reach assms(7) assms(8) lappend_llist_of_llist_of lastt_def)

  have "trv1 = [] \<longleftrightarrow> trv2 = []" using trv1(2-4) trv2(2-4) unfolding list_all_nth 
  apply safe
    subgoal by simp (smt (verit) Simple_Transition_System.validFromS_def assms(3) assms(7) gam 
    hd_append hd_conv_nth length_greater_0_conv lunwindSDCond_def snoc_eq_iff_butlast unw)
    subgoal by simp (smt (verit) Simple_Transition_System.validFromS_def assms(3) assms(7) gam 
    hd_append hd_conv_nth length_greater_0_conv lunwindSDCond_def snoc_eq_iff_butlast unw) .

  hence ddd: "(trv1 = [] \<and> trv2 = []) \<or> (trv1 \<noteq> [] \<and> trv2 \<noteq> [])" by blast

  show ?thesis
  using ddd proof(elim conjE disjE)
    assume trv12: "trv1 = []" "trv2 = []"
    hence sv12: "ssv1 = lastt sv1 trv1" "ssv2 = lastt sv2 trv2" and sv12': "ssv1 = sv1" "ssv2 = sv2"
    and secl: "ssecl1 = ssecl1'" "ssecl2 = ssecl2'"
    using trv1(2) trv2(2) ssecl1'_def ssecl2'_def by auto
    
    show ?thesis proof safe
     show g: "\<Gamma> ssv1 ssecl1 ssv2 ssecl2" unfolding sv12 secl using gg .
     assume "getActV ssv1 = getActV ssv2"
     thus "getObsV ssv1 = getObsV ssv2" 
     using lunwindSDCond_imp[OF unw rsv1 rsv2, unfolded sv12[symmetric], OF g] trv1(4) by auto
    qed
  next
    assume trv12: "trv1 \<noteq> []" "trv2 \<noteq> []"
    have n: "\<not> isIntV (last trv1)"  
      by (metis append_butlast_last_id list.pred_inject(2) list_all_append trv1(3) trv12(1))
    have v1: "validTransV (lastt sv1 trv1, ssv1)" 
    by (metis Van.validFromS_def Van.validS_validTrans lastt_def list.sel(1) not_Cons_self snoc_eq_iff_butlast trv1(2) trv12(1))
    have v2: "validTransV (lastt sv2 trv2, ssv2)" 
    by (metis Nil_is_append_conv Van.validFromS_def Van.validS_validTrans lastt_def list.discI list.sel(1) trv12(2) trv2(2))
    show ?thesis proof safe
     assume gssv12: "getActV ssv1 = getActV ssv2"
     show g: "\<Gamma> ssv1 ssecl1 ssv2 ssecl2"  
     apply(rule lunwindSDCond_lmove12[OF unw rsv1 rsv2 gg, unfolded lmove12_def, rule_format])
     unfolding lvalidEtransO.simps ssecl1'_def ssecl2'_def
     using trv12 v1 v2 n by (auto simp: lastt_def)  
     
     show "getObsV ssv1 = getObsV ssv2" using gssv12
     using lunwindSDCond_imp[OF unw _ _ g]  
     by (metis Van.reach.Step fst_conv rsv1 rsv2 snd_conv trv1(4) v1 v2) 
    qed
  qed
qed

proposition lunwindSDCond_aux:
assumes unw: "lunwindSDCond \<Gamma>"
and 1: "\<Gamma> sv1 secl1 sv2 secl2" 
"reachV sv1" "Van.lvalidFromS sv1 trv1" "lcompletedFromV sv1 trv1"
"reachV sv2" "Van.lvalidFromS sv2 trv2" "lcompletedFromV sv2 trv2"
"Van.lS trv1 = secl1" "Van.lS trv2 = secl2" 
"Van.lA trv1 = Van.lA trv2"
shows "Van.lO trv1 = Van.lO trv2" 
proof-
  {fix obl1 obl2
   assume "\<exists>sv1 trv1 secl1 sv2 trv2 secl2. obl1 = Van.lO trv1 \<and> obl2 = Van.lO trv2 \<and> 
    \<Gamma> sv1 secl1 sv2 secl2 \<and> 
    reachV sv1 \<and> Van.lvalidFromS sv1 trv1 \<and> lcompletedFromV sv1 trv1 \<and> 
    reachV sv2 \<and> Van.lvalidFromS sv2 trv2 \<and> lcompletedFromV sv2 trv2 \<and> 
    Van.lS trv1 = secl1 \<and> Van.lS trv2 = secl2 \<and> Van.lA trv1 = Van.lA trv2"
   hence "obl1 = obl2"
   proof (coinduct rule: llist.coinduct)
     case (Eq_llist obl1 obl2)
     then obtain sv1 trv1 secl1 sv2 trv2 secl2 where obl: "obl1 = Van.lO trv1" "obl2 = Van.lO trv2"
     and gam: "\<Gamma> sv1 secl1 sv2 secl2"
     and trv1: "reachV sv1" "Van.lvalidFromS sv1 trv1" "lcompletedFromV sv1 trv1"
     and trv2: "reachV sv2" "Van.lvalidFromS sv2 trv2" "lcompletedFromV sv2 trv2" 
     and Str: "Van.lS trv1 = secl1" "Van.lS trv2 = secl2" and Atr: "Van.lA trv1 = Van.lA trv2"
     by blast
     show ?case proof(intro conjI impI)
      show lnull: "lnull obl1 = lnull obl2" 
      using obl Atr unfolding lnull_def 
      by (metis LNil_eq_lmap Van.lA.lmap_lfilter Van.lO.lmap_lfilter)

      assume ln:  "\<not> lnull obl1" "\<not> lnull obl2"
      then obtain ob1 obl1' ob2 obl2' where 
      obl1: "obl1 = LCons ob1 obl1'" and obl2: "obl2 = LCons ob2 obl2'"
      unfolding lnull_def using llist.exhaust_sel by blast
      hence lhd: "lhd obl1 = ob1" "lhd obl2 = ob2" 
      and ltl: "ltl obl1 = obl1'" "ltl obl2 = obl2'" 
      by auto

      obtain ftrv1 sv1' trv1' where 
      trv1_eq: "trv1 = lappend (llist_of ftrv1) (sv1' $ trv1')" and ftrv1a: "never isIntV ftrv1"
      and sv1': "isIntV sv1'" "getObsV sv1' = ob1" and trv1': "Van.lO trv1' = obl1'"
      using Van.lO.eq_LCons[OF obl(1)[symmetric, unfolded obl1]] by auto
      define sv11 where "sv11 = lastt sv1 ftrv1"
      have trv11': "Van.lvalidFromS sv1' (sv1' $ trv1')" 
      and ftrv1b: "Van.validFromS sv1 ftrv1" 
      "(ftrv1 = [] \<and> sv1 = sv1' \<and> sv11 = sv1) \<or> (ftrv1 \<noteq> [] \<and> validTransV (sv11, sv1'))"
      using trv1(2) 
      unfolding trv1_eq unfolding Van.lvalidFromS_lappend_LCons
      unfolding lastt_def sv11_def by auto
      note ftrv1 = ftrv1a ftrv1b
      have fftrv1: "filter isIntV ftrv1 = []" by (metis ftrv1(1) never_Nil_filter)
      have ftrv1c: "Van.validFromS sv1 (ftrv1 @ [sv1'])"

      by (metis Van.lvalidFromS_lappend_finite lappend_llist_of_LCons trv1(2) trv1_eq)  
      define ssv1' where "ssv1' \<equiv> if trv1' = [[]] then sv1' else lhd trv1'"
      
      obtain ftrv2 sv2' trv2' where 
      trv2_eq: "trv2 = lappend (llist_of ftrv2) (sv2' $ trv2')" and ftrv2a: "never isIntV ftrv2"
      and sv2': "isIntV sv2'" "getObsV sv2' = ob2" and trv2': "Van.lO trv2' = obl2'"
      using Van.lO.eq_LCons[OF obl(2)[symmetric, unfolded obl2]] by auto
      define sv22 where "sv22 = lastt sv2 ftrv2"
      have trv22': "Van.lvalidFromS sv2' (sv2' $ trv2')" 
      and ftrv2b: "Van.validFromS sv2 ftrv2" 
      "(ftrv2 = [] \<and> sv2 = sv2' \<and> sv22 = sv2) \<or> (ftrv2 \<noteq> [] \<and> validTransV (sv22, sv2'))"
      using trv2(2) 
      unfolding trv2_eq unfolding Van.lvalidFromS_lappend_LCons
      unfolding lastt_def sv22_def by auto
      note ftrv2 = ftrv2a ftrv2b
      have fftrv2: "filter isIntV ftrv2 = []" by (metis ftrv2(1) never_Nil_filter)
      have ftrv2c: "Van.validFromS sv2 (ftrv2 @ [sv2'])"   
      by (metis Van.lvalidFromS_lappend_finite lappend_llist_of_LCons trv2(2) trv2_eq)
      
      define ssv2' where "ssv2' \<equiv> if trv2' = [[]] then sv2' else lhd trv2'"
      have rsv1': "reachV sv1'"  
        by (metis Van.reach.Step Van.reach_validFromS_reach 
                fst_conv ftrv1b(1) ftrv1b(2) lastt_def sv11_def snd_conv trv1(1))
      have rsv2': "reachV sv2'"  
        by (metis Van.reach.Step Van.reach_validFromS_reach fst_conv ftrv2b(1) 
          ftrv2b(2) lastt_def sv22_def snd_conv trv2(1))

      have rsv11: "reachV sv11" 
        by (metis Van.reach_validFromS_reach ftrv1b(1) lastt_def sv11_def trv1(1))
      have rsv22: "reachV sv22" 
        by (metis Van.reach_validFromS_reach ftrv2b(1) lastt_def sv22_def trv2(1))

      define secl1' secl2' where secl1': "secl1' \<equiv> Van.lS trv1'" and secl2': "secl2' \<equiv> Van.lS trv2'"
 
      define ssecl1' where "ssecl1' \<equiv> Van.lS (sv1' $ trv1')"
      define ssecl2' where "ssecl2' \<equiv> Van.lS (sv2' $ trv2')" 

      have trv12'ne: "trv1' \<noteq> [[]] \<and> trv2' \<noteq> [[]]"  
      by (metis Van.lO.lmap_lfilter Van.lO.simps(4) fftrv1 fftrv2 lappend_LNil2 lbutlast_lappend 
      lbutlast_singl lfilter_LNil lfilter_llist_of llist.distinct(1) llist_of.simps(1) obl(1) obl(2) obl1 obl2 trv1_eq trv2_eq)


      have gasv12': "getActV sv1' = getActV sv2'" using Atr trv12'ne unfolding trv1_eq trv2_eq 
      unfolding Van.lA.lmap_lfilter 
      using fftrv1 fftrv2 sv1'(1) sv2'(1) 
      by (auto simp: lbutlast_lappend lmap_lappend_distrib lappend_eq_LNil_iff split: if_splits)

      have ggam_gao: "(getActV sv1' = getActV sv2' \<longrightarrow> \<Gamma> sv1' ssecl1' sv2' ssecl2') \<and> (getActV sv1' = getActV sv2' \<longrightarrow> getObsV sv1' = getObsV sv2')" 
      apply(rule unwindSDCond_inductive[OF unw gam 
        trv1(1) ftrv1c ftrv1(1) sv1'(1)
        trv2(1) ftrv2c ftrv2(1) sv2'(1)
        ])
        subgoal unfolding Str(1)[symmetric] unfolding trv1_eq 
        unfolding ssecl1'_def sv11_def Van.S.map_filter Van.lS.lmap_lfilter
        by (auto simp: lastt_def lbutlast_lappend lmap_lappend_distrib lappend_eq_LNil_iff split: if_splits)   
        subgoal unfolding Str(2)[symmetric] unfolding trv2_eq 
        unfolding ssecl2'_def sv11_def Van.S.map_filter Van.lS.lmap_lfilter
        by (auto simp: lastt_def lbutlast_lappend lmap_lappend_distrib lappend_eq_LNil_iff) .
      note ggam = ggam_gao[THEN conjunct1, rule_format, OF gasv12']  note gao = ggam_gao[THEN conjunct2, rule_format, OF gasv12']
       
      have "getObsV sv1' = getObsV sv2'" using gao gasv12' by simp
     
      thus "lhd obl1 = lhd obl2"   
      unfolding lhd sv1'(2)[symmetric] sv2'(2)[symmetric] .

      show "\<exists>sv1 trv1 secl1 sv2 trv2 secl2.
      ltl obl1 = Van.lO trv1 \<and> ltl obl2 = Van.lO trv2 \<and>
      \<Gamma> sv1 secl1 sv2 secl2 \<and>
      reachV sv1 \<and> Van.lvalidFromS sv1 trv1 \<and> lcompletedFromV sv1 trv1 \<and>
      reachV sv2 \<and> Van.lvalidFromS sv2 trv2 \<and> lcompletedFromV sv2 trv2 \<and> 
      Van.lS trv1 = secl1 \<and> Van.lS trv2 = secl2 \<and> Van.lA trv1 = Van.lA trv2"
      proof(intro exI[of _ ssv1'] exI[of _ trv1'], rule exI[of _ secl1'], 
            intro exI[of _ ssv2'] exI[of _ trv2'], rule exI[of _ secl2'], 
            intro conjI)
        show "reachV ssv1'"  
        unfolding ssv1'_def using rsv1' apply(cases "trv1' = [[]]", simp_all)
        by (metis Van.lvalidFromS_Cons_iff Van.reach.simps fst_conv snd_conv trv11')
        show "reachV ssv2'"  
        unfolding ssv2'_def using rsv2' apply(cases "trv2' = [[]]", simp_all)
        by (metis Van.lvalidFromS_Cons_iff Van.reach.simps fst_conv snd_conv trv22')       
        show "ltl obl1 = Van.lO trv1'" unfolding ltl trv1' ..
        show "ltl obl2 = Van.lO trv2'" unfolding ltl trv2' ..
        
        show "Van.lvalidFromS ssv1' trv1'" using trv11' Van.lvalidFromS_Cons_iff ssv1'_def by auto
        show lc1': "lcompletedFromV ssv1' trv1'" using trv1(3) unfolding trv1_eq
        unfolding Van.lcompletedFrom_def 
        by (metis lfinite_code(2) lfinite_lappend lfinite_llist_of llast_LCons2 
        llast_lappend_LCons llast_last_llist_of llist.exhaust_sel trv12'ne)
        show "Van.lvalidFromS ssv2' trv2'" using trv22' Van.lvalidFromS_Cons_iff ssv2'_def by auto
        show lc2': "lcompletedFromV ssv2' trv2'" using trv2(3) unfolding trv2_eq
        unfolding Van.lcompletedFrom_def 
        by (metis lfinite_code(2) lfinite_lappend lfinite_llist_of llast_LCons2 llast_lappend_LCons llast_last_llist_of llist.exhaust_sel trv12'ne) 
     
        show "Van.lA trv1' = Van.lA trv2'" 
        using Atr unfolding trv1_eq trv2_eq using ftrv1(1) ftrv2(1) sv1'(1) sv2'(1)
        unfolding Van.lA.lmap_lfilter 
        by (simp add: fftrv1 fftrv2 lbutlast_lappend trv12'ne) 

        show "Van.lS trv1' = secl1'" unfolding secl1' ..
        show "Van.lS trv2' = secl2'" unfolding secl2' ..
      
        show "\<Gamma> ssv1' secl1' ssv2' secl2'" 
        apply(rule lunwindSDCond_lmove12[OF unw rsv1' rsv2' ggam, unfolded lmove12_def, rule_format, OF gasv12'])
          apply(rule conjI)
          subgoal unfolding lvalidEtransO.simps apply(rule conjI)
           subgoal using trv12'ne Van.lvalidFromS_Cons_iff trv11' unfolding ssv1'_def by auto
           subgoal using trv12'ne unfolding ssecl1'_def secl1' by (auto simp: Van.lS.lmap_lfilter) .
          subgoal unfolding lvalidEtransO.simps apply(rule conjI)
           subgoal using trv12'ne Van.lvalidFromS_Cons_iff trv22' unfolding ssv2'_def by auto
           subgoal using trv12'ne unfolding ssecl2'_def secl2' by (auto simp: Van.lS.lmap_lfilter) . .              
      qed
     qed
   qed
  }
  thus ?thesis using assms by blast
qed

theorem unwindSD_lrsecure: 
assumes tr14: "istateO s1" "Opt.lvalidFromS s1 tr1" "lcompletedFromO s1 tr1"
"istateO s2" "Opt.lvalidFromS s2 tr2" "lcompletedFromO s2 tr2"
"Opt.lA tr1 = Opt.lA tr2" "Opt.lO tr1 \<noteq> Opt.lO tr2" 
and init: "\<And>sv1 sv2. istateV sv1 \<Longrightarrow> corrState sv1 s1 \<Longrightarrow> istateV sv2 \<Longrightarrow> corrState sv2 s2 \<Longrightarrow> 
   \<Gamma> sv1 (Opt.lS tr1) sv2 (Opt.lS tr2)"
and unw: "lunwindSDCond \<Gamma>"
shows "\<not> lrsecure"
unfolding lrsecure_def2 unfolding not_all not_imp
apply(rule exI[of _ s1]) apply(rule exI[of _ tr1])
apply(rule exI[of _ s2]) apply(rule exI[of _ tr2])
apply(rule conjI)
  subgoal using tr14 by auto 
  subgoal unfolding not_ex apply safe 
  subgoal for sv1 trv1 sv2 trv2 apply(erule cnf.clause2raw_notE[of "Van.lO trv1 \<noteq> Van.lO trv2"], simp)
  apply(rule lunwindSDCond_aux[OF unw, OF init]) 
  using Van.Istate by auto . .

end (* context Rel_Sec *)

end 