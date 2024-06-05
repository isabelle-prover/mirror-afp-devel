section \<open>Finitary Secret-Directed Unwinding\<close>

text \<open> This theory formalizes the finitary version of secret-directed unwinding, which allows one 
to disprove finitary relative security. \<close>

theory SD_Unwinding_fin
imports Relative_Security.Relative_Security
begin

context Rel_Sec
begin 

fun validEtransO where "validEtransO (s,secl) (s',secl') \<longleftrightarrow> 
  validTransV (s,s') \<and> 
  (\<not> isSecV s \<and> secl = secl' \<or> 
   isSecV s \<and> secl = getSecV s # secl')"

definition "move1 \<Gamma> sv1 secl1 sv2 secl2 \<equiv> 
\<forall> sv1' secl1'. validEtransO (sv1,secl1) (sv1',secl1') \<longrightarrow> \<Gamma> sv1' secl1' sv2 secl2"

definition "move2 \<Gamma> sv1 secl1 sv2 secl2 \<equiv> 
\<forall> sv2' secl2'. validEtransO (sv2,secl2) (sv2',secl2') \<longrightarrow> \<Gamma> sv1 secl1 sv2' secl2'"  

definition "move12 \<Gamma> sv1 secl1 sv2 secl2 \<equiv> 
\<forall> sv1' secl1' sv2' secl2'. 
  validEtransO (sv1,secl1) (sv1',secl1') \<and> validEtransO (sv2,secl2) (sv2',secl2') 
  \<longrightarrow> \<Gamma> sv1' secl1' sv2' secl2'"


definition unwindSDCond :: 
"('stateV \<Rightarrow> 'secret list \<Rightarrow> 'stateV \<Rightarrow> 'secret list \<Rightarrow> bool) \<Rightarrow> bool" 
where 
"unwindSDCond \<Gamma> \<equiv> \<forall>sv1 secl1 sv2 secl2. 
 reachV sv1 \<and> reachV sv2 \<and> 
 \<Gamma> sv1 secl1 sv2 secl2 
 \<longrightarrow> 
 (isIntV sv1 \<longleftrightarrow> isIntV sv2) \<and> 
 (\<not> isIntV sv1 \<longrightarrow> move1 \<Gamma> sv1 secl1 sv2 secl2 \<and> move2 \<Gamma> sv1 secl1 sv2 secl2) \<and> 
 (isIntV sv1 \<longrightarrow> getActV sv1 = getActV sv2 \<longrightarrow> getObsV sv1 = getObsV sv2 \<and> 
                                            move12 \<Gamma> sv1 secl1 sv2 secl2)"

proposition unwindSDCond_aux:
assumes unw: "unwindSDCond \<Gamma>"
and 1: "\<Gamma> sv1 secl1 sv2 secl2" 
"reachV sv1" "Van.validFromS sv1 trv1" "completedFromV sv1 trv1"
"reachV sv2" "Van.validFromS sv2 trv2" "completedFromV sv2 trv2"
"Van.S trv1 = secl1" "Van.S trv2 = secl2" 
"Van.A trv1 = Van.A trv2"
shows "Van.O trv1 = Van.O trv2"  
using 1 proof(induct "length trv1 + length trv2" arbitrary: sv1 sv2 trv1 trv2 secl1 secl2 rule: nat_less_induct)
  case (1 trv1 trv2 sv1 sv2 secl1 secl2)
  show ?case 
  proof(cases "isIntV sv1")
    case True hence "isIntV sv2" using 1(2-) unw unfolding unwindSDCond_def by auto
    note isv12 = True this

    have "\<not> finalV sv1" using isv12 Van.final_not_isInt by auto
    then obtain sv1' trv1' where trv1: "trv1 = sv1 # trv1'" "validTransV (sv1,sv1')" 
    "Van.validFromS sv1' trv1'" "completedFromV sv1' trv1'"
    using 1 by (metis Van.completed_Cons Van.completed_Nil Van.validFromS_Cons_iff list.exhaust)
    have "\<not> finalV sv2" using isv12 Van.final_not_isInt by auto
    then obtain sv2' trv2' where trv2: "trv2 = sv2 # trv2'" "validTransV (sv2,sv2')" 
    "Van.validFromS sv2' trv2'" "completedFromV sv2' trv2'"
    using 1 by (metis Van.completed_Cons Van.completed_Nil Van.validFromS_Cons_iff list.exhaust)

    define secl1' where "secl1' \<equiv> if isSecV sv1 then tl secl1 else secl1"
    have v1: "validEtransO (sv1,secl1) (sv1',secl1')"
    using trv1 unfolding validEtransO.simps secl1'_def 
    using 1 \<open>\<not> finalV sv1\<close> 
    by (auto simp add: Van.S_def)

    define secl2' where "secl2' \<equiv> if isSecV sv2 then tl secl2 else secl2"
    have v2: "validEtransO (sv2,secl2) (sv2',secl2')"
    using trv2 unfolding validEtransO.simps secl2'_def 
    using 1 \<open>\<not> finalV sv2\<close> by (auto simp add: Van.S_def)

    have sl12': "secl1' = Van.S trv1'" "secl2' = Van.S trv2'" 
    using 1(2-) trv1 trv2 unfolding secl1'_def secl2'_def by (auto simp add: Van.S_def)

    have r12': "reachV sv1' \<and> reachV sv2'" 
      by (metis "1.prems"(2) "1.prems"(5) Van.reach.Step fst_conv snd_conv trv1(2) trv2(2))

    have gasv12: "getActV sv1 = getActV sv2" using `Van.A trv1 = Van.A trv2` isv12 unfolding trv1 trv2
    using "1.prems"(4) "1.prems"(7) \<open>\<not> finalV sv2\<close> trv1(1) trv2(1) by auto  
    hence osv12: "getObsV sv1 = getObsV sv2"  
      using `\<Gamma> sv1 secl1 sv2 secl2` "1.prems"(2,5) isv12 unw unfolding unwindSDCond_def by auto

    have gam: "\<Gamma> sv1' secl1' sv2' secl2'"
    using `\<Gamma> sv1 secl1 sv2 secl2` v1 v2 unw r12' isv12 gasv12 unfolding unwindSDCond_def move12_def  
    using 1(2-) by blast  

    have A12: "Van.A trv1' = Van.A trv2'"  
    using "1.prems"(10) "1.prems"(4) "1.prems"(7) True isv12(2) trv1(1) trv2(1) by fastforce

    have O12': "Van.O trv1' = Van.O trv2'"
    apply(rule 1(1)[rule_format]) using trv1 trv2 gam sl12' r12' A12 by auto

    thus ?thesis unfolding trv1(1) trv2(1) using isv12 osv12 
      using "1.prems"(4) "1.prems"(7) \<open>\<not> finalV sv1\<close> \<open>\<not> finalV sv2\<close> trv1(1) trv2(1) by auto
  next
    case False hence "\<not> isIntV sv2" using 1(2-) unw unfolding unwindSDCond_def by auto
    note isv12 = False this

    show ?thesis 
    proof(cases "length trv1 \<le> 1")
      case True note trv1 = True
      show ?thesis 
      proof(cases "length trv2 \<le> 1")
        case True thus ?thesis  
        using One_nat_def Van.O.length_Nil trv1 by presburger
      next
        case False  
        then obtain sv2' trv2' where trv2: "trv2 = sv2 # trv2'" "validTransV (sv2,sv2')" 
        "Van.validFromS sv2' trv2'" "completedFromV sv2' trv2'" 
        using `Van.validFromS sv2 trv2` `completedFromV sv2 trv2`  
        by (smt (z3) One_nat_def Van.completed_Cons Van.length_toS Van.toS_eq_Nil 
             Van.toS_fromS_nonSingl Van.toS_length_gt_eq Van.validFromS_Cons_iff diff_Suc_1 
             diff_is_0_eq le_SucI length_Suc_conv list.size(3))
        define secl2' where "secl2' \<equiv> if isSecV sv2 then tl secl2 else secl2"
        have v2: "validEtransO (sv2,secl2) (sv2',secl2')"
        using trv2 unfolding validEtransO.simps secl2'_def 
        using "1.prems"(7) "1.prems"(9) Van.final_def by auto
        have sl2':  "secl2' = Van.S trv2'" 
        using 1(2-) trv1 trv2 unfolding secl2'_def by auto
        have r2': "reachV sv2'" 
        by (metis "1.prems"(5) Van.reach.Step fst_conv snd_conv trv2(2))

        have gam: "\<Gamma> sv1 secl1 sv2' secl2'"
        using `\<Gamma> sv1 secl1 sv2 secl2` v2 unw r2' isv12 unfolding unwindSDCond_def move2_def  
        using 1(2-) by blast

        have A12: "Van.A trv1 = Van.A trv2'" 
        by (simp add: "1.prems"(10) isv12(2) trv2(1)) 
 
        have O12': "Van.O trv1 = Van.O trv2'"
        apply(rule 1(1)[rule_format, OF _ _ gam])
        using trv1 trv2 gam sl2' r2' A12 1(2-) by auto

        thus ?thesis unfolding trv1(1) trv2(1) using isv12 by auto  
      qed
    next
      case False  
      then obtain sv1' trv1' where trv1: "trv1 = sv1 # trv1'" "validTransV (sv1,sv1')" 
      "Van.validFromS sv1' trv1'" "completedFromV sv1' trv1'" 
      using `Van.validFromS sv1 trv1` `completedFromV sv1 trv1`  
      by (smt (z3) One_nat_def Simple_Transition_System.validFromS_Cons_iff Van.completed_Cons 
       completedFromV_def le_SucI length_Suc_conv list.exhaust list.inject list.size(3) not_less_eq_eq)  

      define secl1' where "secl1' \<equiv> if isSecV sv1 then tl secl1 else secl1"
      have v1: "validEtransO (sv1,secl1) (sv1',secl1')"
      using trv1 unfolding validEtransO.simps secl1'_def 
      using "1.prems" Van.final_def by auto
      have sl1':  "secl1' = Van.S trv1'" 
      using 1(2-) trv1 unfolding secl1'_def by auto
      have r1': "reachV sv1'" 
      by (metis "1.prems"(2) Van.reach.Step fst_conv snd_conv trv1(2))

      have gam: "\<Gamma> sv1' secl1' sv2 secl2"
      using `\<Gamma> sv1 secl1 sv2 secl2` v1 unw r1' isv12 unfolding unwindSDCond_def move1_def  
      using 1(2-) by blast

      have A12: "Van.A trv1' = Van.A trv2" 
      using "1.prems"(10) isv12(1) trv1(1) by auto 
 
      have O12': "Van.O trv1' = Van.O trv2"
      apply(rule 1(1)[rule_format, OF _ _ gam])
      using trv1 gam r1' A12 1(2-) sl1' by auto

      thus ?thesis unfolding trv1(1)  using isv12 by auto
    qed
  qed
qed


(*  *)

(* This version invariant (\<Gamma>) preservation property will support 
the infinitary version: *)

proposition unwindSDCond_aux_strong:
assumes unw: "unwindSDCond \<Gamma>"
and 1: "\<Gamma> sv1 secl1 sv2 secl2" 
"reachV sv1" "Van.validFromS sv1 (trv1 @ [trn1])" "never isIntV trv1" and 11: "isIntV trn1" and 
2: "reachV sv2" "Van.validFromS sv2 (trv2 @ [trn2])" "never isIntV trv2" and 22: "isIntV trn2" and 
3: "Van.S trv1 @ ssecl1 = secl1" "Van.S trv2 @ ssecl2 = secl2" 
shows "\<Gamma> (lastt sv1 trv1) ssecl1 (lastt sv2 trv2) ssecl2"  
using 1 2 3 proof(induct "length trv1 + length trv2" arbitrary: sv1 sv2 trv1 trv2 secl1 secl2 rule: nat_less_induct)
  case (1 trv1 trv2 sv1 sv2 secl1 secl2)
  show ?case 
  proof(cases "isIntV sv1")
    case True hence sv2: "isIntV sv2" using 1(2-) unw unfolding unwindSDCond_def by auto
    note isv12 = True this

    have trv1: "trv1 = []" using True 1(4,5) unfolding list_all_nth apply(cases trv1, auto) 
      by (metis Van.validFromS_Cons_iff nth_Cons_0 zero_less_Suc)
    have trv2: "trv2 = []" using sv2 1(7,8) unfolding list_all_nth apply(cases trv2, auto) 
      by (metis Van.validFromS_Cons_iff nth_Cons_0 zero_less_Suc)

    show ?thesis using 1(2-) by (simp add: trv1 trv2)  
  next
    case False hence "\<not> isIntV sv2" using 1(2-) unw unfolding unwindSDCond_def by auto
    note isv12 = False this
    have trv1ne: "trv1 \<noteq> []" using isv12 "1.prems"(3) "11" by force
    then obtain sv1' trv1' where trv1: "trv1 = sv1 # trv1'" "validTransV (sv1,sv1')" 
    "Van.validFromS sv1' trv1'" "never isIntV trv1'" 
    using `Van.validFromS sv1 (trv1 @ [trn1])` `never isIntV trv1` 
    by (metis Simple_Transition_System.validFromS_Cons_iff Simple_Transition_System.validFromS_def 
       Simple_Transition_System.validS_append1 
      Simple_Transition_System.validS_validTrans hd_append2 list_all_simps(1) neq_Nil_conv snoc_eq_iff_butlast)
    have trv2ne: "trv2 \<noteq> []" using isv12 "1.prems"(6) "22" by force
    then obtain sv2' trv2' where trv2: "trv2 = sv2 # trv2'" "validTransV (sv2,sv2')" 
    "Van.validFromS sv2' trv2'" "never isIntV trv2'" 
    using `Van.validFromS sv2 (trv2 @ [trn2])` `never isIntV trv2` 
    by (metis Simple_Transition_System.validFromS_Cons_iff Simple_Transition_System.validFromS_def 
       Simple_Transition_System.validS_append1 
      Simple_Transition_System.validS_validTrans hd_append2 list_all_simps(1) neq_Nil_conv snoc_eq_iff_butlast)

    show ?thesis 
    proof(cases "length trv1 = Suc 0 \<and> length trv2 = Suc 0") 
      case True
      hence trv12: "trv1 = [sv1] \<and> trv2 = [sv2]" apply(intro conjI) 
        subgoal using 1(4) Van.validFromS_Cons_iff by (cases trv1, auto)
        subgoal using 1(7) Van.validFromS_Cons_iff by (cases trv2, auto) .
      show ?thesis using 1(2) "1.prems"(8,9) trv12 unfolding lastt_def by auto
    next
      case False note f = False
      show ?thesis 
      proof(cases "length trv1 = Suc 0")
        case True
        hence "length trv2 > Suc 0" using f trv2ne by (simp add: Suc_lessI)
        hence trv2'ne: "trv2' \<noteq> []" by (simp add: trv2(1))

        define secl2' where "secl2' \<equiv> if isSecV sv2 then tl secl2 else secl2"
        have v2: "validEtransO (sv2,secl2) (sv2',secl2')"
        using trv2 unfolding validEtransO.simps secl2'_def  
        using "1.prems"(9) trv2'ne by auto 
        have sl2':  "secl2' = Van.S trv2' @ ssecl2"  
        using "1.prems"(9) trv2(1) v2 by (auto simp: trv2'ne)
        have r2': "reachV sv2'" 
        by (metis "1.prems"(5) Van.reach.Step fst_conv snd_conv trv2(2))

        have gam: "\<Gamma> sv1 secl1 sv2' secl2'"
        using `\<Gamma> sv1 secl1 sv2 secl2` v2 unw r2' isv12 unfolding unwindSDCond_def move2_def  
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

        define secl1' where "secl1' \<equiv> if isSecV sv1 then tl secl1 else secl1"
        have v1: "validEtransO (sv1,secl1) (sv1',secl1')"
        using trv1 unfolding validEtransO.simps secl1'_def  
        using "1.prems"(8) trv1'ne by auto
        have sl1':  "secl1' = Van.S trv1' @ ssecl1"  
        using "1.prems"(8) trv1(1) v1 by (auto simp: trv1'ne)
        have r1': "reachV sv1'" 
        by (metis "1.prems"(2) Van.reach.Step fst_conv snd_conv trv1(2))

        have gam: "\<Gamma> sv1' secl1' sv2 secl2"
        using `\<Gamma> sv1 secl1 sv2 secl2` v1 unw r1' isv12 unfolding unwindSDCond_def move1_def  
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

lemma S_eq_empty_ConsE:
  assumes \<open>Van.S (x # xs) = Opt.S (y # ys)\<close> and \<open>xs \<noteq> []\<close> and \<open>ys \<noteq> []\<close>
    shows \<open>(isSecO y \<and> isSecV x \<longrightarrow> getSecV x = getSecO y \<and> Van.S xs = Opt.S ys)
         \<and> (isSecO y \<and> \<not>isSecV x \<longrightarrow> Van.S xs = (getSecO y # Opt.S ys))
         \<and> (\<not>isSecO y \<and> isSecV x \<longrightarrow> (getSecV x # Van.S xs) = Opt.S ys)
         \<and> (\<not>isSecO y \<and> \<not>isSecV x \<longrightarrow> Van.S xs = Opt.S ys)\<close>
  using assms unfolding Van.S.Cons_unfold Opt.S.Cons_unfold
  by (simp split: if_splits)

theorem unwindSD_rsecure:
  assumes tr14: "istateO s1" "Opt.validFromS s1 tr1" "completedFromO s1 tr1"
            "istateO s4" "Opt.validFromS s4 tr2" "completedFromO s4 tr2"
            "Opt.A tr1 = Opt.A tr2" "Opt.O tr1 \<noteq> Opt.O tr2"
      and init: "\<And>sv1 sv2. \<lbrakk>istateV sv1; corrState sv1 s1; istateV sv2; corrState sv2 s4\<rbrakk> \<Longrightarrow>
                    \<Gamma> sv1 (Opt.S tr1) sv2 (Opt.S tr2)"
      and unw: "unwindSDCond \<Gamma>"
    shows "\<not> rsecure"
  unfolding rsecure_def2 unfolding not_all not_imp
  apply(rule exI[of _ s1]) apply(rule exI[of _ tr1])
  apply(rule exI[of _ s4]) apply(rule exI[of _ tr2])
  apply(rule conjI)
  subgoal using tr14 by (intro conjI)
  subgoal by (metis Van.Istate init unw unwindSDCond_aux) .
   
end (* context Relative Security *)


end 