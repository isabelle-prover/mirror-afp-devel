subsection "Proof"
theory Fun3_secure
imports Fun3
begin 

type_synonym stateO = configS
type_synonym stateV = "config \<times> val llist \<times> val llist \<times> loc set"
(* THE PROOF OF SECURITY *)
definition "PC \<equiv> {0..7}"

(* we read "before" as "before or at" *)
definition "beforeInput = {0,1}"
definition "afterInput = {2,3,4,5,6,7}"
definition "startOfThenBranch = 4"
definition "inThenBranchBeforeFence = {4,5}"
definition "elseBranch = 7"
definition "beforeFence = {2..4}" 
definition "beforeAssign_vv = {0..4}"

(* Common to all the unwinding relations in this proof: *)
definition common :: "stateO \<Rightarrow> stateO  \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" 
where 
"common = (\<lambda>
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
   statO. 
(pstate3 = pstate4 \<and> 
 cfg1 = cfg3 \<and> cfg2 = cfg4 \<and> 
 pcOf cfg3 = pcOf cfg4 \<and> map pcOf cfgs3 = map pcOf cfgs4 \<and> 
 pcOf cfg3 \<in> PC \<and> pcOf ` (set cfgs3) \<subseteq> PC \<and>
 \<^cancel>\<open>   \<close>
 array_base aa1 (getAvstore (stateOf cfg3)) = array_base aa1 (getAvstore (stateOf cfg4)) \<and> 
 (\<forall>cfg3'\<in>set cfgs3. array_base aa1 (getAvstore (stateOf cfg3')) = array_base aa1 (getAvstore (stateOf cfg3))) \<and> 
 (\<forall>cfg4'\<in>set cfgs4. array_base aa1 (getAvstore (stateOf cfg4')) = array_base aa1 (getAvstore (stateOf cfg4))) \<and> 
 array_base aa2 (getAvstore (stateOf cfg3)) = array_base aa2 (getAvstore (stateOf cfg4)) \<and> 
 (\<forall>cfg3'\<in>set cfgs3. array_base aa2 (getAvstore (stateOf cfg3')) = array_base aa2 (getAvstore (stateOf cfg3))) \<and> 
 (\<forall>cfg4'\<in>set cfgs4. array_base aa2 (getAvstore (stateOf cfg4')) = array_base aa2 (getAvstore (stateOf cfg4))) \<and> 
 \<^cancel>\<open>   \<close>
 (statA = Diff \<longrightarrow> statO = Diff)))"


lemma common_implies: "common    
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
   statO \<Longrightarrow> 
 pcOf cfg1 < 9 \<and> pcOf cfg2 = pcOf cfg1"
unfolding common_def PC_def by (auto simp: image_def subset_eq)


(* Before input is inserted *)
definition \<Delta>0 :: "enat \<Rightarrow> stateO \<Rightarrow> stateO  \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" where 
"\<Delta>0 = (\<lambda>num 
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
     statO.
 (common    (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
     statO  \<and> 
  ibUT1 = ibUT3 \<and> ibUT2 = ibUT4 \<and>   
  (pcOf cfg3 > 1 \<longrightarrow> same_var_o xx cfg3 cfgs3 cfg4 cfgs4) \<and> 
  (pcOf cfg3 < 2 \<longrightarrow> ibUT1\<noteq>LNil \<and> ibUT2\<noteq>LNil \<and> ibUT3\<noteq>LNil \<and> ibUT4\<noteq>LNil) \<and>
  pcOf cfg3 \<in> beforeInput \<and> 
  ls1 = ls3 \<and> ls2 = ls4 \<and> 
  noMisSpec cfgs3 
 ))"

lemmas \<Delta>0_defs = \<Delta>0_def common_def PC_def beforeInput_def noMisSpec_def same_var_o_def

lemma \<Delta>0_implies: "\<Delta>0 num 
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
   statO \<Longrightarrow> 
   (pcOf cfg3 = 1 \<longrightarrow> ibUT3 \<noteq> LNil) \<and>
   (pcOf cfg4 = 1 \<longrightarrow> ibUT4 \<noteq> LNil) \<and>
   pcOf cfg1 < 8 \<and> pcOf cfg2 = pcOf cfg1 \<and> 
   cfgs3 = [] \<and> pcOf cfg3 < 8 \<and>
   cfgs4 = [] \<and> pcOf cfg4 < 8"
  unfolding \<Delta>0_defs 
  apply(intro conjI)
  apply simp_all 
  by (metis map_is_Nil_conv)

(* After input is inserted, no mis-speculation *)
definition \<Delta>1 :: "enat \<Rightarrow> stateO \<Rightarrow> stateO \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" where 
"\<Delta>1 = (\<lambda>num 
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
     statO.
 (common    
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
     statO \<and> 
  pcOf cfg3 \<in> afterInput \<and> 
  same_var_o xx cfg3 cfgs3 cfg4 cfgs4 \<and>
  ls1 = ls3 \<and> ls2 = ls4 \<and> 
  noMisSpec cfgs3 
 ))"

lemmas \<Delta>1_defs = \<Delta>1_def common_def PC_def afterInput_def same_var_o_def noMisSpec_def

lemma \<Delta>1_implies: "\<Delta>1 num
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2)
   statO \<Longrightarrow> 
   pcOf cfg1 < 8 \<and>
   cfgs3 = [] \<and> pcOf cfg3 \<noteq> 1 \<and> pcOf cfg3 < 8 \<and>
   cfgs4 = [] \<and> pcOf cfg4 \<noteq> 1 \<and> pcOf cfg4 < 8"
  unfolding \<Delta>1_defs 
  apply(intro conjI) apply simp_all
  using One_nat_def verit_eq_simplify(10,12) apply linarith
  apply (metis list.map_disc_iff)
  by linarith


(* Left mis-speculation: *)
definition \<Delta>2 :: "enat \<Rightarrow> stateO \<Rightarrow> stateO  \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" where 
"\<Delta>2 = (\<lambda>num
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2)  
     statO.
 (common    
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2)  
     statO \<and> 
  pcOf cfg3 = startOfThenBranch \<and> 
  pcOf (last cfgs3) = elseBranch \<and> 
  same_var_o xx cfg3 cfgs3 cfg4 cfgs4 \<and>
  ls1 = ls3 \<and> ls2 = ls4 \<and>
  misSpecL1 cfgs3
 ))"

lemmas \<Delta>2_defs = \<Delta>2_def common_def PC_def same_var_def startOfThenBranch_def  
      misSpecL1_def elseBranch_def

lemma \<Delta>2_implies: "\<Delta>2 num    
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
   statO \<Longrightarrow> 
   pcOf (last cfgs3) = 7 \<and> pcOf cfg3 = 4 \<and> 
   pcOf (last cfgs4) = pcOf (last cfgs3) \<and>
   pcOf cfg3 = pcOf cfg4 \<and>
   length cfgs3 = Suc 0 \<and>
   length cfgs3 = length cfgs4"
  apply(intro conjI)
  unfolding \<Delta>2_defs apply simp_all
  apply (simp add: image_subset_iff) 
  apply (metis last_map map_is_Nil_conv)
  by (metis length_map)

(* Right mis-speculation: *)
definition \<Delta>3 :: "enat \<Rightarrow> stateO \<Rightarrow> stateO  \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" where 
"\<Delta>3 = (\<lambda>num 
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
     statO.
 (common (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2)  
     statO \<and> 
  pcOf cfg3 = elseBranch \<and> 
  pcOf (last cfgs3) \<in> inThenBranchBeforeFence \<and>
  same_var_o xx cfg3 cfgs3 cfg4 cfgs4 \<and> 
  Language_Prelims.dist ls3 ls4 \<subseteq> Language_Prelims.dist ls1 ls2 \<and>
  (pcOf (last cfgs3) = 4 \<longrightarrow> ls1 = ls3 \<and> ls2 = ls4) \<and> 
  misSpecL1 cfgs3 
 ))"

lemmas \<Delta>3_defs = \<Delta>3_def common_def PC_def inThenBranchBeforeFence_def
           beforeAssign_vv_def misSpecL1_def elseBranch_def 
           same_var_o_def

lemma \<Delta>3_implies: "\<Delta>3 num
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
   statO \<Longrightarrow> 
   (pcOf (last cfgs3) = 4 \<or> pcOf (last cfgs3) = 5) \<and> pcOf cfg3 = 7 \<and> 
   pcOf (last cfgs4) = pcOf (last cfgs3) \<and>
   pcOf cfg3 = pcOf cfg4 \<and>
   array_base aa1 (getAvstore (stateOf (last cfgs3))) = array_base aa1 (getAvstore (stateOf cfg3)) \<and> 
   array_base aa1 (getAvstore (stateOf (last cfgs4))) = array_base aa1 (getAvstore (stateOf cfg4)) \<and>
   length cfgs3 = Suc 0 \<and>
   length cfgs3 = length cfgs4 \<and>
   vstore (getVstore (stateOf (last cfgs3))) xx = vstore (getVstore (stateOf (last cfgs4))) xx"
apply(intro conjI)
  unfolding \<Delta>3_defs apply simp_all
  apply (simp add: image_subset_iff) 
  apply (metis last_map map_is_Nil_conv)
  apply (metis last_in_set list.size(3) n_not_Suc_n)
  apply (metis One_nat_def last_in_set length_0_conv length_map zero_neq_one)
  apply (metis length_map)
  by (metis last_in_set list.map_disc_iff)


(* *)

definition \<Delta>1' :: "enat \<Rightarrow> stateO \<Rightarrow> stateO \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" where 
"\<Delta>1' = (\<lambda>num 
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
     statO.
 (common    
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
     statO \<and> 
  pcOf cfg3 = elseBranch \<and> 
  same_var_o xx cfg3 cfgs3 cfg4 cfgs4 \<and>
  Language_Prelims.dist ls3 ls4 \<subseteq> Language_Prelims.dist ls1 ls2 \<and>
  noMisSpec cfgs3 
 ))"

lemmas \<Delta>1'_defs = \<Delta>1'_def common_def PC_def afterInput_def same_var_o_def noMisSpec_def
elseBranch_def

lemma \<Delta>1'_implies: "\<Delta>1' num
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2)
   statO \<Longrightarrow> 
   pcOf cfg1 < 8 \<and>
   cfgs3 = [] \<and> pcOf cfg3 \<noteq> 1 \<and> pcOf cfg3 < 8 \<and>
   cfgs4 = [] \<and> pcOf cfg4 \<noteq> 1 \<and> pcOf cfg4 < 8"
  unfolding \<Delta>1'_defs 
  apply(intro conjI) apply simp_all 
  by (metis list.map_disc_iff)


(* End: *)
definition \<Delta>4 :: "enat \<Rightarrow> stateO \<Rightarrow> stateO  \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" where 
"\<Delta>4 = (\<lambda>num 
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2)  
    statO.
   (pcOf cfg3 = endPC \<and> pcOf cfg4 = endPC \<and> cfgs3 = [] \<and> cfgs4 = [] \<and>
    pcOf cfg1 = endPC \<and> pcOf cfg2 = endPC))"

lemmas \<Delta>4_defs = \<Delta>4_def common_def endPC_def  

(* *)

lemma init: "initCond \<Delta>0" 
  unfolding initCond_def apply(intro allI) 
  subgoal for s3 s4 apply(cases s3, cases s4) 
  subgoal for pstate3 cfg3 cfgs3 ibT3 ibUT3 ls3 pstate4 cfg4 cfgs4 ibT4 ibUT4 ls4 
    apply clarify 
    apply(rule exI[of _ "(cfg3, ibT3, ibUT3, ls3)"])
    apply(cases "getAvstore (stateOf cfg3)")
    apply(rule exI[of _ "(cfg4, ibT4, ibUT4, ls4)"])
    apply(cases "getAvstore (stateOf cfg4)")
  unfolding \<Delta>0_defs array_base_def by auto  . .

(* *)
 lemma step0: "unwindIntoCond \<Delta>0 (oor \<Delta>0 \<Delta>1)"
proof(rule unwindIntoCond_simpleI)  
  fix n ss3 ss4 statA ss1 ss2 statO
  assume r: "reachO ss3" "reachO ss4" "reachV ss1" "reachV ss2"
  and \<Delta>0: "\<Delta>0 n ss3 ss4 statA ss1 ss2 statO"

  obtain pstate3 cfg3 cfgs3 ibT3 ibUT3 ls3 where ss3: "ss3 = (pstate3, cfg3, cfgs3, ibT3, ibUT3, ls3)"
  by (cases ss3, auto) 
  obtain pstate4 cfg4 cfgs4 ibT4 ibUT4 ls4 where ss4: "ss4 = (pstate4, cfg4, cfgs4, ibT4, ibUT4, ls4)"
  by (cases ss4, auto)
  obtain cfg1 ibT1 ibUT1 ls1 where ss1: "ss1 = (cfg1, ibT1, ibUT1, ls1)"
  by (cases ss1, auto) 
  obtain cfg2 ibT2 ibUT2 ls2 where ss2: "ss2 = (cfg2, ibT2, ibUT2, ls2)"
  by (cases ss2, auto) 
  note ss = ss3 ss4 ss1 ss2 


  obtain pc3 vs3 avst3 h3 p3 where 
  cfg3: "cfg3 = Config pc3 (State (Vstore vs3) avst3 h3 p3)"
  by (cases cfg3) (metis state.collapse vstore.collapse)
  obtain pc4 vs4 avst4 h4 p4 where 
  cfg4: "cfg4 = Config pc4 (State (Vstore vs4) avst4 h4 p4)"
  by (cases cfg4) (metis state.collapse vstore.collapse)
  note cfg = cfg3 cfg4

  obtain hh3 where h3: "h3 = Heap hh3" by(cases h3, auto)
  obtain hh4 where h4: "h4 = Heap hh4" by(cases h4, auto)
  note hh = h3 h4

  have f1:"\<not>finalN ss1" 
    using \<Delta>0 finalB_pc_iff' unfolding ss finalN_iff_finalB \<Delta>0_defs
    by simp 

  have f2:"\<not>finalN ss2" 
    using \<Delta>0 finalB_pc_iff' unfolding ss finalN_iff_finalB \<Delta>0_defs
    by simp 

  have f3:"\<not>finalS ss3" 
    using \<Delta>0 unfolding ss apply-apply(frule \<Delta>0_implies)
    using finalS_cond by simp

  have f4:"\<not>finalS ss4" 
    using \<Delta>0 unfolding ss apply-apply(frule \<Delta>0_implies)
    using finalS_cond by simp


  note finals = f1 f2 f3 f4
  show "finalS ss3 = finalS ss4 \<and> finalN ss1 = finalS ss3 \<and> finalN ss2 = finalS ss4"
    using finals by auto

  then show "isIntO ss3 = isIntO ss4" by simp


  show "react (oor \<Delta>0 \<Delta>1) ss3 ss4 statA ss1 ss2 statO"
  unfolding react_def proof(intro conjI)
    (* match1 and match2 are imposibT, ibUTle case since isIntO always holds *)
    show "match1 (oor \<Delta>0 \<Delta>1) ss3 ss4 statA ss1 ss2 statO"
    unfolding match1_def by (simp add: finalS_defs)
    show "match2 (oor \<Delta>0 \<Delta>1) ss3 ss4 statA ss1 ss2 statO"
    unfolding match2_def by (simp add: finalS_defs)
    show "match12 (oor \<Delta>0 \<Delta>1) ss3 ss4 statA ss1 ss2 statO"
    (* Choose the match12_12 case (since we have no mis-speculation yet) *)
    proof(rule match12_simpleI, rule disjI2, intro conjI)
      fix ss3' ss4' statA'
      assume statA': "statA' = sstatA' statA ss3 ss4"
      and v: "validTransO (ss3, ss3')" "validTransO (ss4, ss4')" 
      and sa: "Opt.eqAct ss3 ss4"
      note v3 = v(1) note v4 = v(2)
 
      obtain pstate3' cfg3' cfgs3' ibT3' ibUT3' ls3' where ss3': "ss3' = (pstate3', cfg3', cfgs3', ibT3', ibUT3', ls3')"
      by (cases ss3', auto) 
      obtain pstate4' cfg4' cfgs4' ibT4' ibUT4' ls4' where ss4': "ss4' = (pstate4', cfg4', cfgs4', ibT4', ibUT4', ls4')"
      by (cases ss4', auto)
      note ss = ss ss3' ss4'

      obtain pc3 vs3 avst3 h3 p3 where 
      cfg3: "cfg3 = Config pc3 (State (Vstore vs3) avst3 h3 p3)"
      by (cases cfg3) (metis state.collapse vstore.collapse)
      obtain pc4 vs4 avst4 h4 p4 where 
      cfg4: "cfg4 = Config pc4 (State (Vstore vs4) avst4 h4 p4)"
      by (cases cfg4) (metis state.collapse vstore.collapse)
      note cfg = cfg3 cfg4
 
      show "eqSec ss1 ss3"
      using v sa \<Delta>0 unfolding ss 
      by (simp add: \<Delta>0_defs eqSec_def)

      show "eqSec ss2 ss4"
      using v sa \<Delta>0 unfolding ss 
      apply (simp add: \<Delta>0_defs eqSec_def) 
      by (metis length_0_conv length_map) 

      show "Van.eqAct ss1 ss2"
      using v sa \<Delta>0 unfolding ss   
      unfolding Opt.eqAct_def Van.eqAct_def
      apply(simp_all add: \<Delta>0_defs)  
      by (metis f3 map_is_Nil_conv ss3)

      show "match12_12 (oor \<Delta>0 \<Delta>1) ss3' ss4' statA' ss1 ss2 statO"
      unfolding match12_12_def
      proof(rule exI[of _ "nextN ss1"], rule exI[of _ "nextN ss2"],unfold Let_def, intro conjI impI)
        show "validTransV (ss1, nextN ss1)" 
          by (simp add: f1 nextN_stepN)

        show "validTransV (ss2, nextN ss2)" 
          by (simp add: f2 nextN_stepN)

        {assume sstat: "statA' = Diff"
         show "sstatO' statO ss1 ss2 = Diff"
         using v sa \<Delta>0 sstat unfolding ss cfg statA' apply simp
         apply(simp add: \<Delta>0_defs sstatO'_def sstatA'_def finalS_def final_def) 
         using cases_7[of pc3] apply(elim disjE)
         apply simp_all apply(cases statO, simp_all) apply(cases statA, simp_all)
         apply(cases statO, simp_all) apply (cases statA, simp_all)
         by (smt (z3) status.distinct status.exhaust newStat.simps)+
        } note stat = this

        show "oor \<Delta>0 \<Delta>1 \<infinity> ss3' ss4' statA' (nextN ss1) (nextN ss2) (sstatO' statO ss1 ss2)"
        (* the cmbination of nonspec_normal and nonspec_normal is the only nontrivial possibT, ibUTility, deferred to the end *)
          using v3[unfolded ss, simplified] proof(cases rule: stepS_cases)
            case spec_normal
            then show ?thesis using sa \<Delta>0 stat unfolding ss by (simp add: \<Delta>0_defs)
          next
            case spec_mispred
            then show ?thesis using sa \<Delta>0 stat unfolding ss by (simp add: \<Delta>0_defs)
          next
            case spec_Fence
            then show ?thesis using sa \<Delta>0 stat unfolding ss by (simp add: \<Delta>0_defs)
          next
            case spec_resolve
            then show ?thesis using sa \<Delta>0 stat unfolding ss by (simp add: \<Delta>0_defs)
          next
            case nonspec_mispred 
            then show ?thesis using sa \<Delta>0 stat unfolding ss apply (simp add: \<Delta>0_defs) 
              by (metis is_If_pc less_Suc_eq nat_less_le numeral_1_eq_Suc_0 numeral_3_eq_3 
                  one_eq_numeral_iff semiring_norm(83) zero_less_numeral zero_neq_numeral)  
        next
          case nonspec_normal note nn3 = nonspec_normal
          show ?thesis 
          using v3[unfolded ss, simplified] proof(cases rule: stepS_cases)
            case nonspec_mispred
            then show ?thesis using sa \<Delta>0 stat nn3 unfolding ss by (simp add: \<Delta>0_defs)
          next
            case spec_normal
            then show ?thesis using sa \<Delta>0 stat nn3 unfolding ss by (simp add: \<Delta>0_defs)
          next
            case spec_mispred
            then show ?thesis using sa \<Delta>0 stat nn3 unfolding ss by (simp add: \<Delta>0_defs)
          next
            case spec_Fence
            then show ?thesis using sa \<Delta>0 stat nn3 unfolding ss by (simp add: \<Delta>0_defs)
          next
            case spec_resolve
            then show ?thesis using sa \<Delta>0 stat nn3 unfolding ss by (simp add: \<Delta>0_defs)
          next
            case nonspec_normal note nn4=nonspec_normal
            show ?thesis  using sa stat \<Delta>0 v3 v4 nn3 nn4 f4 unfolding ss cfg hh Opt.eqAct_def
            apply clarsimp
            using cases_7[of pc3] apply(elim disjE)
            subgoal apply(rule oorI1) by (simp add: \<Delta>0_defs)
            subgoal apply(rule oorI2) apply (simp add: \<Delta>0_defs,auto) 
              unfolding \<Delta>1_defs 
              subgoal by (simp add: \<Delta>0_defs) 
              subgoal by (simp add: \<Delta>0_defs) .  
            by (simp add: \<Delta>0_defs)+ 
          qed
        qed
      qed
    qed  
  qed
qed
(**)
lemma step1: "unwindIntoCond \<Delta>1 (oor4 \<Delta>1 \<Delta>2 \<Delta>3 \<Delta>4)" 
proof(rule unwindIntoCond_simpleI) 
  fix n ss3 ss4 statA ss1 ss2 statO
  assume r: "reachO ss3" "reachO ss4" "reachV ss1" "reachV ss2"
  and \<Delta>1: "\<Delta>1 n ss3 ss4 statA ss1 ss2 statO"

  obtain pstate3 cfg3 cfgs3 ibT3 ibUT3 ls3 where ss3: "ss3 = (pstate3, cfg3, cfgs3, ibT3, ibUT3, ls3)"
  by (cases ss3, auto) 
  obtain pstate4 cfg4 cfgs4 ibT4 ibUT4 ls4 where ss4: "ss4 = (pstate4, cfg4, cfgs4, ibT4, ibUT4, ls4)"
  by (cases ss4, auto)
  obtain cfg1 ibT1 ibUT1 ls1 where ss1: "ss1 = (cfg1, ibT1, ibUT1, ls1)"
  by (cases ss1, auto) 
  obtain cfg2 ibT2 ibUT2 ls2 where ss2: "ss2 = (cfg2, ibT2, ibUT2, ls2)"
  by (cases ss2, auto) 
  note ss = ss3 ss4 ss1 ss2 


  obtain pc1 vs1 avst1 h1 p1 where 
  cfg1: "cfg1 = Config pc1 (State (Vstore vs1) avst1 h1 p1)"
  by (cases cfg1) (metis state.collapse vstore.collapse)
  obtain pc2 vs2 avst2 h2 p2 where 
  cfg2: "cfg2 = Config pc2 (State (Vstore vs2) avst2 h2 p2)"
  by (cases cfg2) (metis state.collapse vstore.collapse) 
  obtain pc3 vs3 avst3 h3 p3 where 
  cfg3: "cfg3 = Config pc3 (State (Vstore vs3) avst3 h3 p3)"
  by (cases cfg3) (metis state.collapse vstore.collapse)
  obtain pc4 vs4 avst4 h4 p4 where 
  cfg4: "cfg4 = Config pc4 (State (Vstore vs4) avst4 h4 p4)"
  by (cases cfg4) (metis state.collapse vstore.collapse)
  note cfg = cfg1 cfg2 cfg3 cfg4

  obtain hh3 where h3: "h3 = Heap hh3" by(cases h3, auto)
  obtain hh4 where h4: "h4 = Heap hh4" by(cases h4, auto)
  note hh = h3 h4

  have f1:"\<not>finalN ss1" 
    using \<Delta>1 finalB_pc_iff' unfolding ss cfg finalN_iff_finalB \<Delta>1_defs
    by simp linarith

  have f2:"\<not>finalN ss2" 
    using \<Delta>1 finalB_pc_iff' unfolding ss cfg finalN_iff_finalB \<Delta>1_defs
    by simp linarith


  have f3:"\<not>finalS ss3" 
    using \<Delta>1 unfolding ss apply-apply(frule \<Delta>1_implies)
    using finalS_cond by simp

  have f4:"\<not>finalS ss4" 
    using \<Delta>1 unfolding ss apply-apply(frule \<Delta>1_implies)
    using finalS_cond by simp

  note finals = f1 f2 f3 f4

  show "finalS ss3 = finalS ss4 \<and> finalN ss1 = finalS ss3 \<and> finalN ss2 = finalS ss4"
    using finals by auto

  then show "isIntO ss3 = isIntO ss4" by simp

  show "react (oor4 \<Delta>1 \<Delta>2 \<Delta>3 \<Delta>4) ss3 ss4 statA ss1 ss2 statO"
  unfolding react_def proof(intro conjI)
    (* match1 and match2 are imposibT, ibUTle case since isIntO always holds *)
    show "match1 (oor4 \<Delta>1 \<Delta>2 \<Delta>3 \<Delta>4) ss3 ss4 statA ss1 ss2 statO"
    unfolding match1_def by (simp add: finalS_def final_def)
    show "match2 (oor4 \<Delta>1 \<Delta>2 \<Delta>3 \<Delta>4) ss3 ss4 statA ss1 ss2 statO"
    unfolding match2_def by (simp add: finalS_def final_def)
    show "match12 (oor4 \<Delta>1 \<Delta>2 \<Delta>3 \<Delta>4) ss3 ss4 statA ss1 ss2 statO"
    (* Choose the match12_12 case (since we have no mis-speculation yet) *)
    proof(rule match12_simpleI, rule disjI2, intro conjI)
      fix ss3' ss4' statA'
      assume statA': "statA' = sstatA' statA ss3 ss4"
      and v: "validTransO (ss3, ss3')" "validTransO (ss4, ss4')" 
      and sa: "Opt.eqAct ss3 ss4"
      note v3 = v(1) note v4 = v(2)

      obtain pstate3' cfg3' cfgs3' ibT3' ibUT3' ls3' where ss3': "ss3' = (pstate3', cfg3', cfgs3', ibT3', ibUT3', ls3')"
      by (cases ss3', auto) 
      obtain pstate4' cfg4' cfgs4' ibT4' ibUT4' ls4' where ss4': "ss4' = (pstate4', cfg4', cfgs4', ibT4', ibUT4', ls4')"
      by (cases ss4', auto)
      note ss = ss ss3' ss4'

      show "eqSec ss1 ss3"
      using v sa \<Delta>1 unfolding ss
      by (simp add: \<Delta>1_defs eqSec_def)

      show "eqSec ss2 ss4"
      using v sa \<Delta>1 unfolding ss 
      apply (simp add: \<Delta>1_defs eqSec_def) 
      by (metis length_0_conv length_map)
      
      show "Van.eqAct ss1 ss2"
      using v sa \<Delta>1 unfolding ss Van.eqAct_def
      apply (simp_all add: \<Delta>1_defs)  
      by linarith

      show "match12_12 (oor4 \<Delta>1 \<Delta>2 \<Delta>3 \<Delta>4) ss3' ss4' statA' ss1 ss2 statO"
      unfolding match12_12_def
      proof(rule exI[of _ "nextN ss1"], rule exI[of _ "nextN ss2"], unfold Let_def, intro conjI impI)
        show "validTransV (ss1, nextN ss1)" 
          by (simp add: f1 nextN_stepN)

        show "validTransV (ss2, nextN ss2)" 
          by (simp add: f2 nextN_stepN)


        {assume sstat: "statA' = Diff"
         show "sstatO' statO ss1 ss2 = Diff"
         using v sa \<Delta>1 sstat unfolding ss cfg statA'
         apply(simp add: \<Delta>1_defs sstatO'_def sstatA'_def) 
         using cases_7[of pc3] apply(elim disjE)
         defer 1 defer 1 
           subgoal apply(cases statO, simp_all) apply(cases statA, simp_all) 
             using cfg finals ss status.distinct(1) newStat.simps by auto
           subgoal apply(cases statO, simp_all) apply(cases statA, simp_all) 
             using cfg finals ss status.distinct(1) newStat.simps by auto
           subgoal apply(cases statO, simp_all) apply(cases statA, simp_all)
             using cfg finals ss status.distinct(1) newStat.simps by auto
           subgoal apply(cases statO, simp_all) apply(cases statA, simp_all) 
             using cfg finals ss status.distinct(1) newStat.simps by auto
           subgoal apply(cases statO, simp_all) apply(cases statA, simp_all) 
             using cfg finals ss status.distinct(1) newStat.simps by auto
           subgoal apply(cases statO, simp_all) apply(cases statA, simp_all) 
             using cfg finals ss status.distinct(1) newStat.simps by auto
           by simp+
        } note stat = this

        show "(oor4 \<Delta>1 \<Delta>2 \<Delta>3 \<Delta>4) \<infinity> ss3' ss4' statA' (nextN ss1) (nextN ss2) (sstatO' statO ss1 ss2)"
        (* nonspec_normal and nonspec_mispred are the only nontrivial possibT, ibUTility, deferred to the end *)
        using v3[unfolded ss, simplified] proof(cases rule: stepS_cases)
          case spec_normal
          then show ?thesis using sa \<Delta>1 stat unfolding ss by (simp add: \<Delta>1_defs)  
        next
          case spec_mispred
          then show ?thesis using sa \<Delta>1 stat unfolding ss by (simp add: \<Delta>1_defs) 
        next
          case spec_Fence
          then show ?thesis using sa \<Delta>1 stat unfolding ss by (simp add: \<Delta>1_defs) 
        next
          case spec_resolve
          then show ?thesis using sa \<Delta>1 stat unfolding ss by (simp add: \<Delta>1_defs) 
        next
          case nonspec_mispred note nm3 = nonspec_mispred
          show ?thesis using v4[unfolded ss, simplified] proof(cases rule: stepS_cases)
            (* trace 4 can only have the same case as trace 3 as nontrivial case, here nonspec_mispred -- deferred *)
              case nonspec_normal
              then show ?thesis using sa \<Delta>1 stat nm3 unfolding ss by (simp add: \<Delta>1_defs) 
            next
              case spec_normal
              then show ?thesis using sa \<Delta>1 stat nm3 unfolding ss by (simp add: \<Delta>1_defs) 
            next
              case spec_mispred
              then show ?thesis using sa \<Delta>1 stat nm3 unfolding ss by (simp add: \<Delta>1_defs) 
            next
              case spec_Fence
              then show ?thesis using sa \<Delta>1 stat nm3 unfolding ss by (simp add: \<Delta>1_defs) 
            next
              case spec_resolve
              then show ?thesis using sa \<Delta>1 stat nm3 unfolding ss by (simp add: \<Delta>1_defs) 
            next
              case nonspec_mispred note nm4 = nonspec_mispred
              then show ?thesis
              using sa \<Delta>1 stat v3 v4 nm3 nm4 unfolding ss cfg hh apply clarsimp
              using cases_7[of pc3] apply(elim disjE)
                subgoal by simp
                subgoal by simp   
                subgoal by simp
                subgoal using xx_NN_cases[of vs3] apply(elim disjE)
                  subgoal apply(rule oor4I2) by (simp add: \<Delta>1_defs \<Delta>2_defs) 
                  subgoal apply(rule oor4I3) by (simp add: \<Delta>1_defs \<Delta>3_defs) .
                by (simp_all add: \<Delta>1_defs)+  
          qed
        next
          case nonspec_normal note nn3 = nonspec_normal
          show ?thesis using v4[unfolded ss, simplified] proof(cases rule: stepS_cases)
          (* trace 4 can only have the same case as trace 3 as nontrivial case, here nonspec_normal -- deferred *)
            case nonspec_mispred
            then show ?thesis using sa \<Delta>1 stat nn3 unfolding ss by (simp add: \<Delta>1_defs) 
          next
            case spec_normal
            then show ?thesis using sa \<Delta>1 stat nn3 unfolding ss by (simp add: \<Delta>1_defs) 
          next
            case spec_mispred
            then show ?thesis using sa \<Delta>1 stat nn3 unfolding ss by (simp add: \<Delta>1_defs) 
          next
            case spec_Fence
            then show ?thesis using sa \<Delta>1 stat nn3 unfolding ss by (simp add: \<Delta>1_defs) 
          next
            case spec_resolve
            then show ?thesis using sa \<Delta>1 stat nn3 unfolding ss by (simp add: \<Delta>1_defs) 
          next
            case nonspec_normal
            then show ?thesis using sa \<Delta>1 stat v3 v4 nn3 unfolding ss cfg hh apply clarsimp
            using cases_7[of pc3] apply(elim disjE)
              subgoal by (simp add: \<Delta>1_defs)
              subgoal by (simp add: \<Delta>1_defs)
              subgoal apply(rule oor4I1) by(simp add:\<Delta>1_defs) 
              subgoal using xx_NN_cases[of vs3] apply(elim disjE)
                 subgoal apply(rule oor4I1) by (simp add: \<Delta>1_defs)
                 subgoal apply(rule oor4I1) by (simp add: \<Delta>1_defs) .
              subgoal apply(rule oor4I1) by (simp add: \<Delta>1_defs) 
              subgoal apply(rule oor4I1) by (simp add: \<Delta>1_defs) 
              subgoal apply(rule oor4I1) by (simp add: \<Delta>1_defs) 
              subgoal apply(rule oor4I4) by (simp add: \<Delta>1_defs \<Delta>4_defs)
              subgoal apply(rule oor4I4) by (simp add: \<Delta>1_defs \<Delta>4_defs) .
          qed
        qed
      qed
    qed
  qed
qed

(* *)

lemma step2: "unwindIntoCond \<Delta>2 \<Delta>1" 
proof(rule unwindIntoCond_simpleI)
  fix n ss3 ss4 statA ss1 ss2 statO
  assume r: "reachO ss3" "reachO ss4" "reachV ss1" "reachV ss2"
  and \<Delta>2: "\<Delta>2 n ss3 ss4 statA ss1 ss2 statO"

  obtain pstate3 cfg3 cfgs3 ibT3 ibUT3 ls3 where ss3: "ss3 = (pstate3, cfg3, cfgs3, ibT3, ibUT3, ls3)"
  by (cases ss3, auto) 
  obtain pstate4 cfg4 cfgs4 ibT4 ibUT4 ls4 where ss4: "ss4 = (pstate4, cfg4, cfgs4, ibT4, ibUT4, ls4)"
  by (cases ss4, auto)
  obtain cfg1 ibT1 ibUT1 ls1 where ss1: "ss1 = (cfg1, ibT1, ibUT1, ls1)"
  by (cases ss1, auto) 
  obtain cfg2 ibT2 ibUT2 ls2 where ss2: "ss2 = (cfg2, ibT2, ibUT2, ls2)"
  by (cases ss2, auto) 
  note ss = ss3 ss4 ss1 ss2
 
  obtain pc3 vs3 avst3 h3 p3 where 
  lcfgs3: "last cfgs3 = Config pc3 (State (Vstore vs3) avst3 h3 p3)"
  by (cases "last cfgs3") (metis state.collapse vstore.collapse)
  obtain pc4 vs4 avst4 h4 p4 where 
  lcfgs4: "last cfgs4 = Config pc4 (State (Vstore vs4) avst4 h4 p4)"
  by (cases "last cfgs4") (metis state.collapse vstore.collapse)
  note lcfgs = lcfgs3 lcfgs4

  have f1:"\<not>finalN ss1" 
    using \<Delta>2 finalB_pc_iff' unfolding ss finalN_iff_finalB \<Delta>2_defs
    by auto

  have f2:"\<not>finalN ss2" 
    using \<Delta>2 finalB_pc_iff' unfolding ss finalN_iff_finalB \<Delta>2_defs
    by auto

  have f3:"\<not>finalS ss3" 
    using \<Delta>2 unfolding ss apply-apply(frule \<Delta>2_implies)
    using finalS_cond_spec by simp

  have f4:"\<not>finalS ss4" 
    using \<Delta>2 unfolding ss apply-apply(frule \<Delta>2_implies)
    using finalS_cond_spec by simp


  note finals = f1 f2 f3 f4
  show "finalS ss3 = finalS ss4 \<and> finalN ss1 = finalS ss3 \<and> finalN ss2 = finalS ss4"
    using finals by auto

  then show "isIntO ss3 = isIntO ss4" by simp

  show "react \<Delta>1 ss3 ss4 statA ss1 ss2 statO"
  unfolding react_def proof(intro conjI)
    (* match1 and match2 are imposibT,ibUTle case since isIntO always holds *)
    show "match1 \<Delta>1 ss3 ss4 statA ss1 ss2 statO"
    unfolding match1_def by (simp add: finalS_def final_def) 
    show "match2 \<Delta>1 ss3 ss4 statA ss1 ss2 statO"
    unfolding match2_def by (simp add: finalS_def final_def) 
    show "match12 \<Delta>1 ss3 ss4 statA ss1 ss2 statO"
    (* Choose the ignore case (since traces 3 and 4 do speculation) *)
    proof(rule match12_simpleI, rule disjI1, intro conjI)
      fix ss3' ss4' statA'
      assume statA': "statA' = sstatA' statA ss3 ss4"
      and v: "validTransO (ss3, ss3')" "validTransO (ss4, ss4')" 
      and sa: "Opt.eqAct ss3 ss4"
      note v3 = v(1)  note v4 = v(2)

      obtain pstate3' cfg3' cfgs3' ibT3' ibUT3' ls3' where ss3': "ss3' = (pstate3', cfg3', cfgs3', ibT3', ibUT3', ls3')"
      by (cases ss3', auto) 
      obtain pstate4' cfg4' cfgs4' ibT4' ibUT4' ls4' where ss4': "ss4' = (pstate4', cfg4', cfgs4', ibT4', ibUT4', ls4')"
      by (cases ss4', auto)
      note ss = ss ss3' ss4'

      obtain hh3 where h3: "h3 = Heap hh3" by(cases h3, auto)
      obtain hh4 where h4: "h4 = Heap hh4" by(cases h4, auto)
      note hh = h3 h4

      show "\<not> isSecO ss3"
      using v sa \<Delta>2 unfolding ss by (simp add: \<Delta>2_defs) 

      show "\<not> isSecO ss4"
      using v sa \<Delta>2 unfolding ss apply clarsimp 
      by (simp add: \<Delta>2_defs, linarith) 

      show stat: "statA = statA' \<or> statO = Diff"
      using v sa \<Delta>2
      apply (cases ss3, cases ss4, cases ss1, cases ss2)
      apply (cases ss3', cases ss4', clarsimp)
      unfolding ss statA' apply clarsimp        
      apply(simp_all add: \<Delta>2_defs sstatA'_def) 
      apply(cases statO, simp_all) apply(cases statA, simp_all)
      unfolding finalS_defs
      by (smt (verit, ccfv_SIG) newStat.simps(1))

      show "\<Delta>1 \<infinity> ss3' ss4' statA' ss1 ss2 statO"
      (* the only nontrivial combination of cases will be spec_resolve and spec_resolve *)
      using v3[unfolded ss, simplified] proof(cases rule: stepS_cases)
        case nonspec_normal
        then show ?thesis using sa stat \<Delta>2 unfolding ss by (simp add: \<Delta>2_defs)
      next
        case nonspec_mispred
        then show ?thesis using sa stat \<Delta>2 unfolding ss by (simp add: \<Delta>2_defs)
      next
        case spec_normal
        then show ?thesis using sa stat \<Delta>2 v3 unfolding ss apply- 
          apply(frule \<Delta>2_implies) by(simp add: \<Delta>2_defs) 
      next
        case spec_mispred
        then show ?thesis using sa stat \<Delta>2 unfolding ss apply-  
        apply(frule \<Delta>2_implies) by (simp add: \<Delta>2_defs) 
      next
        case spec_Fence 
        then show ?thesis using sa stat \<Delta>2 unfolding ss apply-  
          apply(frule \<Delta>2_implies) by (simp add: \<Delta>2_defs)
      next
        case spec_resolve note sr3 = spec_resolve
        show ?thesis using v4[unfolded ss, simplified] proof(cases rule: stepS_cases)
          case nonspec_normal
          then show ?thesis using sa stat \<Delta>2 sr3 unfolding ss by (simp add: \<Delta>2_defs)
        next
          case nonspec_mispred
          then show ?thesis using sa stat \<Delta>2 sr3 unfolding ss by (simp add: \<Delta>2_defs)
        next
          case spec_normal
          then show ?thesis using sa stat \<Delta>2 sr3 unfolding ss by (simp add: \<Delta>2_defs) 
        next
          case spec_mispred
          then show ?thesis using sa stat \<Delta>2 sr3 unfolding ss by (simp add: \<Delta>2_defs)
        next
          case spec_Fence 
          then show ?thesis using sa stat \<Delta>2 sr3 unfolding ss by (simp add: \<Delta>2_defs)
        next
          case spec_resolve note sr4 = spec_resolve
          show ?thesis using sa stat \<Delta>2 v3 v4 sr3 sr4 
          unfolding ss lcfgs hh apply-
          apply(frule \<Delta>2_implies) apply (simp add: \<Delta>2_defs \<Delta>1_defs) by clarsimp 
        qed 
      qed 
    qed
  qed  
qed 

(* *)

lemma step3: "unwindIntoCond \<Delta>3 (oor \<Delta>3 \<Delta>1')" 
proof(rule unwindIntoCond_simpleI) 
  fix n ss3 ss4 statA ss1 ss2 statO
  assume r: "reachO ss3" "reachO ss4" "reachV ss1" "reachV ss2"
  and \<Delta>3: "\<Delta>3 n ss3 ss4 statA ss1 ss2 statO"

  obtain pstate3 cfg3 cfgs3 ibT3 ibUT3 ls3 where ss3: "ss3 = (pstate3, cfg3, cfgs3, ibT3, ibUT3, ls3)"
  by (cases ss3, auto) 
  obtain pstate4 cfg4 cfgs4 ibT4 ibUT4 ls4 where ss4: "ss4 = (pstate4, cfg4, cfgs4, ibT4, ibUT4, ls4)"
  by (cases ss4, auto)
  obtain cfg1 ibT1 ibUT1 ls1 where ss1: "ss1 = (cfg1, ibT1, ibUT1, ls1)"
  by (cases ss1, auto) 
  obtain cfg2 ibT2 ibUT2 ls2 where ss2: "ss2 = (cfg2, ibT2, ibUT2, ls2)"
  by (cases ss2, auto) 
  note ss = ss3 ss4 ss1 ss2

  obtain pc3 vs3 avst3 h3 p3 where 
  lcfgs3: "last cfgs3 = Config pc3 (State (Vstore vs3) avst3 h3 p3)"
  by (cases "last cfgs3") (metis state.collapse vstore.collapse)
  obtain pc4 vs4 avst4 h4 p4 where 
  lcfgs4: "last cfgs4 = Config pc4 (State (Vstore vs4) avst4 h4 p4)"
  by (cases "last cfgs4") (metis state.collapse vstore.collapse)
  note lcfgs = lcfgs3 lcfgs4

  obtain hh3 where h3: "h3 = Heap hh3" by(cases h3, auto)
  obtain hh4 where h4: "h4 = Heap hh4" by(cases h4, auto)
  note hh = h3 h4

  have f1:"\<not>finalN ss1" 
    using \<Delta>3 finalB_pc_iff' unfolding ss finalN_iff_finalB \<Delta>3_defs
    by auto

  have f2:"\<not>finalN ss2" 
    using \<Delta>3 finalB_pc_iff' unfolding ss finalN_iff_finalB \<Delta>3_defs
    by auto

  have f3:"\<not>finalS ss3" 
    using \<Delta>3 unfolding ss apply-apply(frule \<Delta>3_implies)
    using finalS_cond_spec by simp

  have f4:"\<not>finalS ss4" 
    using \<Delta>3 unfolding ss apply-apply(frule \<Delta>3_implies)
    using finalS_cond_spec by simp

  have "vs3 xx = vs4 xx"
    using \<Delta>3 lcfgs unfolding ss  
    apply-by(frule \<Delta>3_implies, simp)

  note finals = f1 f2 f3 f4
  show "finalS ss3 = finalS ss4 \<and> finalN ss1 = finalS ss3 \<and> finalN ss2 = finalS ss4"
    using finals by auto

  then show "isIntO ss3 = isIntO ss4" by simp

  show "react (oor \<Delta>3 \<Delta>1') ss3 ss4 statA ss1 ss2 statO"
  unfolding react_def proof(intro conjI)
    (* match1 and match2 are imposibT,ibUTle case since isIntO always holds *)
    show "match1 (oor \<Delta>3 \<Delta>1') ss3 ss4 statA ss1 ss2 statO"
    unfolding match1_def by (simp add: finalS_def final_def) 
    show "match2 (oor \<Delta>3 \<Delta>1') ss3 ss4 statA ss1 ss2 statO"
    unfolding match2_def by (simp add: finalS_def final_def) 
    show "match12 (oor \<Delta>3 \<Delta>1') ss3 ss4 statA ss1 ss2 statO"
    proof(rule match12_simpleI, rule disjI1, intro conjI) 
      fix ss3' ss4' statA'
      assume statA': "statA' = sstatA' statA ss3 ss4"
      and v: "validTransO (ss3, ss3')" "validTransO (ss4, ss4')" 
      and sa: "Opt.eqAct ss3 ss4"
      note v3 = v(1) note v4 = v(2)

      obtain pstate3' cfg3' cfgs3' ibT3' ibUT3' ls3' where ss3': "ss3' = (pstate3', cfg3', cfgs3', ibT3', ibUT3', ls3')"
      by (cases ss3', auto) 
      obtain pstate4' cfg4' cfgs4' ibT4' ibUT4' ls4' where ss4': "ss4' = (pstate4', cfg4', cfgs4', ibT4', ibUT4', ls4')"
      by (cases ss4', auto)
      note ss = ss ss3' ss4'

      show "\<not> isSecO ss3"
      using v sa \<Delta>3 unfolding ss by (simp add: \<Delta>3_defs) 

      show "\<not> isSecO ss4"
      using v sa \<Delta>3 unfolding ss  by (simp add: \<Delta>3_defs)  

      show stat: "statA = statA' \<or> statO = Diff"
      using v sa \<Delta>3 
      apply (cases ss3, cases ss4, cases ss1, cases ss2)
      apply(cases ss3', cases ss4', clarsimp)
      unfolding ss statA' apply clarsimp        
      apply(simp_all add: \<Delta>3_defs sstatA'_def) 
      apply(cases statO, simp_all) apply(cases statA, simp_all)
      unfolding finalS_defs  
      by (smt (z3) list.size(3) map_eq_imp_length_eq 
          n_not_Suc_n status.exhaust newStat.simps)


      show "oor \<Delta>3 \<Delta>1' \<infinity> ss3' ss4' statA' ss1 ss2 statO"
      using v3[unfolded ss, simplified] proof(cases rule: stepS_cases)
        case nonspec_normal
        then show ?thesis using sa stat \<Delta>3 lcfgs unfolding ss by (simp_all add: \<Delta>3_defs)  
      next
        case nonspec_mispred
        then show ?thesis using sa stat \<Delta>3 lcfgs unfolding ss by (simp_all add: \<Delta>3_defs) 
      next
        case spec_mispred
        then show ?thesis using sa stat \<Delta>3 lcfgs  unfolding ss apply-         
          apply(frule \<Delta>3_implies, clarsimp)
          by (auto simp add: \<Delta>3_defs)
      next (* the nontrivial cases deferred to the end: *)
        case spec_normal note sn3 = spec_normal
        show ?thesis
        using v4[unfolded ss, simplified] proof(cases rule: stepS_cases)
          case nonspec_normal
          then show ?thesis using sa stat \<Delta>3 lcfgs sn3 unfolding ss 
          by (simp add: \<Delta>3_defs)
        next
          case nonspec_mispred
          then show ?thesis using sa stat \<Delta>3 lcfgs sn3 unfolding ss 
          by (simp add: \<Delta>3_defs)
        next
          case spec_mispred
          then show ?thesis using sa stat \<Delta>3 lcfgs sn3 unfolding ss 
          apply (simp add: \<Delta>3_defs)  
          by (metis config.sel(1) last_map)
        next
          case spec_Fence
          then show ?thesis using sa stat \<Delta>3 lcfgs sn3 unfolding ss 
          apply (simp add: \<Delta>3_defs) 
          by (metis config.sel(1) last_map)
        next
          case spec_resolve
          then show ?thesis using sa stat \<Delta>3 lcfgs sn3 unfolding ss 
          by (simp add: \<Delta>3_defs) 
        next (* the nontrivial case deferred to the end: *)
          case spec_normal note sn4 = spec_normal
          show ?thesis
          apply(intro oorI1)
          unfolding ss \<Delta>3_def apply- apply(clarify,intro conjI)
            subgoal using sa stat \<Delta>3 lcfgs v3 v4 sn3 sn4 unfolding ss hh
            apply- apply(frule \<Delta>3_implies) apply(simp add: \<Delta>3_defs) 
            using cases_7[of pc3] apply simp apply(elim disjE)
            apply simp_all  
            by (metis config.collapse config.inject in_set_butlastD last_in_set length_1_butlast length_map state.sel(2))+  
            subgoal using sa stat \<Delta>3 lcfgs v3 v4 sn3 sn4 unfolding ss hh
            apply- apply(frule \<Delta>3_implies) by(simp add: \<Delta>3_defs)  
            subgoal using sa stat \<Delta>3 lcfgs v3 v4 sn3 sn4 unfolding ss hh
            apply- apply(frule \<Delta>3_implies) apply(simp add: \<Delta>3_defs) 
            using cases_7[of pc3] apply simp apply(elim disjE)
            by simp_all 
            subgoal using sa stat \<Delta>3 lcfgs v3 v4 sn3 sn4 unfolding ss hh 
            apply- apply(frule \<Delta>3_implies) apply(simp add: \<Delta>3_defs ) 
            using cases_7[of pc3] apply simp apply(elim disjE, simp_all)
            unfolding array_loc_def by (metis config.sel(2) dist_insert_su last_in_set state.sel(1) vstore.sel)+
            subgoal using sa stat \<Delta>3 lcfgs v3 v4 sn3 sn4 unfolding ss hh 
              apply- apply(frule \<Delta>3_implies) apply(simp add: \<Delta>3_defs) 
            using cases_7[of pc3] apply simp apply(elim disjE)
            apply simp_all by (metis array_loc_def dist_insert_su)+
            subgoal using sa stat \<Delta>3 lcfgs v3 v4 sn3 sn4 unfolding ss hh 
              apply- apply(frule \<Delta>3_implies) apply(simp add: \<Delta>3_defs) 
              using cases_7[of pc3] by(elim disjE, simp_all)
            subgoal using sa stat \<Delta>3 lcfgs v3 v4 sn3 sn4 unfolding ss hh 
            apply- apply(frule \<Delta>3_implies) apply(simp_all add: \<Delta>3_defs) 
              by (metis length_Suc_conv list.size(3)) .
          qed
        next
          case spec_Fence note sf3 = spec_Fence
          show ?thesis
          using v4[unfolded ss, simplified] proof(cases rule: stepS_cases)
            case nonspec_normal
            then show ?thesis using sa stat \<Delta>3 lcfgs sf3 unfolding ss 
            by (simp add: \<Delta>3_defs)
          next
            case nonspec_mispred
            then show ?thesis using sa stat \<Delta>3 lcfgs sf3 unfolding ss 
            by (simp add: \<Delta>3_defs)
          next
            case spec_mispred
            then show ?thesis using sa stat \<Delta>3 lcfgs sf3 unfolding ss 
            apply (simp add: \<Delta>3_defs) 
            by (metis com.disc config.sel(1) last_map)  
          next
            case spec_resolve
            then show ?thesis using sa stat \<Delta>3 lcfgs sf3 unfolding ss 
            by (simp add: \<Delta>3_defs) 
          next 
            case spec_normal 
            then show ?thesis using sa stat \<Delta>3 lcfgs sf3 unfolding ss 
            apply (simp add: \<Delta>3_defs)  
            by (metis last_map local.spec_Fence(3) local.spec_normal(1) local.spec_normal(4)) 
          next (* the nontrivial case deferred to the end: *)
            case spec_Fence note sf4 = spec_Fence
            show ?thesis
            apply(intro oorI2)
            unfolding ss \<Delta>1'_defs
            using sa stat \<Delta>3 lcfgs v3 v4 sf3 sf4 unfolding ss hh
            apply- by(simp_all add: \<Delta>3_defs \<Delta>1'_defs, blast) 
          qed
        next
          case spec_resolve note sr3 = spec_resolve
          show ?thesis
          using v4[unfolded ss, simplified] proof(cases rule: stepS_cases)
            case nonspec_normal
            then show ?thesis using sa stat \<Delta>3 lcfgs sr3 unfolding ss 
            by (simp add: \<Delta>3_defs)
          next
            case nonspec_mispred
            then show ?thesis using sa stat \<Delta>3 lcfgs sr3 unfolding ss 
            by (simp add: \<Delta>3_defs)
          next
            case spec_mispred
            then show ?thesis using sa stat \<Delta>3 lcfgs sr3 unfolding ss 
            by (simp add: \<Delta>3_defs)   
          next
            case spec_normal
            then show ?thesis using sa stat \<Delta>3 lcfgs sr3 unfolding ss 
            by (simp add: \<Delta>3_defs) 
          next 
            case spec_Fence  
            then show ?thesis using sa stat \<Delta>3 lcfgs sr3 unfolding ss 
            by (simp add: \<Delta>3_defs)    
          next (* the nontrivial case deferred to the end: *)
            case spec_resolve note sr4 = spec_resolve
            show ?thesis
            apply(intro oorI2)
            using sa stat \<Delta>3 lcfgs v3 v4 sr3 sr4 unfolding ss hh
            by(simp add: \<Delta>3_defs \<Delta>1_defs) 
          qed 
        qed
    qed
  qed  
qed 

(**)


lemma step1': "unwindIntoCond \<Delta>1' \<Delta>4" 
proof(rule unwindIntoCond_simpleI) 
  fix n ss3 ss4 statA ss1 ss2 statO
  assume r: "reachO ss3" "reachO ss4" "reachV ss1" "reachV ss2"
  and \<Delta>1': "\<Delta>1' n ss3 ss4 statA ss1 ss2 statO"

  obtain pstate3 cfg3 cfgs3 ibT3 ibUT3 ls3 where ss3: "ss3 = (pstate3, cfg3, cfgs3, ibT3, ibUT3, ls3)"
  by (cases ss3, auto) 
  obtain pstate4 cfg4 cfgs4 ibT4 ibUT4 ls4 where ss4: "ss4 = (pstate4, cfg4, cfgs4, ibT4, ibUT4, ls4)"
  by (cases ss4, auto)
  obtain cfg1 ibT1 ibUT1 ls1 where ss1: "ss1 = (cfg1, ibT1, ibUT1, ls1)"
  by (cases ss1, auto) 
  obtain cfg2 ibT2 ibUT2 ls2 where ss2: "ss2 = (cfg2, ibT2, ibUT2, ls2)"
  by (cases ss2, auto) 
  note ss = ss3 ss4 ss1 ss2
 
  obtain pc3 vs3 avst3 h3 p3 where 
  cfg3: "cfg3 = Config pc3 (State (Vstore vs3) avst3 h3 p3)"
  by (cases cfg3) (metis state.collapse vstore.collapse)
  obtain pc4 vs4 avst4 h4 p4 where 
  cfg4: "cfg4 = Config pc4 (State (Vstore vs4) avst4 h4 p4)"
  by (cases cfg4) (metis state.collapse vstore.collapse)
  note cfg = cfg3 cfg4

  obtain hh3 where h3: "h3 = Heap hh3" by(cases h3, auto)
  obtain hh4 where h4: "h4 = Heap hh4" by(cases h4, auto)
  note hh = h3 h4

  have f1:"\<not>finalN ss1" 
    using \<Delta>1' finalB_pc_iff' unfolding ss cfg finalN_iff_finalB \<Delta>1'_defs
    by simp 

  have f2:"\<not>finalN ss2" 
    using \<Delta>1' finalB_pc_iff' unfolding ss cfg finalN_iff_finalB \<Delta>1'_defs
    by simp 


  have f3:"\<not>finalS ss3" 
    using \<Delta>1' unfolding ss apply-apply(frule \<Delta>1'_implies)
    using finalS_cond by simp

  have f4:"\<not>finalS ss4" 
    using \<Delta>1' unfolding ss apply-apply(frule \<Delta>1'_implies)
    using finalS_cond by simp

  note finals = f1 f2 f3 f4

  show "finalS ss3 = finalS ss4 \<and> finalN ss1 = finalS ss3 \<and> finalN ss2 = finalS ss4"
    using finals by auto

  then show "isIntO ss3 = isIntO ss4" by simp

  show "react \<Delta>4 ss3 ss4 statA ss1 ss2 statO"
  unfolding react_def proof(intro conjI)
    (* match1 and match2 are imposibT,ibUTle case since isIntO always holds *)
    show "match1 \<Delta>4 ss3 ss4 statA ss1 ss2 statO"
    unfolding match1_def by (simp add: finalS_def final_def)
    show "match2 \<Delta>4 ss3 ss4 statA ss1 ss2 statO"
    unfolding match2_def by (simp add: finalS_def final_def)
    show "match12 \<Delta>4 ss3 ss4 statA ss1 ss2 statO"
    (* Choose the match12_12 case (since we have no mis-speculation yet) *)
    proof(rule match12_simpleI, rule disjI2, intro conjI)
      fix ss3' ss4' statA'
      assume statA': "statA' = sstatA' statA ss3 ss4"
      and v: "validTransO (ss3, ss3')" "validTransO (ss4, ss4')" 
      and sa: "Opt.eqAct ss3 ss4"
      note v3 = v(1) note v4 = v(2)

      obtain pstate3' cfg3' cfgs3' ibT3' ibUT3' ls3' where ss3': "ss3' = (pstate3', cfg3', cfgs3', ibT3', ibUT3', ls3')"
      by (cases ss3', auto) 
      obtain pstate4' cfg4' cfgs4' ibT4' ibUT4' ls4' where ss4': "ss4' = (pstate4', cfg4', cfgs4', ibT4', ibUT4', ls4')"
      by (cases ss4', auto)
      note ss = ss ss3' ss4'

      show "eqSec ss1 ss3"
        using v sa \<Delta>1' unfolding ss 
        by (simp add: \<Delta>1'_defs eqSec_def) 

      show "eqSec ss2 ss4"
        using v sa \<Delta>1' unfolding ss 
        by (simp add: \<Delta>1'_defs eqSec_def) 
      
      
      show "Van.eqAct ss1 ss2"
      using v sa \<Delta>1' unfolding ss Van.eqAct_def
      by (simp_all add: \<Delta>1'_defs)  

      show "match12_12 \<Delta>4 ss3' ss4' statA' ss1 ss2 statO"
      unfolding match12_12_def
      proof(rule exI[of _ "nextN ss1"], rule exI[of _ "nextN ss2"], unfold Let_def, intro conjI impI)
        show "validTransV (ss1, nextN ss1)" 
          by (simp add: f1 nextN_stepN)

        show "validTransV (ss2, nextN ss2)" 
          by (simp add: f2 nextN_stepN)

        {assume sstat: "statA' = Diff"
         show "sstatO' statO ss1 ss2 = Diff"
         using v sa \<Delta>1' sstat unfolding ss cfg statA'
         apply(simp add: \<Delta>1'_defs sstatO'_def sstatA'_def) 
         apply(cases statO, simp_all) apply(cases statA, simp_all) 
         using cfg finals ss status.distinct(1) newStat.simps by auto
        } note stat = this

        show "\<Delta>4 \<infinity> ss3' ss4' statA' (nextN ss1) (nextN ss2) (sstatO' statO ss1 ss2)"
        (* nonspec_normal and nonspec_mispred are the only nontrivial possibT,ibUTility, deferred to the end *)
        using v3[unfolded ss, simplified] proof(cases rule: stepS_cases)
          case spec_normal
          then show ?thesis using sa \<Delta>1' stat unfolding ss by (simp add: \<Delta>1'_defs)  
        next
          case spec_mispred
          then show ?thesis using sa \<Delta>1' stat unfolding ss by (simp add: \<Delta>1'_defs) 
        next
          case spec_Fence
          then show ?thesis using sa \<Delta>1' stat unfolding ss by (simp add: \<Delta>1'_defs) 
        next
          case spec_resolve
          then show ?thesis using sa \<Delta>1' stat unfolding ss by (simp add: \<Delta>1'_defs)
        next
          case nonspec_mispred 
          then show ?thesis using sa \<Delta>1' stat unfolding ss by (simp add: \<Delta>1'_defs)
        next
          case nonspec_normal note nn3 = nonspec_normal
          show ?thesis using v4[unfolded ss, simplified] proof(cases rule: stepS_cases)
          (* trace 4 can only have the same case as trace 3 as nontrivial case, here nonspec_normal -- deferred *)
            case nonspec_mispred
            then show ?thesis using sa \<Delta>1' stat nn3 unfolding ss by (simp add: \<Delta>1'_defs) 
          next
            case spec_normal
            then show ?thesis using sa \<Delta>1' stat nn3 unfolding ss by (simp add: \<Delta>1'_defs) 
          next
            case spec_mispred
            then show ?thesis using sa \<Delta>1' stat nn3 unfolding ss by (simp add: \<Delta>1'_defs) 
          next
            case spec_Fence
            then show ?thesis using sa \<Delta>1' stat nn3 unfolding ss by (simp add: \<Delta>1'_defs) 
          next
            case spec_resolve
            then show ?thesis using sa \<Delta>1' stat nn3 unfolding ss by (simp add: \<Delta>1'_defs) 
          next
            case nonspec_normal
            then show ?thesis using sa \<Delta>1' stat v3 v4 nn3 unfolding ss cfg hh apply clarsimp
              by (auto simp add: \<Delta>1'_defs \<Delta>4_defs)
          qed
        qed
      qed
    qed  
  qed
qed

(* *)

lemma stepe: "unwindIntoCond \<Delta>4 \<Delta>4" 
proof(rule unwindIntoCond_simpleI) 
  fix n ss3 ss4 statA ss1 ss2 statO
  assume r: "reachO ss3" "reachO ss4" "reachV ss1" "reachV ss2"
  and \<Delta>4: "\<Delta>4 n ss3 ss4 statA ss1 ss2 statO"

  obtain pstate3 cfg3 cfgs3 ibT3 ibUT3 ls3 where ss3: "ss3 = (pstate3, cfg3, cfgs3, ibT3, ibUT3, ls3)"
  by (cases ss3, auto) 
  obtain pstate4 cfg4 cfgs4 ibT4 ibUT4 ls4 where ss4: "ss4 = (pstate4, cfg4, cfgs4, ibT4, ibUT4, ls4)"
  by (cases ss4, auto)
  obtain cfg1 ibT1 ibUT1 ls1 where ss1: "ss1 = (cfg1, ibT1, ibUT1, ls1)"
  by (cases ss1, auto) 
  obtain cfg2 ibT2 ibUT2 ls2 where ss2: "ss2 = (cfg2, ibT2, ibUT2, ls2)"
  by (cases ss2, auto) 
  note ss = ss3 ss4 ss1 ss2
 
  obtain pc3 vs3 avst3 h3 p3 where 
  cfg3: "cfg3 = Config pc3 (State (Vstore vs3) avst3 h3 p3)"
  by (cases cfg3) (metis state.collapse vstore.collapse)
  obtain pc4 vs4 avst4 h4 p4 where 
  cfg4: "cfg4 = Config pc4 (State (Vstore vs4) avst4 h4 p4)"
  by (cases cfg4) (metis state.collapse vstore.collapse)
  note cfg = cfg3 cfg4

  obtain hh3 where h3: "h3 = Heap hh3" by(cases h3, auto)
  obtain hh4 where h4: "h4 = Heap hh4" by(cases h4, auto)
  note hh = h3 h4

  show "finalS ss3 = finalS ss4 \<and> finalN ss1 = finalS ss3 \<and> finalN ss2 = finalS ss4"
    using \<Delta>4 Opt.final_def Prog.endPC_def finalS_def stepS_endPC endPC_def finalB_endPC 
    unfolding \<Delta>4_defs ss by clarsimp 

  then show "isIntO ss3 = isIntO ss4" by simp

  show "react \<Delta>4 ss3 ss4 statA ss1 ss2 statO"
  unfolding react_def proof(intro conjI)
    (* match1 and match2 are imposibT,ibUTle case since isIntO always holds *)
    show "match1 \<Delta>4 ss3 ss4 statA ss1 ss2 statO"
    unfolding match1_def by (simp add: finalS_def final_def)
    show "match2 \<Delta>4 ss3 ss4 statA ss1 ss2 statO"
    unfolding match2_def by (simp add: finalS_def final_def)
    show "match12 \<Delta>4 ss3 ss4 statA ss1 ss2 statO"
    apply(rule match12_simpleI) using \<Delta>4 unfolding ss apply (simp add: \<Delta>4_defs)
    by (simp add: stepS_endPC)
  qed
qed
 
(* *)

lemmas theConds = step0 step1 step2 step3 step1' stepe


proposition rsecure
proof-
  define m where m: "m \<equiv> (6::nat)"
  define \<Delta>s where \<Delta>s: "\<Delta>s \<equiv> \<lambda>i::nat. 
  if i = 0 then \<Delta>0
  else if i = 1 then \<Delta>1 
  else if i = 2 then \<Delta>2
  else if i = 3 then \<Delta>3 
  else if i = 4 then \<Delta>4 
  else \<Delta>1'" 
  define nxt where nxt: "nxt \<equiv> \<lambda>i::nat. 
  if i = 0 then {0,1::nat}
  else if i = 1 then {1,2,3,4}  
  else if i = 2 then {1} 
  else if i = 3 then {3,5} 
  else {4}"
  show ?thesis apply(rule distrib_unwind_rsecure[of m nxt \<Delta>s])
    subgoal unfolding m by auto
    subgoal unfolding nxt m by auto
    subgoal using init unfolding \<Delta>s by auto
    subgoal 
      unfolding m nxt \<Delta>s apply (simp split: if_splits)
      using theConds
      unfolding oor_def oor4_def by auto . 
qed
end