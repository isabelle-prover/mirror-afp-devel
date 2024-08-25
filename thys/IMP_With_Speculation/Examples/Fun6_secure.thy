subsection "Proof"
theory Fun6_secure
imports Fun6
begin 

(* Common to all the unwinding relations in this proof: *)
definition common :: "enat \<Rightarrow> enat \<Rightarrow> stateO \<Rightarrow> stateO \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" 
where 
"common = (\<lambda>w1 w2
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
 llength ibT1 = \<infinity> \<and> llength ibT2 = \<infinity> \<and>
 llength ibUT1 = \<infinity> \<and> llength ibUT2 = \<infinity> \<and>

 ibT1 = ibT3 \<and> ibT2 = ibT4 \<and>
 ibUT1 = ibUT3 \<and> ibUT2 = ibUT4 \<and>

  w1 = w2 \<and>
 \<^cancel>\<open>   \<close>
 array_base aa1 (getAvstore (stateOf cfg3)) = array_base aa1 (getAvstore (stateOf cfg4)) \<and> 
 (\<forall>cfg3'\<in>set cfgs3. array_base aa1 (getAvstore (stateOf cfg3')) = array_base aa1 (getAvstore (stateOf cfg3))) \<and> 
 (\<forall>cfg4'\<in>set cfgs4. array_base aa1 (getAvstore (stateOf cfg4')) = array_base aa1 (getAvstore (stateOf cfg4))) \<and> 
 array_base aa2 (getAvstore (stateOf cfg3)) = array_base aa2 (getAvstore (stateOf cfg4)) \<and> 
 (\<forall>cfg3'\<in>set cfgs3. array_base aa2 (getAvstore (stateOf cfg3')) = array_base aa2 (getAvstore (stateOf cfg3))) \<and> 
 (\<forall>cfg4'\<in>set cfgs4. array_base aa2 (getAvstore (stateOf cfg4')) = array_base aa2 (getAvstore (stateOf cfg4))) \<and> 
 \<^cancel>\<open>   \<close>
 (statA = Diff \<longrightarrow> statO = Diff) \<and>
  Dist ls1 ls2 ls3 ls4))"

lemma common_implies: "common w1 w2 (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
   statO \<Longrightarrow> 
   pcOf cfg1 < 14 \<and> pcOf cfg2 = pcOf cfg1 \<and>
   ibT1 \<noteq> [[]] \<and> ibT2 \<noteq> [[]] \<and>
   ibUT1 \<noteq> [[]] \<and> ibUT2 \<noteq> [[]] \<and>
   w1 = w2"
unfolding common_def PC_def by (auto simp: image_def subset_eq)


(* Before input is inserted *)
definition \<Delta>0 :: "enat \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> stateO \<Rightarrow> stateO  \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" where 
"\<Delta>0 = (\<lambda>num w1 w2 (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
     statO.
 (common w1 w2 (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
     statO  \<and> 
  pcOf cfg3 \<in> beforeWhile \<and> 
  (pcOf cfg3 > 1 \<longrightarrow> same_var_o tt cfg3 cfgs3 cfg4 cfgs4) \<and>
  (pcOf cfg3 > 2 \<longrightarrow> same_var_o xx cfg3 cfgs3 cfg4 cfgs4) \<and>
  (pcOf cfg3 > 4 \<longrightarrow> same_var_o xx cfg3 cfgs3 cfg4 cfgs4) \<and>
  noMisSpec cfgs3
))"

lemmas \<Delta>0_defs = \<Delta>0_def common_def PC_def same_var_o_def
                  beforeWhile_def noMisSpec_def

lemma \<Delta>0_implies: "\<Delta>0 num w1 w2 (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
   statO \<Longrightarrow> 
   pcOf cfg1 < 14 \<and> pcOf cfg2 = pcOf cfg1 \<and>
   ibT1 \<noteq> [[]] \<and> ibT2 \<noteq> [[]] \<and> 
   ibUT1 \<noteq> [[]] \<and> ibUT2 \<noteq> [[]] \<and> 
   cfgs4 = []"
  apply (meson \<Delta>0_def common_implies)
  by (simp_all add: \<Delta>0_defs, metis Nil_is_map_conv)

(* After input is inserted, no mis-speculation *)
definition \<Delta>1 :: "enat \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> stateO \<Rightarrow> stateO  \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" where 
"\<Delta>1 = (\<lambda>num w1 w2 (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
     statO.
 (common w1 w2 (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2)
     statO \<and> 
  pcOf cfg3 \<in> afterWhile \<and> 
  same_var_o xx cfg3 cfgs3 cfg4 cfgs4 \<and>
  noMisSpec cfgs3
))"
lemmas \<Delta>1_defs = \<Delta>1_def common_def noMisSpec_def PC_def afterWhile_def same_var_o_def
lemma \<Delta>1_implies: "\<Delta>1 n w1 w2 (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
   statO \<Longrightarrow> 
   pcOf cfg3 < 14 \<and> cfgs3 = [] \<and> ibT3 \<noteq> [[]] \<and>
   pcOf cfg4 < 14 \<and> cfgs4 = [] \<and> ibT4 \<noteq> [[]] \<and>
   ibUT3 \<noteq> [[]] \<and> ibUT4 \<noteq> [[]]"
  unfolding \<Delta>1_defs apply clarify 
  by (metis atLeastAtMost_iff eval_nat_numeral(2) infinity_ne_i0 
      less_Suc_eq_le list.map_disc_iff llength_LNil semiring_norm(28))


(* WHILE mis-speculation: *)
definition \<Delta>1' :: "enat \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> stateO \<Rightarrow> stateO  \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" where 
"\<Delta>1' = (\<lambda>num w1 w2 (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
     statO.
 (common w1 w2 (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
     statO  \<and> 
  same_var_o xx cfg3 cfgs3 cfg4 cfgs4 \<and>  
  whileSpeculation cfg3 (last cfgs3) \<and>
  misSpecL1 cfgs3 \<and> misSpecL1 cfgs4 \<and>
  w1 = \<infinity>
))"

lemmas \<Delta>1'_defs = \<Delta>1'_def common_def PC_def same_var_def 
                  startOfIfThen_def startOfElseBranch_def 
                  misSpecL1_def whileSpec_defs

lemma \<Delta>1'_implies: "\<Delta>1' num w1 w2 (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
   statO \<Longrightarrow> 
   pcOf cfg3 < 14 \<and> pcOf cfg4 < 14 \<and>
   whileSpeculation cfg3 (last cfgs3) \<and>
   whileSpeculation cfg4 (last cfgs4) \<and>
   length cfgs3 = Suc 0 \<and> length cfgs4 = Suc 0"
  unfolding \<Delta>1'_defs by clarsimp


(* Left mis-speculation: *)
definition \<Delta>2 :: "enat \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> stateO \<Rightarrow> stateO  \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" where 
"\<Delta>2 = (\<lambda>num w1 w2 (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
     statO.
 (common w1 w2 (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
     statO  \<and> 
  
  same_var_o xx cfg3 cfgs3 cfg4 cfgs4 \<and>  
  pcOf cfg3 = startOfIfThen \<and> pcOf (last cfgs3) \<in> inElseIf \<and> 
  misSpecL1 cfgs3 \<and> misSpecL1 cfgs4 \<and>

  (pcOf (last cfgs3) = startOfElseBranch \<longrightarrow> w1 = \<infinity>) \<and>
  (pcOf (last cfgs3) = 3 \<longrightarrow> w1 = 3) \<and>

  (pcOf (last cfgs3) = startOfWhileThen \<or>
   pcOf (last cfgs3) = whileElse \<longrightarrow> w1 = 1)

))"

lemmas \<Delta>2_defs = \<Delta>2_def common_def PC_def same_var_o_def misSpecL1_def
                  startOfIfThen_def inElseIf_def same_var_def
                  startOfWhileThen_def whileElse_def startOfElseBranch_def

lemma \<Delta>2_implies: "\<Delta>2 num w1 w2 (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
     statO  \<Longrightarrow> 
   pcOf (last cfgs3) \<in> inElseIf \<and> pcOf cfg3 = 7 \<and>
   pcOf (last cfgs4) = pcOf (last cfgs3) \<and>
   pcOf cfg4 = pcOf cfg3 \<and> length cfgs3 = Suc 0 \<and>
   length cfgs4 = Suc 0 \<and> same_var xx (last cfgs3) (last cfgs4)"
apply(intro conjI)
  unfolding \<Delta>2_defs  
        apply (simp_all add: image_subset_iff) 
  by (metis last_in_set length_0_conv Nil_is_map_conv last_map length_map)+

(* 2nd specualtion level: *)
definition \<Delta>2' :: "enat \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> stateO \<Rightarrow> stateO  \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" where 
"\<Delta>2' = (\<lambda>num w1 w2 (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
     statO.
 (common w1 w2 (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
     statO  \<and> 
  same_var_o xx cfg3 cfgs3 cfg4 cfgs4 \<and>  
  pcOf cfg3 = startOfIfThen \<and> 
  whileSpeculation (cfgs3!0) (last cfgs3) \<and>
  misSpecL2 cfgs3 \<and> misSpecL2 cfgs4 \<and>
  w1 = 2
))"

lemmas \<Delta>2'_defs = \<Delta>2'_def common_def PC_def same_var_def   
                   startOfElseBranch_def startOfIfThen_def
                   whileSpec_defs misSpecL2_def

lemma \<Delta>2'_implies: "\<Delta>2' num w1 w2 (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
     statO \<Longrightarrow> 
  pcOf cfg3 = 7 \<and> pcOf cfg4 = 7 \<and>
  whileSpeculation (cfgs3!0) (last cfgs3) \<and>
  whileSpeculation (cfgs4!0) (last cfgs4) \<and>
  length cfgs3 = 2 \<and> length cfgs4 = 2"
  apply(intro conjI)
  unfolding \<Delta>2'_defs apply (simp add: lessI, clarify) 
  apply linarith+ apply simp_all 
  by (metis list.inject map_L2)

(* Right mis-speculation: *)
definition \<Delta>3 :: "enat \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> stateO \<Rightarrow> stateO  \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" where 
"\<Delta>3 = (\<lambda>num w1 w2 (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
     statO.
 (common w1 w2 (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
     statO  \<and> 
  same_var_o xx cfg3 cfgs3 cfg4 cfgs4 \<and>  
  pcOf cfg3 = startOfElseBranch \<and> pcOf (last cfgs3) \<in> inThenIfBeforeOutput \<and> 
  misSpecL1 cfgs3 \<and>
  (pcOf (last cfgs3) = 7 \<longrightarrow> w1 = \<infinity>) \<and>
  (pcOf (last cfgs3) = 8 \<longrightarrow> w1 = 2) \<and>
  (pcOf (last cfgs3) = 9 \<longrightarrow> w1 = 1)
))"

lemmas \<Delta>3_defs = \<Delta>3_def common_def PC_def same_var_o_def 
                  startOfElseBranch_def inThenIfBeforeOutput_def

lemma \<Delta>3_implies: "\<Delta>3 num w1 w2 (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
     statO  \<Longrightarrow> 
   pcOf (last cfgs3) \<in> inThenIfBeforeOutput \<and> 
   pcOf (last cfgs4) = pcOf (last cfgs3) \<and>
   pcOf cfg3 = 12 \<and> pcOf cfg3 = pcOf cfg4 \<and>
   length cfgs3 = Suc 0 \<and> length cfgs4 = Suc 0"
apply(intro conjI)
  unfolding \<Delta>3_defs 
  apply (simp_all add: image_subset_iff) 
  by (metis last_map map_is_Nil_conv length_map)+

(* *)

(* End: *)
definition \<Delta>e :: "enat \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> stateO \<Rightarrow> stateO  \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" where 
"\<Delta>e = (\<lambda>num w1 w2 (pstate3,cfg3,cfgs3,ib3,ls3) 
     (pstate4,cfg4,cfgs4,ib4,ls4)  
     statA 
     (cfg1,ib1,ls1) 
     (cfg2,ib2,ls2) 
     statO.
   (pcOf cfg3 = endPC \<and> pcOf cfg4 = endPC \<and> cfgs3 = [] \<and> cfgs4 = [] \<and>
    pcOf cfg1 = endPC \<and> pcOf cfg2 = endPC))"

lemmas \<Delta>e_defs = \<Delta>e_def common_def endPC_def  

(* *)

lemma init: "initCond \<Delta>0" 
unfolding initCond_def apply safe  
  subgoal for pstate3 cfg3 cfgs3 ibT3 ibUT3 ls3 
              pstate4 cfg4 cfgs4 ibT4 ibUT4 ls4 
  unfolding istateO.simps apply clarsimp
apply(cases "getAvstore (stateOf cfg3)", cases "getAvstore (stateOf cfg4)")
unfolding \<Delta>0_defs  
unfolding array_base_def by auto .

(* *)
 
lemma step0: "unwindIntoCond \<Delta>0 (oor \<Delta>0 \<Delta>1)"
proof(rule unwindIntoCond_simpleI)  
  fix n w1 w2 ss3 ss4 statA ss1 ss2 statO
  assume r: "reachO ss3" "reachO ss4" "reachV ss1" "reachV ss2"
  and \<Delta>0: "\<Delta>0 n w1 w2 ss3 ss4 statA ss1 ss2 statO"

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
    using \<Delta>0 unfolding ss 
    apply-by(frule \<Delta>0_implies, simp)

  have f2:"\<not>finalN ss2" 
    using \<Delta>0 unfolding ss 
    apply-by(frule \<Delta>0_implies, simp)

  have f3:"\<not>finalS ss3" 
    using \<Delta>0 unfolding ss 
    apply-apply(frule \<Delta>0_implies, unfold \<Delta>0_defs)
    using finalS_cond' by simp

  have f4:"\<not>finalS ss4" 
    using \<Delta>0 unfolding ss 
    apply-apply(frule \<Delta>0_implies, unfold \<Delta>0_defs)
    using finalS_cond' by simp

  note finals = f1 f2 f3 f4
  show "finalS ss3 = finalS ss4 \<and> finalN ss1 = finalS ss3 \<and> finalN ss2 = finalS ss4"
    using finals by auto

  then show "isIntO ss3 = isIntO ss4" by simp


  show "match (oor \<Delta>0 \<Delta>1) w1 w2 ss3 ss4 statA ss1 ss2 statO"
  unfolding match_def proof(intro conjI)
    (* match1 and match2 are imposible case since isIntO always holds *)
    show "match1 (oor \<Delta>0 \<Delta>1) w1 w2 ss3 ss4 statA ss1 ss2 statO"
    unfolding match1_def by (simp add: finalS_def final_def)
    show "match2 (oor \<Delta>0 \<Delta>1) w1 w2 ss3 ss4 statA ss1 ss2 statO"
    unfolding match2_def by (simp add: finalS_def final_def)
    show "match12 (oor \<Delta>0 \<Delta>1) w1 w2 ss3 ss4 statA ss1 ss2 statO"
    (* Choose the match12_12 case (since we have no mis-speculation yet) *)
    proof(rule match12_simpleI,rule disjI2, intro conjI)
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
        using v sa \<Delta>0 finals unfolding ss 
        by (simp add: \<Delta>0_defs eqSec_def) 

      show "eqSec ss2 ss4"
        using v sa \<Delta>0 finals unfolding ss 
        by (simp add: \<Delta>0_defs eqSec_def, metis map_is_Nil_conv)

      show "Van.eqAct ss1 ss2"
        using v sa \<Delta>0 unfolding ss   
        apply-apply(frule \<Delta>0_implies)
      unfolding Opt.eqAct_def 
                Van.eqAct_def
      by(simp_all add: \<Delta>0_defs, linarith) 

      show "match12_12 (oor \<Delta>0 \<Delta>1) \<infinity> \<infinity> ss3' ss4' statA' ss1 ss2 statO"
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
         using cases_14[of pc3] apply(elim disjE)
         apply simp_all apply(cases statO, simp_all) apply(cases statA, simp_all)
         apply(cases statO, simp_all) apply (cases statA, simp_all)
         by (smt (z3) status.distinct status.exhaust updStat.simps)+
        } note stat = this

        show "oor \<Delta>0 \<Delta>1 \<infinity> \<infinity> \<infinity> ss3' ss4' statA' (nextN ss1) (nextN ss2) (sstatO' statO ss1 ss2)"
        (* the combination of nonspec_normal and nonspec_normal is the only nontrivial possibility, 
           deferred to the end *)
        using v3[unfolded ss, simplified] proof(cases rule: stepS_cases)
          case nonspec_mispred
          then show ?thesis using sa \<Delta>0 stat unfolding ss
          by (simp add: \<Delta>0_defs numeral_1_eq_Suc_0, linarith) 
        next
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
            case nonspec_normal note nn4 = nonspec_normal
            show ?thesis using sa \<Delta>0 stat v3 v4 nn3 nn4 unfolding ss cfg apply clarsimp
            apply(unfold \<Delta>0_defs, clarsimp, elim disjE)
              subgoal by(rule oorI1, auto simp add: \<Delta>0_defs) 
              subgoal by (rule oorI1, simp add: \<Delta>0_defs) 
              subgoal by (rule oorI2, simp add: \<Delta>1_defs) .
          qed
        qed
      qed
    qed  
  qed
qed

(* *)

lemma step1: "unwindIntoCond \<Delta>1 (oor5 \<Delta>1 \<Delta>1' \<Delta>2 \<Delta>3 \<Delta>e)" 
proof(rule unwindIntoCond_simpleI) 
  fix n w1 w2 ss3 ss4 statA ss1 ss2 statO
  assume r: "reachO ss3" "reachO ss4" "reachV ss1" "reachV ss2"
  and \<Delta>1: "\<Delta>1 n w1 w2 ss3 ss4 statA ss1 ss2 statO"

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
  using \<Delta>1 unfolding ss \<Delta>1_def apply clarify
  apply(frule common_implies) 
  using finalB_pcOf_iff finalN_iff_finalB nat_less_le by metis

  have f2:"\<not>finalN ss2" 
  using \<Delta>1 unfolding ss \<Delta>1_def  apply clarify
  apply(frule common_implies) 
  using finalB_pcOf_iff finalN_iff_finalB nat_less_le by metis


  have f3:"\<not>finalS ss3" 
    using \<Delta>1 unfolding ss 
    apply-apply(frule \<Delta>1_implies)
    by (simp add: finalS_cond')

  have f4:"\<not>finalS ss4" 
    using \<Delta>1 unfolding ss 
    apply-apply(frule \<Delta>1_implies)
    by (simp add: finalS_cond')

  note finals = f1 f2 f3 f4
  show "finalS ss3 = finalS ss4 \<and> finalN ss1 = finalS ss3 \<and> finalN ss2 = finalS ss4"
    using finals by auto

  then show "isIntO ss3 = isIntO ss4" by simp


  show "match (oor5 \<Delta>1 \<Delta>1' \<Delta>2 \<Delta>3 \<Delta>e) w1 w2 ss3 ss4 statA ss1 ss2 statO"
  unfolding match_def proof(intro conjI)
    (* match1 and match2 are imposible case since isIntO always holds *)
    show "match1 (oor5 \<Delta>1 \<Delta>1' \<Delta>2 \<Delta>3 \<Delta>e) w1 w2 ss3 ss4 statA ss1 ss2 statO"
    unfolding match1_def by (simp add: finalS_def final_def)
    show "match2 (oor5 \<Delta>1 \<Delta>1' \<Delta>2 \<Delta>3 \<Delta>e) w1 w2 ss3 ss4 statA ss1 ss2 statO"
    unfolding match2_def by (simp add: finalS_def final_def)
    show "match12 (oor5 \<Delta>1 \<Delta>1' \<Delta>2 \<Delta>3 \<Delta>e) w1 w2 ss3 ss4 statA ss1 ss2 statO"
    (* Choose the match12_12 case (since we have no mis-speculation yet) *)
    proof(rule match12_simpleI,rule disjI2, intro conjI)
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
      using v sa \<Delta>1 finals unfolding ss by (simp add: \<Delta>1_defs eqSec_def) 

      show "eqSec ss2 ss4"
        using v sa \<Delta>1 finals unfolding ss 
        by (simp add: \<Delta>1_defs eqSec_def, metis map_is_Nil_conv) 
      
      show "Van.eqAct ss1 ss2"
      using v sa \<Delta>1 unfolding ss apply- apply(frule \<Delta>1_implies)
      unfolding Opt.eqAct_def Van.eqAct_def
      apply(simp_all add: \<Delta>1_defs)
      by (metis f3 getActO_pcOf numeral_eq_iff numeral_less_iff semiring_norm(77,78,81,89) ss3)

      show "match12_12 (oor5 \<Delta>1 \<Delta>1' \<Delta>2 \<Delta>3 \<Delta>e) \<infinity> \<infinity> ss3' ss4' statA' ss1 ss2 statO"
      unfolding match12_12_def 
      proof(rule exI[of _ "nextN ss1"], rule exI[of _ "nextN ss2"],unfold Let_def, intro conjI impI)
        show "validTransV (ss1, nextN ss1)" 
          by (simp add: f1 nextN_stepN)
 
        show "validTransV (ss2, nextN ss2)" 
          by (simp add: f2 nextN_stepN) 

        {assume sstat: "statA' = Diff"
         show "sstatO' statO ss1 ss2 = Diff"
           using v sa \<Delta>1 sstat finals unfolding ss cfg statA'
           apply-apply(frule \<Delta>1_implies)
         apply(simp add: \<Delta>1_defs sstatO'_def sstatA'_def updStat_EqI) 
         using cases_14[of pc3] apply(elim disjE, simp_all)
         subgoal apply(cases statO, simp_all) 
           by(cases statA, simp_all add: updStat_EqI)
         subgoal apply(cases statO, simp_all) 
           by(cases statA, simp_all add: updStat_EqI) 
         subgoal apply(cases statO, simp_all) 
           by(cases statA, simp_all add: updStat_EqI) 
         subgoal apply(cases statO, simp_all) 
           by(cases statA, simp_all add: updStat_EqI)
         subgoal apply(cases statO, simp_all) 
           by(cases statA, simp_all add: updStat_EqI)
         subgoal apply(cases statO, simp_all) 
           by(cases statA, simp_all add: updStat_EqI)
         subgoal apply(cases statO, simp_all, cases statA) 
           by (simp_all add: updStat_EqI)  
         subgoal apply(cases statO, simp_all) 
           by(cases statA, simp_all add: updStat_EqI)
         subgoal apply(cases statO, simp_all, cases statA) 
           by (simp_all add: updStat_EqI split: if_splits)
         subgoal apply(cases statO, simp_all, cases statA) 
           by (simp_all add: updStat_EqI split: if_splits)
         subgoal apply(cases statO, simp_all, cases statA) 
           by (simp_all add: updStat_EqI split: if_splits) .
        } note stat = this

        show "oor5 \<Delta>1 \<Delta>1' \<Delta>2 \<Delta>3 \<Delta>e \<infinity> \<infinity> \<infinity> ss3' ss4' statA' (nextN ss1) (nextN ss2) (sstatO' statO ss1 ss2)"
        (* nonspec_normal and nonspec_mispred are the only nontrivial possibility, deferred to the end *)
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
            case nonspec_normal note nn4 = nonspec_normal
            then show ?thesis using sa \<Delta>1 stat v3 v4 nn3 nn4 f4 unfolding ss cfg Opt.eqAct_def
            apply clarsimp using cases_14[of pc3] apply(elim disjE)
              subgoal by (simp add: \<Delta>1_defs)
              subgoal by (simp add: \<Delta>1_defs)
              subgoal by (simp add: \<Delta>1_defs)
              subgoal using xx_0_cases[of vs3] apply(elim disjE)
                subgoal by(rule oor5I1, auto simp add: \<Delta>1_defs)
                subgoal by(rule oor5I1, auto simp add: \<Delta>1_defs) .
              subgoal apply(rule oor5I1) by (auto simp add: \<Delta>1_defs) 
              subgoal apply(rule oor5I1) by (auto simp add: \<Delta>1_defs) 
              subgoal using xx_NN_cases[of vs3] apply(elim disjE)
                subgoal by(rule oor5I1, auto simp add: \<Delta>1_defs)
                subgoal by(rule oor5I1, auto simp add: \<Delta>1_defs) .
              subgoal by(rule oor5I1, auto simp add: \<Delta>1_defs hh)
              subgoal by(rule oor5I1, auto simp add: \<Delta>1_defs)   
              subgoal by(rule oor5I1, auto simp add: \<Delta>1_defs hh) 
              subgoal by(rule oor5I1, auto simp add: \<Delta>1_defs hh) 
              subgoal by(rule oor5I1, auto simp add: \<Delta>1_defs)  
              subgoal by(rule oor5I1, auto simp add: \<Delta>1_defs)
              by(rule oor5I5, simp_all add: \<Delta>1_defs \<Delta>e_defs) 
          qed
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
            then show ?thesis using sa \<Delta>1 stat v3 v4 nm3 nm4 unfolding ss cfg apply clarsimp
            using cases_14[of pc3] apply(elim disjE)
              prefer 4 subgoal using xx_0_cases[of vs3] apply(elim disjE)
                subgoal by(rule oor5I2, auto simp add: \<Delta>1_defs \<Delta>1'_defs) 
                subgoal by(rule oor5I2, auto simp add: \<Delta>1_defs \<Delta>1'_defs) .
              prefer 6 subgoal using xx_NN_cases[of vs3] apply(elim disjE)
                subgoal apply(rule oor5I3) by (auto simp add: \<Delta>1_defs \<Delta>2_defs)
                subgoal apply(rule oor5I4) by (auto simp add: \<Delta>1_defs \<Delta>3_defs) .
              by (simp_all add: \<Delta>1_defs) 
          qed
        qed
      qed
    qed  
  qed
qed

(* *)

lemma step2: "unwindIntoCond \<Delta>2 (oor3 \<Delta>2 \<Delta>2' \<Delta>1)" 
proof(rule unwindIntoCond_simpleI)
  fix n w1 w2 ss3 ss4 statA ss1 ss2 statO
  assume r: "reachO ss3" "reachO ss4" "reachV ss1" "reachV ss2"
  and \<Delta>2: "\<Delta>2 n w1 w2 ss3 ss4 statA ss1 ss2 statO"

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
  using \<Delta>2 unfolding ss \<Delta>2_def
  apply clarsimp 
  by(frule common_implies, simp)

  have f2:"\<not>finalN ss2" 
  using \<Delta>2 unfolding ss \<Delta>2_def
  apply clarsimp 
  by(frule common_implies, simp)


  have f3:"\<not>finalS ss3" 
    using \<Delta>2 unfolding ss 
    apply-apply(frule \<Delta>2_implies)
    by (simp add: finalS_if_spec)

  have f4:"\<not>finalS ss4" 
    using \<Delta>2 unfolding ss 
    apply-apply(frule \<Delta>2_implies)
    by (simp add: finalS_if_spec)

  note finals = f1 f2 f3 f4
  show "finalS ss3 = finalS ss4 \<and> finalN ss1 = finalS ss3 \<and> finalN ss2 = finalS ss4"
    using finals by auto

  then show "isIntO ss3 = isIntO ss4" by simp

  then have lpc3:"pcOf (last cfgs3) = 12 \<or> 
                  pcOf (last cfgs3) = 3 \<or>
                  pcOf (last cfgs3) = 4 \<or>
                  pcOf (last cfgs3) = 13"
    using \<Delta>2 unfolding ss \<Delta>2_defs by simp

  (*because of a spliting on the cases, it's simpler to prove these prior*)
  have sec3[simp]:"\<not> isSecO ss3"
    using \<Delta>2 finals unfolding ss isSecO_def 
    by(simp add: \<Delta>2_defs, metis list.size(3) n_not_Suc_n)

  have sec4[simp]:"\<not> isSecO ss4"
    using \<Delta>2 unfolding ss 
    by (simp add: \<Delta>2_defs, metis list.size(3) n_not_Suc_n)   

    have stat[simp]:"\<And>s3' s4' statA'. statA' = sstatA' statA ss3 ss4 \<Longrightarrow> 
               validTransO (ss3, s3') \<Longrightarrow> validTransO (ss4, s4') \<Longrightarrow>
               (statA = statA' \<or> statO = Diff)"
    subgoal for ss3' ss4'
      apply (cases ss3, cases ss4, cases ss1, cases ss2)
      apply (cases ss3', cases ss4', clarsimp)
      using \<Delta>2 finals unfolding ss apply clarsimp        
      apply(simp_all add: \<Delta>2_defs sstatA'_def) 
      apply(cases statO, simp_all) by (cases statA, simp_all add: updStat_EqI) .

  have xx:"vs3 xx = vs4 xx" using \<Delta>2 lcfgs unfolding ss \<Delta>2_defs apply clarsimp
    by (metis cfgs_Suc_zero config.sel(2) list.set_intros(1) state.sel(1) vstore.sel)


  have oor3_rule:"\<And>ss3' ss4'. ss3 \<rightarrow>S ss3' \<Longrightarrow> ss4 \<rightarrow>S ss4' \<Longrightarrow>
                    (pcOf (last cfgs3) = 12 \<longrightarrow> oor3 \<Delta>2 \<Delta>2' \<Delta>1 \<infinity> 3 3 ss3' ss4' (sstatA' statA ss3 ss4) ss1 ss2 statO) 
                  \<and> (pcOf (last cfgs3) = 3 \<and> mispred pstate4 [7, 3] \<longrightarrow> oor3 \<Delta>2 \<Delta>2' \<Delta>1 \<infinity> 2 2 ss3' ss4' (sstatA' statA ss3 ss4) ss1 ss2 statO)
                  \<and> (pcOf (last cfgs3) = 3 \<and> \<not>mispred pstate4 [7, 3] \<longrightarrow> oor3 \<Delta>2 \<Delta>2' \<Delta>1 \<infinity> 1 1 ss3' ss4' (sstatA' statA ss3 ss4) ss1 ss2 statO)
                  \<and> ((pcOf (last cfgs3) = 4 \<or> pcOf (last cfgs3) = 13) \<longrightarrow> oor3 \<Delta>2 \<Delta>2' \<Delta>1 \<infinity> 0 0 ss3' ss4' (sstatA' statA ss3 ss4) ss1 ss2 statO) \<Longrightarrow>
                    \<exists>w1'<w1. \<exists>w2'<w2. oor3 \<Delta>2 \<Delta>2' \<Delta>1 \<infinity> w1' w2' ss3' ss4' (sstatA' statA ss3 ss4) ss1 ss2 statO"       
    subgoal for ss3' ss4' apply(cases ss3', cases ss4')
        subgoal for pstate3' cfg3' cfgs3' ibT3' ibUT3' ls3' 
                    pstate4' cfg4' cfgs4' ibT4' ibUT4' ls4' 
     subgoal premises p using lpc3 apply-apply(erule disjE)
          subgoal apply(intro exI[of _ 3], intro conjI)
            subgoal using \<Delta>2 unfolding ss \<Delta>2_defs apply clarify
              by (metis enat_ord_simps(4) numeral_ne_infinity)
            apply(intro exI[of _ 3], rule conjI)
            subgoal using \<Delta>2 unfolding ss \<Delta>2_defs apply clarify
              by (metis enat_ord_simps(4) numeral_ne_infinity)
            using p by (simp add: p)
          apply(erule disjE)
          subgoal apply(cases "mispred pstate4 [7, 3]")
             subgoal apply(intro exI[of _ 2], intro conjI)
              using \<Delta>2 unfolding ss \<Delta>2_defs apply clarify
                apply (metis enat_ord_number(2) eval_nat_numeral(3) lessI)
              apply(intro exI[of _ 2], rule conjI)
              using \<Delta>2 unfolding ss \<Delta>2_defs apply clarify
               apply (metis enat_ord_number(2) eval_nat_numeral(3) lessI)
             using \<Delta>2 p unfolding ss \<Delta>2_defs by clarify
          subgoal apply(intro exI[of _ 1], intro conjI)
          using \<Delta>2 unfolding ss \<Delta>2_defs apply clarify
            apply (metis one_less_numeral_iff semiring_norm(77))
          apply(intro exI[of _ 1], rule conjI)
          using \<Delta>2 unfolding ss \<Delta>2_defs apply clarify
           apply (metis one_less_numeral_iff semiring_norm(77))
          using \<Delta>2 p unfolding ss \<Delta>2_defs by clarify .
        subgoal apply(intro exI[of _ 0], intro conjI)
            using \<Delta>2 unfolding ss \<Delta>2_defs apply clarify
             apply (metis less_numeral_extra(1))
            apply(intro exI[of _ 0], rule conjI)
            using \<Delta>2 unfolding ss \<Delta>2_defs apply clarify
             apply (metis less_numeral_extra(1))
            using \<Delta>2 p unfolding ss \<Delta>2_defs by clarify . . . .


  show "match (oor3 \<Delta>2 \<Delta>2' \<Delta>1) w1 w2 ss3 ss4 statA ss1 ss2 statO"
  unfolding match_def proof(intro conjI)
    (* match1 and match2 are imposible case since isIntO always holds *)
    show "match1 (oor3 \<Delta>2 \<Delta>2' \<Delta>1) w1 w2 ss3 ss4 statA ss1 ss2 statO"
    unfolding match1_def by (simp add: finalS_def final_def)
    show "match2 (oor3 \<Delta>2 \<Delta>2' \<Delta>1) w1 w2 ss3 ss4 statA ss1 ss2 statO"
    unfolding match2_def by (simp add: finalS_def final_def)
    show "match12 (oor3 \<Delta>2 \<Delta>2' \<Delta>1) w1 w2 ss3 ss4 statA ss1 ss2 statO"
      apply(rule match12_simpleI, simp_all, rule disjI1)
      subgoal for ss3' ss4' apply(cases ss3', cases ss4')
        subgoal for pstate3' cfg3' cfgs3' ibT3' ibUT3' ls3' 
                    pstate4' cfg4' cfgs4' ibT4' ibUT4' ls4' 
        apply-apply(rule oor3_rule, assumption+, intro conjI impI) 
      (*pc12*)
      subgoal premises prem using prem(1)[unfolded ss prem(4)] 
      proof(cases rule: stepS_cases)
        case nonspec_normal
        then show ?thesis using stat \<Delta>2 unfolding ss by (auto simp add: \<Delta>2_defs)  
      next
        case nonspec_mispred
        then show ?thesis using stat \<Delta>2 unfolding ss by (auto simp add: \<Delta>2_defs) 
      next
        case spec_mispred
        then show ?thesis using stat \<Delta>2 prem(6) unfolding ss by (auto simp add: \<Delta>2_defs) 
      next
        case spec_Fence
        then show ?thesis using stat \<Delta>2 prem(6) unfolding ss by (auto simp add: \<Delta>2_defs) 
      next
        case spec_resolve
        then show ?thesis 
          using \<Delta>2 prem(6) unfolding ss apply (simp add: \<Delta>2_defs, clarsimp) 
          by (meson doubleton_eq_iff numeral_eq_iff semiring_norm(89) semiring_norm(90)) 
      next
        case spec_normal note sn3 = spec_normal
        show ?thesis using prem(2)[unfolded ss prem] proof(cases rule: stepS_cases)
          case nonspec_normal
          then show ?thesis using sn3 \<Delta>2 unfolding ss by (simp add: \<Delta>2_defs) 
        next
          case nonspec_mispred
          then show ?thesis using sn3 \<Delta>2 unfolding ss by (simp add: \<Delta>2_defs)
        next
          case spec_Fence
          then show ?thesis using sn3 \<Delta>2 unfolding ss by (simp add: \<Delta>2_defs, metis last_map) 
        next
          case spec_resolve
          then show ?thesis using sn3 \<Delta>2 unfolding ss by (simp add: \<Delta>2_defs, metis last_map) 
        next
          case spec_mispred
          then show ?thesis using sn3 \<Delta>2 unfolding ss by (simp add: \<Delta>2_defs, metis last_map) 
        next
          case spec_normal note sn4 = spec_normal
          have pc4:"pc4 = 12" using \<Delta>2 prem lcfgs unfolding ss \<Delta>2_defs by auto
          show ?thesis 
            using \<Delta>2 prem sn3 sn4 finals stat unfolding ss prem(4,5) lcfgs
            apply-apply(frule \<Delta>2_implies, unfold \<Delta>2_defs) apply clarsimp
            apply(rule oor3I1) apply(simp_all add: \<Delta>2_defs pc4) 
            using final_def config.sel(2) last_in_set 
                  lcfgs state.sel(1,2) vstore.sel xx 
            by (metis (mono_tags, lifting))
       qed
      qed

      (*pc3*)
     subgoal premises prem using prem(1)[unfolded ss prem(4)] 
     proof(cases rule: stepS_cases)
        case nonspec_normal
        then show ?thesis using stat \<Delta>2 prem unfolding ss by (auto simp add: \<Delta>2_defs)  
      next
        case nonspec_mispred
        then show ?thesis using stat \<Delta>2 unfolding ss by (auto simp add: \<Delta>2_defs) 
      next
        case spec_Fence
        then show ?thesis using stat \<Delta>2 prem(6) unfolding ss by (auto simp add: \<Delta>2_defs) 
      next
        case spec_normal 
        then show ?thesis using stat \<Delta>2 prem unfolding ss by (simp add: \<Delta>2_defs, metis cfgs_map) 
      next
        case spec_resolve
        then show ?thesis 
          using \<Delta>2 prem(6) resolve_73 
          unfolding ss \<Delta>2_defs using cfgs_map misSpecL1_def 
          by (clarify,smt (z3) insert_commute list.simps(15) resolve.simps)
      next
        case spec_mispred note sm3 = spec_mispred
        show ?thesis using prem(2)[unfolded ss prem] proof(cases rule: stepS_cases)
          case nonspec_normal
          then show ?thesis using sm3 \<Delta>2 unfolding ss by (simp add: \<Delta>2_defs) 
        next
          case nonspec_mispred
          then show ?thesis using sm3 \<Delta>2 unfolding ss by (simp add: \<Delta>2_defs)
        next
          case spec_resolve
          then show ?thesis using sm3 \<Delta>2 unfolding ss by (simp add: \<Delta>2_defs, metis last_map) 
        next
          case spec_Fence
          then show ?thesis using sm3 \<Delta>2 unfolding ss apply-apply(frule \<Delta>2_implies)
          by (simp add: \<Delta>2_defs)
        next
          case spec_normal 
          then show ?thesis using sm3 \<Delta>2 unfolding ss by (simp add: \<Delta>2_defs, metis last_map)
        next
          case spec_mispred note sm4 = spec_mispred
          have pc:"pc4 = 3" 
            using prem(6) lcfgs \<Delta>2 unfolding ss apply-apply(frule \<Delta>2_implies)
             by (simp add: \<Delta>2_defs ) 
          show ?thesis apply(rule oor3I2)
            unfolding ss \<Delta>2'_def using xx_0_cases[of vs3] apply(elim disjE)
            subgoal using \<Delta>2 lcfgs prem pc sm3 sm4 xx finals stat unfolding ss
              apply- apply(simp add: \<Delta>2_defs \<Delta>2'_defs, clarify) 
              apply(intro conjI)
              subgoal by (metis config.sel(2) last_in_set state.sel(1,2) vstore.sel final_def)
              subgoal by (metis config.sel(2) last_in_set state.sel(2))
              subgoal by (metis config.sel(2) last_in_set state.sel(2))
              subgoal by (metis config.sel(2) last_in_set state.sel(2))
              subgoal by (smt(verit) prem(1) prem(2) ss)
              subgoal by (metis config.sel(2) last_in_set state.sel(1) vstore.sel) .
            subgoal using \<Delta>2 lcfgs prem pc sm3 sm4 xx finals stat unfolding ss
              apply- apply(simp add: \<Delta>2_defs \<Delta>2'_defs, clarify) 
              apply(intro conjI)
              subgoal by (metis config.sel(2) last_in_set state.sel(1,2) vstore.sel final_def)
              subgoal by (metis config.sel(2) last_in_set state.sel(2))
              subgoal by (metis config.sel(2) last_in_set state.sel(2))
              subgoal by (metis config.sel(2) last_in_set state.sel(2))
              subgoal by (smt(verit) prem(1) prem(2) ss)
              subgoal by (metis config.sel(2) last_in_set state.sel(1) vstore.sel) . .
          qed
        qed
        (*\<not>mispred *)
     subgoal premises prem using prem(1)[unfolded ss prem(4)] 
     proof(cases rule: stepS_cases)
        case nonspec_normal
        then show ?thesis using stat \<Delta>2 prem unfolding ss by (auto simp add: \<Delta>2_defs)  
      next
        case nonspec_mispred
        then show ?thesis using stat \<Delta>2 unfolding ss by (auto simp add: \<Delta>2_defs) 
      next
        case spec_Fence
        then show ?thesis using stat \<Delta>2 prem(6) unfolding ss by (auto simp add: \<Delta>2_defs) 
      next
        case spec_mispred
        then show ?thesis using stat \<Delta>2 prem unfolding ss by (auto simp add: \<Delta>2_defs) 
      next
        case spec_resolve
        then show ?thesis 
          using \<Delta>2 prem(6) resolve_73 
          unfolding ss \<Delta>2_defs using cfgs_map misSpecL1_def 
          by (clarify,smt (z3) insert_commute list.simps(15) resolve.simps)
        next
        case spec_normal note sn3 = spec_normal
        show ?thesis using prem(2)[unfolded ss prem] proof(cases rule: stepS_cases)
          case nonspec_normal
          then show ?thesis using sn3 \<Delta>2 unfolding ss by (simp add: \<Delta>2_defs) 
        next
          case nonspec_mispred
          then show ?thesis using sn3 \<Delta>2 unfolding ss by (simp add: \<Delta>2_defs)
        next
          case spec_Fence
          then show ?thesis using sn3 \<Delta>2 unfolding ss by (simp add: \<Delta>2_defs, metis last_map) 
        next
          case spec_resolve
          then show ?thesis using sn3 \<Delta>2 unfolding ss by (simp add: \<Delta>2_defs, metis last_map) 
        next
          case spec_mispred
          then show ?thesis using sn3 \<Delta>2 unfolding ss by (simp add: \<Delta>2_defs, metis last_map) 
        next
          case spec_normal note sn4 = spec_normal
          show ?thesis 
            using \<Delta>2 lcfgs prem sn3 sn4 finals unfolding ss
            apply-apply(frule \<Delta>2_implies, unfold \<Delta>2_defs) apply clarsimp
            apply(rule oor3I1)
              using xx_0_cases[of vs3] apply(elim disjE)
                subgoal apply(simp_all add: \<Delta>2_defs, clarify) 
                using config.sel(2) last_in_set stat state.sel(1,2) vstore.sel 
                by (smt (verit, ccfv_SIG) Opt.final_def config.sel(1) eval_nat_numeral(3) f3 f4 is_Output_1 le_imp_less_Suc le_refl nat_less_le ss)
                subgoal  apply(simp_all add: \<Delta>2_defs, clarify) 
                using  config.sel(2) last_in_set stat state.sel(1,2) vstore.sel 
                apply(intro conjI,unfold config.sel(1)) 
                subgoal by simp
                subgoal by simp
                subgoal by (metis array_baseSimp)
                subgoal by (metis array_baseSimp)
                subgoal by (metis array_baseSimp)
                subgoal by (metis array_baseSimp)
                subgoal by (smt (verit) Opt.final_def ss)
                    apply (smt (verit) cfgs_Suc_zero lcfgs list.set_intros(1))
                   apply (smt (verit) cfgs_Suc_zero lcfgs list.set_intros(1))
                apply presburger
                apply (smt (verit) insertCI list.simps(15) resolve.elims(3) resolve_74 resolve_127)
                by linarith .
               qed
      qed 
      
     subgoal premises prem using prem(1)[unfolded ss prem(4)] 
     proof(cases rule: stepS_cases)
        case nonspec_normal
        then show ?thesis using stat \<Delta>2 prem unfolding ss by (auto simp add: \<Delta>2_defs)  
      next
        case nonspec_mispred
        then show ?thesis using stat \<Delta>2 unfolding ss by (auto simp add: \<Delta>2_defs) 
      next
        case spec_Fence
        then show ?thesis using stat \<Delta>2 prem unfolding ss by (auto simp add: \<Delta>2_defs) 
      next
        case spec_mispred
        then show ?thesis using stat \<Delta>2 prem unfolding ss by (auto simp add: \<Delta>2_defs) 
      next
        case spec_normal
        then show ?thesis using stat \<Delta>2 prem unfolding ss by (auto simp add: \<Delta>2_defs) 
      next
        case spec_resolve note sr3 = spec_resolve
        show ?thesis using prem(2)[unfolded ss prem(5)] proof(cases rule: stepS_cases)
          case nonspec_normal
          then show ?thesis using stat \<Delta>2 sr3 unfolding ss by (simp add: \<Delta>2_defs)
        next
          case nonspec_mispred
          then show ?thesis using stat \<Delta>2 sr3 unfolding ss by (simp add: \<Delta>2_defs)
        next
          case spec_normal
          then show ?thesis using stat \<Delta>2 sr3 unfolding ss by (simp add: \<Delta>2_defs, metis)
        next
          case spec_mispred
          then show ?thesis using stat \<Delta>2 sr3 unfolding ss by (simp add: \<Delta>2_defs, metis)
        next
          case spec_Fence 
          then show ?thesis using stat \<Delta>2 sr3 unfolding ss by (simp add: \<Delta>2_defs, metis)
        next
          case spec_resolve note sr4 = spec_resolve
          show ?thesis using stat \<Delta>2 prem sr3 sr4 
          unfolding ss lcfgs apply-
          apply(frule \<Delta>2_implies) apply (simp add: \<Delta>2_defs \<Delta>1_defs)
          apply(rule oor3I3, simp add: \<Delta>1_defs)
          by (metis prem(1) prem(2) ss)
      qed
    qed. . . 

  qed
qed


(* *)

lemma step3: "unwindIntoCond \<Delta>3 (oor \<Delta>3 \<Delta>1)" 
proof(rule unwindIntoCond_simpleI) 
  fix n w1 w2 ss3 ss4 statA ss1 ss2 statO
  assume r: "reachO ss3" "reachO ss4" "reachV ss1" "reachV ss2"
  and \<Delta>3: "\<Delta>3 n w1 w2 ss3 ss4 statA ss1 ss2 statO"

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
  using \<Delta>3 unfolding ss \<Delta>3_def
  apply clarsimp 
  by(frule common_implies, simp)

  have f2:"\<not>finalN ss2" 
  using \<Delta>3 unfolding ss \<Delta>3_def
  apply clarsimp 
  by(frule common_implies, simp)


  have f3:"\<not>finalS ss3" 
    using \<Delta>3 unfolding ss 
    apply-apply(frule \<Delta>3_implies)
    using finalS_if_spec by force

  have f4:"\<not>finalS ss4" 
    using \<Delta>3 unfolding ss 
    apply-apply(frule \<Delta>3_implies)
    using finalS_if_spec by force

  note finals = f1 f2 f3 f4
  show "finalS ss3 = finalS ss4 \<and> finalN ss1 = finalS ss3 \<and> finalN ss2 = finalS ss4"
    using finals by auto

  then show "isIntO ss3 = isIntO ss4" by simp

  then have lpc3:"pcOf (last cfgs3) = 7 \<or> 
                  pcOf (last cfgs3) = 8"
    using \<Delta>3 unfolding ss \<Delta>3_defs by simp

  (*because of a spliting on the cases, it's simpler to prove these prior*)
  have sec3[simp]:"\<not> isSecO ss3"
    using \<Delta>3 unfolding ss by (simp add: \<Delta>3_defs, metis list.size(3) n_not_Suc_n) 
  have sec4[simp]:"\<not> isSecO ss4"
    using \<Delta>3 unfolding ss 
    by (simp add: \<Delta>3_defs, metis list.size(3) map_is_Nil_conv nat.distinct(1))   

    have stat[simp]:"\<And>s3' s4' statA'. statA' = sstatA' statA ss3 ss4 \<Longrightarrow> 
               validTransO (ss3, s3') \<Longrightarrow> validTransO (ss4, s4') \<Longrightarrow>
               (statA = statA' \<or> statO = Diff)"
    subgoal for ss3' ss4'
      apply (cases ss3, cases ss4, cases ss1, cases ss2)
      apply (cases ss3', cases ss4', clarsimp)
      using \<Delta>3 finals unfolding ss apply clarsimp        
      apply(simp_all add: \<Delta>3_defs sstatA'_def) 
      apply(cases statO, simp_all) by (cases statA, simp_all add: updStat_EqI) .

    have "vs3 xx = vs4 xx" using \<Delta>3 lcfgs unfolding ss \<Delta>3_defs apply clarsimp
      by (metis cfgs_Suc_zero config.sel(2) list.set_intros(1) state.sel(1) vstore.sel)
    
    then have a1x:"(array_loc aa1 (nat (vs4 xx)) avst4) =
                 (array_loc aa1 (nat (vs3 xx)) avst3)"
      using \<Delta>3 lcfgs unfolding ss \<Delta>3_defs array_loc_def apply clarsimp
      by (metis Zero_not_Suc config.sel(2) last_in_set list.size(3) state.sel(2))

    have oor2_rule:"\<And>ss3' ss4'. ss3 \<rightarrow>S ss3' \<Longrightarrow> ss4 \<rightarrow>S ss4' \<Longrightarrow>
                    (pcOf (last cfgs3) = 7 \<longrightarrow> oor \<Delta>3 \<Delta>1 \<infinity> 2 2 ss3' ss4' (sstatA' statA ss3 ss4) ss1 ss2 statO) 
                  \<and> (pcOf (last cfgs3) = 8 \<longrightarrow> oor \<Delta>3 \<Delta>1 \<infinity> 1 1 ss3' ss4' (sstatA' statA ss3 ss4) ss1 ss2 statO)\<Longrightarrow>
                    \<exists>w1'<w1. \<exists>w2'<w2. oor \<Delta>3 \<Delta>1 \<infinity> w1' w2' ss3' ss4' (sstatA' statA ss3 ss4) ss1 ss2 statO"       
      subgoal for ss3' ss4' apply(cases ss3', cases ss4')
        subgoal for pstate3' cfg3' cfgs3' ib3' ls3' 
                    pstate4' cfg4' cfgs4' ib4' ls4' 
        using lpc3 apply(elim disjE)
      (*pc7*)
      subgoal apply(intro exI[of _ 2], intro conjI)
      subgoal using \<Delta>3 unfolding ss \<Delta>3_defs apply clarify
        by (metis enat_ord_simps(4) numeral_ne_infinity)
      apply(intro exI[of _ 2], rule conjI)
      subgoal using \<Delta>3 unfolding ss \<Delta>3_defs apply clarify
        by (metis enat_ord_simps(4) numeral_ne_infinity)
      by simp
      (*pc8*)
    subgoal apply(intro exI[of _ 1], intro conjI)
      subgoal using \<Delta>3 unfolding ss \<Delta>3_defs apply clarify
        by (metis one_less_numeral_iff semiring_norm(76))
      apply(intro exI[of _ 1], rule conjI)
      subgoal using \<Delta>3 unfolding ss \<Delta>3_defs apply clarify
        by (metis one_less_numeral_iff semiring_norm(76))
      by simp . . .

  show "match (oor \<Delta>3 \<Delta>1) w1 w2 ss3 ss4 statA ss1 ss2 statO"
  unfolding match_def proof(intro conjI)
    (* match1 and match2 are imposible case since isIntO always holds *)
    show "match1 (oor \<Delta>3 \<Delta>1) w1 w2 ss3 ss4 statA ss1 ss2 statO"
    unfolding match1_def by (simp add: finalS_def final_def)
    show "match2 (oor \<Delta>3 \<Delta>1) w1 w2 ss3 ss4 statA ss1 ss2 statO"
    unfolding match2_def by (simp add: finalS_def final_def)
  show "match12 (oor \<Delta>3 \<Delta>1) w1 w2 ss3 ss4 statA ss1 ss2 statO"
    apply(rule match12_simpleI, simp_all, rule disjI1)
    subgoal for ss3' ss4' apply(cases ss3', cases ss4')
        subgoal for pstate3' cfg3' cfgs3' ibT3' ibUT3' ls3' 
                    pstate4' cfg4' cfgs4' ibT4' ibUT4' ls4' 
        apply-apply(rule oor2_rule, assumption+, intro conjI impI)
      (*pc7*)
      subgoal premises prem using prem(1)[unfolded ss prem(4)] 
      proof(cases rule: stepS_cases)
        case nonspec_normal
        then show ?thesis using stat \<Delta>3 unfolding ss by (auto simp add: \<Delta>3_defs)  
      next
        case nonspec_mispred
        then show ?thesis using stat \<Delta>3 unfolding ss by (auto simp add: \<Delta>3_defs) 
      next
        case spec_mispred
        then show ?thesis using stat \<Delta>3 prem(6) unfolding ss by (auto simp add: \<Delta>3_defs) 
      next
        case spec_resolve
        then show ?thesis 
          using \<Delta>3 prem(6) resolve_127 
          unfolding ss \<Delta>3_defs by (clarify,metis cfgs_map misSpecL1_def)
      next
        case spec_Fence
        then show ?thesis using stat \<Delta>3 prem(6) unfolding ss by (auto simp add: \<Delta>3_defs) 
      next
        case spec_normal note sn3 = spec_normal
        show ?thesis
        using prem(2)[unfolded ss prem] proof(cases rule: stepS_cases)
          case nonspec_normal
          then show ?thesis using stat \<Delta>3 lcfgs sn3 unfolding ss by (simp add: \<Delta>3_defs)
        next
          case nonspec_mispred
          then show ?thesis using stat \<Delta>3 lcfgs sn3 unfolding ss by (simp add: \<Delta>3_defs)
        next
          case spec_mispred
          then show ?thesis using stat \<Delta>3 lcfgs sn3 unfolding ss by (simp add: \<Delta>3_defs, metis config.sel(1) last_map)  
        next
          case spec_Fence
          then show ?thesis using stat \<Delta>3 lcfgs sn3 unfolding ss 
          by (simp add: \<Delta>3_defs, metis config.sel(1) last_map) 
        next
          case spec_resolve
          then show ?thesis using stat \<Delta>3 lcfgs sn3 unfolding ss by (simp add: \<Delta>3_defs) 
        next (* the nontrivial case deferred to the end: *)
          case spec_normal note sn4 = spec_normal
          show ?thesis
          apply(intro oorI1)
          unfolding ss \<Delta>3_def prem(4,5) apply- apply(clarify,intro conjI)
            subgoal using stat \<Delta>3 lcfgs prem(1,2) sn3 sn4 unfolding ss hh
              apply- apply(frule \<Delta>3_implies) apply(simp add: \<Delta>3_defs) 
            using cases_14[of pc3] apply simp apply(elim disjE)
            apply simp_all by (metis config.sel(2) last_in_set state.sel(2) Dist_ignore a1x )+
            subgoal using stat \<Delta>3 lcfgs prem(1,2) sn3 sn4 unfolding ss prem(4,5) hh
            apply- apply(frule \<Delta>3_implies) apply(simp_all add: \<Delta>3_defs)  
            using cases_14[of pc3] apply simp apply(elim disjE)
            apply simp_all 
            by (metis config.collapse config.inject last_in_set state.sel(1) vstore.sel)+
            subgoal using stat \<Delta>3 lcfgs prem(1,2) sn3 sn4 unfolding ss prem(4,5) hh
            apply- apply(frule \<Delta>3_implies) by(simp add: \<Delta>3_defs) 
            subgoal using stat \<Delta>3 lcfgs prem(1,2) sn3 sn4 unfolding ss hh 
            apply- apply(frule \<Delta>3_implies) apply(simp add: \<Delta>3_defs) 
            using cases_14[of pc3] apply simp apply(elim disjE)
            by simp_all 
            subgoal using stat \<Delta>3 lcfgs sn3 sn4 unfolding ss hh 
            apply- apply(frule \<Delta>3_implies) apply(simp add: \<Delta>3_defs)  
            using cases_14[of pc3] apply (simp add: array_loc_def) apply(elim disjE)
            by (simp_all add: array_loc_def)
            subgoal using stat \<Delta>3 lcfgs sn3 sn4 unfolding ss hh 
            apply- apply(frule \<Delta>3_implies) apply(simp add: \<Delta>3_defs)  
            using cases_14[of pc3] apply (simp add: array_loc_def) apply(elim disjE)
            by (simp_all add: array_loc_def)
            subgoal using stat \<Delta>3 lcfgs sn3 sn4 unfolding ss hh 
            apply- apply(frule \<Delta>3_implies) by(simp add: \<Delta>3_defs) 
            subgoal using stat \<Delta>3 lcfgs sn3 sn4 prem(6) unfolding ss hh 
            apply- apply(frule \<Delta>3_implies) by(simp add: \<Delta>3_defs) .
          qed 
        qed
      subgoal premises prem using prem(1)[unfolded ss prem(4)] 
      proof(cases rule: stepS_cases)
        case nonspec_normal
        then show ?thesis using stat \<Delta>3 unfolding ss by (auto simp add: \<Delta>3_defs)  
      next
        case nonspec_mispred
        then show ?thesis using stat \<Delta>3 unfolding ss by (auto simp add: \<Delta>3_defs) 
      next
        case spec_mispred
        then show ?thesis using stat \<Delta>3 prem(6) unfolding ss by (auto simp add: \<Delta>3_defs) 
      next
        case spec_Fence
        then show ?thesis using stat \<Delta>3 prem(6) unfolding ss by (auto simp add: \<Delta>3_defs) 
      next
        case spec_normal
        then show ?thesis using stat \<Delta>3 prem(6) unfolding ss by (auto simp add: \<Delta>3_defs) 
      next
        case spec_resolve note sr3 = spec_resolve
        show ?thesis using prem(2)[unfolded ss prem] proof(cases rule: stepS_cases)
          case nonspec_normal
          then show ?thesis using stat \<Delta>3 lcfgs sr3 unfolding ss by (simp add: \<Delta>3_defs)
        next
          case nonspec_mispred
          then show ?thesis using stat \<Delta>3 lcfgs sr3 unfolding ss by (simp add: \<Delta>3_defs)
        next
          case spec_mispred
          then show ?thesis using stat \<Delta>3 lcfgs sr3 unfolding ss by (simp add: \<Delta>3_defs)  
        next
          case spec_Fence
          then show ?thesis using stat \<Delta>3 lcfgs sr3 unfolding ss by (simp add: \<Delta>3_defs) 
        next
          case spec_normal
          then show ?thesis using stat \<Delta>3 lcfgs sr3 unfolding ss by (simp add: \<Delta>3_defs) 
        next (* the nontrivial case deferred to the end: *)
          case spec_resolve note sr4 = spec_normal
          show ?thesis using stat \<Delta>3 prem sr3 sr4 
          unfolding ss lcfgs apply-
          apply(frule \<Delta>3_implies) apply (simp add: \<Delta>3_defs \<Delta>1_defs)
          apply(rule oorI2, simp add: \<Delta>1_defs local.spec_resolve)
          by (metis prem(1) ss3) 
      qed qed . . .
    qed
qed

(* *)

lemma step4: "unwindIntoCond \<Delta>1' \<Delta>1" 
proof(rule unwindIntoCond_simpleI) 
  fix n w1 w2 ss3 ss4 statA ss1 ss2 statO
  assume r: "reachO ss3" "reachO ss4" "reachV ss1" "reachV ss2"
  and \<Delta>1': "\<Delta>1' n w1 w2 ss3 ss4 statA ss1 ss2 statO"

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
  using \<Delta>1' unfolding ss \<Delta>1'_def
  apply clarsimp 
  by(frule common_implies, simp)

  have f2:"\<not>finalN ss2" 
  using \<Delta>1' unfolding ss \<Delta>1'_def
  apply clarsimp 
  by(frule common_implies, simp)


  have f3:"\<not>finalS ss3" 
    using \<Delta>1' unfolding ss 
    apply-apply(frule \<Delta>1'_implies)
    by (simp add: finalS_while_spec)

  have f4:"\<not>finalS ss4" 
    using \<Delta>1' unfolding ss 
    apply-apply(frule \<Delta>1'_implies)
    by (simp add: finalS_while_spec)

  note finals = f1 f2 f3 f4
  show "finalS ss3 = finalS ss4 \<and> finalN ss1 = finalS ss3 \<and> finalN ss2 = finalS ss4"
    using finals by auto

  then show "isIntO ss3 = isIntO ss4" by simp

  have match12_aux:"
 (\<And>s1' s2' statA'.
      statA' = sstatA' statA ss3 ss4 \<Longrightarrow>
      validTransO (ss3, s1') \<Longrightarrow>
      validTransO (ss4, s2') \<Longrightarrow>
      Opt.eqAct ss3 ss4 \<Longrightarrow>
      (\<not> isSecO ss3 \<and> \<not> isSecO ss4 \<and>
       (statA = statA' \<or> statO = Diff) \<and>
        \<Delta>1 \<infinity> 1 1 s1' s2' statA' ss1 ss2 statO))
    \<Longrightarrow> match12 \<Delta>1 w1 w2 ss3 ss4 statA ss1 ss2 statO"
    apply(rule match12_simpleI, rule disjI1)
    (*the fillibustering *)
    apply(rule exI[of _ 1], rule conjI) 
      subgoal using \<Delta>1'  unfolding ss \<Delta>1'_defs apply clarify
       by(metis enat_ord_simps(4) infinity_ne_i1)
    apply(rule exI[of _ 1], rule conjI)  
      subgoal using \<Delta>1'  unfolding ss \<Delta>1'_defs apply clarify
        by(metis enat_ord_simps(4) infinity_ne_i1)
     by auto 

  show "match \<Delta>1 w1 w2 ss3 ss4 statA ss1 ss2 statO"
  unfolding match_def proof(intro conjI)
    (* match1 and match2 are imposible case since isIntO always holds *)
    show "match1 \<Delta>1 w1 w2 ss3 ss4 statA ss1 ss2 statO"
    unfolding match1_def by (simp add: finalS_def final_def)
    show "match2 \<Delta>1 w1 w2 ss3 ss4 statA ss1 ss2 statO"
    unfolding match2_def by (simp add: finalS_def final_def)
    show "match12 \<Delta>1 w1 w2 ss3 ss4 statA ss1 ss2 statO"
    proof(rule match12_aux, intro conjI)
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
        using v sa \<Delta>1' unfolding ss 
        by (simp add: \<Delta>1'_defs,metis list.size(3) n_not_Suc_n) 

      show "\<not> isSecO ss4"
        using v sa \<Delta>1' unfolding ss 
        by (simp add: \<Delta>1'_defs,metis list.size(3) n_not_Suc_n) 

    show stat: "statA = statA' \<or> statO = Diff"

      using v sa \<Delta>1'
      apply (cases ss3, cases ss4, cases ss1, cases ss2)
      apply (cases ss3', cases ss4', clarsimp)
      using v sa \<Delta>1' unfolding ss statA' apply clarsimp        
      apply(simp_all add: \<Delta>1'_defs sstatA'_def) 
      apply(cases statO, simp_all) 
      apply(cases statA, simp_all add: updStat_EqI)
      unfolding finalS_def final_def 
      using One_nat_def less_numeral_extra(4) 
          less_one list.size(3) map_is_Nil_conv 
      by (smt (verit) status.exhaust updStat.simps)

      show "\<Delta>1 \<infinity> 1 1 ss3' ss4' statA' ss1 ss2 statO"
        using v3[unfolded ss, simplified] proof(cases rule: stepS_cases)
          case nonspec_normal
          then show ?thesis using sa \<Delta>1' stat unfolding ss by (simp add: \<Delta>1'_defs)
        next
          case nonspec_mispred
          then show ?thesis using sa \<Delta>1' stat unfolding ss by (simp add: \<Delta>1'_defs)
        next
          case spec_Fence
          then show ?thesis using sa \<Delta>1' unfolding ss 
            apply (simp add: \<Delta>1'_defs, clarify, elim disjE)
            by (simp_all add: \<Delta>1_defs \<Delta>1'_defs)
        next
          case spec_mispred
          then show ?thesis using sa \<Delta>1' unfolding ss 
            apply (simp add: \<Delta>1'_defs, clarify, elim disjE)
            by (simp_all add: \<Delta>1_defs \<Delta>1'_defs)
        next
          case spec_normal note sn3 = spec_normal
          show ?thesis using \<Delta>1' sn3(2) unfolding ss 
            apply (simp add: \<Delta>1'_defs, clarsimp)
            by (smt (z3) insert_commute)
        next
          case spec_resolve note sr3 = spec_resolve
          show ?thesis using v4[unfolded ss, simplified] proof(cases rule: stepS_cases)
            case nonspec_normal
            then show ?thesis using \<Delta>1' sr3 unfolding ss by (simp add: \<Delta>1'_defs)
          next
            case nonspec_mispred
            then show ?thesis using \<Delta>1' sr3 unfolding ss by (simp add: \<Delta>1'_defs)
          next
            case spec_mispred
            then show ?thesis using \<Delta>1' sr3 unfolding ss by (simp add: \<Delta>1'_defs, metis) 
          next
            case spec_normal
            then show ?thesis using \<Delta>1' sr3 unfolding ss by (simp add: \<Delta>1'_defs, metis)
          next 
            case spec_Fence  
            then show ?thesis using \<Delta>1' sr3 unfolding ss by (simp add: \<Delta>1'_defs, metis) 
          next 
            case spec_resolve note sr4 = spec_resolve
            show ?thesis
            using sa stat \<Delta>1'  v3 v4 sr3 sr4 unfolding ss hh
            apply(simp add: \<Delta>1'_defs \<Delta>1_defs)  
            by (metis atLeastAtMost_iff atLeastatMost_empty_iff empty_iff empty_set 
                      nat_le_linear numeral_le_iff semiring_norm(68,69,72)
                      length_1_butlast length_map in_set_butlastD)
          qed 
        qed
      qed
    qed
  qed
  

(* *)

lemma step5: "unwindIntoCond \<Delta>2' \<Delta>2" 
proof(rule unwindIntoCond_simpleI) 
  fix n w1 w2 ss3 ss4 statA ss1 ss2 statO
  assume r: "reachO ss3" "reachO ss4" "reachV ss1" "reachV ss2"
  and \<Delta>2': "\<Delta>2' n w1 w2 ss3 ss4 statA ss1 ss2 statO"

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
  using \<Delta>2' unfolding ss \<Delta>2'_def
  apply clarsimp 
  by(frule common_implies, simp)

  have f2:"\<not>finalN ss2" 
  using \<Delta>2' unfolding ss \<Delta>2'_def
  apply clarsimp 
  by(frule common_implies, simp)


  have f3:"\<not>finalS ss3" 
    using \<Delta>2' unfolding ss 
    apply-apply(frule \<Delta>2'_implies)
    using finalS_while_spec_L2 by force

  have f4:"\<not>finalS ss4" 
    using \<Delta>2' unfolding ss 
    apply-apply(frule \<Delta>2'_implies)
    using finalS_while_spec_L2 by force

  note finals = f1 f2 f3 f4
  show "finalS ss3 = finalS ss4 \<and> finalN ss1 = finalS ss3 \<and> finalN ss2 = finalS ss4"
    using finals by auto

  then show "isIntO ss3 = isIntO ss4" by simp

  (*because of a spliting on the cases, it's simpler to prove these prior*)
  have sec3[simp]:"\<not> isSecO ss3"
    using \<Delta>2' unfolding ss 
    by (simp add: \<Delta>2'_defs, metis list.size(3) zero_neq_numeral) 

  have sec4[simp]:"\<not> isSecO ss4"
    using \<Delta>2' unfolding ss 
    by (simp add: \<Delta>2'_defs, metis list.size(3) zero_neq_numeral)   

    have stat[simp]:"\<And>s3' s4' statA'. statA' = sstatA' statA ss3 ss4 \<Longrightarrow> 
               validTransO (ss3, s3') \<Longrightarrow> validTransO (ss4, s4') \<Longrightarrow>
               (statA = statA' \<or> statO = Diff)"
    subgoal for ss3' ss4'
      apply (cases ss3, cases ss4, cases ss1, cases ss2)
      apply (cases ss3', cases ss4', clarsimp)
      using \<Delta>2' finals unfolding ss apply clarsimp        
      apply(simp_all add: \<Delta>2'_defs sstatA'_def) 
      apply(cases statO, simp_all) by (cases statA, simp_all add: updStat_EqI) .


  have match12_aux:"
 (\<And>pstate3' cfg3' cfgs3' ib3' ibUT3' ls3' 
    pstate4' cfg4' cfgs4' ib4' ibUT4' ls4' statA'.
      (pstate3, cfg3, cfgs3, ibT3, ibUT3, ls3) \<rightarrow>S (pstate3', cfg3', cfgs3', ib3', ibUT3', ls3') \<Longrightarrow>
      (pstate4, cfg4, cfgs4, ibT4, ibUT4, ls4) \<rightarrow>S (pstate4', cfg4', cfgs4', ib4', ibUT4', ls4') \<Longrightarrow>
      Opt.eqAct ss3 ss4 \<Longrightarrow> statA' = sstatA' statA ss3 ss4 \<Longrightarrow>
      (\<Delta>2 \<infinity> 1 1 (pstate3', cfg3', cfgs3', ib3', ibUT3', ls3') (pstate4', cfg4', cfgs4', ib4', ibUT4', ls4') statA' ss1 ss2 statO))
    \<Longrightarrow> match12 \<Delta>2 w1 w2 ss3 ss4 statA ss1 ss2 statO"
    apply(rule match12_simpleI, simp_all, rule disjI1)
    (*the fillibustering *)
    apply(rule exI[of _ 1], rule conjI) 
      subgoal using \<Delta>2'  unfolding ss \<Delta>2'_defs apply clarify
        by (metis one_less_numeral_iff semiring_norm(76))
    apply(rule exI[of _ 1], rule conjI)  
      subgoal using \<Delta>2'  unfolding ss \<Delta>2'_defs apply clarify
        by (metis one_less_numeral_iff semiring_norm(76))
    subgoal for ss3' ss4' apply(cases ss3', cases ss4')
      subgoal for pstate3' cfg3' cfgs3' ib3' ibUT3' ls3' 
                  pstate4' cfg4' cfgs4' ib4' ibUT4' ls4' 
        using ss3 ss4 by blast . .

  show "match \<Delta>2 w1 w2 ss3 ss4 statA ss1 ss2 statO"
  unfolding match_def proof(intro conjI)
    (* match1 and match2 are imposible case since isIntO always holds *)
    show "match1 \<Delta>2 w1 w2 ss3 ss4 statA ss1 ss2 statO"
    unfolding match1_def by (simp add: finalS_def final_def)
    show "match2 \<Delta>2 w1 w2 ss3 ss4 statA ss1 ss2 statO"
    unfolding match2_def by (simp add: finalS_def final_def)
    show "match12 \<Delta>2 w1 w2 ss3 ss4 statA ss1 ss2 statO" 
    apply(rule match12_aux) 
    (* Choose the match12_12 case (since we have no mis-speculation yet) *)
    subgoal premises prem using prem(1)[unfolded ss ] 
      proof(cases rule: stepS_cases)
        case nonspec_normal
        then show ?thesis using stat \<Delta>2' unfolding ss by (auto simp add: \<Delta>2'_defs)  
      next
        case nonspec_mispred
        then show ?thesis using stat \<Delta>2' unfolding ss by (auto simp add: \<Delta>2'_defs) 
      next
        case spec_mispred
        then show ?thesis using stat \<Delta>2' prem unfolding ss by (auto simp add: \<Delta>2'_defs) 
      next
        case spec_normal
        then show ?thesis using stat \<Delta>2' prem unfolding ss by (auto simp add: \<Delta>2'_defs) 
      next
        case spec_Fence
        then show ?thesis using stat \<Delta>2' prem unfolding ss by (auto simp add: \<Delta>2'_defs) 
      next
        case spec_resolve note sr3 = spec_resolve
        show ?thesis using prem(2)[unfolded ss prem] proof(cases rule: stepS_cases)
            case nonspec_normal
            then show ?thesis using stat \<Delta>2' sr3 unfolding ss by (simp add: \<Delta>2'_defs)
          next
            case nonspec_mispred
            then show ?thesis using stat \<Delta>2' sr3 unfolding ss by (simp add: \<Delta>2'_defs)
          next
            case spec_mispred
            then show ?thesis using stat \<Delta>2' sr3 unfolding ss by (simp add: \<Delta>2'_defs) 
          next
            case spec_normal
            then show ?thesis using stat \<Delta>2' sr3 unfolding ss by (simp add: \<Delta>2'_defs)
          next 
            case spec_Fence  
            then show ?thesis using stat \<Delta>2' sr3 unfolding ss by (simp add: \<Delta>2'_defs) 
          next 
            case spec_resolve note sr4 = spec_resolve
            show ?thesis
            using stat \<Delta>2' prem sr3 sr4 unfolding ss 
            apply(simp add: \<Delta>2'_defs \<Delta>2_defs)  
            apply(intro conjI)
            apply (metis last_map map_butlast map_is_Nil_conv)
            apply (metis image_subset_iff in_set_butlastD)
            apply(metis) apply(metis) apply (metis in_set_butlastD) 
            apply (metis in_set_butlastD) apply (metis in_set_butlastD)
            apply (metis in_set_butlastD) apply (metis in_set_butlastD) 
            apply (metis in_set_butlastD) apply (metis prem(1) prem(2) ss3 ss4)
            apply (metis in_set_butlastD) apply (metis in_set_butlastD)
            apply (smt (verit, ccfv_SIG) butlast.simps(2) last_ConsL last_map 
                   length_0_conv length_map map_L2 map_butlast not_Cons_self2)
            apply clarify apply(elim disjE) 
               apply (metis map_L2 butlast.simps(2) last.simps last_map list.simps(8) 
                          map_butlast not_Cons_self2 numeral_eq_iff semiring_norm(88)) 
                             
              by (metis map_L2 butlast.simps(2) last.simps last_map list.simps(8)
                  map_butlast image_constant_conv not_Cons_self2 image_subset_iff 
                  list.set_intros(1,2) list.simps(15) resolve.simps resolve_127 
                  set_empty2 subset_insertI resolve_73 numeral_eq_iff )+
        qed
      qed .  
  qed
qed

(**)

lemma stepe: "unwindIntoCond \<Delta>e \<Delta>e" 
proof(rule unwindIntoCond_simpleI) 
  fix n w1 w2 ss3 ss4 statA ss1 ss2 statO
  assume r: "reachO ss3" "reachO ss4" "reachV ss1" "reachV ss2"
  and \<Delta>e: "\<Delta>e n w1 w2 ss3 ss4 statA ss1 ss2 statO"

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
    using \<Delta>e Opt.final_def finalS_def stepS_endPC endPC_def finalB_endPC
    unfolding \<Delta>e_defs ss by clarsimp

  then show "isIntO ss3 = isIntO ss4" by simp

  show "match \<Delta>e w1 w2 ss3 ss4 statA ss1 ss2 statO"
  unfolding match_def proof(intro conjI)
    (* match1 and match2 are imposible case since isIntO always holds *)
    show "match1 \<Delta>e w1 w2 ss3 ss4 statA ss1 ss2 statO"
    unfolding match1_def by (simp add: finalS_def final_def)
    show "match2 \<Delta>e w1 w2 ss3 ss4 statA ss1 ss2 statO"
    unfolding match2_def by (simp add: finalS_def final_def)
    show "match12 \<Delta>e w1 w2 ss3 ss4 statA ss1 ss2 statO"
      apply(rule match12_simpleI) using \<Delta>e unfolding ss 
      by (simp add: \<Delta>e_defs stepS_endPC)
  qed
qed
 
(* *)

lemmas theConds = step0 step1 step2 step3 step4 step5 stepe

proposition lrsecure
proof-
  define m where m: "m \<equiv> (7::nat)"
  define \<Delta>s where \<Delta>s: "\<Delta>s \<equiv> \<lambda>i::nat. 
  if i = 0 then \<Delta>0
  else if i = 1 then \<Delta>1 
  else if i = 2 then \<Delta>2
  else if i = 3 then \<Delta>3 
  else if i = 4 then \<Delta>1'
  else if i = 5 then \<Delta>2'
  else \<Delta>e" 
  define nxt where nxt: "nxt \<equiv> \<lambda>i::nat. 
  if i = 0 then {0,1::nat}
  else if i = 1 then {1,4,2,3,6}  
  else if i = 2 then {2,5,1} 
  else if i = 3 then {3,1}  
  else if i = 4 then {1}
  else if i = 5 then {2} 
  else {6}"
  show ?thesis apply(rule distrib_unwind_lrsecure[of m nxt \<Delta>s])
    subgoal unfolding m by auto
    subgoal unfolding nxt m by auto
    subgoal using init unfolding \<Delta>s by auto
    subgoal 
      unfolding m nxt \<Delta>s apply (simp split: if_splits)
      using theConds
      unfolding oor_def oor3_def oor4_def oor5_def by auto . 
qed


end