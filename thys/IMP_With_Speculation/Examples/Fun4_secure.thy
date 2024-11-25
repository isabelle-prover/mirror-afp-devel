subsection "Proof"
theory Fun4_secure
  imports Fun4
begin 

(* THE PROOF OF SECURITY *)

definition "PC \<equiv> {0..6}"

(*For the counterparts, we chose i=0 to ensure going down the then branch*)
definition "same_xx_cp cfg1 cfg2 \<equiv> 
  vstore (getVstore (stateOf cfg1)) xx = vstore (getVstore (stateOf cfg2)) xx
\<and> vstore (getVstore (stateOf cfg1)) xx = 0"

definition "common_memory cfg cfg' cfgs' \<equiv> 
 array_base aa1 (getAvstore (stateOf cfg)) = array_base aa1 (getAvstore (stateOf cfg')) \<and> 
 (\<forall>cfg''\<in>set cfgs'. array_base aa1 (getAvstore (stateOf cfg'')) = array_base aa1 (getAvstore (stateOf cfg))) \<and> 
 array_base aa2 (getAvstore (stateOf cfg)) = array_base aa2 (getAvstore (stateOf cfg')) \<and> 
 (\<forall>cfg''\<in>set cfgs'. array_base aa2 (getAvstore (stateOf cfg'')) = array_base aa2 (getAvstore (stateOf cfg))) \<and>
 (getHheap (stateOf cfg)) = (getHheap (stateOf cfg')) \<and>
 (\<forall>cfg''\<in>set cfgs'. getHheap (stateOf cfg) = (getHheap (stateOf cfg''))) \<and>
 (getAvstore (stateOf cfg)) = (getAvstore (stateOf cfg'))"


(* we read "before" as "before or at" *)
definition "beforeInput = {0,1}"
definition "afterInput = {2..6}"
definition "elseBranch = 6"
definition "startOfThenBranch = 4"
definition "inThenBranch = {4..6}"

definition "afterInputNotInElse = {2,3,4,5,6,8}"
definition "inThenBranchBeforeOutput = {3,4,5}"
definition "atCond = 3"
definition "atThenOutput = 5" 
definition "atJump = 6"

(* Common to all the unwinding relations in this proof: *)
definition common_strat1 :: "stateO \<Rightarrow> stateO  \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" 
where 
"common_strat1 = 
(\<lambda> (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
   statO.
(pstate3 = pstate4 \<and> 
 cfg1 = cfg3 \<and> cfg2 = cfg4 \<and> 
 pcOf cfg3 = pcOf cfg4 \<and> map pcOf cfgs3 = map pcOf cfgs4 \<and> 
 pcOf cfg3 \<in> PC \<and> pcOf ` (set cfgs3) \<subseteq> PC \<and>

 \<^cancel>\<open>tr1 and tr3 have common memory \<close>
 common_memory cfg1 cfg3 cfgs3 \<and>

 \<^cancel>\<open>likewise tr2 and tr4   \<close>
 common_memory cfg2 cfg4 cfgs4 \<and>

 (\<forall>n\<ge>0. array_loc aa1 0 (getAvstore (stateOf cfg2)) \<noteq> array_loc aa2 n (getAvstore (stateOf cfg2)) \<and>
 array_loc aa1 0 (getAvstore (stateOf cfg1)) \<noteq> array_loc aa2 n (getAvstore (stateOf cfg1))) \<and>
 \<^cancel>\<open>   \<close>
 array_base aa1 (getAvstore (stateOf cfg3)) = array_base aa1 (getAvstore (stateOf cfg4)) \<and> 
 (\<forall>cfg3'\<in>set cfgs3. array_base aa1 (getAvstore (stateOf cfg3')) = array_base aa1 (getAvstore (stateOf cfg3))) \<and> 
 (\<forall>cfg4'\<in>set cfgs4. array_base aa1 (getAvstore (stateOf cfg4')) = array_base aa1 (getAvstore (stateOf cfg4))) \<and> 
 array_base aa2 (getAvstore (stateOf cfg3)) = array_base aa2 (getAvstore (stateOf cfg4)) \<and> 
 (\<forall>cfg3'\<in>set cfgs3. array_base aa2 (getAvstore (stateOf cfg3')) = array_base aa2 (getAvstore (stateOf cfg3))) \<and> 
 (\<forall>cfg4'\<in>set cfgs4. array_base aa2 (getAvstore (stateOf cfg4')) = array_base aa2 (getAvstore (stateOf cfg4))) \<and> 
 \<^cancel>\<open>   \<close>
 (statA = Diff \<longrightarrow> statO = Diff)))"

lemmas common_strat1_defs = common_strat1_def common_memory_def

(* Common to all the unwinding relations in this proof: *)
definition common :: "enat \<Rightarrow> stateO \<Rightarrow> stateO \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" 
  where 
"common = (\<lambda>(num::enat)
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
   statO.
(pstate3 = pstate4 \<and> 

 (num = (endPC - pcOf cfg1) \<or> num = \<infinity>) \<and>

 \<^cancel>\<open>tr1 and tr2 stay on the same path \<close>
 pcOf cfg1 = pcOf cfg2 \<and> 

 \<^cancel>\<open>likewise tr3 and tr4   \<close>
 pcOf cfg3 = pcOf cfg4 \<and>
 map pcOf cfgs3 = map pcOf cfgs4 \<and> 
 pcOf cfg3 \<in> PC \<and> pcOf ` (set cfgs3) \<subseteq> PC \<and> 
 pcOf cfg1 \<in> PC \<and>

 \<^cancel>\<open>tr1 and tr3 have common memory \<close>
 common_memory cfg1 cfg3 cfgs3 \<and>

 \<^cancel>\<open>likewise tr2 and tr4   \<close>
 common_memory cfg2 cfg4 cfgs4 \<and>

 (\<forall>n\<ge>0. array_loc aa1 0 (getAvstore (stateOf cfg2)) \<noteq> array_loc aa2 n (getAvstore (stateOf cfg2)) \<and>
 array_loc aa1 0 (getAvstore (stateOf cfg1)) \<noteq> array_loc aa2 n (getAvstore (stateOf cfg1))) \<and>
 \<^cancel>\<open>All traces have same base addresses
 AtoJ: Maybe this is also worth being extracted as a predicate. \<close>
 array_base aa1 (getAvstore (stateOf cfg3)) = array_base aa1 (getAvstore (stateOf cfg4)) \<and> 
 (\<forall>cfg3'\<in>set cfgs3. array_base aa1 (getAvstore (stateOf cfg3')) = array_base aa1 (getAvstore (stateOf cfg3))) \<and> 
 (\<forall>cfg4'\<in>set cfgs4. array_base aa1 (getAvstore (stateOf cfg4')) = array_base aa1 (getAvstore (stateOf cfg4))) \<and> 
 array_base aa2 (getAvstore (stateOf cfg3)) = array_base aa2 (getAvstore (stateOf cfg4)) \<and> 
 (\<forall>cfg3'\<in>set cfgs3. array_base aa2 (getAvstore (stateOf cfg3')) = array_base aa2 (getAvstore (stateOf cfg3))) \<and> 
 (\<forall>cfg4'\<in>set cfgs4. array_base aa2 (getAvstore (stateOf cfg4')) = array_base aa2 (getAvstore (stateOf cfg4))) \<and>
 (statA = Diff \<longrightarrow> statO = Diff)
))"


lemmas common_defs = common_def common_memory_def 

lemma common_implies: "common num 
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
   statO \<Longrightarrow> 
 pcOf cfg1 < 9 \<and> pcOf cfg3 < 9 \<and>

 (n\<ge>0 \<longrightarrow> array_loc aa1 0 (getAvstore (stateOf cfg2)) \<noteq> array_loc aa2 n (getAvstore (stateOf cfg2)) \<and>
 array_loc aa1 0 (getAvstore (stateOf cfg1)) \<noteq> array_loc aa2 n (getAvstore (stateOf cfg1)))"
  unfolding common_defs PC_def  
  by force


(* Before input is inserted *)
definition \<Delta>0 :: "enat \<Rightarrow> stateO \<Rightarrow> stateO \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" where 
"\<Delta>0 = (\<lambda>num (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
     statO.
 (common num (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2)  
     statO  \<and> 
 
 \<^cancel>\<open>head of the buffers are equal counterpartwise \<close>
  (llength ibUT1 = \<infinity> \<and> llength ibUT2 = \<infinity> \<and> 
   llength ibUT3 = \<infinity> \<and> llength ibUT4 = \<infinity>) \<and> 
 (lhd ibUT3 \<ge> NN \<and> (lhd ibUT1 = 0) \<and> ibUT1 = ibUT2 
 \<or>lhd ibUT3 < NN \<and> ibUT1 = ibUT3 \<and> ibUT2 = ibUT4) \<and> 
  pcOf cfg3 \<in> beforeInput \<and>

 \<^cancel>\<open>since memory is equal, cfg1=cfg3 and cfg2=cfg4 in 'loading' state\<close>
  cfg1 = cfg3 \<and> cfg2 = cfg4 \<and>
  ls1 = ls3 \<and> ls2 = ls4 \<and> 
  ls1 ={} \<and> ls2={} \<and>
  noMisSpec cfgs3
))"
lemmas \<Delta>0_defs' = \<Delta>0_def common_defs PC_def beforeInput_def noMisSpec_def

lemma \<Delta>0_def2: 
"\<Delta>0 num (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
     statO 
 = 
 (common num (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2)  
     statO  \<and> 
 
 \<^cancel>\<open>head of the buffers are equal counterpartwise \<close>
  (llength ibUT1 = \<infinity> \<and> llength ibUT2 = \<infinity> \<and> 
   llength ibUT3 = \<infinity> \<and> llength ibUT4 = \<infinity>) \<and> 
   (ibUT1 \<noteq> [[]] \<and> ibUT2 \<noteq> [[]] \<and> ibUT3 \<noteq> [[]] \<and> ibUT4 \<noteq> [[]]) \<and> 
 (lhd ibUT3 \<ge> NN \<and> (lhd ibUT1 = 0) \<and> ibUT1 = ibUT2 
 \<or>lhd ibUT3 < NN \<and> ibUT1 = ibUT3 \<and> ibUT2 = ibUT4) \<and> 
  pcOf cfg3 \<in> beforeInput \<and>

 \<^cancel>\<open>since memory is equal, cfg1=cfg3 and cfg2=cfg4 in 'loading' state\<close>
  cfg1 = cfg3 \<and> cfg2 = cfg4 \<and>
  ls1 = ls3 \<and> ls2 = ls4 \<and> 
  ls1 ={} \<and> ls2={} \<and>
  noMisSpec cfgs3
 )"
  unfolding \<Delta>0_defs' apply(clarsimp, standard)
  subgoal by (smt (verit) infinity_ne_i0 llength_LNil)
  subgoal by (smt (verit)) . 

lemmas \<Delta>0_defs = \<Delta>0_def2 common_defs PC_def beforeInput_def noMisSpec_def

lemma \<Delta>0_implies: "\<Delta>0 num (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
   statO \<Longrightarrow> 
   (pcOf cfg3 = 1 \<longrightarrow> ibUT3 \<noteq> LNil) \<and>
   (pcOf cfg4 = 1 \<longrightarrow> ibUT4 \<noteq> LNil) \<and>
   pcOf cfg1 < 7 \<and> pcOf cfg2 = pcOf cfg1 \<and> 
   cfgs3 = [] \<and> pcOf cfg3 < 7 \<and>
   cfgs4 = [] \<and> pcOf cfg4 < 7"
  unfolding \<Delta>0_defs 
  apply(intro conjI)
  apply (simp_all) 
  by (metis Nil_is_map_conv)


(* After input is inserted, no mis-speculation *)
definition \<Delta>1 :: "enat \<Rightarrow> stateO \<Rightarrow> stateO \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" where 
"\<Delta>1 = (\<lambda>num 
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
     statO.
 (common_strat1 (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
     statO \<and> 
  pcOf cfg3 \<in> afterInput \<and> 
  same_var_o xx cfg3 cfgs3 cfg4 cfgs4 \<and>
  vstore (getVstore (stateOf cfg3)) xx < NN \<and>

  ls1 = ls3 \<and> ls2 = ls4 \<and> 
  noMisSpec cfgs3 
))"

lemmas \<Delta>1_defs = \<Delta>1_def common_strat1_defs PC_def afterInput_def same_var_o_def noMisSpec_def

lemma \<Delta>1_implies: "\<Delta>1 num
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2)
   statO \<Longrightarrow> 
   pcOf cfg1 < 7 \<and>
   cfgs3 = [] \<and> pcOf cfg3 \<noteq> 1 \<and> pcOf cfg3 < 7 \<and>
   cfgs4 = [] \<and> pcOf cfg4 \<noteq> 1 \<and> pcOf cfg4 < 7"
  unfolding \<Delta>1_defs 
  apply(intro conjI) apply simp_all
  by (metis map_is_Nil_conv)

(* Left mis-speculation: *)
definition \<Delta>2 :: "enat \<Rightarrow> stateO \<Rightarrow> stateO  \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" where 
"\<Delta>2 = (\<lambda>num
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2)  
     statO.
 (common_strat1  
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2)  
     statO \<and> 
  pcOf cfg3 = startOfThenBranch \<and> 
  pcOf cfg1 = pcOf cfg3 \<and>

  pcOf (last cfgs3) = elseBranch \<and> 
  same_var_o xx cfg3 cfgs3 cfg4 cfgs4 \<and>
  vstore (getVstore (stateOf cfg3)) xx < NN \<and>
  ls1 = ls3 \<and> ls2 = ls4 \<and>
  misSpecL1 cfgs3
))"

lemmas \<Delta>2_defs = \<Delta>2_def common_strat1_defs  PC_def same_var_def startOfThenBranch_def  
      misSpecL1_def elseBranch_def

lemma \<Delta>2_implies: "\<Delta>2 num    
   (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
   (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
   statA 
   (cfg1,ibT1,ibUT1,ls1) 
   (cfg2,ibT2,ibUT2,ls2) 
   statO \<Longrightarrow> 
   pcOf (last cfgs3) = 6 \<and> pcOf cfg3 = 4 \<and> 
   pcOf (last cfgs4) = pcOf (last cfgs3) \<and>
   pcOf cfg3 = pcOf cfg4 \<and>
   length cfgs3 = Suc 0 \<and>
   length cfgs3 = length cfgs4"
  apply(intro conjI)
  unfolding \<Delta>2_defs apply simp_all
  apply (metis last_map map_is_Nil_conv)
  by (metis length_map)

(**********************************************)
(**********************************************)
(* After input is inserted and xx \<ge> NN in tr3 *)

definition \<Delta>1' :: "enat \<Rightarrow> stateO \<Rightarrow> stateO \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" where 
  "\<Delta>1' = (\<lambda>num (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2)  
     statO.
 (common num (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2)  
     statO \<and>
 \<^cancel>\<open>   \<close>
  pcOf cfg3 \<in> afterInput \<and> 
  same_var_o xx cfg3 cfgs3 cfg4 cfgs4 \<and>
  
  (pcOf cfg1 > 2 \<longrightarrow> vstore (getVstore (stateOf cfg3)) tt = vstore (getVstore (stateOf cfg4)) tt) \<and>

  vstore (getVstore (stateOf cfg3)) xx \<ge> NN \<and>

  (pcOf cfg1 < 4 \<longrightarrow> pcOf cfg1 = pcOf cfg3 \<and> 
                     ls1 = {} \<and> ls2 = {} \<and> 
                     ls1 = ls3 \<and> ls2 = ls4) \<and> 
  (pcOf cfg1 \<le> 5 \<longrightarrow> ls1 \<subseteq> {array_loc aa1 0 (getAvstore (stateOf cfg1))}
                 \<and> ls1 = ls2 \<and> ls3 = ls4) \<and>

  (Language_Prelims.dist ls3 ls4 \<subseteq> Language_Prelims.dist ls1 ls2) \<and>

  (pcOf cfg1 \<ge> 4 \<longrightarrow> pcOf cfg1 \<in> inThenBranch \<and> pcOf cfg3 = elseBranch) \<and>
  same_xx_cp cfg1 cfg2 \<and>
  vstore (getVstore (stateOf cfg1)) xx = 0 \<and>
  
  ls3 \<subseteq> ls1 \<and> ls4 \<subseteq> ls2 \<and> 
  noMisSpec cfgs3
))"
lemmas \<Delta>1'_defs = \<Delta>1'_def common_defs PC_def afterInput_def 
  same_var_o_def same_xx_cp_def noMisSpec_def inThenBranch_def elseBranch_def
lemma \<Delta>1'_implies: "\<Delta>1' num (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
   statO \<Longrightarrow> 
   pcOf cfg1 < 7 \<and> pcOf cfg1 \<noteq> Suc 0 \<and> 
   pcOf cfg2 = pcOf cfg1 \<and> 
   cfgs3 = [] \<and> pcOf cfg3 < 7 \<and>
   cfgs4 = [] \<and> pcOf cfg4 < 7"
  unfolding \<Delta>1'_defs 
  apply(intro conjI)
  apply simp_all 
  using Suc_lessI startOfThenBranch_def verit_eq_simplify(10) zero_neq_numeral apply linarith
  by (metis list.map_disc_iff)


definition \<Delta>3' :: "enat \<Rightarrow> stateO \<Rightarrow> stateO \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" where 
  "\<Delta>3' = (\<lambda> num (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
     statO.
 (common num (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
     statO \<and> 
 \<^cancel>\<open>   \<close>
  pcOf cfg3 = elseBranch \<and> cfgs3 \<noteq> [] \<and> 
  pcOf (last cfgs3) \<in> inThenBranch \<and> 
  pcOf (last cfgs4) = pcOf(last cfgs3) \<and>
 \<^cancel>\<open>we sync the cp traces with the speculation cfgs3/cfgs4\<close>
  pcOf cfg1 = pcOf(last cfgs3) \<and> 
 
  same_var_o xx cfg3 cfgs3 cfg4 cfgs4 \<and>
  (getAvstore (stateOf cfg3)) = (getAvstore (stateOf (last cfgs3))) \<and>
  (getAvstore (stateOf cfg4)) = (getAvstore (stateOf (last cfgs4))) \<and>


  same_xx_cp cfg1 cfg2 \<and>
  ls1 = ls3 \<and> ls2 = ls4 \<and>

  vstore (getVstore (stateOf cfg3)) tt = vstore (getVstore (stateOf cfg4)) tt \<and>

  vstore (getVstore (stateOf cfg3)) xx \<ge> NN \<and>

(pcOf cfg1 = 4 \<longrightarrow> ls1 = {} \<and> ls2 = {}) \<and>
(pcOf cfg1 \<le> 5 \<longrightarrow> ls1 \<subseteq> {array_loc aa1 0 (getAvstore (stateOf cfg1))}
                 \<and> ls2 \<subseteq> {array_loc aa1 0 (getAvstore (stateOf cfg2))}
                 \<and> ls3 = ls4) \<and>

(pcOf cfg1 > 4 \<longrightarrow>same_var vv cfg1 (last cfgs3) \<and> same_var vv cfg2 (last cfgs4)) \<and>
  misSpecL1 cfgs3
))"
lemmas \<Delta>3'_defs = \<Delta>3'_def common_defs PC_def elseBranch_def
  inThenBranch_def startOfThenBranch_def  
  same_var_o_def same_xx_cp_def misSpecL1_def same_var_def

lemma \<Delta>3'_implies: "\<Delta>3' num (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2)  
   statO \<Longrightarrow> 
  pcOf cfg1 < 7 \<and> pcOf cfg1 \<noteq> Suc 0 \<and> 
  pcOf cfg2 = pcOf cfg1 \<and> 
  pcOf cfg3 < 7 \<and> pcOf cfg4 < 7 \<and>
  (pcOf (last cfgs3) = 4 \<or> pcOf (last cfgs3) = 5 \<or> pcOf (last cfgs3) = 6) \<and> pcOf cfg3 = 6"
  unfolding \<Delta>3'_defs 
  apply(intro conjI)
  apply simp_all 
  by (metis cases_thenBranch le_neq_implies_less less_SucI not_less_eq)
(************************************************)

(* End: *)
definition \<Delta>e :: "enat \<Rightarrow> stateO \<Rightarrow> stateO \<Rightarrow> status \<Rightarrow> stateV \<Rightarrow> stateV \<Rightarrow> status \<Rightarrow> bool" where 
  "\<Delta>e = (\<lambda>(num::enat) (pstate3,cfg3,cfgs3,ibT3,ibUT3,ls3) 
     (pstate4,cfg4,cfgs4,ibT4,ibUT4,ls4)  
     statA 
     (cfg1,ibT1,ibUT1,ls1) 
     (cfg2,ibT2,ibUT2,ls2) 
     statO.
  ((num = (endPC - pcOf cfg1) \<or> num = \<infinity>) \<and>
    pcOf cfg3 = endPC \<and> pcOf cfg4 = endPC \<and> cfgs3 = [] \<and> cfgs4 = [] \<and>
    pcOf cfg1 = endPC \<and> pcOf cfg2 = endPC))"

lemmas \<Delta>e_defs = \<Delta>e_def common_def endPC 

(* *)

context array_nempty
begin 
lemma init: "initCond \<Delta>0"
  unfolding initCond_def apply(intro allI) 
  subgoal for s3 s4 apply(cases s3, cases s4) 
  subgoal for pstate3 cfg3 cfgs3 ibT3 ibUT3 ls3 pstate4 cfg4 cfgs4 ibT4 ibUT4 ls4 apply safe
  apply clarsimp
    apply (cases "lhd ibUT3 < NN")
    subgoal  
      apply(cases "getAvstore (stateOf cfg3)", cases "getAvstore (stateOf cfg4)")
      unfolding \<Delta>0_defs  
      unfolding array_base_def array_loc_def
      using aa1 by auto 
    subgoal  
      apply(cases "getAvstore (stateOf cfg3)", cases "getAvstore (stateOf cfg4)")
      unfolding \<Delta>0_defs'  
      unfolding array_base_def array_loc_def 
      using aa1 apply (simp split: avstore.splits)  
      apply(rule exI[of _ "cfg3"]) using ex_llength_infty by auto
      . . .
(* *)

(*Playing the first strategy*)
lemma step0: "unwindIntoCond \<Delta>0 (oor3 \<Delta>0 \<Delta>1 \<Delta>1')"
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

  show "react (oor3 \<Delta>0 \<Delta>1 \<Delta>1') ss3 ss4 statA ss1 ss2 statO"
    unfolding react_def proof(intro conjI)
    (* match1 and match2 are imposibT,ibUTle case since isIntO always holds *)
    show "match1 (oor3 \<Delta>0 \<Delta>1 \<Delta>1') ss3 ss4 statA ss1 ss2 statO"
      unfolding match1_def by (simp add: finalS_def final_def) 
    show "match2 (oor3 \<Delta>0 \<Delta>1 \<Delta>1') ss3 ss4 statA ss1 ss2 statO"
      unfolding match2_def by (simp add: finalS_def final_def) 
    show "match12 (oor3 \<Delta>0 \<Delta>1 \<Delta>1') ss3 ss4 statA ss1 ss2 statO"
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
        using v \<Delta>0 unfolding ss by (simp add: \<Delta>0_defs) 

      show "eqSec ss2 ss4"
        using v \<Delta>0 unfolding ss 
        apply (simp add: \<Delta>0_defs) by (metis length_0_conv length_map) 

      show saO:"Van.eqAct ss1 ss2"
      using v sa \<Delta>0 unfolding ss   
      unfolding Opt.eqAct_def Van.eqAct_def
      apply(simp_all add: \<Delta>0_defs)   
      by (metis enat.distinct(2) f3 list.map_disc_iff llength_LNil ss3 zero_enat_def)

      show "match12_12 (oor3 \<Delta>0 \<Delta>1 \<Delta>1') ss3' ss4' statA' ss1 ss2 statO"
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
         using cases_6[of pc3] apply(elim disjE)
         apply simp_all apply(cases statO, simp_all) apply(cases statA, simp_all)
         apply(cases statO, simp_all) apply (cases statA, simp_all)
          apply (smt (z3) status.distinct newStat.simps)
         using newStat.simps by (smt (z3) status.exhaust)
        } note stat = this

        show "oor3 \<Delta>0 \<Delta>1 \<Delta>1' \<infinity> ss3' ss4' statA' (nextN ss1) (nextN ss2) (sstatO' statO ss1 ss2)"
          (* the combination of nonspec_normal and nonspec_normal is the only nontrivial possibT,ibUTility, 
           deferred to the end *)
          using v3[unfolded ss, simplified] proof(cases rule: stepS_cases)
          case nonspec_mispred
          then show ?thesis using sa \<Delta>0 stat unfolding ss apply- apply(frule \<Delta>0_implies) 
            by (simp add: \<Delta>0_defs) 
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
            show ?thesis using sa saO \<Delta>0 stat v3 v4 nn3 nn4 f4
              unfolding ss cfg Opt.eqAct_def apply clarsimp
              apply(cases "pc3 = 0")
              subgoal apply(rule oor3I1)
                apply (simp add: \<Delta>0_defs) by (metis config.sel(2) state.sel(2))
              subgoal apply(subgoal_tac "pc4 = 1")
                 defer subgoal by (simp add: \<Delta>0_defs)
                subgoal using xx_NN_cases[of "vstore (getVstore (stateOf cfg3'))"] apply(elim disjE)
                  subgoal apply(rule oor3I2) 
                    by (simp add: \<Delta>0_defs \<Delta>1_defs, metis) 
                  subgoal apply(rule oor3I3) 
                    apply (simp add: \<Delta>0_defs \<Delta>1'_defs)
                    apply(intro conjI, metis+)
                    apply blast by fastforce+ 
                    . . .
          qed
        qed
      qed
    qed  
  qed
qed
(**)
lemma step1: "unwindIntoCond \<Delta>1 (oor3 \<Delta>1 \<Delta>2 \<Delta>e)" 
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
    by simp

  have f2:"\<not>finalN ss2" 
    using \<Delta>1 finalB_pc_iff' unfolding ss cfg finalN_iff_finalB \<Delta>1_defs
    by simp


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

  show "react (oor3 \<Delta>1 \<Delta>2 \<Delta>e) ss3 ss4 statA ss1 ss2 statO"
  unfolding react_def proof(intro conjI)
    (* match1 and match2 are imposible, case since isIntO always holds *)
    show "match1 (oor3 \<Delta>1 \<Delta>2 \<Delta>e) ss3 ss4 statA ss1 ss2 statO"
    unfolding match1_def by (simp add: finalS_def final_def)
    show "match2 (oor3 \<Delta>1 \<Delta>2 \<Delta>e) ss3 ss4 statA ss1 ss2 statO"
    unfolding match2_def by (simp add: finalS_def final_def)
    show "match12 (oor3 \<Delta>1 \<Delta>2 \<Delta>e) ss3 ss4 statA ss1 ss2 statO"
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
      by (simp add: \<Delta>1_defs eqSec_def) 
      
      show "Van.eqAct ss1 ss2"
      using v sa \<Delta>1 unfolding ss Van.eqAct_def
      by (simp_all add: \<Delta>1_defs)  

      show "match12_12 (oor3 \<Delta>1 \<Delta>2 \<Delta>e) ss3' ss4' statA' ss1 ss2 statO"
      unfolding match12_12_def
      proof(rule exI[of _ "nextN ss1"], rule exI[of _ "nextN ss2"],unfold Let_def, intro conjI impI)
        show "validTransV (ss1, nextN ss1)" 
          by (simp add: f1 nextN_stepN)

        show "validTransV (ss2, nextN ss2)" 
          by (simp add: f2 nextN_stepN)


        {assume sstat: "statA' = Diff"
         show "sstatO' statO ss1 ss2 = Diff"
         using v sa \<Delta>1 sstat unfolding ss cfg statA'
         apply(simp add: \<Delta>1_defs sstatO'_def sstatA'_def) 
         using cases_6[of pc3] apply(elim disjE)
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
           by simp_all          
        } note stat = this

        show "(oor3 \<Delta>1 \<Delta>2 \<Delta>e) \<infinity> ss3' ss4' statA' (nextN ss1) (nextN ss2) (sstatO' statO ss1 ss2)"
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
              using cases_6[of pc3] apply(elim disjE, simp_all add: \<Delta>1_defs)
              by(rule oor3I2, simp add: \<Delta>1_defs \<Delta>2_defs, metis)
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
            using cases_6[of pc3] apply(elim disjE)
              subgoal by (simp add: \<Delta>1_defs)
              subgoal by (simp add: \<Delta>1_defs)   
              subgoal apply(rule oor3I1) by(simp add:\<Delta>1_defs, metis) 
              subgoal apply(rule oor3I1) by (simp add: \<Delta>1_defs, metis)
              subgoal apply(rule oor3I1) by (simp add: \<Delta>1_defs, metis)
              subgoal apply(rule oor3I1) by (simp add: \<Delta>1_defs, metis)
              apply(rule oor3I3) by (simp_all add: \<Delta>1_defs \<Delta>e_defs) 
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
    by simp 

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
    proof(rule match12_simpleI,rule disjI1, intro conjI)
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
      apply(cases ss3', cases ss4', clarsimp)
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
          by(frule \<Delta>2_implies, simp add: \<Delta>2_defs \<Delta>1_defs, metis) 
        qed 
      qed 
    qed
  qed  
qed 

(*Playing the first strategy*)
lemma xx_le_NN[simp]:"cfg = Config pc (State (Vstore vs) avst h p) \<Longrightarrow> vs xx = 0 \<Longrightarrow> vs xx < int NN" 
  using NN by auto

(*auxillary lemma to help delint*)
lemma match12I:"match12 (oor3 \<Delta>1' \<Delta>3' \<Delta>e) ss3 ss4 statA ss1 ss2 statO \<Longrightarrow>
    (\<exists>v<n. proact (oor3 \<Delta>1' \<Delta>3' \<Delta>e) v ss3 ss4 statA ss1 ss2 statO) \<or>
    react (oor3 \<Delta>1' \<Delta>3' \<Delta>e) ss3 ss4 statA ss1 ss2 statO"
apply(rule disjI2) unfolding react_def match1_def match2_def 
by(simp_all add: finalS_def final_def) 

(*Playing the first strategy*)
lemma step1': "unwindIntoCond \<Delta>1' (oor3 \<Delta>1' \<Delta>3' \<Delta>e)" 
proof(rule unwindIntoCond_simpleIB) 
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
  note cfg = cfg3 cfg4

  obtain hh1 where h1: "h1 = Heap hh1" by(cases h1, auto)
  obtain hh2 where h2: "h2 = Heap hh2" by(cases h2, auto)
  obtain hh3 where h3: "h3 = Heap hh3" by(cases h3, auto)
  obtain hh4 where h4: "h4 = Heap hh4" by(cases h4, auto)
  note hh = h3 h4

  have f1:"\<not>finalN ss1" 
    using \<Delta>1' 
    unfolding ss apply-apply(frule \<Delta>1'_implies)
    unfolding finalN_iff_finalB \<Delta>1'_defs
    using finalB_pcOf_iff by simp

  have f2:"\<not>finalN ss2" 
    using \<Delta>1' 
    unfolding ss apply-apply(frule \<Delta>1'_implies)
    unfolding finalN_iff_finalB \<Delta>1'_defs
    using finalB_pcOf_iff by simp


  have f3:"\<not>finalS ss3" 
    using \<Delta>1' unfolding ss apply-apply(frule \<Delta>1'_implies)
    using finalS_cond by (simp add: \<Delta>1'_defs)

  have f4:"\<not>finalS ss4" 
    using \<Delta>1' unfolding ss apply-apply(frule \<Delta>1'_implies)
    using finalS_cond by (simp add: \<Delta>1'_defs)

  note finals = f1 f2 f3 f4

  show "finalS ss3 = finalS ss4 \<and> finalN ss1 = finalS ss3 \<and> finalN ss2 = finalS ss4"
    using finals by auto

  then show "isIntO ss3 = isIntO ss4" by simp


  show "(\<exists>v<n. proact (oor3 \<Delta>1' \<Delta>3' \<Delta>e) v ss3 ss4 statA ss1 ss2 statO) \<or> 
        react (oor3 \<Delta>1' \<Delta>3' \<Delta>e) ss3 ss4 statA ss1 ss2 statO"
    using cases_6[of "pcOf cfg1"] apply(elim disjE)
    subgoal using \<Delta>1' unfolding ss by (simp add: \<Delta>1'_defs, linarith) 
    subgoal using \<Delta>1' unfolding ss by (simp add: \<Delta>1'_defs, linarith) 
    subgoal proof(rule match12I, rule match12_simpleI, rule disjI2, intro conjI)
      fix ss3' ss4' statA'
      assume statA': "statA' = sstatA' statA ss3 ss4"
        and v: "validTransO (ss3, ss3')" "validTransO (ss4, ss4')" 
        and sa: "Opt.eqAct ss3 ss4" and pc:"pcOf cfg1 = 2"
      note v3 = v(1) note v4 = v(2)

      obtain pstate3' cfg3' cfgs3' ibT3' ibUT3' ls3' where ss3': "ss3' = (pstate3', cfg3', cfgs3', ibT3', ibUT3', ls3')"
      by (cases ss3', auto) 
      obtain pstate4' cfg4' cfgs4' ibT4' ibUT4' ls4' where ss4': "ss4' = (pstate4', cfg4', cfgs4', ibT4', ibUT4', ls4')"
      by (cases ss4', auto)
      note ss = ss ss3' ss4'

      show "eqSec ss1 ss3"
        using v sa \<Delta>1' unfolding ss apply (simp add: \<Delta>1'_defs) 
        by (metis not_gr_zero not_numeral_le_zero zero_less_numeral)

      show "eqSec ss2 ss4"
        using v sa \<Delta>1' unfolding ss apply (simp add: \<Delta>1'_defs)
        by (metis not_gr_zero not_numeral_le_zero zero_neq_numeral)

      show "Van.eqAct ss1 ss2"
        using v sa \<Delta>1' unfolding ss Van.eqAct_def
        apply (simp_all add: \<Delta>1'_defs) 
        by (metis \<Delta>1' \<Delta>1'_implies ss)

      show "match12_12 (oor3 \<Delta>1' \<Delta>3' \<Delta>e) ss3' ss4' statA' ss1 ss2 statO"
      unfolding match12_12_def
      proof(rule exI[of _ "nextN ss1"], rule exI[of _ "nextN ss2"],unfold Let_def, intro conjI impI)
        show "validTransV (ss1, nextN ss1)" 
          by (simp add: f1 nextN_stepN)

        show "validTransV (ss2, nextN ss2)" 
          by (simp add: f2 nextN_stepN)

        have cfgs4:"cfgs4 = []" using \<Delta>1' unfolding ss \<Delta>1'_defs by (clarify, metis list.map_disc_iff)

        have notJump:"\<not>is_IfJump (prog ! pcOf cfg3)" using \<Delta>1' pc unfolding ss \<Delta>1'_defs 
          by(simp add: \<Delta>1'_defs sstatO'_def sstatA'_def) 


        {assume sstat: "statA' = Diff"
         show "sstatO' statO ss1 ss2 = Diff"
         using v sa \<Delta>1' sstat pc unfolding ss cfg statA'
         apply(simp add: \<Delta>1'_defs sstatO'_def sstatA'_def) 
         apply(cases statO, simp_all) apply(cases statA, simp_all) 
             using cfg finals ss by simp
         } note stat = this

         have pc4:"pc4 = 2" 
           using v sa \<Delta>1' pc unfolding ss cfg
           by (simp_all add: \<Delta>1'_defs) 


        show "(oor3 \<Delta>1' \<Delta>3' \<Delta>e) \<infinity> ss3' ss4' statA' (nextN ss1) (nextN ss2) (sstatO' statO ss1 ss2)"
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
          then show ?thesis using notJump by auto
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
            case nonspec_normal note nn4 = nonspec_normal
            show ?thesis apply(rule oor3I1)
              using sa \<Delta>1' stat pc pc4 v3 v4 nn3 config.sel(2) state.sel(2)
              unfolding ss cfg cfg1 cfg2 hh apply(simp add:\<Delta>1'_defs)
              using numeral_le_iff semiring_norm(69,72) by force
          qed
        qed
      qed
    qed
    subgoal proof(rule match12I, rule match12_simpleI, rule disjI2, intro conjI)
      fix ss3' ss4' statA'
      assume statA': "statA' = sstatA' statA ss3 ss4"
        and v: "validTransO (ss3, ss3')" "validTransO (ss4, ss4')" 
        and sa: "Opt.eqAct ss3 ss4" and pc:"pcOf cfg1 = 3"
      note v3 = v(1) note v4 = v(2)

      obtain pstate3' cfg3' cfgs3' ibT3' ibUT3' ls3' where ss3': "ss3' = (pstate3', cfg3', cfgs3', ibT3', ibUT3', ls3')"
      by (cases ss3', auto) 
      obtain pstate4' cfg4' cfgs4' ibT4' ibUT4' ls4' where ss4': "ss4' = (pstate4', cfg4', cfgs4', ibT4', ibUT4', ls4')"
      by (cases ss4', auto)
      note ss = ss ss3' ss4'

      show "eqSec ss1 ss3"
        using v sa \<Delta>1' unfolding ss apply (simp add: \<Delta>1'_defs) 
        by (metis not_gr_zero not_numeral_le_zero zero_less_numeral)

      show "eqSec ss2 ss4"
        using v sa \<Delta>1' unfolding ss apply (simp add: \<Delta>1'_defs)
        by (metis not_gr_zero not_numeral_le_zero zero_neq_numeral)

      show "Van.eqAct ss1 ss2"
        using v sa \<Delta>1' unfolding ss Van.eqAct_def
        apply (simp_all add: \<Delta>1'_defs) 
        by (metis \<Delta>1' \<Delta>1'_implies ss)

      show "match12_12 (oor3 \<Delta>1' \<Delta>3' \<Delta>e) ss3' ss4' statA' ss1 ss2 statO"
      unfolding match12_12_def
      proof(rule exI[of _ "nextN ss1"], rule exI[of _ "nextN ss2"],unfold Let_def, intro conjI impI)
        show "validTransV (ss1, nextN ss1)" 
          by (simp add: f1 nextN_stepN)

        show "validTransV (ss2, nextN ss2)" 
          by (simp add: f2 nextN_stepN)

        have cfgs4:"cfgs4 = []" using \<Delta>1' unfolding ss \<Delta>1'_defs by (clarify,metis map_is_Nil_conv)

        {assume sstat: "statA' = Diff"
         show "sstatO' statO ss1 ss2 = Diff"
         using v sa \<Delta>1' sstat pc unfolding ss cfg statA'
         apply(simp add: \<Delta>1'_defs sstatO'_def sstatA'_def) 
         apply(cases statO, simp_all) apply(cases statA, simp_all) 
             using cfg finals ss by simp
         } note stat = this

         have pc4:"pc4 = 3" 
           using v sa \<Delta>1' pc unfolding ss cfg
           by (simp_all add: \<Delta>1'_defs) 


        show "(oor3 \<Delta>1' \<Delta>3' \<Delta>e) \<infinity> ss3' ss4' statA' (nextN ss1) (nextN ss2) (sstatO' statO ss1 ss2)"
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
          case nonspec_mispred note nm3 = nonspec_mispred
          show ?thesis using v4[unfolded ss, simplified] proof(cases rule: stepS_cases)
            (* trace 4 can only have the same case as trace 3 as nontrivial case, here nonspec_normal -- deferred *)
            case spec_normal
            then show ?thesis using sa \<Delta>1' stat nm3 unfolding ss by (simp add: \<Delta>1'_defs cfgs4) 
          next
            case spec_mispred
            then show ?thesis using sa \<Delta>1' stat nm3 unfolding ss by (simp add: \<Delta>1'_defs cfgs4) 
          next
            case spec_Fence
            then show ?thesis using sa \<Delta>1' stat nm3 unfolding ss by (simp add: \<Delta>1'_defs cfgs4) 
          next
            case spec_resolve
            then show ?thesis using sa \<Delta>1' stat nm3 unfolding ss by (simp add: \<Delta>1'_defs cfgs4) 
          next
            case nonspec_normal
            then show ?thesis using sa \<Delta>1' stat nm3 unfolding ss by (simp add: \<Delta>1'_defs cfgs4) 
          next
            case nonspec_mispred note nm4 = nonspec_mispred
            show ?thesis apply(rule oor3I2)
              using sa pc4 \<Delta>1' stat pc v3 v4 nm3 nm4 config.sel(2) state.sel(2)
              unfolding ss cfg cfg1 cfg2 hh apply(simp add:\<Delta>1'_defs \<Delta>3'_defs)
              by (metis empty_subsetI nat_less_le nat_neq_iff numeral_eq_iff semiring_norm(89) set_eq_subset) 
          qed
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
            case nonspec_normal note nn4 = nonspec_normal
            show ?thesis apply(rule oor3I1)
              using sa pc4 \<Delta>1' stat pc v3 v4 nn3 config.sel(2) state.sel(2)
              unfolding ss cfg cfg1 cfg2 hh apply(simp add:\<Delta>1'_defs)
              by (metis nat_le_linear nat_less_le numeral_eq_iff semiring_norm(88)) 
          qed
        qed
      qed
    qed
    subgoal apply(rule disjI1, rule exI[of _ 2], rule conjI) 
      subgoal using \<Delta>1' unfolding ss \<Delta>1'_defs  apply clarify
        apply(erule disjE)
        subgoal premises p using p(1,47) unfolding endPC by simp
        subgoal using enat_ord_simps(4) numeral_ne_infinity by presburger .
      unfolding proact_def proof(intro disjI2, intro conjI)
      assume pc:"pcOf cfg1 = 4"   
      (* \<not> isSecV is trivial *)
      show "\<not> isSecV ss1" using \<Delta>1' pc unfolding \<Delta>1'_defs ss cfg by auto

      show "\<not> isSecV ss2" using \<Delta>1' pc unfolding \<Delta>1'_defs ss cfg by auto

      show "Van.eqAct ss1 ss2" using \<Delta>1' pc unfolding \<Delta>1'_defs ss cfg Van.eqAct_def by auto

      show "move_12 (oor3 \<Delta>1' \<Delta>3' \<Delta>e) 2 ss3 ss4 statA ss1 ss2 statO"
        unfolding move_12_def Let_def
      proof (rule exI[of _ "nextN ss1"], rule exI[of _ "nextN ss2"],intro conjI)
        show "validTransV (ss1, nextN ss1)" 
          using \<Delta>1' pc unfolding validTransV_iff_nextN ss \<Delta>1'_defs
          by simp 

        show "validTransV (ss2, nextN ss2)" 
          using \<Delta>1' pc unfolding validTransV_iff_nextN ss \<Delta>1'_defs
          by simp 
        have a1_0:"array_loc aa1 0 avst3 = array_loc aa1 0 avst4" 
          using \<Delta>1' pc unfolding cfg cfg1 ss \<Delta>1'_defs array_loc_def by simp
        have pc1:"pc1 = 4" using \<Delta>1' pc unfolding cfg cfg1 ss \<Delta>1'_defs by simp

        show "oor3 \<Delta>1' \<Delta>3' \<Delta>e 2 ss3 ss4 statA (nextN ss1) (nextN ss2) (sstatO' statO ss1 ss2)" 
          apply(rule oor3I1)
          using \<Delta>1' pc unfolding ss cfg cfg1 cfg2 hh h1 h2 endPC apply(simp add: \<Delta>1'_defs)
          apply-apply(intro conjI)
          subgoal by (metis numeral_eq_enat)
          subgoal by (metis Nil_is_map_conv)
          subgoal by metis
          subgoal by metis
          subgoal unfolding sstatO'_def by simp
          subgoal using a1_0 by force
          subgoal unfolding a1_0 dist_def pc1 array_loc_def by simp 
          subgoal by blast
          subgoal by (simp add: subset_insertI2)
          subgoal by (simp add: subset_insertI2) .
         qed
      qed
      subgoal apply(rule disjI1, rule exI[of _ 1], rule conjI) 
      subgoal using \<Delta>1' unfolding ss \<Delta>1'_defs apply clarify
        apply(erule disjE)
        subgoal premises p using p(1,47) unfolding endPC by (simp add: one_enat_def)
        subgoal by (metis enat_ord_code(4) one_enat_def) .
      unfolding proact_def proof(intro disjI2, intro conjI)
      assume pc:"pcOf cfg1 = 5"   
      (* \<not> isSecV is trivial *)
      show "\<not> isSecV ss1" using \<Delta>1' pc unfolding \<Delta>1'_defs ss cfg by auto

      show "\<not> isSecV ss2" using \<Delta>1' pc unfolding \<Delta>1'_defs ss cfg by auto

      show "Van.eqAct ss1 ss2" using \<Delta>1' pc unfolding \<Delta>1'_defs ss cfg Van.eqAct_def by auto

      show "move_12 (oor3 \<Delta>1' \<Delta>3' \<Delta>e) 1 ss3 ss4 statA ss1 ss2 statO"
        unfolding move_12_def Let_def
      proof (rule exI[of _ "nextN ss1"], rule exI[of _ "nextN ss2"],intro conjI)
        show "validTransV (ss1, nextN ss1)" 
          using \<Delta>1' pc unfolding validTransV_iff_nextN ss \<Delta>1'_defs
          by simp 

        show "validTransV (ss2, nextN ss2)" 
          using \<Delta>1' pc unfolding validTransV_iff_nextN ss \<Delta>1'_defs
          by simp 

        show "oor3 \<Delta>1' \<Delta>3' \<Delta>e 1 ss3 ss4 statA (nextN ss1) (nextN ss2) (sstatO' statO ss1 ss2)" 
          apply(rule oor3I1)
          using \<Delta>1' pc unfolding ss cfg cfg1 cfg2 hh h1 h2 endPC apply(simp add: \<Delta>1'_defs)
          apply-apply(intro conjI)
          subgoal by (metis One_nat_def one_enat_def)
          subgoal by (metis Nil_is_map_conv)
          subgoal by metis
          subgoal by metis
          subgoal unfolding sstatO'_def by simp
          subgoal by (metis Suc_n_not_le_n eval_nat_numeral(3) nat_le_linear)
          subgoal by (metis atThenOutput_def insert_compr less_or_eq_imp_le mult.commute nat_numeral pc subset_insertI2)
          subgoal by (simp add: subset_insertI2) .
        qed
      qed
    subgoal proof(rule match12I, rule match12_simpleI, rule disjI2, intro conjI)
      fix ss3' ss4' statA'
      assume statA': "statA' = sstatA' statA ss3 ss4"
        and v: "validTransO (ss3, ss3')" "validTransO (ss4, ss4')" 
        and sa: "Opt.eqAct ss3 ss4" and pc:"pcOf cfg1 = 6"
      note v3 = v(1) note v4 = v(2)

      obtain pstate3' cfg3' cfgs3' ibT3' ibUT3' ls3' where ss3': "ss3' = (pstate3', cfg3', cfgs3', ibT3', ibUT3', ls3')"
      by (cases ss3', auto) 
      obtain pstate4' cfg4' cfgs4' ibT4' ibUT4' ls4' where ss4': "ss4' = (pstate4', cfg4', cfgs4', ibT4', ibUT4', ls4')"
      by (cases ss4', auto)
      note ss = ss ss3' ss4'

      show "eqSec ss1 ss3"
        using v sa \<Delta>1' unfolding ss apply (simp add: \<Delta>1'_defs) 
        by (metis not_gr_zero not_numeral_le_zero zero_less_numeral)

      show "eqSec ss2 ss4"
        using v sa \<Delta>1' unfolding ss apply (simp add: \<Delta>1'_defs)
        by (metis not_gr_zero not_numeral_le_zero zero_neq_numeral)

      show "Van.eqAct ss1 ss2"
        using v sa \<Delta>1' unfolding ss Van.eqAct_def
        apply (simp_all add: \<Delta>1'_defs) 
        by (metis \<Delta>1' \<Delta>1'_implies ss)

      show "match12_12 (oor3 \<Delta>1' \<Delta>3' \<Delta>e) ss3' ss4' statA' ss1 ss2 statO"
      unfolding match12_12_def
      proof(rule exI[of _ "nextN ss1"], rule exI[of _ "nextN ss2"],unfold Let_def, intro conjI impI)
        show "validTransV (ss1, nextN ss1)" 
          by (simp add: f1 nextN_stepN)

        show "validTransV (ss2, nextN ss2)" 
          by (simp add: f2 nextN_stepN)

        have cfgs4:"cfgs4 = []" using \<Delta>1' unfolding ss \<Delta>1'_defs by (clarify,metis map_is_Nil_conv)

        {assume sstat: "statA' = Diff"
         show "sstatO' statO ss1 ss2 = Diff"
         using v sa \<Delta>1' sstat pc unfolding ss cfg statA'
         apply(simp add: \<Delta>1'_defs sstatO'_def sstatA'_def) 
         apply(cases statO, simp_all) apply(cases statA, simp_all) 
         using cfg finals ss apply (simp split: if_splits)
         unfolding dist_def by blast
         } note stat = this

         have pc4:"pc4 = 6" 
           using v sa \<Delta>1' pc unfolding ss cfg
           by (simp_all add: \<Delta>1'_defs) 

         have notJump:"\<not>is_IfJump (prog ! pcOf cfg3)" using \<Delta>1' pc unfolding ss \<Delta>1'_defs 
          by(simp add: \<Delta>1'_defs sstatO'_def sstatA'_def) 


        show "(oor3 \<Delta>1' \<Delta>3' \<Delta>e) \<infinity> ss3' ss4' statA' (nextN ss1) (nextN ss2) (sstatO' statO ss1 ss2)"
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
          then show ?thesis using notJump by auto
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
            case nonspec_normal note nn4 = nonspec_normal
            show ?thesis apply(rule oor3I3)
              using sa \<Delta>1' stat pc pc4 v3 v4 nn3 config.sel(2) state.sel(2)
              unfolding ss cfg cfg1 cfg2 hh by(simp add:\<Delta>1'_defs \<Delta>e_defs)
          qed
        qed
      qed
    qed
    using \<Delta>1' unfolding ss by(simp add:\<Delta>1'_defs)
qed

lemma step3': "unwindIntoCond \<Delta>3' (oor \<Delta>3' \<Delta>1')" 
proof(rule unwindIntoCond_simpleI) 
  fix n ss3 ss4 statA ss1 ss2 statO
  assume r: "reachO ss3" "reachO ss4" "reachV ss1" "reachV ss2"
    and \<Delta>3': "\<Delta>3' n ss3 ss4 statA ss1 ss2 statO"

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
    by (cases "cfg1") (metis state.collapse vstore.collapse)
  obtain pc2 vs2 avst2 h2 p2 where 
    cfg2: "cfg2 = Config pc2 (State (Vstore vs2) avst2 h2 p2)"
    by (cases "cfg2") (metis state.collapse vstore.collapse)
  obtain pc3 vs3 avst3 h3 p3 where 
    cfg3: "cfg3 = Config pc3 (State (Vstore vs3) avst3 h3 p3)"
    by (cases "cfg3") (metis state.collapse vstore.collapse)
  obtain pc4 vs4 avst4 h4 p4 where 
    cfg4: "cfg4 = Config pc4 (State (Vstore vs4) avst4 h4 p4)"
    by (cases "cfg4") (metis state.collapse vstore.collapse)
  note cfg = cfg1 cfg2 cfg3 cfg4

  obtain lpc3 lvs3 lavst3 lh3 lp3 where 
    lcfgs3: "last cfgs3 = Config lpc3 (State (Vstore lvs3) lavst3 lh3 lp3)"
    by (cases "last cfgs3") (metis state.collapse vstore.collapse)
  obtain lpc4 lvs4 lavst4 lh4 lp4 where 
    lcfgs4: "last cfgs4 = Config lpc4 (State (Vstore lvs4) lavst4 lh4 lp4)"
    by (cases "last cfgs4") (metis state.collapse vstore.collapse)
  note lcfgs = lcfgs3 lcfgs4

  obtain hh1 where h1: "h1 = Heap hh1" by(cases h1, auto)
  obtain hh2 where h2: "h2 = Heap hh2" by(cases h2, auto)

  obtain hh3 where h3: "h3 = Heap hh3" by(cases h3, auto)
  obtain hh4 where h4: "h4 = Heap hh4" by(cases h4, auto)
  obtain lhh3 where lh3: "lh3 = Heap lhh3" by(cases lh3, auto)
  obtain lhh4 where lh4: "lh4 = Heap lhh4" by(cases lh4, auto)
  note hh = h3 h4 lh3 lh4 h1 h2


  define a1_3 where a1_3:"a1_3 = array_loc aa1 0 avst3"
  define a1_4 where a1_4:"a1_4 = array_loc aa1 0 avst4"
  define a2_3 where a2_3:"a2_3 = array_loc aa2 (nat (lvs3 vv * 512)) avst3"
  define a2_4 where a2_4:"a2_4 = array_loc aa2 (nat (lvs4 vv * 512)) avst4"


  have butlast:"butlast cfgs4 = []" 
        using \<Delta>3' unfolding ss apply (simp add: \<Delta>3'_defs) 
        by (metis length_1_butlast length_map)

      have h3_eq:"hh3 = lhh3" 
        using cfg lcfgs hh \<Delta>3' unfolding \<Delta>3'_defs ss apply clarify
        using config.sel(2) getHheap.simps heap.sel last_in_set 
        by metis 

      have h4_eq:"hh4 = lhh4" 
        using cfg lcfgs hh \<Delta>3' unfolding \<Delta>3'_defs ss apply clarify
        using config.sel(2) getHheap.simps heap.sel last_in_set 
        by (metis map_is_Nil_conv)

  have f1:"\<not>finalN ss1" 
    using \<Delta>3' finalB_pc_iff' unfolding ss finalN_iff_finalB \<Delta>3'_defs
    by simp 

  have f2:"\<not>finalN ss2" 
    using \<Delta>3' finalB_pc_iff' unfolding ss cfg finalN_iff_finalB \<Delta>3'_defs
    by simp 

  have f3:"\<not>finalS ss3" 
    using \<Delta>3' unfolding ss apply-apply(frule \<Delta>3'_implies)
    using finalS_cond_spec by (simp add: \<Delta>3'_defs)

  have f4:"\<not>finalS ss4" 
    using \<Delta>3' unfolding ss apply-apply(frule \<Delta>3'_implies)
    using finalS_cond_spec apply (simp add: \<Delta>3'_defs) 
    by (metis length_map)

  note finals = f1 f2 f3 f4

  show "finalS ss3 = finalS ss4 \<and> finalN ss1 = finalS ss3 \<and> finalN ss2 = finalS ss4"
    using finals by auto

  then show "isIntO ss3 = isIntO ss4" by simp

  show "react (oor \<Delta>3' \<Delta>1') ss3 ss4 statA ss1 ss2 statO"

    unfolding react_def proof(intro conjI)
    (* match1 and match2 are impossible case since isIntO always holds *)
    show "match1 (oor \<Delta>3' \<Delta>1') ss3 ss4 statA ss1 ss2 statO"
      unfolding match1_def by (simp add: finalS_def final_def)  
    show "match2 (oor \<Delta>3' \<Delta>1') ss3 ss4 statA ss1 ss2 statO"
      unfolding match2_def by (simp add: finalS_def final_def)  
    show "match12 (oor \<Delta>3' \<Delta>1') ss3 ss4 statA ss1 ss2 statO"
    using cases_thenBranch[of "pcOf (last cfgs3)"] 
    apply(elim disjE) 
    subgoal using \<Delta>3' unfolding ss lcfgs \<Delta>3'_defs
      by (clarify, metis atLeastAtMost_iff inThenBranch_def lcfgs3 le_antisym less_irrefl_nat less_or_eq_imp_le startOfThenBranch_def)
    subgoal
    proof(rule match12_simpleI, rule disjI2, intro conjI) 
      fix ss3' ss4' statA'
      assume statA': "statA' = sstatA' statA ss3 ss4"
        and v: "validTransO (ss3, ss3')" "validTransO (ss4, ss4')" 
        and sa: "Opt.eqAct ss3 ss4"
        and pc:"pcOf (last cfgs3) = 4"
      note v3 = v(1) note v4 = v(2)


      have pc2:"pc2 = 4"
        using \<Delta>3' pc unfolding ss cfg unfolding \<Delta>3'_defs 
        apply clarify
        by (metis config.sel(1))

      obtain pstate3' cfg3' cfgs3' ibT3' ibUT3' ls3' where ss3': "ss3' = (pstate3', cfg3', cfgs3', ibT3', ibUT3', ls3')"
      by (cases ss3', auto) 
      obtain pstate4' cfg4' cfgs4' ibT4' ibUT4' ls4' where ss4': "ss4' = (pstate4', cfg4', cfgs4', ibT4', ibUT4', ls4')"
      by (cases ss4', auto)
      note ss = ss ss3' ss4'

      show "eqSec ss1 ss3"
        using v sa \<Delta>3' unfolding ss by (simp add: \<Delta>3'_defs) 

      show "eqSec ss2 ss4"
        using v sa \<Delta>3' unfolding ss by (simp add: \<Delta>3'_defs) 

      show "Van.eqAct ss1 ss2"
        using v sa \<Delta>3' unfolding ss Van.eqAct_def
        by (simp add: \<Delta>3'_defs lessI less_or_eq_imp_le numeral_3_eq_3 pc) 

      show "match12_12 (oor \<Delta>3' \<Delta>1') ss3' ss4' statA' ss1 ss2 statO"
      unfolding match12_12_def
      proof(rule exI[of _ "nextN ss1"], rule exI[of _ "nextN ss2"], unfold Let_def, intro conjI impI)
        show "validTransV (ss1, nextN ss1)" 
          by (simp add: f1 nextN_stepN)

        show "validTransV (ss2, nextN ss2)" 
          by (simp add: f2 nextN_stepN)

        {assume sstat: "statA' = Diff"
          show "sstatO' statO ss1 ss2 = Diff"
            using v sa \<Delta>3' sstat unfolding ss cfg statA'
            apply(simp add: \<Delta>3'_defs sstatO'_def sstatA'_def) 
            apply(cases statO, simp_all) apply(cases statA, simp_all) 
            by (smt (z3) Nil_is_map_conv cfg finals ss status.distinct(1) newStat.simps(1))
        } note stat = this


        show "oor \<Delta>3' \<Delta>1' \<infinity> ss3' ss4' statA' (nextN ss1) (nextN ss2) (sstatO' statO ss1 ss2)"
            using v3[unfolded ss, simplified] proof(cases rule: stepS_cases)
            case nonspec_mispred
            then show ?thesis using sa \<Delta>3' stat unfolding ss by (simp add: \<Delta>3'_defs) 
          next
            case spec_mispred
            then show ?thesis using sa \<Delta>3' stat unfolding ss by (simp add: \<Delta>3'_defs)
          next
            case spec_Fence
            then show ?thesis using sa \<Delta>3' stat unfolding ss by (simp add: \<Delta>3'_defs)
          next
            case nonspec_normal
            then show ?thesis using sa \<Delta>3' stat unfolding ss by (simp add: \<Delta>3'_defs)
          next
            case spec_resolve 
            then show ?thesis using sa \<Delta>3' stat pc unfolding ss apply (simp add: \<Delta>3'_defs) 
              by (metis last_ConsL last_map n_not_Suc_n numeral_2_eq_2 numeral_3_eq_3 numeral_eq_iff semiring_norm(87))
          (*spec normal is non trivial*)
          next
            case spec_normal note sn3 = spec_normal
            show ?thesis              
              using v4[unfolded ss, simplified] proof(cases rule: stepS_cases)
              case nonspec_mispred
              then show ?thesis using sa \<Delta>3' stat sn3 unfolding ss by (simp add: \<Delta>3'_defs)
            next
              case spec_mispred
              then show ?thesis using sa \<Delta>3' stat sn3 unfolding ss by (simp add: \<Delta>3'_defs)
            next
              case spec_Fence
              then show ?thesis using sa \<Delta>3' stat sn3 unfolding ss by (simp add: \<Delta>3'_defs)
            next
              case spec_resolve
              then show ?thesis using sa \<Delta>3' stat sn3 unfolding ss by (simp add: \<Delta>3'_defs)
            next
              case nonspec_normal note nn4 = nonspec_normal
              then show ?thesis using sa \<Delta>3' stat sn3 unfolding ss by (simp add: \<Delta>3'_defs)
            next  
              case spec_normal note sn4 = spec_normal
              then show ?thesis 
                using \<Delta>3' sn3 sn4 pc2 lcfgs h3_eq h4_eq hh stat a1_3 a1_4 
                unfolding ss cfg
                apply simp
                apply(rule oorI1)
                apply (simp add: \<Delta>3'_defs butlast ) 
                apply clarsimp apply(intro conjI)
                subgoal by (smt (z3) config.sel(2) last_in_set state.sel(1) vstore.sel)
                subgoal by (smt (z3) config.sel(2) last_in_set state.sel(1) vstore.sel)
                subgoal unfolding array_loc_def by simp .
            qed
          qed    
        qed 
      qed
    subgoal proof(rule match12_simpleI, rule disjI2, intro conjI) 
      fix ss3' ss4' statA'
      assume statA': "statA' = sstatA' statA ss3 ss4"
        and v: "validTransO (ss3, ss3')" "validTransO (ss4, ss4')" 
        and sa: "Opt.eqAct ss3 ss4"
        and pc:"pcOf (last cfgs3) = 5"
      note v3 = v(1) note v4 = v(2)

      have pc2:"pc2 = 5"
        using \<Delta>3' \<Delta>3'_implies pc unfolding ss cfg \<Delta>3'_defs 
        apply clarify by (smt (z3) config.sel(1))



      obtain pstate3' cfg3' cfgs3' ibT3' ibUT3' ls3' where ss3': "ss3' = (pstate3', cfg3', cfgs3', ibT3', ibUT3', ls3')"
      by (cases ss3', auto) 
      obtain pstate4' cfg4' cfgs4' ibT4' ibUT4' ls4' where ss4': "ss4' = (pstate4', cfg4', cfgs4', ibT4', ibUT4', ls4')"
      by (cases ss4', auto)
      note ss = ss ss3' ss4'

      show "eqSec ss1 ss3"
        using v sa \<Delta>3' unfolding ss by (simp add: \<Delta>3'_defs pc) 

      show "eqSec ss2 ss4"
        using v sa \<Delta>3' unfolding ss by (simp add: \<Delta>3'_defs pc)  

      show "Van.eqAct ss1 ss2"
        using v sa \<Delta>3' unfolding ss Van.eqAct_def
        by (simp add: \<Delta>3'_defs pc)  

      show "match12_12 (oor \<Delta>3' \<Delta>1') ss3' ss4' statA' ss1 ss2 statO"
      unfolding match12_12_def
      proof(rule exI[of _ "nextN ss1"], rule exI[of _ "nextN ss2"], unfold Let_def, intro conjI impI)
        show "validTransV (ss1, nextN ss1)" 
          by (simp add: f1 nextN_stepN)

        show "validTransV (ss2, nextN ss2)" 
          by (simp add: f2 nextN_stepN)

        {assume sstat: "statA' = Diff"
          show "sstatO' statO ss1 ss2 = Diff"
            using v sa \<Delta>3' sstat unfolding ss cfg statA'
            apply(simp add: \<Delta>3'_defs sstatO'_def sstatA'_def) 
            apply(cases statO, simp_all) apply(cases statA, simp_all) 
            by (smt (z3) Nil_is_map_conv cfg f3 f4 ss status.distinct(1) newStat.simps(1))
        } note stat = this


        show "oor \<Delta>3' \<Delta>1' \<infinity> ss3' ss4' statA' (nextN ss1) (nextN ss2) (sstatO' statO ss1 ss2)"
            using v3[unfolded ss, simplified] proof(cases rule: stepS_cases)
            case nonspec_mispred
            then show ?thesis using sa \<Delta>3' stat unfolding ss by (simp add: \<Delta>3'_defs) 
          next
            case spec_mispred
            then show ?thesis using sa \<Delta>3' stat unfolding ss by (simp add: \<Delta>3'_defs)
          next
            case spec_Fence
            then show ?thesis using sa \<Delta>3' stat unfolding ss by (simp add: \<Delta>3'_defs)
          next
            case nonspec_normal
            then show ?thesis using sa \<Delta>3' stat unfolding ss by (simp add: \<Delta>3'_defs)
          next
            case spec_resolve 
            then show ?thesis using sa \<Delta>3' stat pc unfolding ss apply (simp add: \<Delta>3'_defs) 
            by (metis last_ConsL last_map numeral_eq_iff semiring_norm(89))
          (*spec normal and spec resolve are non trivial*)
          next
            case spec_normal note sn3 = spec_normal
            show ?thesis              
              using v4[unfolded ss, simplified] proof(cases rule: stepS_cases)
              case nonspec_mispred
              then show ?thesis using sa \<Delta>3' stat sn3 unfolding ss by (simp add: \<Delta>3'_defs)
            next
              case spec_mispred
              then show ?thesis using sa \<Delta>3' stat sn3 unfolding ss by (simp add: \<Delta>3'_defs)
            next
              case spec_Fence
              then show ?thesis using sa \<Delta>3' stat sn3 unfolding ss by (simp add: \<Delta>3'_defs)
            next
              case spec_resolve
              then show ?thesis using sa \<Delta>3' stat sn3 unfolding ss by (simp add: \<Delta>3'_defs)
            next
              case nonspec_normal note nn4 = nonspec_normal
              then show ?thesis using sa \<Delta>3' stat sn3 unfolding ss by (simp add: \<Delta>3'_defs)
            next  
              case spec_normal note sn4 = spec_normal
              then show ?thesis 
                using \<Delta>3' sn3 sn4 pc2 lcfgs h3_eq h4_eq hh stat 
                unfolding ss cfg a1_3 a1_4 
                apply simp apply(rule oorI1)
                apply (simp add: \<Delta>3'_defs butlast) 
                apply clarsimp
                by (smt (z3) config.sel(2) last_in_set state.sel(1) vstore.sel)
            qed
          qed
        qed
      qed
    subgoal proof(rule match12_simpleI, rule disjI1, intro conjI) 
      fix ss3' ss4' statA'
      assume statA': "statA' = sstatA' statA ss3 ss4"
        and v: "validTransO (ss3, ss3')" "validTransO (ss4, ss4')" 
        and sa: "Opt.eqAct ss3 ss4"
        and pc:"pcOf (last cfgs3) = 6"
      note v3 = v(1) note v4 = v(2)


      obtain pstate3' cfg3' cfgs3' ibT3' ibUT3' ls3' where ss3': "ss3' = (pstate3', cfg3', cfgs3', ibT3', ibUT3', ls3')"
      by (cases ss3', auto) 
      obtain pstate4' cfg4' cfgs4' ibT4' ibUT4' ls4' where ss4': "ss4' = (pstate4', cfg4', cfgs4', ibT4', ibUT4', ls4')"
      by (cases ss4', auto)
      note ss = ss ss3' ss4'

      show "\<not> isSecO ss3"
        using v sa \<Delta>3' unfolding ss by (simp add: \<Delta>3'_defs) 

      show "\<not> isSecO ss4"
        using v sa \<Delta>3' unfolding ss  by (simp add: \<Delta>3'_defs)  

      show stat: "statA = statA' \<or> statO = Diff"
        using v sa \<Delta>3'
        unfolding ss statA' sstatA'_def   
        apply(simp_all add: \<Delta>3'_defs)  
        apply (cases statA, simp_all)
        by (smt (verit, best) Nil_is_map_conv f3 f4 ss newStat.simps(1))

        show "oor \<Delta>3' \<Delta>1' \<infinity> ss3' ss4' statA' ss1 ss2 statO"
            using v3[unfolded ss, simplified] proof(cases rule: stepS_cases)
            case nonspec_mispred
            then show ?thesis using sa \<Delta>3' stat unfolding ss by (simp add: \<Delta>3'_defs) 
          next
            case spec_mispred
            then show ?thesis using sa \<Delta>3' stat unfolding ss by (simp add: \<Delta>3'_defs)
          next
            case spec_Fence
            then show ?thesis using sa \<Delta>3' stat unfolding ss by (simp add: \<Delta>3'_defs)
          next
            case nonspec_normal
            then show ?thesis using sa \<Delta>3' stat unfolding ss by (simp add: \<Delta>3'_defs)
          next
            case spec_normal note sn3 = spec_normal
            show ?thesis using sa \<Delta>3' stat sn3 pc v3 unfolding ss by (simp add: \<Delta>3'_defs)
          next
           (*resolution is the only possibT,ibUTility*)
            case spec_resolve note sr3 = spec_resolve
            show ?thesis using v4[unfolded ss, simplified] proof(cases rule: stepS_cases)
              case nonspec_mispred
              then show ?thesis using sa \<Delta>3' stat sr3 unfolding ss by (simp add: \<Delta>3'_defs)
            next
              case spec_mispred
              then show ?thesis using sa \<Delta>3' stat sr3 unfolding ss by (simp add: \<Delta>3'_defs)
            next
              case spec_Fence
              then show ?thesis using sa \<Delta>3' stat sr3 unfolding ss by (simp add: \<Delta>3'_defs)
            next
              case nonspec_normal
              then show ?thesis using sa \<Delta>3' stat sr3 unfolding ss by (simp add: \<Delta>3'_defs)
            next
              case spec_normal
              then show ?thesis using sa \<Delta>3' stat sr3 unfolding ss by (simp add: \<Delta>3'_defs)
            next  
              case spec_resolve note sr4 = spec_resolve
              then show ?thesis                 
                using \<Delta>3' sr3 sr4 lcfgs hh stat a2_3 a2_4  
                      butlast array_locBase le_refl
                unfolding ss cfg 
                apply simp
                apply(rule oorI2)
                apply (simp add: \<Delta>3'_defs \<Delta>1'_defs, intro conjI, metis) 
                apply meson apply meson apply blast by meson
            qed
          qed
        qed
        subgoal using \<Delta>3' unfolding ss lcfgs \<Delta>3'_defs
          by (simp add: avstoreOf.cases  elseBranch_def lcfgs3) .
      qed
    qed


lemma stepe: "unwindIntoCond \<Delta>e \<Delta>e" 
proof(rule unwindIntoCond_simpleI) 
  fix n ss3 ss4 statA ss1 ss2 statO
  assume r: "reachO ss3" "reachO ss4" "reachV ss1" "reachV ss2"
    and \<Delta>e: "\<Delta>e n ss3 ss4 statA ss1 ss2 statO"

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
    using \<Delta>e Opt.final_def Prog.endPC_def finalS_def stepS_endPC
    unfolding \<Delta>e_defs ss by clarsimp


  then show "isIntO ss3 = isIntO ss4" by simp

  show "react \<Delta>e ss3 ss4 statA ss1 ss2 statO"
    unfolding react_def proof(intro conjI)
    (* match1 and match2 are imposibT,ibUTle case since isIntO always holds *)
    show "match1 \<Delta>e ss3 ss4 statA ss1 ss2 statO"
      unfolding match1_def by (simp add: finalS_def final_def) 
    show "match2 \<Delta>e ss3 ss4 statA ss1 ss2 statO"
      unfolding match2_def by (simp add: finalS_def final_def)  
    show "match12 \<Delta>e ss3 ss4 statA ss1 ss2 statO"
      apply(rule match12_simpleI) 
      using \<Delta>e stepS_endPC unfolding ss
      by (simp add: \<Delta>e_defs)
  qed
qed

lemmas theConds = step0 step1 step2 
                  step1' step3' stepe


proposition "rsecure" 
proof-
  define m where m: "m \<equiv> (6::nat)"
  define \<Delta>s where \<Delta>s: "\<Delta>s \<equiv> \<lambda>i::nat. 
  if i = 0 then \<Delta>0
  else if i = 1 then \<Delta>1 
  else if i = 2 then \<Delta>2
  else if i = 3 then \<Delta>1'
  else if i = 4 then \<Delta>3'
  else \<Delta>e" 
  define nxt where nxt: "nxt \<equiv> \<lambda>i::nat. 
  if i = 0 then {0,1,3::nat}
  else if i = 1 then {1,2,5}  
  else if i = 2 then {1} 
  else if i = 3 then {3,4,5}  
  else if i = 4 then {4,3} 
  else {5}"
  show ?thesis apply(rule distrib_unwind_rsecure[of m nxt \<Delta>s])
    subgoal unfolding m by auto
    subgoal unfolding nxt m by auto
    subgoal using init unfolding \<Delta>s by auto
    subgoal 
      unfolding m nxt \<Delta>s apply (simp split: if_splits)
      using theConds
      unfolding oor_def oor3_def oor4_def by auto .
qed
end
end