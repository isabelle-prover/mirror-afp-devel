section "Proof of Relative Security for fun2"
theory Fun_mask
  imports  
  "../Instance_IMP/Instance_Secret_IMem"
  "Relative_Security.Unwinding_fin" 
begin 

subsection "Function definition and Boilerplate"
no_notation bot (\<open>\<bottom>\<close>)

consts NN :: int
consts SS :: int

definition aa1 :: "avname" where "aa1 = ''a1''" 
definition aa2 :: "avname" where "aa2 = ''a2''" 
definition vv :: "avname" where "vv = ''v''" 
definition ii :: "avname" where "ii = ''i''" 
definition temp :: "avname" where "temp = ''temp''" 


lemmas vvars_defs = aa1_def aa2_def vv_def ii_def temp_def

lemma vvars_dff[simp]: 
"aa1 \<noteq> aa2" "aa1 \<noteq> vv" "aa1 \<noteq> ii" "aa1 \<noteq> temp"
"aa2 \<noteq> aa1" "aa2 \<noteq> vv" "aa2 \<noteq> ii" "aa2 \<noteq> temp"
"vv \<noteq> aa1" "vv \<noteq> aa2"  "vv \<noteq> ii" "vv \<noteq> temp"
"ii \<noteq> aa1" "ii \<noteq> aa2" "ii \<noteq> vv" "ii \<noteq> temp"
"temp \<noteq> aa1" "temp \<noteq> aa2" "temp \<noteq> vv" "temp \<noteq> ii"
unfolding vvars_defs by auto

consts size_aa1 :: nat
consts size_aa2 :: nat

(* The initial vstore can be anything *)
fun initVstore :: "vstore \<Rightarrow> bool" where
"initVstore vst = True"
(* (vstore vst xx = 0 \<and> vstore vst yy = 0 \<and> vstore vst xx = 0
  \<and> vstore vst vv = 0 \<and> vstore vst ww = 0) *)
(* The initial avstore contains two arrays named aa1 and aa2 located one after the other *)
fun initAvstore :: "avstore \<Rightarrow> bool" where
"initAvstore (Avstore as)  = (as aa1 = (0, size_aa1) \<and> as aa2 = (size_aa1, size_aa2))"

definition "prog \<equiv> 
[
 \<^cancel>\<open>0 \<close> Start , 
 \<^cancel>\<open>1 \<close> Input T ii ,
 \<^cancel>\<open>2 \<close> IfJump (Less (V ii) (N (int (size_aa1)))) 3 7 ,
 \<^cancel>\<open>3 \<close>   vv ::= (Times (VA aa1 (V ii)) (N 512))  ,
 \<^cancel>\<open>4 \<close>   M temp I (Less (V ii) (N (int (size_aa1)))) T VA aa2 (V vv) E (N 0),
 \<^cancel>\<open>5 \<close>   Output U (V temp) ,
 \<^cancel>\<open>6 \<close>   Jump 8 ,
 \<^cancel>\<open>7 \<close> Output U (N 0)
]"

(* *)

lemma cases_8: "(i::pcounter) = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or> i = 5 \<or> 
 i = 6 \<or> i = 7 \<or> i = 8 \<or> i > 8"
apply(cases i, simp_all) 
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
  . . . . . . . . . 

lemma cases_branch:"(i::pcounter) < 3 \<or> i = 3 \<or> i = 4 \<or> i = 5 \<or> i > 5"
apply(cases i, simp_all) 
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
. . . . . . 


lemma ii_aa1_cases: "vs ii < int size_aa1 \<or> vs ii \<ge> int size_aa1" by auto

lemma is_If_pcOf[simp]: 
"pcOf cfg < 8 \<Longrightarrow> is_IfJump (prog ! (pcOf cfg)) \<longleftrightarrow> pcOf cfg = 2"
apply(cases cfg) subgoal for pc s using cases_8[of "pcOf cfg "] 
by (auto simp: prog_def) .

lemma is_If_pc[simp]: 
"pc < 8 \<Longrightarrow> is_IfJump (prog ! pc) \<longleftrightarrow> pc = 2"
using cases_8[of pc] 
by (auto simp: prog_def) 

lemma eq_Fence_pc[simp]: 
"pc < 8 \<Longrightarrow> prog ! pc \<noteq> Fence"
using cases_8[of pc] 
  by (auto simp: prog_def) 


lemma not_isInput3[simp]:"\<not> is_getInput (prog ! 3)"
  unfolding prog_def by simp


lemma not_is_Output[simp]:"\<not> is_Output (prog ! 3)"
  unfolding  prog_def by simp

(* *)

consts mispred :: "predState \<Rightarrow> pcounter list \<Rightarrow> bool"
consts resolve :: "predState \<Rightarrow> pcounter list \<Rightarrow> bool" 
consts update :: "predState \<Rightarrow> pcounter list \<Rightarrow> predState"
consts initPstate :: predState
fun istate ::"state \<Rightarrow> bool" where
"istate s = (initAvstore (getAvstore s))"

(* *)
interpretation Prog_Mispred_Init where 
prog = prog and initPstate = initPstate and
mispred = mispred and resolve = resolve and update = update and 
istate = istate
  by (standard, simp add: prog_def)
(* *)

(* Restoring the abbreviations: *)
abbreviation
  stepB_abbrev :: "config \<times> val llist \<times> val llist \<Rightarrow> config \<times> val llist \<times> val llist \<Rightarrow> bool" (infix "\<rightarrow>B" 55)
  where "x \<rightarrow>B y == stepB x y"

abbreviation
  stepsB_abbrev :: "config \<times> val llist \<times> val llist \<Rightarrow> config \<times> val llist \<times> val llist \<Rightarrow> bool" (infix "\<rightarrow>B*" 55)
  where "x \<rightarrow>B* y == star stepB x y"

abbreviation
  stepM_abbrev :: "config \<times> val llist \<times> val llist \<Rightarrow> config \<times> val llist \<times> val llist \<Rightarrow> bool" (infix "\<rightarrow>M" 55)
  where "x \<rightarrow>M y == stepM x y"

abbreviation
  stepN_abbrev :: "config \<times> val llist \<times> val llist \<times> loc set \<Rightarrow> config \<times> val llist \<times> val llist \<times> loc set \<Rightarrow> bool" (infix "\<rightarrow>N" 55)
  where "x \<rightarrow>N y == stepN x y"

abbreviation
  stepsN_abbrev :: "config \<times> val llist \<times> val llist \<times> loc set \<Rightarrow> config \<times> val llist \<times> val llist \<times> loc set \<Rightarrow> bool" (infix "\<rightarrow>N*" 55)
  where "x \<rightarrow>N* y == star stepN x y"

abbreviation
  stepS_abbrev :: "configS \<Rightarrow> configS \<Rightarrow> bool" (infix "\<rightarrow>S" 55)
  where "x \<rightarrow>S y == stepS x y"

abbreviation
  stepsS_abbrev :: "configS \<Rightarrow> configS \<Rightarrow> bool" (infix "\<rightarrow>S*" 55)
  where "x \<rightarrow>S* y == star stepS x y"

(* *)

lemma endPC[simp]: "endPC = 8"
unfolding endPC_def unfolding prog_def by auto

(* *)
lemma isInput1[simp]:"prog ! Suc 0 = Input T ii"
  unfolding prog_def by simp

lemma is_getTrustedInput_pcOf[simp]: "pcOf cfg < 8 \<Longrightarrow> is_getInput (prog!(pcOf cfg)) \<longleftrightarrow> pcOf cfg = 1"
using cases_8[of "pcOf cfg"] by (auto simp: prog_def)

lemma is_Output_pcOf[simp]: "pcOf cfg < 8 \<Longrightarrow> is_Output (prog!(pcOf cfg)) \<longleftrightarrow> pcOf cfg = 5 \<or> pcOf cfg = 7"
using cases_8[of "pcOf cfg"] by (auto simp: prog_def)

lemma is_Output1[simp]: "is_Output (prog ! 5)"
unfolding is_Output_def prog_def by auto
lemma is_Output2[simp]: "is_Output (prog ! 7)"
unfolding is_Output_def prog_def by auto

(* *)

lemma isSecV_pcOf[simp]: 
"isSecV (cfg,ibT,ibUT) \<longleftrightarrow> pcOf cfg = 0"
using isSecV_def by simp

lemma isSecO_pcOf[simp]: 
"isSecO (pstate,cfg,cfgs,ib,ls) \<longleftrightarrow> (pcOf cfg = 0 \<and> cfgs = [])"
using isSecO_def by simp

(* *)

lemma getActV_pcOf[simp]: 
"pcOf cfg < 8 \<Longrightarrow> 
 getActV (cfg,ibT, ibUT,ls) = 
 (if pcOf cfg = 1 then lhd ibT else \<bottom>)"
apply(subst getActV_simps) unfolding prog_def 
apply simp  
  using getActV_simps not_is_getTrustedInput_getActV  prog_def by auto

lemma getObsV_pcOf[simp]: 
"pcOf cfg < 8 \<Longrightarrow>  
 getObsV (cfg,ibT,ibUT,ls) = 
 (if pcOf cfg = 5 \<or> pcOf cfg = 7 then 
  (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)
  else \<bottom> 
 )"
apply(subst getObsV_simps) 
unfolding prog_def apply simp  
using getObsV_simps not_is_Output_getObsV is_Output_pcOf prog_def by presburger

lemma getActO_pcOf[simp]: 
"pcOf cfg < 8 \<Longrightarrow> 
 getActO (pstate,cfg,cfgs,ibT,ibUT,ls) = 
 (if pcOf cfg = 1 \<and> cfgs = [] then lhd ibT else \<bottom>)"
apply(subst getActO_simps)
apply(cases cfgs, auto)
using getActV_simps getActV_pcOf prog_def by presburger

lemma getObsO_pcOf[simp]: 
"pcOf cfg < 8 \<Longrightarrow>  
 getObsO (pstate,cfg,cfgs,ibT,ibUT,ls) = 
 (if (pcOf cfg = 5 \<or> pcOf cfg = 7) \<and> cfgs = [] then 
  (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)
  else \<bottom> 
 )"
apply(subst getObsO_simps) 
  apply(cases cfgs, auto)
  subgoal unfolding prog_def by auto
  subgoal unfolding prog_def by auto
using getObsV_simps is_Output_pcOf not_is_Output_getObsV prog_def by presburger


(* *)


lemma eqSec_pcOf[simp]:
"eqSec (cfg1, ibT1, ibUT1, ls1) (pstate3, cfg3, cfgs3, ibT3, ibUT3, ls3) \<longleftrightarrow> 
 (pcOf cfg1 = 0 \<longleftrightarrow> pcOf cfg3 = 0 \<and> cfgs3 = []) \<and> 
 (pcOf cfg1 = 0 \<longrightarrow> stateOf cfg1 = stateOf cfg3)"
unfolding eqSec_def by simp


(* nextB, nextM and readLocs behavior 
(for nextM we are only interested at branching points, here only program counter 4): *)

lemma nextB_pc0[simp]: 
"nextB (Config 0 s, ibT, ibUT) = 
 (Config 1 s, ibT, ibUT)"
apply(subst nextB_Start_Skip_Fence)
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc0[simp]: 
"readLocs (Config 0 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc1[simp]: 
"ibT \<noteq> [[]] \<Longrightarrow> nextB (Config 1 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config 2 (State (Vstore (vs(ii := lhd ibT))) avst h p), ltl ibT, ibUT)"
apply(subst nextB_getTrustedInput')
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc1[simp]: 
"readLocs (Config 1 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

lemma nextB_pc1'[simp]: 
"ibT \<noteq> [[]] \<Longrightarrow> nextB (Config (Suc 0) (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config 2 (State (Vstore (vs(ii := lhd ibT))) avst h p), ltl ibT, ibUT)"
apply(subst nextB_getTrustedInput')
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc1'[simp]: 
"readLocs (Config (Suc 0) s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(*  *)
lemma nextB_pc2_then[simp]: 
"vs ii < int size_aa1 \<Longrightarrow>
 nextB (Config 2 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config 3 (State (Vstore vs) avst h p), ibT, ibUT)"
apply(subst nextB_IfTrue)
unfolding endPC_def unfolding prog_def by auto

lemma nextB_pc2_else[simp]: 
"vs ii \<ge> int size_aa1 \<Longrightarrow>
 nextB (Config 2 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config 7 (State (Vstore vs) avst h p), ibT, ibUT)"
apply(subst nextB_IfFalse)
unfolding endPC_def unfolding prog_def by auto

lemma nextB_pc2: 
"nextB (Config 2 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config (if vs ii < int size_aa1 then 3 else 7) (State (Vstore vs) avst h p), ibT, ibUT)"
by(cases "vs ii < int size_aa1", auto)

lemma readLocs_pc2[simp]: 
"readLocs (Config 2 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

lemma nextM_pc2_then[simp]: 
"vs ii \<ge> int size_aa1 \<Longrightarrow>
 nextM (Config 2 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config 3 (State (Vstore vs) avst h p), ibT, ibUT)"
apply(subst nextM_IfTrue)
unfolding endPC_def unfolding prog_def by auto

lemma nextM_pc2_else[simp]: 
"vs ii < int size_aa1 \<Longrightarrow>
 nextM (Config 2 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config 7 (State (Vstore vs) avst h p), ibT, ibUT)"
apply(subst nextM_IfFalse)
unfolding endPC_def unfolding prog_def by auto

lemma nextM_pc2: 
"nextM (Config 2 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config (if vs ii < int size_aa1 then 7 else 3) (State (Vstore vs) avst h p), ibT, ibUT)"
by(cases "vs ii < int size_aa1", auto)

(* *)

lemma nextB_pc3[simp]: 
"nextB (Config 3 (State (Vstore vs) avst (Heap h) p), ibT, ibUT) = 
 (let l = array_loc aa1 (nat (vs ii)) avst 
  in (Config 4 (State (Vstore (vs(vv := h l * 512))) avst (Heap h) p)), ibT, ibUT)"
apply(subst nextB_Assign)
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc3[simp]: 
"readLocs (Config 3 (State (Vstore vs) avst h p)) = {array_loc aa1 (nat (vs ii)) avst}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc4_True[simp]:
"vs ii < int size_aa1 \<Longrightarrow>
 nextB (Config 4 (State (Vstore vs) avst (Heap h) p), ibT, ibUT) =  
  (let l = array_loc aa2 (nat (vs vv)) avst
  in (Config 5 (State (Vstore (vs(temp := h l))) avst (Heap h) p)), ibT, ibUT)"
apply(subst nextB_MaskTrue)
  unfolding endPC_def unfolding prog_def by auto

lemma nextB_pc4_False[simp]:
"vs ii \<ge> int size_aa1 \<Longrightarrow>
 nextB (Config 4 (State (Vstore vs) avst (Heap h) p), ibT, ibUT) =  
  ((Config 5 (State (Vstore (vs(temp := 0))) avst (Heap h) p)), ibT, ibUT)"
apply(subst nextB_MaskFalse)
unfolding endPC_def unfolding prog_def by auto


lemma readLocs_pc4_True[simp]: 
"
vs ii < int size_aa1 \<Longrightarrow>
readLocs (Config 4 (State (Vstore vs) avst h p)) = {array_loc aa2 (nat (vs vv)) avst}"
  unfolding endPC_def readLocs_def unfolding prog_def by auto

lemma readLocs_pc4_False[simp]: 
"
vs ii \<ge> int size_aa1 \<Longrightarrow>
readLocs (Config 4 (State (Vstore vs) avst h p)) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc5[simp]:
"nextB (Config 5 s, ibT, ibUT) = 
(Config 6 s, ibT, ibUT)"
apply(subst nextB_Output)
unfolding endPC_def unfolding prog_def by auto 

lemma readLocs_pc5[simp]: 
"readLocs (Config 5 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc6[simp]:
"nextB (Config 6 s, ibT, ibUT) = (Config 8 s, ibT, ibUT)"
apply(subst nextB_Jump)
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc6[simp]: 
"readLocs (Config 6 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc7[simp]:
"nextB (Config 7 s, ibT, ibUT) = (Config 8 s, ibT, ibUT)"
apply(subst nextB_Output)
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc7[simp]: 
"readLocs (Config 7 s) = {}"
  unfolding endPC_def readLocs_def unfolding prog_def by auto

(*  *)

lemma nextB_stepB_pc: 
"pc < 8 \<Longrightarrow> (pc = 1 \<longrightarrow> ibT \<noteq> [[]]) \<Longrightarrow> 
(Config pc s, ibT, ibUT) \<rightarrow>B nextB (Config pc s, ibT, ibUT)"
apply(cases s) subgoal for vst avst hh p apply(cases vst, cases avst, cases hh)
subgoal for vs as h
using cases_8[of pc] apply safe
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def)
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def)
  (* *)
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  apply (simp add: prog_def) by (metis llist.collapse)
  (* *)
  subgoal apply(cases "vs ii < int size_aa1")  
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) 
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) .
  subgoal apply(cases "vs ii < int size_aa1")  
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) 
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) .
  (* *)
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def) 
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def) 
  (* *)
  subgoal apply(cases "vs ii < int size_aa1")  
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) 
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
      by (simp add: prog_def) .
  subgoal apply(cases "vs ii < int size_aa1")  
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) 
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) .
  (* *)
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def) 
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def) 
  (* *)
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def) 
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def) 
  (* *)
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def) 
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) 
  (* *)
  subgoal by auto
  subgoal by auto 
  . . .

lemma not_finalB: 
"pc < 8 \<Longrightarrow> (pc = 1 \<longrightarrow> ibT \<noteq> [[]]) \<Longrightarrow> 
 \<not> finalB (Config pc s, ibT, ibUT)"
using nextB_stepB_pc by (simp add: stepB_iff_nextB)

lemma finalB_pc_iff': 
"pc < 8 \<Longrightarrow>
 finalB (Config pc s, ibT, ibUT) \<longleftrightarrow> 
 (pc = 1 \<and> ibT = [[]])"
  apply safe
  subgoal using nextB_stepB_pc[of pc] by (auto simp add: stepB_iff_nextB) 
  subgoal using nextB_stepB_pc[of pc] by (auto simp add: stepB_iff_nextB) 
  subgoal using finalB_iff by auto . 


lemma finalB_pc_iff: 
"pc \<le> 8 \<Longrightarrow>
 finalB (Config pc s, ibT, ibUT) \<longleftrightarrow> 
 (pc = 1 \<and> ibT = [[]] \<or> pc = 8)"
   using cases_8[of pc] apply (elim disjE, simp add: finalB_def)
  subgoal by (meson final_def stebB_0)
  by (simp add: finalB_pc_iff' finalB_endPC)+

lemma finalB_pcOf_iff[simp]:
"pcOf cfg \<le> 8 \<Longrightarrow> 
 finalB (cfg, ibT, ibUT) \<longleftrightarrow> (pcOf cfg = 1 \<and> ibT = [[]] \<or> pcOf cfg = 8)"
by (metis config.collapse finalB_pc_iff) 

lemma finalS_cond:"pcOf cfg < 8 \<Longrightarrow> cfgs = [] \<Longrightarrow> (pcOf cfg = 1 \<longrightarrow> ibT \<noteq> LNil) \<Longrightarrow> \<not> finalS (pstate, cfg, cfgs, ibT, ibUT, ls)"
  apply(cases cfg)
  subgoal for pc s apply(cases s)
  subgoal for vst avst hh p apply(cases vst, cases hh)
    subgoal for vs h
      using cases_8[of pc] apply(elim disjE) unfolding finalS_defs
      subgoal using nonspec_normal[of "[]" "Config pc (State (Vstore vs) avst hh p)" 
                                        pstate pstate ibT ibUT 
                                        "Config 1 (State (Vstore vs) avst hh p)" 
                                        ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls]
        using is_If_pc by force


      subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                                    pstate pstate ibT ibUT 
                                    "Config 2 (State (Vstore (vs(ii:= lhd ibT))) avst hh p)" 
                                    "ltl ibT" ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
              prefer 7 subgoal by metis by simp_all 

    subgoal apply(cases "mispred pstate [2]")
      subgoal apply(frule nonspec_mispred[of cfgs "Config pc (State (Vstore vs) avst hh p)"
                                             pstate "update pstate [pcOf (Config pc (State (Vstore vs) avst hh p))]"
                                             ibT ibUT "Config (if vs ii < int size_aa1 then 3 else 7) (State (Vstore vs) avst hh p)"
                                             ibT ibUT "Config (if vs ii < int size_aa1 then 7 else 3) (State (Vstore vs) avst hh p)"
                                             ibT ibUT "[Config (if vs ii < int size_aa1 then 7 else 3) (State (Vstore vs) avst hh p)]"
                                             "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
      prefer 9 subgoal by metis by (simp add: finalM_iff)+ 
        
      subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)"
                                    pstate pstate ibT ibUT 
                                    "Config (if vs ii < int size_aa1 then 3 else 7) (State (Vstore vs) avst hh p)" 
                                    ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
              prefer 7 subgoal by metis by simp_all .
      subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                         pstate pstate ibT ibUT 
                         "(let l = array_loc aa1 (nat (vs ii)) avst
                        in (Config 4 (State (Vstore (vs(vv := h l * 512))) avst (Heap h) p)))" 
                         ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
            prefer 7 subgoal by metis by simp_all

    subgoal apply(cases "vs ii < int size_aa1")
      subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst (Heap h) p)" 
                                    pstate pstate ibT ibUT 
                                    "(let l = array_loc aa2 (nat (vs vv)) avst
  in (Config 5 (State (Vstore (vs(temp := h l))) avst (Heap h) p)))" 
                                    ibT ibUT "[]" "insert (array_loc aa2 (nat (vs vv)) avst) ls" ls])
              prefer 7 subgoal by metis by simp_all
      subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst (Heap h) p)" 
                                    pstate pstate ibT ibUT 
                                    "(Config 5 (State (Vstore (vs(temp := 0))) avst (Heap h) p))" 
                                    ibT ibUT "[]" ls ls])
              prefer 7 subgoal by metis by simp_all .

    subgoal apply(frule nonspec_normal[of cfgs "Config pc s" 
                                    pstate pstate ibT ibUT 
                                    "Config 6 s" 
                                    ibT ibUT "[]" ls ls])
      prefer 7 by (blast,simp_all)

    subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                                    pstate pstate ibT ibUT 
                                    "Config 8 (State (Vstore vs) avst hh p)" 
                                    ibT ibUT "[]" ls ls])
            prefer 7 subgoal by metis by simp_all

    subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)"
                                    pstate pstate ibT ibUT 
                                    "Config 8 (State (Vstore vs) avst hh p)" 
                                    ibT ibUT "[]" ls ls])
            prefer 7 subgoal by metis by simp_all
    by simp_all . . .


lemma not_is_getTrustedInput[simp]:"cfg = Config 3 (State (Vstore vs) (Avstore as) (Heap h) p) \<Longrightarrow> \<not> is_getInput (prog ! pcOf cfg)"
  unfolding is_getInput_def prog_def by simp

lemma notOutput4[simp]:"\<not> is_Output (prog ! 4)" unfolding prog_def by auto

lemma notInput4[simp]:"\<not> is_getInput (prog ! 4)" unfolding prog_def by auto

lemma notInput5[simp]:"\<not> is_getInput (prog ! 5)" unfolding prog_def by auto

lemma finalS_cond_spec:
      "pcOf cfg < 8 \<Longrightarrow> 
       ((pcOf (last cfgs) = 3 \<or> pcOf (last cfgs) = 4 \<or> pcOf (last cfgs) = 5) \<and> pcOf cfg = 7) 
      \<or> (pcOf (last cfgs) = 7 \<and> pcOf cfg = 3) \<Longrightarrow> 
       length cfgs =  Suc 0 \<Longrightarrow>
      \<not> finalS (pstate, cfg, cfgs, ibT, ibUT, ls)"
  apply(cases cfg)
  subgoal for pc s apply(cases s)
  subgoal for vst avst hh p apply(cases vst, cases avst, cases hh)
  subgoal for vs as h apply(cases "last cfgs")
  subgoal for pcs ss apply(cases ss)
    subgoal for vsts avsts hhs ps apply(cases vsts, cases avsts, cases hhs, simp)
      apply(cases "resolve pstate (pcOf cfg # map pcOf cfgs)")
    subgoal unfolding finalS_defs using spec_resolve by (metis list.size(3) n_not_Suc_n)
    subgoal for vss ass hs apply(elim disjE, elim conjE, elim disjE, simp) 
      unfolding finalS_defs
      subgoal apply(rule notI, 
      erule allE[of _ "(pstate,Config 7 (State (Vstore vs) (Avstore as) (Heap h) p),
                        [Config 4 (State (Vstore (vss(vv := hs (array_loc aa1 (nat (vss ii)) avsts)*512))) avsts hhs ps)],
                        ibT,ibUT,ls \<union> readLocs (last cfgs))"])
        by(erule notE, 
        rule spec_normal[of _ _ _ _ _ _"Config 4 (State (Vstore (vss(vv := hs (array_loc aa1 (nat (vss ii)) avsts)*512))) avsts hhs ps)"], auto)


      subgoal apply(cases "vss ii < int size_aa1")
        subgoal apply(rule notI, 
      erule allE[of _ "(pstate,Config 7 (State (Vstore vs) (Avstore as) (Heap h) p),
                        [Config 5 (State (Vstore (vss(temp := hs (array_loc aa2 (nat (vss vv)) avsts)))) avsts hhs ps)],
                        ibT,ibUT,ls \<union> readLocs (last cfgs))"])
          apply(erule notE[of "(pstate, Config pc (State (Vstore vs) (Avstore as) (Heap h) p), cfgs,
        ibT, ibUT, ls) \<rightarrow>S
       (pstate, Config 7 (State (Vstore vs) (Avstore as) (Heap h) p),
        [Config 5
          (State (Vstore (vss(temp := hs (array_loc aa2 (nat (vss vv)) avsts))))
            avsts hhs ps)],
        ibT, ibUT, ls \<union> readLocs (last cfgs))"])
          by(rule spec_normal, auto)
        subgoal apply(rule notI, 
        erule allE[of _ "(pstate,Config 7 (State (Vstore vs) (Avstore as) (Heap h) p),
                          [Config 5 (State (Vstore (vss(temp := 0))) avsts hhs ps)],
                          ibT,ibUT,ls \<union> readLocs (last cfgs))"])
            apply(erule notE[of "(pstate, Config pc (State (Vstore vs) (Avstore as) (Heap h) p), cfgs,
          ibT, ibUT, ls) \<rightarrow>S
         (pstate, Config 7 (State (Vstore vs) (Avstore as) (Heap h) p),
          [Config 5
            (State (Vstore (vss(temp := 0)))
              avsts hhs ps)],
          ibT, ibUT, ls \<union> readLocs (last cfgs))"])
          by(rule spec_normal, auto) .

      subgoal apply(rule notI, 
      erule allE[of _ "(update pstate (7 # map pcOf cfgs),Config 7 (State (Vstore vs) (Avstore as) (Heap h) p),
                       [],ibT,ibUT,ls)"]) 
      by(erule notE, rule spec_resolve, auto) 

      subgoal apply(rule notI, 
      erule allE[of _ "(update pstate (3 # map pcOf cfgs),Config 3 (State (Vstore vs) (Avstore as) (Heap h) p),
                       [],ibT,ibUT,ls)"])
      by(erule notE, rule spec_resolve, auto)
      . . . . . . . 

end