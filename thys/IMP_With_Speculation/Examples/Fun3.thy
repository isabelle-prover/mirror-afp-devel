section "Proof of Relative Security for fun3"
theory Fun3
imports "../Instance_IMP/Instance_Secret_IMem" 
  "Relative_Security.Unwinding_fin"
begin 


subsection "Function definition and Boilerplate"
no_notation bot ("\<bottom>")


consts NN::"nat"

lemma NN:"int NN \<ge> 0" by auto
consts size_aa1 :: nat
consts size_aa2 :: nat
consts mispred :: "predState \<Rightarrow> pcounter list \<Rightarrow> bool"
consts update :: "predState \<Rightarrow> pcounter list \<Rightarrow> predState"
consts initPstate :: predState

definition aa1 :: "avname" where "aa1 = ''a1''" 
definition aa2 :: "avname" where "aa2 = ''a2''" 
definition vv :: "avname" where "vv = ''v''" 
definition xx :: "avname" where "xx = ''x''" 
definition tt :: "avname" where "tt = ''t''" 


lemmas vvars_defs = aa1_def aa2_def vv_def xx_def tt_def

lemma vvars_dff[simp]: 
"aa1 \<noteq> aa2" "aa1 \<noteq> vv" "aa1 \<noteq> xx" "aa1 \<noteq> tt"
"aa2 \<noteq> aa1" "aa2 \<noteq> vv" "aa2 \<noteq> xx" "aa2 \<noteq> tt"
"vv \<noteq> aa1" "vv \<noteq> aa2"  "vv \<noteq> xx" "vv \<noteq> tt"
"xx \<noteq> aa1" "xx \<noteq> aa2" "xx \<noteq> vv" "xx \<noteq> tt"
"tt \<noteq> aa1" "tt \<noteq> aa2" "tt \<noteq> vv" "tt \<noteq> xx"
unfolding vvars_defs by auto

(* The initial avstore contains two arrays named aa1 and aa2 located one after the other *)
fun initAvstore :: "avstore \<Rightarrow> bool" where
"initAvstore (Avstore as)  = (as aa1 = (0, size_aa1) \<and> as aa2 = (size_aa1, size_aa2))"
fun istate ::"state \<Rightarrow> bool" where
"istate s = (initAvstore (getAvstore s))"

definition "prog \<equiv> 
[
 \<^cancel>\<open>0 \<close> Start , 
 \<^cancel>\<open>1 \<close> Input U xx ,
 \<^cancel>\<open>2 \<close> tt ::= (N 0) ,
 \<^cancel>\<open>3 \<close> IfJump (Less (V xx) (N NN)) 4 7 ,
 \<^cancel>\<open>4 \<close>   vv ::= VA aa1 (V xx) ,
 \<^cancel>\<open>5 \<close>   Fence ,
 \<^cancel>\<open>6 \<close>   tt ::= (VA aa2 (Times (V vv) (N 512))) ,
 \<^cancel>\<open>7 \<close> Output U (V tt)
]"

(* *)

lemma cases_7: "(i::pcounter) = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or> i = 5 \<or> 
 i = 6 \<or> i = 7 \<or> i > 7"
apply(cases i, simp_all) 
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
. . . . . . . .


lemma xx_NN_cases: "vs xx < int NN \<or> vs xx \<ge> int NN" by auto

lemma is_If_pcOf[simp]: 
"pcOf cfg < 8 \<Longrightarrow> is_IfJump (prog ! (pcOf cfg)) \<longleftrightarrow> pcOf cfg = 3"
apply(cases cfg) subgoal for pc s using cases_7[of "pcOf cfg "] 
by (auto simp: prog_def) .

lemma is_If_pc[simp]: 
"pc < 8 \<Longrightarrow> is_IfJump (prog ! pc) \<longleftrightarrow> pc = 3"
using cases_7[of pc] 
by (auto simp: prog_def) 

lemma eq_Fence_pc[simp]: 
"pc < 8 \<Longrightarrow> prog ! pc = Fence \<longleftrightarrow> pc = 5"
using cases_7[of pc] 
by (auto simp: prog_def) 


(* *)

fun resolve :: "predState \<Rightarrow> pcounter list \<Rightarrow> bool" where
  "resolve p pc = (if (pc = [4,7]) then True else False)"



(* *)
interpretation Prog_Mispred_Init where 
prog = prog and initPstate = initPstate and 
mispred = mispred and resolve = resolve and update = update and 
istate = istate
  by (standard, simp add: prog_def)
(* *)

(* Restoring the abbreviations: *)
abbreviation
  stepB_abbrev :: "config \<times> val llist \<times> val llist  \<Rightarrow> config \<times> val llist \<times> val llist \<Rightarrow> bool" (infix "\<rightarrow>B" 55)
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

lemma is_getTrustedInput_pcOf[simp]: "pcOf cfg < 8 \<Longrightarrow> is_getInput (prog!(pcOf cfg)) \<longleftrightarrow> pcOf cfg = 1"
using cases_7[of "pcOf cfg"] by (auto simp: prog_def)
lemma getUntrustedInput_pcOf[simp]: "prog!1 = Input U xx"
  by (auto simp: prog_def)

lemma getInput_not3[simp]: "\<not>is_getInput (prog ! 3)"
  by (auto simp: prog_def)

lemma getInput_not4[simp]: "\<not>is_getInput (prog ! 4)"
  by (auto simp: prog_def)
lemma Output_not4[simp]: "\<not>is_Output (prog ! 4)"
  by (auto simp: prog_def)

lemma is_Output_pcOf[simp]: "pcOf cfg < 8 \<Longrightarrow> is_Output (prog!(pcOf cfg)) \<longleftrightarrow> pcOf cfg = 7"
using cases_7[of "pcOf cfg"] by (auto simp: prog_def)

lemma is_Output: "is_Output (prog ! 7)"
  unfolding is_Output_def prog_def by auto

lemma is_Fence[simp]: "(prog ! 5) = Fence"
unfolding prog_def by auto


lemma not_is_getTrustedInput[simp]:"cfg = Config 3 (State (Vstore vs) (Avstore as) (Heap h) p) \<Longrightarrow> \<not> is_getInput (prog ! pcOf cfg)"
  unfolding is_getInput_def prog_def by simp


lemma not_is_Output[simp]:"cfg = Config pc (State (Vstore vs) (Avstore as) (Heap h) p) \<Longrightarrow>
        pc = 3 \<Longrightarrow> \<not> is_Output (prog ! pcOf cfg)"
  unfolding is_Output prog_def by simp
(* *)

lemma isSecV_pcOf[simp]: 
"isSecV (cfg,ibT,ibUT) \<longleftrightarrow> pcOf cfg = 0"
using isSecV_def by simp

lemma isSecO_pcOf[simp]: 
"isSecO (pstate,cfg,cfgs,ibT,ibUT,ls) \<longleftrightarrow> (pcOf cfg = 0 \<and> cfgs = [])"
using isSecO_def by simp

(* *)

lemma getInputT_not[simp]: "pcOf cfg < 8 \<Longrightarrow> 
(prog ! pcOf cfg) \<noteq> Input T inp"
apply(cases cfg) subgoal for pc s using cases_7[of "pcOf cfg "] 
by (auto simp: prog_def) .

lemma getActV_pcOf[simp]: 
"pcOf cfg < 8 \<Longrightarrow> 
 getActV (cfg,ibT,ibUT,ls) = 
 (if pcOf cfg = 1 then lhd ibUT else \<bottom>)"
apply(subst getActV_simps) unfolding prog_def 
  apply simp  
  using cases_7[of "pcOf cfg"] apply(elim disjE)
  using getActV_simps not_is_getTrustedInput_getActV by auto
  
lemma getObsV_pcOf[simp]: 
"pcOf cfg < 8 \<Longrightarrow>  
 getObsV (cfg,ibT,ibUT,ls) = 
 (if pcOf cfg = 7 then 
  (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)
  else \<bottom> 
 )"
apply(subst getObsV_simps) 
  unfolding prog_def apply simp
  using getObsV_simps not_is_Output_getObsV is_Output_pcOf prog_def by presburger

lemma getActO_pcOf[simp]: 
"pcOf cfg < 8 \<Longrightarrow> 
 getActO (pstate,cfg,cfgs,ibT,ibUT,ls) = 
 (if pcOf cfg = 1 \<and> cfgs = [] then lhd ibUT else \<bottom>)"
apply(subst getActO_simps)
apply(cases cfgs, auto)
  unfolding prog_def apply simp 
  using getActV_simps getActV_pcOf prog_def by presburger

lemma getObsO_pcOf[simp]: 
"pcOf cfg < 8 \<Longrightarrow>  
 getObsO (pstate,cfg,cfgs,ibT,ibUT,ls) = 
 (if (pcOf cfg = 7 \<and> cfgs = []) then 
  (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)
  else \<bottom> 
 )"
apply(subst getObsO_simps) 
apply(cases cfgs, auto)
unfolding prog_def apply simp
using getObsV_simps is_Output_pcOf not_is_Output_getObsV prog_def by presburger 

(* *)
(* *) 

lemma eqSec_pcOf[simp]: 
"eqSec (cfg1, ibT,ibUT1, ls1) (pstate3, cfg3, cfgs3, ibT,ibUT3, ls3) \<longleftrightarrow> 
 (pcOf cfg1 = 0 \<longleftrightarrow> pcOf cfg3 = 0 \<and> cfgs3 = []) \<and> 
 (pcOf cfg1 = 0 \<longrightarrow> stateOf cfg1 = stateOf cfg3)"
unfolding eqSec_def by simp


(* nextB, nextM and readLocs behavior 
(for nextM we are only interested at branching points, here only program counter 4): *)

lemma nextB_pc0[simp]: 
"nextB (Config 0 s, ibT,ibUT) = 
 (Config 1 s, ibT,ibUT)"
apply(subst nextB_Start_Skip_Fence)
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc0[simp]: 
"readLocs (Config 0 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc1[simp]: 
"ibUT \<noteq> LNil \<Longrightarrow> nextB (Config 1 (State (Vstore vs) avst h p), ibT,ibUT) = 
 (Config 2 (State (Vstore (vs(xx := lhd ibUT))) avst h p), ibT, ltl ibUT)"
apply(subst nextB_getUntrustedInput')
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc1[simp]: 
"readLocs (Config 1 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

lemma nextB_pc1'[simp]: 
"ibUT \<noteq> LNil \<Longrightarrow> nextB (Config (Suc 0) (State (Vstore vs) avst h p), ibT,ibUT) = 
 (Config 2 (State (Vstore (vs(xx := lhd ibUT))) avst h p), ibT, ltl ibUT)"
apply(subst nextB_getUntrustedInput')
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc1'[simp]: 
"readLocs (Config (Suc 0) s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc2[simp]:
"nextB (Config 2 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config 3 (State (Vstore (vs(tt := 0))) avst h p), ibT, ibUT)"
apply(subst nextB_Assign)
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc2[simp]: 
"readLocs (Config 2 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc3_then[simp]: 
"vs xx < int NN \<Longrightarrow>
 nextB (Config 3 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config 4 (State (Vstore vs) avst h p), ibT, ibUT)"
apply(subst nextB_IfTrue)
unfolding endPC_def unfolding prog_def by auto

lemma nextB_pc3_else[simp]: 
"vs xx \<ge> int NN \<Longrightarrow>
 nextB (Config 3 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config 7 (State (Vstore vs) avst h p), ibT, ibUT)"
apply(subst nextB_IfFalse)
unfolding endPC_def unfolding prog_def by auto

lemma nextB_pc3: 
"nextB (Config 3 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config (if vs xx < NN then 4 else 7) (State (Vstore vs) avst h p), ibT, ibUT)"
  by(cases "vs xx < NN", auto)

lemma nextM_pc3_then[simp]: 
"vs xx \<ge> int NN \<Longrightarrow>
 nextM (Config 3 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config 4 (State (Vstore vs) avst h p), ibT, ibUT)"
apply(subst nextM_IfTrue)
unfolding endPC_def unfolding prog_def by auto

lemma nextM_pc3_else[simp]: 
"vs xx < int NN \<Longrightarrow>
 nextM (Config 3 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config 7 (State (Vstore vs) avst h p), ibT, ibUT)"
apply(subst nextM_IfFalse)
unfolding endPC_def unfolding prog_def by auto

lemma nextM_pc3: 
"nextM (Config 3 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config (if vs xx < NN then 7 else 4) (State (Vstore vs) avst h p), ibT, ibUT)"
by(cases "vs xx < NN", auto)

lemma readLocs_pc3[simp]: 
"readLocs (Config 3 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto


(* *)

lemma nextB_pc4[simp]: 
"nextB (Config 4 (State (Vstore vs) avst (Heap h) p), ibT,ibUT) = 
 (let l = array_loc aa1 (nat (vs xx)) avst 
  in (Config 5 (State (Vstore (vs(vv := h l))) avst (Heap h) p)), ibT,ibUT)"
apply(subst nextB_Assign)
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc4[simp]: 
"readLocs (Config 4 (State (Vstore vs) avst h p)) = {array_loc aa1 (nat (vs xx)) avst}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc5[simp]: 
"nextB (Config 5 s, ibT,ibUT) = (Config 6 s, ibT,ibUT)"
apply(subst nextB_Start_Skip_Fence)
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc5[simp]: 
"readLocs (Config 5 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc6[simp]:
"nextB (Config 6 (State (Vstore vs) avst (Heap h) p), ibT,ibUT) =  
  (let l = array_loc aa2 (nat (vs vv * 512)) avst
  in (Config 7 (State (Vstore (vs(tt := h l))) avst (Heap h) p)), ibT,ibUT)"
apply(subst nextB_Assign)
unfolding endPC_def unfolding prog_def by auto


lemma readLocs_pc6[simp]: 
"readLocs (Config 6 (State (Vstore vs) avst h p)) = {array_loc aa2 (nat (vs vv * 512)) avst}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc7[simp]:
"nextB (Config 7 s, ibT,ibUT) = (Config 8 s, ibT,ibUT)"
apply(subst nextB_Output)
unfolding endPC_def unfolding prog_def by auto 

lemma readLocs_pc7[simp]: 
"readLocs (Config 7 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_stepB_pc: 
"pc < 8 \<Longrightarrow> (pc = 1 \<longrightarrow> ibUT \<noteq> LNil) \<Longrightarrow> 
(Config pc s, ibT,ibUT) \<rightarrow>B nextB (Config pc s, ibT,ibUT)"
apply(cases s) subgoal for vst avst hh p apply(cases vst, cases avst, cases hh)
subgoal for vs as h
using cases_7[of pc] apply safe
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def)
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def)
  (* *)
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def, metis llist.collapse)
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def)
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def)
  (* *)
  subgoal apply(cases "vs xx < NN")  
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) 
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) .
  subgoal apply(cases "vs xx < NN")  
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
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def) 
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def) 
  subgoal by auto          
  subgoal by auto 
  . . .

lemma not_finalB: 
"pc < 8 \<Longrightarrow> (pc = 1 \<longrightarrow> ibUT \<noteq> LNil) \<Longrightarrow> 
 \<not> finalB (Config pc s, ibT,ibUT)"
using nextB_stepB_pc by (simp add: stepB_iff_nextB)

lemma finalB_pc_iff': 
"pc < 8 \<Longrightarrow>
 finalB (Config pc s, ibT,ibUT) \<longleftrightarrow> 
 (pc = 1 \<and> ibUT = LNil)"
  subgoal apply safe
    subgoal using nextB_stepB_pc[of pc] by (auto simp add: stepB_iff_nextB) 
    subgoal using nextB_stepB_pc[of pc] by (auto simp add: stepB_iff_nextB) 
    subgoal using finalB_iff getUntrustedInput_pcOf by auto . .

lemma finalB_pc_iff: 
"pc \<le> 8 \<Longrightarrow>
 finalB (Config pc s, ibT,ibUT) \<longleftrightarrow> 
 (pc = 1 \<and> ibUT = LNil \<or> pc = 8)"
  using cases_7[of pc] apply (elim disjE, simp add: finalB_def)
  subgoal by (meson final_def stebB_0)
  by (simp add: finalB_pc_iff' finalB_endPC)+

lemma finalB_pcOf_iff[simp]:
"pcOf cfg \<le> 8 \<Longrightarrow> 
 finalB (cfg, ibT,ibUT) \<longleftrightarrow> (pcOf cfg = 1 \<and> ibUT = LNil \<or> pcOf cfg = 8)"
by (metis config.collapse finalB_pc_iff) 




lemma finalS_cond:"pcOf cfg < 8 \<Longrightarrow> cfgs = [] \<Longrightarrow> (pcOf cfg = 1 \<longrightarrow> ibUT \<noteq> LNil) \<Longrightarrow> \<not> finalS (pstate, cfg, cfgs, ibT,ibUT, ls)"
apply(rule notI, cases cfg)
subgoal for pc s apply(cases s)
subgoal for vst avst hh p apply(cases vst, cases avst, cases hh)
  subgoal for vs as h
    using cases_7[of pc] apply(elim disjE) unfolding finalS_defs
    subgoal by(erule allE[of _ "(pstate, Config 1 (State (Vstore vs) avst hh p), [], ibT,ibUT, ls)"], erule notE, rule nonspec_normal, auto)

      subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                                    pstate pstate ibT ibUT 
                                    "Config 2 (State (Vstore (vs(xx:= lhd ibUT))) avst hh p)" 
                                    ibT "ltl ibUT" "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
              prefer 7 subgoal by metis by simp_all
      subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                                    pstate pstate ibT ibUT 
                                    "Config 3 (State (Vstore (vs(tt:= 0))) avst hh p)" 
                                    ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
              prefer 7 subgoal by metis by simp_all

    subgoal apply(cases "mispred pstate [3]")
      subgoal by(erule allE[of _ "(update pstate [pcOf (Config pc (State (Vstore vs) avst hh p))], 
                                   Config (if vs xx < NN then 4 else 7) (State (Vstore vs) avst hh p), 
                                  [Config (if vs xx < NN then 7 else 4) (State (Vstore vs) avst hh p)], 
                                   ibT,ibUT, ls)"], erule notE, rule nonspec_mispred, auto simp: finalM_iff)

      subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)"
                                    pstate pstate ibT ibUT 
                                    "Config (if vs xx < NN then 4 else 7) (State (Vstore vs) avst hh p)" 
                                    ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
              prefer 7 subgoal by metis apply simp_all by (simp add: nextB_pc3) .

    subgoal by(erule allE[of _ "(pstate, Config 5 (State (Vstore (vs(vv := h (array_loc aa1 (nat (vs xx)) avst)))) avst hh p), 
                                                                [], ibT,ibUT, ls \<union> {array_loc aa1 (nat (vs xx)) avst})"],
               erule notE, rule nonspec_normal, auto)

    subgoal by(erule allE[of _ "(pstate, Config 6 (State (Vstore vs) avst hh p), [], ibT,ibUT, ls)"], erule notE, rule nonspec_normal, auto)

    subgoal by(erule allE[of _ "(pstate, Config 7 (State (Vstore (vs(tt := h (array_loc aa2 (nat (vs vv * 512)) (Avstore as))))) avst hh p), 
                                 [], ibT,ibUT, ls \<union> {array_loc aa2 (nat (vs vv * 512)) (Avstore as)})"],
              erule notE, rule nonspec_normal, auto)

    subgoal by(erule allE[of _ "(pstate, Config 8 (State (Vstore vs) avst hh p), [], ibT,ibUT, ls)"], erule notE, rule nonspec_normal, auto)

    by simp_all . . .



lemma finalS_cond_spec:
      "pcOf cfg < 8 \<Longrightarrow> 
       (((pcOf (last cfgs) = 4 \<or> pcOf (last cfgs) = 5) \<and> pcOf cfg = 7) \<or> 
        (pcOf (last cfgs) = 7 \<and> pcOf cfg = 4)) \<Longrightarrow> 
       length cfgs = Suc 0 \<Longrightarrow>
      \<not> finalS (pstate, cfg, cfgs, ibT,ibUT, ls)"
using not_is_getTrustedInput not_is_Output
  apply(cases cfg)
  subgoal for pc s apply(cases s)
  subgoal for vst avst hh p apply(cases vst, cases avst, cases hh)
  subgoal for vs as h apply(cases "last cfgs")
  subgoal for pcs ss apply(cases ss)
  subgoal for vsts avsts hhs ps apply(cases vsts, cases avsts, cases hhs, simp)
    subgoal for vss ass hs apply(elim disjE, elim conjE, elim disjE, simp) 
      unfolding finalS_defs 
      subgoal apply(rule notI, 
      erule allE[of _ "(pstate,Config 7 (State (Vstore vs) (Avstore as) (Heap h) p),
                        [Config 5 (State (Vstore (vss(vv := hs (array_loc aa1 (nat (vss xx)) avsts)))) avsts hhs ps)],
                        ibT,ibUT,ls \<union> readLocs (last cfgs))"])
        by(erule notE, 
        rule spec_normal[of _ _ _ _ _ _"Config 5 (State (Vstore (vss(vv := hs (array_loc aa1 (nat (vss xx)) avsts)))) avsts hhs ps)"], auto)
      
      subgoal apply(rule notI, 
      erule allE[of _ "(pstate,Config 7 (State (Vstore vs) (Avstore as) (Heap h) p),[],ibT,ibUT,ls)"])
        apply(erule notE) by(rule spec_Fence, auto)

      subgoal apply(rule notI, 
      erule allE[of _ "(update pstate (4 # map pcOf cfgs),Config 4 (State (Vstore vs) (Avstore as) (Heap h) p),
                       [],ibT,ibUT,ls)"])
        by(erule notE, rule spec_resolve, auto)
      . . . . . . . 
end
