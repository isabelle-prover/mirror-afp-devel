section "Proof of Relative Security for fun5"
theory Fun5
imports "../Instance_IMP/Instance_Secret_IMem"
  "Relative_Security.Unwinding"
begin 

subsection "Function definition and Boilerplate"
no_notation bot (\<open>\<bottom>\<close>)
consts NN :: nat
consts SS :: nat
lemma NN: "int NN \<ge> 0" and SS: "int SS\<ge>0" by auto

definition aa1 :: "avname" where "aa1 = ''a1''" 
definition aa2 :: "avname" where "aa2 = ''a2''" 
definition vv :: "avname" where "vv = ''v''" 
definition xx :: "avname" where "xx = ''x''"
definition tt :: "avname" where "tt = ''y''" 
definition temp :: "avname" where "temp = ''temp''" 


lemmas vvars_defs = aa1_def aa2_def vv_def xx_def tt_def temp_def

lemma vvars_dff[simp]: 
"aa1 \<noteq> aa2" "aa1 \<noteq> vv" "aa1 \<noteq> xx" "aa1 \<noteq> temp" "aa1 \<noteq> tt"
"aa2 \<noteq> aa1" "aa2 \<noteq> vv" "aa2 \<noteq> xx" "aa2 \<noteq> temp" "aa2 \<noteq> tt"
"vv \<noteq> aa1" "vv \<noteq> aa2"  "vv \<noteq> xx" "vv \<noteq> temp" "vv \<noteq> tt"
"xx \<noteq> aa1" "xx \<noteq> aa2" "xx \<noteq> vv" "xx \<noteq> temp" "xx \<noteq> tt"
"tt \<noteq> aa1" "tt \<noteq> aa2" "tt \<noteq> vv" "tt \<noteq> temp" "tt \<noteq> xx"
"temp \<noteq> aa1" "temp \<noteq> aa2" "temp \<noteq> vv" "temp \<noteq> xx" "temp \<noteq> tt"
unfolding vvars_defs by auto

consts size_aa1 :: nat
consts size_aa2 :: nat

(* The initial avstore contains two arrays named aa1 and aa2 located one after the other *)
fun initAvstore :: "avstore \<Rightarrow> bool" where
"initAvstore (Avstore as)  = (as aa1 = (0, size_aa1) \<and> as aa2 = (size_aa1, size_aa2))"

fun istate ::"state \<Rightarrow> bool" where
"istate s = (initAvstore (getAvstore s))"

definition "prog \<equiv> 
[
 \<^cancel>\<open>0 \<close> Start , 
 \<^cancel>\<open>1 \<close> tt ::= (N 0),
 \<^cancel>\<open>2 \<close> xx ::= (N 1),
 \<^cancel>\<open>3 \<close> IfJump (Not (Eq (V xx) (N 0))) 4 11 ,
 \<^cancel>\<open>4 \<close> Input U xx ,
 \<^cancel>\<open>5 \<close> IfJump (Less (V xx) (N NN)) 6 10 ,
 \<^cancel>\<open>6 \<close>   vv ::= VA aa1 (V xx) ,
 \<^cancel>\<open>7 \<close>   Fence ,
 \<^cancel>\<open>8 \<close>   tt ::= (VA aa2 (Times (V vv) (N SS))) ,
 \<^cancel>\<open>9 \<close>   Output U (V tt) ,
 \<^cancel>\<open>10\<close> Jump 3,
 \<^cancel>\<open>11\<close> Output U (N 0)
]"


definition "PC \<equiv> {0..11}"
(* we read "before" as "before or at" *)
definition "beforeWhile = {0,1,2}"
definition "inWhile = {3..11}"
definition "startOfWhileThen = 4"
definition "startOfIfThen = 6"
definition "inThenIfBeforeFence = {6,7}"
definition "startOfElseBranch = 10"
definition "inElseIf = {10,3,4,11}" (*for specualtive cases*)
definition "whileElse = 11"

fun leftWhileSpec where 
  "leftWhileSpec cfg cfg' = 
      (pcOf cfg = whileElse \<and> 
       pcOf cfg' = startOfWhileThen)"

fun rightWhileSpec where 
  "rightWhileSpec cfg cfg' = 
      (pcOf cfg = startOfWhileThen \<and> 
       pcOf cfg' = whileElse)"

fun whileSpeculation where  
 "whileSpeculation cfg cfg' = 
  (leftWhileSpec cfg cfg' \<or>
   rightWhileSpec cfg cfg')"
lemmas whileSpec_def = whileSpeculation.simps 
                       startOfWhileThen_def
                       whileElse_def

lemmas whileSpec_defs = whileSpec_def
                        leftWhileSpec.simps 
                        rightWhileSpec.simps
(* *)

lemma cases_12: "(i::pcounter) = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or> i = 5 \<or> 
 i = 6 \<or> i = 7 \<or> i = 8 \<or> i = 9 \<or> i = 10 \<or> i = 11 \<or> i = 12 \<or> i > 12"
apply(cases i, simp_all) 
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
. . . . . . . . . . . . .


lemma xx_0_cases: "vs xx = 0 \<or> vs xx \<noteq> 0" by auto

lemma xx_NN_cases: "vs xx < int NN \<or> vs xx \<ge> int NN" by auto

lemma is_IfJump_pcOf[simp]: 
"pcOf cfg < 12 \<Longrightarrow> is_IfJump (prog ! (pcOf cfg)) \<longleftrightarrow> pcOf cfg = 3 \<or> pcOf cfg = 5"
apply(cases cfg) subgoal for pc s using cases_12[of "pcOf cfg "] 
by (auto simp: prog_def) .

lemma is_IfJump_pc[simp]: 
"pc < 12 \<Longrightarrow> is_IfJump (prog ! pc) \<longleftrightarrow> pc = 3 \<or> pc = 5"
using cases_12[of pc] 
by (auto simp: prog_def) 

lemma eq_Fence_pc[simp]: 
"pc < 12 \<Longrightarrow> prog ! pc = Fence \<longleftrightarrow> pc = 7"
using cases_12[of pc] 
  by (auto simp: prog_def) 

lemma output1[simp]:
"prog ! 9 = Output U (V tt)" by(simp add: prog_def)
lemma output2[simp]:
"prog ! 11 = Output U (N 0)" by(simp add: prog_def)
lemma is_if[simp]:"is_IfJump (prog ! 3)" by(simp add: prog_def)

lemma is_nif1[simp]:"\<not>is_IfJump (prog ! 6)" by(simp add: prog_def)
lemma is_nif2[simp]:"\<not>is_IfJump (prog ! 7)" by(simp add: prog_def)

lemma is_nin1[simp]:"\<not> is_getInput (prog ! 6)" by(simp add: prog_def)
lemma is_nout1[simp]:"\<not> is_Output (prog ! 6)" by(simp add: prog_def)
lemma is_nin2[simp]:"\<not> is_getInput (prog ! 10)" by(simp add: prog_def)
lemma is_nout2[simp]:"\<not> is_Output (prog ! 10)" by(simp add: prog_def)

lemma fence[simp]:"prog ! 7 = Fence" by(simp add: prog_def)

lemma nfence[simp]:"prog ! 6 \<noteq> Fence" by(simp add: prog_def)
(* *)

consts mispred :: "predState \<Rightarrow> pcounter list \<Rightarrow> bool"
fun resolve :: "predState \<Rightarrow> pcounter list \<Rightarrow> bool" where
  "resolve p pc = 
  (if (set pc = {4,11} \<or> (6 \<in> set pc \<and> (4 \<in> set pc \<or> 11 \<in> set pc)))
   then True else False)"

lemma resolve_63: "\<not>resolve p [6,3]" by auto
lemma resolve_64: "resolve p [6,4]" by auto
lemma resolve_611: "resolve p [6,11]" by auto
lemma resolve_106: "\<not>resolve p [10,6]" by auto

consts update :: "predState \<Rightarrow> pcounter list \<Rightarrow> predState"
consts initPstate :: predState

(* *)
interpretation Prog_Mispred_Init where 
prog = prog and initPstate = initPstate and
mispred = mispred and resolve = resolve and update = update and 
istate = istate
  by (standard, simp add: prog_def)

(* *)

(* Restoring the abbreviations: *)
abbreviation
  stepB_abbrev :: "config \<times> val llist \<times> val llist  \<Rightarrow> config \<times> val llist \<times> val llist \<Rightarrow> bool" (infix \<open>\<rightarrow>B\<close> 55)
  where "x \<rightarrow>B y == stepB x y"

abbreviation
  stepsB_abbrev :: "config \<times> val llist \<times> val llist \<Rightarrow> config \<times> val llist \<times> val llist \<Rightarrow> bool" (infix \<open>\<rightarrow>B*\<close> 55)
  where "x \<rightarrow>B* y == star stepB x y"

abbreviation
  stepM_abbrev :: "config \<times> val llist \<times> val llist \<Rightarrow> config \<times> val llist \<times> val llist \<Rightarrow> bool" (infix \<open>\<rightarrow>MM\<close> 55)
  where "x \<rightarrow>MM y == stepM x y"

abbreviation
  stepN_abbrev :: "config \<times> val llist \<times> val llist \<times> loc set \<Rightarrow> config \<times> val llist \<times> val llist \<times> loc set \<Rightarrow> bool" (infix \<open>\<rightarrow>N\<close> 55)
  where "x \<rightarrow>N y == stepN x y"

abbreviation
  stepsN_abbrev :: "config \<times> val llist \<times> val llist \<times> loc set \<Rightarrow> config \<times> val llist \<times> val llist \<times> loc set \<Rightarrow> bool" (infix \<open>\<rightarrow>N*\<close> 55)
  where "x \<rightarrow>N* y == star stepN x y"

abbreviation
  stepS_abbrev :: "configS \<Rightarrow> configS \<Rightarrow> bool" (infix \<open>\<rightarrow>S\<close> 55)
  where "x \<rightarrow>S y == stepS x y"

abbreviation
  stepsS_abbrev :: "configS \<Rightarrow> configS \<Rightarrow> bool" (infix \<open>\<rightarrow>S*\<close> 55)
  where "x \<rightarrow>S* y == star stepS x y"

(* *)

lemma endPC[simp]: "endPC = 12"
unfolding endPC_def unfolding prog_def by auto

(* *)

lemma is_getInput_pcOf[simp]: "pcOf cfg < 12 \<Longrightarrow> is_getInput (prog!(pcOf cfg)) \<longleftrightarrow> pcOf cfg = 4"
using cases_12[of "pcOf cfg"] by (auto simp: prog_def)

lemma getUntrustedInput_pcOf[simp]: "prog!4 = Input U xx"
  by (auto simp: prog_def)

lemma getInput_not6[simp]: "\<not>is_getInput (prog ! 6)" by (auto simp: prog_def)
lemma getInput_not7[simp]: "\<not>is_getInput (prog ! 7)" by (auto simp: prog_def)
lemma getInput_not10[simp]: "\<not>is_getInput (prog ! 10)" by (auto simp: prog_def)

lemma is_Output_pcOf[simp]: "pcOf cfg < 12 \<Longrightarrow> is_Output (prog!(pcOf cfg)) \<longleftrightarrow> (pcOf cfg = 9 \<or> pcOf cfg = 11)"
using cases_12[of "pcOf cfg"] by (auto simp: prog_def) 

lemma is_Output: "is_Output (prog ! 9)"
unfolding is_Output_def prog_def by auto
lemma is_Output_1: "is_Output (prog ! 11)"
unfolding is_Output_def prog_def by auto
(* *)

lemma isSecV_pcOf[simp]: 
"isSecV (cfg,ibT,ibUT) \<longleftrightarrow> pcOf cfg = 0"
using isSecV_def by simp

lemma isSecO_pcOf[simp]: 
"isSecO (pstate,cfg,cfgs,ibT,ibUT,ls) \<longleftrightarrow> (pcOf cfg = 0 \<and> cfgs = [])"
using isSecO_def by simp

(* *)

lemma getInputT_not[simp]: "pcOf cfg < 12 \<Longrightarrow> 
(prog ! pcOf cfg) \<noteq> Input T inp"
apply(cases cfg) subgoal for pc s using cases_12[of "pcOf cfg "] 
by (auto simp: prog_def) .

lemma getActV_pcOf[simp]: 
"pcOf cfg < 12 \<Longrightarrow> 
 getActV (cfg,ibT,ibUT,ls) = 
 (if pcOf cfg = 4 then lhd ibUT else \<bottom>)"
apply(subst getActV_simps) unfolding prog_def 
apply simp  
  using getActV_simps  
  using cases_12[of "pcOf cfg "]
  by auto

lemma getObsV_pcOf[simp]: 
"pcOf cfg < 12 \<Longrightarrow>  
 getObsV (cfg,ibT,ibUT,ls) = 
 (if pcOf cfg = 9 \<or> pcOf cfg = 11 then 
  (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)
  else \<bottom> 
 )"
apply(subst getObsV_simps) 
unfolding prog_def apply simp  
  using getObsV_simps not_is_Output_getObsV is_Output_pcOf prog_def 
        One_nat_def by presburger

lemma getActO_pcOf[simp]: 
"pcOf cfg < 12 \<Longrightarrow> 
 getActO (pstate,cfg,cfgs,ibT,ibUT,ls) = 
 (if pcOf cfg = 4 \<and> cfgs = [] then lhd ibUT else \<bottom>)"
apply(subst getActO_simps)
  apply(cases cfgs, auto)
  unfolding prog_def
  apply(cases "pcOf cfg = 4", auto)
  using getActV_simps getActV_pcOf prog_def by simp

lemma getObsO_pcOf[simp]: 
"pcOf cfg < 12 \<Longrightarrow>  
 getObsO (pstate,cfg,cfgs,ibT,ibUT,ls) = 
 (if (pcOf cfg = 9 \<or> pcOf cfg = 11) \<and> cfgs = [] then 
  (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)
  else \<bottom> 
 )"
apply(subst getObsO_simps) 
apply(cases cfgs, auto)
unfolding prog_def 
  using getObsV_simps is_Output_pcOf not_is_Output_getObsV prog_def
        One_nat_def by presburger

(* *) 

lemma eqSec_pcOf[simp]: 
"eqSec (cfg1, ibT1,ibUT1, ls1) (pstate3, cfg3, cfgs3, ibT3,ibUT3, ls3) \<longleftrightarrow> 
 (pcOf cfg1 = 0 \<longleftrightarrow> pcOf cfg3 = 0 \<and> cfgs3 = []) \<and> 
 (pcOf cfg1 = 0 \<longrightarrow> stateOf cfg1 = stateOf cfg3)"
unfolding eqSec_def by simp


lemma getActInput:"pc4 = 4 \<Longrightarrow> pc3 = 4 \<Longrightarrow> cfgs3 = [] \<Longrightarrow>  cfgs4 = [] \<Longrightarrow>
       getActO (pstate3, Config pc3 (State (Vstore vs3) avst3 h3 p3), [], ibT3,ibUT3, ls3) =
       getActO (pstate4, Config pc4 (State (Vstore vs4) avst4 h4 p4), [], ibT4,ibUT4, ls4)
   \<Longrightarrow> lhd ibUT3 = lhd ibUT4"
  using getActO_pcOf zero_less_numeral by auto

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
"nextB (Config 1 (State (Vstore vs) avst hh p), ibT,ibUT) = 
 ((Config 2 (State (Vstore (vs(tt := 0))) avst hh p)), ibT,ibUT)"
apply(subst nextB_Assign)
  unfolding endPC_def unfolding prog_def by auto

lemma nextB_pc1'[simp]: 
"nextB (Config (Suc 0) (State (Vstore vs) avst hh p), ibT,ibUT) = 
 ((Config 2 (State (Vstore (vs(tt := 0))) avst hh p)), ibT,ibUT)"
apply(subst nextB_Assign)
  unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc1[simp]: 
"readLocs (Config 1 s) = {}"
  unfolding endPC_def readLocs_def unfolding prog_def by auto

lemma readLocs_pc1'[simp]: 
"readLocs (Config (Suc 0) s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(*  *)

lemma nextB_pc2[simp]: 
"nextB (Config 2 (State (Vstore vs) avst hh p), ibT,ibUT) = 
 ((Config 3 (State (Vstore (vs(xx := 1))) avst hh p)), ibT,ibUT)"
apply(subst nextB_Assign)
  unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc2[simp]: 
"readLocs (Config 2 s) = {}"
  unfolding endPC_def readLocs_def unfolding prog_def by auto

(**)

lemma nextB_pc3_then[simp]: 
"vs xx \<noteq> 0 \<Longrightarrow>
 nextB (Config 3 (State (Vstore vs) avst hh p), ibT,ibUT) = 
 (Config 4 (State (Vstore vs) avst hh p), ibT,ibUT)"
apply(subst nextB_IfTrue)
unfolding endPC_def unfolding prog_def Eq_def by auto

lemma nextB_pc3_else[simp]: 
"vs xx = 0 \<Longrightarrow>
 nextB (Config 3 (State (Vstore vs) avst hh p), ibT,ibUT) = 
 (Config 11 (State (Vstore vs) avst hh p), ibT,ibUT)"
apply(subst nextB_IfFalse)
unfolding endPC_def unfolding prog_def Eq_def by auto

lemma nextB_pc3: 
"nextB (Config 3 (State (Vstore vs) avst hh p), ibT,ibUT) = 
 (Config (if vs xx \<noteq> 0 then 4 else 11) (State (Vstore vs) avst hh p), ibT,ibUT)"
by(cases "vs xx = 0", auto)

lemma readLocs_pc3[simp]: 
"readLocs (Config 3 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def Eq_def by auto

lemma nextM_pc3_then[simp]: 
"vs xx = 0 \<Longrightarrow>
 nextM (Config 3 (State (Vstore vs) avst hh p), ibT,ibUT) = 
 (Config 4 (State (Vstore vs) avst hh p), ibT,ibUT)"
apply(subst nextM_IfTrue)
unfolding endPC_def unfolding prog_def Eq_def by auto

lemma nextM_pc3_else[simp]: 
"vs xx \<noteq> 0 \<Longrightarrow>
 nextM (Config 3 (State (Vstore vs) avst hh p), ibT,ibUT) = 
 (Config 11 (State (Vstore vs) avst hh p), ibT,ibUT)"
apply(subst nextM_IfFalse)
unfolding endPC_def unfolding prog_def Eq_def by auto

lemma nextM_pc3: 
"nextM (Config 3 (State (Vstore vs) avst hh p), ibT,ibUT) = 
 (Config (if vs xx \<noteq> 0 then 11 else 4) (State (Vstore vs) avst hh p), ibT,ibUT)"
  by(cases "vs xx = 0", auto)

(* *)

lemma nextB_pc4[simp]: 
"ibUT \<noteq> LNil \<Longrightarrow> nextB (Config 4 (State (Vstore vs) avst hh p), ibT,ibUT) = 
 (Config 5 (State (Vstore (vs(xx := lhd ibUT))) avst hh p), ibT, ltl ibUT)"
apply(subst nextB_getUntrustedInput')
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc4[simp]: 
"readLocs (Config 4 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc5_then[simp]: 
"vs xx < int NN \<Longrightarrow>
 nextB (Config 5 (State (Vstore vs) avst hh p), ibT,ibUT) = 
 (Config 6 (State (Vstore vs) avst hh p), ibT,ibUT)"
apply(subst nextB_IfTrue)
unfolding endPC_def unfolding prog_def Eq_def by auto

lemma nextB_pc5_else[simp]: 
"vs xx \<ge> int NN \<Longrightarrow>
 nextB (Config 5 (State (Vstore vs) avst hh p), ibT,ibUT) = 
 (Config 10 (State (Vstore vs) avst hh p), ibT,ibUT)"
apply(subst nextB_IfFalse)
unfolding endPC_def unfolding prog_def Eq_def by auto

lemma nextB_pc5: 
"nextB (Config 5 (State (Vstore vs) avst hh p), ibT,ibUT) = 
 (Config (if vs xx < NN then 6 else 10) (State (Vstore vs) avst hh p), ibT,ibUT)"
by(cases "vs xx < NN", auto)

lemma readLocs_pc5[simp]: 
"readLocs (Config 5 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def Eq_def by auto

lemma nextM_pc5_then[simp]: 
"vs xx \<ge> int NN \<Longrightarrow>
 nextM (Config 5 (State (Vstore vs) avst hh p), ibT,ibUT) = 
 (Config 6 (State (Vstore vs) avst hh p), ibT,ibUT)"
apply(subst nextM_IfTrue)
unfolding endPC_def unfolding prog_def Eq_def by auto

lemma nextM_pc5_else[simp]: 
"vs xx < int NN \<Longrightarrow>
 nextM (Config 5 (State (Vstore vs) avst hh p), ibT,ibUT) = 
 (Config 10 (State (Vstore vs) avst hh p), ibT,ibUT)"
apply(subst nextM_IfFalse)
unfolding endPC_def unfolding prog_def Eq_def by auto

lemma nextM_pc5: 
"nextM (Config 5 (State (Vstore vs) avst hh p), ibT,ibUT) = 
 (Config (if vs xx < NN then 10 else 6) (State (Vstore vs) avst hh p), ibT,ibUT)"
  by(cases "vs xx < NN", auto)

(* *)

lemma nextB_pc6[simp]: 
"nextB (Config 6 (State (Vstore vs) avst (Heap hh) p), ibT,ibUT) = 
 (let l = array_loc aa1 (nat (vs xx)) avst 
  in (Config 7 (State (Vstore (vs(vv := hh l))) avst (Heap hh) p)), ibT,ibUT)"
apply(subst nextB_Assign)
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc6[simp]: 
"readLocs (Config 6 (State (Vstore vs) avst hh p)) = {array_loc aa1 (nat (vs xx)) avst}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc7[simp]: 
"nextB (Config 7 s, ibT,ibUT) = (Config 8 s, ibT,ibUT)"
apply(subst nextB_Start_Skip_Fence)
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc7[simp]: 
"readLocs (Config 7 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc8[simp]:
"nextB (Config 8 (State (Vstore vs) avst (Heap hh) p), ibT,ibUT) =  
  (let l = array_loc aa2 (nat (vs vv * SS)) avst
  in (Config 9 (State (Vstore (vs(tt := hh l))) avst (Heap hh) p)), ibT,ibUT)"
apply(subst nextB_Assign)
unfolding endPC_def unfolding prog_def by auto


lemma readLocs_pc8[simp]: 
"readLocs (Config 8 (State (Vstore vs) avst hh p)) = {array_loc aa2 (nat (vs vv * SS)) avst}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc9[simp]:
"nextB (Config 9 s, ibT,ibUT) = (Config 10 s, ibT,ibUT)"
apply(subst nextB_Output)
unfolding endPC_def unfolding prog_def by auto 

lemma readLocs_pc9[simp]: 
"readLocs (Config 9 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc10[simp]:
"nextB (Config 10 s, ibT,ibUT) = (Config 3 s, ibT,ibUT)"
apply(subst nextB_Jump)
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc10[simp]: 
"readLocs (Config 10 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto


lemma nextB_pc11[simp]: 
"nextB (Config 11 s, ibT,ibUT) = 
 (Config 12 s, ibT,ibUT)"
apply(subst nextB_Output)
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc11[simp]: 
"readLocs (Config 11 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(**)
lemma map_L1:"length cfgs = Suc 0 \<Longrightarrow> 
    pcOf (last cfgs) = y \<Longrightarrow> map pcOf cfgs = [y]"
  by (smt (verit,del_insts) Suc_length_conv cfgs_map last.simps 
      length_0_conv map_eq_Cons_conv nth_Cons_0 numeral_2_eq_2)

lemma map_L2:"length cfgs = 2 \<Longrightarrow> 
    pcOf (cfgs ! 0) = x \<Longrightarrow>
    pcOf (last cfgs) = y \<Longrightarrow> map pcOf cfgs = [x,y]"
  by (smt (verit) Suc_length_conv cfgs_map last.simps 
      length_0_conv map_eq_Cons_conv nth_Cons_0 numeral_2_eq_2)

lemma "length cfgs = 2 \<Longrightarrow> (cfgs ! 0) = last (butlast cfgs)" 
  by (cases cfgs, auto) 

lemma nextB_stepB_pc: 
"pc < 12 \<Longrightarrow> (pc = 4 \<longrightarrow> ibUT \<noteq> LNil) \<Longrightarrow> 
(Config pc s, ibT,ibUT) \<rightarrow>B nextB (Config pc s, ibT,ibUT)"
apply(cases s) subgoal for vst avst hh p apply(cases vst, cases avst, cases hh)
subgoal for vs as h
using cases_12[of pc] apply safe
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def)
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def)
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) 
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def)

 (*  *)

  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def)
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def)
  (* *)
  subgoal apply(cases "vs xx = 0")  
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def Eq_def) 
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def Eq_def, auto)  .
  subgoal apply(cases "vs xx = 0")  
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def Eq_def) 
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
      by (simp add: prog_def Eq_def, auto)  .
  subgoal apply(cases "vs xx = 0")  
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
      by (simp add: prog_def Eq_def, metis llist.exhaust_sel)
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
      by (simp add: prog_def Eq_def, metis llist.exhaust_sel)  .
  subgoal apply(cases "vs xx < NN")  
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
      by (simp add: prog_def Eq_def) 
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
      by (simp add: prog_def Eq_def) .
  (* *)

  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    apply (simp add: prog_def) 
    using nextB_pc5 prog_def by presburger
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) 

  (* *)
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def) 
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def) 
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def) 
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def) 

  (* *)
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) 
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) 
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) 
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def)  
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) 
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) 
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) 
  subgoal by simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) . .
  (*  *)

lemma not_finalB: 
"pc < 12 \<Longrightarrow> (pc = 4 \<longrightarrow> ibUT \<noteq> LNil) \<Longrightarrow> 
 \<not> finalB (Config pc s, ibT,ibUT)"
using nextB_stepB_pc by (simp add: stepB_iff_nextB)


lemma finalB_pc_iff': 
"pc < 12 \<Longrightarrow>
 finalB (Config pc s, ibT,ibUT) \<longleftrightarrow> 
 (pc = 4 \<and> ibUT = LNil)"
  subgoal apply safe
    subgoal using nextB_stepB_pc[of pc] by (auto simp add: stepB_iff_nextB) 
    subgoal using nextB_stepB_pc[of pc] by (auto simp add: stepB_iff_nextB) 
    subgoal using finalB_iff getUntrustedInput_pcOf by auto . .


lemma finalB_pc_iff: 
"pc \<le> 12 \<Longrightarrow>
 finalB (Config pc s, ibT,ibUT) \<longleftrightarrow> 
 (pc = 12 \<or> pc = 4 \<and> ibUT = LNil)"
  using  Prog.finalB_iff endPC finalB_pc_iff' order_le_less finalB_iff
  by metis


lemma finalB_pcOf_iff[simp]:
"pcOf cfg \<le> 12 \<Longrightarrow> 
 finalB (cfg, ibT,ibUT) \<longleftrightarrow> (pcOf cfg = 12 \<or> pcOf cfg = 4 \<and> ibUT = LNil)"
by (metis config.collapse finalB_pc_iff) 


lemma finalS_cond:"pcOf cfg < 12 \<Longrightarrow> noMisSpec cfgs \<Longrightarrow> ibUT \<noteq> LNil \<Longrightarrow> \<not> finalS (pstate, cfg, cfgs, ibT,ibUT, ls)"
  apply(cases cfg)
  subgoal for pc s apply(cases s)
  subgoal for vst avst hh p apply(cases vst, cases avst, cases hh)
    subgoal for vs as h
      using cases_12[of pc] apply(elim disjE) unfolding finalS_defs noMisSpec_def
      subgoal using nonspec_normal[of "[]" "Config pc (State (Vstore vs) avst hh p)" 
                                        pstate pstate ibT ibUT 
                                        "Config 1 (State (Vstore vs) avst hh p)" 
                                        ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls]
        using is_IfJump_pc by force


      subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                                    pstate pstate ibT ibUT 
                                    "Config 2 (State (Vstore (vs(tt:= 0))) avst hh p)" 
                                    ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
              prefer 7 subgoal by metis by simp_all 

      subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                                    pstate pstate ibT ibUT 
                                    "Config 3 (State (Vstore (vs(xx:= 1))) avst hh p)" 
                                    ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
              prefer 7 subgoal by metis by simp_all 

    subgoal apply(cases "mispred pstate [3]")
      subgoal apply(frule nonspec_mispred[of cfgs "Config pc (State (Vstore vs) avst hh p)"
                                             pstate "update pstate [pcOf (Config pc (State (Vstore vs) avst hh p))]"
                                             ibT ibUT "Config (if vs xx \<noteq> 0 then 4 else 11) (State (Vstore vs) avst hh p)"
                                             ibT ibUT "Config (if vs xx \<noteq> 0 then 11 else 4) (State (Vstore vs) avst hh p)"
                                             ibT ibUT "[Config (if vs xx \<noteq> 0 then 11 else 4) (State (Vstore vs) avst hh p)]"
                                             "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
      prefer 9 subgoal by metis by (simp add: finalM_iff)+

      subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)"
                                    pstate pstate ibT ibUT 
                                    "Config (if vs xx \<noteq> 0 then 4 else 11) (State (Vstore vs) avst hh p)" 
                                    ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
      prefer 7 subgoal by metis by simp_all . 

      subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                                    pstate pstate ibT ibUT 
                                    "Config 5 (State (Vstore (vs(xx:= lhd ibUT))) avst hh p)" 
                                    ibT "ltl ibUT" "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
              prefer 7 subgoal by metis by simp_all 

    subgoal apply(cases "mispred pstate [5]")
      subgoal apply(frule nonspec_mispred[of cfgs "Config pc (State (Vstore vs) avst hh p)"
                                             pstate "update pstate [pcOf (Config pc (State (Vstore vs) avst hh p))]"
                                             ibT ibUT "Config (if vs xx < NN then 6 else 10) (State (Vstore vs) avst hh p)"
                                             ibT ibUT "Config (if vs xx < NN then 10 else 6) (State (Vstore vs) avst hh p)"
                                             ibT ibUT "[Config (if vs xx < NN then 10 else 6) (State (Vstore vs) avst hh p)]"
                                             "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
      prefer 9 subgoal by metis by (simp add: finalM_iff)+

      subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)"
                                    pstate pstate ibT ibUT 
                                    "Config (if vs xx < NN then 6 else 10) (State (Vstore vs) avst hh p)" 
                                    ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
      prefer 7 subgoal by metis by simp_all . 

    subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                         pstate pstate ibT ibUT 
                         "(let l = (array_loc aa1 (nat (vs xx)) (Avstore as)) 
                                in (Config 7 (State (Vstore (vs(vv := h l))) avst hh p)))" 
                         ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
            prefer 7 subgoal by metis by simp_all

    subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                                    pstate pstate ibT ibUT 
                                    "Config 8 (State (Vstore vs) avst hh p)" 
                                    ibT ibUT "[]" ls ls])
            prefer 7 subgoal by metis by simp_all

    subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                         pstate pstate ibT ibUT 
                         "(let l = (array_loc aa2 (nat (vs vv * SS)) (Avstore as)) 
                                in (Config 9 (State (Vstore (vs(tt := h l))) avst hh p)))" 
                         ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
            prefer 7 subgoal by metis by simp_all

    subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                                    pstate pstate ibT ibUT 
                                    "Config 10 (State (Vstore vs) avst hh p)" 
                                    ibT ibUT "[]" ls ls])
            prefer 7 subgoal by metis by simp_all

    subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                                    pstate pstate ibT ibUT 
                                    "Config 3 (State (Vstore vs) avst hh p)" 
                                    ibT ibUT "[]" ls ls])
            prefer 7 subgoal by metis by simp_all

    subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)"
                                    pstate pstate ibT ibUT 
                                    "Config 12 (State (Vstore vs) avst hh p)" 
                                    ibT ibUT "[]" ls ls])
            prefer 7 subgoal by metis by simp_all
    by simp_all . . .

lemma finalS_cond':"pcOf cfg < 12 \<Longrightarrow> cfgs = [] \<Longrightarrow> ibUT \<noteq> LNil \<Longrightarrow> \<not> finalS (pstate, cfg, cfgs, ibT,ibUT, ls)"
  using finalS_cond by (simp add: noMisSpec_def)

lemma finalS_while_spec:
      "whileSpeculation cfg (last cfgs) \<Longrightarrow> 
       length cfgs = Suc 0 \<Longrightarrow>
      \<not> finalS (pstate, cfg, cfgs, ibT,ibUT, ls)"
  apply(unfold whileSpec_defs, cases cfg)
  subgoal for pc s apply(cases s)
  subgoal for vst avst hh p apply(cases vst, cases avst, cases hh)
    subgoal for vs as h
      apply(elim disjE, elim conjE) unfolding finalS_defs
      subgoal using stepS_spec_resolve_iff[of cfgs pstate cfg ibT ibUT ls "update pstate (pcOf cfg # map pcOf cfgs)"]
            by (metis (no_types, lifting) cfgs_map empty_set insert_commute less_numeral_extra(3) 
                resolve.simps list.simps(15) list.size(3) numeral_2_eq_2 pos2)
      subgoal apply(elim conjE) 
              using spec_resolve[of cfgs pstate cfg "update pstate (pcOf cfg # map pcOf cfgs)" cfg "[]" ibT ibT ibUT ibUT ls ls ]
              by (metis (no_types, lifting) empty_set insert_commute last_ConsL resolve.simps
                  length_0_conv length_1_butlast length_Suc_conv list.simps(9,8,15)) . . . . 

lemma finalS_while_spec_L2:
      "pcOf cfg = 6 \<Longrightarrow>
       whileSpeculation (cfgs!0) (last cfgs) \<Longrightarrow> 
       length cfgs = 2 \<Longrightarrow>
      \<not> finalS (pstate, cfg, cfgs, ibT,ibUT, ls)"
apply(unfold whileSpec_defs, cases cfg)
  subgoal for pc s apply(cases s)
  subgoal for vst avst hh p apply(cases vst, cases avst, cases hh)
    subgoal for vs as h
      apply(elim disjE, elim conjE) unfolding finalS_defs
      subgoal using stepS_spec_resolve_iff[of cfgs pstate cfg ibT ibUT ls "update pstate (pcOf cfg # map pcOf cfgs)"]
        unfolding resolve.simps
        using list.set_intros(1,2) map_L2 zero_neq_numeral
        by fastforce
      subgoal apply(elim conjE) 
        using spec_resolve
        unfolding resolve.simps
        using list.set_intros(1,2) map_L2 zero_neq_numeral
        by (metis (no_types, lifting) Prog_Mispred.spec_resolve Prog_Mispred_axioms list.size(3))
      . . . . 

lemma finalS_if_spec:
      "(pcOf (last cfgs) \<in> inThenIfBeforeFence \<and> pcOf cfg = 10) \<or> 
       (pcOf (last cfgs) \<in> inElseIf \<and> pcOf cfg = 6) \<Longrightarrow> 
       length cfgs = Suc 0 \<Longrightarrow>
      \<not> finalS (pstate, cfg, cfgs, ibT,ibUT, ls)"
  unfolding inThenIfBeforeFence_def inElseIf_def
  apply(simp,cases "last cfgs")
  subgoal for pc s apply(cases s)
  subgoal for vst avst hh p apply(cases vst, cases hh)
    subgoal for vs h
      apply(elim disjE, elim conjE) unfolding finalS_defs
      subgoal apply(elim disjE)
        subgoal apply(rule notI, 
      erule allE[of _ "(pstate,cfg,
                        [Config 7 (State (Vstore (vs(vv := h (array_loc aa1 (nat (vs xx)) avst)))) avst hh p)],
                        ibT,ibUT,ls \<union> readLocs (last cfgs))"])
        by(erule notE, rule spec_normal[of _ _ _ _ _ _"Config 7 (State (Vstore (vs(vv := h (array_loc aa1 (nat (vs xx)) avst)))) avst hh p)"], auto)
        by (metis cfgs_Suc_zero fence not_Cons_self2 stepS_spec_Fence_iff spec_resolve)
      subgoal apply(elim conjE, elim disjE) 
        subgoal apply(rule notI, 
        erule allE[of _ "(pstate,cfg,
                        [Config 3 (State (Vstore vs) avst hh p)],
                        ibT,ibUT,ls \<union> readLocs (last cfgs))"])
          by(erule notE, rule spec_normal[of _ _ _ _ _ _"Config 3 (State (Vstore vs) avst hh p)"], auto)
        subgoal apply(cases "mispred pstate [6,3]")
          subgoal apply(rule notI, erule allE[of _ "
            (update pstate (pcOf cfg # map pcOf cfgs),
           cfg,
           [Config (if vs xx \<noteq> 0 then 4 else 11) (State (Vstore vs) avst hh p),
            Config (if vs xx \<noteq> 0 then 11 else 4) (State (Vstore vs) avst hh p)], ibT,ibUT,
           ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p)))"], erule notE, 
        rule spec_mispred[of _ _ _ _ _ _
           "Config (if vs xx \<noteq> 0 then 4 else 11) (State (Vstore vs) avst hh p)"
        _ _ "Config (if vs xx \<noteq> 0 then 11 else 4) (State (Vstore vs) avst hh p)" ibT ibUT]) 
            by(auto simp: finalM_iff)

        apply(rule notI, erule allE[of _ "
            (pstate, cfg, [Config (if vs xx \<noteq> 0 then 4 else 11) (State (Vstore vs) avst hh p)], ibT,ibUT,
             ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p)))"])
          by(erule notE, rule spec_normal[of _ _ _ _ _ _"Config (if vs xx \<noteq> 0 then 4 else 11) (State (Vstore vs) avst hh p)"], auto)

        subgoal by (metis resolve_64 stepS_spec_resolve_iff 
                          map_L1 cfgs_Suc_zero not_Cons_self2) 
        subgoal by (metis resolve_611 stepS_spec_resolve_iff 
                          map_L1 cfgs_Suc_zero not_Cons_self2) 
  . . . . .


end