section "Proof of Relative Security for fun6"
theory Fun6
imports "../Instance_IMP/Instance_Secret_IMem_Inp"
  "Relative_Security.Unwinding"
begin 

subsection "Function definition and Boilerplate"
no_notation bot ("\<bottom>")
consts NN :: nat
lemma NN: "NN \<ge> 0" by auto

definition aa1 :: "avname" where "aa1 = ''a1''" 
definition aa2 :: "avname" where "aa2 = ''a2''" 
definition vv :: "vname" where "vv = ''v''" 
definition tt :: "vname" where "tt = ''y''" 


lemmas vvars_defs = aa1_def aa2_def vv_def xx_def tt_def yy_def ffile_def

lemma vvars_dff[simp]: 
"aa1 \<noteq> aa2" "aa1 \<noteq> vv" "aa1 \<noteq> xx" "aa1 \<noteq> yy" "aa1 \<noteq> tt" "aa1 \<noteq> ffile"
"aa2 \<noteq> aa1" "aa2 \<noteq> vv" "aa2 \<noteq> xx" "aa2 \<noteq> yy" "aa2 \<noteq> tt" "aa2 \<noteq> ffile"
"vv \<noteq> aa1" "vv \<noteq> aa2"  "vv \<noteq> xx" "vv \<noteq> yy" "vv \<noteq> tt" "vv \<noteq> ffile"
"xx \<noteq> aa1" "xx \<noteq> aa2" "xx \<noteq> vv" "xx \<noteq> yy" "xx \<noteq> tt" "xx \<noteq> ffile"
"tt \<noteq> aa1" "tt \<noteq> aa2" "tt \<noteq> vv" "tt \<noteq> yy" "tt \<noteq> xx" "tt \<noteq> ffile"
"yy \<noteq> aa1" "yy \<noteq> aa2" "yy \<noteq> vv" "yy \<noteq> xx" "yy \<noteq> tt" "yy \<noteq> ffile"
"ffile \<noteq> aa1" "ffile \<noteq> aa2" "ffile \<noteq> vv" "ffile \<noteq> xx" "ffile \<noteq> tt" "ffile \<noteq> yy"
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
 \<^cancel>\<open>3 \<close> IfJump (Not (Eq (V xx) (N 0))) 4 13 ,
 \<^cancel>\<open>4 \<close> Input U xx ,
 \<^cancel>\<open>5 \<close> Input T yy ,
 \<^cancel>\<open>6 \<close> IfJump (Less (V xx) (N NN)) 7 12 ,
 \<^cancel>\<open>7 \<close>   vv ::= VA aa1 (V xx) ,
 \<^cancel>\<open>8 \<close>   writeSecretOnFile,
 \<^cancel>\<open>9 \<close>   Fence ,
 \<^cancel>\<open>10\<close>   tt ::= (VA aa2 (Times (V vv) (N 512))) ,
 \<^cancel>\<open>11\<close>   Output U (V tt) ,
 \<^cancel>\<open>12\<close> Jump 3,
 \<^cancel>\<open>13\<close> Output U (N 0)
]"


definition "PC \<equiv> {0..13}"
(* we read "before" as "before or at" *)
definition "beforeWhile = {0,1,2}"
definition "afterWhile = {3..13}"
definition "startOfWhileThen = 4"
definition "startOfIfThen = 7"
definition "inThenIfBeforeOutput = {7,8}"
definition "startOfElseBranch = 12"
definition "inElseIf = {12,3,4,13}" (*for specualtive cases*)
definition "whileElse = 13"

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

lemma cases_14: "(i::pcounter) = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or> i = 5 \<or> 
 i = 6 \<or> i = 7 \<or> i = 8 \<or> i = 9 \<or> i = 10 \<or> i = 11 \<or> i = 12 \<or> i = 13 \<or> i = 14 \<or> i > 14"
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
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
. . . . . . . . . . . . . . .


lemma xx_0_cases: "vs xx = 0 \<or> vs xx \<noteq> 0" by auto

lemma xx_NN_cases: "vs xx < int NN \<or> vs xx \<ge> int NN" by auto

lemma is_If_pcOf[simp]: 
"pcOf cfg < 14 \<Longrightarrow> is_IfJump (prog ! (pcOf cfg)) \<longleftrightarrow> pcOf cfg = 3 \<or> pcOf cfg = 6"
apply(cases cfg) using cases_14[of "pcOf cfg"] by (auto simp: prog_def)

lemma is_If_pc[simp]: 
"pc < 14 \<Longrightarrow> is_IfJump (prog ! pc) \<longleftrightarrow> pc = 3 \<or> pc = 6"
using cases_14[of pc] by (auto simp: prog_def) 

lemma eq_Fence_pc[simp]: 
"pc < 14 \<Longrightarrow> prog ! pc = Fence \<longleftrightarrow> pc = 9"
using cases_14[of pc] by (auto simp: prog_def) 

lemma output1[simp]:"prog ! 11 = Output U (V tt)" by(simp add: prog_def)
lemma output2[simp]:"prog ! 13 = Output U (N 0)" by(simp add: prog_def)
lemma is_if[simp]:"is_IfJump (prog ! 3)" by(simp add: prog_def)

lemma is_nif1[simp]:"\<not>is_IfJump (prog ! 7)" by(simp add: prog_def)
lemma is_nif2[simp]:"\<not>is_IfJump (prog ! 8)" by(simp add: prog_def)

lemma getInput_not6[simp]:"\<not> is_getInput (prog ! 6)" by(simp add: prog_def)
lemma Output_not6[simp]:"\<not> is_Output (prog ! 6)" by(simp add: prog_def)

lemma getInput_not7[simp]:"\<not> is_getInput (prog ! 7)" by(simp add: prog_def)
lemma Output_not7[simp]:"\<not> is_Output (prog ! 7)" by(simp add: prog_def)

lemma getInput_not8[simp]:"\<not> is_getInput (prog ! 8)" by(simp add: prog_def)
lemma Output_not8[simp]:"is_Output (prog ! 8)" by(simp add: prog_def)

lemma is_nif[simp]:"\<not> is_IfJump (prog ! 9)" by(simp add: prog_def)
lemma getInput_not10[simp]:"\<not> is_getInput (prog ! 10)" by(simp add: prog_def)
lemma Output_not10[simp]:"\<not> is_Output (prog ! 10)" by(simp add: prog_def)

lemma getInput_not12[simp]:"\<not> is_getInput (prog ! 12)" by(simp add: prog_def)
lemma Output_not12[simp]:"\<not> is_Output (prog ! 12)" by(simp add: prog_def)

lemma fence[simp]:"prog ! 9 = Fence" by(simp add: prog_def)

lemma nfence[simp]:"prog ! 7 \<noteq> Fence" by(simp add: prog_def)
(* *)

consts mispred :: "predState \<Rightarrow> pcounter list \<Rightarrow> bool"
fun resolve :: "predState \<Rightarrow> pcounter list \<Rightarrow> bool" where
  "resolve p pc = 
  (if (set pc = {4,13} \<or> (7 \<in> set pc \<and> (4 \<in> set pc \<or> 13 \<in> set pc)) \<or> pc = [12,8])
   then True else False)"

lemma resolve_73: "\<not>resolve p [7,3]" by auto
lemma resolve_74: "resolve p [7,4]" by auto
lemma resolve_713: "resolve p [7,13]" by auto
lemma resolve_127: "\<not>resolve p [12,7]" by auto
lemma resolve_129: "\<not>resolve p [12,9]" by auto


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
  stepB_abbrev :: "config \<times> val llist \<times> val llist \<Rightarrow> config \<times> val llist \<times> val llist \<Rightarrow> bool" (infix "\<rightarrow>B" 55)
  where "x \<rightarrow>B y == stepB x y"

abbreviation
  stepsB_abbrev :: "config \<times> val llist \<times> val llist \<Rightarrow> config \<times> val llist \<times> val llist \<Rightarrow> bool" (infix "\<rightarrow>B*" 55)
  where "x \<rightarrow>B* y == star stepB x y"

abbreviation
  stepM_abbrev :: "config \<times> val llist \<times> val llist \<Rightarrow> config \<times> val llist \<times> val llist \<Rightarrow> bool" (infix "\<rightarrow>MM" 55)
  where "x \<rightarrow>MM y == stepM x y"

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

lemma endPC[simp]: "endPC = 14"
unfolding endPC_def unfolding prog_def by auto

(* *)
lemma is_getInput_pcOf[simp]: "pcOf cfg < 14 \<Longrightarrow> is_getInput (prog!(pcOf cfg)) \<longleftrightarrow> pcOf cfg = 4 \<or> pcOf cfg = 5"
  using cases_14[of "pcOf cfg"] by (auto simp: prog_def)

lemma is_Output_pcOf[simp]: "pcOf cfg < 14 \<Longrightarrow> is_Output (prog!(pcOf cfg)) \<longleftrightarrow> (pcOf cfg = 8 \<or> pcOf cfg = 11 \<or> pcOf cfg = 13)"
using cases_14[of "pcOf cfg"] by (auto simp: prog_def) 

lemma is_Output_T: "is_Output (prog ! 8)"
unfolding is_Output_def prog_def by auto
lemma is_Output: "is_Output (prog ! 11)"
unfolding is_Output_def prog_def by auto
lemma is_Output_1: "is_Output (prog ! 13)"
unfolding is_Output_def prog_def by auto
(* *)

lemma isSecV_pcOf[simp]: 
"isSecV (cfg,ibT,ibUT,ls) \<longleftrightarrow> \<not>finalB (cfg,ibT,ibUT)"
using isSecV_def by simp

lemma isSecO_pcOf[simp]: 
"isSecO (pstate,cfg,cfgs,ibT,ibUT,ls) \<longleftrightarrow> 
 \<not>finalS (pstate,cfg,cfgs,ibT,ibUT,ls) \<and> cfgs = []"
using isSecO_def by simp

(* *)

lemma getActV_pcOf[simp]: 
"pcOf cfg < 14 \<Longrightarrow> 
 getActV (cfg,ibT,ibUT,ls) = 
 (if pcOf cfg = 4 then lhd ibUT 
  else if pcOf cfg = 5 then lhd ibT 
  else \<bottom>)"
apply(subst getActV_simps) unfolding prog_def 
apply simp  
using getActV_simps not_is_getInput_getActV prog_def by auto

lemma getObsV_pcOf[simp]: 
"pcOf cfg < 14 \<Longrightarrow>  
 getObsV (cfg,ibT,ibUT,ls) = 
 (if pcOf cfg = 11 \<or> pcOf cfg = 13 then 
  (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)
  else \<bottom> 
 )"
apply(subst getObsV_simps) 
 apply (simp add: prog_def)
  unfolding getObsV_simps not_is_Output_getObsV is_Output_pcOf prog_def One_nat_def 
  using cases_14[of "pcOf cfg"] by auto

lemma getActO_pcOf[simp]: 
"pcOf cfg < 12 \<Longrightarrow> 
 getActO (pstate,cfg,cfgs,ibT,ibUT,ls) = 
 (if cfgs = [] then 
  (if pcOf cfg = 4 then lhd ibUT
   else if pcOf cfg = 5 then lhd ibT 
  else \<bottom>) else \<bottom>)"
apply(subst getActO_simps)
  apply(cases cfgs, auto)
  unfolding prog_def apply simp 
  apply(cases "pcOf cfg = 4", auto)
  using getActV_simps getActV_pcOf prog_def by simp

lemma getObsO_pcOf[simp]: 
"pcOf cfg < 14 \<Longrightarrow>  
 getObsO (pstate,cfg,cfgs,ibT,ibUT,ls) = 
 (if (pcOf cfg = 11 \<or> pcOf cfg = 13) \<and> cfgs = [] then 
  (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)
  else \<bottom> 
 )"
apply(subst getObsO_simps) 
apply(cases cfgs, auto)
  using getObsV_simps is_Output_pcOf not_is_Output_getObsV prog_def
        One_nat_def 
unfolding prog_def 
  using cases_14[of "pcOf cfg"] 
  by auto


(* *) 

lemma getActTrustedInput:"pc4 = 4 \<Longrightarrow> pc3 = 4 \<Longrightarrow> cfgs3 = [] \<Longrightarrow>  cfgs4 = [] \<Longrightarrow>
       getActO (pstate3, Config pc3 (State (Vstore vs3) avst3 h3 p3), [], ib3T, ib3UT, ls3) =
       getActO (pstate4, Config pc4 (State (Vstore vs4) avst4 h4 p4), [], ib4T, ib4UT, ls4)
   \<Longrightarrow> lhd ib3UT = lhd ib4UT"
  using getActO_pcOf zero_less_numeral by auto

lemma getActUntrustedInput:"pc4 = 5 \<Longrightarrow> pc3 = 5 \<Longrightarrow> cfgs3 = [] \<Longrightarrow>  cfgs4 = [] \<Longrightarrow>
       getActO (pstate3, Config pc3 (State (Vstore vs3) avst3 h3 p3), [], ib3T, ib3UT, ls3) =
       getActO (pstate4, Config pc4 (State (Vstore vs4) avst4 h4 p4), [], ib4T, ib4UT, ls4)
   \<Longrightarrow> lhd ib3T = lhd ib4T"
  using getActO_pcOf zero_less_numeral by auto

(* nextB, nextM and readLocs behavior 
(for nextM we are only interested at branching points, here only program counter 4): *)

lemma nextB_pc0[simp]: 
"nextB (Config 0 s, ibT, ibUT) = (Config 1 s, ibT, ibUT)"
apply(subst nextB_Start_Skip_Fence)
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc0[simp]: 
"readLocs (Config 0 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc1[simp]: 
"nextB (Config 1 (State (Vstore vs) avst hh p), ibT, ibUT) = 
 ((Config 2 (State (Vstore (vs(tt := 0))) avst hh p)), ibT, ibUT)"
apply(subst nextB_Assign)
  unfolding endPC_def unfolding prog_def by auto

lemma nextB_pc1'[simp]: 
"nextB (Config (Suc 0) (State (Vstore vs) avst hh p), ibT, ibUT) = 
 ((Config 2 (State (Vstore (vs(tt := 0))) avst hh p)), ibT, ibUT)"
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
"nextB (Config 2 (State (Vstore vs) avst hh p), ibT, ibUT) = 
 ((Config 3 (State (Vstore (vs(xx := 1))) avst hh p)), ibT, ibUT)"
apply(subst nextB_Assign)
  unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc2[simp]: 
"readLocs (Config 2 s) = {}"
  unfolding endPC_def readLocs_def unfolding prog_def by auto

(**)

lemma nextB_pc3_then[simp]: 
"vs xx \<noteq> 0 \<Longrightarrow>
 nextB (Config 3 (State (Vstore vs) avst hh p), ibT, ibUT) = 
 (Config 4 (State (Vstore vs) avst hh p), ibT, ibUT)"
apply(subst nextB_IfTrue)
unfolding endPC_def unfolding prog_def Eq_def by auto

lemma nextB_pc3_else[simp]: 
"vs xx = 0 \<Longrightarrow>
 nextB (Config 3 (State (Vstore vs) avst hh p), ibT, ibUT) = 
 (Config 13 (State (Vstore vs) avst hh p), ibT, ibUT)"
apply(subst nextB_IfFalse)
unfolding endPC_def unfolding prog_def Eq_def by auto

lemma nextB_pc3: 
"nextB (Config 3 (State (Vstore vs) avst hh p), ibT, ibUT) = 
 (Config (if vs xx \<noteq> 0 then 4 else 13) (State (Vstore vs) avst hh p), ibT, ibUT)"
by(cases "vs xx = 0", auto)

lemma readLocs_pc3[simp]: 
"readLocs (Config 3 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def Eq_def by auto

lemma nextM_pc3_then[simp]: 
"vs xx = 0 \<Longrightarrow>
 nextM (Config 3 (State (Vstore vs) avst hh p), ibT, ibUT) = 
 (Config 4 (State (Vstore vs) avst hh p), ibT, ibUT)"
apply(subst nextM_IfTrue)
unfolding endPC_def unfolding prog_def Eq_def by auto

lemma nextM_pc3_else[simp]: 
"vs xx \<noteq> 0 \<Longrightarrow>
 nextM (Config 3 (State (Vstore vs) avst hh p), ibT, ibUT) = 
 (Config 13 (State (Vstore vs) avst hh p), ibT, ibUT)"
apply(subst nextM_IfFalse)
unfolding endPC_def unfolding prog_def Eq_def by auto

lemma nextM_pc3: 
"nextM (Config 3 (State (Vstore vs) avst hh p), ibT, ibUT) = 
 (Config (if vs xx \<noteq> 0 then 13 else 4) (State (Vstore vs) avst hh p), ibT, ibUT)"
  by(cases "vs xx = 0", auto)

(* *)

lemma nextB_pc4[simp]: 
"ibUT \<noteq> LNil \<Longrightarrow> nextB (Config 4 (State (Vstore vs) avst hh p), ibT, ibUT) = 
 (Config 5 (State (Vstore (vs(xx := lhd ibUT))) avst hh p), ibT, ltl ibUT)"
apply(subst nextB_getUntrustedInput')
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc4[simp]: 
"readLocs (Config 4 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc5[simp]: 
"ibT \<noteq> LNil \<Longrightarrow> nextB (Config 5 (State (Vstore vs) avst hh p), ibT, ibUT) = 
 (Config 6 (State (Vstore (vs(yy := lhd ibT))) avst hh p), ltl ibT, ibUT)"
apply(subst nextB_getTrustedInput')
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc5[simp]: 
"readLocs (Config 5 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc6_then[simp]: 
"vs xx < int NN \<Longrightarrow>
 nextB (Config 6 (State (Vstore vs) avst hh p), ibT, ibUT) = 
 (Config 7 (State (Vstore vs) avst hh p), ibT, ibUT)"
apply(subst nextB_IfTrue)
unfolding endPC_def unfolding prog_def Eq_def by auto

lemma nextB_pc6_else[simp]: 
"vs xx \<ge> int NN \<Longrightarrow>
 nextB (Config 6 (State (Vstore vs) avst hh p), ibT, ibUT) = 
 (Config 12 (State (Vstore vs) avst hh p), ibT, ibUT)"
apply(subst nextB_IfFalse)
unfolding endPC_def unfolding prog_def Eq_def by auto

lemma nextB_pc6: 
"nextB (Config 6 (State (Vstore vs) avst hh p), ibT, ibUT) = 
 (Config (if vs xx < int NN then 7 else 12) (State (Vstore vs) avst hh p), ibT, ibUT)"
by(cases "vs xx < int NN", auto)

lemma readLocs_pc6[simp]: 
"readLocs (Config 6 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def Eq_def by auto

lemma nextM_pc6_then[simp]: 
"vs xx \<ge> int NN \<Longrightarrow>
 nextM (Config 6 (State (Vstore vs) avst hh p), ibT, ibUT) = 
 (Config 7 (State (Vstore vs) avst hh p), ibT, ibUT)"
apply(subst nextM_IfTrue)
unfolding endPC_def unfolding prog_def Eq_def by auto

lemma nextM_pc6_else[simp]: 
"vs xx < int NN \<Longrightarrow>
 nextM (Config 6 (State (Vstore vs) avst hh p), ibT, ibUT) = 
 (Config 12 (State (Vstore vs) avst hh p), ibT, ibUT)"
apply(subst nextM_IfFalse)
unfolding endPC_def unfolding prog_def Eq_def by auto

lemma nextM_pc6: 
"nextM (Config 6 (State (Vstore vs) avst hh p), ibT, ibUT) = 
 (Config (if vs xx < int NN then 12 else 7) (State (Vstore vs) avst hh p), ibT, ibUT)"
  by(cases "vs xx < int NN", auto)

(* *)

lemma nextB_pc7[simp]: 
"nextB (Config 7 (State (Vstore vs) avst (Heap hh) p), ibT, ibUT) = 
 (let l = array_loc aa1 (nat (vs xx)) avst 
  in (Config 8 (State (Vstore (vs(vv := hh l))) avst (Heap hh) p)), ibT, ibUT)"
apply(subst nextB_Assign)
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc7[simp]: 
"readLocs (Config 7 (State (Vstore vs) avst hh p)) = {array_loc aa1 (nat (vs xx)) avst}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)
lemma nextB_pc8[simp]: 
"nextB (Config 8 (State (Vstore vs) avst hh p), ibT, ibUT) = 
 ((Config 9 (State (Vstore vs) avst hh p)), ibT, ibUT)"
apply(subst nextB_Output)
  unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc8[simp]: 
"readLocs (Config 8 s) = {}"
  unfolding endPC_def readLocs_def 
  unfolding prog_def  by auto

(* *)
lemma nextB_pc9[simp]: 
"nextB (Config 9 s, ibT, ibUT) = (Config 10 s, ibT, ibUT)"
apply(subst nextB_Start_Skip_Fence)
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc9[simp]: 
"readLocs (Config 9 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc10[simp]:
"nextB (Config 10 (State (Vstore vs) avst (Heap hh) p), ibT, ibUT) =  
  (let l = array_loc aa2 (nat (vs vv * 512)) avst
  in (Config 11 (State (Vstore (vs(tt := hh l))) avst (Heap hh) p)), ibT, ibUT)"
apply(subst nextB_Assign)
unfolding endPC_def unfolding prog_def by auto


lemma readLocs_pc10[simp]: 
"readLocs (Config 10 (State (Vstore vs) avst hh p)) = {array_loc aa2 (nat (vs vv * 512)) avst}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc11[simp]:
"nextB (Config 11 s, ibT, ibUT) = (Config 12 s, ibT, ibUT)"
apply(subst nextB_Output)
unfolding endPC_def unfolding prog_def by auto 

lemma readLocs_pc11[simp]: 
"readLocs (Config 11 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc12[simp]:
"nextB (Config 12 s, ibT, ibUT) = (Config 3 s, ibT, ibUT)"
apply(subst nextB_Jump)
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc12[simp]: 
"readLocs (Config 12 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto


lemma nextB_pc13[simp]: 
"nextB (Config 13 s, ibT, ibUT) = 
 (Config 14 s, ibT, ibUT)"
apply(subst nextB_Output)
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc13[simp]: 
"readLocs (Config 13 s) = {}"
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
"pc < 14 \<Longrightarrow> (pc = 4 \<longrightarrow> ibUT \<noteq> LNil) \<Longrightarrow> (pc = 5 \<longrightarrow> ibT \<noteq> LNil) \<Longrightarrow>
(Config pc s, ibT, ibUT) \<rightarrow>B nextB (Config pc s, ibT, ibUT)"
apply(cases s) subgoal for vst avst hh p apply(cases vst, cases avst, cases hh)
subgoal for vs as h
using cases_14[of pc] apply safe
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
    by (simp add: prog_def Eq_def) 
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
      by (simp add: prog_def Eq_def, auto)  .
  subgoal apply(cases "vs xx = 0")  
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def Eq_def) 
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
      by (simp add: prog_def Eq_def, auto)  .
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def, metis llist.exhaust_sel)
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def, metis llist.exhaust_sel)
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def, metis llist.exhaust_sel)
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def, metis llist.exhaust_sel)

  subgoal apply(cases "vs xx < NN")  
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
      by (simp add: prog_def Eq_def) 
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
      by (simp add: prog_def Eq_def) .
  subgoal apply(cases "vs xx < NN")  
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
      by (simp add: prog_def Eq_def) 
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
      by (simp add: prog_def Eq_def) .
  subgoal apply(cases "vs xx < NN")  
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
      by (simp add: prog_def Eq_def) 
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
      by (simp add: prog_def Eq_def) .
  subgoal apply(cases "vs xx < NN")  
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
      by (simp add: prog_def Eq_def) 
    subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
      by (simp add: prog_def Eq_def) .

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
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) 
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) 
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def) 
  by simp_all . . 
  (*  *)

lemma not_finalB: 
"pc < 14 \<Longrightarrow> (pc = 4 \<longrightarrow> ibUT \<noteq> LNil) \<Longrightarrow> (pc = 5 \<longrightarrow> ibT \<noteq> LNil) \<Longrightarrow>
 \<not> finalB (Config pc s, ibT, ibUT)"
using nextB_stepB_pc by (simp add: stepB_iff_nextB)


lemma finalB_pc_iff': 
"pc < 14 \<Longrightarrow>
 finalB (Config pc s, ibT, ibUT) \<longleftrightarrow> 
 (pc = 4 \<and> ibUT = LNil) \<or> (pc = 5 \<and> ibT = LNil)"
  apply standard
    subgoal using nextB_stepB_pc[of pc] by (auto simp add: stepB_iff_nextB) 
    unfolding finalB_iff by (elim disjE, simp_all add: prog_def)
  

lemma finalB_pc_iff: 
"pc \<le> 14 \<Longrightarrow>
 finalB (Config pc s, ibT, ibUT) \<longleftrightarrow> 
 (pc = 14 \<or> (pc = 4 \<and> ibUT = LNil) \<or> (pc = 5 \<and> ibT = LNil))"
  using  Prog.finalB_iff endPC finalB_pc_iff' order_le_less finalB_iff
  by metis


lemma finalB_pcOf_iff[simp]:
"pcOf cfg \<le> 14 \<Longrightarrow> 
 finalB (cfg, ibT, ibUT) \<longleftrightarrow> (pcOf cfg = 14 \<or> (pcOf cfg = 4 \<and> ibUT = LNil) \<or> (pcOf cfg = 5 \<and> ibT = LNil))"
 using config.collapse finalB_pc_iff by metis


lemma finalS_cond:"pcOf cfg < 14 \<Longrightarrow> noMisSpec cfgs \<Longrightarrow> ibT \<noteq> LNil \<Longrightarrow> ibUT \<noteq> LNil \<Longrightarrow> \<not> finalS (pstate, cfg, cfgs, ibT, ibUT, ls)"
  apply(cases cfg)
  subgoal for pc s apply(cases s)
  subgoal for vst avst hh p apply(cases vst, cases avst, cases hh)
    subgoal for vs as h
      using cases_14[of pc] apply(elim disjE) unfolding finalS_defs noMisSpec_def
      subgoal using nonspec_normal[of "[]" "Config pc (State (Vstore vs) avst hh p)" 
                                        pstate pstate ibT ibUT 
                                        "Config 1 (State (Vstore vs) avst hh p)" 
                                        ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls]
        using is_If_pc by force


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
                                             ibT ibUT "Config (if vs xx \<noteq> 0 then 4 else 13) (State (Vstore vs) avst hh p)"
                                             ibT ibUT "Config (if vs xx \<noteq> 0 then 13 else 4) (State (Vstore vs) avst hh p)"
                                             ibT ibUT "[Config (if vs xx \<noteq> 0 then 13 else 4) (State (Vstore vs) avst hh p)]"
                                             "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
      prefer 9 subgoal by metis by (simp add: finalM_iff)+

      subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)"
                                    pstate pstate ibT ibUT 
                                    "Config (if vs xx \<noteq> 0 then 4 else 13) (State (Vstore vs) avst hh p)" 
                                    ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
      prefer 7 subgoal by metis by simp_all . 

      subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                                    pstate pstate ibT ibUT 
                                    "Config 5 (State (Vstore (vs(xx:= lhd ibUT))) avst hh p)" 
                                    ibT "ltl ibUT" "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
              prefer 7 subgoal by metis by simp_all 

      subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                                    pstate pstate ibT ibUT 
                                    "Config 6 (State (Vstore (vs(yy:= lhd ibT))) avst hh p)" 
                                    "ltl ibT" ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
              prefer 7 subgoal by metis by simp_all 

    subgoal apply(cases "mispred pstate [6]")
      subgoal apply(frule nonspec_mispred[of cfgs "Config pc (State (Vstore vs) avst hh p)"
                                             pstate "update pstate [pcOf (Config pc (State (Vstore vs) avst hh p))]"
                                             ibT ibUT "Config (if vs xx < NN then 7 else 12) (State (Vstore vs) avst hh p)"
                                             ibT ibUT "Config (if vs xx < NN then 12 else 7) (State (Vstore vs) avst hh p)"
                                             ibT ibUT "[Config (if vs xx < NN then 12 else 7) (State (Vstore vs) avst hh p)]"
                                             "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
      prefer 9 subgoal by metis by (simp add: finalM_iff)+

      subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)"
                                    pstate pstate ibT ibUT 
                                    "Config (if vs xx < NN then 7 else 12) (State (Vstore vs) avst hh p)" 
                                    ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
      prefer 7 subgoal by metis by simp_all . 

    subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                         pstate pstate ibT ibUT 
                         "(let l = (array_loc aa1 (nat (vs xx)) (Avstore as)) 
                                in (Config 8 (State (Vstore (vs(vv := h l))) avst hh p)))" 
                         ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
            prefer 7 subgoal by metis by simp_all

    subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                         pstate pstate ibT ibUT 
                         "(Config 9 (State (Vstore vs) avst hh p))" 
                         ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
            prefer 7 subgoal by metis by simp_all

    subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                                    pstate pstate ibT ibUT 
                                    "Config 10 (State (Vstore vs) avst hh p)" 
                                    ibT ibUT "[]" ls ls])
            prefer 7 subgoal by metis by simp_all

    subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                         pstate pstate ibT ibUT 
                         "(let l = (array_loc aa2 (nat (vs vv * 512)) (Avstore as)) 
                                in (Config 11 (State (Vstore (vs(tt := h l))) avst hh p)))" 
                         ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
            prefer 7 subgoal by metis by simp_all

    subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                                    pstate pstate ibT ibUT 
                                    "Config 12 (State (Vstore vs) avst hh p)" 
                                    ibT ibUT "[]" ls ls])
            prefer 7 subgoal by metis by simp_all

    subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)"
                                    pstate pstate ibT ibUT 
                                    "Config 3 (State (Vstore vs) avst hh p)" 
                                    ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
      prefer 7 subgoal by metis by simp_all 

    subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)"
                                    pstate pstate ibT ibUT 
                                    "Config 14 (State (Vstore vs) avst hh p)" 
                                    ibT ibUT "[]" ls ls])
            prefer 7 subgoal by metis by simp_all
    by simp_all . . .

lemma finalS_cond':"pcOf cfg < 14 \<Longrightarrow> cfgs = [] \<Longrightarrow> ibT \<noteq> LNil \<Longrightarrow> ibUT \<noteq> LNil \<Longrightarrow>
                    \<not> finalS (pstate, cfg, cfgs, ibT, ibUT, ls)"
  using finalS_cond by (simp add: noMisSpec_def)

lemma finalS_while_spec:
      "whileSpeculation cfg (last cfgs) \<Longrightarrow> 
       length cfgs = Suc 0 \<Longrightarrow>
      \<not> finalS (pstate, cfg, cfgs, ibT, ibUT, ls)"
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
        using empty_set  resolve.simps length_0_conv 
              length_1_butlast length_Suc_conv list.simps(9,15) 
              cfgs_map not_Cons_self2 spec_resolve by metis . . . . 

lemma finalS_while_spec_L2:
      "pcOf cfg = 7 \<Longrightarrow>
       whileSpeculation (cfgs!0) (last cfgs) \<Longrightarrow> 
       length cfgs = 2 \<Longrightarrow>
      \<not> finalS (pstate, cfg, cfgs, ibT, ibUT, ls)"
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
      "(pcOf (last cfgs) \<in> inThenIfBeforeOutput \<and> pcOf cfg = 12) \<or> 
       (pcOf (last cfgs) \<in> inElseIf \<and> pcOf cfg = 7) \<Longrightarrow> 
       length cfgs = Suc 0 \<Longrightarrow>
      \<not> finalS (pstate, cfg, cfgs, ibT, ibUT, ls)"
  unfolding inThenIfBeforeOutput_def inElseIf_def
  apply(simp,cases "last cfgs")
  subgoal for pc s apply(cases s)
  subgoal for vst avst hh p apply(cases vst, cases hh)
    subgoal for vs h
      apply(elim disjE, elim conjE) unfolding finalS_defs
      subgoal apply(elim disjE)
        subgoal apply(rule notI, 
      erule allE[of _ "(pstate,cfg,
                        [Config 8 (State (Vstore (vs(vv := h (array_loc aa1 (nat (vs xx)) avst)))) avst hh p)],
                        ibT,ibUT,ls \<union> readLocs (last cfgs))"])
          by (erule notE, 
        rule spec_normal[of _ _ _ _ _ _"Config 8 (State (Vstore (vs(vv := h (array_loc aa1 (nat (vs xx)) avst)))) avst hh p)"], auto)
        subgoal apply(rule notI, erule allE[of _ "(update pstate (pcOf cfg # map pcOf cfgs),cfg,[],ibT,ibUT,ls \<union> readLocs (last cfgs))"])
          by(erule notE, rule spec_resolve, auto) .
      subgoal apply(elim conjE, elim disjE) 
        subgoal apply(rule notI, erule allE[of _ "
            (pstate, cfg, [Config 3 (State (Vstore vs) avst hh p)], ibT,ibUT,
             ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p)))"])
          by(erule notE, rule spec_normal[of _ _ _ _ _ _"Config 3 (State (Vstore vs) avst hh p)"], auto)

        subgoal apply(cases "mispred pstate [7,3]")
          subgoal apply(rule notI, erule allE[of _ "
            (update pstate (pcOf cfg # map pcOf cfgs),
           cfg,
           [Config (if vs xx \<noteq> 0 then 4 else 13) (State (Vstore vs) avst hh p),
            Config (if vs xx \<noteq> 0 then 13 else 4) (State (Vstore vs) avst hh p)], ibT, ibUT,
           ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p)))"])
                  apply(erule notE, 
        rule spec_mispred[of _ _ _ _ _ _
           "Config (if vs xx \<noteq> 0 then 4 else 13) (State (Vstore vs) avst hh p)" _
         _ "Config (if vs xx \<noteq> 0 then 13 else 4) (State (Vstore vs) avst hh p)" ibT ibUT]) 
            by(auto simp: finalM_iff)

        apply(rule notI, erule allE[of _ "
            (pstate, cfg, [Config (if vs xx \<noteq> 0 then 4 else 13) (State (Vstore vs) avst hh p)], ibT,ibUT,
             ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p)))"])
          by (erule notE, 
        rule spec_normal[of _ _ _ _ _ _"Config (if vs xx \<noteq> 0 then 4 else 13) (State (Vstore vs) avst hh p)"], auto)

        subgoal by (metis resolve_74 stepS_spec_resolve_iff 
                          map_L1 cfgs_Suc_zero not_Cons_self2) 
        subgoal by (metis resolve_713 stepS_spec_resolve_iff 
                          map_L1 cfgs_Suc_zero not_Cons_self2) 
  . . . . .



end