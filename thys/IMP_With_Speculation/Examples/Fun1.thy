section "Disproof of Relative Security for fun1"
theory Fun1
imports "../Instance_IMP/Instance_Secret_IMem" 
  "Secret_Directed_Unwinding.SD_Unwinding_fin" 
begin 

subsection "Function definition and Boilerplate"
no_notation bot ("\<bottom>")
consts NN :: nat

consts input :: int
definition aa1 :: "avname" where "aa1 = ''a1''" 
definition aa2 :: "avname" where "aa2 = ''a2''" 
definition vv :: "avname" where "vv = ''v''" 
definition xx :: "avname" where "xx = ''i''" 
definition tt :: "avname" where "tt = ''tt''" 

lemma NN_suc[simp]:"nat (NN + 1) = Suc (nat NN)" 
  by force

lemma NN:"NN\<ge>0" by auto


lemmas vvars_defs = aa1_def aa2_def vv_def xx_def tt_def

lemma vvars_dff[simp]: 
"aa1 \<noteq> aa2" "aa1 \<noteq> vv" "aa1 \<noteq> xx" "aa1 \<noteq> tt"
"aa2 \<noteq> aa1" "aa2 \<noteq> vv" "aa2 \<noteq> xx" "aa2 \<noteq> tt"
"vv \<noteq> aa1" "vv \<noteq> aa2"  "vv \<noteq> xx" "vv \<noteq> tt"
"xx \<noteq> aa1" "xx \<noteq> aa2" "xx \<noteq> vv" "xx \<noteq> tt"
"tt \<noteq> aa1" "tt \<noteq> aa2" "tt \<noteq> vv" "tt \<noteq> xx"
unfolding vvars_defs by auto


consts size_aa1 :: nat
consts size_aa2 :: nat

definition "s_add = {a. a \<noteq> nat NN+1}"
fun vs\<^sub>0::"char list \<Rightarrow> int" where 
           "vs\<^sub>0 x = 0"

lemma vs0[simp]:"(\<lambda>x. 0) = vs\<^sub>0"  unfolding vs\<^sub>0.simps by simp

(*avstore*)
fun as:: "char list \<Rightarrow> nat \<times> nat" where 
        "as a = (if a = aa1 then (0, nat NN)
                   else (if a = aa2 then (nat NN, nat size_aa2) 
                   else (nat size_aa2,0)))"

definition "avst' \<equiv> (Avstore as)"

lemmas avst_defs = avst'_def as.simps

lemma avstore_loc[simp]:"Avstore (\<lambda>a. if a = aa1 then (0, nat NN) else if a = aa2 then (nat NN, nat size_aa2) else (nat size_aa2, 0)) =
    avst'"
  unfolding avst_defs by auto

abbreviation "read_add \<equiv> {a. a \<noteq> (nat NN + 1)}"

(* The initial vstore can be anything *)
fun initVstore :: "vstore \<Rightarrow> bool" where
"initVstore (Vstore vst) = (vst = vs\<^sub>0)"
(* The initial avstore contains two arrays named aa1 and aa2 located one after the other *)
fun initAvstore :: "avstore \<Rightarrow> bool" where
"initAvstore avst  = (avst = avst')"
fun initHeap::"(nat \<Rightarrow> int) \<Rightarrow> bool" where
"initHeap h = (\<forall>x\<in>read_add. h x = 0)"

lemma initAvstore_0[intro]:"initAvstore avst' \<Longrightarrow> array_base aa1 avst' = 0"
  unfolding avst_defs array_base_def
  by (smt (verit, del_insts) avstore.case fstI)

fun istate ::"state \<Rightarrow> bool"  where
  "istate s = 
  (initVstore (getVstore s) \<and> 
  initAvstore (getAvstore s) \<and> 
  initHeap (getHheap s))"

definition "prog \<equiv>
[
 \<^cancel>\<open>0 \<close> Start , 
 \<^cancel>\<open>1 \<close> Input U xx ,
 \<^cancel>\<open>2 \<close> tt ::= (N 0),
 \<^cancel>\<open>3 \<close> IfJump (Less (V xx) (N NN)) 4 5,
 \<^cancel>\<open>4 \<close>   tt ::= (VA aa2 (Times (VA aa1 (V xx)) (N 512))) ,
 \<^cancel>\<open>5 \<close> Output U (V tt) 
]"

(* *)

lemma cases_5: "(i::pcounter) = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or> i = 5 \<or> i > 5"
apply(cases i, simp_all) 
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
subgoal for i apply(cases i, simp_all)
  . . . . . . 

lemma xx_NN_cases: "vs xx < (int NN) \<or> vs xx \<ge> (int NN)" by auto

lemma is_If_pcOf[simp]: 
"pcOf cfg < 6 \<Longrightarrow> is_IfJump (prog ! (pcOf cfg)) \<longleftrightarrow> pcOf cfg = 3"
apply(cases cfg) subgoal for pc s using cases_5[of "pcOf cfg "] 
apply (auto simp: prog_def) . .

lemma is_If_pc[simp]: 
"pc < 6 \<Longrightarrow> is_IfJump (prog ! pc) \<longleftrightarrow> pc = 3"
using cases_5[of pc] 
by (auto simp: prog_def) 

lemma eq_Fence_pc[simp]: 
"pc < 6 \<Longrightarrow> prog ! pc \<noteq> Fence"
using cases_5[of pc] 
  by (auto simp: prog_def)



 
(* *)

fun mispred :: "predState \<Rightarrow> pcounter list \<Rightarrow> bool" where
  "mispred p pc = (if pc = [3] then True else False)"

fun resolve :: "predState \<Rightarrow> pcounter list \<Rightarrow> bool" where
  "resolve p pc = (if pc = [5,5] then True else False)"

consts update :: "predState \<Rightarrow> pcounter list \<Rightarrow> predState"
consts pstate\<^sub>0 :: predState
(* *)
interpretation Prog_Mispred_Init where 
prog = prog and initPstate = pstate\<^sub>0 and 
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

lemma endPC[simp]: "endPC = 6"
unfolding endPC_def unfolding prog_def by auto

(* *)

lemma is_getTrustedInput_pcOf[simp]: "pcOf cfg < 6 \<Longrightarrow> is_getInput (prog!(pcOf cfg)) \<longleftrightarrow> pcOf cfg = 1"
  using cases_5[of "pcOf cfg"] by (auto simp: prog_def)

lemma getTrustedInput_pcOf[simp]: "(prog!1) = Input U xx"
   by (auto simp: prog_def)


lemma is_Output_pcOf[simp]: "pcOf cfg < 6 \<Longrightarrow> is_Output (prog!(pcOf cfg)) \<longleftrightarrow> pcOf cfg = 5 \<or> pcOf cfg = 6"
using cases_5[of "pcOf cfg"] by (auto simp: prog_def)


lemma is_Fence_pcOf[simp]: "pcOf cfg < 6 \<Longrightarrow>(prog!(pcOf cfg)) \<noteq> Fence"
using cases_5[of "pcOf cfg"] by (auto simp: prog_def)

lemma prog0[simp]:"prog ! 0 = Start"
  by (auto simp: prog_def)

lemma prog1[simp]:"prog ! (Suc 0) = Input U xx"
  by (auto simp: prog_def)

lemma prog2[simp]:"prog ! 2 = tt ::= (N 0)"
  by (auto simp: prog_def)

lemma prog3[simp]:"prog ! 3 = IfJump (Less (V xx) (N NN)) 4 5"
  by (auto simp: prog_def)

lemma prog4[simp]:"prog ! 4 = tt ::= (VA aa2 (Times (VA aa1 (V xx)) (N 512)))"
  by (auto simp: prog_def)

lemma prog5[simp]:"prog ! 5 = Output U (V tt)"
  by (auto simp: prog_def)
(* *)

lemma isSecV_pcOf[simp]: 
"isSecV (cfg,ibT, ibUT) \<longleftrightarrow> pcOf cfg = 0"
using isSecV_def by simp

lemma isSecO_pcOf[simp]: 
"isSecO (pstate,cfg,cfgs,ibT,ibUT,ls) \<longleftrightarrow> (pcOf cfg = 0 \<and> cfgs = [])"
using isSecO_def by simp

(* *)

lemma getInputT_not[simp]: "pcOf cfg < 6 \<Longrightarrow> 
(prog ! pcOf cfg) \<noteq> Input T x"
apply(cases cfg) subgoal for pc s using cases_5[of "pcOf cfg "] 
by (auto simp: prog_def) .

lemma getActV_pcOf[simp]: 
"pcOf cfg < 6 \<Longrightarrow> 
 getActV (cfg,ibT,ibUT,ls) = 
 (if pcOf cfg = 1 then lhd ibUT else \<bottom>)"
apply(subst getActV_simps) unfolding prog_def 
apply simp  
using getActV_simps not_is_getTrustedInput_getActV prog_def by auto

lemma getObsV_pcOf[simp]: 
"pcOf cfg < 6 \<Longrightarrow>  
 getObsV (cfg,ibT,ibUT,ls) = 
 (if pcOf cfg = 5 then 
  (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)
  else \<bottom> 
 )"
apply(subst getObsV_simps) 
unfolding prog_def apply simp  
using getObsV_simps not_is_Output_getObsV is_Output_pcOf prog_def 
  by (metis less_irrefl_nat)

lemma getActO_pcOf[simp]: 
"pcOf cfg < 6 \<Longrightarrow> 
 getActO (pstate,cfg,cfgs,ibT,ibUT,ls) = 
 (if pcOf cfg = 1 \<and> cfgs = [] then lhd ibUT else \<bottom>)"
apply(subst getActO_simps)
apply(cases cfgs, auto)
unfolding prog_def 
using getActV_simps getActV_pcOf prog_def by presburger

lemma getObsO_pcOf[simp]: 
"pcOf cfg < 6 \<Longrightarrow>  
 getObsO (pstate,cfg,cfgs,ibT,ibUT,ls) = 
 (if (pcOf cfg = 5 \<and> cfgs = []) then 
  (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)
  else \<bottom> 
 )"
apply(subst getObsO_simps) 
apply(cases cfgs, auto)
unfolding prog_def 
using getObsV_simps is_Output_pcOf not_is_Output_getObsV prog_def 
  by (metis getObsV_pcOf)

(* *)

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
"ibUT \<noteq> LNil \<Longrightarrow> nextB (Config 1 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config 2 (State (Vstore (vs(xx := lhd ibUT))) avst h p), ibT, ltl ibUT)"
apply(subst nextB_getUntrustedInput')
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc1[simp]: 
"readLocs (Config 1 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

lemma nextB_pc1'[simp]: 
"ibUT \<noteq> LNil \<Longrightarrow> nextB (Config (Suc 0) (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config 2 (State (Vstore (vs(xx := lhd ibUT))) avst h p), ibT, ltl ibUT)"
apply(subst nextB_getUntrustedInput')
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc1'[simp]: 
"readLocs (Config (Suc 0) s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)
lemma nextB_pc2[simp]: 
"nextB (Config 2 (State (Vstore vs) avst h p), ibT, ibUT) = 
 ((Config 3 (State (Vstore (vs(tt := 0))) avst h p)), ibT, ibUT)"
apply(subst nextB_Assign)
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc2[simp]: 
"readLocs (Config 2 (State (Vstore vs) avst h p)) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc3_then[simp]: 
"vs xx < NN \<Longrightarrow>
 nextB (Config 3 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config 4 (State (Vstore vs) avst h p), ibT, ibUT)"
apply(subst nextB_IfTrue)
unfolding endPC_def unfolding prog_def by auto

lemma nextB_pc3_else[simp]: 
"vs xx \<ge> NN \<Longrightarrow>
 nextB (Config 3 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config 5 (State (Vstore vs) avst h p), ibT, ibUT)"
apply(subst nextB_IfFalse)
unfolding endPC_def unfolding prog_def by auto

lemma nextB_pc3: 
"nextB (Config 3 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config (if vs xx < NN then 4 else 5) (State (Vstore vs) avst h p), ibT, ibUT)"
  by(cases "vs xx < NN", auto)

lemma nextM_pc3_then[simp]: 
"vs xx \<ge> NN \<Longrightarrow>
 nextM (Config 3 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config 4 (State (Vstore vs) avst h p), ibT, ibUT)"
apply(subst nextM_IfTrue)
unfolding endPC_def unfolding prog_def by auto

lemma nextM_pc3_else[simp]: 
"vs xx < NN \<Longrightarrow>
 nextM (Config 3 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config 5 (State (Vstore vs) avst h p), ibT, ibUT)"
apply(subst nextM_IfFalse)
unfolding endPC_def unfolding prog_def by auto

lemma nextM_pc3: 
"nextM (Config 3 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config (if vs xx < NN then 5 else 4) (State (Vstore vs) avst h p), ibT, ibUT)"
by(cases "vs xx < NN", auto)

lemma readLocs_pc3[simp]: 
"readLocs (Config 3 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc4[simp]: 
"nextB (Config 4 (State (Vstore vs) avst (Heap h) p), ibT, ibUT) = 
 (let i = array_loc aa1 (nat (vs xx)) avst; j = (array_loc aa2 (nat ((h i) * 512)) avst) 
  in (Config 5 (State (Vstore (vs(tt := h j))) avst (Heap h) p)), ibT, ibUT)"
apply(subst nextB_Assign)
  unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc4[simp]: 
"readLocs (Config 4 (State (Vstore vs) avst (Heap h) p)) = 
(let i = array_loc aa1 (nat (vs xx)) avst; 
     j = (array_loc aa2 (nat ((h i) * 512)) avst)
in {i, j})"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)


lemma nextB_pc5[simp]:
"nextB (Config 5 s, ibT, ibUT) = (Config 6 s, ibT, ibUT)"
apply(subst nextB_Output)
unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc5[simp]: 
"readLocs (Config 5 (State (Vstore vs) avst (Heap h) p)) = 
 {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto


lemma nextB_stepB_pc: 
"pc < 6 \<Longrightarrow> (pc = 1 \<longrightarrow> ibUT \<noteq> LNil) \<Longrightarrow> 
(Config pc s, ibT, ibUT) \<rightarrow>B nextB (Config pc s, ibT, ibUT)"
apply(cases s) subgoal for vst avst hh p apply(cases vst, cases avst, cases hh)
subgoal for vs as h
using cases_5[of pc] apply safe
  subgoal by simp 
  subgoal by simp 
  (* *)
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def, metis llist.collapse)

  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
    by (simp add: prog_def)  
  subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
  by (simp add: prog_def)
  (* *)
  subgoal by(cases "vs xx < NN", simp_all)  
  subgoal by(cases "vs xx < NN", simp_all)  
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
  by simp+ . . 


lemma not_finalB: 
"pc < 6 \<Longrightarrow> (pc = 1 \<longrightarrow> ibUT \<noteq> LNil) \<Longrightarrow> 
 \<not> finalB (Config pc s, ibT, ibUT)"
using nextB_stepB_pc by (simp add: stepB_iff_nextB)

lemma finalB_pc_iff': 
"pc < 6 \<Longrightarrow>
 finalB (Config pc s, ibT, ibUT) \<longleftrightarrow> 
 (pc = 1 \<and> ibUT = LNil)"
  subgoal apply safe
    subgoal using nextB_stepB_pc[of pc] by (auto simp add: stepB_iff_nextB) 
    subgoal using nextB_stepB_pc[of pc] by (auto simp add: stepB_iff_nextB) 
    subgoal using finalB_iff by auto . .


lemma finalB_pc_iff: 
"pc \<le> 6 \<Longrightarrow>
 finalB (Config pc s, ibT, ibUT) \<longleftrightarrow> 
 (pc = 1 \<and> ibUT = LNil \<or> pc = 6)"
  using cases_5[of pc] apply (elim disjE, simp add: finalB_def)
  subgoal by (meson final_def stebB_0)
  by (simp add: finalB_pc_iff' finalB_endPC)+

lemma finalB_pcOf_iff[simp]:
"pcOf cfg \<le> 6 \<Longrightarrow> 
 finalB (cfg, ibT, ibUT) \<longleftrightarrow> (pcOf cfg = 1 \<and> ibUT = LNil \<or> pcOf cfg = 6)"
  by (metis config.collapse finalB_pc_iff) 


definition "vs\<^sub>i_t cfg \<equiv> (vstore (getVstore (stateOf cfg)) xx) < NN"
definition "vs\<^sub>i_f cfg \<equiv> (vstore (getVstore (stateOf cfg)) xx) \<ge> NN"
lemma vs_xx_cases:"vs\<^sub>i_t cfg \<or> vs\<^sub>i_f cfg" unfolding vs\<^sub>i_t_def vs\<^sub>i_f_def by auto

lemmas vs\<^sub>i_defs = vs\<^sub>i_t_def vs\<^sub>i_f_def

lemma bool_invar[simp]:"\<not>vs\<^sub>i_t (Config 6 s) \<Longrightarrow> vs\<^sub>i_t (Config 6 s) \<Longrightarrow> (Config 6 s, ib1) \<rightarrow>B (Config 6 s, ib1) \<Longrightarrow> False"
  unfolding vs\<^sub>i_defs
  by simp
lemma nextB_vs_consistent_aux: 
  "2 \<le> pc \<and> pc < 6 \<Longrightarrow>
   (nextB (Config pc (State (Vstore vs) avst (Heap h) p),ibT, ibUT)) = (Config pc' (State (Vstore vs') avst'' (Heap h') p'),ibT', ibUT') \<Longrightarrow> 
    avst = avst'' \<and>
    vs xx = vs' xx \<and>
    h = h'  \<and>
    pc < pc'"
  using cases_5[of pc] apply(elim disjE) apply simp_all
  subgoal by auto
  subgoal using xx_NN_cases[of vs] by(elim disjE, simp_all)
  by auto 

lemma nextB_vs_consistent: 
  "2 \<le> pcOf cfg \<and> pcOf cfg < 6 \<Longrightarrow>
   (nextB (cfg, ibT, ibUT)) = (cfg', ibT', ibUT') \<Longrightarrow> 
    (getAvstore (stateOf cfg)) = (getAvstore (stateOf cfg')) \<and> 
    (getHheap (stateOf cfg)) = (getHheap (stateOf cfg')) \<and> 
    vstore (getVstore (stateOf cfg)) xx = vstore (getVstore (stateOf cfg')) xx"
  apply(cases cfg) subgoal for pc s 
  apply(cases s) subgoal for vstore avst heap_h p 
  apply (cases heap_h, cases vstore, cases avst) subgoal for h vs 
  apply(cases cfg') subgoal for pc' s'
  apply(cases s') subgoal for vstore' avst'' heap_h' p' 
  apply (cases heap_h', cases vstore', cases avst'')  subgoal for h vs 
  using nextB_vs_consistent_aux apply simp 
  by blast . . . . . .


lemma nextB_vs\<^sub>i_t_consistent: 
  "2 \<le> pcOf cfg \<and> pcOf cfg < 6 \<Longrightarrow>
   (nextB (cfg, ibT, ibUT)) = (cfg', ibT', ibUT') \<Longrightarrow> 
   vs\<^sub>i_t cfg \<longleftrightarrow> vs\<^sub>i_t cfg'"
  unfolding vs\<^sub>i_defs using  nextB_vs_consistent 
  by simp

lemma nextB_vs\<^sub>i_f_consistent: 
  "2 \<le> pcOf cfg \<and> pcOf cfg < 6 \<Longrightarrow>
   (nextB (cfg, ibT, ibUT)) = (cfg', ibT', ibUT') \<Longrightarrow> 
   vs\<^sub>i_f cfg \<longleftrightarrow> vs\<^sub>i_f cfg'"
  unfolding vs\<^sub>i_defs using  nextB_vs_consistent 
  by simp


end